open LeanExpr
module N = LeanName
module Json = Yojson.Safe
module RRange = LeanParseShared.RRange

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
  seen_meta : bool;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
    seen_meta = false;
  }

let is_ndjson_line l =
  let l = String.trim l in
  String.length l > 0 && l.[0] = '{'

let err ~lcnt msg =
  CErrors.user_err Pp.(str "NDJSON parse error at line " ++ int lcnt ++ str ": " ++ str msg)

let member name = function
  | `Assoc fields -> List.assoc_opt name fields
  | _ -> None

let require_member ~lcnt name json =
  match member name json with
  | Some v -> v
  | None -> err ~lcnt ("missing field " ^ name)

let require_string ~lcnt name json =
  match require_member ~lcnt name json with
  | `String s -> s
  | _ -> err ~lcnt ("field " ^ name ^ " must be a string")

let require_int ~lcnt name json =
  match require_member ~lcnt name json with
  | `Int i -> i
  | _ -> err ~lcnt ("field " ^ name ^ " must be an integer")

let require_bool ~lcnt name json =
  match require_member ~lcnt name json with
  | `Bool b -> b
  | _ -> err ~lcnt ("field " ^ name ^ " must be a boolean")

let forbid_member ~lcnt name json =
  match member name json with
  | Some _ -> err ~lcnt ("unexpected field " ^ name)
  | None -> ()

let require_list ~lcnt name json =
  match require_member ~lcnt name json with
  | `List xs -> xs
  | _ -> err ~lcnt ("field " ^ name ^ " must be an array")

let as_int ~lcnt = function
  | `Int i -> i
  | _ -> err ~lcnt "expected integer"

(* Export records are tagged unions: an index field plus exactly one "kind"
   key carrying the payload.  [tagged] returns that single key and its payload,
   rejecting records that carry none of [keys] (or more than one). *)
let tagged ~lcnt ~what keys json =
  match
    List.filter_map
      (fun k -> match member k json with Some v -> Some (k, v) | None -> None)
      keys
  with
  | [ tag ] -> tag
  | _ -> err ~lcnt ("bad " ^ what ^ " record")

let get_name ~lcnt state i =
  try RRange.get state.names i
  with Not_found -> err ~lcnt ("unknown name id " ^ string_of_int i)

let get_expr ~lcnt state i =
  try RRange.get state.exprs i
  with Not_found -> err ~lcnt ("unknown expression id " ^ string_of_int i)

let get_univ ~lcnt state i =
  try RRange.get state.univs i
  with Not_found -> err ~lcnt ("unknown level id " ^ string_of_int i)

let expect_next ~lcnt kind expected actual =
  if expected <> actual then
    err
      ~lcnt
      (kind ^ " id " ^ string_of_int actual ^ " is not the next expected id "
     ^ string_of_int expected)

let binders ~lcnt = function
  | "default" -> NotImplicit
  | "implicit" -> Maximal
  | "strictImplicit" -> NonMaximal
  | "instImplicit" -> Typeclass
  | b -> err ~lcnt ("unknown Lean binderInfo " ^ b)

let parse_name ~lcnt state json =
  let next = require_int ~lcnt "in" json in
  expect_next ~lcnt "name" (RRange.length state.names) next;
  let base p = get_name ~lcnt state (require_int ~lcnt "pre" p) in
  let name =
    match tagged ~lcnt ~what:"name" [ "str"; "num" ] json with
    | "str", p -> N.append (base p) (require_string ~lcnt "str" p)
    | "num", p -> N.raw_append (base p) (string_of_int (require_int ~lcnt "i" p))
    | _ -> err ~lcnt "bad name record"
  in
  ({ state with names = RRange.append state.names name }, None)

let parse_level ~lcnt state json =
  let next = require_int ~lcnt "il" json in
  expect_next ~lcnt "level" (RRange.length state.univs) next;
  let univ j = get_univ ~lcnt state (as_int ~lcnt j) in
  let level =
    match tagged ~lcnt ~what:"level" [ "succ"; "max"; "imax"; "param" ] json with
    | "succ", `Int base -> U.Succ (get_univ ~lcnt state base)
    | "max", `List [ a; b ] -> U.Max (univ a, univ b)
    | "imax", `List [ a; b ] -> U.IMax (univ a, univ b)
    | "param", `Int n -> U.UNamed (get_name ~lcnt state n)
    | _ -> err ~lcnt "bad level record"
  in
  ({ state with univs = RRange.append state.univs level }, None)

let parse_nat_lit ~lcnt = function
  | `String n ->
    let n =
      try Z.of_string n
      with Invalid_argument _ | Failure _ -> err ~lcnt "bad natural literal"
    in
    if Z.sign n < 0 then err ~lcnt "natural literal must be non-negative";
    n
  | `Int n ->
    let n = Z.of_int n in
    if Z.sign n < 0 then err ~lcnt "natural literal must be non-negative";
    n
  | _ -> err ~lcnt "bad natural literal"

let parse_expr ~lcnt state json =
  let next = require_int ~lcnt "ie" json in
  expect_next ~lcnt "expression" (RRange.length state.exprs) next;
  let int_at p k = require_int ~lcnt k p in
  let name_at p k = get_name ~lcnt state (int_at p k) in
  let expr_at p k = get_expr ~lcnt state (int_at p k) in
  let abstraction p =
    ( binders ~lcnt (require_string ~lcnt "binderInfo" p),
      name_at p "name",
      expr_at p "type",
      expr_at p "body" )
  in
  let expr =
    match
      tagged ~lcnt ~what:"expression"
        [ "bvar"; "sort"; "const"; "app"; "lam"; "forallE"; "letE"; "proj";
          "natVal"; "strVal"; "mdata" ]
        json
    with
    | "bvar", `Int n -> Bound n
    | "sort", `Int u -> Sort (get_univ ~lcnt state u)
    | "const", p ->
      let us =
        require_list ~lcnt "us" p
        |> List.map (fun u -> get_univ ~lcnt state (as_int ~lcnt u))
      in
      Const (name_at p "name", us)
    | "app", p -> App (expr_at p "fn", expr_at p "arg")
    | "lam", p ->
      let bk, nm, ty, body = abstraction p in
      Lam (bk, nm, ty, body)
    | "forallE", p ->
      let bk, nm, ty, body = abstraction p in
      Pi (bk, nm, ty, body)
    | "letE", p ->
      Let
        {
          name = name_at p "name";
          ty = expr_at p "type";
          v = expr_at p "value";
          rest = expr_at p "body";
        }
    | "proj", p -> Proj (name_at p "typeName", int_at p "idx", expr_at p "struct")
    | "natVal", n -> Nat (parse_nat_lit ~lcnt n)
    | "strVal", `String s -> String s
    | "mdata", p -> expr_at p "expr"
    | _ -> err ~lcnt "bad expression record"
  in
  ({ state with exprs = RRange.append state.exprs expr }, None)

let level_params ~lcnt state payload =
  require_list ~lcnt "levelParams" payload
  |> List.map (fun n -> get_name ~lcnt state (as_int ~lcnt n))

let line_msg ~lcnt name =
  Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)

let parse_axiom ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  line_msg ~lcnt name;
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Ax { name; ty; univs })))

let reducibility_height ~lcnt payload =
  match require_member ~lcnt "hints" payload with
  | `String ("opaque" | "abbrev") -> None
  | `Assoc fields -> (
    match List.assoc_opt "regular" fields with
    | Some (`Int n) when n >= 0 -> Some n
    | _ -> err ~lcnt "field hints must be opaque, abbrev, or regular")
  | _ -> err ~lcnt "field hints must be opaque, abbrev, or regular"

let require_safety ~lcnt payload =
  match require_member ~lcnt "safety" payload with
  | `String ("unsafe" | "safe" | "partial") -> ()
  | _ -> err ~lcnt "field safety must be unsafe, safe, or partial"

let parse_deflike_common ~height ~lcnt state payload =
  let name = get_name ~lcnt state (require_int ~lcnt "name" payload) in
  line_msg ~lcnt name;
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" payload) in
  let body = get_expr ~lcnt state (require_int ~lcnt "value" payload) in
  let univs = level_params ~lcnt state payload in
  (state, Some (Entry (Def { name; ty; body; univs; height })))

let validate_mutual_group ~lcnt state payload =
  require_list ~lcnt "all" payload
  |> List.iter (fun n -> ignore (get_name ~lcnt state (as_int ~lcnt n)))

let parse_def ~lcnt state payload =
  forbid_member ~lcnt "isUnsafe" payload;
  let height = reducibility_height ~lcnt payload in
  require_safety ~lcnt payload;
  validate_mutual_group ~lcnt state payload;
  parse_deflike_common ~height ~lcnt state payload

let parse_thm ~lcnt state payload =
  forbid_member ~lcnt "isUnsafe" payload;
  forbid_member ~lcnt "safety" payload;
  validate_mutual_group ~lcnt state payload;
  parse_deflike_common ~height:None ~lcnt state payload

let parse_opaque ~lcnt state payload =
  ignore (require_bool ~lcnt "isUnsafe" payload);
  validate_mutual_group ~lcnt state payload;
  parse_deflike_common ~height:None ~lcnt state payload

let parse_quot ~lcnt state payload =
  ignore (require_string ~lcnt "kind" payload);
  line_msg ~lcnt LeanParseShared.quot_name;
  (state, Some (Entry (Quot LeanParseShared.quot_name)))

let parse_ctor_val ~lcnt state ctor_json =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ctor_json) in
  let ty = get_expr ~lcnt state (require_int ~lcnt "type" ctor_json) in
  (name, ty)

let parse_ind_param_shape ~lcnt f =
  try f ()
  with Assert_failure _ ->
    err ~lcnt "inductive parameter count does not match exported type"

let parse_ind_val ~lcnt state ind_json ctor_jsons =
  let name = get_name ~lcnt state (require_int ~lcnt "name" ind_json) in
  line_msg ~lcnt name;
  let nparams = require_int ~lcnt "numParams" ind_json in
  let ty0 = get_expr ~lcnt state (require_int ~lcnt "type" ind_json) in
  let params, ty =
    parse_ind_param_shape ~lcnt (fun () -> LeanParseShared.pop_params nparams ty0)
  in
  let ctors =
    ctor_jsons
    |> List.map (parse_ctor_val ~lcnt state)
    |> List.map (fun (ctor_name, ctor_ty) ->
      (ctor_name, parse_ind_param_shape ~lcnt (fun () ->
        LeanParseShared.fix_ctor name nparams ctor_ty)))
  in
  let univs = level_params ~lcnt state ind_json in
  Entry (Ind { name; params; ty; ctors; univs })

let parse_inductive ~lcnt state payload =
  let types = require_list ~lcnt "types" payload in
  let ctors = require_list ~lcnt "ctors" payload in
  match types with
  | [ ind_json ] -> (state, Some (parse_ind_val ~lcnt state ind_json ctors))
  | _ -> err ~lcnt "mutual inductive groups are not supported by the current importer model"

let parse_meta ~lcnt state json =
  let meta = require_member ~lcnt "meta" json in
  let format = require_member ~lcnt "format" meta in
  let version = require_string ~lcnt "version" format in
  if version <> "3.1.0" then err ~lcnt ("unsupported export format " ^ version);
  ({ state with seen_meta = true }, None)

let parse_line ~prefix ~lcnt state l =
  let l = String.trim l in
  if l = "" then (state, None)
  else
    let json =
      try Json.from_string l
      with Yojson.Json_error msg -> err ~lcnt msg
    in
    let has k = member k json <> None in
    if has "meta" then parse_meta ~lcnt state json
    else if not state.seen_meta then
      err ~lcnt "expected metadata object before export records"
    else if has "str" || has "num" then parse_name ~lcnt state json
    else if has "succ" || has "max" || has "imax" || has "param" then
      parse_level ~lcnt state json
    else if has "ie" then parse_expr ~lcnt state json
    else
      (* Declaration records; skipped (without parsing) while scanning a prefix
         for the name/level/expr context that precedes the entry of interest. *)
      let declaration (k, parse) =
        match member k json with
        | Some payload ->
          Some (if prefix then (state, None) else parse ~lcnt state payload)
        | None -> None
      in
      match
        List.find_map declaration
          [ ("axiom", parse_axiom);
            ("def", parse_def);
            ("thm", parse_thm);
            ("opaque", parse_opaque);
            ("quot", parse_quot);
            ("inductive", parse_inductive) ]
      with
      | Some result -> result
      | None ->
        if prefix then (state, None) else err ~lcnt "unsupported NDJSON record"

let do_prefix_line ~lcnt state l =
  fst (parse_line ~prefix:true ~lcnt state l)

let do_line ~lcnt state l =
  parse_line ~prefix:false ~lcnt state l

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
