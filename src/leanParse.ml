open LeanExpr
module N = LeanName

module RRange : sig
  type +'a t
  (** Like Range.t, but instead of cons we append *)

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end = struct
  type 'a t = { data : 'a Range.t; len : int }

  let empty = { data = Range.empty; len = 0 }
  let length x = x.len
  let append { data; len } x = { data = Range.cons x data; len = len + 1 }

  let get { data; len } i =
    if i >= len then raise Not_found else Range.get data (len - i - 1)

  let singleton x = { data = Range.cons x Range.empty; len = 1 }
end

let do_bk = function
  | "#BD" -> NotImplicit
  | "#BI" -> Maximal
  | "#BS" -> NonMaximal
  | "#BC" -> Typeclass
  | bk ->
    CErrors.user_err
      Pp.(str "unknown binder kind " ++ str bk ++ str "." ++ fnl ())

let do_notation_kind = function
  | "#PREFIX" -> Prefix
  | "#INFIX" -> Infix
  | "#POSTFIX" -> Postfix
  | k -> assert false

type parsing_state = {
  names : N.t RRange.t;
  exprs : expr RRange.t;
  univs : U.t RRange.t;
}

let empty_state =
  {
    names = RRange.singleton N.anon;
    exprs = RRange.empty;
    univs = RRange.singleton U.Prop;
  }

let get_name state n =
  let n = int_of_string n in
  RRange.get state.names n

let get_expr state e =
  let e = int_of_string e in
  RRange.get state.exprs e

let rec do_ctors state nctors acc l =
  if nctors = 0 then (List.rev acc, l)
  else
    match l with
    | name :: ty :: rest ->
      let name = get_name state name
      and ty = get_expr state ty in
      do_ctors state (nctors - 1) ((name, ty) :: acc) rest
    | _ -> CErrors.user_err Pp.(str "Not enough constructors")

(** Replace [n] (meant to be an the inductive type appearing in the constructor
    type) by (Bound k). *)
let rec replace_ind ind k = function
  | Const (n', _) when N.equal ind n' -> Bound k
  | (Const _ | Bound _ | Sort _) as e -> e
  | App (a, b) -> App (replace_ind ind k a, replace_ind ind k b)
  | Let { name; ty; v; rest } ->
    Let
      {
        name;
        ty = replace_ind ind k ty;
        v = replace_ind ind k v;
        rest = replace_ind ind (k + 1) rest;
      }
  | Lam (bk, name, a, b) ->
    Lam (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)
  | Pi (bk, name, a, b) ->
    Pi (bk, name, replace_ind ind k a, replace_ind ind (k + 1) b)
  | Proj (n, field, c) -> Proj (n, field, replace_ind ind k c)
  | (Nat _ | String _) as x -> x

let rec pop_params npar ty =
  if npar = 0 then ([], ty)
  else
    match ty with
    | Pi (bk, name, a, b) ->
      let pars, ty = pop_params (npar - 1) b in
      ((bk, name, a) :: pars, ty)
    | _ -> assert false

let fix_ctor ind nparams ty =
  let _, ty = pop_params nparams ty in
  replace_ind ind nparams ty

let as_univ state s = RRange.get state.univs (int_of_string s)

let parse_hexa c =
  if 'A' <= c && c <= 'F' then int_of_char c - int_of_char 'A'
  else begin
    assert ('0' <= c && c <= '9');
    int_of_char c - int_of_char '0'
  end

let parse_char s =
  assert (String.length s = 2);
  Char.chr ((parse_hexa s.[0] * 16) + parse_hexa s.[1])

let quot_name = N.append N.anon "Quot"

let do_line ~lcnt state l =
  let line_msg name =
    Feedback.msg_info Pp.(str "line " ++ int lcnt ++ str ": " ++ N.pp name)
  in
  (* Lean printing strangeness: sometimes we get double spaces (typically with INFIX) *)
  match
    List.filter (fun s -> s <> "") (String.split_on_char ' ' (String.trim l))
  with
  | [] -> (state, None) (* empty line *)
  | "#DEF" :: name :: ty :: body :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and body = get_expr state body
    and univs = List.map (get_name state) univs in
    let def = { name; ty; body; univs; } in
    (state, Some (Entry (Def def)))
  | "#AX" :: name :: ty :: univs ->
    let name = get_name state name in
    line_msg name;
    let ty = get_expr state ty
    and univs = List.map (get_name state) univs in
    let ax = { name; ty; univs } in
    (state, Some (Entry (Ax ax)))
  | "#IND" :: nparams :: name :: ty :: nctors :: rest ->
    let name = get_name state name in
    line_msg name;
    let nparams = int_of_string nparams
    and ty = get_expr state ty
    and nctors = int_of_string nctors in
    let params, ty = pop_params nparams ty in
    let ctors, univs = do_ctors state nctors [] rest in
    let ctors =
      List.map (fun (nctor, ty) -> (nctor, fix_ctor name nparams ty)) ctors
    in
    let univs = List.map (get_name state) univs in
    let ind = { name; params; ty; ctors; univs } in
    (state, Some (Entry (Ind ind)))
  | [ "#QUOT" ] ->
    line_msg quot_name;
    (state, Some (Entry (Quot quot_name)))
  | (("#PREFIX" | "#INFIX" | "#POSTFIX") as kind) :: rest ->
    (match rest with
    | [ n; level; token ] ->
      let kind = do_notation_kind kind
      and n = get_name state n
      and level = int_of_string level in
      (state, Some (Nota { kind; head = n; level; token }))
    | _ ->
      CErrors.user_err
        Pp.(
          str "bad notation: " ++ prlist_with_sep (fun () -> str "; ") str rest))
  | next :: rest ->
    let next =
      try int_of_string next
      with Failure _ ->
        CErrors.user_err Pp.(str "Unknown start of line " ++ str next)
    in
    let state =
      match rest with
      | [ "#NS"; base; cons ] ->
        assert (next = RRange.length state.names);
        let base = get_name state base in
        let cons = N.append base cons in
        { state with names = RRange.append state.names cons }
      | [ "#NI"; base; cons ] ->
        assert (next = RRange.length state.names);
        (* NI: private name. cons is an int, base is expected to be _private :: stuff
           (true in lean stdlib, dunno elsewhere) *)
        let base = get_name state base in
        let n = N.raw_append base cons in
        { state with names = RRange.append state.names n }
      | [ "#US"; base ] ->
        assert (next = RRange.length state.univs);
        let base = as_univ state base in
        { state with univs = RRange.append state.univs (Succ base) }
      | [ "#UM"; a; b ] ->
        assert (next = RRange.length state.univs);
        let a = as_univ state a
        and b = as_univ state b in
        { state with univs = RRange.append state.univs (Max (a, b)) }
      | [ "#UIM"; a; b ] ->
        assert (next = RRange.length state.univs);
        let a = as_univ state a
        and b = as_univ state b in
        { state with univs = RRange.append state.univs (IMax (a, b)) }
      | [ "#UP"; n ] ->
        assert (next = RRange.length state.univs);
        let n = get_name state n in
        { state with univs = RRange.append state.univs (UNamed n) }
      | [ "#EV"; n ] ->
        assert (next = RRange.length state.exprs);
        let n = int_of_string n in
        { state with exprs = RRange.append state.exprs (Bound n) }
      | [ "#ES"; u ] ->
        assert (next = RRange.length state.exprs);
        let u = as_univ state u in
        { state with exprs = RRange.append state.exprs (Sort u) }
      | "#EC" :: n :: univs ->
        let n = get_name state n in
        assert (next = RRange.length state.exprs);
        let univs = List.map (as_univ state) univs in
        { state with exprs = RRange.append state.exprs (Const (n, univs)) }
      | [ "#EA"; a; b ] ->
        assert (next = RRange.length state.exprs);
        let a = get_expr state a
        and b = get_expr state b in
        { state with exprs = RRange.append state.exprs (App (a, b)) }
      | [ "#EZ"; n; ty; v; rest ] ->
        assert (next = RRange.length state.exprs);
        let n = get_name state n
        and ty = get_expr state ty
        and v = get_expr state v
        and rest = get_expr state rest in
        {
          state with
          exprs = RRange.append state.exprs (Let { name = n; ty; v; rest });
        }
      | [ "#EL"; bk; n; ty; body ] ->
        assert (next = RRange.length state.exprs);
        let bk = do_bk bk
        and n = get_name state n
        and ty = get_expr state ty
        and body = get_expr state body in
        { state with exprs = RRange.append state.exprs (Lam (bk, n, ty, body)) }
      | [ "#EP"; bk; n; ty; body ] ->
        assert (next = RRange.length state.exprs);
        let bk = do_bk bk
        and n = get_name state n
        and ty = get_expr state ty
        and body = get_expr state body in
        { state with exprs = RRange.append state.exprs (Pi (bk, n, ty, body)) }
      | [ "#EJ"; ind; field; term ] ->
        let ind = get_name state ind
        and field = int_of_string field
        and term = get_expr state term in
        {
          state with
          exprs = RRange.append state.exprs (Proj (ind, field, term));
        }
      | [ "#ELN"; n ] ->
        let n = Z.of_string n in
        { state with exprs = RRange.append state.exprs (Nat n) }
      | "#ELS" :: bytes ->
        let s = Seq.map parse_char (List.to_seq bytes) in
        let s = String.of_seq s in
        { state with exprs = RRange.append state.exprs (String s) }
      | _ ->
        CErrors.user_err
          Pp.(str "cannot understand " ++ str l ++ str "." ++ fnl ())
    in
    (state, None)

let pp_state state =
  let open Pp in
  str "- " ++ int (RRange.length state.univs) ++ str " universe expressions" ++ fnl () ++
  str "- " ++ int (RRange.length state.names) ++ str " names" ++ fnl () ++
  str "- " ++ int (RRange.length state.exprs) ++ str " expression nodes" ++ fnl ()
