
module U : sig
  type t = Prop | Succ of t | Max of t * t | IMax of t * t | UNamed of LeanName.t
end

type binder_kind =
  | NotImplicit
  | Maximal
  | NonMaximal
  | Typeclass  (** WRT Coq, Typeclass is like Maximal. *)

type expr =
  | Bound of int
  | Sort of U.t
  | Const of LeanName.t * U.t list
  | App of expr * expr
  | Let of { name : LeanName.t; ty : expr; v : expr; rest : expr }
      (** Let: undocumented in export_format.md *)
  | Lam of binder_kind * LeanName.t * expr * expr
  | Pi of binder_kind * LeanName.t * expr * expr
  | Proj of LeanName.t * int * expr  (** Proj: name of ind, field, term *)
  | Nat of Z.t
  | String of string

type def = {
  name : LeanName.t;
  ty : expr;
  body : expr;
  univs : LeanName.t list;
  height : int option;
}
type ax = { name : LeanName.t; ty : expr; univs : LeanName.t list }

type ind = {
  name : LeanName.t;
  params : (binder_kind * LeanName.t * expr) list;
  ty : expr;
  ctors : (LeanName.t * expr) list;
  univs : LeanName.t list;
}

type notation_kind = Prefix | Infix | Postfix

type notation = {
  kind : notation_kind;
  head : LeanName.t;
  level : int;
  token : string;
}

type entry = Def of def | Ax of ax | Ind of ind | Quot of LeanName.t

type action = Entry of entry | Nota of notation
