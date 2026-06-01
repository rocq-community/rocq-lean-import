open LeanExpr

module RRange : sig
  type +'a t
  (** Like Range.t, but instead of cons we append *)

  val empty : 'a t
  val length : 'a t -> int
  val append : 'a t -> 'a -> 'a t
  val get : 'a t -> int -> 'a
  val singleton : 'a -> 'a t
end

val pop_params : int -> expr -> (binder_kind * LeanName.t * expr) list * expr
val fix_ctor : LeanName.t -> int -> expr -> expr
val quot_name : LeanName.t
