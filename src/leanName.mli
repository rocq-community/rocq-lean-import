open Names

type t = private string list

val anon : t
val of_list : string list -> t [@@warning "-32"]
val append : t -> string -> t
val append_list : t -> string list -> t
val unappend : t -> (t * string) option
val equal : t -> t -> bool

val raw_append : t -> string -> t
(** for private names *)

val to_coq_string : t -> string
val to_lean_string : t -> string
val to_id : t -> Id.t
val to_name : t -> Name.t
val pp : t -> Pp.t

module Set : CSet.S with type elt = t
module Map : CMap.ExtS with type key = t and module Set := Set
