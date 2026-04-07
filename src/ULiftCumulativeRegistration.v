(** Cumulative ULift definitions for instance 0 (both r, s non-SProp).

    When this module is [Require Import]ed before [Lean Import], Lean's [ULift]
    (at instance 0) is translated as a transparent definition leveraging
    cumulativity, rather than as an inductive type.  SProp instances (1-3)
    still fall through to normal inductive translation since Rocq does not
    have cumulativity between SProp and Set. *)

Set Universe Polymorphism.

Definition ULift_cumul@{r s|} (α : Type@{s}) : Type@{max(r,s)} := α.
Register ULift_cumul as lean.ULift.cumul.

Definition ULift_up_cumul@{r s|} {α : Type@{s}} (a : α) : ULift_cumul@{r s} α := a.
Register ULift_up_cumul as lean.ULift_up.cumul.

Definition ULift_down_cumul@{r s|} {α : Type@{s}} (a : ULift_cumul@{r s} α) : α := a.
Register ULift_down_cumul as lean.ULift_down.cumul.

Definition ULift_rec_cumul@{motive r s|} {α : Type@{s}} {P : ULift_cumul@{r s} α -> Type@{motive}}
  (mk : forall (down : α), P (ULift_up_cumul down))
  (t : ULift_cumul@{r s} α) : P t
  := mk t.
Register ULift_rec_cumul as lean.ULift_rec.cumul.

Definition ULift_ind_cumul@{r s|} {α : Type@{s}} {P : ULift_cumul@{r s} α -> SProp}
  (mk : forall (down : α), P (ULift_up_cumul down))
  (t : ULift_cumul@{r s} α) : P t
  := mk t.
Register ULift_ind_cumul as lean.ULift_rec.cumul.ind.
