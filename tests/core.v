From LeanImport Require Import Lean.

(* Set Lean Upfront Instantiation. *)
Redirect "core1.log" Lean Import "../dumps/core" 1 17012.

(* theorem usize_size_eq :
USize.size = 4294967296 ∨ USize.size = 18446744073709551616  is too slow *)
Redirect "core2.log" Fail Timeout 1 Lean Import "../dumps/core" 17012 17013.

Redirect "core3.log" Lean Import "../dumps/core" 17013 17035.

(* Error at line 12522 (for USize.toUInt64.proof_1): #DEF 1441 10569 10615
missing usize_size_eq *)
Redirect "core4.log" Fail Lean Import "../dumps/core" 17035 17036.

Redirect "core5.log" Lean Import "../dumps/core" 17036 17058.

(* Error at line 12532 (for USize.toUInt64): #DEF 1361 10616 10624
missing USize.toUInt64.proof_1 *)
Redirect "core6.log" Fail Lean Import "../dumps/core" 17058 17059.

Redirect "core7.log" Lean Import "../dumps/core" 17059 17267.

(* Error:
Error at line 14481 (for Quotient): #DEF 1613 12306 12311 3
missing Quot *)
Redirect "core8.log" Fail Lean Import "../dumps/core" 17267 81107.


(* Unset Lean Upfront Instantiation. *)
(* Redirect "core12.log" Lean Import "../dumps/core" 5464 5487. *)
(* Set Lean Upfront Instantiation. *)
(* Redirect "core13.log" Lean Import "../dumps/core" 5487 5584. *)

(* Redirect "core2.log" Fail Lean Import "../dumps/core" 5584 63566. *)

(* Print *)
(* Redirect "core3.log" Lean Import "../dumps/core" 5086 63566. *)
(*
Set Printing Universes.
Print String.
Print Char.
Print UInt32.
Eval hnf in LT_lt_inst1 Nat instLTNat.
Print Nat_le.
Print Or.
Print And.
Print Fin.
Print UInt32_isValidChar.
Print Nat_isValidChar.
Print UInt32_toNat.
Print LT_lt_inst1.
Print instLTNat.
Print LT_inst1. *)
(* Compute Z.of_nat (nat_of_Nat UInt32_size. *)
(* n < 0xd800 ∨ (0xdfff < n ∧ n < 0x110000) *)
(* Eval hnf in UInt32_isValidChar _. *)