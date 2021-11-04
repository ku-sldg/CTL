Require Import Coq.Lists.List.
Import ListNotations.


(* Control flow tactics

   These tactics are largely *experimental*.
*)

(* Ltac's execution semantics can be unclear. Sometimes, an ltac expression
   being passed to a higher-order combinator isn't delayed as expected.
   This `quote` tactic, although just the identity, seems to delay
   execution in such cases.
 *)
Tactic Notation "quote" tactic(tac) := tac.
Tactic Notation "`" tactic(tac) := tac.


Ltac true := idtac.
Ltac false := fail.

Tactic Notation "not" tactic3(tac) :=
  assert_fails tac.

Tactic Notation "both" tactic3(tac1) "and" tactic3(tac2) :=
  tac1; tac2.

Tactic Notation "either" tactic3(tac1) "or" tactic3(tac2) :=
  tac1 + tac2.

Tactic Notation "if" tactic3(tCond) "then" tactic3(tThen) "else" tactic3(tElse) :=
  tryif tCond then tThen else tElse.

Tactic Notation "while" tactic3(tCond) tactic3(tDo) :=
  repeat (tCond; tDo).


(* `repeat_count` behaves like `repeat`, but it counts the number of 
  iterations, which it passes to a continuation.
 *)

Ltac _repeat_count tac cont n :=
  if tac then 
    _repeat_count tac cont (S n)
  else 
    cont n.

Tactic Notation "repeat_count" tactic3(tac) "then" tactic3(cont) := 
  _repeat_count tac cont 0.


(* `do_upto` is a mix of repeat and do. It perform up to n repetitions. *)

Ltac _do_upto n tac :=
  try match n with 
  | S ?n' => tac; _do_upto n' tac
  | 0 => idtac 
  end.
Tactic Notation "do_upto" constr(n) tactic3(tac) :=
  _do_upto n tac.


Ltac foreach l tac :=
  match l with 
  | ?h :: ?t => tac h; foreach t tac
  | [] => idtac
  end.
Tactic Notation "foreach" constr(l) tactic3(tac) :=
  foreach l tac.
