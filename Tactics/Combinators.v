(* Control flow tactics *)

Ltac not tac :=
  assert_fails tac.

Tactic Notation "ifnot" tactic(tCond) "then" tactic(tThen) :=
  not tCond;
  tThen.

Tactic Notation "if" tactic(tCond) "then" tactic(tThen) "else" tactic(tElse) :=
  tryif tCond then tThen else tElse.

Tactic Notation "if" tactic(tCond) "then" tactic(tThen) "else" tactic(tElse) "end" :=
  if tCond then tThen else tElse.

(* `repeat_count` behaves as `repeat`, but it counts the number of successful 
   invocations, and passes that value to its continuation.
 *)

Ltac repeat_count_then_aux tac cont n :=
  first [ tac; repeat_count_then_aux tac cont (S n)
        | cont n].

Tactic Notation "repeat_count" tactic(tac) "then" tactic(cont) := 
  repeat_count_then_aux tac cont 0.

Tactic Notation "repeat_count" tactic(tac) "then" tactic(cont) "end" := 
  repeat_count tac then cont.


(* This idiom was taken from Chargueraud TLC library.
   My understanding is that effectively obscures types.
   Since Ltac is dynamic, this is often ideal.
 *)
Inductive Box : Type :=
  | box : forall {A: Type}, A -> Box.


(* `do_u` is exactly the `do` tactic, but it avoids typing the 
   numeric argument using the "box" idiom
 *)

Ltac _do_u n tac :=
  match n with 
  | box (S ?n') => tac; _do_u (box n') tac
  | _ => idtac 
  end.

Tactic Notation "do_u" uconstr(n) tactic(tac) :=
  (* idtac "do_u"; *)
  _do_u (box n) tac.


(* Somehow inserting an idtac/semicolon delays execution *)
(* Ltac's execution semantics can be unclear. Sometimes, an ltac expression
   being passed to a higher-order combinator isn't delayed as expected.
   This `delay` tactic, although just the identity, seems to delay
   execution in such cases.
 *)
Tactic Notation "delay" tactic(tac) := idtac; tac.
Tactic Notation "delay" tactic(tac) "end" := delay tac.
