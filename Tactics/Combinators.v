Require Import Coq.Lists.List.
Import ListNotations.

(* Set Ltac Backtrace. *)

(* Control flow tactics *)

(* Ltac's execution semantics can be unclear. Sometimes, an ltac expression
   being passed to a higher-order combinator isn't delayed as expected.
   This `quote` tactic, although just the identity, seems to delay
   execution in such cases.
 *)
Tactic Notation "quote" tactic(tac) := tac.
(* Tactic Notation "'" tactic(tac) := tac. *)
(* In Lisp, "'" is used, but this conflicts visually with the common 
   pattern of including the quote in derived names
 *)
Tactic Notation "`" tactic(tac) := tac.

Ltac not tac :=
  assert_fails tac.

(* Note, on tactics such as this where it ends with a parsed tactic,
   the parsing will extend passed semicolons. I.e.

   `ifnot foo then a; b` is equivalent to 
   `ifnot foo then (a; b)`, not 
   `(ifnot foo then a); b)`.
 *)
Tactic Notation "ifnot" tactic(tCond) "then" tactic(tThen) :=
  not tCond;
  tThen.
(* Tactic Notation "ifnot" tactic(tCond) "then" tactic(tThen) :=
  first [tCond|tThen]. *)

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


(* This idiom was taken from Chargueraud's TLC library.
   My understanding is that it effectively obscures types.
   Since Ltac is dynamic, this is often ideal.
 *)
Inductive Box : Type :=
  | box : forall {A: Type}, A -> Box.

Ltac unbox b :=
  match b with 
  | box ?x => x
end.

Ltac boxcons h t :=
  let t' := unbox h in
  constr:(box (h :: t')).


(* `do_u` is exactly the `do` tactic, but it avoids typing the 
   numeric argument using the "box" idiom
 *)

Ltac _do_u n tac :=
  match n with 
  | box (S ?n') => tac; _do_u (box n') tac
  | box 0 => idtac 
  | _ => fail "Argument to _do_u is not a boxed natural"
  end.

Tactic Notation "do_u" uconstr(n) tactic(tac) :=
  _do_u (box n) tac.


(* `do_upto` is a mix of repeat and do. It perform up to n repetitions. *)

Ltac _do_upto n tac :=
  try match n with 
  | box (S ?n') => tac; _do_upto (box n') tac
  | box 0 => idtac 
  end.

Tactic Notation "do_upto" uconstr(n) tactic(tac) :=
  _do_upto (box n) tac.

(* Might be though of as a scan *)
(* repeat_accum : A -> (A -> (A -> ltac) -> ltac) -> ltac *)
Ltac repeat_accum a tac :=
  let cont := fun a => repeat_accum a tac in 
  try tac a cont.

Tactic Notation "repeat_accum" constr(a) tactic(tac) :=
  repeat_accum a tac.

Tactic Notation "repeat_accum" constr(a) tactic(tac) "end" :=
  repeat_accum a tac.

Ltac foreach l tac :=
  match l with 
  | ?h :: ?t => tac h; foreach t tac
  | [] => idtac
  end.
Tactic Notation "foreach" constr(l) tactic(tac) :=
  foreach l tac.

Ltac foreach_bl l tac :=
  match l with 
  | box ?h :: ?t => tac h; foreach_bl t tac
  | [] => idtac
  end.
Tactic Notation "foreach_bl" constr(l) tactic(tac) :=
  foreach_bl l tac.

Tactic Notation "while" tactic(tCond) tactic(tDo) :=
  repeat (tCond; tDo).

Ltac true := idtac.
Ltac false := fail.
