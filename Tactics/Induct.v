Require Import Tactics.General.
Require Import Tactics.Combinators.
Require Import Tactics.Gen.

(* `Induct`: a modified induction strategy. Seeks to replicate the behavior 
   of `dependent induction` when it comes to conserving equalities, without
   pulling in equality axioms.

   induction tactics starting with "max" will set up a maximally
   generalized induction hypothesis
 *) 

Ltac gen_eq_something H :=
  repeat match type of H with
  | context[_ ?x] => 
      ifnot is_var x then
      gen eq ? := x in *
  end.

Ltac _induct_by H inductStep :=
  repeat_count progress gen_eq_something H
  then fun n => 
    inductStep H; do_u (S n) (intros [=<-] + intro)
  end;
  repeat match goal with
  | H: _ = _ -> _ |- _ => cuth H by easy
  end.
  
Tactic Notation "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp using c).

Ltac hyp_eq H H' :=
  match H with 
  | H' => idtac
  end.

Ltac revert_all_but H :=
  repeat match goal with 
  | H': _ |- _ =>
      ifnot delay hyp_eq H H' then
      revert H'
  end.

(* TODO, repeat_list (repeat_accum?) *)
Ltac _max_induction_by H inductStep :=
  move H at top;
  repeat_count delay match goal with
  | H': _ |- _ =>
      ifnot delay hyp_eq H H' then
      revert H'
  end then fun n =>
    inductStep H; do_u (S n) intro
  end.

Tactic Notation "max" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => induction H).

Tactic Notation "max" "induction" hyp(H) "using" constr(c) :=
  _max_induction_by H ltac:(fun hyp => induction H using c).

Tactic Notation "max" "dependent" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => dependent induction hyp).

(* Why is this not parsing? *)
(* Tactic Notation "max" "dependent" "induction" hyp(H) "using" uconstr(c) :=
  _max_induction_by H ltac:(fun hyp => dependent induction hyp using c). *)

Tactic Notation "max" "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => max induction hyp using c).
