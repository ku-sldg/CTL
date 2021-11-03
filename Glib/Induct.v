Require Import GeneralTactics.
Require Import TacticCombinators.
Require Import Gen.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.
Import ListNotations.

(* `Induct`: a modified induction strategy. Seeks to replicate the behavior 
   of `dependent induction` when it comes to conserving equalities, without
   pulling in equality axioms.

   This pattern may be thought of as simultaneous inversion/induction

   induction tactics starting with "max" will set up a maximally
   generalized induction hypothesis
 *) 

Ltac gen_eq_something H :=
  repeat match type of H with
  | context[_ ?x] => 
      ifnot is_var x then
      (* Should this be `in H`?
         Perhaps in any situation where it would matter, we would 
         want it this general.
       *)
      gen eq ? := x in *
  end.

Ltac intro_try_rew :=
  intros [=<-] +
  intros [=->] +
  intros [=] +
  intro.

Ltac _induct_by H inductStep :=
  repeat progress gen_eq_something H;
  inductStep H;
  repeat intro_try_rew.
  
Tactic Notation "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct" hyp(H) "as" simple_intropattern(pat) :=
  _induct_by H ltac:(fun hyp => induction hyp as pat).

Tactic Notation "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp using c).

Tactic Notation "induct" hyp(H) "as" simple_intropattern(pat) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp as pat using c).


(* induct! variant does more work to clean up the context.
   
   In particular, regular induct can leaves behind silly hypotheses
   of the form
     H : forall x' ... z', x ... z = x' ... z' -> foo
   induct* will automatically instantiate and cut such hypotheses to
   reach the form
     H : foo
 *)

Ltac ecut_eq_aux IH :=
  first
    [ match type of IH with 
      | _ = _ -> _ =>
          try forward IH by exact eq_refl
      end
    | especialize IH;
      ecut_eq_aux IH].
    
Ltac has_no_evar t := assert_fails (has_evar t).

Ltac ecut_eq IH :=
  ecut_eq_aux IH;
  let t := type of IH in 
  `has_no_evar t.

Ltac find_ecut_eqs :=
  repeat match goal with 
  | IH: context[_ = _ -> _] |- _ =>
      ecut_eq IH
  end.

Ltac _induct_excl_by H inductStep :=
  _induct_by H inductStep;
  find_ecut_eqs;
  subst!.

Tactic Notation "induct!" hyp(H) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct!" hyp(H) "as" simple_intropattern(pat) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp as pat).

Tactic Notation "induct!" hyp(H) "using" uconstr(c) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp using c).

Tactic Notation "induct!" hyp(H) "as" simple_intropattern(pat) "using" uconstr(c) :=
  _induct_excl_by H ltac:(fun hyp => induction hyp as pat using c).


Ltac hyp_eq H H' :=
  match H with 
  | H' => idtac
  end.

Ltac revert_all_but H :=
  repeat find (fun H' =>
    assert_fails (`hyp_eq H H');
    revert H'
  ).

Ltac _max_induction_by H inductStep :=
  move H at top;
  revert_all_but H;
  inductStep H;
  intros.

Tactic Notation "max" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => induction hyp).

Tactic Notation "max" "induction" hyp(H) "as" simple_intropattern(pat) :=
  _max_induction_by H ltac:(fun hyp => induction hyp as pat).

Tactic Notation "max" "induction" hyp(H) "using" constr(c) :=
  _max_induction_by H ltac:(fun hyp => induction hyp using c).

Tactic Notation "max" "induction" hyp(H) "as" simple_intropattern(pat) "using" constr(c) :=
  _max_induction_by H ltac:(fun hyp => induction hyp as pat using c).

Tactic Notation "max" "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct" hyp(H) "as" simple_intropattern(pat) :=
  _induct_by H ltac:(fun hyp => max induction hyp as pat).

Tactic Notation "max" "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => max induction hyp using c).

Tactic Notation "max" "induct" hyp(H) "as" simple_intropattern(pat) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => max induction hyp as pat using c).

Tactic Notation "max" "induct!" hyp(H) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct!" hyp(H) "as" simple_intropattern(pat) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp as pat).

Tactic Notation "max" "induct!" hyp(H) "using" uconstr(c) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp using c).

Tactic Notation "max" "induct!" hyp(H) "as" simple_intropattern(pat) "using" uconstr(c) :=
  _induct_excl_by H ltac:(fun hyp => max induction hyp as pat using c).


(* destruction *)

Tactic Notation "destruction" constr(H) :=
  _induct_by H ltac:(fun hyp => destruct H);
  subst!.

Tactic Notation "destruction" constr(H) "as" simple_intropattern(pat) :=
  _induct_by H ltac:(fun hyp => destruct H as pat);
  subst!.

Tactic Notation "destruction" constr(H) "eqn" ":" ident(I) :=
  _induct_by H ltac:(fun hyp => destruct H eqn:I);
  subst!.

Tactic Notation "destruction" constr(H) "as" simple_intropattern(pat)
  "eqn" ":" ident(I) :=
  _induct_by H ltac:(fun hyp => destruct H as pat eqn:I);
  subst!.
