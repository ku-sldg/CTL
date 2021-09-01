Require Import Tactics.General.
Require Import Tactics.Combinators.
Require Import Tactics.Gen.

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
  repeat_count progress gen_eq_something H
  then fun n => 
    (* It seem like there is sometimes an off by one error. S n is sometimes 
       one too many, and n is sometimes one too few. *)
    (* inductStep H; do_u (S n) intro_try_rew *)
    inductStep H; repeat intro_try_rew
  end.
  
Tactic Notation "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => induction hyp using c).


(* induct* variant does more work to clean up the context.
   
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
          try cuth IH by exact eq_refl
      end
    | especialize IH;
      ecut_eq_aux IH].

Ltac ecut_eq IH :=
  ecut_eq_aux IH;
  let t := type of IH in 
  assert_fails `has_evar t.

(* Ltac foo IH :=
  let ecut_eq_aux IH := first
    [ match type of IH with 
      | _ = _ -> _ =>
          try cuth IH by exact eq_refl
      end
    | especialize IH;
      ecut_eq_aux IH] in
  ecut_eq_aux IH;
  let t := type of IH in 
  assert_fails `has_evar t. *)

Ltac find_ecut_eqs :=
  repeat match goal with 
  | IH: context[_ = _ -> _] |- _ =>
      ecut_eq IH
  end.

Ltac _induct_star_by H inductStep :=
  repeat_count progress gen_eq_something H
  then fun n => 
    inductStep H; repeat intro_try_rew
  end;
  find_ecut_eqs;
  subst;
  repeat match goal with 
  | H: ?x = ?x |- _ => clear H
  end.

Tactic Notation "induct!" hyp(H) :=
  _induct_star_by H ltac:(fun hyp => induction hyp).

Tactic Notation "induct!" hyp(H) "using" uconstr(c) :=
  _induct_star_by H ltac:(fun hyp => induction hyp using c).

Ltac hyp_eq H H' :=
  match H with 
  | H' => idtac
  end.

Ltac revert_all_but H :=
  repeat match goal with 
  | H': _ |- _ =>
      ifnot `hyp_eq H H' then
      revert H'
  end.

Ltac revert_bl bl :=
  foreach_bl bl fun H => revert H.

(* Not working as expected *)
Ltac revert_all_but_do_intros H tac :=
  repeat_accum ([]: list Box) fun a cont =>
    match goal with 
    | H': _ |- _ =>
        ifnot `hyp_eq H H' then quote(
          revert H';
          cont (box H' :: a))
    end +
    (tac; revert_bl a).

Ltac _max_induction_by H inductStep :=
  move H at top;
  repeat_count `match goal with
  | H': _ |- _ =>
      ifnot `hyp_eq H H' then
      revert H'
  end then fun n =>
    inductStep H; do_u n intro
  end.

(* Ltac _max_induction_by H inductStep :=
  move H at top;
  revert_all_but_do_intros H ltac:(`inductStep H). *)

Tactic Notation "max" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => induction hyp).

Tactic Notation "max" "induction" hyp(H) "using" constr(c) :=
  _max_induction_by H ltac:(fun hyp => induction hyp using c).

(* Can't call this? *)
Tactic Notation "max" "dependent" "induction" hyp(H) :=
  _max_induction_by H ltac:(fun hyp => dependent induction hyp).

(* Why is this not parsing? *)
(* Tactic Notation "max" "dependent" "induction" hyp(H) "using" uconstr(c) :=
  _max_induction_by H ltac:(fun hyp => dependent induction hyp using c). *)

Tactic Notation "max" "induct" hyp(H) :=
  _induct_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct" hyp(H) "using" uconstr(c) :=
  _induct_by H ltac:(fun hyp => max induction hyp using c).

Tactic Notation "max" "induct*" hyp(H) :=
  _induct_star_by H ltac:(fun hyp => max induction hyp).

Tactic Notation "max" "induct*" hyp(H) "using" uconstr(c) :=
  _induct_star_by H ltac:(fun hyp => max induction hyp using c).


(* destruction / inversion *)

Tactic Notation "destruction" constr(H) :=
  _induct_by H ltac:(fun hyp => destruct H);
  subst.

Tactic Notation "destruction" constr(H) "eqn" ":" ident(I) :=
  _induct_by H ltac:(fun hyp => destruct H eqn:I);
  subst.

Ltac inv H :=
  let H' := fresh H in 
  copy H H';
  destruction H'.

Ltac invc H :=
  inv H;
  clear H.

(* Dependent inv
   Sometimes, inversion leaves behind equalities of existT terms. This tactic 
   uses dependent destruction to break these into further equalities.
   (Note, this leverages axioms about equality)
 *)

Ltac dep_destr_sigma :=
  repeat match goal with 
  | H: existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
  end.

Tactic Notation "dependent" "inv" hyp(H) :=
  inv H;
  dep_destr_sigma.

Tactic Notation "dependent" "invc" hyp(H) :=
  invc H;
  dep_destr_sigma.
