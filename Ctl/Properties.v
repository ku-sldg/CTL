Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import BinaryRelations.

Require Import Coq.Init.Logic.
Import EqNotations.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Program.Equality.
Require Import Ctl.Tactics.
Require Import Tactics.General.

Lemma AG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ AG P -> R@s ⊨ AG (AG P).
Proof.
  intros R s P H.
  intros n p x Hin.
  intros n' p' x' Hin'.
  eapply in_path_combine in Hin'; [|eassumption].
  destruct exists Hin' n'' p''.
  eapply H.
  eassumption.
Qed.

Lemma EG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ EG P -> R@s ⊨ EG (EG P).
Proof.
  intros R s P H.
  intro n.
  copy H Hpath1.
  tspecialize Hpath1 n.
  destruct exists Hpath1 p.
  exists p.
  intros s' Hin.
  (* simpl in *. *)

  (* induction Hin; [assumption|assumption|]. *)
  (* intros n'. *)
Admitted.

(*
Theorem rtc_AG {state}: forall (R: relation state) s P, 
  (forall s', R^* s s' -> R@s' ⊨ P) ->
  R@s ⊨ AG P.
Proof.
  intros R s P H.
  intros n p s' Hin.
  apply H.
  eapply in_path_impl_rtc.
  eapply path_to_rtc.
  eassumption.
Qed. 

Theorem AG_rtc {state}: forall (R: relation state) s P, 
  R@s ⊨ AG P ->
  forall s', R^* s s' -> R@s' ⊨ P.
Proof.
  intros R s P H s' Hsteps.
  apply rtc_to_path in Hsteps.
  destruct exists Hsteps n p.
  apply H with (p:=p).
  assumption.
Qed.
*)

Theorem tModusPonens {state}: forall (M: relation state) s P Q,
  M@s ⊨ P --> Q -> M@s ⊨ P -> M@s ⊨ Q.
Proof. auto. Qed.

Theorem tModusPonens_flipped {state}: forall (M: relation state) s P Q,
  M@s ⊨ P -> M@s ⊨ P --> Q -> M@s ⊨ Q.
Proof. auto. Qed.

Theorem tModusTollens {state}: forall (R: relation state) s P Q,
  R@s ⊨ (P --> Q) --> ¬Q --> ¬P.
Proof.
  intros R s P Q.
  intros Hpq Hnq Hp.
  tapply Hnq.
  tapply Hpq.
  assumption.
Qed.

Theorem tbimpl_neg {state}: forall (R: relation state) s P Q,
  R@s ⊨ (P <--> Q) --> (¬P <--> ¬Q).
Proof.
  intros R s P Q.
  split; intro; (eapply (tModusTollens R); [apply H | assumption]).
  (* (etapply (tModusTollens R); [apply H | assumption]). *)
Qed.

(* Good test for tactics *)
Theorem TImpl_trans {state}: forall M (s: state) P Q R,
  M@s ⊨ (P --> Q) --> (Q --> R) --> P --> R.
Proof.
  (* backwards reasoning *)
  intros M s P Q R Hpq Hqr Hp.
  tapply Hqr.
  tapply Hpq.
  exact Hp.

  Restart.
  (* forward reasoning *)
  intros M s P Q R Hpq Hqr Hp.
  tspecialize Hpq Hp.
  tspecialize Hqr Hpq.
  exact Hqr.

  Restart.
  simpl. auto.
Qed.

(* This is an alternate means of defining TNot *)
Theorem tNot_def {state}: forall M (s: state) P, M@s ⊨ ¬P <--> (P --> ⊥).
Proof.
  intros M s P.
  split; intros H; auto.
Qed.

(*
Lemma AG_steps_strong {state}: forall (R: relation state) s s' P,
  R^* s s' -> R@s ⊨ AG P -> R@s' ⊨ AG P.
Proof.
  intros R s s' P Hsteps H.
  pose proof (AG_rtc _ _ _ H) as H0; clear H; rename H0 into H.
  apply rtc_AG.
  intros s'' Hsteps2.
  apply H.
  eapply rtc_trans; eassumption.
Qed.

Lemma AG_steps_weak {state}: forall (R: relation state) s s' P,
  R^* s s' -> R@s ⊨ AG P -> R@s' ⊨ P.
Proof.
  intros R s s' P Hsteps H.
  pose proof (AG_steps_strong _ _ _ _ Hsteps H) as Hstrong.
  apply Hstrong with (p:= path_trivial s').
  constructor.
Qed.
*)

Lemma path_step_rev_preserves_in {state}: 
  forall (R: relation state) s s' (r: R s s') n (p: path R n s') x,
    in_path x p ->
    in_path x (path_step_rev R n s s' r p).
Proof using.
  introv H.
  invc H.
  induction H0; simpl; repeat constructor.
  simpl in IHin_rtcT_idx.
  dependent induction IHin_rtcT_idx.
  assumption.
Qed.

(* TODO: add in type-specific UIPs *)
Ltac inv_rew H :=
  inversion H;
  inversion_sigma;
  subst;
  (* Look for equalities we can destruct into eq_refl *)
  repeat match goal with
  | H: ?x = ?x |- _ => destruct H
  end;
  (* Simplify rews *)
  (* repeat match goal with 
  | H: context[rew [_] eq_refl in ?x] |- _ => change (rew [_] eq_refl in x) with x in H
  | |- context[rew [_] eq_refl in ?x] => change (rew [_] eq_refl in x) with x
  end. *)
  repeat change (rew [_] eq_refl in ?x) with x in *.

Ltac inv_rewc H := inv_rew H; clear H.

Lemma rtcT_idx_path_step__rtcT_idx_path_step_rev {X}:
  forall (R: relation X) s x x' n,
    R x x' ->
    R^# n s x ->
    {s' &
      R s s' &
      R^# n s' x'}.
Proof using.
  introv Rxx' Rsx.
  revert x' Rxx'.
  induction Rsx; intros.
  - exists x'.
    + assumption. 
    + constructor.
  - applyc IHRsx in r.
    destruct exists r s'.
    exists s'.
    + assumption.
    + econstructor; eassumption.
Qed.

(* Expansion Laws *)
Theorem expand_AG {state}: forall (R: relation state) s P, R@s ⊨ AG P <--> P ∧ AX (AG P).
Proof.
  intros R s P.
  split; intro H.
  - split.
    + eapply H.
      repeat econstructor.
    + intros s' Hstep n p x Hin.
      etapply H.
      eapply (path_step_rev_preserves_in _ _ _ Hstep).
      eassumption.
  - destruct H as [H1 H2].
    intros n p s' Hin.
    destruct exists p s''.
    inv_rewc Hin.
    induction H3; try assumption.
    eapply rtcT_idx_path_step__rtcT_idx_path_step_rev in p;
      [|eassumption]; clear r.
    destruct exists p s'.
    etapply H2.
    + eassumption.
    + apply (in_path_last _ _ _ _ r).
Qed.

Theorem expand_EG {state}: forall (R: relation state) s P, R@s ⊨ EG P <--> P ∧ EX (EG P).
Admitted.

Theorem expand_AF {state}: forall (R: relation state) s P, R@s ⊨ AF P <--> P ∧ AX (AF P).
Admitted.

Theorem expand_EF {state}: forall (R: relation state) s P, R@s ⊨ EF P <--> P ∧ EX (EF P).
Admitted.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall R (s: state) P, R@s ⊨ AF (¬P) --> ¬EG P.
Proof.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H n.
  tspecialize H2 n.
  destruct exists H2 p.
  tspecialize H p.
  destruct exists H s'.
  tspecialize H2 s'.
  destruct H; auto.
Qed.

(* Needs classical axioms *)
(*
Theorem AF_EG' {state}: forall R (s: state) P, R@s ⊨ ¬AF P --> EG (¬P).
Proof.
  intros R s P H.
  intro n.
  induction n.
  - exists (path_trivial s).
    intros s' Hin H2.
    inv Hin.
    tapply H.
    exists 0.
    intro p.
    exists s'.
    split.
    + apply in_path_head.
    + assumption.
  - destruct exists IHn p.
    (* Could proceed from induction on p.
       But where to deduce extra step at the end of the path?
       Hypothetically, from H. But can that be done intuitionistically? *)
    simpl in H.
    (* Can't extract any information from H until I get to a "False" goal.
       But I can't move my goal forward until I provide a path.
       Giving an existential won't work, since the ultimate value would 
       presumably not be in the current scope. *)
Abort.
*)

Theorem EG_AF {state}: forall R (s: state) P, R@s ⊨ EG (¬P) --> ¬AF P.
Proof.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H2 n.
  tspecialize H n.
  destruct exists H p.
  tspecialize H2 p.
  destruct exists H2 s'.
  tspecialize H s'.
  destruct H2.
  apply H; assumption.
Qed.

Theorem AG_EF {state}: forall R (s: state) P, R@s ⊨ AG (¬P) --> ¬EF P.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H2 n p s'.
  tspecialize H n p s'.
  tapply H; destruct H2; assumption.
Qed.

Theorem EF_AG {state}: forall R (s: state) P, R@s ⊨ EF (¬P) --> ¬AG P.
Admitted.

Theorem AX_EX {state}: forall R (s: state) P, R@s ⊨ AX (¬P) --> ¬EX P.
Admitted.

Theorem EX_AX {state}: forall R (s: state) P, R@s ⊨ EX (¬P) --> ¬AX P.
Admitted.
