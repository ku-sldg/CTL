Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Basic.
Require Import BinaryRelations.
Open Scope tprop_scope.

(* Require Import Coq.Program.Equality. *)
Require Import Ctl.Tactics.
Require Import Tactics.Tactics.
Require Import Classical.

Section Properties.

Context {state: Type}.
Variable R: relation state.
Context {t: transition R}.

(* Properties of implication *)

Theorem timpl_refl : forall (s: state) a,
  R @s ⊨ a ⟶ a.
Proof using.
  intros.
  tintro.
  assumption.
Qed.

Theorem timpl_trans : forall (s: state) a b c,
  R @s ⊨ (a ⟶ b) ⟶ (b ⟶ c) ⟶ a ⟶ c.
Proof using.
  intros s a b c.
  tintros Hab Hbc Ha.
  tapplyc Hbc.
  tapplyc Hab. 
  assumption.
Qed.

Theorem timpl_trans' : forall (s: state) a b c,
  R @s ⊨ a ⟶ b ->
  R @s ⊨ b ⟶ c -> 
  R @s ⊨ a ⟶ c.
Proof using.
  intros s a b c Hab Hbc.
  tintros Ha.
  tapplyc Hbc.
  tapplyc Hab. 
  assumption.
Qed.

Ltac treflexivity := simple apply timpl_refl.
Ltac treflexive := 
  match goal with 
  | |- _ @_ ⊨ ?a ⟶ ?a => treflexivity
  | |- _ @_ ⊨ ?a ⟶ ?b =>
      replace a with b;
        [ treflexivity
        | try easy; symmetry
        ]
  end.

Ltac ttransitivity x :=
  match goal with
  | |- ?R @?s ⊨ ?a ⟶ ?b =>
      simple apply (timpl_trans' R s a x b)
  end.

Ltac ettransitivity :=
  match goal with
  | |- ?R @?s ⊨ ?a ⟶ ?b =>
      simple eapply (timpl_trans' R s a _ b)
  end.

Theorem textensionality : forall s P Q,
  R @s ⊨ P ⟷ Q ->
  (R @s ⊨ P) = (R @s ⊨ Q).
Proof using.
  intros.
  extensionality.
  assumption.
Qed.

Lemma tNNPP : forall s P, 
(* TODO: fix precedence so parantheses not necessary *)
  R @s ⊨ (¬¬P) ⟶ P.
Proof using.
  intros *.
  tintro H.
  now apply NNPP.
Qed.

Lemma rew_tNNPP : forall s P, 
  (R @s ⊨ ¬¬P) = (R @s ⊨ P).
Proof using.
  intros *.
  extensionality.
  split.
  - tapply tNNPP.
  - intro.
    tintro contra.
    now tapply contra.
Qed.


(* Properties of CTL path-quantifying formulas *)

Theorem star__AG : forall s P,
  (forall s', R^* s s' -> R @s' ⊨ P) ->
  R @s ⊨ AG P.
Proof using.
  intros * H.
  tsimpl.
  intros * Hin.
  applyc H.
  enow eapply in_path__star.
Qed.

Theorem AG__star : forall s P,
  R @s ⊨ AG P ->
  forall s', R^* s s' -> R @s' ⊨ P.
Proof using.
  intros * H.
  intros s' Hstar.
  apply (star__in_path _ _ _ _ trans_serial) in Hstar.
  destruct exists Hstar p.
  enow etapply H.
Qed.

Theorem rew_AG_star : forall s P,
  R @s ⊨ AG P =
    forall s', R^* s s' -> R @s' ⊨ P.
Proof using.
  intros *.
  extensionality.
  split.
  - now apply AG__star.
  - apply star__AG.
Qed.

(* Lemma in_path_combine {state}: forall (R: relation state),
  forall s (p: path R s) s' (p': path R s') s'',
    in_path s' p ->
    in_path s'' p' ->
    in_path s'' p.
Proof using.
  intros * Hin Hin'.
  induct Hin.
  - 
  - apply in_tail.
    find eapplyc.
    find eapplyc. *)

(* TODO: demorgans tactic which uses an extensible hint database for rewriting? *)

Theorem AG_idempotent : forall s P,
  R @s ⊨ AG P ⟶ AG (AG P).
Proof using.
  intros *.
  tintro H.
  tsimpl.
  intros * Hin * Hin'.
  etapply H.
Admitted.


(* De Morgan's Laws *)

Theorem AF_EG : forall s P,
  R @s ⊨ AF (¬P) ⟶ ¬EG P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists Hcontra p.
  specialize (H p).
  destruct exists H s'.
  destruct H; auto.
Qed.

Theorem AF_EG' : forall s P,
  R @s ⊨ ¬AF P ⟶ EG (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  overwrite H (not_all_ex_not _ _ H); simpl in H.
  destruct exists H p.
  exists p.
  intros s' Hin contra.
  overwrite H (not_ex_all_not _ _ H); simpl in H.
  enow eapply H.
Qed.

Theorem EG_AF : forall s P,
  R @s ⊨ EG (¬P) ⟶ ¬AF P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists H p.
  specialize (Hcontra p).
  destruct exists Hcontra s'.
  destruct Hcontra.
  enow etapply H.
Qed.

Theorem EG_AF' : forall s P,
  R @s ⊨ ¬EG P ⟶ AF (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros p.
  overwrite H (not_ex_all_not _ _ H); simpl in H.
  specialize (H p).
  overwrite H (not_all_ex_not _ _ H); simpl in H.
  destruct exists H s'.
  exists s'.
  split.
  - enow eapply not_imply_elim.
  - enow eapply not_imply_elim2.
Qed.

Theorem rew_AF_EG : forall s P,
  (R @s ⊨ AF (¬P)) = (R @s ⊨ ¬EG P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply AF_EG.
  - tapply EG_AF'.
Qed.

Theorem rew_EG_AF : forall s P,
  (R @s ⊨ EG (¬P)) = (R @s ⊨ ¬AF P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply EG_AF.
  - tapply AF_EG'.
Qed.


Theorem AG_EF : forall s P,
  R @s ⊨ AG (¬P) ⟶ ¬EF P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists Hcontra p s'.
  specialize (H p s').
  now destruct H.
Qed.

Theorem AG_EF' : forall s P,
  R @s ⊨ ¬AG P ⟶ EF (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  overwrite H (not_all_ex_not _ _ H); simpl in H.
  destruct exists H p.
  overwrite H (not_all_ex_not _ _ H); simpl in H.
  destruct exists H s'.
  exists p s'.
  split.
  - enow eapply not_imply_elim.
  - enow eapply not_imply_elim2.
Qed.

Theorem EF_AG : forall s P,
  R @s ⊨ EF (¬P) ⟶ ¬AG P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists H p s'.
  specialize (Hcontra p s').
  destruct H as [H1 H2].
  enow etapply H2.
Qed.

Theorem EF_AG' : forall s P,
  R @s ⊨ ¬EF P ⟶ AG (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros p s' Hin contra.
  overwrite H (not_ex_all_not _ _ H); simpl in H.
  specialize (H p).
  overwrite H (not_ex_all_not _ _ H); simpl in H.
  enow eapply H.
Qed.

Theorem rew_AG_EF : forall s P,
  (R @s ⊨ AG (¬P)) = (R @s ⊨ ¬EF P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply AG_EF.
  - tapply EF_AG'.
Qed.

Theorem rew_EF_AG : forall s P,
  (R @s ⊨ EF (¬P)) = (R @s ⊨ ¬AG P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply EF_AG.
  - tapply AG_EF'.
Qed.


Theorem AX_EX : forall s P,
  R @s ⊨ AX (¬P) ⟶ ¬EX P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists Hcontra s'.
  specialize (H s').
  destruct Hcontra.
  now apply H.
Qed.

Theorem AX_EX' : forall s P,
  R @s ⊨ ¬AX P ⟶ EX (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  overwrite H (not_all_ex_not _ _ H); simpl in H.
  destruct exists H s'.
  exists s'.
  split.
  - enow eapply not_imply_elim.
  - enow eapply not_imply_elim2.
Qed.

Theorem EX_AX : forall s P,
  R @s ⊨ EX (¬P) ⟶ ¬AX P.
Proof using.
  intros *.
  tintros H Hcontra.
  tsimpl in *.
  destruct exists H s'.
  specialize (Hcontra s').
  destruct H as [H1 H2].
  enow etapply H2.
Qed.

Theorem EX_AX' : forall s P,
  R @s ⊨ ¬EX P ⟶ AX (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros s' Hin contra.
  overwrite H (not_ex_all_not _ _ H); simpl in H.
  specialize (H s').
  enow eapply H.
Qed.

Theorem rew_AX_EX : forall s P,
  (R @s ⊨ AX (¬P)) = (R @s ⊨ ¬EX P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply AX_EX.
  - tapply EX_AX'.
Qed.

Theorem rew_EX_AX : forall s P,
  (R @s ⊨ EX (¬P)) = (R @s ⊨ ¬AX P).
Proof using.
  intros.
  apply textensionality.
  split.
  - tapply EX_AX.
  - tapply AX_EX'.
Qed.


(* Expansion Laws *)

Theorem expand_AG : forall s P,
  R @s ⊨ AG P ⟶ P ∧ AX (AG P).
Proof.
  intros *.
  tintro H.
  rewrite rew_AG_star in H.
  split.
  - apply H.
    reflexivity.
  - unfold_AX.
    intros * Hstep.
    rewrite rew_AG_star.
    intros * Hstar.
    apply H.
    etransitivity; [|eassumption].
    econstructor.
    + eassumption.
    + constructor.
Qed.

Theorem unexpand_AG : forall s P,
  R @s ⊨ P ∧ AX (AG P) ⟶ AG P.
Proof.
  intros *.
  tintro H.
  destruct H as [H1 H2].
  unfold_AX in H2.
  rewrite rew_AG_star.
  intros * Hstar.
  apply star_rt1n in Hstar.
  inv Hstar.
  - assumption.
  - specialize (H2 y H).
    rewrite rew_AG_star in H2.
    apply H2.
    now apply rt1n_star.
Qed.

Theorem rew_expand_AG : forall s P,
  (R @s ⊨ AG P) = (R @s ⊨ P ∧ AX (AG P)).
Proof.
  intros *.
  apply textensionality.
  split.
  - tapply expand_AG.
  - tapply unexpand_AG.
Qed.

End Properties.
