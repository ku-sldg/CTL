Require Import Ctl.BinaryRelations.
Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Basic.
Require Import Ctl.Tactics.

Require Import Glib.Glib.
Require Import Lia.

Section Properties.
Open Scope tprop_scope.

Context {state: Type}.
Context (R: relation state).
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
  follows eapply in_path_star.
Qed.

Theorem AG__star : forall s P,
  R @s ⊨ AG P ->
  forall s', R^* s s' -> R @s' ⊨ P.
Proof using.
  intros * H * Hstar.
  inhabit star__seq in Hstar.
  pose (p := prepend R Hstar (serial_witness__path R trans_serial s')).
  unshelve etapply H.
  - exact p.
  - apply in_prepend_seq.
    constructor.
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

Theorem star__EF : forall s P,
  (exists s', R^* s s' /\ R @s' ⊨ P) ->
  R @s ⊨ EF P.
Proof using.
  intros * H.
  tsimpl.
  destruct H as (s' & Hstar & H).
  inhabit star__seq in Hstar.
  pose (p := prepend R Hstar (serial_witness__path R trans_serial s')).
  exists p s'.
  split.
  - follows apply in_prepend_seq.
  - assumption. 
Qed.

Theorem EF__star : forall s P,
  R @s ⊨ EF P ->
  exists s', R^* s s' /\ R @s' ⊨ P.
Proof using.
  intros * H.
  tsimpl in H.
  destruct H as (p & s' & Hin & H).
  exists s'.
  split.
  - follows eapply in_path_star.
  - assumption.
Qed.

Theorem rew_EF_star : forall s P,
  R @s ⊨ EF P =
    exists s', R^* s s' /\ R @s' ⊨ P.
Proof using.
  intros *.
  extensionality.
  split.
  - follows apply EF__star.
  - apply star__EF.
Qed.

Theorem AU_trivial : forall s P Q,
  R @s ⊨ Q ⟶ A[P U Q].
Proof using.
  intros *.
  tintro H.
  tsimpl.
  intros.
  exists 0.
  split.
  - intros * Hin_before.
    follows inv Hin_before.
  - follows rewrite state_at_0.
Qed.

(* Extract the first satisfactory state *)
Lemma first_state : forall s (p: path R s) P,
  (exists s', in_path s' p /\ R @s' ⊨ P) ->
  exists i, 
    (forall x, in_path_before x i p -> R @x ⊨ ¬P) /\
    R @(p i) ⊨ P.
Proof using.
  intros * (s' & [i <-] & H).
  (* transform H (exists j, j >= i /\ R @(p j) ⊨ P) by eauto. *)
  transform H (exists j, j <= i /\ R @(p j) ⊨ P) by eauto.
  induction i.
  - exists 0.
    split.
    + now intros * [].
    (* + assumption. *)
    + destruct H as (j & jlt & Hj).
      follows inv jlt.
  - destruct H as (j & jlt & Hj).
    destruct classic (j < S i) as case.
    + apply IHi.
      exists j.
      split.
      * lia.
      * assumption.
    + replace j with (S i) by lia.
      clear jlt case.
      exists (S i).
Admitted.

    
(* Lemma first_state : forall s (p: path R s) P,
  (exists s', in_path s' p /\ R @s' ⊨ P) ->
  exists s' i, 
    in_path_at s' i p /\ 
    (forall x, in_path_before x i p -> R @x ⊨ ¬P) /\
    R @s' ⊨ P.
Proof using.
  intros * H.
  destruct H as (s'' & Hin & H).
  induction Hin.
  - exists s 0.
    max split.
    + constructor.
    + intros * contra.
      now inv contra.
    + assumption.
  - forward IHHin by assumption.
    destruct IHHin as (s'0 & i & Hin' & IH1 & IH2).
    destruct classic (R @s ⊨ P) as case.
    + exists s 0.
      max split.
      * constructor.
      * intros * contra.
        now inv contra.
      * assumption.
    + exists s'0 (S i).
      max split.
      * now constructor.
      * intros * Hbefore.
        destruct Hbefore as (m & Hlt & Hin''). 
        destruct m.
       -- now inv Hin''.
       -- apply IH1.
          dependent invc Hin''.
          exists m.
          split.
         ++ lia.
         ++ assumption.
      * assumption.
Qed. *)

(* Theorem seq__AW : forall s P Q,
  (R @s ⊨ P ∨ Q ->
  forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P ∧ ¬Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P ∨ Q) ->
  R @s ⊨ A[P W Q].
Proof using.
  tsimpl.
  intros * H *.
  (* Proceed by classical destruction on whether there exists some 
     state sQ in p entailing Q.
   *)
  destruct classic (
    exists sQ, in_path sQ p /\ R @sQ ⊨ Q
  ) as case.
  - right.
    (* Need to strengthen case to the *first* such sQ *)
    apply first_state in case.
    destruct case as (sQ & i & Hin & Hbefore_entails & HsQ).
    exists sQ i.
    max split; try assumption.
    intros * Hbefore.

    (* Strategy: 
         get prefix sequence including state before sQ.
         reflect in_path_before to in_seq
         Induct over in_seq. apply to H to get P ∨ Q. 
         Show Q contradicts that sQ is first. Therefore, P
     *)
Admitted. *)


(* TODO: demorgans tactic which uses an extensible hint database for rewriting? *)

Theorem AG_idempotent : forall s P,
  R @s ⊨ AG P ⟶ AG (AG P).
Proof using.
  intros *.
  tintro H.
  tsimpl.
  intros * Hin * Hin'.
  pose proof (ex_in_path_composition _ _ _ _ _ _ Hin Hin') as [? ?].
  follows etapply H.
Qed.

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
  positivity in H.
  destruct exists H p.
  positivity in H.
  exists p.
  repeat intro.
  follows eapply H.
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
  follows etapply H.
Qed.

Theorem EG_AF' : forall s P,
  R @s ⊨ ¬EG P ⟶ AF (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros p.
  positivity in H.
  specialize (H p).
  positivity in H.
  destruct exists H s'.
  follows positivity in H.
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
  positivity in H.
  destruct exists H p.
  positivity in H.
  destruct exists H s'.
  exists p s'.
  follows positivity in H.
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
  follows etapply H2.
Qed.

Theorem EF_AG' : forall s P,
  R @s ⊨ ¬EF P ⟶ AG (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros p s' Hin contra.
  positivity in H.
  specialize (H p).
  positivity in H.
  follows eapply H.
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
  positivity in H.
  destruct exists H s'.
  exists s'.
  follows positivity in H.
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
  follows etapply H2.
Qed.

Theorem EX_AX' : forall s P,
  R @s ⊨ ¬EX P ⟶ AX (¬P).
Proof using.
  intros *.
  tintro H.
  tsimpl in *.
  intros s' Hin contra.
  positivity in H.
  specialize (H s').
  follows eapply H.
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

Theorem AG_AU_AW (s: state)(P Q: tprop state):
  tentails R s
            (timpl (tdisj (AG (tconj P (tnot Q))) (AU P Q)) (AW P Q)).
Proof.
  unfold_timpl.
  intros Hdisj.
  unfold_tdisj in Hdisj.
  inversion_clear Hdisj.
  { unfold_AW.
    intros p.
    left.
    unfold_AG in H.
    specialize (H p).
    trivial. }
  { unfold_AW.
    intros p.
    right.
    unfold_AU in H.
    specialize (H p).
    trivial. }
Qed.

Close Scope tprop_scope.
End Properties.
