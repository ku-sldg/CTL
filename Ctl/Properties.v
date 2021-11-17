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

Lemma ex_first_sat_index : forall s (p: path R s) P i,
  R @(p i) ⊨ P -> 
  exists j, 
    R @(p j) ⊨ P /\
    forall x, in_path_before x j p -> R @x ⊨ !P.
Proof using.
  intros * Hi.
  cut (forall j, 
    j <= i ->
    (forall x, in_path_before x (S j) p -> R @x ⊨ !P) \/
      exists k,
        k <= j /\
        R @(p k) ⊨ P /\
        (forall x, in_path_before x k p -> R @x ⊨ !P)
  ).
  - intro H.
    specialize (H i).
    forward H by tedious.
    destruct H.
    + contradict Hi.
      follows tapply H.
    + tedious.
  - intro j; induction j.
    + intros _.
      destruct classic (R @(p 0) ⊨ P) as case.
      * follows right.
      * left.
        intros ? (j & jlt & <-).
        after destruct j.
        follows inv jlt.
    + intros sjlt.
      forward IHj by lia.
      destruct IHj as [H|H].
      * destruct classic (R @(p (S j)) ⊨ P) as case.
       -- follows right.
       -- left.
          intros x (k & klt & pkx).
          transform klt (k = S j \/ k < S j) by lia.
          destruct klt; subst!.
         ++ assumption.
         ++ follows apply H.
      * right.
        destruct H as (k & ?).
        follows exists k.
Qed.

Corollary earliest_ex : forall s (p: path R s) P,
  (exists s', in_path s' p /\ R @s' ⊨ P) ->
  exists i, 
    (forall x, in_path_before x i p -> R @x ⊨ !P) /\
    R @(p i) ⊨ P.
Proof using.
  intros * (s' & [i <-] & H).
  follows apply ex_first_sat_index in H.
Qed.

Definition AW_seq s P Q :=
  R @s ⊨ P || Q /\ 
  forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P && !Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P || Q.

(* Should likely use `AW_in_before_nQ` instead *)
Theorem AW_seq_nQ : forall s P Q s' (seq: R#* s s'),
  AW_seq s P Q ->
  (forall x, in_seq x seq -> R @x ⊭ Q) ->
  forall x, in_seq x seq -> R @x ⊨ P.
Proof using.
  intros * [Hs HAW] HnQ x Hin.
  transform Hs (R @s ⊨ P).
  { after destruct or Hs.
    contradict Hs.
    apply HnQ.
    apply in_seq_first.
  }
  apply in_seq__in_seq_at in Hin as [i Hin].
  revert x Hin;
    wf_induction i lt;
    intros x Hin.
  destruct i.
  - follows apply inv_in_seq_at_0 in Hin as ->.
  - pose proof (ex_in_seq_at_le_length R seq i) as Hin'.
    forward Hin'.
    { after transitivity (S i).
      follows eapply in_seq_at_length.
    }
    destruct exists Hin' w.
    pose proof (in_seq_at_succ_related R seq) as HR.
    do 3 especialize HR;
      specialize (HR Hin' Hin).
    epose proof (ex_seq_at_prefix R seq i Hin') as prefix.
    destruct prefix as (prefix & prefix_length & Hprefix).
    specialize (HAW w prefix).
    forward HAW.
    { intros * Hin_prefix.
      apply in_seq__in_seq_at in Hin_prefix as [j Hin_prefix].
      assert (R @x0 ⊭ Q).
      { apply HnQ.
        follows eapply in_seq_at__in_seq.
      }
      constructor; [|follows tsimpl].
      after apply wfIH with (y := j).
      apply in_seq_at_length in Hin_prefix.
      lia.
    }
    specialize (HAW x HR).
    after destruct or HAW.
    contradict HAW.
    apply HnQ.
    follows eapply in_seq_at__in_seq.
Qed.
(* Print Assumptions AW_seq_nQ. *)

Theorem AW_in_before_nQ : forall s P Q (p: path R s) i,
  AW_seq s P Q ->
  (forall x, in_path_before x i p -> R @x ⊭ Q) ->
  forall x, in_path_before x i p -> R @x ⊨ P.
Proof using.
  intros * [Hs HAW] HnQ x Hin.
  transform Hs (R @s ⊨ P).
  { after destruct or Hs.
    contradict Hs.
    apply HnQ.
    exists 0.
    split.
    - destruct i.
      + exfalso. inv Hin; lia.
      + lia.
    - apply state_at_0.
  }
  revert x Hin;
    wf_induction i lt;
    intros x Hin.
  destruct i.
  - exfalso. inv Hin; lia.
  - destruct Hin as (j & jlt & <-).
    destruct j; [follows rewrite state_at_0|].
    specialize (HAW (p j) (prefix R p j)).
    forward HAW.
    + intros * Hin.
      apply inv_in_prefix in Hin.
      constructor.
      * after apply (wfIH (S j)).
        intros.
        apply HnQ.
        follows eapply in_path_before_grow.
      * tsimpl.
        apply HnQ.
        follows eapply in_path_before_grow.
    + specialize (HAW (p (S j))).
      forward HAW by follows repeat destructr p.
      after destruct or HAW.
      contradict HAW.
      follows apply HnQ.
Qed.

Theorem AW_intro : forall s P Q,
  AW_seq s P Q ->
  R @s ⊨ A[P W Q].
Proof using.
  unfold AW_seq.
  tsimpl.
  intros * [H IH] *.
  destruct classic (exists i, R @(p i) ⊨ Q) as case.
  - right.
    destruct case as [i Hi].
    apply ex_first_sat_index in Hi;
      clear i;
      destruct Hi as (i & Hi & Hi_before).
    exists i.
    after split.
    after eapply AW_in_before_nQ.
    intros.
    follows tapply Hi_before.
  - left.
    positivity in case.
    intros ? [i <-].
    constructor; [|follows tsimpl].
    gen x := (p i) to (λ x, in_path_before x (S i) p)
      by tedious;
      cbn beta;
      revert x.
    follows eapply AW_in_before_nQ.
Qed.

(* Prove AW by info of just the previous step *)
Theorem AW_intro_weak : forall s P Q,
  R @s ⊨ P || Q ->
  (forall s',
    R^* s s' ->
    (R @s' ⊨ P && !Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P || Q) ->
  R @s ⊨ A[P W Q].
Proof using.
  intros * H0 HS.
  apply AW_intro.
  split; [assumption|].
  intros * H.
  apply HS.
  - follows apply seq__star.
  - follows apply H.
Qed.
 
Theorem AW_elim : forall s P Q,
  R @s ⊨ A[P W Q] ->
  forall (p: path R s) i,
    (forall x, in_path_before x i p -> R @x ⊭ Q) ->
    forall x, in_path_before x i p -> R @x ⊨ P.
Proof using.
  intros * HAW * H * Hin.
  tsimpl in HAW.
  specialize (HAW p).
  destruct or HAW.
  - specialize (HAW x).
    forward HAW by tedious.
    follows destruct HAW.
  - destruct HAW as (j & Hbefore & HQ).
    assert (i <= j).
    + contradict goal.
      transform contra (j < i) by lia.
      contradict HQ.
      follows apply H.
    + apply Hbefore.
      follows eapply in_path_before_grow.
Qed.

Theorem AU_is_AW_and_AF : forall s P Q,
  (R @s ⊨ A[P U Q]) = (R @s ⊨ A[P W Q] && AF Q).
Proof using.
  intros *.
  extensionality H.
  - split.
    + follows tsimpl in *.
    + tsimpl in *.
      intro p.
      follows specialize (H p).
  - destruct H as [H H'].
    tsimpl in *.
    intro p.
    specialize (H p);
      specialize (H' p).
    destruct H; [|assumption].
    exfalso.
    destruct H' as (s' & s'_in & H').
    specialize (H s' s'_in).
    tedious.
Qed.

Theorem tprop_extensionality : forall P Q,
  (forall (R: relation state) (t: transition R) s, R @s ⊨ P = R @s ⊨ Q) ->
  (P = Q).
Proof using.
  intros * ext_eq.
  extensionality R' t' s.
  change (?tp R' t' s) with (R' @s ⊨ tp).
  tedious.
Qed.

Theorem tentails_eq_is_eq : forall P Q,
  (forall (R: relation state) (t: transition R) s, R @s ⊨ P = R @s ⊨ Q) =
  (P = Q).
Proof using.
  intros *.
  extensionality; split.
  - apply tprop_extensionality.
  - follows intros ->.
Qed.


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

Theorem AG_weaken : forall s P Q,
  (forall x, R @x ⊨ P --> Q) ->
  R @s ⊨ AG P --> AG Q.
Proof using.
  intros * HWeakenAt.
  tintro HAGP.
  rewrite rew_AG_star in *.
  intros * Hstep.
  follows tapply HWeakenAt.
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
