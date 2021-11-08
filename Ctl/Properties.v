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

Theorem AW_seq_nQ : forall s P Q s' (seq: R#* s s'),
  AW_seq s P Q ->
  (forall x, in_seq x seq -> R @x ⊭ Q) ->
  forall x, in_seq x seq -> R @x ⊨ P.
Proof using.
  intros *.
  intros [Hs HAW] HnQ x Hin.
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
  - pose proof (ex_in_seq_at_lt_length R seq i) as Hin'.
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
      after apply H with (y := j).
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

(* Theorem seq__AW : forall s P Q,
  (R @s ⊨ P || Q /\
  forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P && !Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P || Q) ->
  R @s ⊨ A[P W Q]. *)

Theorem seq__AW : forall s P Q,
  R @s ⊨ P || Q ->
  (forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P && !Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P || Q) ->
  R @s ⊨ A[P W Q].
Proof using.
  tsimpl.
  intros * H IH *.
  destruct classic (exists i, R @(p i) ⊨ Q) as case.
  - right.
    destruct case as [i Hi].
    apply ex_first_sat_index in Hi as (j & Hj & Hj_before).
    exists j.
    split.
    + intros x x_in_before.
      destruct j as [|j']; [tedious|].
      destruct x_in_before as (k & klt & <-).
      wf_induction k lt.
      destruct k.
      * rewrite <- (state_at_0 _ _ p) in H.
        destruct H.
       -- assumption.
       -- contradict H.
          follows tapply Hj_before.
      * specialize (IH (p k) (prefix R p k)).
        forward IH.
       -- intros * Hin.
          apply inv_in_prefix in Hin as (xi & xilt & <-).
          constructor.
         ++ apply H0; lia.
         ++ apply Hj_before.
            exists xi.
            after split.
            lia.
       -- specialize (IH (p (S k))).
          forward IH by follows destruct p as (? & ? & ?).
          destruct IH.
         ++ assumption.
         ++ contradict H1.
            tapply Hj_before.
            tedious.
    + assumption.
  - left.
    positivity in case.
    intros ? [i <-].
    constructor.
    + destruct i.
      * rewrite state_at_0.
        after destruct H.
        follows contradict H.
      * specialize (IH (p i) (prefix R p i)).
        transform H (R @s ⊨ P). (* necessary? *)
        { destruct H. 
          - assumption.
          - contradict H.
            rewrite <- (state_at_0 _ _ p).
            apply case.
        }
        forward IH.
       -- intros * Hin.
          apply inv_in_prefix in Hin as (j & jlt & <-).
          induction i.
         ++ destruct j; [|lia]; clear jlt.
            constructor.
           ** follows rewrite state_at_0.
           ** follows tsimpl.
         ++ invc jlt.
           ** constructor; [|follows tsimpl].
              forward IH.
            --- intros * Hin.
                apply inv_in_prefix in Hin as (j & jlt & <-).
                constructor.
              +++ forward IH.
              +++ follows tsimpl.
            --- 
           ** 
 

          induction j.
         ++ clear jlt.
            subst.
            constructor.
           ** follows rewrite state_at_0.
           ** follows tsimpl.
         ++ 
       -- specialize (IH (p (S i))).
          forward IH by follows destruct p as (? & ? & ?).
          destruct or IH.
         ++ assumption.
         ++ follows contradict IH.
    + follows tsimpl.
Admitted.



Theorem seq__AW : forall s P Q,
  R @s ⊨ P || Q ->
  (forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P && !Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P || Q) ->
  R @s ⊨ A[P W Q].
Proof using.
  tsimpl.
  intros * H IH *.
  destruct classic (exists i, R @(p i) ⊨ Q) as case.
  - right.
    destruct case as [i Hi].
    apply ex_first_sat_index in Hi as (j & Hj & Hj_before).
    exists j.
    split.
    + (*  *)
      intros * x_in_before.
      admit.
    + assumption.
  - left.
    positivity in case.
    intros ? [i <-].
    constructor.
    + destruct i.
      * rewrite state_at_0.
        after destruct H.
        follows contradict H.
      * specialize (IH (p i) (nseq__seq R (prefix R p i))).
        forward IH.
       -- intros * Hin.
          transform H (R @s ⊨ P).
          { destruct H. 
            - assumption.
            - contradict H.
              rewrite <- (state_at_0 _ _ p).
              apply case.
          }
          transform Hin (in_nseq x (prefix R p i)) by admit.
          apply inv_in_prefix in Hin as [j <-].
          constructor.
         ++ 
            admit.
         ++ follows tsimpl.
       -- specialize (IH (p (S i))).
          forward IH by follows destruct p as (? & ? & ?).
          destruct or IH.
         ++ assumption.
         ++ follows contradict IH.
    + follows tsimpl.
Admitted.

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

Close Scope tprop_scope.
End Properties.