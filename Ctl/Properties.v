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
  apply (star__in_path _ _ _ trans_serial) in Hstar.
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

Theorem star__EF : forall s P,
  (exists s', R^* s s' /\ R @s' ⊨ P) ->
  R @s ⊨ EF P.
Proof using.
  intros * H.
  tsimpl.
  destruct H as (s' & Hstar & H).
  apply (star__in_path _ _ _ trans_serial) in Hstar.
  destruct exists Hstar p.
  now exists p s'.
Qed.

Theorem EF__star : forall s P,
  R @s ⊨ EF P ->
  exists s', R^* s s' /\ R @s' ⊨ P.
Proof using.
  intros * H.
  tsimpl in *.
  destruct H as (p & s' & Hin & H).
  exists s'.
  split.
  - enow eapply in_path__star.
  - assumption.
Qed.

Theorem rew_EF_star : forall s P,
  R @s ⊨ EF P =
    exists s', R^* s s' /\ R @s' ⊨ P.
Proof using.
  intros *.
  extensionality.
  split.
  - now apply EF__star.
  - apply star__EF.
Qed.

Theorem AU_trivial : forall s P Q,
  R @s ⊨ Q ⟶ A[P U Q].
Proof using.
  intros *.
  tintro H.
  tsimpl.
  intros.
  exists s 0.
  split; [|split].
  - destruct p. constructor.
  - intros * Hin_before.
    now inv Hin_before.
  - assumption.
Qed.

(* Extract the first satisfactory state *)
Lemma first_state : forall s (p: path R s) P,
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
Qed.

Theorem seq__AW : forall s P Q,
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

    copy Hin _temp;
      apply in_path_at__seq'' in _temp as [seq Hbefore_seq].
 
    destruct seq as [|s sQ' sQ].
    { exfalso; clear - Hbefore_seq Hbefore.
      destruct (path_at R p 1) as [y Hat].
      specialize (Hbefore_seq y 1).
      forward Hbefore_seq.
      - contradict goal.
        transform contra (i = 0) by lia.
        now inv Hbefore.
      - rewrite Hbefore_seq in Hat.
        dependent invc Hat.
        discriminate H2.
    }

    assert (Hbefore': in_seq sP seq) by todo.

    (* Inconvenient induction principle. Should start from the beginning *)
    (* induction Hbefore'. *)
    todo.
  - overwrite case (not_ex_all_not _ _ case); simpl in case.
    transform case (forall s', in_path s' p -> R @s' ⊨ ¬Q).
    { clear - case.
      intros s' Hin.
      specialize (case s').
      apply not_and_or in case.
      now destruct case.
    }
    left.
    intros * Hin.
    induction Hin.
    + specialize (case s).
      forward case by constructor.
      split; [|assumption].
      (* specialize (H s (seq_refl R s)).
      forward H.
      * intros * contra.
        dependent invc contra. *)
Admitted.

(*
Theorem seq__AW : forall s P Q,
  (forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P ∧ ¬Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P ∨ Q) ->
  R @s ⊨ A[P W Q].
Proof using.
  intros * H.
  tsimpl.
  unfold_tdisj.
  (* Wait, is this correct? What if it's AG on some paths, and AU on 
     others? I think I may need to redefine.
   *)
  intros *.


Theorem AW__seq : forall s P Q,
  R @s ⊨ A[P W Q] ->
  forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P ∧ ¬Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P ∨ Q.
Proof using.
  intros * H * H' * Hstep.
  tsimpl in H.
  destruct or H.
  - apply tentails_tdisj_l.
    rewrite rew_AG_star in H.
    applyc H.
    transitivity s'.
    + now apply seq__star.
    + now apply star_lift.
  - tsimpl in H.
    pose proof (prefix := seq_prefix _ _ _ trans_serial
      (seq_step R s s' s'' Hstep seq)).
    destruct exists prefix p.
    specialize (H p).
    destruct H as (sQ & i & Hin_at & Hin_before & H).
    destruct classic (in_path_before s'' i p) as Hbefore.
    + apply tentails_tdisj_l.
      now apply Hin_before.
    + clear Hin_before.
      (* s'' is in p (by prefix), but not before i.
         Therefore, it must be after i.
         This means i/sP is before s''. 
         Which means i/sP is in the prefix.
         It is therefore either in `seq`, in which case we get the contradiction 
         `R @sQ ⊨ ¬Q` from H', or sQ = s'', in which case
         solve goal by right.
       *)
      pose proof (in_prefix _ _ _ _ _ s'' prefix) as Hin.
      forward Hin by constructor.
      todo.
      (* contradict H.
      specialize (H' sQ).
      applyc H'. *)
Admitted.
*) 

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

Close Scope tprop_scope.
End Properties.