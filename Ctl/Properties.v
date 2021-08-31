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
  Check (trans_serial R).
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


End Properties.
(* ------------------------ old stuff --------------------------- *)

Lemma AG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ AG P -> R@s ⊨ AG (AG P).
Proof.
  intros R s P H.
  rewrite rew_AG.
  intros n p x Hin.
  rewrite rew_AG.
  intros n' p' x' Hin'.
  eapply in_path_combine in Hin'; [|eassumption].
  destruct exists Hin' n'' p''.
  etapplyc H.
  eassumption.
Qed.

Lemma EG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ EG P -> R@s ⊨ EG (EG P).
Proof.
  intros R s P H.
  rewrite rew_EG.
  intro n.
  copy H Hpath1.
  specialize (Hpath1 n).
  destruct exists Hpath1 p.
  exists p.
  intros s' Hin.
  (* simpl in *. *)

  (* induction Hin; [assumption|assumption|]. *)
  (* intros n'. *)
Abort.

(* Expansion Laws *)
Theorem expand_AG {state}: forall (R: relation state) s P, R@s ⊨ AG P ⟷ P ∧ AX (AG P).
Proof.
  intros R s P.
  split; intro H.
  - split.
    + etapply H.
      repeat econstructor.
    + rewrite rew_AX.
      setoid_rewrite rew_AG.
      intros s' Hstep n p x Hin.
      etapply H.
      (* changes path type from `path R n s' to `path R (S n) s` *)
      eapply (path_step_rev_preserves_in _ _ _ Hstep).
      eassumption.
  - destruct H as [H1 H2].
    rewrite rew_AG.
    intros n p s' Hin.
    destruct exists p s''.
    dependent invc Hin.
    induction H; try assumption.
    eapply nseq_step__nseq_step_rev in p;
      [|eassumption]; clear r.
    destruct p as [s' Rss' Rs'x'].
    (* Note: unfold_AX in H2; unfold_AG in H2 doesn't seem to work here. Problem with binder? *)
    (* It works now, but only because I added manual rewrites *)
    etapplyc H2.
    + eassumption.
    + apply (in_path_last _ _ _ _ Rs'x').
Qed.

Theorem expand_EG {state}: forall (R: relation state) s P, R@s ⊨ EG P ⟷ P ∧ EX (EG P).
Admitted.

Theorem expand_AF {state}: forall (R: relation state) s P, R@s ⊨ AF P ⟷ P ∧ AX (AF P).
Admitted.

Theorem expand_EF {state}: forall (R: relation state) s P, R@s ⊨ EF P ⟷ P ∧ EX (EF P).
Admitted.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall R (s: state) P, R@s ⊨ AF (¬P) ⟶ ¬EG P.
Proof.
  intros.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H1 n.
  specialize (H2 n).
  destruct exists H2 p.
  specialize (H1 p).
  destruct exists H1 s'.
  specialize (H2 s').
  destruct H1; auto.
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

Theorem EG_AF {state}: forall R (s: state) P, R@s ⊨ EG (¬P) ⟶ ¬AF P.
Proof.
  intros R s P.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H2 n.
  specialize (H1 n).
  destruct exists H1 p.
  specialize (H2 p).
  destruct exists H2 s'.
  specialize (H1 s').
  destruct H2.
  apply H1; assumption.
Qed.

Theorem AG_EF {state}: forall R (s: state) P, R@s ⊨ AG (¬P) ⟶ ¬EF P.
  intros R s P.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H2 n p s'.
  specialize (H1 n p s').
  apply H1; destruct H2; assumption.
Qed.

Theorem EF_AG {state}: forall R (s: state) P, R@s ⊨ EF (¬P) ⟶ ¬AG P.
Admitted.

Theorem AX_EX {state}: forall R (s: state) P, R@s ⊨ AX (¬P) ⟶ ¬EX P.
Admitted.

Theorem EX_AX {state}: forall R (s: state) P, R@s ⊨ EX (¬P) ⟶ ¬AX P.
Admitted.

(* in_path_before operator well_founded? *)

(* How I want to prove R @s ⊨ A[P W Q]:
    - At first state, either P or Q
    - for some path from the start, we assume P has held.
      Now we prove that for some additional step, either P holds 
      or Q holds
 *)

Theorem AW_ind {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ∨ Q ->
  (forall s' (Rss': R#* s s'),
    (forall x, in_seq x Rss' -> R @x ⊨ P ∧ ¬ Q) ->
    forall s'', R s' s'' ->
    R @s'' ⊨ P ∨ Q) -> 
  R @s ⊨ A[P W Q].
Proof using.
  intros R s P Q Hinit Hstep.
  rewrite rew_AW.
  intros n p y i Hat Hbefore.
  let _temp := fresh in
    copy Hat _temp;
    apply in_path_at__get_prefix in _temp as [p' Hprefix].
  destruct exists p' x.
  induction p'.
  - apply in_path_at_first_inv in Hat; subst.
    assumption.
  - specialize (IHp' Hinit Hstep).
Abort. 

Theorem AW_ind {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ∨ Q ->
  (forall s' (Rss': R#* s s'),
    (forall x, in_seq x Rss' -> R @x ⊨ P ∧ ¬ Q) ->
    forall s'', R s' s'' ->
    R @s'' ⊨ P ∨ Q) -> 
  R @s ⊨ A[P W Q].
Proof using.
  intros R s P Q Hinit Hstep.
  rewrite rew_AW.
  intros n p y i Hin Hbefore.
  invc Hin.
  apply in_nseq_at__get_prefix in H.
  destruct exists H r'.
  induction r'.
  - assumption.
  - specialize (IHr' Hinit Hstep r).
    (* Here is the time for the classical reasoning.
       If R @y ⊨ P ∧ ¬ Q, then apply IHr'.
       else, goal is true by right.
     *)
    Require Import Classical.
    destruct classic Hclass: (R @y ⊨ P ∧ ¬ Q).
    + admit.
    + 
      clear - Hclass.
      (* apply tentails_tdisj_r. *)
      rewrite <- rew_tnot in Hclass.
      assert (tconj_demorgans:
        forall state (R: relation state) s (P Q: tprop state),
          R @s ⊨ ¬ (P ∧ Q) ⟷ ¬ P ∨ ¬ Q).
      { clear.
        intros.
        rewrite rew_tbiimpl.
        split; intro H.
        - rewrite rew_tdisj.
          repeat rewrite rew_tnot.
          apply not_and_or.
          setoid_rewrite <- rew_tconj.
          rewrite <- rew_tnot.
          assumption.
        - rewrite rew_tnot.
          rewrite rew_tconj.
          apply or_not_and.
          repeat rewrite <- rew_tnot.
          rewrite <- rew_tdisj.
          assumption.
      }
      applyc tconj_demorgans in Hclass.

(*
  induction H.
  - assumption.
  - specialize (Hstep x (nseq_to_seq p)).
    applyc Hstep; [|eassumption].
    intros x0 Hin.
    applyc Hbefore.
    econstructor.

    clear - Hin.
    (* Obvious from Hin *)
    todo.
  - apply IHin_nseq_at.
    intros x0 Hbefore2.
    applyc Hbefore.
    (* Obvious from Hbefore2 *)
    todo.
*)
Abort.

(* Theorem AU_from_AW {state}: forall (R: relation state) s P Q,
  R @s ⊨ A[P W Q] ∧ AF Q ->
  R @s ⊨ A[P U Q].
Proof using. *)

Lemma not_before_0 {state}: forall (R: relation state) n s (p: path R n s) x,
  ~ in_path_before x 0 p.
Proof using.
  intros.
  let H := fresh in 
    intro H; destruct H as [? [H _]]; inv H.
Qed. 

Definition seq_to_path {state} {R: relation state} {x y} (r: R#* x y): {n & path R n x}.
  apply seq_to_nseq in r.
  destruct exists r n.
  exists n.
  econstructor.
  eassumption.
Defined.

Lemma in_path_ind : forall (state: Type) (R: relation state) n x (p: path R n x),
  forall P: state -> Prop,
  P x ->
  (forall y z, R y z -> R#* x y -> P y -> P z) ->
  forall y, in_path y p -> P y.
Proof using.
  intros state R n x p P Hinit Hstep y Hin.
  construct in_path__get_prefix_seq in Hin.
  induction Hin.
  - assumption.
  - eapply Hstep; try eassumption.
    apply IHHin; assumption.
Qed.

Lemma in_path_ind' : forall (state: Type) (R: relation state) x,
  forall P: state -> forall n, path R n x -> Prop,
  P x 0 (nseq_to_path (nseq_refl R x)) ->
  (forall n y z (Ryz: R y z) (Rxy: R#n x y),
    P y n (nseq_to_path Rxy) ->
    P z (S n) (nseq_to_path (nseq_step R n x y z Ryz Rxy))) ->
  forall n (p: path R n x) y, in_path y p -> P y n p.
Proof using.
  intros state R x P Hinit Hstep n p y Hin.
  apply in_path__get_prefix in Hin.
  destruct exists Hin m p'.
  destruct p' as [x' r].
  induction r.
  - dependent destruction Hin. 
Abort.

(*
(* This is essentially well-founded induction *)
Lemma in_path_before_ind {state}: forall (R: relation state) n s (p: path R n s),
  forall P : state -> Prop,
  (forall i y,
    in_path_at y i p ->
    (forall x, in_path_before x i p -> P x) ->
    P y) ->
  forall s', in_path s' p -> P s'.
Proof using.
  intros R n s p P H s' Hin.
  eapply in_path_ind; [| |apply Hin].
  - eapply H.
    + apply in_path_at_first.
    + intros x Hbefore.
      contradict Hbefore.
      apply not_before_0.
  - intros y z Ryz Rsy Py.
    (* apply in_path__in_path_at in Hin.
    destruct Hin as [m [_ Hin]]. *)
    eapply H.
    + eassumption.

  induction Hin using in_path_ind.
  destruct Hin.
  apply in_nseq__in_nseq_at in H0.
  destruct H0 as [m [mLtn Hin]].

  induction Hin.
  - eapplyc H.
    + repeat constructor.
    + intros x Hbefore.
      contradict Hbefore.
      apply not_before_0.
  - eapplyc H.
    + repeat constructor.
    + intros x0 Hbefore.
      
      unfold nseq_to_path in Hbefore.
      simpl in Hbefore.

  apply in_path__in_path_at in Hin.
  destruct Hin as [? [_ Hin]].
  eapplyc H.
  - eassumption.
  - intros x0 Hbefore.
*)

(* Exposes the earliest witness of AF *)
Theorem AF_earliest {state}: forall (R: relation state) s P,
  R @s ⊨ AF P ->
  exists n, forall p: path R n s, exists y i,
    in_path_at y i p /\ R @y ⊨ P /\ 
    forall x, in_path_before x i p -> R @x ⊭ P.
Proof using.
  intros R s P H.
  tsimpl in H.
  destruct exists H n.
  exists n.
  intro p.
  specialize (H p).
  (* induct over in_path. At each step, use classical reasoning to 
     destruct cases of P is satisfied. If so, end early and prove ealiest.
     Else, continue.
   *)
  (* Actually, induct over in_path_before s' *)
  destruct H as [s' [Hin Hs']].
  invc Hin.
  induction H.
  - exists s 0.
    max split.
    + constructor.
    + assumption.
    + intros x Hbefore.
      contradict Hbefore.
      apply not_before_0.
  - exists x' n.
    admit.
  - specialize (IHin_nseq Hs').
Abort.

Theorem AW_AF__AU {state}: forall (R: relation state) s P Q,
  (* R @s ⊨ A[P W Q] ∧ AF Q ⟶ A[P U Q]. *)
  R @s ⊨ A[P W Q] ⟶ AF Q ⟶ A[P U Q].
Proof using.
  intros.
  (* tintro H.
  destruct H as [H1 H2]. *)
  tintros HAW HAF.
  (* tsimpl. *)
  rewrite rew_AU.
  rewrite rew_AF in HAF.
  destruct exists HAF n.
  exists n.
  intro p.
  specialize (HAF p).
  (* Problem: need to get *earliest* s' satisfying HAF *)
  destruct HAF as [s' [Hin Hs'Q]].
  exists s'.
  apply in_path__in_path_at in Hin.
  destruct Hin as [i [iLt Hin]].
  exists i.
  max split; try assumption.
  intros sP Hbefore.
  rewrite rew_AW in HAW.
  specialize (HAW n p s' i Hin).
  (* Might need to induct on Hbefore? *)
Abort.

Theorem EU_seq {state}: forall (R: relation state) s P Q,
  (exists s' n (r: R# n s s') s'', 
    R s' s'' /\
    R @s'' ⊨ Q /\ 
    forall x, in_nseq x r -> R @x ⊨ P)
  -> R @s ⊨ E[P U Q].
Proof using.
  intros.
  destruct exists H s' n r s''.
  destruct H as [H1 [H2 H3]].
  rewrite rew_EU.
  exists (S n).
  copy r r1.
  eapply nseq_step in r1; [|eassumption]; clear H1.
  exists (nseq_to_path r1) s'' n.
  max split.
  - (* in_nseq_at_last *)
    admit.
  - assumption.
  - 
Abort. 

Theorem EU_seq {state}: forall (R: relation state) s P Q,
  (exists s' (r: R#* s s') s'', 
    R s' s'' /\
    R @s'' ⊨ Q /\ 
    forall x, in_seq x r -> R @x ⊨ P)
  -> R @s ⊨ E[P U Q].
Proof using.
  intros.
  destruct exists H s' r s''.
  destruct H as [H1 [H2 H3]].
  rewrite rew_EU.
  (* apply seq_to_nseq in r. *)
Abort.
