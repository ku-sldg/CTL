Require Import SepLogic.Definition.
Require Import SepLogic.Separation.
Require Import SepLogic.Equality.

Require Import GeneralTactics.
Require Import Coq.Program.Equality.

Reserved Notation "x ⊢ y" (at level 70).
Inductive sentails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | sentails_refl : forall x,
      x ⊢ x
  | seq_entails : forall x x' y y',
      x ≅ x' ->
      y ≅ y' ->
      x ⊢ y ->
      x' ⊢ y'
  | sep_con_intro : forall x x' y y',
      x ⊢ x' ->
      y ⊢ y' ->
      separate x y ->
      x ** y ⊢ x' ** y'
  where "x ⊢ y" := (sentails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70).

Theorem seq_is_semantic_equivalence {comp loc}: forall x y: sprop comp loc,
  x ≅ y -> 
  x ⊢ y /\ y ⊢ x.
Proof.
  intros x y Hseq.
  split.
  - eapply seq_entails. 
    + apply seq_refl.
    + eassumption.
    + apply sentails_refl.
  - eapply seq_entails.
    + apply seq_refl.
    + apply seq_sym.
      eassumption.
    + apply sentails_refl.
Qed.

Theorem sentails_trans {comp loc}: forall x y z: sprop comp loc,
  x ⊢ y ->
  y ⊢ z -> 
  x ⊢ z.
Proof using.
  intros x y z Hxy Hyz.
  dependent induction Hyz.
  - assumption.
  - eapply seq_entails.
    + apply seq_refl.
    + eassumption.
    + applyc IHHyz.
      eapply seq_entails.
      * apply seq_refl.
      * apply seq_sym.
        eassumption.
      * assumption.
  - clear IHHyz1 IHHyz2.
    (*
    pose proof Hxy as foo;
      apply only_sep_con_entails_sep_con in foo;
      destruct exists foo a b;
      subst.
    invc Hxy.
    + apply sep_con_intro; assumption.
    + eapply seq_entails.
      * eassumption.
      * apply seq_refl.
      * clear H0. *)
(* Seems like we need inductive hypothesis *)
(* Need a better way to induct over seq/sentails *)
Admitted.    

Theorem separation_preserved_entailment {comp loc}: forall x y: sprop comp loc,
  x ⊢ y ->
  forall z, separate x z <-> separate y z.
Proof using.
  intros x y H z.
  split; intro Hsep.
  (* - invc H. *)
  - intro Hcontra.
    applyc Hsep.
    induction H.
    + assumption.
    + admit.
    + invc Hcontra.
      * constructor. destruct or H5; auto.
      * destruct or H2.
       -- invc H2.
        ++ destruct or H6.
          ** apply overlap_sep_con_left. left.
             apply IHsentails1.
             constructor; auto.
          ** apply overlap_sep_con_left. right.
             apply IHsentails2.
             constructor; auto.
        ++ 
Admitted.

Lemma flip_sentails_trans {comp loc}: forall (x y z: sprop comp loc),
  y ⊢ z ->
  x ⊢ y ->
  x ⊢ z.
Proof.
  intros.
  eapply sentails_trans; eassumption.
Qed.

(* Tactics *)

Ltac seq_entails_from uc :=
  eapply seq_entails; [idtac|idtac|apply uc];
  try match goal with
  | |- ?x ≅ ?x => simple apply seq_refl
  end.

Lemma backwards_normalize_left {comp loc}: forall (a b c z: sprop comp loc),
  a ** b ** c ⊢ z -> (a ** b) ** c ⊢ z.
Proof.
  intros.
  seq_entails_from H.
  apply sep_con_eq_assoc_r.
  apply seq_refl.
Qed.

Lemma backwards_normalize_right {comp loc}: forall (a b c z: sprop comp loc),
  z ⊢ a ** b ** c -> z ⊢ (a ** b) ** c.
Proof.
  intros.
  seq_entails_from H.
  apply sep_con_eq_assoc_r.
  apply seq_refl.
Qed.

Lemma forwards_normalize_left {comp loc}: forall (a b c z: sprop comp loc),
  (a ** b) ** c ⊢ z -> a ** b ** c ⊢ z.
Proof.
  intros.
  seq_entails_from H.
  apply sep_con_eq_assoc_l.
  apply seq_refl.
Qed.

Lemma forwards_normalize_right {comp loc}: forall (a b c z: sprop comp loc),
  z ⊢ (a ** b) ** c -> z ⊢ a ** b ** c.
Proof.
  intros.
  seq_entails_from H.
  apply sep_con_eq_assoc_l.
  apply seq_refl.
Qed.

Tactic Notation "normalize_sprop" :=
  repeat match goal with 
  | [_:_ |- (_ ** _) ** _ ⊢ _] => 
      simple apply backwards_normalize_left
  | [_:_ |- _ ⊢ (_ ** _) ** _] =>
      simple apply backwards_normalize_right
  end.

Tactic Notation "normalize_sprop" "in" hyp(H) :=
  repeat match type of H with 
  | (_ ** _) ** _ ⊢ _ => 
      simple apply forwards_normalize_left in H
  | _ ⊢ (_ ** _) ** _ =>
      simple apply forwards_normalize_right in H
  end.

Tactic Notation "normalize_sprop" "in" "*" :=
  repeat match goal with
  | [H:_ |- _] => normalize_sprop in H
  end.

Ltac normalize_sprops := normalize_sprop; normalize_sprop in *.

Ltac sprop_facts :=
  repeat match goal with 
  | [H1: _ ⊢ ?x, H2: ?x ⊢ _ |- _] => pose new proof (sentails_trans _ _ _ H1 H2)
  end.

Lemma sep_con_only_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ** y ⊢ z -> exists x' y', z = x' ** y'.
Proof.
  intros.
  dependent induction H; eauto.
  apply only_sep_con_seq_sep_con in H.
  destruct exists H a b; subst.
  specialize (IHsentails a b).
  cut IHsentails by reflexivity.
  destruct exists IHsentails c d; subst.
  eapply only_sep_con_seq_sep_con.
  apply seq_sym.
  eassumption.
Qed.

Lemma only_sep_con_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ⊢ y ** z -> exists y' z', x = y' ** z'.
Proof.
  intros.
  dependent induction H; eauto.
  apply only_sep_con_seq_sep_con in H0.
  destruct exists H0 a b; subst.
  specialize (IHsentails a b).
  cut IHsentails by reflexivity.
  destruct exists IHsentails c d; subst.
  eapply only_sep_con_seq_sep_con.
  apply seq_sym.
  eassumption.
Qed.

Lemma val_at_only_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
  l ↦ v ⊢ z -> z = l ↦ v.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_val_at_seq_val_at in H; subst.
    specialize (IHsentails l V v).
    cut IHsentails by reflexivity.
    subst.
    eapply only_val_at_seq_val_at.
    apply seq_sym.
    assumption.
Qed.

(* This tactic is useful in simplifying assumption which arise from dependent induction *)
(* Ltac spec_cut_refl H := *)

Lemma only_val_at_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
  z ⊢ l ↦ v -> z = l ↦ v.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_val_at_seq_val_at in H0; subst.
    specialize (IHsentails l V v).
    cut IHsentails by reflexivity.
    subst.
    eapply only_val_at_seq_val_at.
    apply seq_sym.
    assumption.
Qed.

Lemma acc_at_only_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
  a @ l ⊢ z -> z = a @ l.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_acc_at_seq_acc_at in H; subst.
    specialize (IHsentails a l).
    cut IHsentails by reflexivity.
    subst.
    eapply only_acc_at_seq_acc_at.
    apply seq_sym.
    assumption.
Qed.

Lemma only_acc_at_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
  z ⊢ a @ l -> z = a @ l.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_acc_at_seq_acc_at in H0; subst.
    specialize (IHsentails a l).
    cut IHsentails by reflexivity.
    subst.
    eapply only_acc_at_seq_acc_at.
    apply seq_sym.
    assumption.
Qed.

Lemma empty_only_entails_empty {comp loc}: forall z: sprop comp loc,
  empty ⊢ z -> z = empty.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_empty_seq_empty in H; subst.
    cut IHsentails by reflexivity.
    subst.
    eapply only_empty_seq_empty.
    apply seq_sym.
    assumption.
Qed.

Lemma only_empty_entails_empty {comp loc}: forall z: sprop comp loc,
  z ⊢ empty -> z = empty.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - apply only_empty_seq_empty in H0; subst.
    cut IHsentails by reflexivity.
    subst.
    eapply only_empty_seq_empty.
    apply seq_sym.
    assumption.
Qed.

(* Not true! 
   E.G.: (a ** b) ** (c ** d) ⊢ (a ** c) ** (b ** d) by seq
*)
(* Lemma inv_sep_con_entails {comp loc}: forall (a b c d: sprop comp loc),
  a ** b ⊢ c ** d ->
  (a ⊢ c /\ b ⊢ d) \/ (a ⊢ d /\ b ⊢ c).
Proof. *)

Ltac sprop_discriminate_basic H :=
  match type of H with
  | _ ⊢ _ =>
    ((simple apply val_at_only_entails_val_at in H
    + simple apply acc_at_only_entails_acc_at in H
    + simple apply empty_only_entails_empty in H
    ); discriminate H) +
    ((simple apply only_val_at_entails_val_at in H
    + simple apply only_acc_at_entails_acc_at in H
    + simple apply only_empty_entails_empty in H
    ); discriminate H) +
    fail "Could not discriminate sprop"
  end.

(* TODO: rewrite without inv_sep_con_entails *)
(* Ltac _sprop_discriminate H :=
  match type of H with
  | _ ⊢ _ =>
    sprop_discriminate_basic H + (
      simple apply inv_sep_con_entails in H;
      destruct or H; 
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      (_sprop_discriminate H1) + (_sprop_discriminate H2)
    )
  end.
Tactic Notation "sprop_discriminate" hyp(H) := _sprop_discriminate H. *)
Tactic Notation "sprop_discriminate" hyp(H) := sprop_discriminate_basic H.

Tactic Notation "sprop_discriminate" :=
  repeat (simpl in *; unfold not);
  intros;
  break_context;
  sprop_facts;
  match goal with
  | [H: _ |- _] => sprop_discriminate H
  end.

Ltac sentails :=
  normalize_sprops;
  try sprop_discriminate;
  try (sprop_facts; assumption);
  (* repeat *)
  match goal with
  | [_:_ |- ?x ⊢ ?x] => exact (seq_entails x x (seq_refl x))
  (* find common conjuncts, shuffle them to the left side, then elim them *)
  (* | [_:_ |- ?x ** ?y ⊢ ?z] => *)
  (* | [H: ?x ⊢ ?y |- ?x ⊢ ?y] => exact H *)
  end.
