Require Import SepLogic.Definition.
Require Import SepLogic.Separation.

Require Import GeneralTactics.
Require Import Coq.Program.Equality.

Reserved Notation "x ⊢ y" (at level 70).
Inductive sentails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | val_at_entails : forall V l a1 a2 (v: V),
      access_eq a1 a2 ->
      l;a1 ↦ v ⊢ l;a2 ↦ v
  | sep_con_intro : forall x x' y y',
      x ⊢ x' ->
      y ⊢ y' ->
      separate x y ->
      x ** y ⊢ x' ** y'
  (* | sep_pure_intro_l : forall (p: Prop) x x',
      (p -> x ⊢ x') ->
      ⟨p⟩ ** x ⊢ x'
  | sep_pure_intro_r : forall (p: Prop) x x',
      p ->
      x ⊢ x' ->
      x ⊢ ⟨p⟩ ** x' *)
  | sep_empty_intro_l : forall (p: Prop) x x',
      x ⊢ x' ->
      ⟨⟩ ** x ⊢ x'
  | sep_empty_intro_r : forall (p: Prop) x x',
      x ⊢ x' ->
      x ⊢ ⟨⟩ ** x'
  | sep_con_assoc_l : forall a b c d,
      a ** b ** c ⊢ d ->
      (a ** b) ** c ⊢ d
  | sep_con_assoc_r : forall a b c d,
      a ⊢ b ** c ** d ->
      a ⊢ (b ** c) ** d
  | sep_con_comm_l : forall a b c,
      a ** b ⊢ c ->
      b ** a ⊢ c
  | sep_con_comm_r : forall a b c,
      a ⊢ b ** c ->
      a ⊢ c ** b
  where "x ⊢ y" := (sentails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70).

(* Definition sentails_ind': forall (comp loc : Set) (P : sprop comp loc -> sprop comp loc -> Prop),
  (forall (l : loc) (V : Type) (v : V),
    P (l ↦ v) (l ↦ v)) ->
  (forall (a1 a2 : access comp) (l : loc),
    access_eq a1 a2 ->
    P (a1 @ l) (a2 @ l)) ->
  (forall x x' y y' : sprop comp loc,
    x ⊢ x' ->
    P x x' ->
    y ⊢ y' ->
    P y y' ->
    separate x y ->
    P (x ** y) (x' ** y')) ->
  (forall (p : Prop) (x x' : sprop comp loc),
    (p -> x ⊢ x') ->
    (p -> P x x') ->
    P (⟨ p ⟩ ** x) x') ->
  (forall (p : Prop) (x x' : sprop comp loc),
    p ->
    x ⊢ x' ->
    P x x' ->
    P x (⟨ p ⟩ ** x')) ->
  (forall a b c d : sprop comp loc,
    a ** b ** c ⊢ d ->
    P (a ** b ** c) d ->
    P ((a ** b) ** c) d) ->
  (forall a b c d : sprop comp loc,
    a ⊢ b ** c ** d ->
    P a (b ** c ** d) ->
    P a ((b ** c) ** d)) ->
  (forall a b c : sprop comp loc,
    a ** b ⊢ c ->
    P (a ** b) c ->
    P (b ** a) c) ->
  (forall a b c : sprop comp loc,
    a ⊢ b ** c ->
    P a (b ** c) ->
    P a (c ** b)) ->
  forall s s0 : sprop comp loc, s ⊢ s0 -> P s s0.
Admitted. *)

Theorem sentails_trans {comp loc}: forall x y z: sprop comp loc,
  x ⊢ y ->
  y ⊢ z -> 
  x ⊢ z.
Proof using.
  (* intros x y z Hxy Hyz.
  revert x Hxy.
  dependent induction Hyz; intros.
  - assumption.
  - dependent induction Hxy.
    + constructor.
      (* transitivity *)
      (* todo: prove acces_eq is eq *)
      admit.
    + apply sep_pure_intro_l.
      intro pWitness.
      eapply H0.
      * assumption.
      * eassumption.
      * reflexivity.
    +  *)
Admitted. 

Lemma sep_con_assoc_l_rev {comp loc}: forall a b c d: sprop comp loc,
  (a ** b) ** c ⊢ d ->
  a ** b ** c ⊢ d.
Proof using.
  intros a b c d H.
  apply sep_con_comm_l; apply sep_con_assoc_l.
  apply sep_con_comm_l; apply sep_con_assoc_l.
  apply sep_con_comm_l.
  assumption.
Qed.

Lemma sep_con_assoc_r_rev {comp loc}: forall a b c d: sprop comp loc,
  a ⊢ (b ** c) ** d ->
  a ⊢ b ** c ** d.
Proof using.
  intros a b c d H.
  apply sep_con_comm_r; apply sep_con_assoc_r.
  apply sep_con_comm_r; apply sep_con_assoc_r.
  apply sep_con_comm_r.
  assumption.
Qed.

Lemma empty_elim_l {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  ⟨⟩ ** x ⊢ x'.
Proof using.
  intros x x' H.
  apply sep_pure_intro_l.
  intro.
  assumption.
Qed.

Lemma empty_elim_r {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  x ⊢ ⟨⟩ ** x'.
Proof using.
  intros x x' H.
  apply sep_pure_intro_r.
  - exact I.
  - assumption.
Qed.

(* sep_pure sanity check *)
(* Goal forall {comp loc} a l,
  ⟨False⟩ ** a @ l ⊢ (a @ l ** ⟨False⟩: sprop comp loc).
intros comp loc a l.
apply sep_pure_intro_l.
intro F.
apply sep_con_comm_r.
apply sep_pure_intro_r.
- assumption.
- apply sentails_refl.
Qed. *)

Definition seq {comp loc} (a b: sprop comp loc) :=
  a ⊢ b /\ b ⊢ a.
Notation "a ≅ b" := (seq a b) (at level 70).
Notation "a ≇ b" := (~ seq a b) (at level 70).

Theorem separation_preserved_entailment {comp loc}: forall x y: sprop comp loc,
  x ⊢ y ->
  forall z, separate x z <-> separate y z.
Proof using.
Admitted.

Lemma flip_sentails_trans {comp loc}: forall (x y z: sprop comp loc),
  y ⊢ z ->
  x ⊢ y ->
  x ⊢ z.
Proof.
  intros.
  eapply sentails_trans; eassumption.
Qed.

Theorem sentails_wf_l {comp loc}: forall a b: sprop comp loc,
  a ⊢ b ->
  well_formed a.
Proof using.
  intros a b H.
  induction H.
  - unfold well_formed. auto.
  - unfold well_formed.

  - simpl. auto.
  - simpl. auto.
  - simpl.
Admitted.

Theorem sentails_wf_r {comp loc}: forall a b: sprop comp loc,
  a ⊢ b ->
  well_formed b.
Admitted.

Lemma sentails_wf_refl {comp loc}: forall a: sprop comp loc,
  well_formed a ->
  a ⊢ a.
Proof using.
  intros a H.
Admitted.


(* Tactics *)


Lemma rewrite_in_sep_tail_r {comp loc}: forall a b c c': sprop comp loc,
  c ⊢ c' ->
  a ⊢ b ** c ->
  a ⊢ b ** c'.
Proof using.
  intros a b c c' Hc H.
  eapply sentails_trans.
  - eassumption.
  - apply sep_con_intro.
    + apply sentails_wf_refl.
      apply sentails_wf_r in H.
      simpl in H.
      easy.
    + assumption.
    + apply sentails_wf_r in H.
      simpl in H.
      easy.
Qed.

Ltac percolate_up_sep_pure :=
  match goal with
  | |- _ ⊢ a ** b =>
      (* percolate up in b *)
  | |- a ** b ⊢ _ =>
  end.

Tactic Notation "normalize_sprop" :=
  repeat match goal with 
  | [_:_ |- (_ ** _) ** _ ⊢ _] => 
      simple apply sep_con_assoc_l
  | [_:_ |- _ ⊢ (_ ** _) ** _] =>
      simple apply sep_con_assoc_r
  end.

Tactic Notation "normalize_sprop" "in" hyp(H) :=
  repeat match type of H with 
  | (_ ** _) ** _ ⊢ _ => 
      simple apply sep_con_assoc_l_rev in H
  | _ ⊢ (_ ** _) ** _ =>
      simple apply sep_con_assoc_r_rev in H
  end.

Tactic Notation "normalize_sprop" "in" "*" :=
  try normalize_sprop;
  repeat match goal with
  | [H:_ |- _] => normalize_sprop in H
  end.

Ltac sprop_facts :=
  repeat match goal with 
  | [H1: _ ⊢ ?x, H2: ?x ⊢ _ |- _] => pose new proof (sentails_trans _ _ _ H1 H2)
  end.

Lemma sep_con_only_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  spatial x ->
  spatial y ->
  x ** y ⊢ z ->
  exists x' y', z = x' ** y'.
Proof.
  intros x y z Hx Hy H.
  dependent induction H; try solve [eauto].
  - contradiction Hx.
  - specialize (IHsentails a (b ** y)).
    apply IHsentails.
Admitted.   

(* Lemma only_sep_con_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
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
Qed. *)

(* Lemma val_at_only_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
  spatial z ->
  l ↦ v ⊢ z ->
  z = l ↦ v.
Proof.
  intros. dependent induction H.
  - reflexivity.
  - specialize (IHsentails l V v).
    cut_hyp IHsentails by reflexivity.
    subst.
    apply sep_pure_intro_l.
  - apply only_val_at_seq_val_at in H; subst.
    specialize (IHsentails l V v).
    cut IHsentails by reflexivity.
    subst.
    eapply only_val_at_seq_val_at.
    apply seq_sym.
    assumption.
Qed. *)

(* Lemma only_val_at_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
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
Qed. *)

(* Lemma acc_at_only_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
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
Qed. *)

(* Lemma only_acc_at_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
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
Qed. *)

(* Lemma empty_only_entails_empty {comp loc}: forall z: sprop comp loc,
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
Qed. *)

(* Lemma only_empty_entails_empty {comp loc}: forall z: sprop comp loc,
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
Qed. *)

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
  repeat normalize_sprop in *;
  try sprop_discriminate;
  try (sprop_facts; assumption);
  (* repeat *)
  match goal with
  | [_:_ |- ?x ⊢ ?x] => exact (seq_entails x x (seq_refl x))
  (* find common conjuncts, shuffle them to the left side, then elim them *)
  (* | [_:_ |- ?x ** ?y ⊢ ?z] => *)
  (* | [H: ?x ⊢ ?y |- ?x ⊢ ?y] => exact H *)
  end.
