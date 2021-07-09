Require Import GeneralTactics.
Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.

Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.

Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.

(* This separation logic is restricted in its lack of arbitrary propositions,
   and its treatment of `empty` (which is only equal to and can only entail `empty`) *)
Inductive sprop (comp loc: Set) :=
  | sep_con  : sprop comp loc -> sprop comp loc -> sprop comp loc
  | val_at   : forall v, loc -> v -> sprop comp loc
  | acc_at   : loc -> access comp -> sprop comp loc
  | empty : sprop comp loc.

Arguments sep_con {comp loc}%type_scope.
Arguments val_at  {comp loc v}%type_scope.
Arguments acc_at  {comp loc}%type_scope.
Arguments empty   {comp loc}%type_scope.

(* Declare Scope sep_scope. *)
(* Bind Scope sep_scope with sprop. *)

(* Not sure why this is disallowed. Todo, look at other coq sep logics. *)
(* Notation "X * Y" := (sep_con X Y) (at level 45, right associativity) : sep_scope. *)
Notation "X ** Y" := (sep_con X Y) (at level 55, right associativity).
Notation "l ↦ v" := (val_at l v) (at level 50).
(* Also not sure why this one isn't working *)
(* Notation "l : V ↦ v" := (@val_at _ _ V l v) (at level 40). *)
(* Check (0 ↦ 1). *)
(* Check (0 : nat ↦ 1). *)
Notation "a @ l" := (acc_at l a) (at level 50).

(* Non-contradictory and non-redundant *)
Inductive overlap {comp loc}: sprop comp loc -> sprop comp loc -> Prop :=
  | overlap_val_at : forall l V1 (v1: V1) V2 (v2: V2),
      overlap (l ↦ v1) (l ↦ v2)
  | overlap_acc_at : forall l a1 a2,
      overlap (l @ a1) (l @ a2)
  | overlap_sep_con_left : forall x y z,
      overlap x z \/ overlap y z ->
      overlap (x ** y) z
  | overlap_sep_con_right : forall x y z,
      overlap x y \/ overlap x z ->
      overlap x (y ** z)
  | overlap_empty_l : forall x,
      overlap empty x
  | overlap_empty_r : forall x,
      overlap x empty.

Theorem overlap_is_eq {comp loc}: equivalence (sprop comp loc) overlap.
Proof.
  split.
  - unfold reflexive.
    induction x; try constructor.
    left.
    constructor.
    left.
    assumption.
  - unfold transitive.
    intros.
    induction H.
Admitted.

Definition separate {comp loc} (x y: sprop comp loc ):=
  ~ overlap x y.

(* TODO: seq (acc1 @ l) (acc2 @ l) if (forall c p, acc1 c p <-> acc2 c p) *)
Reserved Notation "a ≅ b" (at level 90).
(* Reserved Notation "a ⊣⊢ b" (at level 20). *)
Inductive seq {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | seq_refl : forall x,
      x ≅ x
  | sep_con_eq : forall x x' y y',
      x ≅ x' ->
      y ≅ y' ->
      x ** y ≅ x' ** y'
  | sep_con_eq_comm_r : forall a b c, 
      a ≅ b ** c ->
      a ≅ c ** b
  | sep_con_eq_comm_l : forall a b c, 
      a ** b ≅ c ->
      b ** a ≅ c
  | sep_con_eq_assoc_r : forall a b c d,
      a ≅ b ** c ** d ->
      a ≅ (b ** c) ** d
  | sep_con_eq_assoc_l : forall a b c d,
      a ** b ** c ≅ d ->
      (a ** b) ** c ≅ d
  where "a ≅ b" := (seq a b).

Lemma only_sep_con_seq_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ≅ y ** z ->
  exists y' z', x = y' ** z'.
Proof using.
  intros x y z Hseq.
  dependent induction Hseq; eauto.
Qed.

Lemma only_val_at_seq_val_at {comp loc}: forall (x: sprop comp loc) l V (v: V),
  x ≅ l ↦ v ->
  x = l ↦ v.
Proof using.
  intros x l V v Hseq.
  dependent induction Hseq; eauto.
  - specialize (IHHseq l V v).
    cut IHHseq by reflexivity.
    discriminate IHHseq.
  - specialize (IHHseq l V v).
    cut IHHseq by reflexivity.
    discriminate IHHseq.
Qed.

Lemma only_acc_at_seq_acc_at {comp loc}: forall (x: sprop comp loc) a l,
  x ≅ a @ l ->
  x = a @ l.
Proof using.
  intros x a l Hseq.
  dependent induction Hseq; eauto.
  - specialize (IHHseq a l).
    cut IHHseq by reflexivity.
    discriminate IHHseq.
  - specialize (IHHseq a l).
    cut IHHseq by reflexivity.
    discriminate IHHseq.
Qed.

Lemma only_empty_seq_empty {comp loc}: forall (x: sprop comp loc),
  x ≅ empty ->
  x = empty.
Proof using.
  intros x Hseq.
  dependent induction Hseq; eauto.
  - cut IHHseq by reflexivity.
    discriminate IHHseq.
  - cut IHHseq by reflexivity.
    discriminate IHHseq.
Qed.

Lemma sep_con_eq_assoc_r_undo {comp loc}: forall a b c d: sprop comp loc,
  a ≅ (b ** c) ** d ->
  a ≅ b ** c ** d.
Proof using.
  intros a b c d H.
  apply sep_con_eq_comm_r; apply sep_con_eq_assoc_r.
  apply sep_con_eq_comm_r; apply sep_con_eq_assoc_r.
  apply sep_con_eq_comm_r.
  assumption.
Qed.

Lemma sep_con_eq_assoc_l_undo {comp loc}: forall a b c d: sprop comp loc,
  (a ** b) ** c ≅ d ->
  a ** b ** c ≅ d.
Proof using.
  intros a b c d H.
  apply sep_con_eq_comm_l; apply sep_con_eq_assoc_l.
  apply sep_con_eq_comm_l; apply sep_con_eq_assoc_l.
  apply sep_con_eq_comm_l.
  assumption.
Qed.

Theorem seq_sym {comp loc}: symmetric (sprop comp loc) seq.
Proof.
  unfold symmetric.
  intros x y H.
  dependent induction H; constructor; assumption.
Qed.

Ltac _seq_discriminate_basic_r H :=
  ((simple apply only_val_at_seq_val_at in H
  + simple apply only_acc_at_seq_acc_at in H
  + simple apply only_empty_seq_empty in H
  ); discriminate H) +
  fail "Could not discriminate seq".

Ltac seq_discriminate_basic H :=
  match type of H with
  | _ ≅ _ => 
      _seq_discriminate_basic_r H +
      (apply seq_sym in H; _seq_discriminate_basic_r H)
  end.

(* TODO: advanced discriminate that dives into sep_con *)
Ltac seq_discriminate H := seq_discriminate_basic H.

Tactic Notation "seq_discriminate" :=
  repeat (simpl in *; unfold not); intros;
  break_context;
  match goal with
  | [H: _ |- _] => seq_discriminate H
  end.

(* Definition sprop_eq := clos_refl_sym_transn1 _ sprop_eq_step. *)
Theorem seq_is_eq {comp loc}: equivalence (sprop comp loc) seq.
Proof.
  split.
  - unfold reflexive.
    constructor.
  - unfold transitive.
    intros x y z Hxy Hyz.
    dependent induction Hyz.
    + assumption.
    + apply only_sep_con_seq_sep_con in Hxy.
      destruct exists Hxy a b; subst.
      (* Bad induction principle *)
      admit.
    + constructor. apply IHHyz. assumption.
    + apply IHHyz. constructor. assumption.  
    + apply sep_con_eq_assoc_r.
      apply IHHyz.
      assumption.
    + apply IHHyz.
      apply sep_con_eq_assoc_r_undo.
      assumption.
  - apply seq_sym.
Admitted.

Theorem separation_preserved_seq {comp loc}: forall x y: sprop comp loc,
  x ≅ y ->
  forall z, separate x z <-> separate y z.
Proof using.
  intros x y H z.
  split; intro Hsep.
  - unfold separate in *.
    intro Hcontra.
    applyc Hsep.
    induction Hcontra.
    + apply only_val_at_seq_val_at in H; subst. 
      constructor.
    + apply only_acc_at_seq_acc_at in H; subst.
      constructor.
    + destruct or H0.
      * inv H0.
       -- 
       (* This proof seems doable, just really tedious *)
Admitted.

(* Reserved Notation "x ⊢ y" (at level 70).
Inductive sentails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | seq_entails : forall x x',
      seq x x' ->
      x ⊢ x'
  | sep_con_intro : forall x x' y y',
      x ⊢ x' ->
      y ⊢ y' ->
      separate x y ->
      x ** y ⊢ x' ** y'
  | sentails_trans : forall x y z,
      x ⊢ y ->
      y ⊢ z ->
      x ⊢ z
  where "x ⊢ y" := (sentails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70). *)
(* Alt defininition *)
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

(* Lemma only_sep_con_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ⊢ y ** z -> exists y' z', x = y' ** z'.
Admitted. *)
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

(* Ltac _espec_cut_by H tac :=
  match type of H with
  | _ -> _ =>
      cut H by tac;
      _espec_cut_by H tac
  | forall (x: ?t), _ => 
      let xfresh := fresh x in
      evar (xfresh: t);
      specialize (H xfresh);
      _espec_cut_by H tac
  | _ => idtac
  end.
Tactic Notation "espec_cut" hyp(H) "by" tactic(tac) := _espec_cut_by H tac. *)

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

(* Ltac find_sprop_discriminate H :=
  match goal with
  | [H: _ |- _] => sprop_discriminate H
  end.
Tactic Notation "sprop_discriminate" :=
  repeat (simpl in *; unfold not);
  intros;
  break_context;
  sprop_facts;
  find_sprop_discriminate. *)
Tactic Notation "sprop_discriminate" :=
  repeat (simpl in *; unfold not);
  intros;
  break_context;
  sprop_facts;
  match goal with
  | [H: _ |- _] => sprop_discriminate H
  end.

(* Lemma foobar {comp loc: Set}: forall (l: loc) V (v: V) (a: access comp),
  (l ↦ v ** empty : sprop comp loc) ⊬ (empty ** a @ l : sprop comp loc).
Proof.
  intros.
  sprop_discriminate.
Qed. *)

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
