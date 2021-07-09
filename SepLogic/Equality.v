Require Import SepLogic.Definition.
Require Import SepLogic.Separation.
Require Import Coq.Relations.Relation_Definitions.

Require Import GeneralTactics.
Require Import Coq.Program.Equality.

(* TODO: seq (acc1 @ l) (acc2 @ l) if (forall c p, acc1 c p <-> acc2 c p) *)
Reserved Notation "a ≅ b" (at level 70).
Reserved Notation "a ≇ b" (at level 70).
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
  where "a ≅ b" := (seq a b)
    and "a ≇ b" := (~ a ≅ b).

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

