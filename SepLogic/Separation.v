Require Import SepLogic.Definition.
Require Import Coq.Relations.Relation_Definitions.

Require Import Coq.Program.Equality.
Require Import GeneralTactics.

(* Contradictory or redundant *)
Inductive overlap {comp loc}: sprop comp loc -> sprop comp loc -> Prop :=
  | overlap_val_at : forall l a1 a2 V1 (v1: V1) V2 (v2: V2),
      overlap (l#a1 ↦ v1) (l#a2 ↦ v2)
  | overlap_sep_con_ll : forall x y z,
      overlap x z ->
      overlap (x ** y) z
  | overlap_sep_con_lr : forall x y z,
      overlap y z ->
      overlap (x ** y) z
  | overlap_sep_con_rl : forall x y z,
      overlap x y ->
      overlap x (y ** z)
  | overlap_sep_con_rr : forall x y z,
      overlap x z ->
      overlap x (y ** z).

Theorem overlap_sym {comp loc}: symmetric (sprop comp loc) overlap.
Proof using.
  unfold symmetric.
  intros x y H.
  dependent induction H.
  - constructor.
  - apply overlap_sep_con_rl.
    assumption.
  - apply overlap_sep_con_rr.
    assumption.
  - apply overlap_sep_con_ll.
    assumption.
  - apply overlap_sep_con_lr.
    assumption.
Qed.

Definition separate {comp loc} (x y: sprop comp loc ):=
  ~ overlap x y.

Theorem separate_sym {comp loc}: symmetric (sprop comp loc) separate.
Proof using.
  unfold symmetric.
  intros x y.
  unfold separate.
  intros H Hcontra.
  applyc H.
  apply overlap_sym.
  assumption.
Qed.

Lemma empty_is_separate {comp loc}: forall x: sprop comp loc,
  separate ⟨⟩ x.
Proof using.
  intros x Hcontra.
  dependent induction Hcontra.
  - apply IHHcontra. reflexivity. 
  - apply IHHcontra. reflexivity.
Qed.

Lemma separate_sep_con_elim_r {comp loc}: forall a b c: sprop comp loc,
  separate a (b ** c) ->
  separate a b /\ separate a c.
Proof using.
  unfold separate, not.
  intros a b c H.
  split; intro.
  - applyc H.
    apply overlap_sep_con_rl.
    assumption.
  - applyc H.
    apply overlap_sep_con_rr.
    assumption.
Qed.

Lemma separate_sep_con_elim_l {comp loc}: forall a b c: sprop comp loc,
  separate (a ** b) c ->
  separate a c /\ separate b c.
Proof using.
  intros.
  apply separate_sym in H.
  apply separate_sep_con_elim_r in H.
  destruct H as [H1 H2].
  split; apply separate_sym; assumption.
Qed.

Lemma separate_sep_con_intro_r {comp loc}: forall a b c: sprop comp loc,
  separate a b ->
  separate a c ->
  separate a (b ** c).
Proof using.
  unfold separate, not.
  intros a b c H1 H2 Hcontra.
  dependent induction Hcontra.
  - eapply (IHHcontra b c); clear IHHcontra.
    + intro H.
      apply H1.
      apply overlap_sep_con_ll.
      assumption.
    + intro H.
      apply H2.
      apply overlap_sep_con_ll.
      assumption.
    + reflexivity.
  - eapply (IHHcontra b c); clear IHHcontra.
    + intro H.
      apply H1.
      apply overlap_sep_con_lr.
      assumption.
    + intro H.
      apply H2.
      apply overlap_sep_con_lr.
      assumption.
    + reflexivity.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

Lemma separate_sep_con_intro_l {comp loc}: forall a b c: sprop comp loc,
  separate a c ->
  separate b c ->
  separate (a ** b) c.
Proof using.
  intros.
  apply separate_sym.
  apply separate_sep_con_intro_r; apply separate_sym; assumption.
Qed.

Fixpoint well_formed {comp loc} (s: sprop comp loc) : Prop :=
  match s with 
  | _#_ ↦ _ => True 
  | ⟨⟩ => True
  | sep_con s1 s2 =>
      well_formed s1 /\
      well_formed s2 /\
      separate s1 s2
  end.
