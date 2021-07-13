Require Import SepLogic.Definition.
Require Import SepLogic.Separation.
Require Import SepLogic.Entailment.
Require Import Coq.Relations.Relation_Definitions.

Require Import GeneralTactics.


Definition sprop_wf comp loc := {s: sprop comp loc| well_formed s}.
Definition sentails_wf {comp loc} (a b: sprop_wf comp loc) :=
  proj1_sig a ⊢ proj1_sig b.

Definition seq {comp loc} (a b: sprop_wf comp loc) := sentails_wf a b.
Notation "a ≅ b" := (seq a b) (at level 70).
Notation "a ≇ b" := (~ seq a b) (at level 70).

Theorem seq_refl {comp loc}: reflexive (sprop_wf comp loc) seq.
Proof using.
  unfold reflexive.
  intro x.
  destruct x as [x Hwf].
  unfold seq, sentails_wf; simpl. 
  induction x.
  - constructor.
    apply access_eq_refl.
  - constructor.
  - apply sep_con_intro.
    + apply IHx1.
      destruct Hwf; easy.
    + apply IHx2.
      destruct Hwf; easy.
    + destruct Hwf; easy.
Qed.

Theorem seq_sym {comp loc}: symmetric (sprop_wf comp loc) seq.
Proof using.
  unfold symmetric, seq.
  intros x y.
  apply sentails_sym.
Qed.

Theorem seq_trans {comp loc}: transitive (sprop_wf comp loc) seq.
Proof using.
  unfold transitive, seq.
  intros x y z.
  apply sentails_trans.
Qed.

Theorem seq_is_eq {comp loc}: equivalence (sprop_wf comp loc) seq.
Proof using.
  split.
  - apply seq_refl.
  - apply seq_trans.
  - apply seq_sym.
Qed.

Require Import Setoid.
Add Parametric Relation (comp loc: Set): (sprop_wf comp loc) (@seq comp loc)
  reflexivity proved by (@seq_refl comp loc)
  symmetry proved by (@seq_sym comp loc)
  transitivity proved by (@seq_trans comp loc)
  as seq_rel.

Add Parametric Relation (comp loc: Set): (sprop comp loc) (@sentails comp loc)
  symmetry proved by (@seq_sym comp loc)
  transitivity proved by (@seq_trans comp loc)
  as sentails_rel.

(* Add Parametric Morphism (comp loc: Set): (@sentails_wf comp loc)
  with signature (@seq comp loc) ==> (@seq comp loc) ==> (@seq comp loc) as sentails_wf_mor.
Proof. *)

Theorem seq_implies_sentails {comp loc}:
  forall (x y : sprop comp loc) (wf_x: well_formed x) (wf_y: well_formed y),
  exist well_formed x wf_x ≅ exist well_formed y wf_y -> x ⊢ y.
Proof using.
  intros x y wf_x wf_y H.
  unfold seq, sentails_wf in H;
  simpl in H.
  assumption.
Qed.

Theorem sentails_implies_seq {comp loc}: forall x y : sprop comp loc,
  x ⊢ y ->
  {wf_x & {wf_y & exist well_formed x wf_x ≅ exist well_formed y wf_y}}.
Proof using.
  intros x y H.
  exists (sentails_wf_l _ _ H).
  exists (sentails_wf_r _ _ H).
  unfold seq, sentails_wf.
  simpl.
  assumption.
Defined.

(* Rewrite lemmas *)
Theorem val_at_seq {comp loc: Set}: forall V (l: loc) (a1 a2: access comp) (v: V) wf_l wf_r,
  access_eq a1 a2 ->
  (exist _ (l#a1 ↦ v) wf_l) ≅ (exist _ (l#a2 ↦ v) wf_r).
Proof using.
  intros.
  unfold seq, sentails_wf. simpl.
  apply val_at_entails.
  assumption.
Qed.

Theorem sep_con_seq_intro {comp loc}:
  forall (x x' y y': sprop comp loc) wf_x wf_x' wf_y wf_y',
  exist _ x wf_x ≅ exist _ x' wf_x' ->
  exist _ y wf_y ≅ exist _ y' wf_y' ->
  separate x y ->
  {wf_xy & {wf_x'y' & exist _ (x ** y) wf_xy ≅ exist _ (x' ** y') wf_x'y'}}.
Proof using.
  simpl.
  intros.
  unfold seq, sentails_wf in *. simpl in *.
  eexists; [easy|].
  eexists.
  - max_split; try assumption.
    eapply sentails_preserves_separation_strong; eassumption.
  - apply sep_con_intro; assumption.
Qed. 

(* Theorem seq_extend_empty {comp loc}: forall (x x': sprop comp loc) wf_x wf_x',
  exist _ x wf_x ≅ exist _ x' wf_x' ->
  exist _ (⟨⟩ ** x) wf_x ≅ exist _ x' wf_x' ->
 *)

Theorem sep_con_assoc_seq {comp loc}: forall (a b c: sprop comp loc) wf_abc,
  {wf_abc' & exist _ (a ** b ** c) wf_abc ≅ exist _ ((a ** b) ** c) wf_abc'}.
Proof using.
  unfold seq, sentails_wf; simpl.
  intros.
  eexists.
  - max_split; try easy.
    + destruct wf_abc as [_ [_ wf_abc]].
      apply separate_sep_con_elim_r in wf_abc.
      easy.
    + apply separate_sep_con_intro_l.
      * destruct wf_abc as [_ [_ wf_abc]].
        apply separate_sep_con_elim_r in wf_abc.
        easy.
      * easy.
  - apply sep_con_assoc_r.
    eapply seq_implies_sentails.
    apply seq_refl.
    Unshelve.
    simpl.
    assumption.
Qed.


Goal forall comp loc (a b c: sprop comp loc),
  a ⊢ b ** c ** ⟨⟩ ->
  a ⊢ b ** c.
Proof. 
  intros.
  apply sentails_implies_seq in H;
    destruct exists H wf_x wf_y.
  eapply seq_implies_sentails.
  rewrite H.
