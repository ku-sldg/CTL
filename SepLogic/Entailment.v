Require Import SepLogic.Definition.
Require Import SepLogic.Separation.
Require Import Coq.Relations.Relation_Definitions.

Require Import Coq.Lists.List.
Import ListNotations.

Require Coq.Sorting.Permutation.
Import Permutation.

Require Import GeneralTactics.
Require Import Coq.Program.Equality.

(* Can potentially be deleted *)
(* Theorem permutation_singleton {A}: forall (x: list A) (y: A), 
  Permutation x [y] ->
  x = [y].
Proof using.
  intros.
  symmetry in H.
  apply Permutation_length_1_inv in H.
  assumption.
Qed.  *)

Reserved Notation "x ⊢ y" (at level 70).
Inductive sentails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | val_at_entails : forall V l a1 a2 (v: V),
      access_eq a1 a2 ->
      [l#a1 ↦ v] ⊢ [l#a2 ↦ v]
  (* | sep_con_intro : forall x x' y y',
      x ⊢ x' ->
      y ⊢ y' ->
      separate x y ->
      x ** y ⊢ x' ** y' *)
  | head_intro : forall x x' y y',
     [x] ⊢ [x'] ->
     y ⊢ y' ->
     atom_sprop_separate x y ->
     x :: y ⊢ x' :: y'
  | empty_entails :
      ⟨⟩ ⊢ ⟨⟩
  | sentails_perm : forall x x' y y',
      Permutation x x' ->
      Permutation y y' ->
      x ⊢ y ->
      x' ⊢ y'
  where "x ⊢ y" := (sentails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70).

Theorem empty_intro_l {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  ⟨⟩ ** x ⊢ x'.
Proof. auto. Qed.

Theorem empty_intro_r {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  x ⊢ ⟨⟩ ** x'.
Proof. auto. Qed.

Theorem empty_elim_l {comp loc}: forall x x': sprop comp loc,
  ⟨⟩ ** x ⊢ x' ->
  x ⊢ x'.
Proof. auto. Qed.

Theorem empty_elim_r {comp loc}: forall x x': sprop comp loc,
  x ⊢ ⟨⟩ ** x' ->
  x ⊢ x'.
Proof. auto. Qed.

Theorem sep_con_assoc_l {comp loc}: forall a x y z: sprop comp loc,
  x ** y ** z ⊢ a <-> (x ** y) ** z ⊢ a.
Proof. 
  intros.
  unfold sep_con. 
  rewrite app_assoc.
  split; auto.
Qed.

Theorem sep_con_assoc_r {comp loc}: forall a x y z: sprop comp loc,
  a ⊢ x ** y ** z <-> a ⊢ (x ** y) ** z.
Proof. 
  intros.
  unfold sep_con. 
  rewrite app_assoc.
  split; auto.
Qed.

Lemma empty_only_entails_empty {comp loc}: forall x: sprop comp loc,
  ⟨⟩ ⊢ x ->
  x = ⟨⟩.
Proof.
  intros x H.
  dependent induction H.
  - reflexivity.
  - symmetry in H; apply Permutation_nil in H; subst.
    cut_hyp IHsentails by reflexivity. subst.
    apply Permutation_nil in H0; subst.
    reflexivity.
Qed.

Lemma only_empty_entails_empty {comp loc}: forall x: sprop comp loc,
  x ⊢ ⟨⟩ ->
  x = ⟨⟩.
Proof.
  intros x H.
  dependent induction H.
  - reflexivity.
  - symmetry in H0; apply Permutation_nil in H0; subst.
    cut_hyp IHsentails by reflexivity. subst.
    apply Permutation_nil in H; subst.
    reflexivity.
Qed.

Lemma only_val_at_entails_val_at {comp loc}: forall (x: sprop comp loc) V l a1 (v: V),
  x ⊢ [l #a1 ↦ v] ->
  exists a2, x = [l #a2 ↦ v] /\ access_eq a1 a2.
Proof using.
  intros x V l a1 v H.
  dependent induction H.
  - eexists.
    split.
    + reflexivity.
    + symmetry. eassumption.
  - apply only_empty_entails_empty in H0; subst.
    apply IHsentails1.
    reflexivity.
  - symmetry in H0; apply Permutation_length_1_inv in H0; subst.
    specialize (IHsentails V l a1 v).
    cut_hyp IHsentails by reflexivity.
    destruct exists IHsentails a2.
    exists a2.
    split; [|easy].
    destruct IHsentails as [IHsentails _]; subst.
    apply Permutation_length_1_inv in H; subst.
    reflexivity.
Qed.

Lemma val_at_only_entails_val_at {comp loc}: forall (x: sprop comp loc) V l a1 (v: V),
  [l #a1 ↦ v] ⊢ x ->
  exists a2, x = [l #a2 ↦ v] /\ access_eq a1 a2.
Proof using.
  intros x V l a1 v H.
  dependent induction H.
  - eexists.
    split. 
    + reflexivity.
    + assumption.
  - apply empty_only_entails_empty in H0; subst.
    apply IHsentails1.
    reflexivity.
  - symmetry in H; apply Permutation_length_1_inv in H; subst.
    specialize (IHsentails V l a1 v).
    cut_hyp IHsentails by reflexivity.
    destruct exists IHsentails a2.
    exists a2.
    split; [|easy].
    destruct IHsentails as [IHsentails _]; subst.
    apply Permutation_length_1_inv in H0; subst.
    reflexivity.
Qed.

Lemma sentails_preserves_separation {comp loc}: forall x x' y: sprop comp loc,
  x ⊢ x' ->
  separate x y ->
  separate x' y.
Proof using.
  intros x x' y H Hsep.
  induction H.
  - invc Hsep; clear H3; rename H2 into Hsep.
    repeat constructor.
    induction y.
    + constructor.
    + invc Hsep.
      specializec IHy H3.
      constructor. 
      * invc H2.
        constructor.
        assumption.
      * assumption.
  - invc Hsep.
    cut_hyp IHsentails1.
    { repeat constructor. assumption. }
    invc IHsentails1; clear H7; rename H6 into IHsentails1.
    constructor.
    + assumption.
    + apply IHsentails2.
      assumption.
  - apply separate_empty_l.
  - eapply separate_perm; [eassumption|reflexivity|].
    apply IHsentails.
    eapply separate_perm. 
    + symmetry. eassumption.
    + reflexivity.
    + assumption.
Qed.

Lemma sentails_preserves_separation_strong {comp loc}: forall x x' y y': sprop comp loc,
  x ⊢ x' ->
  y ⊢ y' ->
  separate x y ->
  separate x' y'.
Proof.
  intros x x' y y' Hx Hy Hsep.
  eapply sentails_preserves_separation; [eassumption|].
  symmetry.
  eapply sentails_preserves_separation; [eassumption|].
  symmetry.
  assumption.
Qed.

Theorem sentails_sym {comp loc}: symmetric (sprop comp loc) sentails.
Proof using.
  unfold symmetric.
  intros x y H.
  induction H.
  - constructor.
    apply access_eq_sym.
    assumption.
  - apply head_intro.
    + assumption.
    + assumption.
    + apply separate_singleton.
      eapply sentails_preserves_separation_strong.
      * eassumption.
      * eassumption.
      * apply separate_singleton.
        assumption.
  - constructor.
  - eapply sentails_perm; eassumption.
Qed.

Theorem concat_eq_singleton {A}: forall (x y: list A) (z: A),
  x ++ y = [z] ->
  (x = [] /\ y = [z]) \/ (x = [z] /\ y = []).
Proof using.
  intros x y z H.
  destruct x.
  - left. split.
    + reflexivity.
    + apply H.
  - right. destruct y.
    + split.
      * rewrite app_nil_r in H.
        assumption.
      * reflexivity.
    + simpl in H.
      invc H.
      destruct x; discriminate H2.
Qed.

Theorem sep_con_eq_singleton {comp loc}: forall (x y: sprop comp loc) z,
  x ** y = [z] -> 
  (x = ⟨⟩ /\ y = [z]) \/ (x = [z] /\ y = ⟨⟩).
Proof using.
  apply concat_eq_singleton.
Qed.

Theorem sep_con_empty_r {comp loc}: forall x: sprop comp loc,
  x ** ⟨⟩ = x.
Proof.
  apply app_nil_r.
Qed.

Theorem sentails_trans_perm' {comp loc}: forall x y y' z: sprop comp loc,
  Permutation y y' ->
  x ⊢ y ->
  y' ⊢ z ->
  x ⊢ z.
Proof using.
  intros x y y' z perm Hxy Hyz;
    revert x y perm Hxy.
  induction Hyz; intros.
  - admit.
  - dependent induction Hxy.
    + admit.
    + Print Permutation.
      dependent induction perm.
      * apply head_intro.
       -- eapply IHHyz1.
        ++ reflexivity.
        ++ assumption.
       -- eapply IHHyz2; eassumption.
       -- assumption.
      * apply head_intro.
       -- eapply IHHyz1; [|eassumption].
 
  (* intros x y y' z perm Hxy;
    revert y' z perm.
  induction Hxy; intros.
  - admit.
  - specialize (IHHxy1 [x']).
    (* cut_hyp IHHxy1 by reflexivity. *)
    + eapply sentails_perm. *)
Admitted.

(* Theorem sentails_trans_perm {comp loc}: forall x x' y y' z z': sprop comp loc,
  Permutation x x' ->
  Permutation y y' ->
  Permutation z z' ->
  x ⊢ y ->
  y' ⊢ z ->
  x' ⊢ z'.
Proof using.
  intros x x' y y' z z' permx permy permz Hxy;
    revert x' y' z z' permx permy permz.
  induction Hxy; intros.
  - apply Permutation_length_1_inv in permx, permy; subst.
    apply val_at_only_entails_val_at in H0.
    destruct exists H0 a3.
    destruct H0 ; subst.
    apply Permutation_length_1_inv in permz; subst.
    apply val_at_entails.
    eapply access_eq_trans; eassumption.
  - dependent induction H0.
    + symmetry in permy; apply Permutation_length_1_inv in permy; invc permy.
      apply only_empty_entails_empty in Hxy2; subst.
      apply Permutation_length_1_inv in permz; subst.
      apply Permutation_length_1_inv in permx; subst.
      apply only_val_at_entails_val_at in Hxy1.
      destruct exists Hxy1 a3.
      destruct Hxy1 as [_temp Hxy1]; rewrite _temp; clear _temp.
      apply val_at_entails.
      eapply access_eq_trans.
      * symmetry. eassumption.
      * assumption.
    + eapply IHHxy2.
      * 
Admitted.
  
Theorem sentails_trans {comp loc}: transitive (sprop comp loc) sentails.
Proof using.
  unfold transitive.
  intros x y z Hxy; revert z.
  induction Hxy; intros z Hyz.
  - dependent induction Hyz.
    + constructor.
      eapply access_eq_trans; eassumption.
    + apply empty_only_entails_empty in Hyz2; subst.
      eapply IHHyz1.
      * eassumption.
      * reflexivity.
    + symmetry in H1; apply Permutation_length_1_inv in H1; subst.
      eapply sentails_perm.
      * reflexivity.
      * eassumption.
      * eapply IHHyz.
       -- eassumption.
       -- reflexivity.
  - dependent induction Hyz.
    + apply head_intro; try assumption.
      apply only_val_at_entails_val_at in Hxy1.
      destruct exists Hxy1 a3.
      destruct Hxy1 as [Htemp Hxy1]; rewrite Htemp; clear Htemp.
      constructor.
      eapply access_eq_trans.
      * symmetry. eassumption.
      * assumption.
    + apply head_intro.
      * apply IHHxy1. assumption.
      * apply IHHxy2. assumption.
      * assumption.
    + eapply sentails_perm.
      * reflexivity.
      * eassumption.
      * eapply IHHyz; try eassumption.
        
        
Admitted.  *)

(* This pattern is likely important for induction over entailments *)
Theorem singleton_entails_strong {comp loc}: forall a (x b: sprop comp loc),
  Permutation x (a :: b) ->
  [a] ⊢ x ->
  b = ⟨⟩.
Proof using.
  intros a x b Hperm H.
  dependent induction H. 
  - apply Permutation_length_1_inv in Hperm.
    invc Hperm.
    reflexivity.
  - apply sep_con_eq_singleton in x.
    destruct or x; destruct x; subst.
    + apply empty_only_entails_empty in H; subst.
      simpl in Hperm.
      eapply IHsentails2.
      * eassumption.
      * reflexivity.
    + apply empty_only_entails_empty in H0; subst.
      rewrite sep_con_empty_r in Hperm.
      eapply IHsentails1.
      * eassumption.
      * reflexivity.
  - symmetry in H.
    apply Permutation_length_1_inv in H; subst.
    eapply IHsentails.
    + eapply Permutation_trans; eassumption.
    + reflexivity.
Qed.

Theorem singleton_entails {comp loc}: forall a (x b: sprop comp loc),
  [a] ⊢ a :: b ->
  b = ⟨⟩.
Proof using.
  intros.
  eapply singleton_entails_strong; [|eassumption].
  reflexivity.
Qed.

Theorem head_elim_strong {comp loc}: forall a (b x y: sprop comp loc),
  Permutation x (a :: b) ->
  x ⊢ y ->
  exists a' b', 
    Permutation y (a' :: b') /\
    [a] ⊢ [a'] /\
    b ⊢ b'.
Proof using.
  intros a b x y Hperm H.
  revert a b Hperm.
  dependent induction H; intros a b Hperm.
  - apply Permutation_length_1_inv in Hperm; invc Hperm.
    repeat eexists.
    + reflexivity.
    + constructor.
      assumption.
    + constructor.
  - specialize (IHsentails1 x []).
    cut_hyp IHsentails1 by reflexivity.
    destruct exists IHsentails1 a' b'.
    destruct IHsentails1 as [Hpermx' [_ Htemp]];
      apply empty_only_entails_empty in Htemp; subst.
    apply Permutation_length_1 in Hpermx'; subst.
    destruct y.
    * apply empty_only_entails_empty in H0; subst.
      apply Permutation_length_1_inv in Hperm; invc Hperm.
      exists a'.
      exists [].
      max_split.
     -- reflexivity.
     -- assumption.
     -- constructor.
    * (* induction on Hperm? *)
      admit.
  - apply Permutation_nil_cons in Hperm.
    contradiction Hperm.
  - specialize (IHsentails a b).
    cut_hyp IHsentails by (eapply Permutation_trans; eassumption).
    destruct exists IHsentails a' b'.
    destruct IHsentails as [IHsentails1 [IHsentails2 IHsentails3]].
    exists a';
    exists b'.
    max_split; try assumption.
    eapply Permutation_trans.
    + symmetry. eassumption.
    + assumption.
Admitted.   

Theorem head_elim {comp loc}: forall a (b x: sprop comp loc),
  a :: b ⊢ x ->
  exists a' b', 
    Permutation x (a' :: b') /\
    [a] ⊢ [a'] /\
    b ⊢ b'.
Proof using.
  intros a b x H.
  dependent induction H.
  - repeat eexists.
    + reflexivity.
    + constructor.
      assumption.
    + constructor.
  - specialize (IHsentails1 a []).
    cut_hyp IHsentails1 by reflexivity.
    destruct exists IHsentails1 a' b'.
    destruct IHsentails1 as [IHsentails1 [_ Htemp]];
      apply empty_only_entails_empty in Htemp; subst.
    apply Permutation_length_1 in IHsentails1; subst.
    exists a'.
    exists y'.
    max_split; try assumption.
    reflexivity.
  - 
 Admitted. 

Theorem sep_con_intro {comp loc}: forall x x' px px' (y y': sprop comp loc),
  Permutation x px ->
  Permutation x' px' ->
  x ⊢ x' ->
  y ⊢ y' ->
  separate x y ->
  px ** y ⊢ px' ** y'.
Proof using.
  intros x x' px px' y y' perm_x perm_x' Hx;
    revert y y' px px' perm_x perm_x'.
  induction Hx; intros.
  - apply Permutation_length_1_inv in perm_x, perm_x'; subst.
    apply head_intro.
    + apply val_at_entails.
      assumption.
    + assumption.
    + apply separate_singleton.
      assumption.
  - specialize (IHHx2 y0 y'0 y y').
    repeat cut_hyp IHHx2 by reflexivity.
    cut_hyp IHHx2 by assumption.
    cut_hyp IHHx2 by (invc H1; assumption).

  - simpl.
    apply head_intro.
    + assumption.
    + eapply IHHx2.
      * reflexivity.
      * reflexivity.
      * assumption.
      * invc H1.
        assumption.
    + apply Forall_app. split. 
      * assumption.
      * invc H1.
        assumption.
  - simpl.
    assumption.
  - eapply IHHx. 

    
  induction Hx; intros.
  - apply head_intro.
    + apply val_at_entails.
      assumption.
    + assumption.
    + apply separate_singleton.
      assumption.
  - simpl.
    apply head_intro.
    + assumption.
    + eapply IHHx2.
      * reflexivity.
      * reflexivity.
      * assumption.
      * invc H1.
        assumption.
    + apply Forall_app. split. 
      * assumption.
      * invc H1.
        assumption.
  - simpl.
    assumption.
  - eapply IHHx. 
Qed.

Theorem sep_con_elim_weak {comp loc}: forall a (b c: sprop comp loc),
  a :: b ⊢ a :: c ->
  b ⊢ c.
Proof using.
  intros a b.
  revert a.
  induction b; intros.
  - assert ()


  intros a b c H.
  dependent induction H.
  - constructor. 
  - specialize (IHsentails1 a (b ** y)).
  
 

Theorem sep_con_elim {comp loc}: forall a b c: sprop comp loc,
  a ** b ⊢ a ** c ->
  b ⊢ c.
Proof using.
  intros a b c H.
  dependent induction H.
  - symmetry in x0, x.
    apply sep_con_eq_singleton in x0, x.
    destruct or x0; destruct or x; destruct multi x0 x; subst.
    + constructor.
      assumption.
    + discriminate H2.
    + discriminate H2.
    + constructor.
  - 


Theorem empty_intro_l {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  ⟨⟩ ** x ⊢ x'.
Proof. auto. Qed.

Theorem empty_intro_r {comp loc}: forall x x': sprop comp loc,
  x ⊢ x' ->
  x ⊢ ⟨⟩ ** x'.
Proof. auto. Qed.

Theorem empty_elim_l {comp loc}: forall x x': sprop comp loc,
  ⟨⟩ ** x ⊢ x' ->
  x ⊢ x'.
Proof. auto. Qed.

Theorem empty_elim_r {comp loc}: forall x x': sprop comp loc,
  x ⊢ ⟨⟩ ** x' ->
  x ⊢ x'.
Proof. auto. Qed.

Theorem sep_con_assoc_l {comp loc}: forall a x y z: sprop comp loc,
  x ** y ** z ⊢ a ->
  (x ** y) ** z ⊢ a.
Proof. 
  intros.
  unfold sep_con. 
  rewrite <- app_assoc.
  assumption.
Qed.



(* Theorem empty_elim {comp loc}: forall x y z: sprop comp loc,
  z = ⟨⟩ ** y \/ z = y ** ⟨⟩ ->
  x ⊢ z ->
  x ⊢ y.
Proof using.
  intros x y z Hz Hxz.
  induction Hxz;
    try solve [destruct or Hz; discriminate Hz].
  - destruct or Hz; subst; invc Hz.
    + apply empty_intro_r. *)

Lemma sentails_preserves_separation {comp loc}: forall x x' y: sprop comp loc,
  x ⊢ x' ->
  separate x y ->
  separate x' y.
Proof using.
  intros x x' y Hsent Hsep.
  induction Hsent.
  - unfold separate in *.
    intro Hcontra; applyc Hsep.
    dependent induction Hcontra.
    + constructor.
    + apply overlap_sep_con_rl.
      eapply IHHcontra; [|reflexivity].
      assumption.
    + apply overlap_sep_con_rr.
      eapply IHHcontra; [|reflexivity].
      assumption.
  - apply separate_sep_con_intro_l.
    + apply IHHsent1.
      apply separate_sep_con_elim_l in Hsep.
      easy.
    + apply IHHsent2.
      apply separate_sep_con_elim_l in Hsep.
      easy.
  - assumption. 
  - apply IHHsent.
    apply separate_sep_con_elim_l in Hsep.
    easy.
  - apply IHHsent.
    apply separate_sep_con_intro_l.
    * apply empty_is_separate.
    * assumption.
  - apply separate_sep_con_intro_l.
    + apply empty_is_separate.
    + apply IHHsent.
      assumption.
  - applyc IHHsent in Hsep.
    apply separate_sep_con_elim_l in Hsep.
    easy.
  - apply IHHsent.
    apply separate_sep_con_intro_l.
    + apply separate_sep_con_elim_l in Hsep.
      destruct Hsep as [Hsep _].
      apply separate_sep_con_elim_l in Hsep.
      easy.
    + apply separate_sep_con_intro_l.
      * apply separate_sep_con_elim_l in Hsep.
        destruct Hsep as [Hsep _].
        apply separate_sep_con_elim_l in Hsep.
        easy.
      * apply separate_sep_con_elim_l in Hsep.
        easy.
  - applyc IHHsent in Hsep.
    apply separate_sep_con_intro_l.
    + apply separate_sep_con_intro_l.
      * apply separate_sep_con_elim_l in Hsep.
        easy.
      * apply separate_sep_con_elim_l in Hsep.
        destruct Hsep as [_ Hsep].
        apply separate_sep_con_elim_l in Hsep.
        easy.
    + apply separate_sep_con_elim_l in Hsep.
      destruct Hsep as [_ Hsep].
      apply separate_sep_con_elim_l in Hsep.
      easy.
  - applyc IHHsent.
    apply separate_sep_con_elim_l in Hsep.
    apply separate_sep_con_intro_l; easy.
  - applyc IHHsent in Hsep.
    apply separate_sep_con_elim_l in Hsep.
    apply separate_sep_con_intro_l; easy.
  - apply IHHsent2.
    apply IHHsent1.
    assumption.
Qed. 

Lemma sentails_preserves_separation_strong {comp loc}: forall x x' y y': sprop comp loc,
  x ⊢ x' ->
  y ⊢ y' ->
  separate x y ->
  separate x' y'.
Proof using.
  intros x x' y y' Hx Hy Hsep.
  eapply sentails_preserves_separation in Hsep; [|eassumption].
  apply separate_sym in Hsep.
  eapply sentails_preserves_separation in Hsep; [|eassumption].
  apply separate_sym in Hsep.
  assumption.
Qed.

Theorem sentails_sym {comp loc}: symmetric (sprop comp loc) sentails.
Proof using.
  unfold symmetric.
  intros x y H.
  induction H.
  - constructor.
    apply access_eq_sym.
    assumption.
  - apply sep_con_intro; try assumption.
    eapply sentails_preserves_separation_strong; eassumption.
  - constructor.
  - apply empty_intro_r.
    assumption.
  - apply empty_elim_r.
    assumption.
  - apply empty_intro_l.
    assumption.
  - apply empty_elim_l.
    assumption.
  - apply sep_con_assoc_r.
    assumption.
  - apply sep_con_assoc_l.
    assumption.
  - apply sep_con_comm_r.
    assumption.
  - apply sep_con_comm_l.
    assumption.
  - eapply sentails_trans; eassumption.
Qed.

Require Import Setoid.
Add Parametric Relation (comp loc: Set): (sprop comp loc) (@sentails comp loc)
  symmetry proved by (@sentails_sym comp loc)
  transitivity proved by (@sentails_trans comp loc)
  as sentails_rel.
  
Theorem normalization_preserves_entailment_l {comp loc}:
  forall (x x' y: sprop comp loc) Hnorm,
    normalize x = exist _ x' Hnorm ->
    x ⊢ y ->
    x' ⊢ y.
Proof using.
  simpl.
  intros. 
  induction H0.
  - invc H.
    constructor.
    assumption.
  - 
  

Lemma empty_entails_decomp_l {comp loc}: forall e1 e2: sprop comp loc,
  e1 ** e2 ⊢ ⟨⟩ ->
  e1 ⊢ ⟨⟩ /\ e2 ⊢ ⟨⟩.
Proof using.
  intros e1 e2 H.
  

  dependent induction H.
  - split. 
    + constructor. 
    + assumption.
  - 


Theorem sentails_wf_l {comp loc}: forall a b: sprop comp loc,
  a ⊢ b ->
  well_formed a.
Proof using.
  intros a b H.
  induction H.
  - simpl. auto.
  - simpl. auto.
  - simpl. auto.
  - simpl. split; [|split].
    + exact I.
    + assumption. 
    + apply empty_is_separate.
  - simpl in IHsentails. easy.
  - assumption.
  - assumption.
  - simpl in *.
    max_split; try easy.
    + destruct IHsentails as [_ [_ IHsentails]].
      apply separate_sep_con_elim_r in IHsentails.
      easy.
    + destruct IHsentails as [_ [[_ [_ H1]] H2]].
      apply separate_sep_con_elim_r in H2.
      destruct H2 as [_ H2].
      apply separate_sep_con_intro_l; assumption.
  - assumption.
  - simpl in *.
    destruct IHsentails as [H1 [H2 H3]].
    max_split; try assumption.
    apply separate_sym.
    assumption.
  - assumption.
  - assumption.
Qed.

Theorem sentails_wf_r {comp loc}: forall a b: sprop comp loc,
  a ⊢ b ->
  well_formed b.
Proof using.
  intros a b H.
  eapply sentails_wf_l.
  apply sentails_sym.
  eassumption.
Qed.

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

(*
Lemma empty_entails_decomp_l {comp loc}: forall e1 e2: sprop comp loc,
  e1 ** e2 ⊢ ⟨⟩ ->
  e1 ⊢ ⟨⟩.
Proof using.
  intros e1.
  destruct e1.
  - intros.
    apply 
Admitted.

Lemma empty_is_separate_strong {comp loc}: forall e x: sprop comp loc,
  e ⊢ ⟨⟩ ->
  separate e x.
Proof using.
  induction e; intros x H.
  - inversion H.
  - apply empty_is_separate.
  - induction x.
    + apply separate_sep_con_intro_l.
      * apply IHe1.
        eapply empty_entails_decomp_l.
        eassumption.
      * apply IHe2.
        eapply empty_entails_decomp_l.
        apply sep_con_comm_l.
        eassumption.
    + apply separate_sym.
      apply empty_is_separate.
    + apply separate_sep_con_intro_r; assumption.
Qed.

Lemma empty_strong_intro_l {comp loc}: forall x y y': sprop comp loc,
  x ⊢ ⟨⟩ ->
  y ⊢ y' ->
  x ** y ⊢ y'.
Proof using.
  intros x; induction x; intros y y' Hx Hy.
  - inversion Hx.
  - apply empty_intro_l.
    assumption.
  - apply empty_elim_r.
    apply sep_con_intro.
    + assumption.
    + assumption.
    + apply empty_is_separate_strong.
      assumption.
Qed.

Theorem entailment_preserves_separation {comp loc}: forall x y: sprop comp loc,
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

(* Tactics *)


Lemma rewrite_in_tail_r {comp loc}: forall a b c c': sprop comp loc,
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

Lemma empty_intro_r_tail {comp loc}: forall (x x': sprop comp loc),
  x ⊢ x' ->
  x ⊢ x' ** ⟨⟩.
Proof using.
  intros x x' H.
  apply sep_con_comm_r.
  apply empty_intro_r.
  assumption.
Qed.

Lemma empty_intro_l_tail {comp loc}: forall (x x': sprop comp loc),
  x ⊢ x' ->
  x ** ⟨⟩ ⊢ x'.
Proof using.
  intros x x' H.
  apply sep_con_comm_l.
  apply empty_intro_l.
  assumption.
Qed.

Lemma empty_intro_r_tail_wf_refl {comp loc}: forall x: sprop comp loc,
  well_formed x ->
  x ⊢ x ** ⟨⟩.
Proof using.
  intros x Hwf.
  apply empty_intro_r_tail.
  apply sentails_wf_refl.
  assumption.
Qed.

Lemma empty_intro_l_tail_wf_refl {comp loc}: forall x: sprop comp loc,
  well_formed x ->
  x ** ⟨⟩ ⊢ x.
Proof using.
  intros x Hwf.
  apply empty_intro_l_tail.
  apply sentails_wf_refl.
  assumption.
Qed.

(* Lemma foo {comp loc}: forall a b c d: sprop comp loc,
  a ⊢ b ** c ** d ** ⟨⟩ ->
  a ⊢ b ** c ** d.
Proof using.
  intros.
  pose proof (sentails_wf_r _ _ H).
  simpl in H0.

  pose proof (empty_intro_l_tail_wf_refl d).
  cut_hyp H1 by easy.
  
  (* pose proof (rewrite_in_tail_r _ _ _ _ H2 H). *)

  eapply (rewrite_in_tail_r _ _ _ _ ) in H.
  all: cycle 1.
  eapply (rewrite_in_tail_r _ _ _ _ ).
  all: cycle 1. *)

(* Fixpoint _percolate_up_empty_aux c H :=
  match c with 
  | a ** ⟨⟩ => pose proof _ as H
  | ⟨⟩ ** b =>
  | a ** b =>
  end *)

(* Ltac percolate_up_empty :=
  match goal with
  | |- _ ⊢ a ** b => 
      simpl apply (rewrite_in_sep_tail_r _ _ _ _ 
      (* percolate up in b *)
  | |- a ** b ⊢ _ =>
  end. *)

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

(* Lemma sep_con_only_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
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
Admitted.    *)

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

(* Ltac sprop_discriminate_basic H :=
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
  end. *)

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

(* Tactic Notation "sprop_discriminate" hyp(H) := sprop_discriminate_basic H.

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
  end. *)

*)