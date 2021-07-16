Require Import SepLogic.Definition.
Require Import SepLogic.Separation.
Require Import Coq.Relations.Relation_Definitions.

Require Import Coq.Lists.List.
Import ListNotations.

Require Coq.Sorting.Permutation.
Import Permutation.

Require Import Setoid.
Require Import GeneralTactics.
Require Import Coq.Program.Equality.

Reserved Notation "x ⊢ₐ y" (at level 70).
Inductive atom_sentails {comp loc}
  : sprop_atom comp loc -> sprop_atom comp loc -> Prop :=
  | val_at_entails : forall V l a1 a2 (v: V),
      access_eq a1 a2 ->
      l #a1 ↦ v ⊢ₐ l #a2 ↦ v
  where "x ⊢ₐ y" := (atom_sentails x y).

Theorem atom_sentails_refl {comp loc}: 
  reflexive (sprop_atom comp loc) atom_sentails.
Proof using.
  intros x.
  destruct x.
  constructor.
  reflexivity.
Qed.

Theorem atom_sentails_sym {comp loc}: 
  symmetric (sprop_atom comp loc) atom_sentails.
Proof using.
  intros x y H.
  invc H.
  constructor.
  symmetry.
  assumption.
Qed.

Theorem atom_sentails_trans {comp loc}: 
  transitive (sprop_atom comp loc) atom_sentails.
Proof using.
  intros x y z Hxy Hyz.
  dependent induction Hxy; dependent induction Hyz.
  constructor.
  eapply access_eq_trans; eassumption.
Qed.

Lemma atom_sentails_eq {comp loc}: 
  equivalence (sprop_atom comp loc) atom_sentails.
Proof using.
  split. 
  - exact atom_sentails_refl.
  - exact atom_sentails_trans.
  - exact atom_sentails_sym.
Qed.

Add Parametric Relation (comp loc: Set): (sprop_atom comp loc) (@atom_sentails comp loc)
  reflexivity proved by (@atom_sentails_refl comp loc)
  symmetry proved by (@atom_sentails_sym comp loc)
  transitivity proved by (@atom_sentails_trans comp loc)
  as atom_sentails_rel.


Reserved Notation "x ⊢ y" (at level 70).
Inductive sentails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | empty_entails :
      ⟨⟩ ⊢ ⟨⟩
  | head_intro : forall x x' y y',
      x ⊢ₐ x' ->
      y ⊢ y' ->
      atom_sprop_separate x y ->
      x :: y ⊢ x' :: y'
  | sentails_perm : forall x x' y y',
      Permutation x x' ->
      Permutation y y' ->
      x ⊢ y ->
      x' ⊢ y'
  where "x ⊢ y" := (sentails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70).

Theorem sentails_singleton {comp loc}: forall a a': sprop_atom comp loc,
  a ⊢ₐ a' <-> [a] ⊢ [a'].
Proof using.
  intros a a'.
  split; intro H.
  - apply head_intro.
    + assumption.
    + constructor.
    + constructor.
  - dependent induction H.
    + assumption.
    + symmetry in H, H0.
      apply Permutation_length_1_inv in H; subst.
      apply Permutation_length_1_inv in H0; subst.
      apply IHsentails; reflexivity.
Qed.

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

Ltac invc_empty_entail H :=
  match type of H with 
  | ⟨⟩ ⊢ _ => apply empty_only_entails_empty in H; subst
  | [] ⊢ _ => apply empty_only_entails_empty in H; subst
  | _ ⊢ ⟨⟩ => apply only_empty_entails_empty in H; subst
  | _ ⊢ [] => apply only_empty_entails_empty in H; subst
  end.

Ltac invc_atom_sentails H := dependent induction H.

Lemma only_val_at_entails_val_at {comp loc}: forall (x: sprop comp loc) V l a1 (v: V),
  x ⊢ [l #a1 ↦ v] ->
  exists a2, x = [l #a2 ↦ v] /\ access_eq a1 a2.
Proof using.
  intros x V l a1 v H.
  dependent induction H.
  - invc_empty_entail H0.
    invc_atom_sentails H.
    eexists; split. 
    + reflexivity.
    + symmetry. assumption.
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
  - invc_empty_entail H0.
    invc_atom_sentails H.
    eexists; split. 
    + reflexivity.
    + assumption.
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

Lemma atom_sprop_separate_same_loc {comp loc}:
  forall l a1 a2 V1 (v1: V1) V2 (v2: V2) (x: sprop comp loc),
    atom_sprop_separate (l #a1 ↦ v1) x ->
    atom_sprop_separate (l #a2 ↦ v2) x.
Proof using.
  intros.
  induction x.
  - constructor.
  - invc H.
    constructor.
    + invc H2.
      constructor.
      assumption.
    + apply IHx.
      assumption.
Qed.

Lemma sentails_preserves_separation {comp loc}: forall x x' y: sprop comp loc,
  x ⊢ x' ->
  separate x y ->
  separate x' y.
Proof using.
  intros x x' y H Hsep.
  induction H.
  - assumption.
  - invc_atom_sentails H.
    invc Hsep.
    repeat constructor.
    + eapply atom_sprop_separate_same_loc.
      eassumption.
    + apply IHsentails.
      assumption.
  - eapply separate_perm.
    { eassumption. }
    { reflexivity. }
    apply IHsentails.
    eapply separate_perm.
    + symmetry. eassumption.
    + reflexivity.
    + assumption.
Qed.

Lemma sentails_preserves_atom_sprop_separation {comp loc}: 
  forall a a' (x: sprop comp loc),
    a ⊢ₐ a' ->
    atom_sprop_separate a x ->
    atom_sprop_separate a' x.
Proof using.
  intros a a' x Ha Hsep.
  apply separate_singleton.
  eapply sentails_preserves_separation.
  + eapply sentails_singleton.
    eassumption.
  + apply separate_singleton.
    assumption.
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

Lemma sentails_preserves_atom_sprop_separation_strong {comp loc}: 
  forall a a' (x x': sprop comp loc),
    a ⊢ₐ a' ->
    x ⊢ x' ->
    atom_sprop_separate a x ->
    atom_sprop_separate a' x'.
Proof using.
  intros a a' x x' Ha Hx Hsep.
  apply separate_singleton.
  eapply sentails_preserves_separation_strong.
  + eapply sentails_singleton.
    eassumption.
  + eassumption.
  + apply separate_singleton.
    assumption.
Qed.

Theorem sentails_wf_l {comp loc}: forall x y: sprop comp loc,
  x ⊢ y ->
  well_formed x.
Proof using.
  intros x y H.
  induction H.
  - constructor.
  - constructor; assumption.
  - eapply wf_perm; eassumption.
Qed.

Theorem sentails_wf_r {comp loc}: forall x y: sprop comp loc,
  x ⊢ y ->
  well_formed y.
Proof using.
  intros x y H.
  induction H.
  - constructor.
  - constructor. 
    + eapply sentails_preserves_atom_sprop_separation_strong; eassumption.
    + assumption.
  - eapply wf_perm; eassumption.
Qed.

Theorem sentails_wf_refl {comp loc}: forall x: sprop comp loc,
  well_formed x ->
  x ⊢ x.
Proof using.
  intros x H.
  induction H.
  - constructor.
  - apply head_intro; try assumption.
    reflexivity.
Qed.

Theorem sentails_sym {comp loc}: symmetric (sprop comp loc) sentails.
Proof using.
  unfold symmetric.
  intros x y H.
  induction H.
  - constructor.
  - apply head_intro.
    + symmetry. assumption.
    + assumption.
    + eapply sentails_preserves_atom_sprop_separation_strong; eassumption.
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

Lemma Permutation_cons_structure {A}: forall x (y z: list A),
  Permutation (x :: y) z ->
  exists z1 z2,
    z = z1 ++ x :: z2.
Proof using.
  intros x y z H.
  apply in_split.
  eapply Permutation_in.
  - eassumption.
  - left; reflexivity.
Qed. 

Theorem entails_cons_l_inv_strong {comp loc}: forall y ax,
  ax ⊢ y ->
    forall(a : sprop_atom comp loc) (x : sprop comp loc),
      Permutation (a :: x) ax ->
      exists (a' : sprop_atom comp loc) (x' : list (sprop_atom comp loc)),
        Permutation y (a' :: x') /\
        a ⊢ₐ a' /\
        x' ⊢ x'.
Proof using.
  intros y ax H a x Hperm; revert a x Hperm.
  induction H; intros.
  - symmetry in Hperm.
    apply Permutation_nil in Hperm; discriminate Hperm.
  - apply Permutation_cons_structure in Hperm.
    destruct exists Hperm z1 z2.
    destruct z1.  
    + simpl in Hperm.
      invc Hperm.
      exists x' y'.
      max_split.
      * reflexivity.
      * assumption.
      * apply sentails_wf_refl.
        eapply sentails_wf_r.
        eassumption.
    + simpl in Hperm.
      invc Hperm.
      specialize (IHsentails a (z1 ++ z2)).
      cut_hyp IHsentails.
      { apply Permutation_cons_app. reflexivity. }
      destruct exists IHsentails a' y'0.
      exists a'; exists (x' :: y'0).
      destruct IHsentails as [IHsentails1 [IHsentails2 IHsentails3]].
      max_split.
      * eapply perm_trans; [|eapply perm_swap].
        apply perm_skip.
        assumption.
      * assumption.
      (* This bullet needs to be cleaned *)
      * apply head_intro.
       -- reflexivity.
       -- assumption.
       -- eapply sentails_preserves_atom_sprop_separation; [eassumption|].
          eapply atom_sprop_separate_subperm.
          { eapply perm_trans.
            - apply (Permutation_cons_append y'0 a').
            - reflexivity. }
          eapply atom_sprop_separate_perm; [eassumption|].
          eapply sentails_preserves_atom_sprop_separation_strong.
         ++ reflexivity. 
         ++ apply H0.
         ++ assumption.
  - specialize (IHsentails a x0).
    cut_hyp IHsentails.
    { eapply Permutation_trans. 
      + eassumption.
      + symmetry. assumption. }
    destruct exists IHsentails a' y'0.
    destruct IHsentails as [IHsentails1 [IHsentails2 IHsentails3]].
    exists a'; exists y'0.
    max_split; try assumption.
    eapply Permutation_trans.
    + symmetry; eassumption.
    + eassumption. 
Qed.

Theorem entails_cons_l_inv {comp loc}: forall a (x y: sprop comp loc),
  a :: x ⊢ y ->
  exists a' x',
    Permutation y (a' :: x') /\ 
    a ⊢ₐ a' /\
    x' ⊢ x'.
Proof using.
  intros.
  eapply entails_cons_l_inv_strong.
  - eassumption.
  - reflexivity.
Qed.

Theorem entails_cons_r_inv_strong {comp loc}: forall b (x y y': sprop comp loc),
  Permutation y (b :: y') ->
  x ⊢ y ->
  exists a x',
    Permutation x (a :: x') /\ 
    a ⊢ₐ b /\
    x' ⊢ y'.
Proof using.
  intros b x y y' Hperm H; revert b y' Hperm.
  induction H; intros.
  - apply Permutation_nil in Hperm; discriminate Hperm.

  (* - assert (H2: exists x'y', Permutation (x' :: y') x'y') by (eexists; reflexivity);
      destruct exists H2 x'y'.
    assert (H3: exists by'0, Permutation (b :: y'0) by'0) by (eexists; reflexivity);
      destruct exists H3 by'0.
    rename Hperm into Hperm'.
    assert (Hperm: Permutation x'y' by'0).
    { eapply Permutation_trans.
      - symmetry. eassumption.
      - eapply Permutation_trans; [|eassumption].
        assumption. }
    clear Hperm'.
    induction Hperm.
    + admit. (* easy *)
    + exists x e *)
        

  (* - dependent induction Hperm.
    + exists x; exists y.
      max_split.
      * reflexivity.
      * assumption.
      * eapply sentails_perm.
       -- reflexivity.
       -- eassumption.
       -- assumption.
    + specialize (IHsentails b l).
      cut_hyp IHsentails by reflexivity.
      destruct exists IHsentails a y'.
      destruct IHsentails as [IHsentails1 [IHsentails2 IHsentails3]].
      exists a; exists (x :: y').
      max_split.
      * destruct y.
       -- apply Permutation_nil in IHsentails1; discriminate IHsentails1.
       -- eapply perm_trans.
        ++ apply perm_skip.
           eassumption.
        ++ eapply perm_swap.
      * assumption.
      * apply head_intro.
       -- assumption.
       -- assumption.
       -- eapply atom_sprop_separate_subperm; [|eassumption].
          eapply Permutation_trans; [eassumption|].
          apply Permutation_cons_append.
    + eapply IHHperm2; try eassumption.
       *)
           
  - admit.

  - specialize (IHsentails b y'0).
    cut_hyp IHsentails.
    { eapply Permutation_trans; eassumption. }
    destruct exists IHsentails a x'0.
    destruct IHsentails as [IHsentails1 [IHsentails2 IHsentails3]].
    exists a; exists x'0.
    max_split; try assumption.
    eapply Permutation_trans.
    + symmetry; eassumption.
    + eassumption. 
Admitted.

Theorem entails_cons_r_inv {comp loc}: forall a (x y: sprop comp loc),
  x ⊢ a :: y ->
  exists a' y',
    Permutation x (a' :: y') /\ 
    a' ⊢ₐ a /\
    y' ⊢ y.
Proof using.
  (* intros.
  invc H.
  - eexists; eexists; split. 
    + reflexivity.
    + split; assumption.
  - 
    induction H2.

    + apply Permutation_nil in H1; discriminate H1.
    +  *)

  intros a x y H.
  dependent induction H.
  - eexists; eexists; split. 
    + reflexivity.
    + split; assumption.
  - 


Theorem sentails_trans {comp loc}: transitive (sprop comp loc) sentails.
Proof using.
  unfold transitive.
  intros x y z Hxy Hyz. revert x Hxy.
  induction Hyz; intros.
  - assumption.
  - assert (H1: exists xy, Permutation (x :: y) xy) by (eexists; reflexivity).
    destruct exists H1 xy.
    eapply sentails_perm in Hxy; [|reflexivity|eassumption].
    induction Hxy.
    + symmetry in H1.
      apply Permutation_nil in H1.
      discriminate H1.
    + clear IHHxy.
      dependent induction H1.
      * apply head_intro. 
       -- eapply atom_sentails_trans; eassumption.
       -- apply IHHyz.
          eapply sentails_perm.
         ++ reflexivity.
         ++ symmetry; eassumption.
         ++ assumption.
       -- assumption.
      * 
    (* + apply head_intro.
      * eapply atom_sentails_trans; [eassumption|].
      * apply IHHyz.
        assumption.
      * e *)
    + eapply sentails_perm.
      { eassumption. }
      { reflexivity. }
      eapply IHHxy.
      eapply Permutation_trans.
      * eassumption.
      * symmetry. assumption.
  - 

    
    dependent induction Hxy.
    + apply head_intro.
      * eapply atom_sentails_trans; eassumption.
      * apply IHHyz.
        assumption.
      * eapply sentails_preserves_atom_sprop_separation_strong. 
       -- symmetry. eassumption.
       -- apply sentails_sym. eassumption.
       -- assumption.
    + eapply sentails_perm.
      { eassumption. }
      { reflexivity. }
      eapply IHHxy.
      * eassumption.
      * eassumption.
      * assumption.
      * assumption.
      * 



  - dependent induction Hxy.
    + apply head_intro.
      * eapply atom_sentails_trans; eassumption.
      * apply IHHyz.
        assumption.
      * eapply sentails_preserves_atom_sprop_separation_strong. 
       -- symmetry. eassumption.
       -- apply sentails_sym. eassumption.
       -- assumption.
    + eapply sentails_perm.
      { eassumption. }
      { reflexivity. }
      eapply IHHxy.
      * eassumption.
      * eassumption.
      * assumption.
      * assumption.
      * 

Admitted.

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