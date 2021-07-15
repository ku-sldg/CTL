Require Import SepLogic.Definition.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.List.
Import ListNotations.
Require Coq.Sorting.Permutation.
Import Permutation.

Require Setoid.
Require Import Coq.Program.Equality.
Require Import GeneralTactics.

Theorem neq_sym {A}: forall x y: A,
  x <> y ->
  y <> x.
Proof using.
  intros x y H ->.
  applyc H.
  reflexivity.
Qed.

Inductive atom_separate {comp loc}
  : sprop_atom comp loc -> sprop_atom comp loc -> Prop :=
  | separate_val_at : forall (l1 l2: loc) a1 a2 V1 (v1: V1) V2 (v2: V2),
      l1 <> l2 ->
      atom_separate (l1 #a1 ↦ v1) (l2 #a2 ↦ v2).

Theorem atom_separate_sym {comp loc}:
  symmetric (sprop_atom comp loc) atom_separate.
Proof using.
  intros x y H.
  invc H.
  constructor.
  apply neq_sym.
  assumption.
Qed.

Add Parametric Relation (comp loc: Set)
  : (sprop_atom comp loc) (@atom_separate comp loc)
  symmetry proved by (@atom_separate_sym comp loc)
  as atom_separate_rel.

Definition atom_sprop_separate {comp loc} (s: sprop_atom comp loc)
  : sprop comp loc -> Prop:=
  Forall (atom_separate s).

Definition Forall_prod {A B} (P: A -> B -> Prop) (la: list A) (lb: list B) :=
  (* Forall (uncurry P) (list_prod l1 l2). *)
  Forall (fun a => Forall (P a) lb) la.

Theorem Forall_prod_nil_l {A B}: forall (P: A -> B -> Prop) lb,
  Forall_prod P [] lb.
Proof using.
  intros P lb.
  constructor.
Qed.

Theorem Forall_prod_nil_r {A B}: forall (P: A -> B -> Prop) la,
  Forall_prod P la [].
Proof using.
  intros P la.
  destruct la; repeat constructor.
  induction la; repeat constructor.
  assumption.
Qed.

Lemma Forall_prod_head_l {A B}: forall (P: A -> B -> Prop) a la lb,
  Forall (P a) lb ->
  Forall_prod P la lb ->
  Forall_prod P (a :: la) lb.
Proof using.
  intros P a la lb Hforall Hprod.
  constructor; assumption.
Qed.

Lemma Forall_singleton {A}: forall (P: A -> Prop) a,
  P a <-> Forall P [a].
Proof using.
  intros P a.
  split; intro H.
  - repeat constructor.
    assumption.
  - invc H.
    assumption.
Qed.

Lemma Forall_prod_singleton_l {A B}: forall (P: A -> B -> Prop) a lb,
  Forall (P a) lb ->
  Forall_prod P [a] lb.
Proof using.
  intros P a lb H. 
  repeat constructor.
  assumption.
Qed.

Lemma Forall_prod_singleton_r {A B}: forall (P: A -> B -> Prop) la b,
  Forall (fun a => P a b) la ->
  Forall_prod P la [b].
Proof using.
  intros P la b H.
  destruct la.
  - apply Forall_prod_nil_l.
  - constructor.
    + constructor.
      * invc H.
        assumption.
      * constructor.
    + invc H.
      clear - H3.
      induction la.
      * constructor.
      * invc H3.
        repeat constructor.
       -- assumption.
       -- apply IHla. 
          assumption.
Qed.

Lemma Forall_prod_head_r {A B}: forall (P: A -> B -> Prop) la b lb,
  Forall (fun a => P a b) la ->
  Forall_prod P la lb ->
  Forall_prod P la (b :: lb).
Proof using.
  intros P la b lb Hforall Hprod.
  induction la; repeat constructor.
  - invc Hforall.
    assumption.
  - invc Hprod.
    assumption.
  - apply IHla.
    + invc Hforall.
      assumption.
    + invc Hprod.
      assumption.
Qed.

Theorem Forall_prod_sym {A}: forall (P: A -> A -> Prop),
  symmetric A P ->
  symmetric (list A) (Forall_prod P).
Proof using.
  intros P Hsym x y H.
  induction H.
  - apply Forall_prod_nil_r.
  - apply Forall_prod_head_r.
    + clear - Hsym H.
      induction y; repeat constructor.
      * invc H.
        apply Hsym.
        assumption.
      * apply IHy.
        invc H.
        assumption.
    + assumption.
Qed.

Definition separate {comp loc}: sprop comp loc -> sprop comp loc -> Prop :=
  Forall_prod atom_separate.

Theorem separate_sym {comp loc}: symmetric (sprop comp loc) separate.
Proof using.
  intros x y H.
  apply Forall_prod_sym.
  - apply atom_separate_sym.
  - assumption.
Qed. 

Add Parametric Relation (comp loc: Set)
  : (sprop comp loc) (@separate comp loc)
  symmetry proved by (@separate_sym comp loc)
  as separate_rel.

Lemma separate_empty_r {comp loc}: forall s: sprop comp loc,
  separate s ⟨⟩.
Proof using.
  intro s.
  apply Forall_prod_nil_r.
Qed.

Lemma separate_empty_l {comp loc}: forall s: sprop comp loc,
  separate ⟨⟩ s.
Proof using.
  intro s.
  symmetry.
  apply separate_empty_r.
Qed.

Inductive well_formed {comp loc}: sprop comp loc -> Prop :=
  | wf_empty : 
      well_formed ⟨⟩
  | wf_cons : forall h t,
      atom_sprop_separate h t ->
      well_formed t ->
      well_formed (h :: t).

Lemma concat_eq_empty {A}: forall x y: list A,
  x ++ y = [] -> 
  x = [] /\ y = [].
Proof using.
  intros x y H.
  destruct x.
  - split. 
    + reflexivity.
    + simpl in H.
      assumption.
  - simpl in H.
    discriminate H.
Qed.

Theorem Forall_perm {A}: forall (P: A -> Prop) (x y: list A),
  Permutation x y ->
  Forall P x ->
  Forall P y.
Proof using.
  intros a x y Hperm; revert a.
  induction Hperm; intros a H.
  - assumption.
  - invc H.
    constructor.
    + assumption.
    + apply IHHperm.
      assumption.
  - invc H.
    invc H3.
    repeat constructor; assumption.
  - apply IHHperm2.
    apply IHHperm1.
    assumption.
Qed.

Theorem Forall_sublist {A}: forall (P: A -> Prop) (x y: list A),
  Forall P (x ++ y) ->
  Forall P x.
Proof using.
  intros P x y HForall.
  induction x.
  - constructor.
  - simpl in HForall.
    invc HForall.
    specializec IHx H2.
    constructor; assumption.
Qed.

Lemma Forall_subperm {A}: forall (P: A -> Prop) (x y z: list A),
  Permutation x (y ++ z) ->
  Forall P x ->
  Forall P y.
Proof using.
  intros P x y z Hperm Hx.
  eapply Forall_sublist.
  eapply Forall_perm; eassumption.
Qed.

Theorem atom_sprop_separate_perm {comp loc}: forall a (x y: sprop comp loc),
  Permutation x y ->
  atom_sprop_separate a x ->
  atom_sprop_separate a y.
Proof using. 
  intros.
  eapply Forall_perm; eassumption.
Qed.

Theorem atom_sprop_separate_sublist {comp loc}: forall a (x y: sprop comp loc),
  atom_sprop_separate a (x ++ y) ->
  atom_sprop_separate a x.
Proof using. 
  intros.
  eapply Forall_sublist; eassumption.
Qed.

Theorem atom_sprop_separate_subperm {comp loc}: forall a (x y z: sprop comp loc),
  Permutation x (y ++ z) ->
  atom_sprop_separate a x ->
  atom_sprop_separate a y.
Proof using. 
  intros.
  eapply Forall_subperm; eassumption.
Qed.

Theorem atom_sprop_separate_sublist' {comp loc}: forall a (x y: sprop comp loc),
  atom_sprop_separate a (x ++ y) ->
  atom_sprop_separate a y.
Proof using. 
  intros.
  eapply atom_sprop_separate_subperm; [|eassumption].
  apply Permutation_app_comm.
Qed.

Theorem Forall_prod_perm {A B}: forall (P: A -> B -> Prop) x x' y y',
  Permutation x x' ->
  Permutation y y' ->
  Forall_prod P x y ->
  Forall_prod P x' y'.
Proof using.
  intros P x x' y y' Hperm. revert P y y'.
  induction Hperm; intros.
  - constructor.
  - invc H0.
    constructor.
    + eapply Forall_perm; eassumption.
    + eapply IHHperm; eassumption.
  - invc H0.
    invc H4.
    repeat constructor.
    + eapply Forall_perm; eassumption.
    + eapply Forall_perm; eassumption.
    + induction l.
      * constructor.
      * invc H5.
        constructor.
       -- eapply Forall_perm; eassumption.
       -- apply IHl. assumption.
  - eapply IHHperm2; [eassumption|].
    eapply IHHperm1.
    + reflexivity.
    + assumption.
Qed.

Theorem Forall_prod_sublist {A B}: forall (P: A -> B -> Prop) x x' y y',
  Forall_prod P (x ++ x') (y ++ y') ->
  Forall_prod P x y.
Proof using.
  intros P x; revert P.
  induction x; intros P x' y y' H.
  - constructor.
  - simpl in H.
    invc H.
    constructor.
    + eapply Forall_sublist. eassumption.
    + eapply IHx. eassumption.
Qed. 

Theorem Forall_prod_subperm {A B}: 
  forall (P: A -> B -> Prop) x x' x'' y y' y'',
    Permutation x (x' ++ x'') ->
    Permutation y (y' ++ y'') ->
    Forall_prod P x y ->
    Forall_prod P x' y'.
Proof using.
  intros.
  eapply Forall_prod_sublist.
  eapply Forall_prod_perm; eassumption.
Qed. 

Theorem separate_perm {comp loc}: forall x x' y y': sprop comp loc,
  Permutation x x' ->
  Permutation y y' ->
  separate x y ->
  separate x' y'.
Proof using.
  intros.
  eapply Forall_prod_perm; eassumption.
Qed. 

Theorem separate_sublist {comp loc}: forall x x' y y': sprop comp loc,
  separate (x ++ x') (y ++ y') ->
  separate x y.
Proof using.
  intros.
  eapply Forall_prod_sublist.
  eassumption.
Qed.
 
Theorem separate_subperm {comp loc}: 
  forall x x' x'' y y' y'': sprop comp loc,
    Permutation x (x' ++ x'') ->
    Permutation y (y' ++ y'') ->
    separate x y ->
    separate x' y'.
Proof using.
  intros.
  eapply Forall_prod_subperm; eassumption.
Qed.

Lemma separate_singleton {comp loc}: forall x (y: sprop comp loc),
  separate [x] y <-> atom_sprop_separate x y.
Proof.
  intros x y.
  split; intro H.
  - invc H.
    assumption.
  - repeat constructor.
    assumption.
Qed.

Theorem wf_perm {comp loc}: forall x y: sprop comp loc,
  Permutation x y ->
  well_formed x ->
  well_formed y.
Proof using.
  intros x y Hperm H.
  induction Hperm.
  - assumption.
  - invc H.
    constructor.
    + eapply atom_sprop_separate_perm; eassumption.
    + apply IHHperm. assumption.
  - invc H.
    invc H2.
    invc H3.
    repeat constructor; try assumption.
    symmetry.
    assumption.
  - apply IHHperm2.
    apply IHHperm1.
    assumption.
Qed.

Theorem wf_subset {comp loc}: forall x y: sprop comp loc,
  well_formed (x ** y) ->
  well_formed x.
Proof using.
  intro x; induction x; intros y H.
  - constructor.
  - simpl in H.
    invc H.
    constructor.
    + eapply atom_sprop_separate_sublist.
      eassumption.
    + eapply IHx.
      eassumption.
Qed. 

Theorem wf_subperm {comp loc}: forall x y z: sprop comp loc,
  Permutation x (y ** z) ->
  well_formed x ->
  well_formed y.
Proof using.
  intros.
  eapply wf_subset.
  eapply wf_perm; eassumption.
Qed.

Theorem wf_subset' {comp loc}: forall x y: sprop comp loc,
  well_formed (x ** y) ->
  well_formed y.
Proof using.
  intros.
  eapply wf_subperm; [|eassumption].
  eapply Permutation_app_comm.
Qed. 

Theorem wf_sep_con_separate {comp loc}: forall x y: sprop comp loc,
  well_formed (x ** y) ->
  separate x y.
Proof using.
  intros x y H.
  induction x.
  - apply separate_empty_l.
  - simpl in H.
    invc H.
    specialize (IHx H3).
    constructor.
    + eapply atom_sprop_separate_sublist'.
      eassumption.
    + assumption.
Qed.
 
Theorem wf_sep_con_inv {comp loc}: forall x y: sprop comp loc,
  well_formed (x ** y) ->
  well_formed x /\ 
  well_formed y /\ 
  separate x y.
Proof using.
  intros x y H.
  max_split;
  [ eapply wf_subset
  | eapply wf_subset'
  | eapply wf_sep_con_separate];
  eassumption.
Qed.