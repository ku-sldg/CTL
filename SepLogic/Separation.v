Require Import SepLogic.Definition.
Require Import Coq.Relations.Relation_Definitions.

Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq.Program.Equality.
Require Import GeneralTactics.

(* Contradictory or redundant *)
Inductive overlap {comp loc}: sprop comp loc -> sprop comp loc -> Prop :=
  | overlap_val_at : forall l a1 a2 V1 (v1: V1) V2 (v2: V2),
      overlap (l;a1 ↦ v1) (l;a2 ↦ v2)
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

Fixpoint pure {comp loc} (s: sprop comp loc) : Prop :=
  match s with
  | val_at _ _ _ => False
  | sep_pure _ => True
  | sep_con s1 s2 => pure s1 /\ pure s2
  end.

Fixpoint spatial {comp loc} (s: sprop comp loc) : Prop :=
  match s with
  | val_at _ _ _ => True
  | sep_pure _ => False
  | sep_con s1 s2 => spatial s1 \/ spatial s2
  end.

Theorem pure_is_nonspatial {comp loc}: forall s: sprop comp loc,
  pure s <-> ~ spatial s.
Proof.
  intro s; induction s; simpl; try easy.
  split.
  - intros [H1 H2].
    applyc IHs1 in H1;
    applyc IHs2 in H2.
    intro Hcontra; destruct or Hcontra; auto.
  - intro H.
    split.
    + apply IHs1.
      auto.
    + apply IHs2.
      auto.
Qed.

Definition spatial_dec {comp loc} (s: sprop comp loc):
  {spatial s} + {~ spatial s}.
induction s; try solve [simpl; auto].
destruct multi IHs1 IHs2; try solve [simpl; auto].
simpl.
right.
intro H.
destruct or H; contradiction H.
Defined.

Theorem pure_is_separate {comp loc}: forall x y: sprop comp loc,
  pure x ->
  separate x y.
Proof using.
  intros x y H.
  apply pure_is_nonspatial in H.
  unfold separate, not in *.
  intros Hcontra.
  applyc H.
  induction Hcontra; simpl; auto.
Qed.


(* Inductive well_formed {comp loc} : sprop comp loc -> Prop :=
  | wf_val_at: forall V l a (v: V),
      well_formed (l;a ↦ v)
  | wf_sep_pure: forall P: Prop,
      well_formed ⟨P⟩
  | wf_sep_con:
      well_formed (a ** b)
  . *)

Fixpoint conjunct_list (l: list Prop) : Prop := 
  match l with 
  | [] => True
  | [P] => P
  | P :: t => P /\ conjunct_list t
  end.

Definition get_pure_props {comp loc} (s: sprop comp loc) : Prop :=
  let get_pure_props_list := fix get_pure_props_list s :=
    match s with 
    | _;_ ↦ _ => []
    | ⟨P⟩ => [P]
    | s1 ** s2 => get_pure_props_list s1 ++ get_pure_props_list s2
    end
  in 
    conjunct_list (get_pure_props_list s).

Fixpoint get_spatial_props {comp loc} (s: sprop comp loc) : sprop comp loc :=
  match s with 
  | _;_ ↦ _ => s 
  | ⟨_⟩ => ⟨⟩
  | a ** b =>
    match get_spatial_props a ** get_spatial_props b with
    | x ** ⟨_⟩ => x
    | ⟨_⟩ ** x => x
    | x  => x
    end
  end.

(* Fixpoint well_formed_no_assumptions {comp loc} (s: sprop comp loc) : Prop :=
  match s with 
  | val_at _ _ _ => True 
  | sep_pure _ => True
  | sep_con s1 s2 =>
      well_formed_no_assumptions s1 /\
      well_formed_no_assumptions s2 /\
      separate s1 s2
  end.

Definition well_formed {comp loc} (s: sprop comp loc) : Prop :=
  get_pure_props s -> well_formed_no_assumptions s. *)


Inductive well_formed {comp loc} : sprop comp loc -> Prop :=
  | wf_val_at: forall V l a (v: V),
      well_formed (l;a ↦ v)
  | wf_sep_pure: forall P: Prop,
      well_formed ⟨P⟩
  | wf_sep_con:
      a ** b ⊢ ⟨P⟩
      well_formed (a ** b)
  .


Definition well_formed {comp loc} (s: sprop comp loc) : Prop :=
  get_pure_props s -> well_formed_no_assumptions s. 
