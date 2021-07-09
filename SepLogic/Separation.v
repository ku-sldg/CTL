Require Import SepLogic.Definition.
Require Import Coq.Relations.Relation_Definitions.

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
