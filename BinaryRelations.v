Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Lists.List.

Definition rel_singleton {A} (x y : A): relation A :=
  fun x' y' => x' = x /\ y' = y -> True.

(* Notation for reflexive transitive closures *)
Notation "R ^*" := (clos_refl_trans _ R) (at level 35).

Definition is_serial {A} (R: relation A) := forall a, exists b, R a b.
Definition serial A := {R: relation A | is_serial R}.

Definition is_serialT {A} (R: relation A) := forall a, {b | R a b}.
Definition serialT A := {R: relation A & is_serialT R}.

Definition reachable {A} (R: relation A) (l: list A) (b: A) := exists a, In a l /\ R^* a b.

Inductive steps : nat -> forall {A}, relation A -> relation A :=
  | steps_one   : forall {A} (R: relation A) x y,
      R x y -> steps 1 R x y
  | steps_multi : forall {A} n (R: relation A) x y z,
      steps n R x y -> R y x -> steps (S n) R x z.
