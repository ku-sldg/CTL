Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Lists.List.

Require Import Setoid.
Require Import Tactics.General.

Definition rel_singleton {A} (x y : A): relation A :=
  fun x' y' => x' = x /\ y' = y -> True.

(* This definition of reflexive transitive closure for the convenient inductive structure *)
(* Notation "R ^*" := (clos_refl_trans_n1 _ R) (at level 35, format "R ^*"). *)
Notation "R ^*" := (clos_refl_trans_n1 _ R) (at level 5, format "R ^*").

Lemma rtc_trans {A}: forall R: relation A,
  transitive A R^*.
Proof.
  intros R x y z Hxy Hyz.
  induction Hyz.
  - assumption.
  - econstructor; eassumption.
Qed.

Lemma rtc_alt_trans {A}: forall (R: relation A) a b c,
  R a b -> R^* b c -> R^* a c.
Proof.
  intros R a b c Hab Hbc.
  eapply rtc_trans; [|eassumption].
  econstructor.
  - eassumption.
  - constructor.
Qed.

Add Parametric Relation (A: Type) (R: relation A): A (clos_refl_trans_n1 A R)
  reflexivity  proved by (rtn1_refl A R)
  transitivity proved by (rtc_trans R)
  as rtc_rel.


Lemma rtc_1n_n1_equiv {A}: forall (R: relation A) a b,
  clos_refl_trans_1n _ R a b <-> R^* a b.
Proof.
  (* intros R a b H1n.
  induction H1n.
  - constructor.
  - induction IHH1n.
    + econstructor.
      * eassumption.
      * constructor.
    + econstructor.
      * eassumption.
      * apply IHIHH1n. *)
Admitted.

Definition is_serial {A} (R: relation A) := forall a, exists b, R a b.
Definition serial A := {R: relation A | is_serial R}.

(* Definition is_serialT {A} (R: relation A) := forall a, {b | R a b}. *)
(* Definition serialT A := {R: relation A & is_serialT R}. *)
Definition serial_witness {A} (R: relation A) := forall a, {b | R a b}.
Definition serialT A := {R: relation A & serial_witness R}.

Definition reachable {A} (R: relation A) (l: list A) (b: A) := exists a, In a l /\ R^* a b.

Definition is_serial_from {A} (R: relation A) s :=
  forall s', R^* s s' -> exists s'', R s' s''.

Definition serial_from_witness {A} (R: relation A) s :=
  forall s', R^* s s' -> {s''| R s' s''}.

Inductive steps : nat -> forall {A}, relation A -> relation A :=
  | steps_one   : forall {A} (R: relation A) x y,
      R x y -> steps 1 R x y
  | steps_multi : forall {A} n (R: relation A) x y z,
      steps n R x y -> R y x -> steps (S n) R x z.
