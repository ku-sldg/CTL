Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalFacts.

Require Import Notation.
Require Import GeneralTactics.
Require Import UipFacts.

Require Export Coq.Logic.Classical.


Tactic Notation "destruct" "classic" uconstr(c) "as" ident(H) :=
  destruct (classic c) as [H|H].

Tactic Notation "destruct" "classic" uconstr(c) :=
  let x := fresh in
  destruct classic c as x.

Tactic Notation "contradict" "goal" ident(H) :=
  apply NNPP; intro H.

Tactic Notation "contradict" "goal" :=
  let contra := fresh "contra" in
  apply NNPP; intro contra.


(* Consequences of classical LEM *)


(* Proof irrelevance *)

Lemma proof_irrelevance : forall (P: Prop) (p1 p2: P),
  p1 = p2.
Proof using.
  intros *.
  apply proof_irrelevance_cci.
  exact classic.
Qed.

Lemma exist_eq : forall A (P: A -> Prop) x y p q,
  x = y -> 
  exist P x p = exist P y q.
Proof using.
  intros * ->.
  now rewrite (proof_irrelevance _ p q).
Qed.

Lemma exist_eq' : forall A (P: A -> Prop) (x y: {a | P a}),
  proj1_sig x = proj1_sig y -> 
  x = y.
Proof using.
  intros *.
  destruct x, y.
  apply exist_eq.
Qed.

Lemma exist_neq : forall A (P: A -> Prop) x y p q,
  exist P x p <> exist P y q ->
  x <> y.
Proof using.
  intros * Hneq ?.
  apply Hneq.
  now apply exist_eq.
Qed.

Lemma exist_neq' : forall A (P: A -> Prop) (x y: {a | P a}),
  x <> y ->
  proj1_sig x <> proj1_sig y.
Proof using.
  intros *.
  destruct x, y.
  apply exist_neq.
Qed.

Lemma exists_prop_unique : forall (A: Prop) (P: A -> Prop),
  (exists a, P a) <-> exists! a, P a.
Proof using.
  tedious using proof_irrelevance.
Qed.

Lemma exists_prop_forall : forall (A: Prop) (P: A -> Prop),
  (exists a, P a) -> forall a, P a.
Proof using.
  intros * [a ?].
  intro a'.
  follows replace a' with a by apply proof_irrelevance.
Qed.


(* UIP *)

Module ClassicalUipImpl.
Lemma uip_refl : forall A (x: A) (h: x = x), h = eq_refl x.
Proof using.
  exact (proof_irrelevance__uip_refl proof_irrelevance).
Qed.
End ClassicalUipImpl.

Module UipTheory := UipTheory(ClassicalUipImpl).
Export UipTheory.

#[global]
Hint Resolve inj_pair2 inj_pairT2: eqdep.


Lemma JMproof_irrelevance : forall (P Q: Prop) (p: P) (q: Q),
  P = Q ->
  p ~=~ q.
Proof using.
  intros * <-.
  apply eq_JMeq.
  apply proof_irrelevance.
Qed.
