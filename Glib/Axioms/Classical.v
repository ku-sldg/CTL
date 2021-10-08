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

Tactic Notation "contradict" "goal" hyp(H) :=
  apply NNPP; intro H.

Tactic Notation "contradict" "goal" :=
  let contra := fresh "contra" in
  apply NNPP; intro contra.


(* Consequences of classical LEM *)

Lemma proof_irrelevance : forall (P: Prop) (p1 p2: P),
  p1 = p2.
Proof using.
  intros *.
  apply proof_irrelevance_cci.
  exact classic.
Qed.

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