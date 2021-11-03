Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.

Theorem inj_pair1 : forall A (B: A -> Type) (a a': A) (b: B a) (b': B a'),
  ⟨a, b⟩ = ⟨a', b'⟩ -> a = a'.
Proof using.
  intros * H.
  now inv H.
Qed.

Theorem inj_pair2_heq : forall A (B: A -> Type) (a a': A) (b: B a) (b': B a'),
  ⟨a, b⟩ = ⟨a', b'⟩ -> b ~= b'.
Proof using.
  intros * H.
  now inv H.
Qed.

Theorem inj_pair : forall A (B: A -> Type) (a a': A) (b: B a) (b': B a'),
  ⟨a, b⟩ = ⟨a', b'⟩ -> a = a' /\ b ~= b'.
Proof using.
  intros * H.
  split.
  - follows eapply inj_pair1.
  - follows eapply inj_pair2_heq.
Qed.

Lemma forall_eq_intro : forall A (B C: A -> Type),
  B = C ->
  (forall a, B a) = (forall a, C a).
Proof using.
  follows intros * <-.
Qed.

Require Import FinFun.
Lemma injective_neq : forall A B (f: A -> B) (x y: A),
  Injective f -> 
  x <> y ->
  f x <> f y.
Proof using.
  intros * f_inj Hneq Hcontra.
  follows apply f_inj in Hcontra.
Qed.