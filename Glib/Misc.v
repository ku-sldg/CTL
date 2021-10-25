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
  - enow eapply inj_pair1.
  - enow eapply inj_pair2_heq.
Qed.