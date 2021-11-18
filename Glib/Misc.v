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


Lemma exists_unique_exists : forall A (P: A -> Prop),
  (exists! a, P a) ->
  exists a, P a.
Proof using.
  tedious.
Qed.


Lemma forall_eq_intro : forall A (B C: A -> Type),
  B = C ->
  (forall a, B a) = (forall a, C a).
Proof using.
  follows intros * <-.
Qed.

Require Import FinFun.
Lemma injective_neg_defn : forall A B (f: A -> B),
  Injective f =
  forall x y: A, x <> y -> f x <> f y.
Proof using.
  intros *.
  extensionality.
  after split.
  intros inj_neg x y f_eq.
  contradict goal contra.
  follows eapply inj_neg.
Qed.


(* any type *)

Definition any : Type := Σ t: Type, t.
Definition box {t} (x: t) : any := existT (λ x, x) t x.

Definition unbox {A} (a: any) (elim: forall t, t -> A) : A :=
  elim (projT1 a) (projT2 a).

Definition any_destr (a: any) : Σ t (v: t), a = box v.
  follows destruct a.
Defined.

Lemma any_canonical : forall a: any,
  exists t (v: t), a = box v.
Proof using.
  follows destruct a.
Qed.

Lemma box_eq_homo : forall t (v v': t),
  box v = box v' ->
  v = v'.
Proof using.
  intros * H.
  follows inject H.
Qed.

Lemma box_eq_hetero : forall t (v: t) t' (v': t'),
  box v = box v' ->
  v ~= v'.
Proof using.
  intros * H.
  follows inject H.
Qed.