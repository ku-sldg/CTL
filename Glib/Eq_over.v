Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.

Import EqNotations.

(* This definition is taken from a snippet provided by Hugo Herbelin in a 
   conversation on the Coq mailing list
 *)

Reserved Notation "x =_{ H } y" (at level 70, format "x  =_{ H }  y").
Inductive eq_over {A} (x:A) : forall {B} (y:B), A = B -> Prop :=
  | eq_over_refl : x =_{eq_refl A} x 
where "x =_{ H } y" := (eq_over x y H).


Definition eq_inv {X} {a b: X} : (a = b) -> (b = a).
  now intros [].
Defined.

Lemma eq_inv_inv {X} {a b: X} : forall (h: a = b),
  eq_inv (eq_inv h) = h.
Proof using.
  intros *.
  follows destruct h.
Qed.


Definition eq_comp {X} {a b c: X} : (a = b) -> (b = c) -> (a = c).
  now intros [].
Defined.

Lemma eq_comp_assoc {X} {a b c d: X} :
  forall (h: a = b) (j: b = c) (k: c = d),
    eq_comp h (eq_comp j k) = eq_comp (eq_comp h j) k.
Proof using.
  follows repeat intros <-.
Qed.

Lemma eq_inv_distr_comp {X} {a b c: X} : forall (h: a = b) (j: b = c),
  eq_inv (eq_comp h j) = eq_comp (eq_inv j) (eq_inv h).
Proof using.
  follows repeat intros <-.
Qed.


Theorem eq_over_rew {A B} : forall (h: A = B) (a: A) (b: B), 
  a =_{h} b <-> rew h in a = b.
Proof using.
  tedious.
Qed.

Theorem eq_over_eq_refl {A} : forall (a a': A), 
  a =_{eq_refl A} a' <-> a = a'.
Proof using.
  apply eq_over_rew.
Qed.

(* Uses UIP *)
Theorem eq_over_homo {A} : forall (h: A = A) (a a': A), 
  a =_{h} a' <-> a = a'.
Proof using.
  intros *.
  rewrite (uip_refl _ _ h).
  apply eq_over_eq_refl.
Qed.


Theorem eq_over_sym {A B}: forall (h: A = B) (a: A) (b: B),
  a =_{h} b -> 
  b =_{eq_inv h} a.
Proof using.
  follows intros * <-.
Qed.

Theorem eq_over_trans {A B C}: forall (h: A = B) (j: B = C) (a: A) (b: B) (c: C),
  a =_{h} b -> 
  b =_{j} c ->
  a =_{eq_comp h j} c.
Proof using.
  intros <- <-.
  intros * Hh Hj.
  cbn.
  apply eq_over_eq_refl in Hh as <-, Hj as <-.
  constructor.
Qed.
