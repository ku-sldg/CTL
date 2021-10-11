Require Import Notation.
Require Import Axioms.
Require Import GeneralTactics.
Require Import Quotient.

Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.

Import ListNotations.
Open Scope list_scope.


Section Fin_set.

Context {A: Type}.

Definition fin_set_eq (s1 s2: list A) := forall a, In a s1 <-> In a s2.

Theorem fin_set_eq_is_equiv : Equivalence fin_set_eq.
Proof using.
  split; try easy.
  intros x y z Hxy Hyz a.
  split; intro Hin.
  - apply Hyz.
    now apply Hxy.
  - apply Hxy.
    now apply Hyz.
Qed.

Instance Equivalence_fin_set_eq : Equivalence fin_set_eq := fin_set_eq_is_equiv.

Definition fin_set := list A / fin_set_eq.

Definition empty_set : fin_set :=
  qclass _ [].

Definition singleton_set a : fin_set :=
  qclass _ [a].

Definition union : fin_set -> fin_set -> fin_set.
  refine (liftQ2 _ (@app A) _).
Proof using.
  intros x x' y y' Heq Heq' a. 
  split; intro Hin.
  - apply in_app_iff.
    apply in_app_iff in Hin as [Hin|Hin].
    + left. now apply Heq.
    + right. now apply Heq'.
  - apply in_app_iff.
    apply in_app_iff in Hin as [Hin|Hin].
    + left. now apply Heq.
    + right. now apply Heq'.
Qed.

Definition 
 
End Fin_set.