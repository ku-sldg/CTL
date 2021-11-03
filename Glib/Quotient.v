Require Import Notation.
Require Import Axioms.
Require Import GeneralTactics.

Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Program.Basics.

(* Require Export Coq.Sets.Ensembles. *)

Open Scope program_scope.


(* This representation of equivalent-class predicates is inspired by 
   the presentation in the HoTT book (section 6.10)
 *)

Section Quotient.

Context {A} (R: relation A) {equivR: Equivalence R}.

Notation "x ∼ y" := (R x y) (at level 70, no associativity).

Definition In {U} A x := In U A x.


Definition equiv_class (e: Ensemble A) :=
  exists x, forall y, x ∼ y <-> In e y.

Theorem ec_all_in_related : forall e,
  equiv_class e ->
  forall x y, In e x -> In e y -> x ∼ y.
Proof using A R equivR.
  intros * H * Hx Hy.
  destruct H as [a H].
  transitivity a.
  - symmetry.
    now apply H.
  - now apply H.
Qed.

Theorem ec_all_related_in : forall e,
  equiv_class e ->
  forall x y, x ∼ y -> In e x -> In e y.
Proof using A R equivR.
  intros * H * Heq Hx.
  destruct H as [a H].
  apply H.
  transitivity x.
  - now apply H.
  - assumption.
Qed.

Definition quotient := {e | equiv_class e}.

Definition class_to_ensemble (c: quotient) : Ensemble A := proj1_sig c.
Coercion class_to_ensemble : quotient >-> Ensemble.

Definition qclass (a: A) : quotient.
  (* refine (exist _ (λ x, a ∼ x) _). *)
  refine (exist _ (R a) _).
Proof.
  now exists a.
Defined.

Theorem in_qclass : forall a,
  In (qclass a) a.
Proof using A R equivR.
  intros *.
  cbn.
  reflexivity.
Qed.

Theorem qclass_eq : forall a (c: quotient),
  In c a -> 
  c = qclass a.
Proof using A R equivR.
  intros * Hin.
  destruct c as [e p].
  simpl in Hin.
  apply exist_eq.
  extensionality x.
  extensionality H.
  - follows eapply ec_all_in_related.
  - follows eapply ec_all_related_in.
Qed.

Lemma in_some_class : forall a,
  exists c: quotient, In c a.
Proof using A R equivR.
  intros *.
  exists (qclass a).
  apply in_qclass.
Qed.

Theorem class_nonempty : forall c: quotient,
  exists x, In c x.
Proof using A R equivR.
  intros *.
  destruct c as (? & a & p).
  exists a.
  apply p.
  reflexivity.
Qed.

Lemma classes_partition : forall a,
  exists! c: quotient, In c a.
Proof using A R equivR.
  intros *.
  exists (qclass a).
  split.
  - apply in_qclass.
  - intros * Hin.
    symmetry.
    now apply qclass_eq.
Qed.

Lemma class_unique : forall (c1 c2: quotient) a,
  In c1 a ->
  In c2 a ->
  c1 = c2.
Proof using A R equivR.
  intros * Hin Hin'.
  apply qclass_eq in Hin, Hin'.
  now subst.
Qed.

Lemma classes_disjoint : forall (c1 c2: quotient) a,
  c1 <> c2 ->
  In c1 a -> ~ In c2 a.
Proof using A R equivR.
  intros * Hneq Hin Hin'.
  applyc Hneq.
  follows eapply class_unique.
Qed.

Theorem qclass_surjective : Surjective qclass.
Proof using A R equivR.
  intros c.
  destruct (class_nonempty c) as [a ?].
  exists a.
  symmetry.
  now apply qclass_eq.
Qed.

Theorem qclass_spec : forall x y,
  (qclass x = qclass y) = (x ∼ y).
Proof using A R equivR.
  intros *.
  extensionality H.
  - apply eq_sig_fst in H.
    symmetry.
    pattern x.
    induction H.
    reflexivity.
  - apply exist_eq.
    extensionality a.
    extensionality H'.
    + now transitivity x.
    + now transitivity y.
Qed.

Definition quotient_rect :
  forall (P: quotient -> Type),
    (forall Q p, P (exist _ Q p)) ->
    forall c, P c.
Proof using.
  intros * H *.
  destruct c.
  apply H.
Defined.

Definition quotient_rec :
  forall (P: quotient -> Set),
    (forall Q p, P (exist _ Q p)) ->
    forall c, P c
  := quotient_rect.

(* Our inductive principle is more pleasant, because we can reflect arbitrary 
   classes to the canonical qclass representation
 *)
Theorem quotient_ind :
  forall (P: quotient -> Prop),
    (forall a, P (qclass a)) ->
    forall c, P c.
Proof using A R equivR.
  intros * H *.
  destruct c as [Q p].
  eta.
  destruct (qclass_surjective (exist _ Q p)) as [? <-].
  assumption!.
Qed.

Definition respects_equiv (f: A -> A) :=
  forall x y, x ∼ y -> (f x) ∼ (f y).

Definition respects_equiv2 (f: A -> A -> A) :=
  forall x x' y y', x ∼ x' -> y ∼ y' -> (f x y) ∼ (f x' y').

Definition liftQ (f: A -> A) (re: respects_equiv f) : quotient -> quotient.
Proof using A R equivR.
  intros [P p].
  refine (exist _ (λ a, ∃ x, (f x) ∼ a /\ P x) _).
  destruct p as [a p].
  exists (f a).
  intros *.
  split; intro H.
  - exists a.
    split.
    + assumption.
    + apply p.
      reflexivity.
  - destruct H as (? & <- & ?).
    apply re.
    now apply p.
Defined.
 
Theorem liftQ_qclass : forall (f: A -> A) (re: respects_equiv f) a,
  liftQ f re (qclass a) = qclass (f a).
Proof using.
  intros *.
  apply exist_eq'.
  simpl.
  extensionality x.
  extensionality; split.
  - intros (? & <- & ?).
    now apply re.
  - intros ?.
    now exists a.
Qed.

Definition liftQ2 (f: A -> A -> A) (re: respects_equiv2 f) :
  quotient -> quotient -> quotient.
Proof using A R equivR.
  intros [P p] [Q q].
  refine (exist _ (λ a, ∃ x y, (f x y) ∼ a /\ P x /\ Q y) _).
  destruct p as [a p], q as [a' q].
  exists (f a a').
  intros *.
  split; intro H.
  - exists a a'.
    max split.
    + assumption.
    + now apply p.
    + now apply q.
  - destruct H as (? & ? & <- & ? & ?).
    apply re.
    + now apply p.
    + now apply q.
Defined.

Theorem liftQ2_qclass : forall (f: A -> A -> A) (re: respects_equiv2 f) x y,
  liftQ2 f re (qclass x) (qclass y) = qclass (f x y).
Proof using.
  intros *.
  apply exist_eq'.
  simpl.
  extensionality a.
  extensionality; split.
  - intros (x' & y' & <- & H & H').
    now apply re.
  - intros ?.
    now exists x y.
Qed.

End Quotient.

Arguments quotient A R : clear implicits.
Notation "A / R" := (quotient A R) : type_scope.

Notation "f 'respects' R"  := (respects_equiv  R f) (at level 50).
Notation "f 'respects2' R" := (respects_equiv2 R f) (at level 50).

Close Scope program_scope.