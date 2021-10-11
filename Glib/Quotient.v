Require Import Notation.
Require Import Axioms.
Require Import GeneralTactics.

Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Basics.

Open Scope program_scope.


Section Quotient.

Context {A} (R: relation A) {equivR: Equivalence R}.

Notation "x ~ y" := (R x y) (at level 70, no associativity).


Definition all_sat_related (P: A -> Prop) :=
  forall x y, P x -> P y -> x ~ y.

Definition all_related_sat (P: A -> Prop) :=
  forall x y, x ~ y -> P x -> P y.

Definition ex_sat (P: A -> Prop) := 
  exists x, P x.

(* P corresponds to a nonempty equivalence class *)
Definition describes_equiv_class (P: A -> Prop) :=
  all_sat_related P /\
  all_related_sat P /\ 
  ex_sat P.

Definition quotient := {P | describes_equiv_class P}.

Definition qclass (a: A) : quotient.
  refine (exist _ (λ x, a ~ x) _).
Proof.
  max split.
  - intros ? ? -> ->. 
    reflexivity.
  - intros ? ? -> ->.
    reflexivity.
  - exists a.
    reflexivity.
Defined.

Definition in_class a (c: quotient) : Prop := 
  match c with 
  | exist _ P _ => P a
  end.

Theorem in_qclass : forall a,
  in_class a (qclass a).
Proof using.
  intros *.
  simpl.
  reflexivity.
Qed.

Theorem qclass_eq : forall a c,
  in_class a c -> 
  c = qclass a.
Proof using.
  intros * Hin.
  destruct c as [P p].
  simpl in Hin.
  inversion p as (Hall & Honly & Hnonempty).
  apply exist_eq.
  extensionality.
  - intros *.
    extensionality H.
    + now apply Hall.
    + enow eapply Honly.
Qed.

Lemma in_some_class : forall a,
  exists c, in_class a c.
Proof using A R equivR.
  intros *.
  exists (qclass a).
  apply in_qclass.
Qed.

Theorem class_nonempty : forall c,
  exists x, in_class x c.
Proof using.
  intros *.
  destruct c as [P p].
  inversion p as (_ & _ & [a ?]).
  now exists a.
Qed.

Lemma classes_partition : forall a,
  exists! c, in_class a c.
Proof using A R equivR.
  intros *.
  exists (qclass a).
  split.
  - apply in_qclass.
  - intros * Hin.
    symmetry.
    now apply qclass_eq.
Qed.

Lemma class_unique : forall c1 c2 a,
  in_class a c1 ->
  in_class a c2 ->
  c1 = c2.
Proof using A R equivR.
  intros * Hin Hin'.
  apply qclass_eq in Hin, Hin'.
  now subst.
Qed.

Lemma classes_disjoint : forall c1 c2 a,
  c1 <> c2 ->
  in_class a c1 -> ~ in_class a c2.
Proof using A R equivR.
  intros * Hneq Hin Hin'.
  applyc Hneq.
  enow eapply class_unique.
Qed.

Theorem qclass_surjective : Surjective qclass.
Proof using.
  intros c.
  destruct (class_nonempty c) as [a ?].
  exists a.
  symmetry.
  now apply qclass_eq.
Qed.

Theorem qclass_spec : forall x y,
  (qclass x = qclass y) = (x ~ y).
Proof using.
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
Proof using.
  intros * H *.
  destruct c as [Q p].
  eta.
  destruct (qclass_surjective (exist _ Q p)) as [? <-].
  assumption!.
Qed.

Definition respects_equiv (f: A -> A) :=
  forall x y, x ~ y -> (f x) ~ (f y).

Definition respects_equiv2 (f: A -> A -> A) :=
  forall x x' y y', x ~ x' -> y ~ y' -> (f x y) ~ (f x' y').

Definition liftQ (f: A -> A) (re: respects_equiv f) : quotient -> quotient.
Proof using A R equivR.
  intros [P p].
  inversion p as (Hall & Honly & Hnonempty).
  refine (exist _ (λ a, ∃ x, (f x) ~ a /\ P x) _).
  max split.
  - intros x y (x' & <- & px') (y' & <- & py').
    apply re.
    now apply Hall.
  - intros x y H (x' & Heq & px').
    exists x'.
    split.
    + now transitivity x.
    + assumption.
  - destruct Hnonempty as [x ?].
    now exists (f x) x.
Defined.

Theorem liftQ_qclass : forall (f: A -> A) (re: respects_equiv f) a,
  liftQ f re (qclass a) = qclass (f a).
Proof using.
  intros *.
  apply exist_eq'.
  simpl.
  extensionality x.
  extensionality; split.
  - intros (x' & <- & H').
    now apply re.
  - intros ?.
    now exists a.
Qed.

Definition liftQ2 (f: A -> A -> A) (re: respects_equiv2 f) :
  quotient -> quotient -> quotient.
Proof using A R equivR.
  intros [P p] [Q q].
  inversion p as (HallP & HonlyP & HnonemptyP).
  inversion q as (HallQ & HonlyQ & HnonemptyQ).
  refine (exist _ (λ a, ∃ x y, R (f x y) a /\ P x /\ Q y) _).
  max split.
  - intros x y (x' & y' & <- & Hx' & Hy') (x'' & y'' & <- & Hx'' & Hy'').
    apply re.
    + now apply HallP.
    + now apply HallQ.
  - intros x y Heq (x' & y' & Heq' & Hx' & Hy').
    exists x' y'.
    max split.
    + now transitivity x.
    + assumption.
    + assumption.
  - destruct HnonemptyP as [x ?], HnonemptyQ as [y ?].
    now exists (f x y) x y.
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

Notation "f 'respects' R"  := (respects_equiv R f) (at level 50).
Notation "f 'respects2' R" := (respects_equiv2 R f) (at level 50).

Close Scope program_scope.