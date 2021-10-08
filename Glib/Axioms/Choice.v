Require Import Coq.Logic.ChoiceFacts.

Require Import Notation.
Require Import GeneralTactics.
Require Import Truncations.
Require Import Axioms.Extensionality.


(* "If `x: A` implies there exists some `B x`, then there exists 
   some function `Π x: A, B x`". *)
Axiom choice : Π (A: Type) (B: A -> Type),
  (Π x, ‖B x‖) -> ‖Π x, B x‖.

Lemma choice_ext : Π (A: Type) (B: A -> Type),
  (Π x, ‖B x‖) = ‖Π x, B x‖.
Proof using.
  intros *.
  extensionality; split.
  - apply choice.
  - intros H *.
    now uninhabit H.
Qed.

Theorem nondep_choice : forall A B,
  (A -> ‖B‖) -> ‖A -> B‖.
Proof using.
  intros * f.
  now apply choice.
Qed.

Theorem nondep_choice_ext : forall A B,
  (A -> ‖B‖) = ‖A -> B‖.
Proof using.
  intros.
  apply choice_ext.
Qed.

Lemma fun_choice : forall A B (R: A -> B -> Prop),
  (forall a, exists b, R a b) ->
  exists f: A -> B, forall a, R a (f a).
Proof using.
  intros * Rltotal.
  transform Rltotal (Π x, ‖{y | R x y}‖) by
    (intros; now rewrite trunc_sig_eq_exists).
  apply choice in Rltotal.
  uninhabit Rltotal.
  define exists.
  - intro a.
    specialize (Rltotal a).
    now destruct Rltotal.
  - intros *.
    simpl.
    now destruct (Rltotal a).
Qed.

Theorem dependent_choice : forall (A: Type) (B: A -> Type) (R: forall a, B a -> Prop),
  (forall a, exists b, R a b) ->
  exists f: (forall a, B a),
    forall a, R a (f a).
Proof using.
  apply non_dep_dep_functional_choice.
  exact fun_choice.
Qed.

(* Functional choice does not require an axiom when the proof of left-totalness 
   is transparent/constructive
 *)
Definition fun_choice_constructive : forall A B (R: A -> B -> Prop),
  (forall a, Σ b, R a b) ->
  Σ f: A -> B, forall a, R a (f a).
Proof using.
  intros * Rltotal.
  define exists.
  - intro a.
    specialize (Rltotal a).
    now destruct Rltotal.
  - intro a.
    simpl.
    now destruct (Rltotal a).
Defined.

Lemma rel_choice : forall A B (R: A -> B -> Prop),
  (forall x, exists y, R x y) -> 
  exists R': A -> B -> Prop, 
    subrelation R' R /\
    forall x, exists! y, R' x y.
Proof using.
  intros * Rltotal.
  transform Rltotal (Π x, ‖{y | R x y}‖) by
    (intros; now rewrite trunc_sig_eq_exists).
  apply choice in Rltotal.
  uninhabit Rltotal.
  define exists.
  - intro a.
    specialize (Rltotal a).
    destruct exists Rltotal b.
    exact (λ x, b = x).
  - simpl.
    split.
    + unfold subrelation.
      intros * ?.
      destruct (Rltotal x).
      now subst.
    + intros *.
      enow destruct (Rltotal x).
Qed.
