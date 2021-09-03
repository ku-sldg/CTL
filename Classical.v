Require Import Notation.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalFacts.

Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.PropExtensionality.

Theorem destruct_impl : forall p q,
  ~p \/ p /\ q <-> (p -> q).
Proof using.
  intros p q.
  split; intro H.
  - destruct H.
    + intro Hp. contradiction.
    + intro H1. apply H.
  - destruct (classic p); auto.
Qed.

Tactic Notation "destruct" "classic" uconstr(c) "as" ident(H) :=
  destruct (classic c) as [H|H].

Tactic Notation "destruct" "classic" uconstr(c) :=
  let x := fresh in
  destruct classic c as x.

Require Import Coq.Logic.JMeq.
Require Import Tactics.Tactics.


Theorem JMeq_same_type : forall (A B: Type) (x: A) (y: B),
  x ~= y ->
  A = B.
Proof using.
  intros * H.
  destruct H.
  reflexivity.
Qed.

(* In practice, likely no need to transform to regular equality. *)
Ltac JMeq_eq H :=
  match type of H with 
  | ?x ~= ?y =>
      destruct (JMeq_same_type _ _ x y H);
      apply JMeq_eq in H
  end.

Ltac classical_contradict H :=
  apply NNPP; contradict H.


(* Modified from `Coq.Logic.FunctionalExtensionality` to include propositional
   extensionality
 *)
Tactic Notation "extensionality" :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (propositional_extensionality X Y) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality)
  end.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    ((apply (propositional_extensionality X Y); split) ||
     apply (@functional_extensionality _ _ X Y) ||
     apply (@functional_extensionality_dep _ _ X Y) ||
     apply forall_extensionalityP ||
     apply forall_extensionalityS ||
     apply forall_extensionality) ; intro x
  end.

(* Ltac old_extensionality x := extensionality x.

Tactic Notation "extensionality" :=
  match goal with
  | |- ?P = ?Q =>
      apply (propositional_extensionality P Q)
  end || (
    let i := fresh in 
    old_extensionality i;
    revert i
  ).

Tactic Notation "extensionality" ident(x) :=
  match goal with
  | |- ?P = ?Q =>
      apply (propositional_extensionality P Q);
      split;
      intro x
  end ||
  old_extensionality x. *)


Theorem rew_NNPP: forall P: Prop,
  (~~P) = P.
Proof using.
  intros *.
  extensionality.
  split.
  - apply NNPP.
  - auto.
Qed.

(* Constructive helpers *)
Lemma modus_tollens : forall P Q: Prop,
  (P -> Q) ->
  ~Q -> ~P.
Proof using. auto. Qed.

Lemma double_neg_intro : forall P: Prop,
  P -> ~~P.
Proof using. auto. Qed.

Lemma modus_tollens' : forall P Q: Prop,
  (P -> ~Q) ->
  Q -> ~P.
Proof using.
  intros * Hpq Hq.
  apply double_neg_intro in Hq.
  apply (modus_tollens P (~Q) Hpq Hq).
Qed.


(* Builds proof irrelevance from excluded middle *)
Theorem proof_irrelevance : forall (P: Prop) (p1 p2: P),
  p1 = p2.
Proof using.
  intros *.
  apply proof_irrelevance_cci.
  exact classic.
Qed.
(* Print Assumptions proof_irrelevance. *)