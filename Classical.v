Require Import Notation.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.ClassicalFacts.
Require Import Coq.Logic.Eqdep.

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


Tactic Notation "contradict" "goal" hyp(H) :=
  apply NNPP; intro H.

Tactic Notation "contradict" "goal" :=
  let contra := fresh "contra" in
  apply NNPP; intro contra.


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

Definition uip_refl := forall U (x:U) (p: x = x),
  p = eq_refl.

Definition eq_rect_eq := forall U (p:U) (Q:U -> Type) (x:Q p) (h:p = p),
  x = eq_rect p Q x p h.

Theorem uip__eq_rect_eq:
  uip_refl ->
  eq_rect_eq.
Proof using.
  unfold uip_refl, eq_rect_eq.
  intros H *.
  now rewrite (H _ _ h).
Qed.


(* De Morgan's + extensionality *)

Theorem rew_not_and : forall P Q: Prop,
  (~ (P /\ Q)) = ~P \/ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_and_or.
  - now apply or_not_and.
Qed.

Theorem rew_not_or : forall P Q: Prop,
  (~ (P \/ Q)) = ~P /\ ~Q.
Proof using.
  intros *.
  extensionality H.
  - now apply not_or_and.
  - now apply and_not_or.
Qed.

Theorem rew_imply_or : forall P Q: Prop,
  (P -> Q) = ~P \/ Q.
Proof using.
  intros *.
  extensionality H.
  - now apply imply_to_or.
  - now apply or_to_imply.
Qed.

Theorem rew_not_all : forall U (P:U -> Prop),
  (~ forall n, P n) = exists n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_all_ex_not.
  - now apply ex_not_not_all.
Qed.

Theorem rew_not_ex : forall U (P:U -> Prop),
  (~ exists n, P n) = forall n, ~ P n.
Proof using.
  intros *.
  extensionality H.
  - now apply not_ex_all_not.
  - now apply all_not_not_ex.
Qed.


(* Dependent inv
   Sometimes, inversion leaves behind equalities of existT terms. This 
   uses excluded middle (we could also directly axiomitize eq_rect_eq)
 *)

Theorem inj_pairT2_paramterized :
  eq_rect_eq ->
  forall U (P: U -> Type) p x y,
    existT P p x = existT P p y ->
    x = y.
Proof using.
  intros eq_rect_eq * H.
  inversion_sigma.
  now rewrite <- eq_rect_eq in H1.
Qed.

(* Uses classic axiom *)
Theorem inj_pairT2_classic : forall U (P: U -> Type) p x y,
  existT P p x = existT P p y ->
  x = y.
Proof using.
  apply inj_pairT2_paramterized.
  exact Classical_Prop.Eq_rect_eq.eq_rect_eq.
Qed.

Ltac destr_sigma_eq :=
  repeat match goal with 
  | H: existT _ _ _ = existT _ _ _ |- _ =>
      simple apply inj_pairT2_classic in H
  end.

Tactic Notation "dependent" "inv" hyp(H) :=
  inv H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "inv" hyp(H) "as" simple_intropattern(pat) :=
  inv H as pat;
  destr_sigma_eq;
  subst!.


Tactic Notation "dependent" "invc" hyp(H) :=
  invc H;
  destr_sigma_eq;
  subst!.

Tactic Notation "dependent" "invc" hyp(H) "as" simple_intropattern(pat) :=
  invc H as pat;
  destr_sigma_eq;
  subst!.
