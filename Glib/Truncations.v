Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.Classical.
Require Import Axioms.Extensionality.

Require Import Setoid.

(* The inhabited type constructor is sometimes called "propositional truncation"
   because, under the proof-irrelevance interpretation, it truncates types down to 
   a single witness.
 *)

Notation "| a |" := (inhabits a)
  (at level 50, format "| a |").
Notation "‖ A ‖" := (inhabited A)
  (at level 50, format "‖ A ‖").


Definition to_trunc (a b: Type): Prop := a -> ‖b‖.

(* If `H: ‖a‖`, and the goal is a Prop, then `uninhabit H` transforms the
   hypothesis into `H: a` by inversion.
 *)
Ltac uninhabit H := 
  let i := fresh in
  inversion H as [i];
  clear H;
  rename i into H.

(* `inhabit`/`in` applies the inhabits-valued theorem in the hypothesis, and then 
   `uninhabits` the hypothesis.
 *)
Tactic Notation "inhabit" uconstr(c) "in" hyp(H) :=
  apply c in H;
  uninhabit H.

Tactic Notation "einhabit" uconstr(c) "in" hyp(H) :=
  eapply c in H;
  uninhabit H.

Tactic Notation "inhabitc" hyp(c) "in" hyp(H) :=
  inhabit c in H;
  clear c.

Tactic Notation "einhabitc" hyp(c) "in" hyp(H) :=
  einhabit c in H;
  clear c.

Theorem inhabited_codomain: forall a b,
  (a -> b) ->
  a -> ‖b‖.
Proof using.
  intros * H Ha.
  constructor.
  auto.
Qed. 

Theorem extend_truncation_domain: forall a b,
  (a -> ‖b‖) ->
  ‖a‖ -> ‖b‖.
Proof using.
  intros a b H inhA.
  uninhabit inhA.
  auto.
Qed.

Theorem lift_trunc_arrow : forall A B,
  (A -> B) -> 
  ‖A‖ -> ‖B‖.
Proof using.
  intros * f [a].
  exists (f a).
Qed.

Theorem domain_truncated_irrelevant : forall A B,
  (A -> ‖B‖) = (‖A‖ -> ‖B‖).
Proof using.
  intros *.
  extensionality; split.
  - intros f [a].
    now apply f.
  - intros f a.
    apply f.
    exists a.
Qed.

(* Transforms goal from `‖a‖` to `a` *)
Tactic Notation "inhabit" :=
  match goal with 
  | |- ‖ _ ‖ => constructor
  end.

(* ` *)
Tactic Notation "inhabit" uconstr(c) :=
  solve [inhabit; apply c] + 
  match type of c with 
  | ‖ _ ‖ -> ‖ _ ‖ => apply c
  | _ -> ‖ _ ‖ => apply (extend_truncation_domain _ _ c)
  end +
  apply c.

Tactic Notation "einhabit" uconstr(c) :=
  solve [inhabit; eapply c] + 
  match type of c with 
  | ‖ _ ‖ -> ‖ _ ‖ => eapply c
  | _ -> ‖ _ ‖ => eapply (extend_truncation_domain _ _ c)
  end +
  eapply c.

Tactic Notation "inhabitc" hyp(c) :=
  inhabit c; clear c.

Tactic Notation "einhabitc" hyp(c) :=
  einhabit c; clear c.

Theorem truncation_idempotent: forall a,
  ‖a‖ = ‖‖a‖‖.
Proof using.
  intro a.
  extensionality H.
  - inhabit H.
  - now uninhabit H.
Qed.

Theorem to_trunc_refl : reflexive Type to_trunc.
Proof using.
  intros ? x.
  inhabit x.
Qed.

Theorem to_trunc_trans : transitive Type to_trunc.
Proof using.
  unfold transitive, to_trunc.
  intros X Y Z Hxy Hyz x.
  inhabit Hyz.
  inhabit Hxy.
  inhabit x.
Qed.

Add Parametric Relation : Type to_trunc
  reflexivity  proved by to_trunc_refl
  transitivity proved by to_trunc_trans
  as to_trunc_rel.

Theorem to_trunc_weaker: forall a b (P: Prop),
  (a -> ‖b‖) ->
  (b -> P) ->
  a -> P.
Proof using.
  intros * Hab ? a.
  inhabitc Hab in a.
  auto.
Qed.

Theorem truncated_eq_exists_true : forall A,
  ‖A‖ = exists _: A, True.
Proof using.
  intros *.
  extensionality H; now destruct H.
Qed.

Theorem truncated_eq_double_neg : forall A: Type,
  ‖A‖ = ((A -> False) -> False).
Proof using.
  intros *.
  extensionality H.
  - intros ?.
    now uninhabit H.
  - contradict goal.
    applyc H.
    auto.
Qed.


(* Various truncation-equivalents *)

Lemma trunc_prod_eq_conj : forall P Q: Prop,
  ‖P × Q‖ = (P /\ Q).
Proof using.
  intros *.
  extensionality H.
  - uninhabit H.
    now destruct H.
  - now inhabit.
Qed.

Lemma trunc_sig_eq_exists : forall A (P: A -> Prop),
  ‖{x | P x}‖ = ∃ x, P x.
Proof using.
  intros *.
  extensionality H.
  - uninhabit H.
    follows destruct H.
  - follows destruct H.
Qed.

Lemma trunc_sigma_eq_exists : forall A (P: A -> Type),
  ‖Σ x, P x‖ = ∃ x, ‖P x‖.
Proof using.
  intros *.
  extensionality H.
  - uninhabit H.
    follows destruct H.
  - follows destruct H as [? [?]].
Qed.

Lemma trunc_sum_eq_disj : forall P Q: Prop,
  ‖{P} + {Q}‖ = (P \/ Q).
Proof using.
  intros *.
  extensionality H.
  - uninhabit H.
    now destruct H; [left|right].
  - now destruct H; inhabit; [left|right].
Qed.

Theorem sig_factor_trunc : forall (A: Type) (B: A -> Type),
  (Σ x, ‖B x‖) -> ‖Σ x, B x‖.
Proof using.
  intros * [x H].
  uninhabit H.
  exists ⟨x, H⟩.
Qed.