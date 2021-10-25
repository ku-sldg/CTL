Require Import Notation.
Require Import GeneralTactics.

Import EqNotations.


Lemma proof_irrelevance__uip_refl :
  (forall (P: Prop) (p1 p2: P), p1 = p2) ->
  forall A (x: A) (h: x = x), h = eq_refl x.
Proof using.
  intros ? *.
  assumption!.
Qed.


Module Type UipImpl.
  Axiom uip_refl : forall A (x: A) (h: x = x), h = eq_refl x.
End UipImpl.

Module UipTheory (M: UipImpl).

Lemma uip_refl : forall A (x: A) (h: x = x), h = eq_refl x.
Proof using.
  exact M.uip_refl.
Qed.


Lemma uip : forall A (x y: A) (p q: x = y),
  p = q.
Proof using.
  intros.
  destruct q.
  apply uip_refl.
Qed.

Lemma eq_K : forall A (x: A) (P: x = x -> Type),
  P (eq_refl x) ->
  forall p: x = x, P p.
Proof using.
  intros.
  now rewrite uip_refl.
Qed.

Lemma eq_rect_eq : forall A (x: A) (P: A -> Type) (y: P x) (h: x = x),
  y = eq_rect x P y x h.
Proof using.
  intros *.
  now rewrite (uip_refl _ _ h).
Qed.

Lemma inj_pair2 :
  forall A (P: A -> Type) a (x y: P a),
    ⟨a, x⟩ = ⟨a, y⟩ ->
    x = y.
Proof using.
  intros.
  inversion_sigma.
  now find rewrite <- eq_rect_eq in.
Qed.

Notation inj_pairT2 := inj_pair2.

(* Dependent inversion tactics leveraging LEM *)

Ltac destr_sigma_eq :=
  repeat match goal with 
  | H: existT _ _ _ = existT _ _ _ |- _ =>
      simple apply inj_pairT2 in H
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
  

(* Here we give a redefinition of the JMeq construct. Unfortunately, the 
   existing JMeq definition is irrevocably tied to the JMeq_eq axiom,
   which we'd rather not accept here, since it can be derived by 
   UIP (and by extesion, LEM).
 *)

(* heq stands for "heterogeneous equality" *)
Unset Elimination Schemes.
Inductive heq (A: Type) (x : A) : forall B : Type, B -> Prop :=
	| heq_refl : heq A x A x.
Set Elimination Schemes.
Arguments heq {A} x {B} y.
Arguments heq_refl {A} x.

Notation "x ~= y" := (heq x y) (at level 70, no associativity).

(* Note: this is in fact equivalent to UIP. *)
Lemma heq_eq : forall A (x y: A), 
  x ~= y ->
  x = y.
Proof using.
  intros * Heq.
  now dependent inv Heq.
Qed.

Lemma eq_heq : forall A (x y: A), 
  x = y ->
  x ~= y.
Proof using.
  now intros * ->.
Qed.

Lemma heq_is_eq : forall A (x y: A),
  x ~= y <-> x = y.
Proof using.
  intros *.
  split; intros ?.
  - now apply heq_eq.
  - now apply eq_heq.
Qed.

Theorem heq_rect : forall (A: Type) (x: A) (P : A -> Type),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using.
  intros * ? * Heq.
  apply heq_eq in Heq.
  now induction Heq.
Qed.

Lemma heq_rec : forall (A: Type) (x: A) (P : A -> Set),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using. 
  exact heq_rect.
Qed.

Lemma heq_ind : forall (A: Type) (x: A) (P : A -> Prop),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using.
  exact heq_rect.
Qed.

Definition transport {A B} (H: A = B) (a: A) : B := rew [λ x, x] H in a.

Theorem transport_heq {A B} : forall (H: A = B) a,
  a ~= transport H a.
Proof using.
  intros *.
  now destruct H.
Qed.

Definition hcast {A B} (H: A = B) (a: A) : {b: B | a ~= b}.
  exists (transport H a).
  apply transport_heq.
Defined.

Theorem heq_by_transport_eq {A B}: forall (H: A = B) (x: A) (y: B),
  transport H x = y ->
  x ~= y.
Proof using.
  intros * Heq.
  transitivity (transport H x).
  - apply transport_heq.
  - now rewrite Heq.
Qed.

Theorem heq_by_transport_eqr {A B}: forall (H: B = A) (x: A) (y: B),
  x = transport H y ->
  x ~= y.
Proof using.
  intros * Heq.
  transitivity (transport H y).
  - now rewrite Heq.
  - symmetry.
    apply transport_heq. 
Qed.

Theorem transport_eq_refl_cancel : forall A (x: A),
  transport eq_refl x = x.
Proof using.
  easy.
Qed.

Theorem transport_cancel: forall A (H: A = A) x,
  transport H x = x.
Proof using.
  intros.
  rewrite (uip_refl _ _ H).
  apply transport_eq_refl_cancel.
Qed.

Theorem existT_eq_intro :
  forall (A: Type) (B: A -> Type) (a a': A) (b: B a) (b': B a'),
    a = a' ->
    b ~= b' ->
    ⟨a, b⟩ = ⟨a', b'⟩.
Proof using.
  intros * <- Heq'.
  f_equal.
  now apply heq_eq.
Qed.

Lemma pair_heq_intro : 
  forall A B C D (a: A) (b: B) (c: C) (d: D),
    a ~= b ->
    c ~= d ->
    (a, c) ~= (b, d).
Proof using.
  now intros * [] [].
Qed.

End UipTheory.