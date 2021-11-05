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

Unset Elimination Schemes.
Inductive JMeq (A: Type) (x : A) : forall B : Type, B -> Prop :=
  | JMeq_refl : JMeq A x A x.
Set Elimination Schemes.
Arguments JMeq {A} x {B} y.
Arguments JMeq_refl {A} x.

Notation "x ~= y" := (JMeq x y) (at level 70, no associativity).

Register JMeq as core.JMeq.type.
Register JMeq_refl as core.JMeq.refl.

#[global]
Hint Resolve JMeq_refl : core.

Definition JMeq_hom {A} (x y: A) := x ~= y.
Register JMeq_hom as core.JMeq.hom.

(* Note: this is in fact equivalent to UIP. *)
Lemma JMeq_eq : forall A (x y: A), 
  x ~= y ->
  x = y.
Proof using.
  intros * Heq.
  now dependent inv Heq.
Qed.

Lemma eq_JMeq : forall A (x y: A), 
  x = y ->
  x ~= y.
Proof using.
  now intros * ->.
Qed.

Lemma JMeq_is_eq : forall A (x y: A),
  x ~= y <-> x = y.
Proof using.
  intros *.
  split; intros ?.
  - now apply JMeq_eq.
  - now apply eq_JMeq.
Qed.

Theorem JMeq_rect : forall (A: Type) (x: A) (P : A -> Type),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using.
  intros * ? * Heq.
  apply JMeq_eq in Heq.
  now induction Heq.
Qed.

Lemma JMeq_rec : forall (A: Type) (x: A) (P : A -> Set),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using. 
  exact JMeq_rect.
Qed.

Lemma JMeq_ind : forall (A: Type) (x: A) (P : A -> Prop),
  P x ->
  forall y : A, x ~= y -> P y.
Proof using.
  exact JMeq_rect.
Qed.

Register JMeq_ind as core.JMeq.ind.

Theorem JMeq_sym : forall A B (a: A) (b: B),
  a ~= b ->
  b ~= a.
Proof using.
  intros.
  follows destruct H.
Qed.

#[global]
Hint Immediate JMeq_sym : core.
Register JMeq_sym as core.JMeq.sym.

Theorem JMeq_trans : forall A B C (a: A) (b: B) (c: C),
  a ~= b ->
  b ~= c ->
  a ~= c.
Proof using.
  intros * [] [].
  constructor.
Qed.

Register JMeq_trans as core.JMeq.trans.

Theorem JMeq_congr : forall A (x: A) B (f: A -> B) (y: A), 
  x ~= y ->
  f x = f y.
Proof using.
  intros * H.
  pattern y.
  follows eapply JMeq_ind.
Qed.

Register JMeq_congr as core.JMeq.congr.

Theorem f_JMequal : forall A (B: A -> Type) (f: forall a, B a) (x y: A),
  x = y -> 
  f x ~= f y.
Proof using.
  follows intros * <-.
Qed.

Theorem JMeq_type_eq {A B} {a: A} {b: B}: 
  a ~= b ->
  A = B.
Proof using.
  follows intros [].
Defined.


Lemma rew_JMeq {A B} : forall (H: A = B) (a: A),
  rew H in a ~= a.
Proof using.
  intros *.
  now destruct H.
Qed.

Corollary rew_JMeq_sym {A B} : forall (H: A = B) (a: A),
  a ~= rew H in a.
Proof using.
  symmetry.
  apply rew_JMeq.
Qed.

Definition JMcast {A B} (H: A = B) (a: A) : {b: B | a ~= b} :=
  exist _ (rew H in a) (rew_JMeq_sym H a).

Theorem JMeq_by_rew_eq {A B}: forall (H: A = B) (x: A) (y: B),
  rew H in x = y ->
  x ~= y.
Proof using.
  intros * Heq.
  apply JMeq_trans with (b := rew H in x).
  - apply rew_JMeq_sym.
  - follows rewrite Heq.
Qed.

Theorem rew_eq_by_JMeq {A B}: forall (x: A) (y: B),
  forall h: x ~= y,
  rew JMeq_type_eq h in x = y.
Proof using.
  intros *.
  follows destruct h.
Qed.

Theorem JMeq_by_rew_eqr {A B}: forall (H: B = A) (x: A) (y: B),
  x = rew H in y ->
  x ~= y.
Proof using.
  intros * Heq.
  apply JMeq_trans with (b := rew H in y).
  - follows rewrite Heq.
  - apply rew_JMeq. 
Qed.

Theorem rew_eqr_by_JMeq {A B}: forall (x: A) (y: B),
  forall h: x ~= y,
  x = rew eq_sym (JMeq_type_eq h) in y.
Proof using.
  intros *.
  follows destruct h.
Qed.

Theorem rew_eq_refl_cancel : forall A (x: A),
  rew eq_refl A in x = x.
Proof using.
  tedious.
Qed.

Theorem rew_cancel: forall A (H: A = A) (x: A),
  rew H in x = x.
Proof using.
  intros.
  rewrite (uip_refl _ _ H).
  apply rew_eq_refl_cancel.
Qed.


Theorem existT_eq_intro :
  forall (A: Type) (B: A -> Type) (a a': A) (b: B a) (b': B a'),
    a = a' ->
    b ~= b' ->
    ⟨a, b⟩ = ⟨a', b'⟩.
Proof using.
  intros * <- Heq'.
  f_equal.
  follows apply JMeq_eq.
Qed.

Lemma pair_JMeq_intro : 
  forall A B C D (a: A) (b: B) (c: C) (d: D),
    a ~= b ->
    c ~= d ->
    (a, c) ~= (b, d).
Proof using.
  follows intros * [] [].
Qed.


(* `simpl_eq` is based on `cbn`, but which breaks down equality terms based on UIP *)

Ltac _simpl_eq :=
  cbn; try (
    repeat+ match goal with 
    | |- context[?p] =>
        progress match type of p with 
        | ?x = ?x => rewrite (uip_refl _ x p)
        | _ = _ => destruct p
        end
    end;
    _simpl_eq
  ).
Tactic Notation "simpl_eq" := _simpl_eq.

Ltac _simpl_eq_in H :=
  cbn in H; try (
    repeat+ match type of H with 
    | context[?p] =>
        match type of p with 
        | ?x = ?x => rewrite (uip_refl _ x p) in H
        | _ = _ => destruct p
        end
    end;
    _simpl_eq_in H
  ).
Tactic Notation "simpl_eq" "in" hyp(H) := _simpl_eq_in H.

Tactic Notation "simpl_eq" "in" "*" := 
  _simpl_eq;
  repeat find (fun H => _simpl_eq_in H).

End UipTheory.