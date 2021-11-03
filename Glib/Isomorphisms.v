Require Import Notation.
Require Import GeneralTactics.
Require Import Axioms.
Require Import Truncations.
Require Import Quotient.

Require Import Coq.Logic.FinFun.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Setoid.
Require Import Lia.

Open Scope program_scope.


Definition isomorphic A B : Prop :=
  exists (f: A -> B) (g: B -> A), 
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

Definition isomorphism A B :=
  Σ (f: A -> B) (g: B -> A),
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

Notation "A ≃ B"  := (isomorphic A B)  (at level 75).
Notation "A ≃> B" := (isomorphism A B) (at level 75).


(* Could also be called an automorphism *)
Definition permutation A := A ≃> A.


(* Analogous to reflexivity *)
Definition id_isomorphism A : A ≃> A.
  now exists id id.
Defined.

(* Analogous to symmetry *)
Definition isomorphism_invert {A B} (ϕ: A ≃> B) : B ≃> A.
  destruct ϕ as (f & g & ?).
  now exists g f.
Defined.
Notation "ϕ ⁻¹" := (isomorphism_invert ϕ)
  (at level 5, format "ϕ ⁻¹").

(* Analogous to transitivity *)
Theorem isom_compose {X Y Z}: 
  X ≃> Y ->
  Y ≃> Z ->
  X ≃> Z.
Proof using.
  intros * Hxy Hyz.
  destruct Hxy as (fxy & gyx & fxy_gyx & gyx_fxy).
  destruct Hyz as (fyz & gzy & fyz_gzy & gzy_gyz).
  exists (fyz ∘ fxy) (gyx ∘ gzy).
  split; intros; unfold compose; find rewrite ->; assumption!.
Defined. 


(* Projections and lifts *)

Definition iso_proj1 {A B} (ϕ: A ≃> B) : A -> B :=
  match ϕ with 
  | ⟨f, _⟩ => f 
  end.
Coercion iso_proj1 : isomorphism >-> Funclass.

Definition iso_proj2 {A B} (ϕ: A ≃> B) : B -> A :=
  match ϕ with 
  | ⟨_, g, _⟩ => g
  end.

Definition iso_liftl {A B X: Type} (ϕ: A ≃> B) (f: A -> A) : B -> B :=
  iso_proj1 ϕ ∘ f ∘ iso_proj2 ϕ.

Definition iso_lift2 {A B X: Type} (ϕ: A ≃> B) (f: B -> B) : A -> A :=
  iso_proj2 ϕ ∘ f ∘ iso_proj1 ϕ.


Definition iso_inh_proj1 {A B} (ϕ: A ≃ B) : ‖A -> B‖.
  now destruct ϕ.
Defined.

Definition iso_construct_proj2 {A B} (ϕ: A ≃ B) : ‖B -> A‖.
  now destruct ϕ as (_ & ? & _).
Defined.


(* Properties *)

Theorem iso_refl :
  reflexive Type isomorphic.
Proof using.
  unfold reflexive.
  intros.
  now exists id id.
Qed.

Theorem iso_sym : 
  symmetric Type isomorphic.
Proof using.
  unfold symmetric.
  intros * H.
  destruct exists H f g.
  now exists g f.
Qed.

Theorem iso_trans :
  transitive Type isomorphic.
Proof using.
  unfold transitive.
  intros * Hxy Hyz.
  destruct Hxy as (fxy & gyx & fxy_gyx & gyx_fxy).
  destruct Hyz as (fyz & gzy & fyz_gzy & gzy_gyz).
  exists (fyz ∘ fxy) (gyx ∘ gzy).
  split; intros *; unfold compose; find rewrite ->; find apply.
Qed. 

Add Parametric Relation : Type isomorphic
  reflexivity  proved by iso_refl
  symmetry     proved by iso_sym
  transitivity proved by iso_trans
  as iso_rel.

Theorem isomorphism__isomorphic {A B}:
  A ≃> B ->
  A ≃ B.
Proof using.
  intros H.
  destruct exists H f g.
  now exists f g.
Qed. 
Coercion isomorphism__isomorphic : isomorphism >-> isomorphic.

Theorem isomorphic__isomorphism {A B}:
  A ≃ B ->
  ‖A ≃> B‖.
Proof using.
  intros H.
  destruct exists H f g.
  constructor.
  now exists f g.
Qed.

Theorem iso_cancel_inv {A B}: forall (ϕ: A ≃> B) b,
  ϕ (ϕ⁻¹ b) = b.
Proof using.
  intros.
  destruct ϕ as (? & ? & ?).
  assumption!.
Qed.

Theorem inv_cancel_iso {A B}: forall (ϕ: A ≃> B) a,
  ϕ⁻¹ (ϕ a) = a.
Proof using.
  intros.
  destruct ϕ as (? & ? & ?).
  assumption!.
Qed.

Theorem inv_cancel_inv {A B}: forall (ϕ: A ≃> B),
  (ϕ⁻¹)⁻¹ = ϕ.
Proof using.
  intros *.
  now destruct ϕ as (? & ? & ?).
Qed.

Lemma eq_cancel_left {A B}: forall (ϕ: A ≃> B) a b,
  a = ϕ⁻¹ b ->
  ϕ a = b.
Proof using.
  intros * ->.
  apply iso_cancel_inv.
Qed.

Lemma eq_cancel_right {A B}: forall (ϕ: A ≃> B) a b,
  ϕ⁻¹ b = a ->
  b = ϕ a.
Proof using.
  intros * <-.
  symmetry.
  apply iso_cancel_inv.
Qed.

Lemma eq_cancel_inv_left {A B}: forall (ϕ: A ≃> B) a b,
  b = ϕ a ->
  ϕ⁻¹ b = a.
Proof using.
  intros * ->.
  apply inv_cancel_iso.
Qed.

Lemma eq_cancel_inv_right {A B}: forall (ϕ: A ≃> B) a b,
  ϕ a = b ->
  a = ϕ⁻¹ b.
Proof using.
  intros * <-.
  symmetry.
  apply inv_cancel_iso.
Qed.


Theorem iso_iso_inv {A B}: 
  (A ≃> B) ≃> (B ≃> A).
Proof using.
  do 2 exists isomorphism_invert.
  split; intros *; apply inv_cancel_inv.
Defined.

(* Reflect a proof goal into the domain of the isomorphism *)
Theorem isomorphism_refl {A B}: forall P: B -> Type,
  forall ϕ: A ≃> B,
  (forall a, P (ϕ a)) -> 
  forall b, P b.
Proof using.
  intros * ? b.
  find specialize (ϕ⁻¹ b).
  now find rewrite iso_cancel_inv in.
Defined.

(* Reflect a proof goal into the image of the isomorphism *)
Theorem isomorphism_refl_inv {A B}: forall P: A -> Type,
  forall ϕ: A ≃> B,
  (forall b, P (ϕ⁻¹ b)) -> 
  forall a, P a.
Proof using.
  intros * ? a.
  find specialize (ϕ a).
  now find rewrite inv_cancel_iso in.
Defined.
  
(* Reflects hypothesis H to its corresponding term under isomorphism ϕ
   (with new name i). If the goal depends on H, the goal will be reflected as well.

   TODO: handle when H is in another hypothesis. Could be done cheaply by reverting
   such hypotheses, calling iso, then intro-ing them. This could mess with the order
   though.
*)
Ltac _iso ϕ H i :=
  let Hϕ := fresh "ϕ" in
  epose (Hϕ := ϕ);
  repeat especialize_term Hϕ;
  match type of Hϕ with 
  | ?A ≃> ?B =>
      let tH := type of H in first
        [ unify A tH;
          match goal with 
          | |- context[H] =>
              pattern H;
              apply (fun goal => isomorphism_refl_inv _ Hϕ goal H);
              clear H;
              intro i
          | _ => apply Hϕ in H
          end
        | unify B tH;
          match goal with 
          | |- context[H] =>
              pattern H;
              apply (fun goal => isomorphism_refl _ Hϕ goal H);
              clear H;
              intro i
          | _ => apply (Hϕ⁻¹) in H
          end
        | fail "Cannot unify the type of the hypothesis with either iso type"]
  | ?A ≃ ?B =>
      match goal with 
      | |- ?g =>
          match type of g with 
          | Prop => idtac
          | _ => fail "Prop-level isomorphism cannot be used on a non-Prop goal"
          end
      end;
      inhabit isomorphic__isomorphism in Hϕ;
      _iso Hϕ H;
      (* Will this ever fail? *)
      try clear Hϕ
  end + fail "First argument should be an isomorphism";
  (* Will this ever fail? *)
  try (unfold Hϕ; clear Hϕ).

Tactic Notation "iso" uconstr(ϕ) hyp(H) ident(i) := _iso ϕ H i.

(* Optionally, you can leave off the last identifier to re-use the H identifier *)
Tactic Notation "iso" uconstr(ϕ) hyp(H) := iso ϕ H H.


Theorem isomorphism_refl_sig {A B}: forall P: B -> Type,
  forall ϕ: A ≃> B,
  (Σ a, P (ϕ a)) ->
  Σ b, P b.
Proof using.
  intros * [a ?].
  now exists (ϕ a).
Qed.

Theorem isomorphism_refl_sig_inv {A B}: forall P: A -> Type,
  forall ϕ: A ≃> B,
  (Σ b, P (ϕ⁻¹ b)) ->
  Σ a, P a.
Proof using.
  intros * [a ?].
  now exists (ϕ⁻¹ a).
Qed.

Theorem isomorphism_refl_exists {A B}: forall P: B -> Prop,
  forall ϕ: A ≃> B,
  (exists a, P (ϕ a)) ->
  exists b, P b.
Proof using.
  intros * [a ?].
  now exists (ϕ a).
Qed.

Theorem isomorphism_refl_exists_inv {A B}: forall P: A -> Prop,
  forall ϕ: A ≃> B,
  (exists b, P (ϕ⁻¹ b)) ->
  exists a, P a.
Proof using.
  intros * [a ?].
  now exists (ϕ⁻¹ a).
Qed.


Definition iso_equiv {A B C} (ϕ: A ≃> B) (fa : A -> C) (fb : B -> C) :=
  forall a, fa a = fb (ϕ a).

Theorem iso_equiv_flip {A B C}: forall (ϕ: A ≃> B) (fa : A -> C) (fb : B -> C),
  iso_equiv ϕ fa fb = forall b, fb b = fa (ϕ⁻¹ b).
Proof using. 
  intros *.
  extensionality.
  unfold iso_equiv; split; intros H *.
  - iso ϕ b a. 
    rewrite inv_cancel_iso.
    now find rewrite.
  - iso ϕ a b. 
    rewrite iso_cancel_inv.
    now find rewrite.
Qed. 


(* Images and inverses *)

Definition image {A B} (f: A -> B) :=
  {b | exists a, f a = b}.

Definition image_proj {A B} {f: A -> B} (i: image f) : B.
  now destruct i.
Defined.

Definition image_dep {A B} (f: forall a: A, B a) :=
  Σ a (b: B a), f a = b.

Definition image_dep_proj {A B} {f: forall a: A, B a}
  (img: image_dep f) : Σ a, B a.
Proof using.
  destruct img as (a & ? & ?).
  now exists a.
Defined.


Definition iso_image_lift {A B} (ϕ: A ≃> B) (b: B) : image ϕ.
  exists b (ϕ⁻¹ b).
  apply iso_cancel_inv.
Defined.

Definition iso_image {A B}: forall ϕ: A ≃> B,
  image ϕ ≃> B.
Proof using.
  intros *.
  exists image_proj (iso_image_lift ϕ).
  split; intros *.
  - reflexivity.
  - destruct a as (? & a & ?); subst.
    simpl.
    unfold iso_image_lift.
    f_equal.
    apply proof_irrelevance.
Defined.

Theorem iso_image_inv {A B}: forall ϕ: A ≃> B,
  image ϕ⁻¹ ≃> A.
Proof using.
  intros *.
  iso iso_iso_inv ϕ.
  cbn.
  rewrite inv_cancel_inv.
  apply iso_image.
Qed.

Definition f_image {A B} (f: A -> B) : A -> image f.
  intro a.
  now exists (f a) a.
Defined.

(* Dependent on axiomatic choice to construct inverse *)
Theorem inverse_injection : forall A B (f: A -> B),
  Injective f ->
  exists g: image f -> A, 
    (forall i, f_image f (g i) = i) /\
    (forall a, g (f_image f a) = a).
Proof using.
  intros * Hinj.
  transform Hinj (Injective (f_image f)).
  { unfold Injective.
    intros * H.
    invc H as [H].
    now apply Hinj in H.
  }
  pose proof (fun_choice _ _ (fun i a => f_image f a = i)) as g.
  forward g by follows intros (? & ? & <-).
  destruct g as [g H].
  exists g.
  split; [assumption|].
  intros *.
  specialize (H (f_image f a)).
  now apply Hinj in H.
Qed.

(* Dependent on axiomatic choice to construct inverse *)
Theorem injection_image : forall A B (f: A -> B),
  Injective f ->
  A ≃ image f.
Proof using.
  intros * Hinj.
  pose proof (inverse_injection A B f Hinj) as [g ?].
  now exists (f_image f) g.
Qed. 

(* Dependent on axiomatic choice to construct inverse *)
Lemma surjection_image : forall A B (f: A -> B),
  Surjective f ->
  image f ≃ B.
Proof using.
  unfold Surjective.
  intros * Hsur.
  transform Hsur (Π b, ‖{a | f a = b}‖) by
    (intros; now rewrite trunc_sig_eq_exists).
  inhabit choice in Hsur.
  define exists by (now intros [? _]).
  define exists.
  { intros b.
    exists b.
    destruct (Hsur b) as [a ?].
    now exists a.
  }
  split.
  - auto.
  - intros (b & a & ?).
    now apply exist_eq.
Qed.

Lemma iso_injective : forall A B (ϕ : A ≃> B),
  Injective ϕ.
Proof using.
  intros * a a' H.
  apply (f_equal ϕ⁻¹) in H.
  now repeat rewrite inv_cancel_iso in H.
Qed.

Lemma iso_surjective : forall A B (ϕ : A ≃> B),
  Surjective ϕ.
Proof using.
  intros * b.
  exists (ϕ⁻¹ b).
  apply iso_cancel_inv.
Qed.

Definition Bijective  {A B} (f: A -> B) := Injective f /\ Surjective f.

Corollary iso_bijective : forall A B (ϕ : A ≃> B),
  Bijective ϕ.
Proof using.
  intros *.
  split.
  - apply iso_injective.
  - apply iso_surjective.
Qed.

Theorem bijection_iso : forall A B (f: A -> B),
  Bijective f -> 
  A ≃ B.
Proof using.
  intros * [? ?].
  transitivity (image f).
  - now apply injection_image.
  - now apply surjection_image.
Qed.

Corollary ex_bijection_iso : forall A B,
  (exists f: A -> B, Bijective f) -> 
  A ≃ B.
Proof using.
  intros * [? ?].
  follows eapply bijection_iso.
Qed.

Theorem iso_prop : forall P Q: Prop,
  P ≃ Q ->
  (P <-> Q).
Proof using.
  intros * H.
  now destruct H as (? & ? & ?).
Qed.

(* An isomorphism of Props is equality, assuming extensionality *)
Theorem iso_prop_extenionality : forall P Q: Prop,
  (P ≃ Q) = (P = Q).
Proof using.
  intros *.
  extensionality.
  split; [|now intros ->].
  intro H.
  extensionality.
  now destruct H as (? & ? & ?).
Qed.

(* A slightly weaker conclusion than iso_prop_extensionality, which depends on the 
   weaker assumption of proof irrelevance
 *)
Theorem iso_proof_irrelevance : forall P Q: Prop,
  (forall (P: Prop) (p1 p2: P), p1 = p2) ->
  (P ≃ Q) <-> (P <-> Q).
Proof using.
  intros * proof_irrelevance.
  split.
  - intro ϕ.
    inhabit isomorphic__isomorphism in ϕ.
    split; intros ?.
    + now apply ϕ.
    + now apply (ϕ⁻¹).
  - intros [H1 H2].
    exists H1 H2.
    split; intros; apply proof_irrelevance.
Qed.

Theorem iso_proof_irrelevance' : forall P Q: Prop,
  (forall (P: Prop) (p1 p2: P), p1 = p2) ->
  (P ≃ Q) ≃ (P <-> Q).
Proof using.
  intros * proof_irrelevance.
  let _temp := fresh in 
    pose proof iso_proof_irrelevance as _temp;
    do 2 especialize _temp;
    specialize (_temp proof_irrelevance);
    destruct _temp as [H1 H2].
  exists H1 H2.
  split; intros; apply proof_irrelevance.
Qed. 


(* Arithmetic properties of isomorphisms *)

(* Rather than naively folding `sum unit` over the nat, we manually recurse in 
   order to distinguish the number `1` and avoid the unecessary sum with `0`.
 *)
Fixpoint nat_to_set (n: nat) : Set :=
  match n with 
  | 0 => Empty_set 
  | 1 => unit
  | S n' => unit + (nat_to_set n')
  end.
Coercion nat_to_set : nat >-> Sortclass.

Theorem two_is_bool :
  2 ≃ bool.
Proof using.
  exists (λ b: 2, if b then true else false).
  exists (λ b: bool, if b then inl tt else inr tt).
  split.
  - now intros [|].
  - now intros [[]|[]].
Qed.

Theorem sum_comm : forall A B,
  A + B ≃ B + A.
Proof using.
  intros *.
  do 2 define exists by (now (intros [?|?]; [right|left])).
  split; now intros [?|?].
Qed.

Theorem sum_id_l : forall A,
  0 + A ≃ A.
Proof using.
  intros *.
  define exists by (now intros [?|?]).
  exists (λ a, inr a).
  split.
  - easy.
  - now intros [?|?].
Qed.
  
Theorem sum_id_r : forall A,
  A + 0 ≃ A.
Proof using.
  intros *.
  etransitivity.
  - apply sum_comm.
  - apply sum_id_l.
Qed.

Theorem sum_assoc : forall A B C,
  A + (B + C) ≃ (A + B) + C.
Proof using.
  intros *.
  define exists.
  { intros [?|[?|?]].
    + now (left; left).
    + now (left; right).
    + now right.
  }
  define exists.
  { intros [[?|?]|?].
    + now left.
    + now (right; left).
    + now (right; right).
  }
  split.
  - now intros [[?|?]|?].
  - now intros [?|[?|?]].
Qed.

Theorem S_type : forall n: nat,
  S n ≃ 1 + n.
Proof using.
  intros n.
  induction n.
  - now rewrite sum_id_r.
  - reflexivity.
Qed.

Theorem sum_iso_intro : forall A A' B B',
  A ≃ A' ->
  B ≃ B' ->
  A + B ≃ A' + B'.
Proof using.
  intros * ϕA ϕB.
  inhabit isomorphic__isomorphism in ϕA;
  inhabit isomorphic__isomorphism in ϕB.
  apply ex_bijection_iso.
  define exists; [|split].
  - intros [a|b].
    + exact (inl (ϕA a)).
    + exact (inr (ϕB b)).
  - intros [a|b] [a'|b'] [=].
    + f_equal.
      follows eapply iso_injective.
    + f_equal.
      follows eapply iso_injective.
  - intros [a'|b'].
    + exists (inl (ϕA⁻¹ a')).
      f_equal.
      apply iso_cancel_inv.
    + exists (inr (ϕB⁻¹ b')).
      f_equal.
      apply iso_cancel_inv.
Qed.

Theorem prod_comm : forall A B,
  A × B ≃ B × A.
Proof using.
  intros *.
  do 2 define exists by (now intros [? ?]).
  split; now intros [? ?].
Qed.

Theorem prod_id_l : forall A,
  1 × A ≃ A.
Proof using.
  intros *.
  exists (λ '(_, a), a) (λ a, (tt, a)).
  split.
  - easy.
  - now intros [[] ?].
Qed.

Theorem prod_id_r : forall A,
  A × 1 ≃ A.
Proof using.
  intros *.
  etransitivity.
  - apply prod_comm.
  - apply prod_id_l.
Qed.

Theorem prod_assoc : forall A B C,
  A × (B × C) ≃ (A × B) × C.
Proof using.
  intros *.
  define exists by (now intros [? [? ?]]).
  define exists by (now intros [[? ?] ?]).
  split.
  - now intros [[? ?] ?].
  - now intros [? [? ?]].
Qed.

Theorem sum_prod_distribute : forall A B C,
  A × (B + C) ≃ A × B + A × C.
Proof using.
  intros *.
  define exists.
  { intros [? [?|?]].
    - now left.
    - now right.
  }
  define exists.
  { intros [[? ?]|[? ?]].
    - split; [assumption| now left].
    - split; [assumption| now right].
  }
  split.
  - now intros [[? ?]|[? ?]].
  - now intros [? [?|?]].
Qed.

Theorem quotient_identity : forall A, 
  A ≃ A / eq.
Proof using.
  intros *.
  apply ex_bijection_iso.
  exists (qclass eq).
  split.
  + intros x y [=].
    symmetry.
    pattern x.
    now find (fun H => induction H).
  + apply qclass_surjective.
    apply eq_equivalence.
Qed.

Theorem quotient_universal_property : forall A R B {equivR: Equivalence R},
  (A/R -> B) ≃ (exists f: A -> B, forall x y, R x y -> f x = f y).
Proof using.
  intros * equivR.
  apply ex_bijection_iso.
  define exists.
  { intro c.
    admit.
  }
Admitted.

Theorem quotient_disjoint_decomposition : forall A R {equivR: Equivalence R},
  (Σ a, { !c : A/R | In c a}) ≃ A.
Proof using.
  intros * equivR.
  define exists by (now intros [? _]).
  define exists.
  { intros a.
    exists a (qclass R a).
    split.
    - now apply in_qclass.
    - intros.
      symmetry.
      now apply qclass_eq.
  }
  split.
  - easy.
  - intros (? & ? & ? & ?).
    f_equal.
    apply exist_eq.
    symmetry.
    now apply qclass_eq.
Qed.

Theorem sigma_binary_sum : forall A B,
  A + B ≃ Σ b: 2, if b then A else B.
Proof using.
  intros *.
  define exists.
  { intros [?|?].
    + now exists (inl tt).
    + now exists (inr tt).
  }
  define exists by (intros [[|] ?]; auto).
  split.
  - now intros [[[]|[]] ?].
  - now intros [?|?].
Qed.

Theorem pi_binary_prod : forall A B,
  A × B ≃ Π b: 2, if b then A else B.
Proof using.
  intros *.
  define exists by (now intros [? ?] [[]|[]]).
  exists (λ f, (f (inl tt), f (inr tt))).
  split.
  - intros H.
    extensionality b.
    now destruct b as [[]|[]].
  - now intros [? ?].
Qed.


Close Scope program_scope.
