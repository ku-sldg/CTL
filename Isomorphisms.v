Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Setoid.

Require Import Tactics.Tactics.

Open Scope program_scope.


Notation "'sigma' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'sigma' '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Notation "'Σ' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Σ'  '/ ' x .. y , '/ ' p ']'")
  : type_scope.

Definition iso (A B: Type) :=
  exists (f: A -> B) (g: B -> A), 
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

(* Transparent witnesses to an isomorphism *)
Definition isoT (A B: Type) :=
  Σ (f: A -> B) (g: B -> A),
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

Notation "A ≅ B" := (iso A B) (at level 75).


(* Projections and lifts *)

Definition iso_proj1 {A B} (ϕ: isoT A B) : A -> B :=
  match ϕ with 
  | existT _ f _ => f
  end.

Definition iso_proj2 {A B} (ϕ: isoT A B) : B -> A :=
  match ϕ with 
  | existT _ _ (existT _ g _) => g
  end.

Definition iso_liftl {A B X: Type} (ϕ: isoT A B) (f: A -> A) : B -> B :=
  iso_proj1 ϕ ∘ f ∘ iso_proj2 ϕ.

Definition iso_lift2 {A B X: Type} (ϕ: isoT A B) (f: B -> B) : A -> A :=
  iso_proj2 ϕ ∘ f ∘ iso_proj1 ϕ.

(* Properties *)

Theorem iso_refl :
  reflexive Type iso.
Proof using.
  unfold reflexive.
  intros.
  now exists id id.
Qed.

Theorem iso_sym : 
  symmetric Type iso.
Proof using.
  unfold symmetric.
  intros * H.
  destruct exists H f g.
  now exists g f.
Qed.

Theorem iso_trans :
  transitive Type iso.
Proof using.
  unfold transitive.
  intros * Hxy Hyz.
  destruct Hxy as (fxy & gyx & fxy_gyx & gyx_fxy).
  destruct Hyz as (fyz & gzy & fyz_gzy & gzy_gyz).
  exists (fyz ∘ fxy) (gyx ∘ gzy).
  split; intros *; unfold compose; find rewrite ->; find apply.
Qed. 

Add Parametric Relation : Type iso
  reflexivity  proved by iso_refl
  symmetry     proved by iso_sym
  transitivity proved by iso_trans
  as iso_rel.

Theorem isoT__iso {A B}:
  isoT A B ->
  iso A B.
Proof using.
  intros H.
  destruct exists H f g.
  now exists f g.
Qed. 

Theorem iso__isoT {A B}:
  iso A B ~>
  isoT A B.
Proof using.
  intros H.
  destruct exists H f g.
  constructor.
  now exists f g.
Qed.

Theorem iso_proj12_cancel {A B}: forall (ϕ: isoT A B) b,
  iso_proj1 ϕ (iso_proj2 ϕ b) = b.
Proof using.
  intros *.
  destruct ϕ as (? & ? & ? & ?).
  cbn.
  find apply.
Qed.

Theorem iso_proj21_cancel {A B}: forall (ϕ: isoT A B) a,
  iso_proj2 ϕ (iso_proj1 ϕ a) = a.
Proof using.
  intros *.
  destruct ϕ as (? & ? & ? & ?).
  cbn.
  find apply.
Qed.

Theorem iso_refl_type1 {A B}: forall P: B -> Prop,
  forall ϕ: isoT A B,
  (forall a, P (iso_proj1 ϕ a)) -> 
  forall b, P b.
Proof using.
  intros * ? *.
  find specialize (iso_proj2 ϕ b).
  find rewrite iso_proj12_cancel in.
  assumption.
Qed.

Theorem iso_refl_type2 {A B}: forall P: A -> Prop,
  forall ϕ: isoT A B,
  (forall b, P (iso_proj2 ϕ b)) -> 
  forall a, P a.
Proof using.
  intros * ? *.
  find specialize (iso_proj1 ϕ a).
  find rewrite iso_proj21_cancel in.
  assumption.
Qed.

Definition iso_construct_proj1 {A B} (ϕ: isoT A B) : ~> (A -> B) :=
  match ϕ with 
  | existT _ f _ => inhabits f
  end.

Definition iso_construct_proj2 {A B} (ϕ: isoT A B) : ~> (B -> A) :=
  match ϕ with 
  | existT _ _ (existT _ g _) => inhabits g
  end.

(* TODO: support parametric isomorphisms *)
(* by especialization? *)
Ltac iso i H :=
  match type of i with 
  | isoT ?A ?B =>
      pattern H;
      first [match type of H with
      | A => apply (fun goal => iso_refl_type2 _ i goal H)
      | B => apply (fun goal => iso_refl_type1 _ i goal H)
      end | fail "Hypothesis matches neither iso type"];
      clear H;
      intro
  | ?A ≅ ?B =>
      let fr := fresh "isoT" in
      epose proof i as fr;
      construct iso__isoT in fr;
      iso fr H
      (* clear fr *)
  end +
  fail "First argument not an iso".
