Require Import Notation.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Combinators.
Require Import Setoid.

Require Import Tactics.Tactics.
Require Import Axioms.

Open Scope program_scope.


Definition isomorphic A B : Prop :=
  exists (f: A -> B) (g: B -> A), 
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

Definition isomorphism A B :=
  Σ (f: A -> B) (g: B -> A),
    (forall b, f (g b) = b) /\
    (forall a, g (f a) = a).

Notation "A ≅ B"  := (isomorphic A B)  (at level 75).
Notation "A ≅> B" := (isomorphism A B) (at level 75).
(* Notation "A ≃ B"  := (isomorphic A B)  (at level 75).
Notation "A ≃> B" := (isomorphism A B) (at level 75). *)


(* Could also be called an automorphism *)
Definition permutation A := A ≅> A.


(* Analogous to reflexivity *)
Definition id_isomorphism A : A ≅> A.
  now exists id id.
Defined.

(* Analogous to symmetry *)
Definition isomorphism_invert {A B} (ϕ: A ≅> B) : B ≅> A.
  destruct ϕ as (f & g & ?).
  now exists g f.
Defined.
Notation "ϕ ⁻¹" := (isomorphism_invert ϕ)
  (at level 5, format "ϕ ⁻¹").

(* Class invertible {U} (P: U -> U -> Type) :=
  {inverse : forall {A B}, P A B -> P B A}.
Notation "x ⁻¹" := (inverse x) (at level 5, format "x ⁻¹").

Instance isomorphism_invertible : invertible isomorphism := 
  {inverse := @isomorphism_invert}. *)

(* Analogous to transitivity *)
Theorem isom_compose {X Y Z}: 
  X ≅> Y ->
  Y ≅> Z ->
  X ≅> Z.
Proof using.
  intros * Hxy Hyz.
  destruct Hxy as (fxy & gyx & fxy_gyx & gyx_fxy).
  destruct Hyz as (fyz & gzy & fyz_gzy & gzy_gyz).
  exists (fyz ∘ fxy) (gyx ∘ gzy).
  split; intros; unfold compose; find rewrite ->; assumption!.
Defined. 


(* Projections and lifts *)

Definition iso_proj1 {A B} (ϕ: A ≅> B) : A -> B := 
  match ϕ with 
  | existT _ f _ => f
  end.
Coercion iso_proj1 : isomorphism >-> Funclass.

Definition iso_proj2 {A B} (ϕ: A ≅> B) : B -> A :=
  match ϕ with 
  | existT _ _ (existT _ g _) => g
  end.

Definition iso_liftl {A B X: Type} (ϕ: A ≅> B) (f: A -> A) : B -> B :=
  iso_proj1 ϕ ∘ f ∘ iso_proj2 ϕ.

Definition iso_lift2 {A B X: Type} (ϕ: A ≅> B) (f: B -> B) : A -> A :=
  iso_proj2 ϕ ∘ f ∘ iso_proj1 ϕ.


Definition iso_construct_proj1 {A B} (ϕ: A ≅ B) : ~> (A -> B) :=
  match ϕ with 
  | ex_intro _ f _ => inhabits f
  end.

Definition iso_construct_proj2 {A B} (ϕ: A ≅ B) : ~> (B -> A) :=
  match ϕ with 
  | ex_intro _ _ (ex_intro _ g _) => inhabits g
  end.


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
(* Instance isomorphic_invertible : invertible isomorphic := 
  {inverse := iso_sym}. *)


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
  A ≅> B ->
  A ≅ B.
Proof using.
  intros H.
  destruct exists H f g.
  now exists f g.
Qed. 
Coercion isomorphism__isomorphic : isomorphism >-> isomorphic.

Theorem isomorphic__isomorphism {A B}:
  A ≅ B ~>
  A ≅> B.
Proof using.
  intros H.
  destruct exists H f g.
  constructor.
  now exists f g.
Qed.

Theorem iso_cancel_inv {A B}: forall (ϕ: A ≅> B) b,
  ϕ (ϕ⁻¹ b) = b.
Proof using.
  intros.
  destruct ϕ as (? & ? & ?).
  assumption!.
Qed.

Theorem inv_cancel_iso {A B}: forall (ϕ: A ≅> B) a,
  ϕ⁻¹ (ϕ a) = a.
Proof using.
  intros.
  destruct ϕ as (? & ? & ?).
  assumption!.
Qed.

Theorem inv_cancel_inv {A B}: forall (ϕ: A ≅> B),
  (ϕ⁻¹)⁻¹ = ϕ.
Proof using.
  intros *.
  now destruct ϕ as (? & ? & ?).
Qed.

Theorem iso_iso_inv {A B}: 
  (A ≅> B) ≅> (B ≅> A).
Proof using.
  do 2 exists isomorphism_invert.
  split; intros *; apply inv_cancel_inv.
Defined.

(* Reflect a proof goal into the domain of the isomorphism *)
Theorem isomorphism_refl {A B}: forall P: B -> Type,
  forall ϕ: A ≅> B,
  (forall a, P (ϕ a)) -> 
  forall b, P b.
Proof using.
  intros * ? b.
  find specialize (ϕ⁻¹ b).
  now find rewrite iso_cancel_inv in.
Defined.

(* Reflect a proof goal into the image of the isomorphism *)
Theorem isomorphism_refl_inv {A B}: forall P: A -> Type,
  forall ϕ: A ≅> B,
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
  | ?A ≅> ?B =>
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
  | ?A ≅ ?B =>
      match goal with 
      | |- ?g =>
          match type of g with 
          | Prop => idtac
          | _ => fail "Prop-level isomorphism cannot be used on a non-Prop goal"
          end
      end;
      construct isomorphic__isomorphism in Hϕ;
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
  forall ϕ: A ≅> B,
  (Σ a, P (ϕ a)) ->
  Σ b, P b.
Proof using.
  intros * [a H].
  now exists (ϕ a).
Qed.

Theorem isomorphism_refl_sig_inv {A B}: forall P: A -> Type,
  forall ϕ: A ≅> B,
  (Σ b, P (ϕ⁻¹ b)) ->
  Σ a, P a.
Proof using.
  intros * [a H].
  now exists (ϕ⁻¹ a).
Qed.

Theorem isomorphism_refl_exists {A B}: forall P: B -> Prop,
  forall ϕ: A ≅> B,
  (exists a, P (ϕ a)) ->
  exists b, P b.
Proof using.
  intros * [a H].
  now exists (ϕ a).
Qed.

Theorem isomorphism_refl_exists_inv {A B}: forall P: A -> Prop,
  forall ϕ: A ≅> B,
  (exists b, P (ϕ⁻¹ b)) ->
  exists a, P a.
Proof using.
  intros * [a H].
  now exists (ϕ⁻¹ a).
Qed.


Definition iso_equiv {A B C} (ϕ: A ≅> B) (fa : A -> C) (fb : B -> C) :=
  forall a, fa a = fb (ϕ a).

Theorem iso_equiv_flip {A B C}: forall (ϕ: A ≅> B) (fa : A -> C) (fb : B -> C),
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


Definition iso_image_lift {A B} (ϕ: A ≅> B) (b: B) : image ϕ.
  exists b (ϕ⁻¹ b).
  apply iso_cancel_inv.
Defined.

Theorem iso_image {A B}: forall ϕ: A ≅> B,
  image ϕ ≅> B.
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
Qed.

Theorem iso_image_inv {A B}: forall ϕ: A ≅> B,
  image ϕ⁻¹ ≅> A.
Proof using.
  intros *.
  iso iso_iso_inv ϕ.
  cbn.
  rewrite inv_cancel_inv.
  apply iso_image.
Qed.


Definition injective  {A B} (f: A -> B) := forall a a', f a = f a' -> a = a'.
Definition surjective {A B} (f: A -> B) := forall b, exists a, f a = b.
Definition bijective  {A B} (f: A -> B) := injective f /\ surjective f.

Definition f_image {A B} (f: A -> B) : A -> image f.
  intro a.
  now exists (f a) a.
Defined.

(* Dependent on axiomatic classical choice to construct inverse *)
Theorem inverse_injection : forall A B (f: A -> B),
  injective f ->
  exists g: image f -> A, 
    (forall i, f_image f (g i) = i) /\
    (forall a, g (f_image f a) = a).
Proof using.
  intros * Hinj.
  transform Hinj (injective (f_image f)).
  { unfold injective.
    intros * H.
    invc H as [H].
    now apply Hinj in H.
  }
  pose proof (choice (fun i a => f_image f a = i)) as g.
  forward g.
  { intros (x & y & <-). now exists y. }
  destruct g as [g H].
  exists g.
  split; [assumption|].
  intros *.
  specialize (H (f_image f a)).
  now apply Hinj in H.
Qed.

(* Dependent on axiomatic classical choice to construct inverse *)
Theorem f_iso_f_image : forall A B (f: A -> B),
  injective f ->
  A ≅ image f.
Proof using.
  intros * Hinj.
  pose proof (inverse_injection A B f Hinj) as [g ?].
  now exists (f_image f) g.
Qed. 


Theorem iso_prop : forall P Q: Prop,
  P ≅ Q ->
  (P <-> Q).
Proof using.
  intros * H.
  now destruct H as (? & ? & ?).
Qed.

(* An isomorphism of Props is equality, assuming extensionality *)
Theorem iso_prop_extenionality : forall P Q: Prop,
  (P ≅ Q) = (P = Q).
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
  (P ≅ Q) <-> (P <-> Q).
Proof using.
  intros * proof_irrelevance.
  split.
  - intro ϕ.
    construct isomorphic__isomorphism in ϕ.
    split; intros ?.
    + now apply ϕ.
    + now apply (ϕ⁻¹).
  - intros [H1 H2].
    exists H1 H2.
    split; intros; apply proof_irrelevance.
Qed.

Theorem iso_proof_irrelevance2 : forall P Q: Prop,
  (forall (P: Prop) (p1 p2: P), p1 = p2) ->
  (P ≅ Q) ≅ (P <-> Q).
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

(* Think twice before including this axiom. It's not necessarily compatible
   with other common axioms! (for instance, UIP / K)
 *)
Axiom weak_univalence : forall A B,
  (A ≅ B) -> A = B.

(* weak univalence + proof irrelevance *)
Theorem univalence : forall A B,
  (A = B) ≅ (A ≅ B).
Proof using.
  intros *.
  define exists by (intros ->; apply iso_refl).
  exists (weak_univalence A B).
  split; intros; apply proof_irrelevance.
Qed.

(* univalence + prop extensionality *)
Theorem strong_univalence : 
  forall A B, (A = B) = (A ≅ B).
Proof using. 
  intros *.
  rewrite <- iso_prop_extenionality.
  apply univalence.
Qed.

(* This does not apply the isomorphism, it simply casts the type *)
Definition cast {A B} (ϕ: A ≅ B) (a: A) : B.
  rewrite <- strong_univalence in ϕ.
  now destruct ϕ.
Defined.

(* This does not apply the isomorphism, it simply casts the type *)
Definition cast_inv {A B} (ϕ: A ≅ B) (b: B) : A.
  symmetry in ϕ.
  now apply (cast ϕ).
Defined.

Lemma cast_inv_eq_cast_sym : forall A B (ϕ: A ≅ B), 
  cast_inv ϕ = cast (iso_sym _ _ ϕ).
Proof using.
  reflexivity.
Qed.

Theorem cast_eq : forall A B (ϕ: A ≅ B) a,
  cast ϕ a ~= a.
Proof using.
  intros *.
  unfold cast.
  destruct strong_univalence.
  now subst.
Qed. 

Theorem cast_inv_eq : forall A B (ϕ: A ≅ B) b,
  cast_inv ϕ b ~= b.
Proof using.
  intros *.
  rewrite cast_inv_eq_cast_sym.
  apply cast_eq.
Qed. 

Close Scope program_scope.