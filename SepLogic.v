Require Import GeneralTactics.
Require Import Coq.Program.Equality.

Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.

Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.

Inductive sprop (comp loc: Set) :=
  | sep_con  : sprop comp loc -> sprop comp loc -> sprop comp loc
  | val_at   : forall v, loc -> v -> sprop comp loc
  | acc_at   : loc -> access comp -> sprop comp loc
  | sep_pure : Prop -> sprop comp loc.

Arguments sep_con  {comp loc}%type_scope.
Arguments val_at   {comp loc v}%type_scope.
Arguments acc_at   {comp loc}%type_scope.
(* Arguments empty   {comp loc}%type_scope. *)
Arguments sep_pure {comp loc}%type_scope.

(* Declare Scope sep_scope. *)
(* Bind Scope sep_scope with sprop. *)

(* Not sure why this is disallowed. Todo, look at other coq sep logics. *)
(* Notation "X * Y" := (sep_con X Y) (at level 45, right associativity) : sep_scope. *)
Notation "X ** Y" := (sep_con X Y) (at level 55, right associativity).
Notation "l ↦ v" := (val_at l v) (at level 50).
(* Also not sure why this one isn't working *)
(* Notation "l : V ↦ v" := (@val_at _ _ V l v) (at level 40). *)
(* Check (0 ↦ 1). *)
(* Check (0 : nat ↦ 1). *)
Notation "a @ l" := (acc_at l a) (at level 50).

Inductive overlap {comp loc}: sprop comp loc -> sprop comp loc -> Prop :=
  | overlap_val_at : forall l V1 (v1: V1) V2 (v2: V2),
      overlap (l ↦ v1) (l ↦ v2)
  | overlap_acc_at : forall l a1 a2,
      overlap (l @ a1) (l @ a2)
  | overlap_sep_con_left : forall x y z,
      overlap x z \/ overlap y z ->
      overlap (x ** y) z
  | overlap_sep_con_right : forall x y z,
      overlap x y \/ overlap x z ->
      overlap x (y ** z).
Definition separate {comp loc} (x y: sprop comp loc ):=
  ~ overlap x y.

(* TODO, introduce sep_eq? *)
Reserved Notation "X ⊢ Y" (at level 70).
Inductive sEntails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | sep_con_intro : forall x x' y y',
      x ⊢ x' ->
      y ⊢ y' ->
      separate x y ->
      x ** y ⊢ x' ** y'
  | sep_con_comm  : forall x y, 
      x ** y ⊢ y ** x
  | sep_con_assoc_l : forall x y z,
      x ** y ** z ⊢ (x ** y) ** z
  | sep_con_assoc_r : forall x y z,
      (x ** y) ** z ⊢ x ** y ** z
  | pure_entails : forall (p q: Prop),
      (p -> q) ->
      sep_pure p ⊢ sep_pure q
  | sEntails_refl : forall x,
      x ⊢ x
  | sEntails_trans : forall x y z,
      x ⊢ y ->
      y ⊢ z ->
      x ⊢ z
  where "x ⊢ y" := (sEntails x y).
Notation "x ⊬ y" := (~ x ⊢ y) (at level 70).

Definition empty {comp loc}: sprop comp loc := sep_pure True.

Definition flip_sEntails_trans {comp loc}: forall (x y z: sprop comp loc),
  y ⊢ z ->
  x ⊢ y ->
  x ⊢ z.
Proof.
  intros.
  eapply sEntails_trans; eassumption.
Qed.

(* Tactics *)

Tactic Notation "normalize_sprop" :=
  repeat match goal with 
  | [_:_ |- (_ ** _) ** _ ⊢ _] => 
      simple apply (sEntails_trans _ _ _ (sep_con_assoc_r _ _ _))
  | [_:_ |- _ ⊢ (_ ** _) ** _] =>
      simple apply (flip_sEntails_trans _ _ _ (sep_con_assoc_l _ _ _))
  end.

Tactic Notation "normalize_sprop" "in" hyp(H) :=
  repeat match type of H with 
  | (_ ** _) ** _ ⊢ _ => 
      simple apply (sEntails_trans _ _ _ (sep_con_assoc_l _ _ _)) in H
  | _ ⊢ (_ ** _) ** _ =>
      simple apply (flip_sEntails_trans _ _ _ (sep_con_assoc_r _ _ _)) in H
  end.

Tactic Notation "normalize_sprop" "in" "*" :=
  repeat match goal with
  | [H:_ |- _] => normalize_sprop in H
  end.

Ltac normalize_sprops := normalize_sprop; normalize_sprop in *.

(* Lemma foo {comp loc}: forall (a b c: sprop comp loc),
  (a ** b) ** c ⊢ (a ** b) ** c ->
  (a ** b) ** c ⊢ (a ** b) ** c.
Proof.
  intros.
  normalize_sprops. *)

Ltac sprop_facts :=
  repeat match goal with 
  | [H1: _ ⊢ ?x, H2: ?x ⊢ _ |- _] => pose new proof (sEntails_trans _ _ _ H1 H2)
  end.

(* Lemma foo {comp loc}: forall (a b c: sprop comp loc),
  a ⊢ b -> b ⊢ c -> a ⊢ c.
Proof.
  intros.
  sprop_facts. *)

(* Ltac percolate_up_sprop x H := *)

Ltac sentails :=
  normalize_sprops;
  (* repeat *)
  match goal with
  | [_:_ |- ?x ⊢ ?x] => exact (sEntails_refl x)
  (* find common conjuncts, shuffle them to the left side, then elim them *)
  (* | [_:_ |- ?x ** ?y ⊢ ?z] => *)
  (* | [H: ?x ⊢ ?y |- ?x ⊢ ?y] => exact H *)
  end.

Lemma sep_con_only_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ** y ⊢ z -> exists x' y', z = x' ** y'.
Proof.
  intros.
  dependent induction H; eauto.
  specialize (IHsEntails1 x y).
  cut IHsEntails1 by reflexivity.
  destruct exists IHsEntails1 x' y'.
  subst.
  eapply IHsEntails2.
  reflexivity.
Qed. 

Lemma only_sep_con_entails_sep_con {comp loc}: forall (x y z: sprop comp loc),
  x ⊢ y ** z -> exists y' z', x = y' ** z'.
Proof.
  intros.
  dependent induction H; eauto.
  specialize (IHsEntails2 y z).
  cut IHsEntails2 by reflexivity.
  destruct exists IHsEntails2 y' z'.
  subst.
  eapply IHsEntails1.
  reflexivity.
Qed.

Lemma val_at_only_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
  l ↦ v ⊢ z -> z = l ↦ v.
Proof.
  intros. dependent induction H; auto.
Qed.

Lemma only_val_at_entails_val_at {comp loc}: forall l V (v: V) (z: sprop comp loc),
  z ⊢ l ↦ v -> z = l ↦ v.
Proof.
  intros. dependent induction H; auto.
Qed.

Lemma acc_at_only_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
  a @ l ⊢ z -> z = a @ l.
Proof.
  intros. dependent induction H; auto.
Qed.

Lemma only_acc_at_entails_acc_at {comp loc}: forall a l (z: sprop comp loc),
  z ⊢ a @ l -> z = a @ l.
Proof.
  intros. dependent induction H; auto.
Qed.

(* Ltac _espec_cut_by H tac :=
  match type of H with
  | _ -> _ =>
      cut H by tac;
      _espec_cut_by H tac
  | forall (x: ?t), _ => 
      let xfresh := fresh x in
      evar (xfresh: t);
      specialize (H xfresh);
      _espec_cut_by H tac
  | _ => idtac
  end.
Tactic Notation "espec_cut" hyp(H) "by" tactic(tac) := _espec_cut_by H tac. *)

Lemma sep_pure_only_entails_sep_pure {comp loc}: forall (p: Prop) (z: sprop comp loc),
  sep_pure p ⊢ z -> exists (q: Prop), (p -> q) /\ z = sep_pure q.
Proof.
  intros.
  dependent induction H; eauto.
  (* TODO: specializecut tactic which automatically specializes to cut *)
  specialize (IHsEntails1 p).
  cut IHsEntails1 by reflexivity.
  destruct exists IHsEntails1 q.
  specialize (IHsEntails2 q).
  cut IHsEntails2 by my_crush.
  destruct exists IHsEntails2 q'.
  exists q'.
  destruct IHsEntails1; destruct IHsEntails2; auto.
Qed.

Lemma only_sep_pure_entails_sep_pure {comp loc}: forall (q: Prop) (z: sprop comp loc),
  z ⊢ sep_pure q -> exists (p: Prop), (p -> q) /\ z = sep_pure p.
Proof.
  intros.
  dependent induction H; eauto.
  specialize (IHsEntails2 q).
  cut IHsEntails2 by reflexivity.
  destruct exists IHsEntails2 p.
  specialize (IHsEntails1 p).
  cut IHsEntails1 by my_crush.
  destruct exists IHsEntails1 p'.
  exists p'.
  destruct IHsEntails1; destruct IHsEntails2; auto.
Qed.

(* Lemma bar {comp loc: Set}: forall (l l': loc) V (v: V) (a: access comp),
  ((l ↦ v) : sprop comp loc) ⊬ (a @ l').
Proof.
  unfold not. intros.
  simple apply val_at_only_entails_val_at in H.
  discriminate H.
Qed. *)

(* Tactic Notation "sprop_discriminate" hyp(H) :=
  match type of H with
  | _ ↦ _ ⊢ _ => simple apply val_at_only_entails_val_at in H; discriminate H
  | _ @ _ ⊢ _ => simple apply acc_at_only_entails_acc_at in H; discriminate H
  | empty ⊢ _ => simple apply empty_only_entails_empty in H; discriminate H
  end. *)

Tactic Notation "destruct" "or" hyp(H) := destruct H as [H|H].

Lemma inv_sep_con_entails {comp loc}: forall (a b c d: sprop comp loc),
  a ** b ⊢ c ** d ->
  (a ⊢ c /\ b ⊢ d) \/ (a ⊢ d /\ b ⊢ c).
Proof.
  intros a b c d H.
  dependent induction H.
  - left. split; assumption.
  - right. split; apply sEntails_refl.
  - admit.
  - admit.
  - left. split; apply sEntails_refl.
  - apply sep_con_only_entails_sep_con in H.
    destruct exists H x' y'.
    subst.
    specialize (IHsEntails1 a b x' y').
    specialize (IHsEntails2 x' y' c d).
    auto_cut by reflexivity.
    destruct or IHsEntails1;
    destruct IHsEntails1;
    destruct or IHsEntails2;
    destruct IHsEntails2;
    sprop_facts; auto.
Admitted.

Ltac sprop_discriminate_basic H :=
  match type of H with
  | _ ⊢ _ =>
    ((simple apply val_at_only_entails_val_at in H
    + simple apply acc_at_only_entails_acc_at in H
    + simple apply sep_pure_only_entails_sep_pure in H
    ); discriminate H) +
    ((simple apply only_val_at_entails_val_at in H
    + simple apply only_acc_at_entails_acc_at in H
    + simple apply only_sep_pure_entails_sep_pure in H
    ); discriminate H) +
    fail "Could not discriminate sprop"
  end.

(* Note, Tactic Notation doesn't put name into scope, so we first define it using the
   Ltac command to achieve recursive definition. *)
Ltac _sprop_discriminate H :=
  match type of H with
  | _ ⊢ _ =>
    sprop_discriminate_basic H + (
      simple apply inv_sep_con_entails in H;
      destruct or H; 
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [H1 H2];
      (_sprop_discriminate H1) + (_sprop_discriminate H2)
    )
  end.
Tactic Notation "sprop_discriminate" hyp(H) := _sprop_discriminate H.

Tactic Notation "sprop_discriminate" :=
  unfold not;
  intros;
  sprop_facts;
  match goal with
  | [H: _ |- _] => sprop_discriminate H
  end.

(* Lemma foobar {comp loc: Set}: forall (l: loc) V (v: V) (a: access comp),
  (l ↦ v ** empty : sprop comp loc) ⊬ (empty ** a @ l : sprop comp loc).
Proof.
  intros.
  sprop_discriminate.
Qed. *)