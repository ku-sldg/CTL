Require Import Coq.Relations.Relation_Definitions.

Require Import GeneralTactics.

Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.

Definition access_eq {component} (a1 a2: access component) :=
  forall c p, a1 c p <-> a2 c p.

Theorem access_eq_is_eq {comp}: equivalence (access comp) access_eq.
Proof using.
  split.
  - easy.
  - unfold access_eq.
    intros a1 a2 a3 Hab Hbc.
    intros c p.
    split; intro H.
    + apply Hbc.
      apply Hab.
      assumption.
    + apply Hab.
      apply Hbc.
      assumption.
  - unfold symmetric, access_eq.
    intros x y H c p.
    split; intro H2. 
    + apply H. assumption.
    + apply H. assumption.
Qed.
Lemma access_eq_refl {comp}: reflexive (access comp) access_eq.
Proof.
  exact (equiv_refl _ _ access_eq_is_eq).
Qed.
Lemma access_eq_sym {comp}: symmetric (access comp) access_eq.
Proof.
  exact (equiv_sym _ _ access_eq_is_eq).
Qed.
Lemma access_eq_trans {comp}: transitive (access comp) access_eq.
Proof.
  exact (equiv_trans _ _ access_eq_is_eq).
Qed.

(* TODO: move these definitions *)
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.
Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.


Inductive sprop (comp loc: Set) :=
  | val_at  : forall v, loc -> access comp -> v -> sprop comp loc
  | empty   : sprop comp loc
  | sep_con : sprop comp loc -> sprop comp loc -> sprop comp loc.

Arguments val_at  {comp loc v}%type_scope.
Arguments empty   {comp loc}%type_scope.
Arguments sep_con {comp loc}%type_scope.

Notation "l # a ↦ v" := (val_at l a v) (at level 50).
Notation "⟨⟩" := (empty) (at level 0).
Notation "x ** y" := (sep_con x y) (at level 55, right associativity).

Inductive normal {comp loc}: sprop comp loc -> Prop :=
  | empty_normal: 
      normal ⟨⟩
  | val_at_normal: forall V l a (v: V),
      normal (l #a ↦ v)
  | sep_con_normal: forall V l a (v: V) s,
      s <> ⟨⟩ ->
      normal s ->
      normal (l #a ↦ v ** s).

Definition normal_sprop comp loc := {s: sprop comp loc | normal s}.

(* Auxiliary function. Coq couldn't find the decreasing structure when using 
   sig-typed arguments (as in `concat_norm_sprop`) *)
Fixpoint _concat_norm_sprop {comp loc}
  (s1 s2: sprop comp loc) (Hs1: normal s1) (Hs2: normal s2)
  : normal_sprop comp loc.
specialize (_concat_norm_sprop comp loc).
destruct s1.
- destruct s2.
  + exists (l #a ↦ v0 ** l0 #a0 ↦ v2).
    constructor.
    * discriminate.
    * assumption.
  + exists (l #a ↦ v0).
    assumption.
  + exists (l #a ↦ v0 ** s2_1 ** s2_2).
    constructor.
    * discriminate.
    * assumption.
- exists s2.
  assumption.
- destruct s1_1.
  + specialize (_concat_norm_sprop s1_2 s2).
    cut_hyp _concat_norm_sprop.
    { invc Hs1. assumption. }
    cut_hyp _concat_norm_sprop by assumption.
    destruct _concat_norm_sprop.
    destruct x.
    * exists (l #a ↦ v0 ** l0 #a0 ↦ v2).
      constructor.
     -- discriminate.
     -- constructor.
    * (* Should derive contradiction from Hs1 *)
      exists (l #a ↦ v0).
      constructor.
    * exists (l #a ↦ v0 ** x1 ** x2).
      constructor.
     -- discriminate.
     -- assumption.
  + exfalso. inv Hs1.
  + exfalso. inv Hs1.
Defined.

Definition concat_norm_sprop {comp loc} (s1 s2: normal_sprop comp loc)
  : normal_sprop comp loc :=
  match s1,s2 with 
  | exist _ s1' Hs1, exist _ s2' Hs2 => _concat_norm_sprop s1' s2' Hs1 Hs2
  end.

Fixpoint normalize {comp loc} (s: sprop comp loc): {s': sprop comp loc | normal s'} :=
  match s with
  | ⟨⟩ => exist _ ⟨⟩ empty_normal
  | l #a ↦ v => exist _ (l #a ↦ v) (val_at_normal _ l a v)
  | ⟨⟩ ** x => normalize x
  | x ** ⟨⟩ => normalize x
  | x ** y => concat_norm_sprop (normalize x) (normalize y)
  end.