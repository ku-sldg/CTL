
Require Import Coq.Relations.Relation_Definitions.

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
  (* | sep_pure : Prop -> sprop comp loc *)
  | empty   : sprop comp loc
  | sep_con : sprop comp loc -> sprop comp loc -> sprop comp loc.

Arguments val_at  {comp loc v}%type_scope.
(* Arguments sep_pure {comp loc}%type_scope. *)
Arguments empty   {comp loc}%type_scope.
Arguments sep_con {comp loc}%type_scope.

Notation "l # a ↦ v" := (val_at l a v) (at level 50).
(* Notation "⟨ p ⟩" := (sep_pure p) (at level 0).
Notation "⟨ ⟩" := (sep_pure True) (at level 0). *)
Notation "⟨⟩" := (empty) (at level 0).
Notation "x ** y" := (sep_con x y) (at level 55, right associativity).
