Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.

Definition access_eq {component} (a1 a2: access component) :=
  forall c p, a1 c p <-> a2 c p.

(* TODO: move these definitions *)
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.
Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.


Inductive sprop (comp loc: Set) :=
  | val_at  : forall v, loc -> access comp -> v -> sprop comp loc
  (* | sep_pure : Prop -> sprop comp loc *)
  | empty   : Prop -> sprop comp loc
  | sep_con : sprop comp loc -> sprop comp loc -> sprop comp loc.

Arguments val_at  {comp loc v}%type_scope.
(* Arguments sep_pure {comp loc}%type_scope. *)
Arguments empty   {comp loc}%type_scope.
Arguments sep_con {comp loc}%type_scope.

Notation "l ; a ↦ v" := (val_at l a v) (at level 50).
(* Notation "⟨ p ⟩" := (sep_pure p) (at level 0).
Notation "⟨ ⟩" := (sep_pure True) (at level 0). *)
Notation "⟨⟩" := (empty) (at level 0).
Notation "x ** y" := (sep_con x y) (at level 55, right associativity).
