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

(* Is acc_at a spatial predicate? I think so *)
Inductive sprop (comp loc: Set) :=
  | sep_con : sprop comp loc -> sprop comp loc -> sprop comp loc
  (* | sep_at  : forall v, loc -> access -> v -> sprop loc *)
  | val_at  : forall v, loc -> v -> sprop comp loc
  | acc_at  : loc -> access comp -> sprop comp loc
  | empty   : sprop comp loc.

Arguments sep_con {comp loc}%type_scope.
Arguments val_at  {comp loc v}%type_scope.
Arguments acc_at  {comp loc}%type_scope.
Arguments empty   {comp loc}%type_scope.

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

Reserved Notation "X ⊢ Y" (at level 70).
(* Reserved Notation "X ⊬ Y" (at level 70). *)
Inductive sEntails {comp loc} : sprop comp loc -> sprop comp loc -> Prop :=
  | sep_con_comm  : forall X Y, X ** Y ⊢ Y ** X
  | sep_con_assoc : forall X Y Z, X ** Y ** Z ⊢ (X ** Y) ** Z
  where "X ⊢ Y" := (sEntails X Y).
