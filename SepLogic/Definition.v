Notation component := nat (only parsing).

Inductive privilege : Set :=
  | read 
  | write 
  | exec.

Definition access component := component -> privilege -> Prop.

(* TODO: move these definitions *)
Inductive readonly {component} : access component :=
  | ro : forall c, readonly c read.
Inductive private {component} (c: component): access component :=
  | anyPriv : forall (p: privilege), private c c p.

(* This separation logic is restricted in its lack of arbitrary propositions,
   and its treatment of `empty` (which is only equal to and can only entail `empty`) *)
Inductive sprop (comp loc: Set) :=
  | sep_con  : sprop comp loc -> sprop comp loc -> sprop comp loc
  | val_at   : forall v, loc -> v -> sprop comp loc
  | acc_at   : loc -> access comp -> sprop comp loc
  | empty : sprop comp loc.

Arguments sep_con {comp loc}%type_scope.
Arguments val_at  {comp loc v}%type_scope.
Arguments acc_at  {comp loc}%type_scope.
Arguments empty   {comp loc}%type_scope.

Notation "X ** Y" := (sep_con X Y) (at level 55, right associativity).
Notation "l ↦ v" := (val_at l v) (at level 50).
Notation "a @ l" := (acc_at l a) (at level 50).
