Require Import Ctl.Paths.

Require Import Coq.Relations.Relation_Definitions.

Inductive TProp state : Type :=
  | TTop  : TProp state
  | TBot  : TProp state
  | TLift : (state -> Prop) -> TProp state
  | TNot  : TProp state -> TProp state
  | TConj : TProp state -> TProp state -> TProp state
  | TDisj : TProp state -> TProp state -> TProp state
  | TImpl : TProp state -> TProp state -> TProp state
  | AX    : TProp state -> TProp state
  | EX    : TProp state -> TProp state
  | AF    : TProp state -> TProp state
  | EF    : TProp state -> TProp state
  | AG    : TProp state -> TProp state
  | EG    : TProp state -> TProp state
  | AU    : TProp state -> TProp state -> TProp state
  | EU    : TProp state -> TProp state -> TProp state.

(* Make state argument implicit *)
Arguments TTop  {state}%type_scope.
Arguments TBot  {state}%type_scope.
Arguments TLift {state}%type_scope.
Arguments TNot  {state}%type_scope.
Arguments TConj {state}%type_scope.
Arguments TDisj {state}%type_scope.
Arguments TImpl {state}%type_scope.
Arguments AX    {state}%type_scope.
Arguments EX    {state}%type_scope.
Arguments AF    {state}%type_scope.
Arguments EF    {state}%type_scope.
Arguments AG    {state}%type_scope.
Arguments EG    {state}%type_scope.
Arguments AU    {state}%type_scope.
Arguments EU    {state}%type_scope.

Notation "⊤" := (TTop).
Notation "⊥" := (TBot).
(* Notation "⟨ P ⟩" := (TLift P) (at level 35). *)
Notation "P ∧ Q" := (TConj P Q) (at level 45, right associativity).
Notation "P ∨ Q" := (TDisj P Q) (at level 55, right associativity).
Notation "P --> Q" := (TImpl P Q) (at level 68,  right associativity).
Notation "P <--> Q" := ((P --> Q) ∧ (Q --> P)) (at level 65,  right associativity).
Notation "¬ P" := (TNot P) (at level 40).
Notation "'A' [ P 'U' Q ]" := (AU P Q) (at level 40).
Notation "'E' [ P 'U' Q ]" := (EU P Q) (at level 40).

Reserved Notation "M ; s ⊨ P" (at level 70).
Reserved Notation "M ; s ⊭ P" (at level 70).
(* Replace binary_relation with serial_transition if needed *)
Fixpoint tEntails {state} (R: relation state) (s: state) (tp: TProp state) : Prop :=
  match tp with
  | ⊤ => True
  | ⊥ => False
  | TLift P => P s
  | ¬P => R;s ⊭ P
  | P ∧ Q => R;s ⊨ P /\ R;s ⊨ Q
  | P ∨ Q => R;s ⊨ P \/ R;s ⊨ Q
  | P --> Q => R;s ⊨ P -> R;s ⊨ Q
  | AX P => forall s', R s s' -> R;s' ⊨ P
  | EX P => exists s', R s s' -> R;s' ⊨ P
  | AG P => forall n, forall (p: path R s n), forall s', in_path s' p -> R;s' ⊨ P
  | EG P => forall n, exists (p: path R s n), forall s', in_path s' p -> R;s' ⊨ P
  | AF P => exists n, forall (p: path R s n), exists s', in_path s' p /\ R;s' ⊨ P
  | EF P => exists n, exists (p: path R s n), exists s', in_path s' p /\ R;s' ⊨ P
  (* TODO: AU and EU *)
  | _ => False
  end
  where "M ; s ⊨ P" := (tEntails M s P)
    and "M ; s ⊭ P" := (~ M;s ⊨ P).

