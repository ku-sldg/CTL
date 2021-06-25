Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.

Require Import Coq.Relations.Relation_Definitions.

Inductive path {state} (R: relation state) : list state -> Prop :=
  | pathRefl  : forall s, path R [s]
  | pathTrans : forall s1 s2 p, R s1 s2 -> path R (s2 :: p) -> path R (s1 :: s2 :: p).

(* Inductive TProp (state: Set) : Type := *)
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

(* s ⊨ AG P := forall s', s ~>* s' => P s'

EF
 | P holds for s
 | exists s', s ~>* s' /\ P s'

EG := forall s', EG_aux s' -> exists s'' EG_aux s'' ?
EG_aux
 | P holds for s
 | exists

(EG) exists_forall_path P s := P s /\
  (forall s', forall_path_seg R P s s' -> forall_path_seg R P s s'')
forall_path_seg R P s : state -> Prop :=
 | P s -> forall_path_seg s s
 | forall_path P s s' -> R s s'' -> P s'' -> forall_path_seg P s s''

exists_forall_path_seg R P s : state -> Prop := 
  | P s -> exists_forall_path_seg R P s s
  | exists_forall_path P s s' -> R s s'' -> P s'' -> exists_forall_path_seg P s s''
exists_forall_path R P s := P s /\ (forall s', exists_forall_path_seg R P s -> ) *)

Reserved Notation "M ; s ⊨ P" (at level 70).
Reserved Notation "M ; s ⊭ P" (at level 70).
(* Replace binary_relation with serial_transition if needed *)
Fixpoint tEntails {state} (M: relation state) (s: state) (tp: TProp state): Prop :=
  match tp with
  | TTop => True
  | TBot => False
  | TLift P => P s
  | TNot P => M;s ⊭ P
  | TConj P Q => M;s ⊨ P /\ M;s ⊨ Q
  | TDisj P Q => M;s ⊨ P \/ M;s ⊨ Q
  | TImpl P Q => M;s ⊨ P -> M;s ⊨ Q
  | AX P => forall s', M s s' -> M;s' ⊨ P
  | EX P => exists s', M s s' -> M;s' ⊨ P
  | AG P => forall p, path M (s :: p) -> forall s', In s' (s :: p) -> M;s' ⊨ P
  | EG P => exists p, path M (s :: p) /\ forall s', In s' (s :: p) -> M;s' ⊨ P
  | AF P => forall p, path M (s :: p) -> exists s', In s' (s :: p) /\ M;s' ⊨ P
  | EF P => exists p, path M (s :: p) /\ exists s', In s' (s :: p) /\ M;s' ⊨ P
  (* Needs index. Maybe replace neList with vec, and zip with index *)
  (* | AU P Q => forall p, path m s p -> exists s', inPath s' p /\ M;s' ⊨ P /\ forall s'', inPath s'' (pathBefore s' p) ->  *)
  | _ => False
  end
  where "M ; s ⊨ P" := (tEntails M s P)
    and "M ; s ⊭ P" := (~ M;s ⊨ P).

Notation "⊤" := (TTop).
Notation "⊥" := (TBot).
Notation "^ P" := (TLift P) (at level 35).
Notation "P ∧ Q" := (TConj P Q) (at level 45, right associativity).
Notation "P ∨ Q" := (TDisj P Q) (at level 55, right associativity).
Notation "P --> Q" := (TImpl P Q) (at level 68,  right associativity).
Notation "P <--> Q" := ((P --> Q) ∧ (Q --> P)) (at level 65,  right associativity).
Notation "¬ P" := (TNot P) (at level 40).
Notation "'A' [ P 'U' Q ]" := (AU P Q) (at level 40).
Notation "'E' [ P 'U' Q ]" := (EU P Q) (at level 40).
