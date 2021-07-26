Require Import Ctl.Paths.
Require Import Coq.Relations.Relation_Definitions.

(* A very shallow CTL embedding *)


Definition tprop state := relation state -> state -> Prop.

Delimit Scope tprop_scope with tprop.
Open Scope tprop_scope.

Definition tentails {state} (R: relation state) (s: state) (P: tprop state) :=
  P R s.
Notation "R @ s ⊨ P" := (tentails R s P) (at level 70, format "R  @ s  ⊨  P") : tprop_scope.
Notation "R @ s ⊭ P" := (~ tentails R s P) (at level 70, format "R  @ s  ⊭  P") : tprop_scope.


(* State props *)

Definition ttop {state}: tprop state :=
  fun _ _ => True.

Definition tbot {state}: tprop state :=
  fun _ _ => False.
Definition tconj {state} (P Q: tprop state): tprop state :=
  fun R s => R @s ⊨ P /\ R @s ⊨ Q.

Definition tdisj {state} (P Q: tprop state): tprop state := 
  fun R s => R @s ⊨ P \/ R @s ⊨ Q.

Definition timpl {state} (P Q: tprop state): tprop state :=
  fun R s => R @s ⊨ P -> R @s ⊨ Q.

Definition tbiimpl {state} (P Q: tprop state): tprop state :=
  fun R s => R @s ⊨ P <-> R @s ⊨ Q.

Definition tnot {state} (P: tprop state): tprop state :=
  fun R s => R @s ⊭ P.

(* State prop notations *)
Notation "⊤" := (ttop) : tprop_scope.
Notation "⊥" := (tbot) : tprop_scope.
Notation "P ∧ Q" := (tconj P Q) (at level 45, right associativity) : tprop_scope.
Notation "P ∨ Q" := (tdisj P Q) (at level 55, right associativity) : tprop_scope.
Notation "P ⟶ Q" := (timpl P Q) (at level 68,  right associativity) : tprop_scope.
Notation "P ⟷ Q" := (tbiimpl P Q) (at level 65,  right associativity) : tprop_scope.
Notation "¬ P" := (tnot P) (at level 40) : tprop_scope.

(* path-quantifying props *)

Definition AX {state} (P: tprop state): tprop state :=
  fun R s => forall s', R s s' -> R @s' ⊨ P.
  
Definition EX {state} (P: tprop state): tprop state :=
  fun R s => exists s', R s s' /\ R @s' ⊨ P.

Definition AG {state} (P: tprop state): tprop state :=
  fun R s => forall n (p: path R n s) s', 
    in_path s' p -> R @s' ⊨ P.

Definition EG {state} (P: tprop state): tprop state :=
  fun R s => forall n, exists p: path R n s, forall s',
    in_path s' p -> R @s' ⊨ P.

Definition AF {state} (P: tprop state): tprop state :=
  fun R s => exists n, forall p: path R n s, exists s',
    in_path s' p /\ R @ s' ⊨ P.

Definition EF {state} (P: tprop state): tprop state :=
  fun R s => exists n (p: path R n s) s',
    in_path s' p /\ R @s' ⊨ P.

Definition AU {state} (P Q: tprop state): tprop state :=
  fun R s => exists n, forall p: path R n s,
      exists sQ i, in_path_at sQ i p /\ 
        R @sQ ⊨ Q /\
        forall sP, in_path_before sP i p -> R @sP ⊨ P.

Definition EU {state} (P Q: tprop state): tprop state :=
  fun R s => exists n, exists p: path R n s,
      exists sQ i, in_path_at sQ i p /\ 
        R @sQ ⊨ Q /\
        forall sP, in_path_before sP i p -> R @sP ⊨ P.

Definition AW {state} (P Q: tprop state): tprop state :=
  fun R s => forall n (p: path R n s) y i,
      in_path_at y i p ->
      (forall x,
        in_path_before x i p ->
        R @x ⊨ P ∧ ¬Q) ->
      R @y ⊨ P ∨ Q.

(* Path-quantifying prop notations *)
Notation "A[ P 'U' Q ]" := (AU P Q) (at level 40, format "A[ P  'U'  Q ]") : tprop_scope.
Notation "E[ P 'U' Q ]" := (EU P Q) (at level 40, format "E[ P  'U'  Q ]") : tprop_scope.
Notation "A[ P 'W' Q ]" := (AW P Q) (at level 40, format "A[ P  'W'  Q ]") : tprop_scope.

Global Opaque tentails.
Global Opaque ttop.
Global Opaque tbot.
Global Opaque tconj.
Global Opaque tdisj.
Global Opaque timpl.
Global Opaque tbiimpl.
Global Opaque AX.
Global Opaque EX.
Global Opaque AF.
Global Opaque EF.
Global Opaque AU.
Global Opaque EU.
Global Opaque AW.