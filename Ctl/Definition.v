Require Import Ctl.Paths.
Require Import BinaryRelations.
Require Import Isomorphisms.

Class transition {A} (R: relation A) := 
  {trans_serial: serial_witness R}.

(* Definition tprop state := relation state -> state -> Prop. *)

Definition tprop state :=
  forall R: relation state,
    transition R ->
    state ->
    Prop.

Delimit Scope tprop_scope with tprop.
Open Scope tprop_scope.

Definition tentails {state} (R: relation state) {t: transition R}
  (s: state) (P: tprop state) :=
  P R t s.
Notation "R @ s ⊨ P" := (tentails R s P)   (at level 70, format "R  @ s  ⊨  P") : tprop_scope.
Notation "R @ s ⊭ P" := (~ tentails R s P) (at level 70, format "R  @ s  ⊭  P") : tprop_scope.


(* State props *)

Definition ttop {state}: tprop state :=
  fun _ _ _ => True.

Definition tbot {state}: tprop state :=
  fun _ _ _ => False.

Definition tconj {state} (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P /\ R @s ⊨ Q.

Definition tdisj {state} (P Q: tprop state): tprop state := 
  fun R _ s => R @s ⊨ P \/ R @s ⊨ Q.

Definition timpl {state} (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P -> R @s ⊨ Q.

Definition tbiimpl {state} (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P <-> R @s ⊨ Q.

Definition tnot {state} (P: tprop state): tprop state :=
  fun R _ s => R @s ⊭ P.

Definition tlift {state} (P: state -> Prop): tprop state :=
  fun _ _ s => P s.

(* State prop notations *)
Notation "⊤"      := (ttop) : tprop_scope.
Notation "⊥"      := (tbot) : tprop_scope.
Notation "P ∧ Q"  := (tconj P Q)   (at level 45, right associativity) : tprop_scope.
Notation "P ∨ Q"  := (tdisj P Q)   (at level 55, right associativity) : tprop_scope.
Notation "P ⟶ Q" := (timpl P Q)   (at level 68,  right associativity) : tprop_scope.
Notation "P ⟷ Q" := (tbiimpl P Q) (at level 65,  right associativity) : tprop_scope.
Notation "¬ P"    := (tnot P)      (at level 40, format "¬ P") : tprop_scope.
Notation "⟨ P ⟩"   := (tlift P)     (format "⟨ P ⟩"): tprop_scope.


(* path-quantifying props *)

Definition AX {state} (P: tprop state) : tprop state :=
  fun R t s => forall s', R s s' -> R @s' ⊨ P.
  
Definition EX {state} (P: tprop state) : tprop state :=
  fun R t s => exists s', R s s' /\ R @s' ⊨ P.

Definition AG {state} (P: tprop state) : tprop state :=
  fun R t s => forall (p: path R s) s', in_path s' p -> R @s' ⊨ P.

Definition EG {state} (P: tprop state) : tprop state :=
  fun R t s => exists p: path R s, forall s', in_path s' p -> R @s' ⊨ P.

Definition AF {state} (P: tprop state) : tprop state :=
  fun R t s => forall p: path R s, exists s', in_path s' p /\ R @s' ⊨ P.
  
Definition EF {state} (P: tprop state) : tprop state :=
  fun R t s => exists (p: path R s) s', in_path s' p /\ R @s' ⊨ P.

Definition AU {state} (P Q: tprop state) : tprop state :=
  fun R t s => forall p: path R s, exists sQ i,
    in_path_at sQ i p /\ 
    (forall sP, in_path_before sP i p -> R @sP ⊨ P) /\ 
    R @sQ ⊨ Q.

Definition EU {state} (P Q: tprop state) : tprop state :=
  fun R t s => exists (p: path R s) sQ i,
    in_path_at sQ i p /\ 
    (forall sP, in_path_before sP i p -> R @sP ⊨ P) /\ 
    R @sQ ⊨ Q.

(* Path-quantifying prop notations *)
Notation "A[ P 'U' Q ]" := (AU P Q) (at level 40, format "A[ P  'U'  Q ]") : tprop_scope.
Notation "E[ P 'U' Q ]" := (EU P Q) (at level 40, format "E[ P  'U'  Q ]") : tprop_scope.

Definition AW {state} (P Q: tprop state) : tprop state :=
  fun R t s => R @s ⊨ A[P U Q] ∨ ¬AF P.
  (* fun R s => forall s' (seq: R#* s s'),
    (forall x, in_seq x seq -> R @x ⊨ P ∧ ¬Q) ->
    forall s'', 
      R s' s'' ->
      R @s'' ⊨ P ∨ Q. *)
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

Close Scope tprop_scope.