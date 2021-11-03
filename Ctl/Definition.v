Require Import Ctl.BinaryRelations.
Require Import Ctl.Paths.

Class transition {A} (R: relation A) := 
  {trans_serial: serial_witness R}.

(* Note: none of the CTL formulas explicitly use the transition instance, but they do 
   make recursive entailment assertions which implicitly pass the transition instance
   forward.

   Ultimately, the transition instance is only used by the theorems in Properties.v.
   It is nonetheless important that a transition instance be mandated for entailments. 
   Otherwise, the path-quantifying formulas would lose their current meaning.
 *)
Definition tprop state :=
  forall R: relation state,
    transition R ->
    state ->
    Prop.

Declare Scope tprop_scope.
(* Delimit Scope tprop_scope with tprop. *)
Bind Scope tprop_scope with tprop.
Open Scope tprop_scope.

Definition tentails {state} (R: relation state) {t: transition R}
  (s: state) (P: tprop state) :=
  P R t s.
Notation "R @ s ⊨ P" := (tentails R s P)   (at level 69, format "R  @ s  ⊨  P") : tprop_scope.
Notation "R @ s ⊭ P" := (~ tentails R s P) (at level 69, format "R  @ s  ⊭  P") : tprop_scope.


Section StateProps.

Context {state: Type}.

Definition ttop : tprop state :=
  fun _ _ _ => True.

Definition tbot : tprop state :=
  fun _ _ _ => False.

Definition tconj (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P /\ R @s ⊨ Q.

Definition tdisj (P Q: tprop state): tprop state := 
  fun R _ s => R @s ⊨ P \/ R @s ⊨ Q.

Definition timpl (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P -> R @s ⊨ Q.

Definition tbiimpl (P Q: tprop state): tprop state :=
  fun R _ s => R @s ⊨ P <-> R @s ⊨ Q.

Definition tnot (P: tprop state): tprop state :=
  fun R _ s => R @s ⊭ P.

Definition tlift (P: state -> Prop): tprop state :=
  fun _ _ s => P s.

End StateProps.

Notation "⊤"      := (ttop) : tprop_scope.
Notation "⊥"      := (tbot) : tprop_scope.
Notation "P ∧ Q"  := (tconj P Q)   (at level 45, right associativity) : tprop_scope.
Notation "P ∨ Q"  := (tdisj P Q)   (at level 55, right associativity) : tprop_scope.
Notation "P ⟶ Q" := (timpl P Q)   (at level 68,  right associativity) : tprop_scope.
Notation "P ⟷ Q" := (tbiimpl P Q) (at level 65,  right associativity) : tprop_scope.
Notation "¬ P"    := (tnot P)      (at level 40, format "¬ P") : tprop_scope.
Notation "⟨ P ⟩"   := (tlift P)     (format "⟨ P ⟩"): tprop_scope.


Section PathProps.

Context {state: Type}.

Definition AX (P: tprop state) : tprop state :=
  fun R _ s => forall s', R s s' -> R @s' ⊨ P.
  
Definition EX (P: tprop state) : tprop state :=
  fun R _ s => exists s', R s s' /\ R @s' ⊨ P.

Definition AG (P: tprop state) : tprop state :=
  fun R _ s => forall (p: path R s) s', in_path s' p -> R @s' ⊨ P.

Definition EG (P: tprop state) : tprop state :=
  fun R _ s => exists p: path R s, forall s', in_path s' p -> R @s' ⊨ P.

Definition AF (P: tprop state) : tprop state :=
  fun R _ s => forall p: path R s, exists s', in_path s' p /\ R @s' ⊨ P.
  
Definition EF (P: tprop state) : tprop state :=
  fun R _ s => exists (p: path R s) s', in_path s' p /\ R @s' ⊨ P.

Definition AU (P Q: tprop state) : tprop state :=
  fun R _ s => forall p: path R s, exists i,
    (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
    R @(p i) ⊨ Q.

Definition EU (P Q: tprop state) : tprop state :=
  fun R _ s => exists (p: path R s) i,
    (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
    R @(p i) ⊨ Q.

Definition AW {state} (P Q: tprop state) : tprop state :=
  fun R _ s => forall p: path R s,
    (forall x, in_path x p -> R @x ⊨ P ∧ ¬Q) \/
    (exists i,
      (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
      R @(p i) ⊨ Q).

End PathProps.

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

Close Scope tprop_scope.