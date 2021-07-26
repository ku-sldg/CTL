Require Import Ctl.Paths.
Require Import Ctl.Definition.
Open Scope tprop_scope.

Require Import Coq.Relations.Relation_Definitions.


Theorem tentails_ttop {state}: forall (R: relation state) s,
  R @s ⊨ ⊤.
Proof using. intros; exact I. Qed.

Theorem ntentails_tbot {state}: forall (R: relation state) s,
  R @s ⊭ ⊥.
Proof using. auto. Qed.

Theorem tentails_tconj {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ->
  R @s ⊨ Q ->
  R @s ⊨ P ∧ Q.
Proof using. 
  intros.
  split; assumption.
Qed.

Theorem rew_tconj {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ∧ Q =
  (R @s ⊨ P /\ R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem tentails_tdisj_l {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ->
  R @s ⊨ P ∨ Q.
Proof using.
  intros.
  left.
  assumption.
Qed.

Theorem tentails_tdisj_r {state}: forall (R: relation state) s P Q,
  R @s ⊨ Q ->
  R @s ⊨ P ∨ Q.
Proof using.
  intros.
  right.
  assumption. 
Qed.

Theorem rew_tdisj {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ∨ Q = 
  (R @s ⊨ P \/ R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_timpl {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ⟶ Q =
  (R @s ⊨ P -> R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_tbiimpl {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ⟷ Q =
  (R @s ⊨ P <-> R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_tnot {state}: forall (R: relation state) s P,
  R @s ⊨ ¬ P =
  (R @s ⊭ P).
Proof using. reflexivity. Qed.

Theorem rew_AX {state}: forall (R: relation state) s P,
  R @s ⊨ AX P =
  forall s', R s s' -> R @s' ⊨ P.
Proof using. reflexivity. Qed. 

Theorem rew_EX {state}: forall (R: relation state) s P,
  R @s ⊨ EX P =
  exists s', R s s' /\ R @s' ⊨ P.
Proof using. reflexivity. Qed. 

Theorem rew_AG {state}: forall (R: relation state) s P,
  R @s ⊨ AG P =
  forall n (p: path R n s) s', in_path s' p -> R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_EG {state}: forall (R: relation state) s P,
  R @s ⊨ EG P = 
  forall n, exists p: path R n s, forall s', in_path s' p -> R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_AF {state}: forall (R: relation state) s P,
  R @s ⊨ AF P = 
  exists n, forall p: path R n s, exists s', in_path s' p /\ R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_EF {state}: forall (R: relation state) s P,
  R @s ⊨ EF P =
  exists n (p: path R n s) s', in_path s' p /\ R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_AU {state}: forall (R: relation state) s P Q,
  R @s ⊨ A[P U Q] =  
  exists n, forall p: path R n s, exists sQ i,
    in_path_at sQ i p /\ 
    R @sQ ⊨ Q /\
    forall sP, in_path_before sP i p -> R @sP ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_EU {state}: forall (R: relation state) s P Q,
  R @s ⊨ E[P U Q] =
  exists n (p: path R n s) sQ i,
    in_path_at sQ i p /\ 
    R @sQ ⊨ Q /\
    forall sP, in_path_before sP i p -> R @sP ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_AW {state}: forall (R: relation state) s P Q,
  R @s ⊨ A[P W Q] =
  forall n (p: path R n s) y i,
    in_path_at y i p ->
    (forall x,
      in_path_before x i p ->
      R @x ⊨ P ∧ ¬Q) ->
    R @y ⊨ P ∨ Q.
Proof using. reflexivity. Qed.
