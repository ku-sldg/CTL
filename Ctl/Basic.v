Require Import Ctl.BinaryRelations.
Require Import Ctl.Paths.
Require Import Ctl.Definition.
Open Scope tprop_scope.

Section Basic.

Variable state : Type.
Variable R: relation state.
Context {T: transition R}.
Variable s: state.

Theorem tentails_ttop :
  R @s ⊨ ⊤.
Proof using. intros; exact I. Qed.

Theorem ntentails_tbot :
  R @s ⊭ ⊥.
Proof using. auto. Qed.

Theorem tentails_tconj : forall P Q,
  R @s ⊨ P ->
  R @s ⊨ Q ->
  R @s ⊨ P ∧ Q.
Proof using. 
  intros.
  split; assumption.
Qed.

Theorem rew_tconj : forall P Q,
  R @s ⊨ P ∧ Q =
  (R @s ⊨ P /\ R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem tentails_tdisj_l : forall P Q,
  R @s ⊨ P ->
  R @s ⊨ P ∨ Q.
Proof using.
  intros.
  left.
  assumption.
Qed.

Theorem tentails_tdisj_r : forall P Q,
  R @s ⊨ Q ->
  R @s ⊨ P ∨ Q.
Proof using.
  intros.
  right.
  assumption. 
Qed.

Theorem rew_tdisj : forall P Q,
  R @s ⊨ P ∨ Q = 
  (R @s ⊨ P \/ R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_timpl : forall P Q,
  R @s ⊨ P ⟶ Q =
  (R @s ⊨ P -> R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_tbiimpl : forall P Q,
  R @s ⊨ P ⟷ Q =
  (R @s ⊨ P <-> R @s ⊨ Q).
Proof using. reflexivity. Qed.

Theorem rew_tnot : forall P,
  R @s ⊨ ¬ P =
  (R @s ⊭ P).
Proof using. reflexivity. Qed.

Theorem rew_tlift : forall P,
  R @s ⊨ ⟨P⟩ =
  P s.
Proof using. reflexivity. Qed.

Theorem rew_AX : forall P,
  R @s ⊨ AX P =
  forall s', R s s' -> R @s' ⊨ P.
Proof using. reflexivity. Qed. 

Theorem rew_EX : forall P,
  R @s ⊨ EX P =
  exists s', R s s' /\ R @s' ⊨ P.
Proof using. reflexivity. Qed. 

Theorem rew_AG : forall P,
  R @s ⊨ AG P =
  forall (p: path R s) s', in_path s' p -> R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_EG : forall P,
  R @s ⊨ EG P = 
  exists p: path R s, forall s', in_path s' p -> R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_AF : forall P,
  R @s ⊨ AF P = 
  forall p: path R s, exists s', in_path s' p /\ R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_EF : forall P,
  R @s ⊨ EF P =
  exists (p: path R s) s', in_path s' p /\ R @s' ⊨ P.
Proof using. reflexivity. Qed.

Theorem rew_AU : forall P Q,
  R @s ⊨ A[P U Q] =  
  forall p: path R s, exists i,
    (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
    R @(p i) ⊨ Q.
Proof using. reflexivity. Qed.

Theorem rew_EU : forall P Q,
  R @s ⊨ E[P U Q] =
  exists (p: path R s) i,
    (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
    R @(p i) ⊨ Q.
Proof using. reflexivity. Qed.

Theorem rew_AW : forall P Q,
  R @s ⊨ A[P W Q] =
  forall p: path R s,
    (forall x, in_path x p -> R @x ⊨ P ∧ ¬Q) \/
    (exists i,
      (forall x, in_path_before x i p -> R @x ⊨ P) /\ 
      R @(p i) ⊨ Q).
Proof using. reflexivity. Qed.

End Basic.
Close Scope tprop_scope.