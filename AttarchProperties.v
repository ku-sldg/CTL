Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Properties.
Require Import Ctl.Tactics.

Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Tactics.General.
Require Import Tactics.Weaken.

Definition useram_key_secure : TProp (attarch_global * attarch_state) := 
  ⟨fun st =>
    val_at (useram_key (fst st)) = Some good_useram_key -> 
    acc_at (useram_key (fst st)) = useram_key_acc
  ⟩. 

Theorem useram_key_never_compromised:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  intros n p s' Hin.
  weaken in_path__rtc in Hin.
  clear p.
  dependent induction Hin.
  - discriminate.
  - invc r; try apply IHHin.
    invc H.
    + invc H1; try apply IHHin.
      simpl.
      reflexivity.
    + invc H1; try apply IHHin.
      invc H0; apply IHHin.
Qed.
