Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Properties.

Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Tactics.General.
Require Import Ctl.Tactics.

Definition useram_key_secure : TProp (attarch_global * attarch_state) := 
  ⟨fun st =>
    val_at (useram_key (fst st)) = Some good_useram_key -> 
    acc_at (useram_key (fst st)) = useram_key_acc
  ⟩. 

Theorem useram_key_never_compromised:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  apply rtc_AG.
  intros s' Hsteps.
  dependent induction Hsteps.
  - discriminate.
  - invc H; try apply IHHsteps.
    invc H0.
    + invc H1; try apply IHHsteps.
      simpl. reflexivity.
    + invc H1; try apply IHHsteps.
      invc H0; apply IHHsteps.
Qed.

Theorem useram_key_never_compromised__induct_path:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  intros n p s' H.
  dependent induction p.
  - invc H.
    discriminate.
  - 
    
  (* Bad induction principle *)
  (* dependent induction H; try discriminate. *)