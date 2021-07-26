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
Require Import Tactics.Construct.

Definition useram_key_secure : TProp (attarch_global * attarch_state) := 
  ⟨fun st =>
    val_at (useram_key (fst st)) = Some good_useram_key -> 
    acc_at (useram_key (fst st)) = useram_key_acc
  ⟩. 

Theorem useram_key_never_compromised:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  intros n p s' Hin.
  construct in_path__rtc in Hin.
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

Definition setup_done : TProp (attarch_global * attarch_state) := 
  ⟨fun st =>
    snd st = sel4_run (platam_run, vm_run useram_waiting_request)
  ⟩. 

Theorem useram_key_never_compromised_setup:
  attarch_trans @initial_state_good ⊨ A[useram_key_secure U setup_done].
Proof using.
  (* expand_tEntails. *)
  intros n p.
  destruct exists p m.
  invc p.