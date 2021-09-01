Require Import Ctl.Ctl.
Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Tactics.Tactics.

Definition useram_key_secure : tprop (attarch_global * attarch_state) := 
  ⟨fun st =>
    val_at (useram_key (fst st)) = Some good_useram_key -> 
    acc_at (useram_key (fst st)) = useram_key_acc⟩. 

Theorem useram_key_never_compromised:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  rewrite rew_AG_star.
  intros * Hstar.
  induct! Hstar.
  - tentails!. discriminate.
  - invc H; try assumption!.
    invc H0.
    + invc H; try assumption!.
      now tentails!.
    + invc H; [|inv H0]; assumption!.
Qed.
Print Assumptions useram_key_never_compromised.

(*
Definition setup_done : tprop (attarch_global * attarch_state) := 
  fun _ st =>
    snd st = sel4_run (platam_run, vm_run useram_waiting_request). 

Theorem useram_key_never_compromised_setup:
  attarch_trans @initial_state_good ⊨ A[useram_key_secure W setup_done].
Proof using.
  rewrite rew_AW.
  intros n p y i Hin Hprev.
  let Hin' := fresh in
    copy Hin Hin';
    apply in_path_at__get_prefix in Hin' as [p' Hprefix].
  destruct exists p' curr_state.
  max induct* p'.
  - apply in_path_at_first_inv in Hin as ->.
    apply tentails_tdisj_l.
    tentails.
    discriminate.
  -
Abort.
*)