Require Import Ctl.Ctl.
Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Tactics.Tactics.

Definition useram_key_secure : tprop (attarch_global * attarch_state) := 
  fun _ st =>
    val_at (useram_key (fst st)) = Some good_useram_key -> 
    acc_at (useram_key (fst st)) = useram_key_acc. 

Theorem useram_key_never_compromised:
  attarch_trans @initial_state_good ⊨ AG useram_key_secure.
Proof.
  tsimpl.
  intros n p s' Hin.
  construct in_path__get_prefix_seq in Hin.
  clear p n.
  (* max induct Hin. *)
  induct Hin.
  - tentails. discriminate.
  - invc r; try (apply IHHin; reflexivity).
    invc H.
    + invc H1; try (apply IHHin; reflexivity).
      tentails!.
      reflexivity.
    + invc H1; [|inv H0]; apply IHHin; reflexivity.
Qed.
(* Print Assumptions useram_key_never_compromised. *)

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
  induct p'.
  - apply in_path_at_first_inv in Hin as ->.
    apply tentails_tdisj_l.
    tentails.
    discriminate.
  -
Abort.
