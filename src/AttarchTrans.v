Require Import Privilege.
Require Import TransitionSystems.

Require Import Ctl.BinaryRelations.
Require Import Ctl.Definition.
Require Import Glib.Glib.

Open Scope string_scope.
Open Scope env_scope.


(* value types *)

Inductive boot_token_t :=
  | good_boot_token
  | bad_boot_token.
Inductive vm_ev_t :=
  | good_vm_ev
  | bad_vm_ev.
Inductive platam_key_t :=
  | good_platam_key
  | encr_platam_key
  | bad_platam_key.
Inductive useram_key_t :=
  | good_useram_key
  | encr_useram_key
  | bad_useram_key.
Inductive useram_key_decr_key_t :=
  | good_decr_key
  | encr_decr_key
  | bad_decr_key.


(* Transition definitions *)

Inductive platam_label :=
  | platam_init 
  | platam_meas_release
  | platam_listen.

(* Definition platam_state := dynamic_state platam_label. *)
Definition platam_state := platam_label × env.
Definition platam_init_state : platam_state :=
  (platam_init,
   private "platam" ? (
     "platam_key" ↦ encr_platam_key ;;
     "useram_key_decr_key" ↦ encr_decr_key
  )).

Definition decrypt_platam_key key token : platam_key_t := 
  match (key, token) with 
  | (encr_platam_key, good_boot_token) => good_platam_key
  | _ => bad_platam_key
  end.

Definition decrypt_useram_key_decr_key decr_key platam_key : useram_key_decr_key_t := 
  match (decr_key, platam_key) with 
  | (encr_decr_key, good_platam_key) => good_decr_key
  | _ => bad_decr_key
  end.

Inductive platam_trans : relation (platam_state × env) := 
  | platam_unlock_key : forall Γl Γl' Γg key token,
      read  Γl "platam" "platam_key" key ->
      read  Γg "platam" "boot_token" token ->
      write Γl "platam" "platam_key" (decrypt_platam_key key token) Γl' ->
      platam_trans 
        (platam_init, Γl, Γg)
        (platam_meas_release, Γl', Γg)
  | platam_measure_release : forall Γl Γg Γg' platam_key decr_key,
      read  Γg "platam" "good_image" true ->
      read  Γl "platam" "useram_key_decr_key" decr_key ->
      read  Γl "platam" "platam_key" platam_key -> 
      write Γg "platam" "vmm_dataport" (decrypt_useram_key_decr_key decr_key platam_key) Γg' ->
      platam_trans 
        (platam_meas_release, Γl, Γg)
        (platam_listen, Γl, Γg').

(* TODO, bad_platam_trans, *)

Inductive useram_label := 
  | useram_wait_key
  | useram_listen.

Definition useram_state := useram_label × env.

Definition useram_init_state : useram_state := 
  (useram_wait_key, private "useram" ? "useram_key" ↦ encr_useram_key).

Definition decrypt_useram_key key decr_key : useram_key_t := 
  match (key, decr_key) with 
  | (encr_useram_key, good_decr_key) => good_useram_key
  | _ => bad_useram_key
  end.

Inductive useram_trans : relation (useram_state × env) :=
  | useram_get_key : forall Γl Γl' Γg encr_key decr_key,
      read  Γl "useram" "useram_key" encr_key ->
      read  Γg "useram" "vmm_dataport" decr_key ->
      write Γl "useram" "useram_key" (decrypt_useram_key encr_key decr_key) Γl' ->
      useram_trans 
        (useram_wait_key, Γl, Γg)
        (useram_listen, Γl', Γg).

Inductive vm_label := 
  | vm_run : useram_state -> vm_label.

Definition vm_state := vm_label.

Definition vm_init_state : vm_state := vm_run useram_init_state.

Inductive vm_trans : relation (vm_state × env) := 
  | useram_step : forall x y Γ Γ',
      useram_trans (x, Γ) (y, Γ') ->
      vm_trans (vm_run x, Γ) (vm_run y, Γ').

Inductive attarch_label :=
  | boot
  | sel4_run : platam_state -> vm_state -> attarch_label
  | attarch_bot.

Definition attarch_state := attarch_label × env.

Definition attarch_init_state : attarch_state := (boot, allReadOnly ? "good_image" ↦ true).

Inductive attarch_trans : relation attarch_state :=
  | boot_good : forall Γ,
      read Γ "root_of_trust" "good_image" true -> 
      attarch_trans
        (boot, Γ)
        (sel4_run platam_init_state vm_init_state,
          allReadOnly ? "boot_token" ↦ good_boot_token;; Γ)
  | boot_bad : forall Γ,
      read Γ "root_of_trust" "good_image" false -> 
      attarch_trans
        (boot, Γ)
        (sel4_run platam_init_state vm_init_state,
          allReadOnly ? "boot_token" ↦ bad_boot_token;; Γ)
  | platam_step : forall x l l' Γl Γl' Γg Γg',
      platam_trans (l, Γl, Γg) (l', Γl', Γg') ->
      attarch_trans 
        (sel4_run (l, Γl) x, Γg)
        (sel4_run (l', Γl') x, Γg')
  | vm_step : forall x l l' Γg Γg',
      vm_trans (l, Γg) (l', Γg') ->
      attarch_trans 
        (sel4_run x l, Γg)
        (sel4_run x l', Γg')
 | attarch_diverge : forall l Γ,
      attarch_trans (l, Γ) (attarch_bot, Γ).


Lemma attarch_trans_serial : 
  serial_witness attarch_trans.
Proof using.
  unfold serial_witness.
  intros [l ?].
  eexists.
  apply attarch_diverge.
Defined.

Instance transition__attarch_trans : transition attarch_trans :=
  { trans_serial := attarch_trans_serial }.

Close Scope env_scope.
Close Scope string_scope.
