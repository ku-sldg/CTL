Require Import Ctl.Definition.
Require Import TransitionSystems.
Require Import SepLogic.

(* Maybe sel4 should not be its own place *)
Inductive component : Set := 
  | sel4 
  | platam 
  | vmm 
  | useram
  | malicious_linux_component.

Inductive loc : Set :=
  | boot_ev 
  | vm_ev
  | useram_key.

Definition stransition a := transition (sprop component loc) a.

(* Add linux state under vm? *)
(* Note, all sudoers have access to useram/platam channel *)
Inductive useram_state : Set :=
  | useram_waiting_key (* initial state *)
  | useram_waiting_request
  | useram_measuring
  | useram_making_request
  | useram_sending_response.

Inductive useram_trans : stransition useram_state :=
  | useram_get_key : forall (acc: access component) (k: nat),
      acc useram read ->
      useram_trans
        (acc @ useram_key ** useram_key ↦ k, useram_waiting_key)
        (acc @ useram_key ** useram_key ↦ k, useram_waiting_request)
  (* | useram_get_request : useram_trans 
      (s, useram_waiting_key)
      (s,useram_) *)
  .
(* Definition useram_strans := stransition useram_trans. *)

Inductive platam_state : Set :=
  | platam_init
  | platam_appraise
  | platam_run.

Definition good_vm_ev : nat. Admitted.
Definition bad_vm_ev  : nat. Admitted.
Definition useram_key_val  : nat. Admitted.
Inductive useram_key_acc : access component :=
  | useram_useram_key_read  : useram_key_acc useram read
  | platam_useram_key_read  : useram_key_acc platam read
  | platam_useram_key_write : useram_key_acc platam write.
Inductive platam_trans : stransition platam_state :=
  | platam_measure_good_vm : platam_trans
      (empty, platam_init)
      (private platam @ vm_ev ** vm_ev ↦ good_vm_ev, platam_appraise)
  | platam_measure_bad_vm : platam_trans
      (empty, platam_init)
      (private platam @ vm_ev ** vm_ev ↦ bad_vm_ev, platam_appraise)
  | platam_release_key : forall (acc: access component),
      acc platam read ->
      platam_trans
        (acc @ vm_ev ** vm_ev ↦ good_vm_ev,
          platam_appraise)
        (acc @ vm_ev ** vm_ev ↦ good_vm_ev **
        useram_key_acc @ useram_key ** useram_key ↦ useram_key_val,
          platam_run).

Inductive vm_state : Set :=
  | vm_init
  | vm_run : useram_state -> vm_state.

Inductive vm_trans : stransition vm_state :=
  | vm_boot : vm_trans
      (empty, vm_init)
      (empty, vm_run useram_waiting_key)
  | vm_linux_step : forall g g' s s',
      useram_trans (g,s) (g',s') ->
      vm_trans
        (g, vm_run s)
        (g, vm_run s').

Inductive attarch_state : Set :=
  | boot_from_good_plat (* initial state *)
  | boot_from_bad_plat  (* initial state *)
  | sel4_run : platam_state * vm_state -> attarch_state.

Definition good_boot_ev : nat. Admitted.
Definition bad_boot_ev  : nat. Admitted.
Inductive attarch_trans : stransition attarch_state :=
  | good_boot : attarch_trans 
      (empty, boot_from_good_plat)
      (readonly @ boot_ev ** boot_ev ↦ good_boot_ev, sel4_run (platam_init, vm_init))
  | bad_boot : attarch_trans 
      (empty, boot_from_bad_plat)
      (readonly @ boot_ev ** boot_ev ↦ bad_boot_ev, sel4_run (platam_init, vm_init))
  | component_step : forall g g' s s',
      (platam_trans ⊔ vm_trans) (g,s) (g',s') ->
      attarch_trans 
        (g, sel4_run s)
        (g', sel4_run s').
Definition attarch_strans := sprop_closure attarch_trans.
