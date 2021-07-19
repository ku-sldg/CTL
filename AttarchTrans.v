Require Import Ctl.Definition.
Require Import TransitionSystems.
Require Import Privilege.

(* Maybe sel4 should not be its own place *)
Inductive component : Set := 
  | sel4 
  | platam 
  | vmm 
  | useram
  | malicious_linux_component.

Record mem_store v : Type := mkMem_store 
  { acc_at: access component
  ; val_at: option v
  }.
Arguments acc_at {v}%type_scope.
Arguments val_at {v}%type_scope.

Record attarch_global := mkAttarchGl
  { boot_ev    : mem_store nat
  ; vm_ev      : mem_store nat
  ; useram_key : mem_store nat
  }.

Definition set_boot_ev (st: attarch_global) (m: mem_store nat) : attarch_global :=
  {| boot_ev    := m; 
     vm_ev      := vm_ev st;
     useram_key := useram_key st |}.
Definition set_vm_ev (st: attarch_global) (m: mem_store nat) : attarch_global :=
  {| boot_ev    := boot_ev st;
     vm_ev      := m;
     useram_key := useram_key st |}.
Definition set_useram_key (st: attarch_global) (m: mem_store nat) : attarch_global :=
  {| boot_ev    := boot_ev st; 
     vm_ev      := vm_ev st;
     useram_key := m |}.

Definition good_boot_ev : nat.
exact 0. Qed.
Definition bad_boot_ev  : nat.
exact 0. Qed.
Definition initial_global_state_good :=
  {| boot_ev    := {|acc_at := allAcc; val_at := Some good_boot_ev|};
     vm_ev      := {|acc_at := allAcc; val_at := None|};
     useram_key := {|acc_at := allAcc; val_at := None|}
  |}.


(* Add linux state under vm? *)
(* Note, all sudoers have access to useram/platam channel *)
Inductive useram_state : Set :=
  | useram_waiting_key (* initial state *)
  | useram_waiting_request
  | useram_measuring
  | useram_making_request
  | useram_sending_response.

Inductive useram_trans : transition attarch_global useram_state :=
  | useram_get_key : forall st,
      acc_at (useram_key st) useram read ->
      useram_trans 
        (st, useram_waiting_key)
        (st, useram_waiting_request)
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
Definition good_useram_key : nat. Admitted.
Inductive useram_key_acc : access component :=
  | useram_useram_key_read  : useram_key_acc useram read
  | platam_useram_key_read  : useram_key_acc platam read
  | platam_useram_key_write : useram_key_acc platam write.

Inductive platam_trans : transition attarch_global platam_state :=
  | platam_measure_good_vm : forall st,
      platam_trans
        (st, platam_init)
        (set_vm_ev st {|acc_at := private platam; val_at := Some good_vm_ev|}, platam_appraise)
  | platam_measure_bad_vm : forall st,
      platam_trans
        (st, platam_init)
        (set_vm_ev st {|acc_at := private platam; val_at := Some bad_vm_ev|}, platam_appraise)
  | platam_release_key : forall st,
      acc_at (vm_ev st) platam read ->
      val_at (vm_ev st) = Some good_vm_ev ->
      platam_trans
        (st, platam_appraise)
        (set_useram_key st {|acc_at := useram_key_acc; val_at := Some good_useram_key|}, platam_run).

Inductive vm_state : Set :=
  | vm_init
  | vm_run : useram_state -> vm_state.

Inductive vm_trans : transition attarch_global vm_state :=
  | vm_boot : forall st,
      vm_trans 
        (st, vm_init)
        (st, vm_run useram_waiting_key)
  | vm_linux_step : forall g g' s s',
      useram_trans (g,s) (g',s') ->
      vm_trans
        (g, vm_run s)
        (g', vm_run s').

Inductive attarch_state : Set :=
  | boot
  | sel4_run : platam_state * vm_state -> attarch_state.

Inductive attarch_trans : transition attarch_global attarch_state :=
  (* | good_boot : forall st,
      (fst (boot_ev st)) sel4 read ->
      (snd (boot_ev st)) = good_boot_ev ->
      attarch_trans 
        (st, boot_from_good_plat)
        (st, sel4_run (platam_init, vm_init)) *)
  | attarch_boot : forall st,
      attarch_trans 
        (st, boot)
        (st, sel4_run (platam_init, vm_init))
  | component_step : forall g g' s s',
      (platam_trans ⊔ vm_trans) (g,s) (g',s') ->
      attarch_trans 
        (g, sel4_run s)
        (g', sel4_run s').

Definition initial_state_good := (initial_global_state_good, boot).
