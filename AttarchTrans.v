Require Import Ctl.Definition.
Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.

Inductive component : Set := 
  | platam 
  | vmm 
  | useram
  | malicious_linux_component.

Inductive boot_ev_t :=
  | good_boot_ev 
  | bad_boot_ev.
Inductive vm_ev_t :=
  | good_vm_ev
  | bad_vm_ev.
Inductive platam_key_t :=
  | good_platam_key
  | bad_platam_key.
Inductive useram_key_t :=
  | good_useram_key
  | bad_useram_key.

Record mem_store v : Type := mkMem_store 
  { acc_at: access component
  ; val_at: option v
  }.
Arguments acc_at {v}%type_scope.
Arguments val_at {v}%type_scope.

Record attarch_global := mkAttarchGl
  { boot_ev    : mem_store boot_ev_t
  ; vm_ev      : mem_store vm_ev_t
  ; platam_key : mem_store platam_key_t
  ; useram_key : mem_store useram_key_t
  }.

Definition set_boot_ev (st: attarch_global) m : attarch_global :=
  {| boot_ev    := m; 
     vm_ev      := vm_ev st;
     platam_key := platam_key st;
     useram_key := useram_key st |}.
Definition set_vm_ev (st: attarch_global) m : attarch_global :=
  {| boot_ev    := boot_ev st;
     vm_ev      := m;
     platam_key := platam_key st;
     useram_key := useram_key st |}.
Definition set_useram_key (st: attarch_global) m : attarch_global :=
  {| boot_ev    := boot_ev st; 
     vm_ev      := vm_ev st;
     platam_key := platam_key st;
     useram_key := m |}.
Definition set_platam_key (st: attarch_global) m : attarch_global :=
  {| boot_ev    := boot_ev st; 
     vm_ev      := vm_ev st;
     platam_key := m;
     useram_key := useram_key st |}.


Definition initial_global_state_good :=
  {| boot_ev    := {|acc_at := readonly; val_at := Some good_boot_ev|};
     vm_ev      := {|acc_at := allAcc; val_at := None|};
     platam_key := {|acc_at := allAcc; val_at := None|};
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

Inductive useram_trans : state_trans attarch_global useram_state :=
  | useram_get_key : forall st,
      acc_at (useram_key st) useram read ->
      useram_trans 
        (st, useram_waiting_key)
        (st, useram_waiting_request).

Inductive platam_state : Set :=
  | platam_init
  | platam_measure
  | platam_appraise
  | platam_run.


Inductive useram_key_acc : access component :=
  | useram_useram_key_read  : useram_key_acc useram read
  | platam_useram_key_read  : useram_key_acc platam read
  | platam_useram_key_write : useram_key_acc platam write.

Definition acquire_key boot_ev :=
  match boot_ev with 
  | good_boot_ev => good_platam_key
  | bad_boot_ev => bad_platam_key
  end.

Inductive platam_trans : state_trans attarch_global platam_state :=
  | platam_acquire_key : forall st boot_ev_val,
      acc_at (boot_ev st) platam read ->
      val_at (boot_ev st) = Some boot_ev_val ->
      platam_trans 
        (st, platam_init)
        (set_platam_key st 
          {|acc_at := private platam; val_at := Some (acquire_key boot_ev_val)|}, 
          platam_measure)
  | platam_measure_good_vm : forall st,
      platam_trans
        (st, platam_measure)
        (set_vm_ev st {|acc_at := private platam; val_at := Some good_vm_ev|}, platam_appraise)
  | platam_measure_bad_vm : forall st,
      platam_trans
        (st, platam_measure)
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

Inductive vm_trans : state_trans attarch_global vm_state :=
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
  | sel4_run : platam_state * vm_state -> attarch_state
  | attarch_bot.

Inductive attarch_trans : state_trans attarch_global attarch_state :=
  (* TODO: add some boolean "good seL4 image" field to global state to determine boot? *)
  | good_boot : forall st,
      attarch_trans 
        (st, boot)
        (set_boot_ev st {|acc_at := readonly; val_at := Some good_boot_ev|}, sel4_run (platam_init, vm_init))
  | bad_boot : forall st,
      attarch_trans 
        (st, boot)
        (set_boot_ev st {|acc_at := readonly; val_at := Some bad_boot_ev|}, sel4_run (platam_init, vm_init))
  | component_step : forall g g' s s',
      (platam_trans ⊔ vm_trans) (g,s) (g',s') ->
      attarch_trans 
        (g, sel4_run s)
        (g', sel4_run s')
  | diverge : forall x y,
      attarch_trans (x, y) (x, attarch_bot).

Definition initial_state_good := (initial_global_state_good, boot).

Lemma attarch_trans_serial : 
  serial_witness attarch_trans.
Proof using.
  unfold serial_witness.
  intros a.
  destruct a as [global local].
  exists (global, attarch_bot).
  constructor.
Defined.

Instance transition__attarch_trans : transition attarch_trans :=
  { trans_serial := attarch_trans_serial }.