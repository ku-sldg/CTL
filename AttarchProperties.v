Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Tactics.
Require Import Ctl.Properties.

Require Import SepLogic.Definition.
Require Import SepLogic.Entailment.

Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import GeneralTactics.

(* Assert some fact about the global state *)
Definition gassert {comp loc L} (s: sprop comp loc) : TProp (sprop comp loc * L) :=
    TLift (fun st => exists frame, fst st ⊢ s ** frame).

Theorem useram_key_never_compromised: forall V (v: V) (acc: access component),
  acc malicious_linux_component read ->
  attarch_strans; (⟨⟩, boot_from_good_plat) ⊨ ¬ EF (gassert (useram_key #acc ↦ v)).
Proof.
  intros V v acc Hmal_acc.
  tapply AG_EF.
  apply rtc_AG.
  intros s' Hsteps.
  dependent induction Hsteps.
  - simpl. 
    (* Trivial by sentails discrimination *)
    admit.
  - 
    (* intros Hcontra. *)
    invc H.
    invc H2.
    + intro Hcontra.
      simpl in Hcontra.
      (* Hcontra is a contradiction. 
         y' can only entail `bootev # readonly ↦ ...`, by H1.
         z0 can't entail `useram_key # ...` either, by IHHsteps
       *)
      admit.
    + (* Hsteps is an impossible path *)
      invc Hsteps.
      invc H.
      inv H9.
    +  

Admitted.