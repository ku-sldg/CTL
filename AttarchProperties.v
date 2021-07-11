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
    TLift (fun st => fst st ⊢ s \/ exists frame, fst st ⊢ s ** frame).

Theorem useram_key_never_compromised: forall (acc: access component),
  acc malicious_linux_component read ->
  attarch_strans; (empty, boot_from_good_plat) ⊨ ¬ EF (gassert (acc @ useram_key)).
Proof.
  intros acc Hmal_acc.
  tapply AG_EF.
  apply rtc_AG.
  intros s' Hsteps.
  dependent induction Hsteps.
  - sentails.
  - intros Hcontra.
    (* simpl in Hcontra. *)
    invc H.
    + invc H2.
      * invc Hcontra.
       -- sprop_discriminate.
       -- destruct exists H frame.
          simpl in H.
          sprop_facts.
          (* From H2 derive
             readonly @ boot_ev ⊢ acc @ useram_key
             This is a contradiction, since the two acces locations 
             are not equal
           *)
          admit.
      * invc Hcontra.
       -- sprop_discriminate.
       -- simpl in H.
          (* contradiction found by advanced sprop_discriminate *)
          admit.
      * 

Admitted.