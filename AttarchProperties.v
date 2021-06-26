Require Import Ctl.Definition.
Require Import Ctl.Tactics.
Require Import Ctl.Properties.

Require Import SepLogic.
Require Import TransitionSystems.
Require Import AttarchTrans.

Require Import Coq.Program.Equality.
Require Import Coq.Relations.Relation_Definitions.
Require Import GeneralTactics.

Definition gassert {comp loc L} (s: sprop comp loc) : TProp (sprop comp loc * L) :=
    ^ fun st => fst st ⊢ s.

Theorem useram_key_never_compromised: forall (acc: access component),
  acc malicious_linux_component read ->
  attarch_strans; (empty, boot_from_good_plat) ⊨ ¬ EF (gassert (acc @ useram_key)).
Proof.
  intros acc Hmal_acc.
  Check EF_AG.
  (* tapply shouldn't be simplifying!! *)
  tapply (EF_AG attarch_strans).
  intros p Hpath s HIn.

  (* Likely needs to be generalized *)
  (* Print path. *)
  dependent induction Hpath.
  - destruct HIn; [|find_solve_inversion].
    subst.
    simpl.
    intro H; inversion H.
  - eapply IHHpath.
    + assumption.
    + 

  - inv H.
    (* sEntails_pre *)
    + (* inv H2 *)
      find_solve_inversion.
    (* sEntails_post *)
    + 
      (* Do I need to go back and induct on H? It seems like I am left with an 
      equivalently shaped hypothesis H4. *)
      invc HIn.
      * find_solve_inversion.
      * 

Admitted.
  