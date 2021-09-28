Require Import Notation.
Require Import Ctl.Ctl.
Require Import BinaryRelations.
Require Import TransitionSystems.
Require Import Privilege.
Require Import AttarchTrans.

Require Import Tactics.Tactics.

Open Scope string_scope.
Open Scope tprop_scope.
Open Scope env_scope.

Definition useram_key_secure : tprop attarch_state := ⟨λ '(l, _),
    forall Γ l' s c,
      l = sel4_run (l', Γ) s ->
      read Γ c "useram_key" good_useram_key -> 
      c = "useram"
  ⟩.

Definition diverged : tprop attarch_state :=
  ⟨λ '(l, _), l = attarch_bot⟩.

Ltac star_notation := 
  repeat change (clos_refl_trans_n1 _ ?R) with (R^*) in *.

(* AG strong induction. Reflect to seq. Hypothesis 
   is in_seq x -> R @ x ⊨ H
 *)

Theorem useram_key_never_compromised:
  attarch_trans @attarch_init_state ⊨ AG useram_key_secure.
Proof.
  apply star__AG.
  intros * Hstar.
  induct! Hstar; star_notation.
  - tentails!. discriminate.
  - invc H.
    + tentails!.
      intros * [=] H'; subst.
      econtradiction no_lookup_no_read; [|eassumption].
      now unfold map_access.
    + tentails!.
      intros * [=] H'; subst.
      econtradiction no_lookup_no_read; [|eassumption].
      now unfold map_access.
    + invc H.
      * tentails! in *.
        intros * [=] H'; subst.
        eapply IHHstar.
        reflexivity.
        eapply write_unchanged_read'; try eassumption.
        discriminate.
      * tentails! in *.
        intros * [=] H'; subst.
        now eapply IHHstar.
    + invc H.
      invc H0.
      tentails! in *.
      intros * [=] H'; subst.
      now eapply IHHstar.
    + now tentails!.
Qed.
Print Assumptions useram_key_never_compromised.


Close Scope tprop_scope.
Close Scope string_scope.