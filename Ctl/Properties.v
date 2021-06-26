Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Tactics.
Require Import BinaryRelations.
Require Import GeneralTactics.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Program.Equality.

(* Require Import Coq.Logic.Eqdep_dec. *)

Theorem AG_refl_finite {state}: forall (R: relation state) s P, 
  (forall s', R^* s s' -> R;s' ⊨ P) ->
  R;s ⊨ AG P.
Proof.
  intros R s P H.
  intros p s' Hin.
  apply H.
  apply in_path_refl_finite in Hin.
  destruct Hin as [n Hin].
  (* destruct p as [s'' r p]. *)
  dependent induction Hin.
  - apply rt_refl.
  - 
    (* simpl in x. *)
    (* Set Keep Proof Equalities. *)
    (* injection x. *)
    eapply rt_trans.
    + eapply rt_step. eassumption.
    + 
      eapply IHHin.
      * intros s'' HR.
        apply H.
        eapply rt_trans.
        -- eapply rt_step. eassumption.
        -- assumption.
      * destruct p as [s'' r' p'].
        simpl in x.
        (* assert (finite_path_UIP: forall (x y: finite_path R s (S n)) (p1 p2: x = y), p1 = p2). *)
        (* assert (finite_path_UIP_refl: forall (x: finite_path R s (S n)) (p: x = x), p = eq_refl x). *)
        (* { admit. } *)
        (* apply finite_path_UIP in x. *)
        admit.
(* Qed. *)
Admitted.

  | AG P => forall (p: path R s), forall s', in_path s' p -> R;s' ⊨ P
  | EG P => exists (p: path R s), forall s', in_path s' p -> R;s' ⊨ P
  | AF P => forall (p: path R s), exists s', in_path s' p /\ R;s' ⊨ P
  | EF P => exists (p: path R s), exists s', in_path s' p /\ R;s' ⊨ P


Theorem tModusPonens {state}: forall (M: relation state) s P Q,
  M;s ⊨ P --> Q -> M;s ⊨ P -> M;s ⊨ Q.
Proof. auto. Qed.

Theorem tModusPonens_flipped {state}: forall (M: relation state) s P Q,
  M;s ⊨ P -> M;s ⊨ P --> Q -> M;s ⊨ Q.
Proof. auto. Qed.

(* Good test for tactics *)
Theorem TImpl_trans {state}: forall M (s: state) P Q R,
  M;s ⊨ (P --> Q) --> (Q --> R) --> P --> R.
Proof.
  (* backwards reasoning *)
  intros M s P Q R Hpq Hqr Hp.
  tapply Hqr.
  tapply Hpq.
  exact Hp.

  Restart.
  (* forward reasoning *)
  intros M s P Q R Hpq Hqr Hp.
  tspecialize Hpq Hp.
  tspecialize Hqr Hpq.
  exact Hqr.

  Restart.
  simpl. auto.
Qed.

(* This is an alternate means of defining TNot *)
Theorem tNot_def {state}: forall M (s: state) P, M;s ⊨ ¬P <--> (P --> ⊥).
Proof.
  intros M s P.
  split; intros H; auto.
Qed.

Theorem path_from_serial {state}: forall (M: serialT state) s, path (projT1 M) s.
Proof.
  intros M.
  destruct M as [M Hserial]; simpl.
  cofix coIH.
  intros s.
  specialize (Hserial s).
  destruct Hserial as [s' Hserial].
  econstructor.
  - eassumption.
  - auto.
Qed.

Theorem path_from_serial' {state}:
  forall (M: relation state), is_serialT M -> forall s, path M s.
Proof. 
  intros M Hserial.
  cofix coIH.
  intros s.
  specialize (Hserial s).
  destruct Hserial as [s' Hserial].
  econstructor.
  - eassumption.
  - auto.
Qed.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall M (s: state) P, M;s ⊨ ¬AF P <--> EG (¬P).
Proof.
  intros M s P.
  split; intro H.
  - (* Need to construct a path based on contradiction at each step *)
    simpl. 
    refine (ex_intro _ (
      (cofix F s' : path M s' := _) s
    ) _).
    intros s' Hin H2.
    tapply H.
    intros p.
    exists s'.
    split.
    + 
    + assumption.
  - intros H2.
    destruct H as [p H].
    tspecialize H2 p.
    destruct H2 as [s' [HIn H2]].
    tapply (H s'); assumption.
Qed.

Theorem AF_EG' {state}: forall M (s: state) P, M;s ⊨ AF (¬P) <--> ¬EG P.
Admitted.

Theorem EF_AG {state}: forall M (s: state) P, M;s ⊨ ¬EF P <--> AG (¬ P).
Proof.
  (* intros M s P.
  split.
  - intros H p Hpath s' Hin H2.
    tconsume H.
    eauto.
  - intros H H2.
    destruct H2 as [p [Hpath [s' [Hin H2]]]].
    tspecialize3 H p Hpath s'.
    tconsume H; assumption.
Qed. *)
Admitted.

Theorem AX_EX {state}: forall M (s: state) P, M;s ⊨ ¬AX P <--> EX (¬ P).
Admitted.
