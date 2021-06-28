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
  induction Hin.
  - apply rt_refl.
  - eapply rt_trans.
    + eapply rt_step. eassumption.
    + applyc IHHin.
      intros s'' H2.
      apply H.
      eapply rt_trans.
      * eapply rt_step. eassumption.
      * assumption.
Qed. 

CoFixpoint generate_path {state}
  (R: relation state) (genNext: nat -> forall s, {s' | R s s'}) n s : path R s :=
  match genNext n s with
  | exist _ s' r => step s s' r (generate_path R genNext (S n) s')
  end.

(* CoFixpoint refl_existential_finite_path {state} (R: relation state) s P
(* CoFixpoint refl_existential_finite_path {state} (R: relation state) s P (n: nat) *)
  (H: forall n, {fp: finite_path R s n | forall s', in_finite_path s' n fp -> R;s' ⊨ P})
  : path R s.
pose proof (H 1) as Hone.
destructExists Hone fp.
inv fp.
(* clear fp Hone X. *)
econstructor; [eassumption|].
(* clear fp Hone X. *)
eapply refl_existential_finite_path.
intros n.
(* eexists. (* ?fp : finite_path R s' n *) *)
specialize (H (S n)).
destructExists H fp'.
inv fp'.
(* need to show s'0 = s' (both from a finite_path inversion) *)
exists X0.
 *)

Ltac genExPath R s := 
  refine (ex_intro _ (generate_path R _ 0 s) _).

(* Ltac genExPath R s := 
  refine (ex_intro _ (generate_path R _ 0 s) _);
  Unshelve;
  all: cycle 1.
 *)
Theorem EG_refl_finite {state}: forall (R: relation state) s P,
  (forall n, {fp: finite_path R s n | forall s', in_finite_path s' n fp -> R;s' ⊨ P}) ->
  R;s ⊨ EG P.
Proof.
  intros R s P H.
  simpl.
  (* Check generate_path. *)
  (* refine (ex_intro _ (generate_path R _ 0 s) _). *)
  genExPath R s.
  Unshelve. all: cycle 1.

  intros R s P H.
  simpl.
  Locate "{ _ }".
  refine (ex_intro _ (
      (* (cofix coIH s' (Hin: exists n (fp: finite_path R s n), in_finite_path s' n fp) : path R s' := _) s _ *)
      (cofix coIH
        s'
        (* (Hin: {n & {fp: finite_path R s n | in_finite_path s' n fp}}) *)
        n
        : path R s'
        := _
      ) s 1
    ) _).
  Unshelve.
  all: cycle 1.
  - 
    (* destruct Hin as [n [fp Hin]]. *)
    (* destructExists Hin n. *)
    (* destructExists Hin fp. *)
    specialize (H n).
    destructExists H fp.
    
  - exists 1. eexists. constructor.
  - 
  

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
