Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import BinaryRelations.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import Coq.Program.Equality.
Require Import Ctl.Tactics.
Require Import Tactics.General.

Lemma AG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ AG P -> R@s ⊨ AG (AG P).
Proof.
  intros R s P H.
  intros n p x Hin.
  intros n' p' x' Hin'.
  pose proof (path_combine _ _ _ _ _ p p' Hin Hin') as HIn''.
  destruct exists HIn'' n'' p''.
  eapply H.
  eassumption.
Qed.

Ltac copy H ident := pose proof H as ident.

Lemma EG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ EG P -> R@s ⊨ EG (EG P).
Proof.
  intros R s P H.
  intro n.
  copy H Hpath1.
  tspecialize Hpath1 n.
  destruct exists Hpath1 p.
  exists p.
  intros s' Hin.
  (* simpl in *. *)

  induction Hin; [assumption|assumption|].
  intros n'.
Admitted.

Theorem rtc_AG {state}: forall (R: relation state) s P, 
  (forall s', R^* s s' -> R@s' ⊨ P) ->
  R@s ⊨ AG P.
Proof.
  intros R s P H.
  intros n p s' Hin.
  apply H.
  eapply path_to_rtc.
  eassumption.
Qed. 

Theorem AG_rtc {state}: forall (R: relation state) s P, 
  R@s ⊨ AG P ->
  forall s', R^* s s' -> R@s' ⊨ P.
Proof.
  intros R s P H s' Hsteps.
  apply rtc_to_path in Hsteps.
  destruct exists Hsteps n p.
  apply H with (p:=p).
  assumption.
Qed.

Theorem tModusPonens {state}: forall (M: relation state) s P Q,
  M@s ⊨ P --> Q -> M@s ⊨ P -> M@s ⊨ Q.
Proof. auto. Qed.

Theorem tModusPonens_flipped {state}: forall (M: relation state) s P Q,
  M@s ⊨ P -> M@s ⊨ P --> Q -> M@s ⊨ Q.
Proof. auto. Qed.

Theorem tModusTollens {state}: forall (R: relation state) s P Q,
  R@s ⊨ (P --> Q) --> ¬Q --> ¬P.
Proof.
  intros R s P Q.
  intros Hpq Hnq Hp.
  tapply Hnq.
  tapply Hpq.
  assumption.
Qed.

Theorem tbimpl_neg {state}: forall (R: relation state) s P Q,
  R@s ⊨ (P <--> Q) --> (¬P <--> ¬Q).
Proof.
  intros R s P Q.
  split; intro; (eapply (tModusTollens R); [apply H | assumption]).
  (* (etapply (tModusTollens R); [apply H | assumption]). *)
Qed.

(* Good test for tactics *)
Theorem TImpl_trans {state}: forall M (s: state) P Q R,
  M@s ⊨ (P --> Q) --> (Q --> R) --> P --> R.
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
Theorem tNot_def {state}: forall M (s: state) P, M@s ⊨ ¬P <--> (P --> ⊥).
Proof.
  intros M s P.
  split; intros H; auto.
Qed.

Lemma AG_steps_strong {state}: forall (R: relation state) s s' P,
  R^* s s' -> R@s ⊨ AG P -> R@s' ⊨ AG P.
Proof.
  intros R s s' P Hsteps H.
  pose proof (AG_rtc _ _ _ H) as H0; clear H; rename H0 into H.
  apply rtc_AG.
  intros s'' Hsteps2.
  apply H.
  eapply rtc_trans; eassumption.
Qed.

Lemma AG_steps_weak {state}: forall (R: relation state) s s' P,
  R^* s s' -> R@s ⊨ AG P -> R@s' ⊨ P.
Proof.
  intros R s s' P Hsteps H.
  pose proof (AG_steps_strong _ _ _ _ Hsteps H) as Hstrong.
  apply Hstrong with (p:= path_trivial s').
  constructor.
Qed.

(* Expansion Laws *)
Theorem expand_AG {state}: forall (R: relation state) s P, R@s ⊨ AG P <--> P ∧ AX (AG P).
Proof.
  intros R s P.
  split; intro H.
  - split.
    + eapply H.
      econstructor.
    + intros s' Hstep.
      eapply AG_steps_strong.
      * eapply rtn1_trans; [eassumption|constructor].
      * assumption.
  - destruct H as [H1 H2].
    intros n p s' Hin.
    move Hin at top.
    generalize dependent P.
    induction Hin; intros; try assumption.
    clear H1.
    applyc IHHin.
    + eapply H2.
      * eassumption.
      * econstructor.
    + intros s'' r' n' p' y Hin'.
      apply H2 with (p:= path_step s' s'' n' r' p').
      * assumption.
      * constructor. assumption.
Qed.

Theorem expand_EG {state}: forall (R: relation state) s P, R@s ⊨ EG P <--> P ∧ EX (EG P).
Admitted.

Theorem expand_AF {state}: forall (R: relation state) s P, R@s ⊨ AF P <--> P ∧ AX (AF P).
Admitted.

Theorem expand_EF {state}: forall (R: relation state) s P, R@s ⊨ EF P <--> P ∧ EX (EF P).
Admitted.

Lemma in_path_head {state} {R: relation state}:
  forall s n (p: path R s n), in_path s p.
Proof.
  intros s n p.
  destruct p; constructor.
Qed.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall R (s: state) P, R@s ⊨ AF (¬P) --> ¬EG P.
Proof.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H n.
  tspecialize H2 n.
  destruct exists H2 p.
  tspecialize H p.
  destruct exists H s'.
  tspecialize H2 s'.
  destruct H; auto.
Qed.

(* Needs classical axioms *)
Theorem AF_EG' {state}: forall R (s: state) P, R@s ⊨ ¬AF P --> EG (¬P).
Proof.
  intros R s P H.
  intro n.
  induction n.
  - exists (path_trivial s).
    intros s' Hin H2.
    inv Hin.
    tapply H.
    exists 0.
    intro p.
    exists s'.
    split.
    + apply in_path_head.
    + assumption.
  - destruct exists IHn p.
    (* Could proceed from induction on p.
       But where to deduce extra step at the end of the path?
       Hypothetically, from H. But can that be done intuitionistically? *)
    simpl in H.
    (* Can't extract any information from H until I get to a "False" goal.
       But I can't move my goal forward until I provide a path.
       Giving an existential won't work, since the ultimate value would 
       presumably not be in the current scope. *)
Abort.

Theorem exists_deMorg: forall X (P: X -> Prop), ~(exists x, P x) -> forall x, ~ P x.
Proof.
  intros X P H.
  intros x.
  intros H'.
  apply H.
  exists x.
  assumption.
Qed.

Theorem AF_EG' {state}: forall R (s: state) P, 
  serial_from_witness R s ->
  R@s ⊨ ¬AF P --> EG (¬P).
Proof.
  intros R s P Hserial H n.
  simpl in H.
  pose proof (exists_deMorg _ _ H n) as H2; clear H; rename H2 into H; simpl in H.
  exists (gen_path Hserial n).
  intros s' Hin H2.
  apply H.
  intros p'.
  exists s'.
  split; [|assumption].
  (* No relation between p' and the generated path *)
Abort.

Definition classical_double_neg_elim : Prop := forall (P: Prop), ~~P -> P.
Theorem AF_EG' {state}: forall R (s: state) P, 
  classical_double_neg_elim ->
  R@s ⊨ ¬AF P --> EG (¬P).
Proof.
  (* Proof sketch:
    ¬AF P ≡ ¬AF (¬¬P)
          ≡ ¬¬EG (¬¬P)
          ≡ EG P (double elimination)
  *)
Admitted.

Theorem EG_AF {state}: forall R (s: state) P, R@s ⊨ EG (¬P) --> ¬AF P.
Proof.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H2 n.
  tspecialize H n.
  destruct exists H p.
  tspecialize H2 p.
  destruct exists H2 s'.
  tspecialize H s'.
  destruct H2.
  apply H; assumption.
Qed.

Theorem AG_EF {state}: forall R (s: state) P, R@s ⊨ AG (¬P) --> ¬EF P.
  intros R s P H H2.
  simpl in H, H2.
  destruct exists H2 n p s'.
  tspecialize H n p s'.
  tapply H; destruct H2; assumption.
Qed.

Theorem EF_AG {state}: forall R (s: state) P, R@s ⊨ EF (¬P) --> ¬AG P.
Admitted.

Theorem AX_EX {state}: forall R (s: state) P, R@s ⊨ AX (¬P) --> ¬EX P.
Admitted.

Theorem EX_AX {state}: forall R (s: state) P, R@s ⊨ EX (¬P) --> ¬AX P.
Admitted.
