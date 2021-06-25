Require Import Coq.Lists.List.
Import ListNotations.
Open Scope list_scope.
Require Import Coq.Relations.Relation_Definitions.

Require Import Ctl.Definition.
Require Import Ctl.Tactics.
Require Import Tactics.


Theorem tModusPonens {state}: forall (M: relation state) s P Q,
  M;s ⊨ P --> Q -> M;s ⊨ P -> M;s ⊨ Q.
Proof. auto. Qed.

Theorem tModusPonens_flipped {state}: forall (M: relation state) s P Q,
  M;s ⊨ P -> M;s ⊨ P --> Q -> M;s ⊨ Q.
Proof. auto. Qed.

(* Good test for tactics *)
Theorem TImpl_trans {state}: forall M (s: state) P Q R, M;s ⊨ (P --> Q) --> (Q --> R) --> P --> R.
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

Theorem paths_nonempty {state}: forall (M: relation state) s, exists p, path M (s :: p).
Proof.
  intros.
  eexists.
  econstructor.
Qed.

Definition arbitrary_path {state} (M: relation state) s : {π | path M (s :: π)}.
  repeat econstructor.
Defined.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall M (s: state) P, M;s ⊨ ¬AF P <--> EG (¬P).
Proof.
  intros M s P.
  split.
  - intros H.
    exists nil.
    split; [constructor|].
    intros s' Hin Hp.
    inv Hin.
    tconsume H.
    eauto.
  - intros H H2.
    destruct H as [p [Hpath H]].
    tspecialize2 H2 p Hpath.
    destruct H2 as [s' [Hin H2]].
    specialize (H s').
    consume H; assumption.
Qed.

Theorem AF_EG' {state}: forall M (s: state) P, M;s ⊨ AF (¬P) <--> ¬EG P.
Admitted.

Theorem EF_AG {state}: forall M (s: state) P, M;s ⊨ ¬EF P <--> AG (¬ P).
Proof.
  intros M s P.
  split.
  - intros H p Hpath s' Hin H2.
    tconsume H.
    eauto.
  - intros H H2.
    destruct H2 as [p [Hpath [s' [Hin H2]]]].
    tspecialize3 H p Hpath s'.
    tconsume H; assumption.
Qed.

Theorem AX_EX {state}: forall M (s: state) P, M;s ⊨ ¬AX P <--> EX (¬ P).
Admitted.
