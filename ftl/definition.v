(* From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. *)

Require Import Coq.Program.Basics.
Open Scope program_scope.

Require Import extra.
Require Import my_tactics.

(* Definition path (state: Set) := neList state. *)

(* Definition currentState {state} (p : path state) := neHd p. *)

(* Definition extendsPath {state} (p1 p2: path state) := extendsNe p1 p2. *)

Definition binary_relation (A: Type) := A -> A -> Prop.
Definition serial {A} (R : binary_relation A) := forall a, exists b, R a b.
Definition serial_transition A := sig (@serial A).

Inductive existsPath {state} (R: binary_relation state) : state -> state -> Prop :=
  | existsNow   : forall s, existsPath R s s
  | existsLater : forall s1 s2 s3, R s2 s3 -> existsPath R s1 s2 -> existsPath R s1 s3.

Inductive path {state} (R: binary_relation state) : state -> neList state -> Prop :=
  | pathTrivial : forall s, path R s (neSome s)
  | pathStep    : forall s1 s2 p, R s1 s2 -> path R s2 p -> path R s1 (neCons s1 p).

Definition inPath {state} (s: state) := inNe s.

(* Transition relation assumed to be serial (i.e. every state has at least one successor) *)
(* Note, this is a sigma type, but with the first element indexed into the type. *)
(* Inductive model : Set -> Type :=
  | Model : forall state: Set, binary_relation state -> model state.

Definition getStateType {state} (M: model state) := state.
Definition validPaths {state} (M: model state) :=
  match M with
  | Model _ paths => paths
  end. *)

(* Inductive TProp (state: Set) : Type := *)
Inductive TProp state : Type :=
  | TTop  : TProp state
  | TBot  : TProp state
  | TLift : (state -> Prop) -> TProp state
  | TNot  : TProp state -> TProp state
  | TConj : TProp state -> TProp state -> TProp state
  | TDisj : TProp state -> TProp state -> TProp state
  | TImpl : TProp state -> TProp state -> TProp state
  | AX    : TProp state -> TProp state
  | EX    : TProp state -> TProp state
  | AF    : TProp state -> TProp state
  | EF    : TProp state -> TProp state
  | AG    : TProp state -> TProp state
  | EG    : TProp state -> TProp state
  | AU    : TProp state -> TProp state -> TProp state
  | EU    : TProp state -> TProp state -> TProp state.

(* Make state argument implicit *)
Arguments TTop  {state}%type_scope.
Arguments TBot  {state}%type_scope.
Arguments TLift {state}%type_scope.
Arguments TNot  {state}%type_scope.
Arguments TConj {state}%type_scope.
Arguments TDisj {state}%type_scope.
Arguments TImpl {state}%type_scope.
Arguments AX    {state}%type_scope.
Arguments EX    {state}%type_scope.
Arguments AF    {state}%type_scope.
Arguments EF    {state}%type_scope.
Arguments AG    {state}%type_scope.
Arguments EG    {state}%type_scope.
Arguments AU    {state}%type_scope.
Arguments EU    {state}%type_scope.

(* Definition futurePath {state} (M: model state) (p: path state) (s: state) :=
  validPaths M p /\ (neHd p = s). *)

(* This theorem supports alternate definitions:
  | AG P => forall s', existsPath M s s' -> M;s' ⊨ P
  | EF P => exists s', existsPath M s s' -> M;s' ⊨ P *)
Theorem existsPathEq {state}: forall M (s: state) (P: state -> Prop),
  (forall p, path M s p -> forall s', inPath s' p -> P s')
  <->
  (forall s', existsPath M s s' -> P s').
Admitted.

Reserved Notation "M ; s ⊨ P" (at level 70).
Reserved Notation "M ; s ⊭ P" (at level 70).
(* Replace binary_relation with serial_transition if needed *)
Fixpoint TEntails {state} (M: binary_relation state) (s: state) (tp: TProp state): Prop :=
  match tp with
  | TTop => True
  | TBot => False
  | TLift P => P s
  | TNot P => M;s ⊭ P
  | TConj P Q => M;s ⊨ P /\ M;s ⊨ Q
  | TDisj P Q => M;s ⊨ P \/ M;s ⊨ Q
  | TImpl P Q => M;s ⊨ P -> M;s ⊨ Q
  | AX P => forall s', M s s' -> M;s' ⊨ P
  | EX P => exists s', M s s' -> M;s' ⊨ P
  | AG P => forall p, path M s p -> forall s', inPath s' p -> M;s' ⊨ P
  | EG P => exists p, path M s p /\ forall s', inPath s' p -> M;s' ⊨ P
  | AF P => forall p, path M s p -> exists s', inPath s' p /\ M;s' ⊨ P
  | EF P => exists p, path M s p /\ exists s', inPath s' p /\ M;s' ⊨ P
  (* Needs index. Maybe replace neList with vec, and zip with index *)
  (* | AU P Q => forall p, path m s p -> exists s', inPath s' p /\ M;s' ⊨ P /\ forall s'', inPath s'' (pathBefore s' p) ->  *)
  | _ => False
  end
  where "M ; s ⊨ P" := (TEntails M s P)
    and "M ; s ⊭ P" := (~ M;s ⊨ P).

Notation "⊤" := (TTop).
Notation "⊥" := (TBot).
Notation "^ P" := (TLift P) (at level 35).
Notation "P ∧ Q" := (TConj P Q) (at level 45, right associativity).
Notation "P ∨ Q" := (TDisj P Q) (at level 55, right associativity).
Notation "P --> Q" := (TImpl P Q) (at level 68,  right associativity).
Notation "P <--> Q" := ((P --> Q) ∧ (Q --> P)) (at level 65,  right associativity).
Notation "¬ P" := (TNot P) (at level 40).
Notation "'A' [ P 'U' Q ]" := (AU P Q) (at level 40).
Notation "'E' [ P 'U' Q ]" := (EU P Q) (at level 40).

(* Basic Properties *)

Theorem tModusPonens {state}: forall (M: binary_relation state) s P Q,
  M;s ⊨ P --> Q -> M;s ⊨ P -> M;s ⊨ Q.
Proof. auto. Qed.

Theorem tModusPonens_flipped {state}: forall (M: binary_relation state) s P Q,
  M;s ⊨ P -> M;s ⊨ P --> Q -> M;s ⊨ Q.
Proof. auto. Qed.

(* TODO: if H is a biimpl, destruct into two impls, try both *)
(* or is this case already handled? *)
Ltac tapply H :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H';
  clear H'.

Ltac etapply H :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  eapply H';
  clear H'.

Ltac tapply_in H H2 :=
  let H' := fresh in 
  pose proof @H as H';
  (* simpl should reduce implications (among other things) *)
  simpl in H';
  apply H' in H2;
  clear H'.

(* If simpl isn't called before specialize, and specializable binder isn't visible,
   then specialize will over-evaluate before specializing *)
Ltac tspecialize H a := simpl in H; specialize (H a).
(* Alternative version: *)
(* Only works in modusPonens *)
(* Ltac tspecialize H a :=
  apply (tModusPonens_flipped _ _ _ _ a) in H. *)
Tactic Notation "tspecialize2" hyp(H) ident(a) ident(b) :=
    tspecialize H a;
    tspecialize H b.
Tactic Notation "tspecialize3" hyp(H) ident(a) ident(b) ident(c) :=
    tspecialize2 H a b;
    tspecialize H c.
Tactic Notation "tspecialize4" hyp(H) ident(a) ident(b) ident(c) ident(d) :=
    tspecialize3 H a b c;
    tspecialize H d.

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

(* Can we use a tactic to rewrite biimplications? *)

Theorem paths_nonempty {state}: forall M (s: state), exists p, path M s p.
Proof.
  intros.
  eexists.
  econstructor.
Qed.

(* While the type makes this look arbitrary, it is just the trivial path *)
Definition arbitrary_path {state} (M: binary_relation state) (s: state) : {π | path M s π} :=
  exist (path M s) (neSome s) (pathTrivial M s).

Theorem inPathTrivial {state}: forall M (s: state) p, path M s p -> inPath s p.
Proof.
  (* intros M s p Hpath.
  inv Hpath; constructor. *)
  intros; find_solve_inversion.
Qed.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall M (s: state) P, M;s ⊨ ¬AF P <--> EG (¬P).
Proof.
  intros M s P.
  split.
  - intros H.
    exists (neSome s).
    split; [constructor|].
    intros s' _ Hp.
    simpl in H; apply H.
    intros p _.
    exists s'.
    intros _.
    assumption.
  - intros H H2.

    (* switch to backwards reasoning? *)
    (* simpl in H2.
    specialize (H2 (neSome s) (pathTrivial M s)).
    destruct H2 as [s' H2]. *)

    simpl in H.
    destruct H as [p [H H1]].
    apply (H1 s).
    + eapply inPathTrivial; eassumption.
    + exfalso.
      tspecialize2 H2 p H.
      destruct H2 as [s' H2].
      apply (H1 s').
Qed.


