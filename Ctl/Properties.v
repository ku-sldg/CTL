Require Import Ctl.Paths.
Require Import Ctl.Definition.
Require Import Ctl.Basic.
Open Scope tprop_scope.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import BinaryRelations.

Require Import Coq.Program.Equality.
Require Import Ctl.Tactics.
Require Import Tactics.General.

(* Require Import Setoid. *)

Theorem timpl_refl {state}: forall R (s: state) a,
  R @s ⊨ a ⟶ a.
Proof using.
  intros.
  tintro.
  assumption.
Qed.

Theorem timpl_trans {state}: forall R (s: state) a b c,
  R @s ⊨ (a ⟶ b) ⟶ (b ⟶ c) ⟶ a ⟶ c.
Proof using.
  intros R s a b c.
  tintros Hab Hbc Ha.
  tapplyc Hbc.
  tapplyc Hab. 
  assumption.
Qed.

Theorem timpl_trans' {state}: forall R (s: state) a b c,
  R @s ⊨ a ⟶ b ->
  R @s ⊨ b ⟶ c -> 
  R @s ⊨ a ⟶ c.
Proof using.
  intros R s a b c Hab Hbc.
  tintros Ha.
  tapplyc Hbc.
  tapplyc Hab. 
  assumption.
Qed.

Ltac treflexivity := simple apply timpl_refl.
Ltac treflexive := 
  match goal with 
  | |- _ @_ ⊨ ?a ⟶ ?a => treflexivity
  | |- _ @_ ⊨ ?a ⟶ ?b =>
      replace a with b;
        [ treflexivity
        | try easy; symmetry
        ]
  end.

Ltac ttransitivity x :=
  match goal with
  | |- ?R @?s ⊨ ?a ⟶ ?b =>
      simple apply (timpl_trans' R s a x b)
  end.

Ltac ettransitivity :=
  match goal with
  | |- ?R @?s ⊨ ?a ⟶ ?b =>
      simple eapply (timpl_trans' R s a _ b)
  end.

Lemma AG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ AG P -> R@s ⊨ AG (AG P).
Proof.
  intros R s P H.
  rewrite rew_AG.
  intros n p x Hin.
  rewrite rew_AG.
  intros n' p' x' Hin'.
  eapply in_path_combine in Hin'; [|eassumption].
  destruct exists Hin' n'' p''.
  etapplyc H.
  eassumption.
Qed.

Lemma EG_idempotent {state}:
  forall (R: relation state) s P, R@s ⊨ EG P -> R@s ⊨ EG (EG P).
Proof.
  intros R s P H.
  rewrite rew_EG.
  intro n.
  copy H Hpath1.
  specialize (Hpath1 n).
  destruct exists Hpath1 p.
  exists p.
  intros s' Hin.
  (* simpl in *. *)

  (* induction Hin; [assumption|assumption|]. *)
  (* intros n'. *)
Admitted.

Lemma path_step_rev_preserves_in {state}: 
  forall (R: relation state) s s' (r: R s s') n (p: path R n s') x,
    in_path x p ->
    in_path x (path_step_rev R n s s' r p).
Proof using.
  introv H.
  invc H.
  induction H0; simpl; repeat constructor.
  simpl in IHin_rtcT_idx.
  dependent induction IHin_rtcT_idx.
  assumption.
Qed.

Lemma rtcT_idx_path_step__rtcT_idx_path_step_rev {X}:
  forall (R: relation X) s x x' n,
    R x x' ->
    R^# n s x ->
    {s' &
      R s s' &
      R^# n s' x'}.
Proof using.
  introv Rxx' Rsx.
  revert x' Rxx'.
  induction Rsx; intros.
  - exists x'.
    + assumption. 
    + constructor.
  - applyc IHRsx in r.
    destruct exists r s'.
    exists s'.
    + assumption.
    + econstructor; eassumption.
Qed.

(* Expansion Laws *)
Theorem expand_AG {state}: forall (R: relation state) s P, R@s ⊨ AG P ⟷ P ∧ AX (AG P).
Proof.
  intros R s P.
  split; intro H.
  - split.
    + etapply H.
      repeat econstructor.
    + rewrite rew_AX.
      setoid_rewrite rew_AG.
      intros s' Hstep n p x Hin.
      etapply H.
      (* changes path type from `path R n s' to `path R (S n) s` *)
      eapply (path_step_rev_preserves_in _ _ _ Hstep).
      eassumption.
  - destruct H as [H1 H2].
    rewrite rew_AG.
    intros n p s' Hin.
    destruct exists p s''.
    invc Hin.
    induction H3; try assumption.
    eapply rtcT_idx_path_step__rtcT_idx_path_step_rev in p;
      [|eassumption]; clear r.
    destruct exists p s'.
    (* Note: unfold_AX in H2; unfold_AG in H2 doesn't seem to work here. Problem with binder? *)
    (* It works now, but only because I added manual rewrites *)
    etapplyc H2.
    + eassumption.
    + apply (in_path_last _ _ _ _ r).
Qed.

Theorem expand_EG {state}: forall (R: relation state) s P, R@s ⊨ EG P ⟷ P ∧ EX (EG P).
Admitted.

Theorem expand_AF {state}: forall (R: relation state) s P, R@s ⊨ AF P ⟷ P ∧ AX (AF P).
Admitted.

Theorem expand_EF {state}: forall (R: relation state) s P, R@s ⊨ EF P ⟷ P ∧ EX (EF P).
Admitted.

(* De Morgan's Laws *)
Theorem AF_EG {state}: forall R (s: state) P, R@s ⊨ AF (¬P) ⟶ ¬EG P.
Proof.
  intros.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H1 n.
  specialize (H2 n).
  destruct exists H2 p.
  specialize (H1 p).
  destruct exists H1 s'.
  specialize (H2 s').
  destruct H1; auto.
Qed.

(* Needs classical axioms *)
(*
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
*)

Theorem EG_AF {state}: forall R (s: state) P, R@s ⊨ EG (¬P) ⟶ ¬AF P.
Proof.
  intros R s P.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H2 n.
  specialize (H1 n).
  destruct exists H1 p.
  specialize (H2 p).
  destruct exists H2 s'.
  specialize (H1 s').
  destruct H2.
  apply H1; assumption.
Qed.

Theorem AG_EF {state}: forall R (s: state) P, R@s ⊨ AG (¬P) ⟶ ¬EF P.
  intros R s P.
  tintros H1 H2.
  tsimpl in *.
  destruct exists H2 n p s'.
  specialize (H1 n p s').
  apply H1; destruct H2; assumption.
Qed.

Theorem EF_AG {state}: forall R (s: state) P, R@s ⊨ EF (¬P) ⟶ ¬AG P.
Admitted.

Theorem AX_EX {state}: forall R (s: state) P, R@s ⊨ AX (¬P) ⟶ ¬EX P.
Admitted.

Theorem EX_AX {state}: forall R (s: state) P, R@s ⊨ EX (¬P) ⟶ ¬AX P.
Admitted.

(* in_path_before operator well_founded? *)

(* How I want to prove R @s ⊨ A[P W Q]:
    - At first state, either P or Q
    - for some path from the start, we assume P has held.
      Now we prove that for some additional step, either P holds 
      or Q holds
 *)

Theorem AW_ind {state}: forall (R: relation state) s P Q,
  R @s ⊨ P ∨ Q ->
  (forall s' (Rss': R^* s s'),
    (forall x, in_rtcT x Rss' -> R @x ⊨ P ∧ ¬ Q) ->
    forall s'', R s' s'' ->
    R @s'' ⊨ P ∨ Q) -> 
  R @s ⊨ A[P W Q].
Proof using.
  intros R s P Q Hinit Hstep.
  rewrite rew_AW.
  intros n p y i Hin Hbefore.
  invc Hin.
  induction H.
  - assumption.
  - specialize (Hstep x (rtcT_idx_to_rtcT p)).
    applyc Hstep; [|eassumption].
    intros x0 Hin.
    applyc Hbefore.

    clear - Hin.
    (* Obvious from Hin *)
    todo.
  - apply IHin_rtcT_idx_at.
    intros x0 Hbefore2.
    applyc Hbefore.
    (* Obvious from Hbefore2 *)
    todo.
Admitted.

(* Theorem AU_from_AW {state}: forall (R: relation state) s P Q,
  R @s ⊨ A[P W Q] ∧ AF Q ->
  R @s ⊨ A[P U Q].
Proof using. *)

(* Exposes the earliest witness of AF *)
Theorem AF_earliest {state}: forall (R: relation state) s P,
  R @s ⊨ AF P ->
  exists n, forall p: path R n s, exists y i,
    in_path_at y i p /\ R @y ⊨ P /\ 
    forall x, in_path_before x i p -> R @x ⊭ P.
Proof using.
  intros R s P H.
  tsimpl in H.
  destruct exists H n.
  exists n.
  intro p.
  specialize (H p).
  (* induct over in_path. At each step, use classical reasoning to 
     destruct cases of P is satisfied. If so, end early and prove ealiest.
     Else, continue.
   *)

Theorem AW_AF__AU {state}: forall (R: relation state) s P Q,
  (* R @s ⊨ A[P W Q] ∧ AF Q ⟶ A[P U Q]. *)
  R @s ⊨ A[P W Q] ⟶ AF Q ⟶ A[P U Q].
Proof using.
  intros.
  (* tintro H.
  destruct H as [H1 H2]. *)
  tintros HAW HAF.
  (* tsimpl. *)
  rewrite rew_AU.
  rewrite rew_AF in HAF.
  destruct exists HAF n.
  exists n.
  intro p.
  specialize (HAF p).
  (* Problem: need to get *earliest* s' satisfying HAF *)
  destruct HAF as [s' [Hin Hs'Q]].
  exists s'.
  apply in_path__in_path_at in Hin.
  destruct Hin as [i [iLt Hin]].
  exists i.
  max split; try assumption.
  intros sP Hbefore.
  rewrite rew_AW in HAW.
  specialize (HAW n p s' i Hin).
  (* Might need to induct on Hbefore? *)



(* How I want to prove R @s ⊨ A[P U Q]:
 *)

Theorem EU_rtcT {state}: forall (R: relation state) s P Q,
  (exists s' n (r: R^# n s s') s'', 
    R s' s'' /\
    R @s'' ⊨ Q /\ 
    forall x, in_rtcT_idx x r -> R @x ⊨ P)
  -> R @s ⊨ E[P U Q].
Proof using.
  intros.
  destruct exists H s' n r s''.
  destruct H as [H1 [H2 H3]].
  expand_tEntails.
  exists (S n).
  copy r r1.
  eapply rtcT_idx_step in r1; [|eassumption]; clear H1.
  exists (rtcT_idx_to_path r1) s'' n.
  max split.
  - (* in_rtcT_idx_at_last *)
    admit.
  - assumption.
  - 
 

Theorem EU_rtcT {state}: forall (R: relation state) s P Q,
  (exists s' (r: R^* s s') s'', 
    R s' s'' /\
    R @s'' ⊨ Q /\ 
    forall x, in_rtcT x r -> R @x ⊨ P)
  -> R @s ⊨ E[P U Q].
Proof using.
  intros.
  destruct exists H s' r s''.
  destruct H as [H1 [H2 H3]].
  expand_tEntails.
  apply rtcT_to_rtcT_idx in r.
  exists 

  *)