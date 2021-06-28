Require Import GeneralTactics.

Require Import Coq.Relations.Relation_Definitions.

CoInductive path {state} (R: relation state) (s: state) := 
  | step : forall s', R s s' -> path R s' -> path R s.
Arguments step {state R}%type_scope.

(* Definition path_coind {state: Set} {R: relation state}
  (P: forall s, path R s -> Prop)
  (coind_step: forall s s' (r : R s s') p, P s' p -> P s (step s s' r p))
  : forall {s} (p: path R s), (P s p).
refine (cofix F {s} p := _).

Definition path_coind {state: Set} {R: relation state}
  (P: forall s, path R s -> Prop)
  (coind_step: forall s s' (r : R s s') p, P s' p -> P s (step s s' r p)) :=
  cofix F {s} (p: path R s) : (P s p) :=
    (* match p as pname return (P s pname) with  *)
    match p with 
    | step _ s' r p' => coind_step s s' r p' (F p')
    end. *)

CoInductive forall_in_path {state R s} (P: state -> Prop) : path R s -> Prop :=
  | forall_in_step : forall s' r (p: path R s'),
      P s ->
      (* Coq infers the wrong value for `s` *)
      (* forall_path P p -> *)
      @forall_in_path state R s' P p ->
      forall_in_path P (step s s' r p).

Inductive in_path {state} {R: relation state} {s} : state -> path R s -> Prop :=
  | in_head : forall s' r p,
      in_path s (step s s' r p)
  | in_tail : forall s' x r p,
      @in_path state R s' x p ->
      in_path x (step s s' r p).

Definition forall_in_path' {state} {R: relation state} {s: state}
  (P: state -> Prop) (p: path R s) :=
  forall s', in_path s' p -> P s'.

CoInductive exists_in_path {state R s} (P: state -> Prop) : path R s -> Prop :=
  | exists_in_step : forall s' r (p: path R s'),
      P s \/ @exists_in_path state R s' P p ->
      exists_in_path P (step s s' r p).

CoInductive exists_path {state R} (P: state -> Prop) (s: state) : Prop :=
  | exists_step :
      P s ->
      (exists s', R s s' /\ exists_path P s') ->
      exists_path P s.

(* Require Import Coq.Vectors.VectorDef. *)
Inductive finite_path {state} (R: relation state) : state -> nat -> Type := 
  | finite_trivial : forall s, finite_path R s 0
  | finite_step : forall s s' n,
      R s s' ->
      finite_path R s' n ->
      finite_path R s (S n).
Arguments finite_trivial {state R}%type_scope.
Arguments finite_step    {state R}%type_scope.

Inductive in_finite_path {state} {R: relation state} {s}
  : state -> forall n: nat, finite_path R s n -> Prop :=
  | in_finite_head : forall s' n r p,
      in_finite_path s (S n) (finite_step s s' n r p)
  | in_finite_tail : forall s' x n r p,
      @in_finite_path state R s' x n p ->
      in_finite_path x (S n) (finite_step s s' n r p).

Fixpoint path_to_finite {state} {R: relation state} {s} 
  (p: path R s) (n: nat) : finite_path R s n :=
  match n with
  | 0 => finite_trivial s
  | S n' =>
      match p with
      | step _ s' r p => finite_step s s' n' r (path_to_finite p n')
      end
  end.

Require Import Psatz.
Definition finite_path_pop n {state} {R: relation state} {m s} (fp: finite_path R s m) 
  : {s' & finite_path R s' (m-n)}.
  induction n.
  - exists s.
    replace (m - 0) with m by lia.
    assumption.
  - destructExists IHn s'.
    inv IHn.
    + exists s'.
      rewrite <- H1 in IHn.
      replace (m - S n) with 0 by lia.
      assumption.
    + exists s'0.
      replace (m - S n) with n0 by lia.
      assumption.
Qed.

Definition finite_path_tail {state} {R: relation state} {s n}
  (fp: finite_path R s (S n)) : {s' & finite_path R s' n}.
inv fp.
eexists.
eassumption.
Defined.

Lemma finite_path_tail_correct {state} {R: relation state}:
  forall s s' n r (fp: finite_path R s' n),
  (* finite_path_tail (finite_step s s' n r fp) = existT _ s' fp. *)
  projT2 (finite_path_tail (finite_step s s' n r fp)) = fp.
Proof. reflexivity. Qed.

Definition finite_path_get_step {state} {R: relation state} {m s}
  n (HinBounds: n < m) (fp: finite_path R s m) : {x & {y | R x y}}.
max_induction n; intros.
- inv fp.
  + lia.
  + repeat eexists. eassumption.
- destruct m as [|m']; [lia|].
  inv fp.
  clear H1.
  assert (HLt: n < m') by lia.
  specialize (IHn state R m' s' HLt X).
  destructExists IHn x.
  destructExists IHn y.
  repeat eexists.
  eapply IHn.
Defined.

Theorem in_path_refl_finite {state} {R: relation state} {s} :
  forall (p: path R s) s',
  in_path s' p ->
  exists n, in_finite_path s' n (path_to_finite p n).
Proof.
  intros p s' Hin.
  induction Hin.
  - exists 1.
    constructor.
  - destructExists IHHin n.
    exists (S n).
    constructor; assumption.
Qed.

Theorem in_path_refl_infinite {state} {R: relation state} {s} :
  forall (p: path R s) s',
  (exists n, in_finite_path s' n (path_to_finite p n)) ->
  in_path s' p.
Proof.
  (* intros p. *)

  intros p s' H.
  destructExists H n.
  induction H.
  - destruct p; constructor.
  - 
  
Admitted.

Theorem in_path_refl {state} {R: relation state} {s} :
  forall (p: path R s) s',
  in_path s' p <->
  exists n, in_finite_path s' n (path_to_finite p n).
Proof.
Admitted.

Theorem forall_in_path_refl_finite {state} {R: relation state} {s}:
  forall (P: state -> Prop) (p: path R s),
    (forall n s', in_finite_path s' n (path_to_finite p n) -> P s') ->
    (forall s', in_path s' p -> P s').
Proof.
  intros P p H s' Hin.
  induction Hin.
  - apply (H 1).
    constructor.
  - apply IHHin.
    intros n x' H'.
    apply (H (S n)).
    constructor; assumption.
Qed.

Require Import Coq.Program.Equality.
Theorem exists_in_path_refl_finite {state} {R: relation state} {s}:
  forall P (p: path R s),
    (exists n s', in_finite_path s' n (path_to_finite p n) /\ P s') ->
    (exists s', in_path s' p /\ P s').
Proof.
  intros P p H.
  destruct H as [n [s' [Hin HP]]].
  exists s'.
  split; [|assumption].
  dependent induction Hin.
  - destruct p as [x' r' p].
    simpl in x.
    assert (s' = x'). { admit. }
    constructor.
  - try apply IHHin.
Admitted.
