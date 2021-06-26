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

Inductive in_path {state: Type} {R: relation state} {s} : state -> path R s -> Prop :=
  | in_head : forall s' r p,
      in_path s (step s s' r p)
  | in_tail : forall s' x r p,
      @in_path state R s' x p ->
      in_path x (step s s' r p).

Definition forall_in_path' {state: Type} {R: relation state} {s: state}
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
Inductive finite_path {state} (R: relation state) : state -> nat -> Prop := 
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

Lemma in_path_refl_finite {state} {R: relation state} {s} :
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

Theorem exists_in_path_refl_finite {state} {R: relation state} {s}:
  forall P (p: path R s),
    (exists n s', in_finite_path s' n (path_to_finite p n) /\ P s') ->
    (exists s', in_path s' p /\ P s').
Proof.
Admitted.