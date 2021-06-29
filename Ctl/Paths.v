Require Import GeneralTactics.
Require Import BinaryRelations.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Inductive path {state} (R: relation state) : state -> nat -> Type := 
  | path_trivial : forall s, path R s 0
  | path_step : forall s s' n,
      R s s' ->
      path R s' n ->
      path R s (S n).
Arguments path_trivial {state R}%type_scope.
Arguments path_step    {state R}%type_scope.

Inductive in_path {state} {R: relation state} {s}
  : state -> forall {n}, path R s n -> Prop :=
  | in_path_head_trivial :
      in_path s (path_trivial s)
  | in_path_head_step : forall s' n r p,
      in_path s (path_step s s' n r p)
  | in_path_tail : forall s' x n r p,
      @in_path state R s' x n p ->
      in_path x (path_step s s' n r p).

(* A single-step path *)
Definition path_singleton {state} {R: relation state} {x y} (r: R x y) : path R x 1 :=
  path_step x y 0 r (path_trivial y).

Require Import Psatz.
Definition path_pop n {state} {R: relation state} {m s} (p: path R s m) 
  : {s' & path R s' (m-n)}.
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

Definition path_tail {state} {R: relation state} {s n}
  (p: path R s (S n)) : {s' & path R s' n}.
inv p.
eexists.
eassumption.
Defined.

Lemma path_tail_correct {state} {R: relation state}:
  forall s s' n r (p: path R s' n),
  (* path_tail (path_step s s' n r p) = existT _ s' p. *)
  projT2 (path_tail (path_step s s' n r p)) = p.
Proof. reflexivity. Qed.

Definition path_get_step {state} {R: relation state} {m s}
  n (HinBounds: n < m) (p: path R s m) : {x & {y | R x y}}.
move n at top.
generalize_max.
induction n; intros.
- inv p.
  + lia.
  + repeat eexists. eassumption.
- destruct m as [|m']; [lia|].
  inv p.
  clear H1.
  assert (HLt: n < m') by lia.
  specialize (IHn state R m' s' HLt X).
  destructExists IHn x.
  destructExists IHn y.
  repeat eexists.
  eapply IHn.
Defined.

Definition arbitrary_path {state} {R: relation state} 
  (sw: serial_witness R) s n: path R s n.
induction n.
- constructor.
- induction IHn.
  + specialize (sw s).
    destructExists sw s'.
    econstructor.
    * eassumption.
    * constructor.
  + econstructor; eassumption.
Defined.

Definition gen_path {state} {R: relation state} {s}
  (sfw: serial_from_witness R s) n: path R s n.
induction n.
- constructor.
- induction IHn.
  + specialize (sfw s (rt_refl _ R s)).
    destructExists sfw s'.
    econstructor.
    * eassumption.
    * constructor.
  + econstructor.
    * eassumption.
    * apply IHIHn.
      intros s'' Hsteps.
      apply sfw.
      eapply rt_trans.
      -- eapply rt_step. eassumption.
      -- assumption.
Defined.