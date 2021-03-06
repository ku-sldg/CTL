Require Import Notation.
Require Import TacticCombinators.

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.


(* expanded exists tactic to work with inhabited type *)
Tactic Notation "_exists" uconstr(u) := 
  match goal with 
  | |- inhabited _ => refine (inhabits u)
  | _ => exists u
  end.

Tactic Notation "exists" uconstr(x1) :=
  _exists x1.
Tactic Notation "exists" uconstr(x1) uconstr(x2) :=
  exists x1; _exists x2.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) :=
  exists x1 x2; _exists x3.
Tactic Notation "exists" uconstr(x1) uconstr(x2) uconstr(x3) uconstr(x4) :=
  exists x1 x2 x3; _exists x4.


(* destruct variants *)

Tactic Notation "destruct" "exists" hyp(H) ident(id) :=
  destruct H as [id H].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) :=
  destruct H as [id1 [id2 H]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) :=
  destruct H as [id1 [id2 [id3 H]]].
Tactic Notation "destruct" "exists" hyp(H) ident(id1) ident(id2) ident(id3) ident (id4) :=
  destruct H as [id1 [id2 [id3 [id4 H]]]].

Tactic Notation "destruct" "or" hyp(H) := destruct H as [H|H].

Ltac destructl H := destruct H as [H ?].
Ltac destructr H := destruct H as [? H].


(* Clear variants. Tactics postfixed with "c" clear a hypothesis
   after using it.
 *)

Tactic Notation "applyc" hyp(H) := apply H; clear H.
Tactic Notation "applyc" hyp(H) "in" hyp(H2) := apply H in H2; clear H.

Tactic Notation "eapplyc" hyp(H) := eapply H; clear H.
Tactic Notation "eapplyc" hyp(H) "in" hyp(H2) := eapply H in H2; clear H.

Ltac specializec H x := specialize (H x); clear x.

Tactic Notation "rewritec" hyp(H) :=
  rewrite H; clear H.
Tactic Notation "rewritec" hyp(H) "in" hyp(H2) :=
  rewrite H in H2; clear H.
Tactic Notation "rewritec" hyp(H) "in" "*" :=
  rewrite H in *; clear H.

Tactic Notation "rewritec" "->" hyp(H) :=
  rewrite -> H; clear H.
Tactic Notation "rewritec" "->" hyp(H) "in" hyp(H2) :=
  rewrite -> H in H2; clear H.
Tactic Notation "rewritec" "->" hyp(H) "in" "*" :=
  rewrite -> H in *; clear H.

Tactic Notation "rewritec" "<-" hyp(H) :=
  rewrite <- H; clear H.
Tactic Notation "rewritec" "<-" hyp(H) "in" hyp(H2) :=
  rewrite <- H in H2; clear H.
Tactic Notation "rewritec" "<-" hyp(H) "in" "*" :=
  rewrite <- H in *; clear H.


(* Unfold one layer *)
Tactic Notation "expand" constr(x) := unfold x; fold x.
Tactic Notation "expand" constr(x) "in" hyp(H) := unfold x in H; fold x in H.
Tactic Notation "expand" constr(x) "in" "*" := unfold x in *; fold x in *.


(* Like `contradiction`, but introduces unification variables instead of failing *)
Tactic Notation "econtradiction" uconstr(u) := exfalso; eapply u.

(* `pose new proof`, variant of `pose proof` that fails if such a hypothesis
   already exists in the context. Useful for automation which saturates the 
   context with generated facts
 *)

Ltac assumed H :=
  let t := type of H in
  match goal with 
  | _: t |- _ => true
  end + 
  fail "Hypothesis not assumed".

Tactic Notation "pose" "new" "proof" constr(H) :=
  not assumed H;
  pose proof H.

Tactic Notation "pose" "new" "proof" constr(H) "as" ident(H2) :=
  not assumed H;
  pose proof H as H2.


(* Maximally recursive split *)
Ltac _max_split := try (split; _max_split).
Tactic Notation "max" "split" := _max_split.


(* Copy a hypothesis *)
Tactic Notation "copy" hyp(H) :=
  let H' := fresh H in
  pose proof H as H'.

Tactic Notation "copy" hyp(H) ident(I) := pose proof H as I.


(* Overwrite a hypothesis *)
Ltac overwrite H c := 
  let temp := fresh in
  pose proof c as temp;
  clear H;
  rename temp into H.

Tactic Notation "transform" hyp(H) uconstr(c) :=
  let _temp := fresh in
  assert (_temp : c);
  [|overwrite H _temp; clear _temp].

Tactic Notation "transform" hyp(H) uconstr(c) "by" tactic3(tac) :=
  let _temp := fresh in
  assert (_temp : c);
  [tac|overwrite H _temp; clear _temp].


(* When `unset x` is invoked with hypothesis `x := t` (commonly introduced by 
   tactic `set`), replaces all instances of `x` with `t`, and clears `x`.
 *)
Ltac unset x := unfold x in *; clear x.


(* `todo`: synonymous with `admit` *)
Ltac todo := admit.
(* The follows version would use a specially named unification variable.
   However, it doesn't have the `admit` highlighting, and the unification
   variable is rarely ever seen. *)
(* Ltac todo :=
  match goal with 
  | |- ?goal =>
      let i := fresh "TODO" in
      evar (i : goal);
      exact i
  end. *)


(* Solve a (registered) reflexive relation by proving the arguments equal *)
Ltac reflexive := 
  match goal with 
  | |- _ ?x ?y =>
      replace x with y;
        [ reflexivity
        | try easy; symmetry
        ]
  end.


(* Taken from StructTact 
https://github.com/uwplse/StructTact/blob/a0f4aa3491edf27cf70ea5be3190b7efa8899971/theories/StructTactics.v#L309
 *)
Ltac break_let :=
  match goal with
    | [ H : context [ (let (_,_) := ?X in _) ] |- _ ] => destruct X eqn:?
    | [ |- context [ (let (_,_) := ?X in _) ] ] => destruct X eqn:?
  end.


(* More tactic-equivalents which don't lose term definitions *)

(* Like `assert`, but doesn't hide underlying term *)
Tactic Notation "define" uconstr(c) "as" ident(H) :=
  unshelve evar (H : c).

Tactic Notation "define" uconstr(c) "as" ident(H) "by" tactic3(tac) :=
  define c as H; [solve[tac]|].

Tactic Notation "define" uconstr(c) :=
  let H := fresh in
  define c as H.

Tactic Notation "define" uconstr(c) "by" tactic3(tac) :=
  define c; [solve[tac]|].

Tactic Notation "define" "exists" :=
  unshelve eexists.

Tactic Notation "define" "exists" "by" tactic3(tac) :=
  define exists; [solve[tac]|].


(* `forward` conducts forward reasoning on a hypothesis. It provides a subgoal whose 
   definition will be used to specialize the hypothesis.
 *)

Tactic Notation "forward" hyp(H):=
  match type of H with 
  | forall i: ?x, _ =>
      let var := fresh i in 
      define x as var;
      [|specialize (H var); 
        unfold var in H;
        clear var
      ]
  end.

(* `oforward` (short for "opaque forward") is will obscure the new term's definition *)
Tactic Notation "oforward" hyp(H):=
  match type of H with 
  | forall i: ?x, _ =>
      let var := fresh i in 
      assert x as var;
      [|specialize (H var); 
        try clear var]
  end.


Tactic Notation "forward" hyp(H) "by" tactic3(tac) :=
  forward H; [solve [tac]|].

Tactic Notation "oforward" hyp(H) "by" tactic3(tac) :=
  oforward H; [solve [tac]|].


(* "max" variant of `forward`. Invokes forward on each assumption of a chained implication *)

Ltac _max_forward H := try (forward H; [|_max_forward H]).
Tactic Notation "max" "forward" hyp(H) := _max_forward H.

Ltac _max_forward_by H tac := try (forward H by tac; [|_max_forward_by H tac]).
Tactic Notation "max" "forward" hyp(H) "by" tactic3(tac) := _max_forward_by H tac.


(* Specialize hypothesis with a unification variable *)
(* Ltac especialize H := 
  match type of H with 
  | forall x : ?T, _ => 
      let x' := fresh x in
      evar (x': T);
      specialize (H x');
      unfold x' in H;
      clear x'
  end. *)
Ltac especialize H := forward H by shelve.

(* Like especialize, but doesn't lose term definitions *)
Ltac especialize_term H :=
  match type of H with 
  | forall x : ?T, _ => 
      let x' := fresh x in
      evar (x': T);
      let _temp := fresh in 
      epose (_temp := H x');
      unfold x' in _temp; clear x';
      unfold H in _temp; clear H;
      rename _temp into H
  end.


(* Tactic variants which preserved transparent definitions *)
  
Ltac specialize_term H x :=
  let _temp := fresh in 
  epose (_temp := H x);
  unfold H in _temp;
  clear H;
  rename _temp into H.

Tactic Notation "overwrite_term" hyp(H) uconstr(c) :=
  let _temp := fresh in
  epose (_temp := c);
  unfold H in _temp;
  clear H;
  rename _temp into H.

(* Note, this is vastly less powerful than `apply` *)
Tactic Notation "apply_term" uconstr(c) "in" hyp(H) :=
  let _temp := fresh in 
  epose (_temp := c);
  repeat (overwrite_term H (_temp H) + especialize_term _temp);
  unfold _temp in H;
  clear _temp.

(* This will replace the local definition with an equality *)
Tactic Notation "destruct_term" hyp(H)
  "as" simple_intropattern(pat) "eqn" ":" ident(i) :=
  let _temp := fresh in 
  rename H into _temp;
  destruct _temp as pat eqn:i;
  unfold _temp in i;
  clear _temp.

Tactic Notation "destruct_term" hyp(H) "eqn" ":" ident(i) :=
  let _temp := fresh in 
  rename H into _temp;
  destruct _temp eqn:i;
  unfold _temp in i;
  clear _temp.


(* repeat one or more times *)
Tactic Notation "repeat+" tactic(tac) :=
  tac; repeat tac.


(* Find a hypothesis to apply the tactic to. Fails on non-progress. *)
Tactic Notation "find" tactic3(tac) :=
  match goal with 
  | H : _ |- _ => progress tac H
  end.

Tactic Notation "find" "apply" :=
  find (fun H => apply H).
Tactic Notation "find" "applyc" :=
  find (fun H => applyc H).

Tactic Notation "find" "eapply" :=
  find (fun H => eapply H).
Tactic Notation "find" "eapplyc" :=
  find (fun H => eapplyc H).

Tactic Notation "find" "inversion" :=
  find (fun H => inversion H).

Tactic Notation "find" "rewrite" "->" :=
  find (fun H => rewrite -> H).
Tactic Notation "find" "rewrite" "->" uconstr(u) "in" :=
  find (fun H => rewrite -> u in H).

Tactic Notation "find" "rewrite" "<-" :=
  find (fun H => rewrite <- H).
Tactic Notation "find" "rewrite" "<-" uconstr(u) "in" :=
  find (fun H => rewrite <- u in H).

Tactic Notation "find" "rewrite" :=
  find rewrite -> + find rewrite <-.
Tactic Notation "find" "rewrite" uconstr(u) "in" :=
  find rewrite -> u in + find rewrite <- u in.

Tactic Notation "find" "specialize" uconstr(u1) :=
  find (fun H => specialize (H u1)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) :=
  find (fun H => specialize (H u1 u2)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) uconstr(u3) :=
  find (fun H => specialize (H u1 u2 u3)).
Tactic Notation "find" "specialize" uconstr(u1) uconstr(u2) uconstr(u3) uconstr(u4) :=
  find (fun H => specialize (H u1 u2 u3 u4)).

(* Like assumption, but instead of finding a hypothesis to solve by exact, it 
   finds one to solve by `apply`
 *)
Tactic Notation "assumption!" :=
  solve [find apply].


(* goal is a *value* tactic *)
Ltac goal := 
  match goal with 
  | |- ?goal => goal
  end.
 

(* `guard_negation tac` fails if `tac` solves the goal's negations.

   This is especially useful for deep proof search. Before attempting 
   a rigorous search for a proof, we may attempt a cursory search for 
   its negation. If we think the environment is non-contradictory, then 
   we can backtrack early.
*)

Tactic Notation "guard_negation" tactic3(tac) :=
  let g := goal in
  if (assert (~ g) by tac) then 
    fail "Found proof of negation"
  else 
    idtac.


(* `negative_search` first tries to close the goal by proving False.
   If it can't, it assumes the assumptions to be consistents and 
   guards against the goal's negation
*)
Tactic Notation "negative_search" tactic3(tac) :=
  try (exfalso; solve[tac]);
  guard_negation tac.


(* `tedious`/`follows` are more powerful alternatives to `easy`/`now`. *)

(* Induction failure occasionally produces odd warnings:
     https://github.com/coq/coq/issues/10766
   We silence these warnings with the following setting.
 *)
Global Set Warnings "-cannot-remove-as-expected".

Ltac _etedious n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (eauto; easy) +
      (constructor; _etedious n') +
      (econstructor; _etedious n') +
      (* ((find (fun H => injection H + induction H + destruct H)); _etedious n') + *)
      (find (fun H => first[injection H| induction H| destruct H]); _etedious n') +
      (fail 1 "Cannot solve goal")
    )
  end.

Ltac _tedious n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      (auto; easy) +
      (constructor; _tedious n') +
      (econstructor; _etedious n') +
      (* ((find (fun H => injection H + induction H + destruct H)); _tedious n') + *)
      (find (fun H => first[injection H| induction H| destruct H]); _tedious n') +
      (fail 1 "Cannot solve goal")
    )
  end.

(* Slows exponentially with gas. Wouldn't suggest higher than 10. *)
Tactic Notation "tedious" constr(n) :=
  if has_evar goal then 
    _etedious n
  else 
    _tedious n.

Tactic Notation "tedious" :=
  tedious 5.

Tactic Notation "follows" tactic3(tac) :=
  tac; tedious.

Tactic Notation "after" tactic3(tac) :=
  tac; try tedious.

Tactic Notation "tedious" "using" constr(lemmas) :=
  follows (foreach lemmas (fun H => epose proof H)).
  

(* `force` (short for "brute force") is similar to `tedious`, but sacrifices 
   performance for deeper search.
 *)

Ltac _force n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' => intros; (
      solve[eauto] +
      intuition ((auto with * + eauto with *); easy) +
      (constructor; _force n') +
      (econstructor; _force n') +
      ((find (fun H => injection H + induction H + destruct H)); _force n') +
      (fail 1 "Cannot solve goal")
    )
  end.

Tactic Notation "force" constr(n) :=
  _force n.

Tactic Notation "force" :=
  force 5.


(* `squash` is intended to be a smarter version of force which may heurisitcally
   abandon a path early if the goal is obviously false and the assumptions appear
   non-contradictory.

   In fact, in testing, it appears to generally be slower than `force` in pratical 
   usage. It seems that automatically generated subgoals are very rarely "obviously 
   false", and so we in fact end up wasting time looking for such cases.
*)

Ltac _squash n := 
  match n with 
  | 0 => fail 1 "Ran out of gas"
  | S ?n' =>
      (* intros; negative_search (tedious n'); ( *)
      intros; negative_search (auto n'); (
        solve[intuition (auto with *; easy)] +
        solve[intuition (eauto with *; easy)] +
        (constructor; _force n') +
        (econstructor; _force n') +
        ((find (fun H => injection H + induction H + destruct H)); _force n') +
        (fail 1 "Cannot solve goal")
      )
  end.

Tactic Notation "squash" constr(n) :=
  _squash n.

Tactic Notation "squash" :=
  squash 5.


(* Check that a tactic succeeds, but don't perform its effects *)
Ltac possible tac :=
  (assert_fails tac; gfail 1 "tactic doesn't succeed") || idtac.


(* Improved substitution *)

Definition get_instance {A} (class: A -> Type) (a: A) {instance: class a}
  : class a := instance.

Ltac infer_instance := refine (get_instance _ _).

(* Note, this fails if it cannot resolve *all* implicits. *)
Tactic Notation "has_instance" uconstr(class) uconstr(a) :=
  let _ := constr:(get_instance  class a) in true.

Tactic Notation "setoid_subst" hyp(H) :=
  match type of H with 
  | ?R ?A ?x ?y =>
      has_instance RewriteRelation (R A);
      ( is_var x;
        try rewrite H in *;
        clear H x
      ) + (
        is_var y;
        try rewrite <- H in *;
        clear H y
      )
  | ?R ?x ?y =>
      has_instance RewriteRelation R;
      ( is_var x;
        try rewrite H in *;
        clear H x
      ) + (
        is_var y;
        try rewrite <- H in *;
        clear H y
      )
  end.

Tactic Notation "setoid_subst" :=
  repeat find (fun H => setoid_subst H).

Ltac clear_reflexives :=
  repeat match goal with 
  | H : ?R ?A ?x ?x |- _ =>
      has_instance Reflexive (R A);
      clear H
  | H : ?R ?x ?x |- _ =>
      has_instance Reflexive R;
      clear H
  end.

Ltac clear_redundant := 
  repeat match goal with 
  | H : ?x, H' : ?x |- _ => 
      match type of x with 
      | Prop => clear H' + clear H
      end
  end.

Tactic Notation "setoid_subst!" :=
  repeat progress (subst || setoid_subst);
  clear_reflexives;
  clear_redundant.

Tactic Notation "subst!" :=
  try subst;
  repeat match goal with 
  | H : ?x = ?x |- _ => clear H
  end;
  clear_redundant.


(* Improved inversion *)

Tactic Notation "inv" hyp(H) :=
  inversion H;
  subst!.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(pat) :=
  inversion H as pat;
  subst!.

Tactic Notation "invc" hyp(H) :=
  (* Rename H first to free identifier *)
  let _temp := fresh "_temp" in
  rename H into _temp;
  inv _temp;
  (* Some inversions will clear the hypothesis automatically
     (notably inversions on equalities), so we should only `try`
     to clear it. *)
  try clear _temp.

Tactic Notation "invc" hyp(H) "as" simple_intropattern(pat) :=
  let _temp := fresh in 
  rename H into _temp;
  inv _temp as pat;
  try clear _temp.


Tactic Notation "dependent" "destruction" uconstr(c) :=
  fail "To use dependent destruction, first [Require Import Coq.Program.Equality]".


(* eta reduction / expansion *)

Tactic Notation "eta" :=
  change (?? x, ?f x) with f.

Tactic Notation "eta" "in" hyp(H) :=
  change (?? x, ?f x) with f in H.

Tactic Notation "eta" "in" "*" :=
  change (?? x, ?f x) with f in *.

Tactic Notation "eta_expand" uconstr(f) :=
  change f with (?? x, f x).

Tactic Notation "eta_expand" uconstr(f) "in" hyp(H) :=
  change f with (?? x, f x) in H.

Tactic Notation "eta_expand" uconstr(f) "in" "*" :=
  change f with (?? x, f x) in *.


Ltac is_proof_term p :=
  not is_var p;
  match type of p with
  | ?P => match type of P with 
          | Prop => true
          end
  end.

Tactic Notation "hide_proof_terms" := 
  repeat match goal with 
  | |- context[?p] =>
      is_proof_term p;
      let ident := fresh "p" in
      set (ident := p);
      clearbody ident
  end.

Tactic Notation "hide_proof_terms" "in" hyp(H) := 
  repeat match type of H with 
  | context[?p] =>
      is_proof_term p;
      let ident := fresh "p" in
      set (ident := p) in H;
      clearbody ident
  end.

Tactic Notation "hide_proof_terms" "in" "*" := 
  hide_proof_terms;
  find (fun H => hide_proof_terms in H).


Ltac revert_all_except ls :=
  repeat find (fun H =>
    not (`in_list H ls);
    revert H
  ).

Ltac revert_all :=
  revert_all_except hnil.

Tactic Notation "do_generalized" constr(ls) tactic3(tac) :=
  repeat_count (
    find (fun H =>
      not (`in_list H ls);
      revert H
  )) (fun n => 
    tac;
    do_g n intro
  ).


(* An inverse of `f_equal`. Transforms a hypothesis of type `?f ?a <> ?f ?b`
   to `a <> b`, and recurses.*)
Ltac f_nequal H := 
  match type of H with 
  | ?f ?a <> ?f ?b =>
      simple apply (?? H: f a <> f b,
        (?? Heq: a = b, H (f_equal f Heq)): a <> b)
      in H;
      try f_nequal H
  end.

(* Like `f_nequal`, but potentially unifies functions *)
Ltac ef_nequal H := 
  match type of H with 
  | ?f ?a <> ?f ?b =>
      simple apply (?? H: f a <> f b,
        (?? Heq: a = b, H (f_equal f Heq)): a <> b)
      in H;
      try ef_nequal H
  | ?f ?a <> ?g ?b =>
      unify f g;
      ef_nequal H
  end.
