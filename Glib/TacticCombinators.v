Require Import Coq.Lists.List.
Import ListNotations.


(* Control flow tactics

   These tactics are largely *experimental*.
*)

(* Ltac's execution semantics can be unclear. Sometimes, an ltac expression
   being passed to a higher-order combinator isn't delayed as expected.
   This `quote` tactic, although just the identity, seems to delay
   execution in such cases.
 *)
Tactic Notation "quote" tactic(tac) := tac.
Tactic Notation "`" tactic(tac) := tac.


Ltac true := idtac.
Ltac false := fail.

Tactic Notation "not" tactic3(tac) :=
  assert_fails tac.

Tactic Notation "both" tactic3(tac1) "and" tactic3(tac2) :=
  tac1; tac2.

Tactic Notation "either" tactic3(tac1) "or" tactic3(tac2) :=
  tac1 + tac2.

(* Note: the semantics of `if` seems to meaningfully diverge from `tryif`.
   For instance, see `HList_minus`
 *)
Tactic Notation "if" tactic3(tCond) "then" tactic3(tThen) "else" tactic3(tElse) :=
  tryif tCond then tThen else tElse.

Tactic Notation "while" tactic3(tCond) tactic3(tDo) :=
  repeat (tCond; tDo).


(* `repeat_count` behaves like `repeat`, but it counts the number of 
  iterations, which it passes to a continuation.
 *)

Ltac _repeat_count tac cont n :=
  if tac then 
    _repeat_count tac cont (S n)
  else 
    cont n.

Tactic Notation "repeat_count" tactic3(tac) tactic3(cont) := 
  _repeat_count tac cont 0.


(* `do_g` is `do`, but with Gallina naturals *)
Ltac _do_g n tac :=
  match n with 
  | S ?n' => tac; _do_g n' tac
  | 0 => idtac 
  end.
Tactic Notation "do_g" constr(n) tactic3(tac) :=
  _do_g n tac.


(* `do_upto` is a mix of repeat and do. It perform up to n repetitions. *)
Ltac _do_upto n tac :=
  try match n with 
  | S ?n' => tac; _do_upto n' tac
  | 0 => idtac 
  end.
Tactic Notation "do_upto" constr(n) tactic3(tac) :=
  _do_upto n tac.


(* Because of the dynamicness of Ltac, it is more convenient to use list-like
   tuples as opposed to proper Gallina lists. The convention for tactics over 
   lists is to treat the pair (x, y) as a head element x and a tail list y.
   Anything else is treated as the empty list. Typically, the Prop False is 
   provided to represent the empty list.
 *)

Notation "?[ ]" := False
  (format "?[ ]").
Notation "?[ x ]" := (pair x False)
  (format "?[ x ]").
Notation "?[ x ; y ; .. ; z ]" := (pair x (pair y .. (pair z False) ..))
  (format "?[ x ;  y ;  .. ;  z ]").

Ltac _foreach ls ftac :=
  match ls with 
  | (?H, ?ls') =>
      first [ftac H| fail 1 ftac "failed on" H]; 
      _foreach ls' ftac
  | _ => idtac
  end.
Tactic Notation "foreach" constr(ls) tactic3(ftac) :=
  _foreach ls ftac.

Ltac _forsome ls ftac :=
  match ls with 
  | (?H, ?ls') =>
      ftac H + _forsome ls' ftac
  | _ => fail 1 ftac "failed on every hypothesis"
  end.
Tactic Notation "forsome" constr(ls) tactic3(ftac) :=
  _forsome ls ftac.

(* Tests for syntactic equality (stricter than convertibility) *)
Ltac syn_eq H H' :=
  match H with 
  | H' => true
  end.

Ltac in_list H ls := forsome ls (syn_eq H).

Ltac _list_minus ls1 ls2 keep cont :=
  match ls1 with
  | (?h, ?t) => 
      tryif in_list h ls2 then 
        _list_minus t ls2 keep cont
      else 
        _list_minus t ls2 (h, keep) cont
  | _ => cont keep
  end.
Tactic Notation "list_minus" constr(ls1) constr(ls2) tactic3(cont) :=
  _list_minus ls1 ls2 False cont.

(* passes a list of the current hypotheses to the continuation *)
Ltac _env ls cont :=
  match goal with
  | H : _ |- _ =>
      not (in_list H ls);
      _env (H, ls) cont
  end + (cont ls).
Tactic Notation "env" tactic3(cont) :=
  _env False cont.

(* passes a list of the new hypotheses to the continuation after running `tac` *)
Tactic Notation "env_delta" tactic3(tac) tactic3(cont) :=
  env (fun old =>
  tac;
  env (fun new =>
  list_minus new old cont
  )).
