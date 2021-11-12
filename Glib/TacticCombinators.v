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


(* We use arbitrary-length tuples as a sort of heterogeneous list for our 
   tactics. Due to the way pairs associate, `(t, h)` is the "cons" of `h` to `t`.
   The special value `hnil` is introduced to represent an empty heterogeneous list.
   Note that one should not form heterogeneous lists of tuples, as this representation
   would yield ambiguity.
 *)

Inductive Hnil : Set := hnil.

Ltac _foreach ls ftac :=
  lazymatch ls with 
  | hnil => idtac
  | (?ls', ?H) =>
      first [ftac H| fail 0 ftac "failed on" H]; 
      _foreach ls' ftac
  | ?H => first [ftac H| fail 0 ftac "failed on" H]
  end.
Tactic Notation "foreach" constr(ls) tactic3(ftac) :=
  _foreach ls ftac.

Ltac _forsome ls ftac :=
  lazymatch ls with 
  | hnil => fail 0 ftac "failed on every hypothesis"
  | (?ls', ?H) =>
      ftac H + _forsome ls' ftac
  | ?H => ftac H + fail 0 ftac "failed on every hypothesis"
  end.
Tactic Notation "forsome" constr(ls) tactic3(ftac) :=
  _forsome ls ftac.

(* Tests for syntactic equality (stricter than convertibility) *)
Ltac syn_eq H H' :=
  match H with 
  | H' => true
  end.

Ltac in_list H ls := (forsome ls (syn_eq H)) + fail 0 H "not in list".

Ltac _list_minus ls1 ls2 keep cont :=
  lazymatch ls1 with
  | hnil => cont keep
  | (?t, ?h) => 
      tryif in_list h ls2 then 
        _list_minus t ls2 keep cont
      else 
        _list_minus t ls2 (keep, h) cont
  | ?h => 
      tryif in_list h ls2 then 
        cont keep
      else 
        cont (keep, h)
  end.
Tactic Notation "list_minus" constr(ls1) constr(ls2) tactic3(cont) :=
  _list_minus ls1 ls2 hnil cont.

(* passes a list of the current hypotheses to the continuation *)
Ltac _env ls cont :=
  match goal with
  | H : _ |- _ =>
      not (in_list H ls);
      _env (ls, H) cont
  end + (cont ls).
Tactic Notation "env" tactic3(cont) :=
  _env hnil cont.

(* passes a list of the new hypotheses to the continuation after running `tac` *)
Tactic Notation "env_delta" tactic3(tac) tactic3(cont) :=
  env (fun old =>
  tac;
  env (fun new =>
  list_minus new old cont
  )).
