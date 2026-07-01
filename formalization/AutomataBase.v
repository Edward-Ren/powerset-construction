(************************************************************)
(* Basic definitions for the whole project                  *)
(************************************************************)
From Coq Require Export Lists.List.
From Coq Require Export Lists.ListSet.

(* 
In order to make definitions generic, 
DFA and NFA are parameterized by State and Symbol.
In the powerset construction, the state type changes from 
State to State -> bool, while keeping the same symbol type.
*)
Definition word (Symbol : Type) := list Symbol.

Definition lang (Symbol : Type) := word Symbol -> Prop.

Record DFA (State Symbol : Type) := {
  dfa_start : State;
  dfa_final : State -> bool;
  dfa_trans : State -> Symbol -> State
}.

Record NFA (State Symbol : Type) := {
  nfa_start : State;
  nfa_final : State -> bool;
  nfa_trans : State -> Symbol -> set State
}.

(*
I package finiteness as a record. A FiniteType is not only a type,
but also carries some data and proofs.
The field finite_type uses ":>", so Rocq can automatically treat a
FiniteType as a Type when needed. Thus, if State : FiniteType, I can
still write State -> bool.  At the same time, I can use finite_list
State and finite_eq_dec State later in the construction.
*)
Record FiniteType := {
  finite_type :> Type;
  finite_list : list finite_type;
  finite_cover : forall x : finite_type, In x finite_list;
  finite_nodup : NoDup finite_list;
  finite_eq_dec : forall x y : finite_type, {x = y} + {x <> y}
}.
