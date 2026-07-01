(************************************************************)
(* Run and acceptance semantics for DFAs and NFAs.          *)
(************************************************************)

From PowersetProject Require Import AutomataBase.

(************************************************************)
(* DFA semantics                                            *)
(************************************************************)

Section DFA_Semantics.

Variables (State Symbol : Type).
Variable D : DFA State Symbol.

Fixpoint dfa_run (s : State) (w : word Symbol) : State :=
  match w with
  | [] => s
  | a :: w' =>
      dfa_run (dfa_trans State Symbol D s a) w'
  end.

Definition dfa_accept_from (s : State) (w : word Symbol) : Prop :=
  dfa_final State Symbol D (dfa_run s w) = true.

Definition dfa_accept (w : word Symbol) : Prop :=
  dfa_accept_from (dfa_start State Symbol D) w.

Definition dfa_lang : lang Symbol := dfa_accept.

End DFA_Semantics.

(************************************************************)
(* NFA semantics                                            *)
(************************************************************)

Section NFA_Semantics.

Variables (State Symbol : Type).
Variable N : NFA State Symbol.

(* Decidable equality is needed for ListSet operations such as
   set_union and set_mem. *)
Variable State_eq_dec : forall x y : State, {x = y} + {x <> y}.

Definition singleton (x : State) : set State := [x].

Fixpoint nfa_step_set (X : set State) (a : Symbol) : set State :=
  match X with
  | [] => []
  | q :: X' =>
      set_union State_eq_dec
        (nfa_trans State Symbol N q a)
        (nfa_step_set X' a)
  end.

Fixpoint nfa_run_set (X : set State) (w : word Symbol) : set State :=
  match w with
  | [] => X
  | a :: w' => nfa_run_set (nfa_step_set X a) w'
  end.

Definition nfa_accept (w : word Symbol) : Prop :=
  exists q : State,
    In q (nfa_run_set (singleton (nfa_start State Symbol N)) w) /\
    nfa_final State Symbol N q = true.

Definition nfa_lang : lang Symbol := nfa_accept.

End NFA_Semantics.
