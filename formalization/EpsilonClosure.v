(************************************************************)
(* Epsilon-NFAs, epsilon-closure and determinization.      *)
(************************************************************)

From PowersetProject Require Import AutomataBase.
From PowersetProject Require Import AutomataSemantics.

(* Epsilon NFAs and epsilon-closure                         *)
(************************************************************)

(*
  The main development above treats NFAs without epsilon transitions.
  This section records the standard extension: an epsilon-NFA may also
  move without consuming an input symbol.  In Coq, I represent labels by
  option Symbol:

      None      means an epsilon transition
      Some a    means a normal transition on symbol a

  The key extra operation is epsilon_closure.  Starting from a set of
  states X, epsilon_closure X adds all states reachable from X by zero
  or more epsilon transitions.

  Because State is a FiniteType, a simple bounded iteration is enough for
  an executable closure operation: after at most length finite_list many
  rounds, every reachable state has had enough chances to be added.

  The determinized DFA uses the usual rule:

      delta_D(X, a) = epsilon_closure(move(epsilon_closure(X), a))

  In words: close under epsilon, take one real input-symbol step, and
  close under epsilon again.
*)

Record ENFA (State Symbol : Type) := {
  enfa_start : State;
  enfa_final : State -> bool;
  enfa_trans : State -> option Symbol -> set State
}.

Section EpsilonPowersetConstruction.

Variable State : FiniteType.
Variable Symbol : Type.
Variable E : ENFA State Symbol.

Definition EDState : Type := State -> bool.

Definition esingleton_subset (s0 : State) : EDState :=
  fun s =>
    match finite_eq_dec State s s0 with
    | left _ => true
    | right _ => false
    end.

Definition elist_to_subset (xs : set State) : EDState :=
  fun s => set_mem (finite_eq_dec State) s xs.

Fixpoint esubset_to_list_aux
  (X : EDState) (xs : list State) : set State :=
  match xs with
  | [] => []
  | x :: xs' =>
      if X x
      then x :: esubset_to_list_aux X xs'
      else esubset_to_list_aux X xs'
  end.

Definition esubset_to_list (X : EDState) : set State :=
  esubset_to_list_aux X (finite_list State).

(* Union of all transitions with the same label from a list of states. *)
Fixpoint enfa_step_set
  (X : set State) (label : option Symbol) : set State :=
  match X with
  | [] => []
  | q :: X' =>
      set_union (finite_eq_dec State)
        (enfa_trans State Symbol E q label)
        (enfa_step_set X' label)
  end.

Definition epsilon_step_set (X : set State) : set State :=
  enfa_step_set X None.

(* One closure round keeps the old states and adds one epsilon step. *)
Definition epsilon_closure_round (X : set State) : set State :=
  set_union (finite_eq_dec State) X (epsilon_step_set X).

Fixpoint epsilon_closure_steps
  (n : nat) (X : set State) : set State :=
  match n with
  | O => X
  | S n' => epsilon_closure_steps n' (epsilon_closure_round X)
  end.

(* Executable epsilon-closure by bounded iteration over the finite state
   space.  This is the operation used by the determinization below. *)
Definition epsilon_closure_set (X : set State) : set State :=
  epsilon_closure_steps (length (finite_list State)) X.

Definition epsilon_closure_subset (X : EDState) : EDState :=
  elist_to_subset (epsilon_closure_set (esubset_to_list X)).

(* Move by one real input symbol from a subset. *)
Definition enfa_move_subset (X : EDState) (a : Symbol) : EDState :=
  fun s' =>
    existsb
      (fun s =>
         X s &&
         set_mem (finite_eq_dec State)
           s'
           (enfa_trans State Symbol E s (Some a)))
      (finite_list State).

(* The epsilon-aware deterministic step. *)
Definition enfa_step_subset (X : EDState) (a : Symbol) : EDState :=
  epsilon_closure_subset
    (enfa_move_subset (epsilon_closure_subset X) a).

Definition enfa_start_subset : EDState :=
  epsilon_closure_subset (esingleton_subset (enfa_start State Symbol E)).

Definition enfa_final_subset (X : EDState) : bool :=
  existsb
    (fun s => X s && enfa_final State Symbol E s)
    (finite_list State).

Fixpoint enfa_run_subset (X : EDState) (w : word Symbol) : EDState :=
  match w with
  | [] => X
  | a :: w' => enfa_run_subset (enfa_step_subset X a) w'
  end.

Definition enfa_accept_subset (w : word Symbol) : Prop :=
  exists s : State,
    enfa_run_subset enfa_start_subset w s = true /\
    enfa_final State Symbol E s = true.

Definition enfa_lang_subset : lang Symbol := enfa_accept_subset.

Definition enfa_to_dfa : DFA EDState Symbol := {|
  dfa_start := enfa_start_subset;
  dfa_final := enfa_final_subset;
  dfa_trans := enfa_step_subset
|}.

Lemma enfa_run_to_dfa_run_correct :
  forall (w : word Symbol) (X : EDState),
    dfa_run EDState Symbol enfa_to_dfa X w = enfa_run_subset X w.
Proof.
  induction w as [|a w' IHw].
  - intros X. simpl. reflexivity.
  - intros X. simpl. apply IHw.
Qed.

Theorem enfa_to_dfa_correct :
  forall w : word Symbol,
    enfa_lang_subset w <->
    dfa_lang EDState Symbol enfa_to_dfa w.
Proof.
  intro w.
  unfold enfa_lang_subset, dfa_lang.
  unfold enfa_accept_subset, dfa_accept, dfa_accept_from.
  simpl.
  rewrite (enfa_run_to_dfa_run_correct w enfa_start_subset).
  unfold enfa_final_subset.
  split.
  - intros [s [Hs_run Hs_final]].
    apply existsb_exists.
    exists s.
    split.
    + apply finite_cover.
    + apply andb_true_iff.
      split; assumption.
  - intro H.
    apply existsb_exists in H.
    destruct H as [s [_ Hs]].
    apply andb_true_iff in Hs.
    destruct Hs as [Hs_run Hs_final].
    exists s.
    split; assumption.
Qed.

End EpsilonPowersetConstruction.
