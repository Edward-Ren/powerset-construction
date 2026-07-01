(************************************************************)
(* NFA-to-DFA powerset construction.                        *)
(************************************************************)

From PowersetProject Require Import AutomataBase.
From PowersetProject Require Import AutomataSemantics.

(************************************************************)
(* Powerset construction                                    *)
(************************************************************)

Section PowersetConstruction.

Variable State : FiniteType.
Variable Symbol : Type.
Variable N : NFA State Symbol.

(* A state of the constructed DFA is a subset of NFA states.
   I represent such a subset as its characteristic function:
   X q = true means that q is currently reachable. This avoids
   reasoning about list order and duplicate elements when using
   subsets as DFA states. *)
Definition DState : Type := State -> bool.

Definition singleton_subset (s0 : State) : DState :=
  fun s =>
    match finite_eq_dec State s s0 with
    | left _ => true
    | right _ => false
    end.

Definition nfa_step_subset (X : DState) (a : Symbol) : DState :=
  fun s' =>
    existsb
      (fun s =>
         X s &&
         set_mem (finite_eq_dec State)
           s'
           (nfa_trans State Symbol N s a))
      (finite_list State).

Fixpoint nfa_run_subset (X : DState) (w : word Symbol) : DState :=
  match w with
  | [] => X
  | a :: w' => nfa_run_subset (nfa_step_subset X a) w'
  end.

Definition nfa_accept_subset (w : word Symbol) : Prop :=
  exists s : State,
    nfa_run_subset
      (singleton_subset (nfa_start State Symbol N)) w s = true /\
    nfa_final State Symbol N s = true.

Definition nfa_lang_subset : lang Symbol := nfa_accept_subset.

Definition dfa_start_subset : DState :=
  singleton_subset (nfa_start State Symbol N).

Definition dfa_final_subset (X : DState) : bool :=
  existsb
    (fun s => X s && nfa_final State Symbol N s)
    (finite_list State).

Definition nfa_to_dfa : DFA DState Symbol := {|
  dfa_start := dfa_start_subset;
  dfa_final := dfa_final_subset;
  dfa_trans := nfa_step_subset
|}.

Lemma nfa_run_to_dfa_run_correct :
  forall (w : word Symbol) (X : DState),
    dfa_run DState Symbol nfa_to_dfa X w = nfa_run_subset X w.
Proof.
  induction w as [|a w' IHw].
  - intros X. simpl. reflexivity.
  - intros X. simpl. apply IHw.
Qed.

(* Language preservation for the subset semantics of the NFA. *)
Theorem nfa_to_dfa_correct :
  forall w : word Symbol,
    nfa_lang_subset w <->
    dfa_lang DState Symbol nfa_to_dfa w.
Proof.
  intro w.
  unfold nfa_lang_subset, dfa_lang.
  unfold nfa_accept_subset, dfa_accept, dfa_accept_from.
  simpl.
  rewrite (nfa_run_to_dfa_run_correct w dfa_start_subset).
  unfold dfa_start_subset, dfa_final_subset.
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

End PowersetConstruction.

