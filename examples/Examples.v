(************************************************************)
(* Small executable examples for the project.           *)
(************************************************************)
From Coq Require Import Lists.List.
From Coq Require Import Lists.ListSet.
Import ListNotations.

From PowersetProject Require Import AutomataBase.
From PowersetProject Require Import AutomataSemantics.
From PowersetProject Require Import PowersetConstruction.
From PowersetProject Require Import Finiteness.
From PowersetProject Require Import EpsilonClosure.

Module SmallExample.

Inductive ExState : Type :=
| q0
| q1.

Definition ExState_eq_dec :
  forall x y : ExState, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition ExState_finite_list : list ExState := [q0; q1].

Lemma ExState_cover :
  forall x : ExState, In x ExState_finite_list.
Proof.
  intro x.
  destruct x; simpl; auto.
Qed.

Lemma ExState_nodup :
  NoDup ExState_finite_list.
Proof.
  unfold ExState_finite_list.
  constructor.
  - simpl.
    intros H.
    destruct H as [H | H].
    + discriminate H.
    + contradiction.
  - constructor.
    + simpl.
      intros H.
      contradiction.
    + constructor.
Qed.

Definition ExFinite : FiniteType := {|
  finite_type := ExState;
  finite_list := ExState_finite_list;
  finite_cover := ExState_cover;
  finite_nodup := ExState_nodup;
  finite_eq_dec := ExState_eq_dec
|}.

Inductive ExSymbol : Type :=
| a
| b.

Definition ex_trans (q : ExState) (x : ExSymbol) : set ExState :=
  match q, x with
  | q0, a => [q0; q1]
  | q0, b => [q0]
  | q1, a => []
  | q1, b => [q1]
  end.

Definition ex_nfa : NFA ExFinite ExSymbol := {|
  nfa_start := q0;
  nfa_final := fun q =>
    match q with
    | q0 => false
    | q1 => true
    end;
  nfa_trans := ex_trans
|}.

Example ex_nfa_accepts_a :
  nfa_lang_subset ExFinite ExSymbol ex_nfa [a].
Proof.
  unfold nfa_lang_subset, nfa_accept_subset.
  exists q1.
  simpl.
  split; reflexivity.
Qed.

Example ex_dfa_accepts_a :
  dfa_lang
    (DState ExFinite)
    ExSymbol
    (nfa_to_dfa ExFinite ExSymbol ex_nfa)
    [a].
Proof.
  apply (proj1 (nfa_to_dfa_correct ExFinite ExSymbol ex_nfa [a])).
  apply ex_nfa_accepts_a.
Qed.

End SmallExample.

(************************************************************)
(* Small executable epsilon example                         *)
(************************************************************)

Module SmallEpsilonExample.

Inductive EState : Type :=
| e0
| e1
| e2.

Definition EState_eq_dec :
  forall x y : EState, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition EState_finite_list : list EState := [e0; e1; e2].

Lemma EState_cover :
  forall x : EState, In x EState_finite_list.
Proof.
  intro x.
  destruct x; simpl; auto.
Qed.

Lemma EState_nodup :
  NoDup EState_finite_list.
Proof.
  unfold EState_finite_list.
  constructor.
  - simpl.
    intros [H | [H | []]]; discriminate H.
  - constructor.
    + simpl.
      intros [H | []]; discriminate H.
    + constructor.
      * simpl. intros [].
      * constructor.
Qed.

Definition EFinite : FiniteType := {|
  finite_type := EState;
  finite_list := EState_finite_list;
  finite_cover := EState_cover;
  finite_nodup := EState_nodup;
  finite_eq_dec := EState_eq_dec
|}.

Inductive ESymbol : Type :=
| ea.

(* e0 --epsilon--> e1 --a--> e2, and e2 is final. *)
Definition eps_trans
  (q : EState) (label : option ESymbol) : set EState :=
  match q, label with
  | e0, None => [e1]
  | e1, Some ea => [e2]
  | _, _ => []
  end.

Definition eps_enfa : ENFA EFinite ESymbol := {|
  enfa_start := e0;
  enfa_final := fun q =>
    match q with
    | e2 => true
    | _ => false
    end;
  enfa_trans := eps_trans
|}.

Example eps_closure_reaches_e1 :
  epsilon_closure_subset
    EFinite ESymbol eps_enfa
    (esingleton_subset EFinite e0)
    e1 = true.
Proof.
  simpl. reflexivity.
Qed.

Example eps_enfa_accepts_a :
  enfa_lang_subset EFinite ESymbol eps_enfa [ea].
Proof.
  unfold enfa_lang_subset, enfa_accept_subset.
  exists e2.
  simpl.
  split; reflexivity.
Qed.

Example eps_dfa_accepts_a :
  dfa_lang
    (EDState EFinite)
    ESymbol
    (enfa_to_dfa EFinite ESymbol eps_enfa)
    [ea].
Proof.
  apply (proj1 (enfa_to_dfa_correct EFinite ESymbol eps_enfa [ea])).
  apply eps_enfa_accepts_a.
Qed.

End SmallEpsilonExample.
