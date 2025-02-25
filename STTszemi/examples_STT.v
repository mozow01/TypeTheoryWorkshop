Require Import List.
Require Import Arith Peano.
Import ListNotations.

Fixpoint length {A : Type} (l : list A) : nat :=
  match l with
  | [] => 0
  | a :: t => 1 + length t
  end.

Lemma length_cons : forall (A : Type) (x : A) (l : list A),
  length (x :: l) = 1 + length l.
Proof.
  intuition.
  Show Proof.
Qed.

Definition dep : forall (b : bool), if b then bool else nat := 
fun (b : bool) =>
  match b with
  | true => true
  | false => 2
  end.

Inductive nList (A : Type) : nat -> Type :=
  | nNil : nList A 0
  | nCons : forall (n : nat), A -> nList A n -> nList A (S n).

Definition vHead {A : Type} {n : nat} (v : nList A (S n)) : A :=
  match v with
  | nCons _ _ x _ => x
  end.

Definition ex1 : nList nat 2 :=
(nCons nat 1 42 (nCons nat 0 23 (nNil nat))).

Compute vHead ex1. 

Print eq.


