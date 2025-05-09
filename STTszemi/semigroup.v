Class Semigroup (A : Type) : Type :=
  mk_semigroup {
    op : A -> A -> A;
    assoc : forall x y z : A, op x (op y z) = op (op x y) z
  }.

Class UnSem (A : Type) (S : Semigroup A) : Type :=
  mk_UnSem {
    e_l : A;
    e_r: A;
    left_id_ax : forall x : A, op e_l x = x;
    right_id_ax : forall x : A, op x e_r = x
  }.

Require Import Coq.Arith.Arith.
Require Import Coq.Init.Nat.


Instance nat_semigroup : Semigroup nat. 
Proof.
  apply mk_semigroup with (op:=add).
  apply Nat.add_assoc.
Defined. 

Print Nat.add_0_l.

Instance nat_unsem : UnSem nat nat_semigroup :=
  mk_UnSem nat nat_semigroup 0 0
  Nat.add_0_l
  Nat.add_0_r.

Theorem egyegységelem (A : Type) (S : Semigroup A) (U : UnSem A S) : e_l = e_r. 
Proof.
rewrite <- (right_id_ax e_l).
rewrite left_id_ax.
assert (K : op e_l e_r = e_r).
apply left_id_ax.
assert (L : op e_l e_r = e_l).
apply right_id_ax.
congruence.
Defined.


