Require Import Coq.Lists.List.
Import ListNotations.

(* TCondL nyelv induktív típus-definíciója *)
Inductive TCondL : Type :=
  | tt : TCondL
  | ff : TCondL
  | var : nat -> TCondL
  | if_then_else : TCondL -> TCondL -> TCondL -> TCondL.

(* Kontextus definíciója *)
Definition context := list nat.

(* Típusolási szabályok *)

Inductive has_type : context -> TCondL -> Prop :=
  | T_True : forall Gamma,
       has_type Gamma tt
  | T_False : forall Gamma,
      has_type Gamma ff
  | T_If : forall Gamma p q r,
      has_type Gamma p ->
      has_type Gamma q ->
      has_type Gamma r ->
      has_type Gamma (if_then_else p q r)
  | T_Context_Head : forall Gamma x,
      has_type (x :: Gamma) (var x)
  | T_Context_Tail : forall Gamma x y,
      has_type Gamma (var x) ->
      has_type (y :: Gamma) (var x).

Notation "Gamma '⊢' t '[: bool]'" := (has_type Gamma t) (at level 40, left associativity).

(* Példák a típusolás használatára *)
Example example1 : [0] ⊢ (var 0) '[: bool]'.
Proof.
  apply T_Context_Head.
Qed.

Example example2 : [1; 0] ⊢ (var 0) '[: bool]'.
Proof.
  apply T_Context_Tail.
  apply T_Context_Head.
Qed.

Example example3 : [] ⊢ tt '[: bool]'.
Proof.
  apply T_True.
Qed.

Example example4 : [0] ⊢ if_then_else (var 0) ff tt '[: bool]'.
Proof.
  apply T_If.
  - apply T_Context_Head.
  - apply T_False.
  - apply T_True.
Qed.

Inductive D_equiv : context -> TCondL -> TCondL -> Prop :=
  | E_Refl : forall Gamma t,
      D_equiv Gamma t t 
  | E_Symm : forall Gamma t s,
      D_equiv Gamma t s ->
      D_equiv Gamma s t
  | E_Trans : forall Gamma t s u,
      D_equiv Gamma t s ->
      D_equiv Gamma s u ->
      D_equiv Gamma t u
  | E_If : forall Gamma p1 p2 q1 q2 r1 r2,
      D_equiv Gamma p1 p2 ->
      D_equiv Gamma q1 q2 ->
      D_equiv Gamma r1 r2 ->
      D_equiv Gamma (if_then_else p1 q1 r1) (if_then_else p2 q2 r2)
  | E_beta_True : forall Gamma p q,
      D_equiv Gamma (if_then_else tt p q) p
  | E_beta_False : forall Gamma p q,
      D_equiv Gamma (if_then_else ff p q) q.

Notation "Gamma '⊢' t '≡' s '[: boole]'" := (D_equiv Gamma t s) (at level 45, left associativity).

Example example_equiv1 : D_equiv [] (if_then_else tt tt ff) tt.
Proof.
  apply E_beta_True.
Qed.


(* Setoidnak nevezünk egy típust és az elemei közötti ekvivalenciarelációt (voltaképpen typeoid) *)
Require Import Coq.Setoids.Setoid.
Add Parametric Relation (Gamma : context) : TCondL (D_equiv Gamma)
  reflexivity proved by (E_Refl Gamma)
  symmetry proved by (E_Symm Gamma)
  transitivity proved by (E_Trans Gamma)
  as D_equiv_rel.

Example example_equiv2 : D_equiv [] (if_then_else tt tt ff) (if_then_else ff ff tt).
Proof.
  rewrite E_beta_True.
  rewrite E_beta_False.
  reflexivity.
Qed.







