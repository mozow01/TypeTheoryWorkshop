Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom; 
  Id : forall x, Hom x x; 
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); 

  (* equivalence *)
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;

  (* equivalence properties *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h 
         -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;

  (* associativity, identity*)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  
  (* congruence *)
  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Notation "f ≡ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.

Require Import List Arith Peano Lia.
Import ListNotations.

(* STT *)

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Arr : Typ -> Typ -> Typ.

Notation "x ⇒ y" := (Arr x y) (at level 90, right associativity) :
type_scope.

Inductive Trm : Set :=
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Arr A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Arr A B) -> Tyty Γ s A -> Tyty Γ (app t s) B.

Notation "G '⊢' t '[:]' A" := (Tyty G t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

(*
Lemma problem_1 : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
Check (q (p x)).
intros A B C p q x.
apply q.
apply p.
apply x.
Show Proof.
Qed.
*)

Lemma problem_2 : forall A B C : Typ, exists (t : Trm), [ Arr A B; Arr B C ] ⊢ t [:] (Arr A C).
Proof.
intros.
(* [ A; Arr A B; Arr B C ] *)
exists (lam A (app (hyp 2) (app (hyp 1) (hyp 0)))).
apply STT_lam.
apply STT_app with (A:=B).
apply STT_hypS.
apply STT_hypS.
apply STT_hypO.
apply STT_app with (A:=A).
apply STT_hypS.
apply STT_hypO.
apply STT_hypO.
Qed.



Definition Obj_STT := Typ.

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (x ⇒ y)}.

Definition Id_STT_term (x : Obj_STT) := (lam x (hyp 0)).

Lemma Id_STT_type (x : Obj_STT) : ⊢ (Id_STT_term x) [:] (x ⇒ x).
Proof.
unfold Id_STT_term.
apply STT_lam.
apply STT_hypO.
Defined.

Definition Id_STT (x : Typ) : {t : Trm | ⊢ t [:] (x ⇒ x)} :=
  exist (fun t => ⊢ t [:] (x ⇒ x)) (Id_STT_term x) (Id_STT_type x).

Lemma weakening_weak : forall Γ Δ t A,
  Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  simpl; auto.
  intros Γ Δ t A H.
  induction H.
  all: try rewrite K; try rewrite <- app_assoc; try rewrite <- K.
  - apply STT_hypO.
  - apply STT_hypS.
    auto.
  - apply STT_lam.
    rewrite K in IHTyty.
    rewrite <- app_assoc in IHTyty.
    rewrite <- K in IHTyty.
    auto.
  - apply STT_app with (A := A).
    all: auto.
Defined.

Definition Compose_STT_term {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) := lam x (app (proj1_sig f) (app (proj1_sig g) (hyp 0))).

Definition Compose_STT_type {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : ⊢ (Compose_STT_term f g) [:] (x ⇒ z).
Proof.
unfold Compose_STT_term.
apply STT_lam.
assert (Kf : ⊢ (proj1_sig f) [:] (y ⇒ z)).
 { exact (proj2_sig f). }
assert (Kg : ⊢ (proj1_sig g) [:] (x ⇒ y)).
 { exact (proj2_sig g). }
assert (Kfx : [x] ⊢ (proj1_sig f) [:] (y ⇒ z)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f); auto. }
assert (Kgx : [x] ⊢ (proj1_sig g) [:] (x ⇒ y)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g); auto. }
apply STT_app with (A:=y). auto.
apply STT_app with (A:=x). auto.
apply STT_hypO.
Defined.

Definition Compose_STT {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : {t : Trm | ⊢ t [:] (x ⇒ z)} :=
  exist (fun t => ⊢ t [:] (x ⇒ z)) (Compose_STT_term f g) (Compose_STT_type f g).

(*weak beta és eta*)
Inductive STT_equiv : Cntxt -> Typ -> Trm -> Trm -> Prop :=
  | E_Refl : forall Γ A t,
      STT_equiv Γ A t t
  | E_Symm : forall Γ A t s,
      STT_equiv Γ A t s ->
      STT_equiv Γ A s t
  | E_Trans : forall Γ A t s u,
      STT_equiv Γ A t s ->
      STT_equiv Γ A s u ->
      STT_equiv Γ A t u
  | E_app : forall Γ A p1 p2 q1 q2,
      STT_equiv Γ A p1 p2 ->
      STT_equiv Γ A q1 q2 ->
      STT_equiv Γ A (app p1 q1) (app p2 q2)
  | E_lam : forall Γ p1 p2 A B C,
      STT_equiv Γ A p1 p2 -> 
      STT_equiv Γ C (lam B p1) (lam B p2) 
  | E_beta : forall Γ A B,
      STT_equiv Γ B (app (lam A (hyp 0)) (hyp 0)) (hyp 0)
  | E_eta : forall Γ t A B,
      STT_equiv Γ B (lam A (app t (hyp 0))) t.

Notation "Γ '⊢' t '≡' s '[:]' A" := (STT_equiv Γ A t s) (at level 45, left associativity).

(* Setoidnak nevezünk egy típust és az elemei közötti ekvivalenciarelációt (voltaképpen typeoid) *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma STT_equiv_Transitive : forall Γ A t s u,
  STT_equiv Γ A t s -> STT_equiv Γ A s u -> STT_equiv Γ A t u.
Proof.
  intros Γ A t s u H1 H2.
  apply E_Trans with (s := s); assumption.
Qed.

Add Parametric Relation (Γ : Cntxt) (A : Typ) : Trm (STT_equiv Γ A)
  reflexivity proved by (E_Refl Γ A)
  symmetry proved by (E_Symm Γ A)
  transitivity proved by (STT_equiv_Transitive Γ A)
  as STT_equiv_rel.

Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := STT_equiv nil x (proj1_sig f) (proj1_sig g).

Lemma id_1_STT : forall x y (f : (Hom_STT x y)), EqMor_STT (Compose_STT f (Id_STT x)) f.
Proof.
intros.
unfold EqMor_STT.
unfold Compose_STT.
simpl.
unfold Compose_STT_term.
unfold Id_STT.
simpl.
unfold Id_STT_term.
(* itt rewrite sajnos nem működik, ezért kézzel kell az egyenlőséget igazolni, de a setoid reláció hozzáadása miatt működik a 

reflexivity, 

symmetry, 

transitivity, 

és 

ha már vannak egyenlőségek a feltételek között, akkor adott H egyenlőségfeltétel estén a rewrite H

*)
assert (K1 : STT_equiv nil x
(app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0))) (app (proj1_sig f) (hyp 0))).
 { apply E_app.
   reflexivity.
   apply E_beta. }
assert (K2 : STT_equiv nil x (lam x
    (app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0)))) (lam x
    (app (proj1_sig f) (hyp 0)))).
 { apply E_lam with (A:=x).
   apply K1. }
rewrite K2.
apply E_eta.
Defined.

(* 
emlékeztető:
Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := STT_equiv nil x (proj1_sig f) (proj1_sig g).

*)


Lemma EqMor_STT_ref : forall {x y} (f : Hom_STT x y), EqMor_STT f f.
Proof.
intros.
unfold EqMor_STT.
apply E_Refl.
Qed.

Lemma EqMor_STT_sym : forall {x y} (f g : Hom_STT x y), EqMor_STT f g -> EqMor_STT g f.
Proof.
(*
intros x y f g H.
unfold EqMor_STT in *.
symmetry.
exact H.
*)
intros.
unfold EqMor_STT.
apply E_Symm.
assumption.
Qed.

Lemma EqMor_STT_trans : forall {x y} (f g h : Hom_STT x y), EqMor_STT f g -> EqMor_STT g h -> EqMor_STT f h.
Proof.
intros.
unfold EqMor_STT.
apply E_Trans with (s := proj1_sig g); assumption.
Qed.

Lemma EqMor_STT_eq: forall {x y z} (f g: Hom_STT y z) (h i : Hom_STT x y), EqMor_STT f g /\ EqMor_STT h i ->
        EqMor_STT (Compose_STT f h) (Compose_STT g i).
Proof.
intros.
unfold EqMor_STT in *.
unfold Compose_STT in *.
unfold Compose_STT_term in *.
unfold Compose_STT_type in *.
unfold Hom_STT in *.
simpl in *.
destruct H.



 
Abort.

Lemma EqMor_STT_assoc : forall x y z w (f : (Hom_STT z w)) (g:(Hom_STT y z)) (h:(Hom_STT x y)),
        EqMor_STT (Compose_STT f (Compose_STT g h) ) (Compose_STT (Compose_STT f g) h).
Proof.
intros.
unfold EqMor_STT.
unfold Compose_STT.
unfold Compose_STT_term.
unfold Hom_STT in f.
simpl. 
(*
lam x
    (app (proj1_sig f)
       (app
          (lam x
             (app (proj1_sig g)
                (app (proj1_sig h) (hyp 0))))
          (hyp 0)))
≡ 
    (app
       (lam y
          (app (proj1_sig f)
             (app (proj1_sig g) (hyp 0))))
       (app (proj1_sig h) (hyp 0)))



          
             lam x
    (app (proj1_sig f) (app (proj1_sig g)
                (app (proj1_sig h) (hyp 0)))


lam x
          (app (proj1_sig f)
             (app (proj1_sig g) (app (proj1_sig h) (hyp 0)))
       



*)
Abort.

Lemma EqMor_STT_id_2 : forall x y (f : (Hom_STT x y)), EqMor_STT (Compose_STT (Id_STT y) f) f.
Proof.
Abort.
  


