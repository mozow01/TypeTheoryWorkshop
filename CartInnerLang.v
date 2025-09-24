Require Import List Arith Peano Lia.
Import ListNotations.

(* /\ + T *)

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | idc : Typ -> Trm
  | comp : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | Cart_top : forall Γ, Tyty Γ top Top
  | Cart_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | Cart_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | Cart_id : forall Γ A, Tyty (A :: Γ) (idc A) A
  | Cart_comp : forall Γ A B C f g, Tyty (A :: Γ) g B -> Tyty (B :: Γ) f C -> Tyty (A :: Γ) (comp f g) C
  | Cart_cnj :
      forall Γ t s A B,
      Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | Cart_proj1 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | Cart_proj2 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.


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

(* morfizmus egyenlőség: \cong term egyenlőség: \equiv *)
Notation "f ≅ g" := (EqMor f g) (at level 40, left associativity) :
type_scope.



Definition Obj_Cart := Typ.

Definition Hom_Cart (x y : Obj_Cart) := { t : Trm | [ x ] ⊢ t [:] y}.

Definition Id_Cart_term (x : Obj_Cart) := idc x.

Lemma Id_Cart_type (x : Obj_Cart) : [ x ] ⊢ (Id_Cart_term x) [:] x.
Proof.
unfold Id_Cart_term.
apply Cart_id.
Defined.

Definition Id_Cart (x : Typ) : {t : Trm | [ x ] ⊢ t [:] x} :=
  exist (fun t => [ x ] ⊢ t [:] x) (Id_Cart_term x) (Id_Cart_type x).

Lemma weakening_weak : forall Γ Δ t A,
  Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  simpl; auto.
  intros Γ Δ t A H.
  induction H.
  all: try rewrite K; try rewrite <- app_assoc; try rewrite <- K.
  - apply Cart_top.
  - apply Cart_hypO.
  - apply Cart_hypS.
    auto.
  - apply Cart_id.
  - apply Cart_comp with (B:=B).
    all: intuition.
  - apply Cart_cnj.
    all: auto.
  - apply Cart_proj1 with (Γ := Γ ++ Δ ) (B:=B).
    auto.
 - apply Cart_proj2 with (Γ := Γ ++ Δ ) (A:=A).
    auto.
Defined.

Definition Compose_Cart_term {x y z : Obj_Cart} (f : Hom_Cart y z) (g : Hom_Cart x y) := comp (proj1_sig f) (proj1_sig g).

Definition Compose_Cart_type {x y z : Obj_Cart} (f : Hom_Cart y z) (g : Hom_Cart x y) : [ x ] ⊢ (Compose_Cart_term f g) [:] z.
Proof.
unfold Compose_Cart_term.
apply Cart_comp with (B:=y).
exact (proj2_sig g).
exact (proj2_sig f).
Defined.

Definition Compose_Cart {x y z : Obj_Cart} (f : Hom_Cart y z) (g : Hom_Cart x y) : {t : Trm | [ x ] ⊢ t [:] z } :=
  exist (fun t => [ x ] ⊢ t [:] z) (Compose_Cart_term f g) (Compose_Cart_type f g).

Definition Prodmor_Cart_term (x y z : Obj_Cart) (f : {t : Trm | [ x ] ⊢ t [:]  y} ) (g : {t : Trm | [ x ] ⊢ t [:]  z } ) := (cnj (proj1_sig f) (proj1_sig g)).

Lemma Prodmor_Cart_type (x y z : Obj_Cart) (f : {t : Trm | [ x ] ⊢ t [:] y } ) (g : {t : Trm | [ x ] ⊢ t [:] z } ) : [ x ] ⊢ cnj (proj1_sig f) (proj1_sig g) [:] (Cnj y z).
Proof.
apply Cart_cnj.
exact (proj2_sig f).
exact (proj2_sig g).
Defined.

Definition Prodmor_Cart (x y z : Obj_Cart) (f : {t : Trm | [ x ] ⊢ t [:] y} ) (g : {t : Trm | [ x ] ⊢ t [:] z } ) : {t : Trm | [ x ] ⊢ t [:] (Cnj y z)} :=
  exist (fun t => [ x ] ⊢ t [:] (Cnj y z)) (Prodmor_Cart_term x y z f g) (Prodmor_Cart_type x y z f g).

Definition Topmor_Cart_term (A : Obj_Cart) := top.

Lemma Topmor_Cart_type (A : Obj_Cart) : [ A ] ⊢ (top) [:] Top.
Proof.
intros.
apply Cart_top.
Defined.

Definition Topmor_Cart (x : Typ) : Hom_Cart x Top :=
  exist (fun t => [x] ⊢ t [:] Top) (Topmor_Cart_term x) (Topmor_Cart_type x).

Definition First_Cart_term (x y : Obj_Cart) := proj_1.


(*EDDIG*)


Definition First_Cart (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) x)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) x)) (First_Cart_term x y) (First_Cart_type x y).

Lemma Second_Cart_type (x y : Obj_Cart) : ⊢ (lam (Cnj x y) (proj_2 (hyp 0))) [:] (Imp (Cnj x y) y).
Proof.
apply Cart_lam.
apply Cart_proj2 with (A:=x) (B:=y).
apply Cart_hypO.
Defined.

Definition Second_Cart_term (x y : Obj_Cart) := (lam (Cnj x y) (proj_2 (hyp 0))). 

Definition Second_Cart (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) y)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) y)) (Second_Cart_term x y) (Second_Cart_type x y).


(*weak beta és eta*)
Inductive Cart_equiv : Trm -> Trm -> Prop :=
  | E_Refl : forall t,
      Cart_equiv t t
  | E_Symm : forall t s,
      Cart_equiv t s ->
      Cart_equiv s t
  | E_Trans : forall t s u,
      Cart_equiv t s ->
      Cart_equiv s u ->
      Cart_equiv t u
  | E_app : forall  p1 p2 q1 q2,
      Cart_equiv p1 p2 ->
      Cart_equiv  q1 q2 ->
      Cart_equiv (app p1 q1) (app p2 q2)
  | E_lam : forall  p1 p2 A,
      Cart_equiv p1 p2 -> 
      Cart_equiv (lam A p1) (lam A p2)
  | E_beta_1 : forall A t,
      Cart_equiv (app (lam A (hyp 0)) t) t
  | E_beta_2 : forall A t s,
      Cart_equiv  
(app (lam A (app t (app s (hyp 0)))) (hyp 0)) 
((app t (app s (hyp 0))))
  | E_beta_3 : forall A t s r, Cart_equiv
(app (lam A (app t (app s (hyp 0)))) (app r (hyp 0)))
(app t (app s (app r (hyp 0))))
  | E_cnj : forall t1 s1 t2 s2,
      Cart_equiv t1 t2 ->
      Cart_equiv s1 s2 ->
      Cart_equiv (cnj t1 s1) (cnj t2 s2)
  | E_eta : forall t A,
      Cart_equiv (lam A (app t (hyp 0))) t
  | E_top : forall A (g : {t : Trm | ⊢ t [:] (A ⊃ Top)}), Cart_equiv (proj1_sig g) (lam A top)
 | E_prod_ax1 : forall t s, Cart_equiv (proj_1 (cnj t s)) t
 | E_prod_ax2 : forall {x y z : Typ} (f g : Trm),
      Cart_equiv
        (app
           (lam (Cnj y z) (proj_2 (hyp 0)))
           (app (lam x (cnj (app f (hyp 0)) (app g (hyp 0)))) (hyp 0)))
        (app g (hyp 0))
 | E_prod_eta : forall {x y z : Typ} (g_t : Trm),
      let f_comp := (lam z (app (lam (Cnj x y) (proj_1 (hyp 0))) (app g_t (hyp 0)))) in
      let g_comp := (lam z (app (lam (Cnj x y) (proj_2 (hyp 0))) (app g_t (hyp 0)))) in
      Cart_equiv (lam z (cnj (app f_comp (hyp 0)) (app g_comp (hyp 0)))) g_t
| E_exp_ax : forall {x y z} (g : Hom_Cart (Cnj x y) z),
      Cart_equiv (proj1_sig (Compose_Cart (Expapp_Cart y z) (Prodmor_Cart (Cnj x y) (Imp y z) y (Compose_Cart (Lam_Cart x y z g) (First_Cart x y)) (Compose_Cart (Id_Cart y) (Second_Cart x y))))) (proj1_sig g)
  | E_unique_exp : forall {x y z} (h : Hom_Cart x (Imp y z)),
      Cart_equiv (proj1_sig (Lam_Cart x y z (Compose_Cart (Expapp_Cart y z) (Prodmor_Cart (Cnj x y) (Imp y z) y (Compose_Cart h (First_Cart x y)) (Compose_Cart (Id_Cart y) (Second_Cart x y)))))) (proj1_sig h).

Notation "t ≡ s" := (Cart_equiv t s) (at level 45, left associativity).

(* Setoidnak nevezünk egy típust és az elemei közötti ekvivalenciarelációt (voltaképpen typeoid) *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma Cart_equiv_Transitive : forall t s u,
  Cart_equiv t s -> Cart_equiv s u -> Cart_equiv t u.
Proof.
  intros t s u H1 H2.
  apply E_Trans with (s := s); assumption.
Defined.

Add Parametric Relation : Trm (Cart_equiv )
  reflexivity proved by (E_Refl )
  symmetry proved by (E_Symm)
  transitivity proved by (Cart_equiv_Transitive )
  as Cart_equiv_rel.

Lemma E_comp_1 : forall t1 t2 s1 s2 A,
      Cart_equiv t1 t2 -> 
      Cart_equiv s1 s2 -> 
      Cart_equiv (lam A (app t1 (app s1 (hyp 0))))
  (lam A (app t2 (app s2 (hyp 0)))).
Proof.
intros t1 t2 s1 s2 A H H0.
apply E_lam.
apply E_app.
apply H.
apply E_app.
apply H0.
reflexivity.
Defined.

Lemma E_beta_0 : forall A,
      Cart_equiv (app (lam A (hyp 0)) (hyp 0)) (hyp 0).
Proof.
intros.
apply E_beta_1 with (A:=A) (t:=hyp 0).
Defined.

Definition EqMor_Cart {x y : Obj_Cart} (f g : Hom_Cart x y) := Cart_equiv (proj1_sig f) (proj1_sig g).

Lemma id_1_Cart : forall x y (f : (Hom_Cart x y)), EqMor_Cart (Compose_Cart f (Id_Cart x)) f.
Proof.
intros.
unfold EqMor_Cart.
unfold Compose_Cart.
simpl.
unfold Compose_Cart_term.
unfold Id_Cart.
simpl.
unfold Id_Cart_term.
assert (K1 : Cart_equiv
(app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0))) (app (proj1_sig f) (hyp 0))).
 { apply E_app.
   reflexivity.
   apply E_beta_0. }
assert (K2 : Cart_equiv (lam x
    (app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0)))) (lam x
    (app (proj1_sig f) (hyp 0)))).
 { apply E_lam with (A:=x).
   apply K1. }
rewrite K2.
apply E_eta.
Defined.

Lemma EqMor_Cart_id_2 : forall x y (f : (Hom_Cart x y)), EqMor_Cart (Compose_Cart (Id_Cart y) f) f.
Proof.
intros.
unfold EqMor_Cart.
unfold Compose_Cart.
simpl.
unfold Compose_Cart_term.
unfold Id_Cart.
simpl.
unfold Id_Cart_term.
assert (K1 : Cart_equiv 
(app (lam y (hyp 0)) (app (proj1_sig f) (hyp 0))) (app (proj1_sig f) (hyp 0))).
apply E_beta_1.
assert (K2 : Cart_equiv 

(lam x (app (lam y (hyp 0)) (app (proj1_sig f) (hyp 0))))

(lam x (app (proj1_sig f) (hyp 0)))
).
apply E_lam with (A:=x).
apply K1.
rewrite K2.
apply E_eta.
Defined.

Lemma EqMor_Cart_ref : forall {x y} (f : Hom_Cart x y), EqMor_Cart f f.
Proof.
intros.
unfold EqMor_Cart.
apply E_Refl.
Defined.

Lemma EqMor_Cart_sym : forall {x y} (f g : Hom_Cart x y), EqMor_Cart f g -> EqMor_Cart g f.
Proof.
intros.
unfold EqMor_Cart.
apply E_Symm.
assumption.
Defined.

Lemma EqMor_Cart_trans : forall {x y} (f g h : Hom_Cart x y), EqMor_Cart f g -> EqMor_Cart g h -> EqMor_Cart f h.
Proof. 
intros.
unfold EqMor_Cart.
apply E_Trans with (s := proj1_sig g); assumption.
Defined.


Lemma EqMor_Cart_assoc : forall x y z w (f : (Hom_Cart z w)) (g:(Hom_Cart y z)) (h:(Hom_Cart x y)),
        EqMor_Cart (Compose_Cart f (Compose_Cart g h) ) (Compose_Cart (Compose_Cart f g) h).
Proof.
intros.
unfold EqMor_Cart.
unfold Compose_Cart.
unfold Compose_Cart_term.
unfold Hom_Cart in f.
simpl. 
assert (K1: Cart_equiv 
(lam x
    (app (proj1_sig f)
       (app (lam x (app (proj1_sig g) (app (proj1_sig h) (hyp 0)))) (hyp 0))))
(lam x
    (app (proj1_sig f)
       (app (proj1_sig g) (app (proj1_sig h) (hyp 0)))))).
apply E_lam with (A:=x).
apply E_app.
reflexivity.
apply E_beta_2.
assert (K2: Cart_equiv 
(lam x (app (lam y (app (proj1_sig f) (app (proj1_sig g) (hyp 0)))) (app (proj1_sig h) (hyp 0))))

(lam x ((app (proj1_sig f) (app (proj1_sig g) (app (proj1_sig h) (hyp 0))))))).
apply E_lam with (A:=x).
apply E_beta_3.
rewrite K1.
rewrite K2.
reflexivity.
Defined.

Lemma EqMor_Cart_eq: forall {x y z} (f g: Hom_Cart y z) (h i : Hom_Cart x y), EqMor_Cart f g /\ EqMor_Cart h i ->
        EqMor_Cart (Compose_Cart f h) (Compose_Cart g i).
Proof.
intros.
unfold EqMor_Cart in *.
unfold Compose_Cart in *.
unfold Compose_Cart_term in *.
unfold Compose_Cart_type in *.
unfold Hom_Cart in *.
simpl in *.
elim H.
intros H0 H1.
apply E_comp_1.
apply H0. apply H1.
Defined.

Instance Cart_as_a_Cat : Category. 
Proof. 
apply cat_mk with (Obj := Obj_Cart) (Hom := Hom_Cart) (Id := Id_Cart) (Compose := @Compose_Cart) (EqMor := @EqMor_Cart).
{ intros. apply EqMor_Cart_ref. }
{ intros. apply EqMor_Cart_trans with (g:=g). all: auto. } 
{ intros. apply EqMor_Cart_sym. all: auto. } 
{ intros. apply EqMor_Cart_assoc. }
{ intros. apply id_1_Cart. }
{ intros. apply EqMor_Cart_id_2. }
{ intros. apply EqMor_Cart_eq. auto. }
Defined.

