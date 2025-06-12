Require Import List Arith Peano Lia.
Import ListNotations.

(* STT + /\ + T *)

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_top : forall Γ, Tyty Γ top Top
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | STT_cnj :
      forall Γ t s A B,
      Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | STT_proj1 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | STT_proj2 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.

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



Definition Obj_STT := Typ.

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (x ⊃ y)}.

Definition Id_STT_term (x : Obj_STT) := (lam x (hyp 0)).

Lemma Id_STT_type (x : Obj_STT) : ⊢ (Id_STT_term x) [:] (x ⊃ x).
Proof.
unfold Id_STT_term.
apply STT_lam.
apply STT_hypO.
Defined.

Definition Id_STT (x : Typ) : {t : Trm | ⊢ t [:] (x ⊃ x)} :=
  exist (fun t => ⊢ t [:] (x ⊃ x)) (Id_STT_term x) (Id_STT_type x).

Lemma weakening_weak : forall Γ Δ t A,
  Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  simpl; auto.
  intros Γ Δ t A H.
  induction H.
  all: try rewrite K; try rewrite <- app_assoc; try rewrite <- K.
  - apply STT_top.
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
  - apply STT_cnj.
    all: auto.
  - apply STT_proj1 with (Γ := Γ ++ Δ ) (B:=B).
    auto.
 - apply STT_proj2 with (Γ := Γ ++ Δ ) (A:=A).
    auto.
Defined.

Definition Compose_STT_term {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) := lam x (app (proj1_sig f) (app (proj1_sig g) (hyp 0))).

Definition Compose_STT_type {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : ⊢ (Compose_STT_term f g) [:] (x ⊃ z).
Proof.
unfold Compose_STT_term.
apply STT_lam.
assert (Kf : ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { exact (proj2_sig f). }
assert (Kg : ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { exact (proj2_sig g). }
assert (Kfx : [x] ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f); auto. }
assert (Kgx : [x] ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g); auto. }
apply STT_app with (A:=y). auto.
apply STT_app with (A:=x). auto.
apply STT_hypO.
Defined.

Definition Compose_STT {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : {t : Trm | ⊢ t [:] (x ⊃ z)} :=
  exist (fun t => ⊢ t [:] (x ⊃ z)) (Compose_STT_term f g) (Compose_STT_type f g).

(*weak beta és eta*)
Inductive STT_equiv : Trm -> Trm -> Prop :=
  | E_Refl : forall t,
      STT_equiv t t
  | E_Symm : forall t s,
      STT_equiv t s ->
      STT_equiv s t
  | E_Trans : forall t s u,
      STT_equiv t s ->
      STT_equiv s u ->
      STT_equiv t u
  | E_app : forall  p1 p2 q1 q2,
      STT_equiv p1 p2 ->
      STT_equiv  q1 q2 ->
      STT_equiv (app p1 q1) (app p2 q2)
  | E_lam : forall  p1 p2 A,
      STT_equiv p1 p2 -> 
      STT_equiv (lam A p1) (lam A p2)
  | E_beta_1 : forall A t,
      STT_equiv (app (lam A (hyp 0)) t) t
  | E_beta_2 : forall A t s,
      STT_equiv  
(app (lam A (app t (app s (hyp 0)))) (hyp 0)) 
((app t (app s (hyp 0))))
  | E_beta_3 : forall A t s r, STT_equiv
(app (lam A (app t (app s (hyp 0)))) (app r (hyp 0)))
(app t (app s (app r (hyp 0))))
  | E_eta : forall t A,
      STT_equiv (lam A (app t (hyp 0))) t
  | E_top : forall A (g : {t : Trm | ⊢ t [:] (A ⊃ Top)}), STT_equiv (proj1_sig g) (lam A top)
 | E_prod_ax1 : forall {x y z : Typ} (f g : Trm),
      STT_equiv
        (app
           (lam (Cnj y z) (proj_1 (hyp 0)))
           (app (lam x (cnj (app f (hyp 0)) (app g (hyp 0)))) (hyp 0)))
        (app f (hyp 0))
 | E_prod_ax2 : forall {x y z : Typ} (f g : Trm),
      STT_equiv
        (app
           (lam (Cnj y z) (proj_2 (hyp 0)))
           (app (lam x (cnj (app f (hyp 0)) (app g (hyp 0)))) (hyp 0)))
        (app g (hyp 0)).

Notation "t ≡ s" := (STT_equiv t s) (at level 45, left associativity).

(* Setoidnak nevezünk egy típust és az elemei közötti ekvivalenciarelációt (voltaképpen typeoid) *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Lemma STT_equiv_Transitive : forall t s u,
  STT_equiv t s -> STT_equiv s u -> STT_equiv t u.
Proof.
  intros t s u H1 H2.
  apply E_Trans with (s := s); assumption.
Defined.

Add Parametric Relation : Trm (STT_equiv )
  reflexivity proved by (E_Refl )
  symmetry proved by (E_Symm)
  transitivity proved by (STT_equiv_Transitive )
  as STT_equiv_rel.

Lemma E_comp_1 : forall t1 t2 s1 s2 A,
      STT_equiv t1 t2 -> 
      STT_equiv s1 s2 -> 
      STT_equiv (lam A (app t1 (app s1 (hyp 0))))
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
      STT_equiv (app (lam A (hyp 0)) (hyp 0)) (hyp 0).
Proof.
intros.
apply E_beta_1 with (A:=A) (t:=hyp 0).
Defined.

Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := STT_equiv (proj1_sig f) (proj1_sig g).

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
assert (K1 : STT_equiv
(app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0))) (app (proj1_sig f) (hyp 0))).
 { apply E_app.
   reflexivity.
   apply E_beta_0. }
assert (K2 : STT_equiv (lam x
    (app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0)))) (lam x
    (app (proj1_sig f) (hyp 0)))).
 { apply E_lam with (A:=x).
   apply K1. }
rewrite K2.
apply E_eta.
Defined.

Lemma EqMor_STT_id_2 : forall x y (f : (Hom_STT x y)), EqMor_STT (Compose_STT (Id_STT y) f) f.
Proof.
intros.
unfold EqMor_STT.
unfold Compose_STT.
simpl.
unfold Compose_STT_term.
unfold Id_STT.
simpl.
unfold Id_STT_term.
assert (K1 : STT_equiv 
(app (lam y (hyp 0)) (app (proj1_sig f) (hyp 0))) (app (proj1_sig f) (hyp 0))).
apply E_beta_1.
assert (K2 : STT_equiv 

(lam x (app (lam y (hyp 0)) (app (proj1_sig f) (hyp 0))))

(lam x (app (proj1_sig f) (hyp 0)))
).
apply E_lam with (A:=x).
apply K1.
rewrite K2.
apply E_eta.
Defined.

Lemma EqMor_STT_ref : forall {x y} (f : Hom_STT x y), EqMor_STT f f.
Proof.
intros.
unfold EqMor_STT.
apply E_Refl.
Defined.

Lemma EqMor_STT_sym : forall {x y} (f g : Hom_STT x y), EqMor_STT f g -> EqMor_STT g f.
Proof.
intros.
unfold EqMor_STT.
apply E_Symm.
assumption.
Defined.

Lemma EqMor_STT_trans : forall {x y} (f g h : Hom_STT x y), EqMor_STT f g -> EqMor_STT g h -> EqMor_STT f h.
Proof. 
intros.
unfold EqMor_STT.
apply E_Trans with (s := proj1_sig g); assumption.
Defined.


Lemma EqMor_STT_assoc : forall x y z w (f : (Hom_STT z w)) (g:(Hom_STT y z)) (h:(Hom_STT x y)),
        EqMor_STT (Compose_STT f (Compose_STT g h) ) (Compose_STT (Compose_STT f g) h).
Proof.
intros.
unfold EqMor_STT.
unfold Compose_STT.
unfold Compose_STT_term.
unfold Hom_STT in f.
simpl. 
assert (K1: STT_equiv 
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
assert (K2: STT_equiv 
(lam x (app (lam y (app (proj1_sig f) (app (proj1_sig g) (hyp 0)))) (app (proj1_sig h) (hyp 0))))

(lam x ((app (proj1_sig f) (app (proj1_sig g) (app (proj1_sig h) (hyp 0))))))).
apply E_lam with (A:=x).
apply E_beta_3.
rewrite K1.
rewrite K2.
reflexivity.
Defined.

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
elim H.
intros H0 H1.
apply E_comp_1.
apply H0. apply H1.
Defined.

Instance STT_as_a_Cat : Category. 
Proof. 
apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT) (EqMor := @EqMor_STT).
{ intros. apply EqMor_STT_ref. }
{ intros. apply EqMor_STT_trans with (g:=g). all: auto. } 
{ intros. apply EqMor_STT_sym. all: auto. } 
{ intros. apply EqMor_STT_assoc. }
{ intros. apply id_1_STT. }
{ intros. apply EqMor_STT_id_2. }
{ intros. apply EqMor_STT_eq. auto. }
Defined.


Class CartClosedCat (C : Category) := CartClosedCat_mk {

(* terminal *)

  Top_obj : Obj;

  Top_mor : forall {x}, x → Top_obj;

(* szorzat *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;

(* exponenciális *)

  Exp_obj : Obj -> Obj -> Obj;

  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

(* Egyenlőségek *)

  unique_top : forall {x} (f : x → Top_obj), f ≅ Top_mor;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (First ∘ (Prod_mor f g) ≅ f) /\ (Second ∘ (Prod_mor f g) ≅ g);
  
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y
z),
    ((First ∘ h) ≅ f) /\ ((Second ∘ h) ≅ g) -> h ≅ Prod_mor f g;

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) ≅ g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) ≅ h
}.

Definition Prodmor_STT_term (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) := lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g)(hyp 0) )).

Lemma Prodmor_STT_type (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) : ⊢ lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g)(hyp 0) )) [:] (Imp x (Cnj y z)).
Proof.
apply STT_lam.
apply STT_cnj.
apply STT_app with (A:=x).
apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f).
exact (proj2_sig f).
apply STT_hypO.
apply STT_app with (A:=x).
apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g).
exact (proj2_sig g).
apply STT_hypO.
Defined.

Definition Prodmor_STT (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) : {t : Trm | ⊢ t [:]  (Imp x (Cnj y z))} :=
  exist (fun t => ⊢ t [:] (Imp x (Cnj y z))) (Prodmor_STT_term x y z f g) (Prodmor_STT_type x y z f g).


Definition Topmor_STT_term (A : Obj_STT) := (lam A top).

Lemma Topmor_STT_type (A : Obj_STT) : ⊢ (lam A top) [:] (Imp A Top).
Proof.
intros.
apply STT_lam.
apply STT_top.
Defined.

Definition Topmor_STT (x : Typ) : {t : Trm | ⊢ t [:] (Imp x Top)} :=
  exist (fun t => ⊢ t [:] ((Imp x Top))) (Topmor_STT_term x) (Topmor_STT_type x).

Lemma First_STT_type (x y : Obj_STT) : ⊢ (lam (Cnj x y) (proj_1 (hyp 0))) [:] (Imp (Cnj x y) x).
Proof.
apply STT_lam.
apply STT_proj1 with (A:=x) (B:=y).
apply STT_hypO.
Defined.

Definition First_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_1 (hyp 0))). 

Definition First_STT (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) x)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) x)) (First_STT_term x y) (First_STT_type x y).

Lemma Second_STT_type (x y : Obj_STT) : ⊢ (lam (Cnj x y) (proj_2 (hyp 0))) [:] (Imp (Cnj x y) y).
Proof.
apply STT_lam.
apply STT_proj2 with (A:=x) (B:=y).
apply STT_hypO.
Defined.

Definition Second_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_2 (hyp 0))). 

Definition Second_STT (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) y)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) y)) (Second_STT_term x y) (Second_STT_type x y).

Lemma Expapp_STT_type (y z : Typ) : ⊢ lam (Cnj (Imp y z) y) (app (proj_1 (hyp 0)) (proj_2 (hyp 0)) ) [:] (Imp (Cnj (Imp y z) y) z).
Proof.
apply STT_lam.
assert (K0 : [Cnj (y ⊃ z) y] ⊢ (hyp 0) [:] (Cnj (y ⊃ z) y)).
apply STT_hypO.
assert (K1 : [Cnj (y ⊃ z) y] ⊢ (proj_1 (hyp 0)) [:] (y ⊃ z)).
apply STT_proj1 in K0.
auto.
assert (K2 : [Cnj (y ⊃ z) y] ⊢ (proj_2 (hyp 0)) [:] y).
apply STT_proj2 in K0.
auto.
apply STT_app with (A:=y) (B:=z).
all: auto.
Defined.

Definition Expapp_STT_term (y z : Obj_STT) := lam (Cnj (Imp y z) y) (app (proj_1 (hyp 0)) (proj_2 (hyp 0)) ). 

Definition Expapp_STT (y z : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj (Imp y z) y) z)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj (Imp y z) y) z)) (Expapp_STT_term y z) (Expapp_STT_type y z).

Lemma Lam_STT_type (x y z : Obj_STT) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) : ⊢ (lam x (lam y (app (proj1_sig g) (cnj (hyp 1) (hyp 0))))) [:] Imp x (Imp y z).
Proof.
apply STT_lam.
apply STT_lam.
assert (K1 : ⊢ (proj1_sig g) [:] (Cnj x y ⊃ z)).
exact (proj2_sig g).
assert (K2 : [y; x] ⊢ (cnj (hyp 1) (hyp 0)) [:] (Cnj x y)).
apply STT_cnj.
apply STT_hypS.
apply STT_hypO.
apply STT_hypO.
apply STT_app with (A:=(Cnj x y)) (B:=z).
all: auto.
apply weakening_weak with (Γ:=nil) (Δ:=[y; x]).
auto.
Defined.

Definition Lam_STT_term (x y z : Obj_STT) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) := (lam x (lam y (app (proj1_sig g) (cnj (hyp 1) (hyp 0))))). 

Definition Lam_STT (x y z : Typ) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) : {t : Trm | ⊢ t [:] (Imp x (Imp y z))} :=
  exist (fun t => ⊢ t [:] (Imp x (Imp y z))) (Lam_STT_term x y z g) (Lam_STT_type x y z g).

Lemma unique_top_STT : forall A (g : {t : Trm | ⊢ t [:] (Imp A Top)}), EqMor_STT g (Topmor_STT A). 
Proof.
intros.
unfold EqMor_STT.
unfold Topmor_STT.
unfold Topmor_STT_term.
unfold Topmor_STT_type.
simpl.
rewrite E_top.
reflexivity.
Defined.

Lemma prod_ax_1_STT : forall {x y z} (f : Hom_STT x y) (g : Hom_STT x z),
  EqMor_STT (Compose_STT (First_STT y z) (Prodmor_STT x y z f g)) f.
Proof.
  intros x y z f g.
  unfold EqMor_STT, Compose_STT, Prodmor_STT, First_STT.
  simpl.
  unfold Compose_STT_term, Prodmor_STT_term, First_STT_term.

  (* A cél a következő ekvivalencia igazolása:
     STT_equiv
       (lam x
          (app (lam (Cnj y z) (proj_1 (hyp 0)))
             (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
                (hyp 0))))
       (proj1_sig f)
  *)

  (* Először a lambda-kifejezés törzsére vonatkozó ekvivalenciát igazoljuk. *)
  assert (K_body_equiv : STT_equiv
    (app (lam (Cnj y z) (proj_1 (hyp 0)))
         (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
              (hyp 0)))
    (app (proj1_sig f) (hyp 0))).
  {
    (* Ezt az újonnan felvett szabályunk biztosítja. *)
    apply E_prod_ax1.
  }

  (* Ezt az ekvivalenciát "beemeljük" a külső lambda alá. *)
  assert (K_lam_equiv : STT_equiv
    (lam x (app (lam (Cnj y z) (proj_1 (hyp 0)))
                (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
                     (hyp 0))))
    (lam x (app (proj1_sig f) (hyp 0)))).
  {
    apply E_lam.
    apply K_body_equiv.
  }

  (* A `rewrite` után a cél `lam x (app (proj1_sig f) (hyp 0)) ≅ proj1_sig f`. *)
  rewrite K_lam_equiv.

  (* Ez pedig pontosan az éta-ekvivalencia. *)
  apply E_eta.
Defined.

Lemma prod_ax_2_STT : forall {x y z} (f : Hom_STT x y) (g : Hom_STT x z),
  EqMor_STT (Compose_STT (Second_STT y z) (Prodmor_STT x y z f g)) g.
Proof.
  intros x y z f g.
  unfold EqMor_STT, Compose_STT, Prodmor_STT, Second_STT.
  simpl.
  unfold Compose_STT_term, Prodmor_STT_term, Second_STT_term.

  (* A cél a következő ekvivalencia igazolása:
     STT_equiv
       (lam x
          (app (lam (Cnj y z) (proj_2 (hyp 0)))
             (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
                (hyp 0))))
       (proj1_sig g)
  *)

  (* Ismét a lambda-kifejezés törzsére vonatkozó ekvivalenciát igazoljuk. *)
  assert (K_body_equiv : STT_equiv
    (app (lam (Cnj y z) (proj_2 (hyp 0)))
         (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
              (hyp 0)))
    (app (proj1_sig g) (hyp 0))). 
  {
    (* Ezt a most felvett E_prod_ax2 szabály biztosítja. *)
    apply E_prod_ax2.
  }

  (* Ezt az ekvivalenciát "beemeljük" a külső lambda alá. *)
  assert (K_lam_equiv : STT_equiv
    (lam x (app (lam (Cnj y z) (proj_2 (hyp 0)))
                (app (lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))))
                     (hyp 0))))
    (lam x (app (proj1_sig g) (hyp 0)))).
  {
    apply E_lam.
    apply K_body_equiv.
  }

  (* A `rewrite` után a cél `lam x (app (proj1_sig g) (hyp 0)) ≅ proj1_sig g`. *)
  rewrite K_lam_equiv.

  (* Ez ismét pontosan az éta-ekvivalencia. *)
  apply E_eta.
Defined.
