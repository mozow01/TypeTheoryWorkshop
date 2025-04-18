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


Inductive Typ : Set :=
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
  | E_app : forall p1 p2 q1 q2,
      STT_equiv p1 p2 ->
      STT_equiv q1 q2 ->
      STT_equiv (app p1 q1) (app p2 q2)
  | E_lam : forall p1 p2 A,
      STT_equiv p1 p2 -> 
      STT_equiv (lam A p1) (lam A p2) 
  | E_beta : forall A,
      STT_equiv (app (lam A (hyp 0)) (hyp 0)) (hyp 0)
  | E_eta : forall t A,
      STT_equiv (lam A (app t (hyp 0))) t.

Notation "'⊢' t '≡' s " := (STT_equiv t s) (at level 45, left associativity).

(* Setoidnak nevezünk egy típust és az elemei közötti ekvivalenciarelációt (voltaképpen typeoid) *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.RelationClasses.

Add Parametric Relation : Trm (STT_equiv)
  reflexivity proved by (E_Refl)
  symmetry proved by (E_Symm )
  transitivity proved by (E_Trans)
  as STT_equiv_rel.

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
   apply E_beta. }
assert (K2 : STT_equiv (lam x
    (app (proj1_sig f)
       (app (lam x (hyp 0)) (hyp 0)))) (lam x
    (app (proj1_sig f) (hyp 0)))).
 { apply E_lam with (A:=x).
   apply K1. }
assert (K3 : STT_equiv (lam x (app (proj1_sig f) (hyp 0))) (proj1_sig f)).
 { apply E_eta. }
apply E_Trans with (t:= lam x
         (app (proj1_sig f)
            (app (lam x (hyp 0)) (hyp 0)))) (s:= lam x (app (proj1_sig f) (hyp 0))) (u:= proj1_sig f).
all: auto.
Defined.

Lemma EqMor_STT_ref : forall {x y} (f : Hom_STT x y), EqMor_STT f f.
Proof.
intros.
unfold EqMor_STT.
reflexivity.
Defined.

Lemma EqMor_STT_sim : forall {x y} (f g : Hom_STT x y), EqMor_STT f g -> EqMor_STT g f.
Proof.
intros.
unfold EqMor_STT.
unfold EqMor_STT in H.
congruence.
Defined.

Lemma EqMor_STT_trans : forall {x y} (f g h : Hom_STT x y), EqMor_STT f g -> EqMor_STT g h 
         -> EqMor_STT f h.
Proof.
intros.
unfold EqMor_STT.
unfold EqMor_STT in H, H0.
congruence.
Defined.

Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | hyp i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) hyp (i + n)
                  | right _ => (* k > i *) hyp i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

Definition lift t n := lift_aux n t 0.

Lemma liftappaux (n : nat) (M N : Trm) (k : nat) : lift_aux n (app M N) k = app (lift_aux n M k) (lift_aux n N k).
Proof.
simpl; auto.
Defined.

Lemma liftapp (n : nat) (M N : Trm) : lift (app M N) n  = app (lift M n) (lift N n).
Proof.
simpl; auto.
Defined.

Lemma lifthypS (n : nat) (i : nat) : lift (hyp i) n = hyp (i + n).
Proof.
induction i.
compute; auto.
unfold lift.
simpl; auto.
Defined.

Lemma liftlam_aux (n : nat) (k : nat) (A : Typ) (M : Trm) : lift_aux n (lam A M) k = lam A (lift_aux n M (S k)).
Proof.
simpl; auto.
Defined.





