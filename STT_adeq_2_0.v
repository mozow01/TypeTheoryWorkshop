Require Import List.
Import ListNotations.

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

Lemma TwoCompose_1 {x y z w : Obj_STT} (f : Hom_STT z w) (g : Hom_STT y z) (h : Hom_STT x y) : [ ] ⊢ (Compose_STT_term f (Compose_STT g h)) [:] (x ⊃ w).
Proof.
unfold Hom_STT in *.
unfold Compose_STT_term in *.
unfold Compose_STT in *.
simpl.
unfold Compose_STT_term in *.
apply STT_lam.
apply STT_app with (A:=z).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig f).
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply STT_lam.
apply STT_app with (A:=y).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig g).
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig h).
all: apply STT_hypO.
Defined.

Lemma TwoCompose_2 {x y z w : Obj_STT} (f : Hom_STT z w) (g : Hom_STT y z) (h : Hom_STT x y) : [ ] ⊢ (lam x (app (lam y (app (proj1_sig f) (app (proj1_sig g) (hyp 0)))) (app (proj1_sig h) (hyp 0)))) [:] (x ⊃ w).
Proof.
apply STT_lam.
apply STT_app with (A:=y).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply STT_lam.
apply STT_app with (A:=z).
apply weakening_weak with (Γ:=nil) (Δ:=[y]).
apply (proj2_sig f).
apply STT_app with (A:=y).
apply weakening_weak with (Γ:=nil) (Δ:=[y]).
apply (proj2_sig g).
apply STT_hypO.
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig h).
apply STT_hypO.
Defined.

(*weak beta és eta*)
Inductive STT_equiv : Cntxt -> Typ -> Trm -> Trm -> Prop :=
  | E_proofirrel : forall Γ A t s, Tyty Γ t A -> Tyty Γ s A ->  
      STT_equiv Γ A t s.

Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := STT_equiv nil (x ⊃ y) (proj1_sig f) (proj1_sig g).

Instance STT_as_a_Cat : Category. 
Proof. 
apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT) (EqMor := @EqMor_STT).
{ intros. unfold Hom_STT in *. unfold EqMor_STT. apply E_proofirrel. all: apply (proj2_sig f). }
{ intros. unfold Hom_STT in *. unfold EqMor_STT. apply E_proofirrel. apply (proj2_sig f). apply (proj2_sig h). } 
{ intros. unfold Hom_STT in *. unfold EqMor_STT. apply E_proofirrel. apply (proj2_sig g). apply (proj2_sig f). } 
{ intros. unfold Hom_STT in *. unfold EqMor_STT. simpl. 
unfold Compose_STT_term in *.
simpl.
unfold Compose_STT_term in *.
simpl.
apply E_proofirrel.
apply TwoCompose_1.
apply TwoCompose_2. }
{ intros. unfold Hom_STT in *. unfold EqMor_STT. unfold Compose_STT in *. simpl. unfold Compose_STT_term in *. simpl. unfold Id_STT_term in *. simpl. apply E_proofirrel.
apply STT_lam.
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig f).
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply STT_lam.
apply STT_hypO.
apply STT_hypO.
apply (proj2_sig f). }
{ intros. unfold Hom_STT in *. unfold EqMor_STT. unfold Compose_STT in *. simpl. unfold Compose_STT_term in *. simpl. unfold Id_STT_term in *. simpl. apply E_proofirrel.
apply STT_lam.
apply STT_app with (A:=y).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply STT_lam.
apply STT_hypO.
apply STT_app with (A:=x).
apply weakening_weak with (Γ:=nil) (Δ:=[x]).
apply (proj2_sig f).
apply STT_hypO.
apply (proj2_sig f). }
{ intros. unfold EqMor_STT. apply E_proofirrel. all: unfold Compose_STT in *. all: simpl.
all: apply Compose_STT_type. }
Defined.
