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
  | Arr : Typ -> Typ -> Typ.

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

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (Arr x y)}.

Lemma Id_STT (x : Obj_STT) : { t : Trm | ⊢ t [:] (Arr x x)}.
Proof.
exists (lam x (hyp 0)).
apply STT_lam.
apply STT_hypO.
Defined.

Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) := ((proj1_sig f) = (proj1_sig g)).

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

Definition weak0 t := lift_aux 1 t 0.

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
compute. auto.
unfold lift.
simpl. auto.
Defined.


Lemma liftlam_aux (n : nat) (k : nat) (A : Typ) (M : Trm) : lift_aux n (lam A M) k = lam A (lift_aux n M (S k)).
Proof.
simpl; auto.
Defined.


Lemma Compose_STT (x y z : Obj_STT) : (Hom_STT y z) -> (Hom_STT x y) -> (Hom_STT x z).
Proof.



