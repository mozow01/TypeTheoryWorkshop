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

Fixpoint lift_aux (n : nat) (t : Trm) (k : nat) {struct t} : Trm :=
   match t with
     | hyp i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) hyp (i + n)
                  | right _ => (* k > i *) hyp i
                end
     | app M N => app (lift_aux n M k) (lift_aux n N k)
     | lam A M => lam A (lift_aux n M (S k))
   end.

Definition lift P n := lift_aux n P 0.

Definition lift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => lift (s 0) 1
     | S m => lift (s (S m)) 1
  end.

Definition shift_seq (s : nat -> Trm) (k : nat) : Trm  :=
  match k with 
     | 0 => hyp 0
     | S m => (s m)
  end.

Fixpoint subst_aux (t : Trm) (n : nat) (s : nat -> Trm) {struct t} : Trm :=
  match t with
    | hyp i => match (Nat.eq_dec n i)  with 
                 | left _ => s n
                 | right _ => hyp i
               end
    | app M N => app (subst_aux M n s) (subst_aux N n s)
    | lam A M => lam A (subst_aux M (S n) (shift_seq ( lift_seq s)))
  end.

Definition subst P s := subst_aux P 0 s.

Definition subs P Q := subst_aux P 0 (fun k : nat => 
match k with | 0 => Q | S _ => hyp 0 end).

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
  | E_beta : forall A t s,
      STT_equiv (app (lam A t) s) (subs t s)
  | E_eta : forall t A,
      STT_equiv (lam A (app t (hyp 0))) t.

Notation "t ≡ s" := (STT_equiv t s) (at level 45, left associativity).

