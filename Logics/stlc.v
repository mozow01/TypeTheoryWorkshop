Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Uni : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.
  
  (* Γ ⊢ p : A, 
  
  x : C ⊢ p : A ,  ⊢ lambda x:C.p : C → A *)
  
Inductive Trm : Set :=
  | uni : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.
  
Definition Cntxt := list Typ.

Print list_rect.


Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_uni : forall Γ, Tyty Γ uni Uni
  | STT_hyp0 : forall Γ A, Tyty (A :: Γ) (hyp 0) A
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


Lemma problem_1 : forall A : Prop, A -> A.
Proof.
intro A. 
intro x.
exact x.
Show Proof.
Qed. 

(* 

x: A ⊢ x [:] A              ;   A ⊢ hyp 0 [:] A 
------------------          ; 
 x: A ⊢ ? [:] A             ;
-----------------------     ;  
 ⊢ ? [:] (A ⊃ A)            ;     ⊢ lam A (hyp 0) [:] (A ⊃ A)

  *)

Lemma indentity : forall A : Typ, exists t, ⊢ t [:] (A ⊃ A).
Proof.
intros.
exists (lam A (hyp 0)).
apply STT_lam.
apply STT_hyp0.
Qed.

Lemma problem_2 : forall A B C : Prop, (A -> B) -> ((B -> C) -> (A -> C)).
Proof.
intros A B C. 
intro x.
intro y.
intro z.
apply y.
apply x.
exact z.
Show Proof.
Qed. 

(* 
            z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 2 [:] A ⊃ B   z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 0 [:] A   
                              -------------------------------------------------------------------------
z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ hyp 1 [:] B ⊃ C    z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ app (hyp 2) (hyp 0) [:] B            
-------------------------------------------------------------------------------
z: A, y: (B ⊃ C), x: (A ⊃ B) ⊢ app (hyp 1) (app (hyp 2) (hyp 0)) [:] C       ;  
------------------------------------------------------
y: (B ⊃ C), x: (A ⊃ B) ⊢ (lam A (app (hyp 1) (app (hyp 2) (hyp 0)))) [:] (A ⊃ C)           ;  
------------------          ; 
 x: (A ⊃ B) ⊢ ? [:] (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0))))) ((B ⊃ C) ⊃ (A ⊃ C))       ;
-----------------------     ;  
 ⊢ (lam (A ⊃ B)  (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0)))))) [:] ((A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))     ;     ⊢ lam A (hyp 0) [:] (A ⊃ A)

  *)

Lemma chain : forall A B C : Typ, exists t, ⊢ t [:] ((A ⊃ B) ⊃ ((B ⊃ C) ⊃ (A ⊃ C))).
Proof.
intros.
exists ((lam (A ⊃ B)  (lam (B ⊃ C) (lam A (app (hyp 1) (app (hyp 2) (hyp 0))))))).
apply STT_lam.
apply STT_lam.
apply STT_lam.
apply STT_app with (A:=B).
apply STT_hypS.
apply STT_hyp0.
apply STT_app with (A:=A).
apply STT_hypS.
apply STT_hypS.
apply STT_hyp0.
apply STT_hyp0.
Qed.

(*HF*)

Lemma vex : forall A B : Typ, exists t, ⊢ t [:] (A ⊃ (B ⊃ A)).
Proof.


      
