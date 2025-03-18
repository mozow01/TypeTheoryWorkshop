Parameter Invar : Set.

(*Extrm: formula former expressing that a term is constructivelly defined.*)
Inductive Fm : Set :=
  | Tru : Fm
  | Imp : Fm -> Fm -> Fm
  | Cnj : Fm -> Fm -> Fm
  | Exi : Fm -> Fm
  | Sub : Tm -> Fm -> Fm
  | Extrm : Tm -> Fm
with Tm : Set :=
  | Invarisatrm : Invar -> Tm
  | Eps : Fm -> Tm.

(*For all formula there is a set of proof variables
of that type.*)
Parameter Pfvar : Fm -> Set.

Inductive Pf : Fm -> Set := 
  | tt : Pf Tru
  | hyp : forall (A : Fm), (Pfvar A -> Pf A)
  | lam : forall (A B : Fm), (Pfvar A -> Pf B) -> Pf (Imp A B)
  | app : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B
  | andi : forall (A B : Fm), Pf A -> Pf B -> Pf (Cnj A B)
  | ande : forall A B C : Fm, Pf (Cnj A B) -> (Pfvar A -> Pfvar B -> Pf C) -> Pf C
  | exii : forall (A : Fm) (t : Tm), Pf (Extrm t) -> Pf (Sub t A) -> Pf (Exi A)
  | exie : forall (A C : Fm), Pf (Exi A) -> (forall x : Invar, Pfvar (Extrm (Invarisatrm x)) ->  Pfvar (Sub (Invarisatrm x) A) -> Pf C) -> Pf C
  | epsi : forall (A : Fm) (t : Tm), Pf (Extrm t) -> Pf (Sub t A) -> Pf (Sub (Eps A) A)
  | epse : forall (A C : Fm), Pf (Sub (Eps A) A) -> (forall x : Invar, Pfvar (Extrm (Invarisatrm x)) ->  Pfvar (Sub (Invarisatrm x) A) -> Pf C) -> Pf C
  | eps_const : forall (A : Fm), Pf (Extrm (Eps A))
  | sub_and1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Cnj A B)) -> Pf (Cnj (Sub t A) (Sub t B))
  | sub_and2 : forall (A B : Fm) (t : Tm), Pf (Cnj (Sub t A) (Sub t B)) -> Pf (Sub t (Cnj A B)) 
  | sub_imp1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Imp A B)) -> Pf (Imp (Sub t A) (Sub t B))
  | sub_imp2 : forall (A B : Fm) (t : Tm), Pf (Imp (Sub t A) (Sub t B)) -> Pf (Sub t (Imp A B))
  | sub_exi : forall (A : Fm) (t : Tm), Pf (Sub t (Exi A)) -> Pf (Exi A)
. 

Infix "⊃" := Imp (at level 80, right associativity). 

Infix "∧" := Cnj (at level 20, left associativity).
Lemma ex_eps : forall (A : Fm), Pf (Exi ( (Exi A) ⊃ A )).
Proof.
intros. 
apply exii with (t:=Eps A).
apply eps_const.
apply sub_imp2 with (A:=(Exi A)) (B:=A) (t:=Eps A).
apply lam.
intros.
apply hyp in H.
apply sub_exi in H.
apply exie with (C:=(Sub (Eps A) A)) in H.
auto.
intros.
apply hyp in H0, H1.
apply epsi with (t:=(Invarisatrm x)).
all: auto.
Qed.
