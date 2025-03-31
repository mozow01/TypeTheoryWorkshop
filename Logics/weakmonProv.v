(*Zero order logic
in weak SOGAT setup but inductive*)

Inductive Fm : Set :=
  | Tru : Fm
  | Imp : Fm -> Fm -> Fm
  | Cnj : Fm -> Fm -> Fm
  | Dis : Fm -> Fm -> Fm.

(*For all formula (type) there is a set of proof variables
of that type.*)
Parameter Pfvar : Fm -> Set.

(*Proofs of a formula or inhabitants of a type.*)
Inductive Pf : Fm -> Set := 
  | tt : Pf Tru
  | hyp : forall (A : Fm), (Pfvar A -> Pf A)
  | lam : forall (A B : Fm), (Pfvar A -> Pf B) -> Pf (Imp A B)
  | app : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B
  | cnj : forall (A B : Fm), Pf A -> Pf B -> Pf (Cnj A B)
  | pr1 : forall A B : Fm, Pf (Cnj A B) -> Pf A
  | pr2 : forall A B : Fm, Pf (Cnj A B) -> Pf B
  | in1 : forall (A B : Fm), Pf A -> Pf (Dis A B)
  | in2 : forall (A B : Fm), Pf B -> Pf (Dis A B)
  | dis : forall A B C : Fm, Pf (Dis A B) -> (Pfvar A -> Pf C) -> (Pfvar B -> Pf C) -> Pf C. 

Example Currying : forall A B C : Fm, (Pf A -> Pf B -> Pf C) -> (Pf (Cnj A B) -> Pf C).
Proof.
intros.
apply H.
apply pr1 with (A:=A) (B:=B).
exact H0. 
apply pr2 with (A:=A) (B:=B).
exact H0.
Qed.

Example Currying2 : forall A B C : Fm, Pf (Imp A (Imp B C)) -> Pf (Imp (Cnj A B) C).
Proof.
Abort.


