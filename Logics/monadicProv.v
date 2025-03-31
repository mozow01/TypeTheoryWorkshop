(*SOGAT monadic provability

SOGAT = second order generalized algebraic theory

second order = use of (one order) functions like (Pf A -> Pf B) 
generalized = use of more than one universe set (Fm : Type; Pf : Fm -> Type)
algebraic = universe + operators + equalities

*)

Class monProv := mk_monProv {
  (*sorts*)
  Fm : Type;
  Pf : Fm -> Type;
  
  (*operations*)
  Tru : Fm;
  Fal : Fm;
  Imp : Fm -> Fm -> Fm;
  Cnj : Fm -> Fm -> Fm;
  Dis : Fm -> Fm -> Fm;

  (*more operations*)
  tru : Pf Tru;
  fal : forall A : Fm, Pf Fal -> Pf A;
  lam : forall A B : Fm, (Pf A -> Pf B) -> Pf (Imp A B);
  app : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B;
  pr1 : forall A B : Fm, Pf (Cnj A B) -> Pf A;
  pr2 : forall A B : Fm, Pf (Cnj A B) -> Pf B;
  cnj : forall A B : Fm, Pf A -> Pf B -> Pf (Cnj A B);
  in1 : forall A B : Fm, Pf A -> Pf (Dis A B);
  in2 : forall A B : Fm, Pf B -> Pf (Dis A B);
  dis : forall A B C : Fm, (Pf A -> Pf C) -> (Pf B -> Pf C) -> Pf (Dis A B) -> Pf C; 
  
  (*equalities -- optional :) *)
  beta : forall A B F p, (app A B) (lam A B F) p = F p;
  eta : forall A B f, lam A B (app A B f) = f; 

  beta_cnj1 : forall A B p q, (pr1 A B) (cnj A B p q) = p;
  beta_cnj2 : forall A B p q, (pr2 A B) (cnj A B p q) = q;
  eta_cnj : forall A B c, cnj A B (pr1 A B c) (pr2 A B c) = c;

  beta_dis1 : forall A B p q, (pr1 A B) (cnj A B p q) = p;
  beta_dis2 : forall A B p q, (pr2 A B) (cnj A B p q) = q;
  eta_dis : forall A B C (H : Pf (Dis A B) -> Pf C), 
     dis A B C (fun x => H (in1 A B x)) (fun x => H (in2 A B x)) = H;
}.

Example Currying {P : monProv} : forall A B C : Fm, (Pf A -> Pf B -> Pf C) -> (Pf (Cnj A B) -> Pf C).
Proof.
intros.
apply X.
apply pr1 with (A:=A) (B:=B).
exact X0. 
apply pr2 with (A:=A) (B:=B).
exact X0.
Qed. 

Example Currying2 {P : monProv} : forall A B C : Fm, Pf (Imp A (Imp B C)) -> Pf (Imp (Cnj A B) C).
Proof.
intros.
apply lam.
intros.
assert (K1 : Pf A).
apply pr1 in X0.
auto.
assert (K2 : Pf B).
apply pr2 in X0.
auto.
assert (H : Pf (Imp B C)).
apply app with (A:=A) (B:=Imp B C).
all: try auto.
apply app with (A:=B) (B:=C).
all: try auto.
Qed. 

(*A^BA^C=A^(B+C) #1*)
Example CnjDisImp1 {P : monProv} : forall A B C : Fm, Pf (Cnj (Imp B A) (Imp C A)) -> Pf (Imp (Dis B C) A).
Proof.
intros.
apply lam.
intros.
assert (K1 : Pf (Imp B A)).
apply pr1 in X.
auto.
assert (K2 : Pf (Imp C A)).
apply pr2 in X.
auto.
apply dis with (A:=B) (B:=C) (C:=A).
all: try intros. 
apply app with (A:=B) (B:=A).
all: try auto.
apply app with (A:=C) (B:=A).
all: try auto.
Qed. 

(*A^BA^C=A^(B+C) #2*)
Example CnjDisImp2 {P : monProv} : forall A B C : Fm, Pf (Imp (Dis B C) A) -> Pf (Cnj (Imp B A) (Imp C A)).
Proof.
Abort. 

