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


Class Category := cat_mk {
  Obj : Type;

  uHom := Type : Type;

  Hom : Obj -> Obj -> uHom;

  Id : forall x, Hom x x;

  Dom {x y} (f: Hom x y) := x;

  CoDom {x y} (f: Hom x y) := y;

  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);

  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;

  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;

}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Theorem monProv_is_a_cat (P : monProv) : Category.
Proof.
apply cat_mk with (Obj:=@Fm P) (Hom:=fun A B => @Pf P (Imp A B)).
