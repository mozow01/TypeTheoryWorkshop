Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;
}.

Notation "x → y" := (Hom x y) (at level 70, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 71, left associativity) :
type_scope.

Class CartClosedCat (C : Category) := CartClosedCat_mk {
  (* 1 *)
  Termi_obj : Obj;
  Termi_mor : forall {x}, x → Termi_obj;
  unique_top : forall {x} (f : x → Termi_obj), f = Termi_mor;
  
  (* × *)
  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;

  (*           First              Second
     A_1 <----------- A_1 x A_2 -------------> A_2
          \               |               /
         f_1  \  f_1 x f_2|           /   f_2
                 \       \|/    /
                          C                            *)
  prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), 
    ((First ∘ (Prod_mor f g)) = f);
  prod_ax_2 : forall {x y z} (f : x → y) (g : x → z),((Second ∘ (Prod_mor f g)) = g);
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y z),
    ((First ∘ h) = f) /\ ((Second ∘ h) = g) -> h = (Prod_mor f g);
  
  (* ^ *)
  Exp_obj : Obj -> Obj -> Obj;
  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);
  
  (* C                     C x A
     |                       |    \ 
     | λ f          λf ∏ Id_A|            \ f
    \|/                     \|/                    \
     B^A                 B^A x A ----------------------> B 
                                         eval                      *)
  exp_ax : forall {x y z} (g : ((Prod_obj x y) → z)), 
    (Exp_app ∘ (Prod_mor ((Lam g) ∘ First) ((Id y) ∘ Second))) = g;
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (h ∘ First) ((Id y) ∘ Second))) = h
}.

Infix "x × y" := (Prod_obj x y) (at level 80, right associativity).

Infix "x ∏ y" := (Prod_obj x y) (at level 80, right associativity). (* product; \prod *)

Notation "1" := (Termi_obj) (at level 70, right associativity) :
type_scope.

Notation "! x" := (Termi_mor x) (at level 71, left associativity) :
type_scope.


Definition Isomophism {C : Category} {A B : Obj} (f : Hom A B) := (exists g : Hom B A, ((f ∘ g) = Id B ) /\ ((g ∘ f) = Id A )). 








