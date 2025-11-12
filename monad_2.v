Class Category := mk_cat {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  Id : forall x : Obj, Hom x x;
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

Class CartClosed {C : Category} := {

(* terminal *)

  Terminal_obj : Obj;

  Terminal_mor : forall {x}, x → Terminal_obj;
 
  unique_terminal : forall {x} (f : x → Terminal_obj), f = Terminal_mor;

(* initial *)

  Initial_obj : Obj;

  Initial_mor : forall {x}, Initial_obj → x;

  unique_initial : forall {x} (f : Initial_obj → x), f = Initial_mor;

(* product *)
 (*           pr_1                 pr_2
     A_1 <----------- A_1 x A_2 -------------> A_2
          \              /|\              /
         f_1  \  f_1 x f_2|           /   f_2
                 \        |    /
                          C                            *)

  Prod_obj : Obj -> Obj -> Obj;

  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;

  pr_1 {x y} : (Prod_obj x y) → x;
  pr_2 {x y} : (Prod_obj x y) → y;

  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) = f) /\ (pr_2 ∘ (Prod_mor f g) = g);
    
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (pr_1 ∘ g) (pr_2 ∘ g) = g;

(* exponential *)
(* C                     C x A
     |                       |    \ 
     | λ f          λf ∏ Id_A|            \ f
    \|/                     \|/                    \
     B^A                 B^A x A ----------------------> B 
                                         eval                      *)

  Exp_obj : Obj -> Obj -> Obj;

  Ev: forall {y z}, (Prod_obj (Exp_obj z y) y) → z;

  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
    Ev ∘ (Prod_mor ((Lam g) ∘ pr_1) ((Id y) ∘ pr_2)) = g;
  
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Ev ∘ (Prod_mor (h ∘ pr_1) ((Id y) ∘ pr_2))) = h

}.


Notation "⊤" := (Terminal_obj) (at level 40, no
associativity) : type_scope.

Notation "〇" := (Initial_obj) (at level 40, no associativity) : type_scope.

(* product: \prod *)
Notation "f '∏' g" := (Prod_mor f g) (at level 40, no associativity) : type_scope.

(* torii: \Pi *)
Notation "h 'Π' k" := (Prod_mor (h ∘ pr_1) (k ∘ pr_2)) (at level 40, no associativity) : type_scope.


Notation "x × y" := (Prod_obj x y) (at level 40, left associativity) :
type_scope. 

Notation "x 'e↑' y" := (Exp_obj x y) (at level 80, right associativity) :
type_scope.

Lemma prod_ax_1 {C : Category} {CC : CartClosed} : forall {x y z} (f : x → y) (g : x → z), 
    (pr_1 ∘ (Prod_mor f g) = f).
Proof.
intros.
apply prod_ax.
Defined.

Lemma prod_ax_2 {C : Category} {CC : CartClosed} : forall {x y z} (f : x → y) (g : x → z),
   (pr_2 ∘ (Prod_mor f g) = g).
Proof.
intros.
apply prod_ax.
Defined.

Theorem unique_prod {C : Category} {CC : @CartClosed C} : forall x y z (f1 : x → y) (f2 : x → z) (g : x → Prod_obj y z),
    ((pr_1 ∘ g) = f1) /\ ((pr_2 ∘ g) = f2) ->  Prod_mor f1 f2 = g.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H1; rewrite <- H2.
apply prod_eq.
Defined.

Theorem compos_prod {C : Category} {CC : @CartClosed C} : forall x y z w (f : w → y ) (g : w → z ) (h : x → w),
  (f ∘ h) ∏ (g ∘ h) = ( f ∏ g ) ∘ h.
Proof.
intros.
apply unique_prod.
split.
assert (H:pr_1 ∘ (f ∏ g ∘ h) = pr_1 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_1 ∘ (f ∏ g)=f).
apply prod_ax.
rewrite K.
auto.
assert (H: pr_2 ∘ ((f ∏ g) ∘ h) = pr_2 ∘ (f ∏ g) ∘ h).
apply assoc.
rewrite H.
assert (K:pr_2 ∘ (f ∏ g)=g).
apply prod_ax.
rewrite K.
auto.
Defined.


Class CovariantFunctor (C : Category) (D : Category) := mk_Functor {
  F_Obj : @Obj C -> @Obj D;
  F_Hom : forall (x y : @Obj C), (x → y) -> (F_Obj x → F_Obj y);
  F_id : forall (x : @Obj C), F_Hom x x (Id x) = Id (F_Obj x);
  F_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    F_Hom x z (g ∘ f) = (F_Hom y z g) ∘ (F_Hom x y f);
}.


Lemma pr_and_id {C : Category} {CC : @CartClosed C} : forall (A B : @Obj C), Id (A × B) = pr_1 ∏ pr_2.
Proof.
intros.
assert (H : (pr_1 ∘ (Id (A × B))) ∏ (pr_2 ∘ (Id (A × B))) = pr_1 ∏ pr_2).
rewrite id_1.
symmetry.
rewrite id_1.
reflexivity.
rewrite <- H.
symmetry.
rewrite prod_eq.
reflexivity.
Defined.


Instance ProdFunctor {C : Category} {CC : @CartClosed C} (A : @Obj C) : CovariantFunctor C C.
Proof.
(*Nem biztos, de próba szerencse, ki kell találni a morfizmust!*)
apply mk_Functor with (F_Obj := fun X => X × A) (F_Hom := fun x y f => (f ∘ pr_1) ∏ pr_2).
 - intros X.
   rewrite id_2.
   rewrite pr_and_id.
   reflexivity.
 - intros X Y Z g f.
   apply unique_prod.
   split.
   + rewrite assoc. rewrite prod_ax_1. rewrite <- assoc. rewrite prod_ax_1. rewrite assoc. reflexivity.
   + rewrite assoc. rewrite prod_ax_2. rewrite prod_ax_2. reflexivity.
Defined.


Lemma prod_id {C: Category} {CC : @CartClosed C} (X Y Z A: @Obj C) : forall (f: X → Y) (g: Y → Z),
    (g Π (Id A)) ∘ (f Π (Id A)) = (g ∘ f) Π (Id A).
Proof. intros. assert ( H1:   pr_1 ∘ (g Π Id A ∘ (f Π Id A)) = pr_1 ∘ ((g ∘ f) Π Id A)). {
  rewrite prod_ax_1. rewrite assoc. rewrite prod_ax_1. rewrite <- assoc. 
   rewrite prod_ax_1. rewrite assoc. reflexivity. }
assert ( H2:  pr_2 ∘ (g Π Id A ∘ (f Π Id A)) = pr_2 ∘ ((g ∘ f) Π Id A) ). {
  rewrite prod_ax_2. rewrite assoc. rewrite prod_ax_2. 
  symmetry. rewrite <- assoc. rewrite prod_ax_2. rewrite id_2. rewrite id_2. reflexivity. }
symmetry. apply unique_prod. split.
-rewrite H1. rewrite prod_ax_1. reflexivity.
-rewrite H2. rewrite prod_ax_2. reflexivity. 
Defined.



Instance ExpFunctor {C : Category} {CC : @CartClosed C} (A : @Obj C) : CovariantFunctor C C.
Proof.
(*Nem biztos, de próba szerencse, ki kell találni a morfizmust!*)
apply mk_Functor with (F_Obj := fun X => X e↑ A)
(F_Hom := fun x y f => Lam (f ∘ Ev)).
-intros. rewrite id_2. assert (H: Lam (Ev ∘ (Prod_mor (Id (Exp_obj x A) ∘ pr_1) ((Id A) ∘ pr_2))) = Id (Exp_obj x A) ). {
  apply unique_exp. }
rewrite <- H. rewrite id_2. rewrite id_2. rewrite <- pr_and_id. rewrite id_1. reflexivity.
-intros. assert (H: g ∘ (Ev ∘  ( Prod_mor (Lam ( f ∘ Ev ) ∘ pr_1) (Id A ∘ pr_2))) = g ∘ (f ∘ Ev )). {
  rewrite exp_ax. reflexivity. }
rewrite <- assoc. rewrite <- H. rewrite assoc. assert (H1 : (g ∘ Ev ∘ (Lam (f ∘ Ev) Π Id A)) = Ev ∘ ( Lam ( g ∘ Ev) Π Id A) ∘ (Lam ( f ∘ Ev) Π Id A )). {
  rewrite exp_ax. reflexivity. }
rewrite  H1. rewrite <- assoc. rewrite prod_id. rewrite unique_exp. reflexivity. Defined.



Class IsLeftAdjoint  (C D : Category) (F : CovariantFunctor D C) := mk_IsLeftAdjoint {

  rightadjobj : @Obj C -> @Obj D;
  epsilon : forall (X : @Obj C), (@F_Obj D C F (rightadjobj X)) → X;
  rightadjmor : forall {Y : @Obj D} {X : @Obj C} (f : (@F_Obj D C F Y) → X), Y → (rightadjobj X);

  lambek_1 : forall {Y X} (f : (@F_Obj D C F Y) → X),
    (epsilon X) ∘ (@F_Hom D C F _ _ (rightadjmor f)) = f;
  lambek_2 : forall {Y X} (h : Y → (rightadjobj X)),
    rightadjmor ((epsilon X) ∘ (@F_Hom D C F _ _ h)) = h}.


Class IsRightAdjoint {C D : Category} (G : CovariantFunctor C D) := mk_IsRightAdjoint {
  leftadjobj : @Obj D -> @Obj C;
  unit : forall (Y : @Obj D), Y → (@F_Obj C D G (leftadjobj Y));
  leftadjmor : forall {Y : @Obj D} {X : @Obj C} (g : Y → (@F_Obj C D G X)), (leftadjobj Y) → X;

  lambek_1_dual : forall {Y : @Obj D} {X : @Obj C} (g : Y → (@F_Obj C D G X)),
    (@F_Hom C D G _ _ (leftadjmor g)) ∘ (unit Y) = g;
  lambek_2_dual : forall {Y : @Obj D} {X : @Obj C} (f : (leftadjobj Y) → X),
    leftadjmor ((@F_Hom C D G _ _ f) ∘ (unit Y)) = f
}.

Instance RightAdjFunc (C D : Category) (F : CovariantFunctor D C) (FLAdj : IsLeftAdjoint C D F) :
   CovariantFunctor C D.
Proof.
apply mk_Functor with (F_Obj := @rightadjobj C D F FLAdj)
      (F_Hom := fun X1 X2 f => @rightadjmor C D F FLAdj (rightadjobj X1)
X2 (f ∘ epsilon X1 )).
  - intros X.
    rewrite id_2.
    assert (H: rightadjmor ((epsilon X) ∘ (F_Hom (rightadjobj X) (rightadjobj X) (Id (rightadjobj X)))) = Id (rightadjobj X)).
    apply lambek_2.
    assert (K: F_Hom (rightadjobj X) (rightadjobj X) (Id (rightadjobj X)) = Id (F_Obj (rightadjobj X))). { rewrite F_id; reflexivity. }
    rewrite K in H.
    clear K.
    rewrite id_1 in H.
    exact H.
  - intros X1 X2 X3 g f.
    rewrite <- (lambek_2).
    apply f_equal.
    rewrite F_comp.
    rewrite assoc.
    rewrite lambek_1.
    replace (g ∘ epsilon X2 ∘ F_Hom (rightadjobj X1) (rightadjobj X2) (rightadjmor (f ∘ epsilon X1)))
    with (g ∘ (epsilon X2 ∘ F_Hom (rightadjobj X1) (rightadjobj X2) (rightadjmor (f ∘ epsilon X1)))).
    2: { rewrite assoc; reflexivity. }
    rewrite lambek_1.
    rewrite <- assoc.
    reflexivity.
Defined.

Instance LeftAdjFunc (C D : Category) (F : CovariantFunctor D C) (FRAdj : IsRightAdjoint F) :
   CovariantFunctor C D.
Proof.
apply mk_Functor with (F_Obj := @leftadjobj D C F FRAdj)
      (F_Hom := fun X1 X2 f => @leftadjmor D C F FRAdj X1
( leftadjobj X2) ( (unit X2 ) ∘ f)).
  - intros.
    rewrite id_1.
    assert (H: leftadjmor ( (F_Hom (leftadjobj x) (leftadjobj x) (Id (leftadjobj x))) ∘ unit x) = Id (leftadjobj x)).
    apply lambek_2_dual.
    assert (K: F_Hom (leftadjobj x) (leftadjobj x) (Id (leftadjobj x)) = Id (F_Obj (leftadjobj x))). { rewrite F_id; reflexivity. }
    rewrite K in H.
    clear K.
    rewrite id_2 in H.
    exact H.
  - intros.
    rewrite <- lambek_2_dual.
    apply f_equal.
    rewrite F_comp.
    rewrite <- assoc.
    rewrite lambek_1_dual.
    replace (F_Hom (leftadjobj y) (leftadjobj z) (leftadjmor (unit z ∘ g)) ∘ (unit y ∘ f)) with
    ((F_Hom (leftadjobj y) (leftadjobj z) (leftadjmor (unit z ∘ g)) ∘ unit y) ∘ f).
    2: { rewrite assoc; reflexivity. }
    rewrite lambek_1_dual.
    rewrite <- assoc.
    reflexivity.
Defined.
    
    

Class Monad {C : Category} (M : CovariantFunctor C C) := mk_monad {
  return_op : forall {A}, (A → @F_Obj C C M A);
  join_op : forall {A}, (@F_Obj C C M (@F_Obj C C M A) → @F_Obj C C M A);

  monad_law_left_unit : forall {A},
    (@join_op A) ∘ (@F_Hom C C M _ _ (@return_op A)) = Id (@F_Obj C C M A);

  monad_law_right_unit : forall {A},
    (@join_op A) ∘ (@return_op (@F_Obj C C M A)) = Id (@F_Obj C C M A);

  monad_law_assoc : forall {A},
    (@join_op A) ∘ (@F_Hom C C M _ _ (@join_op A)) = (@join_op A) ∘ (@join_op (@F_Obj C C M A))
}.

Class Comonad {C : Category} (W : CovariantFunctor C C) := mk_comonad {
  extract : forall {A}, (@F_Obj C C W A → A);
  duplicate : forall {A}, (@F_Obj C C W A → @F_Obj C C W (@F_Obj C C W A));

  comonad_law_left_unit : forall {A},
    (@F_Hom C C W _ _ (@extract A)) ∘ (@duplicate A) = Id (@F_Obj C C W A);

  comonad_law_right_unit : forall {A},
    (@extract (@F_Obj C C W A)) ∘ (@duplicate A) = Id (@F_Obj C C W A);

  comonad_law_assoc : forall {A},
    (@F_Hom C C W _ _ (@duplicate A)) ∘ (@duplicate A) = (@duplicate (@F_Obj C C W A)) ∘ (@duplicate A)
}.




Class Monad_Bind_Style {Cat : Category} (M : CovariantFunctor Cat Cat) := mk_Monad_Bind_Style {
  return_b : forall {A}, (A → @F_Obj Cat Cat M A);
  bind_b : forall {A B}, (A → @F_Obj Cat Cat M B) -> (@F_Obj Cat Cat M A → @F_Obj Cat Cat M B);
  bind_law1 : forall {A B} (f : A → @F_Obj Cat Cat M B), (bind_b f) ∘ return_b = f;
  bind_law2 : forall {A}, bind_b (@return_b A) = Id _;
  bind_law3 : forall {A B C} (f : A → @F_Obj Cat Cat M B) (g : B → @F_Obj Cat Cat M C),
    (bind_b g) ∘ (bind_b f) = bind_b ( (bind_b g) ∘ f )
}.

Class CoMonad_Extend_Style {Cat : Category} (W : CovariantFunctor Cat Cat) := mk_CoMonad_Extend_Style {
  extract_b : forall {A}, (@F_Obj Cat Cat W A → A);
  extend_b : forall {A B}, (@F_Obj Cat Cat W B →  A) -> (@F_Obj Cat Cat W B → @F_Obj Cat Cat W A);
  extend_law1: forall {A B} (f : @F_Obj Cat Cat W B → A), extract_b ∘ (extend_b f)  = f;
  extend_law2: forall {A}, extend_b (@extract_b A) = Id _;
  extend_law3: forall {A B C} (f : @F_Obj Cat Cat W C → B) (g :  @F_Obj Cat Cat W B → A),
    (extend_b g) ∘ (extend_b f) = extend_b ( g ∘ ( extend_b f ))
}.

Definition bind_from_join {Cat : Category} {M : CovariantFunctor Cat Cat} {MJ : Monad M} {A B}
  (f : A → @F_Obj Cat Cat M B) : (@F_Obj Cat Cat M A → @F_Obj Cat Cat M B) :=
  (@join_op Cat M MJ B) ∘ (@F_Hom Cat Cat M A (@F_Obj Cat Cat M B) f).

Definition join_from_bind {Cat : Category} {M : CovariantFunctor Cat Cat}  {MB : Monad_Bind_Style M} {A}
  : (@F_Obj Cat Cat M (@F_Obj Cat Cat M A) → @F_Obj Cat Cat M A) :=
  @bind_b Cat M MB (@F_Obj Cat Cat M A) A (Id (@F_Obj Cat Cat M A)).


Instance Join_Implies_Bind {Cat : Category} {M : CovariantFunctor Cat Cat} (MJ : Monad M) : Monad_Bind_Style M.
Proof.
Abort.

Instance Bind_Implies_Join {Cat : Category} {M : CovariantFunctor Cat Cat} (MB : Monad_Bind_Style M) : Monad M.
Proof.
Abort.

Definition ComposeFunctors {C D E : Category}
  (F : CovariantFunctor C D) (G : CovariantFunctor D E) : CovariantFunctor C E.
Proof.
  apply (mk_Functor C E) with
    (F_Obj := fun x => @F_Obj D E G (@F_Obj C D F x))
    (F_Hom := fun x y f => @F_Hom D E G _ _ (@F_Hom C D F x y f)).
  - intros; simpl; rewrite F_id, F_id; reflexivity.
  - intros; simpl; rewrite F_comp, F_comp; reflexivity.
Defined.


(* Ez kéne valahogy*)
Instance AdjFuncMonad (C D : Category) (F : CovariantFunctor C D) (G_adj: IsRightAdjoint F): Monad_Bind_Style (ComposeFunctors (LeftAdjFunc D C F G_adj) F).
Proof.
  (* We apply the constructor for the Monad_Bind_Style class. *)
  apply mk_Monad_Bind_Style with

  (* 1. Define the return operation *)
  (return_b := fun (A : @Obj D) =>
    (* `return` is the monad unit `η`, which is directly the `unit` of the adjunction. *)
    @unit C D F G_adj A)

  (* 2. Define the bind operation *)
  (bind_b := fun (A B : @Obj D) (f : A → @F_Obj D D (ComposeFunctors (LeftAdjFunc D C F G_adj) F) B) =>
    @F_Hom C D F _ _ (@leftadjmor C D F G_adj A (@F_Obj D C (LeftAdjFunc D C F G_adj) B) f)).
(* The next steps would be to prove the three bind laws using the adjunction axioms. *)
- intros. (* bind_law1 *)
  apply @lambek_1_dual with (Y:=A)(X:=F_Obj B)(g:=f).
- intros. (* bind_law2 *)
  rewrite <- F_id. simpl. 
  rewrite id_1. 
  reflexivity. 
- intros X Y Z f g. (* bind_law3 *) 
  simpl.
  rewrite <- F_comp.
  f_equal.
  symmetry. 
  rewrite <- lambek_2_dual.
  apply f_equal.
  rewrite F_comp.
  rewrite <- assoc.
  rewrite lambek_1_dual.
  reflexivity.
Defined.
  

Instance AdjFuncCoMonad (C D : Category) (G : CovariantFunctor C D) (F_adj: IsLeftAdjoint D C G): CoMonad_Extend_Style (ComposeFunctors (RightAdjFunc D C G F_adj) G).
Proof.
  apply mk_CoMonad_Extend_Style with

  (* 1. Define the extract operation (Comonad Counit ε) *)
  (extract_b := fun (A : @Obj D) =>
    (* `extract` is the comonad counit `ε`, which is directly the `epsilon`
       field of the IsLeftAdjoint adjunction class. *)
    @epsilon D C G F_adj A)

  (* 2. Define the extend operation *)
  (extend_b := fun (A B : @Obj D) (f : @F_Obj D D (ComposeFunctors (RightAdjFunc D C G F_adj) G) B → A) =>
    (* `extend f` is dual to `bind f`. It is constructed in two steps:
       1. Use `rightadjmor` to map `f : G(F(B)) → A` to `f' : F(B) → F(A)`.
       2. Apply the functor `G` to `f'` to get the final morphism `G(f') : G(F(B)) → G(F(A))`. *)
    @F_Hom C D G _ _ (@rightadjmor D C G F_adj (@F_Obj D C (RightAdjFunc D C G F_adj) B) A f)).
  -intros. (* extend_law1 *)
  apply @lambek_1 with ( X := A) (Y := F_Obj B).
  -intros. (* extend_law2 *)
  rewrite <- F_id. 
  simpl. 
  rewrite id_2. 
  reflexivity.
  -intros X Y Z f g. (* extend_law3 *) 
  simpl.
  rewrite <- F_comp.
  f_equal.
  symmetry. 
  rewrite <- lambek_2.
  apply f_equal.
  rewrite F_comp.
  rewrite assoc.
  rewrite lambek_1.
  reflexivity.
Defined.
  