
Polymorphic Class Category @{o h} := mk_cat {
  Obj : Type@{o};
  Hom : Obj -> Obj -> Type@{h};
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

Class ContravariantFunctor (C : Category) (D : Category) := mk_ContraFunctor {
  CoF_Obj : @Obj C -> @Obj D;
  CoF_Hom : forall (x y : @Obj C), @Hom C x y -> @Hom D (CoF_Obj y) (CoF_Obj x);
  CoF_id : forall (x : @Obj C), (@CoF_Hom x x (@Id C x)) = (@Id D (@CoF_Obj x));
  CoF_comp : forall (x y z : @Obj C) (f : @Hom C y z) (g : @Hom C x y), (@CoF_Hom x z (@Compose C _ _ _ f g)) =
    (@Compose D _ _ _ (@CoF_Hom x y g) (@CoF_Hom y z f));
}.
 

Class NaturalTransformation (C : Category) (D : Category) (F G : ContravariantFunctor C D) := mk_NatTrans {
  trans_mor : forall (x : @Obj C), @Hom D ((@CoF_Obj C D F) x) ((@CoF_Obj C D G) x);
  naturality_square : forall (x y : @Obj C) (f : @Hom C x y),
    (@Compose D _ _ _ (trans_mor x) (@CoF_Hom C D F x y f)) =
    (@Compose D _ _ _ (@CoF_Hom C D G x y f) (trans_mor y))
}.

Definition IdNaturalTransformation (C D: Category) (F : ContravariantFunctor C D) : NaturalTransformation C D F F. 
Proof.
apply (mk_NatTrans C D F F) with 
      (trans_mor:=(fun (x : @Obj C) => @Id D (@CoF_Obj C D F x))).
      intros x y f.
      simpl.
      rewrite (@id_2 D _ _ (@CoF_Hom C D F x y f)).
      rewrite (@id_1 D _ _ (@CoF_Hom C D F x y f)).
      reflexivity.
Defined.

Definition ComposeNaturalTransformation (C D : Category)
           (F G H : ContravariantFunctor C D)
           (theta : NaturalTransformation C D G H)
           (eta : NaturalTransformation C D F G)
           : NaturalTransformation C D F H.
Proof.
  apply (mk_NatTrans C D F H) with
    (trans_mor := fun x => @Compose D _ _ _ (theta.(trans_mor) x) (eta.(trans_mor) x)).
  intros x y f.
  rewrite assoc.
  rewrite <- naturality_square.
  rewrite <- assoc.
  rewrite naturality_square.
  rewrite assoc.
  reflexivity.
Defined.

Class CovariantFunctor (C : Category) (D : Category) := mk_Functor {
  F_Obj : @Obj C -> @Obj D;
  F_Hom : forall (x y : @Obj C), (x → y) -> (F_Obj x → F_Obj y);
  F_id : forall (x : @Obj C), F_Hom x x (Id x) = Id (F_Obj x);
  F_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    F_Hom x z (g ∘ f) = (F_Hom y z g) ∘ (F_Hom x y f);
}.

Class NaturalTransformationCov (C : Category) (D : Category) (F G : CovariantFunctor C D) := mk_NatTransCoV {
  trans_mor_Cov : forall (x : @Obj C), @Hom D ((@F_Obj C D F) x) ((@F_Obj C D G) x);
  naturality_square_Cov : forall (x y : @Obj C) (f : @Hom C x y),
    (@Compose D _ _ _ (@F_Hom C D G x y f) (trans_mor_Cov x) ) =
    (@Compose D _ _ _ (trans_mor_Cov y) (@F_Hom C D F x y f) )
}.

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
  leftadjmor : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)), (leftadjobj X) → Y;

  lambek_1_dual : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)),
    (@F_Hom C D G _ _ (leftadjmor g)) ∘ (unit X) = g;
  lambek_2_dual : forall {X : @Obj D} {Y : @Obj C} (f : (leftadjobj X) → Y),
    leftadjmor ((@F_Hom C D G _ _ f) ∘ (unit X)) = f
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

Definition ComposeFunctors {C D E : Category}
  (F : CovariantFunctor C D) (G : CovariantFunctor D E) : CovariantFunctor C E.
Proof.
  apply (mk_Functor C E) with
    (F_Obj := fun x => @F_Obj D E G (@F_Obj C D F x))
    (F_Hom := fun x y f => @F_Hom D E G _ _ (@F_Hom C D F x y f)).
  - intros; simpl; rewrite F_id, F_id; reflexivity.
  - intros; simpl; rewrite F_comp, F_comp; reflexivity.
Defined.

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
  apply @lambek_1_dual with (X:=A)(Y:=F_Obj B)(g:=f).
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

Definition IdentityFunctor (C : Category) : CovariantFunctor C C.
Proof.
  apply mk_Functor with
    (F_Obj := fun x => x)
    (F_Hom := fun _ _ f => f).
  - intros; reflexivity.
  - intros; reflexivity.
Defined.

(*Indexed Category plus pushforwards*)


Class GoodFibration (B : Category) := mk_GoodFibration {
  Fiber : @Obj B -> Category;
  Fiber_is_CCC : forall I : @Obj B, @CartClosed (Fiber I);

  Pullback {I J} : (I → J) -> CovariantFunctor (Fiber J) (Fiber I);

  pullback_preserves_id {I} :
    Pullback (Id I) = IdentityFunctor (Fiber I);

  pullback_preserves_comp {I J K} (g : J → K) (f : I → J) :
    Pullback (g ∘ f) = ComposeFunctors (Pullback g) (Pullback f); 

  pullback_has_left_adjoint {I J} (f : I → J) :
    @IsRightAdjoint (Fiber J) (Fiber I) (Pullback f);

  pullback_has_right_adjoint {I J} (f : I → J) :
    @IsLeftAdjoint (Fiber I) (Fiber J) (Pullback f)
}.


Definition Sigma_f {B} {LF : GoodFibration B} {I J} (f : I → J)
  : CovariantFunctor (Fiber I) (Fiber J).
Proof.
  pose proof (@pullback_has_left_adjoint B LF I J f) as adj_proof.
  exact (LeftAdjFunc (Fiber I) (Fiber J) (Pullback f) adj_proof).
Defined.

Definition Pi_f {B} {LF : GoodFibration B} {I J} (f : I → J)
  : CovariantFunctor (Fiber I) (Fiber J).
Proof.
  pose proof (@pullback_has_right_adjoint B LF I J f) as adj_proof.
  exact (RightAdjFunc (Fiber I) (Fiber J) (Pullback f) adj_proof).
Defined.

Class TwoSortCategory (B : Category) := mk_TwoSortCategory {
  One : @Obj B;
  terminal_mor : forall X, X → One;
  terminal_mor_unique : forall X (f : X → One), f = terminal_mor X;
  S : @Obj B;
  S_is_not_Terminal : S <> One
}.

Definition bang (B : Category) (TSC : TwoSortCategory B) : Hom S One :=
  terminal_mor S.


Definition ExistsQuantifier (B : Category) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : CovariantFunctor (Fiber S) (Fiber One).
Proof.
 exact (Sigma_f (bang B TSC)). 
Defined.

Definition ForallQuantifier (B : Category) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : CovariantFunctor (Fiber S) (Fiber One).
Proof.
  exact (Pi_f (bang B TSC)).
Defined.
