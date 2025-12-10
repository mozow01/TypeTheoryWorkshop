Require Import List.
Import ListNotations.

(** Kategória definíciója EqMor ekvivalenciarelációval  *)
Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z) -> (Hom x y) -> (Hom x z);
  
  (* Ekvivalenciareláció a morfizmusokon *)
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;
  
  (* Ekvivalencia tulajdonságok *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;
  
  (* Kongruencia és kategória axiómák *)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  eq_cong: forall {x y z} (f g: Hom y z) (h i : Hom x y), 
        EqMor f g -> EqMor h i -> EqMor (Compose f h) (Compose g i);
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≅ g" := (EqMor f g) (at level 40, no associativity) : type_scope.

(** CCC definíciója, amely illeszkedik az EqMor alapú kategóriához  *)
Class CartClosedCat (C : Category) := CartClosedCat_mk {
  Top_obj : Obj;
  Top_mor : forall {x}, x → Top_obj;
  
  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;
  
  Exp_obj : Obj -> Obj -> Obj;
  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);
  
  (* Egyenlőségek EqMor (≅) használatával *)
  unique_top : forall {x} (f : x → Top_obj), f ≅ Top_mor;
  prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), First ∘ (Prod_mor f g) ≅ f;
  prod_ax_2 : forall {x y z} (f : x → y) (g : x → z), Second ∘ (Prod_mor f g) ≅ g;
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y z), 
      ((First ∘ h) ≅ f) /\ ((Second ∘ h) ≅ g) -> h ≅ (Prod_mor f g);
  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), 
      Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) ≅ g;
  unique_exp : forall {x y z} (h : x → Exp_obj z y), 
      Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) ≅ h
}.

(* Szükséges könyvtárak a rewrite és setoid használatához *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

(* 1. Dekraláljuk az EqMor-t mint átíró relációt (Setoid) *)
Add Parametric Relation (C : Category) (x y : @Obj C) : (@Hom C x y) (@EqMor C x y)
  reflexivity proved by (@Eq_ref C x y)
  symmetry proved by (@Eq_sim C x y)
  transitivity proved by (@Eq_trans C x y)
  as eqmor_rel.

(* 2. Megtanítjuk a Coq-nak, hogy a kompozíció (Compose) mindkét oldalon 
      tiszteletben tartja az egyenlőséget (Proper instance) *)
Instance compose_proper (C : Category) (x y z : @Obj C) : 
  Proper (@EqMor C y z ==> @EqMor C x y ==> @EqMor C x z) (@Compose C x y z).
Proof.
  do 2 red. intros f f' Hf g g' Hg. (* 2 mélységben unfoldol a do 2 red*)
  eapply eq_cong; assumption.
Defined.

(** Kovariáns Funktor definíciója, adaptálva az EqMor használatához. F_mor mező biztosítja, hogy a funktor tiszteli az ekvivalenciát. *)
Class CovariantFunctor (C : Category) (D : Category) := mk_Functor {
  F_Obj : @Obj C -> @Obj D;
  F_Hom : forall (x y : @Obj C), (x → y) -> (F_Obj x → F_Obj y);
  
  (* Az ekvivalencia megőrzése *)
  F_mor : forall (x y : @Obj C) (f g : x → y), f ≅ g -> (F_Hom x y f) ≅ (F_Hom x y g);
  
  (* Egyenlőségek *)
  F_id : forall (x : @Obj C), F_Hom x x (Id x) ≅ Id (F_Obj x);
  
  F_comp : forall (x y z : @Obj C) (g : y → z) (f : x → y),
    F_Hom x z (g ∘ f) ≅ ((F_Hom y z g) ∘ (F_Hom x y f));
}.


Definition ComposeFunctors {C D E : Category}
  (F : CovariantFunctor C D) (G : CovariantFunctor D E) : CovariantFunctor C E.
Proof.
  apply (mk_Functor C E) with
    (F_Obj := fun x => @F_Obj D E G (@F_Obj C D F x))
    (F_Hom := fun x y f => @F_Hom D E G _ _ (@F_Hom C D F x y f)).
  - (* F_mor *)
    intros x y f g H.
    apply F_mor; apply F_mor; assumption.
  - (* F_id *)
    intros.
    eapply Eq_trans.
    apply F_mor. apply F_id.
    apply F_id.
  - (* F_comp *)
    intros.
    eapply Eq_trans.
    apply F_mor. apply F_comp.
    apply F_comp.
Defined.

(** Bal adjungált EqMor (≅) használatával *)
Class IsLeftAdjoint (C D : Category) (F : CovariantFunctor D C) := mk_IsLeftAdjoint {
  rightadjobj : @Obj C -> @Obj D;
  epsilon : forall (X : @Obj C), (@F_Obj D C F (rightadjobj X)) → X;
  rightadjmor : forall {Y : @Obj D} {X : @Obj C} (f : (@F_Obj D C F Y) → X), Y → (rightadjobj X);
  
  (* A morfizmus leképezésnek is tisztelet tartja az ekvivalenciát *)
  rightadjmor_cong : forall {Y X} (f g : (@F_Obj D C F Y) → X), f ≅ g -> rightadjmor f ≅ rightadjmor g;

  (* Lambek törvények ≅-vel *)
  lambek_1 : forall {Y X} (f : (@F_Obj D C F Y) → X),
    (epsilon X) ∘ (@F_Hom D C F _ _ (rightadjmor f)) ≅ f;
  lambek_2 : forall {Y X} (h : Y → (rightadjobj X)),
    rightadjmor ((epsilon X) ∘ (@F_Hom D C F _ _ h)) ≅ h
}.

(** Jobb adjungált EqMor (≅) használatával *)
Class IsRightAdjoint {C D : Category} (G : CovariantFunctor C D) := mk_IsRightAdjoint {
  leftadjobj : @Obj D -> @Obj C;
  unit : forall (Y : @Obj D), Y → (@F_Obj C D G (leftadjobj Y));
  leftadjmor : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)), (leftadjobj X) → Y;
  
  leftadjmor_cong : forall {X Y} (f g : X → (@F_Obj C D G Y)), f ≅ g -> leftadjmor f ≅ leftadjmor g;

  lambek_1_dual : forall {X : @Obj D} {Y : @Obj C} (g : X → (@F_Obj C D G Y)),
    (@F_Hom C D G _ _ (leftadjmor g)) ∘ (unit X) ≅ g;
  lambek_2_dual : forall {X : @Obj D} {Y : @Obj C} (f : (leftadjobj X) → Y),
    leftadjmor ((@F_Hom C D G _ _ f) ∘ (unit X)) ≅ f
}.

(* Megtanítjuk a Coq-nak, hogy a 'rightadjmor' tiszteletben tartja az EqMor-t *)
Instance rightadjmor_proper (C D : Category) (F : CovariantFunctor D C) 
    (LA : IsLeftAdjoint C D F) (Y : @Obj D) (X : @Obj C) :
    Proper (@EqMor C (@F_Obj D C F Y) X ==> @EqMor D Y (@rightadjobj C D F LA X)) 
    (@rightadjmor C D F LA Y X).
Proof.
  do 2 red. intros f g H. 
  apply rightadjmor_cong. assumption.
Defined.

(* A bal adjungáltra (leftadjmor)  tiszteletben tartja az EqMor-*)
Instance leftadjmor_proper (C D : Category) (G : CovariantFunctor C D) 
    (RA : IsRightAdjoint G) (X : @Obj D) (Y : @Obj C) :
    Proper (@EqMor D X (@F_Obj C D G Y) ==> @EqMor C (@leftadjobj C D G RA X) Y)
    (@leftadjmor C D G RA X Y).
Proof.
  do 2 red. intros f g H.
  apply leftadjmor_cong. assumption.
Defined.
 
Instance RightAdjFunc (C D : Category) (F : CovariantFunctor D C) (FLAdj : IsLeftAdjoint C D F) :
   CovariantFunctor C D.
Proof.
  apply mk_Functor with (F_Obj := @rightadjobj C D F FLAdj)
      (F_Hom := fun X1 X2 f => @rightadjmor C D F FLAdj (rightadjobj X1) X2 (f ∘ epsilon X1 )).
  - (* F_mor *)
    intros x y f g H.
    rewrite H. 
    apply Eq_ref.
  - (* F_id *)
    intros X.
    rewrite id_2.       (* rightadjmor (Id ∘ epsilon) --> rightadjmor epsilon *)
    eapply Eq_trans.
    2: { apply (@lambek_2 C D F FLAdj (rightadjobj X) X (Id (rightadjobj X))). }
    apply rightadjmor_cong.
    rewrite F_id.
    rewrite id_1.
    apply Eq_ref.
    
  - (* F_comp *)
    intros X1 X2 X3 g f.
    
    (* 1. A jobb oldalt átírjuk lambek_2 segítségével *)
    rewrite <- (lambek_2 (rightadjmor (g ∘ epsilon X2) ∘ rightadjmor (f ∘ epsilon X1))).
    
    (* 2. Levesszük a külső rightadjmor-t *)
    apply rightadjmor_cong. 
    
    (* 3. Beviszük az F-et és rendezzük az asszociativitást *)
    rewrite F_comp.
    rewrite assoc.      (* (epsilon ∘ F(...)) ∘ F(...) *)
    rewrite lambek_1.   (* (g ∘ epsilon) ∘ F(...) *)
    rewrite <- assoc.   (* g ∘ (epsilon ∘ F(...)) *)
   
    (* Bal oldal: (g ∘ f) ∘ epsilon *)
    (* Jobb oldal: g ∘ (epsilon ∘ F (rightadjmor (f ∘ epsilon))) *)
    
    (* 4. JAVÍTÁS: A bal oldalt is átrendezzük asszociativitással *)
    rewrite <- assoc.   (* Bal oldal: g ∘ (f ∘ epsilon) *)
    
    (* Most már mindkét oldal "g ∘ ...", alkalmazhatjuk a kongruenciát *)
    apply eq_cong.
    + apply Eq_ref. (* g ≅ g *)
    + (* Most a belső részt kell bizonyítani: f ∘ epsilon ≅ epsilon ∘ F (...) *)
      symmetry. (* Megfordítjuk, hogy alkalmazható legyen a lambek_1 *)
      (* CÉL: epsilon ∘ F (rightadjmor (f ∘ epsilon)) ≅ f ∘ epsilon *)
      apply (lambek_1 (f ∘ epsilon X1)).
Defined.


Instance LeftAdjFunc (C D : Category) (F : CovariantFunctor D C) (FRAdj : IsRightAdjoint F) :
   CovariantFunctor C D.
Proof.
  apply mk_Functor with (F_Obj := @leftadjobj D C F FRAdj)
      (F_Hom := fun X1 X2 f => @leftadjmor D C F FRAdj X1 (leftadjobj X2) ((unit X2) ∘ f)).
  - (* F_mor *)
    intros x y f g H.
    rewrite H. 
    apply Eq_ref.
    
  - (* F_id *)
    intros x.
    rewrite id_1.       (* leftadjmor (unit ∘ Id) --> leftadjmor unit *)
    eapply Eq_trans.
    2: { apply (@lambek_2_dual D C F FRAdj x (leftadjobj x) (Id (leftadjobj x))). }
    apply leftadjmor_cong.
    rewrite F_id.
    rewrite id_2.
    apply Eq_ref.

  - (* F_comp *)
    intros X1 X2 X3 g f.
    
    (* 1. A jobb oldalt (leftadjmor ... ∘ leftadjmor ...) átírjuk lambek_2_dual segítségével *)
    rewrite <- (lambek_2_dual (leftadjmor (unit X3 ∘ g) ∘ leftadjmor (unit X2 ∘ f))).
    
    (* 2. Levesszük a külső leftadjmor-t *)
    apply leftadjmor_cong.
    
    (* 3. Beviszük az F-et a kompozícióba *)
    rewrite F_comp.
    
    (* 4. Átrendezzük a jobb oldalt: (A ∘ B) ∘ unit --> A ∘ (B ∘ unit) *)
    rewrite <- assoc.
    
    (* 5. Belső lambek_1_dual alkalmazása *)
    rewrite lambek_1_dual.
    
    (* Most RHS: F_Hom (leftadjmor (unit ∘ g)) ∘ (unit ∘ f) *)
    (* LHS: unit ∘ (g ∘ f) *)
    
    (* 6. JAVÍTÁS: Mindkét oldalt átrendezzük (.. ∘ ..) ∘ f alakra *)
    
    rewrite assoc. (* Bal oldal: unit ∘ (g ∘ f) --> (unit ∘ g) ∘ f *)
    rewrite assoc. (* Jobb oldal: F_Hom ... ∘ (unit ∘ f) --> (F_Hom ... ∘ unit) ∘ f *)
    
    (* 7. Most már azonos a szerkezet, alkalmazhatjuk a kongruenciát *)
    apply eq_cong.
    
    + (* Bal ág: Bizonyítjuk, hogy (F_Hom ... ∘ unit) ≅ (unit ∘ g) *)
      symmetry. (* Megfordítjuk, mert a lambek a fordítottját adja *)
      (* CÉL: F_Hom (leftadjmor (unit ∘ g)) ∘ unit ≅ unit ∘ g *)
      apply (lambek_1_dual (unit X3 ∘ g)). 
      
    + (* Jobb ág: f ≅ f *)
      apply Eq_ref.
Defined.

(** Két objektum izomorf, ha van köztük oda-vissza út, ami identitást ad.
    Ez helyettesíti a szigorú egyenlőséget (=) a GoodFibration-ben. *)
Class Iso {C : Category} (A B : @Obj C) := {
  iso_to : A → B;
  iso_from : B → A;
  (* A kompozíciók EqMor (≅) szerint identitások *)
  iso_1 : iso_to ∘ iso_from ≅ Id B;
  iso_2 : iso_from ∘ iso_to ≅ Id A
}.

Notation "A ≅O B" := (Iso A B) (at level 40) : type_scope.

(** GoodFibration definíciója izomorfizmussal mint objektum-egyenlőséggel. *)
Class GoodFibration (B : Category) := mk_GoodFibration {
  Fiber : @Obj B -> Category;
  Fiber_is_CCC : forall I : @Obj B, CartClosedCat (Fiber I);

  (* Pullback funktor: (I -> J) morfizmushoz rendel egy funktort visszafelé *)
  Pullback {I J} : (I → J) -> CovariantFunctor (Fiber J) (Fiber I);

  
  (* 1. Pullback (Id) A ≅O A *)
  (* Azaz: A[id] izomorf A-val. *)
  pullback_id_iso : forall {I} (A : @Obj (Fiber I)), 
      (@F_Obj (Fiber I) (Fiber I) (Pullback (Id I)) A) ≅O A;

  (* 2. Pullback (g ∘ f) A ≅O Pullback f (Pullback g A) *)
  (* Azaz: A[g ∘ f] izomorf (A[g])[f]-fel. *)
  pullback_comp_iso : forall {I J K} (g : J → K) (f : I → J) (A : @Obj (Fiber K)),
      (@F_Obj (Fiber K) (Fiber I) (Pullback (g ∘ f)) A) ≅O 
      (@F_Obj (Fiber J) (Fiber I) (Pullback f) (@F_Obj (Fiber K) (Fiber J) (Pullback g) A));

  (* Bal adjungált (Sigma ) létezése *)
  pullback_has_left_adjoint {I J} (f : I → J) :
      @IsRightAdjoint (Fiber J) (Fiber I) (Pullback f);
      
  (* Jobb adjungált (Pi) létezése *)
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

(** Base kategória struktúra két fajtával (típussal):
    - One: Terminális objektum (a "kontextus nélküli" állítások indexe, nulla változós formulák típusindexe )
    - S: Az individuumok típusa (amin kvantifikálunk) *)
Class TwoSortCategory (B : Category) := mk_TwoSortCategory {
  One : @Obj B;
  terminal_mor : forall X, X → One;
  
  (* A terminális morfizmus egyedisége (EqMor ≅ használatával) *)
  terminal_mor_unique : forall X (f : X → One), f ≅ terminal_mor X;
  
  S : @Obj B;
  (* S nem lehet a terminális objektum *)
  S_is_not_Terminal : S <> One 
}.

(** A "bang" morfizmus: Az S típusból a terminálisba (S -> 1) *)
Definition bang (B : Category) (TSC : TwoSortCategory B) : Hom S One :=
  terminal_mor S.

(** Exisztenciális kvantor: 
    A Sigma funktor az (S -> 1) morfizmus mentén. 
    Ez a (Fiber S)-ből a (Fiber One)-ba visz. *)
Definition ExistsQuantifier (B : Category) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : CovariantFunctor (Fiber S) (Fiber One).
Proof.
 exact (Sigma_f (bang B TSC)). 
Defined.

(** Univerzális kvantor: 
    A Pi funktor az (S -> 1) morfizmus mentén. 
    Ez a (Fiber S)-ből a (Fiber One)-ba visz. *)
Definition ForallQuantifier (B : Category) {GF : GoodFibration B} {TSC : TwoSortCategory B}
  : CovariantFunctor (Fiber S) (Fiber One).
Proof.
  exact (Pi_f (bang B TSC)).
Defined.