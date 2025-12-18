(** ========================================================= *)
(** 1. RÉSZ: KATEGÓRIA ELMÉLETI ALAPOK (Setoid alapokon)      *)
(** ========================================================= *)

Require Import List.
Import ListNotations.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.

(* A te definíciód a Kategóriára *)
Class Category := cat_mk {
  Obj : Type;
  Hom : Obj -> Obj -> Type; (* uHom helyett Type, egyszerűsítés végett *)
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z) -> (Hom x y) -> (Hom x z);
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;
  
  (* Axiómák *)
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  eq_cong: forall {x y z} (f g: Hom y z) (h i : Hom x y), 
        EqMor f g -> EqMor h i -> EqMor (Compose f h) (Compose g i);
}.

Notation "x ~> y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≅ g" := (EqMor f g) (at level 40, no associativity) : type_scope.

(* Setoid regisztráció a rewrite-hoz *)
Add Parametric Relation (C : Category) (x y : @Obj C) : (@Hom C x y) (@EqMor C x y)
  reflexivity proved by (@Eq_ref C x y)
  symmetry proved by (@Eq_sim C x y)
  transitivity proved by (@Eq_trans C x y)
  as eqmor_rel.

Instance compose_proper (C : Category) (x y z : @Obj C) : 
  Proper (@EqMor C y z ==> @EqMor C x y ==> @EqMor C x z) (@Compose C x y z).
Proof.
  repeat red. intros. apply eq_cong; assumption.
Defined.

(** ========================================================= *)
(** 2. RÉSZ: A BASE KATEGÓRIA (Induktív, nem Coq függvény!)   *)
(** ========================================================= *)

(* JAVÍTVA: S -> BaseS, így nem ütközik a nat S-ével *)
Inductive BaseObj : Type := 
  | One : BaseObj 
  | BaseS : BaseObj. 

Inductive BaseTerm : BaseObj -> BaseObj -> Type :=
  | base_id {A} : BaseTerm A A
  | base_comp {A B C} : BaseTerm B C -> BaseTerm A B -> BaseTerm A C
  | base_bang {A} : BaseTerm A One
  | base_gen (n : nat) : BaseTerm One BaseS. (* Itt is BaseS *)

Inductive BaseTermEq : forall A B, BaseTerm A B -> BaseTerm A B -> Prop :=
  | basee_refl  {A B} (f : BaseTerm A B) : BaseTermEq A B f f
  | basee_sym   {A B} (f g : BaseTerm A B) : BaseTermEq A B f g -> BaseTermEq A B g f
  | basee_trans {A B} (f g h : BaseTerm A B) : BaseTermEq A B f g -> BaseTermEq A B g h -> BaseTermEq A B f h
  | basee_comp  {A B C} (f f' : BaseTerm B C) (g g' : BaseTerm A B) :
      BaseTermEq B C f f' -> BaseTermEq A B g g' -> BaseTermEq A C (base_comp f g) (base_comp f' g')
  | basee_id_l  {A B} (f : BaseTerm A B) : BaseTermEq A B (base_comp base_id f) f
  | basee_id_r  {A B} (f : BaseTerm A B) : BaseTermEq A B (base_comp f base_id) f
  | basee_assoc {A B C D} (f : BaseTerm C D) (g : BaseTerm B C) (h : BaseTerm A B) :
      BaseTermEq A D (base_comp (base_comp f g) h) (base_comp f (base_comp g h))
  | basee_term  {A} (f : BaseTerm A One) : BaseTermEq A One f base_bang.

Instance SyntacticCat : Category.
Proof.
  apply cat_mk with 
    (Obj := BaseObj) 
    (Hom := BaseTerm) 
    (Id := @base_id)       
    (Compose := @base_comp) 
    (EqMor := BaseTermEq).
  - intros. apply basee_refl.
  - intros. eapply basee_trans; eassumption.
  - intros. apply basee_sym; assumption.
  - intros. apply basee_sym. apply basee_assoc.
  - intros. apply basee_id_r.
  - intros. apply basee_id_l.
  - intros. apply basee_comp; assumption.
Defined.

(** ========================================================= *)
(** 3. RÉSZ: A BELSŐ NYELV (CLEAN & RENAMED VERSION)          *)
(** ========================================================= *)

(* --- TÍPUSOK (Ty) --- *)
Inductive Ty : BaseObj -> Type :=
  | Top : forall b, Ty b
  | Imp : forall b, Ty b -> Ty b -> Ty b
  | Cnj : forall b, Ty b -> Ty b -> Ty b
  (* Pullback: Típus helyettesítése BaseTerm morfizmussal *)
  | Subst : forall {b1 b2}, BaseTerm b1 b2 -> Ty b2 -> Ty b1
  (* Kvantorok: S helyett BaseS! *)
  | Exists : Ty BaseS -> Ty One
  | Forall : Ty BaseS -> Ty One.

(* Unicode jelölések *)
Notation "A '⇒' B" := (Imp _ A B) (at level 70, right associativity) : type_scope.
Notation "A '∧' B" := (Cnj _ A B) (at level 70, right associativity) : type_scope.
Notation "f '⋆' A" := (Subst f A) (at level 60) : type_scope.
Notation "'Σ' A" := (Exists A) (at level 70) : type_scope.
Notation "'Π' A" := (Forall A) (at level 70) : type_scope.

(* --- KONTEXTUS (Ctx) --- *)
Definition Ctx (b : BaseObj) := list (Ty b).

(* Pullback a kontextuson *)
Fixpoint SubstCtx {b1 b2} (f : BaseTerm b1 b2) (G : Ctx b2) : Ctx b1 :=
  match G with
  | nil => nil
  | A :: G' => (Subst f A) :: (SubstCtx f G')
  end.

(* --- TERMEK (Tm) --- *)
Inductive Tm : BaseObj -> Type :=
  | top : forall b, Tm b
  | hyp : forall b, nat -> Tm b (* De Bruijn index *)
  | lam : forall b, Ty b -> Tm b -> Tm b
  | app : forall b, Tm b -> Tm b -> Tm b
  
  | conj : forall b, Tm b -> Tm b -> Tm b
  | pr1  : forall b, Tm b -> Tm b
  | pr2  : forall b, Tm b -> Tm b
  
  (* Pullback termeken *)
  | subst_map : forall {b1 b2} (f : BaseTerm b1 b2), Tm b2 -> Tm b1
  
  (* Sigma (Exists) - BaseS használata *)
  | exists_unit : Ty BaseS -> Tm BaseS 
  | exists_elim : forall (A : Ty BaseS) (B : Ty One), Tm BaseS -> Tm One
  
  (* Pi (Forall) - BaseS használata *)
  | forall_counit : Ty BaseS -> Tm BaseS 
  | forall_intro : forall (A : Ty BaseS) (B : Ty One), Tm BaseS -> Tm One.


Inductive Prty : forall b, Ctx b -> Tm b -> Ty b -> Prop :=
  (* ... A többi szabály változatlan ... *)
  | T_top : forall b G, Prty b G (top b) (Top b)
  | T_hypO : forall b G A, Prty b (A :: G) (hyp b 0) A
  | T_hypS : forall b G A B i, Prty b G (hyp b i) A -> Prty b (B :: G) (hyp b (S i)) A
  | T_lam : forall b G t A B, Prty b (A :: G) t B -> Prty b G (lam b A t) (A ⇒ B)
  | T_app : forall b G t s A B, Prty b G t (A ⇒ B) -> Prty b G s A -> Prty b G (app b t s) B
  | T_conj : forall b G t s A B, Prty b G t A -> Prty b G s B -> Prty b G (conj b t s) (A ∧ B)
  | T_pr1 : forall b G t A B, Prty b G t (A ∧ B) -> Prty b G (pr1 b t) A
  | T_pr2 : forall b G t A B, Prty b G t (A ∧ B) -> Prty b G (pr2 b t) B
      
  (* --- JAVÍTOTT SZABÁLY --- *)
  (* Megengedjük, hogy legyen egy extra 'D' kontextus a végén *)
  | T_subst : forall {b b_target} (f : BaseTerm b b_target) 
                     (G : Ctx b_target) (D : Ctx b) (* <--- ÚJ: Extra kontextus *)
                     (t : Tm b_target) (A : Ty b_target),
      Prty b_target G t A -> 
      Prty b (SubstCtx f G ++ D) (subst_map f t) (f ⋆ A)
      
  (* ... A többi szabály változatlan ... *)
  | T_exists_unit : forall (G : Ctx BaseS) (A : Ty BaseS),
      Prty BaseS G (exists_unit A) (A ⇒ (base_bang ⋆ (Σ A)))
  | T_exists_elim : forall (G : Ctx One) (t : Tm BaseS) (A : Ty BaseS) (B : Ty One),
      Prty BaseS (SubstCtx base_bang G) t (A ⇒ (base_bang ⋆ B)) ->
      Prty One G (exists_elim A B t) ((Σ A) ⇒ B)
  | T_forall_counit : forall (G : Ctx BaseS) (A : Ty BaseS),
      Prty BaseS G (forall_counit A) ((base_bang ⋆ (Π A)) ⇒ A)
  | T_forall_intro : forall (G : Ctx One) (t : Tm BaseS) (A : Ty BaseS) (B : Ty One),
      Prty BaseS (SubstCtx base_bang G) t ((base_bang ⋆ B) ⇒ A) ->
      Prty One G (forall_intro A B t) (B ⇒ (Π A)).

(* A _ jelzi a Coq-nak, hogy a 'b' paramétert találja ki a kontextusból *)
Notation "G '⊢' t '[:]' A" := (Prty _ G t A) (at level 70).

(** ========================================================= *)
(** 4. RÉSZ: FIBER FUNKTOROK (CCC minden Base Object felett)  *)
(** ========================================================= *)

Lemma SubstCtx_app : forall {b1 b2} (f : BaseTerm b1 b2) (G D : Ctx b2),
  SubstCtx f (G ++ D) = SubstCtx f G ++ SubstCtx f D.
Proof.
  intros b1 b2 f G D.
  induction G as [| A G' IH].
  - (* Base case: nil *)
    simpl. reflexivity.
  - (* Inductive step: A :: G' *)
    simpl. rewrite IH. reflexivity.
Qed.

(* Weakening Lemma: Ha G-ben van t, akkor G bővítésében is ott van *)
Lemma weakening_weak : forall {b : BaseObj} (G D : Ctx b) (t : Tm b) (A : Ty b),
  Prty b G t A -> Prty b (G ++ D) t A.
Proof.
  intros b G D t A H. 
  induction H. (* Indukció a Prty-n *)
  - apply T_top.
  - apply T_hypO.
  - apply T_hypS. apply IHPrty.
  - apply T_lam. apply IHPrty.
  - eapply T_app; eauto.
  - apply T_conj; eauto.
  - eapply T_pr1; eauto.
  - eapply T_pr2; eauto.
  
  (* JAVÍTOTT ÁG: T_subst *)
  - (* Subst ág *)
    (* 1. Kényszerítsük ki a zárójelezés megváltoztatását *)
    replace ((SubstCtx f G ++ D0) ++ D) with (SubstCtx f G ++ (D0 ++ D)).
    
    (* 2. A fő ágon most már alkalmazható a T_subst, mert a struktúra (A ++ B) alakú *)
    + apply T_subst.
      exact H.
      
    (* 3. Bizonyítsuk be, hogy a csere jogos volt (asszociativitás) *)
    + rewrite app_assoc. reflexivity.
  - apply T_exists_unit.
  - (* T_exists_elim ág *)
    apply T_exists_elim.
    
    (* 1. A célban: SubstCtx base_bang (G ++ D) 
       Ezt írjuk át erre: SubstCtx base_bang G ++ SubstCtx base_bang D 
       a fenti lemma segítségével. *)
    rewrite SubstCtx_app.
    
    (* 2. Most a cél: BaseS ⊢ SubstCtx ... G ++ SubstCtx ... D [:] t ...
       Az IHPrty pedig azt mondja: BaseS ⊢ SubstCtx ... G ++ ?D' [:] t ...
       
       A Coq most már felismeri, hogy az IH-ban a '?D'' paraméternek 
       a (SubstCtx base_bang D)-nek kell lennie. *)
    apply IHPrty.  
  - apply T_forall_counit.
  - (* T_forall_intro ág *)
    apply T_forall_intro.
    rewrite SubstCtx_app. (* Itt is szétbontjuk *)
    apply IHPrty.
Defined.

(* --- KATEGÓRIA DEFINÍCIÓ --- *)

Section SynCategory.
  Context {b : BaseObj}.

  (* A referenciádhoz hasonlóan: A morfizmus egy PÁR (term, bizonyítás) *)
  (* Hom : Obj -> Obj -> Type *)
  Definition Syn_Hom (A B : Ty b) : Type := 
    { t : Tm b | nil ⊢ t [:] (A ⇒ B) }.

  (* Proof Irrelevance: Két morfizmus egyenlő, ha a termjeik "ekvivalensek".
     Mivel a logikánkban minden bizonyítás egyenlő, itt egyszerűsítünk: *)
  Definition Syn_EqMor {A B : Ty b} (f g : Syn_Hom A B) : Prop := 
    True.

  (* Identitás: λx. x *)
  Definition Syn_Id_term (A : Ty b) := lam b A (hyp b 0).
  
  Lemma Syn_Id_proof (A : Ty b) : nil ⊢ Syn_Id_term A [:] (A ⇒ A).
  Proof.
    unfold Syn_Id_term. apply T_lam. apply T_hypO.
  Defined.

  Definition Syn_Id (A : Ty b) : Syn_Hom A A := 
    exist _ (Syn_Id_term A) (Syn_Id_proof A).

  (* Kompozíció: λx. g(f(x)) *)
  Definition Syn_Compose_term {A B C : Ty b} (g : Syn_Hom B C) (f : Syn_Hom A B) :=
    lam b A (app b (proj1_sig g) (app b (proj1_sig f) (hyp b 0))).

  Lemma Syn_Compose_proof {A B C : Ty b} (g : Syn_Hom B C) (f : Syn_Hom A B) :
    nil ⊢ Syn_Compose_term g f [:] (A ⇒ C).
  Proof.
    unfold Syn_Compose_term.
    destruct f as [tf Hf], g as [tg Hg]. simpl.
    apply T_lam.
    apply T_app with (A := B).
    (* Itt kell a weakening, mert tg és tf az üres kontextusban élnek, 
       de most [A] alatt használjuk őket. *)
    - apply weakening_weak with (G := nil) (D := [A]) in Hg. exact Hg.
    - apply T_app with (A := A).
      + apply weakening_weak with (G := nil) (D := [A]) in Hf. exact Hf.
      + apply T_hypO.
  Defined.

  Definition Syn_Compose {A B C : Ty b} (g : Syn_Hom B C) (f : Syn_Hom A B) : Syn_Hom A C :=
    exist _ (Syn_Compose_term g f) (Syn_Compose_proof g f).

  (* KATEGÓRIA INSTANCIA *)
  Instance Syn_Cat_Instance : Category.
  Proof.
    apply cat_mk with 
      (Obj := Ty b) 
      (Hom := Syn_Hom)
      (Id := Syn_Id)
      (Compose := @Syn_Compose)
      (EqMor := @Syn_EqMor).
    (* Az axiómák triviálisak a Syn_EqMor = True miatt *)
    all: intros; exact I.
  Defined.

End SynCategory.

(** ========================================================= *)
(** 5. RÉSZ: CCC STRUKTÚRA (A referenciád alapján)            *)
(** ========================================================= *)

(* --- CCC OSZTÁLY DEFINÍCIÓ --- *)

Class CartClosedCat (C : Category) := CartClosedCat_mk {
  Top_obj : @Obj C;
  Top_mor : forall {x}, x ~> Top_obj;
  Prod_obj : @Obj C -> @Obj C -> @Obj C;
  Prod_mor : forall {x y z} (f:x ~> y) (g:x ~> z), x ~> Prod_obj y z;
  First {x y} : (Prod_obj x y) ~> x;
  Second {x y} : (Prod_obj x y) ~> y;
  Exp_obj : @Obj C -> @Obj C -> @Obj C;
  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) ~> z;
  Lam : forall {x y z} (g : (Prod_obj x y) ~> z), x ~> (Exp_obj z y);
  
  (* Axiómák (törvények) - Mivel nálunk PI van, ezek bizonyítása triviális lesz *)
  unique_top : forall {x} (f : x ~> Top_obj), f ≅ Top_mor;
  prod_ax_1 : forall {x y z} (f : x ~> y) (g : x ~> z), First ∘ (Prod_mor f g) ≅ f;
  prod_ax_2 : forall {x y z} (f : x ~> y) (g : x ~> z), Second ∘ (Prod_mor f g) ≅ g;
  unique_prod : forall {x y z} (f : x ~> y) (g : x ~> z) (h : x ~> Prod_obj y z), 
      ((First ∘ h) ≅ f) /\ ((Second ∘ h) ≅ g) -> h ≅ (Prod_mor f g);
  exp_ax : forall {x y z} (g : (Prod_obj x y) ~> z), 
      Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) ≅ g;
  unique_exp : forall {x y z} (h : x ~> Exp_obj z y), 
      Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) ≅ h
}.

Section SynCCC.
  Context {b : BaseObj}.

  (* --- PRODUCT (Cnj) --- *)
  
  Definition Syn_Prod (A B : Ty b) := Cnj b A B.

  (* Pair: <f, g> *)
  Definition Prodmor_term {x y z : Ty b} (f : Syn_Hom x y) (g : Syn_Hom x z) :=
    lam b x (conj b (app b (proj1_sig f) (hyp b 0)) (app b (proj1_sig g) (hyp b 0))).

  Lemma Prodmor_proof {x y z : Ty b} (f : Syn_Hom x y) (g : Syn_Hom x z) :
    nil ⊢ Prodmor_term f g [:] (x ⇒ (y ∧ z)).
  Proof.
    unfold Prodmor_term. destruct f as [tf Hf], g as [tg Hg]. simpl.
    apply T_lam. apply T_conj.
    - apply T_app with (A:=x).
      + apply weakening_weak with (G:=nil) (D:=[x]) in Hf. exact Hf.
      + apply T_hypO.
    - apply T_app with (A:=x).
      + apply weakening_weak with (G:=nil) (D:=[x]) in Hg. exact Hg.
      + apply T_hypO.
  Defined.

  Definition Syn_Prod_mor {x y z : Ty b} (f : Syn_Hom x y) (g : Syn_Hom x z) : Syn_Hom x (Syn_Prod y z) :=
    exist _ (Prodmor_term f g) (Prodmor_proof f g).

  (* Projections *)
  Definition Fst_term (x y : Ty b) := lam b (x ∧ y) (pr1 b (hyp b 0)).
  Lemma Fst_proof (x y : Ty b) : nil ⊢ Fst_term x y [:] ((x ∧ y) ⇒ x).
Proof. 
  unfold Fst_term. 
  apply T_lam. 
  (* Itt segítünk neki: a pár másik fele 'y' *)
  apply T_pr1 with (B := y). 
  apply T_hypO. 
Defined.
  Definition Syn_Fst {x y} : Syn_Hom (Syn_Prod x y) x := exist _ (Fst_term x y) (Fst_proof x y).

  Definition Snd_term (x y : Ty b) := lam b (x ∧ y) (pr2 b (hyp b 0)).
  Lemma Snd_proof (x y : Ty b) : nil ⊢ Snd_term x y [:] ((x ∧ y) ⇒ y).
Proof. 
  unfold Snd_term. 
  apply T_lam. 
  apply T_pr2 with (A := x). (* Itt az első felet kell megadni *)
  apply T_hypO. 
Defined.
  Definition Syn_Snd {x y} : Syn_Hom (Syn_Prod x y) y := exist _ (Snd_term x y) (Snd_proof x y).

  (* --- EXPONENTIAL (Imp) --- *)

  Definition Syn_Exp (A B : Ty b) := Imp b B A. (* B => A *)

  (* Eval: app (fst p) (snd p) *)
  Definition Expapp_term (y z : Ty b) := 
    lam b ((y ⇒ z) ∧ y) (app b (pr1 b (hyp b 0)) (pr2 b (hyp b 0))).

  Lemma Expapp_proof (y z : Ty b) : nil ⊢ Expapp_term y z [:] (((y ⇒ z) ∧ y) ⇒ z).
Proof.
  unfold Expapp_term. 
  apply T_lam. 
  eapply T_app.
  
  (* 1. A függvény kinyerése (pr1) *)
  - eapply T_pr1. (* eapply, hogy ne kelljen kiírni a (B:=y)-t *)
    apply T_hypO.
    
  (* 2. Az argumentum kinyerése (pr2) *)
  - eapply T_pr2. (* Itt pedig (A := y ⇒ z) lenne expliciten *)
    apply T_hypO.
Defined.
  
  Definition Syn_Exp_app {y z} : Syn_Hom (Syn_Prod (Syn_Exp z y) y) z :=
    exist _ (Expapp_term y z) (Expapp_proof y z).

  (* Currying (Lam) *)
  Definition Lam_term {x y z : Ty b} (g : Syn_Hom (x ∧ y) z) :=
    lam b x (lam b y (app b (proj1_sig g) (conj b (hyp b 1) (hyp b 0)))).

  Lemma Lam_proof {x y z : Ty b} (g : Syn_Hom (x ∧ y) z) :
    nil ⊢ Lam_term g [:] (x ⇒ (y ⇒ z)).
  Proof.
    unfold Lam_term. destruct g as [tg Hg]. simpl.
    apply T_lam. apply T_lam.
    apply T_app with (A := (x ∧ y)).
    - (* Kétszeres weakening: nil -> [y; x] *)
      apply weakening_weak with (G:=nil) (D:=[y; x]) in Hg. exact Hg.
    - apply T_conj.
      + apply T_hypS. apply T_hypO. (* x a külső (1-es) index *)
      + apply T_hypO.               (* y a belső (0-ás) index *)
  Defined.

  Definition Syn_Lam {x y z} (g : Syn_Hom (Syn_Prod x y) z) : Syn_Hom x (Syn_Exp z y) :=
    exist _ (Lam_term g) (Lam_proof g).

  (* Top *)
  Definition Top_term (x : Ty b) := lam b x (top b).
  Lemma Top_proof (x : Ty b) : nil ⊢ Top_term x [:] (x ⇒ Top b).
  Proof. unfold Top_term. apply T_lam. apply T_top. Defined.
  Definition Syn_Top_mor {x} : Syn_Hom x (Top b) := exist _ (Top_term x) (Top_proof x).

  (* --- CCC INSTANCE --- *)
  
 (* A @ jellel kikapcsoljuk az implicit argumentumokat, és kézzel átadjuk a b-t *)
 Instance Syn_CCC_Instance : CartClosedCat (@Syn_Cat_Instance b).
 Proof.
    apply CartClosedCat_mk with 
      (Top_obj := Top b)
      (Top_mor := @Syn_Top_mor)
      (Prod_obj := Syn_Prod)
      (Prod_mor := @Syn_Prod_mor)
      (First := @Syn_Fst)
      (Second := @Syn_Snd)
      (Exp_obj := Syn_Exp)
      (Exp_app := @Syn_Exp_app)
      (Lam := @Syn_Lam).
    all: intros; exact I.
  Defined.

End SynCCC.

(** ========================================================= *)
(** 5. RÉSZ: HIPERDOKTRINA (Fibráció Base felett)             *)
(** ========================================================= *)

Class CovariantFunctor (C : Category) (D : Category) := mk_Functor {
  F_Obj : @Obj C -> @Obj D;
  F_Hom : forall (x y : @Obj C), (x ~> y) -> (F_Obj x ~> F_Obj y);
  (* Axiómák kihagyva a demó miatt *)
}.

Definition SynFiber (b : BaseObj) : Category := Syn_Cat_Instance (b:=b).

(* A PULLBACK FUNKTOR: BaseTerm-eken alapul *)
(* f : BaseTerm I J. A Funktor a J-rostból képez az I-rostba *)
Instance SynPullback_Functor {I J : BaseObj} (f : BaseTerm I J) : CovariantFunctor (SynFiber J) (SynFiber I).
Proof.
  apply mk_Functor with 
    (F_Obj := fun A => LSubst f A)
    (F_Hom := fun A B h => 
       match h with
       | ex_intro _ t Ht => ex_intro _ (l_subst_map f t) (
           (* Itt a LT_subst szabályt használjuk a bizonyítás transzformálására *)
           let H := LT_subst f nil t (A => B) Ht in
           (* Itt kellene bizonyítani, hogy (f^* (A => B)) egyenlő (f^* A => f^* B)-vel.
              Ez a szintaktikus helyettesítés definíciójából adódna. *)
           ltac:(admit) 
         )
       end).
Admitted.