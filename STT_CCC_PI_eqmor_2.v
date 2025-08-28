Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_top : forall Γ, Tyty Γ top Top
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS : forall Γ A B i, Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam : forall Γ t A B, Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | STT_app : forall Γ t s A B, Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | STT_cnj : forall Γ t s A B, Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | STT_proj1 : forall Γ t A B, Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | STT_proj2 : forall Γ t A B, Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.
Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.
Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) : type_scope.

Require Import PeanoNat Arith Peano Lia.

(* Segédfüggvény a változók indexének növeléséhez (lifting) *)
Fixpoint lift (k : nat) (t : Trm) : Trm :=
  match t with
  | top => top
  | hyp i => if k <=? i then hyp (S i) else hyp i
  | lam A t' => lam A (lift (S k) t')
  | app t1 t2 => app (lift k t1) (lift k t2)
  | cnj t1 t2 => cnj (lift k t1) (lift k t2)
  | proj_1 t' => proj_1 (lift k t')
  | proj_2 t' => proj_2 (lift k t')
  end.

(* A helyettesítés függvény *)
Fixpoint subst (t : Trm) (i : nat) (s : Trm) : Trm :=
  match t with
  | top => top
  | hyp j => match Nat.compare j i with
             | Eq => s
             | Lt => hyp j
             | Gt => hyp (j - 1)
             end
  | lam A t' => lam A (subst t' (S i) (lift 0 s))
  | app t1 t2 => app (subst t1 i s) (subst t2 i s)
  | cnj t1 t2 => cnj (subst t1 i s) (subst t2 i s)
  | proj_1 t' => proj_1 (subst t' i s)
  | proj_2 t' => proj_2 (subst t' i s)
  end.



(* Kategória definíciója EqMor ekvivalenciarelációval *)
Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);
  EqMor : forall {x y}, (Hom x y) -> (Hom x y) -> Prop;
  Eq_ref : forall {x y} (f : Hom x y), EqMor f f;
  Eq_trans : forall {x y} (f g h : Hom x y), EqMor f g -> EqMor g h -> EqMor f h;
  Eq_sim : forall {x y} (f g : Hom x y), EqMor f g -> EqMor g f;
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        EqMor (Compose f (Compose g h) ) (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), EqMor (Compose f (Id x)) f;
  id_2 : forall x y (f : (Hom x y)), EqMor (Compose (Id y) f) f;
  eq: forall {x y z} (f g: Hom y z) (h i : Hom x y), EqMor f g /\ EqMor h i ->
        EqMor (Compose f h) (Compose g i);
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) : type_scope.
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) : type_scope.
Notation "f ≅ g" := (EqMor f g) (at level 40, left associativity) : type_scope.

Definition Obj_STT := Typ.
Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (x ⊃ y)}.

(* A Proof Irrelevance-t megtestesítő EGYETLEN ekvivalencia-szabály *)
Inductive STT_equiv : Trm -> Trm -> Prop :=
  | PI_rule : forall Γ A t s,
      (Γ ⊢ t [:] A) -> (Γ ⊢ s [:] A) -> STT_equiv t s.

Definition EqMor_STT {x y : Obj_STT} (f g : Hom_STT x y) :=
  STT_equiv (proj1_sig f) (proj1_sig g).

Lemma EqMor_STT_ref : forall {x y} (f : Hom_STT x y), EqMor_STT f f.
Proof.
  intros x y f. unfold EqMor_STT.
  apply (PI_rule nil (x ⊃ y) (proj1_sig f) (proj1_sig f)).
  - exact (proj2_sig f).
  - exact (proj2_sig f).
Defined.

Lemma EqMor_STT_sym : forall {x y} (f g : Hom_STT x y), EqMor_STT f g -> EqMor_STT g f.
Proof.
  intros x y f g H. unfold EqMor_STT in *.
  apply (PI_rule nil (x ⊃ y) (proj1_sig g) (proj1_sig f)).
  - exact (proj2_sig g).
  - exact (proj2_sig f).
Defined.

Lemma EqMor_STT_trans : forall {x y} (f g h : Hom_STT x y), EqMor_STT f g -> EqMor_STT g h -> EqMor_STT f h.
Proof.
  intros x y f g h Hfg Hgh. unfold EqMor_STT.
  apply (PI_rule nil (x ⊃ y) (proj1_sig f) (proj1_sig h)).
  - exact (proj2_sig f).
  - exact (proj2_sig h).
Defined.

(* Az axiómák bizonyításai drasztikusan leegyszerűsödnek *)

Lemma generic_axiom_proof : forall {x y} (f g : Hom_STT x y), EqMor_STT f g.
Proof.
  intros x y f g. unfold EqMor_STT.
  apply (PI_rule nil (x ⊃ y)).
  - exact (proj2_sig f).
  - exact (proj2_sig g).
Defined.

(* A kategória definíciók és a CCC konstrukciók maradnak, de az axióma bizonyítások az új sémát követik *)
Definition Id_STT_term (x : Obj_STT) := (lam x (hyp 0)).
Lemma Id_STT_type (x : Obj_STT) : ⊢ (Id_STT_term x) [:] (x ⊃ x).
Proof. unfold Id_STT_term. apply STT_lam. apply STT_hypO. Defined.
Definition Id_STT (x : Typ) : Hom_STT x x := exist _ (Id_STT_term x) (Id_STT_type x).

Lemma weakening_weak : forall Γ Δ t A, Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l). { simpl; auto. }
  intros Γ Δ t A H. induction H; try (rewrite K; try rewrite <- app_assoc; try rewrite <- K); auto.
  - apply STT_top.
  - apply STT_hypO.
  - apply STT_hypS; auto.
  - apply STT_lam; auto.
  - apply STT_app with (A:=A); auto.
  - apply STT_cnj; auto.
  - apply STT_proj1 with (Γ := Γ ++ Δ) (B:=B); auto.
  - apply STT_proj2 with (Γ := Γ ++ Δ) (A:=A); auto.
Defined.

Definition Compose_STT_term {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) := lam x (app (proj1_sig f) (app (proj1_sig g) (hyp 0))).
Lemma Compose_STT_type {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : ⊢ (Compose_STT_term f g) [:] (x ⊃ z).
Proof.
  unfold Compose_STT_term. apply STT_lam.
  apply STT_app with (A:=y).
  - apply weakening_weak with (Γ := nil); exact (proj2_sig f).
  - apply STT_app with (A:=x).
    -- apply weakening_weak with (Γ := nil); exact (proj2_sig g).
    -- apply STT_hypO.
Defined.
Definition Compose_STT {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : Hom_STT x z := exist _ (Compose_STT_term f g) (Compose_STT_type f g).

Instance STT_as_a_Cat : Category.
Proof.
  apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT) (EqMor := @EqMor_STT).
  - (* Eq_ref *)
    intros; apply EqMor_STT_ref.
  - (* Eq_trans *)
    intros. eapply EqMor_STT_trans. exact H. exact H0.
  - (* Eq_sim *)
    intros; apply EqMor_STT_sym; assumption.
  - (* assoc *)
    intros; apply generic_axiom_proof.
  - (* id_1 *)
    intros; apply generic_axiom_proof.
  - (* id_2 *)
    intros; apply generic_axiom_proof.
  - (* eq (kongruencia) *)
    intros; destruct H; apply generic_axiom_proof.
Defined.

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
  
  unique_top : forall {x} (f : x → Top_obj), f ≅ Top_mor;
  prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), First ∘ (Prod_mor f g) ≅ f;
  prod_ax_2 : forall {x y z} (f : x → y) (g : x → z), Second ∘ (Prod_mor f g) ≅ g;
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y z), ((First ∘ h) ≅ f) /\ ((Second ∘ h) ≅ g) -> h ≅ (Prod_mor f g);
  exp_ax : forall {x y z} (g : (Prod_obj x y) → z), Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second)) ≅ g;
  unique_exp : forall {x y z} (h : x → Exp_obj z y), Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) ≅ h
}.

(* CCC Konstrukciók és bizonyításaik *)
Definition Topmor_STT_term (A : Obj_STT) := (lam A top).
Lemma Topmor_STT_type (A : Obj_STT) : ⊢ (lam A top) [:] (Imp A Top).
Proof. intros; apply STT_lam; apply STT_top. Defined.
Definition Topmor_STT (x : Typ) : Hom_STT x Top := exist _ (Topmor_STT_term x) (Topmor_STT_type x).

Definition Prodmor_STT_term (x y z : Obj_STT) (f : Hom_STT x y) (g : Hom_STT x z) := lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g) (hyp 0))).
Lemma Prodmor_STT_type (x y z : Obj_STT) (f : Hom_STT x y) (g : Hom_STT x z) : ⊢ Prodmor_STT_term x y z f g [:] (Imp x (Cnj y z)).
Proof.
  (* Az Imp bevezetéséhez a kontextust [x]-re bővítjük *)
  unfold Prodmor_STT_term; apply STT_lam.

  (* A Cnj bevezetéséhez a célt kettébontjuk *)
  apply STT_cnj.

  - (* 1. CÉL: [x] ⊢ app (proj1_sig f) (hyp 0) [:] y *)
    (* Az app bevezetése, expliciten megadva, hogy a (hyp 0) típusa x *)
    apply STT_app with (A:=x).
    + unfold Hom_STT in *.
      apply weakening_weak with (Γ:=nil) (Δ:=[x]).
      exact (proj2_sig f).
    + (* 1b. alkcél: az argumentum tipizálása *)
      apply STT_hypO.

  - (* 2. CÉL: [x] ⊢ app (proj1_sig g) (hyp 0) [:] z *)
    (* Ugyanaz a logika, mint az 1. célnál, csak 'g'-vel *)
    apply STT_app with (A:=x).
    + apply weakening_weak with (Γ:=nil) (Δ:=[x]).
      exact (proj2_sig g).
    + apply STT_hypO.
Defined.
Definition Prodmor_STT (x y z : Obj_STT) (f : Hom_STT x y) (g : Hom_STT x z) : Hom_STT x (Cnj y z) := exist _ (Prodmor_STT_term x y z f g) (Prodmor_STT_type x y z f g).

Definition First_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_1 (hyp 0))).
Lemma First_STT_type (x y : Obj_STT) : ⊢ (First_STT_term x y) [:] (Imp (Cnj x y) x).
Proof. unfold First_STT_term; apply STT_lam. eapply STT_proj1. apply STT_hypO. Defined.
Definition First_STT (x y : Typ) : Hom_STT (Cnj x y) x := exist _ (First_STT_term x y) (First_STT_type x y).

Definition Second_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_2 (hyp 0))).
Lemma Second_STT_type (x y : Obj_STT) : ⊢ (Second_STT_term x y) [:] (Imp (Cnj x y) y).
Proof. unfold Second_STT_term; apply STT_lam; eapply STT_proj2; apply STT_hypO. Defined.
Definition Second_STT (x y : Typ) : Hom_STT (Cnj x y) y := exist _ (Second_STT_term x y) (Second_STT_type x y).

Definition Expapp_STT_term (y z : Obj_STT) := lam (Cnj (Imp y z) y) (app (proj_1 (hyp 0)) (proj_2 (hyp 0)) ).
Lemma Expapp_STT_type (y z : Typ) : ⊢ Expapp_STT_term y z [:] (Imp (Cnj (Imp y z) y) z).
Proof. unfold Expapp_STT_term; apply STT_lam; eapply STT_app; [eapply STT_proj1 | eapply STT_proj2]; apply STT_hypO. Defined.
Definition Expapp_STT (y z : Typ) : Hom_STT (Cnj (Imp y z) y) z := exist _ (Expapp_STT_term y z) (Expapp_STT_type y z).

Definition Lam_STT_term (x y z : Obj_STT) (g : Hom_STT (Cnj x y) z) := (lam x (lam y (app (proj1_sig g) (cnj (hyp 1) (hyp 0))))).
Lemma Lam_STT_type (x y z : Obj_STT) (g : Hom_STT (Cnj x y) z) : ⊢ Lam_STT_term x y z g [:] Imp x (Imp y z).
Proof.
  unfold Lam_STT_term; apply STT_lam; apply STT_lam.
  apply STT_app with (A:= (Cnj x y)).
  - apply weakening_weak  with (Γ:=nil) (Δ:=[y; x]); exact (proj2_sig g).
  - apply STT_cnj; [apply STT_hypS, STT_hypO | apply STT_hypO].
Defined.
Definition Lam_STT (x y z : Typ) (g : Hom_STT (Cnj x y) z) : Hom_STT x (Imp y z) := exist _ (Lam_STT_term x y z g) (Lam_STT_type x y z g).

Instance STT_as_a_CCC : CartClosedCat STT_as_a_Cat.
Proof.
  apply CartClosedCat_mk with
    (Top_obj := Top) (Top_mor := Topmor_STT) (Prod_obj := Cnj)
    (Prod_mor := Prodmor_STT) (First := First_STT) (Second := Second_STT)
    (Exp_obj := fun z y => Imp y z) (Exp_app := Expapp_STT) (Lam := Lam_STT).
  all: intros; apply generic_axiom_proof.
Defined.

(* Soundness és Completeness rész változatlan marad *)
Structure VAL (C : Category) (CC : CartClosedCat C) : Type := makeVAL {
  V :> Typ -> Obj;
  VAL_top : V Top = Top_obj;
  VAL_imp : forall {A B}, V (Imp A B) = Exp_obj (V B) (V A);
  VAL_cnj : forall {A B}, V (Cnj A B) = Prod_obj (V A) (V B);
}.

Fixpoint VAL_Cntxt (C : Category) (CC : CartClosedCat C) (v : VAL C CC) (Γ : list Typ) :=
  match Γ with
  | nil => Top_obj
  | A :: Γ' => Prod_obj (VAL_Cntxt C CC v Γ') (v A)
  end.

Lemma Soundness_ver (C : Category) (CC : CartClosedCat C) : 
forall v Γ A, (exists t, (Γ ⊢ t [:] A)) -> inhabited (Hom (VAL_Cntxt C CC v Γ) (v A)).
Proof.
  intros v Γ A H.
  elim H.
  intros. 
  induction H0.
  - apply inhabits.
  rewrite VAL_top.
  exact (Top_mor).
  - apply inhabits; simpl.
  exact (@Second C CC (VAL_Cntxt C CC v Γ) (v A) ).
  - assert (H1 : (exists t : Trm, Γ ⊢ t [:] A)). 
    { exists (hyp i). exact H0. } 
  apply IHTyty in H1.
  induction H1; apply inhabits.
  exact (Compose X (@First C CC (VAL_Cntxt C CC v Γ) (v B))).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v (A :: Γ)) → v B)). 
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t. 
  rewrite VAL_imp; simpl in Inh. 
  induction Inh; apply inhabits. 
  exact (@Lam C CC (VAL_Cntxt C CC v Γ) (v A) (v B) X). 
  - assert (Inh1 : inhabited ((VAL_Cntxt C CC v Γ) → v (Imp A B))).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ((VAL_Cntxt C CC v Γ) → v A)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  rewrite VAL_imp in Inh1.
  induction Inh1, Inh2; apply inhabits.
  assert (Y : ((VAL_Cntxt C CC v Γ) → (Prod_obj (Exp_obj (v B) (v A))) (v A ))).
  { exact (@Prod_mor C CC ((VAL_Cntxt C CC v Γ)) (Exp_obj (v B) (v A)) (v A) X X0 ). }
  assert (Z : (Prod_obj (Exp_obj (v B) (v A)) (v A)) → v B ).
  { exact (@Exp_app C CC (v A) (v B)). }
  exact (Compose Z Y).
  - assert (Inh1 : inhabited ((VAL_Cntxt C CC v Γ) → v A)).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ((VAL_Cntxt C CC v Γ) → v B)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  induction Inh1, Inh2; apply inhabits.
  rewrite VAL_cnj.
  exact (@Prod_mor C CC (VAL_Cntxt C CC v Γ) (v A) (v B) X X0).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v Γ) → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : (Prod_obj (v A) (v B) ) → v A).
  { exact (@First C CC (v A) (v B)). }
  exact (Compose Y X).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v Γ) → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : (Prod_obj (v A) (v B) ) → v B).
  { exact (@Second C CC (v A) (v B)). }
  exact (Compose Y X).
Defined.

Theorem Soundness : (forall A Γ, (exists t, (Γ ⊢ t [:] A)) -> (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A)))).
Proof. 
assert (S : (forall (C : Category) (CC : CartClosedCat C) v Γ A, (exists t, (Γ ⊢ t [:] A)) -> inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))) -> (forall A Γ, (exists t, (Γ ⊢ t [:] A)) -> (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))))).
auto.
apply S.
apply Soundness_ver.
Defined. 

Fixpoint Cnj_Cntxt (Γ : list Typ) := 
  match Γ with 
    | nil => Top
    | A :: Γ' => Cnj (Cnj_Cntxt Γ') A 
  end.

Definition V_STT : VAL STT_as_a_Cat STT_as_a_CCC.
Proof.
apply (makeVAL STT_as_a_Cat STT_as_a_CCC) with (V := (fun A : Typ => A)).
all: simpl; auto.
Defined.

Lemma cntx_1 : forall Γ, VAL_Cntxt STT_as_a_Cat STT_as_a_CCC V_STT Γ = Cnj_Cntxt Γ.
Proof.
intros.
induction Γ.
simpl; auto.
simpl.
rewrite IHΓ.
auto.
Defined.

Lemma imp_cntx_1 : forall A B t, (⊢ t
     [:] (B ⊃ A)) -> [ B ] ⊢ (app t (hyp 0)) [:] A.
Proof. 
  intros A B t H.
  assert (K : [B] ⊢ t [:] (B ⊃ A)).
  apply weakening_weak with (Γ := nil) (Δ := [B]) (t := t).
  auto.
  assert (L : [B] ⊢ (hyp 0) [:] B).
  apply STT_hypO.
  apply STT_app with (A:=B) (B:=A).
  all: auto.
Defined.

Lemma val_1 : forall A, V_STT A = A.
Proof.
intros.
compute.
auto.
Defined.

Theorem Completeness : 
forall A Γ, (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))) -> (exists t, ( [ Cnj_Cntxt Γ ] ⊢ t [:] A)).
Proof.
intros.
assert (K : inhabited (Hom (VAL_Cntxt STT_as_a_Cat STT_as_a_CCC V_STT Γ) (V_STT A))).
apply H.
elim K.
intros L.
simpl Obj in *; simpl Hom in *.
rewrite cntx_1 with (Γ := Γ) in L.
assert (L1 : ⊢ proj1_sig L
  [:] ((Cnj_Cntxt Γ) ⊃ V_STT A)).
exact (proj2_sig L).
assert (L2 : [ Cnj_Cntxt Γ ] ⊢ (app (proj1_sig L) (hyp 0))
     [:] (V_STT A)).
apply imp_cntx_1 with ( B := Cnj_Cntxt Γ) (A := V_STT A).
auto.
rewrite val_1 in L2. 
exists (app (proj1_sig L) (hyp 0)).
auto.
Defined.