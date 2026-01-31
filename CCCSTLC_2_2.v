Require Import List Arith PeanoNat Lia.
Import ListNotations.  

(* ================================================================= *)
(*                    TYPES AND TERMS                                *)
(* ================================================================= *)

(* --- Types --- *)
Inductive ty : Set :=
  | Ty_Atomic  : nat -> ty      (* Atomic type *)
  | Ty_Unit   : ty               (* Unit type *)
  | Ty_Arrow : ty -> ty -> ty   (* Function type (Imp) *)
  | Ty_Prod  : ty -> ty -> ty.  (* Product type (Cnj) *)

(* --- Terms --- *)
Inductive tm : Set :=
  | tm_unit  : tm                      (* Unit term *)
  | tm_var  : nat -> tm               (* Variable (de Bruijn index) *)
  | tm_lam  : ty -> tm -> tm          (* Lambda abstraction *)
  | tm_app  : tm -> tm -> tm          (* Application *)
  | tm_pair : tm -> tm -> tm          (* Pair creation *)
  | tm_fst  : tm -> tm                (* First projection *)
  | tm_snd  : tm -> tm.               (* Second projection *)

Definition context := list ty.

(* ================================================================= *)
(*                    TYPING SYSTEM                                  *)
(* ================================================================= *)

Inductive typeability : context -> tm -> ty -> Prop :=
  | T_Unit : forall Gamma, 
      typeability Gamma tm_unit Ty_Unit

  | T_Var0 : forall Gamma A, 
      typeability (A :: Gamma) (tm_var 0) A

  | T_VarS : forall Gamma A B i,
      typeability Gamma (tm_var i) A -> 
      typeability (B :: Gamma) (tm_var (S i)) A

  | T_Lam : forall Gamma t A B,
      typeability (A :: Gamma) t B -> 
      typeability Gamma (tm_lam A t) (Ty_Arrow A B)

  | T_App : forall Gamma t s A B,
      typeability Gamma t (Ty_Arrow A B) -> 
      typeability Gamma s A -> 
      typeability Gamma (tm_app t s) B

  | T_Pair : forall Gamma t s A B,
      typeability Gamma t A -> 
      typeability Gamma s B -> 
      typeability Gamma (tm_pair t s) (Ty_Prod A B)

  | T_Fst : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) -> 
      typeability Gamma (tm_fst t) A

  | T_Snd : forall Gamma t A B,
      typeability Gamma t (Ty_Prod A B) -> 
      typeability Gamma (tm_snd t) B.

(* Notation for readability *)
Notation "Gamma '⊢' t '[:]' A" := (typeability Gamma t A) (at level 70, no associativity).

(* ================================================================= *)
(*                  OPERATIONS (LIFT, INSERT, SUBST)                 *)
(* ================================================================= *)

(* --- Shifting indices (Lift) --- *)
Fixpoint lift (n : nat) (k : nat) (t : tm) : tm := 
  match t with
  | tm_unit => tm_unit
  | tm_var i => 
      if k <=? i then tm_var (n + i) else tm_var i
  | tm_lam A t' => 
      tm_lam A (lift n (S k) t')
  | tm_app t1 t2 => 
      tm_app (lift n k t1) (lift n k t2)
  | tm_pair t1 t2 => 
      tm_pair (lift n k t1) (lift n k t2)
  | tm_fst t' => 
      tm_fst (lift n k t')
  | tm_snd t' => 
      tm_snd (lift n k t')
  end.

(* --- Inserting a type into context --- *)
(* Strict definition: fails (returns empty) if index out of bounds *)
Fixpoint insert_at (n : nat) (B : ty) (Gamma : context) : context :=
  match n, Gamma with
  | 0, _ => B :: Gamma
  | S n', h :: t => h :: insert_at n' B t
  | S n', [] => [] (* Strict rejection *)
  end.

(* --- Weakening Lemma --- *)
Theorem weakening_general : forall Gamma t A B n,
  Gamma ⊢ t [:] A ->
  (insert_at n B Gamma) ⊢ (lift 1 n t) [:] A.
Proof.
  intros Gamma t A B n H.
  revert n B.
  induction H; intros n0 B0; simpl.
  - (* T_Unit *)  
    apply T_Unit.
  - (* T_Var0 *)
    destruct n0 as [|n0].
    + (* n0 = 0: Insertion at head *)
      simpl. apply T_VarS. apply T_Var0.
    + (* n0 = S n0: Insertion deeper *)
      (* Context is (A :: Gamma), so insert_at (S n0) steps over A *)
      simpl. apply T_Var0.

  - (* T_VarS *)
    destruct n0 as [|n0].
    + (* n0 = 0 *)
      simpl. apply T_VarS. apply T_VarS. assumption.
    + (* n0 = S n0 *)
      simpl.
      specialize (IHtypeability n0 B0).
      destruct (n0 <=? i) eqn:Heq.
      * (* Case true *)
        apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var (S i)) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. simpl. reflexivity.
      * (* Case false *)
        apply T_VarS.
        replace (lift 1 n0 (tm_var i)) with (tm_var i) in IHtypeability.
        exact IHtypeability.
        unfold lift. rewrite Heq. reflexivity.

  - (* T_Lam *)
    apply T_Lam.
    (* Pass (S n0) to the induction hypothesis *)
    apply (IHtypeability (S n0) B0).
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
Defined.

(* --- Substitution --- *)
Fixpoint subst (k : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tm_unit => tm_unit
  | tm_var i =>
      if k =? i then s                (* Match: replace with s *)
      else if k <? i then tm_var (i - 1) (* Greater: decrement index *)
      else tm_var i                   (* Smaller: unchanged *)
  | tm_lam A t' => 
      (* Under lambda: increment index (S k) and lift s *)
      tm_lam A (subst (S k) (lift 1 0 s) t')
  | tm_app t1 t2 => 
      tm_app (subst k s t1) (subst k s t2)
  | tm_pair t1 t2 => 
      tm_pair (subst k s t1) (subst k s t2)
  | tm_fst t' => 
      tm_fst (subst k s t')
  | tm_snd t' => 
      tm_snd (subst k s t')
  end.

(* ================================================================= *)
(*                  HELPER LEMMAS FOR SUBSTITUTION                   *)
(* ================================================================= *)

(* Lemma 1: Lookup exactly at insertion point *)
Lemma nth_error_insert_at_eq : forall A (Gamma : list ty) n,
  n <= length Gamma -> nth_error (insert_at n A Gamma) n = Some A.
Proof.
  intros A Gamma n. revert Gamma.
  induction n as [|n IHn].
  - (* n = 0 *)
    intros Gamma Hlen. simpl. reflexivity.
  - (* n = S n *)
    intros Gamma Hlen.
    destruct Gamma as [|t Gamma'].
    + (* Gamma empty *)
      simpl in Hlen. lia. 
    + (* Gamma cons *)
      simpl. apply IHn. simpl in Hlen. lia.
Defined.

(* Lemma 2: Lookup before insertion point *)
Lemma nth_error_insert_at_lt : forall A (Gamma : list ty) n i,
  i < n -> nth_error (insert_at n A Gamma) i = nth_error Gamma i.
Proof.
  intros A Gamma n i Hlt. revert Gamma i Hlt.
  induction n as [|n IHn].
  - (* n = 0 *)
    intros Gamma i Hlt. inversion Hlt.
  - (* n = S n *)
    intros Gamma i Hlt.
    destruct Gamma as [|t Gamma'].
    + (* Gamma empty *)
      simpl. destruct i; reflexivity.
    + (* Gamma cons *)
      simpl. destruct i as [|i'].
      * (* i = 0 *) reflexivity.
      * (* i = S i' *)
        simpl. apply IHn. lia.
Defined.

(* Lemma 3: Lookup after insertion point *)
Lemma nth_error_insert_at_gt : forall A (Gamma : list ty) n i,
  n <= i -> nth_error (insert_at n A Gamma) (S i) = nth_error Gamma i.
Proof.
  intros A Gamma n i Hle. revert Gamma i Hle.
  induction n as [|n IHn].
  - (* n = 0 *)
    intros Gamma i Hle. simpl. reflexivity.
  - (* n = S n *)
    intros Gamma i Hle.
    destruct Gamma as [|t Gamma'].
    + (* Gamma empty *)
      simpl. destruct i; reflexivity.
    + (* Gamma cons *)
      simpl. destruct i as [|i'].
      * (* i = 0 *) lia.
      * (* i = S i' *)
        simpl. apply IHn. lia. 
Defined.

(* Lemma 4: Valid index implies length bound *)
Lemma nth_error_insert_at_valid : forall A (Gamma : list ty) n,
  nth_error (insert_at n A Gamma) n = Some A -> n <= length Gamma.
Proof.
  intros A Gamma n. revert Gamma.
  induction n as [|n IHn]; intros Gamma H.
  - (* n = 0 *) lia.
  - (* n = S n *)
    destruct Gamma.
    + (* Gamma nil *) simpl in H. discriminate.
    + (* Gamma cons *)
      simpl in H. simpl.
      apply IHn in H. lia.
Defined.

(* ================================================================= *)
(*                    MAIN SUBSTITUTION THEOREM                      *)
(* ================================================================= *)

Theorem substitution_lemma : forall Gamma t s A B n,
  (insert_at n A Gamma) ⊢ t [:] B ->
  Gamma ⊢ s [:] A ->
  Gamma ⊢ (subst n s t) [:] B.
Proof.
  intros Gamma t s A B n Ht Hs.
  remember (insert_at n A Gamma) as Gamma_ext eqn:Heq_ctx.
  revert Gamma n s A Heq_ctx Hs.
  
  induction Ht; intros Gamma0 n0 s0 A0 Heq_ctx Hs0; simpl.

  - (* T_Unit *) 
    apply T_Unit.

  - (* T_Var0 *)
    destruct n0 as [|n0]; simpl in Heq_ctx.
    + (* n0 = 0 *)
      injection Heq_ctx. intros. subst. simpl. assumption.
    + (* n0 = S n0 *)
      destruct Gamma0; simpl in Heq_ctx.
      * discriminate Heq_ctx.
      * injection Heq_ctx. intros. subst. simpl. apply T_Var0.

  - (* T_VarS *)
    destruct n0 as [|n0]; simpl in Heq_ctx.
    + (* n0 = 0 *)
      injection Heq_ctx. intros. subst. simpl.
      replace (i - 0) with i by lia.
      exact Ht.
      
    + (* n0 = S n0 *)
      destruct Gamma0; simpl in Heq_ctx.
      * discriminate Heq_ctx.
      * injection Heq_ctx. intros. subst. simpl.
        
        specialize (IHHt Gamma0 n0 s0 A0).
        assert (Heq_refl: insert_at n0 A0 Gamma0 = insert_at n0 A0 Gamma0). { reflexivity. }
        specialize (IHHt Heq_refl).

        destruct (n0 =? i) eqn:Heq_eq.
        
        (* --- EQUALITY BRANCH (n0 = i) --- *)
        -- apply Nat.eqb_eq in Heq_eq. subst.
           
           (* 1. Extraction: typeability -> nth_error *)
           assert (H_extract: forall G x T, G ⊢ tm_var x [:] T -> nth_error G x = Some T).
           { 
             intros G0 x0 T0 Htyp.
             remember (tm_var x0) as term eqn:Heqterm.
             generalize dependent x0.
             induction Htyp; intros x0 Heqterm; inversion Heqterm; subst; simpl; auto.
           }
           apply H_extract in Ht.
           
           (* 2. Combined proof of Length and Equality *)
           assert (H_combo: i <= length Gamma0 /\ A = A0).
           {
             clear - Ht.
             revert Gamma0 Ht.
             induction i; intros Gamma0 Ht; destruct Gamma0; simpl in Ht.
             - injection Ht. intros. subst. split; [ simpl; lia | reflexivity ].
             - injection Ht. intros. subst. split; [ simpl; lia | reflexivity ].
             - try discriminate. 
             - simpl. apply IHi in Ht. destruct Ht as [Hlen Heq].
               split; [ simpl; lia | assumption ].
           }
           
           destruct H_combo as [_ Heq]. subst.
           apply Hs0.

        (* --- INEQUALITY BRANCH (n0 <> i) --- *)
        -- apply Nat.eqb_neq in Heq_eq.
           destruct (S n0 <? S i) eqn:Heq_lt.

           (* Subcase 1: n0 < i *)
           {
             apply Nat.ltb_lt in Heq_lt.
             replace (i - 0) with i by lia.
             destruct i.
             - lia. 
             - (* i = S i0 *)
               apply T_VarS.
               
               (* Extraction *)
               assert (H_extract: forall G x T, G ⊢ tm_var x [:] T -> nth_error G x = Some T).
               { 
                 intros G0 x0 T0 Htyp.
                 remember (tm_var x0) as term eqn:Heqterm.
                 generalize dependent x0.
                 induction Htyp; intros x0 Heqterm; inversion Heqterm; subst; simpl; auto.
                
               
               }
               apply H_extract in Ht.
               
               (* Apply Lemma *)
               rewrite nth_error_insert_at_gt in Ht; [| lia].
               
               (* Back to Typing *)
               assert (H_back: forall G x T, nth_error G x = Some T -> G ⊢ tm_var x [:] T).
               {
                 intros G0 x0 T0 H. revert G0 H.
                 induction x0; intros G0 H; destruct G0; simpl in H; try discriminate.
                 - injection H. intros. subst. apply T_Var0. 
                 - apply T_VarS. apply IHx0. assumption.
               }
               apply H_back in Ht. assumption.
           }

           (* Subcase 2: n0 > i *)
           {
             apply Nat.ltb_ge in Heq_lt.
             apply T_VarS.
             
             (* Extraction *)
             assert (H_extract: forall G x T, G ⊢ tm_var x [:] T -> nth_error G x = Some T).
             { 
                 intros G0 x0 T0 Htyp.
                 remember (tm_var x0) as term eqn:Heqterm.
                 generalize dependent x0.
                 induction Htyp; intros x0 Heqterm; inversion Heqterm; subst; simpl; auto.
               
             }
             apply H_extract in Ht.
             
             (* Apply Lemma *)
             rewrite nth_error_insert_at_lt in Ht; [| lia].
             
             (* Back to Typing *)
             assert (H_back: forall G x T, nth_error G x = Some T -> G ⊢ tm_var x [:] T).
             {
                 intros G0 x0 T0 H. revert G0 H.
                 induction x0; intros G0 H; destruct G0; simpl in H; try discriminate.
                 - injection H. intros. subst. apply T_Var0.
                 - apply T_VarS. apply IHx0. assumption.
             }
             apply H_back in Ht. assumption.
           }
          
  - (* T_Lam *)
    simpl. apply T_Lam.
    eapply IHHt.
    + rewrite Heq_ctx. reflexivity.
    + change (A :: Gamma0) with (insert_at 0 A Gamma0). 
      apply weakening_general. exact Hs0.

  - (* T_App *)
    simpl. eapply T_App.
    + eapply IHHt1; eauto.
    + eapply IHHt2; eauto.

  - (* T_Pair *)
    simpl. apply T_Pair.
    + eapply IHHt1; eauto.
    + eapply IHHt2; eauto.

  - (* T_Fst *)
    simpl. eapply T_Fst. eapply IHHt; eauto.

  - (* T_Snd *)
    simpl. eapply T_Snd. eapply IHHt; eauto.
Defined.


(* ================================================================= *)
(*              OPERATIONAL SEMANTICS (SMALL-STEP)                   *)
(* ================================================================= *)

(* 1. TERMINAL VALUES *)
(* Terms that are considered "finished" results. *)
Inductive terminal : tm -> Prop :=
  | term_unit : terminal tm_unit
  | term_lam  : forall A t, terminal (tm_lam A t)
  (* A pair is a value ("terminal term") only if both components are values *)
  | term_pair : forall v1 v2,
      terminal v1 -> terminal v2 -> terminal (tm_pair v1 v2).

Reserved Notation "t '==>' t'" (at level 40).

(* 2. STEP RELATION *)
Inductive step : tm -> tm -> Prop :=
  
  (* --- BETA RULES (Computation) --- *)
  
  (* Function application: (\x.t) v ==> t[x:=v] *)
  (* Only fires if the argument (v2) is already a terminal value! (Call-by-Value) *)
  | ST_AppLam : forall A t1 v2,
      terminal v2 ->
      (tm_app (tm_lam A t1) v2) ==> (subst 0 v2 t1)

  (* Pair projection (fst): fst (v1, v2) ==> v1 *)
  | ST_FstPair : forall v1 v2,
      terminal v1 -> 
      terminal v2 ->
      (tm_fst (tm_pair v1 v2)) ==> v1

  (* Pair projection (snd): snd (v1, v2) ==> v2 *)
  | ST_SndPair : forall v1 v2,
      terminal v1 -> 
      terminal v2 ->
      (tm_snd (tm_pair v1 v2)) ==> v2

  (* --- CONGRUENCE RULES (Structural rules) --- *)

  (* Reduce left side of application *)
  | ST_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      (tm_app t1 t2) ==> (tm_app t1' t2)

  (* Reduce right side of application (only if left is value) *)
  | ST_App2 : forall v1 t2 t2',
      terminal v1 ->
      t2 ==> t2' ->
      (tm_app v1 t2) ==> (tm_app v1 t2')

  (* Reduce first component of a pair *)
  | ST_Pair1 : forall t1 t1' t2,
      t1 ==> t1' ->
      (tm_pair t1 t2) ==> (tm_pair t1' t2)

  (* Reduce second component of a pair (only if first is value) *)
  | ST_Pair2 : forall v1 t2 t2',
      terminal v1 ->
      t2 ==> t2' ->
      (tm_pair v1 t2) ==> (tm_pair v1 t2')

  (* Reduce argument of fst *)
  | ST_Fst1 : forall t1 t1',
      t1 ==> t1' ->
      (tm_fst t1) ==> (tm_fst t1')

  (* Reduce argument of snd *)
  | ST_Snd1 : forall t1 t1',
      t1 ==> t1' ->
      (tm_snd t1) ==> (tm_snd t1')
 
where "t '==>' t'" := (step t t').

(* ================================================================= *)
(*                        Canonical Form Lemma                       *)
(* ================================================================= *)

(* Defines the expected shape of a value based on its type.
   This function maps a term 'v' and a type 'T' to a Proposition.
   It acts as a single source of truth for Canonical Forms. *)
Definition canonical_property (v : tm) (T : ty) : Prop :=
  match T with
  (* Unit type: The value must be the unit constant *)
  | Ty_Unit => v = tm_unit
  
  (* Atomic type: No closed values exist for atomic types (Logical False) *)
  | Ty_Atomic _ => False
  
  (* Arrow type: The value must be a lambda abstraction *)
  | Ty_Arrow A B => exists t, v = tm_lam A t
  
  (* Product type: The value must be a pair of values *)
  | Ty_Prod A B => exists v1 v2, v = tm_pair v1 v2 /\ terminal v1 /\ terminal v2
  end.
  
(* Theorem: General Canonical Forms
   
   If a term 'v' is a terminal value and has type 'T' in an empty context,
   then it satisfies the 'canonical_property' for 'T'. 
*)
Theorem canonical_forms_lemma : forall v T,
  terminal v ->         (* Assumption 1: v is a value (terminal) *)
  [] ⊢ v [:] T ->       (* Assumption 2: v is well-typed in empty context *)
  canonical_property v T.
Proof.
  intros v T Val Typ.
  
  (* We proceed by induction on the structure of the TYPE 'T', not the term. *)
  destruct T.

  - (* Case: Ty_Atomic *)
    simpl.
    (* Invert the value and typing derivations to show contradiction.
       There are no constructors for Atomic types in the language. *)
    inversion Val; subst; inversion Typ; subst.

  - (* Case: Ty_Unit *)
    simpl.
    (* Invert derivations. Only tm_unit has type Ty_Unit and is a value. *)
    inversion Val; subst; inversion Typ; subst; try reflexivity.
   
  - (* Case: Ty_Arrow (Functions) *)
    simpl.
    inversion Val; subst; inversion Typ; subst.
    (* Success: The term must be a lambda *)
    exists t. reflexivity.
    
  - (* Case: Ty_Prod (Pairs) *)
    simpl.
    inversion Val; subst; inversion Typ; subst.
    (* Success: The term must be a pair. 
       Note: The typing rule for pairs implies components are well-typed,
       and the terminal rule for pairs implies components are terminal. *)
    exists v1, v2. split. 
    + reflexivity. 
    + split; assumption.
Qed.

(* --- Canonical Forms Lemmas --- *)
(* These lemmas state: "If a term is a Value AND has a specific Type,
   we know exactly which constructor was used." *)


Lemma canonical_forms_arrow : forall v A B,
  terminal v ->
  [] ⊢ v [:] (Ty_Arrow A B) ->
  exists t, v = tm_lam A t.
Proof.
  intros v A B Val Typ.
  apply canonical_forms_lemma in Typ; [| assumption].
  simpl in Typ.
  assumption.
Qed.

Lemma canonical_forms_prod : forall v A B,
  terminal v ->
  [] ⊢ v [:] (Ty_Prod A B) ->
  exists v1 v2, v = tm_pair v1 v2 /\ terminal v1 /\ terminal v2.
Proof.
  intros v A B Val Typ.
  apply canonical_forms_lemma in Typ; [| assumption].
  simpl in Typ.
  assumption.
Qed.


(* ================================================================= *)
(*            Preservation Theorem (Subject Reduction)               *)
(* ================================================================= *)

(* "If a term has type T and takes a step, the resulting term still has type T." *)

Theorem preservation : forall t t' T,
  [] ⊢ t [:] T ->
  t ==> t' ->
  [] ⊢ t' [:] T.
Proof.
  intros t t' T HT Hstep.
  generalize dependent T.
  
  (* Induction on the step derivation *)
  induction Hstep; intros T HT.

  (* --- BETA RULES --- *)
  
  - (* ST_AppLam: (\x.t1) v2 ==> t1[v2] *)
    (* 1. Invert the application typing to get types of function and argument *)
    inversion HT; subst.
    (* Now we have: 
       H2 (or similar): [] |- tm_lam A t1 : Ty_Arrow A0 T 
       H4 (or similar): [] |- v2 : A0 
       Note: The names H2, H4 depend on Coq version. We look at the context. *)
    
    (* 2. Invert the lambda typing to get the type of its body *)
    (* We look for the hypothesis stating the lambda is well-typed. *)
    (* In your error log, this was H3. *)
    inversion H3; subst. 
    
    (* Now we have: 
       H7 : (A0 :: []) |- t1 : T 
       H4 : [] |- v2 : A0 *)
       
    (* 3. Apply the Substitution Lemma *)
    (* We need to match the form (insert_at 0 A Gamma) *)
    change (A0 :: []) with (insert_at 0 A0 []) in H2.
    eapply substitution_lemma.
    + apply H2. (* The body t1 under context (A0 :: []) *)
    + apply H5. (* The argument v2 under empty context *)

  - (* ST_FstPair: fst (v1, v2) ==> v1 *)
    inversion HT; subst. (* Invert fst typing *)
    inversion H3; subst. (* Invert pair typing to get components *)
    assumption.

  - (* ST_SndPair: snd (v1, v2) ==> v2 *)
    inversion HT; subst.
    inversion H3; subst.
    assumption.

 (* --- CONGRUENCE RULES --- *)

  - (* ST_App1: t1 lép, t2 áll *)
    inversion HT; subst.
    eapply T_App.
    + (* Bal ág: t1 -> t1' *)
      apply IHHstep. 
      (* Itt a H2-t (vagy ami a t1 típusa) kell alkalmazni *)
      apply H2. 
    + (* Jobb ág: t2 változatlan *)
      (* Itt a H4-et (vagy ami a t2 típusa) kell alkalmazni *)
      apply H4.

  - (* ST_App2: v1 áll, t2 lép *)
    inversion HT; subst.
    eapply T_App.
    + (* Bal ág: v1 változatlan *)
      apply H3.
    + (* Jobb ág: t2 -> t2' *)
      apply IHHstep. 
      apply H5.

  - (* ST_Pair1: t1 lép *)
    inversion HT; subst.
    apply T_Pair.
    + apply IHHstep. apply H2.
    + apply H4.

  - (* ST_Pair2: t2 lép *)
    inversion HT; subst.
    apply T_Pair.
    + apply H3.
    + apply IHHstep. apply H5.

  - (* ST_Fst1: argumentum lép *)
    inversion HT; subst.
    eapply T_Fst.
    apply IHHstep. apply H1.

  - (* ST_Snd1: argumentum lép *)
    inversion HT; subst.
    eapply T_Snd.
    apply IHHstep. apply H1.
Qed.

(* ================================================================= *)
(*                       Progress Theorem                            *)
(* ================================================================= *)


(* "A well-typed closed term is either a Value or can take a Step." *)

(* Helper: No variables exist in an empty context *)
Lemma empty_context_no_var : forall i T,
  [] ⊢ (tm_var i) [:] T -> False.
Proof.
  intros i T H.
  inversion H. (* Both T_Var0 and T_VarS imply a non-empty context *)
Qed.

Theorem progress : forall t T,
  [] ⊢ t [:] T ->
  terminal t \/ exists t', t ==> t'.
Proof.
  intros t T HT.
  (* Induction on typing derivation *)
  remember [] as Gamma eqn:HeqG.
  induction HT; subst.

  - (* T_Unit *)
    left. apply term_unit.

  - (* T_Var0 - Impossible because A :: Gamma cannot be [] *)
    discriminate HeqG.

  - (* T_VarS - Impossible because B :: Gamma cannot be [] *)
    discriminate HeqG.

  - (* T_Lam *)
    left. apply term_lam.

  - (* T_App: t s *)
    right.
    (* Check progress of left side (t) *)
    destruct IHHT1 as [Val1 | [t1' Step1]]; auto.
    + (* Left side is Value. Check right side (s). *)
      destruct IHHT2 as [Val2 | [s' Step2]]; auto.
      * (* Both are Values! *)
        (* Use Canonical Forms: t must be a lambda *)
        pose proof (canonical_forms_arrow t A B Val1 HT1) as [body Heq].
        subst.
        (* Since t is a lambda and s is a value, ST_AppLam applies *)
        exists (subst 0 s body).
        apply ST_AppLam. assumption.
      * (* Right side steps -> ST_App2 *)
        exists (tm_app t s').
        apply ST_App2; assumption.
    + (* Left side steps -> ST_App1 *)
      exists (tm_app t1' s).
      apply ST_App1. assumption.

  - (* T_Pair *)
    destruct IHHT1 as [Val1 | [t' Step1]]; auto.
    + (* Left is Value. Check right. *)
      destruct IHHT2 as [Val2 | [s' Step2]]; auto.
      * (* Both Values -> The pair itself is a Value *)
        left. apply term_pair; assumption.
      * (* Right steps -> ST_Pair2 *)
        right. exists (tm_pair t s'). apply ST_Pair2; assumption.
    + (* Left steps -> ST_Pair1 *)
      right. exists (tm_pair t' s). apply ST_Pair1. assumption.

  - (* T_Fst *)
    right.
    destruct IHHT as [Val | [t' Step]]; auto.
    + (* Argument is Value. Must be a Pair (Canonical Forms) *)
      pose proof (canonical_forms_prod t A B Val HT) as [v1 [v2 [Heq [Val1 Val2]]]].
      subst.
      (* Reduces via ST_FstPair *)
      exists v1. apply ST_FstPair; assumption.
    + (* Argument steps -> ST_Fst1 *)
      exists (tm_fst t'). apply ST_Fst1. assumption.

  - (* T_Snd *)
    right.
    destruct IHHT as [Val | [t' Step]]; auto.
    + (* Canonical Forms *)
      pose proof (canonical_forms_prod t A B Val HT) as [v1 [v2 [Heq [Val1 Val2]]]].
      subst.
      exists v2. apply ST_SndPair; assumption.
    + (* Step *)
      exists (tm_snd t'). apply ST_Snd1. assumption.
Qed.

(* ================================================================= *)
(* DEFINITIONAL EQUALITY (BETA-ETA EQUIVALENCE)                      *)
(* ================================================================= *)

(* This relation defines when two terms are considered "equal" 
   in the mathematical sense of the Type Theory (STLC + Prod + Unit).
   
   It includes:
   1. Equivalence rules (Reflexivity, Symmetry, Transitivity)
   2. Congruence rules (Equality is preserved inside constructors)
   3. Beta rules (Computation steps)
   4. Eta rules (Uniqueness principles / Extensionality)
*)
 
Inductive beta_eta_eq : context -> tm -> tm -> ty -> Prop :=

  (* --- EQUIVALENCE RELATIONS --- *)
  
  | BE_Refl : forall Gamma t T,
      Gamma ⊢ t [:] T ->
      beta_eta_eq Gamma t t T

  | BE_Sym : forall Gamma t1 t2 T,
      beta_eta_eq Gamma t1 t2 T ->
      beta_eta_eq Gamma t2 t1 T

  | BE_Trans : forall Gamma t1 t2 t3 T,
      beta_eta_eq Gamma t1 t2 T ->
      beta_eta_eq Gamma t2 t3 T ->
      beta_eta_eq Gamma t1 t3 T

  (* --- CONGRUENCE RULES --- *)

  | BE_Abs : forall Gamma A B t1 t2,
      beta_eta_eq (A :: Gamma) t1 t2 B ->
      beta_eta_eq Gamma (tm_lam A t1) (tm_lam A t2) (Ty_Arrow A B)

  | BE_App : forall Gamma A B t1 t1' t2 t2',
      beta_eta_eq Gamma t1 t1' (Ty_Arrow A B) ->
      beta_eta_eq Gamma t2 t2' A ->
      beta_eta_eq Gamma (tm_app t1 t2) (tm_app t1' t2') B

  | BE_Pair : forall Gamma A B t1 t1' t2 t2',
      beta_eta_eq Gamma t1 t1' A ->
      beta_eta_eq Gamma t2 t2' B ->
      beta_eta_eq Gamma (tm_pair t1 t2) (tm_pair t1' t2') (Ty_Prod A B)

  | BE_Fst : forall Gamma A B t t',
      beta_eta_eq Gamma t t' (Ty_Prod A B) ->
      beta_eta_eq Gamma (tm_fst t) (tm_fst t') A

  | BE_Snd : forall Gamma A B t t',
      beta_eta_eq Gamma t t' (Ty_Prod A B) ->
      beta_eta_eq Gamma (tm_snd t) (tm_snd t') B

  (* --- BETA RULES --- *)

  | BE_BetaArrow : forall Gamma A B t1 t2,
      (A :: Gamma) ⊢ t1 [:] B ->
      Gamma ⊢ t2 [:] A ->
      beta_eta_eq Gamma (tm_app (tm_lam A t1) t2) (subst 0 t2 t1) B

  | BE_BetaFst : forall Gamma A B t1 t2,
      Gamma ⊢ t1 [:] A ->
      Gamma ⊢ t2 [:] B ->
      beta_eta_eq Gamma (tm_fst (tm_pair t1 t2)) t1 A

  | BE_BetaSnd : forall Gamma A B t1 t2,
      Gamma ⊢ t1 [:] A ->
      Gamma ⊢ t2 [:] B ->
      beta_eta_eq Gamma (tm_snd (tm_pair t1 t2)) t2 B

  (* --- ETA RULES --- *)

  | BE_EtaUnit : forall Gamma t,
      Gamma ⊢ t [:] Ty_Unit ->
      beta_eta_eq Gamma t tm_unit Ty_Unit

  | BE_EtaProd : forall Gamma A B t,
      Gamma ⊢ t [:] (Ty_Prod A B) ->
      beta_eta_eq Gamma t (tm_pair (tm_fst t) (tm_snd t)) (Ty_Prod A B)

  | BE_EtaArrow : forall Gamma A B t,
      Gamma ⊢ t [:] (Ty_Arrow A B) ->
      beta_eta_eq Gamma t (tm_lam A (tm_app (lift 1 0 t) (tm_var 0))) (Ty_Arrow A B).


Theorem step_implies_beta_eta : forall t t' T,
  ([] ⊢ t [:] T) ->     (* Ha t jól típusozott... *)
  t ==> t' ->         (* ...és t lép t'-be... *)
  (beta_eta_eq [] t t' T). (* ...akkor ők matematikailag egyenlőek. *)
Proof.
  intros t t' T HT Hstep.
  generalize dependent T.
  induction Hstep; intros T HT.
 
  - (* ST_AppLam: (\x.t12) v2 ==> t12[x:=v2] *)
    inversion HT; subst. inversion H3; subst.
    (* Most már megvannak a típusok, alkalmazzuk a szabályt *)
    apply BE_BetaArrow.
    + assumption. (* A függvény törzsének típusa *)
    + assumption. (* Az argumentum típusa *)

  - (* ST_FstPair: fst (v1, v2) ==> v1 *)
    inversion HT; subst. inversion H3; subst.
    eapply BE_BetaFst.
    + assumption.
    + eapply H8.

  - (* ST_SndPair: snd (v1, v2) ==> v2 *)
    inversion HT; subst. inversion H3; subst.
    eapply BE_BetaSnd.
    + eapply H6.
    + assumption.

  (* --- KONGRUENCIA SZABÁLYOK (Ahol csak beljebb lépünk) --- *)

  - (* ST_App1: t1 lép t1'-be *)
    inversion HT; subst.
    eapply BE_App.
    (* MOST MÁR MŰKÖDIK: Az IHHstep univerzális ("forall T, ...") *)
    + eapply IHHstep. apply H2. (* Itt a T automatikusan (Ty_Arrow A T) lesz *)
    + apply BE_Refl. assumption.

  - (* ST_App2: t2 lép *)
    inversion HT; subst.
    eapply BE_App.
    + apply BE_Refl. apply H3.
    + apply IHHstep. assumption.

  - (* ST_Pair1 *)
    inversion HT; subst.
    apply BE_Pair.
    + apply IHHstep. assumption.
    + apply BE_Refl. assumption.

  - (* ST_Pair2 *)
    inversion HT; subst.
    apply BE_Pair.
    + apply BE_Refl. assumption.
    + apply IHHstep. assumption.

  - (* ST_Fst1 *)
    inversion HT; subst.
    eapply BE_Fst.
    apply IHHstep. apply H1.

  - (* ST_Snd1 *)
    inversion HT; subst.
    eapply BE_Snd.
    apply IHHstep. apply H1.
Qed.

(* ================================================================= *)
(* NOTE: THE POWER OF REFERENTIAL TRANSPARENCY                       *)
(* ================================================================= *)
(* In STLC, the equation 'fst (pair x y) == x' is a mathematical truth.
   This property is called "Referential Transparency": we can always
   replace a term with its value without changing the program's behavior.

   In imperative languages (like C, Java, Python), this equality 
   DOES NOT hold due to "Side Effects".
   
   Counter-example in C: 
       int y = print("Boom!");
       fst(pair(5, y))
   
   - Left side (execution): Prints "Boom!", then returns 5.
   - Right side (replacement): Returns 5 (without printing).
   
   Since the observable behavior differs, they are NOT equivalent.
   STLC is "pure", meaning it models timeless logic, not stateful actions.
*)