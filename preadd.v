Require Import List.
Import ListNotations.

(* Típusok definiálása *)
Inductive Typ : Set :=
  | At : nat -> Typ          (* Atomikus típusok *)
  | Top : Typ                (* Triviális típus *)
  | Arr : Typ -> Typ -> Typ  (* Függvénytípus (A → B) *)
  | Bprod : Typ -> Typ -> Typ. (* Biproduct típus (A × B) *)

Notation "x ⇒ y" := (Arr x y) (at level 90, right associativity) : type_scope.
Notation "x × y" := (Bprod x y) (at level 80, right associativity) : type_scope.

(* Termek definiálása *)
Inductive Trm : Set :=
  | hyp : nat -> Trm   (* Változók, de Bruijn-indexekkel *)
  | lam : Typ -> Trm -> Trm  (* Lambda absztrakció *)
  | app : Trm -> Trm -> Trm  (* Függvényalkalmazás *)

  (* Biproduct termek *)
  | pair : Trm -> Trm -> Trm  (* Párosítás *)
  | fst : Trm -> Trm          (* Első komponens kinyerése *)
  | snd : Trm -> Trm          (* Második komponens kinyerése *)

  (* Injekciók *)
  | inl : Trm -> Trm          (* Baloldali injekció *)
  | inr : Trm -> Trm          (* Jobboldali injekció *)

  (* Biproduct elimináció *)
  | case : Trm -> Trm -> Trm -> Trm. (* Esetbontás biproduct típusra *)

(* Kontextus *)
Definition Cntxt := list Typ.

(* Típusolási szabályok *)
Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  (* Változó típusolás *)
  | STT_hypO : forall Γ A, 
      Tyty (A :: Γ) (hyp 0) A
  | STT_hypS : forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A

  (* Lambda absztrakció és alkalmazás *)
  | STT_lam : forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (A ⇒ B)
  | STT_app : forall Γ t s A B,
      Tyty Γ t (A ⇒ B) -> Tyty Γ s A -> Tyty Γ (app t s) B

  (* Biproduct típus szabályai *)
  | STT_pair : forall Γ t1 t2 A B,
      Tyty Γ t1 A -> Tyty Γ t2 B -> Tyty Γ (pair t1 t2) (A × B)

  | STT_fst : forall Γ t A B,
      Tyty Γ t (A × B) -> Tyty Γ (fst t) A
  | STT_snd : forall Γ t A B,
      Tyty Γ t (A × B) -> Tyty Γ (snd t) B

  (* Inklúziók *)
  | STT_inl : forall Γ t A B,
      Tyty Γ t A -> Tyty Γ (inl t) (A × B)
  | STT_inr : forall Γ t A B,
      Tyty Γ t B -> Tyty Γ (inr t) (A × B)

  (* Elimináció: Esetbontás biproduct típusra *)
  | STT_case : forall Γ t tc1 tc2 A B C,
      Tyty Γ t (A × B) ->
      Tyty Γ tc1 (A ⇒ C) ->
      Tyty Γ tc2 (B ⇒ C) ->
      Tyty Γ (case t tc1 tc2) C.
