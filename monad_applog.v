(* Műveletek, amik elromolanak: - kivezet nat-ból.*)

Require Import Arith.

(* safe_minus: csak akkor von ki, ha az eredmény nem negatív. *)
Definition safe_minus (a b : nat) : option nat :=
  if a <? b then None else Some (a - b).

Locate "<?".
Print Nat.ltb.

Print option. (*Option monád, maybe monád: kivételek kezelése*)

(* Próbák: *)
Compute (safe_minus 10 3). (* = Some 7 *)
Compute (safe_minus 5 8).  (* = None *)

(*Rossz láncolás: A Végzet Piramisa*)

(* (a - b) - c *)
Definition chained_subtraction_1 (a b c : nat) : option nat :=
  match (safe_minus a b) with
  | None => None              (*gyors kilépési pont*)
  | Some result1 =>           (*kicsomagol, végrehajt, visszacsomagol*)
      match (safe_minus result1 c) with 
      | None => None          (*gyors kilépési pont*)
      | Some result2 =>
          Some result2 
      end
  end.

(*Gusztustalan.*)

(*Hozzáveszünk az option típuskonstruktorhoz egy láncoló parancsot: "bind" és egy láncolás vége parancsot: "return". bind egy MA csomagot és egy A-> MB függvényt (Kleisli-morfizmus) eszik és egy MB csomagot ad vissza.

Option monád bind és return parancsa *)

Definition bind_opt {A B: Type} (opt_a : option A) (f : A -> option B) : option B :=
  match opt_a with
  | Some a => f a      (* "létező érték" esetén továbbadja f-nek *)
  | None   => None      (* "nem létezés" esetén kilép. *)
  end.

Definition return_opt {A : Type} (x : A) : option A :=
  Some x.

(* A láncolt kivonás: szép megoldás. *)
Definition chained_subtraction_2 (a b c : nat) : option nat :=
  bind_opt (safe_minus a b) (fun result1 =>
  bind_opt (safe_minus result1 c) (fun result2 =>
  return_opt result2)).

Compute (chained_subtraction_2 10 3 2). (* = Some 5 *)
Compute (chained_subtraction_2 10 12 3). (* = None, az első lépésnél elhasal*)

(* Haskellization:

Notation "x '>>=' f" := (bind_opt x f) (at level 70, no associativity) : type_scope.

Definition chained_subtraction_3 (a b c : nat) : option nat :=
  (safe_minus a b) >>= (fun result1 =>
  (safe_minus result1 c) >>= (fun result2 =>
  return_opt result2)).
*)


(* A (doboz, bind, return) hármas a "monád" struktúra. M: típuskonstruktor ("doboz") (ez fent az option). A return (vagy unit): betesz egy értéket a dobozba. 

        return : A -> M A

A bind függvény (>>=): összeláncol egy dobozolt értéket egy olyan függvénnyel, ami egy sima értékből csinál egy új dobozoltat

        bind : M A -> (A -> M B) -> M B

Ahhoz, hogy valami monád legyen, teljesítenie kell három törvényt:

        bal-identitás: bind (return x) f = f x      / a bind függvényhívás

        jobb-identitás: bind m return = m           / return a vége

        bind (bind m f) g = bind m (fun x => bind (f x) g) / bind láncol*)

Class Monad : Type := mk_monad {
  M : Type -> Type;
  bind : forall {A B}, M A -> (A -> M B) -> M B;
  unit : forall {A}, A -> M A;

  left_id_law : forall A B (x:A) (f:A->M B), bind (unit x) f = f x;
  right_id_law : forall A (m:M A), bind m unit = m;
  assoc_law : forall A B C (m:M A) (f:A->M B) (g:B->M C),
    bind (bind m f) g = bind m (fun x => bind (f x) g)
}.

Theorem Option_is_a_Monad : Monad.
Proof.
apply mk_monad with (M := option) (bind := @bind_opt) (unit := @return_opt).
  - intros; simpl; auto.
  - intros A ma; induction ma; compute; auto.
  - intros A B C ma f g; induction ma; compute; auto. 
Defined. 

(* Adatok: neveket, életkorok. *)
Require Import List.
Import ListNotations.

(* name mező típusa *)
Inductive name : Set := | Anna | Béla | Cili.

(* name egyenlősége eldönthető: name_eq_dec *)
Lemma name_eq_dec : forall k1 k2 : name, {k1 = k2} + {k1 <> k2}.
Proof. induction k1, k2; try (left; reflexivity); (right; discriminate). Defined.

Definition data : list (name * nat) :=
  [ (Anna, 30); (Béla, 45) ].

Definition age := nat.

(* Vagy megtalálunk egy embert és a korát: (Some kor), vagy nem (None). *)
Fixpoint find_age (na : name) (l : list (name * age)) : option age :=
  match l with
  | [] => None
  | (k, age) :: rest => if (name_eq_dec k na) then Some age else find_age na rest
  end.

(* Feladat: keressük meg Anna korát, és vonjunk le belőle 5 évet! (egy pályázathoz kell???)

Két hibalehetőséget:

    Lehet, hogy Anna nincs is az adatbázisban (find_age None-t ad).

    Lehet, hogy a kivonás sikertelen (pl. ha 2 éves korából akarnánk 5-öt levonni). *)

Definition find_and_subtract (na : name) (k : age) (l : list (name * age)) : option age :=
  bind_opt (find_age na l) (fun age =>
  bind_opt (safe_minus age k) (fun newage =>
  return_opt newage )).

Compute (find_and_subtract Anna 5 data). (* = Some 25 *)
Compute (find_and_subtract Anna 40 data). (* = None (a kivonás hibája) *)
Compute (find_and_subtract Cili 10 data). (* = None (a keresés hibája) *)













