# Coq Tutorial

## Alapvető taktikák implikáció és konjunkció

A propozíciós logika (`->`, `/\`) konnektívumainak kezelése Coq-ban. 

Minden bizonyítási szabályt egy *taktikával* hívunk elő, amely visszakeresi a szabály leékséges feltételeit. A legfontosabbak:

* **`intros`**: az implikáció és az univerzális kvantor bevezetési szabálya konklúziójának illesztése a célra.
* **`apply H`**: a kondicionális (vagy az univerzális kvantor) kiküszöbölési szabálya főpremisszájának illesztése `H`-ra és a konklúziójának a célra.
* **`exact H`**: a cél pontosan megegyezik `H`-val.
* **`split`**: a konjunkció bevezetési szabályának alkalmazása a célra
* **`destruct H`**: a konjunkció (és az alternáció) kiküszöbölési szabálya főpremisszája illesztése a H-ra és a konklúziójának a célra 
* **`assumption`**: a cél megkeresése a feltételeink között.
* **`auto`**: A Coq legegyszerűbb automatizált bizonyításkeresője. 

---

## 1. Kondicionális (`->`)

Kondicionális: „ha..., akkor...”.

* **Kiküszöbölési szabály (`->E`, Modus Ponens)**:

$$\dfrac{A\to B\quad A}{B} \qquad \dfrac{\vdash f:A\to B\quad \vdash a:A}{\vdash f a : B} $$

`A -> B`, de `A` tehát `B`. 

Coq taktika: `apply H` - a kondicionális kiküszöbölési szabálya főpremisszájának (A->B) illesztése `H`-ra és a konklúziójának (B) a célra.

* **Bevezetési szabály (`->I`, dedukciótétel, függvényképzés)**:
  
$$\begin{matrix} A \\ \vdots \\ B \end{matrix} \qquad\dfrac{x:A\vdash p(x):B}{\vdash\lambda x. p(x):A\to B}$$

Az `A -> B` állítás bizonyításához tételezzük fel `A`-t, és ebből vezessük le `B`-t.

Coq taktika: a kondicionális (A->B) bevezetési szabálya konklúziójának illesztése a célra.

### Mintapéldák

**1.1 Identitás (Reflexivitás)**

```coq
Example problem_I_comb : forall A : Prop, A -> A.

<details>
<summary>1. megoldás (direkt)</summary>
Coq

Proof.
  intros A H.
  exact H.
Qed.

Magyarázat: Az intros A H bevezeti a Prop típusú A változót és a H : A feltételt. Ekkor a célunk A lesz, ami pontosan megegyezik H-val.

</details>

<details>
<summary>2. megoldás (assumption)</summary>
Coq

Proof.
  intros A H.
  assumption.
Qed.

Magyarázat: Az assumption taktika megtalálja, hogy a cél (A) már szerepel a hipotézisek között (H : A), és befejezi a bizonyítást.

</details>

<details>
<summary>3. megoldás (automatikus)</summary>
Coq

Proof.
  auto.
Qed.

Magyarázat: Az auto taktika automatikusan megoldja az ilyen egyszerű logikai azonosságokat.

</details>

1.2 Gyengítés (Tetszőleges feltétel hozzáadása)
Coq

Example problem_verum_ex : forall A B : Prop, A -> (B -> A).

<details>
<summary>1. megoldás (lépésenként)</summary>
Coq

Proof.
  intros A B H_A H_B.
  exact H_A.
Qed.

Magyarázat: Két intros-szal bevezetjük az összes feltételt. A célunk (A) már szerepel a feltételek között (H_A), a felesleges H_B hipotézist figyelmen kívül hagyjuk.

</details>
<details>
<summary>2. megoldás (auto)</summary>
Coq

Proof.
  auto.
Qed.

</details>

1.3 Láncszabály (Tranzitivitás)
Coq

Example problem_chain : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).

<details>
<summary>1. megoldás (visszafelé apply)</summary>
Coq

Proof.
  intros A B C H_AB H_BC H_A.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.

Magyarázat: A Coq visszafelé építi fel a láncot: az apply H_BC a C célt B-re cseréli, majd az apply H_AB a B célt A-ra, ami már adott.

</details>

<details>
<summary>2. megoldás (direkt terminus)</summary>
Coq

Proof.
  intros A B C H_AB H_BC H_A.
  exact (H_BC (H_AB H_A)).
Qed.

Magyarázat: A bizonyítási terminusok explicit felírásával egy lépésben megadjuk a megoldást.

</details>

További Feladatok Megoldásokkal

1.4 Láncszabály (más formában)
Coq

Example practice_1_1 (A B C : Prop) (H_BC : B -> C) (H_AB : A -> B) : A -> C.

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros H_A.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.

</details>
<details>
<summary>2. megoldás</summary>
Coq

Proof.
  intros H_A.
  exact (H_BC (H_AB H_A)).
Qed.

</details>

1.5 Feltételek felhasználása
Coq

Example practice_1_2 (A B C : Prop) (H_A : A) (H_AB : A -> B) : (B -> C) -> C.

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros H_BC.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.

</details>
<details>
<summary>2. megoldás</summary>
Coq

Proof.
  intros H_BC.
  exact (H_BC (H_AB H_A)).
Qed.

</details>

1.6 Felesleges feltételek
Coq

Example practice_1_3 (A B : Prop) : (A -> B) -> (B -> A) -> (A -> A).

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros H_AB H_BA H_A.
  exact H_A.
Qed.

</details>
<details>
<summary>2. megoldás</summary>
Coq

Proof.
  auto.
Qed.

</details>

2. Rész: A Konjunkció (/\) és az Implikáció

A konjunkció az „és” kapcsolat. A /\ B azt jelenti, hogy A és B is igaz.

    Bevezetési szabály (/\I): Egy A /\ B állítás bizonyításához le kell vezetni A-t is és B is külön-külön. Ezt a split taktikával tehetjük meg, ami a célt két alcélra bontja.

    Kiküszöbölési szabály (/\E): Ha tudjuk, hogy A /\ B igaz, akkor tudjuk A-t és tudjuk B is. A destruct H as [HA HB] taktika egy H : A /\ B hipotézist két új hipotézisre bont: HA : A és HB : B.

Mintapéldák

2.1 Kommutativitás
Coq

Example problem_comm : forall A B : Prop, A /\ B -> B /\ A.

<details>
<summary>1. megoldás (destruct + split)</summary>
Coq

Proof.
  intros A B H.
  destruct H as [HA HB].
  split.
  - exact HB.
  - exact HA.
Qed.

Magyarázat: Először destruct-tal szétszedjük az A /\ B feltételt. Utána split-tel kettébontjuk a B /\ A célt. Az első alcél (B) megegyezik HB-vel, a második (A) pedig HA-val.

</details>

<details>
<summary>2. megoldás (rövidített intros)</summary>
Coq

Proof.
  intros A B [HA HB].
  split.
  - assumption.
  - assumption.
Qed.

Magyarázat: Az intros is képes destruálni. Az intros [HA HB] egyből szétszedi a következő bevezetendő /\ típusú hipotézist.

</details>

2.2 Curry-Howard izomorfizmus (Currying)
Coq

Example problem_curry : forall A B C : Prop, ((A /\ B) -> C) -> (A -> B -> C).

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros A B C H H_A H_B.
  apply H.
  split.
  - exact H_A.
  - exact H_B.
Qed.

Magyarázat: A cél C, amihez a H feltétel (A /\ B)-t kér. Ezt a split segítségével, H_A-ból és H_B-ből rakjuk össze.

</details>
<details>
<summary>2. megoldás (auto)</summary>
Coq

Proof.
  auto.
Qed.

</details>

2.3 Curry-Howard izomorfizmus (Uncurrying)
Coq

Example problem_uncurry : forall A B C : Prop, (A -> B -> C) -> ((A /\ B) -> C).

<details>
<summary>1. megoldás (destruct)</summary>
Coq

Proof.
  intros A B C H H_AB.
  destruct H_AB as [HA HB].
  apply H.
  - exact HA.
  - exact HB.
Qed.

Magyarázat: A H : A -> B -> C feltétel alkalmazásához két argumentum kell: egy A és egy B. Ezeket a destruct H_AB segítségével nyerjük ki.

</details>
<details>
<summary>2. megoldás (rövidített intros)</summary>
Coq

Proof.
  intros A B C H [HA HB].
  apply H.
  - assumption.
  - assumption.
Qed.

</details>

További Feladatok Megoldásokkal

2.4 Disztributivitás
Coq

Example practice_2_1 : forall A B C : Prop, (A -> B /\ C) -> (A -> B) /\ (A -> C).

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros A B C H.
  split.
  - intros HA.
    apply H in HA.
    destruct HA as [HB HC].
    exact HB.
  - intros HA.
    apply H in HA.
    destruct HA as [HB HC].
    exact HC.
Qed.

</details>
<details>
<summary>2. megoldás (assert)</summary>
Coq

Proof.
  intros A B C H.
  split.
  - intros HA.
    assert (K : B /\ C).
    { apply H. exact HA. }
    destruct K as [HB HC].
    exact HB.
  - intros HA.
    assert (K : B /\ C).
    { apply H; assumption. }
    destruct K; assumption.
Qed.

</details>

2.5 Disztributivitás fordítva
Coq

Example practice_2_2 : forall A B C : Prop, (A -> B) /\ (A -> C) -> (A -> B /\ C).

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros A B C H.
  destruct H as [H_AB H_AC].
  intros HA.
  split.
  - apply H_AB. exact HA.
  - apply H_AC. exact HA.
Qed.

</details>
<details>
<summary>2. megoldás (rövidítve)</summary>
Coq

Proof.
  intros A B C [H_AB H_AC] HA.
  split.
  - apply H_AB; assumption.
  - apply H_AC; assumption.
Qed.

</details>

2.6 Modus Ponens /\-val
Coq

Example practice_2_3 : forall A B : Prop, A /\ (A -> B) -> B.

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros A B H.
  destruct H as [HA H_AB].
  apply H_AB.
  exact HA.
Qed.

</details>
<details>
<summary>2. megoldás (rövidített intros)</summary>
Coq

Proof.
  intros A B [HA H_AB].
  apply H_AB; assumption.
Qed.

</details>

2.7 Összerakás
Coq

Example practice_2_4 : forall A B : Prop, A -> B -> A /\ B.

<details>
<summary>1. megoldás</summary>
Coq

Proof.
  intros A B HA HB.
  split.
  - exact HA.
  - exact HB.
Qed.

</details>
<details>
<summary>2. megoldás (auto)</summary>
Coq

Proof.
  auto.
Qed.

</details>














## Egyszerű logikai feladatok ##

Igazold Coq-ban az alábbi állításokat!

1.1

```coq
Example problem_1 : forall A B : Prop, A /\ B -> B /\ A.
```
<details>
  <summary>1. megoldás.</summary>
  
```destruct``` taktikával és ```split```-tel:
  
```coq
Proof.
intros A B H.
destruct H as [H1 H2].
split.
 - exact H2.
 - exact H1.
Qed.
```
</details>

<details>
  <summary>2. megoldás.</summary>
  
```induction``` taktikával:

```coq
Proof.
intros A B H.
induction H as [a b].
Print conj.
exact (conj b a).
Qed.
```
</details>

1.2. 

```coq
Example problem_2 : forall A B C : Prop, (A -> B /\ C) -> (A -> B) /\ (A -> C).
```
<details>
  <summary>Megoldás.</summary>
  
```destruct``` taktikával és ```split```-tel:
  
```coq
Proof.
intros A B H.
destruct H as [H1 H2].
split.
 - exact H2.
 - exact H1.
Qed.
```
</details>
