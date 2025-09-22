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
  
$$\dfrac{\begin{matrix} A \newline \vdots \newline B \end{matrix}}{A\to B} \qquad\dfrac{x:A\vdash p(x):B}{\vdash\lambda x. p(x):A\to B}$$

Az `A -> B` állítás bizonyításához tételezzük fel `A`-t, és ebből vezessük le `B`-t.

Coq taktika: a kondicionális (A->B) bevezetési szabálya konklúziójának illesztése a célra.

### Mintapéldák

**1.1 (I-kombinátor)**

````coq
Example problem_I_comb : forall A : Prop, A -> A.
````

<details>
<summary>1. megoldás (direkt)</summary>
  
````coq
Proof.
  intros A H.
  exact H.
Qed.
````
  
Magyarázat: Az intros A H bevezeti a Prop típusú A változót és a H : A feltételt. Ekkor a célunk A lesz, ami pontosan megegyezik H-val.

</details>

<details>
<summary>2. megoldás (assumption)</summary>

````coq
Proof.
  intros A H.
  assumption.
Qed.
````
  
Magyarázat: Az assumption taktika megtalálja, hogy a cél (A) már szerepel a hipotézisek között (H : A), és befejezi a bizonyítást.

</details>


**1.2 Weakening (az igaz mindenből következik, K-kombinátor)**

````coq
Example problem_verum_ex : forall A B : Prop, A -> (B -> A).
````
<details>
<summary>1. megoldás (lépésenként)</summary>

  ````coq
Proof.
  intros A B H_A H_B.
  exact H_A.
Qed.
````

Magyarázat: Két intros-szal bevezetjük az összes feltételt. A cél (A) már szerepel a feltételek között (H_A), a felesleges H_B hipotézist figyelmen kívül hagyjuk.

</details>


**1.3 Láncszabály (S-kobinátor)**

````coq
Example problem_chain : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
````

<details>
<summary>1. megoldás (visszafelé apply)</summary>

````coq
Proof.
  intros A B C H_AB H_BC H_A.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.
````

Magyarázat: A Coq visszafelé építi fel a láncot: az apply H_BC a C célt B-re cseréli, majd az apply H_AB a B célt A-ra, ami már adott.

</details>

<details>
<summary>2. megoldás (direkt term)</summary>

````coq
Proof.
  intros A B C H_AB H_BC H_A.
  exact (H_BC (H_AB H_A)).
Qed.
````

Magyarázat: A bizonyításterm explicit felírásával egy lépésben megadjuk a megoldást.

</details>

### Gyakorló példák

**1.4 Láncszabály (más formában)**

````coq
Example practice_1_1 (A B C : Prop) (H_BC : B -> C) (H_AB : A -> B) : A -> C.
````
<details>

<summary>1. megoldás</summary>

````coq
Proof.
  intros H_A.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.
````
</details>

<details>
<summary>2. megoldás</summary>

````coq
Proof.
  intros H_A.
  exact (H_BC (H_AB H_A)).
Qed.
````
</details>

**1.5 Feltételek felhasználása**

````coq
Example practice_1_2 (A B C : Prop) (H_A : A) (H_AB : A -> B) : (B -> C) -> C.
````

<details>
<summary>1. megoldás</summary>

````coq
Proof.
  intros H_BC.
  apply H_BC.
  apply H_AB.
  exact H_A.
Qed.
````

</details>
<details>
<summary>2. megoldás</summary>

````coq
Proof.
  intros H_BC.
  exact (H_BC (H_AB H_A)).
Qed.
````

</details>

**1.6 Felesleges feltételek**

````coq
Example practice_1_3 (A B : Prop) : (A -> B) -> (B -> A) -> (A -> A).
````

<details>
<summary>1. megoldás</summary>
  
````coq
Proof.
  intros H_AB H_BA H_A.
  exact H_A.
Qed.
````

</details>
<details>
<summary>2. megoldás</summary>

```coq
Proof.
  intros H_AB H_BA.
  apply problem_I_comb.
Qed.
````coq

</details>
