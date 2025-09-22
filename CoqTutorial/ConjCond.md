## 2. Rész: A konjunkció ( /\ ) és a koncicionális

Konjunkció: ... és ... ( A /\ B ).

* **Bevezetési szabály (/\ I):**

$$\dfrac{A\qquad B}{A\land B}\qquad \dfrac{\vdash a: A \quad \vdash b:B}{\vdash \text{conj}ab:A\land B}$$

A /\ B bizonyításához le kell vezetni A-t is és B-t is külön-külön, ezt a `split` taktika hívja elő.

* **Kiküszöbölési szabály (/\ E):**

$$\dfrac{A_1\land A_2}{A_i}\quad (i=1;2)\qquad \dfrac{\vdash p:A_1\land A_2}{\vdash \text{proj}_i \; p:A_i} \quad (i=1;2)$$

Ha tudjuk, hogy A /\ B levezethető, akkor A is és B is levezethető. A `destruct H as [HA HB]` taktika egy `H : A /\ B` hipotézist két új hipotézisre bont: `HA : A` és `HB : B`.

### Mintapéldák

**2.1 Kommutativitás**

````coq
Example problem_comm : forall A B : Prop, A /\ B -> B /\ A.
````

<details>
<summary>1. megoldás (destruct + split)</summary>

````coq
Proof.
  intros A B H.
  destruct H as [HA HB].
  split.
  - exact HB. (*az indentelés célra fókuszál*)
  - exact HA.
Qed.
````

Magyarázat: Először destruct-tal szétszedjük az A /\ B feltételt. Utána split-tel kettébontjuk a B /\ A célt. Az első alcél (B) megegyezik HB-vel, a második (A) pedig HA-val.

</details>

<details>
<summary>2. megoldás (rövidített intros)</summary>

````coq
Proof.
  intros A B [HA HB].
  split.
  - assumption.
  - assumption.
Qed.
````

Magyarázat: Az intros is képes destruálni. Az intros [HA HB] egyből szétszedi a következő bevezetendő /\ típusú hipotézist.

</details>

**2.2 Currying**

````coq
Example problem_curry : forall A B C : Prop, ((A /\ B) -> C) -> (A -> B -> C).
````

<details>
<summary>1. megoldás</summary>

````coq
Proof.
  intros A B C H H_A H_B.
  apply H.
  split.
  - exact H_A.
  - exact H_B.
Qed.
````

Magyarázat: A cél C, amihez a H feltétel (A /\ B)-t kér. Ezt a split segítségével, H_A-ból és H_B-ből rakjuk össze.

</details>
<details>
<summary>2. megoldás (auto)</summary>

````coq
Proof.
  auto. (* ezt az AI csinálta, majd lesz tanukságosabb :D *)
Qed.
````

</details>

**2.3 Uncurrying**

````coq
Example problem_uncurry : forall A B C : Prop, (A -> B -> C) -> ((A /\ B) -> C).
````

<details>
<summary>1. megoldás (destruct)</summary>

````coq
Proof.
  intros A B C H H_AB.
  destruct H_AB as [HA HB].
  apply H.
  - exact HA.
  - exact HB.
Qed.
````

Magyarázat: A H : A -> B -> C feltétel alkalmazásához két argumentum kell: egy A és egy B. Ezeket a destruct H_AB segítségével nyerjük ki.

</details>
<details>
<summary>2. megoldás (rövidített intros)</summary>

````coq
Proof.
  intros A B C H [HA HB].
  apply H.
  - assumption.
  - assumption.
Qed.
````
</details>

**2.4 Disztributivitás**
````coq
Example practice_2_1 : forall A B C : Prop, (A -> B /\ C) -> (A -> B) /\ (A -> C).
````
<details>
<summary>1. megoldás</summary>
````coq
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
````
</details>
<details>
<summary>2. megoldás (assert)</summary>
````coq
Proof.
  intros A B C H.
  split.
  - intros HA.
    assert (K : B /\ C).
    { apply H. exact HA. } (* assert után illik fókuszálni zárójellel*)
    destruct K as [HB HC].
    exact HB.
  - intros HA.
    assert (K : B /\ C).
    { apply H; assumption. }
    destruct K; assumption.
Qed.
````
</details>

### További feladatok megoldásokkal

**2.5 Disztributivitás fordítva**
````coq
Example practice_2_2 : forall A B C : Prop, (A -> B) /\ (A -> C) -> (A -> B /\ C).
````
<details>
<summary>1. megoldás</summary>

````coq
Proof.
  intros A B C H.
  destruct H as [H_AB H_AC].
  intros HA.
  split.
  - apply H_AB. exact HA.
  - apply H_AC. exact HA.
Qed.
````

</details>
<details>
<summary>2. megoldás (rövidítve)</summary>

````coq
Proof.
  intros A B C [H_AB H_AC] HA.
  split.
  - apply H_AB; assumption.
  - apply H_AC; assumption.
Qed.
````
  
</details>

**2.6 Modus Ponens /\ -val**

````coq
Example practice_2_3 : forall A B : Prop, A /\ (A -> B) -> B.
````

<details>
<summary>1. megoldás</summary>

  ````coq
Proof.
  intros A B H.
  destruct H as [HA H_AB].
  apply H_AB.
  exact HA.
Qed.
````

</details>
<details>
<summary>2. megoldás (rövidített intros)</summary>
````coq
Proof.
  intros A B [HA H_AB].
  apply H_AB; assumption.
Qed.
````
  
</details>

**2.7 És bevezetés**

````coq
Example practice_2_4 : forall A B : Prop, A -> B -> A /\ B.
````

<details>
<summary>1. megoldás</summary>
  
````coq
Proof.
  intros A B HA HB.
  split.
  - exact HA.
  - exact HB.
Qed.
````
  
</details>
