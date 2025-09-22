# Coq Tutorial

## Alapvető taktikák (kondicionális) implikáció és konjunkció

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

## Kondicionális (`->`)

Kondicionális: „ha..., akkor...”.

* **Kiküszöbölési szabály (`->E`, Modus Ponens)**:

$$\dfrac{A\to B\quad A}{B} \qquad \dfrac{\vdash f:A\to B\quad \vdash a:A}{\vdash f a : B} $$

`A -> B`, de `A` tehát `B`. 

Coq taktika: `apply H` - a kondicionális kiküszöbölési szabálya főpremisszájának (A->B) illesztése `H`-ra és a konklúziójának (B) a célra.

* **Bevezetési szabály (`->I`, dedukciótétel, függvényképzés)**:
  
$$\dfrac{\begin{matrix} A \newline \vdots \newline B \end{matrix}}{A\to B} \qquad\dfrac{x:A\vdash p(x):B}{\vdash\lambda x. p(x):A\to B}$$

Az `A -> B` állítás bizonyításához tételezzük fel `A`-t, és ebből vezessük le `B`-t.

Coq taktika: a kondicionális (A->B) bevezetési szabálya konklúziójának illesztése a célra.

### Feladatok: 

[https://github.com/mozow01/TypeTheoryWorkshop/blob/main/CoqTutorial/Imp.md] 

## Konjunkció ( /\ )

Konjunkció: ... és ... ( A /\ B ).

* **Bevezetési szabály (/\ I):**

$$\dfrac{A\qquad B}{A\land B}\qquad \dfrac{\vdash a: A \quad \vdash b:B}{\vdash \text{conj}ab:A\land B}$$

A /\ B bizonyításához le kell vezetni A-t is és B-t is külön-külön, ezt a `split` taktika hívja elő.

* **Kiküszöbölési szabály (/\ E):**

$$\dfrac{A_1\land A_2}{A_i}\quad (i=1;2)\qquad \dfrac{\vdash p:A_1\land A_2}{\vdash \text{proj}_i \; p:A_i} \quad (i=1;2)$$

Ha tudjuk, hogy A /\ B levezethető, akkor A is és B is levezethető. A `destruct H as [HA HB]` taktika egy `H : A /\ B` hipotézist két új hipotézisre bont: `HA : A` és `HB : B`.

### Feladatok: 

[https://github.com/mozow01/TypeTheoryWorkshop/blob/main/CoqTutorial/ConjCond.md]
