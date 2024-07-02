# TypeTheoryWorkshop

## Lean4 & Mathlib4

Lean4: https://leanprover-community.github.io/learn.html

Creating a Lean4 project: https://leanprover-community.github.io/install/project.html 

````my_project```` is going to be your Lean4 project (within a folder say Dokumentumok/Lean, where you are in, in Terminal or "Parancssor" for win)  

````terminal
lake +leanprover/lean4:nightly-2024-04-24 new my_project math
````

Then ````my_project/my_project```` and ````my_project/my_project/Basic.lean```` are created, and within it, you can start to programming in Lean4.  

If you use VSCode, then **open** the project as a **folder** (my_project) and you have to activate the **Lean4 language extension,** then probably **restart** VSCode for a several times :D

To check that Mathlib works well, we create a theorem in Basic.lean (clearly, you can create new .lean files in this folder).

````lean
theorem flipterms : forall A B : Prop, A ∧ B → B ∧ A
````
the standard **surface form** is

````theorem name_of_the_theorem : proposition_of_the_theorem := proof_term````, 

however deep in it **the meaning is:**

````definition name_of_the_inhabitant : type_of_the_inhabitan_where_it_lives := the_inhabitant````

Here ````the_inhabitant```` is a term of program in Lean4's native **functional** language.

You start the so called proof mode by "by" then, you jump into an **imperative** language of tactics, that generates the proof terms. In the proof mode there are premisses and a goal in the following form: 

$$\dfrac{\begin{matrix}
\text{Premiss}1\\ 
\text{Premiss}2  \\  
\vdots \\
\text{Premiss}n
\end{matrix}}{\vdash \text{Goal}}$$

If the theorem is in the form "forall A, if B then C", then you can put the conditions A and B into the premmisses by the tactic **"intros".** If you name the contitions then they are going to get names: "intros A B" gives names to them. 

$$
\dfrac{|}{\vdash \forall A B C : Prop, B \to C}
\underset{\text{intros A B C h}}{\to} 
\dfrac{\begin{matrix}
A\text{ : Prop}\\ 
B\text{ : Prop}\\  
C\text{ : Prop}\\
h\text{ : B}\\
\end{matrix}}
{\vdash C}$$

Tactic **"apply?"** searches for a logical inference rule or a lemma in **Mathlib4** which potencially can prove the goal.



