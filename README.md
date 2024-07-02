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
the standard surface form is

: ````theorem name_of_the_theorem : proposition_of_the_theorem````, 

however deep in it the meaning is: 
: ````definition name_of_the_inhabitant : type_of_the_inhabitans_where_it_lives := the_inhabitant````


