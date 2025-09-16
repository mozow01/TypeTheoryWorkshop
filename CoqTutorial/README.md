## Egyszerű logikai feladatok ##

Igazold Coq-ban az alábbi állítársokat!

1.1

````coq
Example problem_1 : forall A B : Prop, A /\ B -> B /\ A.
````
<details>
  <summary>Megoldás.</summary>
````coq
Proof.
intros.
destruct H as [H1 H2].
split.
 - exact H2.
 - exact H1.
Qed.
````
</details>
