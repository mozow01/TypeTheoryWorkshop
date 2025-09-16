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
intros.
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
