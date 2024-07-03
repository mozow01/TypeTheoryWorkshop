Theorem comp_1 : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
firstorder.
Show Proof.
Qed.

(* (fun (A B C : Prop) (H : A -> B) 
   (H0 : B -> C) (H1 : A) =>
 (fun H2 : B => (fun H3 : C => H3) (H0 H2)) (H H1)) *)

Definition comp {A B C : Prop} 
   (f : B -> C) (g : A -> B)  := 
 (fun a : A => (fun b : B => (fun c : C => c) (f b)) (g a)).


Theorem comp_2 : forall (A B C D : Prop) (h: A -> B) (g: B -> C) (f: C -> D), comp f (comp g h) = comp (comp f g)h.
Proof.
intros.
compute.
reflexivity.
Qed.

