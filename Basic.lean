-- Ellenőrizzük, hogy a Lean4 és a Mathlib4 betöltődött-e:

theorem flipterms : forall A B : Prop, A ∧ B → B ∧ A
:=
by
intros A B h
-- apply?
exact And.comm.mp h
