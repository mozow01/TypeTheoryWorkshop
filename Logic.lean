theorem Curry (A B C : Prop) (x : A → (B → C)) : A ∧ B → C := by
  /- x : A → B → C ⊢ A ∧ B → C -/
  intro y
  /- x : A → B → C, y : A ∧ B ⊢ C -/
  apply x; apply And.left y; apply And.right y
  /- case #1: x : A → B → C, y : A ∧ B ⊢ A
     case #2: x : A → B → C, y : A ∧ B ⊢ B -/
#print Curry
/- theorem Curry :
∀ (A B C : Prop), (A → B → C) → A ∧ B → C :=
fun A B C x y => x y.left y.right -/

def Opt (A B : Type) : Option (A → B) → (Option A → Option B)
