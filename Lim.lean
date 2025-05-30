import Mathlib

open Set Filter Topology Filter Classical Real

-- A tétel azt mondja, hogy ha f és g is a végtelenben a végetlenbe tart, akkor az összegük is oda tart.
theorem tendsto_add_at_top : forall (f g : ℝ → ℝ),
Tendsto f atTop atTop → Tendsto g atTop atTop → Tendsto (λ x => f x + g x) atTop atTop := by

  /- by után {...} kéne, de ezt helyetesíthetjük egy "behúzással", ami ezután a proof mode-t indítja el, egyébként minden by után "{" -t kérne -/
  intros f g h1 h2

  --rw?     rw?, apply?, exact? taktikák keresnek a Mathlib könyvtárban
  rw [@tendsto_atTop_atTop]
  rw [@tendsto_atTop_atTop] at h1 h2

  intros K

  -- innen a Mathlib nem tudja folytatni; "matek" kell hozzá: K/2-höz adnak a feltételek küszöbszámot
  have h1b := h1 (K/2)
  have h2b := h2 (K/2)

  /- h1b "exists"-szel kezdődik, továbbkövetkeztetni az "esists" kikküszöbölési szabályával lehet:

  Exists.elim.{u} {α : Sort u} {p : α → Prop} {b : Prop} (h₁ : ∃ x, p x) (h₂ : ∀ (a : α), p a → b) : b azaz

  h₁ : ∃ x, p x          h₂ : ∀ (a : α), p a → b
  ------------------------------------------------
                Exists.elim h₁ h₂ : b
  -/
  apply Exists.elim h1b
  intros i1 H1
  apply Exists.elim h2b
  intros i2 H2

  /- "exists"-tel kezdődő goal igazolásához meg kell adni egy dolgot:
  use = Exists.intro, ami
  Exists.intro.{u} {α : Sort u} {p : α → Prop} (w : α) (h : p w) : Exists p

  w : α                h : p w
  -----------------------------
  Exists.intro w h : Exists p

  tehát a küszöbszám max i1 i2 lesz.
  -/
  use (max i1 i2)
  intros x H3

  have K1 : i1 ≤ (max i1 i2) := by
    exact le_max_left i1 i2

  have K2 : i2 ≤ (max i1 i2) := by
    exact le_max_right i1 i2

  have K11 : i1 ≤ x := by
    exact Preorder.le_trans i1 (max i1 i2) x K1 H3

  have K21 : i2 ≤ x := by
    exact Preorder.le_trans i2 (max i1 i2) x K2 H3

  have M1 : (K/2) + (K/2) ≤ f x + g x := by
    exact add_le_add (H1 x K11) (H2 x K21)

  have M2 : (K/2) + (K/2) = K := by
    rw [@add_halves']

  exact le_of_eq_of_le (id (Eq.symm M2)) M1
