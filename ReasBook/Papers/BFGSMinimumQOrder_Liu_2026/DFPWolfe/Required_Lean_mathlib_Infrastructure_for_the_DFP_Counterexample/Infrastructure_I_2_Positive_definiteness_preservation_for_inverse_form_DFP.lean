module

public import ReasLib.Optimization.DFP.InverseUpdate

open scoped Matrix

universe u

/- Infrastructure I.2 (Positive-definiteness preservation for inverse-form DFP) (1):
the inverse-form DFP update and its entrywise formula. -/
#check (Matrix.inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n], Matrix n n ℝ → (n → ℝ) → (n → ℝ) → Matrix n n ℝ)
#check (Matrix.inverseDFPUpdate_apply :
  ∀ {n : Type u} [Fintype n] (H : Matrix n n ℝ) (s y : n → ℝ) (i j : n),
    Matrix.inverseDFPUpdate H s y i j =
      H i j - (y ⬝ᵥ (H *ᵥ y))⁻¹ * ((H *ᵥ y) i * (y ᵥ* H) j) +
        (s ⬝ᵥ y)⁻¹ * (s i * s j))

/- Infrastructure I.2 (Positive-definiteness preservation for inverse-form DFP) (2):
positive definiteness and positive curvature make both denominators nonzero. -/
#check (Matrix.PosDef.inverseDFPUpdate_denominator_pos :
  ∀ {n : Type u} [Fintype n] {H : Matrix n n ℝ} {s y : n → ℝ},
    H.PosDef → 0 < s ⬝ᵥ y → 0 < y ⬝ᵥ (H *ᵥ y))
#check (Matrix.PosDef.inverseDFPUpdate_denominators_ne_zero :
  ∀ {n : Type u} [Fintype n] {H : Matrix n n ℝ} {s y : n → ℝ},
    H.PosDef → 0 < s ⬝ᵥ y → y ⬝ᵥ (H *ᵥ y) ≠ 0 ∧ s ⬝ᵥ y ≠ 0)

/- Infrastructure I.2 (Positive-definiteness preservation for inverse-form DFP) (3):
the update remains positive definite and hence symmetric. -/
#check (Matrix.PosDef.inverseDFPUpdate :
  ∀ {n : Type u} [Fintype n] {H : Matrix n n ℝ} {s y : n → ℝ},
    H.PosDef → 0 < s ⬝ᵥ y → (Matrix.inverseDFPUpdate H s y).PosDef)
#check (Matrix.PosDef.isHermitian :
  ∀ {n : Type u} [Fintype n] {H : Matrix n n ℝ}, H.PosDef → H.IsHermitian)
