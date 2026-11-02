module

public import Mathlib.Data.Rat.Cast.CharZero
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.FeasibleRegion

public section

open scoped Matrix

section Definition122

variable {m n p : ℕ}

/-- Definition 1.22. The mixed integer linear set cut out by rational data `A`, `G`, and `b` is
the nonnegative mixed-integer feasible region
`{(x, y) ∈ ℤ_+^n × ℝ_+^p | A x + G y ≤ b}`. -/
abbrev rationalMixedIntegerLinearSet
    (A : Matrix (Fin m) (Fin n) ℚ)
    (G : Matrix (Fin m) (Fin p) ℚ)
    (b : Fin m → ℚ) : Set (MixedRealPoint n p) :=
  milp_feasible_set (A.map (Rat.castHom ℝ)) (G.map (Rat.castHom ℝ)) fun i ↦ (b i : ℝ)

/-- Membership in `rationalMixedIntegerLinearSet A G b` means satisfying the rational mixed linear
system `A x + G y ≤ b`, coordinatewise nonnegativity of `x` and `y`, and integrality of `x`. -/
theorem mem_rationalMixedIntegerLinearSet_iff
    {A : Matrix (Fin m) (Fin n) ℚ}
    {G : Matrix (Fin m) (Fin p) ℚ}
    {b : Fin m → ℚ}
    {xy : MixedRealPoint n p} :
    xy ∈ rationalMixedIntegerLinearSet A G b ↔
      ((A.map (Rat.castHom ℝ)) *ᵥ xy.1 + (G.map (Rat.castHom ℝ)) *ᵥ xy.2 ≤ fun i ↦ (b i : ℝ)) ∧
        0 ≤ xy.1 ∧ 0 ≤ xy.2 ∧ ∀ j : Fin n, ∃ z : ℤ, xy.1 j = (z : ℝ) :=
  -- Reuse the canonical real-valued MILP feasible-set membership criterion after casting the
  -- rational presentation data into `ℝ`.
  mem_milp_feasible_set_iff
    (A := A.map (Rat.castHom ℝ))
    (G := G.map (Rat.castHom ℝ))
    (b := fun i ↦ (b i : ℝ))
    (xy := xy)

end Definition122
