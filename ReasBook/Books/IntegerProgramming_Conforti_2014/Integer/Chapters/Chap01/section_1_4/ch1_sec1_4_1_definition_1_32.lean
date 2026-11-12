/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Operations

public section

/-- Definition 1.32. For `β : ℝ`, define the mixed-integer linear set
`S := {(x, y) ∈ ℤ × ℝ_+ | x - y ≤ β}` as a subset of `ℝ × ℝ`. -/
def mixedIntegerStrip (β : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Set.range (Int.cast : ℤ → ℝ)} ∩
    {p | 0 ≤ p.2} ∩
    {p | p.1 - p.2 ≤ β}

/-- Membership in `mixedIntegerStrip β` means that the first coordinate is an integer, the second
coordinate is nonnegative, and the defining inequality `x - y ≤ β` holds. -/
theorem mem_mixedIntegerStrip_iff
    {β : ℝ} {p : ℝ × ℝ} :
    p ∈ mixedIntegerStrip β ↔
      p.1 ∈ Set.range (Int.cast : ℤ → ℝ) ∧
        0 ≤ p.2 ∧
        p.1 - p.2 ≤ β := by
  -- Expand the defining intersection so membership is expressed as a conjunction.
  simp only [mixedIntegerStrip, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

/-- An integer-real pair `((x : ℝ), y)` belongs to `mixedIntegerStrip β` exactly when `y ≥ 0`
and `(x : ℝ) - y ≤ β`. -/
theorem intPair_mem_mixedIntegerStrip_iff
    {β : ℝ} {x : ℤ} {y : ℝ} :
    ((x : ℝ), y) ∈ mixedIntegerStrip β ↔
      0 ≤ y ∧
        (x : ℝ) - y ≤ β := by
  -- Reuse the canonical membership characterization and discharge the integrality condition.
  rw [mem_mixedIntegerStrip_iff]
  constructor
  · intro h
    rcases h with ⟨_, hy, hineq⟩
    exact ⟨hy, hineq⟩
  · intro h
    rcases h with ⟨hy, hineq⟩
    exact ⟨Set.mem_range_self x, hy, hineq⟩

end
