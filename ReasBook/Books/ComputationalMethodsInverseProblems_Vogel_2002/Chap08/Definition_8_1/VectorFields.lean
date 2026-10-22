/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

public section

namespace VariationalRegularization

/-- The unit square `[0,1] × [0,1]` in `ℝ × ℝ`. -/
def unitSquare : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- A readable membership criterion for `unitSquare`. -/
theorem mem_unitSquare (p : ℝ × ℝ) :
    p ∈ unitSquare ↔ p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 := Iff.rfl

/-- The boundary of the unit square `[0,1] × [0,1]` in `ℝ × ℝ`. -/
def unitSquareBoundary : Set (ℝ × ℝ) :=
  {p | p ∈ unitSquare ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1)}

/-- A readable membership criterion for `unitSquareBoundary`. -/
theorem mem_unitSquareBoundary (p : ℝ × ℝ) :
    p ∈ unitSquareBoundary ↔
      p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
        (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = 1) := by
  rcases p with ⟨x, y⟩
  simp [unitSquareBoundary, unitSquare, Prod.le_def, and_assoc, and_left_comm, and_comm]

noncomputable section

/-- A `C¹` test vector field on the unit square with pointwise norm bounded by
`1` and vanishing boundary values. -/
structure UnitSquareTestField where
  v₁ : ℝ × ℝ → ℝ
  v₂ : ℝ × ℝ → ℝ
  contDiffOn_v₁ : ContDiffOn ℝ 1 v₁ unitSquare
  contDiffOn_v₂ : ContDiffOn ℝ 1 v₂ unitSquare
  norm_le_one :
    ∀ p, p ∈ unitSquare → Real.sqrt (v₁ p ^ 2 + v₂ p ^ 2) ≤ 1
  eq_zero_of_mem_boundary : ∀ p, p ∈ unitSquareBoundary → v₁ p = 0 ∧ v₂ p = 0

namespace UnitSquareTestField

/-- Build a unit-square test field from explicit component functions and
admissibility proofs. -/
def ofComponents
    (v₁ v₂ : ℝ × ℝ → ℝ)
    (contDiffOn_v₁ : ContDiffOn ℝ 1 v₁ unitSquare)
    (contDiffOn_v₂ : ContDiffOn ℝ 1 v₂ unitSquare)
    (norm_le_one : ∀ p, p ∈ unitSquare → Real.sqrt (v₁ p ^ 2 + v₂ p ^ 2) ≤ 1)
    (eq_zero_of_mem_boundary : ∀ p, p ∈ unitSquareBoundary → v₁ p = 0 ∧ v₂ p = 0) :
    UnitSquareTestField :=
  { v₁ := v₁
    v₂ := v₂
    contDiffOn_v₁ := contDiffOn_v₁
    contDiffOn_v₂ := contDiffOn_v₂
    norm_le_one := norm_le_one
    eq_zero_of_mem_boundary := eq_zero_of_mem_boundary }

/-- The source-facing admissibility conditions of a `UnitSquareTestField`. -/
theorem spec (v : UnitSquareTestField) :
    (ContDiffOn ℝ 1 v.v₁ unitSquare ∧ ContDiffOn ℝ 1 v.v₂ unitSquare) ∧
      (∀ p, p ∈ unitSquare → Real.sqrt (v.v₁ p ^ 2 + v.v₂ p ^ 2) ≤ 1) ∧
      (∀ p, p ∈ unitSquareBoundary → v.v₁ p = 0 ∧ v.v₂ p = 0) := by
  exact ⟨⟨v.contDiffOn_v₁, v.contDiffOn_v₂⟩, v.norm_le_one, v.eq_zero_of_mem_boundary⟩

end UnitSquareTestField

/-- The divergence of a unit-square test field, computed canonically from the
within-derivatives of its two components on `[0,1] × [0,1]`. -/
@[expose]
def unitSquareDivergence (v : UnitSquareTestField) (p : ℝ × ℝ) : ℝ :=
  fderivWithin ℝ v.v₁ unitSquare p (1, 0) + fderivWithin ℝ v.v₂ unitSquare p (0, 1)

/-- The defining formula for `unitSquareDivergence`. -/
theorem unitSquareDivergence_def (v : UnitSquareTestField) (p : ℝ × ℝ) :
    unitSquareDivergence v p =
      fderivWithin ℝ v.v₁ unitSquare p (1, 0) +
        fderivWithin ℝ v.v₂ unitSquare p (0, 1) := rfl

end

end VariationalRegularization
