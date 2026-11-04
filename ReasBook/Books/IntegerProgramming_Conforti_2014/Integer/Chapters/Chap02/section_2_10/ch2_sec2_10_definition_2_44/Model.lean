/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Real.Basic

public section

noncomputable section

/-- Definition 2.44 [Fixed-charge cost via a big-`M` formulation]: a scalar fixed-charge
formulation with fixed cost `c`, variable cost `h`, and upper bound `M`, where the decision
variables satisfy `y ≤ M * x`, `x ∈ {0, 1}`, and `0 ≤ y`. -/
structure FixedChargeBigM where
  fixedCost : ℝ
  variableCost : ℝ
  upperBound : ℝ
  fixedCost_nonneg : 0 ≤ fixedCost
  variableCost_nonneg : 0 ≤ variableCost
  upperBound_pos : 0 < upperBound

namespace FixedChargeBigM

/-- Construct a scalar fixed-charge big-`M` formulation from its fixed cost, variable cost, upper
bound, and the corresponding nonnegativity/positivity assumptions. -/
def ofData
    (fixedCost variableCost upperBound : ℝ)
    (h_fixedCost_nonneg : 0 ≤ fixedCost)
    (h_variableCost_nonneg : 0 ≤ variableCost)
    (h_upperBound_pos : 0 < upperBound) :
    FixedChargeBigM :=
  { fixedCost := fixedCost
    variableCost := variableCost
    upperBound := upperBound
    fixedCost_nonneg := h_fixedCost_nonneg
    variableCost_nonneg := h_variableCost_nonneg
    upperBound_pos := h_upperBound_pos }

/-- The feasible scalar pairs `(x, y)` for `P`: the usage variable `y` is nonnegative, bounded by
`P.upperBound * x`, and the activation variable `x` is binary. -/
def feasible
    (P : FixedChargeBigM)
    (x y : ℝ) : Prop :=
  0 ≤ y ∧ y ≤ P.upperBound * x ∧ (x = 0 ∨ x = 1)

/-- Membership in `P.feasible x y` is exactly the conjunction of nonnegativity of `y`, the
big-`M` upper bound `y ≤ P.upperBound * x`, and the binary constraint `x ∈ {0, 1}`. -/
theorem feasible_iff
    (P : FixedChargeBigM)
    {x y : ℝ} :
    P.feasible x y ↔ 0 ≤ y ∧ y ≤ P.upperBound * x ∧ (x = 0 ∨ x = 1) := by
  -- This companion theorem is just the definition of feasibility.
  rfl

/-- The linear fixed-charge objective value of a candidate pair `(x, y)` is
`P.fixedCost * x + P.variableCost * y`. -/
def objectiveValue
    (P : FixedChargeBigM)
    (x y : ℝ) : ℝ :=
  P.fixedCost * x + P.variableCost * y

/-- Unfolding equation for `P.objectiveValue x y`. -/
theorem objectiveValue_def
    (P : FixedChargeBigM)
    (x y : ℝ) :
    P.objectiveValue x y = P.fixedCost * x + P.variableCost * y := by
  -- This unfolding equation records the linear objective formula.
  rfl

/-- The source-facing modeled cost of usage level `y`: no fixed charge at `y = 0`, and fixed plus
variable charge otherwise. -/
def modeledCost
    (P : FixedChargeBigM)
    (y : ℝ) : ℝ :=
  if y = 0 then 0 else P.fixedCost + P.variableCost * y

/-- The modeled cost at `y = 0` is `0`. -/
theorem modeledCost_zero
    (P : FixedChargeBigM) :
    P.modeledCost 0 = 0 := by
  -- At zero usage the piecewise cost takes its zero branch.
  simp [FixedChargeBigM.modeledCost]

/-- For positive usage, the modeled cost is the fixed charge plus the variable charge. -/
theorem modeledCost_pos
    (P : FixedChargeBigM)
    {y : ℝ}
    (hy : 0 < y) :
    P.modeledCost y = P.fixedCost + P.variableCost * y := by
  -- Positive usage lands on the nonzero branch of the piecewise definition.
  simp [FixedChargeBigM.modeledCost, hy.ne']

/-- A usage level `y` admits some feasible activation variable exactly when `y` is nonnegative and
bounded above by `P.upperBound`. -/
theorem exists_feasible_iff
    (P : FixedChargeBigM)
    {y : ℝ} :
    (∃ x, P.feasible x y) ↔ 0 ≤ y ∧ y ≤ P.upperBound := by
  constructor
  · intro h
    rcases h with ⟨x, hx⟩
    rcases P.feasible_iff.mp hx with ⟨hy_nonneg, hy_bigM, hx_binary⟩
    constructor
    · exact hy_nonneg
    · -- Split on the binary activation to reduce the big-`M` bound.
      rcases hx_binary with rfl | rfl
      · have hy_eq_zero : y = 0 := by
          have hy_le_zero : y ≤ 0 := by simpa using hy_bigM
          exact le_antisymm hy_le_zero hy_nonneg
        rw [hy_eq_zero]
        exact le_of_lt P.upperBound_pos
      · simpa using hy_bigM
  · rintro ⟨hy_nonneg, hy_le⟩
    -- The admissible interval is realized by activating the binary variable.
    refine ⟨1, ?_⟩
    rw [P.feasible_iff]
    constructor
    · exact hy_nonneg
    constructor
    · simpa using hy_le
    · exact Or.inr rfl

/-- Positive usage forces the binary activation variable of a feasible pair to equal `1`. -/
theorem positive_usage_forces_activation
    (P : FixedChargeBigM)
    {x y : ℝ}
    (hxy : P.feasible x y)
    (hy : 0 < y) :
    x = 1 := by
  rcases P.feasible_iff.mp hxy with ⟨_, hy_bigM, hx_binary⟩
  -- Positive usage rules out the inactive branch `x = 0`.
  rcases hx_binary with rfl | rfl
  · have hy_le_zero : y ≤ 0 := by simpa using hy_bigM
    exact False.elim ((not_lt_of_ge hy_le_zero) hy)
  · rfl

/-- On the positive-usage branch, the linear objective of a feasible pair coincides with the
source-facing modeled cost. -/
theorem objectiveValue_eq_modeledCost_of_pos
    (P : FixedChargeBigM)
    {x y : ℝ}
    (hxy : P.feasible x y)
    (hy : 0 < y) :
    P.objectiveValue x y = P.modeledCost y := by
  -- Positive feasible usage forces `x = 1`, so both models have the same cost.
  calc
    P.objectiveValue x y = P.fixedCost * x + P.variableCost * y := P.objectiveValue_def x y
    _ = P.fixedCost * 1 + P.variableCost * y := by
      rw [P.positive_usage_forces_activation hxy hy]
    _ = P.fixedCost + P.variableCost * y := by simp
    _ = P.modeledCost y := by rw [P.modeledCost_pos hy]

/-- Every feasible pair has objective value at least the source-facing modeled cost. -/
theorem modeledCost_le_objectiveValue_of_feasible
    (P : FixedChargeBigM)
    {x y : ℝ}
    (hxy : P.feasible x y) :
    P.modeledCost y ≤ P.objectiveValue x y := by
  by_cases hy_zero : y = 0
  · -- At zero usage the modeled cost vanishes, so only objective nonnegativity remains.
    rw [hy_zero, P.modeledCost_zero]
    rcases P.feasible_iff.mp hxy with ⟨_, _, hx_binary⟩
    rcases hx_binary with rfl | rfl
    · rw [P.objectiveValue_def]
      simp
    · rw [P.objectiveValue_def]
      simpa using P.fixedCost_nonneg
  · have hy_nonneg : 0 ≤ y := (P.feasible_iff.mp hxy).1
    have hy_pos : 0 < y := by
      have hy_ne : 0 ≠ y := by
        intro h0
        exact hy_zero h0.symm
      exact lt_of_le_of_ne hy_nonneg hy_ne
    -- The nonzero branch is exactly the positive-usage equality theorem.
    rw [P.objectiveValue_eq_modeledCost_of_pos hxy hy_pos]

/-- For every admissible usage level `y`, some activation choice attains the modeled cost while
remaining feasible. -/
theorem exists_activation_eq_modeledCost
    (P : FixedChargeBigM)
    {y : ℝ}
    (hy_nonneg : 0 ≤ y)
    (hy_le : y ≤ P.upperBound) :
    ∃ x, P.feasible x y ∧ P.objectiveValue x y = P.modeledCost y := by
  by_cases hy_zero : y = 0
  · -- When usage is zero, choosing `x = 0` is feasible and incurs zero cost.
    refine ⟨0, ?_⟩
    refine And.intro ?_ ?_
    · rw [P.feasible_iff]
      constructor
      · simpa [hy_zero]
      constructor
      · simpa [hy_zero]
      · exact Or.inl rfl
    · rw [hy_zero, P.objectiveValue_def, P.modeledCost_zero]
      simp
  · have hy_pos : 0 < y := by
      have hy_ne : 0 ≠ y := by
        intro h0
        exact hy_zero h0.symm
      exact lt_of_le_of_ne hy_nonneg hy_ne
    have hfeasible : P.feasible 1 y := by
      -- Positive admissible usage is feasible with the active binary choice.
      rw [P.feasible_iff]
      constructor
      · exact hy_nonneg
      constructor
      · simpa using hy_le
      · exact Or.inr rfl
    -- The active choice `x = 1` realizes the positive-usage modeled cost.
    refine ⟨1, ?_⟩
    refine And.intro ?_ ?_
    · exact hfeasible
    · exact P.objectiveValue_eq_modeledCost_of_pos hfeasible hy_pos

end FixedChargeBigM
