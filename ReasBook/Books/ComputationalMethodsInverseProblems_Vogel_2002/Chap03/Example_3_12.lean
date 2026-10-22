/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_1_1.Iterates
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_2.DescentDirection
public import Mathlib.Analysis.SpecificLimits.Normed

public section

/-!
Example 3.12. Statement-stage blocker with an explicit inconsistency witness.

The source tuple `x₀ = 2`, `p_v = -1`, `τ_v = 2 ^ (-v + 1)`, and
`x_v = 1 + 2 ^ (-v)` is internally inconsistent with the Chapter 3 update rule
`x_(v + 1) = x_v + τ_v • p_v`. In Lean-compatible notation, the displayed
step lengths are `τ v = 2 * ((1 / 2 : ℝ) ^ v)`, while the displayed closed form
together with `p_v = -1` forces a different recurrence.

Until the step-length formula, indexing convention, or recurrence is clarified
upstream, this file keeps the displayed tuple itself together with a theorem
showing that it already contradicts the update rule at `v = 0`. The canonical
backend owners checked below remain the intended reuse points for a later
source-faithful repair.
-/

noncomputable section

namespace LineSearch
namespace Example312

/-- The printed initial point in Example 3.12 is `x₀ = 2`. -/
def initialPoint : ℝ := 2

/-- The printed search directions in Example 3.12 are constantly `p_v = -1`. -/
def direction : ℕ → ℝ := fun _ ↦ -1

/-- The printed step-length sequence in Example 3.12 is
`τ_v = 2 ^ (-v + 1) = 2 * (1 / 2 : ℝ) ^ v`. -/
def stepSize (v : ℕ) : ℝ := 2 * ((1 / 2 : ℝ) ^ v)

/-- The printed closed form in Example 3.12 is `x_v = 1 + 2 ^ (-v)`. -/
def iterate (v : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ v

/-- The printed closed form does recover the printed initial point `x₀ = 2`. -/
@[simp] theorem iterate_zero :
    iterate 0 = initialPoint := by
  norm_num [iterate, initialPoint]

/-- Example 3.12. Main labeled source-facing blocker theorem: the printed tuple
already fails the Chapter 3 update rule at the first step, so it cannot be the
iterate sequence of that recurrence without an upstream source correction. -/
theorem iterate_one_ne_update_zero :
    iterate 1 ≠ iterate 0 + stepSize 0 • direction 0 := by
  norm_num [iterate, stepSize, direction]

/-- The printed tuple from Example 3.12 does not satisfy the Chapter 3 update
rule `x_(v + 1) = x_v + τ_v • p_v`. -/
theorem not_followsUpdateRule :
    ¬ ∀ v : ℕ, iterate (v + 1) = iterate v + stepSize v • direction v := by
  intro hUpdate
  exact iterate_one_ne_update_zero (hUpdate 0)

end Example312
end LineSearch

/- Verified backend anchors for a later source-faithful repair once the
step-size formula, indexing convention, or recurrence is clarified upstream. -/

#check LineSearch.IsDescentDirection
#check SteepestDescent.update
#check SteepestDescent.iterates
#check IsMinOn
#check Filter.Tendsto
#check tendsto_pow_atTop_nhds_zero_of_abs_lt_one
#check sq_nonneg
