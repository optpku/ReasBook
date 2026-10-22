/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace ERealFunction

attribute [local instance] Classical.propDecidable

/-- The explicit `EReal`-valued formula from Example 10.19 on `ℝ²`. -/
noncomputable def example10_19FunctionEReal : (ℝ × ℝ) → EReal :=
  fun x ↦
    if x.1 = 0 ∧ x.2 = 0 then
      0
    else if 0 < x.1 ∧ 0 < x.2 then
      (((x.2 ^ (2 : ℕ)) / (2 * x.1) + x.2 ^ (2 : ℕ) : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: split on the three defining branches of `example10_19FunctionEReal`. The origin
-- branch gives `0`, the positive-orthant branch is a real number, and the remaining branch gives
-- `⊤`; all three values lie strictly above `⊥`.
/-- The explicit formula from Example 10.19 never takes the value `-∞`. -/
theorem example10_19FunctionEReal_gt_bot (x : ℝ × ℝ) :
    ⊥ < example10_19FunctionEReal x := sorry

/-- The `]-∞,+∞]`-valued function from Example 10.19. -/
noncomputable def example10_19Function : (ℝ × ℝ) → Set.Ioi (⊥ : EReal) :=
  fun x ↦ ⟨example10_19FunctionEReal x, example10_19FunctionEReal_gt_bot x⟩

/-- Coercing the Example 10.19 function to `EReal` recovers its explicit formula. -/
@[simp] theorem example10_19Function_apply (x : ℝ × ℝ) :
    example10_19Function.asEReal x = example10_19FunctionEReal x :=
  rfl

/-- The set `C = B(0; ρ) ∩ dom f` from Example 10.19. -/
def example10_19Set (ρ : Set.Ioi (0 : ℝ)) : Set (ℝ × ℝ) :=
  Metric.ball (0 : ℝ × ℝ) (ρ : ℝ) ∩ effectiveDomain example10_19Function

section Statements

variable (ρ : Set.Ioi (0 : ℝ))

-- Proof sketch: analyze the explicit formula on the positive orthant, where the Hessian is
-- positive definite, and note that the value `⊤` outside the effective domain forces the strict
-- Jensen inequality whenever one endpoint leaves the domain.
/-- Example 10.19 (1): the explicit function on `ℝ²` is strictly convex. -/
theorem example10_19Function_strictlyConvex :
    StrictlyConvex example10_19Function := sorry

-- Proof sketch: since `ρ > 0`, the origin belongs to the open ball of radius `ρ`; the defining
-- formula gives the finite value `0` at the origin, so `0 ∈ C`.
/-- Example 10.19 (2): for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f` is nonempty. -/
theorem example10_19Set_nonempty :
    (example10_19Set ρ).Nonempty := sorry

-- Proof sketch: `example10_19Set ρ` is contained in the open ball `B(0; ρ)`, and every metric
-- ball in a normed space is bounded.
/-- Example 10.19 (3): for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f` is bounded. -/
theorem example10_19Set_bounded :
    Bornology.IsBounded (example10_19Set ρ) := sorry

-- Proof sketch: identify `dom f` with `{(ξ, η) | ξ = 0 ∧ η = 0} ∪ {(ξ, η) | 0 < ξ ∧ 0 < η}` and
-- verify that this domain is convex; then intersect with the convex ball `B(0; ρ)`.
/-- Example 10.19 (4): for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f` is convex. -/
theorem example10_19Set_convex :
    Convex ℝ (example10_19Set ρ) := sorry

-- Proof sketch: this is immediate from the definition `C = B(0; ρ) ∩ dom f`.
/-- Example 10.19 (5): for every positive radius `ρ`, the set `C = B(0;ρ) ∩ dom f` is contained
in `dom f`. -/
theorem example10_19Set_subset_effectiveDomain :
    example10_19Set ρ ⊆ effectiveDomain example10_19Function := fun _ hx ↦ hx.2

-- Proof sketch: restrict the global strict convexity from clause (1) to the subset `C`.
/-- Example 10.19 (6): for every positive radius `ρ`, the function is strictly convex on
`C = B(0;ρ) ∩ dom f`. -/
theorem example10_19Function_strictlyConvexOn_set :
    StrictlyConvexOn example10_19Function (example10_19Set ρ) :=
  example10_19Function_strictlyConvex.strictlyConvexOn (example10_19Set_nonempty ρ)
    (example10_19Set_subset_effectiveDomain ρ)

-- Proof sketch: on `C` the function is finite and given by a continuous real formula on the
-- positive-orthant branch together with the value `0` at the origin, so the restricted `EReal`
-- function is lower semicontinuous on `C`.
/-- Example 10.19 (7): for every positive radius `ρ`, the restriction of the function to
`C = B(0;ρ) ∩ dom f` is lower semicontinuous. -/
theorem example10_19Function_restriction_lowerSemicontinuous :
    LowerSemicontinuousOn example10_19Function.asEReal (example10_19Set ρ) := sorry

-- Proof sketch: use the explicit boundary points `z_η = (√(ρ² - η²), η)` from the textbook
-- proof to show that the exact Jensen gap along the segment from `0` to `z_η` equals `η²`, which
-- tends to `0`; therefore no modulus positive away from `0` can witness uniform convexity on `C`.
/-- Example 10.19 (8): for every positive radius `ρ`, the function is not uniformly convex on
`C = B(0;ρ) ∩ dom f`. -/
theorem example10_19Function_not_uniformlyConvexOn_set :
    ¬ ∃ φ : NNReal → EReal, UniformlyConvexOn example10_19Function (example10_19Set ρ) φ := sorry

end Statements

end ERealFunction
