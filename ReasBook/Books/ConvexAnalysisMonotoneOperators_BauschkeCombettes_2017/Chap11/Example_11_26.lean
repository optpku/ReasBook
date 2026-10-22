/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Set
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u}

section

variable [AddCommGroup H] [Module ℝ H]
variable (x : H)

local notation "xₙ" => fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x

-- Proof sketch: each term of `n ↦ ((-1 : ℝ) ^ n) • x` is one of the endpoints `x` or `-x`,
-- hence lies in `segment ℝ (-x) x`; therefore the indicator of that segment vanishes along the
-- whole sequence, so the function values converge to the infimum `0`.
/-- Example 11.26 (1): the alternating sequence `xₙ = (-1)^n x` is a minimizing sequence for the
indicator of the symmetric segment `[-x,x]`. -/
theorem alternatingSequence_isMinimizing_symmetricSegmentIndicator (x : H) :
    IsMinimizingSequence (ι[segment ℝ (-x) x]).asEReal xₙ := sorry

end

section

variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (x : H)

local notation "xₙ" => fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x

-- Proof sketch: the range of `n ↦ ((-1 : ℝ) ^ n) • x` is contained in the two-point set
-- `{x, -x}`, and every finite set is bounded in a normed additive group.
/-- Example 11.26 (2): the alternating sequence `xₙ = (-1)^n x` has bounded range. -/
theorem alternatingSequence_isBounded (x : H) :
    Bornology.IsBounded (range xₙ) := sorry

end

section

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (x : H)

local notation "xₙ" => fun n : ℕ ↦ ((-1 : ℝ) ^ n) • x

-- Proof sketch: if the alternating sequence converged weakly to some `y`, then its even
-- subsequence, which is constantly `x`, and its odd subsequence, which is constantly `-x`, would
-- both converge weakly to `y`; uniqueness of weak limits would force `x = -x`, hence `x = 0`,
-- contradicting the hypothesis.
/-- Example 11.26 (3): for `x ≠ 0`, the alternating sequence `xₙ = (-1)^n x` is not weakly
convergent. -/
theorem alternatingSequence_not_tendsto_weakly (x : H) (hx : x ≠ 0) :
    ¬ ∃ y : H,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H y)) := sorry

end

end ERealFunction
