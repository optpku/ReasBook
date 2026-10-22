/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The scalar branch `ξ ↦ 1 - √ξ` on `ℝ₊`, extended by `+∞` on `(-∞, 0)`. -/
def oneSubSqrtIciExtension (ξ : ℝ) : EReal :=
  if 0 ≤ ξ then ((1 - Real.sqrt ξ : ℝ) : EReal) else ⊤

/-- The extended-real-valued counterexample `(ξ₁, ξ₂) ↦ max {g(ξ₁), |ξ₂|}` from Remark 16.28. -/
def oneSubSqrtAbsMaxValue (x : ℝ²) : EReal :=
  max (oneSubSqrtIciExtension (x 0)) ((|x 1| : ℝ) : EReal)

-- Proof sketch: if `x.1 < 0`, then `oneSubSqrtIciExtension x.1 = ⊤`, so the maximum is `⊤ > ⊥`.
-- If `0 ≤ x.1`, then both entries of the maximum are real casts to `EReal`, hence each lies above
-- `⊥`, and so does their maximum.
/-- The counterexample value never takes the value `-∞`. -/
theorem oneSubSqrtAbsMaxValue_gt_bot (x : ℝ²) :
    (⊥ : EReal) < oneSubSqrtAbsMaxValue x := sorry

-- Proof sketch: `oneSubSqrtAbsMaxValue_gt_bot` rules out the value `-∞`, and the origin lies in
-- the ordinary domain because the explicit maximum there is `1`.
/-- The underlying `EReal`-valued counterexample is proper. -/
theorem oneSubSqrtAbsMaxValue_isProper :
    IsProper oneSubSqrtAbsMaxValue := by
  refine ⟨?_, ⟨0, ?_⟩⟩
  · intro x
    exact ne_of_gt (oneSubSqrtAbsMaxValue_gt_bot x)
  · change oneSubSqrtAbsMaxValue 0 < ⊤
    simpa [oneSubSqrtAbsMaxValue, oneSubSqrtIciExtension] using (EReal.coe_lt_top (1 : ℝ))

/-- The `]-∞,+∞]`-valued counterexample function from Remark 16.28. -/
def oneSubSqrtAbsMaxCounterexample : ℝ² → Set.Ioi (⊥ : EReal) :=
  properIoi oneSubSqrtAbsMaxValue oneSubSqrtAbsMaxValue_isProper

-- Proof sketch: `ξ₁ ↦ oneSubSqrtIciExtension ξ₁` is the lower-semicontinuous convex extension of
-- `1 - √ξ` from `ℝ₊`, and `(ξ₁, ξ₂) ↦ (|ξ₂| : EReal)` is convex and lower semicontinuous on
-- `ℝ²`. The pointwise maximum of these two lower-semicontinuous convex functions is again a member
-- of `Γ₀(ℝ²)`.
/-- The explicit counterexample from Remark 16.28 belongs to `Γ₀(ℝ²)`. -/
theorem oneSubSqrtAbsMaxCounterexample_mem_gammaZero :
    oneSubSqrtAbsMaxCounterexample ∈ Γ₀(ℝ²) := sorry

-- Proof sketch: analyze the subgradient inequality separately on the open half-plane `ξ₁ > 0`,
-- on the boundary line `ξ₁ = 0`, and on the region `ξ₁ < 0` where the function takes value
-- `+∞`. For `ξ₁ > 0` the smooth branch `1 - √ξ₁` gives subgradients, while at `ξ₁ = 0` the
-- vertical strip `|ξ₂| < 1` is excluded because the singular first-coordinate branch destroys
-- subdifferentiability there. This yields exactly the stated set.
/-- Remark 16.28: for the function
`f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` with `g(ξ₁) = 1 - √ξ₁` on `ℝ₊` and `g(ξ₁) = +∞` on
`(-∞, 0)`, the domain of the subdifferential is
`(ℝ₊ × ℝ) \ ({0} × ]-1,1[)`. -/
theorem subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq :
    SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample) =
      {x : ℝ² | 0 ≤ x 0} \
        {x : ℝ² | x 0 = 0 ∧ x 1 ∈ Set.Ioo (-1 : ℝ) 1} := sorry

-- Proof sketch: use the explicit domain formula from
-- `subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_eq`. The points `(0, -1)` and `(0, 1)`
-- belong to the domain, but their midpoint `(0, 0)` lies in the removed strip `{0} × ]-1,1[`.
/-- The subdifferential domain in Remark 16.28 is not convex. -/
theorem subdifferentialDomain_oneSubSqrtAbsMaxCounterexample_not_convex :
    ¬ Convex ℝ
      ((SetValuedOperator.dom (∂ oneSubSqrtAbsMaxCounterexample)) : Set ℝ²) := sorry

end

end ERealFunction
