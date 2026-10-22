/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Corollary_10_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- The midpoint Jensen-gap modulus takes the infimum of the midpoint Jensen gaps over all
effective-domain pairs at a prescribed distance. -/
noncomputable def midpointModulusOfConvexity
    : NNReal → EReal :=
  fun t ↦ sInf
    {δ : EReal |
      ∃ x ∈ effectiveDomain f, ∃ y ∈ effectiveDomain f,
        ‖x - y‖₊ = t ∧
          δ = jensenGap f (1 / 2 : ℝ) x y}

/-- The midpoint Jensen-gap modulus is bounded above by every midpoint Jensen gap realized at the
given radius. -/
-- Proof sketch: unfold `midpointModulusOfConvexity` and apply `sInf_le` to the witness set element
-- determined by the chosen points `x` and `y`.
theorem midpointModulusOfConvexity_le_gap
    {t : NNReal} {x y : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) (ht : ‖x - y‖₊ = t) :
    midpointModulusOfConvexity f t ≤ jensenGap f (1 / 2 : ℝ) x y := sorry

-- Proof sketch: compare the midpoint Jensen gap with the normalized gaps used in
-- `exactModulusOfConvexity`; convexity at coefficients `α ∈ (0, 1/2]` yields the lower bound
-- `2 ψ ≤ φ`.
/-- Proposition 10.14 (1): twice the midpoint Jensen-gap modulus is bounded above by the exact
modulus of convexity. -/
theorem two_mul_midpointModulusOfConvexity_le_exactModulusOfConvexity
    (hconv : ConvexOn f (effectiveDomain f))
    (t : NNReal) :
    2 * midpointModulusOfConvexity f t ≤ exactModulusOfConvexity f t := sorry

-- Proof sketch: specialize the defining infimum in `exactModulusOfConvexity` to the coefficient
-- `α = 1 / 2`, so the normalization factor becomes `1 / 4` and gives the estimate `φ ≤ 4 ψ`.
/-- Proposition 10.14 (2): the exact modulus of convexity is bounded above by four times the
midpoint Jensen-gap modulus. -/
theorem exactModulusOfConvexity_le_four_mul_midpointModulusOfConvexity
    (t : NNReal) :
    exactModulusOfConvexity f t ≤ 4 * midpointModulusOfConvexity f t := sorry

-- Proof sketch: combine parts `(1)` and `(2)` with the facts that multiplication by the positive
-- scalars `2` and `4` preserves equality to `0` in `EReal`.
/-- The midpoint and exact moduli of convexity vanish at exactly the same radii. -/
theorem midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero
    (hconv : ConvexOn f (effectiveDomain f))
    (t : NNReal) :
    midpointModulusOfConvexity f t = 0 ↔ exactModulusOfConvexity f t = 0 := sorry

-- Proof sketch: combine the midpoint-criterion equivalence above with the canonical owner theorem
-- `exactModulusOfConvexity_uniformlyConvex_iff`.
/-- Proposition 10.14 (3), canonical owner form: the exact modulus of convexity is a modulus of
uniform convexity precisely when the midpoint Jensen-gap modulus vanishes only at `0`. -/
theorem exactModulusOfConvexity_uniformlyConvex_iff_midpointModulusOfConvexity_eq_zero_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    UniformlyConvex f (exactModulusOfConvexity f) ↔
      ∀ t : NNReal, midpointModulusOfConvexity f t = 0 ↔ t = 0 := by
  rw [exactModulusOfConvexity_uniformlyConvex_iff f hconv]
  constructor
  · intro h t
    rw [midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero f hconv t]
    exact h t
  · intro h t
    rw [← midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero f hconv t]
    exact h t

-- Proof sketch: transport the vanishing criterion along
-- `midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero`, then apply the
-- canonical Corollary 10.13 owner theorem for `exactModulusOfConvexity`.
/-- Proposition 10.14 (3): a proper convex function is uniformly convex if and only if its midpoint
Jensen-gap modulus vanishes only at `0`. -/
theorem uniformlyConvex_exists_iff_midpointModulusOfConvexity_eq_zero_iff
    (hconv : ConvexOn f (effectiveDomain f)) :
    (∃ φ : NNReal → EReal, UniformlyConvex f φ) ↔
      ∀ t : NNReal, midpointModulusOfConvexity f t = 0 ↔ t = 0 := by
  rw [uniformlyConvex_exists_iff_exactModulusOfConvexity_eq_zero_iff f hconv]
  constructor
  · intro h t
    rw [midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero f hconv t]
    exact h t
  · intro h t
    rw [← midpointModulusOfConvexity_eq_zero_iff_exactModulusOfConvexity_eq_zero f hconv t]
    exact h t

end ERealFunction
