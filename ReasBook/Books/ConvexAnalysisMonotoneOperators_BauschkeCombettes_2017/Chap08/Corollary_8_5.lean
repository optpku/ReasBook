/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

omit [AddCommMonoid H] [Module ℝ H] in
/-- Helper for Corollary 8.5: membership in a real lower level set forces membership in the
effective domain. -/
private lemma mem_dom_of_mem_lowerLevelSet (f : H → EReal) {ξ : ℝ} {x : H}
    (hx : x ∈ lowerLevelSet f ξ) : x ∈ dom f := by
  -- A real upper bound from the lower level set shows that the value is strictly below `+∞`.
  rw [mem_dom_iff]
  exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ x).mp hx) (EReal.coe_lt_top ξ)

omit [AddCommMonoid H] [Module ℝ H] in
/-- Helper for Corollary 8.5: if two extended-real values both lie below the same real level `ξ`,
then every convex combination of them with nonnegative coefficients summing to `1` also lies below
`ξ`. -/
private lemma weighted_sum_le_level_of_le_level (ξ : ℝ) {u v : EReal} {a b : ℝ}
    (hu : u ≤ (ξ : EReal)) (hv : v ≤ (ξ : EReal)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : (a : EReal) * u + (b : EReal) * v ≤ (ξ : EReal) := by
  -- First compare each weighted term with the corresponding weight times the common level `ξ`.
  have haE : 0 ≤ (a : EReal) := by
    rw [EReal.coe_nonneg]
    exact ha
  have hbE : 0 ≤ (b : EReal) := by
    rw [EReal.coe_nonneg]
    exact hb
  have hu_weighted :
      (a : EReal) * u ≤ (a : EReal) * (ξ : EReal) :=
    mul_le_mul_of_nonneg_left hu haE
  have hv_weighted :
      (b : EReal) * v ≤ (b : EReal) * (ξ : EReal) :=
    mul_le_mul_of_nonneg_left hv hbE
  -- Then collapse the weighted sum of `ξ` back to `ξ` using `a + b = 1`.
  calc
    (a : EReal) * u + (b : EReal) * v
        ≤ (a : EReal) * (ξ : EReal) + (b : EReal) * (ξ : EReal) :=
      add_le_add hu_weighted hv_weighted
    _ = ((a * ξ + b * ξ : ℝ) : EReal) := by
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    _ = (ξ : EReal) := by
      have hsum : a * ξ + b * ξ = ξ := by
        -- Rewrite `(a + b) * ξ = ξ` using the coefficient identity `a + b = 1`.
        simpa [add_mul] using congrArg (fun t : ℝ => t * ξ) hab
      simpa using congrArg (fun t : ℝ => (t : EReal)) hsum

-- Proof sketch: convert the convex-epigraph hypothesis into the canonical convexity statement for
-- `f`, then apply the standard fact that a sublevel set of a convex function is convex.
/-- Corollary 8.5: for an extended-real-valued convex function on a real vector space, every lower
level set `lev_{≤ ξ} f = {x | f x ≤ ξ}` is convex. -/
theorem convex_lowerLevelSet_of_convex_epigraph (f : H → EReal)
    (hconv : Convex ℝ (epigraph f)) (ξ : ℝ) :
    Convex ℝ (lowerLevelSet f ξ) := by
  refine (convex_iff_forall_pos).2 ?_
  intro x hx y hy a b ha hb hab
  -- Proposition 8.4 works on `dom f`, so first upgrade lower-level membership to domain
  -- membership at both endpoints.
  have hx_dom : x ∈ dom f := mem_dom_of_mem_lowerLevelSet f hx
  have hy_dom : y ∈ dom f := mem_dom_of_mem_lowerLevelSet f hy
  have ha_lt_one : a < 1 := by
    nlinarith
  have hb_eq : b = 1 - a := by
    nlinarith
  have hJensen :
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y := by
    -- Rewrite the second coefficient into Proposition 8.4's `1 - a` form.
    simpa [hb_eq] using
      ((convex_epigraph_iff_jensen_on_dom f).1 hconv hx_dom hy_dom ha ha_lt_one)
  -- Lower-level membership is exactly the statement that the convex combination stays below `ξ`.
  rw [mem_lowerLevelSet_iff]
  -- The Jensen upper bound is controlled by the common level bound on `x` and `y`.
  exact hJensen.trans <|
    weighted_sum_le_level_of_le_level ξ
      ((mem_lowerLevelSet_iff f ξ x).mp hx)
      ((mem_lowerLevelSet_iff f ξ y).mp hy)
      (le_of_lt ha) (le_of_lt hb) hab

end ERealFunction
