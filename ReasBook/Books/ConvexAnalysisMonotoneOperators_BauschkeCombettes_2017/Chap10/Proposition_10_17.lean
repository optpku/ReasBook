/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Bridge to the source-facing `EReal` notion: a strictly convex real-valued function on a
nonempty set is strictly convex on that set after applying `Function.toEReal`. -/
theorem _root_.StrictConvexOn.toStrictlyConvexOn_toEReal
    {f : H → ℝ} {C : Set H} (hC_nonempty : C.Nonempty) (hstrict : StrictConvexOn ℝ C f) :
    StrictlyConvexOn f.toEReal C := by
  refine ⟨hC_nonempty, by simp [Function.effectiveDomain_toEReal], ?_⟩
  intro x hx y hy hxy α hα0 hα1
  have hβ0 : 0 < 1 - α := sub_pos.mpr hα1
  have hαβ : α + (1 - α) = 1 := by ring
  have hineq :
      f (α • x + (1 - α) • y) < α * f x + (1 - α) * f y :=
    hstrict.2 hx hy hxy hα0 hβ0 hαβ
  have hineqE :
      (((f (α • x + (1 - α) • y) : ℝ) : EReal)) <
        (((α * f x + (1 - α) * f y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  simpa [Function.toEReal_apply, smul_eq_mul, EReal.coe_mul, EReal.coe_add] using hineqE

-- Proof sketch: define the midpoint-gap infimum over pairs of points of `C` at fixed distance.
-- Compactness and continuity on `C` produce minimizing pairs, while strict convexity on `C`
-- forces every nonzero-distance minimizing pair to have strictly positive midpoint gap. Apply the
-- canonical midpoint-modulus criterion on `C` to obtain a real-valued modulus positive away from
-- `0`, hence a canonical `UniformConvexOn` statement there.
/-- Proposition 10.17: if `C` is compact, `f` is strictly convex on `C`, and `f|_C` is
continuous, then `f` admits a modulus positive away from `0` making it uniformly convex on `C`. -/
theorem exists_uniformConvexOn_of_isCompact_of_strictConvexOn_of_continuousOn
    (f : H → ℝ) (C : Set H)
    (hC_compact : IsCompact C)
    (hstrict : StrictConvexOn ℝ C f) (hcont : ContinuousOn f C) :
    ∃ ψ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ f := sorry

/-- Bridge/view form of Proposition 10.17 in the source-facing `EReal` layer, stated with the
owner `StrictlyConvexOn f.toEReal C`. -/
theorem exists_uniformlyConvexOn_toEReal_of_isCompact_of_strictlyConvexOn_of_continuousOn
    (f : H → ℝ) (C : Set H) (hC_compact : IsCompact C)
    (hstrict : StrictlyConvexOn f.toEReal C) (hcont : ContinuousOn f C) :
    ∃ φ : NNReal → EReal, UniformlyConvexOn f.toEReal C φ := by
  sorry

end ERealFunction
