/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- A source-facing strictly convex `]-∞,+∞]`-valued function with nonempty effective domain
yields the Chapter 10 owner `StrictlyQuasiconvex` on its canonical underlying `EReal`-valued
function. -/
theorem StrictlyConvex.toStrictlyQuasiconvex_asEReal
    {f : H → Set.Ioi (⊥ : EReal)} (hstrict : StrictlyConvex f)
    (hdom : (effectiveDomain f).Nonempty) :
    StrictlyQuasiconvex f.asEReal := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  intro x y hx hy hxy α hα0 hα1
  have hx_eff : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy_eff : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hstrict' :
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hstrict.ineq hx_eff hy_eff hxy hα0 hα1
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ (((1 - α : ℝ) : EReal)) := by
    exact_mod_cast sub_nonneg.mpr hα1.le
  have hweight_sum : (α : EReal) + (((1 - α : ℝ) : EReal)) = 1 := by
    exact_mod_cast (show α + (1 - α : ℝ) = 1 by ring)
  calc
    (f (α • x + (1 - α) • y) : EReal)
        < (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := hstrict'
    _ ≤ (α : EReal) * max (f x : EReal) (f y : EReal) +
          (((1 - α : ℝ) : EReal) * max (f x : EReal) (f y : EReal)) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max (f x : EReal) (f y : EReal) := by
      rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg, hweight_sum, one_mul]

/-- Corollary 11.9: a strictly convex `]-∞,+∞]`-valued function with nonempty effective domain has
at most one global minimizer. -/
-- Proof sketch: strict convexity upgrades the canonical underlying function `f.asEReal` to a
-- strictly quasiconvex function, so Proposition 11.8 applies directly to the global owner
-- `Argmin`.
theorem argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty)
    (hstrict : StrictlyConvex f) :
    (Argmin f.asEReal).Subsingleton :=
  argmin_subsingleton_of_strictlyQuasiconvex <|
    hstrict.toStrictlyQuasiconvex_asEReal hdom

end ERealFunction
