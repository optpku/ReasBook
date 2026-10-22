/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u}

section StrictQuasiconvex

variable [AddCommMonoid H] [Module ℝ H]

/-- A strictly quasiconvex objective has at most one global minimizer. -/
theorem argmin_subsingleton_of_strictlyQuasiconvex
    {f : H → EReal} (hstrict : StrictlyQuasiconvex f) :
    (Argmin f).Subsingleton := by
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxmin : ∀ z, f x ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hx)
  have hymin : ∀ z, f y ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hy)
  rcases hstrict.isProper.2 with ⟨z, hz_dom⟩
  have hx_dom : x ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hxtop
    have : (⊤ : EReal) ≤ f z := by simpa [hxtop] using hxmin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  have hy_dom : y ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hytop
    have : (⊤ : EReal) ≤ f z := by simpa [hytop] using hymin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  let z : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hstrict_z : f z < max (f x) (f y) :=
    hstrict.ineq hx_dom hy_dom hxy (by norm_num) (by norm_num)
  have hx_z : f x ≤ f z := hxmin z
  have hy_z : f y ≤ f z := hymin z
  have hmax_z : max (f x) (f y) ≤ f z := max_le hx_z hy_z
  exact (not_lt_of_ge hmax_z hstrict_z).elim

/-- Proposition 11.8 (1): if the indicator-augmented function `f + ι_C` is strictly
quasiconvex, then `f` has at most one minimizer on `C`. -/
-- Proof sketch: strict quasiconvexity of `f + ι[C]` already makes
-- `f + ι_C` proper, so any two constrained
-- minimizers lie in its domain. Applying the strict midpoint inequality to two distinct
-- minimizers contradicts minimality.
theorem argminOn_subsingleton_of_indicator_strictlyQuasiconvex
    {f : H → EReal} {C : Set H}
    (hstrict : StrictlyQuasiconvex (f + (ι[C]).asEReal)) :
    (Argmin[C] f).Subsingleton := by
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    have hg : (f + (ι[C]).asEReal) x ≠ ⊥ := hstrict.isProper.1 x
    exact hg <| by simp [hxC, hfx]
  rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
  exact (argmin_subsingleton_of_strictlyQuasiconvex hstrict).anti Set.inter_subset_right

end StrictQuasiconvex

section ConvexMinimizer

variable [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]
variable [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Proposition 11.8 (2): if `f` is convex on its effective domain, `C` is disjoint from
`Argmin f`, `C ∩ effectiveDomain f` is nonempty, and `C` is strictly convex, then `f` has at
most one minimizer on `C`. -/
-- Proof sketch: if two distinct points of `C` both minimize `f`, strict convexity of `C` places
-- the open segment between them in `interior C`, so in particular their midpoint lies in
-- `interior C`. The feasibility hypothesis provides one point of `C ∩ effectiveDomain f`, and
-- comparing against that feasible point shows any constrained minimizer of `f` on `C` already
-- lies in `effectiveDomain f`. Convexity on `effectiveDomain f` then shows that this midpoint is
-- also a constrained minimizer, and Proposition 11.5 upgrades it to a global minimizer,
-- contradicting the disjointness from `Argmin f`.
theorem argminOn_subsingleton_of_strictConvex
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hconv : ConvexOn f (effectiveDomain f))
    (hdisjoint : Disjoint C (Argmin f.asEReal))
    (hC_dom : (C ∩ effectiveDomain f).Nonempty)
    (hstrictC : StrictConvex ℝ C) :
    (Argmin[C] f.asEReal).Subsingleton := sorry

end ConvexMinimizer

end ERealFunction
