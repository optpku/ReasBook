/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Continuous
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2

open Set

namespace Function.Sublinear

section Module

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] {g : E → ℝ}

/-- Lemma 6.15 (1). Every sublinear function on a real vector space is convex. Specializing to
`Fin n → ℝ` recovers the textbook `ℝ^n` formulation. -/
theorem convexOn_univ (hg : g.Sublinear) : ConvexOn ℝ univ g := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  calc
    g (a • x + b • y) ≤ g (a • x) + g (b • y) := hg.subadditive _ _
    _ = a • g x + b • g y := by
      simp only [smul_eq_mul]
      rw [hg.positivelyHomogeneous.smul_nonneg x a ha, hg.positivelyHomogeneous.smul_nonneg y b hb]

end Module

section Continuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {g : E → ℝ}

/-- A sublinear function on a finite-dimensional real normed space is locally Lipschitz. -/
theorem locallyLipschitz (hg : g.Sublinear) : LocallyLipschitz g :=
  hg.convexOn_univ.locallyLipschitz

/-- Lemma 6.15 (2). Every sublinear function on a finite-dimensional real normed space is
continuous. Specializing to `Fin n → ℝ` recovers the textbook `ℝ^n` formulation. -/
theorem continuous (hg : g.Sublinear) : Continuous g := by
  exact hg.locallyLipschitz.continuous

end Continuous

end Function.Sublinear
