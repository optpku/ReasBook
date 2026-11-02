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
