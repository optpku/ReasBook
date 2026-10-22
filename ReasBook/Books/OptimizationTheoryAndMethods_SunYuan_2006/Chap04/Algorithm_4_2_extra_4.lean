/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Algorithm_4_2_extra_1

-- Domain sampling:
-- * `ConjugateGradientRun`
-- * `ConjugateGradientIterativeScheme`
-- * `BealeThreeTermConjugateGradientMethod`
-- * `CrowderWolfeConjugateGradientMethod`
--
-- Owner choice:
-- * `ConjugateGradientRun` already owns the common iterate/gradient/direction/step-size data.
-- * The PRP method is the `source-facing` owner here: its additional mathematical content is the
--   PRP coefficient and recurrence, not a second copy of the shared run data.

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Polak-Ribiere-Polyak coefficient
`β_k = ⟪g_(k + 1), g_(k + 1) - g_k⟫ / ⟪g_k, g_k⟫`. -/
def polakRibierePolyakBeta (gPrev gNext : E) : ℝ :=
  inner ℝ gNext (gNext - gPrev) / inner ℝ gPrev gPrev

end

/-- A Polak-Ribiere-Polyak conjugate-gradient method on `ℝ^n` keeps only the PRP-specific data
on top of the chapter owner `ConjugateGradientRun`: the coefficient sequence, the initial
steepest-descent direction, exact line search on each nonstationary step, the iterate update,
and the PRP coefficient and direction recurrences whenever two consecutive stages are
nonstationary. -/
structure PolakRibierePolyakConjugateGradientMethod (n : ℕ)
    (f : ConjugateGradientPoint n → ℝ)
    extends ConjugateGradientRun (ConjugateGradientPoint n) f where
  β : ℕ → ℝ
  direction_zero : d 0 = -g 0
  exactLineSearch :
    ∀ k : ℕ, g k ≠ 0 →
      IsExactLineSearchStepOnNonnegativeRay f (x k) (d k) (α k)
  iterate_eq :
    ∀ k : ℕ, g k ≠ 0 →
      x (k + 1) = x k + α k • d k
  beta_eq :
    ∀ k : ℕ, g k ≠ 0 → g (k + 1) ≠ 0 →
      β k = polakRibierePolyakBeta (g k) (g (k + 1))
  direction_eq :
    ∀ k : ℕ, g k ≠ 0 → g (k + 1) ≠ 0 →
      d (k + 1) = -g (k + 1) + β k • d k
