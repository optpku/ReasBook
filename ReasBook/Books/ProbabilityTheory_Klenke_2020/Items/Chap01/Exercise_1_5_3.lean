/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: combine the canonical scaling law `gaussianReal_const_mul` with the translation
-- law `gaussianReal_add_const`; the hypothesis `a ≠ 0` matches the textbook formulation coming
-- from the transformation formula.
/-- Scaling and translating a Gaussian random variable preserves Gaussianity, with the expected
transformed mean and variance. -/
theorem hasLaw_gaussian_affine
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := by
  -- First transport the law through the scaling map and then through the translation map.
  have hAffine :=
    ProbabilityTheory.gaussianReal_add_const
      (ProbabilityTheory.gaussianReal_const_mul hX a) b
  -- The only remaining step is to normalize the variance parameter.
  have hVariance :
      gaussianReal (a * μ + b) (⟨a ^ 2, sq_nonneg a⟩ * ⟨σ ^ 2, sq_nonneg σ⟩) =
        gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩ := by
    apply ProbabilityTheory.gaussianReal_ext_iff.2
    constructor
    · rfl
    · ext
      change a ^ 2 * σ ^ 2 = (a * σ) ^ 2
      ring
  exact hVariance ▸ hAffine

/-- Exercise 1.5.3 (1): Item (i). If a real random variable `X` has Gaussian law `N(μ, σ^2)`,
then the affine transform `aX + b` has Gaussian law `N(aμ + b, a^2σ^2)` for `a ≠ 0`. -/
theorem gaussian_affine_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P)
    (_ha : a ≠ 0) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := by
  simpa using hasLaw_gaussian_affine hX

-- Proof sketch: apply the one-dimensional transformation formula to the density defining
-- `expMeasure θ` under the measurable equivalence `x ↦ a * x`, using `a > 0` to preserve the
-- support on `[0, ∞)` and to rewrite the transformed density as the exponential density with rate
-- `θ / a`.
/-- Helper for Exercise 1.5.3: pushing `expMeasure θ` forward along `x ↦ a * x` with `a > 0`
produces the exponential law of rate `θ / a`. -/
lemma expMeasure_map_const_mul
    {θ a : ℝ} (hθ : 0 < θ) (ha : 0 < a) :
    (expMeasure θ).map (fun x : ℝ ↦ a * x) = expMeasure (θ / a) := by
  have hθ_div_a : 0 < θ / a := by
    positivity
  letI : IsProbabilityMeasure (expMeasure θ) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hθ
  letI : IsProbabilityMeasure ((expMeasure θ).map (fun x : ℝ ↦ a * x)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (expMeasure (θ / a)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hθ_div_a
  apply MeasureTheory.Measure.eq_of_cdf
  ext x
  -- Rewrite the pushed-forward cdf through the preimage of the interval `Iic x`.
  have hMapCdf :
      cdf ((expMeasure θ).map (fun x : ℝ ↦ a * x)) x =
        cdf (expMeasure θ) (x / a) := by
    rw [ProbabilityTheory.cdf_eq_real]
    rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Iic]
    rw [Set.preimage_const_mul_Iic₀ x ha]
    rw [← ProbabilityTheory.cdf_eq_real (μ := expMeasure θ) (x / a)]
  rw [hMapCdf]
  rw [ProbabilityTheory.cdf_expMeasure_eq hθ, ProbabilityTheory.cdf_expMeasure_eq hθ_div_a]
  by_cases hx : 0 ≤ x
  · have hxa : 0 ≤ x / a := by
      positivity
    -- On the positive branch the exponents agree after a single field normalization.
    have hRate :
        -((θ / a) * x) = -(θ * (x / a)) := by
      field_simp [ha.ne']
    simp [hx, hxa, hRate]
  · have hxa : ¬ 0 ≤ x / a := by
      rw [not_le]
      exact div_neg_iff.mpr (Or.inr ⟨lt_of_not_ge hx, ha⟩)
    -- On the negative branch both cdfs vanish.
    simp [hx, hxa]

/-- Multiplying an exponentially distributed random variable by a positive scalar divides its rate
by that scalar. -/
theorem hasLaw_exponential_pos_mul
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ) (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := by
  -- Compose the original law with the positive scaling map and identify the pushforward measure.
  exact HasLaw.comp ⟨by fun_prop, expMeasure_map_const_mul hθ ha⟩ hX

/-- Exercise 1.5.3 (2): Item (ii). If a real random variable `X` has exponential law with rate
`θ` and `a > 0`, then the scaled variable `aX` has exponential law with rate `θ / a`. -/
theorem exponential_pos_mul_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ)
    (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := by
  exact hasLaw_exponential_pos_mul hX hθ ha
