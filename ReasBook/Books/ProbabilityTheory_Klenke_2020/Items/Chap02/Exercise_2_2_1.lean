/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: identify the event `{ω | X ω < Y ω}` with the region below the diagonal for the
-- joint law of `(X, Y)`, use independence and the two exponential marginals to factor the joint
-- density, integrate over `{(x, y) | 0 ≤ x ∧ x < y}`, and simplify the resulting elementary
-- integral.
/-- Helper for Exercise 2.2.1: rewrite integration against `expMeasure θ` as integration against
its real-valued density. -/
private lemma integralExpMeasure_eq_integral_density {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, exponentialPDFReal θ x * f x := by
  -- Proof comment: unfold `expMeasure` through `withDensity` and simplify the density on `ℝ`.
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x, smul_eq_mul]

/-- Helper for Exercise 2.2.1: independence upgrades the marginal exponential laws of `X` and `Y`
to the product law of the pair `(X, Y)`. -/
private lemma indepExponentialPair_hasLaw_prod
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ} {θ ρ : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hY : HasLaw Y (expMeasure ρ) P)
    (hXY : X ⟂ᵢ[P] Y)
    (hθ : 0 < θ) :
    HasLaw (fun ω ↦ (X ω, Y ω)) ((expMeasure θ).prod (expMeasure ρ)) P := by
  -- Proof comment: use the independence criterion given by the product pushforward of the pair map.
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  letI : IsProbabilityMeasure P := hX.isProbabilityMeasure
  refine ⟨hX.aemeasurable.prodMk hY.aemeasurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hXY,
    hX.map_eq, hY.map_eq]

/-- Helper for Exercise 2.2.1: integrating the indicator of the region `{(x, y) | x < y}` against
the product exponential law reduces to the exponential tail function of the second coordinate. -/
private lemma ltRegionIntegral_eq_tailIntegral {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) :
    ∫ z, Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun _ ↦ (1 : ℝ)) z
        ∂((expMeasure θ).prod (expMeasure ρ)) =
      ∫ x, (expMeasure ρ).real (Set.Ioi x) ∂expMeasure θ := by
  -- Proof comment: apply Fubini and identify each vertical section with the tail set `Ioi x`.
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  letI : IsProbabilityMeasure (expMeasure ρ) := isProbabilityMeasure_expMeasure hρ
  have hIntegrable :
      Integrable (Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun _ ↦ (1 : ℝ)))
        ((expMeasure θ).prod (expMeasure ρ)) := by
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_lt measurable_fst measurable_snd)
  rw [integral_prod _ hIntegrable]
  refine integral_congr_ae ?_
  filter_upwards with x
  have hSection :
      (fun y ↦ Set.indicator {p : ℝ × ℝ | p.1 < p.2} (fun _ ↦ (1 : ℝ)) (x, y)) =
        Set.indicator (Set.Ioi x) (fun _ ↦ (1 : ℝ)) := by
    -- Proof comment: for fixed `x`, the slice of the region `{p | p.1 < p.2}` is exactly `Ioi x`.
    funext y
    simp [Set.indicator]
  rw [hSection]
  simpa using (integral_indicator_one (μ := expMeasure ρ) (s := Set.Ioi x) measurableSet_Ioi)

/-- Helper for Exercise 2.2.1: the exponential tail above `x` is `exp (-(ρ * x))` on the support
and equals `1` below `0`. -/
private lemma expMeasure_real_Ioi {ρ x : ℝ} (hρ : 0 < ρ) :
    (expMeasure ρ).real (Set.Ioi x) = if 0 ≤ x then Real.exp (-(ρ * x)) else 1 := by
  -- Proof comment: compute the tail as the complement of the cdf on `Iic x`.
  letI : IsProbabilityMeasure (expMeasure ρ) := isProbabilityMeasure_expMeasure hρ
  have hIic :
      (expMeasure ρ).real (Set.Iic x) =
        if 0 ≤ x then 1 - Real.exp (-(ρ * x)) else 0 := by
    rw [← cdf_eq_real (μ := expMeasure ρ) x, cdf_expMeasure_eq hρ x]
  calc
    (expMeasure ρ).real (Set.Ioi x)
        = 1 - (expMeasure ρ).real (Set.Iic x) := by
            simpa using
              (probReal_compl_eq_one_sub (μ := expMeasure ρ) (s := Set.Iic x) measurableSet_Iic)
    _ = 1 - (if 0 ≤ x then 1 - Real.exp (-(ρ * x)) else 0) := by rw [hIic]
    _ = if 0 ≤ x then Real.exp (-(ρ * x)) else 1 := by
      by_cases hx : 0 ≤ x
      · simp [hx]
      · simp [hx]

/-- Helper for Exercise 2.2.1: the exponential expectation of the survival function of an
independent `Exp(ρ)` variable is `θ / (θ + ρ)`. -/
private lemma expMeasure_integral_tail_eq_rateRatio {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 < ρ) :
    ∫ x, (if 0 ≤ x then Real.exp (-(ρ * x)) else 1) ∂expMeasure θ = θ / (θ + ρ) := by
  -- Proof comment: rewrite `expMeasure θ` by its density and evaluate the remaining exponential
  -- integral on `(0, ∞)` using the Gamma-function identity at shape parameter `1`.
  rw [integralExpMeasure_eq_integral_density hθ]
  have hIndicator :
      (fun x ↦ exponentialPDFReal θ x * (if 0 ≤ x then Real.exp (-(ρ * x)) else 1)) =
        Set.indicator (Set.Ici 0) (fun x ↦ θ * Real.exp (-((θ + ρ) * x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp [exponentialPDFReal, gammaPDFReal, hx]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    · simp [exponentialPDFReal, gammaPDFReal, hx]
  rw [hIndicator, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hRewrite :
      (fun x ↦ θ * Real.exp (-((θ + ρ) * x))) =
        fun x ↦ θ * (x ^ ((1 : ℝ) - 1) * Real.exp (-((θ + ρ) * x))) := by
    -- Proof comment: cast the integrand into the standard Gamma-integral shape with exponent `1`.
    funext x
    rw [show ((1 : ℝ) - 1) = 0 by norm_num, Real.rpow_zero]
    ring
  rw [hRewrite, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := θ + ρ) (by norm_num) (add_pos hθ hρ)]
  rw [Real.Gamma_one, Real.rpow_one]
  field_simp [hθ.ne', hρ.ne', (add_pos hθ hρ).ne']

/-- Exercise 2.2.1: if `X` and `Y` are independent real random variables with exponential laws of
rates `θ` and `ρ`, then the probability that `X < Y` is `θ / (θ + ρ)`. -/
theorem indep_exponential_lt_probability
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ} {θ ρ : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hY : HasLaw Y (expMeasure ρ) P)
    (hXY : X ⟂ᵢ[P] Y)
    (hθ : 0 < θ) (hρ : 0 < ρ) :
    P.real {ω | X ω < Y ω} = θ / (θ + ρ) := by
  let region : Set (ℝ × ℝ) := {p | p.1 < p.2}
  have hPair :
      HasLaw (fun ω ↦ (X ω, Y ω)) ((expMeasure θ).prod (expMeasure ρ)) P :=
    indepExponentialPair_hasLaw_prod hX hY hXY hθ
  have hEventNull :
      NullMeasurableSet {ω | X ω < Y ω} P := by
    -- Proof comment: the event is the preimage of a measurable region under the a.e.-measurable
    -- pair map.
    simpa [region] using
      (hX.aemeasurable.prodMk hY.aemeasurable).nullMeasurableSet_preimage
        (s := region) (measurableSet_lt measurable_fst measurable_snd)
  have hIndicator :
      Set.indicator {ω | X ω < Y ω} (fun _ ↦ (1 : ℝ)) =
        fun ω ↦ Set.indicator region (fun _ ↦ (1 : ℝ)) (X ω, Y ω) := by
    -- Proof comment: the event indicator is exactly the region indicator evaluated on `(X, Y)`.
    funext ω
    simp [region, Set.indicator]
  have hRegionMeas : Measurable (Set.indicator region (fun _ ↦ (1 : ℝ))) := by
    -- Proof comment: the diagonal region `{p | p.1 < p.2}` is Borel measurable.
    exact measurable_const.indicator (measurableSet_lt measurable_fst measurable_snd)
  calc
    P.real {ω | X ω < Y ω}
        = ∫ ω, Set.indicator {ω | X ω < Y ω} (fun _ ↦ (1 : ℝ)) ω ∂P := by
            -- Proof comment: express the probability of the event as the integral of its indicator.
            symm
            rw [integral_indicator₀ hEventNull]
            exact setIntegral_one_eq_measureReal
    _ = ∫ ω, Set.indicator region (fun _ ↦ (1 : ℝ)) (X ω, Y ω) ∂P := by
      rw [hIndicator]
    _ = ∫ z, Set.indicator region (fun _ ↦ (1 : ℝ)) z ∂((expMeasure θ).prod (expMeasure ρ)) := by
      -- Proof comment: transport the indicator integral along the joint law of `(X, Y)`.
      simpa [Function.comp_def] using
        hPair.integral_comp (f := Set.indicator region (fun _ ↦ (1 : ℝ)))
          hRegionMeas.aestronglyMeasurable
    _ = ∫ x, (expMeasure ρ).real (Set.Ioi x) ∂expMeasure θ := by
      -- Proof comment: Fubini reduces the region integral to the exponential tail of `Y`.
      simpa [region] using ltRegionIntegral_eq_tailIntegral hθ hρ
    _ = ∫ x, (if 0 ≤ x then Real.exp (-(ρ * x)) else 1) ∂expMeasure θ := by
      -- Proof comment: rewrite the exponential tail function by its explicit closed form.
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [expMeasure_real_Ioi hρ]
    _ = θ / (θ + ρ) := expMeasure_integral_tail_eq_rateRatio hθ hρ
