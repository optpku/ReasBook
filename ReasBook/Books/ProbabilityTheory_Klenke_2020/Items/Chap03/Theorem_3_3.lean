/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: the pushforward of a probability measure along a measurable map is again a
-- probability measure, by `Measure.isProbabilityMeasure_map`.
/-- The law of a measurable `ℕ`-valued random variable is again a probability measure after
pushing forward the ambient probability measure. -/
theorem isProbabilityMeasure_map_of_measurable (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) :
    IsProbabilityMeasure (P.map X) := by
  -- The pushforward of a probability measure along an a.e.-measurable map is again a probability
  -- measure, so the measurable random variable `X` has a probability law.
  simpa using Measure.isProbabilityMeasure_map hX.aemeasurable

/-- The `PMF` associated to an `ℕ`-valued measurable random variable under a probability measure. -/
noncomputable def natRandomVariableLaw (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) : PMF ℕ :=
  let _ : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map_of_measurable P X hX
  (P.map X).toPMF

-- Proof sketch: unfold `natRandomVariableLaw` and use `Measure.toPMF_toMeasure` for the
-- pushforward measure `P.map X`.
/-- The measure associated to `natRandomVariableLaw` is the pushforward law of the random
variable. -/
theorem natRandomVariableLaw_toMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℕ) (hX : Measurable X) :
    (natRandomVariableLaw P X hX).toMeasure = P.map X := by
  -- Unfold the `PMF` built from the pushforward law and then collapse `toPMF.toMeasure`.
  unfold natRandomVariableLaw
  simp [Measure.toPMF_toMeasure]

-- Proof sketch: finite sums of measurable `ℕ`-valued functions are measurable; apply the
-- standard measurability theorem for finite sums over `Fin n`.
/-- A finite sum of measurable `ℕ`-valued random variables is measurable. -/
theorem measurable_sum_natFamily {n : ℕ} (X : Fin n → Ω → ℕ)
    (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω ↦ ∑ i : Fin n, X i ω) := by
  -- Finite sums preserve measurability, so the summed random variable has a well-defined law.
  fun_prop

/-- Helper for Theorem 3.3: the probability generating function of the law of a measurable
`ℕ`-valued random variable is the expectation of the power map `ω ↦ z ^ X ω`. -/
theorem probabilityGeneratingFunction_natRandomVariableLaw_eq_integral (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℕ) (hX : Measurable X) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction (natRandomVariableLaw P X hX) z : ℝ) =
      ∫ ω, (z : ℝ) ^ X ω ∂P := by
  let _ : IsProbabilityMeasure (P.map X) := isProbabilityMeasure_map_of_measurable P X hX
  have h_pow_meas : Measurable (fun n : ℕ ↦ (z : ℝ) ^ n) := by
    fun_prop
  have h_pow_integrable_map : Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) (P.map X) := by
    -- On `[0, 1]`, every power of `z` has norm at most `1`, so the integrand is bounded.
    refine Integrable.of_bound h_pow_meas.aestronglyMeasurable 1 ?_
    filter_upwards with n
    rw [Real.norm_of_nonneg (pow_nonneg z.2.1 n)]
    simpa using (pow_le_one₀ (n := n) z.2.1 z.2.2)
  have h_pow_integrable_law :
      Integrable (fun n : ℕ ↦ (z : ℝ) ^ n) (natRandomVariableLaw P X hX).toMeasure := by
    simpa [natRandomVariableLaw_toMeasure P X hX] using h_pow_integrable_map
  calc
    (probabilityGeneratingFunction (natRandomVariableLaw P X hX) z : ℝ)
        = ∑' n : ℕ, ((natRandomVariableLaw P X hX) n).toReal * (z : ℝ) ^ n := by
            rw [probabilityGeneratingFunction_apply]
    _ = ∫ n, (z : ℝ) ^ n ∂(natRandomVariableLaw P X hX).toMeasure := by
          -- The pmf-series defining the pgf is exactly the Bochner integral against the law.
          symm
          rw [PMF.integral_eq_tsum _ _ h_pow_integrable_law]
          simp [smul_eq_mul]
    _ = ∫ n, (z : ℝ) ^ n ∂(P.map X) := by
          rw [natRandomVariableLaw_toMeasure P X hX]
    _ = ∫ ω, (z : ℝ) ^ X ω ∂P := by
          -- Push the integral back from the law of `X` to the original probability space.
          rw [integral_map hX.aemeasurable h_pow_meas.aestronglyMeasurable]

-- Proof sketch: proceed by induction on `n`. For the step from `n` to `n + 1`, combine the
-- two-variable multiplicativity coming from the convolution law of sums of independent random
-- variables with the power-series identity `ψ_{μ ∗ ν} = ψ_μ ψ_ν`.
/-- Theorem 3.3: For a finite independent family of `ℕ`-valued random variables, the probability
generating function of the sum is the product of the individual probability generating
functions. -/
theorem probabilityGeneratingFunction_sum_eq_prod_of_iIndepFun {n : ℕ} (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Fin n → Ω → ℕ) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P) (z : Set.Icc (0 : ℝ) 1) :
    (probabilityGeneratingFunction
        (natRandomVariableLaw P (fun ω ↦ ∑ i : Fin n, X i ω)
          (measurable_sum_natFamily X hX_meas)) z : ℝ) =
      ∏ i : Fin n, (probabilityGeneratingFunction (natRandomVariableLaw P (X i) (hX_meas i)) z : ℝ) :=
  by
  let sumX : Ω → ℕ := fun ω ↦ ∑ i : Fin n, X i ω
  have hsumX_meas : Measurable sumX := measurable_sum_natFamily X hX_meas
  have h_pow_indep : iIndepFun (fun i ↦ fun ω ↦ (z : ℝ) ^ X i ω) P := by
    -- Independence is preserved under measurable coordinatewise transforms.
    simpa [Function.comp] using
      hX_indep.comp (fun _ : Fin n ↦ fun m : ℕ ↦ (z : ℝ) ^ m) (fun _ ↦ by fun_prop)
  have h_pow_aestrong : ∀ i : Fin n, AEStronglyMeasurable (fun ω ↦ (z : ℝ) ^ X i ω) P := by
    intro i
    exact ((hX_meas i).const_pow (z : ℝ)).aestronglyMeasurable
  have h_pow_sum_eq_prod :
      (fun ω ↦ (z : ℝ) ^ sumX ω) = fun ω ↦ ∏ i : Fin n, (z : ℝ) ^ X i ω := by
    -- The exponent of a finite sum splits into the product of the coordinatewise powers.
    funext ω
    simpa [sumX] using
      (Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin n ↦ X i ω) (z : ℝ)).symm
  -- Rewrite the pgf of the total sum as an expectation, then factor the expectation using
  -- independence of the transformed family `ω ↦ z ^ X i ω`.
  rw [probabilityGeneratingFunction_natRandomVariableLaw_eq_integral P sumX hsumX_meas z]
  rw [h_pow_sum_eq_prod]
  calc
    ∫ ω, ∏ i : Fin n, (z : ℝ) ^ X i ω ∂P = ∏ i : Fin n, ∫ ω, (z : ℝ) ^ X i ω ∂P := by
      simpa using h_pow_indep.integral_prod_eq_prod_integral h_pow_aestrong
    _ = ∏ i : Fin n,
          (probabilityGeneratingFunction (natRandomVariableLaw P (X i) (hX_meas i)) z : ℝ) := by
            -- Each factor is the pgf of the corresponding marginal law.
            refine Finset.prod_congr rfl ?_
            intro i hi
            symm
            exact probabilityGeneratingFunction_natRandomVariableLaw_eq_integral P (X i)
              (hX_meas i) z
