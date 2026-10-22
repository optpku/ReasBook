/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Example_6_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Lemma_21_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The textbook Laplace transform of the branching diffusion started from `x` and observed at time
`t`. -/
def branchingDiffusionLaplaceTransform (t x : NNReal) : ℝ → ℝ :=
  fun l ↦ Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1)))

/-- Evaluating `branchingDiffusionLaplaceTransform` gives the explicit exponential formula
`exp (-x λ / (1 + t λ))`. -/
theorem branchingDiffusionLaplaceTransform_apply (t x : NNReal) (l : ℝ) :
    branchingDiffusionLaplaceTransform t x l =
      Real.exp (-((x : ℝ) * l / (l * (t : ℝ) + 1))) :=
  rfl

/-- Helper for Lemma 21.47: the explicit branching-diffusion Laplace transform is normalized to
`1` at the origin. -/
lemma branchingDiffusionLaplaceTransform_zero (t x : NNReal) :
    branchingDiffusionLaplaceTransform t x 0 = 1 := by
  -- Proof comment: substituting `λ = 0` kills the rational exponent, so the exponential becomes
  -- `exp 0`.
  simp [branchingDiffusionLaplaceTransform]

section BranchingDiffusion

variable {κ : NNReal → Kernel NNReal NNReal}
variable {P : NNReal → ProbabilityMeasure Ω} {Y : NNReal → Ω → NNReal}
variable (hY : IsMarkovProcessRealization κ P Y)
variable (hκ : HasBranchingDiffusionLaplaceTransform κ)

/-- A realization of a branching-diffusion kernel inherits the textbook one-time Laplace-transform
formula, with the source-faithful Laplace parameter domain `λ ≥ 0`. -/
theorem IsMarkovProcessRealization.branchingDiffusionLaplaceTransform
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t l : NNReal) :
    ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) =
      ProbabilityTheory.branchingDiffusionLaplaceTransform t x l := by
  -- Proof comment: push the observable through the one-time marginal map, replace that map by the
  -- kernel row `κ t x`, and then evaluate the Laplace transform with `hκ`.
  calc
    ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) =
        ∫ y, Real.exp (-((l : ℝ) * (y : ℝ))) ∂((P x : Measure Ω).map (Y t)) := by
          symm
          rw [MeasureTheory.integral_map (hY.measurable_process t).aemeasurable (by fun_prop)]
    _ = ∫ y, Real.exp (-((l : ℝ) * (y : ℝ))) ∂κ t x := by rw [hY.transition_eq x t]
    _ = Real.exp (-((l : ℝ) * (x : ℝ)) / (((l : ℝ) * (t : ℝ)) + 1)) := hκ x t l
    _ = ProbabilityTheory.branchingDiffusionLaplaceTransform t x l := by
          simp [ProbabilityTheory.branchingDiffusionLaplaceTransform, mul_comm, neg_div]

/-- Helper for Lemma 21.47: on the positive half-line, the moment-generating function of `-Y t`
matches the explicit branching-diffusion Laplace transform. -/
lemma branchingDiffusion_mgf_neg_eq_explicit_of_pos
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} {r : ℝ} (hr : 0 < r) :
    mgf (fun ω ↦ -((Y t ω : ℝ))) (P x : Measure Ω) r =
      branchingDiffusionLaplaceTransform t x r := by
  let l : NNReal := ⟨r, hr.le⟩
  -- Proof comment: a positive real Laplace parameter is an `NNReal`, so the mgf of `-Y t`
  -- becomes the already-proved one-time Laplace-transform identity.
  calc
    mgf (fun ω ↦ -((Y t ω : ℝ))) (P x : Measure Ω) r =
        ∫ ω, Real.exp (-((l : ℝ) * (Y t ω : ℝ))) ∂(P x : Measure Ω) := by
          simp [ProbabilityTheory.mgf, l]
    _ = branchingDiffusionLaplaceTransform t x l :=
      hY.branchingDiffusionLaplaceTransform hκ x t l
    _ = branchingDiffusionLaplaceTransform t x r := rfl

/-- Helper for Lemma 21.47: the explicit branching-diffusion Laplace transform is analytic at the
origin. -/
lemma branchingDiffusionLaplaceTransform_analyticAt_zero (t x : NNReal) :
    AnalyticAt ℝ (branchingDiffusionLaplaceTransform t x) 0 := by
  -- Proof comment: the exponent is a quotient of affine maps whose denominator equals `1` at the
  -- origin, so the exponential composition is analytic there.
  have hnum : AnalyticAt ℝ (fun l : ℝ ↦ (x : ℝ) * l) 0 := by
    fun_prop
  have hden : AnalyticAt ℝ (fun l : ℝ ↦ l * (t : ℝ) + 1) 0 := by
    fun_prop
  have hfrac : AnalyticAt ℝ (fun l : ℝ ↦ ((x : ℝ) * l) / (l * (t : ℝ) + 1)) 0 := by
    refine hnum.div hden ?_
    norm_num
  simpa [branchingDiffusionLaplaceTransform] using hfrac.neg.rexp'

/-- Helper for Lemma 21.47: the explicit branching-diffusion Laplace transform has derivative
`-x` at `0`. -/
lemma branchingDiffusionLaplaceTransform_hasDerivAt_zero (t x : NNReal) :
    HasDerivAt (branchingDiffusionLaplaceTransform t x) (-(x : ℝ)) 0 := by
  -- Proof comment: differentiate the affine numerator and denominator, use the quotient rule at
  -- the point where the denominator is `1`, and then apply the exponential chain rule.
  have hnum : HasDerivAt (fun l : ℝ ↦ (x : ℝ) * l) (x : ℝ) 0 := by
    simpa [mul_comm] using (hasDerivAt_id (0 : ℝ)).const_mul (x : ℝ)
  have hden : HasDerivAt (fun l : ℝ ↦ l * (t : ℝ) + 1) (t : ℝ) 0 := by
    simpa [mul_comm] using ((hasDerivAt_id (0 : ℝ)).mul_const (t : ℝ)).add_const (1 : ℝ)
  have hfrac : HasDerivAt (fun l : ℝ ↦ ((x : ℝ) * l) / (l * (t : ℝ) + 1)) (x : ℝ) 0 := by
    simpa using
      (hnum.div hden (by norm_num : (fun l : ℝ ↦ l * (t : ℝ) + 1) 0 ≠ 0))
  have hexp :
      HasDerivAt
        (fun l : ℝ ↦ Real.exp (-(((x : ℝ) * l) / (l * (t : ℝ) + 1))))
        (Real.exp 0 * (-(x : ℝ))) 0 := by
    simpa using hfrac.neg.exp
  simpa [branchingDiffusionLaplaceTransform] using hexp

/-- Helper for Lemma 21.47: the signed first iterated derivative of the explicit branching
diffusion Laplace transform at the origin is the initial state `x`. -/
lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_one (t x : NNReal) :
    (-1 : ℝ) ^ 1 * iteratedDeriv 1 (branchingDiffusionLaplaceTransform t x) 0 = x := by
  -- Proof comment: rewrite the first iterated derivative as the ordinary derivative and negate the
  -- derivative identity from the previous lemma.
  rw [iteratedDeriv_one]
  simpa using congrArg Neg.neg (branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv

-- Proof sketch: identify the Laplace transform of `Y t` with
-- `branchingDiffusionLaplaceTransform t x`, differentiate the identity `k` times at `λ = 0`,
-- and use the standard relation between derivatives of `λ ↦ E_x[exp (-λ Y_t)]` and moments.
/-- Claim (1) in Lemma 21.47: for a realization of the branching-diffusion semigroup, the
`k`th marginal moment at time `t` is obtained by differentiating the textbook Laplace transform
at `0`. -/
theorem branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} (k : ℕ) :
    moment (fun ω ↦ (Y t ω : ℝ)) k (P x : Measure Ω) =
      (-1 : ℝ) ^ k * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0 := by
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  let μ : Measure Ω := (P x : Measure Ω)
  have hX_meas : Measurable X := by
    -- Proof comment: the realized process is measurable at each fixed time, and the coercion
    -- `NNReal → ℝ` preserves measurability.
    exact (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
      (hY.measurable_process t)
  have hX_ae : AEMeasurable X μ := hX_meas.aemeasurable
  have hX_nonneg : ∀ᵐ ω ∂μ, 0 ≤ X ω := Eventually.of_forall fun _ ↦ by
    positivity
  let Xm : Ω → ℝ := hX_ae.mk X
  have hXm_meas : Measurable Xm := hX_ae.measurable_mk
  have hX_eq_Xm : X =ᵐ[μ] Xm := hX_ae.ae_eq_mk
  have hXm_nonneg : ∀ᵐ ω ∂μ, 0 ≤ Xm ω := by
    -- Proof comment: the measurable representative agrees almost everywhere with the original
    -- nonnegative process, so it is nonnegative almost everywhere as well.
    filter_upwards [hX_nonneg, hX_eq_Xm] with ω hω hω_eq
    simpa [hω_eq] using hω
  have h_eqOn :
      Set.EqOn (mgf (-Xm) μ) (branchingDiffusionLaplaceTransform t x) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    calc
      mgf (-Xm) μ r = mgf (-X) μ r := by
        rw [ProbabilityTheory.mgf, ProbabilityTheory.mgf]
        refine integral_congr_ae ?_
        filter_upwards [hX_eq_Xm] with ω hω_eq
        simp [X, Xm, hω_eq]
      _ = branchingDiffusionLaplaceTransform t x r := by
        have h_mgf :
            mgf (fun ω ↦ -((Y t ω : ℝ))) (P x : Measure Ω) r =
              branchingDiffusionLaplaceTransform t x r :=
          branchingDiffusion_mgf_neg_eq_explicit_of_pos hY hκ hr
        simpa [X, μ, Pi.neg_apply] using h_mgf
  have h_iterEq :
      Set.EqOn (iteratedDeriv k (mgf (-Xm) μ))
        (iteratedDeriv k (branchingDiffusionLaplaceTransform t x)) (Set.Ioi (0 : ℝ)) := by
    intro r hr
    have h_open : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have h_within :
        Set.EqOn
          (iteratedDerivWithin k (mgf (-Xm) μ) (Set.Ioi (0 : ℝ)))
          (iteratedDerivWithin k (branchingDiffusionLaplaceTransform t x) (Set.Ioi (0 : ℝ)))
          (Set.Ioi (0 : ℝ)) :=
      iteratedDerivWithin_congr h_eqOn
    -- Proof comment: on the open right half-line, equality of the Laplace transforms propagates
    -- to equality of all iterated derivatives.
    calc
      iteratedDeriv k (mgf (-Xm) μ) r =
          iteratedDerivWithin k (mgf (-Xm) μ) (Set.Ioi (0 : ℝ)) r := by
            symm
            exact iteratedDerivWithin_of_isOpen h_open hr
      _ =
          iteratedDerivWithin k (branchingDiffusionLaplaceTransform t x) (Set.Ioi (0 : ℝ)) r :=
        h_within hr
      _ = iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r := by
            exact iteratedDerivWithin_of_isOpen h_open hr
  have h_limit_mgf :
      Tendsto
        (fun r : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ k) * iteratedDeriv k (mgf (-Xm) μ) r))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ)) :=
    tendsto_ofReal_signed_iteratedDeriv_laplaceTransform_right_zero hXm_meas hXm_nonneg k
  have h_eventually_eq :
      (fun r : ℝ ↦ ENNReal.ofReal (((-1 : ℝ) ^ k) * iteratedDeriv k (mgf (-Xm) μ) r)) =ᶠ[𝓝[>] 0]
        (fun r : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    rw [h_iterEq hr.1]
  have h_limit_transform :
      Tendsto
        (fun r : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ)) := by
    exact Filter.Tendsto.congr' h_eventually_eq h_limit_mgf
  have h_analytic :
      AnalyticAt ℝ (branchingDiffusionLaplaceTransform t x) 0 :=
    branchingDiffusionLaplaceTransform_analyticAt_zero t x
  have h_iterCont :
      ContinuousAt
        (fun r : ℝ ↦ iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r) 0 := by
    simpa [iteratedDeriv_eq_iterate] using (h_analytic.iterated_deriv k).continuousAt
  have h_signedCont :
      ContinuousAt
        (fun r : ℝ ↦
          ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r)
        0 :=
    h_iterCont.const_mul ((-1 : ℝ) ^ k)
  have h_ofReal_cont :
      ContinuousAt ENNReal.ofReal
        (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0) :=
    ENNReal.continuous_ofReal.continuousAt
  have h_limit_value :
      Tendsto
        (fun r : ℝ ↦
          ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r))
        (𝓝[>] (0 : ℝ))
        (𝓝
          (ENNReal.ofReal
            (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0))) := by
    exact h_ofReal_cont.tendsto.comp (h_signedCont.tendsto.mono_left nhdsWithin_le_nhds)
  have h_lintegral :
      ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ =
        ENNReal.ofReal
          (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0) :=
    tendsto_nhds_unique h_limit_transform h_limit_value
  have h_signed_nonneg_pos :
      ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
        0 ≤ ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
    have h_sign :
        ∀ ω,
          ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) =
            (Xm ω) ^ k * Real.exp (-(r * Xm ω)) := by
      intro ω
      have hpow :
          ((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k = (Xm ω) ^ k := by
        calc
          ((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k =
              ((-1 : ℝ) ^ k) * (((-1 : ℝ) * Xm ω) ^ k) := by
                congr 1
                ring
          _ = ((-1 : ℝ) ^ k) * (((-1 : ℝ) ^ k) * (Xm ω) ^ k) := by
                rw [mul_pow]
          _ = ((((-1 : ℝ) ^ k) * (-1 : ℝ) ^ k) * (Xm ω) ^ k) := by ring
          _ = (Xm ω) ^ k := by
                rw [← pow_add]
                simp
      calc
        ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) =
            (((-1 : ℝ) ^ k) * (-(Xm ω)) ^ k) * Real.exp (-(r * Xm ω)) := by ring
        _ = (Xm ω) ^ k * Real.exp (-(r * Xm ω)) := by rw [hpow]
    rw [← h_iterEq hr.1, iteratedDeriv_laplaceTransform_eq hXm_meas hXm_nonneg k hr.1]
    calc
      ((-1 : ℝ) ^ k) * ∫ ω, (-(Xm ω)) ^ k * Real.exp (-(r * Xm ω)) ∂μ =
          ∫ ω, ((-1 : ℝ) ^ k) * ((-(Xm ω)) ^ k * Real.exp (-(r * Xm ω))) ∂μ := by
            rw [← integral_const_mul]
      _ = ∫ ω, (Xm ω) ^ k * Real.exp (-(r * Xm ω)) ∂μ := by
            refine integral_congr_ae (Eventually.of_forall h_sign)
      _ ≥ 0 := by
            refine integral_nonneg_of_ae ?_
            filter_upwards [hXm_nonneg] with ω hω
            exact mul_nonneg (pow_nonneg hω _) (Real.exp_pos _).le
  have h_signed_nonneg :
      0 ≤ ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0 := by
    have h_tendsto_signed :
        Tendsto
          (fun r : ℝ ↦
            ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r)
          (𝓝[>] (0 : ℝ))
          (𝓝 (((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0)) :=
      h_signedCont.tendsto.mono_left nhdsWithin_le_nhds
    have h_nonneg_mem :
        ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) r ∈
            Set.Ici (0 : ℝ) := h_signed_nonneg_pos
    exact IsClosed.mem_of_tendsto isClosed_Ici h_tendsto_signed h_nonneg_mem
  have h_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ =
        ∫⁻ ω, ENNReal.ofReal ((X ω) ^ k) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hX_eq_Xm] with ω hω_eq
    simp [hω_eq]
  have h_pow_nonneg_Xm : 0 ≤ᵐ[μ] fun ω ↦ (Xm ω) ^ k := by
    filter_upwards [hXm_nonneg] with ω hω
    exact pow_nonneg hω _
  have h_pow_int_Xm :
      Integrable (fun ω ↦ (Xm ω) ^ k) μ := by
    have h_meas_enn :
        AEMeasurable (fun ω ↦ ENNReal.ofReal ((Xm ω) ^ k)) μ := by
      fun_prop
    have h_lintegral_ne_top :
        ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ ≠ ∞ := by
      rw [h_lintegral]
      exact ENNReal.ofReal_ne_top
    refine (integrable_toReal_of_lintegral_ne_top h_meas_enn h_lintegral_ne_top).congr ?_
    filter_upwards [hXm_nonneg] with ω hω
    simp [ENNReal.toReal_ofReal, pow_nonneg hω]
  have h_moment_eq :
      moment X k μ = moment Xm k μ := by
    rw [moment_def, moment_def]
    refine integral_congr_ae ?_
    filter_upwards [hX_eq_Xm] with ω hω_eq
    simp [X, Xm, hω_eq]
  have h_moment_nonneg_Xm :
      0 ≤ moment Xm k μ := by
    rw [moment_def]
    exact integral_nonneg_of_ae h_pow_nonneg_Xm
  have h_ofReal_moment_Xm :
      ENNReal.ofReal (moment Xm k μ) = ∫⁻ ω, ENNReal.ofReal ((Xm ω) ^ k) ∂μ := by
    simpa [moment_def] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_pow_int_Xm h_pow_nonneg_Xm)
  have h_moment_Xm :
      moment Xm k μ =
        ((-1 : ℝ) ^ k) * iteratedDeriv k (branchingDiffusionLaplaceTransform t x) 0 := by
    rw [← ENNReal.ofReal_eq_ofReal_iff h_moment_nonneg_Xm h_signed_nonneg]
    rw [h_ofReal_moment_Xm, h_lintegral]
  -- Proof comment: the measurable representative has the same moments as the original process, so
  -- the real moment identity follows from the right-limit computation at the explicit transform.
  exact h_moment_eq.trans h_moment_Xm

-- Proof sketch: specialize
-- `branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv` to `k = 1` and evaluate the first
-- derivative of `λ ↦ exp (-x λ / (1 + t λ))` at `0`.
/-- Claim (2) in Lemma 21.47: the first moment of the branching diffusion remains equal to the
initial state `x`. -/
theorem branchingDiffusion_first_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 1 (P x : Measure Ω) = x := by
  -- Proof comment: specialize the signed-derivative moment identity to `k = 1` and evaluate the
  -- first signed derivative of the explicit Laplace transform at `0`.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 1 (P x : Measure Ω) =
        (-1 : ℝ) ^ 1 * iteratedDeriv 1 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 1
    _ = x := branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_one t x

/-- Helper for Lemma 21.47: the branching-diffusion kernel preserves the linear observable
`y ↦ (y : ℝ)` in expectation. -/
lemma branchingDiffusionKernelIntegral_id
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (u z : NNReal) :
    ∫ y, (y : ℝ) ∂κ u z = z := by
  have h_integral_realization :
      ∫ ω, (Y u ω : ℝ) ∂(P z : Measure Ω) = ∫ y, (y : ℝ) ∂κ u z := by
    -- Proof comment: the realized one-time marginal at time `u` is exactly the kernel row
    -- `κ u z`, so the linear observable can be pushed through the map identity.
    calc
      ∫ ω, (Y u ω : ℝ) ∂(P z : Measure Ω) =
          ∫ y, (y : ℝ) ∂((P z : Measure Ω).map (Y u)) := by
            symm
            rw [MeasureTheory.integral_map (hY.measurable_process u).aemeasurable (by fun_prop)]
      _ = ∫ y, (y : ℝ) ∂κ u z := by
            rw [hY.transition_eq z u]
  -- Proof comment: transport the kernel-row integral back to the realized process using the
  -- one-time marginal law, rewrite that integral as the first moment, and then apply the
  -- signed-derivative first-moment computation.
  calc
    ∫ y, (y : ℝ) ∂κ u z =
        ∫ ω, (Y u ω : ℝ) ∂(P z : Measure Ω) := by
          exact h_integral_realization.symm
    _ = z := by
          have h_first : moment (fun ω ↦ (Y u ω : ℝ)) 1 (P z : Measure Ω) = z :=
            branchingDiffusion_first_moment hY hκ
          simpa [moment_one] using h_first

/-- Helper for Lemma 21.47: every fixed-time branching-diffusion coordinate is integrable under
the start law `P x`. -/
lemma branchingDiffusion_integrable
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t : NNReal) :
    Integrable (fun ω ↦ (Y t ω : ℝ)) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hMoment : ∫ ω, X ω ∂μ = x := by
    have h_first : moment (fun ω ↦ (Y t ω : ℝ)) 1 (P x : Measure Ω) = x :=
      branchingDiffusion_first_moment hY hκ
    simpa [μ, X, moment_one] using h_first
  by_cases hx : x = 0
  · have hLaplace :
      ∫ ω, Real.exp (-(Y t ω : ℝ)) ∂μ = 1 := by
        simpa [ProbabilityTheory.branchingDiffusionLaplaceTransform, μ, hx] using
          hY.branchingDiffusionLaplaceTransform hκ (0 : NNReal) t (1 : NNReal)
    have hExpInt : Integrable (fun ω ↦ Real.exp (-(Y t ω : ℝ))) μ := by
      have h_exp : Measurable fun z : ℝ ↦ Real.exp z := Real.continuous_exp.measurable
      have hExpMeas : Measurable (fun ω ↦ Real.exp (-(Y t ω : ℝ))) := by
        exact h_exp.comp ((measurable_subtype_coe.comp (hY.measurable_process t)).neg)
      refine Integrable.of_bound hExpMeas.aestronglyMeasurable 1 ?_
      exact Eventually.of_forall fun ω ↦ by
        have hle : Real.exp (-(Y t ω : ℝ)) ≤ 1 := by
          exact Real.exp_le_one_iff.2 (neg_nonpos.mpr (by positivity))
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        exact hle
    let g : Ω → ℝ := fun ω ↦ 1 - Real.exp (-(Y t ω : ℝ))
    have hgNonneg : ∀ᵐ ω ∂μ, 0 ≤ g ω := Eventually.of_forall fun ω ↦ by
      dsimp [g]
      exact sub_nonneg.2 (Real.exp_le_one_iff.2 (neg_nonpos.mpr (by positivity)))
    have hgInt : Integrable g μ := by
      dsimp [g]
      exact (integrable_const (1 : ℝ)).sub hExpInt
    have hgZero : ∫ ω, g ω ∂μ = 0 := by
      calc
        ∫ ω, g ω ∂μ = ∫ ω, (1 : ℝ) ∂μ - ∫ ω, Real.exp (-(Y t ω : ℝ)) ∂μ := by
            simp [g, integral_sub (integrable_const (1 : ℝ)) hExpInt]
        _ = 1 - 1 := by simp [μ, hLaplace]
        _ = 0 := by ring
    have hgAe : g =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hgNonneg hgInt).1 hgZero
    have hXZero : X =ᵐ[μ] 0 := by
      filter_upwards [hgAe] with ω hω
      dsimp [g, X] at hω ⊢
      have hExpEq : Real.exp (-(Y t ω : ℝ)) = 1 := by linarith
      have hZero : -(Y t ω : ℝ) = 0 := (Real.exp_eq_one_iff _).1 hExpEq
      linarith
    refine
      (show Integrable (fun _ : Ω ↦ (0 : ℝ)) μ from
        integrable_zero Ω ℝ μ).congr hXZero.symm
  · by_contra hInt
    have hxReal : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    have hZero : ∫ ω, X ω ∂μ = 0 := integral_undef hInt
    exact hxReal (by simpa [hMoment] using hZero)

/-- Helper for Lemma 21.47: near `0`, the linear denominator `1 + t l` stays away from `0`. -/
private lemma branchingDiffusionLaplaceTransform_denominator_ne_zero_nhds_zero (t : NNReal) :
    ∀ᶠ l : ℝ in 𝓝 (0 : ℝ), (t : ℝ) * l + 1 ≠ 0 := by
  have hcont : ContinuousAt (fun l : ℝ ↦ (t : ℝ) * l + 1) 0 := by
    fun_prop
  have hzero : (t : ℝ) * (0 : ℝ) + 1 ≠ 0 := by
    norm_num
  exact hcont.eventually_ne hzero

/-- Helper for Lemma 21.47: away from the pole of `1 + t l`, the explicit Laplace transform has
the weighted derivative shape `F' = -x (1 + t l)⁻² F`. -/
private lemma branchingDiffusionLaplaceTransform_hasDerivAt_weighted
    (t x : NNReal) {l : ℝ} (hden : (t : ℝ) * l + 1 ≠ 0) :
    HasDerivAt (branchingDiffusionLaplaceTransform t x)
      ((-(x : ℝ)) *
        ((((t : ℝ) * l + 1)⁻¹)^2 * branchingDiffusionLaplaceTransform t x l)) l := by
  have hnum : HasDerivAt (fun u : ℝ ↦ (x : ℝ) * u) (x : ℝ) l := by
    simpa [mul_comm] using (hasDerivAt_id l).const_mul (x : ℝ)
  have hden' : HasDerivAt (fun u : ℝ ↦ (t : ℝ) * u + 1) (t : ℝ) l := by
    simpa [mul_comm] using ((hasDerivAt_id l).const_mul (t : ℝ)).add_const (1 : ℝ)
  have hfrac :
      HasDerivAt (fun u : ℝ ↦ ((x : ℝ) * u) / ((t : ℝ) * u + 1))
        ((x : ℝ) * (((t : ℝ) * l + 1)⁻¹)^2) l := by
    convert hnum.div hden' hden using 1
    · field_simp [hden]
      ring
  have hexp :
      HasDerivAt
        (fun u : ℝ ↦ Real.exp (-(((x : ℝ) * u) / ((t : ℝ) * u + 1))))
        (Real.exp (-(((x : ℝ) * l) / ((t : ℝ) * l + 1))) *
          ((-(x : ℝ)) * (((t : ℝ) * l + 1)⁻¹)^2)) l := by
    simpa using hfrac.neg.exp
  -- Proof comment: after the quotient-rule calculation for the exponent, the chain rule only
  -- leaves a commutative-ring normalization.
  convert hexp using 1
  · funext u
    simp [branchingDiffusionLaplaceTransform, mul_comm]
  · simp [branchingDiffusionLaplaceTransform, mul_assoc, mul_comm]

/-- Helper for Lemma 21.47: the inverse linear factor `l ↦ (1 + t l)⁻¹` is smooth at `0`. -/
private lemma branchingDiffusion_inverseLinear_contDiffAt_zero
    (t : NNReal) (k : ℕ) :
    ContDiffAt ℝ k (fun l : ℝ ↦ ((t : ℝ) * l + 1)⁻¹) 0 := by
  have hlin : ContDiffAt ℝ k (fun l : ℝ ↦ (t : ℝ) * l + 1) 0 := by
    fun_prop
  simpa using hlin.inv (by norm_num : (fun l : ℝ ↦ (t : ℝ) * l + 1) 0 ≠ 0)

/-- Helper for Lemma 21.47: near `0`, the derivative of the explicit Laplace transform agrees
with the normalized weighted product form used for the raw-moment recursion. -/
private lemma branchingDiffusionLaplaceTransform_deriv_eq_nhds_zero (t x : NNReal) :
    deriv (branchingDiffusionLaplaceTransform t x) =ᶠ[𝓝 (0 : ℝ)]
      fun l ↦
        (-(x : ℝ)) *
          (((((t : ℝ) * l + 1)⁻¹)^2) * branchingDiffusionLaplaceTransform t x l) := by
  -- Proof comment: the denominator side condition is automatic on a neighborhood of `0`, so the
  -- pointwise derivative identity can be read off from `HasDerivAt`.
  filter_upwards [branchingDiffusionLaplaceTransform_denominator_ne_zero_nhds_zero t] with l hden
  exact (branchingDiffusionLaplaceTransform_hasDerivAt_weighted t x hden).deriv

/-- Helper for Lemma 21.47: near `0`, the inverse linear factor differentiates to the inverse
square factor scaled by `-t`. -/
private lemma branchingDiffusion_inverseLinear_deriv_eq_nhds_zero (t : NNReal) :
    deriv (fun l : ℝ ↦ ((t : ℝ) * l + 1)⁻¹) =ᶠ[𝓝 (0 : ℝ)]
      fun l ↦ (-(t : ℝ)) * (((t : ℝ) * l + 1)⁻¹)^2 := by
  -- Proof comment: the affine denominator stays nonzero near `0`, so the derivative is the
  -- standard inverse-function derivative on that neighborhood.
  filter_upwards [branchingDiffusionLaplaceTransform_denominator_ne_zero_nhds_zero t] with l hden
  have hlin : HasDerivAt (fun u : ℝ ↦ (t : ℝ) * u + 1) (t : ℝ) l := by
    simpa [mul_comm] using ((hasDerivAt_id l).const_mul (t : ℝ)).add_const (1 : ℝ)
  simpa [div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm] using (hlin.inv hden).deriv

/-- Helper for Lemma 21.47: the signed derivatives at `0` of the inverse linear factor
`l ↦ (1 + t l)⁻¹` are `k! t^k`. -/
private lemma branchingDiffusion_inverseLinear_signedIteratedDerivAtZero
    (t : NNReal) (k : ℕ) :
    (-1 : ℝ) ^ k * iteratedDeriv k (fun l : ℝ ↦ ((t : ℝ) * l + 1)⁻¹) 0 =
      (k.factorial : ℝ) * (t : ℝ) ^ k := by
  -- Proof comment: rewrite `iteratedDeriv` as `deriv^[k]`, evaluate the closed formula for the
  -- affine inverse at `0`, and then collapse the two sign factors algebraically.
  rw [iteratedDeriv_eq_iterate]
  have h := congrArg (fun g : ℝ → ℝ ↦ g 0) (iter_deriv_inv_linear k (t : ℝ) (1 : ℝ))
  simp only [mul_zero] at h
  norm_num at h
  rw [h]
  have hsign : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← pow_add]
    simp
  calc
    (-1 : ℝ) ^ k * (((-1 : ℝ) ^ k * (k.factorial : ℝ)) * (t : ℝ) ^ k) =
        (((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) * (k.factorial : ℝ)) * (t : ℝ) ^ k := by
          ring
    _ = (k.factorial : ℝ) * (t : ℝ) ^ k := by
          rw [hsign]
          ring

/-- Helper for Lemma 21.47: the signed derivatives at `0` of `l ↦ (1 + t l)⁻²` are
`(k + 1)! t^k`. -/
private lemma branchingDiffusion_inverseSquare_signedIteratedDerivAtZero
    (t : NNReal) (k : ℕ) :
    (-1 : ℝ) ^ k * iteratedDeriv k (fun l : ℝ ↦ (((t : ℝ) * l + 1)⁻¹)^2) 0 =
      (((k + 1).factorial : ℝ) * (t : ℝ) ^ k) := by
  by_cases ht : t = 0
  · subst ht
    cases k with
    | zero =>
        -- Proof comment: at `t = 0`, the inverse-square factor is the constant function `1`.
        simp
    | succ k =>
        -- Proof comment: every positive-order iterated derivative of the constant function `1`
        -- vanishes.
        rw [iteratedDeriv_succ']
        simp
  · have hderivEq :
      iteratedDeriv k (deriv (fun l : ℝ ↦ ((t : ℝ) * l + 1)⁻¹)) 0 =
        iteratedDeriv k (fun l : ℝ ↦ (-(t : ℝ)) * (((t : ℝ) * l + 1)⁻¹)^2) 0 := by
      exact
        Filter.EventuallyEq.iteratedDeriv_eq k
          (branchingDiffusion_inverseLinear_deriv_eq_nhds_zero t)
    have hk1 := branchingDiffusion_inverseLinear_signedIteratedDerivAtZero t (k + 1)
    rw [iteratedDeriv_succ', hderivEq, iteratedDeriv_const_mul_field] at hk1
    have hk1' :
        (t : ℝ) *
            (((-1 : ℝ) ^ k) *
              iteratedDeriv k (fun l : ℝ ↦ (((t : ℝ) * l + 1)⁻¹)^2) 0) =
          (((k + 1).factorial : ℝ) * (t : ℝ) ^ (k + 1)) := by
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hk1
    have hk1'' :
        (t : ℝ) *
            (((-1 : ℝ) ^ k) *
              iteratedDeriv k (fun l : ℝ ↦ (((t : ℝ) * l + 1)⁻¹)^2) 0) =
          (t : ℝ) * ((((k + 1).factorial : ℝ) * (t : ℝ) ^ k)) := by
      calc
        (t : ℝ) *
            (((-1 : ℝ) ^ k) *
              iteratedDeriv k (fun l : ℝ ↦ (((t : ℝ) * l + 1)⁻¹)^2) 0) =
            (((k + 1).factorial : ℝ) * (t : ℝ) ^ (k + 1)) := hk1'
        _ = (t : ℝ) * ((((k + 1).factorial : ℝ) * (t : ℝ) ^ k)) := by
            rw [pow_succ']
            ring
    have ht0 : (t : ℝ) ≠ 0 := by
      exact_mod_cast ht
    exact mul_left_cancel₀ ht0 hk1''

/-- Helper for Lemma 21.47: the signed derivatives of the explicit Laplace transform satisfy the
Leibniz recursion coming from `F' = -x (1 + t l)⁻² F`. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ
    (t x : NNReal) (k : ℕ) :
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv (k + 1) (branchingDiffusionLaplaceTransform t x) 0 =
      (x : ℝ) *
        (Finset.sum (Finset.range (k + 1)) fun i ↦
          (k.choose i : ℝ) *
            ((((i + 1).factorial : ℝ) * (t : ℝ) ^ i) *
              (((-1 : ℝ) ^ (k - i)) *
                iteratedDeriv (k - i) (branchingDiffusionLaplaceTransform t x) 0))) := by
  let G : ℝ → ℝ := fun l ↦ (((t : ℝ) * l + 1)⁻¹)^2
  let F : ℝ → ℝ := branchingDiffusionLaplaceTransform t x
  have hcontG : ContDiffAt ℝ k G 0 := by
    -- Proof comment: the inverse linear factor is smooth at `0`, and squaring preserves that
    -- regularity.
    simpa [G] using (branchingDiffusion_inverseLinear_contDiffAt_zero t k).pow 2
  have hcontF : ContDiffAt ℝ k F 0 := by
    -- Proof comment: the explicit Laplace transform is analytic at the origin.
    simpa [F] using (branchingDiffusionLaplaceTransform_analyticAt_zero t x).contDiffAt
  have hderivEq :
      iteratedDeriv k (deriv F) 0 =
        iteratedDeriv k (fun l ↦ (-(x : ℝ)) * (G l * F l)) 0 := by
    -- Proof comment: near `0`, the derivative has the stable normal form `-x * G * F`, so their
    -- `k`th iterated derivatives at `0` coincide.
    exact
      Filter.EventuallyEq.iteratedDeriv_eq k <|
        by
          simpa [F, G, mul_assoc, mul_left_comm, mul_comm] using
            branchingDiffusionLaplaceTransform_deriv_eq_nhds_zero t x
  have hsignNeg : (-1 : ℝ) ^ (k + 1) * (-(1 : ℝ)) = (-1 : ℝ) ^ k := by
    rw [show (-(1 : ℝ)) = (-1 : ℝ) by norm_num]
    rw [show k + 1 = k + 1 by omega, pow_add]
    norm_num
  have hsum :
      (-1 : ℝ) ^ k *
          Finset.sum (Finset.range (k + 1)) (fun i ↦
            (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0) =
        Finset.sum (Finset.range (k + 1)) (fun i ↦
          (k.choose i : ℝ) *
            ((((i + 1).factorial : ℝ) * (t : ℝ) ^ i) *
              (((-1 : ℝ) ^ (k - i)) * iteratedDeriv (k - i) F 0))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_le : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hpow : (-1 : ℝ) ^ k = (-1 : ℝ) ^ i * (-1 : ℝ) ^ (k - i) := by
      rw [← pow_add]
      congr 1
      symm
      exact Nat.add_sub_of_le hi_le
    -- Proof comment: split the global sign into the inverse-square part and the remaining
    -- transform part, then substitute the inverse-square closed formula.
    calc
      (-1 : ℝ) ^ k * ((k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0) =
          (k.choose i : ℝ) *
            ((((-1 : ℝ) ^ i) * iteratedDeriv i G 0) *
              (((-1 : ℝ) ^ (k - i)) * iteratedDeriv (k - i) F 0)) := by
            rw [hpow]
            ring
      _ = (k.choose i : ℝ) *
            ((((i + 1).factorial : ℝ) * (t : ℝ) ^ i) *
              (((-1 : ℝ) ^ (k - i)) * iteratedDeriv (k - i) F 0)) := by
            rw [branchingDiffusion_inverseSquare_signedIteratedDerivAtZero t i]
  calc
    (-1 : ℝ) ^ (k + 1) * iteratedDeriv (k + 1) F 0 =
        (-1 : ℝ) ^ (k + 1) * iteratedDeriv k (deriv F) 0 := by
          rw [iteratedDeriv_succ']
    _ =
        (-1 : ℝ) ^ (k + 1) * iteratedDeriv k (fun l ↦ (-(x : ℝ)) * (G l * F l)) 0 := by
          rw [hderivEq]
    _ =
        (-1 : ℝ) ^ (k + 1) *
          ((-(x : ℝ)) *
            Finset.sum (Finset.range (k + 1)) (fun i ↦
              (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0)) := by
          rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_mul hcontG hcontF]
    _ =
        (x : ℝ) *
          (((-1 : ℝ) ^ k) *
            Finset.sum (Finset.range (k + 1)) (fun i ↦
              (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0)) := by
          rw [show (-(x : ℝ)) = (-(1 : ℝ)) * (x : ℝ) by ring]
          calc
            (-1 : ℝ) ^ (k + 1) *
                ((-(1 : ℝ)) * (x : ℝ) *
                  Finset.sum (Finset.range (k + 1)) (fun i ↦
                    (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0)) =
                (((-1 : ℝ) ^ (k + 1) * (-(1 : ℝ))) * (x : ℝ)) *
                  Finset.sum (Finset.range (k + 1)) (fun i ↦
                    (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0) := by
                      ring
            _ = (((-1 : ℝ) ^ k) * (x : ℝ)) *
                  Finset.sum (Finset.range (k + 1)) (fun i ↦
                    (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0) := by
                      rw [hsignNeg]
            _ = (x : ℝ) *
                  (((-1 : ℝ) ^ k) *
                    Finset.sum (Finset.range (k + 1)) (fun i ↦
                      (k.choose i : ℝ) * iteratedDeriv i G 0 * iteratedDeriv (k - i) F 0)) := by
                      ring
    _ =
        (x : ℝ) *
          (Finset.sum (Finset.range (k + 1)) fun i ↦
            (k.choose i : ℝ) *
              ((((i + 1).factorial : ℝ) * (t : ℝ) ^ i) *
                (((-1 : ℝ) ^ (k - i)) * iteratedDeriv (k - i) F 0))) := by
          rw [hsum]

/-- Helper for Lemma 21.47: the signed second derivative of the explicit Laplace transform at `0`
is `2xt + x²`. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two
    (t x : NNReal) :
    (-1 : ℝ) ^ 2 * iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 =
      2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
  have hrec := by
    simpa [Finset.sum_range_succ, branchingDiffusionLaplaceTransform_zero] using
      (branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ t x 1)
  -- Proof comment: expand the concrete two-term Leibniz sum and rewrite the zeroth and first
  -- signed derivatives by the previously established identities.
  rw [(branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv] at hrec
  ring_nf at hrec ⊢
  exact hrec

/-- Helper for Lemma 21.47: the signed third derivative of the explicit Laplace transform at `0`
is `6xt² + 6x²t + x³`. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_three
    (t x : NNReal) :
    (-1 : ℝ) ^ 3 * iteratedDeriv 3 (branchingDiffusionLaplaceTransform t x) 0 =
      6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
  have hrec := by
    simpa [Finset.sum_range_succ, branchingDiffusionLaplaceTransform_zero] using
      (branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ t x 2)
  -- Proof comment: the order-three case is the `k = 2` concrete recurrence with the known
  -- derivatives of orders at most two substituted in.
  have h2raw :
      iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 =
        2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa using branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two t x
  rw [(branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv, h2raw] at hrec
  ring_nf at hrec ⊢
  exact hrec

/-- Helper for Lemma 21.47: the signed fourth derivative of the explicit Laplace transform at `0`
is the textbook fourth raw-moment polynomial. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_four
    (t x : NNReal) :
    (-1 : ℝ) ^ 4 * iteratedDeriv 4 (branchingDiffusionLaplaceTransform t x) 0 =
      24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
        12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
  have hrec := by
    simpa [Finset.sum_range_succ, branchingDiffusionLaplaceTransform_zero] using
      (branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ t x 3)
  -- Proof comment: expand the four Leibniz terms and use the already-closed formulas up to order
  -- three.
  have h2raw :
      iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 =
        2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa using branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two t x
  rw [(branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv, h2raw,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_three t x] at hrec
  ring_nf at hrec ⊢
  exact hrec

/-- Helper for Lemma 21.47: the signed fifth derivative of the explicit Laplace transform at `0`
is the textbook fifth raw-moment polynomial. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_five
    (t x : NNReal) :
    (-1 : ℝ) ^ 5 * iteratedDeriv 5 (branchingDiffusionLaplaceTransform t x) 0 =
      120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
        (x : ℝ) ^ 5 := by
  have hrec := by
    simpa [Finset.sum_range_succ, branchingDiffusionLaplaceTransform_zero] using
      (branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ t x 4)
  -- Proof comment: after the finite Leibniz expansion at `k = 4`, only the already-established
  -- signed derivatives of orders at most four remain.
  have h2raw :
      iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 =
        2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa using branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two t x
  rw [(branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv, h2raw,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_three t x,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_four t x] at hrec
  ring_nf at hrec ⊢
  norm_num [Nat.choose] at hrec
  ring_nf at hrec
  exact hrec

/-- Helper for Lemma 21.47: the signed sixth derivative of the explicit Laplace transform at `0`
is the textbook sixth raw-moment polynomial. -/
private lemma branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_six
    (t x : NNReal) :
    (-1 : ℝ) ^ 6 * iteratedDeriv 6 (branchingDiffusionLaplaceTransform t x) 0 =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
        30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := by
  have hrec := by
    simpa [Finset.sum_range_succ, branchingDiffusionLaplaceTransform_zero] using
      (branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_succ t x 5)
  -- Proof comment: the sixth-order identity is the last concrete recurrence, simplified after
  -- rewriting all lower-order signed derivatives.
  have h2raw :
      iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 =
        2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa using branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two t x
  rw [(branchingDiffusionLaplaceTransform_hasDerivAt_zero t x).deriv, h2raw,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_three t x,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_four t x,
    branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_five t x] at hrec
  ring_nf at hrec ⊢
  norm_num [Nat.choose] at hrec
  ring_nf at hrec
  exact hrec

-- Proof sketch: differentiate the Laplace transform twice at `0`, or specialize the general
-- moment formula with `k = 2` and simplify the resulting polynomial.
/-- Claim (3) in Lemma 21.47: the second moment of the branching diffusion is `2xt + x²`. -/
theorem branchingDiffusion_second_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 2 (P x : Measure Ω) =
      2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
  -- Proof comment: transport the second raw moment to the signed second derivative of the
  -- explicit Laplace transform and then insert its closed form at `0`.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 2 (P x : Measure Ω) =
        (-1 : ℝ) ^ 2 * iteratedDeriv 2 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 2
    _ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 :=
          branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_two t x

-- Proof sketch: differentiate the Laplace transform three times at `0` and simplify the
-- coefficient expansion.
/-- Claim (4) in Lemma 21.47: the third moment of the branching diffusion is
`6xt² + 6x²t + x³`. -/
theorem branchingDiffusion_third_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 3 (P x : Measure Ω) =
      6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
  -- Proof comment: clause (1) reduces the third raw moment to the third signed derivative of the
  -- explicit Laplace transform.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 3 (P x : Measure Ω) =
        (-1 : ℝ) ^ 3 * iteratedDeriv 3 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 3
    _ = 6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 :=
          branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_three t x

-- Proof sketch: differentiate the Laplace transform four times at `0` and collect the resulting
-- polynomial coefficients.
/-- Claim (5) in Lemma 21.47: the fourth moment of the branching diffusion is
`24xt³ + 36x²t² + 12x³t + x⁴`. -/
theorem branchingDiffusion_fourth_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
      24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
        12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
  -- Proof comment: the fourth raw moment is the fourth signed derivative of the explicit
  -- Laplace transform at `0`.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
        (-1 : ℝ) ^ 4 * iteratedDeriv 4 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 4
    _ = 24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 :=
          branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_four t x

-- Proof sketch: differentiate the Laplace transform five times at `0` and simplify the resulting
-- coefficients.
/-- Claim (6) in Lemma 21.47: the fifth moment of the branching diffusion is
`120xt⁴ + 240x²t³ + 120x³t² + 20x⁴t + x⁵`. -/
theorem branchingDiffusion_fifth_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 5 (P x : Measure Ω) =
      120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
        (x : ℝ) ^ 5 := by
  -- Proof comment: clause (1) converts the fifth raw moment to the fifth signed derivative of the
  -- Laplace transform, which was computed recursively above.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 5 (P x : Measure Ω) =
        (-1 : ℝ) ^ 5 * iteratedDeriv 5 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 5
    _ = 120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
          120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
          (x : ℝ) ^ 5 :=
          branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_five t x

-- Proof sketch: differentiate the Laplace transform six times at `0` and collect the polynomial
-- coefficients of the resulting expression.
/-- Claim (7) in Lemma 21.47: the sixth moment of the branching diffusion is
`720xt⁵ + 1800x²t⁴ + 1200x³t³ + 300x⁴t² + 30x⁵t + x⁶`. -/
theorem branchingDiffusion_sixth_moment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    moment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
        30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := by
  -- Proof comment: the sixth raw moment is the sixth signed derivative value of the explicit
  -- Laplace transform at the origin.
  calc
    moment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
        (-1 : ℝ) ^ 6 * iteratedDeriv 6 (branchingDiffusionLaplaceTransform t x) 0 := by
          simpa using branchingDiffusion_moment_eq_neg_one_pow_iteratedDeriv hY hκ 6
    _ = 720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
          1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
          30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 :=
          branchingDiffusionLaplaceTransform_signedIteratedDerivAtZero_six t x

/-- Helper for Lemma 21.47: if the branching diffusion starts from `0`, every later coordinate
vanishes almost surely. -/
private lemma branchingDiffusion_ae_eq_zero_of_zero_start
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (t : NNReal) :
    (fun ω ↦ (Y t ω : ℝ)) =ᵐ[(P 0 : Measure Ω)] fun _ ↦ 0 := by
  let μ : Measure Ω := (P 0 : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have h_int : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ 0 t
  have h_nonneg : 0 ≤ᵐ[μ] X := Eventually.of_forall fun _ ↦ by
    positivity
  have h_zero_int : ∫ ω, X ω ∂μ = 0 := by
    have h_first : moment X 1 μ = 0 := by
      simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := 0) (t := t))
    simpa [moment_one] using h_first
  exact (integral_eq_zero_iff_of_nonneg_ae h_nonneg h_int).1 h_zero_int

/-- Helper for Lemma 21.47: the sixth power of the branching-diffusion coordinate is integrable. -/
private lemma branchingDiffusion_integrable_pow_six
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t : NNReal) :
    Integrable (fun ω ↦ (Y t ω : ℝ) ^ 6) (P x : Measure Ω) := by
  by_cases hx : x = 0
  · have hzero :
        (fun ω ↦ (Y t ω : ℝ) ^ 6) =ᵐ[(P x : Measure Ω)] fun _ ↦ 0 := by
          simpa [hx] using
            (branchingDiffusion_ae_eq_zero_of_zero_start hY hκ t).mono fun ω hω ↦ by
              simp [hω]
    exact (integrable_zero Ω ℝ (P x : Measure Ω)).congr hzero.symm
  · by_contra h_int
    have h_formula :
        moment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
          720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
            1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
            30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 :=
      branchingDiffusion_sixth_moment hY hκ
    have hx_pos : 0 < (x : ℝ) := by
      exact_mod_cast (show 0 < x from pos_iff_ne_zero.mpr hx)
    have hx6_pos : 0 < (x : ℝ) ^ 6 := by
      positivity
    have h_rhs_pos :
        0 <
          720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
            1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
            30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := by
      have h1 : 0 ≤ 720 * (x : ℝ) * (t : ℝ) ^ 5 := by positivity
      have h2 : 0 ≤ 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 := by positivity
      have h3 : 0 ≤ 1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 := by positivity
      have h4 : 0 ≤ 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 := by positivity
      have h5 : 0 ≤ 30 * (x : ℝ) ^ 5 * (t : ℝ) := by positivity
      nlinarith
    have h_zero :
        moment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) = 0 := by
      simpa [moment_def] using
        (integral_undef h_int :
          ∫ ω, ((fun ω ↦ (Y t ω : ℝ)) ^ 6) ω ∂(P x : Measure Ω) = 0)
    linarith

/-- Helper for Lemma 21.47: every power of the branching-diffusion coordinate up to degree `6`
is integrable. -/
private lemma branchingDiffusion_integrable_pow_le_six
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x t : NNReal) {p : ℕ} (hp : p ≤ 6) :
    Integrable (fun ω ↦ (Y t ω : ℝ) ^ p) (P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hX_meas : Measurable X := by
    exact (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).measurable.comp
      (hY.measurable_process t)
  have h6 : Integrable (fun ω ↦ X ω ^ 6) μ := by
    simpa [X, μ] using branchingDiffusion_integrable_pow_six hY hκ x t
  have h6norm : Integrable (fun ω ↦ ‖X ω‖ ^ 6) μ := by
    have hX_nonneg : ∀ ω, 0 ≤ X ω := fun ω ↦ by positivity
    refine h6.congr ?_
    filter_upwards [Eventually.of_forall hX_nonneg] with ω hω
    simp [Real.norm_eq_abs, abs_of_nonneg hω]
  have hpnorm :
      Integrable (fun ω ↦ ‖X ω‖ ^ p) μ :=
    integrable_norm_pow_of_le hX_meas.aestronglyMeasurable hp h6norm
  -- Proof comment: since the coordinate process is nonnegative, absolute values disappear and the
  -- `L¹` control of the sixth power descends to all lower powers.
  have hX_nonneg : ∀ ω, 0 ≤ X ω := fun ω ↦ by positivity
  refine hpnorm.congr ?_
  filter_upwards [Eventually.of_forall hX_nonneg] with ω hω
  simp [X, Real.norm_eq_abs, abs_of_nonneg hω]

/-- Helper for Lemma 21.47: conditioning the future state event `{Y (s + t) ∈ A}` on the
present state `Y s` gives the kernel row `κ t (Y s ·)`. -/
private lemma markovRealization_futureEvent_condExp_eq_kernelRow
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {A : Set NNReal} (hA : MeasurableSet A) :
    (P x : Measure Ω)⟦Y (s + t) ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ =ᵐ[
        (P x : Measure Ω)]
      fun ω ↦ ((κ t) (Y s ω)).real A := by
  let μ : Measure Ω := (P x : Measure Ω)
  have hHist :
      μ⟦Y (s + t) ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
        fun ω ↦ ((κ t) (Y s ω)).real A := by
    -- Proof comment: this is exactly the event-level Markov field carried by the realization.
    simpa [μ, add_comm, add_left_comm, add_assoc] using hY.markov_property x hA s t
  have hNat :
      μ⟦Y (s + t) ⁻¹' A | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
        μ⟦Y (s + t) ⁻¹' A | MeasurableSpace.comap (Y s) inferInstance⟧ := by
    -- Proof comment: the derived natural Markov property identifies conditioning on the whole
    -- history with conditioning only on the present state.
    simpa [μ] using
      (hY.hasNaturalMarkovProperty x).2
        (s := s) (t := s + t) (le_add_of_nonneg_right t.2) (A := A) hA
  exact hNat.symm.trans hHist

/-- Helper for Lemma 21.47: the rectangle mass of the joint law of the present state `Y s` and
the future state `Y (s + t)` is the present-state integral of the kernel row `κ t`. -/
private lemma markovRealization_pairLaw_realProd_eq_stateIntegral
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {hs ht : Set NNReal} (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet ht) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → NNReal := Y s
    let next : Ω → NNReal := Y (s + t)
    (μ.map (fun ω ↦ (H ω, next ω))).real (hs ×ˢ ht) =
      ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → NNReal := Y s
  set next : Ω → NNReal := Y (s + t)
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state map is measurable by the realization interface.
    simpa [H] using hY.measurable_process s
  have hnext_meas : Measurable next := by
    -- Proof comment: the future-state map is another measurable time slice of the realization.
    simpa [next] using hY.measurable_process (s + t)
  have hpair_meas : Measurable (fun ω ↦ (H ω, next ω)) := by
    -- Proof comment: the pair map is measurable coordinatewise.
    fun_prop
  have hnext_pre_meas : MeasurableSet (next ⁻¹' ht) := hnext_meas ht_meas
  have hIndicatorInt :
      Integrable (Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: indicators of measurable events are integrable under the probability law.
    exact (integrable_const (1 : ℝ)).indicator hnext_pre_meas
  have hcond :
      μ⟦next ⁻¹' ht | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ ((κ t) (H ω)).real ht := by
    -- Proof comment: specialize the event-level kernel-row identity to the future event `ht`.
    simpa [μ, H, next] using
      markovRealization_futureEvent_condExp_eq_kernelRow hY x s t ht_meas
  calc
    (μ.map (fun ω ↦ (H ω, next ω))).real (hs ×ˢ ht)
        = ENNReal.toReal ((μ.map (fun ω ↦ (H ω, next ω))) (hs ×ˢ ht)) := by
            rfl
    _ = ENNReal.toReal (μ ((fun ω ↦ (H ω, next ω)) ⁻¹' (hs ×ˢ ht))) := by
          rw [Measure.map_apply hpair_meas (hs_meas.prod ht_meas)]
    _ = ENNReal.toReal (μ (H ⁻¹' hs ∩ next ⁻¹' ht)) := by
          have hpre :
              (fun ω ↦ (H ω, next ω)) ⁻¹' (hs ×ˢ ht) = H ⁻¹' hs ∩ next ⁻¹' ht := by
            ext ω
            simp [Set.preimage, H, next]
          rw [hpre]
    _ = ∫ ω in H ⁻¹' hs ∩ next ⁻¹' ht, (1 : ℝ) ∂μ := by
          symm
          exact MeasureTheory.setIntegral_one_eq_measureReal
    _ = ∫ ω in H ⁻¹' hs, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
          -- Proof comment: first restrict to the present-state event and then expose the future
          -- event by an indicator on the restricted measure.
          calc
            ∫ ω in H ⁻¹' hs ∩ next ⁻¹' ht, (1 : ℝ) ∂μ
                = (μ.restrict (H ⁻¹' hs)).real (next ⁻¹' ht) := by
                    rw [MeasureTheory.measureReal_restrict_apply (μ := μ) (s := H ⁻¹' hs)
                      (t := next ⁻¹' ht) hnext_pre_meas, Set.inter_comm,
                      ← MeasureTheory.setIntegral_one_eq_measureReal]
            _ = ∫ ω, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ.restrict (H ⁻¹' hs) := by
                  symm
                  simpa using
                    (MeasureTheory.integral_indicator_one
                      (μ := μ.restrict (H ⁻¹' hs)) hnext_pre_meas)
            _ = ∫ ω in H ⁻¹' hs, Set.indicator (next ⁻¹' ht) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  rfl
    _ = ∫ ω in H ⁻¹' hs,
          (μ⟦next ⁻¹' ht | MeasurableSpace.comap H inferInstance⟧) ω ∂μ := by
          -- Proof comment: conditional expectation preserves the integral over any
          -- `σ(Y s)`-measurable event.
          symm
          exact
            MeasureTheory.setIntegral_condExp hH_meas.comap_le hIndicatorInt
              ⟨hs, hs_meas, rfl⟩
    _ = ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
          -- Proof comment: replace the conditional probability by the kernel row on the
          -- present-state sigma-algebra.
          refine MeasureTheory.setIntegral_congr_ae (hH_meas hs_meas) ?_
          filter_upwards [hcond] with ω hω hωhs
          exact hω

/-- Helper for Lemma 21.47: the rectangle mass of the composition product
`(P x).map (Y s) ⊗ₘ κ t` matches the same present-state integral as the joint law. -/
private lemma markovRealization_compProd_realProd_eq_stateIntegral
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {hs ht : Set NNReal} (hs_meas : MeasurableSet hs) (ht_meas : MeasurableSet ht) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → NNReal := Y s
    (μ.map H ⊗ₘ κ t).real (hs ×ˢ ht) =
      ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
  set μ : Measure Ω := (P x : Measure Ω)
  set H : Ω → NNReal := Y s
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each kernel row is a time-`t` marginal of the realized process, hence a
    -- probability measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state map is measurable by the realization interface.
    simpa [H] using hY.measurable_process s
  have hrow_meas : Measurable fun y ↦ ((κ t) y).real ht := by
    -- Proof comment: kernel-row masses on a measurable target set vary measurably with the
    -- present state.
    exact ((κ t).measurable_coe ht_meas).ennreal_toReal
  calc
    (μ.map H ⊗ₘ κ t).real (hs ×ˢ ht)
        = ∫ z in hs ×ˢ ht, (1 : ℝ) ∂(μ.map H ⊗ₘ κ t) := by
            symm
            exact MeasureTheory.setIntegral_one_eq_measureReal
    _ = ∫ y in hs, ∫ z in ht, (1 : ℝ) ∂(κ t y) ∂(μ.map H) := by
          have hone :
              Integrable (fun _ : NNReal × NNReal ↦ (1 : ℝ)) (μ.map H ⊗ₘ κ t) := by
            simp
          exact MeasureTheory.Measure.setIntegral_compProd hs_meas ht_meas hone.integrableOn
    _ = ∫ y in hs, ((κ t) y).real ht ∂(μ.map H) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simp
    _ = ∫ ω in H ⁻¹' hs, ((κ t) (H ω)).real ht ∂μ := by
          exact
            MeasureTheory.setIntegral_map hs_meas hrow_meas.aestronglyMeasurable
              hH_meas.aemeasurable

/-- Helper for Lemma 21.47: the joint law of `(Y s, Y (s + t))` factors as the law of `Y s`
followed by the kernel row `κ t`. -/
private lemma markovRealization_pairLaw_eq_map_present_compProd_kernelRow
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal) :
    let μ : Measure Ω := (P x : Measure Ω)
    let H : Ω → NNReal := Y s
    let next : Ω → NNReal := Y (s + t)
    μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ κ t := by
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: each candidate row is a realized one-time marginal, so it is a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  -- Proof comment: compare the two candidate measures on measurable rectangles and then invoke
  -- product-measure extensionality.
  refine Measure.ext_prod ?_
  intro hs ht hs_meas ht_meas
  have hreal :
      ((P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω))).real (hs ×ˢ ht) =
        ((((P x : Measure Ω).map (Y s)) ⊗ₘ κ t).real (hs ×ˢ ht)) := by
    calc
      ((P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω))).real (hs ×ˢ ht)
          = ∫ ω in (Y s) ⁻¹' hs, ((κ t) (Y s ω)).real ht ∂(P x : Measure Ω) := by
              simpa using
                (markovRealization_pairLaw_realProd_eq_stateIntegral hY x s t hs_meas ht_meas)
      _ = ((((P x : Measure Ω).map (Y s)) ⊗ₘ κ t).real (hs ×ˢ ht)) := by
            symm
            simpa using
              (markovRealization_compProd_realProd_eq_stateIntegral hY x s t hs_meas ht_meas)
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)))
      (ν := ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t)
      (s := hs ×ˢ ht) (t := hs ×ˢ ht)
      (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp hreal

/-- Helper for Lemma 21.47: the regular conditional law of the future state `Y (s + t)` given the
present state `Y s` is the kernel row `κ t` evaluated at that present state. -/
private lemma markovRealization_futureCondDistrib_eq_kernelRow
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal) :
    condDistrib (Y (s + t)) (Y s) (P x : Measure Ω) =ᵐ[(P x : Measure Ω).map (Y s)] κ t := by
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: every candidate row `κ t y` is a realized marginal law, hence Markov.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hpair :
      (P x : Measure Ω).map (fun ω ↦ (Y s ω, Y (s + t) ω)) =
        ((P x : Measure Ω).map (Y s)) ⊗ₘ κ t := by
    -- Proof comment: the pair-law factorization is the joint-law owner needed by `condDistrib`
    -- uniqueness.
    simpa using markovRealization_pairLaw_eq_map_present_compProd_kernelRow hY x s t
  -- Proof comment: once the pair law factors, `condDistrib` is the unique conditional kernel of
  -- the future state given the present state.
  simpa using
    (ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := (P x : Measure Ω)) (X := Y s) (Y := Y (s + t))
      (hY.measurable_process s) (hY.measurable_process (s + t)) hpair)

/-- Helper for Lemma 21.47: the future coordinate has conditional expectation equal to the present
coordinate when conditioning only on the present-state sigma-algebra. -/
private lemma branchingDiffusion_condExp_coordinate_ae_eq_presentState
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t : NNReal) :
    (P x : Measure Ω)[fun ω ↦ (Y (s + t) ω : ℝ) |
        MeasurableSpace.comap (Y s) inferInstance] =ᵐ[(P x : Measure Ω)]
      fun ω ↦ (Y s ω : ℝ) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → NNReal := Y s
  let next : Ω → NNReal := Y (s + t)
  have hH_meas : Measurable H := by
    -- Proof comment: the present-state map is measurable by the realization interface.
    simpa [H] using hY.measurable_process s
  have hcondExp :
      μ[fun ω ↦ (next ω : ℝ) | MeasurableSpace.comap H inferInstance] =ᵐ[μ]
        fun ω ↦ ∫ z, (z : ℝ) ∂condDistrib next H μ (H ω) := by
    -- Proof comment: identify the present-state conditional expectation as the integral of the
    -- identity observable against the regular conditional law of the future state.
    exact
      ProbabilityTheory.condExp_ae_eq_integral_condDistrib
        (μ := μ) (X := H) (Y := next) hH_meas
        (hY.measurable_process (s + t)).aemeasurable
        (continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).stronglyMeasurable
        (by simpa [μ, next] using branchingDiffusion_integrable hY hκ x (s + t))
  have hkernelComp :
      (fun ω ↦ condDistrib next H μ (H ω)) =ᵐ[μ] fun ω ↦ κ t (H ω) := by
    -- Proof comment: pull the identified conditional law back from state space to sample space
    -- through the present-state map.
    exact
      MeasureTheory.ae_eq_comp hH_meas.aemeasurable
        (markovRealization_futureCondDistrib_eq_kernelRow hY x s t)
  have hrewrite :
      (fun ω ↦ ∫ z, (z : ℝ) ∂condDistrib next H μ (H ω)) =ᵐ[μ]
        fun ω ↦ (H ω : ℝ) := by
    -- Proof comment: after replacing the conditional law by `κ t`, the kernel preserves the
    -- coordinate observable in expectation.
    filter_upwards [hkernelComp] with ω hω
    rw [hω]
    exact branchingDiffusionKernelIntegral_id hY hκ t (H ω)
  exact hcondExp.trans hrewrite

/-- Helper for Lemma 21.47: evaluating a Markov-kernel composition against a restricted
pushforward is the same as integrating the kernel row over the restricted source event. -/
private lemma kernelComp_restrictMap_real_eq_setIntegral
    {α : Type*} [MeasurableSpace α]
    (κ : Kernel α NNReal) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → α} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set NNReal} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure α := (μ.restrict B).map Y
  have hkernel_int :
      Integrable (fun y : α ↦ (κ y).real A) ν := by
    -- Proof comment: every kernel row is a probability measure, so its mass on `A` is integrable.
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : α ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    -- Proof comment: pull the kernel-row integral back through the restricted present-state map.
    change ∫ y, (κ y).real A ∂((μ.restrict B).map Y) = ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Lemma 21.47: on every history event at time `s`, the restricted future law is the
composition of the restricted present-state law with the kernel row `κ t`. -/
private lemma markovRealization_restrictMap_eq_kernelComp_of_history
    (hY : IsMarkovProcessRealization κ P Y) (x s t : NNReal)
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace Y s] B) :
    (((P x : Measure Ω).restrict B).map (Y (s + t))) =
      (κ t) ∘ₘ (((P x : Measure Ω).restrict B).map (Y s)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: every row `κ t y` is a realized one-time marginal, hence a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hgenerated_le : generatedFiltrationSpace Y s ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: each history generator is ambient measurable because every time slice of the
    -- realization is measurable.
    refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
    exact (hY.measurable_process r).comap_le
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  refine Measure.ext fun A hA ↦ ?_
  let futureEvent : Set Ω := Y (s + t) ⁻¹' A
  have hfuture_meas : MeasurableSet futureEvent := by
    simpa [futureEvent] using (hY.measurable_process (s + t)) hA
  have hleft_real :
      (((μ.restrict B).map (Y (s + t))).real A) =
        ∫ ω in B, ((κ t) (Y s ω)).real A ∂μ := by
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace Y s⟧ =ᵐ[μ]
          fun ω ↦ ((κ t) (Y s ω)).real A := by
      -- Proof comment: this is the event-level Markov field at the time pair `(s, t)`.
      simpa [μ, futureEvent, add_comm, add_left_comm, add_assoc] using hY.markov_property x hA s t
    have hmass :
        μ.real (B ∩ futureEvent) = ∫ ω in B, ((κ t) (Y s ω)).real A ∂μ := by
      calc
        μ.real (B ∩ futureEvent)
            = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace Y s⟧) ω ∂μ := by
                rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                  ← MeasureTheory.integral_indicator hB_ambient]
                simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                  Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                  (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                    (hB_ambient.inter hfuture_meas)).symm
        _ = ∫ ω in B, ((κ t) (Y s ω)).real A ∂μ := by
              exact MeasureTheory.integral_congr_ae hmarkov.restrict
    calc
      (((μ.restrict B).map (Y (s + t))).real A) = (μ.restrict B).real futureEvent := by
        simpa [futureEvent] using
          MeasureTheory.map_measureReal_apply
            (μ := μ.restrict B) (f := Y (s + t)) (hY.measurable_process (s + t)) hA
      _ = μ.real (futureEvent ∩ B) := by
        simpa [futureEvent] using
          (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B) (t := futureEvent)
            hfuture_meas)
      _ = ∫ ω in B, ((κ t) (Y s ω)).real A ∂μ := by
        simpa [futureEvent, Set.inter_comm] using hmass
  have hright_real :
      (((κ t) ∘ₘ (((μ.restrict B).map (Y s)))).real A) =
        ∫ ω in B, ((κ t) (Y s ω)).real A ∂μ := by
    exact kernelComp_restrictMap_real_eq_setIntegral
      (κ := κ t) (μ := μ) (hY := hY.measurable_process s) (_hB := hB_ambient) (hA := hA)
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict B).map (Y (s + t))))
      (ν := (κ t) ∘ₘ (((μ.restrict B).map (Y s))))
      (s := A) (t := A)).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Lemma 21.47: on every generated-history event at time `s`, the future coordinate
and the present coordinate have the same restricted integral. -/
private lemma branchingDiffusion_historySetIntegral_futureCoordinate_eq_present
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t : NNReal) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace Y s] B) :
    ∫ ω in B, (Y (s + t) ω : ℝ) ∂(P x : Measure Ω) =
      ∫ ω in B, (Y s ω : ℝ) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let H : Ω → NNReal := Y s
  let next : Ω → NNReal := Y (s + t)
  let ν : Measure NNReal := (μ.restrict B).map H
  letI : IsMarkovKernel (κ t) := by
    -- Proof comment: every row `κ t y` is a realized one-time marginal, hence a probability
    -- measure.
    refine ⟨fun y ↦ ?_⟩
    rw [← hY.transition_eq y t]
    exact
      Measure.isProbabilityMeasure_map
        (μ := (P y : Measure Ω)) (f := Y t) (hY.measurable_process t).aemeasurable
  have hgenerated_le : generatedFiltrationSpace Y s ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: the history sigma-algebra is ambient because every coordinate of the
    -- realization is ambient measurable.
    refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
    exact (hY.measurable_process r).comap_le
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  have hH_meas : Measurable H := by
    simpa [H] using hY.measurable_process s
  have hnext_meas : Measurable next := by
    simpa [next] using hY.measurable_process (s + t)
  have hnext_int : Integrable (fun ω ↦ (next ω : ℝ)) μ := by
    simpa [μ, next] using branchingDiffusion_integrable hY hκ x (s + t)
  have hnext_map_int : Integrable (fun z : NNReal ↦ (z : ℝ)) ((μ.restrict B).map next) := by
    -- Proof comment: restricting the future coordinate keeps integrability, and the pushforward
    -- turns that into integrability of the identity on the restricted future law.
    refine
      (MeasureTheory.integrable_map_measure
        (μ := μ.restrict B) (f := next) (g := fun z : NNReal ↦ (z : ℝ))
        (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).aestronglyMeasurable
        hnext_meas.aemeasurable).2 ?_
    simpa [next] using hnext_int.restrict
  have hrestrict :
      ((μ.restrict B).map next) = (κ t) ∘ₘ ν := by
    -- Proof comment: the event-level Markov property identifies the whole restricted future law.
    simpa [μ, H, next, ν] using
      markovRealization_restrictMap_eq_kernelComp_of_history hY x s t hB
  have hcomp_int : Integrable (fun z : NNReal ↦ (z : ℝ)) ((κ t) ∘ₘ ν) := by
    simpa [hrestrict] using hnext_map_int
  have hprod_int : Integrable (fun p : NNReal × NNReal ↦ (p.2 : ℝ)) (ν ⊗ₘ κ t) := by
    -- Proof comment: integrability for the composed measure is equivalent to integrability of the
    -- second-coordinate observable on the composition-product measure.
    simpa using
      (MeasureTheory.Measure.integrable_compProd_snd_iff
        (μ := ν) (κ := κ t)
        (f := fun z : NNReal ↦ (z : ℝ))
        (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).aestronglyMeasurable).2
        hcomp_int
  calc
    ∫ ω in B, (next ω : ℝ) ∂μ = ∫ z, (z : ℝ) ∂((μ.restrict B).map next) := by
        symm
        simpa using
          (MeasureTheory.integral_map hnext_meas.aemeasurable
            (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).aestronglyMeasurable)
    _ = ∫ z, (z : ℝ) ∂((κ t) ∘ₘ ν) := by rw [hrestrict]
    _ = ∫ p : NNReal × NNReal, (p.2 : ℝ) ∂(ν ⊗ₘ κ t) := by
          rw [← Measure.snd_compProd ν (κ t)]
          change ∫ z, (z : ℝ) ∂(Measure.map Prod.snd (ν ⊗ₘ κ t)) = _
          simpa using
            (MeasureTheory.integral_map measurable_snd.aemeasurable
              (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).aestronglyMeasurable)
    _ = ∫ y, ∫ z, (z : ℝ) ∂κ t y ∂ν := by
          simpa using (MeasureTheory.Measure.integral_compProd (μ := ν) (κ := κ t) hprod_int)
    _ = ∫ y, (y : ℝ) ∂ν := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall fun y ↦ branchingDiffusionKernelIntegral_id hY hκ t y
    _ = ∫ ω in B, (H ω : ℝ) ∂μ := by
          simpa [ν] using
            (MeasureTheory.integral_map hH_meas.aemeasurable
              (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).aestronglyMeasurable)

/-- Helper for Lemma 21.47: the generated-history conditional expectation should agree with the
present-state conditional expectation because the event-level natural Markov property identifies the
two conditional laws. -/
private lemma branchingDiffusion_condExp_coordinate_ae_eq_present
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x s t : NNReal) :
    (P x : Measure Ω)[fun ω ↦ (Y (s + t) ω : ℝ) | generatedFiltrationSpace Y s] =ᵐ[
        (P x : Measure Ω)]
      fun ω ↦ (Y s ω : ℝ) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let next : Ω → ℝ := fun ω ↦ (Y (s + t) ω : ℝ)
  let present : Ω → ℝ := fun ω ↦ (Y s ω : ℝ)
  have hgenerated_le : generatedFiltrationSpace Y s ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: the generated history is ambient because every realized coordinate is
    -- measurable.
    refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
    exact (hY.measurable_process r).comap_le
  have hnext_int : Integrable next μ := by
    simpa [μ, next] using branchingDiffusion_integrable hY hκ x (s + t)
  have hpresent_int : Integrable present μ := by
    simpa [μ, present] using branchingDiffusion_integrable hY hκ x s
  have hpresentState_meas :
      Measurable[generatedFiltrationSpace Y s] (Y s) := by
    -- Proof comment: the present `NNReal` coordinate is one of the generators of the history at
    -- time `s`.
    refine Measurable.of_comap_le ?_
    rw [generatedFiltrationSpace]
    exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl
  have hpresent_meas :
      Measurable[generatedFiltrationSpace Y s] present := by
    -- Proof comment: composing the present `NNReal` coordinate with the continuous coercion
    -- `NNReal → ℝ` preserves history measurability.
    change Measurable[generatedFiltrationSpace Y s] (fun ω ↦ ((Y s ω : NNReal) : ℝ))
    exact
      (continuous_subtype_val : Continuous fun z : NNReal ↦ (z : ℝ)).measurable.comp
        hpresentState_meas
  -- Route correction: instead of chasing a history-level `condDistrib`, identify restricted
  -- future laws on every history event and then close the conditional expectation by set-integral
  -- uniqueness.
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hnext_int
      (fun B _ _ ↦ hpresent_int.integrableOn)
      (fun B hB _ ↦ ?_) hpresent_meas.aestronglyMeasurable).symm
  -- Proof comment: the restricted-law identity from
  -- `branchingDiffusion_historySetIntegral_futureCoordinate_eq_present` supplies the required
  -- set-integral equality on every history event.
  simpa [μ, next, present] using
    (branchingDiffusion_historySetIntegral_futureCoordinate_eq_present hY hκ x s t hB).symm

/-- Lemma 21.47: claim (8) states that for a realization of the branching-diffusion semigroup from
Lemma 21.46, the coordinate process `Y` is a martingale with respect to its natural filtration
under each initial law `P x`. -/
theorem branchingDiffusion_martingale
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    (x : NNReal) :
    Martingale (fun t ω ↦ (Y t ω : ℝ))
      (Filtration.natural Y
        (fun t ↦ ((hY.hasNaturalMarkovProperty x).1 t).stronglyMeasurable))
      (P x : Measure Ω) := by
  let hNat := hY.hasNaturalMarkovProperty x
  let hStrongY :
      StronglyAdapted
        (Filtration.natural Y (fun t ↦ (hNat.1 t).stronglyMeasurable))
        Y :=
    Filtration.stronglyAdapted_natural (u := Y) (hum := fun t ↦ (hNat.1 t).stronglyMeasurable)
  have hStrongReal :
      StronglyAdapted
        (Filtration.natural Y (fun t ↦ (hNat.1 t).stronglyMeasurable))
        (fun t ω ↦ (Y t ω : ℝ)) := by
    intro t
    -- Proof comment: composing the natural-filtration measurable coordinate with the continuous
    -- coercion `NNReal → ℝ` keeps strong measurability.
    exact
      StronglyMeasurable.comp_measurable
        ((continuous_subtype_val : Continuous fun y : NNReal ↦ (y : ℝ)).stronglyMeasurable)
        (hStrongY t).measurable
  refine ⟨hStrongReal, ?_⟩
  intro s t hst
  obtain ⟨u, hu⟩ := exists_add_of_le hst
  have hgen :
      (P x : Measure Ω)[fun ω ↦ (Y t ω : ℝ) | generatedFiltrationSpace Y s] =ᵐ[
          (P x : Measure Ω)]
        fun ω ↦ (Y s ω : ℝ) := by
    -- Proof comment: rewrite `t` as `s + u` and apply the generated-history conditional
    -- expectation formula.
    simpa [hu, add_comm, add_left_comm, add_assoc] using
      branchingDiffusion_condExp_coordinate_ae_eq_present hY hκ x s u
  -- Proof comment: the source-facing generated filtration agrees with the natural filtration for
  -- this measurable process, so the generated-history identity is exactly the martingale clause.
  simpa [hNat, generatedFiltration_eq_natural Y
    (fun t ↦ (hNat.1 t).stronglyMeasurable)] using hgen

-- Proof sketch: use the first-moment identity to rewrite the second central moment around the
-- mean `x`, expand `centralMoment`, and simplify with the explicit raw second moment formula.
/-- Lemma 21.47 (9): the second centered moment of the branching diffusion is `2xt`. -/
theorem branchingDiffusion_second_centralMoment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 2 (P x : Measure Ω) =
      2 * (x : ℝ) * (t : ℝ) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = x := by
    -- Proof comment: the center in `centralMoment` is the first raw moment, and that mean is
    -- exactly `x`.
    simpa [X, μ, moment_one] using
      (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have hX : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ x t
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 2) (by norm_num)
  have h1 : moment X 1 μ = x := by
    simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have h2 : moment X 2 μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [X, μ] using (branchingDiffusion_second_moment hY hκ (x := x) (t := t))
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  rw [ProbabilityTheory.centralMoment, hmean]
  change ∫ ω, (X ω - x) ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ)
  rw [show (fun ω ↦ (X ω - x) ^ 2) =
      fun ω ↦ X ω ^ 2 - (2 * (x : ℝ)) * X ω + (x : ℝ) ^ 2 by
    funext ω
    ring]
  -- Proof comment: expand the square, integrate termwise, and substitute the first two raw
  -- moments.
  have hA : Integrable (fun ω ↦ X ω ^ 2 - (2 * (x : ℝ)) * X ω) μ := by
    exact hX2.sub (hX.const_mul _)
  rw [integral_add hA (integrable_const _)]
  rw [integral_sub hX2 (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the third centered moment in terms of the raw moments, then substitute the
-- first and third moment formulas and simplify.
/-- Lemma 21.47 (10): the third centered moment of the branching diffusion is `6xt²`. -/
theorem branchingDiffusion_third_centralMoment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 3 (P x : Measure Ω) =
      6 * (x : ℝ) * (t : ℝ) ^ 2 := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = x := by
    -- Proof comment: rewrite the center in the cubic moment by the already-known first moment.
    simpa [X, μ, moment_one] using
      (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have hX : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ x t
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 3) (by norm_num)
  have h1 : moment X 1 μ = x := by
    simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have h2 : moment X 2 μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [X, μ] using (branchingDiffusion_second_moment hY hκ (x := x) (t := t))
  have h3 :
      moment X 3 μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [X, μ] using (branchingDiffusion_third_moment hY hκ (x := x) (t := t))
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  rw [ProbabilityTheory.centralMoment, hmean]
  change ∫ ω, (X ω - x) ^ 3 ∂μ = 6 * (x : ℝ) * (t : ℝ) ^ 2
  rw [show (fun ω ↦ (X ω - x) ^ 3) =
      fun ω ↦
        (X ω ^ 3 - (3 * (x : ℝ)) * X ω ^ 2) +
          ((3 * (x : ℝ) ^ 2) * X ω - (x : ℝ) ^ 3) by
    funext ω
    ring]
  -- Proof comment: the cubic expansion leaves only raw moments of orders one through three.
  have hA : Integrable (fun ω ↦ X ω ^ 3 - (3 * (x : ℝ)) * X ω ^ 2) μ := by
    exact hX3.sub (hX2.const_mul _)
  have hB : Integrable (fun ω ↦ (3 * (x : ℝ) ^ 2) * X ω - (x : ℝ) ^ 3) μ := by
    exact (hX.const_mul _).sub (integrable_const _)
  rw [integral_add hA hB]
  rw [integral_sub hX3 (hX2.const_mul _)]
  rw [integral_sub (hX.const_mul _) (integrable_const _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the fourth centered moment via the binomial formula, substitute the raw
-- moment identities, and collect coefficients.
/-- Lemma 21.47 (11): the fourth centered moment of the branching diffusion is
`24xt³ + 12x²t²`. -/
theorem branchingDiffusion_fourth_centralMoment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 4 (P x : Measure Ω) =
      24 * (x : ℝ) * (t : ℝ) ^ 3 + 12 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = x := by
    -- Proof comment: fix the center at `x` before expanding the quartic.
    simpa [X, μ, moment_one] using
      (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have hX : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ x t
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 4) (by norm_num)
  have h1 : moment X 1 μ = x := by
    simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have h2 : moment X 2 μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [X, μ] using (branchingDiffusion_second_moment hY hκ (x := x) (t := t))
  have h3 :
      moment X 3 μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [X, μ] using (branchingDiffusion_third_moment hY hκ (x := x) (t := t))
  have h4 :
      moment X 4 μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [X, μ] using (branchingDiffusion_fourth_moment hY hκ (x := x) (t := t))
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - x) ^ 4 ∂μ = 24 * (x : ℝ) * (t : ℝ) ^ 3 + 12 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2
  rw [show (fun ω ↦ (X ω - x) ^ 4) =
      fun ω ↦
        ((X ω ^ 4 - (4 * (x : ℝ)) * X ω ^ 3) +
            ((6 * (x : ℝ) ^ 2) * X ω ^ 2 - (4 * (x : ℝ) ^ 3) * X ω)) +
          (x : ℝ) ^ 4 by
    funext ω
    ring]
  -- Proof comment: integrate the quartic expansion termwise, then substitute the closed raw
  -- moment formulas.
  have hA : Integrable (fun ω ↦ X ω ^ 4 - (4 * (x : ℝ)) * X ω ^ 3) μ := by
    exact hX4.sub (hX3.const_mul _)
  have hB : Integrable (fun ω ↦ (6 * (x : ℝ) ^ 2) * X ω ^ 2 - (4 * (x : ℝ) ^ 3) * X ω) μ := by
    exact (hX2.const_mul _).sub (hX.const_mul _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 4 - (4 * (x : ℝ)) * X ω ^ 3) +
            ((6 * (x : ℝ) ^ 2) * X ω ^ 2 - (4 * (x : ℝ) ^ 3) * X ω)) μ := by
    exact hA.add hB
  rw [integral_add hAB (integrable_const _)]
  rw [integral_add hA hB]
  rw [integral_sub hX4 (hX3.const_mul _)]
  rw [integral_sub (hX2.const_mul _) (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: express the fifth centered moment in terms of raw moments, then substitute the
-- formulas up to order five and simplify.
/-- Lemma 21.47 (12): the fifth centered moment of the branching diffusion is
`120xt⁴ + 120x²t³`. -/
theorem branchingDiffusion_fifth_centralMoment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 5 (P x : Measure Ω) =
      120 * (x : ℝ) * (t : ℝ) ^ 4 + 120 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = x := by
    -- Proof comment: center the quintic expansion at the deterministic mean `x`.
    simpa [X, μ, moment_one] using
      (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have hX : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ x t
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 4) (by norm_num)
  have hX5 : Integrable (fun ω ↦ X ω ^ 5) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 5) (by norm_num)
  have h1 : moment X 1 μ = x := by
    simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have h2 : moment X 2 μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [X, μ] using (branchingDiffusion_second_moment hY hκ (x := x) (t := t))
  have h3 :
      moment X 3 μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [X, μ] using (branchingDiffusion_third_moment hY hκ (x := x) (t := t))
  have h4 :
      moment X 4 μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [X, μ] using (branchingDiffusion_fourth_moment hY hκ (x := x) (t := t))
  have h5 :
      moment X 5 μ =
        120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
          120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
          (x : ℝ) ^ 5 := by
    simpa [X, μ] using (branchingDiffusion_fifth_moment hY hκ (x := x) (t := t))
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  have hInt5 :
      ∫ ω, X ω ^ 5 ∂μ =
        120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
          120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
          (x : ℝ) ^ 5 := by
    simpa [moment_def] using h5
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - x) ^ 5 ∂μ = 120 * (x : ℝ) * (t : ℝ) ^ 4 + 120 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3
  rw [show (fun ω ↦ (X ω - x) ^ 5) =
      fun ω ↦
        ((X ω ^ 5 - (5 * (x : ℝ)) * X ω ^ 4) +
            ((10 * (x : ℝ) ^ 2) * X ω ^ 3 - (10 * (x : ℝ) ^ 3) * X ω ^ 2)) +
          ((5 * (x : ℝ) ^ 4) * X ω - (x : ℝ) ^ 5) by
    funext ω
    ring]
  -- Proof comment: the quintic centered moment is a linear combination of raw moments of orders
  -- one through five.
  have hA : Integrable (fun ω ↦ X ω ^ 5 - (5 * (x : ℝ)) * X ω ^ 4) μ := by
    exact hX5.sub (hX4.const_mul _)
  have hB :
      Integrable (fun ω ↦ (10 * (x : ℝ) ^ 2) * X ω ^ 3 - (10 * (x : ℝ) ^ 3) * X ω ^ 2) μ := by
    exact (hX3.const_mul _).sub (hX2.const_mul _)
  have hC : Integrable (fun ω ↦ (5 * (x : ℝ) ^ 4) * X ω - (x : ℝ) ^ 5) μ := by
    exact (hX.const_mul _).sub (integrable_const _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 5 - (5 * (x : ℝ)) * X ω ^ 4) +
            ((10 * (x : ℝ) ^ 2) * X ω ^ 3 - (10 * (x : ℝ) ^ 3) * X ω ^ 2)) μ := by
    exact hA.add hB
  rw [integral_add hAB hC]
  rw [integral_add hA hB]
  rw [integral_sub hX5 (hX4.const_mul _)]
  rw [integral_sub (hX3.const_mul _) (hX2.const_mul _)]
  rw [integral_sub (hX.const_mul _) (integrable_const _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt5, hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

-- Proof sketch: expand the sixth centered moment, substitute the raw moments through order six,
-- and collect the remaining polynomial terms.
/-- Lemma 21.47 (13): the sixth centered moment of the branching diffusion is
`720xt⁵ + 1080x²t⁴ + 120x³t³`. -/
theorem branchingDiffusion_sixth_centralMoment
    (hY : IsMarkovProcessRealization κ P Y) (hκ : HasBranchingDiffusionLaplaceTransform κ)
    {x t : NNReal} :
    centralMoment (fun ω ↦ (Y t ω : ℝ)) 6 (P x : Measure Ω) =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1080 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 := by
  let μ : Measure Ω := (P x : Measure Ω)
  let X : Ω → ℝ := fun ω ↦ (Y t ω : ℝ)
  have hmean : ∫ ω, X ω ∂μ = x := by
    -- Proof comment: replace the centralizing expectation by `x` before expanding the sixth
    -- power.
    simpa [X, μ, moment_one] using
      (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have hX : Integrable X μ := by
    simpa [X, μ] using branchingDiffusion_integrable hY hκ x t
  have hX2 : Integrable (fun ω ↦ X ω ^ 2) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 2) (by norm_num)
  have hX3 : Integrable (fun ω ↦ X ω ^ 3) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 3) (by norm_num)
  have hX4 : Integrable (fun ω ↦ X ω ^ 4) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 4) (by norm_num)
  have hX5 : Integrable (fun ω ↦ X ω ^ 5) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 5) (by norm_num)
  have hX6 : Integrable (fun ω ↦ X ω ^ 6) μ := by
    simpa [X, μ] using
      branchingDiffusion_integrable_pow_le_six hY hκ x t (p := 6) (by norm_num)
  have h1 : moment X 1 μ = x := by
    simpa [X, μ] using (branchingDiffusion_first_moment hY hκ (x := x) (t := t))
  have h2 : moment X 2 μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [X, μ] using (branchingDiffusion_second_moment hY hκ (x := x) (t := t))
  have h3 :
      moment X 3 μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [X, μ] using (branchingDiffusion_third_moment hY hκ (x := x) (t := t))
  have h4 :
      moment X 4 μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [X, μ] using (branchingDiffusion_fourth_moment hY hκ (x := x) (t := t))
  have h5 :
      moment X 5 μ =
        120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
          120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
          (x : ℝ) ^ 5 := by
    simpa [X, μ] using (branchingDiffusion_fifth_moment hY hκ (x := x) (t := t))
  have h6 :
      moment X 6 μ =
        720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
          1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
          30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := by
    simpa [X, μ] using (branchingDiffusion_sixth_moment hY hκ (x := x) (t := t))
  have hInt2 : ∫ ω, X ω ^ 2 ∂μ = 2 * (x : ℝ) * (t : ℝ) + (x : ℝ) ^ 2 := by
    simpa [moment_def] using h2
  have hInt3 :
      ∫ ω, X ω ^ 3 ∂μ =
        6 * (x : ℝ) * (t : ℝ) ^ 2 + 6 * (x : ℝ) ^ 2 * (t : ℝ) + (x : ℝ) ^ 3 := by
    simpa [moment_def] using h3
  have hInt4 :
      ∫ ω, X ω ^ 4 ∂μ =
        24 * (x : ℝ) * (t : ℝ) ^ 3 + 36 * (x : ℝ) ^ 2 * (t : ℝ) ^ 2 +
          12 * (x : ℝ) ^ 3 * (t : ℝ) + (x : ℝ) ^ 4 := by
    simpa [moment_def] using h4
  have hInt5 :
      ∫ ω, X ω ^ 5 ∂μ =
        120 * (x : ℝ) * (t : ℝ) ^ 4 + 240 * (x : ℝ) ^ 2 * (t : ℝ) ^ 3 +
          120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 2 + 20 * (x : ℝ) ^ 4 * (t : ℝ) +
          (x : ℝ) ^ 5 := by
    simpa [moment_def] using h5
  have hInt6 :
      ∫ ω, X ω ^ 6 ∂μ =
        720 * (x : ℝ) * (t : ℝ) ^ 5 + 1800 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
          1200 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3 + 300 * (x : ℝ) ^ 4 * (t : ℝ) ^ 2 +
          30 * (x : ℝ) ^ 5 * (t : ℝ) + (x : ℝ) ^ 6 := by
    simpa [moment_def] using h6
  rw [ProbabilityTheory.centralMoment, hmean]
  change
    ∫ ω, (X ω - x) ^ 6 ∂μ =
      720 * (x : ℝ) * (t : ℝ) ^ 5 + 1080 * (x : ℝ) ^ 2 * (t : ℝ) ^ 4 +
        120 * (x : ℝ) ^ 3 * (t : ℝ) ^ 3
  rw [show (fun ω ↦ (X ω - x) ^ 6) =
      fun ω ↦
        ((X ω ^ 6 - (6 * (x : ℝ)) * X ω ^ 5) +
            ((15 * (x : ℝ) ^ 2) * X ω ^ 4 - (20 * (x : ℝ) ^ 3) * X ω ^ 3)) +
          (((15 * (x : ℝ) ^ 4) * X ω ^ 2 - (6 * (x : ℝ) ^ 5) * X ω) + (x : ℝ) ^ 6) by
    funext ω
    ring]
  -- Proof comment: the sextic centered moment collapses to the first six raw moments after the
  -- binomial expansion.
  have hA : Integrable (fun ω ↦ X ω ^ 6 - (6 * (x : ℝ)) * X ω ^ 5) μ := by
    exact hX6.sub (hX5.const_mul _)
  have hB :
      Integrable (fun ω ↦ (15 * (x : ℝ) ^ 2) * X ω ^ 4 - (20 * (x : ℝ) ^ 3) * X ω ^ 3) μ := by
    exact (hX4.const_mul _).sub (hX3.const_mul _)
  have hC : Integrable (fun ω ↦ (15 * (x : ℝ) ^ 4) * X ω ^ 2 - (6 * (x : ℝ) ^ 5) * X ω) μ := by
    exact (hX2.const_mul _).sub (hX.const_mul _)
  have hAB :
      Integrable
        (fun ω ↦
          (X ω ^ 6 - (6 * (x : ℝ)) * X ω ^ 5) +
            ((15 * (x : ℝ) ^ 2) * X ω ^ 4 - (20 * (x : ℝ) ^ 3) * X ω ^ 3)) μ := by
    exact hA.add hB
  have hCD :
      Integrable
        (fun ω ↦
          ((15 * (x : ℝ) ^ 4) * X ω ^ 2 - (6 * (x : ℝ) ^ 5) * X ω) + (x : ℝ) ^ 6) μ := by
    exact hC.add (integrable_const _)
  rw [integral_add hAB hCD]
  rw [integral_add hA hB]
  rw [integral_add hC (integrable_const _)]
  rw [integral_sub hX6 (hX5.const_mul _)]
  rw [integral_sub (hX4.const_mul _) (hX3.const_mul _)]
  rw [integral_sub (hX2.const_mul _) (hX.const_mul _)]
  simp_rw [integral_const_mul]
  rw [integral_const]
  rw [hInt6, hInt5, hInt4, hInt3, hInt2, hmean]
  simp [μ]
  ring

end BranchingDiffusion

end ProbabilityTheory
