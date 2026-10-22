/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Theorem_23_17

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped ENNReal Topology Pointwise

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E]

/-- Helper for Theorem 23.19: the positive-parameter filter is nontrivial because it is the
pullback of the punctured right-neighborhood filter at `0`. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  -- Proof comment: reindex the nontrivial right-neighborhood filter at `0` along the coercion
  -- `PositiveParameter → ℝ`.
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- The tilted rate function from (23.21), namely the nonnegative extended-real gap between the
global supremum of `φ - I` and its value at `x`, viewed as an `ℝ≥0∞`-valued map. -/
def tiltedRateFunction (I : E → ENNReal) (φ : E → ℝ) : E → ENNReal :=
  fun x ↦
    (sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
      (((φ x : EReal) - (I x : EReal)))).toENNReal

-- Proof sketch: unfold `tiltedRateFunction`; the right-hand side is exactly the formula
-- `sup_z (φ z - I z) - (φ x - I x)` from (23.21), interpreted in `EReal` and then converted back
-- to `ℝ≥0∞` via `EReal.toENNReal`.
/-- Unfolding `tiltedRateFunction I φ` gives the shifted supremum formula from (23.21). -/
theorem tiltedRateFunction_def (I : E → ENNReal) (φ : E → ℝ) (x : E) :
    tiltedRateFunction I φ x =
      (sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
        (((φ x : EReal) - (I x : EReal)))).toENNReal := by
  -- Proof comment: `tiltedRateFunction` was defined by exactly this shifted-supremum formula.
  rfl

-- Proof sketch: apply `isProbabilityMeasure_tilted` to the underlying measure of the probability
-- measure `ν`; the integrability hypothesis is already stated in the exact form required by the
-- tilted-measure API.
/-- The tilted measure of a probability measure is again a probability measure when the exponential
weight is integrable. -/
theorem tilted_isProbabilityMeasure_of_probabilityMeasure
    (ν : ProbabilityMeasure E) (f : E → ℝ)
    (hf : Integrable (fun x ↦ Real.exp (f x)) (ν : Measure E)) :
    IsProbabilityMeasure ((ν : Measure E).tilted f) := by
  -- Proof comment: the mathlib tilted-measure API already proves that tilting a probability
  -- measure by an integrable exponential density preserves total mass `1`.
  simpa using isProbabilityMeasure_tilted (μ := (ν : Measure E)) (f := f) hf

/-- The exponentially tilted family `μᵠ_ε(dx) ∝ exp (φ x / ε) μ_ε(dx)` on the positive parameter
space `ε > 0`. -/
def tiltedProbabilityMeasureFamily
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E)) :
    PositiveProbabilityFamily E :=
  fun ε ↦
    ⟨(μ ε : Measure E).tilted (fun x ↦ φ x / (ε : ℝ)),
      tilted_isProbabilityMeasure_of_probabilityMeasure
        (μ ε) (fun x ↦ φ x / (ε : ℝ)) (h_integrable ε)⟩

-- Proof sketch: unfold `tiltedProbabilityMeasureFamily`; the result is exactly the exponentially
-- tilted measure `(μ ε).tilted (fun x ↦ φ x / ε)`.
/-- Evaluating `tiltedProbabilityMeasureFamily μ φ h_integrable` at `ε > 0` gives the textbook's
exponentially tilted law. -/
theorem tiltedProbabilityMeasureFamily_apply
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    (ε : PositiveParameter) :
    (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E) =
      (μ ε : Measure E).tilted (fun x ↦ φ x / (ε : ℝ)) := rfl

/-- Helper for Theorem 23.19: the scaled logarithmic mass of a set under the tilted family is the
restricted Laplace exponent minus the common normalizing constant. -/
private theorem tiltedScaledLogMass_eq_restrictedLaplaceExponent_sub_normalizer
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    (s : Set E) (ε : PositiveParameter) :
    scaledLogMassAlong
        (fun ε ↦ (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E)) id s ε =
      ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict s)) -
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
  let numerator : ℝ≥0∞ :=
    ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict s)
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hNormalizerPos :
      0 < ∫ x, Real.exp (φ x / (ε : ℝ)) ∂(μ ε : Measure E) := by
    -- Proof comment: the exponential weight is strictly positive everywhere, so its integral is
    -- strictly positive as soon as the function is integrable.
    exact MeasureTheory.integral_exp_pos (h_integrable ε)
  have hNormalizerEq :
      ENNReal.ofReal (∫ x, Real.exp (φ x / (ε : ℝ)) ∂(μ ε : Measure E)) =
        varadhanLaplaceFunctional μ φ ε := by
    -- Proof comment: the chapter's Laplace functional is precisely the `lintegral` version of the
    -- same exponential integral.
    rw [varadhanLaplaceFunctional_def]
    exact ofReal_integral_eq_lintegral_ofReal (h_integrable ε) (ae_of_all _ fun _ ↦ by positivity)
  have hMass :
      (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E) s =
        numerator * (varadhanLaplaceFunctional μ φ ε)⁻¹ := by
    -- Proof comment: `Measure.tilted_apply` rewrites the tilted mass as a restricted integral of
    -- the exponential density divided by the common normalizer, and the constant denominator then
    -- factors out of the restricted integral.
    have hIntegrand :
        (fun a : E ↦
          ENNReal.ofReal
            (Real.exp (φ a / (ε : ℝ)) / ∫ x, Real.exp (φ x / (ε : ℝ)) ∂(μ ε : Measure E))) =
          fun a : E ↦
            ENNReal.ofReal (Real.exp (φ a / (ε : ℝ))) *
              (ENNReal.ofReal (∫ x, Real.exp (φ x / (ε : ℝ)) ∂(μ ε : Measure E)))⁻¹ := by
      funext a
      rw [ENNReal.ofReal_div_of_pos hNormalizerPos, div_eq_mul_inv]
    rw [tiltedProbabilityMeasureFamily_apply, tilted_apply]
    simp_rw [hIntegrand]
    rw [lintegral_mul_const'' _ (((h_integrable ε).1.aemeasurable.ennreal_ofReal).restrict)]
    rw [← hNormalizerEq]
  have hScaledMass :
      scaledLogMassAlong
          (fun ε ↦ (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E)) id s ε =
        ((ε : ℝ) : EReal) * ENNReal.log (numerator * (varadhanLaplaceFunctional μ φ ε)⁻¹) := by
    -- Proof comment: apply the scaled-log operator to the mass identity from `hMass`.
    simpa [scaledLogMassAlong_def] using
      congrArg (fun m : ℝ≥0∞ ↦ ((ε : ℝ) : EReal) * ENNReal.log m) hMass
  -- Proof comment: after taking logarithms, the product from `hMass` becomes a sum, and the
  -- inverse normalizer contributes the subtraction term.
  calc
    scaledLogMassAlong
        (fun ε ↦ (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E)) id s ε
      = ((ε : ℝ) : EReal) * ENNReal.log (numerator * (varadhanLaplaceFunctional μ φ ε)⁻¹) :=
        hScaledMass
    _ = ((ε : ℝ) : EReal) *
          (ENNReal.log numerator + ENNReal.log ((varadhanLaplaceFunctional μ φ ε)⁻¹)) := by
          rw [ENNReal.log_mul_add]
    _ = ((ε : ℝ) : EReal) * ENNReal.log numerator +
          ((ε : ℝ) : EReal) * ENNReal.log ((varadhanLaplaceFunctional μ φ ε)⁻¹) := by
          rw [EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = ((ε : ℝ) : EReal) * ENNReal.log numerator -
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
          rw [ENNReal.log_inv, sub_eq_add_neg, ← mul_neg]
    _ = ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict s)) -
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
          rfl

/-- Helper for Theorem 23.19: coercing a positive parameter to `ℝ` sends the chapter's
positive-parameter filter back to `𝓝[>] (0 : ℝ)`. -/
private theorem map_positiveParameterFilter :
    Filter.map ((↑) : PositiveParameter → ℝ) positiveParameterFilter = 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `positiveParameterFilter` is the pullback of `𝓝[>] 0`, so mapping forward
  -- along the same coercion recovers the original filter.
  rw [positiveParameterFilter]
  refine Filter.map_comap_of_mem ?_
  simpa [PositiveParameter, Subtype.range_coe] using
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))

/-- Helper for Theorem 23.19: inside an open set `U`, continuity gives a smaller open neighborhood
on which `φ` stays above the chosen lower threshold `φ x - δ`. -/
private theorem exists_openLowerControlNeighborhoodWithin
    {φ : E → ℝ} (hφ : Continuous φ) {x : E} {U : Set E} (hU : IsOpen U) (hxU : x ∈ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V, φ x - δ ≤ φ y := by
  refine ⟨U ∩ φ ⁻¹' Set.Ioi (φ x - δ), hU.inter (hφ.isOpen_preimage _ isOpen_Ioi), ?_, ?_, ?_⟩
  · -- Proof comment: `x` stays in the original open set and also satisfies the strict lower
    -- control `φ x > φ x - δ`.
    refine ⟨hxU, ?_⟩
    simp [sub_lt_self_iff, hδ]
  · -- Proof comment: the refined neighborhood is built inside `U`.
    intro y hy
    exact hy.1
  · -- Proof comment: membership in the `Ioi` preimage is exactly the desired lower bound.
    intro y hy
    exact le_of_lt hy.2

/-- Helper for Theorem 23.19: a pointwise lower control `c ≤ φ` on a set `U` gives the
corresponding lower bound for the restricted Laplace exponent over `U`. -/
private theorem lowerControlOnSet_le_restrictedLaplaceExponent
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    {U : Set E} {c : ℝ}
    (hLower : ∀ y ∈ U, c ≤ φ y) :
    ∀ ε : PositiveParameter,
      (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε ≤
        ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) := by
  intro ε
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hPointwise :
      ∫⁻ y in U, ENNReal.ofReal (Real.exp (c / (ε : ℝ))) ∂(μ ε : Measure E) ≤
        ∫⁻ y in U, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂(μ ε : Measure E) := by
    -- Proof comment: inside `U`, the constant exponential `exp (c / ε)` is pointwise bounded by
    -- the actual integrand `exp (φ / ε)`.
    refine setLIntegral_mono_ae (((h_integrable ε).1.aemeasurable.ennreal_ofReal).restrict) ?_
    exact ae_of_all (μ ε : Measure E) fun y hyU ↦
      ENNReal.ofReal_le_ofReal <|
        Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right ε.2).2 (hLower y hyU))
  have hConst :
      ∫⁻ y in U, ENNReal.ofReal (Real.exp (c / (ε : ℝ))) ∂(μ ε : Measure E) =
        ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U) := by
    -- Proof comment: the constant integrand over the restricted measure contributes its value
    -- times the restricted mass.
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hLog :
      ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U)) ≤
        ENNReal.log
          (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) := by
    exact ENNReal.log_le_log (hConst.symm ▸ hPointwise)
  have hMul :
      ((ε : ℝ) : EReal) * ENNReal.log
          (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U)) ≤
        ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) := by
    exact mul_le_mul_of_nonneg_left hLog hε
  have hcancelReal : (ε : ℝ) * (c / (ε : ℝ)) = c := by
    field_simp [show (ε : ℝ) ≠ 0 by exact ne_of_gt ε.2]
  have hFirstTerm :
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) = (c : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), ← EReal.coe_mul, Real.log_exp, hcancelReal]
  -- Proof comment: taking logarithms isolates the deterministic contribution `c`, leaving the
  -- scaled logarithmic mass of `U`.
  calc
    (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε
      = (c : EReal) + ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) U) := by
          simp [scaledLogMassAlong_def]
    _ = ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) +
          ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) U) := by
            rw [hFirstTerm]
    _ = ((ε : ℝ) : EReal) *
          (ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) +
            ENNReal.log ((μ ε : Measure E) U)) := by
            rw [← EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U)) := by
            rw [ENNReal.log_mul_add]
    _ ≤ ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) :=
      hMul

/-- Helper for Theorem 23.19: a pointwise upper control `φ ≤ c` on a set `A` bounds the
restricted Laplace exponent over `A` by `c` plus the scaled logarithmic mass of `A`. -/
private theorem restrictedLaplaceExponent_le_upperControlOnSet
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) {A : Set E} {c : ℝ}
    (hUpper : ∀ y ∈ A, φ y ≤ c) :
    ∀ ε : PositiveParameter,
      ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A)) ≤
        (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id A ε := by
  intro ε
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hPointwise :
      ∫⁻ y in A, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂(μ ε : Measure E) ≤
        ∫⁻ y in A, ENNReal.ofReal (Real.exp (c / (ε : ℝ))) ∂(μ ε : Measure E) := by
    -- Proof comment: on `A`, the exponential weight is bounded above by the constant
    -- `exp (c / ε)`.
    refine setLIntegral_mono_ae (measurable_const.aemeasurable.restrict) ?_
    exact ae_of_all (μ ε : Measure E) fun y hyA ↦
      ENNReal.ofReal_le_ofReal <|
        Real.exp_le_exp.mpr ((div_le_div_iff_of_pos_right ε.2).2 (hUpper y hyA))
  have hConst :
      ∫⁻ y in A, ENNReal.ofReal (Real.exp (c / (ε : ℝ))) ∂(μ ε : Measure E) =
        ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A) := by
    -- Proof comment: the dominating constant integrates to its value times the mass of `A`.
    rw [lintegral_const, Measure.restrict_apply_univ]
  have hLog :
      ENNReal.log
          (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A)) ≤
        ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A)) := by
    exact hConst ▸ ENNReal.log_le_log hPointwise
  have hMul :
      ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A)) ≤
        ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A)) := by
    exact mul_le_mul_of_nonneg_left hLog hε
  have hcancelReal : (ε : ℝ) * (c / (ε : ℝ)) = c := by
    field_simp [show (ε : ℝ) ≠ 0 by exact ne_of_gt ε.2]
  have hFirstTerm :
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) = (c : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), ← EReal.coe_mul, Real.log_exp, hcancelReal]
  -- Proof comment: after logarithms, the constant exponential contributes `c`, and the remaining
  -- factor is the scaled logarithmic mass of `A`.
  calc
    ((ε : ℝ) : EReal) *
        ENNReal.log
          (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A))
      ≤ ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A)) :=
        hMul
    _ = ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) +
          ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) A) := by
            rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = (c : EReal) + ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) A) := by
          rw [hFirstTerm]
    _ = (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id A ε := by
          simp [scaledLogMassAlong_def]

/-- Helper for Theorem 23.19: the localized open-set lower bounds give the numerator estimate
`sup_{x ∈ U} (φ x - I x) ≤ liminf ε log ∫_U exp (φ / ε) dμ_ε`. -/
private theorem sourceSupOnOpen_le_restrictedLaplaceLiminf
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) (hφ : Continuous φ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    {U : Set E} (hU : IsOpen U) :
    sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' U)) ≤
      Filter.liminf
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)))
        positiveParameterFilter := by
  refine sSup_le ?_
  rintro z ⟨x, hxU, rfl⟩
  refine (EReal.ge_of_forall_gt_iff_ge).1 ?_
  intro y hy
  by_cases hIx_top : I x = ⊤
  · exfalso
    simp [hIx_top] at hy
  let ix : ℝ := (I x).toReal
  have hIxEReal : ((I x : ENNReal) : EReal) = (ix : EReal) := by
    simp [ix, EReal.coe_ennreal_toReal, hIx_top]
  have hy' : (y : EReal) < (φ x : EReal) - (ix : EReal) := by
    simpa [hIxEReal] using hy
  have hyReal : y + ix < φ x := by
    have hyEReal : (y : EReal) + (ix : EReal) < (φ x : EReal) := EReal.add_lt_of_lt_sub hy'
    exact_mod_cast hyEReal
  let δ : ℝ := φ x - (y + ix)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  obtain ⟨V, hV, hxV, hVU, hLower⟩ :=
    exists_openLowerControlNeighborhoodWithin (hφ := hφ) (U := U) hU hxU (δ := δ) hδ
  have hLocalPointwise :
      ∀ ε : PositiveParameter,
        ((φ x - δ : ℝ) : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε ≤
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) := by
    intro ε
    have hBase :
        ((φ x - δ : ℝ) : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε ≤
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict V)) := by
      -- Proof comment: the refined neighborhood `V` already carries the desired lower control.
      simpa using
        (lowerControlOnSet_le_restrictedLaplaceExponent
          (μ := μ) (φ := φ) h_integrable (U := V) (c := φ x - δ) hLower ε)
    have hIntegral :
        ∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict V) ≤
          ∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U) := by
      -- Proof comment: enlarging the restriction set from `V` to `U` can only increase the
      -- restricted integral.
      exact lintegral_mono' (Measure.restrict_mono hVU le_rfl) le_rfl
    have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast le_of_lt ε.2
    calc
      ((φ x - δ : ℝ) : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε
        ≤ ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict V)) :=
          hBase
      _ ≤ ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)) := by
            exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hIntegral) hε
  have hOpenLower :
      -sInf ((fun y ↦ (I y : EReal)) '' V) ≤
        Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V)
          positiveParameterFilter := by
    -- Proof comment: the owner LDP applies to the open neighborhood `V`.
    simpa using hLDP.open_lower_bound (U := V) hV
  have hsInf_le :
      sInf ((fun y ↦ (I y : EReal)) '' V) ≤ (I x : EReal) := by
    -- Proof comment: `x` belongs to `V`, so its rate value bounds the infimum from above.
    exact sInf_le ⟨x, hxV, rfl⟩
  have hNeg :
      -(I x : EReal) ≤ -sInf ((fun y ↦ (I y : EReal)) '' V) := by
    exact EReal.neg_le_neg_iff.2 hsInf_le
  have hLiminfAdd :
      ((φ x - δ : ℝ) : EReal) +
          Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V)
            positiveParameterFilter ≤
        Filter.liminf
          (fun ε : PositiveParameter ↦
            ((φ x - δ : ℝ) : EReal) +
              scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε)
          positiveParameterFilter := by
    simpa using
      (EReal.le_liminf_add
        (u := fun _ : PositiveParameter ↦ ((φ x - δ : ℝ) : EReal))
        (v := scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V)
        (f := positiveParameterFilter))
  have hLiminfMono :
      Filter.liminf
          (fun ε : PositiveParameter ↦
            ((φ x - δ : ℝ) : EReal) +
              scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε)
          positiveParameterFilter ≤
        Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log
                (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)))
          positiveParameterFilter := by
    exact Filter.liminf_le_liminf <| Eventually.of_forall hLocalPointwise
  have hδeq : φ x - δ = y + ix := by
    dsimp [δ]
    linarith
  -- Proof comment: add the open-set LDP lower bound on `V` to the deterministic contribution
  -- `φ x - δ`, then rewrite that contribution back to the chosen comparison level `y`.
  calc
    (y : EReal) = ((y : EReal) + (ix : EReal)) - (ix : EReal) := by
      symm
      simpa [add_comm] using (EReal.add_sub_cancel_right (a := (y : EReal)) (b := ix))
    _ = (((φ x - δ : ℝ) : EReal) - (I x : EReal)) := by
      rw [hδeq, hIxEReal]
      simp
    _ = ((φ x - δ : ℝ) : EReal) + (-(I x : EReal)) := by
      rw [sub_eq_add_neg]
    _ ≤ ((φ x - δ : ℝ) : EReal) + (-sInf ((fun y ↦ (I y : EReal)) '' V)) := by
      gcongr
    _ ≤ ((φ x - δ : ℝ) : EReal) +
          Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V)
            positiveParameterFilter := by
      gcongr
    _ ≤ Filter.liminf
          (fun ε : PositiveParameter ↦
            ((φ x - δ : ℝ) : EReal) +
              scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id V ε)
          positiveParameterFilter := hLiminfAdd
    _ ≤ Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log
                (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict U)))
          positiveParameterFilter := hLiminfMono

/-- Helper for Theorem 23.19: the finite-sum limsup of scaled logarithmic terms is controlled by
the finite supremum of the individual limsups. -/
private theorem scaledLogFinsetSumLimsup_le_iSup {ι : Type*}
    (s : Finset ι) (u : ι → PositiveParameter → ℝ≥0∞) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε))
        positiveParameterFilter ≤
      ⨆ i ∈ s,
        Filter.limsup
          (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (u i ε))
          positiveParameterFilter := by
  let uReal : ι → ℝ → ℝ≥0∞ := fun i ε ↦ if hε : 0 < ε then u i ⟨ε, hε⟩ else 0
  have hMain :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε))
          positiveParameterFilter =
        ENNReal.smallNoiseExpGrowthSup (fun ε : ℝ ↦ s.sum fun i ↦ uReal i ε) := by
    -- Proof comment: transport the positive-parameter family once to the standard
    -- right-neighborhood filter at `0`.
    rw [show
      (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε)) =
        (fun ε : ℝ ↦ ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ uReal i ε)) ∘
          ((↑) : PositiveParameter → ℝ) by
        funext ε
        simpa [uReal, show (0 : ℝ) < (ε : ℝ) from ε.2]]
    rw [Filter.limsup_comp, map_positiveParameterFilter, ENNReal.smallNoiseExpGrowthSup_def]
  have hSingle :
      ∀ i,
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (u i ε))
            positiveParameterFilter =
          ENNReal.smallNoiseExpGrowthSup (uReal i) := by
    intro i
    -- Proof comment: each summand uses the same filter-transport bridge.
    rw [show
      (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (u i ε)) =
        (fun ε : ℝ ↦ ((ε : ℝ) : EReal) * ENNReal.log (uReal i ε)) ∘
          ((↑) : PositiveParameter → ℝ) by
        funext ε
        simpa [uReal, show (0 : ℝ) < (ε : ℝ) from ε.2]]
    rw [Filter.limsup_comp, map_positiveParameterFilter, ENNReal.smallNoiseExpGrowthSup_def]
  have hEq :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε))
          positiveParameterFilter =
        ⨆ i ∈ s,
          Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (u i ε))
            positiveParameterFilter := by
    -- Proof comment: the real-parameter aggregation theorem already identifies the finite-sum
    -- growth rate with the supremum of the individual growth rates.
    calc
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε))
          positiveParameterFilter
        = ENNReal.smallNoiseExpGrowthSup (fun ε : ℝ ↦ s.sum fun i ↦ uReal i ε) := hMain
      _ = ⨆ i ∈ s, ENNReal.smallNoiseExpGrowthSup (uReal i) := by
        rw [show (fun ε : ℝ ↦ s.sum (fun i ↦ uReal i ε)) = s.sum uReal by
          funext ε
          simp]
        simpa using ENNReal.smallNoiseExpGrowthSup_sum uReal s
      _ = ⨆ i ∈ s,
            Filter.limsup
              (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (u i ε))
              positiveParameterFilter := by
        simp [hSingle]
  exact hEq.le

/-- Helper for Theorem 23.19: if `A` is covered by finitely many sets `B i`, then the restricted
measure on `A` is dominated by the finite sum of the corresponding restricted measures. -/
private theorem restrict_le_sum_restrict_of_subset_iUnion {ι : Type*}
    (ν : Measure E) (A : Set E) (s : Finset ι) (B : ι → Set E)
    (hA : A ⊆ ⋃ i ∈ (s : Set ι), B i) :
    ν.restrict A ≤ Finset.sum s (fun i ↦ ν.restrict (B i)) := by
  classical
  have hUnion :
      ∀ t : Finset ι,
        ν.restrict (⋃ i ∈ (t : Set ι), B i) ≤ Finset.sum t (fun i ↦ ν.restrict (B i)) := by
    intro t
    -- Proof comment: expand the finite union one set at a time and use the subadditivity of
    -- `restrict` under unions.
    induction t using Finset.induction_on with
    | empty =>
        simp
    | @insert i t hi ht =>
        calc
          ν.restrict (⋃ j ∈ ((insert i t : Finset ι) : Set ι), B j)
            = ν.restrict (B i ∪ ⋃ j ∈ (t : Set ι), B j) := by
                simp
          _ ≤ ν.restrict (B i) + ν.restrict (⋃ j ∈ (t : Set ι), B j) :=
            Measure.restrict_union_le (B i) (⋃ j ∈ (t : Set ι), B j)
          _ ≤ ν.restrict (B i) + Finset.sum t (fun j ↦ ν.restrict (B j)) := by
            gcongr
          _ = Finset.sum (insert i t) (fun j ↦ ν.restrict (B j)) := by
            simp [hi]
  -- Proof comment: first enlarge `A` to the covering union, then apply the finite-union
  -- domination `hUnion`.
  exact le_trans (Measure.restrict_mono hA le_rfl) (hUnion s)

/-- Helper for Theorem 23.19: every scaled logarithmic mass is nonpositive for a probability
family, because every event has mass at most `1`. -/
private theorem scaledLogMassAlong_nonpos_of_probability
    (μ : PositiveProbabilityFamily E) {s : Set E} (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id s ε ≤ 0 := by
  -- Proof comment: event masses under a probability measure are bounded by `1`, so their
  -- logarithms are nonpositive, and the positive factor `ε` preserves that inequality.
  rw [scaledLogMassAlong_def]
  have hMass : ((μ ε : Measure E) s) ≤ 1 := by
    calc
      (μ ε : Measure E) s ≤ (μ ε : Measure E) Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := by simp
  have hLog : ENNReal.log ((μ ε : Measure E) s) ≤ 0 := by
    simpa using
      (ENNReal.log_le_log hMass :
        ENNReal.log ((μ ε : Measure E) s) ≤ ENNReal.log (1 : ℝ≥0∞))
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  exact mul_nonpos_of_nonneg_of_nonpos hε hLog

/-- Helper for Theorem 23.19: compactness of `Set.Icc a b` gives a finite cover by closed
intervals of width at most `η`. -/
private theorem existsIccCoverWithWidth
    (a b η : ℝ) (hab : a ≤ b) (hη : 0 < η) :
    ∃ s : Finset ℝ,
      Set.Icc a b ⊆ ⋃ c ∈ (s : Set ℝ), Set.Icc (c - η / 2) (c + η / 2) ∧
      ∀ c ∈ s, (c + η / 2) - (c - η / 2) ≤ η := by
  classical
  have hOpenCover : Set.Icc a b ⊆ ⋃ c ∈ Set.Icc a b, Set.Ioo (c - η / 2) (c + η / 2) := by
    intro x hx
    refine Set.mem_iUnion.2 ?_
    refine ⟨x, Set.mem_iUnion.2 ?_⟩
    refine ⟨hx, ?_⟩
    constructor <;> linarith
  obtain ⟨t, htSubset, htFinite, htCover⟩ :
      ∃ t : Set ℝ, t ⊆ Set.Icc a b ∧ t.Finite ∧
        Set.Icc a b ⊆ ⋃ c ∈ t, Set.Ioo (c - η / 2) (c + η / 2) := by
    exact isCompact_Icc.elim_finite_subcover_image (fun c _hc ↦ isOpen_Ioo) hOpenCover
  refine ⟨htFinite.toFinset, ?_, ?_⟩
  · intro x hx
    have hxOpen : x ∈ ⋃ c ∈ t, Set.Ioo (c - η / 2) (c + η / 2) := htCover hx
    have hxClosed : x ∈ ⋃ c ∈ t, Set.Icc (c - η / 2) (c + η / 2) := by
      rcases Set.mem_iUnion.1 hxOpen with ⟨c, hxc⟩
      rcases Set.mem_iUnion.1 hxc with ⟨hc, hmem⟩
      refine Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hc, ?_⟩⟩
      exact ⟨hmem.1.le, hmem.2.le⟩
    simpa [Set.Finite.mem_toFinset] using hxClosed
  · intro c hc
    have hWidth : (c + η / 2) - (c - η / 2) = η := by
      ring
    simpa [hWidth]

/-- Helper for Theorem 23.19: on a closed interval of width at most `η`, the endpoint term
`b - inf I` over `C ∩ φ ⁻¹' Set.Icc a b` is controlled by the source supremum on `C` up to `η`. -/
private theorem rightEndpoint_sub_sInf_interPreimageIcc_le_sourceSupOnClosed_add
    (I : E → ENNReal) (φ : E → ℝ) (C : Set E) (a b η : ℝ)
    (hwidth : b - a ≤ η) :
    ((b : EReal) - sInf ((fun x ↦ (I x : EReal)) '' (C ∩ φ ⁻¹' Set.Icc a b))) ≤
      sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
  let S : EReal := sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C))
  let T : Set EReal := (fun x ↦ (I x : EReal)) '' (C ∩ φ ⁻¹' Set.Icc a b)
  have hsInf_nonbot : sInf T ≠ ⊥ := by
    -- Proof comment: all rate values lie in `EReal≥0`, so the infimum cannot be `⊥`.
    have hnonneg : (0 : EReal) ≤ sInf T := by
      refine le_sInf ?_
      intro y hy
      rcases hy with ⟨x, -, rfl⟩
      exact EReal.coe_ennreal_nonneg (I x)
    intro hs
    simp [hs] at hnonneg
  by_cases hsInf_top : sInf T = ⊤
  · -- Proof comment: if all values in the interval piece are infinite, the left-hand side is
    -- already `⊥`.
    simp [T, hsInf_top]
  have hLower : ((b : EReal) - (S + η)) ≤ sInf T := by
    -- Proof comment: every `x` in the interval piece satisfies `φ x ≤ b` and
    -- `((φ x) - I x) ≤ sup_C (φ - I)`, so rearranging gives the desired endpoint estimate.
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxIcc : a ≤ φ x ∧ φ x ≤ b := by
      simpa [Set.mem_preimage, Set.mem_Icc] using hx.2
    by_cases hIx_top : (I x : EReal) = ⊤
    · simp [hIx_top]
    have hIx_bot : (I x : EReal) ≠ ⊥ := EReal.coe_ennreal_ne_bot (I x)
    have hb_le : (b : EReal) ≤ (φ x : EReal) + η := by
      have hreal : b ≤ φ x + η := by
        linarith [hxIcc.1, hwidth]
      exact_mod_cast hreal
    have hpoint : (b : EReal) - (I x : EReal) ≤ S + η := by
      calc
        (b : EReal) - (I x : EReal) ≤ (((φ x : EReal) + η) - (I x : EReal)) := by
          exact EReal.sub_le_sub hb_le le_rfl
        _ = (((φ x : EReal) - (I x : EReal)) + η) := by
          simp [sub_eq_add_neg, add_left_comm, add_comm]
        _ ≤ S + η := by
          gcongr
          exact le_sSup ⟨x, hx.1, rfl⟩
    have hAdd : (b : EReal) ≤ (S + η) + (I x : EReal) := by
      exact (EReal.sub_le_iff_le_add (.inl hIx_bot) (.inl hIx_top)).1 hpoint
    exact EReal.sub_le_of_le_add' (by simpa [add_assoc, add_left_comm, add_comm] using hAdd)
  have hAdd : (b : EReal) ≤ sInf T + (S + η) := by
    exact (EReal.sub_le_iff_le_add (.inr hsInf_top) (.inr hsInf_nonbot)).1 hLower
  -- Proof comment: convert the lower-bound form back into the endpoint-minus-infimum estimate.
  exact EReal.sub_le_of_le_add' (by simpa [add_assoc, add_left_comm, add_comm] using hAdd)

/-- Helper for Theorem 23.19: a single closed slice `C ∩ φ ⁻¹' Set.Icc a b` contributes at most
the source supremum on `C` plus the slice width error `η`. -/
private theorem restrictedIccSliceLimsup_le_sourceSupOnClosed_add
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) (hφ : Continuous φ)
    {C : Set E} (hC : IsClosed C) {a b η : ℝ} (hwidth : b - a ≤ η) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))))
        positiveParameterFilter ≤
      sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
  let g : PositiveParameter → EReal :=
    scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (C ∩ φ ⁻¹' Set.Icc a b)
  have hPointwise :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))) ≤
          (b : EReal) + g ε := by
    intro ε
    -- Proof comment: on the slice `C ∩ φ ⁻¹' Set.Icc a b`, the potential is bounded above by
    -- the right endpoint `b`.
    simpa [g] using
      (restrictedLaplaceExponent_le_upperControlOnSet
        (μ := μ) (φ := φ) (A := C ∩ φ ⁻¹' Set.Icc a b) (c := b)
        (fun x hx ↦ by
          have hxIcc : a ≤ φ x ∧ φ x ≤ b := by
            simpa [Set.mem_preimage, Set.mem_Icc] using hx.2
          exact hxIcc.2) ε)
  have hPointwiseLimsup :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log
                (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                  ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))))
          positiveParameterFilter ≤
        Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter := by
    exact Filter.limsup_le_limsup (Eventually.of_forall hPointwise)
  have hAddLimsup :
      Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter ≤
        (b : EReal) + Filter.limsup g positiveParameterFilter := by
    -- Proof comment: separate the fixed right-endpoint contribution from the logarithmic mass.
    simpa [Filter.limsup_const] using
      (EReal.limsup_add_le
        (u := fun _ : PositiveParameter ↦ (b : EReal))
        (v := g) (f := positiveParameterFilter)
        (Or.inl (by simp)) (Or.inl (by simp)))
  have hSliceClosed : IsClosed (C ∩ φ ⁻¹' Set.Icc a b) := by
    -- Proof comment: the closed LDP bound applies directly to the closed slice.
    exact hC.inter (IsClosed.preimage hφ isClosed_Icc)
  have hClosed :
      Filter.limsup g positiveParameterFilter ≤
        -sInf ((fun x ↦ (I x : EReal)) '' (C ∩ φ ⁻¹' Set.Icc a b)) := by
    simpa [g] using hLDP.closed_upper_bound (C := C ∩ φ ⁻¹' Set.Icc a b) hSliceClosed
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))))
        positiveParameterFilter
      ≤ Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter :=
        hPointwiseLimsup
    _ ≤ (b : EReal) + Filter.limsup g positiveParameterFilter := hAddLimsup
    _ ≤ (b : EReal) + (-sInf ((fun x ↦ (I x : EReal)) '' (C ∩ φ ⁻¹' Set.Icc a b))) := by
      gcongr
    _ = (b : EReal) - sInf ((fun x ↦ (I x : EReal)) '' (C ∩ φ ⁻¹' Set.Icc a b)) := by
      rw [sub_eq_add_neg]
    _ ≤ sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η :=
      rightEndpoint_sub_sInf_interPreimageIcc_le_sourceSupOnClosed_add
        (I := I) (φ := φ) (C := C) a b η hwidth

/-- Helper for Theorem 23.19: a bounded interval `C ∩ φ ⁻¹' Set.Icc a b` is controlled by a
finite cover of width-`η` slices, so its limsup is still at most the source supremum on `C` plus
`η`. -/
private theorem restrictedCompactIntervalLimsup_le_sourceSupOnClosed_add
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) (hφ : Continuous φ)
    {C : Set E} (hC : IsClosed C) {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))))
        positiveParameterFilter ≤
      sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
  classical
  obtain ⟨s, hcover, hwidth⟩ := existsIccCoverWithWidth a b η hab hη
  let pieceSet : ℝ → Set E := fun c ↦ C ∩ φ ⁻¹' Set.Icc (c - η / 2) (c + η / 2)
  let piece : ℝ → PositiveParameter → ℝ≥0∞ := fun c ε ↦
    ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict (pieceSet c))
  have hCoverOnC :
      C ∩ φ ⁻¹' Set.Icc a b ⊆ ⋃ c ∈ (s : Set ℝ), pieceSet c := by
    intro x hx
    have hxIcc : φ x ∈ Set.Icc a b := by
      simpa [Set.mem_preimage] using hx.2
    rcases Set.mem_iUnion.1 (hcover hxIcc) with ⟨c, hc⟩
    rcases Set.mem_iUnion.1 hc with ⟨hcS, hcx⟩
    exact Set.mem_iUnion.2 ⟨c, Set.mem_iUnion.2 ⟨hcS, ⟨hx.1, hcx⟩⟩⟩
  have hIntegralBound :
      ∀ ε : PositiveParameter,
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b)) ≤
          s.sum fun c ↦ piece c ε := by
    intro ε
    have hMeasure :
        (μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b) ≤
          s.sum fun c ↦ (μ ε : Measure E).restrict (pieceSet c) := by
      -- Proof comment: the restriction to the bounded middle strip is dominated by the sum of the
      -- finitely many slice restrictions from the interval cover.
      exact restrict_le_sum_restrict_of_subset_iUnion
        (ν := (μ ε : Measure E)) (A := C ∩ φ ⁻¹' Set.Icc a b) (s := s) (B := pieceSet) hCoverOnC
    have hIntegral :
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b)) ≤
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            (s.sum fun c ↦ (μ ε : Measure E).restrict (pieceSet c)) := by
      exact lintegral_mono' hMeasure le_rfl
    calc
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
          ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))
        ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            (s.sum fun c ↦ (μ ε : Measure E).restrict (pieceSet c)) := hIntegral
      _ = s.sum fun c ↦ piece c ε := by
        simpa [piece] using
          (MeasureTheory.lintegral_finset_sum_measure
            (s := s)
            (f := fun x : E ↦ ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))))
            (μ := fun c ↦ (μ ε : Measure E).restrict (pieceSet c)))
  have hPointwiseLog :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))) ≤
          ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε) := by
    intro ε
    have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast le_of_lt ε.2
    exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hIntegralBound ε)) hε
  have hPiece :
      ∀ c ∈ s,
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (piece c ε))
            positiveParameterFilter ≤
          sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
    intro c hc
    -- Proof comment: each cover piece has width at most `η`, so the single-slice estimate applies.
    simpa [piece, pieceSet] using
      (restrictedIccSliceLimsup_le_sourceSupOnClosed_add
        (μ := μ) (I := I) (φ := φ) hLDP hφ hC
        (a := c - η / 2) (b := c + η / 2) (η := η) (hwidth c hc))
  have hSumBound :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε))
          positiveParameterFilter ≤
        sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
    calc
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε))
          positiveParameterFilter
        ≤ ⨆ c ∈ s,
            Filter.limsup
              (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (piece c ε))
              positiveParameterFilter :=
          scaledLogFinsetSumLimsup_le_iSup (s := s) (u := piece)
      _ ≤ sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := by
        refine iSup_le ?_
        intro c
        refine iSup_le ?_
        intro hc
        exact hPiece c hc
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ φ ⁻¹' Set.Icc a b))))
        positiveParameterFilter
      ≤ Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε))
          positiveParameterFilter := by
            exact Filter.limsup_le_limsup (Eventually.of_forall hPointwiseLog)
    _ ≤ sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) + η := hSumBound

/-- Helper for Theorem 23.19: the left strip `C ∩ {φ ≤ -R}` contributes at most `-R`, because the
remaining logarithmic mass is nonpositive under a probability measure. -/
private theorem restrictedLeftTailLimsup_le
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (C : Set E) (R : ℝ) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ {x | φ x ≤ -R}))))
        positiveParameterFilter ≤
      (-R : EReal) := by
  let A : Set E := C ∩ {x | φ x ≤ -R}
  let g : PositiveParameter → EReal :=
    scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id A
  have hPointwise :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict A)) ≤
          (-R : EReal) + g ε := by
    intro ε
    -- Proof comment: the potential is pointwise bounded above by `-R` on the left strip.
    simpa [A, g] using
      (restrictedLaplaceExponent_le_upperControlOnSet
        (μ := μ) (φ := φ) (A := A) (c := -R) (fun x hx ↦ hx.2) ε)
  have hPointwise_le :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ {x | φ x ≤ -R}))) ≤
          (-R : EReal) := by
    intro ε
    calc
      ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
              ((μ ε : Measure E).restrict (C ∩ {x | φ x ≤ -R})))
        ≤ (-R : EReal) + g ε := by
            simpa [A] using hPointwise ε
      _ ≤ (-R : EReal) + 0 := by
        gcongr
        exact scaledLogMassAlong_nonpos_of_probability (μ := μ) (s := A) ε
      _ = (-R : EReal) := by simp
  -- Proof comment: the pointwise left-strip bound passes directly to the limsup.
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict (C ∩ {x | φ x ≤ -R}))))
        positiveParameterFilter
      ≤ Filter.limsup (fun _ : PositiveParameter ↦ (-R : EReal)) positiveParameterFilter := by
          exact Filter.limsup_le_limsup (Eventually.of_forall hPointwise_le)
    _ = (-R : EReal) := by simp

/-- Helper for Theorem 23.19: the restricted closed-set Laplace exponent is at most the source
supremum on `C`. This is the measurable-free closed numerator upper bound needed for the tilted
LDP. -/
private theorem restrictedLaplaceLimsup_le_sourceSupOnClosed
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) (hφ : Continuous φ)
    {C : Set E} (hC : IsClosed C)
    (h_tail :
      sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict
                {x | M.1 ≤ φ x})))
          positiveParameterFilter) = ⊥) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C)))
        positiveParameterFilter ≤
      sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) := by
  let S : EReal := sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C))
  let laplaceExponent : PositiveParameter → EReal := fun ε ↦
    ((ε : ℝ) : EReal) *
      ENNReal.log
        (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C))
  refine (EReal.le_of_forall_lt_iff_le
    (x := S) (y := Filter.limsup laplaceExponent positiveParameterFilter)).1 ?_
  intro y hSy
  obtain ⟨η, hη, hSη_lt⟩ : ∃ η : ℝ, 0 < η ∧ S + η < y := by
    by_cases hSbot : S = ⊥
    · refine ⟨1, zero_lt_one, ?_⟩
      simpa [hSbot] using (EReal.bot_lt_coe y)
    · have hStop : S ≠ ⊤ := by
        intro hStop
        simpa [hStop] using hSy
      let η : ℝ := (y - S.toReal) / 2
      have hStoReal_lt : S.toReal < y := by
        have hSy' : ((S.toReal : ℝ) : EReal) < y := by
          simpa [EReal.coe_toReal hStop hSbot] using hSy
        exact EReal.coe_lt_coe_iff.1 hSy'
      have hη : 0 < η := by
        dsimp [η]
        linarith
      have hSη_lt : S + η < y := by
        rw [← EReal.coe_toReal hStop hSbot, ← EReal.coe_add]
        dsimp [η]
        exact_mod_cast (by linarith : S.toReal + (y - S.toReal) / 2 < y)
      exact ⟨η, hη, hSη_lt⟩
  obtain ⟨M, hTailM⟩ :
      ∃ M : {M : ℝ // 0 < M},
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) *
                ENNReal.log
                  (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                    ((μ ε : Measure E).restrict {x | M.1 ≤ φ x})))
            positiveParameterFilter < y := by
    by_contra hM
    push_neg at hM
    have hyInf :
        (y : EReal) ≤
          sInf
            (Set.range fun M : {M : ℝ // 0 < M} ↦
              Filter.limsup
                (fun ε : PositiveParameter ↦
                  ((ε : ℝ) : EReal) *
                    ENNReal.log
                      (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                        ((μ ε : Measure E).restrict {x | M.1 ≤ φ x})))
                positiveParameterFilter) := by
      refine le_sInf ?_
      rintro z ⟨M, rfl⟩
      exact hM M
    simpa [h_tail] using hyInf
  let R : ℝ := max 1 (-y + 1)
  have hRpos : 0 < R := by
    exact lt_of_lt_of_le zero_lt_one (by
      dsimp [R]
      exact le_max_left 1 (-y + 1))
  have hLeftLevel : (-R : EReal) < y := by
    have hRLower : -y + 1 ≤ R := by
      dsimp [R]
      exact le_max_right 1 (-y + 1)
    have hLeftLevelReal : -R < y := by
      linarith
    exact_mod_cast hLeftLevelReal
  have hMidOrder : -R ≤ M.1 := by
    linarith [hRpos, M.2]
  let partSet : Fin 3 → Set E
    | 0 => C ∩ {x | φ x ≤ -R}
    | 1 => C ∩ φ ⁻¹' Set.Icc (-R) M.1
    | _ => C ∩ {x | M.1 ≤ φ x}
  let part : Fin 3 → PositiveParameter → ℝ≥0∞ := fun i ε ↦
    ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict (partSet i))
  have hCoverOnC : C ⊆ ⋃ i ∈ ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)), partSet i := by
    intro x hxC
    by_cases hLeft : φ x ≤ -R
    · exact Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, hLeft⟩⟩⟩
    · by_cases hMid : φ x ≤ M.1
      · have hxIcc : φ x ∈ Set.Icc (-R) M.1 := ⟨(lt_of_not_ge hLeft).le, hMid⟩
        exact Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, hxIcc⟩⟩⟩
      · exact Set.mem_iUnion.2 ⟨2, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, le_of_not_ge hMid⟩⟩⟩
  have hIntegralBound :
      ∀ ε : PositiveParameter,
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C) ≤
          Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
    intro ε
    have hMeasure :
        (μ ε : Measure E).restrict C ≤
          Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i) := by
      -- Proof comment: split the closed set into the left strip, the bounded middle strip, and
      -- the upper tail.
      exact restrict_le_sum_restrict_of_subset_iUnion
        (ν := (μ ε : Measure E)) (A := C) (s := Finset.univ) (B := partSet) hCoverOnC
    have hIntegral :
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C) ≤
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            (Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)) := by
      exact lintegral_mono' hMeasure le_rfl
    calc
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C)
        ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            (Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)) := hIntegral
      _ = Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
        simpa [part] using
          (MeasureTheory.lintegral_finset_sum_measure
            (s := Finset.univ)
            (f := fun x : E ↦ ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))))
            (μ := fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)))
  have hPointwiseLog :
      ∀ ε : PositiveParameter,
        laplaceExponent ε ≤
          ((ε : ℝ) : EReal) *
            ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε) := by
    intro ε
    have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast le_of_lt ε.2
    simpa [laplaceExponent] using
      (mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hIntegralBound ε)) hε)
  have hPart0 :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (part 0 ε))
          positiveParameterFilter ≤
        (-R : EReal) := by
    -- Proof comment: the left strip is controlled by the deterministic bound `φ ≤ -R`.
    simpa [part, partSet] using
      (restrictedLeftTailLimsup_le (μ := μ) (φ := φ) (C := C) R)
  have hPart1 :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (part 1 ε))
          positiveParameterFilter ≤
        S + η := by
    -- Proof comment: the bounded middle strip is exactly the compact-interval estimate.
    simpa [S, part, partSet] using
      (restrictedCompactIntervalLimsup_le_sourceSupOnClosed_add
        (μ := μ) (I := I) (φ := φ) hLDP hφ hC
        (a := -R) (b := M.1) (η := η) hMidOrder hη)
  have hPart2 :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε))
          positiveParameterFilter < y := by
    have hPointwisePart2 :
        ∀ ε : PositiveParameter,
          ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε) ≤
            ((ε : ℝ) : EReal) *
              ENNReal.log
                (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                  ((μ ε : Measure E).restrict {x | M.1 ≤ φ x})) := by
      intro ε
      have hIntegral :
          part 2 ε ≤
            ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
              ((μ ε : Measure E).restrict {x | M.1 ≤ φ x}) := by
        -- Proof comment: the restricted tail over `C` is dominated by the global tail from the
        -- hypothesis.
        exact lintegral_mono'
          (Measure.restrict_mono (by intro x hx; exact hx.2) le_rfl) le_rfl
      have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
        exact_mod_cast le_of_lt ε.2
      exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hIntegral) hε
    have hTailLe :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε))
            positiveParameterFilter ≤
          Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) *
                ENNReal.log
                  (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                    ((μ ε : Measure E).restrict {x | M.1 ≤ φ x})))
            positiveParameterFilter := by
      exact Filter.limsup_le_limsup (Eventually.of_forall hPointwisePart2)
    exact lt_of_le_of_lt hTailLe hTailM
  have hSumBound :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
          positiveParameterFilter ≤
        y := by
    calc
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
          positiveParameterFilter
        ≤
          ⨆ i ∈ (Finset.univ : Finset (Fin 3)),
            Filter.limsup
              (fun ε : PositiveParameter ↦
                ((ε : ℝ) : EReal) * ENNReal.log (part i ε))
              positiveParameterFilter :=
        scaledLogFinsetSumLimsup_le_iSup (s := Finset.univ) (u := part)
      _ ≤ y := by
        refine iSup_le ?_
        intro i
        refine iSup_le ?_
        intro hi
        fin_cases i
        · exact hPart0.trans hLeftLevel.le
        · exact hPart1.trans hSη_lt.le
        · exact hPart2.le
  calc
    Filter.limsup laplaceExponent positiveParameterFilter
      ≤
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
          positiveParameterFilter := by
            exact Filter.limsup_le_limsup (Eventually.of_forall hPointwiseLog)
    _ ≤ y := hSumBound

/-- Helper for Theorem 23.19: after coercing back to `EReal`, the tilted rate is the nonnegative
part of the shifted gap `S - (φ x - I x)`. -/
private theorem tiltedRateFunction_coe_ereal
    (I : E → ENNReal) (φ : E → ℝ) (x : E) :
    ((tiltedRateFunction I φ x : ENNReal) : EReal) =
      max 0
        (sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
          (((φ x : EReal) - (I x : EReal)))) := by
  -- Proof comment: coercing `toENNReal` back to `EReal` returns the positive part `max 0 _`.
  rw [tiltedRateFunction_def, EReal.coe_toENNReal_eq_max]

/-- Helper for Theorem 23.19: the source supremum dominates each pointwise value of `φ - I`, so
the shifted gap `S - (φ x - I x)` is nonnegative whenever `S` is not `⊥`. -/
private theorem sourceSup_sub_sourcePoint_nonneg
    (I : E → ENNReal) (φ : E → ℝ)
    (hS_bot :
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) ≠ ⊥)
    (x : E) :
    0 ≤
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
        (((φ x : EReal) - (I x : EReal))) := by
  -- Proof comment: the pointwise value at `x` belongs to the defining range of the supremum, so
  -- `φ x - I x ≤ S`; this is exactly the same as the shifted gap being nonnegative.
  have hPoint_ne_top : (((φ x : EReal) - (I x : EReal))) ≠ ⊤ := by
    -- Proof comment: the finite real term `φ x` prevents the difference from reaching `⊤`.
    rw [sub_eq_add_neg, add_comm]
    exact
      (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (x := -((I x : EReal))) (y := (φ x : EReal))
        (by simp) (by simp)).2 (by simp)
  rw [EReal.sub_nonneg (.inr hPoint_ne_top) (.inl hS_bot)]
  exact le_sSup ⟨x, rfl⟩

/-- Helper for Theorem 23.19: once the source-gap nonnegativity is available, coercing the tilted
rate back to `EReal` recovers the exact shifted gap `S - (φ x - I x)`. -/
private theorem tiltedRateFunction_coe_ereal_eq_sourceSup_sub
    (I : E → ENNReal) (φ : E → ℝ)
    (hS_bot :
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) ≠ ⊥)
    (x : E) :
    ((tiltedRateFunction I φ x : ENNReal) : EReal) =
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) -
        (((φ x : EReal) - (I x : EReal))) := by
  -- Proof comment: the previous lemma turns the `max 0 _` formula from
  -- `tiltedRateFunction_coe_ereal` into the exact source-gap identity.
  rw [tiltedRateFunction_coe_ereal, max_eq_right]
  exact sourceSup_sub_sourcePoint_nonneg (I := I) (φ := φ) hS_bot x

/-- Helper for Theorem 23.19: the tilted rate function is lower semicontinuous because it is the
composition of `toENNReal` with the lower semicontinuous extended-real gap
`S + (I - φ)`. -/
private theorem lowerSemicontinuous_tiltedRateFunction
    (I : E → ENNReal) (φ : E → ℝ)
    (hI_good : IsGoodRateFunction I) (hφ : Continuous φ) :
    LowerSemicontinuous (tiltedRateFunction I φ) := by
  let S : EReal := sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal)))
  by_cases hS_bot : S = ⊥
  · -- Proof comment: if `S = ⊥`, then every shifted gap is already `⊥`, so the tilted rate is
    -- identically `0` after applying `toENNReal`.
    have hZero : tiltedRateFunction I φ = fun _ : E ↦ (0 : ENNReal) := by
      funext x
      simp [tiltedRateFunction_def, S, hS_bot]
    rw [hZero]
    exact lowerSemicontinuous_const
  · have hI_ereal : LowerSemicontinuous fun x : E ↦ (I x : EReal) :=
      -- Proof comment: coerce the original good rate function to `EReal`.
      continuous_coe_ennreal_ereal.comp_lowerSemicontinuous hI_good.lowerSemicontinuous
        (fun _ _ hxy ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 hxy)
    have hNegPhi : LowerSemicontinuous fun x : E ↦ -((φ x : EReal)) :=
      -- Proof comment: the negated continuous potential is still continuous, hence lower
      -- semicontinuous.
      (continuous_neg.comp (continuous_coe_real_ereal.comp hφ)).lowerSemicontinuous
    have hShift :
        LowerSemicontinuous fun x : E ↦ (I x : EReal) + -((φ x : EReal)) := by
      -- Proof comment: add the coerced rate and the negated potential; addition is continuous at
      -- these points because the second summand is always a finite real.
      refine hI_ereal.add' hNegPhi ?_
      intro x
      exact EReal.continuousAt_add (by simp) (by simp)
    have hShift_ne_bot :
        ∀ x : E, (I x : EReal) + -((φ x : EReal)) ≠ ⊥ := by
      -- Proof comment: neither summand is `⊥`, so their sum cannot be `⊥`.
      intro x
      exact (EReal.add_ne_bot_iff.2 ⟨EReal.coe_ennreal_ne_bot (I x), by simp⟩)
    have hCore :
        LowerSemicontinuous fun x : E ↦ S + ((I x : EReal) + -((φ x : EReal))) := by
      -- Proof comment: now add the constant `S`; the only bad point for `EReal`-addition would
      -- be `(⊥, ⊤)`, excluded by `hS_bot`.
      refine lowerSemicontinuous_const.add' hShift ?_
      intro x
      exact EReal.continuousAt_add (.inr (hShift_ne_bot x)) (.inl hS_bot)
    have hCoreToENN :
        LowerSemicontinuous
          (fun x : E ↦ (S + ((I x : EReal) + -((φ x : EReal)))).toENNReal) := by
      -- Proof comment: apply the monotone continuous map `EReal.toENNReal` to the extended-real
      -- core.
      simpa [Function.comp] using
        (EReal.continuous_toENNReal.comp_lowerSemicontinuous hCore fun _ _ hxy ↦
          EReal.toENNReal_le_toENNReal hxy)
    have hRewrite :
        tiltedRateFunction I φ = fun x : E ↦ (S + ((I x : EReal) + -((φ x : EReal)))).toENNReal := by
      -- Proof comment: normalize the owner definition to the stable `S + (I - φ)` form used by
      -- `hCoreToENN`.
      funext x
      rw [tiltedRateFunction_def]
      change
        (S + -(((φ x : EReal) + -((I x : EReal))))).toENNReal =
          (S + ((I x : EReal) + -((φ x : EReal)))).toENNReal
      congr 1
      calc
        S + -(((φ x : EReal) + -((I x : EReal))))
          = S + (-((φ x : EReal)) - (-((I x : EReal)))) := by
              rw [EReal.neg_add (.inl (by simp)) (.inl (by simp))]
        _ = S + (-((φ x : EReal)) + (I x : EReal)) := by
              simp [sub_eq_add_neg]
        _ = S + ((I x : EReal) + -((φ x : EReal))) := by
              simp [add_assoc, add_left_comm, add_comm]
    -- Proof comment: rewrite `tiltedRateFunction` to the `EReal` core `S + (I - φ)` and compose
    -- with the monotone continuous map `EReal.toENNReal`.
    rw [hRewrite]
    exact hCoreToENN

/-- Helper for Theorem 23.19: the global source supremum cannot be `⊥`, because the original LDP
on `Set.univ` forces the rate to take some finite value, and that yields one finite source
point. -/
private theorem sourceSup_ne_bot_of_hasLargeDeviationsPrinciple
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) :
    sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) ≠ ⊥ := by
  have hClosedUniv :
      (0 : EReal) ≤ -sInf ((fun x ↦ (I x : EReal)) '' (Set.univ : Set E)) := by
    -- Proof comment: the original LDP upper bound on `Set.univ` compares the constant logarithmic
    -- mass `0` with the global infimum of the source rate.
    have hMassUniv :
        scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id Set.univ = fun _ : PositiveParameter ↦ 0 := by
      funext ε
      simp [scaledLogMassAlong_def]
    simpa [hMassUniv] using (hLDP.closed_upper_bound (C := Set.univ) isClosed_univ)
  have hRateFinite : ∃ x : E, I x ≠ ⊤ := by
    -- Proof comment: if every rate value were `⊤`, then the infimum on `Set.univ` would also be
    -- `⊤`, contradicting `hClosedUniv`.
    by_contra hAll
    push_neg at hAll
    have hNonempty : Nonempty E := (μ ⟨1, by simpa using zero_lt_one⟩).nonempty
    have hImageTop :
        ((fun x ↦ (I x : EReal)) '' (Set.univ : Set E)) = ({(⊤ : EReal)} : Set EReal) := by
      ext y
      constructor
      · rintro ⟨x, -, rfl⟩
        simp [hAll x]
      · intro hy
        rcases hNonempty with ⟨x⟩
        simp at hy
        subst hy
        exact ⟨x, Set.mem_univ x, by simp [hAll x]⟩
    have hInfTop :
        sInf ((fun x ↦ (I x : EReal)) '' (Set.univ : Set E)) = (⊤ : EReal) := by
      rw [hImageTop]
      simp
    have hClosedUnivTop : (0 : EReal) ≤ -(⊤ : EReal) := by
      rw [← hInfTop]
      exact hClosedUniv
    simpa using hClosedUnivTop
  rcases hRateFinite with ⟨x, hx⟩
  have hPoint_ne_bot : ((φ x : EReal) - (I x : EReal)) ≠ ⊥ := by
    -- Proof comment: a finite real minus a finite-or-`∞` rate is `⊥` only when the rate itself is
    -- `⊤`, ruled out by `hx`.
    simp [sub_eq_add_neg, hx]
  -- Proof comment: the pointwise source value at `x` belongs to the defining range of the
  -- supremum, so that supremum cannot drop to `⊥`.
  intro hS_bot
  have hPoint_le :
      ((φ x : EReal) - (I x : EReal)) ≤
        sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) := by
    exact le_sSup ⟨x, rfl⟩
  have : ((φ x : EReal) - (I x : EReal)) = ⊥ := by
    exact le_antisymm (by simpa [hS_bot] using hPoint_le) bot_le
  exact hPoint_ne_bot this

/-- Helper for Theorem 23.19: after fixing `S ≠ ⊥`, the negative infimum of the tilted-rate image
over a set is the source supremum on that set shifted by `-S`. -/
private theorem neg_sInf_tiltedRateImage_eq_sourceSup_sub
    (I : E → ENNReal) (φ : E → ℝ) (s : Set E)
    (hS_ne_bot :
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) ≠ ⊥)
    (hS_ne_top :
      sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) ≠ ⊤) :
    -sInf ((fun x ↦ ((tiltedRateFunction I φ x : ENNReal) : EReal)) '' s) =
      sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' s)) -
        sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal))) := by
  let S : EReal := sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal)))
  let sourceImage : Set EReal := ((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' s)
  have hImage :
      ((fun x ↦ ((tiltedRateFunction I φ x : ENNReal) : EReal)) '' s) = {S} - sourceImage := by
    -- Proof comment: pointwise, the tilted rate is exactly the translated gap `S - (φ - I)`.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Set.mem_sub.2 ?_
      refine ⟨S, by simp, ((φ x : EReal) - (I x : EReal)), ?_, ?_⟩
      · exact ⟨x, hx, rfl⟩
      · simpa [S] using
          (tiltedRateFunction_coe_ereal_eq_sourceSup_sub
            (I := I) (φ := φ) hS_ne_bot x).symm
    · intro hy
      rcases Set.mem_sub.1 hy with ⟨z, hz, w, hw, hEq⟩
      have hzS : z = S := by simpa using hz
      rcases hw with ⟨x, hx, rfl⟩
      subst hzS
      refine ⟨x, hx, ?_⟩
      calc
        ((tiltedRateFunction I φ x : ENNReal) : EReal)
          = S - (((φ x : EReal) - (I x : EReal))) := by
              simpa [S] using
                (tiltedRateFunction_coe_ereal_eq_sourceSup_sub
                  (I := I) (φ := φ) hS_ne_bot x)
        _ = y := hEq
  let shiftedImage : Set EReal := (fun a : EReal ↦ S - a) '' sourceImage
  have hShifted : {S} - sourceImage = shiftedImage := by
    simpa [shiftedImage] using (Set.singleton_sub (a := S) (t := sourceImage))
  have hInfShifted : sInf shiftedImage = S - sSup sourceImage := by
    have hLower :
        S - sSup sourceImage ≤ sInf shiftedImage := by
      refine le_sInf ?_
      rintro y ⟨a, ha, rfl⟩
      exact EReal.sub_le_sub le_rfl (le_sSup ha)
    have hSupLe : sSup sourceImage ≤ S - sInf shiftedImage := by
      refine sSup_le ?_
      intro a ha
      have hInfLe : sInf shiftedImage ≤ S - a := by
        exact sInf_le ⟨a, ha, rfl⟩
      exact
        (EReal.le_sub_iff_add_le (a := a) (b := sInf shiftedImage) (c := S)
          (Or.inr hS_ne_bot) (Or.inr hS_ne_top)).2 <| by
            have hAdd :
                sInf shiftedImage + a ≤ S := by
              exact
                (EReal.le_sub_iff_add_le (a := sInf shiftedImage) (b := a) (c := S)
                  (Or.inr hS_ne_bot) (Or.inr hS_ne_top)).1 hInfLe
            simpa [add_comm] using hAdd
    have hUpper :
        sInf shiftedImage ≤ S - sSup sourceImage := by
      exact
        (EReal.le_sub_iff_add_le (a := sInf shiftedImage) (b := sSup sourceImage) (c := S)
          (Or.inr hS_ne_bot) (Or.inr hS_ne_top)).2 <| by
            have hAdd :
                sSup sourceImage + sInf shiftedImage ≤ S := by
              exact
                (EReal.le_sub_iff_add_le (a := sSup sourceImage) (b := sInf shiftedImage) (c := S)
                  (Or.inr hS_ne_bot) (Or.inr hS_ne_top)).1 hSupLe
            simpa [add_comm] using hAdd
    exact le_antisymm hUpper hLower
  -- Proof comment: once the image is written as a translated source image, the infimum is the
  -- translated supremum `S - sSup(sourceImage)`, and negating that difference yields the desired
  -- `sourceSup - S` form.
  calc
    -sInf ((fun x ↦ ((tiltedRateFunction I φ x : ENNReal) : EReal)) '' s)
      = -sInf ({S} - sourceImage) := by rw [hImage]
    _ = -sInf shiftedImage := by rw [hShifted]
    _ = -(S - sSup sourceImage) := by rw [hInfShifted]
    _ = sSup sourceImage - S := by
          calc
            -(S - sSup sourceImage) = -S + sSup sourceImage := by
              exact
                EReal.neg_sub (x := S) (y := sSup sourceImage)
                  (Or.inl hS_ne_bot) (Or.inl hS_ne_top)
            _ = sSup sourceImage - S := by
              rw [add_comm]
              rfl
    _ = sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' s)) - S := by
      simp [sourceImage]

-- Proof sketch: apply Varadhan's lemma to the logarithmic normalizing constants of the tilted
-- family, rewrite the logarithmic probabilities of open and closed sets under the tilted laws as
-- the original logarithmic probabilities shifted by the normalizer, and identify the resulting
-- bounds with the rate `tiltedRateFunction I φ`.
/-- Theorem 23.19: if `μ_ε` satisfies an LDP with good rate function `I`, `φ` is continuous and
satisfies the tail condition (23.17), then the exponentially tilted laws
`μ_ε^φ(dx) ∝ exp (φ x / ε) μ_ε(dx)` satisfy an LDP with tilted rate function
`tiltedRateFunction I φ`, i.e. with rate
`x ↦ sup_z (φ z - I z) - (φ x - I x)` from (23.21). -/
theorem hasLargeDeviationsPrinciple_tilted
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hI_good : IsGoodRateFunction I)
    (hLDP : HasLargeDeviationsPrinciple μ I)
    (hφ : Continuous φ)
    (h_integrable :
      ∀ ε : PositiveParameter, Integrable (fun x ↦ Real.exp (φ x / (ε : ℝ))) (μ ε : Measure E))
    (h_tail :
      sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log
              (∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict
                {x | M.1 ≤ φ x})))
          positiveParameterFilter) = ⊥) :
    HasLargeDeviationsPrinciple
      (tiltedProbabilityMeasureFamily μ φ h_integrable)
      (tiltedRateFunction I φ) := by
  -- Route correction: the direct `varadhan_lemma` route is blocked because the public theorem in
  -- 23.17 requires `[BorelSpace E]`, while the current target is intentionally stated over an
  -- arbitrary `MeasurableSpace E`.
  let S : EReal := sSup (Set.range fun z : E ↦ ((φ z : EReal) - (I z : EReal)))
  let numerator : Set E → PositiveParameter → EReal := fun s ε ↦
    ((ε : ℝ) : EReal) *
      ENNReal.log
        (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict s))
  let normalizer : PositiveParameter → EReal := fun ε ↦
    ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε)
  let tiltedMass : Set E → PositiveParameter → EReal := fun s ε ↦
    scaledLogMassAlong
      (fun ε ↦ (tiltedProbabilityMeasureFamily μ φ h_integrable ε : Measure E)) id s ε
  have hTiltedMass :
      ∀ s : Set E, tiltedMass s = fun ε ↦ numerator s ε + (-normalizer ε) := by
    intro s
    -- Proof comment: the tilted logarithmic mass is the restricted Laplace numerator minus the
    -- common normalizing constant from the tilt.
    funext ε
    simpa [tiltedMass, numerator, normalizer, sub_eq_add_neg] using
      (tiltedScaledLogMass_eq_restrictedLaplaceExponent_sub_normalizer
        (μ := μ) (φ := φ) h_integrable (s := s) (ε := ε))
  have hNumeratorLimsup_ne_top :
      ∀ C : Set E, Filter.limsup (numerator C) positiveParameterFilter ≠ ⊤ := by
    intro C
    obtain ⟨M, hTailM⟩ :
        ∃ M : {M : ℝ // 0 < M},
          Filter.limsup (numerator {x | M.1 ≤ φ x}) positiveParameterFilter < (0 : EReal) := by
      -- Proof comment: choose one positive tail level whose restricted numerator limsup is already
      -- strictly negative; this supplies a finite global upper cutoff for the numerator.
      by_contra hM
      push_neg at hM
      have hZeroInf :
          (0 : EReal) ≤
            sInf
              (Set.range fun M : {M : ℝ // 0 < M} ↦
                Filter.limsup (numerator {x | M.1 ≤ φ x}) positiveParameterFilter) := by
        refine le_sInf ?_
        rintro z ⟨M, rfl⟩
        exact hM M
      simpa [numerator, h_tail] using hZeroInf
    let partSet : Fin 3 → Set E
      | 0 => C ∩ {x | φ x ≤ 0}
      | 1 => C ∩ φ ⁻¹' Set.Icc 0 M.1
      | _ => C ∩ {x | M.1 ≤ φ x}
    let part : Fin 3 → PositiveParameter → ℝ≥0∞ := fun i ε ↦
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict (partSet i))
    have hCoverOnC :
        C ⊆ ⋃ i ∈ ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)), partSet i := by
      -- Proof comment: split `C` into the left strip `φ ≤ 0`, the bounded middle strip
      -- `0 ≤ φ ≤ M`, and the upper tail `M ≤ φ`.
      intro x hxC
      by_cases hLeft : φ x ≤ 0
      · exact Set.mem_iUnion.2 ⟨0, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, hLeft⟩⟩⟩
      · by_cases hMid : φ x ≤ M.1
        · have hxIcc : φ x ∈ Set.Icc (0 : ℝ) M.1 := ⟨(lt_of_not_ge hLeft).le, hMid⟩
          exact Set.mem_iUnion.2 ⟨1, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, hxIcc⟩⟩⟩
        · exact Set.mem_iUnion.2 ⟨2, Set.mem_iUnion.2 ⟨by simp, ⟨hxC, le_of_not_ge hMid⟩⟩⟩
    have hIntegralBound :
        ∀ ε : PositiveParameter,
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C) ≤
            Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
      intro ε
      have hMeasure :
          (μ ε : Measure E).restrict C ≤
            Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i) := by
        -- Proof comment: the restriction to `C` is dominated by the sum of the three strip
        -- restrictions.
        exact restrict_le_sum_restrict_of_subset_iUnion
          (ν := (μ ε : Measure E)) (A := C) (s := Finset.univ) (B := partSet) hCoverOnC
      have hIntegral :
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C) ≤
            ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
              (Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)) := by
        exact lintegral_mono' hMeasure le_rfl
      calc
        ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict C)
          ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
              (Finset.univ.sum fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)) := hIntegral
        _ = Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
          simpa [part] using
            (MeasureTheory.lintegral_finset_sum_measure
              (s := Finset.univ)
              (f := fun x : E ↦ ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))))
              (μ := fun i : Fin 3 ↦ (μ ε : Measure E).restrict (partSet i)))
    have hPointwiseLog :
        ∀ ε : PositiveParameter,
          numerator C ε ≤
            ((ε : ℝ) : EReal) * ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε) := by
      intro ε
      have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
        exact_mod_cast le_of_lt ε.2
      simpa [numerator] using
        (mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hIntegralBound ε)) hε)
    have hPart0 :
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (part 0 ε))
            positiveParameterFilter ≤
          (0 : EReal) := by
      -- Proof comment: the left strip has the deterministic upper control `φ ≤ 0`.
      simpa [part, partSet] using
        (restrictedLeftTailLimsup_le (μ := μ) (φ := φ) (C := C) (R := 0))
    have hPart1Pointwise :
        ∀ ε : PositiveParameter,
          ((ε : ℝ) : EReal) * ENNReal.log (part 1 ε) ≤ (M.1 : EReal) := by
      intro ε
      calc
        ((ε : ℝ) : EReal) * ENNReal.log (part 1 ε)
          ≤ (M.1 : EReal) +
              scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (partSet 1) ε := by
                simpa [part, partSet] using
                  (restrictedLaplaceExponent_le_upperControlOnSet
                    (μ := μ) (φ := φ) (A := partSet 1) (c := M.1)
                    (fun x hx ↦ by
                      have hxIcc : (0 : ℝ) ≤ φ x ∧ φ x ≤ M.1 := by
                        simpa [Set.mem_preimage, Set.mem_Icc] using hx.2
                      exact hxIcc.2) ε)
        _ ≤ (M.1 : EReal) + 0 := by
          gcongr
          exact scaledLogMassAlong_nonpos_of_probability (μ := μ) (s := partSet 1) ε
        _ = (M.1 : EReal) := by simp
    have hPart1 :
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (part 1 ε))
            positiveParameterFilter ≤
          (M.1 : EReal) := by
      exact
        (Filter.limsup_le_limsup (Eventually.of_forall hPart1Pointwise)).trans <| by
          simp
    have hPart2 :
        Filter.limsup
            (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε))
            positiveParameterFilter < (0 : EReal) := by
      have hPointwisePart2 :
          ∀ ε : PositiveParameter,
            ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε) ≤ numerator {x | M.1 ≤ φ x} ε := by
        intro ε
        have hIntegral :
            part 2 ε ≤
              ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
                ((μ ε : Measure E).restrict {x | M.1 ≤ φ x}) := by
          -- Proof comment: the tail inside `C` is bounded by the global tail selected by `M`.
          exact lintegral_mono'
            (Measure.restrict_mono (by intro x hx; exact hx.2) le_rfl) le_rfl
        have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
          exact_mod_cast le_of_lt ε.2
        simpa [numerator, part] using
          (mul_le_mul_of_nonneg_left (ENNReal.log_le_log hIntegral) hε)
      have hTailLe :
          Filter.limsup
              (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε))
              positiveParameterFilter ≤
            Filter.limsup (numerator {x | M.1 ≤ φ x}) positiveParameterFilter := by
        exact Filter.limsup_le_limsup (Eventually.of_forall hPointwisePart2)
      exact lt_of_le_of_lt hTailLe hTailM
    have hM_nonneg : (0 : EReal) ≤ (M.1 : EReal) := by
      exact_mod_cast M.2.le
    have hSumBound :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
            positiveParameterFilter ≤
          (M.1 : EReal) := by
      calc
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
            positiveParameterFilter
          ≤
            ⨆ i ∈ (Finset.univ : Finset (Fin 3)),
              Filter.limsup
                (fun ε : PositiveParameter ↦ ((ε : ℝ) : EReal) * ENNReal.log (part i ε))
                positiveParameterFilter :=
          scaledLogFinsetSumLimsup_le_iSup (s := Finset.univ) (u := part)
        _ ≤ (M.1 : EReal) := by
          refine iSup_le ?_
          intro i
          refine iSup_le ?_
          intro hi
          fin_cases i
          · exact hPart0.trans hM_nonneg
          · exact hPart1
          · exact hPart2.le.trans hM_nonneg
    have hNumeratorBound :
        Filter.limsup (numerator C) positiveParameterFilter ≤ (M.1 : EReal) := by
      calc
        Filter.limsup (numerator C) positiveParameterFilter
          ≤ Filter.limsup
              (fun ε : PositiveParameter ↦
                ((ε : ℝ) : EReal) * ENNReal.log (Finset.univ.sum fun i : Fin 3 ↦ part i ε))
              positiveParameterFilter := by
                exact Filter.limsup_le_limsup (Eventually.of_forall hPointwiseLog)
        _ ≤ (M.1 : EReal) := hSumBound
    exact ne_of_lt (lt_of_le_of_lt hNumeratorBound (by simp))
  have hOpenNumerator :
      ∀ {U : Set E}, IsOpen U →
        sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' U)) ≤
          Filter.liminf (numerator U) positiveParameterFilter := by
    intro U hU
    -- Proof comment: the numerator lower bound is now available directly on restricted measures.
    simpa using
      (sourceSupOnOpen_le_restrictedLaplaceLiminf
        (μ := μ) (I := I) (φ := φ) hLDP hφ h_integrable (U := U) hU)
  have hClosedNumerator :
      ∀ {C : Set E}, IsClosed C →
        Filter.limsup (numerator C) positiveParameterFilter ≤
          sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) := by
    intro C hC
    -- Proof comment: the closed numerator upper bound is assembled by the left/middle/tail
    -- decomposition proved above on restricted measures.
    simpa using
      (restrictedLaplaceLimsup_le_sourceSupOnClosed
        (μ := μ) (I := I) (φ := φ) hLDP hφ hC h_tail)
  have hNormalizer :
      Tendsto
          normalizer positiveParameterFilter (𝓝 S) := by
    have hLowerSup :
        S ≤ Filter.liminf normalizer positiveParameterFilter := by
      -- Proof comment: specialize the open numerator lower bound to `Set.univ`.
      simpa [S, normalizer, numerator, varadhanLaplaceFunctional_def] using
        (hOpenNumerator (U := Set.univ) isOpen_univ)
    have hUpperSup :
        Filter.limsup normalizer positiveParameterFilter ≤ S := by
      -- Proof comment: specialize the closed numerator upper bound to `Set.univ`.
      simpa [S, normalizer, numerator, varadhanLaplaceFunctional_def] using
        (hClosedNumerator (C := Set.univ) isClosed_univ)
    -- Proof comment: the numerator lower and upper bounds agree on `Set.univ`, so the common
    -- logarithmic normalizer converges to `S`.
    exact tendsto_of_le_liminf_of_limsup_le hLowerSup hUpperSup
  have hS_ne_bot : S ≠ ⊥ := by
    -- Proof comment: the source supremum is nondegenerate, so the tilted rate can be rewritten
    -- without the intermediate `max 0` branch.
    simpa [S] using
      (sourceSup_ne_bot_of_hasLargeDeviationsPrinciple
        (μ := μ) (I := I) (φ := φ) hLDP)
  have hNormalizerLiminf :
      Filter.liminf normalizer positiveParameterFilter = S := by
    -- Proof comment: convergence of the normalizer identifies both one-sided asymptotic bounds
    -- with the common limit `S`.
    exact Filter.Tendsto.liminf_eq hNormalizer
  have hNormalizerLimsup :
      Filter.limsup normalizer positiveParameterFilter = S := by
    exact Filter.Tendsto.limsup_eq hNormalizer
  have hNormalizer_ne_top :
      Filter.limsup normalizer positiveParameterFilter ≠ ⊤ := by
    -- Proof comment: the three-piece decomposition above also bounds the full normalizer limsup by
    -- a finite real cutoff, so the limit `S` cannot be `⊤`.
    simpa [normalizer, numerator, varadhanLaplaceFunctional_def] using
      hNumeratorLimsup_ne_top Set.univ
  have hS_ne_top : S ≠ ⊤ := by
    simpa [hNormalizerLimsup] using hNormalizer_ne_top
  have hNegNormalizerLiminf :
      Filter.liminf (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter = -S := by
    -- Proof comment: negating the convergent normalizer swaps `limsup` and `liminf`.
    change Filter.liminf (-normalizer) positiveParameterFilter = -S
    rw [EReal.liminf_neg, hNormalizerLimsup]
  have hNegNormalizerLimsup :
      Filter.limsup (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter = -S := by
    change Filter.limsup (-normalizer) positiveParameterFilter = -S
    rw [EReal.limsup_neg, hNormalizerLiminf]
  refine
    { lowerSemicontinuous :=
        lowerSemicontinuous_tiltedRateFunction (I := I) (φ := φ) hI_good hφ
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · intro U hU
    -- Proof comment: rewrite the tilted logarithmic mass as numerator minus normalizer, then add
    -- the open numerator lower bound to the limiting negative normalizer.
    calc
      -sInf ((fun x ↦ ((tiltedRateFunction I φ x : ENNReal) : EReal)) '' U)
        = sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' U)) - S := by
            simpa [S] using
              (neg_sInf_tiltedRateImage_eq_sourceSup_sub
                (I := I) (φ := φ) (s := U) hS_ne_bot hS_ne_top)
      _ = sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' U)) + (-S) := by
            rw [sub_eq_add_neg]
      _ = sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' U)) +
            Filter.liminf (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter := by
            rw [hNegNormalizerLiminf]
      _ ≤ Filter.liminf (numerator U) positiveParameterFilter +
            Filter.liminf (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter := by
            gcongr
            exact hOpenNumerator hU
      _ ≤ Filter.liminf (fun ε : PositiveParameter ↦ numerator U ε + (-normalizer ε))
            positiveParameterFilter := by
            simpa using
              (EReal.le_liminf_add
                (u := numerator U) (v := fun ε : PositiveParameter ↦ -normalizer ε)
                (f := positiveParameterFilter))
      _ = Filter.liminf (tiltedMass U) positiveParameterFilter := by
            rw [(hTiltedMass U).symm]
  · intro C hC
    have hClosedAdd :
        Filter.limsup (fun ε : PositiveParameter ↦ numerator C ε + (-normalizer ε))
            positiveParameterFilter ≤
          Filter.limsup (numerator C) positiveParameterFilter +
            Filter.limsup (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter := by
      -- Proof comment: after isolating one finite tail cutoff, the closed numerator limsup is not
      -- `⊤`, so `EReal.limsup_add_le` applies to the numerator-minus-normalizer decomposition.
      refine EReal.limsup_add_le ?_ ?_
      · right
        rw [hNegNormalizerLimsup]
        simpa [hS_ne_bot]
      · left
        exact hNumeratorLimsup_ne_top C
    -- Proof comment: combine the closed numerator upper bound with the limiting negative
    -- normalizer and then rewrite the right-hand side back to the tilted-rate image.
    calc
      Filter.limsup (tiltedMass C) positiveParameterFilter
        = Filter.limsup (fun ε : PositiveParameter ↦ numerator C ε + (-normalizer ε))
            positiveParameterFilter := by
              rw [hTiltedMass C]
      _ ≤ Filter.limsup (numerator C) positiveParameterFilter +
            Filter.limsup (fun ε : PositiveParameter ↦ -normalizer ε) positiveParameterFilter :=
          hClosedAdd
      _ = Filter.limsup (numerator C) positiveParameterFilter - S := by
            rw [hNegNormalizerLimsup, sub_eq_add_neg]
      _ ≤ sSup (((fun x ↦ ((φ x : EReal) - (I x : EReal))) '' C)) - S := by
            simpa [add_comm, sub_eq_add_neg] using
              add_le_add_left (hClosedNumerator hC) (-S)
      _ = -sInf ((fun x ↦ ((tiltedRateFunction I φ x : ENNReal) : EReal)) '' C) := by
            symm
            simpa [S] using
              (neg_sInf_tiltedRateImage_eq_sourceSup_sub
                (I := I) (φ := φ) (s := C) hS_ne_bot hS_ne_top)

end ProbabilityTheory
