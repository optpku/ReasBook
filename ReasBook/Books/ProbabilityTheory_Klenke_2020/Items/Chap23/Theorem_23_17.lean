/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_9

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory Topology
open scoped Topology NNReal ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E]

/-- Helper for Theorem 23.17: the positive-parameter filter is nontrivial because the right-sided
neighborhoods of `0` contain positive real numbers. -/
private instance positiveParameterFilter_neBot :
    NeBot (positiveParameterFilter : Filter PositiveParameter) := by
  -- Reindex the nontrivial right-neighborhood filter at `0` along the coercion
  -- `PositiveParameter → ℝ`.
  rw [positiveParameterFilter]
  exact (show NeBot (𝓝[>] (0 : ℝ)) from inferInstance).comap_of_range_mem (by
    simpa [PositiveParameter, Subtype.range_coe] using
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)))

/-- Helper for Theorem 23.17: coercing a positive parameter to `ℝ` sends the chapter's
positive-parameter filter back to the standard right-neighborhood filter at `0`. -/
private theorem map_positiveParameterFilter :
    Filter.map ((↑) : PositiveParameter → ℝ) positiveParameterFilter = 𝓝[>] (0 : ℝ) := by
  -- Proof comment: `positiveParameterFilter` is defined as the pullback of `𝓝[>] 0` along the
  -- coercion, so mapping forward by that same coercion recovers the original filter.
  rw [positiveParameterFilter]
  refine Filter.map_comap_of_mem ?_
  simpa [PositiveParameter, Subtype.range_coe] using
    (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))

/-- The exponential Laplace functional `∫ exp (φ / ε) dμ_ε` appearing in Varadhan's lemma. -/
def varadhanLaplaceFunctional
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂(μ ε : Measure E)

-- Proof sketch: unfold `varadhanLaplaceFunctional`.
/-- Unfolding `varadhanLaplaceFunctional` gives the exponential integral
`∫ exp (φ(x) / ε) μ_ε(dx)` as an `ℝ≥0∞`-valued `lintegral`. -/
theorem varadhanLaplaceFunctional_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (ε : PositiveParameter) :
    varadhanLaplaceFunctional μ φ ε =
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂(μ ε : Measure E) := by
  -- The declaration is definitional, so unfolding the owner gives the target integral verbatim.
  rfl

/-- The tail-truncated exponential Laplace functional over the set `{x | M ≤ φ x}`. -/
def varadhanTailLaplaceFunctional
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | M ≤ φ x})

-- Proof sketch: unfold `varadhanTailLaplaceFunctional`.
/-- Unfolding `varadhanTailLaplaceFunctional` gives the exponential integral restricted to the tail
set `{x | M ≤ φ x}`. -/
theorem varadhanTailLaplaceFunctional_def
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (M : ℝ) (ε : PositiveParameter) :
    varadhanTailLaplaceFunctional μ φ M ε =
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | M ≤ φ x}) :=
  by
  -- The tail functional was defined by this restricted `lintegral`, so the statement is `rfl`.
  rfl

/-- Helper for Theorem 23.17: continuity gives an open neighborhood on which `φ` stays above the
chosen lower threshold `φ x - δ`. -/
private theorem exists_openLowerControlNeighborhood
    [TopologicalSpace E]
    [BorelSpace E]
    {φ : E → ℝ} (hφ : Continuous φ) {x : E} {δ : ℝ} (hδ : 0 < δ) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, φ x - δ ≤ φ y := by
  refine ⟨φ ⁻¹' Set.Ioi (φ x - δ), hφ.isOpen_preimage _ isOpen_Ioi, ?_, ?_⟩
  · -- Proof comment: `φ x` is strictly larger than the threshold `φ x - δ`, so `x` belongs to
    -- the chosen preimage neighborhood.
    simp [sub_lt_self_iff, hδ]
  · -- Proof comment: membership in the preimage is exactly the desired lower bound on `φ`.
    intro y hy
    exact le_of_lt hy

/-- Helper for Theorem 23.17: a pointwise lower control `c ≤ φ` on a measurable set `U` turns the
restricted mass of `U` into a pointwise lower bound for the Laplace exponent. -/
private theorem lowerControlOnSet_le_laplaceExponent
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) {U : Set E} (hU : MeasurableSet U) {c : ℝ}
    (hLower : ∀ y ∈ U, c ≤ φ y) :
    ∀ ε : PositiveParameter,
      (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε ≤
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
  intro ε
  have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
    exact_mod_cast le_of_lt ε.2
  have hPointwise :
      ∫⁻ y, U.indicator (fun _ : E ↦ ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) y ∂(μ ε : Measure E) ≤
        varadhanLaplaceFunctional μ φ ε := by
    -- Proof comment: on `U` the integrand is bounded below by `exp (c / ε)`, and outside `U` the
    -- indicator vanishes.
    rw [varadhanLaplaceFunctional_def]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ U
    · have hyc : c / (ε : ℝ) ≤ φ y / (ε : ℝ) := by
        exact (div_le_div_iff_of_pos_right ε.2).2 (hLower y hy)
      simp [hy, ENNReal.ofReal_le_ofReal, Real.exp_le_exp.mpr hyc]
    · simp [hy]
  have hIndicator :
      ∫⁻ y, U.indicator (fun _ : E ↦ ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) y ∂(μ ε : Measure E) =
        ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U) := by
    -- Proof comment: integrating the constant indicator over `U` is the restricted constant
    -- integral, hence the constant times the mass of `U`.
    rw [lintegral_indicator hU]
    simp [Measure.restrict_apply]
  have hLog :
      ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U)) ≤
        ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
    exact ENNReal.log_le_log (hIndicator.symm ▸ hPointwise)
  have hMul :
      ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) U)) ≤
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := by
    exact mul_le_mul_of_nonneg_left hLog hε
  have hcancelReal : (ε : ℝ) * (c / (ε : ℝ)) = c := by
    field_simp [show (ε : ℝ) ≠ 0 by exact ne_of_gt ε.2]
  have hFirstTerm :
      ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) = (c : EReal) := by
    rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), ← EReal.coe_mul, Real.log_exp, hcancelReal]
  -- Proof comment: after taking logarithms, the exponential prefactor contributes exactly `c`.
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
    _ ≤ ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) := hMul

/-- Helper for Theorem 23.17: enlarging the underlying set can only increase the scaled
logarithmic mass because both measure and `ENNReal.log` are monotone. -/
private theorem scaledLogMassAlong_mono {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) {s t : Set E}
    (hst : s ⊆ t) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ scaledLogMassAlong μ ε t i := by
  -- Proof comment: event inclusion gives `μ i s ≤ μ i t`; applying `log` and the positive scale
  -- factor preserves the inequality.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hε : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (measure_mono hst)) hε

/-- Helper for Theorem 23.17: every scaled logarithmic mass is nonpositive for a probability
family, because every event has mass at most `1`. -/
private theorem scaledLogMassAlong_nonpos_of_probability
    (μ : PositiveProbabilityFamily E) {s : Set E} (ε : PositiveParameter) :
    scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id s ε ≤ 0 := by
  -- Proof comment: probability masses are bounded by `1`, hence their logarithms are nonpositive,
  -- and the positive prefactor `ε` preserves that sign.
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

/-- Helper for Theorem 23.17: a pointwise upper control `φ ≤ c` on a measurable set `A` bounds
the restricted Laplace exponent by `c` plus the scaled logarithmic mass of `A`. -/
private theorem upperControlOnSet_laplaceExponent_le
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) {A : Set E} (hA : MeasurableSet A) {c : ℝ}
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
      ∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A) ≤
        ∫⁻ y, A.indicator (fun _ : E ↦ ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) y
          ∂(μ ε : Measure E) := by
    -- Proof comment: on `A` the exponential integrand is bounded above by the constant
    -- `exp (c / ε)`, and outside `A` the indicator vanishes.
    rw [← lintegral_indicator hA]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ A
    · have hyc : φ y / (ε : ℝ) ≤ c / (ε : ℝ) := by
        exact (div_le_div_iff_of_pos_right ε.2).2 (hUpper y hy)
      simp [hy, ENNReal.ofReal_le_ofReal, Real.exp_le_exp.mpr hyc]
    · simp [hy]
  have hIndicator :
      ∫⁻ y, A.indicator (fun _ : E ↦ ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) y ∂(μ ε : Measure E) =
        ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A) := by
    -- Proof comment: integrating a constant indicator over `A` gives the constant times the mass
    -- of `A`.
    rw [lintegral_indicator hA]
    simp [Measure.restrict_apply]
  have hLog :
      ENNReal.log
          (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A)) ≤
        ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A)) := by
    exact hIndicator.symm ▸ ENNReal.log_le_log hPointwise
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
  -- Proof comment: after taking logarithms, the exponential prefactor contributes exactly `c`,
  -- leaving the scaled logarithmic mass of `A`.
  calc
    ((ε : ℝ) : EReal) *
        ENNReal.log
          (∫⁻ y, ENNReal.ofReal (Real.exp (φ y / (ε : ℝ))) ∂((μ ε : Measure E).restrict A))
      ≤ ((ε : ℝ) : EReal) *
          ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ))) * ((μ ε : Measure E) A)) := hMul
    _ = ((ε : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal (Real.exp (c / (ε : ℝ)))) +
          ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) A) := by
            rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hε (by simp)]
    _ = (c : EReal) + ((ε : ℝ) : EReal) * ENNReal.log ((μ ε : Measure E) A) := by
          rw [hFirstTerm]
    _ = (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id A ε := by
          simp [scaledLogMassAlong_def]

/-- Helper for Theorem 23.17: an open neighborhood on which `φ` is bounded below yields the
corresponding lower bound for the liminf Laplace exponent via the LDP open lower bound. -/
private theorem laplaceLiminfLowerBound_of_openLowerControl
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) {x : E} {U : Set E}
    (hU : IsOpen U) (hxU : x ∈ U) {c : ℝ} (hLower : ∀ y ∈ U, c ≤ φ y) :
    (c : EReal) - (I x : EReal) ≤
      Filter.liminf
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
        positiveParameterFilter := by
  have hOpenLower :
      -sInf ((fun y ↦ (I y : EReal)) '' U) ≤
        Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U)
          positiveParameterFilter := by
    -- Proof comment: this is exactly the open-set lower bound from the assumed LDP.
    simpa using hLDP.open_lower_bound (U := U) hU
  have hsInf_le :
      sInf ((fun y ↦ (I y : EReal)) '' U) ≤ (I x : EReal) := by
    -- Proof comment: the center point `x` lies in `U`, so its value bounds the infimum from
    -- above.
    exact sInf_le ⟨x, hxU, rfl⟩
  have hNeg :
      -(I x : EReal) ≤ -sInf ((fun y ↦ (I y : EReal)) '' U) := by
    exact EReal.neg_le_neg_iff.2 hsInf_le
  have hLowerPointwise :
      ∀ ε : PositiveParameter,
        (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε ≤
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε) :=
    lowerControlOnSet_le_laplaceExponent (μ := μ) (φ := φ) hU.measurableSet hLower
  have hLiminfAdd :
      (c : EReal) +
          Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U)
            positiveParameterFilter ≤
        Filter.liminf
          (fun ε : PositiveParameter ↦
            (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε)
          positiveParameterFilter := by
    simpa using
      (EReal.le_liminf_add
        (u := fun _ : PositiveParameter ↦ (c : EReal))
        (v := scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U)
        (f := positiveParameterFilter))
  have hLiminfMono :
      Filter.liminf
          (fun ε : PositiveParameter ↦
            (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε)
          positiveParameterFilter ≤
        Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
          positiveParameterFilter := by
    exact liminf_le_liminf <| Eventually.of_forall hLowerPointwise
  -- Proof comment: add the open-set LDP bound to the deterministic contribution `c`, then compare
  -- with the liminf of the full Laplace exponent.
  calc
    (c : EReal) - (I x : EReal) = (c : EReal) + (-(I x : EReal)) := by
      rw [sub_eq_add_neg]
    _ ≤ (c : EReal) + (-sInf ((fun y ↦ (I y : EReal)) '' U)) := by
      gcongr
    _ ≤ (c : EReal) +
          Filter.liminf (scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U)
            positiveParameterFilter := by
      gcongr
    _ ≤ Filter.liminf
          (fun ε : PositiveParameter ↦
            (c : EReal) + scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id U ε)
          positiveParameterFilter := hLiminfAdd
    _ ≤ Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
          positiveParameterFilter := hLiminfMono

/-- Helper for Theorem 23.17: splitting the Laplace integral at the cutoff `M` separates the
bounded part `{φ < M}` from the tail part `{M ≤ φ}`. -/
private theorem varadhanLaplaceFunctional_splitAt
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (φ : E → ℝ) (hφ : Continuous φ) (M : ℝ)
    (ε : PositiveParameter) :
    varadhanLaplaceFunctional μ φ ε =
      ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | φ x < M}) +
        varadhanTailLaplaceFunctional μ φ M ε := by
  let s : Set E := {x | φ x < M}
  have hs : MeasurableSet s := (hφ.isOpen_preimage _ isOpen_Iio).measurableSet
  have hcompl : sᶜ = {x | M ≤ φ x} := by
    ext x
    simp [s]
  -- Proof comment: decompose the measure into the restriction to `s` and its complement, then
  -- identify the complement with the tail region.
  calc
    varadhanLaplaceFunctional μ φ ε
        = ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂
            (((μ ε : Measure E).restrict s) + ((μ ε : Measure E).restrict sᶜ)) := by
              rw [varadhanLaplaceFunctional_def, Measure.restrict_add_restrict_compl hs]
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict s) +
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict sᶜ) := by
            rw [lintegral_add_measure]
    _ = ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | φ x < M}) +
          varadhanTailLaplaceFunctional μ φ M ε := by
            simp [s, hcompl, varadhanTailLaplaceFunctional_def]

/-- Helper for Theorem 23.17: the scaled logarithmic mass of a closed set under the pushforward
law of `φ` is exactly the scaled logarithmic mass of its preimage under the original law. -/
private theorem scaledLogMassAlong_pushforward_eq
    (μ : PositiveProbabilityFamily E) {φ : E → ℝ} (hφ : Measurable φ) {C : Set ℝ}
    (hC : MeasurableSet C) :
    ∀ ε : PositiveParameter,
      scaledLogMassAlong
          (fun ε ↦ Measure.map φ (μ ε : Measure E))
          id C ε =
        scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (φ ⁻¹' C) ε := by
  intro ε
  -- Proof comment: `ProbabilityMeasure.map_apply'` rewrites the pushforward mass of `C` as the
  -- original mass of the preimage `φ ⁻¹' C`, and the logarithmic prefactor is unchanged.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def, Measure.map_apply hφ hC]

/-- Helper for Theorem 23.17: rewriting the full Laplace integral against the pushforward law of
`φ` moves the exponential weight from `E` to `ℝ`. -/
private theorem pushforwardLaplaceFunctional_eq
    (μ : PositiveProbabilityFamily E) {φ : E → ℝ} (hφ : Measurable φ)
    (ε : PositiveParameter) :
    varadhanLaplaceFunctional μ φ ε =
      ∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
        (Measure.map φ (μ ε : Measure E)) := by
  have hIntegrand :
      AEMeasurable (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ))))
        (Measure.map φ (μ ε : Measure E)) := by
    fun_prop
  -- Proof comment: `lintegral_map'` transports the integral through the measurable map `φ`.
  simpa [varadhanLaplaceFunctional_def] using
    (MeasureTheory.lintegral_map' hIntegrand hφ.aemeasurable).symm

/-- Helper for Theorem 23.17: the tail Laplace integral over `{x | M ≤ φ x}` is the Laplace
integral over `Set.Ici M` for the pushforward law of `φ`. -/
private theorem pushforwardTailLaplaceFunctional_eq
    (μ : PositiveProbabilityFamily E) {φ : E → ℝ} (hφ : Measurable φ) (M : ℝ)
    (ε : PositiveParameter) :
    varadhanTailLaplaceFunctional μ φ M ε =
      ∫⁻ t,
        (Set.Ici M).indicator (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) t
        ∂(Measure.map φ (μ ε : Measure E)) := by
  have hTailSet : MeasurableSet {x | M ≤ φ x} := hφ measurableSet_Ici
  have hBaseIntegrand :
      Measurable (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) := by
    fun_prop
  have hTargetIntegrand :
      AEMeasurable
          ((Set.Ici M).indicator fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ))))
        (Measure.map φ (μ ε : Measure E)) := by
    exact hBaseIntegrand.aemeasurable.indicator measurableSet_Ici
  -- Proof comment: first rewrite the source restriction as an indicator integral, then transport
  -- that indicator through the pushforward law of `φ`.
  calc
    varadhanTailLaplaceFunctional μ φ M ε
        = ∫⁻ x,
            ({x | M ≤ φ x}.indicator
              (fun x : E ↦ ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))))) x
            ∂(μ ε : Measure E) := by
              rw [varadhanTailLaplaceFunctional_def, ← lintegral_indicator hTailSet]
    _ = ∫⁻ t,
          (Set.Ici M).indicator (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) t
          ∂(Measure.map φ (μ ε : Measure E)) := by
            simpa [Set.preimage, Set.mem_Ici] using
              (MeasureTheory.lintegral_map' hTargetIntegrand hφ.aemeasurable).symm

/-- Helper for Theorem 23.17: the LDP closed upper bound transfers to the pushforward laws of
`φ` after rewriting closed sets in `ℝ` as their preimages in `E`. -/
private theorem pushforwardClosedUpperBound_preimageInf
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) {φ : E → ℝ} (hφ : Continuous φ)
    (hLDP : HasLargeDeviationsPrinciple μ I) {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup
        (scaledLogMassAlong
          (fun ε ↦ Measure.map φ (μ ε : Measure E))
          id C)
        positiveParameterFilter ≤
      -sInf ((fun x ↦ (I x : EReal)) '' (φ ⁻¹' C)) := by
  have hRewrite :
      scaledLogMassAlong
          (fun ε ↦ Measure.map φ (μ ε : Measure E))
          id C =
        scaledLogMassAlong (fun ε ↦ (μ ε : Measure E)) id (φ ⁻¹' C) := by
    funext ε
    exact scaledLogMassAlong_pushforward_eq
      (μ := μ) (hφ := hφ.measurable) hC.measurableSet ε
  -- Proof comment: after the pointwise rewrite, the pushforward bound is exactly the assumed
  -- closed-set upper bound for the preimage `φ ⁻¹' C`.
  simpa [hRewrite] using
    hLDP.closed_upper_bound (C := φ ⁻¹' C) (IsClosed.preimage hφ hC)

/-- Helper for Theorem 23.17: on a closed interval of width at most `η`, the endpoint term
`b - inf I` is controlled by the source supremum `sup_x (φ x - I x)` up to the same error `η`. -/
private theorem rightEndpoint_sub_sInf_preimageIcc_le_sourceSup_add
    (I : E → ENNReal) (φ : E → ℝ) (a b η : ℝ)
    (hwidth : b - a ≤ η) :
    ((b : EReal) - sInf ((fun x ↦ (I x : EReal)) '' (φ ⁻¹' Set.Icc a b))) ≤
      sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η := by
  let S : EReal := sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal)))
  let T : Set EReal := (fun x ↦ (I x : EReal)) '' (φ ⁻¹' Set.Icc a b)
  have hsInf_nonbot : sInf T ≠ ⊥ := by
    -- Proof comment: the infimum of nonnegative `EReal` values cannot be `⊥`.
    have hnonneg : (0 : EReal) ≤ sInf T := by
      refine le_sInf ?_
      intro y hy
      rcases hy with ⟨x, -, rfl⟩
      exact EReal.coe_ennreal_nonneg (I x)
    intro hs
    simp [hs] at hnonneg
  by_cases hsInf_top : sInf T = ⊤
  · -- Proof comment: if the interval preimage only contributes `⊤`-rate values, the target is
    -- immediate because the left-hand side is `⊥`.
    simp [T, hsInf_top]
  have hLower : ((b : EReal) - (S + η)) ≤ sInf T := by
    -- Proof comment: show that every rate value above the interval is at least `b - (S + η)`.
    refine le_sInf ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxIcc : a ≤ φ x ∧ φ x ≤ b := by
      simpa [Set.mem_preimage, Set.mem_Icc] using hx
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
          exact le_sSup ⟨x, rfl⟩
    have hAdd : (b : EReal) ≤ (S + η) + (I x : EReal) := by
      exact (EReal.sub_le_iff_le_add (.inl hIx_bot) (.inl hIx_top)).1 hpoint
    exact EReal.sub_le_of_le_add' (by simpa [add_assoc, add_left_comm, add_comm] using hAdd)
  have hAdd : (b : EReal) ≤ sInf T + (S + η) := by
    exact (EReal.sub_le_iff_le_add (.inr hsInf_top) (.inr hsInf_nonbot)).1 hLower
  -- Proof comment: rewrite the lower-bound form back into the endpoint-minus-infimum estimate.
  exact EReal.sub_le_of_le_add' (by simpa [add_assoc, add_left_comm, add_comm] using hAdd)

/-- Helper for Theorem 23.17: the pushforward Laplace integral on a single closed interval is
bounded by the source supremum `sup_x (φ x - I x)` plus the interval width error. -/
private theorem pushforwardIntervalLaplaceLimsup_le_sourceSup_add
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) {φ : E → ℝ} (hφ : Continuous φ)
    (hLDP : HasLargeDeviationsPrinciple μ I)
    {a b η : ℝ} (hwidth : b - a ≤ η) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))))
        positiveParameterFilter ≤
      sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η := by
  let ν : PositiveProbabilityFamily ℝ :=
    fun ε ↦ ProbabilityMeasure.map (μ ε) hφ.measurable.aemeasurable
  let g : PositiveParameter → EReal :=
    scaledLogMassAlong (fun ε ↦ (ν ε : Measure ℝ)) id (Set.Icc a b)
  have hPointwise :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))) ≤
          (b : EReal) + g ε := by
    intro ε
    -- Proof comment: on `Set.Icc a b`, the pushforward integrand is bounded above by `exp (b / ε)`.
    simpa [ν, g] using
      (upperControlOnSet_laplaceExponent_le
        (μ := ν) (φ := fun t : ℝ ↦ t) measurableSet_Icc
        (c := b) (fun t ht ↦ ht.2) ε)
  have hPointwiseLimsup :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) *
              ENNReal.log
                (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                  ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))))
          positiveParameterFilter ≤
        Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter := by
    exact Filter.limsup_le_limsup (Eventually.of_forall hPointwise)
  have hAddLimsup :
      Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter ≤
        (b : EReal) + Filter.limsup g positiveParameterFilter := by
    -- Proof comment: separate the fixed endpoint contribution `b` from the scaled logarithmic mass.
    simpa [Filter.limsup_const] using
      (EReal.limsup_add_le
        (u := fun _ : PositiveParameter ↦ (b : EReal))
        (v := g) (f := positiveParameterFilter)
        (Or.inl (by simp)) (Or.inl (by simp)))
  have hClosed :
      Filter.limsup g positiveParameterFilter ≤
        -sInf ((fun x ↦ (I x : EReal)) '' (φ ⁻¹' Set.Icc a b)) := by
    -- Proof comment: transfer the LDP closed upper bound to the pushforward family on `Set.Icc a b`.
    simpa [ν, g] using
      (pushforwardClosedUpperBound_preimageInf
        (μ := μ) (I := I) (φ := φ) hφ hLDP (C := Set.Icc a b) isClosed_Icc)
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))))
        positiveParameterFilter
      ≤ Filter.limsup (fun ε : PositiveParameter ↦ (b : EReal) + g ε) positiveParameterFilter :=
        hPointwiseLimsup
    _ ≤ (b : EReal) + Filter.limsup g positiveParameterFilter := hAddLimsup
    _ ≤ (b : EReal) + (-sInf ((fun x ↦ (I x : EReal)) '' (φ ⁻¹' Set.Icc a b))) := by
      gcongr
    _ = (b : EReal) - sInf ((fun x ↦ (I x : EReal)) '' (φ ⁻¹' Set.Icc a b)) := by
      rw [sub_eq_add_neg]
    _ ≤ sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η :=
      rightEndpoint_sub_sInf_preimageIcc_le_sourceSup_add (I := I) (φ := φ) a b η hwidth

/-- Helper for Theorem 23.17: after transporting to the right-neighborhood filter at `0`, the
finite-sum limsup of scaled logarithmic terms is controlled by the finite supremum of the
individual limsups. -/
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
  let uReal : ι → ℝ → ℝ≥0∞ :=
    fun i ε ↦ if hε : 0 < ε then u i ⟨ε, hε⟩ else 0
  have hMain :
      Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun i ↦ u i ε))
          positiveParameterFilter =
        ENNReal.smallNoiseExpGrowthSup (fun ε : ℝ ↦ s.sum fun i ↦ uReal i ε) := by
    -- Proof comment: rewrite the positive-parameter family as a composition with the coercion and
    -- then transport once to `𝓝[>] (0 : ℝ)`.
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
    -- Proof comment: each summand is transported through the same coercion bridge.
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
  -- Proof comment: the real-parameter owner `ENNReal.smallNoiseExpGrowthSup_sum` supplies the
  -- finite aggregation identity once the filter transport is in place.
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

/-- Helper for Theorem 23.17: compactness of `Set.Icc a b` provides a finite cover by closed
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

/-- Helper for Theorem 23.17: a finite closed-interval cover of `Set.Icc a b` dominates the
restricted pushforward Laplace integral by the sum of the piecewise integrals. -/
private theorem pushforwardIccLIntegral_le_sum_cover
    (ν : Measure ℝ) (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    (a b η : ℝ) (s : Finset ℝ)
    (hcover : Set.Icc a b ⊆ ⋃ c ∈ (s : Set ℝ), Set.Icc (c - η / 2) (c + η / 2)) :
    ∫⁻ t, (Set.Icc a b).indicator f t ∂ν ≤
      s.sum fun c ↦ ∫⁻ t, (Set.Icc (c - η / 2) (c + η / 2)).indicator f t ∂ν := by
  classical
  have hPointwise :
      (fun t ↦ (Set.Icc a b).indicator f t) ≤
        fun t ↦ s.sum fun c ↦ (Set.Icc (c - η / 2) (c + η / 2)).indicator f t := by
    intro t
    by_cases ht : t ∈ Set.Icc a b
    · rcases Set.mem_iUnion.1 (hcover ht) with ⟨c, htc⟩
      rcases Set.mem_iUnion.1 htc with ⟨hc, hmem⟩
      calc
        (Set.Icc a b).indicator f t = f t := by
          simp [ht]
        _ = (Set.Icc (c - η / 2) (c + η / 2)).indicator f t := by
          simp [hmem]
        _ ≤ s.sum fun c' ↦ (Set.Icc (c' - η / 2) (c' + η / 2)).indicator f t := by
          exact Finset.single_le_sum
            (f := fun c' : ℝ ↦ (Set.Icc (c' - η / 2) (c' + η / 2)).indicator f t)
            (by intro c' hc'; exact zero_le _) hc
    · simp [ht]
  calc
    ∫⁻ t, (Set.Icc a b).indicator f t ∂ν ≤
        ∫⁻ t, s.sum fun c ↦ (Set.Icc (c - η / 2) (c + η / 2)).indicator f t ∂ν := by
          exact lintegral_mono hPointwise
    _ = s.sum fun c ↦ ∫⁻ t, (Set.Icc (c - η / 2) (c + η / 2)).indicator f t ∂ν := by
      rw [MeasureTheory.lintegral_finset_sum]
      intro c hc
      exact hf.indicator measurableSet_Icc

/-- Helper for Theorem 23.17: the pushforward Laplace exponent on a bounded interval is at most
the source supremum `sup_x (φ x - I x)` up to the prescribed width error `η`. -/
private theorem pushforwardCompactIntervalLimsup_le_sourceSup_add
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) {φ : E → ℝ} (hφ : Continuous φ)
    (hLDP : HasLargeDeviationsPrinciple μ I)
    {a b η : ℝ} (hab : a ≤ b) (hη : 0 < η) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))))
        positiveParameterFilter ≤
      sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η := by
  classical
  obtain ⟨s, hcover, hwidth⟩ := existsIccCoverWithWidth a b η hab hη
  let piece : ℝ → PositiveParameter → ℝ≥0∞ := fun c ε ↦
    ∫⁻ t,
      (Set.Icc (c - η / 2) (c + η / 2)).indicator
        (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) t
      ∂(Measure.map φ (μ ε : Measure E))
  have hIntegralBound :
      ∀ ε : PositiveParameter,
        ∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
            ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b)) ≤
          s.sum fun c ↦ piece c ε := by
    intro ε
    calc
      ∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
          ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))
        =
          ∫⁻ t,
            (Set.Icc a b).indicator
              (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) t
            ∂(Measure.map φ (μ ε : Measure E)) := by
              rw [← MeasureTheory.lintegral_indicator measurableSet_Icc]
      _ ≤ s.sum fun c ↦ piece c ε := by
            simpa [piece] using
              (pushforwardIccLIntegral_le_sum_cover
                (ν := Measure.map φ (μ ε : Measure E))
                (f := fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ))))
                (by fun_prop) a b η s hcover)
  have hPointwiseLog :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))) ≤
          ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε) := by
    intro ε
    have hε : (0 : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact_mod_cast le_of_lt ε.2
    exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log (hIntegralBound ε)) hε
  have hPiece :
      ∀ c ∈ s,
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (piece c ε))
            positiveParameterFilter ≤
          sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η := by
    intro c hc
    -- Proof comment: each cover piece has width at most `η`, so the previously proved
    -- one-interval pushforward bound applies directly.
    simpa [piece, MeasureTheory.lintegral_indicator measurableSet_Icc] using
      (pushforwardIntervalLaplaceLimsup_le_sourceSup_add
        (μ := μ) (I := I) (φ := φ) hφ hLDP
        (a := c - η / 2) (b := c + η / 2) (η := η) (hwidth c hc))
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc a b))))
        positiveParameterFilter
      ≤
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (s.sum fun c ↦ piece c ε))
          positiveParameterFilter := by
            exact Filter.limsup_le_limsup (Eventually.of_forall hPointwiseLog)
    _ ≤
        ⨆ c ∈ s,
          Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (piece c ε))
            positiveParameterFilter :=
      scaledLogFinsetSumLimsup_le_iSup (s := s) (u := piece)
    _ ≤ sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) + η := by
      refine iSup_le ?_
      intro c
      refine iSup_le ?_
      intro hc
      exact hPiece c hc

/-- Helper for Theorem 23.17: the pushforward Laplace exponent over the deterministic left tail
`(-∞, -R]` is bounded by `-R`, because the remaining logarithmic mass is nonpositive. -/
private theorem leftTailPushforwardLimsup_le
    (μ : PositiveProbabilityFamily E) {φ : E → ℝ} (hφ : Measurable φ) (R : ℝ) :
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R)))))
        positiveParameterFilter ≤
      (-R : EReal) := by
  let ν : PositiveProbabilityFamily ℝ :=
    fun ε ↦ ProbabilityMeasure.map (μ ε) hφ.aemeasurable
  have hPointwise :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R)))) ≤
          (-R : EReal) + scaledLogMassAlong (fun ε ↦ (ν ε : Measure ℝ)) id (Set.Iic (-R)) ε := by
    intro ε
    -- Proof comment: on the set `(-∞, -R]`, the exponent is pointwise bounded above by `-R / ε`.
    simpa [ν] using
      (upperControlOnSet_laplaceExponent_le
        (μ := ν) (φ := fun t : ℝ ↦ t) measurableSet_Iic
        (c := -R) (fun t ht ↦ ht) ε)
  have hPointwise_le :
      ∀ ε : PositiveParameter,
        ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R)))) ≤
          (-R : EReal) := by
    intro ε
    calc
      ((ε : ℝ) : EReal) *
          ENNReal.log
            (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
              ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R))))
        ≤ (-R : EReal) + scaledLogMassAlong (fun ε ↦ (ν ε : Measure ℝ)) id (Set.Iic (-R)) ε :=
          hPointwise ε
      _ ≤ (-R : EReal) + 0 := by
        gcongr
        exact scaledLogMassAlong_nonpos_of_probability (μ := ν) ε
      _ = (-R : EReal) := by simp
  -- Proof comment: a pointwise bound by the constant `-R` immediately transfers to the limsup.
  calc
    Filter.limsup
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) *
            ENNReal.log
              (∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
                ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R)))))
        positiveParameterFilter
      ≤ Filter.limsup (fun _ : PositiveParameter ↦ (-R : EReal)) positiveParameterFilter := by
          exact Filter.limsup_le_limsup (Eventually.of_forall hPointwise_le)
    _ = (-R : EReal) := by simp

/-- Helper for Theorem 23.17: the pointwise open-neighborhood lower bounds assemble to the global
lower bound `sup_x (φ x - I x) ≤ liminf ε log ∫ exp (φ / ε) dμ_ε`. -/
private theorem sourceSup_le_liminf_laplaceExponent
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hLDP : HasLargeDeviationsPrinciple μ I) (hφ : Continuous φ) :
    sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))) ≤
      Filter.liminf
        (fun ε : PositiveParameter ↦
          ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
        positiveParameterFilter := by
  refine sSup_le ?_
  rintro z ⟨x, rfl⟩
  -- Proof comment: approximate `φ x - I x` from below by real thresholds and apply the local open
  -- lower bound on a neighborhood where `φ` stays above the chosen threshold.
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
  obtain ⟨U, hU, hxU, hLower⟩ :=
    exists_openLowerControlNeighborhood (hφ := hφ) (x := x) (δ := δ) hδ
  have hLocal :
      (((φ x - δ : ℝ) : EReal) - (I x : EReal)) ≤
        Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
          positiveParameterFilter := by
    -- Proof comment: once the neighborhood keeps `φ` above `φ x - δ`, the LDP lower bound gives
    -- the corresponding liminf estimate.
    simpa using
      (laplaceLiminfLowerBound_of_openLowerControl
        (μ := μ) (I := I) (φ := φ) hLDP (x := x) (U := U) hU hxU
        (c := φ x - δ) hLower)
  have hδeq : φ x - δ = y + ix := by
    dsimp [δ]
    linarith
  calc
    (y : EReal) = ((y : EReal) + (ix : EReal)) - (ix : EReal) := by
      symm
      simpa [add_comm] using (EReal.add_sub_cancel_right (a := (y : EReal)) (b := ix))
    _ = (((φ x - δ : ℝ) : EReal) - (I x : EReal)) := by
      rw [hδeq, hIxEReal]
      simp
    _ ≤ Filter.liminf
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
          positiveParameterFilter := hLocal

-- Proof sketch: for the lower bound, localize the exponential integral to small neighborhoods of a
-- point `x` and use the LDP lower bound together with continuity of `φ`. For the upper bound,
-- split the integral into the tail part controlled by the hypothesis and the bounded part, cover a
-- compact level set of the good rate function by finitely many neighborhoods, and apply the LDP
-- upper bound to each piece before sending the auxiliary parameters to their limits. The source's
-- ball/closure localization uses metric regularity, and any later Lean proof should isolate that
-- strengthening in a private bridge rather than on the public labeled statement.
-- Mathlib recall: `Continuous.borel_measurable` restores the intended measurable bridge once
-- `[BorelSpace E]` is assumed on the public theorem.
/-- Theorem 23.17: Varadhan's Lemma (1966). If `I` is a good rate function,
`μ_ε` satisfies the large deviations principle with rate function `I`, `φ` is
continuous, and the tail logarithmic asymptotics in (23.17) are negligible,
then the scaled logarithmic exponential integral converges to
`sup_x (φ x - I x)` as in (23.18). -/
theorem varadhan_lemma
    [TopologicalSpace E]
    [BorelSpace E]
    (μ : PositiveProbabilityFamily E) (I : E → ENNReal) (φ : E → ℝ)
    (hI_good : IsGoodRateFunction I)
    (hLDP : HasLargeDeviationsPrinciple μ I)
    (hφ : Continuous φ)
    (h_tail :
      sInf (Set.range fun M : {M : ℝ // 0 < M} ↦
        Filter.limsup
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
          positiveParameterFilter) = ⊥) :
    Tendsto
      (fun ε : PositiveParameter ↦
        ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε))
      positiveParameterFilter
      (𝓝 (sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal))))) := by
  let S : EReal := sSup (Set.range fun x : E ↦ ((φ x : EReal) - (I x : EReal)))
  let laplaceExponent : PositiveParameter → EReal := fun ε ↦
    ((ε : ℝ) : EReal) * ENNReal.log (varadhanLaplaceFunctional μ φ ε)
  have hLowerSup : S ≤ Filter.liminf laplaceExponent positiveParameterFilter := by
    -- Proof comment: the global lower bound is already reduced to the pointwise open-neighborhood
    -- lower estimates established above.
    simpa [S, laplaceExponent] using
      (sourceSup_le_liminf_laplaceExponent
        (μ := μ) (I := I) (φ := φ) hLDP hφ)
  have hCutoffSplit :
      ∀ M : ℝ, ∀ ε : PositiveParameter,
        varadhanLaplaceFunctional μ φ ε =
          ∫⁻ x, ENNReal.ofReal (Real.exp (φ x / (ε : ℝ))) ∂((μ ε : Measure E).restrict {x | φ x < M}) +
            varadhanTailLaplaceFunctional μ φ M ε := by
    intro M ε
    -- Proof comment: the Laplace integral is already decomposed into the bounded part and the
    -- tail part needed for the upper-bound route.
    simpa using varadhanLaplaceFunctional_splitAt (μ := μ) (φ := φ) hφ M ε
  -- Route correction: the lower bound is now closed as `hLowerSup`, and the one-interval
  -- pushforward upper bound is available through
  -- `pushforwardIntervalLaplaceLimsup_le_sourceSup_add`, and the remaining transport/aggregation
  -- interfaces are now isolated in `map_positiveParameterFilter`,
  -- `scaledLogFinsetSumLimsup_le_iSup`, and `leftTailPushforwardLimsup_le`.
  -- The remaining blocker is the bounded-middle closed-interval cover on `[-R, M]`:
  -- we still need the explicit finite partition of that interval into width-`≤ η` pieces, the
  -- corresponding domination of the restricted Laplace integral by the finite sum of piece
  -- integrals, and then the final three-piece limsup assembly with `h_tail`.
  have hUpperSup : Filter.limsup laplaceExponent positiveParameterFilter ≤ S := by
    -- Proof comment: compare the full Laplace exponent with an arbitrary real level `y > S`,
    -- then split the pushforward integral into the left tail, the bounded middle interval, and
    -- the upper tail selected from `h_tail`.
    refine (EReal.le_of_forall_lt_iff_le (x := S)
      (y := Filter.limsup laplaceExponent positiveParameterFilter)).1 ?_
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
                  ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
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
                      ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε))
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
    let part : Fin 3 → PositiveParameter → ℝ≥0∞ := fun i ε =>
      match i with
      | 0 =>
          ∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
            ((Measure.map φ (μ ε : Measure E)).restrict (Set.Iic (-R)))
      | 1 =>
          ∫⁻ t, ENNReal.ofReal (Real.exp (t / (ε : ℝ))) ∂
            ((Measure.map φ (μ ε : Measure E)).restrict (Set.Icc (-R) M.1))
      | _ =>
          ∫⁻ t,
            (Set.Ici M.1).indicator
              (fun t : ℝ ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))) t
            ∂(Measure.map φ (μ ε : Measure E))
    have hIntegralBound :
        ∀ ε : PositiveParameter,
          varadhanLaplaceFunctional μ φ ε ≤ Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
      intro ε
      let ν : Measure ℝ := Measure.map φ (μ ε : Measure E)
      let f : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (Real.exp (t / (ε : ℝ)))
      let leftInd : ℝ → ℝ≥0∞ := (Set.Iic (-R)).indicator f
      let middleInd : ℝ → ℝ≥0∞ := (Set.Icc (-R) M.1).indicator f
      let tailInd : ℝ → ℝ≥0∞ := (Set.Ici M.1).indicator f
      have hf : Measurable f := by
        fun_prop
      have hPointwise :
          ∀ t : ℝ, f t ≤ leftInd t + middleInd t + tailInd t := by
        intro t
        by_cases htLeft : t ≤ -R
        · calc
            f t = leftInd t := by
              simp [leftInd, f, htLeft]
            _ ≤ leftInd t + middleInd t := by
              exact le_add_of_nonneg_right bot_le
            _ ≤ leftInd t + middleInd t + tailInd t := by
              exact le_add_of_nonneg_right bot_le
        · by_cases htMiddle : t ≤ M.1
          · have htIcc : t ∈ Set.Icc (-R) M.1 := by
              exact ⟨(lt_of_not_ge htLeft).le, htMiddle⟩
            calc
              f t = middleInd t := by
                simp [middleInd, f, htIcc]
              _ ≤ leftInd t + middleInd t := by
                exact le_add_of_nonneg_left bot_le
              _ ≤ leftInd t + middleInd t + tailInd t := by
                exact le_add_of_nonneg_right bot_le
          · have htTail : t ∈ Set.Ici M.1 := le_of_not_ge htMiddle
            calc
              f t = tailInd t := by
                simp [tailInd, f, htTail]
              _ ≤ leftInd t + middleInd t + tailInd t := by
                have hstep : tailInd t ≤ middleInd t + tailInd t := by
                  exact le_add_of_nonneg_left bot_le
                have hstep' : middleInd t + tailInd t ≤ leftInd t + middleInd t + tailInd t := by
                  simpa [add_assoc] using
                    (le_add_of_nonneg_left (show 0 ≤ leftInd t by exact zero_le _) :
                      middleInd t + tailInd t ≤ leftInd t + (middleInd t + tailInd t))
                exact le_trans hstep hstep'
      calc
        varadhanLaplaceFunctional μ φ ε = ∫⁻ t, f t ∂ν := by
          simpa [ν, f] using pushforwardLaplaceFunctional_eq (μ := μ) (φ := φ) hφ.measurable ε
        _ ≤ ∫⁻ t, leftInd t + middleInd t + tailInd t ∂ν := by
          exact lintegral_mono hPointwise
        _ = (∫⁻ t, leftInd t + middleInd t ∂ν) + ∫⁻ t, tailInd t ∂ν := by
          rw [MeasureTheory.lintegral_add_right]
          exact hf.indicator measurableSet_Ici
        _ = ((∫⁻ t, leftInd t ∂ν) + ∫⁻ t, middleInd t ∂ν) + ∫⁻ t, tailInd t ∂ν := by
          congr 1
          rw [MeasureTheory.lintegral_add_right]
          exact hf.indicator measurableSet_Icc
        _ = (∫⁻ t, leftInd t ∂ν) + (∫⁻ t, middleInd t ∂ν) + ∫⁻ t, tailInd t ∂ν := by
          simp [add_assoc]
        _ = part 0 ε + part 1 ε + part 2 ε := by
          simp [part, ν, f, leftInd, middleInd, tailInd, MeasureTheory.lintegral_indicator,
            add_assoc]
        _ = Finset.univ.sum fun i : Fin 3 ↦ part i ε := by
          simp [part, Fin.sum_univ_three]
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
      simpa [part] using
        (leftTailPushforwardLimsup_le (μ := μ) (φ := φ) hφ.measurable R)
    have hPart1 :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (part 1 ε))
            positiveParameterFilter ≤
          S + η := by
      simpa [S, part] using
        (pushforwardCompactIntervalLimsup_le_sourceSup_add
          (μ := μ) (I := I) (φ := φ) hφ hLDP
          (a := -R) (b := M.1) (η := η) hMidOrder hη)
    have hPart2 :
        Filter.limsup
            (fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε))
            positiveParameterFilter < y := by
      have hTailEq :
          (fun ε : PositiveParameter ↦
            ((ε : ℝ) : EReal) * ENNReal.log (part 2 ε)) =
            fun ε : PositiveParameter ↦
              ((ε : ℝ) : EReal) * ENNReal.log (varadhanTailLaplaceFunctional μ φ M.1 ε) := by
        funext ε
        simp [part, pushforwardTailLaplaceFunctional_eq
          (μ := μ) (φ := φ) hφ.measurable M.1 ε]
      rw [hTailEq]
      exact hTailM
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
  exact tendsto_of_le_liminf_of_limsup_le hLowerSup hUpperSup

end ProbabilityTheory
