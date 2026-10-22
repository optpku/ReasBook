/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_11
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Metrizable.Urysohn

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction CompactlySupported Topology ENNReal

universe u v

namespace MeasureTheory
namespace SignedMeasure

/-- Integration of a bounded continuous real-valued test function against a signed measure, via
its Jordan decomposition. -/
private def weakIntegral {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : E →ᵇ ℝ) : SignedMeasure E → ℝ :=
  fun φ ↦
    ∫ x, f x ∂φ.toJordanDecomposition.posPart - ∫ x, f x ∂φ.toJordanDecomposition.negPart

/-- The weak topology on signed measures is the coarsest topology making integration against every
bounded continuous real-valued test function continuous. -/
@[reducible] private def weakTopology (E : Type u) [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] :
    TopologicalSpace (SignedMeasure E) :=
  ⨅ f : E →ᵇ ℝ, TopologicalSpace.induced (weakIntegral f) inferInstance

local instance instTopologicalSpaceSignedMeasure {E : Type u} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] : TopologicalSpace (SignedMeasure E) :=
  weakTopology E

/-- A sequence of signed measures converges weakly when it converges in the signed-measure weak
topology. -/
private def weaklyConvergesTo {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φs : ℕ → SignedMeasure E) (φ : SignedMeasure E) : Prop :=
  Tendsto φs atTop (𝓝 φ)

/-- Helper: weak convergence of signed measures is equivalent to convergence of
all bounded-continuous test integrals. -/
private theorem weaklyConvergesTo_iffTestIntegrals
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {φs : ℕ → SignedMeasure E} {φ : SignedMeasure E} :
    weaklyConvergesTo φs φ ↔
      ∀ f : E →ᵇ ℝ,
        Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 (weakIntegral f φ)) := by
  -- Proof comment: the weak topology is the infimum of the induced test-integral topologies, so
  -- convergence is exactly coordinatewise convergence of those integrals.
  simp [weaklyConvergesTo, nhds_iInf, nhds_induced, Filter.tendsto_iInf,
    Filter.tendsto_comap_iff, Function.comp_def]

/-- Helper: weak convergence to `0` is equivalent to convergence of all
bounded-continuous test integrals to `0`. -/
private theorem weaklyConvergesTo_zero_iffTestIntegrals
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (φs : ℕ → SignedMeasure E) :
    weaklyConvergesTo φs 0 ↔
      ∀ f : E →ᵇ ℝ, Tendsto (fun n ↦ weakIntegral f (φs n)) atTop (𝓝 0) := by
  constructor
  · intro h f
    -- Proof comment: specialize the coordinatewise criterion at the zero signed measure.
    simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using
      (weaklyConvergesTo_iffTestIntegrals.mp h) f
  · intro h
    -- Proof comment: the converse direction is the same coordinatewise criterion in reverse.
    exact weaklyConvergesTo_iffTestIntegrals.mpr fun f ↦ by
      simpa [weakIntegral, SignedMeasure.toJordanDecomposition_zero] using h f

/-- Helper: the total-variation norm controls the value of a signed measure on
every measurable set. -/
private theorem abs_apply_le_totalVariationNorm
    {E : Type u} [MeasurableSpace E] {A : Set E} (hA : MeasurableSet A)
    (s : SignedMeasure E) :
    |s A| ≤ SignedMeasure.totalVariationNorm E s := by
  -- Proof comment: evaluate the Jordan decomposition on `A` and compare with the total variation
  -- mass on `univ`.
  let j := s.toJordanDecomposition
  have hsA : s A = j.posPart.real A - j.negPart.real A := by
    simpa [j, JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA] using
      (congrArg (fun t : SignedMeasure E ↦ t A)
        (SignedMeasure.toSignedMeasure_toJordanDecomposition s)).symm
  calc
    |s A| = |j.posPart.real A - j.negPart.real A| := by rw [hsA]
    _ ≤ j.posPart.real A + j.negPart.real A := by
      refine abs_sub_le_iff.2 ?_
      constructor <;> linarith [show 0 ≤ j.posPart.real A by positivity,
        show 0 ≤ j.negPart.real A by positivity]
    _ ≤ j.posPart.real Set.univ + j.negPart.real Set.univ := by
      exact add_le_add
        (measureReal_mono (Set.subset_univ A) (by finiteness))
        (measureReal_mono (Set.subset_univ A) (by finiteness))
    _ = SignedMeasure.totalVariationNorm E s := by
      simpa [j] using (SignedMeasure.totalVariation_real_univ_eq_jordan s).symm

/-- Helper: evaluating a signed measure on a measurable set is the difference of
the Jordan positive and negative masses on that set. -/
private theorem apply_eq_jordanDifference
    {E : Type u} [MeasurableSpace E] (ψ : SignedMeasure E) {A : Set E} (hA : MeasurableSet A) :
    ψ A = ψ.toJordanDecomposition.posPart.real A - ψ.toJordanDecomposition.negPart.real A := by
  -- Proof comment: this is the defining relation of the Jordan decomposition, evaluated on `A`.
  simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hA] using
    (congrArg (fun t : SignedMeasure E ↦ t A)
      (SignedMeasure.toSignedMeasure_toJordanDecomposition ψ)).symm

/-- Helper: the superlevel-mass function of a bounded-continuous test is
strongly measurable for every signed measure. -/
private theorem aestronglyMeasurable_superlevelApply
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ψ : SignedMeasure E) (g : E →ᵇ ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ ψ {x : E | t ≤ g x})
      (volume.restrict (Set.Ioc 0 ‖g‖)) := by
  have hPosMeas :
      Measurable (fun t : ℝ ↦ ψ.toJordanDecomposition.posPart {x : E | t ≤ g x}) := by
    exact Antitone.measurable fun s t hst ↦ measure_mono fun x hx ↦ hst.trans hx
  have hNegMeas :
      Measurable (fun t : ℝ ↦ ψ.toJordanDecomposition.negPart {x : E | t ≤ g x}) := by
    exact Antitone.measurable fun s t hst ↦ measure_mono fun x hx ↦ hst.trans hx
  have hEq :
      (fun t : ℝ ↦ ψ {x : E | t ≤ g x}) =
        fun t : ℝ ↦
          ψ.toJordanDecomposition.posPart.real {x : E | t ≤ g x} -
            ψ.toJordanDecomposition.negPart.real {x : E | t ≤ g x} := by
    ext t
    exact apply_eq_jordanDifference ψ (g.continuous.measurable measurableSet_Ici)
  -- Proof comment: rewrite the signed mass through the Jordan decomposition and use measurability
  -- of the two monotone superlevel-mass coordinates.
  rw [hEq]
  exact ((Measurable.ennreal_toReal hPosMeas).aestronglyMeasurable).sub
    ((Measurable.ennreal_toReal hNegMeas).aestronglyMeasurable)

/-- Helper: the superlevel real-mass function of a finite measure is strongly
measurable on the bounded layer-cake interval. -/
private theorem aestronglyMeasurable_measureReal_superlevel
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsFiniteMeasure ν] (g : E →ᵇ ℝ) :
    AEStronglyMeasurable
      (fun t : ℝ ↦ ν.real {x : E | t ≤ g x})
      (volume.restrict (Set.Ioc 0 ‖g‖)) := by
  have hmeas : Measurable (fun t : ℝ ↦ ν {x : E | t ≤ g x}) := by
    exact Antitone.measurable fun s t hst ↦ measure_mono fun x hx ↦ hst.trans hx
  -- Proof comment: the superlevel masses are monotone in the threshold, hence measurable before
  -- coercing from `ℝ≥0∞` to `ℝ`.
  simpa [measureReal_def] using (Measurable.ennreal_toReal hmeas).aestronglyMeasurable

/-- Helper: the real-valued superlevel-mass function of a finite measure is
integrable on the bounded layer-cake interval. -/
private theorem integrable_measureReal_superlevel
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsFiniteMeasure ν] (g : E →ᵇ ℝ) :
    Integrable
      (fun t : ℝ ↦ ν.real {x : E | t ≤ g x})
      (volume.restrict (Set.Ioc 0 ‖g‖)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 ‖g‖)) := ⟨by
    simpa using (measure_Ioc_lt_top (0 : ℝ) ‖g‖).ne⟩
  -- Proof comment: every superlevel mass is bounded by the total mass `ν.real univ`, so the
  -- finite interval measure makes the outer integral integrable.
  refine Integrable.of_bound (aestronglyMeasurable_measureReal_superlevel ν g)
    (ν.real Set.univ) ?_
  exact Filter.Eventually.of_forall fun t ↦ by
    simpa [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using
      (measureReal_mono (Set.subset_univ {x : E | t ≤ g x}))

/-- Helper: the signed superlevel-mass function of a bounded-continuous test is
integrable on the bounded layer-cake interval. -/
private theorem integrable_superlevelApply
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ψ : SignedMeasure E) (g : E →ᵇ ℝ) :
    Integrable
      (fun t : ℝ ↦ ψ {x : E | t ≤ g x})
      (volume.restrict (Set.Ioc 0 ‖g‖)) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc 0 ‖g‖)) := ⟨by
    simpa using (measure_Ioc_lt_top (0 : ℝ) ‖g‖).ne⟩
  -- Proof comment: the total-variation norm controls the signed mass of every superlevel set.
  refine Integrable.of_bound (aestronglyMeasurable_superlevelApply ψ g)
    (SignedMeasure.totalVariationNorm E ψ) ?_
  exact Filter.Eventually.of_forall fun t ↦ by
    have hA : MeasurableSet {x : E | t ≤ g x} := g.continuous.measurable measurableSet_Ici
    simpa [Real.norm_eq_abs] using
      (abs_apply_le_totalVariationNorm hA ψ)

/-- Helper: for a nonnegative bounded-continuous test, the signed weak integral
is the layer-cake integral of the signed superlevel masses. -/
private theorem weakIntegral_eq_integral_superlevelApply
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ψ : SignedMeasure E) (g : E →ᵇ ℝ) (hg_nonneg : ∀ x, 0 ≤ g x) :
    weakIntegral g ψ =
      ∫ t, ψ {x : E | t ≤ g x} ∂(volume.restrict (Set.Ioc 0 ‖g‖)) := by
  let I : Set ℝ := Set.Ioc 0 ‖g‖
  haveI : IsFiniteMeasure (volume.restrict I) := ⟨by
    simpa [I] using (measure_Ioc_lt_top (0 : ℝ) ‖g‖).ne⟩
  have hPos :
      ∫ x, g x ∂ψ.toJordanDecomposition.posPart =
        ∫ t, ψ.toJordanDecomposition.posPart.real {x : E | t ≤ g x} ∂(volume.restrict I) := by
    -- Proof comment: apply the nonnegative layer-cake formula to the Jordan positive part.
    simpa [I] using
      (BoundedContinuousFunction.integral_eq_integral_meas_le g
        ψ.toJordanDecomposition.posPart (Eventually.of_forall hg_nonneg))
  have hNeg :
      ∫ x, g x ∂ψ.toJordanDecomposition.negPart =
        ∫ t, ψ.toJordanDecomposition.negPart.real {x : E | t ≤ g x} ∂(volume.restrict I) := by
    -- Proof comment: the same layer-cake rewrite applies to the Jordan negative part.
    simpa [I] using
      (BoundedContinuousFunction.integral_eq_integral_meas_le g
        ψ.toJordanDecomposition.negPart (Eventually.of_forall hg_nonneg))
  have hPosInt :
      Integrable
        (fun t : ℝ ↦ ψ.toJordanDecomposition.posPart.real {x : E | t ≤ g x})
        (volume.restrict I) := by
    exact integrable_measureReal_superlevel ψ.toJordanDecomposition.posPart g
  have hNegInt :
      Integrable
        (fun t : ℝ ↦ ψ.toJordanDecomposition.negPart.real {x : E | t ≤ g x})
        (volume.restrict I) := by
    exact integrable_measureReal_superlevel ψ.toJordanDecomposition.negPart g
  -- Proof comment: after rewriting both Jordan integrals by layer-cake, combine them into one
  -- signed outer integral and collapse the integrand back to `ψ`.
  rw [weakIntegral, hPos, hNeg]
  change
    ∫ t, ψ.toJordanDecomposition.posPart.real {x : E | t ≤ g x} ∂(volume.restrict I) -
      ∫ t, ψ.toJordanDecomposition.negPart.real {x : E | t ≤ g x} ∂(volume.restrict I) =
        ∫ t, ψ {x : E | t ≤ g x} ∂(volume.restrict I)
  rw [← integral_sub hPosInt hNegInt]
  congr with t
  symm
  exact apply_eq_jordanDifference ψ (g.continuous.measurable measurableSet_Ici)

/-- Helper: shifting a bounded-continuous test by a constant shifts the signed
weak integral by the signed mass of the whole space. -/
private theorem weakIntegral_const_sub
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ψ : SignedMeasure E) (f : E →ᵇ ℝ) (c : ℝ) :
    weakIntegral (BoundedContinuousFunction.const E c - f) ψ =
      ψ Set.univ * c - weakIntegral f ψ := by
  -- Proof comment: expand both Jordan integrals with the finite-measure constant-subtraction
  -- formula and then identify the resulting mass difference with `ψ univ`.
  have hPos :
      ∫ x, (BoundedContinuousFunction.const E c - f) x ∂ψ.toJordanDecomposition.posPart =
        ψ.toJordanDecomposition.posPart.real Set.univ • c -
          ∫ x, f x ∂ψ.toJordanDecomposition.posPart := by
    simp [integral_sub (integrable_const c) (f.integrable _)]
  have hNeg :
      ∫ x, (BoundedContinuousFunction.const E c - f) x ∂ψ.toJordanDecomposition.negPart =
        ψ.toJordanDecomposition.negPart.real Set.univ • c -
          ∫ x, f x ∂ψ.toJordanDecomposition.negPart := by
    simp [integral_sub (integrable_const c) (f.integrable _)]
  rw [weakIntegral, weakIntegral, hPos, hNeg]
  have huniv :
      ψ Set.univ =
        ψ.toJordanDecomposition.posPart.real Set.univ -
          ψ.toJordanDecomposition.negPart.real Set.univ :=
    apply_eq_jordanDifference ψ MeasurableSet.univ
  simp [smul_eq_mul, huniv]
  ring

/-- Helper: the signed weak integral is linear in the signed-measure argument. -/
private theorem weakIntegral_sub_eq
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (f : E →ᵇ ℝ) (ψ η : SignedMeasure E) :
    weakIntegral f (ψ - η) = weakIntegral f ψ - weakIntegral f η := by
  let R : ℝ := ‖f‖
  let g : E →ᵇ ℝ := BoundedContinuousFunction.const E R - f
  have hg_nonneg : ∀ x : E, 0 ≤ g x := by
    intro x
    dsimp [g, R]
    have hfx : f x ≤ ‖f‖ := by
      exact (le_abs_self (f x)).trans (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
    linarith
  have hg_sub :
      weakIntegral g (ψ - η) = weakIntegral g ψ - weakIntegral g η := by
    rw [weakIntegral_eq_integral_superlevelApply (ψ - η) g hg_nonneg,
      weakIntegral_eq_integral_superlevelApply ψ g hg_nonneg,
      weakIntegral_eq_integral_superlevelApply η g hg_nonneg]
    have hψInt : Integrable (fun t : ℝ ↦ ψ {x : E | t ≤ g x})
        (volume.restrict (Set.Ioc 0 ‖g‖)) :=
      integrable_superlevelApply ψ g
    have hηInt : Integrable (fun t : ℝ ↦ η {x : E | t ≤ g x})
        (volume.restrict (Set.Ioc 0 ‖g‖)) :=
      integrable_superlevelApply η g
    have hEq :
        (fun t : ℝ ↦ (ψ - η) {x : E | t ≤ g x}) =
          fun t : ℝ ↦ ψ {x : E | t ≤ g x} - η {x : E | t ≤ g x} := by
      ext t
      rw [VectorMeasure.sub_apply]
    rw [hEq, integral_sub hψInt hηInt]
  have hsub :
      weakIntegral f (ψ - η) =
        (ψ - η) Set.univ * R - weakIntegral g (ψ - η) := by
    have hconst := weakIntegral_const_sub (ψ - η) f R
    linarith
  have hψ :
      weakIntegral f ψ = ψ Set.univ * R - weakIntegral g ψ := by
    have hconst := weakIntegral_const_sub ψ f R
    linarith
  have hη :
      weakIntegral f η = η Set.univ * R - weakIntegral g η := by
    have hconst := weakIntegral_const_sub η f R
    linarith
  -- Proof comment: reduce the general test to a nonnegative one, use the outer-integral formula
  -- there, and then expand the constant-shift correction terms.
  calc
    weakIntegral f (ψ - η)
      = (ψ Set.univ - η Set.univ) * R - (weakIntegral g ψ - weakIntegral g η) := by
          rw [hsub, VectorMeasure.sub_apply, hg_sub]
    _ = (ψ Set.univ * R - weakIntegral g ψ) - (η Set.univ * R - weakIntegral g η) := by ring
    _ = weakIntegral f ψ - weakIntegral f η := by rw [hψ, hη]

/-- Auxiliary signed-measure strengthening for Remark 13.14 (1): for finite signed measures, the
functional-analytic criterion
of total-variation boundedness together with convergence on every measurable set is stronger than
the chapter's weak convergence notion. Here this stronger hypothesis is recorded as a sufficient
condition for the private signed-measure helper notion used below. -/
private theorem weaklyConvergesTo_of_bounded_setwise_tendsto
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {φs : ℕ → SignedMeasure E} {φ : SignedMeasure E}
    (h_bdd :
      ∃ C : ℝ, ∀ n, SignedMeasure.totalVariationNorm E (φs n) ≤ C)
    (h_setwise :
      ∀ A : Set E, MeasurableSet A →
        Tendsto (fun n ↦ φs n A) atTop (𝓝 (φ A))) :
    weaklyConvergesTo φs φ := by
  rcases h_bdd with ⟨C, hC⟩
  let C0 : ℝ := max C 0
  have hC0_nonneg : 0 ≤ C0 := le_max_right _ _
  have hC0_bound : ∀ n, SignedMeasure.totalVariationNorm E (φs n) ≤ C0 := by
    intro n
    exact (hC n).trans (le_max_left _ _)
  let ψs : ℕ → SignedMeasure E := fun n ↦ φs n - φ
  have hψ_setwise :
      ∀ A : Set E, MeasurableSet A →
        Tendsto (fun n ↦ ψs n A) atTop (𝓝 0) := by
    intro A hA
    -- Proof comment: subtract the constant limit measure to reduce to convergence on measurable
    -- sets toward `0`.
    have hA_tendsto :
        Tendsto (fun n ↦ φs n A - φ A) atTop (𝓝 0) := by
      simpa using
        (h_setwise A hA).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ φ A) atTop (𝓝 (φ A)))
    simpa [ψs, VectorMeasure.sub_apply] using hA_tendsto
  have hφ_bound :
      ∀ A : Set E, MeasurableSet A → |φ A| ≤ C0 := by
    intro A hA
    have hmem : φ A ∈ Set.Icc (-C0) C0 := by
      refine isClosed_Icc.mem_of_tendsto (h_setwise A hA) ?_
      exact Filter.Eventually.of_forall fun n ↦ by
        have hAbs :
            |φs n A| ≤ C0 :=
          (abs_apply_le_totalVariationNorm hA (φs n)).trans (hC0_bound n)
        simpa [Set.mem_Icc, abs_le] using hAbs
    simpa [Set.mem_Icc, abs_le] using hmem
  have hweakZero : weaklyConvergesTo ψs 0 := by
    refine weaklyConvergesTo_zero_iffTestIntegrals ψs |>.2 ?_
    intro f
    let R : ℝ := ‖f‖
    let g : E →ᵇ ℝ := BoundedContinuousFunction.const E R - f
    have hg_nonneg : ∀ x : E, 0 ≤ g x := by
      intro x
      dsimp [g, R]
      have hfx : f x ≤ ‖f‖ := by
        exact (le_abs_self (f x)).trans (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x)
      linarith
    let I : Set ℝ := Set.Ioc 0 ‖g‖
    haveI : IsFiniteMeasure (volume.restrict I) := ⟨by
      simpa [I] using (measure_Ioc_lt_top (0 : ℝ) ‖g‖).ne⟩
    have hDom :
        ∀ n, ∀ᵐ t ∂(volume.restrict I), ‖ψs n {x : E | t ≤ g x}‖ ≤ 2 * C0 := by
      intro n
      exact Filter.Eventually.of_forall fun t ↦ by
        have hA : MeasurableSet {x : E | t ≤ g x} :=
          g.continuous.measurable measurableSet_Ici
        have hφsn :
            |φs n {x : E | t ≤ g x}| ≤ C0 :=
          (abs_apply_le_totalVariationNorm hA (φs n)).trans (hC0_bound n)
        have hφA : |φ {x : E | t ≤ g x}| ≤ C0 := hφ_bound _ hA
        calc
          ‖ψs n {x : E | t ≤ g x}‖ =
              |φs n {x : E | t ≤ g x} - φ {x : E | t ≤ g x}| := by
                simp [ψs, VectorMeasure.sub_apply, Real.norm_eq_abs]
          _ ≤ |φs n {x : E | t ≤ g x}| + |φ {x : E | t ≤ g x}| := abs_sub _ _
          _ ≤ C0 + C0 := add_le_add hφsn hφA
          _ = 2 * C0 := by ring
    have hOuter :
        Tendsto
          (fun n ↦ ∫ t, ψs n {x : E | t ≤ g x} ∂(volume.restrict I))
          atTop
          (𝓝 (∫ t, (0 : ℝ) ∂(volume.restrict I))) := by
      -- Route correction: instead of the earlier finite-range quantizer route, use the imported
      -- layer-cake formula to rewrite the signed weak integral as an outer integral of superlevel
      -- set masses, where dominated convergence applies directly.
      exact MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : ℝ ↦ 2 * C0)
        (fun n ↦ aestronglyMeasurable_superlevelApply (ψs n) g)
        (integrable_const (2 * C0))
        hDom
        (Filter.Eventually.of_forall fun t ↦
          hψ_setwise {x : E | t ≤ g x} (g.continuous.measurable measurableSet_Ici))
    have hg_zero :
        Tendsto (fun n ↦ weakIntegral g (ψs n)) atTop (𝓝 0) := by
      refine (tendsto_congr' <| Filter.Eventually.of_forall fun n ↦
        weakIntegral_eq_integral_superlevelApply (ψs n) g hg_nonneg).2 ?_
      simpa [I] using hOuter
    have huniv_zero :
        Tendsto (fun n ↦ ψs n Set.univ * R) atTop (𝓝 0) := by
      simpa [R] using (hψ_setwise Set.univ MeasurableSet.univ).mul_const ‖f‖
    have hshift :
        Tendsto
          (fun n ↦ weakIntegral (BoundedContinuousFunction.const E R - f) (ψs n))
          atTop (𝓝 0) := hg_zero
    -- Proof comment: subtract the constant shift back off using the signed mass of `univ`.
    have hrew :
        (fun n ↦ weakIntegral f (ψs n)) =
          fun n ↦ ψs n Set.univ * R -
            weakIntegral (BoundedContinuousFunction.const E R - f) (ψs n) := by
      funext n
      have hconst :=
        weakIntegral_const_sub (ψs n) f R
      linarith
    rw [hrew]
    simpa using huniv_zero.sub hshift
  -- Proof comment: the original sequence converges to `φ` once the difference sequence converges
  -- weakly to `0`.
  refine weaklyConvergesTo_iffTestIntegrals.2 ?_
  intro f
  have htest :
      Tendsto (fun n ↦ weakIntegral f (ψs n)) atTop (𝓝 0) :=
    (weaklyConvergesTo_zero_iffTestIntegrals ψs).1 hweakZero f
  have hconst :
      Tendsto (fun n ↦ weakIntegral f φ + weakIntegral f (ψs n)) atTop
        (𝓝 (weakIntegral f φ + 0)) :=
    tendsto_const_nhds.add htest
  have hdiff :
      Tendsto (fun n ↦ weakIntegral f (φs n) - weakIntegral f φ) atTop (𝓝 0) := by
    refine (tendsto_congr' <| Filter.Eventually.of_forall fun n ↦ ?_).2 htest
    symm
    simpa [ψs] using weakIntegral_sub_eq f (φs n) φ
  have hsum :
      Tendsto
        (fun n ↦ (weakIntegral f (φs n) - weakIntegral f φ) + weakIntegral f φ)
        atTop
        (𝓝 (0 + weakIntegral f φ)) :=
    hdiff.add tendsto_const_nhds
  convert hsum using 1
  · ext n
    ring
  · ring

end SignedMeasure

namespace FiniteMeasure

/-- Positive-measure specialization of the signed-measure criterion above: convergence of finite
measures on every measurable set implies weak convergence in the chapter's canonical topology on
`FiniteMeasure E`.
This is the nonnegative case of the stronger signed-measure criterion discussed in the remark. -/
theorem tendsto_of_setwise_tendsto
    {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {μs : ℕ → FiniteMeasure E} {μ : FiniteMeasure E}
    (h :
      ∀ A : Set E, MeasurableSet A →
        Tendsto (fun n ↦ (μs n : Measure E) A) atTop (𝓝 ((μ : Measure E) A))) :
    Tendsto μs atTop (𝓝 μ) := by
  by_cases hμ : μ = 0
  · -- Proof comment: if the limit mass is zero, setwise convergence on `univ` already forces the
    -- total masses to vanish, so the finite measures converge weakly to `0`.
    have hmass :
        Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 0) := by
      have hmassEN : Tendsto (fun n ↦ (μs n : Measure E) Set.univ) atTop (𝓝 0) := by
        simpa [hμ] using h Set.univ MeasurableSet.univ
      simpa [FiniteMeasure.mass] using
        (ENNReal.tendsto_toNNReal (measure_ne_top (0 : Measure E) Set.univ)).comp hmassEN
    simpa [hμ] using FiniteMeasure.tendsto_zero_of_tendsto_zero_mass hmass
  have hE : Nonempty E := by
    by_contra hE
    haveI : IsEmpty E := not_nonempty_iff.mp hE
    have hzero : μ = 0 := by
      apply Subtype.ext
      ext s hs
      have hsEmpty : s = ∅ := by
        ext x
        exact isEmptyElim x
      simp [hsEmpty]
    exact hμ hzero
  letI : Nonempty E := hE
  have hmass :
      Tendsto (fun n ↦ (μs n).mass) atTop (𝓝 μ.mass) := by
    have hmassEN :
        Tendsto (fun n ↦ (μs n : Measure E) Set.univ) atTop
          (𝓝 ((μ : Measure E) Set.univ)) :=
      h Set.univ MeasurableSet.univ
    change Tendsto (fun n ↦ ENNReal.toNNReal ((μs n : Measure E) Set.univ)) atTop
      (𝓝 (ENNReal.toNNReal ((μ : Measure E) Set.univ)))
    exact (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure E) Set.univ)).comp hmassEN
  have hEventuallyNonzero : ∀ᶠ n in atTop, μs n ≠ 0 := by
    -- Proof comment: nonzero limit mass makes the approximating masses eventually nonzero.
    have hNonzeroNhds : {0}ᶜ ∈ 𝓝 μ.mass :=
      isOpen_compl_singleton.mem_nhds ((FiniteMeasure.mass_nonzero_iff μ).2 hμ)
    filter_upwards [hmass hNonzeroNhds] with n hn
    exact (FiniteMeasure.mass_nonzero_iff (μs n)).mp hn
  have hnormalizeOpens :
      ∀ G : Set E, IsOpen G →
        μ.normalize G ≤ atTop.liminf (fun n ↦ (μs n).normalize G) := by
    intro G hG
    have hGm : MeasurableSet G := hG.measurableSet
    have hGmass :
        Tendsto (fun n ↦ (μs n) G) atTop (𝓝 (μ G)) := by
      have hGEN :
          Tendsto (fun n ↦ (μs n : Measure E) G) atTop (𝓝 ((μ : Measure E) G)) :=
        h G hGm
      change Tendsto (fun n ↦ ENNReal.toNNReal ((μs n : Measure E) G)) atTop
        (𝓝 (ENNReal.toNNReal ((μ : Measure E) G)))
      exact (ENNReal.tendsto_toNNReal (measure_ne_top (μ : Measure E) G)).comp hGEN
    have hMassInv :
        Tendsto (fun n ↦ ((μs n).mass)⁻¹) atTop (𝓝 (μ.mass⁻¹)) := by
      exact (continuousAt_inv₀ ((FiniteMeasure.mass_nonzero_iff μ).2 hμ)).tendsto.comp hmass
    have hRewrite :
        ∀ᶠ n in atTop, (μs n).normalize G = ((μs n).mass)⁻¹ * (μs n) G := by
      filter_upwards [hEventuallyNonzero] with n hn
      exact (μs n).normalize_eq_of_nonzero hn G
    have hNormalize :
        Tendsto (fun n ↦ (μs n).normalize G) atTop (𝓝 (μ.normalize G)) := by
      refine (tendsto_congr' hRewrite).2 ?_
      have hMul := hMassInv.mul hGmass
      exact (μ.normalize_eq_of_nonzero hμ G).symm ▸ hMul
    rw [hNormalize.liminf_eq]
  have hnormalize :
      Tendsto (fun n ↦ (μs n).normalize) atTop (𝓝 μ.normalize) :=
    MeasureTheory.tendsto_of_forall_isOpen_le_liminf hnormalizeOpens
  -- Proof comment: weak convergence of the normalized probabilities together with convergence of
  -- the masses reconstructs weak convergence of the finite measures themselves.
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
    hnormalize hmass

end FiniteMeasure
end MeasureTheory

section WeakTopology

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

local instance : MeasurableSpace (E ⊕ Unit) := borel (E ⊕ Unit)
local instance : BorelSpace (E ⊕ Unit) := ⟨rfl⟩

/-- Helper: restrict a bounded continuous test function on `E ⊕ Unit` to the
`Sum.inl` copy of `E`. -/
private def inlRestrictedTest (g : (E ⊕ Unit) →ᵇ ℝ) : E →ᵇ ℝ :=
  { toContinuousMap := g.toContinuousMap.comp ⟨Sum.inl, continuous_inl⟩
    map_bounded' := by
      rcases g.map_bounded' with ⟨C, hC⟩
      exact ⟨C, fun x y ↦ hC (Sum.inl x) (Sum.inl y)⟩ }

/-- Helper: extend a bounded continuous test function on `E` to `E ⊕ Unit` by
setting the cemetery-point value to `0`. -/
private def cemeteryExtendedTest (f : E →ᵇ ℝ) : (E ⊕ Unit) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨Sum.elim f (fun _ : Unit ↦ 0), Continuous.sumElim f.continuous continuous_const⟩
    (2 * ‖f‖)
    (by
      intro x y
      rcases x with x | x <;> rcases y with y | y
      · simpa using f.dist_le_two_norm x y
      · have hxy : dist (f x) 0 ≤ 2 * ‖f‖ := by
          calc
            dist (f x) 0 = ‖f x‖ := by simp
            _ ≤ ‖f‖ := f.norm_coe_le_norm x
            _ ≤ 2 * ‖f‖ := by nlinarith [norm_nonneg f]
        simpa using hxy
      · have hyx : dist 0 (f y) ≤ 2 * ‖f‖ := by
          calc
            dist 0 (f y) = ‖f y‖ := by simp
            _ ≤ ‖f‖ := f.norm_coe_le_norm y
            _ ≤ 2 * ‖f‖ := by nlinarith [norm_nonneg f]
        simpa using hyx
      · simp)

/-- Helper: the cemetery extension agrees with the original test function on the
`Sum.inl` copy of `E`. -/
@[simp] private theorem cemeteryExtendedTest_inl (f : E →ᵇ ℝ) (x : E) :
    cemeteryExtendedTest f (Sum.inl x) = f x :=
  by simp [cemeteryExtendedTest]

/-- Helper: the cemetery extension vanishes at the added cemetery point. -/
@[simp] private theorem cemeteryExtendedTest_inr (f : E →ᵇ ℝ) (u : Unit) :
    cemeteryExtendedTest f (Sum.inr u) = 0 :=
  by simp [cemeteryExtendedTest]

/-- Helper: restricting the cemetery extension back to `E` recovers the original
test function. -/
@[simp] private theorem inlRestrictedTest_cemeteryExtendedTest (f : E →ᵇ ℝ) :
    inlRestrictedTest (cemeteryExtendedTest f) = f := by
  ext x
  change cemeteryExtendedTest f (Sum.inl x) = f x
  simp

/-- Helper: encode a finite measure as a probability measure on `E ⊕ Unit` by
adding a cemetery atom and renormalizing by the total mass plus one. -/
private def finiteMeasureCemeteryMeasure (μ : MeasureTheory.FiniteMeasure E) :
    Measure (E ⊕ Unit) :=
  ((ENNReal.ofNNReal (μ.mass + 1))⁻¹ • Measure.map Sum.inl (μ : Measure E)) +
    ((ENNReal.ofNNReal (μ.mass + 1))⁻¹ • Measure.dirac (Sum.inr ()))

/-- Helper: the topological inclusion `Sum.inl` is measurable for the local
Borel sum-space structure. -/
private theorem measurableEmbedding_sumInl : MeasurableEmbedding (Sum.inl : E → E ⊕ Unit) :=
  IsOpenEmbedding.inl.measurableEmbedding

/-- Helper: the `Sum.inl` pushforward of a finite measure has the same total
mass as the original measure. -/
private theorem finiteMeasureCemeteryMapInl_univ (μ : MeasureTheory.FiniteMeasure E) :
    Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E) Set.univ = ENNReal.ofNNReal μ.mass := by
  -- Proof comment: evaluate the pushforward on `univ` by pulling `univ` back through the
  -- measurable embedding `Sum.inl`.
  rw [MeasurableEmbedding.map_apply measurableEmbedding_sumInl (μ : Measure E) Set.univ]
  simp [FiniteMeasure.ennreal_mass]

/-- Helper: bounded-continuous integrals transport across the cemetery inclusion
`Sum.inl`. -/
private theorem integral_map_sumInl_boundedContinuous (g : (E ⊕ Unit) →ᵇ ℝ)
    (μ : MeasureTheory.FiniteMeasure E) :
    ∫ z, g z ∂(Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) =
      ∫ x, g (Sum.inl x) ∂((μ : Measure E)) := by
  -- Proof comment: this is the standard `integral_map` rewrite for the measurable inclusion.
  simpa using
    (MeasureTheory.integral_map measurableEmbedding_sumInl.measurable.aemeasurable
      (show AEStronglyMeasurable (fun z : E ⊕ Unit ↦ g z)
          (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) from
        g.continuous.aestronglyMeasurable))

/-- Helper: the cemetery encoding has total mass one. -/
private theorem finiteMeasureCemeteryMeasure_univ (μ : MeasureTheory.FiniteMeasure E) :
    finiteMeasureCemeteryMeasure μ Set.univ = 1 := by
  -- Proof comment: compute the two `univ` masses separately and then cancel the normalization
  -- factor against the total mass `μ.mass + 1`.
  let a : ℝ≥0∞ := ENNReal.ofNNReal (μ.mass + 1)
  have ha0 : a ≠ 0 := by
    simp [a]
  have haTop : a ≠ ∞ := by
    simp [a]
  rw [finiteMeasureCemeteryMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    finiteMeasureCemeteryMapInl_univ]
  simp [smul_eq_mul]
  have huniv : (μ : Measure E) Set.univ = ENNReal.ofNNReal μ.mass := by
    simp [FiniteMeasure.ennreal_mass]
  rw [huniv]
  have hsum : ENNReal.ofNNReal μ.mass + 1 = ENNReal.ofNNReal (μ.mass + 1) := by
    simp
  calc
    ((μ.mass : ℝ≥0∞) + 1)⁻¹ * (μ.mass : ℝ≥0∞) + ((μ.mass : ℝ≥0∞) + 1)⁻¹
      = ((μ.mass : ℝ≥0∞) + 1)⁻¹ * (μ.mass : ℝ≥0∞) +
          ((μ.mass : ℝ≥0∞) + 1)⁻¹ * 1 := by
            rw [mul_one (((μ.mass : ℝ≥0∞) + 1)⁻¹)]
    _ = ((μ.mass : ℝ≥0∞) + 1)⁻¹ * ((μ.mass : ℝ≥0∞) + 1) := by
          rw [← mul_add]
    _ = 1 := by
          rw [hsum, ENNReal.inv_mul_cancel ha0 haTop]

private def finiteMeasureCemeteryProbability (μ : MeasureTheory.FiniteMeasure E) :
    MeasureTheory.ProbabilityMeasure (E ⊕ Unit) :=
  -- Proof comment: bundle the normalized cemetery measure together with the mass-one theorem.
  ⟨finiteMeasureCemeteryMeasure μ,
    MeasureTheory.isProbabilityMeasure_iff.2 <| finiteMeasureCemeteryMeasure_univ μ⟩

/-- Helper for Remark 13.14: on the `Sum.inl` copy of `E`, the cemetery probability is just the
normalized original finite measure. -/
private theorem finiteMeasureCemeteryProbability_apply_inl_image
    (μ : MeasureTheory.FiniteMeasure E) {s : Set E} (hs : MeasurableSet s) :
    (finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) (Sum.inl '' s) =
      ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) * (μ : Measure E) s := by
  have hs' : MeasurableSet (Sum.inl '' s : Set (E ⊕ Unit)) := by
    exact measurableEmbedding_sumInl.measurableSet_image.2 hs
  -- Proof comment: only the pushed-forward `Sum.inl` part contributes on `Sum.inl '' s`; the
  -- cemetery atom at `Sum.inr ()` is disjoint from that image.
  change
    ((((ENNReal.ofNNReal (μ.mass + 1))⁻¹) •
          Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E) +
        ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) • Measure.dirac (Sum.inr ()) :
          Measure (E ⊕ Unit)) (Sum.inl '' s)) =
    ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) * (μ : Measure E) s
  have hmap :
      Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E) (Sum.inl '' s) =
        (μ : Measure E) s := by
    rw [MeasurableEmbedding.map_apply measurableEmbedding_sumInl (μ : Measure E) (Sum.inl '' s)]
    exact congrArg (fun t : Set E ↦ (μ : Measure E) t) <|
      Set.preimage_image_eq _ measurableEmbedding_sumInl.injective
  have hdirac :
      (Measure.dirac (Sum.inr ()) : Measure (E ⊕ Unit)) (Sum.inl '' s) = 0 := by
    simp
  calc
    ((((ENNReal.ofNNReal (μ.mass + 1))⁻¹) •
          Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E) +
        ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) • Measure.dirac (Sum.inr ()) :
          Measure (E ⊕ Unit)) (Sum.inl '' s))
        = (((ENNReal.ofNNReal (μ.mass + 1))⁻¹) •
              Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) (Sum.inl '' s) +
            (((ENNReal.ofNNReal (μ.mass + 1))⁻¹) • Measure.dirac (Sum.inr ())) (Sum.inl '' s) := by
              simpa using
                (Measure.add_apply
                  (((ENNReal.ofNNReal (μ.mass + 1))⁻¹) •
                    Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E))
                  (((ENNReal.ofNNReal (μ.mass + 1))⁻¹) • Measure.dirac (Sum.inr ()))
                  hs')
    _ = ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) * (μ : Measure E) s +
          ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) * 0 := by
            rw [Measure.smul_apply, Measure.smul_apply, hmap, hdirac]
            simp [smul_eq_mul]
    _ = ((ENNReal.ofNNReal (μ.mass + 1))⁻¹) * (μ : Measure E) s := by
          simp

/-- Helper: the encoded probability integrates a bounded continuous test on
`E ⊕ Unit` as the normalized sum of the `E`-part integral and the cemetery-point value. -/
private theorem integral_finiteMeasureCemeteryProbability (g : (E ⊕ Unit) →ᵇ ℝ)
    (μ : MeasureTheory.FiniteMeasure E) :
    ∫ z, g z ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) =
      (((μ.mass : ℝ) + 1)⁻¹) *
        (∫ x, inlRestrictedTest g x ∂((μ : Measure E)) + g (Sum.inr ())) := by
  -- Proof comment: expand the cemetery measure into the pushed-forward finite-measure part and
  -- the cemetery atom, then rewrite each integral contribution separately.
  let a : ℝ≥0∞ := (ENNReal.ofNNReal (μ.mass + 1))⁻¹
  have ha :
      a.toReal = (((μ.mass : ℝ) + 1)⁻¹) := by
    have hunivToReal : (((μ : Measure E) Set.univ + 1).toReal) = ((μ.mass : ℝ) + 1) := by
      simpa [FiniteMeasure.ennreal_mass] using
        (ENNReal.toReal_add (measure_ne_top (μ : Measure E) Set.univ) ENNReal.one_ne_top)
    rw [show a = (((μ : Measure E) Set.univ + 1))⁻¹ by simp [a, FiniteMeasure.ennreal_mass],
      ENNReal.toReal_inv, hunivToReal]
  have haTop : a ≠ ∞ := by
    simp [a]
  have h_map0 :
      Integrable g (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) := by
    simpa using g.integrable (Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E))
  have h_dirac0 :
      Integrable g (Measure.dirac (Sum.inr ())) := by
    simpa using g.integrable (Measure.dirac (Sum.inr ()))
  have h_map :
      Integrable g (a • Measure.map (Sum.inl : E → E ⊕ Unit) (μ : Measure E)) := by
    exact Integrable.of_measure_le_smul haTop (by intro s; simp [Measure.smul_apply]) h_map0
  have h_dirac :
      Integrable g (a • Measure.dirac (Sum.inr ())) := by
    exact Integrable.of_measure_le_smul haTop (by intro s; simp [Measure.smul_apply]) h_dirac0
  change
    ∫ z, g z ∂finiteMeasureCemeteryMeasure μ =
      (((μ.mass : ℝ) + 1)⁻¹) *
        (∫ x, inlRestrictedTest g x ∂((μ : Measure E)) + g (Sum.inr ()))
  rw [finiteMeasureCemeteryMeasure]
  rw [integral_add_measure h_map h_dirac, integral_smul_measure, integral_smul_measure,
    integral_map_sumInl_boundedContinuous, integral_dirac]
  -- Proof comment: after transporting the pushforward term, factor out the common scalar.
  rw [ha]
  simp [smul_eq_mul]
  have hinl :
      ∫ x, inlRestrictedTest g x ∂((μ : Measure E)) =
        ∫ x, g (Sum.inl x) ∂((μ : Measure E)) := by
    change ∫ x, g (Sum.inl x) ∂((μ : Measure E)) =
      ∫ x, g (Sum.inl x) ∂((μ : Measure E))
    rfl
  rw [hinl]
  ring_nf

/-- Helper: bounded-continuous integrals against a finite measure can be
recovered from its cemetery encoding. -/
private theorem integral_eq_massAddOne_mul_cemeteryIntegral (f : E →ᵇ ℝ)
    (μ : MeasureTheory.FiniteMeasure E) :
    ∫ x, f x ∂((μ : Measure E)) =
      (((μ.mass : ℝ) + 1)) *
        ∫ z, cemeteryExtendedTest f z
          ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) := by
  -- Proof comment: specialize the cemetery integral formula to the zero-at-cemetery extension
  -- of `f`, then cancel the reciprocal factor `((μ.mass : ℝ) + 1)⁻¹`.
  have hcem :
      ∫ z, cemeteryExtendedTest f z ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) =
        (((μ.mass : ℝ) + 1)⁻¹) * ∫ x, f x ∂((μ : Measure E)) := by
    simpa using
      (integral_finiteMeasureCemeteryProbability (cemeteryExtendedTest f) μ)
  have hmassPos : 0 < ((μ.mass : ℝ) + 1) := by
    positivity
  calc
    ∫ x, f x ∂((μ : Measure E))
      = ((((μ.mass : ℝ) + 1)) * (((μ.mass : ℝ) + 1)⁻¹)) * ∫ x, f x ∂((μ : Measure E)) := by
          rw [mul_inv_cancel₀ hmassPos.ne', one_mul]
    _ = (((μ.mass : ℝ) + 1)) * ((((μ.mass : ℝ) + 1)⁻¹) * ∫ x, f x ∂((μ : Measure E))) := by
          ring
    _ = (((μ.mass : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z
            ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) := by
          rw [hcem]

/-- Helper: the cemetery embedding records both the total mass and the normalized
probability encoding of a finite measure. -/
private def finiteMeasureCemeteryEmbedding (μ : MeasureTheory.FiniteMeasure E) :
    NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) :=
  (μ.mass, finiteMeasureCemeteryProbability μ)

/-- Helper: the cemetery embedding is injective because its two coordinates
recover all bounded-continuous integrals of the original finite measure. -/
private theorem finiteMeasureCemeteryEmbedding_injective :
    Function.Injective
      (finiteMeasureCemeteryEmbedding :
        MeasureTheory.FiniteMeasure E →
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
  intro μ ν hEmbedding
  have hmass : μ.mass = ν.mass := by
    simpa using congrArg Prod.fst hEmbedding
  have hprob :
      finiteMeasureCemeteryProbability μ = finiteMeasureCemeteryProbability ν := by
    simpa using congrArg Prod.snd hEmbedding
  -- Proof comment: the cemetery probability coordinate recovers every bounded-continuous integral
  -- once we multiply back by the mass coordinate.
  refine FiniteMeasure.ext_of_forall_integral_eq ?_
  intro f
  calc
    ∫ x, f x ∂((μ : Measure E)) =
        (((μ.mass : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z
            ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) := by
          rw [integral_eq_massAddOne_mul_cemeteryIntegral]
    _ = (((ν.mass : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z
            ∂(finiteMeasureCemeteryProbability ν : Measure (E ⊕ Unit)) := by
          rw [hmass, hprob]
    _ = ∫ x, f x ∂((ν : Measure E)) := by
          rw [integral_eq_massAddOne_mul_cemeteryIntegral]

/-- Helper: the cemetery embedding induces the finite-measure weak topology
because the mass coordinate together with the cemetery probability coordinate is equivalent to the
full family of bounded-continuous test integrals. -/
private theorem finiteMeasureCemeteryEmbedding_inducing :
    IsInducing
      (finiteMeasureCemeteryEmbedding :
        MeasureTheory.FiniteMeasure E →
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
  let emb : MeasureTheory.FiniteMeasure E →
      NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) :=
    finiteMeasureCemeteryEmbedding
  have hProbability :
      Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦
        finiteMeasureCemeteryProbability μ) := by
    rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
    intro g
    -- Proof comment: the cemetery probability integral is an explicit continuous expression in
    -- the mass and the original finite-measure integral.
    have hMassInv :
        Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦
          (((μ.mass : ℝ) + 1)⁻¹)) := by
      refine ((NNReal.continuous_coe.comp FiniteMeasure.continuous_mass).add continuous_const).inv₀
        ?_
      intro μ
      have hmassNonneg : 0 ≤ (μ.mass : ℝ) := by exact_mod_cast μ.mass.2
      have hmassPos : 0 < ((μ.mass : ℝ) + 1) := by linarith
      exact hmassPos.ne'
    have hIntegral :
        Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦
          ∫ x, inlRestrictedTest g x ∂((μ : Measure E))) :=
      FiniteMeasure.continuous_integral_boundedContinuousFunction (inlRestrictedTest g)
    simpa [integral_finiteMeasureCemeteryProbability, Function.comp] using
      hMassInv.mul (hIntegral.add continuous_const)
  have hEmbeddingContinuous : Continuous emb := by
    -- Proof comment: the mass coordinate is already continuous, so continuity reduces to the
    -- probability coordinate handled above.
    exact FiniteMeasure.continuous_mass.prodMk hProbability
  rw [Topology.isInducing_iff_nhds]
  intro μ
  refine le_antisymm (hEmbeddingContinuous.continuousAt : ContinuousAt emb μ).le_comap ?_
  -- Proof comment: if a net of cemetery coordinates converges, then every bounded-continuous
  -- finite-measure integral converges by the explicit recovery formula, so the finite measures
  -- converge in their owner weak topology.
  change Tendsto (fun ν : MeasureTheory.FiniteMeasure E ↦ ν) (Filter.comap emb (𝓝 (emb μ)))
    (𝓝 μ)
  exact FiniteMeasure.tendsto_of_forall_integral_tendsto <| by
      intro f
      let recoveredIntegral :
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) → ℝ :=
        fun y ↦ (((y.1 : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit)))
      have hRecoveredIntegral : Continuous recoveredIntegral := by
        have hMass :
            Continuous (fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
              ((y.1 : ℝ) + 1)) :=
          (NNReal.continuous_coe.comp continuous_fst).add continuous_const
        have hIntegral :
            Continuous (fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
              ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit)))) :=
          (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
            (cemeteryExtendedTest f)).comp continuous_snd
        exact hMass.mul hIntegral
      have hFactor :
          (fun ν : MeasureTheory.FiniteMeasure E ↦ ∫ x, f x ∂((ν : Measure E))) =
            recoveredIntegral ∘ emb := by
        funext ν
        simpa [recoveredIntegral, emb] using
          (integral_eq_massAddOne_mul_cemeteryIntegral f ν)
      rw [hFactor]
      have hValue :
          recoveredIntegral (emb μ) = ∫ x, f x ∂((μ : Measure E)) := by
        simpa [recoveredIntegral, emb] using
          (integral_eq_massAddOne_mul_cemeteryIntegral f μ).symm
      simpa [hValue] using
        (hRecoveredIntegral.continuousAt : ContinuousAt recoveredIntegral (emb μ)).tendsto.comp
          Filter.tendsto_comap

/-- Helper: the cemetery embedding is a topological embedding. -/
private theorem finiteMeasureCemeteryEmbedding_isEmbedding
    [TopologicalSpace.SeparableSpace E] :
    IsEmbedding
      (finiteMeasureCemeteryEmbedding :
        MeasureTheory.FiniteMeasure E →
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
  -- Proof comment: after separating the owner-facing topology bookkeeping from the integral
  -- recovery argument, the embedding theorem is immediate.
  exact ⟨finiteMeasureCemeteryEmbedding_inducing, finiteMeasureCemeteryEmbedding_injective⟩

/-- Helper for Remark 13.14: recovering a finite measure from cemetery coordinates rescales the
`Sum.inl` restriction of the probability coordinate by the mass parameter plus one. -/
private def finiteMeasureCemeteryRecovery
    (y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) :
    MeasureTheory.FiniteMeasure E :=
  (y.1 + 1) • (y.2.toFiniteMeasure.comap Sum.inl)

/-- Helper for Remark 13.14: the recovered finite measure integrates a bounded continuous test
function by the same explicit cemetery formula used in the forward embedding. -/
private theorem integral_finiteMeasureCemeteryRecovery
    (f : E →ᵇ ℝ) (y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) :
    ∫ x, f x ∂((finiteMeasureCemeteryRecovery y : Measure E)) =
      (((y.1 : ℝ) + 1)) *
        ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit))) := by
  let ν : MeasureTheory.FiniteMeasure E := y.2.toFiniteMeasure.comap Sum.inl
  have hMap :
      Measure.map (Sum.inl : E → E ⊕ Unit) (ν : Measure E) =
        Measure.restrict (y.2 : Measure (E ⊕ Unit)) (Set.range (Sum.inl : E → E ⊕ Unit)) := by
    -- Proof comment: pushing the `Sum.inl` comap back forward identifies it with restriction to
    -- the `Sum.inl` copy of `E`.
    simpa [ν] using
      (MeasurableEmbedding.map_comap measurableEmbedding_sumInl (y.2 : Measure (E ⊕ Unit)))
  have hRestrict :
      ∫ z, cemeteryExtendedTest f z
          ∂(Measure.restrict (y.2 : Measure (E ⊕ Unit)) (Set.range (Sum.inl : E → E ⊕ Unit))) =
        ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit))) := by
    -- Proof comment: the cemetery extension vanishes on the complement `{Sum.inr ()}`, so
    -- restricting to the `Sum.inl` range does not change the integral.
    rw [← integral_indicator measurableEmbedding_sumInl.measurableSet_range]
    refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
    rcases z with z | u
    · simp [measurableEmbedding_sumInl.measurableSet_range]
    · simp [measurableEmbedding_sumInl.measurableSet_range, cemeteryExtendedTest]
  -- Proof comment: map the comap measure back to the `Sum.inl` copy, then remove the redundant
  -- range restriction because the test extension is already zero at the cemetery point.
  calc
    ∫ x, f x ∂((finiteMeasureCemeteryRecovery y : Measure E))
      = (((y.1 : ℝ) + 1)) * ∫ x, f x ∂((ν : Measure E)) := by
          change
            ∫ x, f x ∂((y.1 + 1 : NNReal) • (ν : Measure E)) =
              (((y.1 : ℝ) + 1)) * ∫ x, f x ∂((ν : Measure E))
          convert
            (integral_smul_measure (fun x : E ↦ f x) (y.1 + 1 : NNReal)) using 1
    _ = (((y.1 : ℝ) + 1)) *
          ∫ x, (cemeteryExtendedTest f) (Sum.inl x) ∂((ν : Measure E)) := by
          refine congrArg (fun t : ℝ ↦ (((y.1 : ℝ) + 1)) * t) ?_
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          simp [cemeteryExtendedTest]
    _ = (((y.1 : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z ∂(Measure.map (Sum.inl : E → E ⊕ Unit) (ν : Measure E)) := by
          rw [integral_map_sumInl_boundedContinuous (cemeteryExtendedTest f) ν]
    _ = (((y.1 : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z
            ∂(Measure.restrict (y.2 : Measure (E ⊕ Unit))
              (Set.range (Sum.inl : E → E ⊕ Unit))) := by
          rw [hMap]
    _ = (((y.1 : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit))) := by
          rw [hRestrict]

/-- Helper for Remark 13.14: the probability coordinate of the cemetery embedding is continuous. -/
private theorem continuous_finiteMeasureCemeteryProbability :
    Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦ finiteMeasureCemeteryProbability μ) := by
  rw [ProbabilityMeasure.continuous_iff_forall_continuous_integral]
  intro g
  -- Proof comment: the cemetery integral is an explicit continuous expression in the total mass
  -- and the original bounded-continuous integral.
  have hMassInv :
      Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦ (((μ.mass : ℝ) + 1)⁻¹)) := by
    refine ((NNReal.continuous_coe.comp FiniteMeasure.continuous_mass).add continuous_const).inv₀
      ?_
    intro μ
    have hmassPos : 0 < ((μ.mass : ℝ) + 1) := by positivity
    exact hmassPos.ne'
  have hIntegral :
      Continuous (fun μ : MeasureTheory.FiniteMeasure E ↦
        ∫ x, inlRestrictedTest g x ∂((μ : Measure E))) :=
    FiniteMeasure.continuous_integral_boundedContinuousFunction (inlRestrictedTest g)
  simpa [integral_finiteMeasureCemeteryProbability, Function.comp] using
    hMassInv.mul (hIntegral.add continuous_const)

-- Proof comment: the next theorem proves continuity of the cemetery recovery map; the separate
-- zero-mass-on-open closedness lemma appears later, once the local compact Polish hypothesis is
-- available.
/-- Helper for Remark 13.14: the cemetery recovery map is continuous because bounded-continuous
integrals factor through the two ambient coordinates by an explicit formula. -/
private theorem continuous_finiteMeasureCemeteryRecovery :
    Continuous
      (finiteMeasureCemeteryRecovery :
        NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) →
          MeasureTheory.FiniteMeasure E) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro f
  have hEq :
      (fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
        ∫ x, f x ∂((finiteMeasureCemeteryRecovery y : Measure E))) =
        fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
          (((y.1 : ℝ) + 1)) *
            ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit))) := by
    funext y
    exact integral_finiteMeasureCemeteryRecovery f y
  -- Proof comment: once the integral is rewritten through the explicit recovery formula, both
  -- factors are continuous in the ambient product coordinates.
  rw [hEq]
  have hMass :
      Continuous (fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
        ((y.1 : ℝ) + 1)) :=
    (NNReal.continuous_coe.comp continuous_fst).add continuous_const
  have hIntegral :
      Continuous (fun y : NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) ↦
        ∫ z, cemeteryExtendedTest f z ∂((y.2 : Measure (E ⊕ Unit)))) :=
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (cemeteryExtendedTest f)).comp continuous_snd
  exact hMass.mul hIntegral

/-- Helper for Remark 13.14: the cemetery recovery map is a genuine inverse to the forward
embedding on finite measures. -/
private theorem finiteMeasureCemeteryRecovery_leftInverse :
    Function.LeftInverse
      (finiteMeasureCemeteryRecovery :
        NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) →
          MeasureTheory.FiniteMeasure E)
      (finiteMeasureCemeteryEmbedding :
        MeasureTheory.FiniteMeasure E →
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
  intro μ
  -- Proof comment: both the forward and backward formulas recover the same bounded-continuous
  -- integrals, so the finite measures coincide.
  refine FiniteMeasure.ext_of_forall_integral_eq ?_
  intro f
  calc
    ∫ x, f x ∂((finiteMeasureCemeteryRecovery (finiteMeasureCemeteryEmbedding μ) : Measure E))
      = (((μ.mass : ℝ) + 1)) *
          ∫ z, cemeteryExtendedTest f z
            ∂(finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) := by
              simpa [finiteMeasureCemeteryEmbedding] using
                integral_finiteMeasureCemeteryRecovery f (finiteMeasureCemeteryEmbedding μ)
    _ = ∫ x, f x ∂((μ : Measure E)) := by
          rw [← integral_eq_massAddOne_mul_cemeteryIntegral]

/-- Helper for Remark 13.14: the cemetery embedding has closed range because the explicit
recovery map is continuous on the whole ambient product. -/
private theorem finiteMeasureCemeteryEmbedding_isClosedEmbedding :
    IsClosedEmbedding
      (finiteMeasureCemeteryEmbedding :
        MeasureTheory.FiniteMeasure E →
          NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
  let emb : MeasureTheory.FiniteMeasure E →
      NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit) :=
    finiteMeasureCemeteryEmbedding
  -- Proof comment: a continuous left inverse upgrades the already explicit cemetery embedding to
  -- a closed embedding.
  exact finiteMeasureCemeteryRecovery_leftInverse.isClosedEmbedding
    continuous_finiteMeasureCemeteryRecovery
    (FiniteMeasure.continuous_mass.prodMk continuous_finiteMeasureCemeteryProbability)

/-- Helper for Remark 13.14: on a compact Polish space, the weak topology on finite measures is
Polish because the cemetery embedding lands in a compact-metrizable ambient probability space. -/
private theorem finiteMeasure_weakTopology_polish_of_compact
    [CompactSpace E] [PolishSpace E] :
    PolishSpace (MeasureTheory.FiniteMeasure E) := by
  letI : CompactSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  letI : TopologicalSpace.MetrizableSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by
    infer_instance
  letI : MetricSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : CompleteSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  letI : SecondCountableTopology (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  letI : PolishSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  letI : PolishSpace (NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  exact finiteMeasureCemeteryEmbedding_isClosedEmbedding.polishSpace

/-- Helper for Remark 13.14: the disjoint sum of locally compact spaces is locally compact. -/
private instance sumLocallyCompactSpace
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    LocallyCompactSpace (X ⊕ Y) := by
  constructor
  intro z t ht
  cases z with
  | inl x =>
      rw [nhds_inl] at ht
      rcases LocallyCompactSpace.local_compact_nhds x (Sum.inl ⁻¹' t) ht with
        ⟨K, hKnhds, hKt, hKcompact⟩
      refine ⟨Sum.inl '' K, ?_, ?_, hKcompact.image continuous_inl⟩
      · rw [nhds_inl]
        have hpre :
            ((Sum.inl : X → X ⊕ Y) ⁻¹' ((Sum.inl : X → X ⊕ Y) '' K)) = K := by
          ext a
          constructor
          · intro ha
            rcases ha with ⟨b, hb, hba⟩
            cases hba
            simpa using hb
          · intro ha
            exact ⟨a, ha, rfl⟩
        simpa [hpre] using hKnhds
      · intro y hy
        rcases hy with ⟨a, ha, rfl⟩
        exact hKt ha
  | inr y =>
      rw [nhds_inr] at ht
      rcases LocallyCompactSpace.local_compact_nhds y (Sum.inr ⁻¹' t) ht with
        ⟨K, hKnhds, hKt, hKcompact⟩
      refine ⟨Sum.inr '' K, ?_, ?_, hKcompact.image continuous_inr⟩
      · rw [nhds_inr]
        have hpre :
            ((Sum.inr : Y → X ⊕ Y) ⁻¹' ((Sum.inr : Y → X ⊕ Y) '' K)) = K := by
          ext a
          constructor
          · intro ha
            rcases ha with ⟨b, hb, hba⟩
            cases hba
            simpa using hb
          · intro ha
            exact ⟨a, ha, rfl⟩
        simpa [hpre] using hKnhds
      · intro y' hy'
        rcases hy' with ⟨a, ha, rfl⟩
        exact hKt ha

/-- Helper for Remark 13.14: pushing forward a probability measure along `X ↪ OnePoint X`
preserves the mass of image sets. -/
private def probabilityMeasureMapCoe
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    (P : MeasureTheory.ProbabilityMeasure X) :
    MeasureTheory.ProbabilityMeasure (OnePoint X) :=
  let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  MeasureTheory.ProbabilityMeasure.map P hf.measurable.aemeasurable

/-- Helper for Remark 13.14: pushing forward a probability measure along `X ↪ OnePoint X`
preserves the mass of image sets. -/
private theorem probabilityMeasure_toMeasure_map_coe_apply_image
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    (P : MeasureTheory.ProbabilityMeasure X) {s : Set X} (hs : MeasurableSet s) :
    ((probabilityMeasureMapCoe P : MeasureTheory.ProbabilityMeasure (OnePoint X)) :
        Measure (OnePoint X))
      (((↑) : X → OnePoint X) '' s) = (P : Measure X) s := by
  let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  -- Proof comment: evaluate the pushforward on an image set and collapse the preimage of that
  -- image along the injective one-point embedding.
  change
    ((MeasureTheory.ProbabilityMeasure.map P hf.measurable.aemeasurable :
        MeasureTheory.ProbabilityMeasure (OnePoint X)) : Measure (OnePoint X))
      (((↑) : X → OnePoint X) '' s) = (P : Measure X) s
  rw [MeasureTheory.ProbabilityMeasure.map_apply' _ hf.measurable.aemeasurable
    (hf.measurableSet_image' hs)]
  rw [OnePoint.coe_injective.preimage_image]

/-- Helper for Remark 13.14: if a probability measure on `OnePoint X` gives full mass to the
embedded copy of `X`, then mapping back the comap along `X ↪ OnePoint X` recovers the original
measure. -/
private theorem measure_map_comap_coe_eq_self_of_fullMass
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    {Q : MeasureTheory.ProbabilityMeasure (OnePoint X)}
    (hQ : Q (Set.range ((↑) : X → OnePoint X)) = 1) :
    Measure.map ((↑) : X → OnePoint X) ((Q : Measure (OnePoint X)).comap ((↑) : X → OnePoint X)) =
      (Q : Measure (OnePoint X)) := by
  let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have hQae : Set.range ((↑) : X → OnePoint X) ∈ ae (Q : Measure (OnePoint X)) := by
    -- Proof comment: full mass on the embedded copy of `X` means the point at infinity is null.
    refine (MeasureTheory.mem_ae_iff_prob_eq_one hf.measurableSet_range).2 ?_
    simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      (congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hQ)
  calc
    Measure.map ((↑) : X → OnePoint X) ((Q : Measure (OnePoint X)).comap ((↑) : X → OnePoint X)) =
        (Q : Measure (OnePoint X)).restrict (Set.range ((↑) : X → OnePoint X)) := by
          simpa using hf.map_comap (Q : Measure (OnePoint X))
    _ = (Q : Measure (OnePoint X)) := Measure.restrict_eq_self_of_ae_mem hQae

/-- Helper for Remark 13.14: if probability measures on the one-point compactification converge
weakly to a limit that still gives full mass to the original space, then the pulled-back
probability measures on the original space converge weakly as well. -/
private theorem tendsto_probabilityMeasure_of_tendsto_onePoint
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [HasOuterApproxClosed (OnePoint X)]
    {Ps : ℕ → MeasureTheory.ProbabilityMeasure X}
    {Q : MeasureTheory.ProbabilityMeasure (OnePoint X)}
    (hQ : Q (Set.range ((↑) : X → OnePoint X)) = 1)
    (h :
      Tendsto
        (fun n ↦ probabilityMeasureMapCoe (Ps n))
        atTop
        (𝓝 Q)) :
    ∃ P : MeasureTheory.ProbabilityMeasure X,
      Tendsto Ps atTop (𝓝 P) ∧
        probabilityMeasureMapCoe P = Q := by
  let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have hQae : Set.range ((↑) : X → OnePoint X) ∈ ae (Q : Measure (OnePoint X)) := by
    -- Proof comment: the limit measure charges only the embedded copy of `X`, so its comap is
    -- again a probability measure.
    refine (MeasureTheory.mem_ae_iff_prob_eq_one hf.measurableSet_range).2 ?_
    simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      (congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hQ)
  let P : MeasureTheory.ProbabilityMeasure X :=
    ⟨(Q : Measure (OnePoint X)).comap ((↑) : X → OnePoint X),
      hf.isProbabilityMeasure_comap hQae⟩
  have hmapMeasure :
      Measure.map ((↑) : X → OnePoint X) (P : Measure X) = (Q : Measure (OnePoint X)) := by
    -- Proof comment: map-comap becomes an exact inverse after removing the null point at
    -- infinity.
    simpa [P] using measure_map_comap_coe_eq_self_of_fullMass hQ
  have hmapP :
      probabilityMeasureMapCoe P = Q := by
    -- Proof comment: upgrade the measure-level recovery statement to an equality of probability
    -- measures by comparing their values on measurable sets.
    apply MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
    intro s hs
    have hs' := congrArg (fun μ : Measure (OnePoint X) ↦ μ s) hmapMeasure
    simpa [MeasureTheory.ProbabilityMeasure.toMeasure_map] using hs'
  have hOpen :
      ∀ G, IsOpen G →
        (P : Measure X) G ≤ atTop.liminf (fun n ↦ (Ps n : Measure X) G) := by
    intro G hG
    let G' : Set (OnePoint X) := ((↑) : X → OnePoint X) '' G
    have hG' : IsOpen G' := by
      simpa [G'] using (OnePoint.isOpen_image_coe.2 hG)
    have hliminf :
        (Q : Measure (OnePoint X)) G' ≤
          atTop.liminf
            (fun n ↦
              ((probabilityMeasureMapCoe (Ps n) :
                  MeasureTheory.ProbabilityMeasure (OnePoint X)) :
                Measure (OnePoint X)) G') := by
      exact MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto h hG'
    have hleft : (P : Measure X) G = (Q : Measure (OnePoint X)) G' := by
      simpa [P, G'] using (hf.comap_apply (Q : Measure (OnePoint X)) G)
    have hright :
        (fun n ↦
            ((probabilityMeasureMapCoe (Ps n) :
                MeasureTheory.ProbabilityMeasure (OnePoint X)) :
              Measure (OnePoint X)) G') =
          fun n ↦ (Ps n : Measure X) G := by
      funext n
      simpa [G'] using
        probabilityMeasure_toMeasure_map_coe_apply_image (Ps n) hG.measurableSet
    rw [← hleft, hright] at hliminf
    exact hliminf
  refine ⟨P, ?_, hmapP⟩
  -- Proof comment: the Portmanteau open-set criterion transports the convergence back from
  -- `OnePoint X` to `X`.
  exact MeasureTheory.tendsto_of_forall_isOpen_le_liminf_nat' hOpen

/-- Helper for Remark 13.14: pushing a probability measure forward along `X ↪ OnePoint X`
assigns zero mass to the point at infinity. -/
private theorem probabilityMeasure_map_coe_apply_infty_eq_zero
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    (P : MeasureTheory.ProbabilityMeasure X) :
    ((probabilityMeasureMapCoe P : MeasureTheory.ProbabilityMeasure (OnePoint X)) :
        Measure (OnePoint X))
      {OnePoint.infty} = 0 := by
  let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  -- Proof comment: the preimage of `∞` under the canonical embedding is empty.
  rw [probabilityMeasureMapCoe, MeasureTheory.ProbabilityMeasure.map_apply' P
    hf.measurable.aemeasurable OnePoint.isClosed_infty.measurableSet]
  simpa [OnePoint.coe_preimage_infty]

/-- Helper for Remark 13.14: the zero-mass-at-`∞` locus inside
`ProbabilityMeasure (OnePoint X)`. -/
private def zeroMassAtInftySubtype
    (X : Type u) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)] :=
  {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
    ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0}

/-- Helper for Remark 13.14: the zero-mass one-point alias carries the induced subtype topology. -/
local instance instTopologicalSpaceZeroMassAtInftySubtype
    (X : Type u) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)] :
    TopologicalSpace (zeroMassAtInftySubtype X) :=
  inferInstanceAs
    (TopologicalSpace
      {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
        ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0})

/-- Helper for Remark 13.14: the embedded copy of `X` has full mass exactly when the mass at
`∞` vanishes. -/
private theorem probabilityMeasure_fullMass_range_of_infty_eq_zero
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    {Q : MeasureTheory.ProbabilityMeasure (OnePoint X)}
    (hQ : ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0) :
    Q (Set.range ((↑) : X → OnePoint X)) = 1 := by
  have hRangeMeasure :
      ((Q : Measure (OnePoint X)) (Set.range ((↑) : X → OnePoint X))) =
        ((Q : Measure (OnePoint X)) Set.univ) := by
    -- Proof comment: the complement of the embedded copy of `X` is exactly `{∞}`, so the null
    -- cemetery mass forces the range to carry the whole probability mass.
    apply MeasureTheory.measure_of_measure_compl_eq_zero
    simpa [OnePoint.compl_range_coe] using hQ
  -- Proof comment: the probability mass splits between the open copy of `X` and the cemetery
  -- point, so vanishing cemetery mass forces full mass on the range of `X`.
  have hRangeMeasure' :
      ((Q : Measure (OnePoint X)) (Set.range ((↑) : X → OnePoint X))) = 1 := by
    simpa using hRangeMeasure
  exact ENNReal.coe_inj.mp <| by
    simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hRangeMeasure'

/-- Helper for Remark 13.14: vanishing cemetery mass implies that the embedded copy of `X` is an
almost-everywhere event. -/
private theorem probabilityMeasure_range_ae_of_infty_eq_zero
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    {Q : MeasureTheory.ProbabilityMeasure (OnePoint X)}
    (hQ : ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0) :
    Set.range ((↑) : X → OnePoint X) ∈ ae (Q : Measure (OnePoint X)) := by
  have hRange : Q (Set.range ((↑) : X → OnePoint X)) = 1 :=
    probabilityMeasure_fullMass_range_of_infty_eq_zero hQ
  -- Proof comment: the owner lemma `mem_ae_iff_prob_eq_one` turns the full-mass statement into
  -- the exact `ae` condition needed by the comap probability-measure constructor.
  refine (MeasureTheory.mem_ae_iff_prob_eq_one
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_range).2 ?_
  simpa [MeasureTheory.ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (congrArg (fun x : NNReal ↦ (x : ℝ≥0∞)) hRange)

/-- Helper for Remark 13.14: the one-point pushforward of probability measures is injective. -/
private theorem probabilityMeasureMapCoe_injective
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)] :
    Function.Injective
      (probabilityMeasureMapCoe :
        MeasureTheory.ProbabilityMeasure X →
          MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
  intro P₁ P₂ hP
  apply MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  -- Proof comment: equality of the pushforwards identifies the masses of all image measurable
  -- sets, and those image masses recover the original measures.
  simpa [probabilityMeasure_toMeasure_map_coe_apply_image P₁ hs,
    probabilityMeasure_toMeasure_map_coe_apply_image P₂ hs] using
    congrArg
      (fun Q : MeasureTheory.ProbabilityMeasure (OnePoint X) ↦
        ((Q : Measure (OnePoint X)) (((↑) : X → OnePoint X) '' s)))
      hP

/-- Helper for Remark 13.14: recover a probability measure on `X` from a one-point measure with
zero mass at `∞` by comapping along `X ↪ OnePoint X`. -/
private def probabilityMeasureRecoverFromOnePoint
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)] :
    zeroMassAtInftySubtype X → MeasureTheory.ProbabilityMeasure X :=
  fun Q ↦
    let hf : MeasurableEmbedding ((↑) : X → OnePoint X) :=
      OnePoint.isOpenEmbedding_coe.measurableEmbedding
    ⟨(Q.1 : Measure (OnePoint X)).comap ((↑) : X → OnePoint X),
      hf.isProbabilityMeasure_comap (probabilityMeasure_range_ae_of_infty_eq_zero Q.2)⟩

/-- Helper for Remark 13.14: the comap recovery map is an actual inverse to the one-point
pushforward on the zero-mass subtype. -/
private theorem probabilityMeasureRecoverFromOnePoint_leftInverse
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)] :
    ∀ Q : zeroMassAtInftySubtype X,
      probabilityMeasureMapCoe (probabilityMeasureRecoverFromOnePoint Q) = Q.1 := by
  intro Q
  have hmapMeasure :
      Measure.map ((↑) : X → OnePoint X)
        ((probabilityMeasureRecoverFromOnePoint Q : MeasureTheory.ProbabilityMeasure X) :
          Measure X) =
        (Q.1 : Measure (OnePoint X)) := by
    -- Proof comment: map-comap is exact because the recovered measure lives entirely on the
    -- embedded copy of `X`.
    exact measure_map_comap_coe_eq_self_of_fullMass
      (probabilityMeasure_fullMass_range_of_infty_eq_zero Q.2)
  apply MeasureTheory.ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  simpa using congrArg (fun μ : Measure (OnePoint X) ↦ μ s) hmapMeasure

/-- Helper for Remark 13.14: the forward one-point pushforward already lands in the zero-mass
subtype. -/
private def probabilityMeasureMapCoe_zeroMass
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)] :
    MeasureTheory.ProbabilityMeasure X → zeroMassAtInftySubtype X :=
  fun P ↦ ⟨probabilityMeasureMapCoe P, probabilityMeasure_map_coe_apply_infty_eq_zero P⟩

/-- Helper for Remark 13.14: recovering from the zero-mass one-point model really inverts the
forward embedding on `ProbabilityMeasure X`. -/
private theorem probabilityMeasureRecoverFromOnePoint_rightInverse
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    (P : MeasureTheory.ProbabilityMeasure X) :
    probabilityMeasureRecoverFromOnePoint (probabilityMeasureMapCoe_zeroMass P) = P := by
  -- Proof comment: the forward map of the recovered probability measure coincides with the
  -- original one-point pushforward, so injectivity of the forward map identifies the source
  -- probability measures.
  apply probabilityMeasureMapCoe_injective
  simpa [probabilityMeasureMapCoe_zeroMass] using
    probabilityMeasureRecoverFromOnePoint_leftInverse
      (Q := probabilityMeasureMapCoe_zeroMass P)

/-- Helper for Remark 13.14: the forward map into the zero-mass one-point model is continuous. -/
private theorem continuous_probabilityMeasureMapCoe_zeroMass
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)] :
    Continuous
      (probabilityMeasureMapCoe_zeroMass :
        MeasureTheory.ProbabilityMeasure X → zeroMassAtInftySubtype X) := by
  -- Proof comment: continuity into the subtype is just continuity of the ambient one-point
  -- pushforward map, together with the already proved zero-mass side condition.
  change Continuous fun P : MeasureTheory.ProbabilityMeasure X ↦
    (⟨probabilityMeasureMapCoe P, probabilityMeasure_map_coe_apply_infty_eq_zero P⟩ :
      zeroMassAtInftySubtype X)
  exact
    (MeasureTheory.ProbabilityMeasure.continuous_map (Ω := X) (Ω' := OnePoint X)
      OnePoint.continuous_coe).subtype_mk
      (fun P ↦ probabilityMeasure_map_coe_apply_infty_eq_zero P)

/-- Helper for Remark 13.14: the one-point compactification of a locally compact Polish space is
again second countable. -/
private theorem onePoint_secondCountable
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [PolishSpace X] :
    SecondCountableTopology (OnePoint X) := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  obtain ⟨bX, hbX_count, -, hbX_basis⟩ := TopologicalSpace.exists_countable_basis X
  let Binf : Set (Set (OnePoint X)) :=
    {s | ∃ n : ℕ, s = (((↑) : X → OnePoint X) '' (K n : Set X))ᶜ}
  let B : Set (Set (OnePoint X)) :=
    ((fun s : Set X ↦ ((↑) : X → OnePoint X) '' s) '' bX) ∪ Binf
  have hBopen : ∀ s ∈ B, IsOpen s := by
    intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨u, hu, rfl⟩
      -- Proof comment: the `X`-side basis sets stay open after applying the open embedding
      -- `X ↪ OnePoint X`.
      exact OnePoint.isOpen_image_coe.2 (hbX_basis.isOpen hu)
    · rcases hs with ⟨n, rfl⟩
      -- Proof comment: neighborhoods of `∞` come from complements of compact exhaustion pieces.
      exact (OnePoint.isClosed_image_coe.mpr ⟨(K.isCompact n).isClosed, K.isCompact n⟩).isOpen_compl
  have hBnhds : ∀ x u, x ∈ u → IsOpen u → ∃ v ∈ B, x ∈ v ∧ v ⊆ u := by
    intro x u hx hu
    cases x using OnePoint.rec with
    | infty =>
        have hu_nhds : u ∈ 𝓝 (OnePoint.infty : OnePoint X) := hu.mem_nhds hx
        obtain ⟨t, htc, htu⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hu_nhds
        rcases htc with ⟨_, htcompact⟩
        rcases K.exists_superset_of_isCompact htcompact with ⟨n, htn⟩
        refine ⟨(((↑) : X → OnePoint X) '' (K n : Set X))ᶜ, Or.inr ⟨n, rfl⟩, ?_, ?_⟩
        · -- Proof comment: `∞` is never in the embedded copy of `X`.
          simp [OnePoint.coe_ne_infty]
        · -- Proof comment: once a compact set is absorbed by some exhaustion piece, the
          -- corresponding complement neighborhood of `∞` is already contained in `u`.
          have himage : ((↑) : X → OnePoint X) '' t ⊆ ((↑) : X → OnePoint X) '' (K n : Set X) := by
            intro y hy
            rcases hy with ⟨z, hz, rfl⟩
            exact ⟨z, htn hz, rfl⟩
          have hsubset :
              (((↑) : X → OnePoint X) '' (K n : Set X))ᶜ ⊆
                ((↑) '' tᶜ : Set (OnePoint X)) ∪ {OnePoint.infty} := by
            simpa [OnePoint.compl_image_coe] using Set.compl_subset_compl.2 himage
          exact hsubset.trans htu
    | coe x =>
        have hu_pre : IsOpen (((↑) : X → OnePoint X) ⁻¹' u) :=
          OnePoint.continuous_coe.isOpen_preimage _ hu
        have hx_pre : x ∈ ((↑) : X → OnePoint X) ⁻¹' u := by
          simpa using hx
        rcases hbX_basis.exists_subset_of_mem_open hx_pre hu_pre with ⟨v, hv, hxv, hvu⟩
        refine ⟨((↑) : X → OnePoint X) '' v, Or.inl ⟨v, hv, rfl⟩, by simpa using hxv, ?_⟩
        -- Proof comment: inside the open copy of `X`, the ambient neighborhood basis is just the
        -- transported countable basis of `X`.
        intro y hy
        rcases hy with ⟨z, hz, rfl⟩
        exact hvu hz
  have hBbasis : TopologicalSpace.IsTopologicalBasis B :=
    TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds hBopen hBnhds
  have hBinf_eq :
      Binf = Set.range (fun n : ℕ => (((↑) : X → OnePoint X) '' (K n : Set X))ᶜ) := by
    ext s
    simp [Binf, eq_comm]
  have hBinf_count : Binf.Countable := by
    rw [hBinf_eq]
    exact Set.countable_range _
  exact hBbasis.secondCountableTopology ((hbX_count.image _).union hBinf_count)

/-- Helper for Remark 13.14: the one-point compactification of a locally compact Polish space is
again Polish. -/
private theorem onePoint_polish
    {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [PolishSpace X] :
    PolishSpace (OnePoint X) := by
  letI : SecondCountableTopology (OnePoint X) := onePoint_secondCountable
  letI : TopologicalSpace.MetrizableSpace (OnePoint X) := by
    infer_instance
  letI : MetricSpace (OnePoint X) := TopologicalSpace.metrizableSpaceMetric _
  letI : CompactSpace (OnePoint X) := by
    infer_instance
  letI : CompleteSpace (OnePoint X) := by
    infer_instance
  -- Proof comment: compactness plus the metrizable structure obtained from Urysohn's theorem
  -- upgrades the one-point compactification to a Polish space.
  infer_instance

/-- Helper for Remark 13.14: the zero-mass one-point recovery map is continuous. -/
private theorem continuous_probabilityMeasureRecoverFromOnePoint
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)]
    [LocallyCompactSpace X] [PolishSpace X] :
    Continuous
      (probabilityMeasureRecoverFromOnePoint :
        zeroMassAtInftySubtype X → MeasureTheory.ProbabilityMeasure X) := by
  letI : PolishSpace (OnePoint X) := onePoint_polish
  letI : TopologicalSpace.MetrizableSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  change Continuous
    (probabilityMeasureRecoverFromOnePoint :
      {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} →
        MeasureTheory.ProbabilityMeasure X)
  let rawRecover :
      {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} →
        MeasureTheory.ProbabilityMeasure X :=
    probabilityMeasureRecoverFromOnePoint
  letI :
      TopologicalSpace.MetrizableSpace
        {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} :=
    Topology.IsEmbedding.subtypeVal.metrizableSpace
  letI :
      SequentialSpace
        {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} := by
    infer_instance
  refine (continuous_iff_seqContinuous :
    Continuous rawRecover ↔ SeqContinuous rawRecover).2 ?_
  intro Qs Q hQs
  have hQsTop :
      Tendsto (fun n ↦ (Qs n).1) atTop (𝓝 Q.1) := by
    simpa [Function.comp] using (continuous_subtype_val.tendsto Q).comp hQs
  have hMapSeq :
      (fun n ↦
          probabilityMeasureMapCoe
            (probabilityMeasureRecoverFromOnePoint (Qs n))) =
        fun n ↦ (Qs n).1 := by
    funext n
    exact probabilityMeasureRecoverFromOnePoint_leftInverse (Q := Qs n)
  obtain ⟨P, hP, hMapP⟩ :=
    tendsto_probabilityMeasure_of_tendsto_onePoint
      (Ps := fun n ↦ probabilityMeasureRecoverFromOnePoint (Qs n))
      (Q := Q.1)
      (probabilityMeasure_fullMass_range_of_infty_eq_zero Q.2) <| by
        simpa [hMapSeq] using hQsTop
  have hRecoverMap :
      probabilityMeasureMapCoe (probabilityMeasureRecoverFromOnePoint Q) = Q.1 :=
    probabilityMeasureRecoverFromOnePoint_leftInverse (Q := Q)
  have hP_eq : P = probabilityMeasureRecoverFromOnePoint Q := by
    apply probabilityMeasureMapCoe_injective
    rw [hMapP, hRecoverMap]
  -- Proof comment: the transported limit is uniquely determined because the one-point pushforward
  -- is injective on probability measures.
  simpa [hP_eq] using hP

/-- Helper for Remark 13.14: the one-point model gives a closed embedding into the zero-mass
subtype. -/
private theorem probabilityMeasureMapCoe_zeroMass_isClosedEmbedding
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)]
    [LocallyCompactSpace X] [PolishSpace X] :
    IsClosedEmbedding
      (probabilityMeasureMapCoe_zeroMass :
        MeasureTheory.ProbabilityMeasure X → zeroMassAtInftySubtype X) := by
  change IsClosedEmbedding
    (fun P : MeasureTheory.ProbabilityMeasure X ↦
      (⟨probabilityMeasureMapCoe P, probabilityMeasure_map_coe_apply_infty_eq_zero P⟩ :
        {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0}))
  let rawForward :
      MeasureTheory.ProbabilityMeasure X →
        {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} :=
    fun P ↦ ⟨probabilityMeasureMapCoe P, probabilityMeasure_map_coe_apply_infty_eq_zero P⟩
  let rawRecover :
      {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} →
        MeasureTheory.ProbabilityMeasure X :=
    probabilityMeasureRecoverFromOnePoint
  letI : PolishSpace (OnePoint X) := onePoint_polish
  letI :
      T2Space
        {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) //
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) = 0} := by
    infer_instance
  -- Proof comment: once both directions are continuous, the explicit inverse package upgrades the
  -- one-point model from a set-theoretic identification to a closed embedding.
  exact Function.LeftInverse.isClosedEmbedding
    (f := rawRecover)
    (g := rawForward)
    (h := fun P ↦ probabilityMeasureRecoverFromOnePoint_rightInverse (P := P))
    (show Continuous rawRecover from continuous_probabilityMeasureRecoverFromOnePoint)
    (show Continuous rawForward from continuous_probabilityMeasureMapCoe_zeroMass)

/-- Helper for Remark 13.14: the strict sublevel sets of the cemetery mass are open in the
one-point probability space. -/
private theorem probabilityMeasure_inftyMass_lt_isOpen
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)]
    [LocallyCompactSpace X] [PolishSpace X] {r : ℝ≥0∞} (hr : 0 < r) :
    IsOpen {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) |
      ((Q : Measure (OnePoint X)) {OnePoint.infty}) < r} := by
  letI : PolishSpace (OnePoint X) := onePoint_polish
  letI : TopologicalSpace.MetrizableSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  letI : SequentialSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  let s : Set (MeasureTheory.ProbabilityMeasure (OnePoint X)) :=
    {Q | r ≤ ((Q : Measure (OnePoint X)) {OnePoint.infty})}
  have hsSeqClosed : IsSeqClosed s := by
    intro Qs Q hQs_mem hQs
    have hr_le_limsup :
        r ≤ atTop.limsup
          (fun n ↦ ((Qs n : Measure (OnePoint X)) {OnePoint.infty})) := by
      exact le_limsup_of_frequently_le <|
        (Filter.Eventually.of_forall hQs_mem).frequently
    -- Proof comment: closed-set Portmanteau makes the `∞`-mass upper semicontinuous, so a
    -- sequence staying above the level `r` cannot drop below `r` in the limit.
    exact hr_le_limsup.trans <|
      MeasureTheory.ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
        (μs := Qs) (μ := Q) hQs OnePoint.isClosed_infty
  have hsClosed : IsClosed s := hsSeqClosed.isClosed
  -- Proof comment: the desired strict sublevel is the complement of the sequentially closed
  -- superlevel set.
  have hEq :
      {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) |
          ((Q : Measure (OnePoint X)) {OnePoint.infty}) < r} = sᶜ := by
    ext Q
    change ((Q : Measure (OnePoint X)) {OnePoint.infty}) < r ↔
      ¬ r ≤ ((Q : Measure (OnePoint X)) {OnePoint.infty})
    exact lt_iff_not_ge
  rw [hEq]
  exact hsClosed.isOpen_compl

/-- Helper for Remark 13.14: an `ℝ≥0∞` quantity is zero if it is strictly smaller than every
reciprocal `1 / (n + 1)`. -/
private theorem ennreal_eq_zero_of_forall_lt_inv_nat_succ {a : ℝ≥0∞}
    (ha : ∀ n : ℕ, a < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) : a = 0 := by
  by_contra hne
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hne
  cases n with
  | zero =>
      simpa using hn
  | succ k =>
      exact (not_le_of_gt hn) (ha k).le

/-- Helper for Remark 13.14: the zero-mass-at-`∞` subtype is Polish via a closed compatibility
model inside a countable product of open sublevels. -/
private theorem zeroMassAtInftySubtype_polish
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace (OnePoint X)] [BorelSpace (OnePoint X)]
    [OpensMeasurableSpace (OnePoint X)]
    [LocallyCompactSpace X] [PolishSpace X] :
    PolishSpace (zeroMassAtInftySubtype X) := by
  letI : PolishSpace (OnePoint X) := onePoint_polish
  letI : CompactSpace (OnePoint X) := by
    infer_instance
  letI : CompactSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  letI : TopologicalSpace.MetrizableSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  letI : MetricSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : CompleteSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  letI : SecondCountableTopology (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  letI : PolishSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) := by
    infer_instance
  let U : ℕ → Set (MeasureTheory.ProbabilityMeasure (OnePoint X)) := fun n ↦
    {Q | ((Q : Measure (OnePoint X)) {OnePoint.infty}) < ((n + 1 : ℕ) : ℝ≥0∞)⁻¹}
  let Y : Type u := (n : ℕ) → {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) // U n Q}
  letI : ∀ n : ℕ, PolishSpace {Q : MeasureTheory.ProbabilityMeasure (OnePoint X) // U n Q} :=
    fun n ↦
      (probabilityMeasure_inftyMass_lt_isOpen (X := X) (r := ((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
        (by simp)).polishSpace
  let C : Set Y := {u | ∀ n, (u n).1 = (u 0).1}
  have hCClosed : IsClosed C := by
    rw [show C = ⋂ n, {u : Y | (u n).1 = (u 0).1} by
      ext u
      simp [C]]
    refine isClosed_iInter ?_
    intro n
    exact isClosed_eq
      (continuous_subtype_val.comp (continuous_apply n))
      (continuous_subtype_val.comp (continuous_apply 0))
  let Z : Type u := {u : Y // C u}
  letI : PolishSpace Z := hCClosed.polishSpace
  let toAmbient : zeroMassAtInftySubtype X → Y := fun Q n ↦
    ⟨Q.1, by
      -- Proof comment: zero cemetery mass lies in every strict reciprocal sublevel.
      change ((Q.1 : Measure (OnePoint X)) {OnePoint.infty}) < (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
      rw [Q.2]
      simp⟩
  let toFun : zeroMassAtInftySubtype X → Z := fun Q ↦
    ⟨toAmbient Q, by
      intro n
      rfl⟩
  let fromAmbient : Z → MeasureTheory.ProbabilityMeasure (OnePoint X) := fun u ↦ (u.1 0).1
  let fromFun : Z → zeroMassAtInftySubtype X := fun u ↦
    ⟨fromAmbient u, by
      have hlt :
          ∀ n : ℕ,
            ((fromAmbient u : Measure (OnePoint X)) {OnePoint.infty}) <
              ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        intro n
        -- Proof comment: the compatibility equations identify every coordinate with the zeroth
        -- one, so each reciprocal bound applies to the same ambient probability measure.
        simpa [fromAmbient, U, u.2 n] using (u.1 n).2
      exact ennreal_eq_zero_of_forall_lt_inv_nat_succ hlt⟩
  have hToAmbientCont : Continuous toAmbient := by
    refine continuous_pi ?_
    intro n
    exact continuous_subtype_val.subtype_mk (fun Q ↦ by
      change ((Q.1 : Measure (OnePoint X)) {OnePoint.infty}) < (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
      rw [Q.2]
      simp)
  have hToCont : Continuous toFun := by
    exact hToAmbientCont.subtype_mk (fun Q ↦ by
      intro n
      rfl)
  have hFromAmbientCont : Continuous fromAmbient := by
    exact continuous_subtype_val.comp
      ((continuous_apply 0).comp continuous_subtype_val)
  have hFromCont : Continuous fromFun := by
    exact hFromAmbientCont.subtype_mk (fun u ↦ by
      have hlt :
          ∀ n : ℕ,
            ((fromAmbient u : Measure (OnePoint X)) {OnePoint.infty}) <
              ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        intro n
        simpa [fromAmbient, U, u.2 n] using (u.1 n).2
      exact ennreal_eq_zero_of_forall_lt_inv_nat_succ hlt)
  let homeo : zeroMassAtInftySubtype X ≃ₜ Z :=
    { toEquiv :=
        { toFun := toFun
          invFun := fromFun
          left_inv := by
            intro Q
            rfl
          right_inv := by
            intro u
            apply Subtype.ext
            funext n
            apply Subtype.ext
            exact (u.2 n).symm }
      continuous_toFun := hToCont
      continuous_invFun := hFromCont }
  -- Proof comment: the closed compatibility locus is Polish, and the explicit constant-family
  -- homeomorphism transfers that structure to the zero-mass subtype.
  exact homeo.isClosedEmbedding.polishSpace

/-- Helper for Remark 13.14: locally compact Polish spaces should have Polish probability-measure
spaces for the weak topology. This is the missing ambient-space input needed to upgrade the
cemetery embedding argument from metrizability to Polishness. -/
private theorem probabilityMeasure_polish_of_compact
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [PolishSpace X] :
    PolishSpace (MeasureTheory.ProbabilityMeasure X) := by
  letI : CompactSpace (MeasureTheory.ProbabilityMeasure X) := by
    infer_instance
  letI : TopologicalSpace.MetrizableSpace (MeasureTheory.ProbabilityMeasure X) := by
    infer_instance
  letI : MetricSpace (MeasureTheory.ProbabilityMeasure X) :=
    TopologicalSpace.metrizableSpaceMetric _
  letI : CompleteSpace (MeasureTheory.ProbabilityMeasure X) := by
    infer_instance
  letI : SecondCountableTopology (MeasureTheory.ProbabilityMeasure X) := by
    infer_instance
  -- Proof comment: on a compact base space, Prokhorov compactness plus metrizability upgrades the
  -- probability-measure weak topology to a Polish space.
  infer_instance

/-- Helper for Remark 13.14: locally compact Polish spaces should have Polish probability-measure
spaces for the weak topology. This is the missing ambient-space input needed to upgrade the
cemetery embedding argument from metrizability to Polishness. -/
private theorem probabilityMeasure_polish_of_locallyCompact
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [PolishSpace X] :
    PolishSpace (MeasureTheory.ProbabilityMeasure X) := by
  letI : MeasurableSpace (OnePoint X) := borel (OnePoint X)
  letI : BorelSpace (OnePoint X) := ⟨rfl⟩
  letI : PolishSpace (OnePoint X) := onePoint_polish
  letI : CompactSpace (OnePoint X) := by
    infer_instance
  letI : PolishSpace (MeasureTheory.ProbabilityMeasure (OnePoint X)) :=
    probabilityMeasure_polish_of_compact
  let hEmbed :
      IsClosedEmbedding
        (probabilityMeasureMapCoe_zeroMass :
          MeasureTheory.ProbabilityMeasure X → zeroMassAtInftySubtype X) :=
    probabilityMeasureMapCoe_zeroMass_isClosedEmbedding
  letI : PolishSpace (zeroMassAtInftySubtype X) := zeroMassAtInftySubtype_polish
  -- Proof comment: after replacing the false closed-locus route by the closed compatibility model
  -- for the zero-mass subtype, the existing closed embedding transfers Polishness immediately.
  exact hEmbed.polishSpace

/- Item (ii) source recall for Remark 13.14. For finite measures, the weak topology is the
canonical topology on `MeasureTheory.FiniteMeasure E` characterized by continuity of integration
against every bounded continuous real-valued test function, and it is the trace of the weak*
topology along the canonical embedding into the weak dual of bounded continuous functions. These
are exactly the existing owner theorems
`MeasureTheory.FiniteMeasure.continuous_iff_forall_continuous_integral` and
`MeasureTheory.FiniteMeasure.tendsto_iff_weakDual_tendsto`. -/
recall MeasureTheory.FiniteMeasure.continuous_iff_forall_continuous_integral
recall MeasureTheory.FiniteMeasure.tendsto_iff_weakDual_tendsto

/-- Item (iii) of Remark 13.14: if `E` is separable, then the weak topology on finite measures is
metrizable. The Prohorov metric is the standard source-side metrization. -/
theorem finiteMeasure_weakTopology_metrizable_of_separable
    [TopologicalSpace.SeparableSpace E] :
    TopologicalSpace.MetrizableSpace (MeasureTheory.FiniteMeasure E) := by
  -- Route correction: instead of the brittle normalize-at-zero parametrization, embed finite
  -- measures into probabilities on `E ⊕ Unit` by adding a cemetery atom.
  exact
    (show IsEmbedding
        (finiteMeasureCemeteryEmbedding :
          MeasureTheory.FiniteMeasure E →
            NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) from
      finiteMeasureCemeteryEmbedding_isEmbedding).metrizableSpace

/-- A second item (iii) consequence in Remark 13.14: if `E` is locally compact and Polish, then the
weak topology on finite measures is Polish. -/
theorem finiteMeasure_weakTopology_polish_of_locallyCompact
    [LocallyCompactSpace E] [PolishSpace E] :
    PolishSpace (MeasureTheory.FiniteMeasure E) := by
  letI : MeasurableSpace (E ⊕ Unit) := borel (E ⊕ Unit)
  letI : BorelSpace (E ⊕ Unit) := ⟨rfl⟩
  letI : LocallyCompactSpace (E ⊕ Unit) := sumLocallyCompactSpace
  letI : PolishSpace (E ⊕ Unit) := by infer_instance
  letI : PolishSpace (MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) :=
    probabilityMeasure_polish_of_locallyCompact
  letI : PolishSpace (NNReal × MeasureTheory.ProbabilityMeasure (E ⊕ Unit)) := by infer_instance
  -- Proof comment: once the ambient probability-measure factor is Polish, the closed cemetery
  -- embedding transfers Polishness to finite measures.
  exact finiteMeasureCemeteryEmbedding_isClosedEmbedding.polishSpace

/-- Helper for Remark 13.14: in the weak topology on finite measures, assigning zero mass to an
open set is a closed condition. -/
private theorem finiteMeasure_isClosed_zeroMassOnOpen
    [LocallyCompactSpace E] [PolishSpace E] {U : Set E} (hU : IsOpen U) :
    IsClosed {μ : MeasureTheory.FiniteMeasure E | ((μ : Measure E) U) = 0} := by
  letI : PolishSpace (MeasureTheory.FiniteMeasure E) :=
    finiteMeasure_weakTopology_polish_of_locallyCompact
  refine (isSeqClosed_iff_isClosed).mp ?_
  intro μs μ hμs hμ
  have hprob :
      Tendsto (fun n ↦ finiteMeasureCemeteryProbability (μs n)) atTop
        (𝓝 (finiteMeasureCemeteryProbability μ)) := by
    exact (continuous_finiteMeasureCemeteryProbability.tendsto _).comp hμ
  have hopenInl : IsOpen (Sum.inl '' U : Set (E ⊕ Unit)) := isOpenMap_inl _ hU
  have hliminf :
      ((finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) (Sum.inl '' U)) ≤
        atTop.liminf (fun n ↦
          (finiteMeasureCemeteryProbability (μs n) : Measure (E ⊕ Unit)) (Sum.inl '' U)) :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hprob hopenInl
  have hzeroSeq :
      ∀ n,
        (finiteMeasureCemeteryProbability (μs n) : Measure (E ⊕ Unit)) (Sum.inl '' U) = 0 := by
    intro n
    rw [finiteMeasureCemeteryProbability_apply_inl_image (μ := μs n) hU.measurableSet]
    simpa using hμs n
  have hzeroProb :
      ((finiteMeasureCemeteryProbability μ : Measure (E ⊕ Unit)) (Sum.inl '' U)) = 0 := by
    have hliminfZero :
        atTop.liminf (fun n ↦
          (finiteMeasureCemeteryProbability (μs n) : Measure (E ⊕ Unit)) (Sum.inl '' U)) = 0 := by
      simp [hzeroSeq]
    apply le_antisymm
    · refine le_trans hliminf ?_
      simpa [hliminfZero]
    · exact bot_le
  rw [finiteMeasureCemeteryProbability_apply_inl_image (μ := μ) hU.measurableSet] at hzeroProb
  have hfactor_ne : ((ENNReal.ofNNReal (μ.mass + 1))⁻¹ : ℝ≥0∞) ≠ 0 := by
    simp
  exact (mul_eq_zero.mp hzeroProb).resolve_left hfactor_ne

end WeakTopology

section RadonTopology

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

instance instIsRadonMeasure (μ : { μ : Measure E // IsRadonMeasure μ }) :
    IsRadonMeasure (μ : Measure E) :=
  μ.2

instance instIsLocallyFiniteMeasureRadonMeasureSubtype
    (μ : { μ : Measure E // IsRadonMeasure μ }) :
    IsLocallyFiniteMeasure (μ : Measure E) :=
  IsRadonMeasure.locallyFinite μ.2

/-- Helper for Remark 13.14: on a locally compact Polish space, a Radon measure is finite on
compact sets. -/
private theorem radonMeasure_isFiniteMeasureOnCompacts
    [LocallyCompactSpace E] [PolishSpace E]
    (μ : { μ : Measure E // IsRadonMeasure μ }) :
    IsFiniteMeasureOnCompacts (μ : Measure E) := by
  -- Proof comment: locally finite measures on `σ`-compact pseudometrizable spaces are regular,
  -- and regularity includes finiteness on compact sets.
  letI : IsLocallyFiniteMeasure (μ : Measure E) := IsRadonMeasure.locallyFinite μ.2
  letI : Measure.Regular (μ : Measure E) := by infer_instance
  infer_instance

/-- Helper for Remark 13.14: the pullback of a Radon measure to one compact-exhaustion piece is a
finite measure. -/
private theorem isFiniteMeasure_compactPieceRadonComap
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    IsFiniteMeasure (Measure.comap Subtype.val (μ : Measure E) : Measure ↥(K n)) := by
  -- Proof comment: once the ambient Radon measure is finite on compact sets, pulling it back to
  -- the compact subtype preserves finite-on-compacts, and compactness upgrades this to finiteness.
  letI : IsFiniteMeasureOnCompacts (μ : Measure E) :=
    radonMeasure_isFiniteMeasureOnCompacts μ
  haveI : CompactSpace ↥(K n) := isCompact_iff_compactSpace.mp (K.isCompact n)
  haveI :=
    IsFiniteMeasureOnCompacts.comap' (μ : Measure E) continuous_subtype_val
      (MeasurableEmbedding.subtype_coe (K.isCompact n).measurableSet)
  infer_instance

/-- Helper for Remark 13.14: package the restriction of a Radon measure to a compact-exhaustion
piece as a finite measure on the compact subtype. -/
private def compactPieceRadonFiniteMeasure
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    MeasureTheory.FiniteMeasure ↥(K n) :=
  ⟨Measure.comap Subtype.val (μ : Measure E),
    isFiniteMeasure_compactPieceRadonComap K μ n⟩

/-- Integration against a compactly supported continuous real-valued test function on the Radon
measure space `𝓜(E)`. -/
def radonVagueIntegral (f : C_c(E, ℝ)) : { μ : Measure E // IsRadonMeasure μ } → ℝ :=
  fun μ ↦ ∫ x, f x ∂(μ : Measure E)

omit [BorelSpace E] in
@[simp] theorem radonVagueIntegral_apply (f : C_c(E, ℝ))
    (μ : { μ : Measure E // IsRadonMeasure μ }) :
    radonVagueIntegral f μ = ∫ x, f x ∂(μ : Measure E) :=
  rfl

/-- Helper for Remark 13.14: if a compactly supported test is supported inside `K n`, then its
integral against a Radon measure depends only on the `n`th compact piece. -/
private theorem integral_compactPieceRadonFiniteMeasure_eq
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) {n : ℕ}
    (f : C_c(E, ℝ)) (hf : tsupport f ⊆ K n) :
    ∫ x : ↥(K n), f x ∂(compactPieceRadonFiniteMeasure K μ n : Measure ↥(K n)) =
      ∫ x, f x ∂(μ : Measure E) := by
  have hsubtype :
      ∫ x : ↥(K n), f x ∂(compactPieceRadonFiniteMeasure K μ n : Measure ↥(K n)) =
        ∫ x in K n, f x ∂(μ : Measure E) := by
    -- Proof comment: the compact-piece owner is exactly the pullback of `μ` to the compact
    -- subtype, so the integral rewrites by the standard `Subtype`-comap formula.
    simpa [compactPieceRadonFiniteMeasure] using
      (integral_subtype_comap ((K.isCompact n).measurableSet) f : _)
  have hrestrict :
      ∫ x in K n, f x ∂(μ : Measure E) = ∫ x, f x ∂(μ : Measure E) := by
    -- Proof comment: outside `K n`, the test vanishes because its topological support is already
    -- contained in `K n`.
    calc
      ∫ x in K n, f x ∂(μ : Measure E) = ∫ x, Set.indicator (K n) f x ∂(μ : Measure E) := by
        rw [integral_indicator ((K.isCompact n).measurableSet)]
      _ = ∫ x, f x ∂(μ : Measure E) := by
        refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
        by_cases hx : x ∈ K n
        · simp [hx]
        · have hfx : f x = 0 := by
            by_contra hne
            exact hx (hf (subset_tsupport f hne))
          simp [hx, hfx]
  exact hsubtype.trans hrestrict

/-- Helper for Remark 13.14: compactly supported vague tests factor through one compact-piece
coordinate once the support is contained in that compact piece. -/
private theorem radonVagueIntegral_factorsThroughCompactPiece
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) {n : ℕ}
    (f : C_c(E, ℝ)) (hf : tsupport f ⊆ K n) :
    radonVagueIntegral f μ =
      ∫ x : ↥(K n), f x ∂(compactPieceRadonFiniteMeasure K μ n : Measure ↥(K n)) := by
  -- Proof comment: this is just the compact-piece integral identity rewritten through the owner
  -- definition of the vague test integral.
  symm
  simpa [radonVagueIntegral_apply] using
    integral_compactPieceRadonFiniteMeasure_eq K μ f hf

/-- Helper for Remark 13.14: the compact-piece coordinate map records the restriction of a Radon
measure to each compact exhaustion piece. -/
private def compactPieceRadonEmbedding
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) :
    { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n) :=
  fun μ n ↦ compactPieceRadonFiniteMeasure K μ n

/-- Helper for Remark 13.14: include the `n`th compact exhaustion piece into the next one. -/
private def compactPieceSuccInclusion [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) :
    ↥(K n) → ↥(K (n + 1)) :=
  fun x ↦ ⟨x, K.subset (Nat.le_succ n) x.2⟩

/-- Helper for Remark 13.14: the image of a measurable subset of `K n` stays measurable in
`K (n + 1)` under the canonical inclusion. -/
private theorem measurableSet_compactPieceSuccInclusion_image [LocallyCompactSpace E]
    (K : CompactExhaustion E) (n : ℕ) {s : Set ↥(K n)} (hs : MeasurableSet s) :
    MeasurableSet (compactPieceSuccInclusion K n '' s : Set ↥(K (n + 1))) := by
  have hs' : MeasurableSet (Subtype.val '' s : Set E) := by
    -- Proof comment: pass measurability of the subtype set through the ambient coercion to `E`.
    exact MeasurableSet.subtype_image ((K.isCompact n).measurableSet) hs
  have himage :
      (compactPieceSuccInclusion K n '' s : Set ↥(K (n + 1))) =
        Subtype.val ⁻¹' (Subtype.val '' s : Set E) := by
    -- Proof comment: the successor inclusion does not change the ambient point of `E`.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨y, hy, Subtype.ext hxy⟩
  rw [himage]
  exact measurable_subtype_coe hs'

/-- Helper for Remark 13.14: restricting the `(n + 1)`st compact-piece Radon coordinate back to
`K n` recovers the `n`th compact-piece coordinate. -/
private theorem compactPieceRadonFiniteMeasure_restrict_succ
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    (compactPieceRadonFiniteMeasure K μ (n + 1)).comap (compactPieceSuccInclusion K n) =
      compactPieceRadonFiniteMeasure K μ n := by
  apply FiniteMeasure.toMeasure_injective
  -- Proof comment: both sides are pullbacks of the same ambient Radon measure along nested subtype
  -- inclusions, so `Measure.comap_comap` collapses the tower.
  simpa [compactPieceRadonFiniteMeasure, compactPieceSuccInclusion, Function.comp] using
    (Measure.comap_comap
      (f := compactPieceSuccInclusion K n)
      (g := (Subtype.val : ↥(K (n + 1)) → E))
      (hf' := fun s hs ↦ measurableSet_compactPieceSuccInclusion_image K n hs)
      (hg := Subtype.val_injective)
      (hg' := fun s hs ↦
        MeasurableSet.subtype_image ((K.isCompact (n + 1)).measurableSet) hs)
      (μ := (μ : Measure E)))

/-- Helper for Remark 13.14: there exists a compactly supported continuous bump function that is
identically `1` on `K n`, has topological support inside `K (n + 1)`, and takes values in
`[0, 1]`. -/
private theorem exists_compactPieceBump
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) :
    ∃ f : C_c(E, ℝ), Set.EqOn f 1 (K n) ∧ tsupport f ⊆ K (n + 1) ∧
      ∀ x, f x ∈ Set.Icc 0 1 := by
  obtain ⟨g, hg_one, hg_compact, hg_support, hg_range⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (K.isCompact n) isOpen_interior (K.subset_interior_succ n)
  let f : C_c(E, ℝ) := ⟨g, hg_compact⟩
  -- Proof comment: the Urysohn bump already comes with compact topological support inside the next
  -- exhaustion piece and the standard `[0, 1]` bounds, so it packages directly as a compactly
  -- supported continuous map.
  exact ⟨f, hg_one, hg_support.trans interior_subset, hg_range⟩

/-- Helper for Remark 13.14: a monotone compactly supported cutoff family adapted to the compact
exhaustion, starting from `0` and reaching the value `1` on each exhaustion piece one step later.
-/
private def compactPieceCutoffFamily [LocallyCompactSpace E] (K : CompactExhaustion E) :
    ℕ → C_c(E, ℝ)
  | 0 => 0
  | n + 1 =>
      let b := Classical.choose (exists_compactPieceBump K n)
      compactPieceCutoffFamily K n ⊔ b

/-- Helper for Remark 13.14: every cutoff in the exhaustion-adapted family takes values in
`[0, 1]`. -/
private theorem compactPieceCutoffFamily_mem_Icc
    [LocallyCompactSpace E] (K : CompactExhaustion E) :
    ∀ n x, compactPieceCutoffFamily K n x ∈ Set.Icc 0 1 := by
  intro n
  induction n with
  | zero =>
      intro x
      simp [compactPieceCutoffFamily]
  | succ n ih =>
      intro x
      let b := Classical.choose (exists_compactPieceBump K n)
      have hb : b x ∈ Set.Icc 0 1 :=
        (Classical.choose_spec (exists_compactPieceBump K n)).2.2 x
      rcases ih x with ⟨hprev0, hprev1⟩
      rcases hb with ⟨hb0, hb1⟩
      -- Proof comment: the next cutoff is the pointwise maximum of the previous cutoff and one
      -- more `[0, 1]`-valued bump, so its values stay inside the same interval.
      simpa [compactPieceCutoffFamily, b] using
        (show max (compactPieceCutoffFamily K n x) (b x) ∈ Set.Icc 0 1 from
          ⟨le_trans hprev0 (le_max_left _ _), max_le hprev1 hb1⟩)

/-- Helper for Remark 13.14: each cutoff is supported inside the matching exhaustion piece. -/
private theorem compactPieceCutoffFamily_tsupport_subset
    [LocallyCompactSpace E] (K : CompactExhaustion E) :
    ∀ n, tsupport (compactPieceCutoffFamily K n) ⊆ K n := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial cutoff is identically zero, so its topological support is
      -- empty.
      simp [compactPieceCutoffFamily]
  | succ n ih =>
      let b := Classical.choose (exists_compactPieceBump K n)
      have hb :
          tsupport b ⊆ K (n + 1) :=
        (Classical.choose_spec (exists_compactPieceBump K n)).2.1
      have hsupp :
          Function.support (compactPieceCutoffFamily K (n + 1)) ⊆ K (n + 1) := by
        intro x hx
        by_contra hxK
        have hprev0 : compactPieceCutoffFamily K n x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hxmem
          exact hxK (K.subset (Nat.le_succ n) (ih hxmem))
        have hb0 : b x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hxmem
          exact hxK (hb hxmem)
        have hxne : compactPieceCutoffFamily K (n + 1) x ≠ 0 := by
          simpa [Function.support] using hx
        have hzero : compactPieceCutoffFamily K (n + 1) x = 0 := by
          change max (compactPieceCutoffFamily K n x) (b x) = 0
          simp [hprev0, hb0]
        exact hxne hzero
      -- Proof comment: outside `K (n + 1)`, both ingredients vanish, so the ordinary support is
      -- contained in `K (n + 1)`; closedness of the compact exhaustion then upgrades this to the
      -- topological support statement.
      rw [tsupport]
      exact (closure_mono hsupp).trans <| by
        rw [(K.isClosed (n + 1)).closure_eq]

/-- Helper for Remark 13.14: the cutoff family reaches the value `1` on each exhaustion piece one
step later. -/
private theorem compactPieceCutoffFamily_eqOn_one
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) :
    Set.EqOn (compactPieceCutoffFamily K (n + 1)) 1 (K n) := by
  let b := Classical.choose (exists_compactPieceBump K n)
  intro x hx
  have hb1 : b x = 1 :=
    (Classical.choose_spec (exists_compactPieceBump K n)).1 hx
  have hprev1 : compactPieceCutoffFamily K n x ≤ 1 :=
    (compactPieceCutoffFamily_mem_Icc K n x).2
  -- Proof comment: on `K n`, the new bump is already equal to `1`, so the pointwise maximum is
  -- forced to be `1` as well.
  change max (compactPieceCutoffFamily K n x) (b x) = 1
  rw [hb1, max_eq_right hprev1]

/-- Helper for Remark 13.14: the exhaustion-adapted cutoff family is monotone. -/
private theorem monotone_compactPieceCutoffFamily
    [LocallyCompactSpace E] (K : CompactExhaustion E) :
    Monotone (compactPieceCutoffFamily K) := by
  intro m n hmn
  induction hmn with
  | refl =>
      exact le_rfl
  | @step n h ih =>
      let b := Classical.choose (exists_compactPieceBump K n)
      -- Proof comment: each successor cutoff is defined by taking the pointwise maximum with one
      -- more bump, so the family can only increase.
      refine fun x ↦ (ih x).trans ?_
      simp [compactPieceCutoffFamily, b]

/-- Helper for Remark 13.14: the annulus weights are the successive differences of the monotone
cutoff family. -/
private def annulusWeight [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) : C_c(E, ℝ) :=
  compactPieceCutoffFamily K (n + 1) - compactPieceCutoffFamily K n

/-- Helper for Remark 13.14: every annulus weight is nonnegative. -/
private theorem annulusWeight_nonneg
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) (x : E) :
    0 ≤ annulusWeight K n x := by
  -- Proof comment: the annulus weights are successive differences in a monotone cutoff family.
  exact sub_nonneg.mpr ((monotone_compactPieceCutoffFamily K) (Nat.le_succ n) x)

/-- Helper for Remark 13.14: every annulus weight still takes values in `[0, 1]`. -/
private theorem annulusWeight_mem_Icc
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) (x : E) :
    annulusWeight K n x ∈ Set.Icc 0 1 := by
  constructor
  · exact annulusWeight_nonneg K n x
  · have hnext1 : compactPieceCutoffFamily K (n + 1) x ≤ 1 :=
      (compactPieceCutoffFamily_mem_Icc K (n + 1) x).2
    have hprev0 : 0 ≤ compactPieceCutoffFamily K n x :=
      (compactPieceCutoffFamily_mem_Icc K n x).1
    change compactPieceCutoffFamily K (n + 1) x - compactPieceCutoffFamily K n x ≤ 1
    linarith

/-- Helper for Remark 13.14: each annulus weight is supported inside the next exhaustion piece. -/
private theorem annulusWeight_tsupport_subset
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) :
    tsupport (annulusWeight K n) ⊆ K (n + 1) := by
  rw [annulusWeight, tsupport]
  have hsupp : Function.support (annulusWeight K n) ⊆ K (n + 1) := by
    intro x hx
    by_contra hxK
    have hnext0 : compactPieceCutoffFamily K (n + 1) x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxmem
      exact hxK (compactPieceCutoffFamily_tsupport_subset K (n + 1) hxmem)
    have hprev0 : compactPieceCutoffFamily K n x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxmem
      exact hxK (K.subset (Nat.le_succ n) (compactPieceCutoffFamily_tsupport_subset K n hxmem))
    have hxne : annulusWeight K n x ≠ 0 := by
      simpa [Function.support] using hx
    have hzero : annulusWeight K n x = 0 := by
      simp [annulusWeight, hnext0, hprev0]
    exact hxne hzero
  -- Proof comment: both consecutive cutoffs already vanish outside `K (n + 1)`, so the
  -- difference does as well.
  exact (closure_mono hsupp).trans <| by
    rw [(K.isClosed (n + 1)).closure_eq]

/-- Helper for Remark 13.14: the annulus weights telescope back to the cutoff family. -/
private theorem sum_annulusWeight_eq_cutoff
    [LocallyCompactSpace E] (K : CompactExhaustion E) :
    ∀ N, Finset.sum (Finset.range N) (fun i ↦ annulusWeight K i) =
      compactPieceCutoffFamily K N := by
  intro N
  induction N with
  | zero =>
      simp [compactPieceCutoffFamily]
  | succ N ih =>
      calc
        Finset.sum (Finset.range (N + 1)) (fun i ↦ annulusWeight K i)
            = Finset.sum (Finset.range N) (fun i ↦ annulusWeight K i) + annulusWeight K N := by
                rw [Finset.sum_range_succ]
        _ = compactPieceCutoffFamily K N +
              (compactPieceCutoffFamily K (N + 1) - compactPieceCutoffFamily K N) := by
                rw [ih, annulusWeight]
        _ = compactPieceCutoffFamily K (N + 1) := by
                ext x
                abel

/-- Helper for Remark 13.14: the finite partial sums of the annulus weights form a partition of
unity on the matching exhaustion piece. -/
private theorem sum_annulusWeight_eqOn_one
    [LocallyCompactSpace E] (K : CompactExhaustion E) (N : ℕ) :
    Set.EqOn (Finset.sum (Finset.range (N + 1)) (fun i ↦ annulusWeight K i)) 1 (K N) := by
  intro x hx
  -- Proof comment: the annulus weights telescope to the `(N + 1)`st cutoff, and that cutoff is
  -- already equal to `1` on `K N`.
  simpa [compactPieceCutoffFamily_eqOn_one K N hx] using
    congrArg (fun g : C_c(E, ℝ) ↦ g x) (sum_annulusWeight_eq_cutoff K (N + 1))

/-- Helper for Remark 13.14: later annulus weights vanish on earlier exhaustion pieces. -/
private theorem annulusWeight_eq_zero_on_piece
    [LocallyCompactSpace E] (K : CompactExhaustion E) {N n : ℕ} (hn : N < n) :
    Set.EqOn (annulusWeight K n) 0 (K N) := by
  rcases n with _ | n
  · cases hn
  intro x hx
  have hxPrev : x ∈ K n := K.subset (Nat.le_of_lt_succ hn) hx
  have hcurr : compactPieceCutoffFamily K (n + 1) x = 1 :=
    compactPieceCutoffFamily_eqOn_one K n hxPrev
  have hxNext : x ∈ K (n + 1) := K.subset (Nat.le_succ n) hxPrev
  have hnext : compactPieceCutoffFamily K (n + 2) x = 1 :=
    compactPieceCutoffFamily_eqOn_one K (n + 1) hxNext
  -- Proof comment: once a point already belongs to an earlier compact piece, both consecutive
  -- cutoffs have stabilized to `1`, so their difference vanishes there.
  simp [annulusWeight, hcurr, hnext]

/-- Helper for Remark 13.14: the compact-piece coordinates separate Radon measures because every
compactly supported test already lives on one compact exhaustion piece. -/
private theorem compactPieceRadonEmbedding_injective
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) :
    Function.Injective (compactPieceRadonEmbedding K) := by
  intro μ ν hcoord
  apply Subtype.ext
  let hsep :
      IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
        (((↑) : C_c(E, ℝ) → E → ℝ) ''
          compactlySupportedUnitIntervalLipschitzRealMapSpace E) :=
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
  -- Proof comment: equality of every compact-piece coordinate forces equality of the integral of
  -- every compactly supported test, so the separating-family theorem identifies the measures.
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep μ.2 ν.2 <| by
    intro g hg _ _
    rcases hg with ⟨g0, -, rfl⟩
    rcases K.exists_superset_of_isCompact g0.hasCompactSupport.isCompact with ⟨n, hgn⟩
    calc
      radonVagueIntegral g0 μ
          = ∫ x : ↥(K n), g0 x
              ∂(compactPieceRadonEmbedding K μ n : Measure ↥(K n)) := by
              simpa [compactPieceRadonEmbedding] using
                radonVagueIntegral_factorsThroughCompactPiece K μ g0 hgn
      _ = ∫ x : ↥(K n), g0 x
              ∂(compactPieceRadonEmbedding K ν n : Measure ↥(K n)) := by
              rw [congrFun hcoord n]
      _ = radonVagueIntegral g0 ν := by
              simpa [compactPieceRadonEmbedding] using
                (radonVagueIntegral_factorsThroughCompactPiece K ν g0 hgn).symm

/-- Helper for Remark 13.14: the `n`th compact layer is the new part of `K n` that is not already
inside the previous compact set. -/
private def compactLayer [LocallyCompactSpace E] (K : CompactExhaustion E) : ℕ → Set E
  | 0 => K 0
  | n + 1 => K (n + 1) \ K n

/-- Helper for Remark 13.14: every compact layer is measurable. -/
private theorem compactLayer_measurableSet [LocallyCompactSpace E] (K : CompactExhaustion E)
    (n : ℕ) : MeasurableSet (compactLayer K n) := by
  -- Proof comment: each layer is a measurable difference of two compact exhaustion pieces.
  cases n with
  | zero =>
      simpa [compactLayer] using (K.isCompact 0).measurableSet
  | succ n =>
      simpa [compactLayer] using
        (K.isCompact (n + 1)).measurableSet.diff (K.isCompact n).measurableSet

/-- Helper for Remark 13.14: each compact layer sits inside the corresponding compact piece. -/
private theorem compactLayer_subset_piece [LocallyCompactSpace E] (K : CompactExhaustion E)
    (n : ℕ) : compactLayer K n ⊆ K n := by
  -- Proof comment: this is immediate from the definition of the layers.
  cases n with
  | zero =>
      simpa [compactLayer]
  | succ n =>
      simpa [compactLayer] using inter_subset_left

/-- Helper for Remark 13.14: later compact layers are disjoint from earlier compact pieces. -/
private theorem compactLayer_disjoint_piece [LocallyCompactSpace E] (K : CompactExhaustion E)
    {m n : ℕ} (hmn : m < n) : Disjoint (K m) (compactLayer K n) := by
  -- Proof comment: `K m` already sits inside the interior of `K (n - 1)`, while the `n`th layer
  -- is defined to avoid that interior.
  rcases n with _ | n
  · cases hmn
  · refine Set.disjoint_left.2 ?_
    intro x hx hm
    exact hm.2 (K.subset (Nat.lt_succ_iff.mp hmn) hx)

/-- Helper for Remark 13.14: distinct compact layers are disjoint. -/
private theorem compactLayer_pairwiseDisjoint [LocallyCompactSpace E] (K : CompactExhaustion E) :
    Pairwise fun m n ↦ Disjoint (compactLayer K m) (compactLayer K n) := by
  -- Proof comment: if `m < n`, then the `m`th layer lies in `K m`, which is already disjoint from
  -- the later `n`th layer.
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact (compactLayer_disjoint_piece K hlt).mono_left (compactLayer_subset_piece K m)
  · exact (compactLayer_disjoint_piece K hgt).symm.mono_right (compactLayer_subset_piece K n)

/-- Helper for Remark 13.14: the compact layers cover the whole space. -/
private theorem iUnion_compactLayer_eq_univ [LocallyCompactSpace E] (K : CompactExhaustion E) :
    ⋃ n, compactLayer K n = Set.univ := by
  -- Proof comment: place `x` in the first compact piece that contains it; then it lies in the
  -- corresponding new layer because it cannot belong to the previous compact piece.
  ext x
  constructor
  · intro _
    trivial
  · intro _
    cases hfind : K.find x with
    | zero =>
        refine Set.mem_iUnion.2 ⟨0, ?_⟩
        simpa [compactLayer, hfind] using K.mem_find x
    | succ n =>
        refine Set.mem_iUnion.2 ⟨n + 1, ?_⟩
        refine ⟨by simpa [compactLayer, hfind] using K.mem_find x, ?_⟩
        intro hxPrev
        have hle : K.find x ≤ n := (K.mem_iff_find_le).mp hxPrev
        simpa [hfind] using hle

/-- Helper for Remark 13.14: a Radon measure is finite on the compact layers. -/
private def compactLayerRadonFiniteMeasure
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    MeasureTheory.FiniteMeasure ↥(compactLayer K n) :=
  ⟨Measure.comap Subtype.val (μ : Measure E), by
    -- Proof comment: the layer sits inside the compact piece `K n`, so its pullback mass is
    -- bounded by the finite mass of that compact exhaustion piece.
    letI : IsFiniteMeasureOnCompacts (μ : Measure E) :=
      radonMeasure_isFiniteMeasureOnCompacts μ
    refine ⟨?_⟩
    rw [show (Measure.comap Subtype.val (μ : Measure E)) Set.univ =
        (μ : Measure E) (compactLayer K n) by
          simpa using comap_subtype_coe_apply
            (compactLayer_measurableSet K n) (μ : Measure E)
            (Set.univ : Set ↥(compactLayer K n))]
    exact (measure_mono (compactLayer_subset_piece K n)).trans_lt
      ((K.isCompact n).measure_lt_top)
  ⟩

/-- Helper for Remark 13.14: recover a measure from arbitrary compact-layer coordinates by summing
their pushforwards along the subtype inclusions. -/
private def compactLayerRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(compactLayer K n)) :
    Measure E :=
  Measure.sum fun n ↦
    (u n : Measure ↥(compactLayer K n)).map Subtype.val

/-- Helper for Remark 13.14: the compact-layer recovery measure is locally finite because every
compact exhaustion piece meets only finitely many layers. -/
private theorem isLocallyFiniteMeasure_compactLayerRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(compactLayer K n)) :
    IsLocallyFiniteMeasure (compactLayerRecoveryMeasure K u) := by
  -- Proof comment: around `x`, choose one compact exhaustion piece `K N` already in the
  -- neighborhood filter. All later layers are disjoint from `K N`, so only finitely many finite
  -- layer measures contribute there.
  constructor
  intro x
  rcases K.exists_mem_nhds x with ⟨N, hKN⟩
  refine ⟨K N, hKN, ?_⟩
  rw [compactLayerRecoveryMeasure, Measure.sum_apply _ (K.isCompact N).measurableSet]
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        ((u n : Measure ↥(compactLayer K n)).map Subtype.val) (K N) = 0 := by
    intro n hn
    have hNn : N < n := by
      exact Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hn)
    have hdisj :
        Disjoint (K N) (compactLayer K n) :=
      compactLayer_disjoint_piece K hNn
    have hpre :
        Subtype.val ⁻¹' K N = (∅ : Set ↥(compactLayer K n)) := by
      ext y
      constructor
      · intro hy
        exact False.elim (hdisj.le_bot ⟨hy, y.2⟩)
      · intro hy
        simp at hy
    rw [Measure.map_apply measurable_subtype_coe (K.isCompact N).measurableSet, hpre, measure_empty]
  rw [tsum_eq_sum hzero]
  simp [measure_lt_top]

/-- Helper for Remark 13.14: package the compact-layer recovery measure as a Radon measure. -/
private def compactLayerRecovery
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(compactLayer K n)) :
    { μ : Measure E // IsRadonMeasure μ } :=
  ⟨compactLayerRecoveryMeasure K u, by
    letI := isLocallyFiniteMeasure_compactLayerRecoveryMeasure K u
    exact IsRadonMeasure.of_owner _⟩

/-- Helper for Remark 13.14: the compact-layer recovery map is a left inverse to the layer
restriction map on Radon measures. -/
private theorem compactLayerRecovery_leftInverse
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Function.LeftInverse
      (compactLayerRecovery K)
      (fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        fun n ↦ compactLayerRadonFiniteMeasure K μ n) := by
  intro μ
  apply Subtype.ext
  ext A hA
  -- Proof comment: the recovered measure is the countable sum of the disjoint restrictions to the
  -- compact layers, and these layers partition the whole space.
  have hmap :
      ∀ n,
        (((compactLayerRadonFiniteMeasure K μ n : MeasureTheory.FiniteMeasure
            ↥(compactLayer K n)) : Measure ↥(compactLayer K n)).map Subtype.val) A =
          (μ : Measure E) (A ∩ compactLayer K n) := by
    intro n
    simp [compactLayerRadonFiniteMeasure, map_comap_subtype_coe
      (compactLayer_measurableSet K n), Measure.restrict_apply hA]
  have hpair :
      Pairwise fun i j ↦ Disjoint (A ∩ compactLayer K i) (A ∩ compactLayer K j) :=
    (compactLayer_pairwiseDisjoint K).mono fun i j hij ↦
      hij.mono inf_le_right inf_le_right
  have hUnion :
      (⋃ n, A ∩ compactLayer K n) = A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨n, hxn⟩
      exact hxn.1
    · intro hx
      rcases Set.mem_iUnion.1 (show x ∈ ⋃ n, compactLayer K n by
        simpa [iUnion_compactLayer_eq_univ K]) with ⟨n, hxn⟩
      exact Set.mem_iUnion.2 ⟨n, ⟨hx, hxn⟩⟩
  calc
    ((compactLayerRecovery K
        (fun n ↦ compactLayerRadonFiniteMeasure K μ n) : { μ : Measure E // IsRadonMeasure μ })
        : Measure E) A
        = ∑' n, (((compactLayerRadonFiniteMeasure K μ n : MeasureTheory.FiniteMeasure
            ↥(compactLayer K n)) : Measure ↥(compactLayer K n)).map Subtype.val) A := by
          change compactLayerRecoveryMeasure K
              (fun n ↦ compactLayerRadonFiniteMeasure K μ n) A = _
          rw [compactLayerRecoveryMeasure, Measure.sum_apply _ hA]
    _ = ∑' n, (μ : Measure E) (A ∩ compactLayer K n) := by
          congr with n
          exact hmap n
    _ = (μ : Measure E) (⋃ n, A ∩ compactLayer K n) := by
          symm
          exact measure_iUnion hpair (fun n ↦ hA.inter (compactLayer_measurableSet K n))
    _ = (μ : Measure E) A := by rw [hUnion]

/-- The vague topology on Radon measures: the coarsest topology making every compactly supported
continuous real-valued test-function integral continuous. -/
@[reducible] def vagueTopology (E : Type u) [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
  ⨅ f : C_c(E, ℝ),
    TopologicalSpace.induced (radonVagueIntegral f) inferInstance

instance instTopologicalSpaceRadonMeasureSubtype :
    TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
  vagueTopology E

/-- Helper for Remark 13.14: the topology induced by the compact-piece coordinate map is finer
than the vague topology, because every vague test factors through one compact piece. -/
private theorem compactPieceRadonEmbedding_induced_le_vague
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) :
    TopologicalSpace.induced (compactPieceRadonEmbedding K) inferInstance ≤
      (inferInstance : TopologicalSpace { μ : Measure E // IsRadonMeasure μ }) := by
  rw [instTopologicalSpaceRadonMeasureSubtype, vagueTopology]
  refine le_iInf ?_
  intro f
  rcases K.exists_superset_of_isCompact f.hasCompactSupport.isCompact with ⟨n, hfn⟩
  let g : C(↥(K n), ℝ) :=
    { toFun := fun x ↦ f x
      continuous_toFun := f.continuous.comp continuous_subtype_val }
  have hfactor :
      radonVagueIntegral f =
        fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
          ∫ x, g x
            ∂(compactPieceRadonEmbedding K μ n : Measure ↥(K n)) := by
    funext μ
    -- Proof comment: once the support of `f` sits inside `K n`, the ambient vague integral is
    -- exactly the integral of the `n`th compact-piece coordinate.
    simpa [compactPieceRadonEmbedding, g] using
      radonVagueIntegral_factorsThroughCompactPiece K μ f hfn
  haveI : CompactSpace ↥(K n) := isCompact_iff_compactSpace.mp (K.isCompact n)
  letI : TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
    TopologicalSpace.induced (compactPieceRadonEmbedding K) inferInstance
  have hcoord :
      Continuous fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        compactPieceRadonEmbedding K μ n := by
    -- Proof comment: under the induced compact-piece topology, each coordinate projection is
    -- continuous by construction.
    simpa [Function.comp, compactPieceRadonEmbedding] using
      (continuous_apply n).comp
        (continuous_induced_dom :
          Continuous (compactPieceRadonEmbedding K))
  have hcont :
      Continuous fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        ∫ x, g x
          ∂(compactPieceRadonEmbedding K μ n : Measure ↥(K n)) :=
    (FiniteMeasure.continuous_integral_continuousMap g).comp hcoord
  exact continuous_iff_le_induced.mp <| by
    simpa [hfactor] using hcont

/-- Helper for Remark 13.14: the annulus weight restricted to the next compact piece is a
nonnegative continuous density. -/
private def annulusWeightOnCompactPiece
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) :
    C(↥(K (n + 1)), NNReal) :=
  { toFun := fun x ↦ ⟨annulusWeight K n x, annulusWeight_nonneg K n x⟩
    continuous_toFun :=
      Continuous.subtype_mk
        ((annulusWeight K n).continuous.comp continuous_subtype_val)
        (fun x ↦ annulusWeight_nonneg K n x) }

/-- Helper for Remark 13.14: the annulus-weighted restriction of a compactly supported test to one
compact exhaustion piece. -/
private def weightedCompactPieceTest
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) (f : C_c(E, ℝ)) :
    C(↥(K (n + 1)), ℝ) :=
  { toFun := fun x ↦ annulusWeightOnCompactPiece K n x • f x
    continuous_toFun :=
      (annulusWeightOnCompactPiece K n).continuous.smul
        (f.continuous.comp continuous_subtype_val) }

/-- Helper for Remark 13.14: the support of the weighted test `annulusWeight K n * f` stays inside
`K (n + 1)`. -/
private theorem annulusWeight_mul_tsupport_subset
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) (f : C_c(E, ℝ)) :
    tsupport (annulusWeight K n * f) ⊆ K (n + 1) := by
  simpa using
    ((tsupport_mul_subset_left
      (f := fun x ↦ annulusWeight K n x) (g := fun x ↦ f x)).trans
        (annulusWeight_tsupport_subset K n))

/-- Helper for Remark 13.14: the `n`th annulus-weighted coordinate measure on the raw
compact-piece product. -/
private def compactPieceWeightedRecoverySummand
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) (n : ℕ) :
    Measure E :=
  Measure.map Subtype.val <|
    (u (n + 1) : Measure ↥(K (n + 1))).withDensity
      fun x ↦ ((annulusWeightOnCompactPiece K n x : NNReal) : ℝ≥0∞)

/-- Helper for Remark 13.14: evaluating one annulus-weighted recovery summand on a measurable set
rewrites directly to the restricted `withDensity` formula on the corresponding compact piece. -/
private theorem compactPieceWeightedRecoverySummand_apply
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) (n : ℕ) {s : Set E}
    (hs : MeasurableSet s) :
    compactPieceWeightedRecoverySummand K u n s =
      ∫⁻ x in Subtype.val ⁻¹' s,
        ((annulusWeightOnCompactPiece K n x : NNReal) : ℝ≥0∞)
          ∂(u (n + 1) : Measure ↥(K (n + 1))) := by
  -- Proof comment: unfold the pushforward summand once and then use the exact `withDensity_apply'`
  -- formula on the compact-piece coordinate measure.
  rw [compactPieceWeightedRecoverySummand, Measure.map_apply measurable_subtype_coe hs,
    withDensity_apply']

/-- Helper for Remark 13.14: the annulus-weighted recovery measure on the raw compact-piece
product. -/
private def compactPieceWeightedRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) :
    Measure E :=
  Measure.sum (compactPieceWeightedRecoverySummand K u)

/-- Helper for Remark 13.14: each annulus-weighted summand is dominated by the corresponding raw
compact-piece coordinate measure after mapping to `E`. -/
private theorem compactPieceWeightedRecoverySummand_le
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) (n : ℕ) :
    compactPieceWeightedRecoverySummand K u n ≤
      Measure.map Subtype.val (u (n + 1) : Measure ↥(K (n + 1))) := by
  refine Measure.map_mono ?_ measurable_subtype_coe
  calc
    (u (n + 1) : Measure ↥(K (n + 1))).withDensity
        (fun x ↦ ((annulusWeightOnCompactPiece K n x : NNReal) : ℝ≥0∞))
      ≤ (u (n + 1) : Measure ↥(K (n + 1))).withDensity 1 := by
          -- Proof comment: the annulus density takes values in `[0, 1]`, so weighting can only
          -- decrease the source compact-piece measure.
          refine withDensity_mono <| Filter.Eventually.of_forall fun x ↦ ?_
          simpa [annulusWeightOnCompactPiece] using (annulusWeight_mem_Icc K n x).2
    _ = (u (n + 1) : Measure ↥(K (n + 1))) := by rw [withDensity_one]

/-- Helper for Remark 13.14: later annulus-weighted recovery summands give zero mass to earlier
compact exhaustion pieces. -/
private theorem compactPieceWeightedRecoverySummand_eq_zero_on_piece
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) {N n : ℕ} (hn : N < n) :
    compactPieceWeightedRecoverySummand K u n (K N) = 0 := by
  -- Proof comment: on `K N`, the annulus weight for every later index `n` is already zero, so the
  -- `withDensity` formula collapses to a zero set integral.
  rw [compactPieceWeightedRecoverySummand_apply K u n (K.isCompact N).measurableSet]
  rw [setLIntegral_eq_zero_iff
      (measurable_subtype_coe ((K.isCompact N).measurableSet))
      ((annulusWeightOnCompactPiece K n).continuous.measurable.coe_nnreal_ennreal)]
  exact Filter.Eventually.of_forall fun x hx ↦ by
    have hzero : annulusWeight K n x = 0 := annulusWeight_eq_zero_on_piece K hn hx
    have hzeroNN : (annulusWeightOnCompactPiece K n x : NNReal) = 0 := by
      ext
      simpa [annulusWeightOnCompactPiece] using hzero
    simpa using congrArg (fun r : NNReal ↦ (r : ℝ≥0∞)) hzeroNN

/-- Helper for Remark 13.14: the annulus-weighted recovery measure is locally finite because only
finitely many annuli meet a fixed compact exhaustion piece. -/
private theorem isLocallyFiniteMeasure_compactPieceWeightedRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) :
    IsLocallyFiniteMeasure (compactPieceWeightedRecoveryMeasure K u) := by
  constructor
  intro x
  rcases K.exists_mem_nhds x with ⟨N, hKN⟩
  refine ⟨K N, hKN, ?_⟩
  rw [compactPieceWeightedRecoveryMeasure, Measure.sum_apply _ (K.isCompact N).measurableSet]
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        compactPieceWeightedRecoverySummand K u n (K N) = 0 := by
    intro n hn
    exact compactPieceWeightedRecoverySummand_eq_zero_on_piece K u <|
      Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hn)
  rw [tsum_eq_sum hzero]
  -- Proof comment: only finitely many annulus summands survive on `K N`, and each surviving
  -- summand is bounded by the corresponding raw compact-piece coordinate measure.
  have hbound :
      Finset.sum (Finset.range (N + 1)) (fun i ↦ compactPieceWeightedRecoverySummand K u i (K N))
        ≤ Finset.sum (Finset.range (N + 1))
            (fun i ↦ Measure.map Subtype.val (u (i + 1) : Measure ↥(K (i + 1))) (K N)) := by
    refine Finset.sum_le_sum fun i hi ↦ ?_
    exact (compactPieceWeightedRecoverySummand_le K u i) (K N)
  have hfinite :
      Finset.sum (Finset.range (N + 1))
          (fun i ↦ Measure.map Subtype.val (u (i + 1) : Measure ↥(K (i + 1))) (K N)) < ∞ := by
    simp [measure_lt_top]
  exact lt_of_le_of_lt hbound hfinite

/-- Helper for Remark 13.14: the annulus-weighted recovery measure is Radon because the preceding
local-finiteness result lets the standard owner instance package it as a Radon measure. -/
private theorem isRadonMeasure_compactPieceWeightedRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) :
    IsRadonMeasure (compactPieceWeightedRecoveryMeasure K u) := by
  letI : IsLocallyFiniteMeasure (compactPieceWeightedRecoveryMeasure K u) :=
    isLocallyFiniteMeasure_compactPieceWeightedRecoveryMeasure K u
  -- Proof comment: on locally compact Polish spaces, locally finite Borel measures are Radon.
  exact IsRadonMeasure.of_owner _

/-- Helper for Remark 13.14: package the annulus-weighted recovery measure as a Radon measure. -/
private def compactPieceWeightedRecovery
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    ((n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) → { μ : Measure E // IsRadonMeasure μ } :=
  fun u ↦
    ⟨compactPieceWeightedRecoveryMeasure K u,
      isRadonMeasure_compactPieceWeightedRecoveryMeasure K u⟩

/-- Helper for Remark 13.14: integrating a compactly supported test against one annulus-weighted
summand is the same as integrating the weighted restriction against the corresponding coordinate. -/
private theorem integral_compactPieceWeightedRecoverySummand_eq
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) (n : ℕ) (f : C_c(E, ℝ)) :
    ∫ x, f x ∂(compactPieceWeightedRecoverySummand K u n) =
      ∫ x : ↥(K (n + 1)), weightedCompactPieceTest K n f x
        ∂(u (n + 1) : Measure ↥(K (n + 1))) := by
  -- Proof comment: first pull the ambient integral back along the subtype embedding, then rewrite
  -- the weighted measure integral by the standard `withDensity` Bochner formula.
  rw [compactPieceWeightedRecoverySummand,
    MeasurableEmbedding.integral_map
      (MeasurableEmbedding.subtype_coe ((K.isCompact (n + 1)).measurableSet))]
  simpa [weightedCompactPieceTest] using
    (integral_withDensity_eq_integral_smul
      (μ := (u (n + 1) : Measure ↥(K (n + 1))))
      (f_meas := (annulusWeightOnCompactPiece K n).continuous.measurable)
      (g := fun x : ↥(K (n + 1)) ↦ f x))

/-- Helper for Remark 13.14: if the support of `f` is already contained in `K N`, then every
later weighted compact-piece test vanishes identically. -/
private theorem weightedCompactPieceTest_eq_zero_of_tsupport_subset
    [LocallyCompactSpace E] (K : CompactExhaustion E) (f : C_c(E, ℝ))
    {N i : ℕ} (hf : tsupport f ⊆ K N) (hNi : N < i) :
    weightedCompactPieceTest K i f = 0 := by
  ext x
  by_cases hx : ((x : ↥(K (i + 1))) : E) ∈ K N
  · -- Proof comment: on the earlier compact piece, the later annulus weight is already zero.
    have hzero : annulusWeight K i x = 0 := annulusWeight_eq_zero_on_piece K hNi hx
    have hzero' : (annulusWeightOnCompactPiece K i x : NNReal) = 0 := by
      ext
      simpa [annulusWeightOnCompactPiece] using hzero
    change (annulusWeightOnCompactPiece K i x : NNReal) • f x = 0
    rw [hzero']
    exact zero_smul NNReal (f x)
  · -- Proof comment: away from `K N`, the support hypothesis forces the original test to vanish.
    have hfx : f x = 0 := by
      by_contra hne
      exact hx (hf (subset_tsupport f hne))
    simp [weightedCompactPieceTest, hfx]

/-- Helper for Remark 13.14: the weighted coordinate integral of the compact-piece embedding is
the ambient vague integral of the corresponding annulus-weighted test. -/
private theorem radonVagueIntegral_annulusWeight_mul_eq_weightedCompactPieceIntegral
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (μ : { μ : Measure E // IsRadonMeasure μ }) (i : ℕ) (f : C_c(E, ℝ)) :
    radonVagueIntegral (annulusWeight K i * f) μ =
      ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
        ∂(compactPieceRadonEmbedding K μ (i + 1) : Measure ↥(K (i + 1))) := by
  -- Proof comment: the annulus-weighted test is supported inside `K (i + 1)`, so the owner
  -- compact-piece factorization lemma applies directly.
  simpa [compactPieceRadonEmbedding, weightedCompactPieceTest, annulusWeightOnCompactPiece,
    Pi.mul_apply] using
    (radonVagueIntegral_factorsThroughCompactPiece K μ (annulusWeight K i * f)
      (annulusWeight_mul_tsupport_subset K i f))

/-- Helper for Remark 13.14: if `tsupport f ⊆ K N`, then integrating `f` against the
annulus-weighted recovery measure reduces to a finite weighted sum over the first `N + 1`
compact-piece coordinates. -/
private theorem radonVagueIntegral_compactPieceWeightedRecovery_eq_sum
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n))
    (f : C_c(E, ℝ)) {N : ℕ} (hf : tsupport f ⊆ K N) :
    radonVagueIntegral f (compactPieceWeightedRecovery K u) =
      Finset.sum (Finset.range (N + 1)) fun i ↦
        ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
          ∂(u (i + 1) : Measure ↥(K (i + 1))) := by
  letI : IsFiniteMeasureOnCompacts (compactPieceWeightedRecoveryMeasure K u) := by
    letI : IsLocallyFiniteMeasure (compactPieceWeightedRecoveryMeasure K u) :=
      IsRadonMeasure.locallyFinite (isRadonMeasure_compactPieceWeightedRecoveryMeasure K u)
    letI : Measure.Regular (compactPieceWeightedRecoveryMeasure K u) := by infer_instance
    infer_instance
  have hfInt : Integrable f (compactPieceWeightedRecoveryMeasure K u) := f.integrable
  have hsum :
      radonVagueIntegral f (compactPieceWeightedRecovery K u) =
        ∑' i,
          ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
            ∂(u (i + 1) : Measure ↥(K (i + 1))) := by
    -- Proof comment: expand the recovery measure as a countable sum, then rewrite each summand
    -- integral by the dedicated coordinate formula.
    calc
      radonVagueIntegral f (compactPieceWeightedRecovery K u)
          = ∫ x, f x ∂(compactPieceWeightedRecoveryMeasure K u) := by
              rfl
      _ = ∑' i, ∫ x, f x ∂(compactPieceWeightedRecoverySummand K u i) := by
            rw [compactPieceWeightedRecoveryMeasure, integral_sum_measure hfInt]
      _ = ∑' i,
            ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
              ∂(u (i + 1) : Measure ↥(K (i + 1))) := by
            congr with i
            exact integral_compactPieceWeightedRecoverySummand_eq K u i f
  have hzero :
      ∀ i ∉ Finset.range (N + 1),
        ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
          ∂(u (i + 1) : Measure ↥(K (i + 1))) = 0 := by
    intro i hi
    have hNi : N < i := Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hi)
    -- Proof comment: once the weighted test is identically zero, the corresponding tail integral
    -- vanishes by simplification.
    rw [weightedCompactPieceTest_eq_zero_of_tsupport_subset K f hf hNi]
    simp
  -- Proof comment: the support condition kills the infinite tail, leaving the finite prefix sum.
  rw [hsum, tsum_eq_sum hzero]

/-- Helper for Remark 13.14: the annulus-weighted recovery map is a left inverse to the
compact-piece embedding. -/
private theorem compactPieceWeightedRecovery_leftInverse
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Function.LeftInverse (compactPieceWeightedRecovery K) (compactPieceRadonEmbedding K) := by
  intro μ
  apply Subtype.ext
  let hsep :
      IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
        (((↑) : C_c(E, ℝ) → E → ℝ) ''
          compactlySupportedUnitIntervalLipschitzRealMapSpace E) :=
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
  -- Proof comment: compare the recovered and original Radon measures through all compactly
  -- supported separating tests.
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep
    (compactPieceWeightedRecovery K (compactPieceRadonEmbedding K μ)).2 μ.2 <| by
    intro g hg _ _
    rcases hg with ⟨g0, -, rfl⟩
    rcases K.exists_superset_of_isCompact g0.hasCompactSupport.isCompact with ⟨N, hgN⟩
    letI : IsFiniteMeasureOnCompacts (μ : Measure E) := radonMeasure_isFiniteMeasureOnCompacts μ
    have hIntAnnulus :
        ∀ i ∈ Finset.range (N + 1),
          Integrable (fun x ↦ (annulusWeight K i * g0) x) (μ : Measure E) := by
      intro i hi
      simpa using (annulusWeight K i * g0).integrable
    calc
      radonVagueIntegral g0
          (compactPieceWeightedRecovery K (compactPieceRadonEmbedding K μ))
          = Finset.sum (Finset.range (N + 1)) fun i ↦
              ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i g0 x
                ∂(compactPieceRadonEmbedding K μ (i + 1) : Measure ↥(K (i + 1))) := by
              exact radonVagueIntegral_compactPieceWeightedRecovery_eq_sum
                K (compactPieceRadonEmbedding K μ) g0 hgN
      _ = Finset.sum (Finset.range (N + 1))
            (fun i ↦ radonVagueIntegral (annulusWeight K i * g0) μ) := by
            refine Finset.sum_congr rfl fun i hi ↦ ?_
            symm
            exact radonVagueIntegral_annulusWeight_mul_eq_weightedCompactPieceIntegral K μ i g0
      _ = radonVagueIntegral
            (Finset.sum (Finset.range (N + 1)) fun i ↦ annulusWeight K i * g0) μ := by
            calc
              Finset.sum (Finset.range (N + 1))
                  (fun i ↦ radonVagueIntegral (annulusWeight K i * g0) μ)
                  = Finset.sum (Finset.range (N + 1))
                      (fun i ↦ ∫ x, (annulusWeight K i * g0) x ∂(μ : Measure E)) := by
                      simp [radonVagueIntegral_apply]
              _ = ∫ x, (Finset.sum (Finset.range (N + 1))
                      fun i ↦ (annulusWeight K i * g0) x)
                      ∂(μ : Measure E) := by
                      symm
                      exact integral_finset_sum (s := Finset.range (N + 1))
                        (f := fun i x ↦ (annulusWeight K i * g0) x) hIntAnnulus
              _ = radonVagueIntegral
                    (Finset.sum (Finset.range (N + 1)) fun i ↦ annulusWeight K i * g0) μ := by
                      rw [radonVagueIntegral_apply]
                      congr with x
                      simp
      _ = radonVagueIntegral
            ((Finset.sum (Finset.range (N + 1)) fun i ↦ annulusWeight K i) * g0) μ := by
            congr 1
            ext x
            simp [Finset.sum_mul]
      _ = radonVagueIntegral g0 μ := by
            rw [radonVagueIntegral_apply]
            refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
            by_cases hx : x ∈ K N
            · -- Proof comment: on `K N`, the annulus weights sum to `1`.
              simp [sum_annulusWeight_eqOn_one K N hx]
            · -- Proof comment: outside `K N`, the original compactly supported test already
              -- vanishes by the support containment.
              have hgx : g0 x = 0 := by
                by_contra hne
                exact hx (hgN (subset_tsupport g0 hne))
              simp [hgx]

/-- Helper for Remark 13.14: the annulus-weighted recovery map is continuous for the vague
topology because every vague test becomes a finite sum of coordinate integrals. -/
private theorem continuous_compactPieceWeightedRecovery
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Continuous
      (compactPieceWeightedRecovery K :
        ((n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) →
          { μ : Measure E // IsRadonMeasure μ }) := by
  rw [instTopologicalSpaceRadonMeasureSubtype, vagueTopology]
  refine continuous_iInf_rng.2 fun f ↦ ?_
  rw [continuous_induced_rng]
  rcases K.exists_superset_of_isCompact f.hasCompactSupport.isCompact with ⟨N, hfN⟩
  have hEq :
      (fun u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n) ↦
        radonVagueIntegral f (compactPieceWeightedRecovery K u)) =
        fun u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n) ↦
          Finset.sum (Finset.range (N + 1)) fun i ↦
            ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
              ∂(u (i + 1) : Measure ↥(K (i + 1))) := by
    funext u
    exact radonVagueIntegral_compactPieceWeightedRecovery_eq_sum K u f hfN
  have hEq' :
      radonVagueIntegral f ∘ compactPieceWeightedRecovery K =
        fun u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n) ↦
          Finset.sum (Finset.range (N + 1)) fun i ↦
            ∫ x : ↥(K (i + 1)), weightedCompactPieceTest K i f x
              ∂(u (i + 1) : Measure ↥(K (i + 1))) := by
    simpa [Function.comp] using hEq
  -- Proof comment: once the vague test integral is rewritten as a finite sum of coordinate
  -- integrals, continuity follows termwise from the compact-factor finite-measure API.
  rw [hEq']
  refine continuous_finset_sum _ fun i hi ↦ ?_
  haveI : CompactSpace ↥(K (i + 1)) := isCompact_iff_compactSpace.mp (K.isCompact (i + 1))
  simpa using
    (FiniteMeasure.continuous_integral_continuousMap (weightedCompactPieceTest K i f)).comp
      (continuous_apply (i + 1))

/-- Helper for Remark 13.14: each annulus-weighted recovery summand is finite because it is
dominated by the corresponding mapped compact-piece finite measure. -/
private theorem isFiniteMeasure_compactPieceWeightedRecoverySummand
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) (n : ℕ) :
    IsFiniteMeasure (compactPieceWeightedRecoverySummand K u n) := by
  let ν : Measure ↥(K (n + 1)) := (u (n + 1) : Measure ↥(K (n + 1)))
  letI : IsFiniteMeasure (Measure.map Subtype.val ν) := by
    infer_instance
  -- Proof comment: the annulus density is bounded by `1`, so the summand sits below a finite
  -- mapped compact-piece measure.
  exact MeasureTheory.isFiniteMeasure_of_le _ (compactPieceWeightedRecoverySummand_le K u n)

/-- Helper for Remark 13.14: the `n`th annulus-weighted piece of a Radon measure, viewed as an
ambient finite measure on `E`. -/
private def compactPieceWeightedFiniteMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    MeasureTheory.FiniteMeasure E :=
  ⟨compactPieceWeightedRecoverySummand K (compactPieceRadonEmbedding K μ) n,
    isFiniteMeasure_compactPieceWeightedRecoverySummand K
      (compactPieceRadonEmbedding K μ) n⟩

/-- Helper for Remark 13.14: integrating a bounded continuous test against one weighted finite
coordinate is the same as integrating the compactly supported weighted test against the original
Radon measure. -/
private theorem integral_compactPieceWeightedFiniteMeasure_eq
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) (g : E →ᵇ ℝ) :
    ∫ x, g x ∂((compactPieceWeightedFiniteMeasure K μ n : MeasureTheory.FiniteMeasure E) : Measure E) =
      radonVagueIntegral (g • annulusWeight K n) μ := by
  let f : C_c(E, ℝ) := g • annulusWeight K n
  have hf :
      tsupport f ⊆ K (n + 1) := by
    -- Proof comment: multiplying by the compactly supported annulus weight keeps the same compact
    -- control on the weighted test.
    simpa [f] using
      (tsupport_smul_subset_right g (annulusWeight K n)).trans
        (annulusWeight_tsupport_subset K n)
  -- Proof comment: unfold the weighted coordinate once, rewrite it by the compact-piece
  -- `withDensity` formula, and then recognize the resulting compactly supported ambient test.
  calc
    ∫ x, g x ∂((compactPieceWeightedFiniteMeasure K μ n : MeasureTheory.FiniteMeasure E) : Measure E)
      = ∫ x, g x
          ∂(compactPieceWeightedRecoverySummand K (compactPieceRadonEmbedding K μ) n) := by
            rfl
    _ = ∫ x : ↥(K (n + 1)), (annulusWeightOnCompactPiece K n x : NNReal) • g x
          ∂(compactPieceRadonEmbedding K μ (n + 1) : Measure ↥(K (n + 1))) := by
            rw [compactPieceWeightedRecoverySummand,
              MeasurableEmbedding.integral_map
                (MeasurableEmbedding.subtype_coe ((K.isCompact (n + 1)).measurableSet))]
            simpa using
              (integral_withDensity_eq_integral_smul
                (μ := (compactPieceRadonEmbedding K μ (n + 1) :
                  Measure ↥(K (n + 1))))
                (f_meas := (annulusWeightOnCompactPiece K n).continuous.measurable)
                (g := fun x : ↥(K (n + 1)) ↦ g x))
    _ = ∫ x : ↥(K (n + 1)), f x
          ∂(compactPieceRadonEmbedding K μ (n + 1) : Measure ↥(K (n + 1))) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
            change (((annulusWeightOnCompactPiece K n x : NNReal) : ℝ) * g x) = f x
            simp [f, annulusWeightOnCompactPiece, mul_comm]
    _ = radonVagueIntegral f μ := by
          symm
          exact radonVagueIntegral_factorsThroughCompactPiece K μ f hf
    _ = radonVagueIntegral (g • annulusWeight K n) μ := by
          rfl

/-- Helper for Remark 13.14: every annulus-weighted finite-measure coordinate is continuous for
the vague topology. -/
private theorem continuous_compactPieceWeightedFiniteMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) (n : ℕ) :
    Continuous
      (fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        compactPieceWeightedFiniteMeasure K μ n) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro g
  have hEq :
      (fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        ∫ x, g x
          ∂((compactPieceWeightedFiniteMeasure K μ n : MeasureTheory.FiniteMeasure E) : Measure E)) =
        radonVagueIntegral (g • annulusWeight K n) := by
    funext μ
    exact integral_compactPieceWeightedFiniteMeasure_eq K μ n g
  -- Proof comment: once the weighted coordinate integral is rewritten as one vague test integral,
  -- continuity is built into the definition of the vague topology.
  rw [hEq]
  exact continuous_iff_le_induced.mpr <| by
    rw [instTopologicalSpaceRadonMeasureSubtype, vagueTopology]
    exact iInf_le _ (g • annulusWeight K n)

/-- Helper for Remark 13.14: the full annulus-weighted coordinate map into ambient finite-measure
factors. -/
private def compactPieceWeightedEmbedding
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E :=
  fun μ n ↦ compactPieceWeightedFiniteMeasure K μ n

/-- Helper for Remark 13.14: the annulus-weighted coordinate map is continuous for the vague
topology because each coordinate is a single vague test integral packaged as a finite measure. -/
private theorem continuous_compactPieceWeightedEmbedding
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Continuous
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  -- Proof comment: the product topology is coordinatewise, so the preceding one-coordinate
  -- continuity result upgrades immediately to the full weighted embedding.
  refine continuous_pi ?_
  intro n
  exact continuous_compactPieceWeightedFiniteMeasure K n

/-- Helper for Remark 13.14: the countable product of ambient finite-measure spaces is Polish once
`E` is locally compact and Polish. -/
private theorem compactPieceWeightedProduct_polish
    [LocallyCompactSpace E] [PolishSpace E] :
    PolishSpace ((n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  letI : PolishSpace (MeasureTheory.FiniteMeasure E) :=
    finiteMeasure_weakTopology_polish_of_locallyCompact (E := E)
  -- Proof comment: each factor is already Polish, and countable products preserve Polishness.
  infer_instance

/-- Helper for Remark 13.14: a compactly supported vague test is a finite sum of annulus-weighted
coordinate integrals of the weighted embedding. -/
private theorem radonVagueIntegral_factorsThroughWeightedEmbedding
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (f : C_c(E, ℝ)) {N : ℕ} (hfN : tsupport f ⊆ K N) :
    radonVagueIntegral f =
      fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        Finset.sum (Finset.range (N + 1)) fun i ↦
          ∫ x, f.toBoundedContinuousFunction x
            ∂((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E) := by
  funext μ
  symm
  calc
    Finset.sum (Finset.range (N + 1)) (fun i ↦
        ∫ x, f.toBoundedContinuousFunction x
          ∂((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E))
      = Finset.sum (Finset.range (N + 1)) (fun i ↦
          radonVagueIntegral (f.toBoundedContinuousFunction • annulusWeight K i) μ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            -- Proof comment: each weighted coordinate is defined so that integrating a bounded
            -- test against it is the same as integrating the annulus-weighted test against `μ`.
            simpa [compactPieceWeightedEmbedding] using
              (integral_compactPieceWeightedFiniteMeasure_eq K μ i
                f.toBoundedContinuousFunction)
    _ = radonVagueIntegral
          (Finset.sum (Finset.range (N + 1)) fun i ↦
            f.toBoundedContinuousFunction • annulusWeight K i) μ := by
              have hInt :
                  ∀ i ∈ Finset.range (N + 1),
                    Integrable
                      (fun x ↦ (f.toBoundedContinuousFunction • annulusWeight K i) x)
                      (μ : Measure E) := by
                intro i hi
                exact (f.toBoundedContinuousFunction • annulusWeight K i).integrable
              -- Proof comment: the finite sum of coordinate integrals is the integral of the
              -- finite sum of the corresponding compactly supported tests.
              simp only [radonVagueIntegral]
              simpa using (integral_finset_sum (Finset.range (N + 1)) hInt).symm
    _ = radonVagueIntegral f μ := by
          congr 1
          ext x
          by_cases hx : x ∈ K N
          · have hsum : (Finset.sum (Finset.range (N + 1)) fun i ↦ annulusWeight K i) x = 1 := by
              simpa using (sum_annulusWeight_eqOn_one K N hx)
            have hsum' :
                Finset.sum (Finset.range (N + 1)) (fun i ↦ annulusWeight K i x) = 1 := by
              simpa using hsum
            -- Proof comment: on the supporting compact piece, the annulus partition of unity sums
            -- to `1`, so the weighted finite sum collapses back to `f`.
            calc
              (Finset.sum (Finset.range (N + 1)) fun i ↦
                  f.toBoundedContinuousFunction • annulusWeight K i) x
                  =
                    Finset.sum (Finset.range (N + 1))
                      (fun i ↦ f.toBoundedContinuousFunction x * annulusWeight K i x) := by
                        simp [Pi.smul_apply]
              _ =
                    f.toBoundedContinuousFunction x *
                      Finset.sum (Finset.range (N + 1)) (fun i ↦ annulusWeight K i x) := by
                      rw [Finset.mul_sum]
              _ = f.toBoundedContinuousFunction x := by rw [hsum', mul_one]
              _ = f x := by
                    simp [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply]
          · have hfx : f x = 0 := by
              by_contra hne
              exact hx (hfN (subset_tsupport f hne))
            -- Proof comment: outside the supporting compact piece, `f` already vanishes, so every
            -- annulus-weighted summand vanishes as well.
            simp [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply, hfx]

/-- Helper for Remark 13.14: the topology induced by the annulus-weighted coordinate map is finer
than the vague topology, because every vague test is a finite sum of weighted coordinate tests. -/
private theorem compactPieceWeightedEmbedding_induced_le_vague
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    TopologicalSpace.induced (compactPieceWeightedEmbedding K) inferInstance ≤
      (inferInstance : TopologicalSpace { μ : Measure E // IsRadonMeasure μ }) := by
  rw [instTopologicalSpaceRadonMeasureSubtype, vagueTopology]
  refine le_iInf ?_
  intro f
  rcases K.exists_superset_of_isCompact f.hasCompactSupport.isCompact with ⟨N, hfN⟩
  have hfactor := radonVagueIntegral_factorsThroughWeightedEmbedding K f hfN
  letI : TopologicalSpace { μ : Measure E // IsRadonMeasure μ } :=
    TopologicalSpace.induced (compactPieceWeightedEmbedding K) inferInstance
  have hcoord :
      ∀ i : ℕ,
        Continuous fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
          compactPieceWeightedEmbedding K μ i := by
    intro i
    -- Proof comment: under the induced topology, each product coordinate is continuous by
    -- construction.
    simpa [Function.comp, compactPieceWeightedEmbedding] using
      (continuous_apply i).comp
        (continuous_induced_dom :
          Continuous (compactPieceWeightedEmbedding K))
  have hcont :
      Continuous fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
        Finset.sum (Finset.range (N + 1)) fun i ↦
          ∫ x, f.toBoundedContinuousFunction x
            ∂((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E) := by
    -- Proof comment: the factorization from the previous lemma is a finite sum of continuous
    -- coordinate integrals in the product topology.
    refine continuous_finset_sum _ fun i hi ↦ ?_
    exact (FiniteMeasure.continuous_integral_boundedContinuousFunction
        f.toBoundedContinuousFunction).comp (hcoord i)
  exact continuous_iff_le_induced.mp <| by
    simpa [hfactor] using hcont

/-- Helper for Remark 13.14: the annulus-weighted embedding is inducing because it is continuous
by construction and already captures every vague test integral. -/
private theorem compactPieceWeightedEmbedding_inducing
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Topology.IsInducing
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  refine ⟨le_antisymm ?_ (compactPieceWeightedEmbedding_induced_le_vague K)⟩
  -- Proof comment: continuity gives one inequality, and the previous factorization lemma gives the
  -- converse inequality.
  exact continuous_iff_le_induced.mp (continuous_compactPieceWeightedEmbedding K)

/-- Helper for Remark 13.14: the annulus-weighted embedding is injective because the weighted
coordinates still determine every compactly supported test integral. -/
private theorem compactPieceWeightedEmbedding_injective
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Function.Injective
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  intro μ ν hcoord
  let hsep :
      IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
        (((↑) : C_c(E, ℝ) → E → ℝ) ''
          compactlySupportedUnitIntervalLipschitzRealMapSpace E) :=
    compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
  apply Subtype.ext
  exact IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep μ.2 ν.2 <| by
    intro g hg _ _
    rcases hg with ⟨g0, -, rfl⟩
    rcases K.exists_superset_of_isCompact g0.hasCompactSupport.isCompact with ⟨N, hgN⟩
    have hfactor := radonVagueIntegral_factorsThroughWeightedEmbedding K g0 hgN
    have hEqVague : radonVagueIntegral g0 μ = radonVagueIntegral g0 ν := by
      have hμ :
          radonVagueIntegral g0 μ =
            Finset.sum (Finset.range (N + 1)) fun i ↦
              ∫ x, g0.toBoundedContinuousFunction x
                ∂((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E) :=
        congrFun hfactor μ
      have hν :
          radonVagueIntegral g0 ν =
            Finset.sum (Finset.range (N + 1)) fun i ↦
              ∫ x, g0.toBoundedContinuousFunction x
                ∂((compactPieceWeightedEmbedding K ν i : MeasureTheory.FiniteMeasure E) : Measure E) :=
        congrFun hfactor ν
      rw [hμ, hν]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa using congrArg
        (fun m : MeasureTheory.FiniteMeasure E ↦
          ∫ x, g0.toBoundedContinuousFunction x ∂((m : MeasureTheory.FiniteMeasure E) : Measure E))
        (congrFun hcoord i)
    simpa [radonVagueIntegral_apply] using hEqVague

/-- Helper for Remark 13.14: the annulus-weighted coordinate map is an embedding for the vague
topology. This is the correct forward model; the raw compact-piece restriction map is not vague
continuous in general. -/
private theorem compactPieceWeightedEmbedding_isEmbedding
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    IsEmbedding
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  -- Proof comment: combine the inducing description of the topology with the separating-family
  -- injectivity argument.
  exact ⟨compactPieceWeightedEmbedding_inducing K,
    compactPieceWeightedEmbedding_injective K⟩

/-- Helper for Remark 13.14: the ambient annulus weight viewed as an `NNReal` density. -/
private def ambientWeightDensity
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) : E → NNReal :=
  fun x ↦ Real.toNNReal (annulusWeight K n x)

/-- Helper for Remark 13.14: the `NNReal` ambient annulus density agrees with the original real
weight. -/
private theorem ambientWeightDensity_coe
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ) (x : E) :
    (ambientWeightDensity K n x : ℝ) = annulusWeight K n x := by
  -- Proof comment: the annulus weight is nonnegative, so `Real.toNNReal` does not change it.
  rw [ambientWeightDensity]
  exact Real.coe_toNNReal _ (annulusWeight_nonneg K n x)

/-- Helper for Remark 13.14: annulus-weighting an ambient finite measure can only decrease it. -/
private theorem ambientWeightedMeasure_le
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ)
    (ν : MeasureTheory.FiniteMeasure E) :
    (ν : Measure E).withDensity (fun x ↦ (ambientWeightDensity K n x : ℝ≥0∞)) ≤
      (ν : Measure E) := by
  calc
    (ν : Measure E).withDensity (fun x ↦ (ambientWeightDensity K n x : ℝ≥0∞))
      ≤ (ν : Measure E).withDensity 1 := by
          -- Proof comment: the annulus density takes values in `[0, 1]`, so `withDensity`
          -- cannot increase the source finite measure.
          refine withDensity_mono <| Filter.Eventually.of_forall fun x ↦ ?_
          have hx : ambientWeightDensity K n x ≤ 1 := by
            simpa [ambientWeightDensity] using
              Real.toNNReal_le_toNNReal (annulusWeight_mem_Icc K n x).2
          change ((ambientWeightDensity K n x : ℝ≥0∞)) ≤ (1 : ℝ≥0∞)
          exact_mod_cast hx
    _ = (ν : Measure E) := by
          rw [withDensity_one]

/-- Helper for Remark 13.14: annulus-weighting an ambient finite measure stays finite. -/
private theorem isFiniteMeasure_ambientWeightedMeasure
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ)
    (ν : MeasureTheory.FiniteMeasure E) :
    IsFiniteMeasure ((ν : Measure E).withDensity
      (fun x ↦ (ambientWeightDensity K n x : ℝ≥0∞))) := by
  letI : IsFiniteMeasure (ν : Measure E) := ν.2
  -- Proof comment: finiteness is inherited from the dominating source finite measure.
  exact MeasureTheory.isFiniteMeasure_of_le _
    (ambientWeightedMeasure_le K n ν)

/-- Helper for Remark 13.14: annulus-weighting an ambient finite measure produces the corresponding
ambient weighted finite-measure coordinate. -/
private def ambientWeightedFiniteMeasure
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ)
    (ν : MeasureTheory.FiniteMeasure E) :
    MeasureTheory.FiniteMeasure E :=
  ⟨(ν : Measure E).withDensity
      (fun x ↦ (ambientWeightDensity K n x : ℝ≥0∞)),
    isFiniteMeasure_ambientWeightedMeasure K n ν⟩

/-- Helper for Remark 13.14: integrating a bounded continuous test against an ambient weighted
finite measure rewrites to integrating the annulus-weighted test against the source measure. -/
private theorem integral_ambientWeightedFiniteMeasure_eq
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ)
    (ν : MeasureTheory.FiniteMeasure E) (g : E →ᵇ ℝ) :
    ∫ x, g x ∂((ambientWeightedFiniteMeasure K n ν : MeasureTheory.FiniteMeasure E) : Measure E) =
      ∫ x, (g • annulusWeight K n) x ∂((ν : MeasureTheory.FiniteMeasure E) : Measure E) := by
  calc
    ∫ x, g x ∂((ambientWeightedFiniteMeasure K n ν : MeasureTheory.FiniteMeasure E) : Measure E)
      = ∫ x, (ambientWeightDensity K n x : ℝ) * g x ∂((ν : Measure E)) := by
          -- Proof comment: unfold the weighted finite measure once and use the standard
          -- `withDensity` integral formula.
          rw [ambientWeightedFiniteMeasure]
          simpa using
            (integral_withDensity_eq_integral_smul
              (μ := (ν : Measure E))
              (f_meas := (annulusWeight K n).continuous.measurable.real_toNNReal)
              (g := fun x : E ↦ g x))
    _ = ∫ x, (g • annulusWeight K n) x ∂((ν : MeasureTheory.FiniteMeasure E) : Measure E) := by
          -- Proof comment: after identifying `ENNReal.ofReal` with the nonnegative annulus
          -- weight, the integrand is exactly the bounded-continuous weighted test.
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          change (ambientWeightDensity K n x : ℝ) * g x = (g • annulusWeight K n) x
          rw [ambientWeightDensity_coe K n x]
          simp [smul_eq_mul, mul_comm]

/-- Helper for Remark 13.14: the ambient annulus-weighting operator is continuous in the weak
topology on finite measures. -/
private theorem continuous_ambientWeightedFiniteMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) (n : ℕ) :
    Continuous
      (fun ν : MeasureTheory.FiniteMeasure E ↦ ambientWeightedFiniteMeasure K n ν) := by
  rw [FiniteMeasure.continuous_iff_forall_continuous_integral]
  intro g
  have hEq :
      (fun ν : MeasureTheory.FiniteMeasure E ↦
        ∫ x, g x ∂((ambientWeightedFiniteMeasure K n ν : MeasureTheory.FiniteMeasure E) : Measure E)) =
        fun ν : MeasureTheory.FiniteMeasure E ↦
          ∫ x, (g • annulusWeight K n) x ∂((ν : MeasureTheory.FiniteMeasure E) : Measure E) := by
    funext ν
    exact integral_ambientWeightedFiniteMeasure_eq K n ν g
  -- Proof comment: after the integral rewrite, continuity is the standard owner theorem for
  -- bounded-continuous finite-measure integrals.
  rw [hEq]
  simpa [CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
    (FiniteMeasure.continuous_integral_boundedContinuousFunction
      (g • annulusWeight K n).toBoundedContinuousFunction)

/-- Helper for Remark 13.14: later ambient weighted finite measures give zero mass to earlier
compact exhaustion pieces. -/
private theorem ambientWeightedFiniteMeasure_eq_zero_on_piece
    [LocallyCompactSpace E] (K : CompactExhaustion E) (n : ℕ)
    (ν : MeasureTheory.FiniteMeasure E) {N : ℕ} (hNn : N < n) :
    ((ambientWeightedFiniteMeasure K n ν : MeasureTheory.FiniteMeasure E) : Measure E) (K N) = 0 := by
  -- Proof comment: on `K N`, the annulus weight for the later index `n` vanishes identically, so
  -- the defining `withDensity` measure evaluates to zero there.
  change
    (ν : Measure E).withDensity
      (fun x ↦ (ambientWeightDensity K n x : ℝ≥0∞)) (K N) = 0
  rw [withDensity_apply']
  change ∫⁻ a in K N, (ambientWeightDensity K n a : ℝ≥0∞) ∂((ν : Measure E)) = 0
  refine (setLIntegral_eq_zero_iff (K.isCompact N).measurableSet ?_).2 ?_
  · simpa [ambientWeightDensity] using
      ((annulusWeight K n).continuous.measurable.real_toNNReal.coe_nnreal_ennreal)
  · exact Filter.Eventually.of_forall fun x hx ↦ by
      have hzero : annulusWeight K n x = 0 := annulusWeight_eq_zero_on_piece K hNn hx
      simp [ambientWeightDensity, hzero]

/-- Helper for Remark 13.14: the weighted embedding coordinates satisfy the finite partial-sum
compatibility equation in the ambient product of finite measures. -/
private theorem compactPieceWeightedEmbedding_coordinate_eq_partialWeightedSum
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    (μ : { μ : Measure E // IsRadonMeasure μ }) (n : ℕ) :
    compactPieceWeightedEmbedding K μ n =
      ambientWeightedFiniteMeasure K n
        ((Finset.sum (Finset.range (n + 2)) fun i ↦ compactPieceWeightedEmbedding K μ i) :
          MeasureTheory.FiniteMeasure E) := by
  refine FiniteMeasure.ext_of_forall_integral_eq ?_
  intro g
  let f : C_c(E, ℝ) := g • annulusWeight K n
  have hf : tsupport f ⊆ K (n + 1) := by
    -- Proof comment: the annulus weight already localizes the weighted test to the next compact
    -- exhaustion piece.
    simpa [f] using
      (tsupport_smul_subset_right g (annulusWeight K n)).trans
        (annulusWeight_tsupport_subset K n)
  have hInt :
      ∀ i ∈ Finset.range (n + 2),
        Integrable (fun x ↦ f.toBoundedContinuousFunction x)
          ((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E) := by
    intro i hi
    exact f.toBoundedContinuousFunction.integrable _
  calc
    ∫ x, g x ∂((compactPieceWeightedEmbedding K μ n : MeasureTheory.FiniteMeasure E) : Measure E)
      = radonVagueIntegral f μ := by
          simpa [compactPieceWeightedEmbedding, f] using
            (integral_compactPieceWeightedFiniteMeasure_eq K μ n g)
    _ = Finset.sum (Finset.range (n + 2)) fun i ↦
          ∫ x, f.toBoundedContinuousFunction x
            ∂((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E) := by
          exact congrFun (radonVagueIntegral_factorsThroughWeightedEmbedding K f hf) μ
    _ = ∫ x, f.toBoundedContinuousFunction x
          ∂(((Finset.sum (Finset.range (n + 2))
              (fun i ↦ compactPieceWeightedEmbedding K μ i) : MeasureTheory.FiniteMeasure E) :
            Measure E)) := by
          symm
          simpa using
            (integral_finset_sum_measure (f := fun x ↦ f.toBoundedContinuousFunction x)
              (μ := fun i ↦
                ((compactPieceWeightedEmbedding K μ i : MeasureTheory.FiniteMeasure E) : Measure E))
              (s := Finset.range (n + 2)) hInt)
    _ = ∫ x, g x
          ∂((ambientWeightedFiniteMeasure K n
              (Finset.sum (Finset.range (n + 2))
                (fun i ↦ compactPieceWeightedEmbedding K μ i) : MeasureTheory.FiniteMeasure E) :
              MeasureTheory.FiniteMeasure E) : Measure E) := by
          symm
          simpa [f, CompactlySupportedContinuousMap.toBoundedContinuousFunction_apply] using
            (integral_ambientWeightedFiniteMeasure_eq K n
              (Finset.sum (Finset.range (n + 2))
                (fun i ↦ compactPieceWeightedEmbedding K μ i) :
                MeasureTheory.FiniteMeasure E) g)

/-- Helper for Remark 13.14: a weighted ambient sequence is compatible when every coordinate is
obtained by annulus-weighting the finite partial sum of the preceding coordinates. -/
@[reducible] private def compactPieceWeightedCompatible
    [LocallyCompactSpace E] (K : CompactExhaustion E)
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure E) : Prop :=
  ∀ n, u n = ambientWeightedFiniteMeasure K n (Finset.sum (Finset.range (n + 2)) fun i ↦ u i)

/-- Helper for Remark 13.14: the compatibility relation for weighted ambient sequences defines a
closed subset of the ambient Polish product. -/
private theorem isClosed_compactPieceWeightedCompatibility
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    IsClosed {u : (n : ℕ) → MeasureTheory.FiniteMeasure E |
      compactPieceWeightedCompatible K u} := by
  have hcoord :
      ∀ n : ℕ,
        Continuous fun u : (n : ℕ) → MeasureTheory.FiniteMeasure E ↦
          ambientWeightedFiniteMeasure K n (Finset.sum (Finset.range (n + 2)) fun i ↦ u i) := by
    intro n
    have hsum :
        Continuous fun u : (n : ℕ) → MeasureTheory.FiniteMeasure E ↦
          Finset.sum (Finset.range (n + 2)) fun i ↦ u i := by
      -- Proof comment: the partial-sum map is a finite sum of product coordinate projections.
      refine continuous_finset_sum _ fun i hi ↦ ?_
      exact continuous_apply i
    exact (continuous_ambientWeightedFiniteMeasure K n).comp hsum
  rw [show {u : (n : ℕ) → MeasureTheory.FiniteMeasure E |
      compactPieceWeightedCompatible K u} =
      ⋂ n : ℕ, {u : (n : ℕ) → MeasureTheory.FiniteMeasure E |
        u n = ambientWeightedFiniteMeasure K n
          (Finset.sum (Finset.range (n + 2)) fun i ↦ u i)} by
      ext u
      simp [compactPieceWeightedCompatible]]
  refine isClosed_iInter ?_
  intro n
  -- Proof comment: each fixed coordinate equation is an equalizer of two continuous maps into the
  -- Hausdorff finite-measure space.
  exact isClosed_eq (continuous_apply n) (hcoord n)

/-- Helper for Remark 13.14: if a compactly supported test is supported inside a measurable set of
zero mass, then its integral against that finite measure vanishes. -/
private theorem integral_eq_zero_of_tsupport_subset_measure_zero
    (ν : MeasureTheory.FiniteMeasure E) (f : C_c(E, ℝ)) {s : Set E}
    (hf : tsupport f ⊆ s) (hs : MeasurableSet s) (hν : ((ν : Measure E) s) = 0) :
    ∫ x, f x ∂((ν : MeasureTheory.FiniteMeasure E) : Measure E) = 0 := by
  have hrestrict : (ν : Measure E).restrict s = 0 := Measure.restrict_eq_zero.2 hν
  -- Proof comment: outside `s` the test already vanishes, and inside `s` the restricted measure is
  -- the zero measure.
  calc
    ∫ x, f x ∂((ν : MeasureTheory.FiniteMeasure E) : Measure E)
      = ∫ x, Set.indicator s f x ∂((ν : Measure E)) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
          by_cases hx : x ∈ s
          · simp [hx]
          · have hfx : f x = 0 := by
              by_contra hne
              exact hx (hf (subset_tsupport f hne))
            simp [hx, hfx]
    _ = ∫ x in s, f x ∂((ν : Measure E)) := by
          rw [integral_indicator hs]
    _ = 0 := by
          rw [hrestrict]
          simp

/-- Helper for Remark 13.14: summing the compatible ambient weighted coordinates gives the
candidate recovered measure. -/
private def compatibleWeightedRecoveryMeasure
    (u : (n : ℕ) → MeasureTheory.FiniteMeasure E) : Measure E :=
  Measure.sum fun n ↦ ((u n : MeasureTheory.FiniteMeasure E) : Measure E)

/-- Helper for Remark 13.14: compatible weighted coordinates vanish on earlier compact pieces. -/
private theorem compactPieceWeightedCompatible_eq_zero_on_piece
    [LocallyCompactSpace E] (K : CompactExhaustion E)
    {u : (n : ℕ) → MeasureTheory.FiniteMeasure E}
    (hu : compactPieceWeightedCompatible K u) {N n : ℕ} (hNn : N < n) :
    ((u n : MeasureTheory.FiniteMeasure E) : Measure E) (K N) = 0 := by
  -- Proof comment: compatibility rewrites the coordinate to an ambient annulus-weighted finite
  -- measure, and the later annulus is already zero on the earlier piece.
  rw [hu n]
  exact ambientWeightedFiniteMeasure_eq_zero_on_piece K n
    ((Finset.sum (Finset.range (n + 2)) fun i ↦ u i) : MeasureTheory.FiniteMeasure E) hNn

/-- Helper for Remark 13.14: the recovered measure from a compatible weighted sequence is locally
finite because only finitely many coordinates meet a fixed compact exhaustion piece. -/
private theorem isLocallyFiniteMeasure_compatibleWeightedRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    {u : (n : ℕ) → MeasureTheory.FiniteMeasure E}
    (hu : compactPieceWeightedCompatible K u) :
    IsLocallyFiniteMeasure (compatibleWeightedRecoveryMeasure u) := by
  constructor
  intro x
  rcases K.exists_mem_nhds x with ⟨N, hKN⟩
  refine ⟨K N, hKN, ?_⟩
  rw [compatibleWeightedRecoveryMeasure, Measure.sum_apply _ (K.isCompact N).measurableSet]
  have hzero :
      ∀ n ∉ Finset.range (N + 1),
        ((u n : MeasureTheory.FiniteMeasure E) : Measure E) (K N) = 0 := by
    intro n hn
    exact compactPieceWeightedCompatible_eq_zero_on_piece K hu <|
      Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hn)
  rw [tsum_eq_sum hzero]
  -- Proof comment: the surviving prefix is finite, and every coordinate is already a finite
  -- measure on `E`.
  simpa [measure_lt_top]

/-- Helper for Remark 13.14: the recovered measure from a compatible weighted sequence is Radon. -/
private theorem isRadonMeasure_compatibleWeightedRecoveryMeasure
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    {u : (n : ℕ) → MeasureTheory.FiniteMeasure E}
    (hu : compactPieceWeightedCompatible K u) :
    IsRadonMeasure (compatibleWeightedRecoveryMeasure u) := by
  letI : IsLocallyFiniteMeasure (compatibleWeightedRecoveryMeasure u) :=
    isLocallyFiniteMeasure_compatibleWeightedRecoveryMeasure K hu
  -- Proof comment: on locally compact Polish spaces, locally finite Borel measures are Radon.
  exact IsRadonMeasure.of_owner _

/-- Helper for Remark 13.14: every compatible weighted ambient sequence comes from a Radon measure
obtained by summing its coordinates. -/
private theorem compactPieceWeightedCompatibility_exists_preimage
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E)
    {u : (n : ℕ) → MeasureTheory.FiniteMeasure E}
    (hu : compactPieceWeightedCompatible K u) :
    ∃ μ : { μ : Measure E // IsRadonMeasure μ }, compactPieceWeightedEmbedding K μ = u := by
  let μ : { μ : Measure E // IsRadonMeasure μ } :=
    ⟨compatibleWeightedRecoveryMeasure u,
      isRadonMeasure_compatibleWeightedRecoveryMeasure K hu⟩
  refine ⟨μ, ?_⟩
  funext n
  refine FiniteMeasure.ext_of_forall_integral_eq ?_
  intro g
  let f : C_c(E, ℝ) := g • annulusWeight K n
  have hf : tsupport f ⊆ K (n + 1) := by
    -- Proof comment: the weighted test is still localized to `K (n + 1)`.
    simpa [f] using
      (tsupport_smul_subset_right g (annulusWeight K n)).trans
        (annulusWeight_tsupport_subset K n)
  letI : IsFiniteMeasureOnCompacts (compatibleWeightedRecoveryMeasure u) := by
    letI : IsLocallyFiniteMeasure (compatibleWeightedRecoveryMeasure u) :=
      IsRadonMeasure.locallyFinite (isRadonMeasure_compatibleWeightedRecoveryMeasure K hu)
    letI : Measure.Regular (compatibleWeightedRecoveryMeasure u) := by infer_instance
    infer_instance
  have hfInt : Integrable f (compatibleWeightedRecoveryMeasure u) := f.integrable
  have htailZero :
      ∀ i ∉ Finset.range (n + 2),
        ∫ x, f x ∂((u i : MeasureTheory.FiniteMeasure E) : Measure E) = 0 := by
    intro i hi
    have hNi : n + 1 < i := Nat.lt_of_not_ge (by simpa [Finset.mem_range] using hi)
    have hzeroMass :
        ((u i : MeasureTheory.FiniteMeasure E) : Measure E) (K (n + 1)) = 0 :=
      compactPieceWeightedCompatible_eq_zero_on_piece K hu hNi
    -- Proof comment: once the support of `f` is contained in `K (n + 1)`, any later coordinate
    -- with zero mass on that piece contributes no integral.
    exact integral_eq_zero_of_tsupport_subset_measure_zero
      (u i) f hf (K.isCompact (n + 1)).measurableSet hzeroMass
  have hIntPrefix :
      ∀ i ∈ Finset.range (n + 2),
        Integrable (fun x ↦ f x) (((u i : MeasureTheory.FiniteMeasure E) : Measure E)) := by
    intro i hi
    exact f.integrable
  calc
    ∫ x, g x ∂((compactPieceWeightedEmbedding K μ n : MeasureTheory.FiniteMeasure E) : Measure E)
      = radonVagueIntegral f μ := by
          simpa [compactPieceWeightedEmbedding, f] using
            (integral_compactPieceWeightedFiniteMeasure_eq K μ n g)
    _ = ∫ x, f x ∂(compatibleWeightedRecoveryMeasure u) := by
          rfl
    _ = ∑' i, ∫ x, f x ∂((u i : MeasureTheory.FiniteMeasure E) : Measure E) := by
          rw [compatibleWeightedRecoveryMeasure, integral_sum_measure hfInt]
    _ = Finset.sum (Finset.range (n + 2)) fun i ↦
          ∫ x, f x ∂((u i : MeasureTheory.FiniteMeasure E) : Measure E) := by
          rw [tsum_eq_sum htailZero]
    _ = ∫ x, f x
          ∂(((Finset.sum (Finset.range (n + 2)) fun i ↦ u i : MeasureTheory.FiniteMeasure E) :
            Measure E)) := by
          symm
          simpa using
            (integral_finset_sum_measure
              (f := fun x ↦ f x)
              (μ := fun i ↦ (((u i : MeasureTheory.FiniteMeasure E) : Measure E)))
              (s := Finset.range (n + 2)) hIntPrefix)
    _ = ∫ x, g x
          ∂((ambientWeightedFiniteMeasure K n
              (Finset.sum (Finset.range (n + 2)) fun i ↦ u i : MeasureTheory.FiniteMeasure E) :
              MeasureTheory.FiniteMeasure E) : Measure E) := by
          symm
          simpa [f] using
            (integral_ambientWeightedFiniteMeasure_eq K n
              (Finset.sum (Finset.range (n + 2)) fun i ↦ u i : MeasureTheory.FiniteMeasure E) g)
    _ = ∫ x, g x ∂((u n : MeasureTheory.FiniteMeasure E) : Measure E) := by
          rw [hu n]

/-- Helper for Remark 13.14: the range of the weighted embedding is exactly the compatible weighted
subspace of the ambient product. -/
private theorem compactPieceWeightedEmbedding_range_eq_compatibility
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    Set.range
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) =
      {u : (n : ℕ) → MeasureTheory.FiniteMeasure E | compactPieceWeightedCompatible K u} := by
  ext u
  constructor
  · rintro ⟨μ, rfl⟩
    -- Proof comment: actual weighted coordinates satisfy the defining compatibility equation.
    intro n
    exact compactPieceWeightedEmbedding_coordinate_eq_partialWeightedSum K μ n
  · intro hu
    rcases compactPieceWeightedCompatibility_exists_preimage K hu with ⟨μ, hμ⟩
    exact ⟨μ, hμ⟩

/-- Helper for Remark 13.14: the annulus-weighted embedding is a closed embedding because its
range is the closed compatibility locus in the ambient weighted product. -/
private theorem compactPieceWeightedEmbedding_isClosedEmbedding
    [LocallyCompactSpace E] [PolishSpace E] (K : CompactExhaustion E) :
    IsClosedEmbedding
      (compactPieceWeightedEmbedding K :
        { μ : Measure E // IsRadonMeasure μ } → (n : ℕ) → MeasureTheory.FiniteMeasure E) := by
  refine ⟨compactPieceWeightedEmbedding_isEmbedding K, ?_⟩
  -- Proof comment: identify the range with the closed compatibility set just proved.
  rw [compactPieceWeightedEmbedding_range_eq_compatibility K]
  exact isClosed_compactPieceWeightedCompatibility K

/-- Helper for Remark 13.14: the countable product of compact-piece finite-measure spaces is
Polish. This is the ambient product needed once the final closed-embedding route is in place. -/
private theorem compactPieceRadonProduct_polish
    [LocallyCompactSpace E] [PolishSpace E]
    (K : CompactExhaustion E) :
    PolishSpace ((n : ℕ) → MeasureTheory.FiniteMeasure ↥(K n)) := by
  letI : ∀ n : ℕ, CompactSpace ↥(K n) := fun n ↦
    isCompact_iff_compactSpace.mp (K.isCompact n)
  letI : ∀ n : ℕ, PolishSpace ↥(K n) := fun n ↦
    (K.isCompact n).isClosed.polishSpace
  letI : ∀ n : ℕ, PolishSpace (MeasureTheory.FiniteMeasure ↥(K n)) := fun n ↦
    finiteMeasure_weakTopology_polish_of_compact (E := ↥(K n))
  -- Proof comment: each compact exhaustion piece contributes a Polish finite-measure factor, and
  -- countable products of Polish spaces remain Polish.
  infer_instance

/-- Helper: the full coordinate map
`μ ↦ (f ↦ radonVagueIntegral f μ)` embeds the Radon-measure subtype into the product of the real
test-integral coordinates. -/
lemma radonVagueIntegral_isEmbedding
    [LocallyCompactSpace E] :
    IsEmbedding (fun μ : { μ : Measure E // IsRadonMeasure μ } ↦
      fun f : C_c(E, ℝ) ↦ radonVagueIntegral f μ) := by
  let coord : { μ : Measure E // IsRadonMeasure μ } → Π f : C_c(E, ℝ), ℝ :=
    fun μ f ↦ radonVagueIntegral f μ
  have hInducing : IsInducing coord := by
    -- Proof comment: the vague topology is defined as the infimum of the induced coordinate
    -- topologies, so it is exactly the topology induced by the combined product map.
    simpa [coord, vagueTopology] using
      (inducing_iInf_to_pi (fun f : C_c(E, ℝ) ↦ radonVagueIntegral f))
  have hInjective : Function.Injective coord := by
    -- Proof comment: equality of all compactly supported continuous test integrals lets the
    -- separating-family theorem recover equality of the underlying Radon measures.
    intro μ ν hcoord
    apply Subtype.ext
    let hsep :
        IsSeparatingFamilyFor {μ : Measure E | IsRadonMeasure μ}
          (((↑) : C_c(E, ℝ) → E → ℝ) ''
            compactlySupportedUnitIntervalLipschitzRealMapSpace E) :=
      compactlySupportedUnitIntervalLipschitzRealFunctionSpace_isSeparatingFamilyFor_radonMeasureSpace
    exact
      IsSeparatingFamilyFor.eq_of_forall_integral_eq hsep μ.2 ν.2 <| by
      intro g hg _ _
      rcases hg with ⟨g0, -, rfl⟩
      simpa [coord, radonVagueIntegral_apply] using congrFun hcoord g0
  exact ⟨hInducing, hInjective⟩

/-- Item (iv) of Remark 13.14: in the chapter's metric Borel/Radon setting,
if `E` is locally compact, then the vague topology on `𝓜(E)` is Hausdorff. -/
theorem vagueTopology_t2Space_of_locallyCompact
    [LocallyCompactSpace E] :
    T2Space { μ : Measure E // IsRadonMeasure μ } := by
  -- Proof comment: once the vague topology is realized as an embedding into a product of Hausdorff
  -- coordinate spaces, Hausdorffness is inherited from the ambient product.
  exact radonVagueIntegral_isEmbedding.t2Space

/-- Remark 13.14 (4): Item (iv). If, in addition, `E` is Polish, then the vague
topology on `𝓜(E)` is Polish. -/
theorem vagueTopology_polish_of_locallyCompact
    [LocallyCompactSpace E] [PolishSpace E] :
    PolishSpace { μ : Measure E // IsRadonMeasure μ } := by
  -- Route correction: the raw compact-piece restriction map is not vague continuous in general, so
  -- the correct forward model is the annulus-weighted embedding into
  -- `ℕ → MeasureTheory.FiniteMeasure E`.
  let K : CompactExhaustion E := CompactExhaustion.choice E
  letI : PolishSpace ((n : ℕ) → MeasureTheory.FiniteMeasure E) :=
    compactPieceWeightedProduct_polish (E := E)
  -- Proof comment: once the weighted embedding is upgraded from an abstract embedding to a closed
  -- embedding, Polishness transfers immediately from the ambient weighted product.
  exact (compactPieceWeightedEmbedding_isClosedEmbedding K).polishSpace

end RadonTopology
