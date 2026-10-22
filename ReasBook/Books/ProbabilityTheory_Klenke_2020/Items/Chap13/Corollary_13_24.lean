/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_60
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

universe u v

section

variable {Ω : ℕ → Type u} {Ω' : Type v}
variable {m : ∀ n, MeasurableSpace (Ω n)} {m' : MeasurableSpace Ω'}
variable {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
variable {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {X : (n : ℕ) → Ω n → ℝ} {Z : Ω' → ℝ}

-- Proof sketch: rewrite clause `(i)` as weak convergence of the pushed-forward laws using the
-- owner bridge `tendstoInDistribution_iff_tendsto_limit_law`. The bounded-continuous clause is
-- then exactly `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto`, after rewriting
-- pushforward integrals as expectations via `HasLaw.integral_comp`. For the cdf clause, pass to
-- the finite-measure owner theorem `tendsto_iff_measureDistributionFunction_tendsto` from
-- Theorem 13.23, unpack its source-facing continuity-point formulation with
-- `measureDistributionFunction_weakly_converges_to_iff`, and finally rewrite
-- `measureDistributionFunction` back to `cdf` using `cdf_eq_measureDistributionFunction`.
/-- Corollary 13.24: for real random variables, convergence in distribution is equivalent both to
convergence of expectations against every bounded continuous test function and to pointwise
convergence of the distribution functions at every continuity point of the limit distribution
function. -/
theorem tendstoInDistribution_real_tfae
    (hX : ∀ n, AEMeasurable (X n) (μ n)) (hZ : AEMeasurable Z μ') :
    List.TFAE
      [ TendstoInDistribution X atTop Z μ μ'
      , ∀ f : ℝ →ᵇ ℝ,
          Tendsto (fun n ↦ ∫ ω, f (X n ω) ∂μ n) atTop (𝓝 (∫ ω, f (Z ω) ∂μ'))
      , ∀ x : ℝ,
          ContinuousAt (cdf (μ'.map Z)) x →
            Tendsto (fun n ↦ cdf ((μ n).map (X n)) x) atTop (𝓝 (cdf (μ'.map Z) x))
      ] := by
  let ν : ProbabilityMeasure ℝ := ⟨μ'.map Z, Measure.isProbabilityMeasure_map hZ⟩
  let νs : ℕ → ProbabilityMeasure ℝ :=
    fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (hX n)⟩
  have hZlaw : HasLaw Z (ν : Measure ℝ) μ' := ⟨hZ, rfl⟩
  have hXlaw : ∀ n, HasLaw (X n) ((νs n : ProbabilityMeasure ℝ) : Measure ℝ) (μ n) :=
    fun n ↦ ⟨hX n, rfl⟩
  tfae_have 1 ↔ 2 := by
    constructor
    · intro h
      have hν : Tendsto νs atTop (𝓝 ν) :=
        (tendstoInDistribution_iff_tendsto_limit_law hX hZlaw).1 h
      intro f
      have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hν) f
      have hmap :
          (fun n ↦ ∫ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ)) =
            fun n ↦ ∫ ω, f (X n ω) ∂μ n := by
        funext n
        symm
        simpa [νs, Function.comp] using
          (hXlaw n).integral_comp f.continuous.aestronglyMeasurable
      have hlim :
          ∫ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
            ∫ ω, f (Z ω) ∂μ' := by
        simpa [ν, Function.comp] using
          (hZlaw.integral_comp f.continuous.aestronglyMeasurable).symm
      simpa [hmap, hlim] using hf
    · intro h
      have hν : Tendsto νs atTop (𝓝 ν) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro f
        have hf := h f
        have hmap :
            (fun n ↦ ∫ x, f x ∂((νs n : ProbabilityMeasure ℝ) : Measure ℝ)) =
              fun n ↦ ∫ ω, f (X n ω) ∂μ n := by
          funext n
          symm
          simpa [νs, Function.comp] using
            (hXlaw n).integral_comp f.continuous.aestronglyMeasurable
        have hlim :
            ∫ x, f x ∂((ν : ProbabilityMeasure ℝ) : Measure ℝ) =
              ∫ ω, f (Z ω) ∂μ' := by
          simpa [ν, Function.comp] using
            (hZlaw.integral_comp f.continuous.aestronglyMeasurable).symm
        simpa [hmap, hlim] using hf
      exact
        (tendstoInDistribution_iff_tendsto_limit_law hX hZlaw).2 hν
  tfae_have 1 ↔ 3 := by
    have hsubν : ν.toFiniteMeasure.mass ≤ 1 := by
      simpa using ν.mass_toFiniteMeasure.le
    have hsubνs : ∀ n, (νs n).toFiniteMeasure.mass ≤ 1 := by
      intro n
      simpa using (νs n).mass_toFiniteMeasure.le
    have hweak :
        Tendsto νs atTop (𝓝 ν) ↔
          ∀ x : ℝ,
            ContinuousAt (cdf (μ'.map Z)) x →
              Tendsto (fun n ↦ cdf ((μ n).map (X n)) x) atTop (𝓝 (cdf (μ'.map Z) x)) := by
      letI : IsProbabilityMeasure (μ'.map Z) := Measure.isProbabilityMeasure_map hZ
      letI : ∀ n, IsProbabilityMeasure ((μ n).map (X n)) :=
        fun n ↦ Measure.isProbabilityMeasure_map (hX n)
      have hcdfμ : cdf (μ'.map Z) = measureDistributionFunction (μ'.map Z) :=
        cdf_eq_measureDistributionFunction (μ'.map Z)
      have hcdfμs : ∀ n, cdf ((μ n).map (X n)) = measureDistributionFunction ((μ n).map (X n)) :=
        fun n ↦ cdf_eq_measureDistributionFunction ((μ n).map (X n))
      have hdf :
          Tendsto νs atTop (𝓝 ν) ↔
            distribution_function_weakly_converges_to
              (fun n ↦ measureDistributionFunction ((μ n).map (X n)))
              (measureDistributionFunction (μ'.map Z)) := by
        rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
        simpa using
          (tendsto_iff_measureDistributionFunction_tendsto
            (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs)
      have hcont :
          distribution_function_weakly_converges_to
              (fun n ↦ measureDistributionFunction ((μ n).map (X n)))
              (measureDistributionFunction (μ'.map Z)) ↔
            ∀ x : ℝ,
              ContinuousAt (cdf (μ'.map Z)) x →
                Tendsto (fun n ↦ cdf ((μ n).map (X n)) x) atTop (𝓝 (cdf (μ'.map Z) x)) := by
        constructor
        · intro hdfweak x hx
          have hpoint :=
            (measureDistributionFunction_weakly_converges_to_iff
              (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).1 hdfweak
          have hx' : ContinuousAt (measureDistributionFunction (μ'.map Z)) x := by
            simpa [hcdfμ] using hx
          simpa [hcdfμ, hcdfμs] using hpoint.2 hx'
        · intro hcdf
          refine
            (measureDistributionFunction_weakly_converges_to_iff
              (fun n ↦ (νs n).toFiniteMeasure) ν.toFiniteMeasure hsubν hsubνs).2 ?_
          refine ⟨?_, ?_⟩
          · simp
          · intro x hx
            have hx' : ContinuousAt (cdf (μ'.map Z)) x := by
              simpa [hcdfμ] using hx
            simpa [hcdfμ, hcdfμs] using hcdf x hx'
      exact hdf.trans hcont
    exact
      (tendstoInDistribution_iff_tendsto_limit_law hX hZlaw).trans hweak
  tfae_finish

end
