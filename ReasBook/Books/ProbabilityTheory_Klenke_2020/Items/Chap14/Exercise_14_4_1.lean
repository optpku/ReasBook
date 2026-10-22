/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_46

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped MeasureTheory Topology

section

variable {d : ℕ}
variable {ν : NNReal → ProbabilityMeasure (Fin d → ℝ)} [IsContinuousConvolutionSemigroup ν]

namespace IsContinuousConvolutionSemigroup

/-- Helper for Exercise 14.4.1: the canonical `L²` identification of `Fin d → ℝ` with the
finite-dimensional `PiLp` model used by mathlib's characteristic-function API. -/
noncomputable abbrev finPiLpEquiv :
    PiLp 2 (fun _ : Fin d ↦ ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d ↦ ℝ)

/-- Helper for Exercise 14.4.1: push a probability measure on `Fin d → ℝ` to the `PiLp`
Euclidean model. -/
noncomputable abbrev mapToPiLp (μ : ProbabilityMeasure (Fin d → ℝ)) :
    ProbabilityMeasure (PiLp 2 (fun _ : Fin d ↦ ℝ)) :=
  μ.map finPiLpEquiv.symm.continuous.measurable.aemeasurable

/-- Helper for Exercise 14.4.1: the pushed-forward law at time `t`, viewed as a measure on the
`PiLp` Euclidean model. -/
noncomputable abbrev piLpLaw (t : NNReal) : Measure (PiLp 2 (fun _ : Fin d ↦ ℝ)) :=
  ((mapToPiLp (d := d) (ν t) : ProbabilityMeasure (PiLp 2 (fun _ : Fin d ↦ ℝ))) :
    Measure (PiLp 2 (fun _ : Fin d ↦ ℝ)))

/-- Helper for Exercise 14.4.1: the characteristic function of the pushed-forward law at time
`t`. -/
noncomputable abbrev piLpChar (t : NNReal) (ξ : PiLp 2 (fun _ : Fin d ↦ ℝ)) : ℂ :=
  charFun (piLpLaw (ν := ν) (d := d) t) ξ

/-- Helper for Exercise 14.4.1: mapping a probability measure to the `PiLp` model and back along
the canonical linear equivalence recovers the original measure. -/
@[simp] lemma mapFromPiLp_mapToPiLp (μ : ProbabilityMeasure (Fin d → ℝ)) :
    (mapToPiLp (d := d) μ).map finPiLpEquiv.continuous.measurable.aemeasurable = μ := by
  ext s hs
  change (((μ : Measure (Fin d → ℝ)).map finPiLpEquiv.symm).map finPiLpEquiv) s =
    (μ : Measure (Fin d → ℝ)) s
  rw [Measure.map_map finPiLpEquiv.continuous.measurable
    finPiLpEquiv.symm.continuous.measurable]
  simp

/-- Helper for Exercise 14.4.1: the semigroup law is preserved after pushing the measures to the
`PiLp` Euclidean model. -/
lemma mapToPiLp_convolution_eq_toMeasure (a b : NNReal) :
    piLpLaw (ν := ν) (d := d) (a + b) =
      piLpLaw (ν := ν) (d := d) a ∗ piLpLaw (ν := ν) (d := d) b := by
  -- Proof comment: `toLp` is linear, so it commutes with additive convolution.
  change ((ν (a + b) : Measure (Fin d → ℝ)).map finPiLpEquiv.symm.toContinuousLinearMap) =
    ((ν a : Measure (Fin d → ℝ)).map finPiLpEquiv.symm.toContinuousLinearMap) ∗
      ((ν b : Measure (Fin d → ℝ)).map finPiLpEquiv.symm.toContinuousLinearMap)
  rw [IsConvolutionSemigroup.convolution_eq_toMeasure (ν := ν) a b,
    Measure.map_conv_continuousLinearMap finPiLpEquiv.symm.toContinuousLinearMap]

/-- Helper for Exercise 14.4.1: the pushed-forward characteristic functions inherit the
convolution-multiplication identity. -/
lemma piLpChar_add (a b : NNReal) (ξ : PiLp 2 (fun _ : Fin d ↦ ℝ)) :
    piLpChar (ν := ν) (d := d) (a + b) ξ =
      piLpChar (ν := ν) (d := d) a ξ * piLpChar (ν := ν) (d := d) b ξ := by
  simpa [piLpChar, MeasureTheory.charFun_conv] using
    congrArg (fun μ : Measure (PiLp 2 (fun _ : Fin d ↦ ℝ)) ↦ charFun μ ξ)
      (mapToPiLp_convolution_eq_toMeasure (ν := ν) (d := d) a b)

/-- Helper for Exercise 14.4.1: if the time increments `u n` converge to `0`, then the
characteristic functions of the mapped increment laws converge pointwise to `1`. -/
lemma incrementCharFun_tendsto_one {u : ℕ → NNReal} (hu : Tendsto u atTop (𝓝 0))
    (ξ : PiLp 2 (fun _ : Fin d ↦ ℝ)) :
    Tendsto (fun n ↦ piLpChar (ν := ν) (d := d) (u n) ξ) atTop (𝓝 1) := by
  -- Proof comment: compose the defining weak continuity at `0` with the increment sequence,
  -- push the result to the Euclidean `PiLp` model, and then read off pointwise convergence of
  -- characteristic functions there.
  have hν :
      Tendsto (fun n ↦ ν (u n)) atTop
        (𝓝 (diracProba (0 : Fin d → ℝ))) :=
    IsContinuousConvolutionSemigroup.tendsto_zero (ν := ν) |>.comp hu
  have hmap :
      Tendsto (fun n ↦ mapToPiLp (d := d) (ν (u n))) atTop
        (𝓝 (mapToPiLp (d := d) (diracProba (0 : Fin d → ℝ)))) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ ν (u n)) (diracProba (0 : Fin d → ℝ)) hν finPiLpEquiv.symm.continuous
  have hchar := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hmap) ξ
  have hdirac :
      charFun (Measure.map finPiLpEquiv.symm (↑(diracProba (0 : Fin d → ℝ)))) ξ = 1 := by
    simp [MeasureTheory.diracProba, Measure.map_dirac, MeasureTheory.charFun_dirac,
      finPiLpEquiv.symm.map_zero]
  simpa [piLpChar, piLpLaw, mapToPiLp, hdirac] using hchar

/-- Helper for Exercise 14.4.1: convolution is continuous on probability measures on `Fin d → ℝ`.
-/
lemma continuousMulProbabilityMeasure :
    Continuous (fun p : ProbabilityMeasure (Fin d → ℝ) × ProbabilityMeasure (Fin d → ℝ) ↦
      p.1 * p.2) := by
  -- Proof comment: convolution is product-measure formation followed by pushforward along
  -- addition.
  have hprod :
      Continuous
        (fun p : ProbabilityMeasure (Fin d → ℝ) × ProbabilityMeasure (Fin d → ℝ) ↦
          p.1.prod p.2) :=
    ProbabilityMeasure.continuous_prod
  have hmap :
      Continuous
        (fun η : ProbabilityMeasure ((Fin d → ℝ) × (Fin d → ℝ)) ↦
          ProbabilityMeasure.map η continuous_add.measurable.aemeasurable) :=
    ProbabilityMeasure.continuous_map continuous_add
  simpa [ProbabilityMeasure.conv_eq_map] using hmap.comp hprod

/-- Helper for Exercise 14.4.1: every continuous convolution semigroup is right-continuous at
each time `t`. -/
lemma tendstoWithinAt_Ici_of_pos {t : NNReal} (_ht : 0 < t) :
    Tendsto ν (𝓝[Set.Ici t] t) (𝓝 (ν t)) := by
  -- Proof comment: write `ν s` as `ν t * ν (s - t)` on `Ici t` and use continuity of
  -- convolution together with the defining continuity at `0`.
  have hsub_subtype :
      Tendsto (fun s : Set.Ici t ↦ s.1 - t) (𝓝 ⟨t, by simp⟩) (𝓝 0) := by
    apply NNReal.tendsto_coe.1
    have hcont : Continuous fun s : Set.Ici t ↦ ((s.1 : NNReal) : ℝ) - (t : ℝ) :=
      (NNReal.continuous_coe.comp continuous_subtype_val).sub continuous_const
    have hcoe :
        (fun s : Set.Ici t ↦ (((s.1 - t : NNReal) : ℝ))) =
          fun s : Set.Ici t ↦ ((s.1 : NNReal) : ℝ) - t := by
      funext s
      exact NNReal.coe_sub s.property
    have hsub_real :
        Tendsto (fun s : Set.Ici t ↦ ((s.1 : NNReal) : ℝ) - t) (𝓝 ⟨t, by simp⟩) (𝓝 0) := by
      convert hcont.continuousAt.tendsto using 1
      simp
    simpa [hcoe] using hsub_real
  have hsub :
      Tendsto (fun s : NNReal ↦ s - t) (𝓝[Set.Ici t] t) (𝓝 0) := by
    rw [tendsto_nhdsWithin_iff_subtype (show t ∈ Set.Ici t by simp)]
    simpa using hsub_subtype
  have hpair :
      Tendsto (fun u : NNReal ↦ (ν t, ν u)) (𝓝 0)
        (𝓝 (ν t, diracProba (0 : Fin d → ℝ))) := by
    exact tendsto_const_nhds.prodMk_nhds (IsContinuousConvolutionSemigroup.tendsto_zero (ν := ν))
  have hmul :
      Tendsto (fun u : NNReal ↦ ν t * ν u) (𝓝 0)
        (𝓝 (ν t * diracProba (0 : Fin d → ℝ))) :=
    continuousMulProbabilityMeasure (d := d) |>.continuousAt.tendsto.comp hpair
  have hconv :
      Tendsto (fun s : NNReal ↦ ν (t + (s - t))) (𝓝[Set.Ici t] t)
        (𝓝 (ν t * diracProba (0 : Fin d → ℝ))) := by
    simpa [IsConvolutionSemigroup.convolution_eq] using hmul.comp hsub
  have hrewrite : (fun s : NNReal ↦ ν (t + (s - t))) =ᶠ[𝓝[Set.Ici t] t] ν := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : t ≤ s := hs
    simp [add_tsub_cancel_of_le hs']
  have hlimit : ν t * diracProba (0 : Fin d → ℝ) = ν t := by
    rw [← ProbabilityMeasure.one_eq_diracProba, mul_one]
  simpa [hlimit] using hconv.congr' hrewrite

/-- Helper for Exercise 14.4.1: every continuous convolution semigroup is left-continuous at
each time `t`. -/
lemma tendstoWithinAt_Iic_of_pos {t : NNReal} (_ht : 0 < t) :
    Tendsto ν (𝓝[Set.Iic t] t) (𝓝 (ν t)) := by
  -- Proof comment: on the left we use `ν t = ν (s n) * ν (t - s n)` and divide by the increment
  -- characteristic function in the Euclidean `PiLp` model, where it is eventually nonzero.
  rw [Filter.tendsto_iff_seq_tendsto]
  intro s hs
  have hs_mem : ∀ᶠ n in atTop, s n ≤ t :=
    hs.eventually self_mem_nhdsWithin
  have hs_to_nhds : Tendsto s atTop (𝓝 t) :=
    hs.mono_right nhdsWithin_le_nhds
  have hs_real : Tendsto (fun n ↦ ((s n : NNReal) : ℝ)) atTop (𝓝 (t : ℝ)) :=
    NNReal.tendsto_coe.2 hs_to_nhds
  have hsub_real :
      Tendsto (fun n ↦ (t : ℝ) - ((s n : NNReal) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (t : ℝ)) atTop (𝓝 (t : ℝ))).sub hs_real
  have hsub_eventually :
      (fun n ↦ (t : ℝ) - ((s n : NNReal) : ℝ)) =ᶠ[atTop]
        fun n ↦ ((t - s n : NNReal) : ℝ) := by
    filter_upwards [hs_mem] with n hn
    exact (NNReal.coe_sub hn).symm
  have hsub :
      Tendsto (fun n ↦ t - s n) atTop (𝓝 0) :=
    NNReal.tendsto_coe.1 (hsub_real.congr' hsub_eventually)
  have hmap :
      Tendsto
        (fun n ↦ mapToPiLp (d := d) (ν (s n))) atTop
        (𝓝 (mapToPiLp (d := d) (ν t))) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro ξ
    have hincr := incrementCharFun_tendsto_one (ν := ν) (d := d) hsub ξ
    have hinv :
        Tendsto
          (fun n ↦ (piLpChar (ν := ν) (d := d) (t - s n) ξ)⁻¹)
          atTop (𝓝 1) := by
      simpa using hincr.inv₀ one_ne_zero
    have hmul :
        Tendsto
          (fun n ↦ piLpChar (ν := ν) (d := d) t ξ *
            (piLpChar (ν := ν) (d := d) (t - s n) ξ)⁻¹)
          atTop
          (𝓝 (piLpChar (ν := ν) (d := d) t ξ)) := by
      simpa using tendsto_const_nhds.mul hinv
    have hnonzero :
        ∀ᶠ n in atTop, piLpChar (ν := ν) (d := d) (t - s n) ξ ≠ 0 :=
      hincr.eventually (eventually_ne_nhds one_ne_zero)
    have hrewrite :
        (fun n ↦ piLpChar (ν := ν) (d := d) (s n) ξ) =ᶠ[atTop]
          fun n ↦ piLpChar (ν := ν) (d := d) t ξ *
            (piLpChar (ν := ν) (d := d) (t - s n) ξ)⁻¹ := by
      filter_upwards [hs_mem, hnonzero] with n hn hne
      have hfactor :
          piLpChar (ν := ν) (d := d) t ξ =
            piLpChar (ν := ν) (d := d) (s n) ξ * piLpChar (ν := ν) (d := d) (t - s n) ξ := by
        simpa [add_tsub_cancel_of_le hn] using
          piLpChar_add (ν := ν) (d := d) (s n) (t - s n) ξ
      exact (eq_mul_inv_iff_mul_eq₀ hne).2 hfactor.symm
    exact hmul.congr' hrewrite.symm
  simpa using
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n ↦ mapToPiLp (d := d) (ν (s n))) (mapToPiLp (d := d) (ν t))
      hmap finPiLpEquiv.continuous

-- Proof sketch: use the semigroup identity to rewrite nearby time marginals as convolutions with
-- increment laws tending to `δ₀`; for `s > t`, use `ν s = ν t ∗ ν (s - t)`, and for `s < t`, use
-- `ν t = ν s ∗ ν (t - s)`. The defining continuity at `0` then shows the increment laws converge
-- weakly to `δ₀`, and convolution with `δ₀` is the identity.
/-- Exercise 14.4.1: a continuous convolution semigroup on the chapter's `ℝ^d` model is
continuous at every positive time. -/
theorem continuousAt_of_pos {t : NNReal} (ht : 0 < t) :
    ContinuousAt ν t := by
  -- Proof comment: once the left and right within-limits are available, ordinary continuity is
  -- exactly their conjunction on the ordered time line.
  rw [continuousAt_iff_continuous_left_right]
  exact ⟨tendstoWithinAt_Iic_of_pos (ν := ν) ht, tendstoWithinAt_Ici_of_pos (ν := ν) ht⟩

/-- Reformulation of Exercise 14.4.1 as the corresponding limit statement. -/
theorem tendsto_of_pos {t : NNReal} (ht : 0 < t) :
    Tendsto ν (𝓝 t) (𝓝 (ν t)) :=
  (continuousAt_of_pos ht).tendsto

end IsContinuousConvolutionSemigroup

end
