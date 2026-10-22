/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Definition_7_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory MeasureTheory.Measure Set
open scoped ENNReal

-- Proof sketch: `gaussianReal 0 1 = volume.withDensity (gaussianPDF 0 1)`, and the Gaussian
-- density is everywhere positive and finite, so applying `withDensity_inv_same` yields the
-- reciprocal-density representation of Lebesgue measure.
/-- Example 7.38 (1): Lebesgue measure is obtained from the standard normal law on `ℝ` by the
reciprocal Gaussian density. -/
theorem standardNormal_withDensity_inv_eq_volume :
    (gaussianReal 0 1).withDensity (fun x ↦ (gaussianPDF 0 1 x)⁻¹) = volume := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero]
  exact withDensity_inv_same (measurable_gaussianPDF 0 1)
    (ae_of_all _ fun x ↦ (gaussianPDF_pos 0 one_ne_zero x).ne')
    (ae_of_all _ fun x ↦ gaussianPDF_ne_top)

/- Example 7.38 (2): Lebesgue measure on `ℝ` is absolutely continuous with respect to the
standard normal law; more generally, mathlib's canonical theorem
`gaussianReal_absolutelyContinuous'` gives `volume ≪ gaussianReal μ v` for every nondegenerate
real Gaussian, and the textbook statement is the specialization `μ = 0`, `v = 1`. -/
recall gaussianReal_absolutelyContinuous' (μ : ℝ) {v : NNReal} (hv : v ≠ 0) :
  volume ≪ gaussianReal μ v

-- Proof sketch: the sets `Ici (n : ℝ)` are decreasing with empty intersection, and
-- `gaussianReal 0 1` is a finite measure; continuity from above gives convergence of their masses
-- to `0`.
/-- Example 7.38 (3): The right-tail masses of the standard normal law converge to `0`. -/
theorem standardNormal_rightTail_tendsto_zero :
    Filter.Tendsto (fun n : ℕ ↦ gaussianReal 0 1 (Ici (n : ℝ))) Filter.atTop (nhds 0) :=
  by
    have hs : ∀ n : ℕ, NullMeasurableSet (Ici (n : ℝ)) (gaussianReal 0 1) :=
      fun _ ↦ measurableSet_Ici.nullMeasurableSet
    have hmono : Antitone fun n : ℕ ↦ Ici (n : ℝ) :=
      fun _ _ hmn ↦ Ici_subset_Ici.2 (Nat.cast_le.mpr hmn)
    have h_empty : (⋂ n : ℕ, Ici (n : ℝ)) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro x
      simpa only [mem_iInter, mem_Ici, not_forall, not_le] using exists_nat_gt x
    simpa [Function.comp, h_empty] using
      tendsto_measure_iInter_atTop hs hmono ⟨0, by simp⟩

/- Example 7.38 (4): Every right tail `[a, ∞)` has infinite Lebesgue measure; the textbook
`n : ℕ` case is the specialization `a = n` of the canonical theorem `Real.volume_Ici`. -/
recall Real.volume_Ici (a : ℝ) : volume (Ici a) = ∞

-- Proof sketch: if `volume` were totally continuous with respect to `gaussianReal 0 1`, then the
-- vanishing standard-normal tails from `standardNormal_rightTail_tendsto_zero` would force the
-- Lebesgue masses of the same tails to become arbitrarily small. This contradicts
-- `Real.volume_Ici`.
/-- Example 7.38 (5): Lebesgue measure is not totally continuous with respect to the standard
normal law. -/
theorem not_totallyContinuous_volume_standardNormal :
    ¬ TotallyContinuous volume (gaussianReal 0 1) := by
  intro htot
  have hone : 0 < (1 : ENNReal) := by
    simp
  rcases htot hone with ⟨δ, hδ, hδ_spec⟩
  have htail :
      ∀ᶠ n : ℕ in Filter.atTop, gaussianReal 0 1 (Ici (n : ℝ)) < δ :=
    standardNormal_rightTail_tendsto_zero.eventually (Iio_mem_nhds hδ)
  obtain ⟨n, hn⟩ := htail.exists
  have hvol_lt : volume (Ici (n : ℝ)) < 1 :=
    hδ_spec measurableSet_Ici hn
  have hnot_lt : ¬ volume (Ici (n : ℝ)) < 1 := by
    simp [Real.volume_Ici]
  exact hnot_lt hvol_lt
