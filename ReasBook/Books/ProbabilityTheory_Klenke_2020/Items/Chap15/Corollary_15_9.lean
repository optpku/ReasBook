/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped RealInnerProductSpace

-- Proof sketch: apply `discreteFourierInversionFormula` to `μ` and `ν`; the hypothesis `hφ`
-- identifies the resulting integrals over `latticeFrequencyCube d`, hence the singleton masses of
-- `μ` and `ν` agree. Since `Fin d → ℤ` is countable, `MeasureTheory.ext_iff_measureReal_singleton`
-- concludes `μ = ν`.
/-- Corollary 15.9: a finite measure on `ℤ^d` is uniquely determined by the values of its
characteristic function on the fundamental domain `[-π, π)^d`. -/
theorem measure_eq_of_lattice_char_fun_eq_on_fundamental_domain
    {d : ℕ} {μ ν : Measure (Fin d → ℤ)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hφ :
      Set.EqOn (charFun (μ.map latticeEmbedding)) (charFun (ν.map latticeEmbedding))
        (latticeFrequencyCube d)) :
    μ = ν := by
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro x
  have hcube : MeasurableSet (latticeFrequencyCube d) := by
    unfold latticeFrequencyCube
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun i : Fin d ↦
      (show
          MeasurableSet
            {t : EuclideanSpace ℝ (Fin d) | t i ∈ Set.Ico (-Real.pi) Real.pi} from
        (PiLp.continuous_apply 2 _ i).measurable measurableSet_Ico)
  have hsingleton :
      ((μ.real ({x} : Set (Fin d → ℤ)) : ℂ)) = (ν.real ({x} : Set (Fin d → ℤ)) : ℂ) := by
    have hμ :
        (μ.real ({x} : Set (Fin d → ℤ)) : ℂ) =
          (((2 * Real.pi : ℝ) ^ d)⁻¹ : ℂ) *
            ∫ t in latticeFrequencyCube d,
              Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
                charFun (μ.map latticeEmbedding) t ∂volume := by
      simpa using (discreteFourierInversionFormula x)
    have hν :
        (ν.real ({x} : Set (Fin d → ℤ)) : ℂ) =
          (((2 * Real.pi : ℝ) ^ d)⁻¹ : ℂ) *
            ∫ t in latticeFrequencyCube d,
              Complex.exp (-((⟪t, latticeEmbedding x⟫ : ℝ) * Complex.I)) *
                charFun (ν.map latticeEmbedding) t ∂volume := by
      simpa using (discreteFourierInversionFormula x)
    rw [hμ, hν]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_mem hcube] with t ht
    simp [hφ ht]
  exact Complex.ofReal_injective hsingleton
