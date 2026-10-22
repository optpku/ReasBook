/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- Proof sketch: apply `MeasureTheory.toReal_rnDeriv_trim` with source measure `ν` and reference
-- measure `μ` to identify each trimmed Radon--Nikodym derivative with the conditional expectation
-- of the ambient density `fun x ↦ (ν.rnDeriv μ x).toReal` given the corresponding sub-σ-algebra.
-- Then use `MeasureTheory.Measure.integrable_toReal_rnDeriv` and
-- `MeasureTheory.Integrable.uniformIntegrable_condExp`.
/-- Example 8.23: if `μ` and `ν` are finite measures with `ν ≪ μ`, then the family of
Radon--Nikodym derivatives of the trimmed measures `ν.trim hℱ` with respect to `μ.trim hℱ`, indexed
by all sub-σ-algebras `ℱ ≤ mΩ`, is uniformly integrable with respect to `μ` after converting the
densities to real-valued functions via `ENNReal.toReal`. -/
theorem uniformIntegrable_trimmed_rnDeriv_family
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≪ μ) :
    UniformIntegrable
      (fun ℱ : {ℱ : MeasurableSpace Ω // ℱ ≤ mΩ} ↦
        fun x ↦ (((ν.trim ℱ.2).rnDeriv (μ.trim ℱ.2) x).toReal))
      1 μ := by
  let g : Ω → ℝ := fun x ↦ (ν.rnDeriv μ x).toReal
  have h_int : Integrable g μ := by
    simpa using
      (Measure.integrable_toReal_rnDeriv :
        Integrable (fun x ↦ (ν.rnDeriv μ x).toReal) μ)
  refine (h_int.uniformIntegrable_condExp fun ℱ ↦ ℱ.2).ae_eq ?_
  intro ℱ
  have htrim :
      (fun x ↦ (((ν.trim ℱ.2).rnDeriv (μ.trim ℱ.2) x).toReal)) =ᵐ[μ.trim ℱ.2]
        μ[g | ℱ.1] := by
    simpa using
      (toReal_rnDeriv_trim ℱ.2 hνμ :
        (fun x ↦ (((ν.trim ℱ.2).rnDeriv (μ.trim ℱ.2) x).toReal)) =ᵐ[μ.trim ℱ.2]
          μ[g | ℱ.1])
  exact (ae_eq_of_ae_eq_trim htrim).symm

/- The trimmed Radon--Nikodym derivative is the conditional expectation of the ambient density
with respect to the smaller σ-algebra. -/
recall MeasureTheory.toReal_rnDeriv_trim

/- Conditional expectations of one integrable real-valued function along any family of
sub-σ-algebras form a uniformly integrable family. -/
recall MeasureTheory.Integrable.uniformIntegrable_condExp
