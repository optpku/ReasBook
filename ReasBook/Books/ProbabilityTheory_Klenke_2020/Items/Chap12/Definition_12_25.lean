/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u v

section Family

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Definition 12.25: the empirical distribution of the finite family `X₁, …, Xₙ` is the
probability measure-valued map obtained by pushing forward the uniform law on the finite index set
`Fin n` along the sampled family. The explicit averaged-Dirac formula is recorded below as a
companion theorem. -/
noncomputable def empiricalDistribution (n : ℕ+) (X : Fin n → Ω → E) :
    Ω → ProbabilityMeasure E :=
  fun ω ↦
    ProbabilityMeasure.map
      ⟨(PMF.uniformOfFintype (Fin n)).toMeasure, inferInstance⟩
      ((Measurable.of_discrete : Measurable (fun i ↦ X i ω)).aemeasurable)

end Family

section Formula

variable {Ω : Type u}
variable {E : Type v} [MeasurableSpace E]

/-- The underlying measure of the empirical distribution is the averaged sum of the Dirac masses
at the sample values. This is the source-facing explicit formula corresponding to the canonical
pushforward definition above. -/
theorem empiricalDistribution_toMeasure
    [MeasurableSpace Ω] (n : ℕ+) (X : Fin n → Ω → E) (ω : Ω) :
    (empiricalDistribution n X ω : Measure E) =
      (n : ENNReal)⁻¹ • ∑ i : Fin n, Measure.dirac (X i ω) := by
  classical
  ext s hs
  rw [empiricalDistribution, ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (Measurable.of_discrete : Measurable (fun i ↦ X i ω)) hs]
  change (PMF.uniformOfFintype (Fin n)).toMeasure ((fun i ↦ X i ω) ⁻¹' s) = _
  have hpre : MeasurableSet ((fun i ↦ X i ω) ⁻¹' s) :=
    (Measurable.of_discrete : Measurable (fun i ↦ X i ω)) hs
  rw [PMF.toMeasure_uniformOfFintype_apply (((fun i ↦ X i ω) ⁻¹' s)) hpre]
  rw [Measure.smul_apply, Measure.finset_sum_apply]
  simp only [hs, smul_eq_mul, Measure.dirac_apply', Finset.sum_indicator_eq_sum_filter]
  rw [Fintype.card_subtype]
  simp [div_eq_mul_inv, mul_comm]

end Formula

section Tuple

variable {E : Type v} [MeasurableSpace E]

/-- The empirical distribution of a deterministic finite tuple. This is the tuple-level
`bridge/view` obtained by specializing `empiricalDistribution` to the deterministic sample space
`Unit`. -/
noncomputable def empiricalDistributionTuple {n : ℕ+} (x : Fin n → E) :
    ProbabilityMeasure E :=
  empiricalDistribution n (fun i (_ : Unit) ↦ x i) ()

end Tuple
