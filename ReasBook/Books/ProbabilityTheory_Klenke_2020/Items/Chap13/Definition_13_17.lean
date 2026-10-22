/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

universe u v w x

/- Definition 13.17: convergence in distribution of random variables is the canonical mathlib
notion `MeasureTheory.TendstoInDistribution`, i.e. weak convergence in `ProbabilityMeasure E` of
the laws of the random variables. -/
recall MeasureTheory.TendstoInDistribution

section

variable {ι : Type u} {Ω : ι → Type v} {Ω' : Type w} {E : Type x}
variable {m : ∀ i, MeasurableSpace (Ω i)} {m' : MeasurableSpace Ω'} {mE : MeasurableSpace E}
variable [TopologicalSpace E] [OpensMeasurableSpace E]
variable {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
variable {μ' : Measure Ω'} [IsProbabilityMeasure μ']
variable {X : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

-- Proof sketch: unfold `MeasureTheory.TendstoInDistribution`; the forward direction is its `tendsto`
-- field rewritten using `hZ.map_eq`, and the reverse direction repackages the given weak
-- convergence of the pushed-forward laws together with the assumed a.e.-measurability.
/-- If `Z` has law `ν`, then convergence in distribution of `X i` to `Z` is exactly weak
convergence of the laws of `X i` to the probability measure `ν`. This is the textbook notation
`X_i \implies \mathbf P_Z` that specifies only the limiting distribution. -/
theorem tendstoInDistribution_iff_tendsto_limit_law
    (hX : ∀ i, AEMeasurable (X i) (μ i)) {ν : ProbabilityMeasure E}
    (hZ : HasLaw Z (ν : Measure E) μ') :
    TendstoInDistribution X l Z μ μ' ↔
      Tendsto
        (fun i ↦ ⟨(μ i).map (X i), Measure.isProbabilityMeasure_map (hX i)⟩) l (𝓝 ν) := by
  constructor
  · intro h
    have hν : (⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩ :
        ProbabilityMeasure E) = ν := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa using hZ.map_eq
    simpa [hν] using h.tendsto
  · intro h
    have hν : (⟨μ'.map Z, Measure.isProbabilityMeasure_map hZ.aemeasurable⟩ :
        ProbabilityMeasure E) = ν := by
      apply ProbabilityMeasure.toMeasure_injective
      simpa using hZ.map_eq
    refine ⟨hX, hZ.aemeasurable, ?_⟩
    simpa [hν] using h

end
