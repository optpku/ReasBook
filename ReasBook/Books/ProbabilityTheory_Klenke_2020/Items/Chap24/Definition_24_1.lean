/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped ENNReal Topology

universe u

section

variable {E : Type u}

/-- The source-facing space `\mathcal{M}(E)` of boundedly finite measures: measures that assign
finite mass to every bounded measurable subset of `E`. -/
def BoundedlyFiniteMeasure (E : Type u) [PseudoMetricSpace E] [MeasurableSpace E] : Type u :=
  {μ : Measure E // ∀ ⦃A : Set E⦄, MeasurableSet A → Bornology.IsBounded A → μ A < ∞}

namespace BoundedlyFiniteMeasure

variable [PseudoMetricSpace E] [MeasurableSpace E]

/-- A boundedly finite measure can be interpreted as an ordinary measure. -/
@[coe] def toMeasure : BoundedlyFiniteMeasure E → Measure E := Subtype.val

instance : Coe (BoundedlyFiniteMeasure E) (Measure E) := ⟨toMeasure⟩

/-- A boundedly finite measure assigns finite mass to every bounded measurable subset of `E`. -/
theorem lt_top_of_isBounded (μ : BoundedlyFiniteMeasure E) {A : Set E}
    (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    (μ : Measure E) A < ∞ :=
  μ.2 hA hA_bdd

end BoundedlyFiniteMeasure

/-- Definition 24.1: `𝕄` is the smallest sigma-algebra on the space `\mathcal{M}(E)` of boundedly
finite measures with respect to which every bounded Borel evaluation map `μ ↦ μ(A)` is
measurable. -/
abbrev randomMeasureMeasurableSpace (E : Type u) [PseudoMetricSpace E]
    [MeasurableSpace E] :
    MeasurableSpace (BoundedlyFiniteMeasure E) :=
  ⨆ (A : Set E) (_ : MeasurableSet A) (_ : Bornology.IsBounded A),
    (borel ℝ≥0∞).comap fun μ ↦ (μ : Measure E) A

/-- The defining supremum formula for the random-measure sigma-algebra on
`BoundedlyFiniteMeasure E`. -/
@[simp]
theorem randomMeasureMeasurableSpace_def [PseudoMetricSpace E] [MeasurableSpace E] :
    randomMeasureMeasurableSpace E =
      ⨆ (A : Set E) (_ : MeasurableSet A) (_ : Bornology.IsBounded A),
        (borel ℝ≥0∞).comap fun μ : BoundedlyFiniteMeasure E ↦ (μ : Measure E) A :=
  rfl

/-- The sigma-algebra `randomMeasureMeasurableSpace E` is the ambient measurable structure on
`BoundedlyFiniteMeasure E`. -/
instance [PseudoMetricSpace E] [MeasurableSpace E] :
    MeasurableSpace (BoundedlyFiniteMeasure E) :=
  randomMeasureMeasurableSpace E

/-- Evaluation on a bounded Borel set is measurable for the random-measure sigma-algebra. -/
theorem measurable_apply_of_isBounded [PseudoMetricSpace E] [MeasurableSpace E]
    (A : Set E) (hA : MeasurableSet A)
    (hA_bdd : Bornology.IsBounded A) :
    Measurable fun μ : BoundedlyFiniteMeasure E ↦ (μ : Measure E) A := by
  exact Measurable.of_comap_le <|
    le_iSup_of_le A <| le_iSup_of_le hA <| le_iSup_of_le hA_bdd <| le_rfl

namespace MeasureTheory
namespace ProbabilityMeasure

variable [PseudoMetricSpace E] [MeasurableSpace E]

/-- Helper for Definition 24.1: a probability measure has finite mass on every bounded measurable
set. -/
theorem lt_top_apply_of_isBounded (μ : ProbabilityMeasure E) {A : Set E}
    (_hA : MeasurableSet A) (_hA_bdd : Bornology.IsBounded A) :
    (μ : Measure E) A < ∞ := by
  exact measure_lt_top (μ : Measure E) A

/-- The canonical inclusion of `\mathcal M_1(E)` into the space `\mathcal M(E)` of boundedly
finite measures. -/
def toBoundedlyFiniteMeasure (μ : ProbabilityMeasure E) : BoundedlyFiniteMeasure E :=
  ⟨μ, fun _ hA hA_bdd ↦ lt_top_apply_of_isBounded μ hA hA_bdd⟩

/-- Coercing `μ.toBoundedlyFiniteMeasure` back to a measure recovers `μ`. -/
@[simp] theorem toMeasure_toBoundedlyFiniteMeasure (μ : ProbabilityMeasure E) :
    (μ.toBoundedlyFiniteMeasure : Measure E) = (μ : Measure E) :=
  rfl

end ProbabilityMeasure
end MeasureTheory

/-- Helper for Definition 24.1: compact support makes `support f` a bounded subset of `E`. -/
lemma isBounded_support_of_hasCompactSupport [PseudoMetricSpace E] {f : E → ℝ}
    (hf_compact : HasCompactSupport f) :
    Bornology.IsBounded (Function.support f) := by
  -- The ordinary support sits inside the compact topological support.
  exact Bornology.IsBounded.subset hf_compact.isCompact.isBounded (subset_tsupport f)

/-- Helper for Definition 24.1: a boundedly finite measure has finite mass on the measurable
support of a measurable compactly supported function. -/
lemma measure_support_lt_top_of_measurable_hasCompactSupport [PseudoMetricSpace E]
    [MeasurableSpace E] (μ : BoundedlyFiniteMeasure E) {f : E → ℝ}
    (hf_measurable : Measurable f) (hf_compact : HasCompactSupport f) :
    (μ : Measure E) (Function.support f) < ∞ := by
  -- The support is measurable because it is the complement of the zero fiber.
  have h_support_meas : MeasurableSet (Function.support f) := by
    have h_support_eq : Function.support f = (f ⁻¹' ({0} : Set ℝ))ᶜ := by
      ext x
      simp [Function.support]
    rw [h_support_eq]
    exact (hf_measurable (measurableSet_singleton 0)).compl
  -- Compact support gives the boundedness required by bounded finiteness.
  have h_support_bdd : Bornology.IsBounded (Function.support f) :=
    isBounded_support_of_hasCompactSupport hf_compact
  exact μ.lt_top_of_isBounded h_support_meas h_support_bdd

/-- Helper for Definition 24.1: a bounded measurable function is integrable on its support against
a boundedly finite measure when its range is bounded and its support is compact. -/
lemma integrableOn_support_of_bounded_range [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : BoundedlyFiniteMeasure E) {f : E → ℝ} (hf_measurable : Measurable f)
    (hf_bdd : Bornology.IsBounded (range f)) (hf_compact : HasCompactSupport f) :
    IntegrableOn f (Function.support f) (μ : Measure E) := by
  -- Use the measurable support as the finite-measure carrier.
  have h_support_finite : (μ : Measure E) (Function.support f) < ∞ :=
    measure_support_lt_top_of_measurable_hasCompactSupport μ hf_measurable hf_compact
  -- Convert bounded range into a global norm bound for `f`.
  obtain ⟨C, hC_range⟩ := hf_bdd.exists_norm_le
  have hC : ∀ x, ‖f x‖ ≤ C := fun x ↦ hC_range _ (mem_range_self x)
  -- A bounded measurable function is integrable on a finite-measure set.
  exact Measure.integrableOn_of_bounded h_support_finite.ne
    hf_measurable.aestronglyMeasurable (ae_of_all _ hC)

-- Proof sketch: the compact support is bounded in a pseudometric space, hence has finite measure
-- for a boundedly finite measure; the bounded range gives a uniform bound on `‖f‖`, so the
-- integral of `|f|` over its support is finite and `f` is integrable.
/-- Every bounded measurable real-valued function with compact support is integrable against a
boundedly finite measure. -/
theorem integrable_of_measurable_isBounded_range_hasCompactSupport
    [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : BoundedlyFiniteMeasure E) {f : E → ℝ} (hf_measurable : Measurable f)
    (hf_bdd : Bornology.IsBounded (range f)) (hf_compact : HasCompactSupport f) :
    Integrable f (μ : Measure E) := by
  -- Work on the measurable support, where bounded finiteness gives finite mass.
  have h_support_integrable : IntegrableOn f (Function.support f) (μ : Measure E) :=
    integrableOn_support_of_bounded_range μ hf_measurable hf_bdd hf_compact
  -- Outside `support f` the function vanishes, so support-local integrability is global.
  exact
    (integrableOn_iff_integrable_of_support_subset
      (subset_rfl : Function.support f ⊆ Function.support f)).mp
      h_support_integrable

/-- Helper for Definition 24.1: the integral of a bounded measurable compactly supported
real-valued function has finite absolute-value integral against a boundedly finite measure. -/
lemma hasFiniteIntegral_of_measurable_isBounded_range_hasCompactSupport
    [PseudoMetricSpace E] [MeasurableSpace E]
    (μ : BoundedlyFiniteMeasure E) {f : E → ℝ} (hf_measurable : Measurable f)
    (hf_bdd : Bornology.IsBounded (range f)) (hf_compact : HasCompactSupport f) :
    HasFiniteIntegral f (μ : Measure E) := by
  -- Reuse the global integrability theorem to package the finiteness statement directly.
  have h_integrable : Integrable f (μ : Measure E) :=
    integrable_of_measurable_isBounded_range_hasCompactSupport
      μ hf_measurable hf_bdd hf_compact
  -- `Integrable` exposes the desired finite-integral property.
  exact h_integrable.hasFiniteIntegral

end
