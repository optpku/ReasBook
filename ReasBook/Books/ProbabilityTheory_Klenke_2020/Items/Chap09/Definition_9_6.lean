/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {I : Type u} {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/- Definition 9.6: the distribution `ℒ[X] = P_X` of a random variable is the canonical
pushforward measure `P.map X`. -/
recall Measure.map

namespace IsStochasticProcess

variable {X : I → Ω → E}

/-- The path-valued map associated with a stochastic process is measurable. -/
theorem measurable_pathMap (hX : IsStochasticProcess X) :
    Measurable[mΩ] (fun ω t ↦ X t ω) :=
  measurable_pi_lambda _ fun t ↦ hX.measurable t

/-- Definition 9.6: the law of a stochastic process is the pushforward of the underlying measure
along the path-valued map `ω ↦ (t ↦ X t ω)`. -/
theorem hasLaw_pathMap (P : Measure Ω) (hX : IsStochasticProcess X) :
    HasLaw (fun ω t ↦ X t ω) (P.map (fun ω t ↦ X t ω)) P :=
  ⟨hX.measurable_pathMap.aemeasurable, rfl⟩

end IsStochasticProcess

/- The random-variable form of a regular conditional distribution is the canonical kernel
`ProbabilityTheory.condDistrib`. -/
recall condDistrib

/- Definition 9.6: the source-facing notion of a conditional law given a sub-σ-algebra is a
regular conditional distribution, organized by the owner abstraction
`ProbabilityTheory.IsRegularCondDistrib`. -/
recall ProbabilityTheory.IsRegularCondDistrib

/- For conditioning by a sub-σ-algebra `𝒢`, the canonical kernel owner is
`ProbabilityTheory.condExpKernel`; the `X`-dependent conditional law is obtained by `Kernel.map`. -/
recall condExpKernel

section CondLaw

/-- Under the standard-Borel hypothesis on `Ω`, the canonical bridge from conditioning by the
sub-σ-algebra `𝒢` to a conditional law of `X` is the mapped kernel
`((condExpKernel P 𝒢).map X)`. -/
theorem isRegularCondDistrib_condExpKernel_map [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → E} (hX : Measurable[mΩ] X)
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) :
    IsRegularCondDistrib P 𝒢 X (((condExpKernel (mΩ := mΩ) P 𝒢).map X)) := by
  refine
    { toIsMarkovKernel := by
        simpa [Kernel.mapOfMeasurable_eq_map _ hX] using
          Kernel.IsMarkovKernel.map (condExpKernel (mΩ := mΩ) P 𝒢) hX
      le_ambient := h𝒢
      measurable_Y := hX
      ae_eq_conditionalProbability := ?_ }
  intro B hB
  have hXB := hX hB
  simpa [measureReal_def, Kernel.map_apply' _ hX _ hB] using
    condExpKernel_ae_eq_condExp (mΩ := mΩ) h𝒢 hXB

/-- Definition 9.6: for a measurable random variable `X`, the canonical bridge
`((condExpKernel P 𝒢).map X)` realizes the conditional probabilities of the events `{X ∈ B}`. -/
theorem condLaw_ae_eq_condExpKernel_map [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → E} (hX : Measurable[mΩ] X)
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {s : Set E} (hs : MeasurableSet s) :
    (fun ω ↦ (((condExpKernel (mΩ := mΩ) P 𝒢).map X) ω).real s) =ᵐ[P]
      P⟦X ⁻¹' s | 𝒢⟧ := by
  have hXs := hX hs
  simpa [measureReal_def, Kernel.map_apply' _ hX _ hs] using
    condExpKernel_ae_eq_condExp (mΩ := mΩ) h𝒢 hXs

namespace IsStochasticProcess

variable {X : I → Ω → E}

/-- Under the standard-Borel hypothesis on `Ω`, the canonical conditional law of the path-valued
map `ω ↦ (t ↦ X t ω)` given `𝒢` is the mapped kernel
`((condExpKernel P 𝒢).map (fun ω t ↦ X t ω))`. -/
theorem isRegularCondDistrib_pathMap_condExpKernel_map [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (hX : IsStochasticProcess X)
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) :
    IsRegularCondDistrib P 𝒢 (fun ω t ↦ X t ω)
      ((condExpKernel (mΩ := mΩ) P 𝒢).map (fun ω t ↦ X t ω)) := by
  have hpath : Measurable[mΩ] (fun ω t ↦ X t ω) :=
    @measurable_pi_lambda Ω I (fun _ ↦ E) mΩ (fun _ ↦ mE) (fun ω t ↦ X t ω)
      fun t ↦ show Measurable[mΩ] (X t) from hX t
  refine
    { toIsMarkovKernel := by
        simpa [Kernel.mapOfMeasurable_eq_map _ hpath] using
          Kernel.IsMarkovKernel.map (condExpKernel (mΩ := mΩ) P 𝒢) hpath
      le_ambient := h𝒢
      measurable_Y := hpath
      ae_eq_conditionalProbability := ?_ }
  intro B hB
  have hpathB := hpath hB
  simpa [measureReal_def, Kernel.map_apply' _ hpath _ hB] using
    condExpKernel_ae_eq_condExp (mΩ := mΩ) h𝒢 hpathB

/-- Definition 9.6: the canonical conditional law of a stochastic process given `𝒢` is the image
of `condExpKernel P 𝒢` under the path-valued map `ω ↦ (t ↦ X t ω)`. -/
theorem pathMap_condLaw_ae_eq_condExpKernel_map [StandardBorelSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (hX : IsStochasticProcess X)
    {𝒢 : MeasurableSpace Ω} (h𝒢 : 𝒢 ≤ mΩ) {s : Set (I → E)} (hs : MeasurableSet s) :
    (fun ω ↦
      (((condExpKernel (mΩ := mΩ) P 𝒢).map (fun ω t ↦ X t ω)) ω).real s) =ᵐ[P]
      P⟦(fun ω t ↦ X t ω) ⁻¹' s | 𝒢⟧ := by
  have hpath : Measurable[mΩ] (fun ω t ↦ X t ω) :=
    @measurable_pi_lambda Ω I (fun _ ↦ E) mΩ (fun _ ↦ mE) (fun ω t ↦ X t ω)
      fun t ↦ show Measurable[mΩ] (X t) from hX t
  have hpaths := hpath hs
  simpa [measureReal_def, Kernel.map_apply' _ hpath _ hs] using
    condExpKernel_ae_eq_condExp (mΩ := mΩ) h𝒢 hpaths

end IsStochasticProcess

end CondLaw
