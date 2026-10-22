/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {S : Type v} [MeasurableSpace S] [TopologicalSpace S]

/-- Definition 25.37: for a domain `G` in the starting space `S`, a starting point `x ∈ G`, a
family of laws `Pₓ`, and a measurable boundary-valued exit-position map, the harmonic measure
`μ_{x,G}` is the pushforward law `Pₓ ∘ W_{τ_{Gᶜ}}⁻¹` on `frontier G`. -/
noncomputable abbrev harmonicMeasure
    (P : S → ProbabilityMeasure Ω) (G : Set S)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    (x : G) : ProbabilityMeasure (frontier G) :=
  (P x).map hExitMeas.aemeasurable

/-- Evaluating `harmonicMeasure` on a measurable set gives the starting law of the preimage under
the exit-position map. -/
@[simp] theorem harmonicMeasure_apply
    (P : S → ProbabilityMeasure Ω) (G : Set S)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    (x : G) {s : Set (frontier G)} (hs : MeasurableSet s) :
    harmonicMeasure P G exitValue hExitMeas x s = P x (exitValue ⁻¹' s) := by
  simpa [harmonicMeasure] using
    ProbabilityMeasure.map_apply (P x) hExitMeas.aemeasurable hs

/-- Integrating against `harmonicMeasure` is the same as integrating the pullback along the
Brownian exit-position map against the starting law. -/
theorem integral_harmonicMeasure
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (P : S → ProbabilityMeasure Ω) (G : Set S)
    (exitValue : Ω → frontier G) (hExitMeas : Measurable exitValue)
    (x : G) {f : frontier G → F}
    (hf : AEStronglyMeasurable f (harmonicMeasure P G exitValue hExitMeas x)) :
    ∫ y, f y ∂(harmonicMeasure P G exitValue hExitMeas x : Measure (frontier G)) =
      ∫ ω, f (exitValue ω) ∂(P x : Measure Ω) := by
  simpa [harmonicMeasure] using
    (integral_map hExitMeas.aemeasurable <| by
      simpa [harmonicMeasure] using hf)

end ProbabilityTheory
