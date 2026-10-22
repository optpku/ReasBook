/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {I : Type v}
variable {E : Type w}

/-- Definition 21.1 (1): two stochastic processes are modifications, or versions, of each other
if for every time `t` the random variables `X t` and `Y t` agree almost surely. -/
abbrev AreModifications (μ : Measure Ω) (X Y : I → Ω → E) : Prop :=
  ∀ t : I, X t =ᵐ[μ] Y t

/-- Definition 21.1 (2): two stochastic processes are indistinguishable if there is a measurable
null set outside of which all time coordinates agree simultaneously. -/
def AreIndistinguishable (μ : Measure Ω) (X Y : I → Ω → E) : Prop :=
  ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ t : I, {ω | X t ω ≠ Y t ω} ⊆ N

-- Proof sketch: if all disagreements are contained in one measurable null set `N`, then for each
-- fixed time `t` the disagreement event `{ω | X t ω ≠ Y t ω}` is also null, which is exactly
-- the almost-everywhere equality statement `X t =ᵐ[μ] Y t`.
/-- Indistinguishable processes are modifications of one another. -/
theorem areModifications_of_areIndistinguishable
    (μ : Measure Ω) (X Y : I → Ω → E) (hXY : AreIndistinguishable μ X Y) :
    AreModifications μ X Y := by
  rcases hXY with ⟨N, -, hN, hNsub⟩
  intro t
  rw [Filter.EventuallyEq, ae_iff]
  exact measure_mono_null (hNsub t) hN

end ProbabilityTheory
