/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace SetValuedOperator

section SelectionContinuity

variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*}
variable {Z : Type*} [TopologicalSpace Z]

/-- A map on the domain of a set-valued operator is continuous at `x` when it is continuous at
each subtype point over `x`. Actual selections are the main source of such maps, but the codomain
may also be changed by a canonical view such as `toWeakSpace`. -/
def SelectionContinuousAt (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) : Prop :=
  ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩

/-- Unfolding `SelectionContinuousAt` gives continuity of the map on the operator domain at each
subtype point over `x`. -/
theorem selectionContinuousAt_iff
    (A : SetValuedOperator X Y) (T : A.dom → Z) (x : X) :
    SelectionContinuousAt A T x ↔
      ∀ hx : x ∈ A.dom, ContinuousAt T ⟨x, hx⟩ :=
  Iff.rfl

end SelectionContinuity

end SetValuedOperator

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Proposition 17.31 identifies Gâteaux differentiability at `x` with singleton
-- subdifferential at `x`. Proposition 16.17 gives local boundedness and nonemptiness of nearby
-- subdifferentials on the interior effective domain, and Proposition 16.36 gives strong-weak
-- sequential closedness of `gra ∂ f`. These ingredients show that Gâteaux differentiability forces
-- every selection to converge weakly to the unique subgradient, while any weakly continuous
-- selection yields the directional-derivative inequalities needed to recover Gâteaux
-- differentiability.
/-- Proposition 17.39: for `f ∈ Γ₀(H)` and `x ∈ interior (effectiveDomain f)`, the following are
equivalent: (i) `x ↦ (f x : EReal).toReal` is Gâteaux differentiable at `x`; (ii) every selection
of `∂ f` is strong-to-weak continuous at `x`; (iii) there exists a selection of `∂ f` with the
same continuity property at `x`. -/
theorem gateauxDifferentiableAt_tfae_subdifferentialSelections_strongToWeakContinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    List.TFAE
      [GateauxDifferentiableAt (fun y ↦ (f y : EReal).toReal) x,
        ∀ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x,
        ∃ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ toWeakSpace ℝ H (G z : H)) x] := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
