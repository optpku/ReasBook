/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_39

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

open SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use the interior-domain hypotheses together with the local boundedness and
-- nonemptiness results for `∂ f` to compare subgradient selections near `x`. Fréchet
-- differentiability forces all such selections to converge to the unique subgradient at `x`,
-- clause (ii) trivially implies clause (iii), and a continuous local selection yields the little-o
-- estimate characterizing Fréchet differentiability.
/-- Proposition 17.41: for `f ∈ Γ₀(H)` and `x ∈ interior (effectiveDomain f)`, the following are
equivalent: (i) `x ↦ (f x : EReal).toReal` is Fréchet differentiable at `x`; (ii) every selection
of `∂ f` is continuous at `x`; (iii) there exists a selection of `∂ f` that is continuous at
`x`. -/
theorem frechetDifferentiableAt_tfae_subdifferentialSelections_continuousAt
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    List.TFAE
      [DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x,
        ∀ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x,
        ∃ G : Selection (∂ f),
          SelectionContinuousAt (∂ f) (fun z : (∂ f).dom ↦ (G z : H)) x] := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
