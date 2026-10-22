/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section GammaZero

variable (f : H → Set.Ioi (⊥ : EReal))

-- Proof sketch: apply Proposition 12.26 at the proximal points of `x` and `y`, add the two
-- resulting variational inequalities, and rewrite the conclusion with the whole-space criterion
-- for firm nonexpansiveness.
/-- Proposition 12.28 (1): for `f ∈ Γ₀(H)`, the proximity operator `Prox_f` is firmly
nonexpansive. -/
theorem proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H))
    : FirmlyNonexpansive (Prox[f, hf]) := sorry

-- Proof sketch: combine the first clause with Proposition 4.4, which identifies firm
-- nonexpansiveness of a map with firm nonexpansiveness of its residual map `Id - T`.
/-- Proposition 12.28 (2): for `f ∈ Γ₀(H)`, the residual map `Id - Prox_f` is firmly
nonexpansive. -/
theorem id_sub_proximityOperator_firmlyNonexpansive_of_mem_gammaZero (hf : f ∈ Γ₀(H))
    : FirmlyNonexpansive (id - Prox[f, hf]) := sorry

end GammaZero

end ERealFunction
