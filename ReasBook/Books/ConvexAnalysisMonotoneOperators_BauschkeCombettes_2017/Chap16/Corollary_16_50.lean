/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_48

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped BigOperators InnerProductSpace Pointwise

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: prove the statement by induction on the family length. In the inductive step,
-- apply Corollary 16.48 to the pair consisting of the last function and the preceding finite sum;
-- clause (i) is used directly, while clauses (ii)--(v) reduce to clause (i) through Proposition
-- 6.20 together with Proposition 8.2, exactly as in the source proof.
/-- Corollary 16.50: for a finite family `f : Fin (n + 2) → Γ₀(H)` corresponding to the textbook
index set `{1, ..., m}` with `m ≥ 2`, if one of the source regularity conditions (i)--(v) holds
for the effective domains, then the subdifferential of the finite sum is the finite sum of the
subdifferentials. -/
theorem subdifferential_sum_eq_sum_of_successiveDomainRegularity
    (n : ℕ) (f : Fin (n + 2) → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin (n + 2), f i ∈ Γ₀(H))
    (hregular :
      (0 : H) ∈ successiveStrongRelativeInteriorIntersection n
          (fun i ↦ effectiveDomain (f i)) ∨
        successiveDifferenceRegularity n (fun i ↦ effectiveDomain (f i))) :
    (∂ (∑ i, f i) : SetValuedOperator H H) = ∑ i, ∂ f i := sorry

end SubdifferentialCalculus

end

end ERealFunction
