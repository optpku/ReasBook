/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Theorem_20_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace
open ERealFunction
open WithLp

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: `hF` gives properness of `F`, while autoconjugacy and Proposition 13.36 yield the
-- pointwise lower bounds `⟪x, u⟫ ≤ F (x, u)` and `⟪x, u⟫ ≤ F∗ (u, x)`. Apply Theorem 20.46 to the
-- transpose-conjugate contact operator `pairingEqualityOperator ((F.asEReal∗)ᵀ)`;
-- autoconjugacy identifies this operator with the original pairing-contact operator
-- `pairingEqualityOperator F`.
/-- Corollary 20.47: on a real Hilbert space, if `F ∈ Γ₀(H × H)` is autoconjugate, then the
operator defined by `gra A = {(x, u) | F (x, u) = ⟪x, u⟫}` is maximally monotone. -/
theorem pairingEqualityOperator_isMaximallyMonotone_of_mem_gammaZero_of_autoconjugate
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H))
    (hauto : autoconjugate F.asEReal) :
    Maximal IsMonotone (pairingEqualityOperator F) := by
  have hF_proper : IsProper F.asEReal := isProper_of_mem_gammaZero hF
  have hF_conv : IsConvex F.asEReal := (asEReal_mem_gamma_of_mem_gammaZero hF).1
  have hFstar_proper : IsProper (F.asEReal∗) := by
    simpa [gammaZeroConjugate_apply] using
      (isProper_of_mem_gammaZero (gammaZeroConjugate_mem_gammaZero hF) :
        IsProper (F∗[hF]).asEReal)
  have hFstar_ge : ∀ x u : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F.asEReal∗ (u, x) := by
    intro x u
    simpa [real_inner_comm] using
      pairing_le_conjugate_of_autoconjugate hF_proper hauto u x
  have hF_ge : ∀ x u : H, ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ F.asEReal (x, u) := by
    intro x u
    simpa using pairing_le_autoconjugate hF_proper hauto x u
  have hmax : Maximal IsMonotone (pairingEqualityOperator ((F.asEReal∗)ᵀ)) :=
    pairingEqualityOperator_conjugateTranspose_isMaximallyMonotone
      F.asEReal hF_conv hFstar_proper hFstar_ge hF_ge
  have hEq : pairingEqualityOperator F = pairingEqualityOperator ((F.asEReal∗)ᵀ) := by
    ext x u
    change (F (x, u) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) ↔
        (F.asEReal∗) (u, x) = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    rw [conjugate_swap_eq_of_autoconjugate hauto x u]
  simpa [hEq] using hmax

end SetValuedOperator
