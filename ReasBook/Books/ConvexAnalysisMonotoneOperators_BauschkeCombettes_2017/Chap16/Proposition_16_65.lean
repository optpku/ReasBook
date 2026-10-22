/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2 prod_normedSpace_l2
  prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.65 records the textbook four-way equivalence at a contact pair
  `(x, u)` for an autoconjugate `F ∈ Γ₀(H × H)`.
- `core/canonical`: the owner notions are `autoconjugate`, `∂ F`, and `Prox[F, hF]`.
- `bridge/view`: this file should therefore only compose the existing Fenchel-conjugacy and
  proximal-point bridge theorems, not introduce a parallel local owner for the same contact set.

The refinement stays at the bridge/view layer and reuses Proposition 13.36 and Proposition 12.26,
with the conjugate contact clause handled directly from the canonical conjugate owner. -/

-- Proof sketch: autoconjugacy rewrites the conjugate contact clause as the primal contact clause.
-- Proposition 16.10 supplies the canonical Fenchel--Young equality criterion for subgradient
-- membership, and autoconjugacy identifies the two terms in that equality; Proposition 13.36 then
-- collapses the resulting doubled equality back to the single contact equation. Finally,
-- Proposition 12.26 identifies the same subdifferential inequality with the proximal-point
-- relation at the base point `(x + u, x + u)`.
/-- Proposition 16.65: for an autoconjugate member `F ∈ Γ₀(H × H)`, the equality
`F(x, u) = ⟪x, u⟫`, the corresponding equality for the conjugate at `(u, x)`, the subgradient
condition `(u, x) ∈ ∂F(x, u)`, and the proximal identity
`(x, u) = Prox_F (x + u, x + u)` are equivalent. -/
theorem autoconjugate_tfae_at_pair
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H))
    (hauto : autoconjugate F.asEReal) (x u : H) :
    List.TFAE
      [(F (x, u) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal),
        (F∗[hF] (u, x) : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal),
        (u, x) ∈ (∂ F) (x, u),
        (x, u) = Prox[F, hF] (x + u, x + u)] := by
  let pairing : EReal := ((⟪x, u⟫_ℝ : ℝ) : EReal)
  have hproper : IsProper F.asEReal := isProper_of_mem_gammaZero hF
  have hpair_le_F : pairing ≤ (F (x, u) : EReal) := by
    simpa [pairing] using pairing_le_autoconjugate hproper hauto x u
  have h12_raw :
      (F (x, u) : EReal) = pairing ↔ F.asEReal∗ (u, x) = pairing := by
    rw [conjugate_swap_eq_of_autoconjugate hauto x u]
  have h12 :
      (F (x, u) : EReal) = pairing ↔ (F∗[hF] (u, x) : EReal) = pairing := by
    simpa [gammaZeroConjugate_apply] using h12_raw
  have h13 :
      (F (x, u) : EReal) = pairing ↔ (u, x) ∈ (∂ F) (x, u) := by
    have hsum :
        (u, x) ∈ (∂ F) (x, u) ↔
          (F (x, u) : EReal) + (F (x, u) : EReal) = pairing + pairing := by
      rw [mem_subdifferential_iff_fenchel_young_eq F (x, u) (u, x),
        conjugate_swap_eq_of_autoconjugate hauto x u]
      have hpair_prod :
          (((⟪(x, u), (u, x)⟫_ℝ : ℝ) : EReal)) = pairing + pairing := by
        unfold pairing
        rw [show ⟪(x, u), (u, x)⟫_ℝ = ⟪x, u⟫_ℝ + ⟪u, x⟫_ℝ by rfl,
          real_inner_comm, ← EReal.coe_add]
      rw [hpair_prod]
    constructor
    · intro hcontact
      rw [hsum, hcontact]
    · intro hsub
      rw [hsum] at hsub
      have hle : (F (x, u) : EReal) ≤ pairing := by
        have hle_shift :
            (F (x, u) : EReal) + pairing ≤ pairing + pairing := by
          calc
            (F (x, u) : EReal) + pairing ≤ (F (x, u) : EReal) + (F (x, u) : EReal) :=
              by simpa [add_comm] using add_le_add_right hpair_le_F (F (x, u) : EReal)
            _ = pairing + pairing := hsub
        simpa [pairing] using
          (EReal.addLECancellable_coe ⟪x, u⟫_ℝ).add_le_add_iff_right.mp hle_shift
      exact le_antisymm hle hpair_le_F
  have h34 :
      (u, x) ∈ (∂ F) (x, u) ↔
        (x, u) = Prox[F, hF] (x + u, x + u) := by
    constructor
    · intro hsub
      apply eq_proximityOperator_of_isProxPoint F (hasUniqueProxPoint_of_mem_gammaZero F hF)
      rw [isProxPoint_iff_forall_inner_add_le F hF.2 (x + u, x + u) (x, u)]
      rw [mem_subdifferential_iff] at hsub
      intro y
      have hres : (x + u, x + u) - (x, u) = (u, x) := by
        simp
      have hy :
          ((⟪y - (x, u), (x + u, x + u) - (x, u)⟫_ℝ : ℝ) : EReal) +
              (F (x, u) : EReal) ≤ F y := by
        rw [hres]
        exact hsub y
      exact hy
    · intro hprox
      have hproxPoint : IsProxPoint F (x + u, x + u) (x, u) := by
        rw [hprox]
        exact proximityOperator_isProxPoint F (hasUniqueProxPoint_of_mem_gammaZero F hF)
          (x + u, x + u)
      rw [isProxPoint_iff_forall_inner_add_le F hF.2 (x + u, x + u) (x, u)] at hproxPoint
      rw [mem_subdifferential_iff]
      intro y
      have hres : (x + u, x + u) - (x, u) = (u, x) := by
        simp
      have hy :
          ((⟪y - (x, u), (u, x)⟫_ℝ : ℝ) : EReal) + (F (x, u) : EReal) ≤ F y := by
        rw [← hres]
        simpa [hprox] using hproxPoint y
      exact hy
  tfae_have 1 ↔ 2 := by
    simpa [pairing] using h12
  tfae_have 1 ↔ 3 := by
    simpa [pairing] using h13
  tfae_have 3 ↔ 4 := by
    change (u, x) ∈ (∂ F) (x, u) ↔
      (x, u) = Prox[F, hF] (x + u, x + u)
    exact h34
  tfae_finish

end SubdifferentialCalculus

end

end ERealFunction
