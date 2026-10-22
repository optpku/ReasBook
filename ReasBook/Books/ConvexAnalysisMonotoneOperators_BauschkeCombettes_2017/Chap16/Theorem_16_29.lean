/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_16

open scoped InnerProductSpace Pointwise Set
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

-- Proof sketch: Proposition 16.16 gives the equivalence of clauses `(i)`, `(ii)`, and `(iii)`.
-- Corollary 16.30 identifies clause `(iv)` with clause `(i)` by rewriting `(∂ f)⁻¹` as the
-- subdifferential of the canonical packaged conjugate `gammaZeroConjugate f hf`.
/-- Theorem 16.29: for `f ∈ Γ₀(H)`, membership of `(x, u)` in the graph of `∂ f`, membership of
`(u, -1)` in the normal cone to `epi f` at `(x, f x)`, equality in the Fenchel--Young identity,
and membership of `(u, x)` in the graph of `∂ f^*` are equivalent. In Lean, clauses (i) and (iv)
are written as the corresponding subdifferential-membership statements, and clause (ii) uses the
real-height epigraph point `(x, (f x : EReal).toReal)`. -/
theorem subdifferential_normalCone_fenchelYoung_conjugate_tfae
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x u : H) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal),
        x ∈ (∂ (gammaZeroConjugate f hf)) u] := by
  have htfae := subdifferential_normalCone_fenchelYoung_tfae f hf.2 x u
  have h12 :
      u ∈ (∂ f) x ↔
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) :=
    by simpa using (htfae _ (by simp) _ (by simp))
  have h23 :
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    by simpa using (htfae _ (by simp) _ (by simp))
  have hinv := inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf
  have h14 :
      u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u := by
    rw [← hinv]
    exact (SetValuedOperator.mem_inverse_iff (∂ f.asEReal) u x).symm
  tfae_have 1 ↔ 2 := by
    change u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
    exact h12
  tfae_have 2 ↔ 3 := by
    change (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    exact h23
  tfae_have 1 ↔ 4 := by
    change u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u
    exact h14
  tfae_finish

end SubdifferentialConjugation

end

end ERealFunction
