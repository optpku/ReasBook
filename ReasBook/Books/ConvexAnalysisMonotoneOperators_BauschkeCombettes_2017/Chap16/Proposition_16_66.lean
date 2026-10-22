/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.ProximityOperator
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap14.Remark_14_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section SubdifferentialCalculus

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_innerProductSpace_l2

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.66 is the textbook swap formula for the proximity operator of
  `F^{*T}`.
- `core/canonical`: the owner constructions are the packaged Fenchel conjugate `F∗[hF]`, the
  transpose-conjugate owner `F∗ᵀ[hF]`, and Moreau's identity
  `Prox[f, hf] + Prox⋆[f, hf] = id`.
- `bridge/view`: this file should therefore use the canonical `Γ₀(H × H)` bridge `F∗ᵀ[hF]` and
  its prox notation `Prox⋆ᵀ[F, hF]`, rather than exposing witness terms for `F^{*T}`.
-/

-- Proof sketch: first transport proximality for `F∗[hF]` across the coordinate swap to identify
-- `Prox_{F^{*T}} p` with `swap (Prox_{F^*} (swap p))`. Then apply Moreau's identity
-- `Prox_F + Prox_{F^*} = Id` at `swap p` and swap the resulting equality back.
/-- Proposition 16.66: if `F ∈ Γ₀(H × H)` and `L(x, u) = (u, x)`, then the proximity operator of
`F^{*T}`, encoded canonically as `F∗ᵀ[hF]`, is `Id - L ∘ Prox_F ∘ L`, i.e.
`p ↦ p - (Prox_F (p.swap)).swap`. -/
theorem proximityOperator_gammaZeroConjugate_transpose_eq_id_sub_swap_proximityOperator_swap
    (F : H × H → Set.Ioi (⊥ : EReal)) (hF : F ∈ Γ₀(H × H)) :
    Prox⋆ᵀ[F, hF] =
      fun p : H × H ↦
        p - (Prox[F, hF] p.swap).swap := by
  funext p
  rcases p with ⟨x, u⟩
  have hswap_prox :
      Prox⋆ᵀ[F, hF] (x, u) = (Prox⋆[F, hF] (u, x)).swap := by
    symm
    apply eq_proximityOperator_of_isProxPoint (F∗ᵀ[hF])
      (hasUniqueProxPoint_of_mem_gammaZero (F∗ᵀ[hF])
        (gammaZeroConjugateTranspose_mem_gammaZero hF))
    rw [isProxPoint_iff_forall_inner_add_le (F∗ᵀ[hF])
      (gammaZeroConjugateTranspose_mem_gammaZero hF).2 (x, u)
      ((Prox⋆[F, hF] (u, x)).swap)]
    intro y
    rcases y with ⟨a, b⟩
    have hproxStar : IsProxPoint (F∗[hF]) (u, x) (Prox⋆[F, hF] (u, x)) :=
      proximityOperator_isProxPoint (F∗[hF])
        (hasUniqueProxPoint_of_mem_gammaZero (F∗[hF]) (gammaZeroConjugate_mem_gammaZero hF))
        (u, x)
    have hineq :=
      (isProxPoint_iff_forall_inner_add_le (F∗[hF])
        (gammaZeroConjugate_mem_gammaZero hF).2 (u, x) (Prox⋆[F, hF] (u, x))).1 hproxStar
    rcases hq : Prox⋆[F, hF] (u, x) with ⟨q₁, q₂⟩
    have hswap_inner :
        ⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ =
          ⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ := by
      rw [show ⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ =
          ⟪a - q₂, x - q₂⟫_ℝ + ⟪b - q₁, u - q₁⟫_ℝ by rfl]
      rw [show ⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ =
          ⟪b - q₁, u - q₁⟫_ℝ + ⟪a - q₂, x - q₂⟫_ℝ by rfl]
      simp [add_comm]
    have hswap_inner_ereal :
        (((⟪(a, b) - (q₁, q₂).swap, (x, u) - (q₁, q₂).swap⟫_ℝ : ℝ) : EReal)) =
          (((⟪(b, a) - (q₁, q₂), (u, x) - (q₁, q₂)⟫_ℝ : ℝ) : EReal)) := by
      exact_mod_cast hswap_inner
    have hineq' := hineq (b, a)
    rw [hswap_inner_ereal]
    simpa [hq, gammaZeroConjugateTranspose_apply, transpose_apply, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc] using hineq'
  have hmoreau_swap :
      (Prox⋆[F, hF] (u, x)).swap + (Prox[F, hF] (u, x)).swap = (x, u) := by
    simpa [add_comm] using congrArg Prod.swap
      (congrFun (proximityOperator_add_conjugateProximityOperator_eq_id_of_mem_gammaZero F hF)
        (u, x))
  calc
    Prox⋆ᵀ[F, hF] (x, u) = (Prox⋆[F, hF] (u, x)).swap := hswap_prox
    _ = (x, u) - (Prox[F, hF] (u, x)).swap := by
      exact (eq_sub_iff_add_eq.2 hmoreau_swap)

end SubdifferentialCalculus

end

end ERealFunction
