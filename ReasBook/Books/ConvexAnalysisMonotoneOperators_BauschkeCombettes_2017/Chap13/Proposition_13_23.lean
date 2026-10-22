/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace translate

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand `conjugate`, pull the positive scalar `α` out of the supremum, and rewrite
-- `⟪x, u⟫ - α f x` as `α * (⟪x, α⁻¹ • u⟫ - f x)`.
/-- Proposition 13.23 (1): clause (i). Scaling an extended-real-valued function by a positive
scalar sends its conjugate to the same scalar multiple of the conjugate evaluated at the inversely
scaled dual variable. -/
theorem conjugate_pos_smul
    (f : H → EReal) (α : Set.Ioi (0 : ℝ)) :
    (fun x : H ↦ ((α : ℝ) : EReal) * f x)∗ =
      fun u : H ↦ ((α : ℝ) : EReal) * f∗ (((α : ℝ)⁻¹) • u) := sorry

-- Proof sketch: combine clause (i) with the change of variables `x = α • z` in the defining
-- supremum, or equivalently precompose by the inverse homothety and absorb the scaling into the
-- dual pairing.
/-- Proposition 13.23 (2): clause (ii). The conjugate of the positively scaled precomposition
`x ↦ α f(α⁻¹ • x)` is the positive scalar multiple `α f*`. -/
theorem conjugate_pos_smul_precompose_inv_smul
    (f : H → EReal) (α : Set.Ioi (0 : ℝ)) :
    (fun x : H ↦ ((α : ℝ) : EReal) * f (((α : ℝ)⁻¹) • x))∗ =
      fun u : H ↦ ((α : ℝ) : EReal) * f∗ u := sorry

-- Proof sketch: translate the supremum by `x = z + y`, separate the linear and constant terms,
-- and identify the remaining supremum with `τ v (f∗)`.
/-- Proposition 13.23 (3): clause (iii). Translating `f` by `y`, adding the linear functional
`x ↦ ⟪x, v⟫`, and shifting by a real constant translates the conjugate by `v` and adds the dual
affine correction. -/
theorem conjugate_translate_add_inner_add_const
    (f : H → EReal) (y v : H) (β : ℝ) :
    ((τ y f) + (fun x : H ↦ ((⟪x, v⟫_ℝ : ℝ) : EReal)) + fun _ : H ↦ ((β : ℝ) : EReal))∗ =
      τ v (f∗) + fun u : H ↦
        ((⟪y, u⟫_ℝ : ℝ) : EReal) - ((⟪y, v⟫_ℝ : ℝ) : EReal) - ((β : ℝ) : EReal) := sorry

section

variable [CompleteSpace H]

-- Proof sketch: rewrite the conjugate of `f ∘ e` by the substitution `x = e.symm z`, then move
-- the operator through the inner product via the adjoint identity and identify the remaining
-- supremum with `conjugate f`.
/-- Proposition 13.23 (4): clause (iv). Precomposing with a continuous linear equivalence sends the
conjugate to precomposition with the adjoint of the inverse operator. -/
theorem conjugate_comp_continuousLinearEquiv
    (f : H → EReal) (e : H ≃L[ℝ] H) :
    (f ∘ e)∗ = f∗ ∘ (e.symm : H →L[ℝ] H).adjoint := sorry

end

-- Proof sketch: substitute `x = -z` in the defining supremum and use
-- `⟪-z, u⟫ = ⟪z, -u⟫` to rewrite the affine defects.
/-- Proposition 13.23 (5): clause (v). Reflecting `f` through the origin commutes with Fenchel
conjugation. -/
theorem conjugate_precompose_neg
    (f : H → EReal) :
    (fᵛ)∗ = (f∗)ᵛ := sorry

section

variable [CompleteSpace H]

-- Proof sketch: because `dom f ⊆ V`, the defining supremum for `conjugate f u` may be restricted
-- to points of `V`; on `V`, the inner product with `u` only depends on the orthogonal projection of
-- `u` to `V`.
/-- Proposition 13.23 (6): clause (vi), first equality. If the effective domain of `f` lies in a
closed subspace `V`, then the conjugate of the restriction `f|_V` composed with the orthogonal
projection onto `V` recovers `f*`. -/
theorem conjugate_restrict_comp_orthogonalProjection_of_dom_subset
    (f : H → EReal) (V : ClosedSubmodule ℝ H) (hdom : dom f ⊆ (V : Set H)) :
    (fun x : (V : Submodule ℝ H) ↦ f x)∗ ∘ V.orthogonalProjection = f∗ := sorry

-- Proof sketch: once clause (vi), first equality identifies `conjugate f` with the restriction
-- conjugate evaluated on orthogonal projections, apply that identity to `V.starProjection u`.
/-- Proposition 13.23 (7): clause (vi), second equality. If the effective domain of `f` lies in a
closed subspace `V`, then `f*` is invariant under orthogonal projection onto `V`. -/
theorem conjugate_eq_conjugate_comp_starProjection_of_dom_subset
    (f : H → EReal) (V : ClosedSubmodule ℝ H) (hdom : dom f ⊆ (V : Set H)) :
    f∗ = f∗ ∘ V.starProjection := by
  ext u
  have hrestrict :
      ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection u) = f∗ u := by
    simpa [Function.comp] using
      congrFun (conjugate_restrict_comp_orthogonalProjection_of_dom_subset f V hdom) u
  have hrestrict_proj :
      ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection (V.starProjection u)) =
        f∗ (V.starProjection u) := by
    simpa [Function.comp] using
      congrFun (conjugate_restrict_comp_orthogonalProjection_of_dom_subset f V hdom)
        (V.starProjection u)
  have hproj : V.orthogonalProjection (V.starProjection u) = V.orthogonalProjection u := by
    simpa using
      (Submodule.orthogonalProjection_mem_subspace_eq_self (V.orthogonalProjection u))
  calc
    f∗ u = ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection u) :=
      hrestrict.symm
    _ = ((fun x : (V : Submodule ℝ H) ↦ f x)∗) (V.orthogonalProjection (V.starProjection u)) := by
      rw [hproj]
    _ = f∗ (V.starProjection u) := hrestrict_proj

end

end Conjugation

end ERealFunction
