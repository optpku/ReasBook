/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_6
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_8
import AlgebraicTopology_May_1999.Chap03.Lemma_3_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]
variable [IsConnected B]

section

variable (b : B) {H K : O(End b)} (α : H ⟶ K)

/- Construction 3.6.5: a morphism `α : H ⟶ K` in the orbit category induces the canonical
morphism `((orbitCategoryToConnectedCovering b).map α)` between the associated connected
coverings over `B`; its commutative-triangle relation over `B` is the field
`((orbitCategoryToConnectedCovering b).map α).hom.comm`. -/
#check ((orbitCategoryToConnectedCovering b).map α)

end

/-- If `α (eH) = γK`, then the canonical covering morphism induced by `α : H ⟶ K` sends the
source-facing object `fH` of `E(G/H)` to the source-facing object `(γ ≫ f)K` of `E(G/K)`. -/
-- Proof sketch: on category-of-elements representatives the induced functor fixes the arrow `f`
-- and applies `α` to the quotient coordinate, so `fH` goes to the class of `(f, γK)`. That class
-- is exactly the source-facing object `(γ ≫ f)K`, since the diagonal `π(B,b)`-action identifies
-- `(γ ≫ f, K)` with `(f, γK)`.
theorem orbitCategoryToConnectedCovering_map_objOfHom_of_apply_one (b : B)
    {H K : O(End b)} (α : H ⟶ K)
    {γ : End b}
    (hα : (Subgroup.orbitCategoryHomEvalOne H K α : End b ⧸ K) = (γ : End b ⧸ K))
    {x : B} (f : b ⟶ x) :
    (((orbitCategoryToConnectedCovering b).map α).hom.left).obj
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) f) =
        orbitSubgroupCoveringObjOfHom b (K : Subgroup (End b)) (γ ≫ f) := by
  change
    (⟨x, Quotient.mk'' (f, α.toFun ((1 : End b) : End b ⧸ H))⟩ :
      (associatedAction b (End b ⧸ K)).Elements) =
      ⟨x, Quotient.mk'' (γ ≫ f, ((1 : End b) : End b ⧸ K))⟩
  rw [show α.toFun ((1 : End b) : End b ⧸ H) = (γ : End b ⧸ K) by simpa using hα]
  congr 1
  apply Quotient.sound
  change
    MulAction.orbitRel (End b) ((b ⟶ x) × (End b ⧸ K))
      (f, (γ : End b ⧸ K)) (γ ≫ f, ((1 : End b) : End b ⧸ K))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
  refine ⟨γ⁻¹, ?_⟩
  change ((γ⁻¹ : End b) • f, (γ⁻¹ : End b) • (γ : End b ⧸ K)) =
      (γ ≫ f, ((1 : End b) : End b ⧸ K))
  ext
  · change (γ⁻¹ : End b) • f = γ ≫ f
    rw [orbitCoveringHomMulAction_smul]
    exact congrArg (fun η : End b ↦ η ≫ f) (inv_inv γ)
  · change (((γ⁻¹ : End b) * γ : End b) : End b ⧸ K) = ((1 : End b) : End b ⧸ K)
    simp
