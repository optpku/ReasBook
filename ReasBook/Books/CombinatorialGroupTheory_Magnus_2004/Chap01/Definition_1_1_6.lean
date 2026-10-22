/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {G : Type u} [Group G]

open CategoryTheory

namespace MonoidHom

/-- A retraction is equivalently a surjective homomorphism onto `S` whose induced endomorphism of
`G` is idempotent. -/
-- Proof sketch: one direction uses the restriction-identity equation to get surjectivity and then
-- rewrites the square of `S.subtype.comp ρ`; the converse uses surjectivity onto `S` to test the
-- restriction identity on arbitrary elements of `S`.
theorem leftInverse_subtype_iff_surjective_and_idempotent {S : Subgroup G} (ρ : G →* S) :
    Function.LeftInverse ρ S.subtype ↔
      Function.Surjective ρ ∧
        (S.subtype.comp ρ).comp (S.subtype.comp ρ) = S.subtype.comp ρ := sorry

end MonoidHom

namespace Subgroup

/-- Definition 1-1-6: a subgroup is a retract of `G` exactly when its inclusion is split. -/
theorem subtype_isSplitMono_iff_exists_leftInverse (S : Subgroup G) :
    IsSplitMono (GrpCat.ofHom S.subtype) ↔ ∃ ρ : G →* S, Function.LeftInverse ρ S.subtype := by
  constructor
  · intro hS
    let _ : IsSplitMono (GrpCat.ofHom S.subtype) := hS
    refine ⟨(retraction (GrpCat.ofHom S.subtype)).hom, ?_⟩
    intro x
    exact
      DFunLike.congr_fun
        (congrArg GrpCat.Hom.hom (IsSplitMono.id (GrpCat.ofHom S.subtype))) x
  · rintro ⟨ρ, hρ⟩
    refine IsSplitMono.mk' ⟨GrpCat.ofHom ρ, ?_⟩
    ext x
    exact congrArg Subtype.val (hρ x)

/-- The whole group is a retract of itself. -/
theorem top_subtype_isSplitMono :
    IsSplitMono (GrpCat.ofHom ((⊤ : Subgroup G).subtype)) := by
  rw [subtype_isSplitMono_iff_exists_leftInverse]
  exact ⟨((Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).symm.toMonoidHom),
    (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).left_inv⟩

end Subgroup
