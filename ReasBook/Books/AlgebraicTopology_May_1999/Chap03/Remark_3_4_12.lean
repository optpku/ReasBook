/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_11
import AlgebraicTopology_May_1999.Chap03.Lemma_3_3_12
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The regularity condition is equivalent to normality of the stabilizer of the distinguished
point in the fiber action. -/
-- Proof sketch: rewrite the stabilizer at `⟨e, rfl⟩` as the image of
-- `Functor.mapVertexGroup p e` using
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range`, then unfold
-- `Functor.IsRegularCovering`.
theorem isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal
    (hp : Functor.IsCovering p) (e : E) :
    by
      letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
        fiberTranslationMulAction hp (p.obj e)
      let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
      exact Functor.IsRegularCovering p e ↔
        (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀).Normal := by
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  constructor
  · intro hreg
    rw [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    exact hreg.2
  · intro hnormal
    exact ⟨hp, by
      rw [← fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
      exact hnormal⟩

/-- Helper for Remark 3.4.12: on a connected total groupoid, universality at `e` is equivalent
to freeness of the fiber-translation action over `p.obj e`. -/
private theorem isUniversalCovering_iff_fiberTranslation_isFree [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔ fiberTranslationMulAction.IsFree hp (p.obj e) := by
  have htrans : fiberTranslationMulAction.IsTransitive hp (p.obj e) :=
    fiberTranslationMulAction_isTransitive hp (p.obj e)
  -- Connectedness supplies the pretransitivity required by Lemma 3.3.12.
  exact isUniversalCovering_iff_fiberTranslation_isFree_of_isPretransitive hp e htrans.2

/-- For a connected total groupoid, universality is equivalent to the fiber translation action
being free and transitive. -/
-- Proof sketch:
-- connectedness supplies transitivity of the whole fiber action, and Lemma 3.3.12 upgrades
-- universality to freeness of the canonical fiber-translation action; pairing these gives the
-- free-transitive description.
theorem isUniversalCovering_iff_fiberTranslation_free_transitive [IsConnected E]
    (hp : Functor.IsCovering p) (e : E) :
    Functor.IsUniversalCovering p e ↔
      fiberTranslationMulAction.IsFree hp (p.obj e) ∧
        fiberTranslationMulAction.IsTransitive hp (p.obj e) := by
  have htrans : fiberTranslationMulAction.IsTransitive hp (p.obj e) :=
    fiberTranslationMulAction_isTransitive hp (p.obj e)
  -- First collapse universality to the freeness criterion specialized to the connected case.
  rw [isUniversalCovering_iff_fiberTranslation_isFree hp e]
  constructor
  · intro hfree
    -- The transitivity witness is global, so freeness is the only remaining datum.
    exact ⟨hfree, htrans⟩
  · rintro ⟨hfree, htrans⟩
    -- The backward direction only needs the freeness component; transitivity is automatic here.
    exact hfree

/-- Remark 3.4.12: regular coverings correspond to normal isotropy subgroups, while on a
connected total groupoid universal coverings correspond to free transitive fiber actions. -/
-- Proof sketch: combine the stabilizer description from Lemma 3.4.11 with the definitions of
-- regular and universal covering, and use connectedness to supply transitivity of the fiber
-- translation action in the universal case.
theorem regular_and_universal_covering_characterizations
    (hp : Functor.IsCovering p) (e : E) [IsConnected E] :
    (Functor.IsRegularCovering p e ↔
        letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
          fiberTranslationMulAction hp (p.obj e)
        let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
        (MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀).Normal) ∧
      (Functor.IsUniversalCovering p e ↔
        fiberTranslationMulAction.IsFree hp (p.obj e) ∧
          fiberTranslationMulAction.IsTransitive hp (p.obj e)) := by
  constructor
  · -- Regularity is exactly normality of the basepoint stabilizer.
    exact isRegularCovering_iff_fiberTranslation_basepoint_stabilizer_normal hp e
  · -- In the connected case, universality is freeness together with transitivity.
    exact isUniversalCovering_iff_fiberTranslation_free_transitive hp e

end CategoryTheory.Functor.IsCovering
