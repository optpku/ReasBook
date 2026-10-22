/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_11
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_2
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Lemma 3.3.12: the isotropy subgroup of the distinguished fiber point `⟨e, rfl⟩`
under fiber translation is exactly the image of the vertex group at `e`. -/
private theorem basepoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction hp (p.obj e)
    MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ =
      (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ext γ
  constructor
  · intro hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hγ
    let u := starLift hp γ⁻¹ x₀
    -- The chosen lift of `γ⁻¹` ends again at `e`, so it closes up to a loop at `e`.
    have hright : u.right = e := by
      exact congrArg Subtype.val hγ
    have hobj : starLift_obj hp γ⁻¹ x₀ = congrArg p.obj hright := by
      apply Subsingleton.elim
    have hloop : p.map (u.hom ≫ eqToHom hright) = γ⁻¹ := by
      -- Normalize the image of the chosen lift and cancel the endpoint transport.
      have hmap : p.map u.hom = γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm := by
        simpa [u, x₀, hobj] using starLift_hom_over hp γ⁻¹ x₀
      have hmapEqToHom : p.map (eqToHom hright) = eqToHom (congrArg p.obj hright) := by
        simpa using eqToHom_map p hright
      have hcancel :
          eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright) = 𝟙 (p.obj e) := by
        rw [hmapEqToHom]
        simp
      calc
        p.map (u.hom ≫ eqToHom hright) = p.map u.hom ≫ p.map (eqToHom hright) := by
          simp
        _ = (γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm) ≫ p.map (eqToHom hright) := by
          exact congrArg (fun k ↦ k ≫ p.map (eqToHom hright)) hmap
        _ = γ⁻¹ ≫ (eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright)) := by
          simp [Category.assoc]
        _ = γ⁻¹ := by
          rw [hcancel]
          simp
    have hmem_inv : γ⁻¹ ∈ (Functor.mapVertexGroup p e).range := by
      refine ⟨u.hom ≫ eqToHom hright, ?_⟩
      exact hloop
    simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hmem_inv
  · rintro ⟨δ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    -- Compare the chosen lift of `p.map δ⁻¹` with the actual inverse loop `δ⁻¹`.
    have hstar : starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀ = Under.mk δ⁻¹ := by
      apply (hp.star_bijective e).injective
      calc
        (Under.post p).obj (starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀) =
            Under.mk (((Functor.mapVertexGroup p e) δ)⁻¹) := by
          simpa [x₀] using starLift_post_eq hp (((Functor.mapVertexGroup p e) δ)⁻¹) x₀
        _ = (Under.post p).obj (Under.mk δ⁻¹) := by
          simp [Under.post]
    apply Subtype.ext
    -- Equality of the lifted under-objects identifies their endpoints.
    change (starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀).right = e
    simpa [x₀] using congrArg Comma.right hstar

/-- Helper for Lemma 3.3.12: universality is equivalent to triviality of the stabilizer of the
distinguished fiber point. -/
private theorem isUniversalCovering_iff_basepoint_stabilizer_eq_bot
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction hp (p.obj e)
    Functor.IsUniversalCovering p e ↔
      MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · rintro ⟨_, hbot⟩
    -- Rewrite the vertex-group image subgroup as the basepoint stabilizer.
    simpa [basepoint_stabilizer_eq_mapVertexGroup_range hp e] using hbot
  · intro hbot
    -- The covering hypothesis is already fixed, so only the subgroup equality remains.
    exact ⟨hp, by simpa [basepoint_stabilizer_eq_mapVertexGroup_range hp e] using hbot⟩

/-- Helper for Lemma 3.3.12: in a pretransitive action, freeness is equivalent to triviality of
the stabilizer of one chosen point. -/
private theorem isCancelSMul_iff_stabilizer_eq_bot_of_isPretransitive
    {G : Type u₁} {S : Type u₂} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) : IsCancelSMul G S ↔ MulAction.stabilizer G s = ⊥ := by
  constructor
  · intro hfree
    letI : IsCancelSMul G S := hfree
    -- A free action has trivial stabilizer at every point, in particular at `s`.
    exact IsCancelSMul.stabilizer_eq_bot s
  · intro hs
    -- Pretransitivity makes every stabilizer a conjugate of the chosen one.
    rw [isCancelSMul_iff_stabilizer_eq_bot]
    intro t
    rcases (MulAction.isPretransitive_iff_base s).mp ‹MulAction.IsPretransitive G S› t with
      ⟨g, rfl⟩
    simpa [hs] using MulAction.stabilizer_smul_eq_stabilizer_map_conj g s

/-- Lemma 3.3.12: if the fiber-translation action on the fiber over `p.obj e` is pretransitive,
then a covering functor is universal at `e` exactly when that action is free. -/
-- Proof sketch: identify universality with triviality of the image subgroup
-- `Functor.mapVertexGroup p e`. By the basepoint-stabilizer computation from Lemma 3.4.11, this
-- is the triviality of the stabilizer of `⟨e, rfl⟩`. Under pretransitivity every fiber point is a
-- translate of `⟨e, rfl⟩`, so all stabilizers are conjugate to the basepoint stabilizer, hence all
-- are trivial exactly when the action is free.
theorem isUniversalCovering_iff_fiberTranslation_isFree_of_isPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (hpre : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    Functor.IsUniversalCovering p e ↔ fiberTranslationMulAction.IsFree hp (p.obj e) := by
  letI := fiberTranslationMulAction hp (p.obj e)
  change Functor.IsUniversalCovering p e ↔ IsCancelSMul (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  -- First rewrite universality as triviality of the isotropy subgroup at the base fiber point.
  have hbase :
      Functor.IsUniversalCovering p e ↔
        MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ :=
    isUniversalCovering_iff_basepoint_stabilizer_eq_bot hp e
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := hpre
  -- Then pretransitivity upgrades triviality of one stabilizer to freeness of the action.
  have hfree :
      IsCancelSMul (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ↔
        MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ :=
    isCancelSMul_iff_stabilizer_eq_bot_of_isPretransitive x₀
  exact hbase.trans hfree.symm

end CategoryTheory.Functor.IsCovering
