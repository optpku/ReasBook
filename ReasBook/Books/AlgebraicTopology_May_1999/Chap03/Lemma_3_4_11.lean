/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_2
import AlgebraicTopology_May_1999.Chap03.Definition_3_4_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Lemma 3.4.11: a morphism upstairs carries the canonical point in one fiber to the
canonical point in the next fiber under the corresponding fiber translation downstairs. -/
lemma fiberTranslationMap_map_eq_of_hom (hp : Functor.IsCovering p) {x y : E} (g : x ⟶ y) :
    fiberTranslationMap hp (p.map g) (⟨x, rfl⟩ : p.Fiber (p.obj x)) = ⟨y, rfl⟩ := by
  apply Subtype.ext
  -- Compare the chosen lift of `p.map g` with the actual arrow `g`.
  have hstar : starLift hp (p.map g) ⟨x, rfl⟩ = Under.mk g := by
    apply (hp.star_bijective x).injective
    calc
      (Under.post p).obj (starLift hp (p.map g) ⟨x, rfl⟩) = Under.mk (p.map g) := by
        simpa using starLift_post_eq hp (p.map g) ⟨x, rfl⟩
      _ = (Under.post p).obj (Under.mk g) := by
        simp [Under.post]
  -- Equality of lifted under-objects identifies their endpoints.
  change (starLift hp (p.map g) ⟨x, rfl⟩).right = y
  simpa using congrArg Comma.right hstar

/-- Helper for Lemma 3.4.11: fiber translation along an `eqToHom` changes only the witness that
the chosen point lies in the relevant fiber. -/
lemma fiberTranslationMap_eqToHom_basepoint (hp : Functor.IsCovering p) {x : E} {b : B}
    (h : p.obj x = b) :
    fiberTranslationMap hp (eqToHom h) (⟨x, rfl⟩ : p.Fiber (p.obj x)) = ⟨x, h⟩ := by
  -- After reducing to the reflexive case, fiber translation along the identity is trivial.
  cases h
  exact congrArg (fun f ↦ f (⟨x, rfl⟩ : p.Fiber (p.obj x))) (fiberTranslationMap_id hp (p.obj x))

/-- Lemma 3.4.11 (1): if the total groupoid of a covering functor is connected, then the vertex
group at each base object acts transitively on the corresponding fiber by fiber translation. -/
-- Proof sketch: for points `x y` in the same fiber over `b`, connectedness of `E` gives a
-- morphism `g : x.1 ⟶ y.1`; its image under `p` is a loop at `b`, and lifting that loop from
-- `x` recovers `g`, so fiber translation sends `x` to `y`.
theorem fiberTranslationMulAction_isTransitive [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMulAction.IsTransitive hp b := by
  letI := fiberTranslationMulAction hp b
  change MulAction.IsTransitive (b ⟶ b) (p.Fiber b)
  rw [MulAction.isTransitive_iff_nonempty_pretransitive]
  obtain ⟨x, rfl⟩ := hp.obj_surjective b
  let x₀ : p.Fiber (p.obj x) := ⟨x, rfl⟩
  refine ⟨⟨x₀⟩, ?_⟩
  -- Use connectedness of `E` to reach every fiber point from the chosen basepoint upstairs.
  have hbase : ∀ y : p.Fiber (p.obj x), ∃ g : p.obj x ⟶ p.obj x, g • x₀ = y := by
    rintro ⟨y, hy⟩
    let g : x ⟶ y :=
      Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid x y)
    let γ : p.obj x ⟶ p.obj x := eqToHom hy.symm ≫ p.map (CategoryTheory.Groupoid.inv g)
    refine ⟨γ, ?_⟩
    have hg : fiberTranslationMap hp (p.map g) x₀ = (⟨y, rfl⟩ : p.Fiber (p.obj y)) := by
      simpa [x₀] using (fiberTranslationMap_map_eq_of_hom (hp := hp) g)
    have htransport :
        fiberTranslationMap hp (eqToHom hy) (⟨y, rfl⟩ : p.Fiber (p.obj y)) = ⟨y, hy⟩ := by
      exact fiberTranslationMap_eqToHom_basepoint (hp := hp) hy
    have hcomp : fiberTranslationMap hp (p.map g ≫ eqToHom hy) x₀ = ⟨y, hy⟩ := by
      -- First follow the lifted arrow `g`, then transport the endpoint into the target fiber.
      rw [fiberTranslationMap_comp]
      simpa [Function.comp, hg] using htransport
    have hγinv : γ⁻¹ = p.map g ≫ eqToHom hy := by
      simp [γ]
    -- The action uses inverse loops, so the witness is the inverse of the image of `g`.
    calc
      γ • x₀ = fiberTranslationMap hp γ⁻¹ x₀ := by
        simpa [fiberTranslationMulAction] using
          (Functor.vertexGroupAction_smul_eq_map_inv
            (T := fiberTranslationFunctor hp) (b := p.obj x) γ x₀)
      _ = fiberTranslationMap hp (p.map g ≫ eqToHom hy) x₀ := by
        rw [hγinv]
      _ = ⟨y, hy⟩ := hcomp
  exact (MulAction.isPretransitive_iff_base x₀).2 hbase

/-- The transitive fiber-translation action is in particular pretransitive. -/
theorem fiberTranslationMulAction_isPretransitive [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMulAction.IsPretransitive hp b := by
  letI := fiberTranslationMulAction hp b
  change MulAction.IsPretransitive (b ⟶ b) (p.Fiber b)
  exact (fiberTranslationMulAction_isTransitive hp b).2

/-- Helper for Lemma 3.4.11: if a loop fixes the distinguished base fiber point, then it comes
from a loop in the vertex group upstairs. -/
private theorem mapVertexGroup_mem_of_fiberTranslation_inv_basepoint_fixed
    (hp : Functor.IsCovering p) (e : E) {γ : p.obj e ⟶ p.obj e}
    (hγ : fiberTranslationMap hp γ⁻¹ (⟨e, rfl⟩ : p.Fiber (p.obj e)) = ⟨e, rfl⟩) :
    γ ∈ (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let u := starLift hp γ⁻¹ x₀
  -- The fixed-point hypothesis forces the lifted arrow of `γ⁻¹` to end back at `e`.
  have hright : u.right = e := by
    exact congrArg Subtype.val hγ
  have hobj : starLift_obj hp γ⁻¹ x₀ = congrArg p.obj hright := by
    apply Subsingleton.elim
  have hloop : p.map (u.hom ≫ eqToHom hright) = γ⁻¹ := by
    -- Normalize the lift, then cancel the endpoint transport coming from `hright`.
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
    refine ⟨u.hom ≫ eqToHom hright, hloop⟩
  simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hmem_inv

/-- Lemma 3.4.11 (2): the stabilizer of the distinguished point `⟨e, rfl⟩` for the fiber
translation action is the image of the vertex group at `e` under the covering functor. -/
-- Proof sketch: a loop `γ` at `p.obj e` fixes `⟨e, rfl⟩` exactly when its chosen lift starting at
-- `e` ends again at `e`; this is equivalent to `γ` lying in the range of `Functor.mapVertexGroup
-- p e`.
theorem fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range
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
    -- A stabilizing loop is exactly a loop whose chosen lift closes up at `e`.
    exact mapVertexGroup_mem_of_fiberTranslation_inv_basepoint_fixed hp e hγ
  · rintro ⟨δ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change fiberTranslationMap hp (p.map δ)⁻¹ x₀ = x₀
    -- The inverse loop `δ⁻¹` upstairs lifts the base loop and returns to the basepoint.
    simpa [x₀] using
      (fiberTranslationMap_map_eq_of_hom (hp := hp) (x := e) (y := e) δ⁻¹)

end CategoryTheory.Functor.IsCovering
