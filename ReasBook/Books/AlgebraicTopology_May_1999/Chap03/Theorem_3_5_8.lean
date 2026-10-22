/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Lemma_3_4_11
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- A morphism of coverings over `B` sends the fiber of `p` over `b` into the fiber of `p'`
over `b`. -/
-- Proof sketch: evaluate the commutative triangle relation `Over.w h` at the chosen point of the
-- fiber and rewrite the result using the defining equality of that fiber point.
theorem mapOfCoverings_obj_mem_fiber {b : B}
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) (e : p.Fiber b) :
    let g : E ⥤ E' := h.left.toFunctor
    p'.obj (g.obj e.1) = b := by
  let g : E ⥤ E' := h.left.toFunctor
  have hgOver : g ⋙ p' = p := by
    -- Unpack the over-category commutativity relation into an equality of functors.
    simpa [g] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
  have hObj : p'.obj (g.obj e.1) = p.obj e.1 := by
    -- Evaluating that functor equality at `e.1` identifies the two base objects.
    simpa [g] using congrArg (fun F : E ⥤ B ↦ F.obj e.1) hgOver
  exact hObj.trans e.2

/-- Restriction of a map of coverings over `B` to the fiber over `b`. -/
def mapOfCoveringsToFiberFun (b : B)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) :
    p.Fiber b → p'.Fiber b :=
  let g : E ⥤ E' := h.left.toFunctor
  fun e ↦ ⟨g.obj e.1, mapOfCoverings_obj_mem_fiber h e⟩

/-- Restriction of a map of coverings to the fiber over `b` commutes with fiber translation by
loops at `b`. -/
-- Proof sketch: a map of coverings sends the chosen lift of a loop starting at `e` to the chosen
-- lift of the same loop starting at the image point, because both arrows project to the same base
-- loop and have the same source. Comparing endpoints gives the equivariance identity.
theorem mapOfCoveringsToFiberFun_comm
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B)
    (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) (γ : b ⟶ b)
    (e : p.Fiber b) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    mapOfCoveringsToFiberFun b h (γ • e) = γ • mapOfCoveringsToFiberFun b h e := by
  rcases e with ⟨e, rfl⟩
  let g : E ⥤ E' := h.left.toFunctor
  have hgOver : g ⋙ p' = p := by
    -- Convert the over-category triangle into an equality of total-space functors.
    simpa [g] using congrArg (fun F ↦ F.toFunctor) (Over.w h)
  have hbase : p'.obj (g.obj e) = p.obj e := by
    -- The image of the chosen source point still lies over the same base object.
    simpa [g] using congrArg (fun F : E ⥤ B ↦ F.obj e) hgOver
  let x : p'.Fiber (p.obj e) := ⟨g.obj e, hbase⟩
  have hx : mapOfCoveringsToFiberFun (p.obj e) h ⟨e, rfl⟩ = x := by
    -- The restricted map is the obvious image point in the target fiber.
    apply Subtype.ext
    rfl
  -- Rewrite both actions in terms of fiber translation along `γ⁻¹`.
  change mapOfCoveringsToFiberFun (p.obj e) h (fiberTranslationMap hp γ⁻¹ ⟨e, rfl⟩) =
    fiberTranslationMap hp' γ⁻¹ (mapOfCoveringsToFiberFun (p.obj e) h ⟨e, rfl⟩)
  rw [hx]
  apply Subtype.ext
  let u : Under e := starLift hp γ⁻¹ ⟨e, rfl⟩
  let v : Under (g.obj e) := starLift hp' γ⁻¹ x
  have hright : p'.obj (g.obj u.right) = p.obj u.right := by
    -- The commuting triangle also identifies the basepoint of the lifted endpoint.
    simpa [g, u] using congrArg (fun F : E ⥤ B ↦ F.obj u.right) hgOver
  have hu : p.map u.hom = γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm := by
    -- Normalize the chosen lift of `γ⁻¹` in the source covering.
    simpa [u] using starLift_hom_over hp γ⁻¹ ⟨e, rfl⟩
  have hmor : (g ⋙ p').map u.hom = eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm := by
    -- Mapping the chosen lift through `g` changes only the source and target transports.
    simpa [u] using CategoryTheory.Functor.congr_hom hgOver u.hom
  have hpostv : (Under.post p').obj v = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
    -- The target chosen lift is characterized by the transported loop `γ⁻¹`.
    rw [show (Under.post p').obj v = x.2.symm ▸ (Under.mk γ⁻¹ : Under (p.obj e)) by
      simpa [v, x] using starLift_post_eq hp' γ⁻¹ x]
    simpa [x] using fiber_transport_under_mk (p := p') γ⁻¹ x
  have hpostu : (Under.post p').obj ((Under.post g).obj u) = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
    -- The image under `g` of the source chosen lift projects to the same transported loop.
    change Under.mk (p'.map (g.map u.hom)) = Under.mk (eqToHom hbase ≫ γ⁻¹)
    rw [show p'.map (g.map u.hom) = (g ⋙ p').map u.hom by rfl]
    rw [hmor]
    have hmiddle :
        eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm =
          eqToHom hbase ≫
            (γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm) ≫
            eqToHom hright.symm := by
      exact congrArg (fun k ↦ eqToHom hbase ≫ k ≫ eqToHom hright.symm) hu
    calc
      Under.mk (eqToHom hbase ≫ p.map u.hom ≫ eqToHom hright.symm) =
          Under.mk
            (eqToHom hbase ≫
              (γ⁻¹ ≫ eqToHom (starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm) ≫
              eqToHom hright.symm) := by
            exact congrArg Under.mk hmiddle
      _ = Under.mk
            (eqToHom hbase ≫ γ⁻¹ ≫
              eqToHom ((starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm.trans hright.symm)) := by
            simp [Category.assoc, eqToHom_trans]
      _ = Under.mk (eqToHom hbase ≫ γ⁻¹) := by
            simpa [Category.assoc] using
              under_mk_comp_eqToHom
                (eqToHom hbase ≫ γ⁻¹)
                ((starLift_obj hp γ⁻¹ ⟨e, rfl⟩).symm.trans hright.symm)
  have hstar : v = (Under.post g).obj u := by
    -- Uniqueness of lifts in the target covering identifies the two candidate lifts of `γ⁻¹`.
    apply (hp'.star_bijective (g.obj e)).injective
    exact hpostv.trans hpostu.symm
  change g.obj u.right = v.right
  -- Reading off endpoints gives the desired equality on fibers.
  simpa [mapOfCoveringsToFiberFun, u, v, x] using congrArg Comma.right hstar.symm

/-- Restriction to the fiber over `b` as a bundled equivariant map. -/
def mapOfCoveringsToFiber (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p')
    (b : B) (h : Over.mk p.toCatHom ⟶ Over.mk p'.toCatHom) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    p.Fiber b →[(b ⟶ b)] p'.Fiber b :=
  letI := fiberTranslationMulAction hp b
  letI := fiberTranslationMulAction hp' b
  { toFun := mapOfCoveringsToFiberFun b h
    map_smul' := mapOfCoveringsToFiberFun_comm hp hp' b h }

/-- Helper for Theorem 3.5.8: the subgroup attached to a fiber point is its stabilizer under the
fiber-translation action. -/
lemma fiberPoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) {b : B} (e : p.Fiber b) :
    letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
    MulAction.stabilizer (b ⟶ b) e = e.2 ▸ (Functor.mapVertexGroup p e.1).range := by
  rcases e with ⟨e, rfl⟩
  -- Reduce to the distinguished basepoint case computed in Lemma 3.4.11.
  simpa [fiberTranslationMulAction] using
    (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e)

/-- Helper for Theorem 3.5.8: an equivariant map sends stabilizers into stabilizers. -/
lemma stabilizer_le_of_equivariant
    {G : Type v} {X Y : Type u} [Group G] [MulAction G X] [MulAction G Y]
    (φ : X →[G] Y) (x : X) :
    MulAction.stabilizer G x ≤ MulAction.stabilizer G (φ x) := by
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  -- Push the fixed-point relation forward using equivariance of `φ`.
  calc
    g • φ x = φ (g • x) := by
      simpa using (φ.map_smul' g x).symm
    _ = φ x := by rw [hg]

/-- Theorem 3.5.8: if `E` is connected, restriction to the fiber over `b` gives a bijection
between maps of coverings `E ⥤ E'` over `B` and `(b ⟶ b)`-equivariant maps
`p.Fiber b → p'.Fiber b`, where `b ⟶ b = π(B,b)`. -/
-- Proof sketch: a map of coverings commutes with fiber translation, so restriction gives an
-- equivariant map on the fiber. For surjectivity, connectedness of `E` makes the
-- `(b ⟶ b)`-action on `p.Fiber b` pretransitive. An equivariant fiber map sends the isotropy
-- subgroup of any chosen `e : p.Fiber b` into the isotropy subgroup of its image, so
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range` and
-- `existsUnique_map_iff_mapVertexGroup_range_le` produce a unique map of coverings with the
-- prescribed value at `e`; pretransitivity then upgrades agreement at `e` to agreement on the
-- whole fiber.
theorem mapOfCoveringsToFiber_bijective [CategoryTheory.IsConnected E]
    (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p') (b : B) :
    letI := fiberTranslationMulAction hp b
    letI := fiberTranslationMulAction hp' b
    Function.Bijective (mapOfCoveringsToFiber hp hp' b) := by
  letI := fiberTranslationMulAction hp b
  letI := fiberTranslationMulAction hp' b
  constructor
  · intro h₁ h₂ hEq
    obtain ⟨e, rfl⟩ := hp.obj_surjective b
    let x : p.Fiber (p.obj e) := ⟨e, rfl⟩
    let x' : p'.Fiber (p.obj e) := mapOfCoveringsToFiber hp hp' (p.obj e) h₁ x
    have hxEq : mapOfCoveringsToFiber hp hp' (p.obj e) h₂ x = x' := by
      -- Equality of restricted equivariant maps gives equality on the chosen fiber point.
      simpa [x'] using congrArg (fun ψ ↦ ψ x) hEq.symm
    let g₁ : E ⥤ E' := h₁.left.toFunctor
    have hg₁ : g₁ ⋙ p' = p := by
      -- Reinterpret the first covering morphism as a lift of `p` through `p'`.
      simpa [g₁] using congrArg (fun F ↦ F.toFunctor) (Over.w h₁)
    have hh₁ : g₁.obj x.1 = x'.1 := by
      -- By definition, `x'` is the image of `x` under the restricted fiber map.
      rfl
    have hle : (Functor.mapVertexGroup p x.1).range ≤
        x'.2 ▸ (Functor.mapVertexGroup p' x'.1).range := by
      -- The first covering morphism supplies the subgroup inclusion from Theorem 3.5.6.
      simpa using Functor.mapVertexGroup_range_le_of_lift x.1 x' hg₁ hh₁
    obtain ⟨_, _, huniq⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p') hp' (p.obj e) x x').2 hle
    have hh₂ : let g₂ : E ⥤ E' := h₂.left.toFunctor; g₂.obj x.1 = x'.1 := by
      -- The second covering morphism sends `x` to the same target point because the restrictions
      -- agree on `x`.
      simpa [x', mapOfCoveringsToFiber, mapOfCoveringsToFiberFun] using congrArg Subtype.val hxEq
    exact (huniq h₁ (by simpa [g₁] using hh₁)).trans (huniq h₂ hh₂).symm
  · intro φ
    obtain ⟨e, rfl⟩ := hp.obj_surjective b
    let x : p.Fiber (p.obj e) := ⟨e, rfl⟩
    let x' : p'.Fiber (p.obj e) := φ x
    have hsub : (Functor.mapVertexGroup p x.1).range ≤
        x'.2 ▸ (Functor.mapVertexGroup p' x'.1).range := by
      have hstab : MulAction.stabilizer (p.obj e ⟶ p.obj e) x ≤
          MulAction.stabilizer (p.obj e ⟶ p.obj e) x' := by
        simpa [x'] using (stabilizer_le_of_equivariant φ x)
      -- Translate the isotropy inclusion into the subgroup inclusion required by Theorem 3.5.6.
      simpa [x', fiberPoint_stabilizer_eq_mapVertexGroup_range hp x,
        fiberPoint_stabilizer_eq_mapVertexGroup_range hp' x'] using hstab
    obtain ⟨hcov, hhcov, _⟩ :=
      (existsUnique_map_iff_mapVertexGroup_range_le
        (p := p) (p' := p') hp' (p.obj e) x x').2 hsub
    refine ⟨hcov, ?_⟩
    apply MulActionHom.ext
    intro y
    have hhx : mapOfCoveringsToFiber hp hp' (p.obj e) hcov x = x' := by
      -- The reconstructed covering morphism has the prescribed value on the chosen base fiber
      -- point.
      apply Subtype.ext
      simpa [mapOfCoveringsToFiber, mapOfCoveringsToFiberFun] using hhcov
    letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction_isTransitive hp (p.obj e) |>.2
    have hy : y ∈ MulAction.orbit (p.obj e ⟶ p.obj e) x := by
      -- Connectedness makes every fiber point a translate of the chosen basepoint `x`.
      simpa [MulAction.orbit_eq_univ (p.obj e ⟶ p.obj e) x]
    rcases hy with ⟨γ, rfl⟩
    calc
      mapOfCoveringsToFiber hp hp' (p.obj e) hcov (γ • x) =
          γ • mapOfCoveringsToFiber hp hp' (p.obj e) hcov x := by
        -- The restricted map of coverings is equivariant for the fiber action.
        simpa using (mapOfCoveringsToFiber hp hp' (p.obj e) hcov).map_smul' γ x
      _ = γ • x' := by rw [hhx]
      _ = γ • φ x := by rfl
      _ = φ (γ • x) := by
        -- Equivariance of `φ` propagates equality from the chosen basepoint to all of the fiber.
        symm
        exact φ.map_smul' γ x

end CategoryTheory.Functor.IsCovering
