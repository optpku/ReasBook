/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_6
import AlgebraicTopology_May_1999.Chap03.Definition_3_8_7
import AlgebraicTopology_May_1999.Chap03.Proposition_3_3_6
import AlgebraicTopology_May_1999.Chap03.Corollary_3_7_8
import AlgebraicTopology_May_1999.Chap03.Example_3_3_9
import AlgebraicTopology_May_1999.Chap03.Theorem_3_5_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open FundamentalGroupoid
open scoped FundamentalGroup
open scoped Pointwise

universe u

variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- The automorphism group of a covering space acts on its total space by evaluation. -/
instance coveringSpaceAutMulAction (p : C(E, B)) :
    MulAction (Aut (Over.mk (TopCat.ofHom p))) E where
  smul α x := α.hom.left.hom x
  -- The identity automorphism evaluates to the identity self-map of `E`.
  one_smul x := by
    rfl
  -- Multiplication in `Aut` is composition, so evaluation is associative.
  mul_smul α β x := by
    rfl

/-- Every covering-space automorphism lies over the identity on the base, so evaluating it does
not change the image under the covering map. -/
-- Proof sketch: the defining commutative triangle of a morphism in the over-category says exactly
-- that `p ∘ α = p`.
private theorem coveringSpaceAut_smul_proj
    (p : C(E, B)) (α : Aut (Over.mk (TopCat.ofHom p))) (x : E) :
    p (α • x) = p x := by
  -- Evaluate the commutative triangle `p ∘ α = p` at the chosen point `x`.
  have hcomm := congrArg (fun f => TopCat.Hom.hom f x) (Over.w α.hom)
  simpa [ContinuousMap.comp_apply] using hcomm

/-- The covering map is constant on orbits of the covering-space automorphism action. -/
-- Proof sketch: two points in the same orbit differ by applying some covering automorphism, and
-- the previous lemma shows that `p` is invariant under that action.
private theorem coveringSpaceAut_proj_eq_of_orbitRel (p : C(E, B)) {x y : E}
    (hxy : MulAction.orbitRel (Aut (Over.mk (TopCat.ofHom p))) E x y) :
    p x = p y := by
  rcases hxy with ⟨α, hα⟩
  -- Orbit-related points differ by a deck transformation, and deck transformations preserve `p`.
  simpa [hα] using coveringSpaceAut_smul_proj p α y

/-- The canonical orbit projection `E / Aut(E) → B` induced by the covering map. -/
def coveringSpaceAutOrbitProjection (p : C(E, B)) :
    C(E /[Aut (Over.mk (TopCat.ofHom p))], B) :=
  ⟨fun x ↦ Quotient.liftOn' x p (fun _ _ hxy ↦ coveringSpaceAut_proj_eq_of_orbitRel p hxy),
    continuous_quot_lift
      (fun _ _ hxy ↦ coveringSpaceAut_proj_eq_of_orbitRel p hxy)
      p.continuous⟩

/-- The deck-transformation group acts on the fiber over `p e` by restricting evaluation to that
fiber. -/
@[reducible] noncomputable def coveringSpaceAutFiberMulAction
    (p : C(E, B)) (e : E) :
    MulAction (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e}) :=
  { smul := fun α x ↦
      ⟨α.hom.left.hom x.1, by
        have hproj : p (α.hom.left.hom x.1) = p x.1 := by
          simpa using coveringSpaceAut_smul_proj p α x.1
        simpa using hproj.trans x.2⟩
    -- The restricted action inherits the identity law from evaluation on `E`.
    one_smul := by
      intro x
      apply Subtype.ext
      rfl
    -- The restricted action inherits associativity from evaluation on `E`.
    mul_smul := by
      intro α β x
      apply Subtype.ext
      rfl }

variable {p : C(E, B)}

/-- Helper for Proposition 3.8.9: the subgroup attached to a categorical fiber point, obtained by
transporting the image of the corresponding vertex-group map to the chosen base vertex. -/
private def fiberPointSubgroup
    {E' B' : Type u} [Groupoid E'] [Groupoid B'] {q : E' ⥤ B'} {b : B'}
    (x : q.Fiber b) : Subgroup (b ⟶ b) :=
  x.2 ▸ (q.mapVertexGroup x.1).range

/-- Helper for Proposition 3.8.9: for any fiber point of a covering functor, the transported
vertex-group image subgroup is exactly the stabilizer of that point under fiber translation. -/
private theorem mapVertexGroup_range_eq_stabilizer
    {E' B' : Type u} [Groupoid E'] [Groupoid B'] {q : E' ⥤ B'}
    (hq : Functor.IsCovering q) {b : B'} (x : q.Fiber b) :
    by
      letI : MulAction (b ⟶ b) (q.Fiber b) := Functor.IsCovering.fiberTranslationMulAction hq b
      exact fiberPointSubgroup x = MulAction.stabilizer (b ⟶ b) x := by
  -- Reduce to the distinguished basepoint of the fiber, where Lemma 3.4.11 computes the
  -- stabilizer explicitly.
  rcases x with ⟨x, rfl⟩
  simpa [Functor.IsCovering.fiberTranslationMulAction] using
    (Functor.IsCovering.fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hq x).symm

/-- Helper for Proposition 3.8.9: an equivariant bijection preserves stabilizers. -/
private theorem stabilizer_eq_of_equivariant_bijective
    {G S : Type u} [Group G] [MulAction G S] (σ : S → S) (hσ : Function.Bijective σ)
    (hσ_eqv : ∀ (g : G) (x : S), σ (g • x) = g • σ x) (s : S) :
    MulAction.stabilizer G (σ s) = MulAction.stabilizer G s := by
  ext g
  constructor
  · intro hg
    -- Injectivity lets us pull the fixed-point condition back through `σ`.
    change g • s = s
    apply hσ.1
    calc
      σ (g • s) = g • σ s := hσ_eqv g s
      _ = σ s := hg
  · intro hg
    -- Equivariance pushes a fixed-point condition forward through `σ`.
    change g • σ s = σ s
    rw [← hσ_eqv g s, hg]

/-- Helper for Proposition 3.8.9: transporting the induced categorical fiber map of a deck
transformation across `fundamentalGroupoidMapFiberEquiv` recovers the ordinary deck action on the
fiber over `p e`. -/
private theorem coveringSpaceAut_fundamentalGroupoidFiberEquiv_smul
    (hp : IsPathConnectedCoveringMap p) (e : E) (α : Aut (Over.mk (TopCat.ofHom p)))
    (x : hp.fundamentalGroupoidMap.Fiber (mk (p e))) :
    letI := coveringSpaceAutFiberMulAction p e
    hp.fundamentalGroupoidMapFiberEquiv (p e)
        (Functor.IsCovering.mapOfCoveringsToFiberFun
          (mk (p e))
          (hp.toFundamentalGroupoidCoveringHom hp α.hom)
          x) =
      α • hp.fundamentalGroupoidMapFiberEquiv (p e) x := by
  -- Both constructions evaluate the same deck transformation on the underlying point of the
  -- chosen fiber.
  apply Subtype.ext
  rfl

/-- Helper for Proposition 3.8.9: moving the chosen fiber point by a deck transformation preserves
the transported categorical subgroup in the base vertex group. -/
private theorem coveringSpaceAut_fundamentalGroup_map_range_eq
    (hp : IsPathConnectedCoveringMap p) (e : E) (x : p ⁻¹' {p e})
    (α : Aut (Over.mk (TopCat.ofHom p)))
    (hα :
      by
        letI := coveringSpaceAutFiberMulAction p e
        exact α • (⟨e, rfl⟩ : p ⁻¹' {p e}) = x) :
    fiberPointSubgroup ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x) =
      fiberPointSubgroup ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm ⟨e, rfl⟩) := by
  -- Route correction: keep the subgroup comparison inside the categorical fiber over `mk (p e)`,
  -- where deck transformations act by an equivariant bijection.
  letI := Functor.IsCovering.fiberTranslationMulAction hp.fundamentalGroupoidMap_isCovering
    (mk (p e))
  letI := coveringSpaceAutFiberMulAction p e
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (mk (p e)) :=
    (hp.fundamentalGroupoidMapFiberEquiv (p e)).symm ⟨e, rfl⟩
  let σ : hp.fundamentalGroupoidMap.Fiber (mk (p e)) →
      hp.fundamentalGroupoidMap.Fiber (mk (p e)) :=
    Functor.IsCovering.mapOfCoveringsToFiberFun (mk (p e))
      (hp.toFundamentalGroupoidCoveringHom hp α.hom)
  have hσ : Function.Bijective σ := by
    refine ⟨?_, ?_⟩
    · intro y z hyz
      have hαyz :
          α • hp.fundamentalGroupoidMapFiberEquiv (p e) y =
            α • hp.fundamentalGroupoidMapFiberEquiv (p e) z := by
        calc
          α • hp.fundamentalGroupoidMapFiberEquiv (p e) y =
              hp.fundamentalGroupoidMapFiberEquiv (p e) (σ y) := by
                symm
                simpa [σ] using coveringSpaceAut_fundamentalGroupoidFiberEquiv_smul hp e α y
          _ = hp.fundamentalGroupoidMapFiberEquiv (p e) (σ z) := by
                rw [hyz]
          _ = α • hp.fundamentalGroupoidMapFiberEquiv (p e) z := by
                simpa [σ] using coveringSpaceAut_fundamentalGroupoidFiberEquiv_smul hp e α z
      have hyz' :
          hp.fundamentalGroupoidMapFiberEquiv (p e) y =
            hp.fundamentalGroupoidMapFiberEquiv (p e) z := by
        have hcancel := congrArg (fun t => α⁻¹ • t) hαyz
        simpa [mul_smul] using hcancel
      exact (hp.fundamentalGroupoidMapFiberEquiv (p e)).injective hyz'
    · intro y
      refine ⟨(hp.fundamentalGroupoidMapFiberEquiv (p e)).symm
        (α⁻¹ • hp.fundamentalGroupoidMapFiberEquiv (p e) y), ?_⟩
      apply (hp.fundamentalGroupoidMapFiberEquiv (p e)).injective
      calc
        hp.fundamentalGroupoidMapFiberEquiv (p e)
            (σ ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm
              (α⁻¹ • hp.fundamentalGroupoidMapFiberEquiv (p e) y))) =
              α • (α⁻¹ • hp.fundamentalGroupoidMapFiberEquiv (p e) y) := by
                simpa [σ] using coveringSpaceAut_fundamentalGroupoidFiberEquiv_smul hp e α
                  ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm
                    (α⁻¹ • hp.fundamentalGroupoidMapFiberEquiv (p e) y))
        _ = hp.fundamentalGroupoidMapFiberEquiv (p e) y := by
              simp
  have hσ_eqv :
      ∀ (g : mk (p e) ⟶ mk (p e)) (y : hp.fundamentalGroupoidMap.Fiber (mk (p e))),
        σ (g • y) = g • σ y := by
    intro g y
    simpa [σ] using
      (Functor.IsCovering.mapOfCoveringsToFiberFun_comm hp.fundamentalGroupoidMap_isCovering
        hp.fundamentalGroupoidMap_isCovering (mk (p e))
        (hp.toFundamentalGroupoidCoveringHom hp α.hom) g y)
  have hmap : σ ξ₀ = (hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x := by
    apply (hp.fundamentalGroupoidMapFiberEquiv (p e)).injective
    simpa [σ, ξ₀] using
      (coveringSpaceAut_fundamentalGroupoidFiberEquiv_smul hp e α ξ₀).trans hα
  calc
    fiberPointSubgroup ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x) =
        MulAction.stabilizer (mk (p e) ⟶ mk (p e))
          ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x) := by
          simpa using mapVertexGroup_range_eq_stabilizer hp.fundamentalGroupoidMap_isCovering
            ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm x)
    _ = MulAction.stabilizer (mk (p e) ⟶ mk (p e)) (σ ξ₀) := by
          rw [hmap]
    _ = MulAction.stabilizer (mk (p e) ⟶ mk (p e)) ξ₀ :=
          stabilizer_eq_of_equivariant_bijective σ hσ hσ_eqv ξ₀
    _ = fiberPointSubgroup ξ₀ := by
          rw [mapVertexGroup_range_eq_stabilizer hp.fundamentalGroupoidMap_isCovering ξ₀]

/-- Helper for Proposition 3.8.9: at the distinguished categorical fiber point over `p e`, the
transported subgroup is the image of the induced vertex-group map. -/
private theorem fiberPointSubgroup_basepoint_eq_mapVertexGroup_range
    (hp : IsPathConnectedCoveringMap p) (e : E) :
    fiberPointSubgroup ((hp.fundamentalGroupoidMapFiberEquiv (p e)).symm ⟨e, rfl⟩) =
      (hp.fundamentalGroupoidMap.mapVertexGroup (mk e)).range := by
  -- At the literal basepoint, the transported subgroup is definitionally the induced image.
  rfl

/-- Proposition 3.8.9: if the restricted deck-transformation action on the fiber over `p e` is
pretransitive, then the image subgroup `p_*(π₁(E,e))` is normal in `π₁(B, b)`. -/
-- Proof sketch: pretransitivity identifies the stabilizers of different points in the chosen
-- fiber, forcing the subgroup `p_*(π₁(E,e))` to be normal.
theorem coveringSpaceAut_transitiveOnFiber_normal_fundamentalGroup_map_range
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (htrans :
      letI := coveringSpaceAutFiberMulAction p e
      MulAction.IsPretransitive (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e})) :
    ((FundamentalGroup.map p e).range).Normal := by
  let ξ₀ : hp.fundamentalGroupoidMap.Fiber (mk (p e)) :=
    (hp.fundamentalGroupoidMapFiberEquiv (p e)).symm ⟨e, rfl⟩
  have hnormal : (fiberPointSubgroup ξ₀).Normal := by
    constructor
    intro n hn g
    rcases Functor.IsCovering.exists_fiberPoint_mapVertexGroup_range_eq_conjugate
        hp.fundamentalGroupoidMap_isCovering ξ₀ g with ⟨ξ, hξ⟩
    let x : p ⁻¹' {p e} := hp.fundamentalGroupoidMapFiberEquiv (p e) ξ
    letI := coveringSpaceAutFiberMulAction p e
    -- Pretransitivity moves the distinguished fiber point to the new categorical point.
    obtain ⟨α, hα⟩ := MulAction.exists_smul_eq (Aut (Over.mk (TopCat.ofHom p)))
      (⟨e, rfl⟩ : p ⁻¹' {p e}) x
    have hsub : fiberPointSubgroup ξ = fiberPointSubgroup ξ₀ := by
      -- The earlier deck-invariance lemma collapses the subgroup at `ξ` back to the base subgroup.
      simpa [x, ξ₀] using coveringSpaceAut_fundamentalGroup_map_range_eq hp e x α hα
    have hconj : MulAut.conj g • fiberPointSubgroup ξ₀ = fiberPointSubgroup ξ₀ := by
      -- Proposition 3.3.6 gives the conjugate subgroup, and pretransitivity identifies it with `ξ₀`.
      calc
        MulAut.conj g • fiberPointSubgroup ξ₀ = fiberPointSubgroup ξ := by
          symm
          exact hξ
        _ = fiberPointSubgroup ξ₀ := hsub
    have hmem : MulAut.conj g • n ∈ MulAut.conj g • fiberPointSubgroup ξ₀ :=
      Subgroup.smul_mem_pointwise_smul n (MulAut.conj g) (fiberPointSubgroup ξ₀) hn
    have hmem' : g ≫ n ≫ inv g ∈ MulAut.conj g • fiberPointSubgroup ξ₀ := by
      simpa [MulAut.conj_apply] using hmem
    -- Transport the conjugated element back to the original subgroup at the basepoint.
    simpa using (hconj ▸ hmem')
  have hnormal' : (hp.fundamentalGroupoidMap.mapVertexGroup (mk e)).range.Normal := by
    simpa [ξ₀, fiberPointSubgroup_basepoint_eq_mapVertexGroup_range] using hnormal
  have hnormal'' : (((FundamentalGroupoid.map p).mapEnd (mk e)).range).Normal := by
    let q : C(E, B) := ⟨p, hp.isCoveringMap.continuous⟩
    have hq : q = p := by
      ext x
      rfl
    have hnormalqv : ((FundamentalGroupoid.map q).mapVertexGroup (mk e)).range.Normal := by
      simpa [q, IsPathConnectedCoveringMap.fundamentalGroupoidMap] using hnormal'
    have hnormalq : (((FundamentalGroupoid.map q).mapEnd (mk e)).range).Normal := by
      constructor
      intro n hn g
      rcases (Subgroup.Normal.conj_mem' hnormalqv n hn g) with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      change Path.Homotopic.Quotient.map x q = g⁻¹ ≫ n ≫ g
      simpa [CategoryTheory.Functor.mapVertexGroup] using hx
    simpa [hq] using hnormalq
  -- Rewrite the distinguished categorical subgroup as the ordinary fundamental-group image.
  simpa [FundamentalGroup.map] using hnormal''

/-- Helper for Proposition 3.8.9: applying a deck transformation to the endpoint of a lifted path
matches lifting the same base path from the translated starting point. -/
private theorem coveringSpaceAut_liftPath_endpoint_comm
    (hp : IsPathConnectedCoveringMap p) (α : Aut (Over.mk (TopCat.ofHom p)))
    {b₀ b₁ : B} (γ : Path b₀ b₁) (x : p ⁻¹' {b₀}) :
    α.hom.left.hom (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm) 1) =
      hp.isCoveringMap.liftPath γ (α • x.1)
        (by
          rw [coveringSpaceAut_smul_proj p α x.1]
          exact γ.source.trans x.2.symm) 1 := by
  -- Route correction: compare the two actual lifts of `γ`, rather than pushing through another
  -- categorical fiber-transport layer.
  let hxα : γ 0 = p (α • x.1) := by
    rw [coveringSpaceAut_smul_proj p α x.1]
    exact γ.source.trans x.2.symm
  have hLiftEq :
      α.hom.left.hom.comp (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm)) =
        hp.isCoveringMap.liftPath γ (α • x.1) hxα := by
    -- Both lifts project to `γ` and start at the translated point, so uniqueness identifies them.
    apply (hp.isCoveringMap.eq_liftPath_iff' hxα).2
    constructor
    · ext t
      have hproj :
          p (α.hom.left.hom (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm) t)) =
            p (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm) t) := by
        simpa using coveringSpaceAut_smul_proj p α
          (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm) t)
      simpa [ContinuousMap.comp_apply] using
        hproj.trans
          (congr_fun (hp.isCoveringMap.liftPath_lifts γ x.1 (γ.source.trans x.2.symm)) t)
    · calc
        (α.hom.left.hom.comp (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm))) 0 =
            α.hom.left.hom ((hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm)) 0) := by
              rfl
        _ = α.hom.left.hom x.1 := by
              rw [hp.isCoveringMap.liftPath_zero]
        _ = α • x.1 := by
              rfl
  -- Evaluate the identified lifts at the endpoint.
  simpa using congrArg (fun f => f 1) hLiftEq

/-- Helper for Proposition 3.8.9: deck transformations commute with fiber translation along a base
path class. -/
private theorem coveringSpaceAut_fiberTranslationMap_comm
    (hp : IsPathConnectedCoveringMap p) (α : Aut (Over.mk (TopCat.ofHom p)))
    {b₀ b₁ : B} (f : mk b₀ ⟶ mk b₁) (x : p ⁻¹' {b₀}) :
    hp.fiberTranslationMap f
      ⟨α • x.1, by
        simpa [x.2] using (coveringSpaceAut_smul_proj p α x.1).trans x.2⟩ =
      ⟨α • (hp.fiberTranslationMap f x).1, by
        simpa using (coveringSpaceAut_smul_proj p α (hp.fiberTranslationMap f x).1).trans
          (hp.fiberTranslationMap f x).2⟩ := by
  -- Reduce the groupoid arrow to a represented path so that Example 3.3.9 applies on endpoints.
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  let xα : p ⁻¹' {b₀} :=
    ⟨α • x.1, by
      simpa [x.2] using (coveringSpaceAut_smul_proj p α x.1).trans x.2⟩
  have hleft := IsPathConnectedCoveringMap.fiberTranslationMap_fromPath_eq_liftPath_endpoint
    hp γ xα
  have hright := IsPathConnectedCoveringMap.fiberTranslationMap_fromPath_eq_liftPath_endpoint
    hp γ x
  apply Subtype.ext
  -- Rewrite both fiber translations to lifted-path endpoints and then compare those endpoints.
  simpa using
    calc
      ↑(hp.fiberTranslationMap (fromPath (Path.Homotopic.Quotient.mk γ)) xα) =
          hp.isCoveringMap.liftPath γ xα.1 (γ.source.trans xα.2.symm) 1 := by
            simpa using congrArg Subtype.val hleft
      _ = α.hom.left.hom (hp.isCoveringMap.liftPath γ x.1 (γ.source.trans x.2.symm) 1) := by
            simpa [xα] using (coveringSpaceAut_liftPath_endpoint_comm hp α γ x).symm
      _ = α.hom.left.hom (hp.fiberTranslationMap (fromPath (Path.Homotopic.Quotient.mk γ)) x).1 := by
            simpa using congrArg (fun z => α.hom.left.hom z) (congrArg Subtype.val hright).symm

/-- Helper for Proposition 3.8.9: fiber translation along a groupoid morphism and then back along
its inverse returns the original point of the fiber. -/
private theorem fiberTranslationMap_apply_inv
    (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B} (f : mk b₀ ⟶ mk b₁)
    (x : p ⁻¹' {b₁}) :
    hp.fiberTranslationMap f (hp.fiberTranslationMap (CategoryTheory.Groupoid.inv f) x) = x := by
  -- Transport the categorical inverse-translation identity to the ordinary fiber.
  apply (hp.fundamentalGroupoidMapFiberEquiv b₁).symm.injective
  calc
    (hp.fundamentalGroupoidMapFiberEquiv b₁).symm
        (hp.fiberTranslationMap f (hp.fiberTranslationMap (CategoryTheory.Groupoid.inv f) x))
        = Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering f
            (Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering
              (CategoryTheory.Groupoid.inv f)
              ((hp.fundamentalGroupoidMapFiberEquiv b₁).symm x)) := by
                simp [IsPathConnectedCoveringMap.fiberTranslationMap, Function.comp]
    _ = Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering
          (CategoryTheory.Groupoid.inv f ≫ f)
          ((hp.fundamentalGroupoidMapFiberEquiv b₁).symm x) := by
            -- Compose the two categorical transport maps before comparing with the identity.
            symm
            exact congrFun
              (Functor.IsCovering.fiberTranslationMap_comp hp.fundamentalGroupoidMap_isCovering
                (CategoryTheory.Groupoid.inv f) f)
              ((hp.fundamentalGroupoidMapFiberEquiv b₁).symm x)
    _ = Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering
          (𝟙 (mk b₁))
          ((hp.fundamentalGroupoidMapFiberEquiv b₁).symm x) := by
            simp
    _ = (hp.fundamentalGroupoidMapFiberEquiv b₁).symm x := by
          exact congrFun
            (Functor.IsCovering.fiberTranslationMap_id hp.fundamentalGroupoidMap_isCovering
              (mk b₁))
            ((hp.fundamentalGroupoidMapFiberEquiv b₁).symm x)

/-- Helper for Proposition 3.8.9: under the chosen-fiber transitivity hypothesis, two points of
`E` lie in the same deck-transformation orbit exactly when they have the same image in `B`. -/
private theorem coveringSpaceAut_orbitRel_iff_proj_eq
    [PathConnectedSpace B]
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (htrans :
      letI := coveringSpaceAutFiberMulAction p e
      MulAction.IsPretransitive (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e}))
    {x y : E} :
    MulAction.orbitRel (Aut (Over.mk (TopCat.ofHom p))) E x y ↔ p x = p y := by
  constructor
  · exact coveringSpaceAut_proj_eq_of_orbitRel p
  · intro hxy
    let γ : Path (p e) (p x) := PathConnectedSpace.somePath (p e) (p x)
    let f : mk (p e) ⟶ mk (p x) := fromPath ⟦γ⟧
    let x' : p ⁻¹' {p x} := ⟨x, rfl⟩
    let y' : p ⁻¹' {p x} := ⟨y, hxy.symm⟩
    let x₀ : p ⁻¹' {p e} := hp.fiberTranslationMap (CategoryTheory.Groupoid.inv f) x'
    let y₀ : p ⁻¹' {p e} := hp.fiberTranslationMap (CategoryTheory.Groupoid.inv f) y'
    letI := coveringSpaceAutFiberMulAction p e
    -- Pull both points back to the chosen fiber and use pretransitivity there.
    obtain ⟨α, hα⟩ := MulAction.exists_smul_eq (Aut (Over.mk (TopCat.ofHom p))) y₀ x₀
    have hα' : ⟨α • y₀.1, by
          simpa [y₀.2] using (coveringSpaceAut_smul_proj p α y₀.1).trans y₀.2⟩ = x₀ := by
      simpa using hα
    have hpush := coveringSpaceAut_fiberTranslationMap_comm hp α f y₀
    rw [hα'] at hpush
    have hpush : hp.fiberTranslationMap f x₀ =
        ⟨α • (hp.fiberTranslationMap f y₀).1, by
          simpa using (coveringSpaceAut_smul_proj p α (hp.fiberTranslationMap f y₀).1).trans
            (hp.fiberTranslationMap f y₀).2⟩ := by
      -- Push the chosen-fiber deck transformation forward along `f`.
      exact hpush
    have hxback : hp.fiberTranslationMap f x₀ = x' := by
      simpa [x₀] using fiberTranslationMap_apply_inv hp f x'
    have hyback : hp.fiberTranslationMap f y₀ = y' := by
      simpa [y₀] using fiberTranslationMap_apply_inv hp f y'
    have hxval : (hp.fiberTranslationMap f x₀).1 = x := by
      simpa [x'] using congrArg Subtype.val hxback
    have hyval : (hp.fiberTranslationMap f y₀).1 = y := by
      simpa [y'] using congrArg Subtype.val hyback
    have hpushval : α • (hp.fiberTranslationMap f y₀).1 = (hp.fiberTranslationMap f x₀).1 := by
      simpa using (congrArg Subtype.val hpush).symm
    -- Translating back recovers the original points, so `x` and `y` lie in the same orbit.
    refine ⟨α, ?_⟩
    calc
      α • y = α • (hp.fiberTranslationMap f y₀).1 := by
        rw [hyval]
      _ = (hp.fiberTranslationMap f x₀).1 := hpushval
      _ = x := hxval

/-- If the base is path connected and the restricted deck-transformation action on one fiber is
pretransitive, then the canonical map from `E / Aut(E)` to `B` is a homeomorphism. -/
-- Proof sketch: path connectedness transports fiberwise pretransitivity from the chosen fiber to
-- every fiber by lifting base paths and using uniqueness of path lifting for deck
-- transformations. The descended orbit map is then bijective, and on evenly covered
-- neighborhoods it is identified with the original covering map modulo permutation of sheets.
theorem coveringSpaceAut_transitiveOnFiber_quotientMap_isHomeomorph
    [PathConnectedSpace B]
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (htrans :
      letI := coveringSpaceAutFiberMulAction p e
      MulAction.IsPretransitive (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e})) :
    IsHomeomorph (coveringSpaceAutOrbitProjection p) := by
  refine ⟨(coveringSpaceAutOrbitProjection p).continuous, ?_, ?_⟩
  · intro U hU
    have hpre : IsOpen
        ((Quotient.mk'' : E → E /[Aut (Over.mk (TopCat.ofHom p))]) ⁻¹' U) := by
      simpa using
        (isOpen_coinduced
          (f := (Quotient.mk'' : E → E /[Aut (Over.mk (TopCat.ofHom p))]))).mp hU
    have himage : (coveringSpaceAutOrbitProjection p) '' U =
        p '' ((Quotient.mk'' : E → E /[Aut (Over.mk (TopCat.ofHom p))]) ⁻¹' U) := by
      -- The descended orbit map has the same image as `p` on representatives of `U`.
      ext b
      constructor
      · rintro ⟨q, hq, hqeq⟩
        obtain ⟨x, rfl⟩ := Quotient.mk''_surjective q
        exact ⟨x, hq, hqeq⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Quotient.mk'' x, hx, rfl⟩
    rw [himage]
    -- The original covering map is open, so the descended orbit map is open as well.
    exact hp.isCoveringMap.isOpenMap _ hpre
  · constructor
    · intro q₁ q₂ hq
      refine Quotient.inductionOn₂' q₁ q₂ (fun x y hxy => ?_) hq
      -- Equal images mean the representatives have the same basepoint, hence are orbit-related.
      exact Quotient.eq''.2
        ((coveringSpaceAut_orbitRel_iff_proj_eq hp e htrans).2
          (by simpa [coveringSpaceAutOrbitProjection] using hxy))
    · intro b
      -- Surjectivity is inherited directly from the covering map.
      obtain ⟨x, rfl⟩ := hp.surjective b
      exact ⟨Quotient.mk'' x, rfl⟩

/-- In a locally path-connected base, fiberwise pretransitivity of deck transformations upgrades
the normality clause of Proposition 3.8.9 to the canonical regular-covering owner. -/
theorem coveringSpaceAut_transitiveOnFiber_isRegularCoveringMap
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (htrans :
      letI := coveringSpaceAutFiberMulAction p e
      MulAction.IsPretransitive (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e})) :
    IsRegularCoveringMap p e := by
  refine
    { toIsPathConnectedCoveringMap := hp
      normal_fundamentalGroup_map_range := ?_ }
  exact coveringSpaceAut_transitiveOnFiber_normal_fundamentalGroup_map_range hp e htrans

/-- Proposition 3.8.9: over a locally path-connected, path-connected base, fiberwise
pretransitivity of deck transformations implies regularity at the chosen fiber point and
identifies the orbit quotient `E / Aut(E)` with `B`. -/
theorem coveringSpaceAut_transitiveOnFiber_regular_and_quotientMap_isHomeomorph
    [LocPathConnectedSpace B] [PathConnectedSpace B]
    (hp : IsPathConnectedCoveringMap p) (e : E)
    (htrans :
      letI := coveringSpaceAutFiberMulAction p e
      MulAction.IsPretransitive (Aut (Over.mk (TopCat.ofHom p))) (p ⁻¹' {p e})) :
    IsRegularCoveringMap p e ∧
      IsHomeomorph (coveringSpaceAutOrbitProjection p) := by
  exact
    ⟨coveringSpaceAut_transitiveOnFiber_isRegularCoveringMap hp e htrans,
      coveringSpaceAut_transitiveOnFiber_quotientMap_isHomeomorph hp e htrans⟩
