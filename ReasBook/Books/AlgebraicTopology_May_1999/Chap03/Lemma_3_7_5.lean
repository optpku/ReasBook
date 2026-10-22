/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_6
import AlgebraicTopology_May_1999.Chap03.Definition_3_7_4
import AlgebraicTopology_May_1999.Chap03.Example_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {E E' B : Type u}
  [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace B]
  [ConnectedSpace E] [ConnectedSpace E'] [ConnectedSpace B]
  [LocPathConnectedSpace E] [LocPathConnectedSpace E'] [LocPathConnectedSpace B]

/-- Helper for Lemma 3.7.5: a morphism of covering spaces over `B` preserves the base projection
pointwise. -/
-- Evaluating the commutative triangle `Over.w h` at a point of the total space recovers the
-- defining relation `p' ∘ h.left = p`.
private theorem covering_space_hom_comm
    {p : C(E, B)} {p' : C(E', B)}
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) (x : E) :
    p' (h.left.hom x) = p x := by
  have hx := congrArg (fun f : TopCat.of E ⟶ TopCat.of B ↦ f.hom x) (Over.w h)
  simpa [ContinuousMap.comp_apply] using hx

/-- Helper for Lemma 3.7.5: a smaller open path-connected neighborhood inside a fundamental
neighborhood is again fundamental. -/
-- We restrict the given local trivialization from `U` to `V` by first rewriting the relevant
-- source as a subtype of `p ⁻¹' U`, then restricting the homeomorphism, and finally re-associating
-- the codomain as `V × (p ⁻¹' {b})`.
private theorem fundamental_neighborhood_restrict {p : E → B} {b : B} {U V : Set B}
    (hU : IsFundamentalNeighborhood p b U) (hVU : V ⊆ U) (hbV : b ∈ V)
    (hVOpen : IsOpen V) (hVPath : IsPathConnected V) :
    IsFundamentalNeighborhood p b V := by
  rcases hU with ⟨hdisc, hbU, hUOpen, hUPath, hpreUOpen, H, hH⟩
  let e₀ : p ⁻¹' V ≃ₜ { x : p ⁻¹' U // p x.1 ∈ V } :=
    { toFun := fun x ↦ ⟨⟨x.1, hVU x.2⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        cases x
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let e₁ :
      { x : p ⁻¹' U // p x.1 ∈ V } ≃ₜ
        { y : U × (p ⁻¹' ({b} : Set B)) // y.1.1 ∈ V } :=
    H.subtype fun x ↦ by
      simpa [hH x]
  let e₂ :
      { y : U × (p ⁻¹' ({b} : Set B)) // y.1.1 ∈ V } ≃ₜ
        V × (p ⁻¹' ({b} : Set B)) :=
    { toFun := fun y ↦ (⟨y.1.1.1, y.2⟩, y.1.2)
      invFun := fun y ↦ ⟨((⟨y.1.1, hVU y.1.2⟩ : U), y.2), y.1.2⟩
      left_inv := by
        intro y
        cases y
        rfl
      right_inv := by
        intro y
        cases y
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  refine ⟨hdisc, hbV, hVOpen, hVPath, ?_, e₀.trans (e₁.trans e₂), ?_⟩
  · let S : Set (p ⁻¹' U) := { x | (H x).1.1 ∈ V }
    have hSOpen : IsOpen S := by
      have hcont₁ : Continuous fun x : p ⁻¹' U ↦ (H x).1 := by
        change Continuous (fun x : p ⁻¹' U ↦ Prod.fst (H x))
        exact continuous_fst.comp H.continuous
      have hcont : Continuous fun x : p ⁻¹' U ↦ (H x).1.1 :=
        continuous_subtype_val.comp hcont₁
      simpa [S] using hVOpen.preimage hcont
    have hSV : Subtype.val '' S = p ⁻¹' V := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [S, hH y] using hy
      · intro hx
        refine ⟨⟨x, hVU hx⟩, ?_, rfl⟩
        simpa [S, hH ⟨x, hVU hx⟩] using hx
    simpa [hSV] using IsOpen.isOpenMap_subtype_val hpreUOpen S hSOpen
  · intro x
    simpa [e₀, e₁, e₂] using hH ⟨x.1, hVU x.2⟩

/-- Helper for Lemma 3.7.5: a morphism of connected covering spaces over the same base is
surjective on total spaces. -/
-- Route correction: instead of packaging the groupoid-fiber argument explicitly, we use the
-- equivalent path-lifting statement. A path from a fixed image point to `y'` lifts through `p`,
-- and composing that lift with `h.left` gives another lift through `p'`; uniqueness of lifted
-- paths forces the endpoint to be `y'`.
private theorem covering_space_hom_surjective
    {p : C(E, B)} {p' : C(E', B)}
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    Function.Surjective h.left := by
  classical
  show ∀ y' : E', ∃ x : E, h.left.hom x = y'
  letI : PathConnectedSpace E := PathConnectedSpace.of_locPathConnectedSpace
  letI : PathConnectedSpace E' := PathConnectedSpace.of_locPathConnectedSpace
  let e₀ : E := Classical.choice (inferInstance : Nonempty E)
  intro y'
  let y₀ : E' := h.left.hom e₀
  let γ : Path y₀ y' := (PathConnectedSpace.joined y₀ y').somePath
  let γB : Path (p' y₀) (p' y') := γ.map hp'.isCoveringMap.continuous
  let Γ : C(↑unitInterval, E) :=
    hp.isCoveringMap.liftPath γB e₀ (γB.source.trans (covering_space_hom_comm h e₀))
  let hΓ : C(↑unitInterval, E') := h.left.hom.comp Γ
  have hhΓ_lifts : p' ∘ hΓ = γB.toContinuousMap := by
    ext t
    calc
      p' (hΓ t) = p (Γ t) := covering_space_hom_comm h (Γ t)
      _ = γB.toContinuousMap t := by
        exact congrFun
          (hp.isCoveringMap.liftPath_lifts γB e₀
            (γB.source.trans (covering_space_hom_comm h e₀))) t
  have hhΓ_zero : hΓ 0 = h.left.hom e₀ := by
    simpa [hΓ, Γ] using congrArg h.left.hom
      (hp.isCoveringMap.liftPath_zero γB e₀ (γB.source.trans (covering_space_hom_comm h e₀)))
  have hhΓ_eq :
      hΓ = hp'.isCoveringMap.liftPath γB y₀ γB.source := by
    refine (hp'.isCoveringMap.eq_liftPath_iff' γB.source).2 ?_
    exact ⟨hhΓ_lifts, hhΓ_zero⟩
  have hγ_eq :
      γ.toContinuousMap = hp'.isCoveringMap.liftPath γB y₀ γB.source := by
    refine (hp'.isCoveringMap.eq_liftPath_iff' γB.source).2 ?_
    constructor
    · ext t
      change p' (γ t) = p' (γ t)
      rfl
    · simpa [γB] using γ.source
  refine ⟨Γ 1, ?_⟩
  change hΓ 1 = y'
  have hendpoint :
      hΓ 1 = γ.toContinuousMap 1 := by
    rw [hhΓ_eq, hγ_eq.symm]
  simpa [hΓ] using hendpoint.trans γ.target

/-- Helper for Lemma 3.7.5: the image of a point in one source sheet over a common fundamental
neighborhood still lies over that same base point in the target cover. -/
-- The commutative triangle `p' ∘ h.left = p` identifies the base coordinates, and the source
-- trivialization records that coordinate as `u`.
private theorem source_sheet_image_mem_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u : V) (i : p ⁻¹' ({b} : Set B)) :
    h.left.hom ((H.symm (u, i)).1) ∈ p' ⁻¹' V := by
  have hbase :
      p' (h.left.hom ((H.symm (u, i)).1)) = p ((H.symm (u, i)).1) :=
    covering_space_hom_comm h ((H.symm (u, i)).1)
  have hu :
      p ((H.symm (u, i)).1) = u.1 := by
    exact (hH (H.symm (u, i))).symm.trans (by simp)
  show p' (h.left.hom ((H.symm (u, i)).1)) ∈ V
  rw [hbase, hu]
  exact u.2

/-- Helper for Lemma 3.7.5: in the common local trivializations, `h.left` preserves the base
coordinate. -/
-- After placing the source point into the source trivialization and applying the over-category
-- commutativity relation, the first coordinate in the target trivialization is forced to be `u`.
private theorem source_sheet_image_first_coordinate
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u : V) (i : p ⁻¹' ({b} : Set B)) :
    (H' ⟨h.left.hom ((H.symm (u, i)).1),
      source_sheet_image_mem_common_neighborhood H hH h u i⟩).1 = u := by
  apply Subtype.ext
  have hbase :
      p' (h.left.hom ((H.symm (u, i)).1)) = p ((H.symm (u, i)).1) :=
    covering_space_hom_comm h ((H.symm (u, i)).1)
  have hu :
      p ((H.symm (u, i)).1) = u.1 := by
    exact (hH (H.symm (u, i))).symm.trans (by simp)
  simpa [hH' _] using hbase.trans hu

/-- Helper for Lemma 3.7.5: over a common path-connected fundamental neighborhood, the image of
one source sheet lands in a single target sheet. -/
-- The target-sheet index is a continuous map from the path-connected space `V` into the discrete
-- fiber `p' ⁻¹' {b}`, so it is constant.
private theorem source_sheet_maps_to_single_target_sheet
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hVPath : IsPathConnected V)
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (u₀ : V) (i : p ⁻¹' ({b} : Set B)) :
    let j :=
      (H' ⟨h.left.hom ((H.symm (u₀, i)).1),
        source_sheet_image_mem_common_neighborhood H hH h u₀ i⟩).2
    ∀ u : V,
      (H' ⟨h.left.hom ((H.symm (u, i)).1),
        source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = j := by
  let c : C(V, p' ⁻¹' ({b} : Set B)) :=
    ⟨fun u ↦
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2,
      by
        have hpair : Continuous fun u : V ↦ ((u, i) : V × (p ⁻¹' ({b} : Set B))) := by
          fun_prop
        have hsource : Continuous fun u : V ↦ (H.symm (u, i)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        have htarget :
            Continuous fun u : V ↦
              (⟨h.left.hom ((H.symm (u, i)).1),
                source_sheet_image_mem_common_neighborhood H hH h u i⟩ : p' ⁻¹' V) := by
          exact Continuous.subtype_mk (h.left.hom.continuous.comp hsource)
            (fun u ↦ source_sheet_image_mem_common_neighborhood H hH h u i)
        have hcomp : Continuous fun u : V ↦
            H' ⟨h.left.hom ((H.symm (u, i)).1),
              source_sheet_image_mem_common_neighborhood H hH h u i⟩ :=
          H'.continuous.comp htarget
        exact continuous_snd.comp hcomp⟩
  letI : PathConnectedSpace V := (isPathConnected_iff_pathConnectedSpace).mp hVPath
  dsimp
  intro u
  have hconst : c u = c u₀ :=
    PreconnectedSpace.constant (hp := inferInstance) (f := c) c.continuous
  simpa [c] using hconst

/-- Helper for Lemma 3.7.5: a target sheet cut out by a fixed sheet index is open in the ambient
total space. -/
-- The sheet condition is the preimage of a singleton in the discrete fiber, so it is open in
-- `p' ⁻¹' V`; then the subtype projection carries it to an open subset of `E'`.
private theorem target_sheet_isOpen
    {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hpreVOpen : IsOpen (p' ⁻¹' V))
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (j : p' ⁻¹' ({b} : Set B)) :
    IsOpen (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) := by
  let S : Set (p' ⁻¹' V) := { y | (H' y).2 = j }
  have hSOpen : IsOpen S := by
    have hcont : Continuous fun y : p' ⁻¹' V ↦ (H' y).2 :=
      continuous_snd.comp H'.continuous
    simpa [S] using (isOpen_discrete ({j} : Set (p' ⁻¹' ({b} : Set B)))).preimage hcont
  simpa [S] using IsOpen.isOpenMap_subtype_val hpreVOpen S hSOpen

/-- Helper for Lemma 3.7.5: the chosen target sheet is homeomorphic to the common fundamental
neighborhood `V`. -/
-- We parameterize the sheet by its base coordinate `u : V`, then pass from the sheet subtype to
-- its image in `E'` through the subtype embedding.
private theorem target_sheet_homeomorph_common_neighborhood
    {p' : C(E', B)} {b : B} {V : Set B}
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (j : p' ⁻¹' ({b} : Set B)) :
    ∃ eW : V ≃ₜ (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }),
      ∀ u : V,
        ((eW u : Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
          (H'.symm (u, j)).1 := by
  let e₀ :
      V ≃ₜ { y : p' ⁻¹' V // (H' y).2 = j } :=
    { toFun := fun u ↦ ⟨H'.symm (u, j), by simp⟩
      invFun := fun y ↦ (H' y.1).1
      left_inv := by
        intro u
        simpa using congrArg Prod.fst (H'.apply_symm_apply (u, j))
      right_inv := by
        intro y
        apply Subtype.ext
        have hy : (H' y.1).2 = j := y.2
        apply H'.injective
        change H' (H'.symm ((H' y.1).1, j)) = H' y.1
        have hpair : ((H' y.1).1, j) = H' y.1 := by
          ext
          · rfl
          · exact congrArg Subtype.val hy.symm
        exact (H'.apply_symm_apply ((H' y.1).1, j)).trans hpair
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let S : Set (p' ⁻¹' V) := { y | (H' y).2 = j }
  let eW :
      V ≃ₜ Set.image (Subtype.val : p' ⁻¹' V → E') S :=
    e₀.trans ((Topology.IsEmbedding.subtypeVal).homeomorphImage S)
  refine ⟨eW, ?_⟩
  -- The chosen parameterization of the target sheet is pointwise the obvious inverse chart.
  intro u
  change (((Topology.IsEmbedding.subtypeVal).homeomorphImage S) (e₀ u)).1 =
      (H'.symm (u, j)).1
  rfl

/-- Helper for Lemma 3.7.5: belonging to the chosen target sheet is equivalent to having the
corresponding source sheet index map to `j`. -/
-- We compare the target trivialization of `h.left x` with the point of the chosen sheet that
-- realizes membership in the image of `Subtype.val`.
private theorem mem_target_sheet_iff_sheet_index
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (x : p ⁻¹' V) :
    h.left.hom x.1 ∈
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ↔
      φ (H x).2 = j := by
  constructor
  · rintro ⟨y, hyj, hyx⟩
    have hxBack : H.symm ((H x).1, (H x).2) = x := by
      simpa using H.symm_apply_apply x
    let hx' : p' ⁻¹' V :=
      ⟨h.left.hom ((H.symm ((H x).1, (H x).2)).1),
        source_sheet_image_mem_common_neighborhood H hH h (H x).1 (H x).2⟩
    have hsub :
        hx' = y := by
      apply Subtype.ext
      simpa [hx', hxBack] using hyx.symm
    have hsnd :
        (H' hx').2 = j := by
      exact (congrArg Prod.snd (congrArg H' hsub)).trans hyj
    simpa [hx', hxBack] using (hφ (H x).1 (H x).2).symm.trans hsnd
  · intro hxj
    have hxBack : H.symm ((H x).1, (H x).2) = x := by
      simpa using H.symm_apply_apply x
    let hx' : p' ⁻¹' V :=
      ⟨h.left.hom ((H.symm ((H x).1, (H x).2)).1),
        source_sheet_image_mem_common_neighborhood H hH h (H x).1 (H x).2⟩
    refine ⟨hx', ?_, ?_⟩
    · simpa [hx', hxBack] using (hφ (H x).1 (H x).2).trans hxj
    · simpa [hx', hxBack]

/-- Helper for Lemma 3.7.5: the preimage of the chosen target sheet is exactly the union of the
source sheets whose image index is `j`. -/
-- Once a point of `E` lands in the chosen target sheet, the commutative square forces its base
-- coordinate into `V`, and the previous iff lemma converts sheet membership into the equation
-- `φ (H x).2 = j`.
private theorem preimage_target_sheet_eq_sheet_index
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) =
      Set.image (Subtype.val : p ⁻¹' V → E) { x | φ (H x).2 = j } := by
  ext x
  constructor
  · intro hx
    have hxV : p x ∈ V := by
      rcases hx with ⟨y, _hyj, hyx⟩
      have hbase : p x = p' y.1 := by
        calc
          p x = p' (h.left.hom x) := (covering_space_hom_comm h x).symm
          _ = p' y.1 := by simpa using congrArg p' hyx.symm
      have hyV : p' y.1 ∈ V := y.2
      simpa [hbase] using hyV
    refine ⟨⟨x, hxV⟩, ?_, rfl⟩
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ ⟨x, hxV⟩).1 hx
  · rintro ⟨xV, hxj, rfl⟩
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).2 hxj

/-- Helper for Lemma 3.7.5: a point whose image lies in the chosen target sheet already lies over
the common neighborhood `V`. -/
-- The target-sheet witness lies in `p' ⁻¹' V`, and the relation `p' ∘ h.left = p` transfers that
-- basepoint membership back to the source point.
private theorem preimage_target_sheet_mem_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (x : h.left ⁻¹'
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) :
    p x.1 ∈ V := by
  rcases x.2 with ⟨y, _hyj, hyx⟩
  have hbase : p x.1 = p' y.1 := by
    calc
      p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
      _ = p' y.1 := by simpa using congrArg p' hyx.symm
  have hyV : p' y.1 ∈ V := y.2
  simpa [hbase] using hyV

/-- Helper for Lemma 3.7.5: over the chosen target sheet, `h.left` is modeled by `V` times the
sheet-index fiber `φ ⁻¹' {j}`. -/
-- We rewrite the restricted preimage as a subset of `p ⁻¹' V`, transport it through the source
-- trivialization `H`, and finally reassociate the remaining subtype into `V × {i // φ i = j}`.
private theorem preimage_target_sheet_homeomorph_common_neighborhood
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    ∃ Hpre :
      (h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) ≃ₜ
        V × { i : p ⁻¹' ({b} : Set B) // φ i = j },
      ∀ x,
        (Hpre x).1 =
          (H ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩).1 := by
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  let S : Set (p ⁻¹' V) := { x | φ (H x).2 = j }
  let e₀ :
      (h.left ⁻¹' W) ≃ₜ Set.image (Subtype.val : p ⁻¹' V → E) S :=
    Homeomorph.setCongr (preimage_target_sheet_eq_sheet_index H hH H' h j φ hφ)
  let e₁ : Set.image (Subtype.val : p ⁻¹' V → E) S ≃ₜ S :=
    ((Topology.IsEmbedding.subtypeVal).homeomorphImage S).symm
  let e₂ : S ≃ₜ { z : V × (p ⁻¹' ({b} : Set B)) // φ z.2 = j } :=
    H.subtype fun x ↦ by
      simp [S]
  let e₃ :
      { z : V × (p ⁻¹' ({b} : Set B)) // φ z.2 = j } ≃ₜ
        V × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    { toFun := fun z ↦ (z.1.1, ⟨z.1.2, z.2⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.1), z.2.2⟩
      left_inv := by
        intro z
        cases z
        rfl
      right_inv := by
        intro z
        cases z
        rfl
      continuous_toFun := by
        fun_prop
      continuous_invFun := by
        fun_prop }
  let Hpre : (h.left ⁻¹' W) ≃ₜ V × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    e₀.trans (e₁.trans (e₂.trans e₃))
  refine ⟨Hpre, ?_⟩
  intro x
  let xV : p ⁻¹' V := ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩
  have hxj : φ (H xV).2 = j := by
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).1 x.2
  let xS : S := ⟨xV, hxj⟩
  have he₀ :
      e₀ x = (Topology.IsEmbedding.subtypeVal).homeomorphImage S xS := by
    apply Subtype.ext
    rfl
  have he₁ : e₁ (e₀ x) = xS := by
    rw [he₀]
    simpa [e₁] using ((Topology.IsEmbedding.subtypeVal).homeomorphImage S).symm_apply_apply xS
  have he₂ :
      e₂ (e₁ (e₀ x)) = ⟨H xV, by simpa [S, xS] using hxj⟩ := by
    rw [he₁]
    apply Subtype.ext
    rfl
  -- After rewriting the restricted preimage into a source sheet union, the first factor is
  -- exactly the `V`-coordinate recorded by the source trivialization.
  change (e₃ (e₂ (e₁ (e₀ x)))).1 = (H xV).1
  rw [he₂]
  rfl

/-- Helper for Lemma 3.7.5: the chosen target-sheet parameterization sends the source-sheet base
coordinate to the actual image point of `x`. -/
-- The first coordinate of the target trivialization is already forced by the over-category
-- relation, and the second coordinate is `j` because `x` lies in the chosen target sheet.
private theorem chosen_target_sheet_image_eq
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i)
    (eW : V ≃ₜ (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }))
    (heW :
      ∀ u : V,
        ((eW u : Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
          (H'.symm (u, j)).1)
    (x : h.left ⁻¹'
      (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j })) :
    ((eW
        ((H ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩).1) :
      Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
      h.left x.1 := by
  let xV : p ⁻¹' V := ⟨x.1, preimage_target_sheet_mem_common_neighborhood H hH H' h j φ hφ x⟩
  have hxj : φ (H xV).2 = j := by
    exact (mem_target_sheet_iff_sheet_index H hH H' h j φ hφ xV).1 x.2
  have hxBack : H.symm ((H xV).1, (H xV).2) = xV := by
    simpa using H.symm_apply_apply xV
  have hxBackVal : (H.symm ((H xV).1, (H xV).2)).1 = x.1 := by
    simpa [xV] using congrArg Subtype.val hxBack
  let hx' : p' ⁻¹' V :=
    ⟨h.left.hom ((H.symm ((H xV).1, (H xV).2)).1),
      source_sheet_image_mem_common_neighborhood H hH h (H xV).1 (H xV).2⟩
  have htarget :
      H' hx' = ((H xV).1, j) := by
    apply Prod.ext
    · apply Subtype.ext
      simpa [hx', hxBackVal] using congrArg Subtype.val
        (source_sheet_image_first_coordinate H hH H' hH' h (H xV).1 (H xV).2)
    · simpa [hx', hxBackVal] using (hφ (H xV).1 (H xV).2).trans hxj
  have hsub : H'.symm ((H xV).1, j) = hx' := by
    apply H'.injective
    simpa [htarget] using H'.apply_symm_apply ((H xV).1, j)
  calc
    ((eW ((H xV).1) :
        Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) : E') =
        (H'.symm ((H xV).1, j)).1 := heW ((H xV).1)
    _ = h.left x.1 := by
      simpa [hx', hxBackVal] using congrArg Subtype.val hsub

/-- Helper for Lemma 3.7.5: the source-sheet indices mapping to the chosen target sheet are
homeomorphic to the actual fiber of `h.left` over `y'`. -/
-- We evaluate a source sheet at the basepoint `b` to land in the fiber over `y'`, and recover the
-- source index of a fiber point by reading its source trivialization coordinate.
private theorem sheet_index_homeomorph_covering_space_hom_fiber
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (hbV : b ∈ V)
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (y' : E') (hy'b : p' y' = b)
    (j : p' ⁻¹' ({b} : Set B))
    (hj : (H' ⟨y', by simpa [hy'b] using hbV⟩).2 = j)
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    Nonempty (
      { i : p ⁻¹' ({b} : Set B) // φ i = j } ≃ₜ
        h.left ⁻¹' ({y'} : Set E')) := by
  let toFun :
      { i : p ⁻¹' ({b} : Set B) // φ i = j } →
        h.left ⁻¹' ({y'} : Set E') :=
    fun i ↦
      let x : E := (H.symm (⟨b, hbV⟩, i.1)).1
      have hxFiber : h.left.hom x ∈ ({y'} : Set E') := by
        let hx' : p' ⁻¹' V :=
          ⟨h.left.hom x,
            source_sheet_image_mem_common_neighborhood H hH h ⟨b, hbV⟩ i.1⟩
        have hfst :
            (H' hx').1 = ⟨b, hbV⟩ := by
          apply Subtype.ext
          simpa [hx', x] using congrArg Subtype.val
            (source_sheet_image_first_coordinate H hH H' hH' h ⟨b, hbV⟩ i.1)
        have htarget :
            H' hx' = (⟨b, hbV⟩, j) := by
          exact Prod.ext hfst (by simpa [hx', x] using (hφ ⟨b, hbV⟩ i.1).trans i.2)
        have hyfst :
            (H' ⟨y', by simpa [hy'b] using hbV⟩).1 = ⟨b, hbV⟩ := by
          apply Subtype.ext
          simpa [hH' ⟨y', by simpa [hy'b] using hbV⟩, hy'b]
        have hy' :
            H' ⟨y', by simpa [hy'b] using hbV⟩ = (⟨b, hbV⟩, j) :=
          Prod.ext hyfst hj
        have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
          apply H'.injective
          exact htarget.trans hy'.symm
        simpa [hx'] using congrArg Subtype.val hsub
      ⟨x, hxFiber⟩
  let invFun :
      h.left ⁻¹' ({y'} : Set E') →
        { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    fun x ↦
      let hxb : p x.1 = b := by
        calc
          p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
          _ = p' y' := by simpa using congrArg p' x.2
          _ = b := hy'b
      let hxV : p x.1 ∈ V := by
        simpa [hxb] using hbV
      let xV' : p ⁻¹' V := ⟨x.1, hxV⟩
      let i : p ⁻¹' ({b} : Set B) := (H xV').2
      have hxSheet :
          φ i = j := by
        have hxBack : H.symm ((H xV').1, (H xV').2) = xV' := by
          simpa [i] using H.symm_apply_apply xV'
        have hxBackVal : (H.symm ((H xV').1, i)).1 = x.1 := by
          exact congrArg Subtype.val hxBack
        let hx' : p' ⁻¹' V :=
          ⟨h.left.hom ((H.symm ((H xV').1, i)).1),
            source_sheet_image_mem_common_neighborhood H hH h (H xV').1 i⟩
        have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
          apply Subtype.ext
          simpa [hx', hxBackVal] using x.2
        have hsnd : (H' hx').2 = j := by
          exact (congrArg Prod.snd (congrArg H' hsub)).trans hj
        simpa [i, xV', hx', hxBackVal] using (hφ (H xV').1 i).symm.trans hsnd
      ⟨i, hxSheet⟩
  have hLeft : Function.LeftInverse invFun toFun := by
    intro i
    apply Subtype.ext
    have hsecond :
        (H ⟨(H.symm (⟨b, hbV⟩, i.1)).1, by
          have hqa' :
              (H (H.symm (⟨b, hbV⟩, i.1))).1.1 = b := by
            simpa using congrArg (fun y : V × (p ⁻¹' ({b} : Set B)) ↦ y.1.1)
              (H.apply_symm_apply (⟨b, hbV⟩, i.1))
          simpa using (hH (H.symm (⟨b, hbV⟩, i.1))).symm.trans hqa'⟩).2 = i.1 := by
      simpa using congrArg Prod.snd (H.apply_symm_apply (⟨b, hbV⟩, i.1))
    simpa [toFun, invFun, hsecond]
  have hRight : Function.RightInverse invFun toFun := by
    intro x
    apply Subtype.ext
    let hxb : p x.1 = b := by
      calc
        p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
        _ = p' y' := by simpa using congrArg p' x.2
        _ = b := hy'b
    let hxV : p x.1 ∈ V := by
      simpa [hxb] using hbV
    let xV' : p ⁻¹' V := ⟨x.1, hxV⟩
    let i : p ⁻¹' ({b} : Set B) := (H xV').2
    have hfst : (H ⟨x.1, hxV⟩).1 = ⟨b, hbV⟩ := by
      apply Subtype.ext
      simpa [hxb] using hH ⟨x.1, hxV⟩
    have hxBack :
        H.symm (⟨b, hbV⟩, i) = ⟨x.1, hxV⟩ := by
      calc
        H.symm (⟨b, hbV⟩, i) = H.symm ((H xV').1, i) := by rw [hfst]
        _ = xV' := by simpa [xV', i] using H.symm_apply_apply xV'
    simpa [toFun, invFun, hxb, hxV, xV', i, hxBack]
  refine ⟨{
      toFun := toFun
      invFun := invFun
      left_inv := hLeft
      right_inv := hRight
      continuous_toFun := by
        have hpair :
            Continuous fun i :
                { i : p ⁻¹' ({b} : Set B) // φ i = j } =>
              ((⟨b, hbV⟩, i.1) : V × (p ⁻¹' ({b} : Set B))) := by
          fun_prop
        have hBase :
            Continuous fun i :
                { i : p ⁻¹' ({b} : Set B) // φ i = j } =>
              (H.symm (⟨b, hbV⟩, i.1)).1 := by
          simpa using continuous_subtype_val.comp (H.symm.continuous.comp hpair)
        exact Continuous.subtype_mk hBase fun i ↦ by
          let x : E := (H.symm (⟨b, hbV⟩, i.1)).1
          let hx' : p' ⁻¹' V :=
            ⟨h.left.hom x,
              source_sheet_image_mem_common_neighborhood H hH h ⟨b, hbV⟩ i.1⟩
          have hfst :
              (H' hx').1 = ⟨b, hbV⟩ := by
            apply Subtype.ext
            simpa [hx', x] using congrArg Subtype.val
              (source_sheet_image_first_coordinate H hH H' hH' h ⟨b, hbV⟩ i.1)
          have htarget :
              H' hx' = (⟨b, hbV⟩, j) := by
            exact Prod.ext hfst (by simpa [hx', x] using (hφ ⟨b, hbV⟩ i.1).trans i.2)
          have hyfst :
              (H' ⟨y', by simpa [hy'b] using hbV⟩).1 = ⟨b, hbV⟩ := by
            apply Subtype.ext
            simpa [hH' ⟨y', by simpa [hy'b] using hbV⟩, hy'b]
          have hy' :
              H' ⟨y', by simpa [hy'b] using hbV⟩ = (⟨b, hbV⟩, j) :=
            Prod.ext hyfst hj
          have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
            apply H'.injective
            exact htarget.trans hy'.symm
          simpa [toFun, x, hx'] using congrArg Subtype.val hsub
      continuous_invFun := by
        have hxV :
            ∀ x : h.left ⁻¹' ({y'} : Set E'),
              p x.1 ∈ V := by
          intro x
          have hxb : p x.1 = b := by
            calc
              p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
              _ = p' y' := by simpa using congrArg p' x.2
              _ = b := hy'b
          simpa [hxb] using hbV
        have hBase :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') => x.1 := by
          exact continuous_subtype_val
        have hLift :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
              (⟨x.1, hxV x⟩ : p ⁻¹' V) := by
          exact Continuous.subtype_mk hBase hxV
        have hSecond :
            Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
              (H ⟨x.1, hxV x⟩).2 := by
          have hComp :
              Continuous fun x : h.left ⁻¹' ({y'} : Set E') =>
                H ⟨x.1, hxV x⟩ := H.continuous.comp hLift
          exact continuous_snd.comp hComp
        exact Continuous.subtype_mk hSecond fun x ↦ by
          let hxb : p x.1 = b := by
            calc
              p x.1 = p' (h.left.hom x.1) := (covering_space_hom_comm h x.1).symm
              _ = p' y' := by simpa using congrArg p' x.2
              _ = b := hy'b
          let xV' : p ⁻¹' V := ⟨x.1, hxV x⟩
          let i : p ⁻¹' ({b} : Set B) := (H xV').2
          have hxBack : H.symm ((H xV').1, (H xV').2) = xV' := by
            simpa [i] using H.symm_apply_apply xV'
          have hxBackVal : (H.symm ((H xV').1, i)).1 = x.1 := by
            exact congrArg Subtype.val hxBack
          let hx' : p' ⁻¹' V :=
            ⟨h.left.hom ((H.symm ((H xV').1, i)).1),
              source_sheet_image_mem_common_neighborhood H hH h (H xV').1 i⟩
          have hsub : hx' = ⟨y', by simpa [hy'b] using hbV⟩ := by
            apply Subtype.ext
            simpa [hx', hxBackVal] using x.2
          have hsnd : (H' hx').2 = j := by
            exact (congrArg Prod.snd (congrArg H' hsub)).trans hj
          simpa [invFun, hxb, i, xV', hxBackVal, hx'] using
            (hφ (H xV').1 i).symm.trans hsnd }⟩

/-- Helper for Lemma 3.7.5: over the chosen target sheet, `h.left` is explicitly a product of the
sheet and the restricted source-sheet index set. -/
-- We reuse the previously identified restricted preimage over the sheet and transport the first
-- factor from `V` to the actual target sheet inside `E'`.
private theorem chosen_target_sheet_trivialization
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (j : p' ⁻¹' ({b} : Set B))
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    ∃ Hh :
      h.left ⁻¹' (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ≃ₜ
        (Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }) ×
          { i : p ⁻¹' ({b} : Set B) // φ i = j },
      ∀ x, (Hh x).1.1 = h.left x := by
  -- Route correction: we keep the sheet-based proof, but separate the restricted-preimage
  -- coordinates from the target-sheet transport instead of expanding the whole composite at once.
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  rcases preimage_target_sheet_homeomorph_common_neighborhood H hH H' h j φ hφ with
    ⟨Hpre, hHpre⟩
  rcases target_sheet_homeomorph_common_neighborhood H' j with ⟨eW, heW⟩
  let Hh :
      (h.left ⁻¹' W) ≃ₜ W × { i : p ⁻¹' ({b} : Set B) // φ i = j } :=
    Hpre.trans (Homeomorph.prodCongr eW (Homeomorph.refl _))
  refine ⟨Hh, ?_⟩
  intro x
  -- The composed trivialization first reads the `V`-coordinate from the source chart and then
  -- reparameterizes that coordinate by the chosen target-sheet homeomorphism.
  change ((eW (Hpre x).1 : W) : E') = h.left x
  rw [hHpre x]
  exact chosen_target_sheet_image_eq H hH H' hH' h j φ hφ eW heW x

/-- Helper for Lemma 3.7.5: the chosen target sheet through `y'` is an evenly covered
neighborhood for `h.left`. -/
-- We first trivialize `h.left` over the chosen sheet using the restricted sheet-index set, then
-- replace that index set by the actual fiber over `y'`.
private theorem chosen_target_sheet_isEvenlyCovered
    {p : C(E, B)} {p' : C(E', B)} {b : B} {V : Set B}
    [DiscreteTopology (p ⁻¹' ({b} : Set B))]
    [DiscreteTopology (p' ⁻¹' ({b} : Set B))]
    (hbV : b ∈ V)
    (hpreVOpen' : IsOpen (p' ⁻¹' V))
    (H : p ⁻¹' V ≃ₜ V × (p ⁻¹' ({b} : Set B)))
    (hH : ∀ x, (H x).1.1 = p x)
    (H' : p' ⁻¹' V ≃ₜ V × (p' ⁻¹' ({b} : Set B)))
    (hH' : ∀ y, (H' y).1.1 = p' y)
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p'))
    (y' : E') (hy'b : p' y' = b)
    (j : p' ⁻¹' ({b} : Set B))
    (hj : (H' ⟨y', by simpa [hy'b] using hbV⟩).2 = j)
    (φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B))
    (hφ :
      ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
        (H' ⟨h.left.hom ((H.symm (u, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i) :
    IsEvenlyCovered h.left y' (h.left ⁻¹' ({y'} : Set E')) := by
  let W : Set E' := Set.image (Subtype.val : p' ⁻¹' V → E') { y | (H' y).2 = j }
  let T : Type u := { i : p ⁻¹' ({b} : Set B) // φ i = j }
  rcases chosen_target_sheet_trivialization H hH H' hH' h j φ hφ with ⟨Hh, hHh⟩
  classical
  let hFiber :=
    Classical.choice
      (sheet_index_homeomorph_covering_space_hom_fiber hbV H hH H' hH' h y' hy'b j hj φ hφ)
  have hy'W : y' ∈ W := by
    refine ⟨⟨y', by simpa [hy'b] using hbV⟩, ?_, rfl⟩
    simpa [hj]
  have hWOpen : IsOpen W := target_sheet_isOpen hpreVOpen' H' j
  have hpreWOpen : IsOpen (h.left ⁻¹' W) := hWOpen.preimage h.left.hom.continuous
  have hEvenlyCoveredT : IsEvenlyCovered h.left y' T := by
    refine ⟨inferInstance, W, hy'W, hWOpen, hpreWOpen, Hh, hHh⟩
  simpa [T] using hEvenlyCoveredT.of_fiber_homeomorph hFiber

/-- Lemma 3.7.5: under the standing hypotheses of this chapter, a morphism of connected
locally path-connected covering spaces over `B` is itself a covering map between the total
spaces. -/
-- Proof sketch: the algebraic analogue gives surjectivity. Fundamental neighborhoods for both
-- covers give fundamental neighborhoods for `h.left` by taking components of inverse images in
-- `E'` of neighborhoods of `B` that are fundamental for both `p` and `p'`.
theorem coveringSpaceHom_isCoveringMap
    {p : C(E, B)} {p' : C(E', B)}
    (hp : IsPathConnectedCoveringMap p) (hp' : IsPathConnectedCoveringMap p')
    (h : Over.mk (TopCat.ofHom p) ⟶ Over.mk (TopCat.ofHom p')) :
    IsPathConnectedCoveringMap h.left := by
  have hsurj : Function.Surjective h.left := covering_space_hom_surjective hp hp' h
  have hcov : IsCoveringMap h.left := by
    intro y'
    let b : B := p' y'
    rcases hp.2 b with ⟨hdisc, U, hbU, hUOpen, hUPath, hpreUOpen, HU, hHU⟩
    rcases hp'.2 b with ⟨hdisc', U', hbU', hU'Open, hU'Path, hpreU'Open, HU', hHU'⟩
    let V : Set B := pathComponentIn (U ∩ U') b
    have hVSubsetInter : V ⊆ U ∩ U' := pathComponentIn_subset
    have hVSubsetU : V ⊆ U := fun x hx ↦ (hVSubsetInter hx).1
    have hVSubsetU' : V ⊆ U' := fun x hx ↦ (hVSubsetInter hx).2
    have hbInter : b ∈ U ∩ U' := ⟨hbU, hbU'⟩
    have hbV : b ∈ V := mem_pathComponentIn_self hbInter
    have hVOpen : IsOpen V := (hUOpen.inter hU'Open).pathComponentIn b
    have hVPath : IsPathConnected V := isPathConnected_pathComponentIn hbInter
    have hFundV : IsFundamentalNeighborhood p b V :=
      fundamental_neighborhood_restrict
        ⟨hdisc, hbU, hUOpen, hUPath, hpreUOpen, HU, hHU⟩
        hVSubsetU hbV hVOpen hVPath
    have hFundV' : IsFundamentalNeighborhood p' b V :=
      fundamental_neighborhood_restrict
        ⟨hdisc', hbU', hU'Open, hU'Path, hpreU'Open, HU', hHU'⟩
        hVSubsetU' hbV hVOpen hVPath
    rcases hFundV with ⟨hdiscV, _, _, _, hpreVOpen, H, hH⟩
    rcases hFundV' with ⟨hdiscV', _, _, _, hpreVOpen', H', hH'⟩
    letI : DiscreteTopology (p ⁻¹' ({b} : Set B)) := hdiscV
    letI : DiscreteTopology (p' ⁻¹' ({b} : Set B)) := hdiscV'
    let u₀ : V := ⟨b, hbV⟩
    let j : p' ⁻¹' ({b} : Set B) :=
      (H' ⟨y', by
        have hyb : p' y' = b := rfl
        show p' y' ∈ V
        simpa [b] using hbV⟩).2
    let φ : p ⁻¹' ({b} : Set B) → p' ⁻¹' ({b} : Set B) :=
      fun i ↦
        (H' ⟨h.left.hom ((H.symm (u₀, i)).1),
          source_sheet_image_mem_common_neighborhood H hH h u₀ i⟩).2
    have hφ :
        ∀ u : V, ∀ i : p ⁻¹' ({b} : Set B),
          (H' ⟨h.left.hom ((H.symm (u, i)).1),
            source_sheet_image_mem_common_neighborhood H hH h u i⟩).2 = φ i := by
      intro u i
      simpa [φ, u₀] using source_sheet_maps_to_single_target_sheet
        (hVPath := hVPath) H hH H' hH' h u₀ i u
    -- The chosen target sheet through `y'` carries the required local product structure.
    exact chosen_target_sheet_isEvenlyCovered
      (hbV := hbV) (hpreVOpen' := hpreVOpen') H hH H' hH' h y' rfl j
      (by simpa [j]) φ hφ
  -- Once `h.left` is a covering map and is surjective, the locally path-connected codomain `E'`
  -- upgrades it to a path-connected covering map in the sense of Definition 3.1.5.
  change IsPathConnectedCoveringMap h.left.hom
  exact IsCoveringMap.isPathConnectedCoveringMap (B := E')
    (show IsCoveringMap h.left.hom from hcov)
    (show Function.Surjective h.left.hom from hsurj)
