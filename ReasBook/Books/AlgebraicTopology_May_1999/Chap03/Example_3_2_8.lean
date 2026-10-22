/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Example_3_1_7
import AlgebraicTopology_May_1999.Chap03.Definition_3_2_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped TopCat

/-- Internal direct-subtype model of `S^n` as the unit sphere in `ℝ^(n+1)`. -/
private abbrev SphereModel (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- Helper for Example 3.2.8: the ambient Euclidean space of the sphere model has the expected
finite dimension. -/
private instance sphereModel_finrank_fact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨@finrank_euclideanSpace_fin ℝ _ (n + 1)⟩

/-- Helper for Example 3.2.8: the last coordinate unit vector lies on the concrete sphere model. -/
private theorem sphereModelNorthPole_mem (n : ℕ) :
    EuclideanSpace.single (Fin.last n) (1 : ℝ) ∈ SphereModel n := by
  -- The chosen vector has norm one, so it belongs to the unit sphere.
  simp [SphereModel]

/-- Helper for Example 3.2.8: a concrete basepoint on the sphere model. -/
private def sphereModelNorthPole (n : ℕ) : SphereModel n :=
  ⟨EuclideanSpace.single (Fin.last n) (1 : ℝ), sphereModelNorthPole_mem n⟩

/-- Helper for Example 3.2.8: the sphere model inherits local path connectedness from its manifold
charts. -/
private theorem sphereModel_locPathConnectedSpace
    (n : ℕ) : LocPathConnectedSpace (SphereModel n) := by
  -- The sphere carries the standard manifold structure with Euclidean model space.
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (SphereModel n) := inferInstance
  let _ : LocPathConnectedSpace (EuclideanSpace ℝ (Fin n)) := inferInstance
  exact ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin n)) (SphereModel n)

/-- The canonical sphere `S^n` is locally path connected. -/
theorem sphere_locPathConnectedSpace (n : ℕ) : LocPathConnectedSpace (𝕊 n) := by
  let _ : LocPathConnectedSpace (SphereModel n) := sphereModel_locPathConnectedSpace n
  exact Homeomorph.ulift.isOpenEmbedding.locPathConnectedSpace

instance (n : ℕ) : LocPathConnectedSpace (𝕊 n) :=
  sphere_locPathConnectedSpace n

/-- Helper for Example 3.2.8: `S^n` is path connected once `n ≥ 2`. -/
private theorem sphereModel_pathConnectedSpace_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (SphereModel n) := by
  -- Convert the dimension hypothesis into the rank hypothesis needed by `isPathConnected_sphere`.
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n + 1 := by
      omega
    simpa using hnat
  have hs : IsPathConnected (SphereModel n) := by
    simpa [SphereModel] using
      (isPathConnected_sphere
        hdim
        (0 : EuclideanSpace ℝ (Fin (n + 1)))
        (by norm_num : 0 ≤ (1 : ℝ)))
  exact isPathConnected_iff_pathConnectedSpace.mp hs

/-- `S^n` is path connected once `n ≥ 2`. -/
theorem sphere_pathConnectedSpace_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (𝕊 n) := by
  let _ : PathConnectedSpace (SphereModel n) := sphereModel_pathConnectedSpace_of_two_le hn
  exact Homeomorph.ulift.symm.surjective.pathConnectedSpace Homeomorph.ulift.symm.continuous

instance (n : ℕ) : LocPathConnectedSpace (RealProjectiveSpace n) := by
  dsimp [RealProjectiveSpace]
  infer_instance

/-- Helper for Example 3.2.8: a punctured sphere chart identifies the complement of one point
with Euclidean space. -/
private def sphereModel_punctured_homeomorph_euclidean (n : ℕ) (v : SphereModel n) :
    ({v}ᶜ : Set (SphereModel n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  -- Rewrite the source and target of `stereographic'` into the concrete punctured-sphere chart.
  let e : ({v}ᶜ : Set (SphereModel n)) ≃ₜ
      (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    have hsource : (stereographic' n v).source = {v}ᶜ := stereographic'_source v
    have htarget : (stereographic' n v).target = Set.univ := stereographic'_target v
    rw [← hsource, ← htarget]
    exact (stereographic' n v).toHomeomorphSourceTarget
  exact e.trans (Homeomorph.Set.univ _)

/-- Helper for Example 3.2.8: every punctured sphere chart is contractible because it is
homeomorphic to Euclidean space. -/
private theorem sphereModel_punctured_contractible (n : ℕ) (v : SphereModel n) :
    ContractibleSpace ({v}ᶜ : Set (SphereModel n)) := by
  -- Transport contractibility across the stereographic homeomorphism.
  exact (sphereModel_punctured_homeomorph_euclidean n v).contractibleSpace

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Example 3.2.8: the stereographic chart with pole `v` sends the antipode `-v` to
the origin. -/
private theorem sphereModel_stereographic_antipode_eq_zero (n : ℕ) (v : SphereModel n) :
    stereographic' n v (-v) = 0 := by
  -- This is the standard stereographic-projection normalization at the opposite pole.
  have h : stereographic' n (-(-v)) (-v) = 0 := by
    dsimp [stereographic']
    simp only [EmbeddingLike.map_eq_zero_iff]
    exact stereographic_neg_apply (-v)
  simpa using h

/-- Helper for Example 3.2.8: removing a point and its antipode from the sphere model gives a
space homeomorphic to punctured Euclidean space. -/
private def sphereModel_doublePunctured_homeomorph_punctured_euclidean
    (n : ℕ) (v : SphereModel n) :
    ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) ≃ₜ
      ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  let e := stereographic' n v
  have hs :
      ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) ⊆ e.source := by
    -- The double-punctured set is contained in the source complement `{v}ᶜ`.
    intro x hx
    rw [stereographic'_source]
    exact hx.1
  have himage :
      e '' ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) =
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hzero
      have hvsource : (-v : SphereModel n) ∈ e.source := by
        rw [stereographic'_source]
        simpa [eq_comm] using (ne_neg_of_mem_unit_sphere ℝ v)
      have hxeq : x = -v := by
        have hxsource : x ∈ e.source := by
          rw [stereographic'_source]
          exact hx.1
        calc
          x = e.symm (e x) := by
            exact (e.left_inv hxsource).symm
          _ = e.symm 0 := by rw [hzero]
          _ = -v := by
            rw [← sphereModel_stereographic_antipode_eq_zero n v]
            exact e.left_inv hvsource
      exact hx.2 hxeq
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hy
      have hytarget : y ∈ e.target := by
        rw [stereographic'_target]
        simp
      have hsrc : e.symm y ∈ e.source := e.map_target hytarget
      have hneq_v : e.symm y ≠ v := by
        rw [stereographic'_source] at hsrc
        exact hsrc
      have hmap : e (e.symm y) = y := e.right_inv hytarget
      refine ⟨e.symm y, ⟨hneq_v, ?_⟩, hmap⟩
      intro hxneg
      have hyzero : y = 0 := by
        calc
          y = e (e.symm y) := hmap.symm
          _ = e (-v) := by rw [hxneg]
          _ = 0 := sphereModel_stereographic_antipode_eq_zero n v
      exact hy hyzero
  -- Restrict the stereographic chart to the complement of the antipode.
  exact e.homeomorphOfImageSubsetSource hs himage

/-- Helper for Example 3.2.8: the overlap of the two antipodal puncture charts is path connected
as soon as `n ≥ 2`. -/
private theorem sphereModel_overlap_pathConnected_of_two_le {n : ℕ} (hn : 2 ≤ n)
    (v : SphereModel n) :
    PathConnectedSpace ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
  have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) := by
    -- The Euclidean chart has dimension `n`, and `n ≥ 2` gives the rank bound.
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n := by
      omega
    simpa using hnat
  have htarget :
      IsPathConnected ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
        Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  let _ :
      PathConnectedSpace ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
        Set (EuclideanSpace ℝ (Fin n))) :=
    isPathConnected_iff_pathConnectedSpace.mp htarget
  let h :=
    sphereModel_doublePunctured_homeomorph_punctured_euclidean n v
  have hdomain :
      IsPathConnected ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
    -- Push forward the punctured Euclidean connectedness through the restricted chart.
    let f :
        ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n))) →
          SphereModel n :=
      fun y ↦ (h.symm y : ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)))
    have hf : Continuous f := continuous_subtype_val.comp h.symm.continuous
    have himage :
        f '' (Set.univ :
          Set ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ : Set (EuclideanSpace ℝ (Fin n)))) =
          ({v}ᶜ ∩ {-v}ᶜ : Set (SphereModel n)) := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact (h.symm y).2
      · intro hx
        refine ⟨h ⟨x, hx⟩, Set.mem_univ _, ?_⟩
        simp [f]
    have himage_path :
        IsPathConnected
          (f '' (Set.univ :
            Set ({(0 : EuclideanSpace ℝ (Fin n))}ᶜ :
              Set (EuclideanSpace ℝ (Fin n))))) :=
      isPathConnected_univ.image hf
    rw [himage] at himage_path
    exact himage_path
  exact isPathConnected_iff_pathConnectedSpace.mp hdomain

/-- Helper for Example 3.2.8: the concrete sphere model of `S^n` is simply connected for `n ≥ 2`.
-/
private theorem sphereModel_simplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (SphereModel n) := by
  -- Route correction: replace the missing global sphere theorem by the two-chart van Kampen proof.
  let v : SphereModel n := sphereModelNorthPole n
  let U : TopologicalSpace.Opens (TopCat.of (SphereModel n)) := ⟨{v}ᶜ, isOpen_compl_singleton⟩
  let V : TopologicalSpace.Opens (TopCat.of (SphereModel n)) := ⟨{-v}ᶜ, isOpen_compl_singleton⟩
  have hU : ContractibleSpace U := by
    -- Each punctured chart is Euclidean, hence contractible.
    simpa [U] using sphereModel_punctured_contractible n v
  have hV : ContractibleSpace V := by
    -- The same contractibility argument applies to the opposite puncture chart.
    simpa [V] using sphereModel_punctured_contractible n (-v)
  let _ : ContractibleSpace U := hU
  let _ : ContractibleSpace V := hV
  let _ : PathConnectedSpace U := by infer_instance
  let _ : SimplyConnectedSpace V := by infer_instance
  let _ : PathConnectedSpace ↥(U ⊓ V) := by
    -- The overlap is punctured Euclidean space, so it stays path connected for `n ≥ 2`.
    simpa [U, V, TopologicalSpace.Opens.coe_inf] using
      sphereModel_overlap_pathConnected_of_two_le hn v
  let _ : PathConnectedSpace (SphereModel n) := sphereModel_pathConnectedSpace_of_two_le hn
  have hcover : U ⊔ V = ⊤ := by
    -- No sphere point can equal both `v` and `-v`, so the two puncture complements cover.
    ext x
    constructor
    · intro _
      simp
    · intro _
      by_cases hx : x = v
      · right
        simpa [hx, eq_comm] using (ne_neg_of_mem_unit_sphere ℝ v)
      · left
        exact hx
  let x : ↥(U ⊓ V) := Classical.choice (PathConnectedSpace.nonempty : Nonempty ↥(U ⊓ V))
  have hsurj :
      Function.Surjective (FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom
        ⟨x.1, x.2.1⟩) :=
    fundamental_group_left_to_union_surjective U V hcover x.1 x.2.1 x.2.2
  have hsub_U :
      Subsingleton (FundamentalGroup U ⟨x.1, x.2.1⟩) := by
    -- Contractibility of the left chart trivializes its based fundamental group.
    let xU : U := ⟨x.1, x.2.1⟩
    change Subsingleton (Path.Homotopic.Quotient xU xU)
    infer_instance
  have hsub_base : Subsingleton (FundamentalGroup (SphereModel n) x.1) := by
    -- Surjectivity from the contractible chart forces the ambient based loop group to be trivial.
    refine ⟨fun γ δ ↦ ?_⟩
    rcases hsurj γ with ⟨γU, rfl⟩
    rcases hsurj δ with ⟨δU, rfl⟩
    exact congrArg
      (FundamentalGroup.map (TopologicalSpace.Opens.inclusion' U).hom ⟨x.1, x.2.1⟩)
      (@Subsingleton.elim _ hsub_U γU δU)
  have hsub_all : ∀ y : SphereModel n, Subsingleton (FundamentalGroup (SphereModel n) y) :=
    fun y ↦ by
      let e : FundamentalGroup (SphereModel n) x.1 ≃* FundamentalGroup (SphereModel n) y :=
        FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x.1 y
      let _ : Subsingleton (FundamentalGroup (SphereModel n) x.1) := hsub_base
      refine ⟨fun γ δ ↦ ?_⟩
      have hpre : e.symm γ = e.symm δ := Subsingleton.elim _ _
      simpa using congrArg e hpre
  -- Convert triviality of every based loop group into null-homotopy of every loop.
  rw [simply_connected_iff_loops_nullhomotopic]
  refine ⟨inferInstance, ?_⟩
  intro y γ
  let _ : Subsingleton (FundamentalGroup (SphereModel n) y) := hsub_all y
  have h :
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) :
        FundamentalGroup (SphereModel n) y) = 1 := by
    exact Subsingleton.elim _ _
  rw [show (1 : FundamentalGroup (SphereModel n) y) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (Path.refl y)) by rfl] at h
  exact Path.Homotopic.Quotient.eq.mp h

/-- `S^n` is simply connected for `n ≥ 2`. -/
theorem sphere_simplyConnected_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    SimplyConnectedSpace (𝕊 n) := by
  let _ : SimplyConnectedSpace (SphereModel n) := sphereModel_simplyConnected_of_two_le hn
  exact Homeomorph.ulift.toHomotopyEquiv.simplyConnectedSpace

/-- Example 3.2.8: for `n ≥ 2`, the antipodal quotient map from `S^n` to `RP^n` is a universal
covering map. -/
-- Proof sketch: upgrade the antipodal quotient map to a covering map in the sense of Definition
-- 3.1.5 by combining quotient surjectivity with path-connected evenly covered neighborhoods, then
-- use the standard fact that `S^n` is simply connected for `n ≥ 2`.
theorem sphereToRealProjectiveSpace_isUniversalCoveringMap {n : ℕ} (hn : 2 ≤ n) :
    IsUniversalCoveringMap (sphereToRealProjectiveSpace n) := by
  have _ : PathConnectedSpace ↥(TopCat.sphere.{0} n) := by
    simpa using sphere_pathConnectedSpace_of_two_le hn
  refine ⟨?_, sphere_simplyConnected_of_two_le hn⟩
  -- Upgrade the covering-map statement to the textbook path-connected version.
  exact
    IsCoveringMap.isPathConnectedCoveringMap
      (sphereToRealProjectiveSpace_isCoveringMap n)
      (by
        simpa [sphereToRealProjectiveSpace] using
          (Quotient.mk''_surjective :
            Function.Surjective
              (Quotient.mk'' : 𝕊 n → RealProjectiveSpace n)))
