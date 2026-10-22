/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section20_part14
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part6

section Chap04
section Section21

/-- Helper for Text 21.3.3: in `Fin n → ℝ`, boundedness is equivalent to trivial recession
cone for nonempty closed convex sets. -/
lemma helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
    {n : ℕ}
    (S : Set (Fin n → ℝ))
    (hSne : S.Nonempty)
    (hSclosed : IsClosed S)
    (hSconv : Convex ℝ S) :
    Bornology.IsBounded S ↔ Set.recessionCone S = ({0} : Set (Fin n → ℝ)) := by
  let e := EuclideanSpace.equiv (Fin n) ℝ
  let S' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' S
  -- Transport nonemptiness/closedness/convexity to Euclidean coordinates.
  have hS'ne : S'.Nonempty := by
    rcases hSne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    refine ⟨x, hx, ?_⟩
    simp
  have hS'closed : IsClosed S' := by
    simpa [S'] using (Homeomorph.isClosed_image e.symm.toHomeomorph).2 hSclosed
  have hS'conv : Convex ℝ S' := by
    simpa [S'] using
      (Convex.linear_image hSconv
        (e.symm.toLinearEquiv : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)))
  have hImageS : e '' S' = S := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      rcases hy with ⟨z, hz, hyz⟩
      have hzEq : z = x := by
        calc
          z = e (e.symm z) := by simp
          _ = e y := by simpa [hyz]
          _ = x := hyx
      simpa [hzEq] using hz
    · intro hx
      refine ⟨e.symm x, ?_, ?_⟩
      · refine ⟨x, hx, ?_⟩
        simp
      · simp
  have hRecEq : Set.recessionCone S = e '' Set.recessionCone S' := by
    have hEq := recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := S')
    simpa [hImageS] using hEq
  have hZeroImage : e '' ({0} : Set (EuclideanSpace ℝ (Fin n))) = ({0} : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨x, hx, hxy⟩
      have hx0 : x = 0 := by
        simpa [Set.mem_singleton_iff] using hx
      subst hx0
      simp at hxy
      simpa [hxy]
    · intro hy
      have hy0 : y = 0 := by
        simpa [Set.mem_singleton_iff] using hy
      subst hy0
      refine ⟨0, ?_, ?_⟩
      · simp
      · simp
  constructor
  · intro hSbdd
    -- Push boundedness to Euclidean coordinates, apply the Euclidean theorem, then pull back.
    have hS'bounded : Bornology.IsBounded S' := by
      simpa [S'] using (e.symm.lipschitz.isBounded_image hSbdd)
    have hRecS' : Set.recessionCone S' = ({0} : Set (EuclideanSpace ℝ (Fin n))) :=
      (bounded_iff_recessionCone_eq_singleton_zero (C := S') hS'ne hS'closed hS'conv).1 hS'bounded
    calc
      Set.recessionCone S = e '' Set.recessionCone S' := hRecEq
      _ = e '' ({0} : Set (EuclideanSpace ℝ (Fin n))) := by simp [hRecS']
      _ = ({0} : Set (Fin n → ℝ)) := hZeroImage
  · intro hRecS
    -- Pull the recession equality into Euclidean coordinates, then transfer boundedness back.
    have hRecEqSymm : Set.recessionCone S' = e.symm '' Set.recessionCone S := by
      simpa [S'] using recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := S)
    have hZeroImageSymm :
        e.symm '' ({0} : Set (Fin n → ℝ)) = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, hx, hxy⟩
        have hx0 : x = 0 := by
          simpa [Set.mem_singleton_iff] using hx
        subst hx0
        simp at hxy
        simpa [hxy]
      · intro hy
        have hy0 : y = 0 := by
          simpa [Set.mem_singleton_iff] using hy
        subst hy0
        refine ⟨0, ?_, ?_⟩
        · simp
        · simp
    have hRecS' : Set.recessionCone S' = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
      calc
        Set.recessionCone S' = e.symm '' Set.recessionCone S := hRecEqSymm
        _ = e.symm '' ({0} : Set (Fin n → ℝ)) := by simp [hRecS]
        _ = ({0} : Set (EuclideanSpace ℝ (Fin n))) := hZeroImageSymm
    have hS'bounded : Bornology.IsBounded S' :=
      (bounded_iff_recessionCone_eq_singleton_zero (C := S') hS'ne hS'closed hS'conv).2 hRecS'
    have hSboundedImage : Bornology.IsBounded (e '' S') := e.lipschitz.isBounded_image hS'bounded
    simpa [hImageS] using hSboundedImage

/-- Helper for Text 21.3.3: the recession cone of a finite intersection is the intersection
of recession cones in `Fin n → ℝ` under nonempty closed convex hypotheses. -/
lemma helperForText_21_3_3_recessionFiniteInter_eq_finiteRecessionInter
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (t : Finset I)
    (htne : (t : Set I).Nonempty)
    (hClosed : ∀ i ∈ t, IsClosed (C i))
    (hConv : ∀ i ∈ t, Convex ℝ (C i))
    (hNonemptyInter : (⋂ i : ↑(t : Set I), C i.1).Nonempty) :
    Set.recessionCone (⋂ i ∈ t, C i) = ⋂ i ∈ t, Set.recessionCone (C i) := by
  let _ := htne
  -- Route correction: switch to subtype-indexed `iInter` so part6 applies directly.
  have hClosedSubtype : ∀ i : ↑(t : Set I), IsClosed (C i.1) := by
    intro i
    exact hClosed i.1 i.2
  have hConvSubtype : ∀ i : ↑(t : Set I), Convex ℝ (C i.1) := by
    intro i
    exact hConv i.1 i.2
  have hRecSubtype :
      Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) =
        ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) :=
    helperForText_21_3_3_recessionCone_iInter_eq_iInter_fin
      (C := fun i : ↑(t : Set I) => C i.1) hClosedSubtype hConvSubtype hNonemptyInter
  have hInterEq : (⋂ i : ↑(t : Set I), C i.1) = (⋂ i ∈ t, C i) := by
    ext x
    simp
  have hRecInterEq :
      (⋂ i : ↑(t : Set I), Set.recessionCone (C i.1)) =
        (⋂ i ∈ t, Set.recessionCone (C i)) := by
    ext x
    simp
  -- Convert back to finite-intersection notation.
  calc
    Set.recessionCone (⋂ i ∈ t, C i) = Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) := by
      rw [hInterEq]
    _ = ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) := hRecSubtype
    _ = ⋂ i ∈ t, Set.recessionCone (C i) := hRecInterEq

/-- Helper for Text 21.3.3: compactness on the unit sphere yields a finite recession
subfamily already forcing intersection `{0}`. -/
lemma helperForText_21_3_3_finite_recession_subfamily_of_global_singleton
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hClosed : ∀ i, IsClosed (C i))
    (hNoCommon : (⋂ i : I, Set.recessionCone (C i)) = ({0} : Set (Fin n → ℝ))) :
    ∃ t : Finset I, (⋂ i ∈ t, Set.recessionCone (C i)) = ({0} : Set (Fin n → ℝ)) := by
  classical
  let sphereOne : Set (Fin n → ℝ) := Metric.sphere (0 : Fin n → ℝ) 1
  -- The global `{0}` condition excludes unit vectors in the total recession intersection.
  have hSphereInterEmpty : sphereOne ∩ (⋂ i : I, Set.recessionCone (C i)) = (∅ : Set (Fin n → ℝ)) := by
    refine Set.eq_empty_iff_forall_notMem.2 ?_
    intro x hx
    rcases hx with ⟨hxSphere, hxInter⟩
    have hxZeroSet : x ∈ ({0} : Set (Fin n → ℝ)) := by
      simpa [hNoCommon] using hxInter
    have hx0 : x = 0 := by
      simpa [Set.mem_singleton_iff] using hxZeroSet
    have hNormEq : ‖x‖ = 1 := by
      simpa [sphereOne, Metric.sphere, dist_eq_norm] using hxSphere
    have : (0 : ℝ) = 1 := by
      simpa [hx0] using hNormEq
    norm_num at this
  have hClosedRec : ∀ i : I, IsClosed (Set.recessionCone (C i)) := by
    intro i
    exact helperForText_21_3_3_recessionCone_isClosed_fin (S := C i) (hClosed i)
  have hcompact : IsCompact sphereOne := by
    simpa [sphereOne] using (isCompact_sphere (0 : Fin n → ℝ) (1 : ℝ))
  rcases hcompact.elim_finite_subfamily_closed
      (t := fun i : I => Set.recessionCone (C i)) hClosedRec hSphereInterEmpty with ⟨u, huEmpty⟩
  refine ⟨u, ?_⟩
  apply Set.Subset.antisymm
  · intro d hd
    by_cases hd0 : d = 0
    · simpa [hd0]
    · have hnormPos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
      have hInvPos : 0 < ‖d‖⁻¹ := inv_pos.mpr hnormPos
      have hNormedMemFinite : (‖d‖⁻¹ : ℝ) • d ∈ ⋂ i ∈ u, Set.recessionCone (C i) := by
        refine Set.mem_iInter₂.mpr ?_
        intro i hi
        have hdi : d ∈ Set.recessionCone (C i) := (Set.mem_iInter₂.mp hd) i hi
        exact recessionCone_smul_pos_fin hdi hInvPos
      have hNormedOnSphere : (‖d‖⁻¹ : ℝ) • d ∈ sphereOne := by
        have hnormNe : ‖d‖ ≠ 0 := ne_of_gt hnormPos
        have hmul : ‖d‖⁻¹ * ‖d‖ = 1 := by
          exact inv_mul_cancel₀ hnormNe
        have hnormEq : ‖(‖d‖⁻¹ : ℝ) • d‖ = 1 := by
          calc
            ‖(‖d‖⁻¹ : ℝ) • d‖ = ‖(‖d‖⁻¹ : ℝ)‖ * ‖d‖ := by
              simpa using norm_smul (‖d‖⁻¹ : ℝ) d
            _ = ‖d‖⁻¹ * ‖d‖ := by simp
            _ = 1 := hmul
        simpa [sphereOne, Metric.sphere, dist_eq_norm] using hnormEq
      have hNormedMemInter : (‖d‖⁻¹ : ℝ) • d ∈ sphereOne ∩ (⋂ i ∈ u, Set.recessionCone (C i)) :=
        ⟨hNormedOnSphere, hNormedMemFinite⟩
      have hFalse : False := by
        simpa [huEmpty] using hNormedMemInter
      exact False.elim hFalse
  · intro d hd
    have hd0 : d = 0 := by
      simpa [Set.mem_singleton_iff] using hd
    subst hd0
    refine Set.mem_iInter₂.mpr ?_
    intro i hi x hx t ht
    simpa using hx

/-- A family of sets in `ℝⁿ` has no common direction of recession when the intersection of
their recession cones is exactly `{0}`. -/
def HasNoCommonRecessionDirection
    {n : ℕ} {I : Type*} (C : I → Set (Fin n → ℝ)) : Prop :=
  (⋂ i : I, Set.recessionCone (C i)) = ({0} : Set (Fin n → ℝ))

/-- A family of sets in `ℝⁿ` has a bounded finite subintersection when some finite
subfamily has nonempty bounded intersection. -/
def ExistsBoundedFiniteSubintersection
    {n : ℕ} {I : Type*} (C : I → Set (Fin n → ℝ)) : Prop :=
  ∃ t : Finset I, (⋂ i ∈ t, C i).Nonempty ∧ Bornology.IsBounded (⋂ i ∈ t, C i)

-- Proof sketch: Use the finite-dimensional recession-cone characterization of bounded closed
-- convex sets and the formula for recession cones of finite intersections; then combine with
-- compactness/Helly-type finite reduction to pass between a global recession condition and the
-- existence of one bounded finite subintersection. The final implication follows since
-- `recessionCone (C i) = {0}` for a bounded closed convex set and the global intersection is
-- contained in each `recessionCone (C i)`.
/-- Text 21.3.3: Let `(C i) (i ∈ I)` be a family of nonempty closed convex subsets of `ℝⁿ`
satisfying the finite intersection property `⋂ i ∈ t, C i ≠ ∅` for every finite `t`.
Then the following are equivalent: (a) `⋂ i, recessionCone (C i) = {0}`; (b) there exists
a finite subset `t` such that `⋂ i ∈ t, C i` is nonempty and bounded. In particular, if one
set `C i` is bounded, then `⋂ i, recessionCone (C i) = {0}`. -/
theorem theorem21_3_3_no_common_recession_iff_bounded_finite_subintersection
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hClosed : ∀ i, IsClosed (C i))
    (hConv : ∀ i, Convex ℝ (C i))
    (hNonemptyAll : ∀ i, (C i).Nonempty)
    (hFiniteInterNonempty : ∀ t : Finset I, (⋂ i ∈ t, C i).Nonempty) :
    (HasNoCommonRecessionDirection C ↔ ExistsBoundedFiniteSubintersection C) ∧
    ((∃ i : I, Bornology.IsBounded (C i)) → HasNoCommonRecessionDirection C) := by
  classical
  -- Build closed/convex facts for finite intersections once for reuse.
  have hFiniteClosed : ∀ t : Finset I, IsClosed (⋂ i ∈ t, C i) := by
    intro t
    have hSetEq : ({x : Fin n → ℝ | ∀ i ∈ t, x ∈ C i} : Set (Fin n → ℝ)) = (⋂ i ∈ t, C i) := by
      ext x
      simp
    rw [← hSetEq]
    exact helperForText_21_3_3_isClosed_finiteIntersection (C := C) hClosed t
  have hFiniteConvex : ∀ t : Finset I, Convex ℝ (⋂ i ∈ t, C i) := by
    intro t
    have hSetEq : ({x : Fin n → ℝ | ∀ i ∈ t, x ∈ C i} : Set (Fin n → ℝ)) = (⋂ i ∈ t, C i) := by
      ext x
      simp
    rw [← hSetEq]
    exact helperForText_21_3_3_convex_finiteIntersection (C := C) hConv t
  have hNoCommonToExists :
      HasNoCommonRecessionDirection C → ExistsBoundedFiniteSubintersection C := by
    intro hNoCommon
    -- Route correction: first extract a finite recession subfamily from compactness on the sphere.
    rcases helperForText_21_3_3_finite_recession_subfamily_of_global_singleton
        (C := C) hClosed hNoCommon with ⟨t, htRecFinite⟩
    have hNonemptyFinite : (⋂ i ∈ t, C i).Nonempty := hFiniteInterNonempty t
    have hNonemptySubtype : (⋂ i : ↑(t : Set I), C i.1).Nonempty := by
      simpa using hNonemptyFinite
    have hClosedSubtype : ∀ i : ↑(t : Set I), IsClosed (C i.1) := by
      intro i
      exact hClosed i.1
    have hConvSubtype : ∀ i : ↑(t : Set I), Convex ℝ (C i.1) := by
      intro i
      exact hConv i.1
    have hRecSubtype :
        Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) =
          ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) :=
      helperForText_21_3_3_recessionCone_iInter_eq_iInter_fin
        (C := fun i : ↑(t : Set I) => C i.1) hClosedSubtype hConvSubtype hNonemptySubtype
    have hInterEq : (⋂ i : ↑(t : Set I), C i.1) = (⋂ i ∈ t, C i) := by
      ext x
      simp
    have hRecInterEq :
        (⋂ i : ↑(t : Set I), Set.recessionCone (C i.1)) =
          (⋂ i ∈ t, Set.recessionCone (C i)) := by
      ext x
      simp
    have hRecFiniteInter :
        Set.recessionCone (⋂ i ∈ t, C i) = ({0} : Set (Fin n → ℝ)) := by
      calc
        Set.recessionCone (⋂ i ∈ t, C i) = Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) := by
          rw [hInterEq]
        _ = ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) := hRecSubtype
        _ = ⋂ i ∈ t, Set.recessionCone (C i) := hRecInterEq
        _ = ({0} : Set (Fin n → ℝ)) := htRecFinite
    have hBoundedFinite : Bornology.IsBounded (⋂ i ∈ t, C i) :=
      (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
        (S := (⋂ i ∈ t, C i)) hNonemptyFinite (hFiniteClosed t) (hFiniteConvex t)).2 hRecFiniteInter
    exact ⟨t, hNonemptyFinite, hBoundedFinite⟩
  have hExistsToNoCommon :
      ExistsBoundedFiniteSubintersection C → HasNoCommonRecessionDirection C := by
    intro hExists
    rcases hExists with ⟨t, hNonemptyFinite, hBoundedFinite⟩
    have hNonemptySubtype : (⋂ i : ↑(t : Set I), C i.1).Nonempty := by
      simpa using hNonemptyFinite
    have hClosedSubtype : ∀ i : ↑(t : Set I), IsClosed (C i.1) := by
      intro i
      exact hClosed i.1
    have hConvSubtype : ∀ i : ↑(t : Set I), Convex ℝ (C i.1) := by
      intro i
      exact hConv i.1
    have hRecFiniteEq :
        Set.recessionCone (⋂ i ∈ t, C i) = ⋂ i ∈ t, Set.recessionCone (C i) := by
      have hRecSubtype :
          Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) =
            ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) :=
        helperForText_21_3_3_recessionCone_iInter_eq_iInter_fin
          (C := fun i : ↑(t : Set I) => C i.1) hClosedSubtype hConvSubtype hNonemptySubtype
      have hInterEq : (⋂ i : ↑(t : Set I), C i.1) = (⋂ i ∈ t, C i) := by
        ext x
        simp
      have hRecInterEq :
          (⋂ i : ↑(t : Set I), Set.recessionCone (C i.1)) =
            (⋂ i ∈ t, Set.recessionCone (C i)) := by
        ext x
        simp
      calc
        Set.recessionCone (⋂ i ∈ t, C i) = Set.recessionCone (⋂ i : ↑(t : Set I), C i.1) := by
          rw [hInterEq]
        _ = ⋂ i : ↑(t : Set I), Set.recessionCone (C i.1) := hRecSubtype
        _ = ⋂ i ∈ t, Set.recessionCone (C i) := hRecInterEq
    have hRecFiniteSingleton :
        (⋂ i ∈ t, Set.recessionCone (C i)) = ({0} : Set (Fin n → ℝ)) := by
      have hRecFiniteInter :
          Set.recessionCone (⋂ i ∈ t, C i) = ({0} : Set (Fin n → ℝ)) :=
        (helperForText_21_3_3_bounded_iff_recessionCone_eq_singleton_zero_fin
          (S := (⋂ i ∈ t, C i)) hNonemptyFinite (hFiniteClosed t) (hFiniteConvex t)).1 hBoundedFinite
      calc
        (⋂ i ∈ t, Set.recessionCone (C i)) = Set.recessionCone (⋂ i ∈ t, C i) := by
          symm
          exact hRecFiniteEq
        _ = ({0} : Set (Fin n → ℝ)) := hRecFiniteInter
    -- Global recession intersection is contained in every finite subintersection.
    have hSubsetFinite :
        (⋂ i : I, Set.recessionCone (C i)) ⊆ (⋂ i ∈ t, Set.recessionCone (C i)) := by
      intro x hx
      refine Set.mem_iInter₂.mpr ?_
      intro i hi
      exact (Set.mem_iInter.mp hx) i
    have hSubsetZero :
        (⋂ i : I, Set.recessionCone (C i)) ⊆ ({0} : Set (Fin n → ℝ)) := by
      intro x hx
      have hxFinite : x ∈ (⋂ i ∈ t, Set.recessionCone (C i)) := hSubsetFinite hx
      simpa [hRecFiniteSingleton] using hxFinite
    have hZeroMemGlobal : (0 : Fin n → ℝ) ∈ (⋂ i : I, Set.recessionCone (C i)) := by
      refine Set.mem_iInter.mpr ?_
      intro i x hx s hs
      simpa using hx
    exact Set.Subset.antisymm hSubsetZero (Set.singleton_subset_iff.2 hZeroMemGlobal)
  have hIff : HasNoCommonRecessionDirection C ↔ ExistsBoundedFiniteSubintersection C :=
    ⟨hNoCommonToExists, hExistsToNoCommon⟩
  constructor
  · exact hIff
  · intro hBoundedOne
    rcases hBoundedOne with ⟨i, hiBounded⟩
    have hFiniteWitness : ExistsBoundedFiniteSubintersection C := by
      refine ⟨{i}, ?_, ?_⟩
      · simpa using hNonemptyAll i
      · simpa using hiBounded
    exact hExistsToNoCommon hFiniteWitness

/-- The first function in the `ℝ²` counterexample, represented on `Fin 2 → ℝ`. -/
noncomputable def text21_3_4_f1 (x : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (x 0 ^ 2 + 1) - x 1

/-- The second function in the `ℝ²` counterexample, represented on `Fin 2 → ℝ`. -/
noncomputable def text21_3_4_f2 (x : Fin 2 → ℝ) : ℝ :=
  Real.sqrt (x 1 ^ 2 + 1) - x 0

/-- The first convex inequality set from the two-function `ℝ²` counterexample. -/
def text21_3_4_set1 : Set (Fin 2 → ℝ) :=
  {x | text21_3_4_f1 x ≤ 0}

/-- The second convex inequality set from the two-function `ℝ²` counterexample. -/
def text21_3_4_set2 : Set (Fin 2 → ℝ) :=
  {x | text21_3_4_f2 x ≤ 0}

/-- Helper for Text 21.3.4: evaluating `f₁` on the vertical ray `t ↦ ![0, t]`. -/
lemma helperForText_21_3_4_f1_on_vertical_ray (t : ℝ) :
    text21_3_4_f1 (![0, t]) = 1 - t := by
  -- Unfold `f₁` and simplify each coordinate of `![0, t]`.
  unfold text21_3_4_f1
  simp [pow_two]

/-- Helper for Text 21.3.4: for each threshold `m`, the range of `f₁` contains a value below `m`. -/
lemma helperForText_21_3_4_exists_range_f1_below (m : ℝ) :
    ∃ y ∈ Set.range (fun x : Fin 2 → ℝ => text21_3_4_f1 x), y < m := by
  -- Route correction: use an explicit ray witness instead of abstract lower-bound search.
  refine ⟨text21_3_4_f1 (![0, |m| + 2]), ?_, ?_⟩
  · exact ⟨![0, |m| + 2], rfl⟩
  · -- Evaluate `f₁` on the chosen ray point and compare with `m`.
    have hEval : text21_3_4_f1 (![0, |m| + 2]) = 1 - (|m| + 2) := by
      simpa using helperForText_21_3_4_f1_on_vertical_ray (|m| + 2)
    have hNegAbsLe : -|m| ≤ m := by
      simpa using (neg_abs_le m)
    have hStrict : 1 - (|m| + 2) < m := by
      linarith
    simpa [hEval] using hStrict

/-- Helper for Text 21.3.4: `range f₁` is not bounded below. -/
lemma helperForText_21_3_4_not_bddBelow_range_f1 :
    ¬ BddBelow (Set.range (fun x : Fin 2 → ℝ => text21_3_4_f1 x)) := by
  intro hBddBelow
  rcases hBddBelow with ⟨m, hm⟩
  -- Pull a value in `range f₁` strictly below the claimed lower bound and contradict it.
  rcases helperForText_21_3_4_exists_range_f1_below m with ⟨y, hyMem, hyLt⟩
  have hLower : m ≤ y := hm hyMem
  linarith

/-- Helper for Text 21.3.4: the `(λ₁, λ₂) = (1,0)` objective equals `f₁` pointwise. -/
lemma helperForText_21_3_4_specialized_lagrangian_eq_f1 :
    (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x) =
      (fun x : Fin 2 → ℝ => text21_3_4_f1 x) := by
  -- Route correction: normalize the problematic specialization into the exact `range f₁` form.
  funext x
  simp

/-- Helper for Text 21.3.4: specializing the universal clause at `(1,0)` forces
`range f₁` to be bounded below. -/
lemma helperForText_21_3_4_specialization_forces_bddBelow_range_f1
    (hUniversal : ∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
      BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) :
    BddBelow (Set.range (fun x : Fin 2 → ℝ => text21_3_4_f1 x)) := by
  -- Specialize at the nonnegative pair `(lambda1, lambda2) = (1, 0)`.
  have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
  have hZeroNonneg : (0 : ℝ) ≤ 0 := by norm_num
  have hSpecialized :
      BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) = 0 :=
    hUniversal 1 0 hOneNonneg hZeroNonneg
  -- Rewrite the specialized objective into the exact `f₁` form.
  simpa [helperForText_21_3_4_specialized_lagrangian_eq_f1] using hSpecialized.1

/-- Helper for Text 21.3.4: the `(λ₁, λ₂) = (1,0)` Lagrangian objective is not bounded below. -/
lemma helperForText_21_3_4_not_bddBelow_specialized_lagrangian :
    ¬ BddBelow
      (Set.range
        (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) := by
  -- After rewriting, the claim is exactly the known unbounded-below fact for `range f₁`.
  simpa [helperForText_21_3_4_specialized_lagrangian_eq_f1] using
    helperForText_21_3_4_not_bddBelow_range_f1

/-- Helper for Text 21.3.4: the specialized `(λ₁, λ₂) = (1,0)` universal-clause output
is already contradictory at the bounded-below component. -/
lemma helperForText_21_3_4_specialized_pair_output_false :
    ¬ (BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) = 0) := by
  intro hSpecializedPair
  -- The contradiction is immediate from the first component.
  exact helperForText_21_3_4_not_bddBelow_specialized_lagrangian hSpecializedPair.1

/-- Helper for Text 21.3.4: the universal nonnegative-multiplier clause is false. -/
lemma helperForText_21_3_4_universal_multiplier_clause_false :
    ¬ (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
      BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) := by
  intro hUniversal
  -- Route correction: specialize directly at `(1,0)` and discharge by the dedicated refutation.
  have hSpecialized :
      BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => (1 : ℝ) * text21_3_4_f1 x + (0 : ℝ) * text21_3_4_f2 x)) = 0 := by
    have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
    have hZeroNonneg : (0 : ℝ) ≤ 0 := by norm_num
    exact hUniversal 1 0 hOneNonneg hZeroNonneg
  exact helperForText_21_3_4_specialized_pair_output_false hSpecialized

/-- Helper for Text 21.3.4: any inhabitant of the universal multiplier clause
immediately yields a contradiction. -/
lemma helperForText_21_3_4_universal_multiplier_clause_implies_false
    (hUniversal : ∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
      BddBelow
          (Set.range
            (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
        sInf
            (Set.range
              (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) :
    False := by
  -- Route correction: this packages the semantic contradiction as a reusable eliminator.
  exact helperForText_21_3_4_universal_multiplier_clause_false hUniversal

/-- Helper for Text 21.3.4: any proof of the full target conjunction forces
`range f₁` to be bounded below via the `(1,0)` specialization. -/
lemma helperForText_21_3_4_target_conjunction_forces_bddBelow_range_f1
    (hTarget : Convex ℝ text21_3_4_set1 ∧
      Convex ℝ text21_3_4_set2 ∧
        text21_3_4_set1 ∩ text21_3_4_set2 = (∅ : Set (Fin 2 → ℝ)) ∧
          (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
            BddBelow
                (Set.range
                  (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
              sInf
                  (Set.range
                    (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) ∧
            ((![1, 1] : Fin 2 → ℝ) ∈
              Set.recessionCone text21_3_4_set1 ∩ Set.recessionCone text21_3_4_set2)) :
    BddBelow (Set.range (fun x : Fin 2 → ℝ => text21_3_4_f1 x)) := by
  -- Route correction: isolate the universal clause from the full conjunction, then specialize.
  have hUniversal :
      ∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
        BddBelow
            (Set.range
              (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
          sInf
              (Set.range
                (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0 :=
    hTarget.2.2.2.1
  -- The dedicated specialization helper yields the bounded-below conclusion for `range f₁`.
  exact helperForText_21_3_4_specialization_forces_bddBelow_range_f1 hUniversal

/-- Helper for Text 21.3.4: the full target conjunction is inconsistent because the
universal nonnegative-multiplier clause is false. -/
lemma helperForText_21_3_4_target_conjunction_false :
    ¬ (Convex ℝ text21_3_4_set1 ∧
      Convex ℝ text21_3_4_set2 ∧
        text21_3_4_set1 ∩ text21_3_4_set2 = (∅ : Set (Fin 2 → ℝ)) ∧
          (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
            BddBelow
                (Set.range
                  (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
              sInf
                  (Set.range
                    (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) ∧
            ((![1, 1] : Fin 2 → ℝ) ∈
              Set.recessionCone text21_3_4_set1 ∩ Set.recessionCone text21_3_4_set2)) := by
  intro hTarget
  -- Route correction: convert the conjunction into the concrete bounded-below claim for `range f₁`.
  have hBddBelowRangeF1 :
      BddBelow (Set.range (fun x : Fin 2 → ℝ => text21_3_4_f1 x)) :=
    helperForText_21_3_4_target_conjunction_forces_bddBelow_range_f1 hTarget
  -- This contradicts the explicit unbounded-below witness along the vertical ray.
  exact helperForText_21_3_4_not_bddBelow_range_f1 hBddBelowRangeF1

/-- Helper for Text 21.3.4: any proof of the full target conjunction yields a contradiction. -/
lemma helperForText_21_3_4_target_conjunction_implies_false :
    (Convex ℝ text21_3_4_set1 ∧
      Convex ℝ text21_3_4_set2 ∧
        text21_3_4_set1 ∩ text21_3_4_set2 = (∅ : Set (Fin 2 → ℝ)) ∧
          (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
            BddBelow
                (Set.range
                  (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
              sInf
                  (Set.range
                    (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) ∧
            ((![1, 1] : Fin 2 → ℝ) ∈
              Set.recessionCone text21_3_4_set1 ∩ Set.recessionCone text21_3_4_set2)) → False := by
  intro hTarget
  -- Route correction: expose the contradiction as an elimination helper for the main theorem.
  exact helperForText_21_3_4_target_conjunction_false hTarget

/-- Helper for Text 21.3.4: the full target conjunction is logically equivalent to `False`. -/
lemma helperForText_21_3_4_target_conjunction_iff_false :
    (Convex ℝ text21_3_4_set1 ∧
      Convex ℝ text21_3_4_set2 ∧
        text21_3_4_set1 ∩ text21_3_4_set2 = (∅ : Set (Fin 2 → ℝ)) ∧
          (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
            BddBelow
                (Set.range
                  (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
              sInf
                  (Set.range
                    (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) ∧
            ((![1, 1] : Fin 2 → ℝ) ∈
              Set.recessionCone text21_3_4_set1 ∩ Set.recessionCone text21_3_4_set2)) ↔ False := by
  constructor
  · intro hTarget
    -- Route correction: map the target conjunction directly to the established contradiction.
    exact helperForText_21_3_4_target_conjunction_implies_false hTarget
  · intro hFalse
    -- The reverse implication is pure logic: `False` eliminates to any proposition.
    exact False.elim hFalse

-- Proof sketch: Identify the two sets as epigraph regions of convex square-root graphs, show
-- they are disjoint, compute that for each nonnegative multiplier pair the objective range is
-- bounded below with infimum `0`, and verify that `(1,1)` is a common recession direction of
-- both sets.
/-- The stronger nonnegative-multiplier formulation suggested by Text 21.3.4 is false as
stated: specializing the universal clause at `(λ₁, λ₂) = (1, 0)` forces `range f₁` to be
bounded below, but `range f₁` is explicitly unbounded below along the vertical ray. -/
theorem text21_3_4_nonnegative_multiplier_zero_infimum_formulation_false :
    ¬ (Convex ℝ text21_3_4_set1 ∧
      Convex ℝ text21_3_4_set2 ∧
        text21_3_4_set1 ∩ text21_3_4_set2 = (∅ : Set (Fin 2 → ℝ)) ∧
          (∀ lambda1 lambda2 : ℝ, 0 ≤ lambda1 → 0 ≤ lambda2 →
            BddBelow
                (Set.range
                  (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) ∧
              sInf
                  (Set.range
                    (fun x : Fin 2 → ℝ => lambda1 * text21_3_4_f1 x + lambda2 * text21_3_4_f2 x)) = 0) ∧
            ((![1, 1] : Fin 2 → ℝ) ∈
              Set.recessionCone text21_3_4_set1 ∩ Set.recessionCone text21_3_4_set2)) := by
  exact helperForText_21_3_4_target_conjunction_false

/-- The first convex function appearing in Text 21.3.5. -/
noncomputable def text21_3_5_f1 (x : Fin 2 → ℝ) : ℝ :=
  Real.sqrt ((x 0) ^ 2 + 1) - x 1

/-- The second convex function appearing in Text 21.3.5. -/
noncomputable def text21_3_5_f2 (x : Fin 2 → ℝ) : ℝ :=
  Real.sqrt ((x 1) ^ 2 + 1) - x 0

/-- The sublevel set `C_{k, ε}` from Text 21.3.5, with `k = 0, 1` corresponding to the
textbook indices `1, 2`. -/
def text21_3_5_sublevelSet (k : Fin 2) (ε : ℝ) : Set (Fin 2 → ℝ) :=
  {x | if k = 0 then text21_3_5_f1 x ≤ ε else text21_3_5_f2 x ≤ ε}

/-- The index type for the family `𝒞 = {C_{k, ε} | k ∈ {1, 2}, ε > 0}` in Text 21.3.5. -/
abbrev text21_3_5Index : Type := Fin 2 × {ε : ℝ // 0 < ε}

/-- The family member indexed by a choice of `k` and a positive threshold `ε` in
Text 21.3.5. -/
def text21_3_5_familyMember (i : text21_3_5Index) : Set (Fin 2 → ℝ) :=
  text21_3_5_sublevelSet i.1 i.2.1

/-- Helper for Text 21.3.5: the product `√(u² + 1) √(v² + 1)` dominates `uv + 1`. -/
lemma helperForText_21_3_5_squareRootProduct_lower_bound (u v : ℝ) :
    u * v + 1 ≤ Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1) := by
  -- Compare the squares and identify the gap with `(u - v)^2`.
  have hu : (Real.sqrt (u ^ 2 + 1)) ^ 2 = u ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hv : (Real.sqrt (v ^ 2 + 1)) ^ 2 = v ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hu' : (Real.sqrt (1 + u ^ 2)) ^ 2 = u ^ 2 + 1 := by
    simpa [add_comm] using hu
  have hv' : (Real.sqrt (1 + v ^ 2)) ^ 2 = v ^ 2 + 1 := by
    simpa [add_comm] using hv
  have hdiff :
      (Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1)) ^ 2 - (u * v + 1) ^ 2 = (u - v) ^ 2 := by
    ring_nf
    rw [hu', hv']
    ring
  have hsq : (u * v + 1) ^ 2 ≤ (Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1)) ^ 2 := by
    have hnonneg : 0 ≤ (u - v) ^ 2 := sq_nonneg (u - v)
    linarith
  have hright_nonneg : 0 ≤ Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1) := by
    positivity
  exact le_of_sq_le_sq hsq hright_nonneg

/-- Helper for Text 21.3.5: the scalar function `u ↦ √(u² + 1)` is convex. -/
lemma helperForText_21_3_5_scalarSqrtSqAddOne_convex
    (u v a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    Real.sqrt ((a * u + b * v) ^ 2 + 1) ≤
      a * Real.sqrt (u ^ 2 + 1) + b * Real.sqrt (v ^ 2 + 1) := by
  -- First control the mixed product by the previous helper.
  have hu : (Real.sqrt (u ^ 2 + 1)) ^ 2 = u ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hv : (Real.sqrt (v ^ 2 + 1)) ^ 2 = v ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hu' : (Real.sqrt (1 + u ^ 2)) ^ 2 = u ^ 2 + 1 := by
    simpa [add_comm] using hu
  have hv' : (Real.sqrt (1 + v ^ 2)) ^ 2 = v ^ 2 + 1 := by
    simpa [add_comm] using hv
  have hprod : u * v + 1 ≤ Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1) :=
    helperForText_21_3_5_squareRootProduct_lower_bound u v
  -- Then compare the two squares and extract the desired inequality.
  have hleftsq : (Real.sqrt ((a * u + b * v) ^ 2 + 1)) ^ 2 = (a * u + b * v) ^ 2 + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hdiff :
      (a * Real.sqrt (u ^ 2 + 1) + b * Real.sqrt (v ^ 2 + 1)) ^ 2 -
        ((a * u + b * v) ^ 2 + 1) =
        2 * a * b * (Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1) - (u * v + 1)) := by
    ring_nf
    rw [hu', hv']
    nlinarith [hab]
  have hterm_nonneg :
      0 ≤ 2 * a * b * (Real.sqrt (u ^ 2 + 1) * Real.sqrt (v ^ 2 + 1) - (u * v + 1)) := by
    apply mul_nonneg
    · nlinarith
    · linarith
  have hsq :
      (Real.sqrt ((a * u + b * v) ^ 2 + 1)) ^ 2 ≤
        (a * Real.sqrt (u ^ 2 + 1) + b * Real.sqrt (v ^ 2 + 1)) ^ 2 := by
    have hdiff_nonneg :
        0 ≤ (a * Real.sqrt (u ^ 2 + 1) + b * Real.sqrt (v ^ 2 + 1)) ^ 2 -
          ((a * u + b * v) ^ 2 + 1) := by
      rw [hdiff]
      exact hterm_nonneg
    linarith
  have hright_nonneg : 0 ≤ a * Real.sqrt (u ^ 2 + 1) + b * Real.sqrt (v ^ 2 + 1) := by
    positivity
  exact le_of_sq_le_sq hsq hright_nonneg

/-- Helper for Text 21.3.5: the diagonal point `![t, t]` evaluates both functions to the
same gap, and that gap is at most `1 / t` for `t > 0`. -/
lemma helperForText_21_3_5_diagonal_gap_bound (t : ℝ) (ht : 0 < t) :
    text21_3_5_f1 (![t, t] : Fin 2 → ℝ) = Real.sqrt (t ^ 2 + 1) - t ∧
      text21_3_5_f2 (![t, t] : Fin 2 → ℝ) = Real.sqrt (t ^ 2 + 1) - t ∧
      Real.sqrt (t ^ 2 + 1) - t ≤ 1 / t := by
  constructor
  · -- On the diagonal, `f₁` is exactly the scalar gap.
    simp [text21_3_5_f1]
  constructor
  · -- The same diagonal identity holds for `f₂`.
    simp [text21_3_5_f2]
  · -- Bound the gap by comparing `√(t² + 1)` with `t + 1 / t`.
    have hsqrt_le : Real.sqrt (t ^ 2 + 1) ≤ t + 1 / t := by
      refine Real.sqrt_le_iff.mpr ?_
      constructor
      · positivity
      · have htne : t ≠ 0 := ne_of_gt ht
        field_simp [htne]
        nlinarith
    linarith

/-- Helper for Text 21.3.5: each sublevel set `C_{k, ε}` is closed. -/
lemma helperForText_21_3_5_sublevelSet_closed (k : Fin 2) (ε : ℝ) :
    IsClosed (text21_3_5_sublevelSet k ε) := by
  fin_cases k
  · -- The `k = 0` branch is a closed sublevel set of a continuous function.
    have hcoord0 : Continuous fun x : Fin 2 → ℝ => x 0 := continuous_apply 0
    have hcoord1 : Continuous fun x : Fin 2 → ℝ => x 1 := continuous_apply 1
    have hsqrt : Continuous fun x : Fin 2 → ℝ => Real.sqrt ((x 0) ^ 2 + 1) := by
      exact Real.continuous_sqrt.comp ((hcoord0.pow 2).add continuous_const)
    have hfun : Continuous fun x : Fin 2 → ℝ => text21_3_5_f1 x := by
      simpa [text21_3_5_f1] using hsqrt.sub hcoord1
    simpa [text21_3_5_sublevelSet] using (isClosed_le hfun continuous_const)
  · -- The `k = 1` branch is symmetric.
    have hcoord0 : Continuous fun x : Fin 2 → ℝ => x 0 := continuous_apply 0
    have hcoord1 : Continuous fun x : Fin 2 → ℝ => x 1 := continuous_apply 1
    have hsqrt : Continuous fun x : Fin 2 → ℝ => Real.sqrt ((x 1) ^ 2 + 1) := by
      exact Real.continuous_sqrt.comp ((hcoord1.pow 2).add continuous_const)
    have hfun : Continuous fun x : Fin 2 → ℝ => text21_3_5_f2 x := by
      simpa [text21_3_5_f2] using hsqrt.sub hcoord0
    simpa [text21_3_5_sublevelSet] using (isClosed_le hfun continuous_const)

/-- Helper for Text 21.3.5: each sublevel set `C_{k, ε}` is convex. -/
lemma helperForText_21_3_5_sublevelSet_convex (k : Fin 2) (ε : ℝ) :
    Convex ℝ (text21_3_5_sublevelSet k ε) := by
  fin_cases k
  · -- For `k = 0`, propagate the scalar convexity estimate along convex combinations.
    intro x hx y hy a b ha hb hab
    simp [text21_3_5_sublevelSet, text21_3_5_f1] at hx hy ⊢
    have hx' : Real.sqrt ((x 0) ^ 2 + 1) ≤ x 1 + ε := by
      linarith
    have hy' : Real.sqrt ((y 0) ^ 2 + 1) ≤ y 1 + ε := by
      linarith
    have hcoord0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by
      simp [Pi.smul_apply]
    have hcoord1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by
      simp [Pi.smul_apply]
    have hax : a * Real.sqrt ((x 0) ^ 2 + 1) ≤ a * (x 1 + ε) :=
      mul_le_mul_of_nonneg_left hx' ha
    have hby : b * Real.sqrt ((y 0) ^ 2 + 1) ≤ b * (y 1 + ε) :=
      mul_le_mul_of_nonneg_left hy' hb
    have hadd :
        a * Real.sqrt ((x 0) ^ 2 + 1) + b * Real.sqrt ((y 0) ^ 2 + 1) ≤
          a * (x 1 + ε) + b * (y 1 + ε) :=
      add_le_add hax hby
    have htarget : Real.sqrt ((a * x 0 + b * y 0) ^ 2 + 1) ≤ a * x 1 + b * y 1 + ε := by
      calc
        Real.sqrt ((a * x 0 + b * y 0) ^ 2 + 1)
            ≤ a * Real.sqrt ((x 0) ^ 2 + 1) + b * Real.sqrt ((y 0) ^ 2 + 1) :=
          helperForText_21_3_5_scalarSqrtSqAddOne_convex (x 0) (y 0) a b ha hb hab
        _ ≤ a * (x 1 + ε) + b * (y 1 + ε) := hadd
        _ = a * x 1 + b * y 1 + ε := by
          calc
            a * (x 1 + ε) + b * (y 1 + ε) = a * x 1 + b * y 1 + (a + b) * ε := by ring
            _ = a * x 1 + b * y 1 + ε := by rw [hab]; ring
    simpa [add_comm, add_left_comm, add_assoc] using htarget
  · -- The `k = 1` branch is the same argument with the coordinates exchanged.
    intro x hx y hy a b ha hb hab
    simp [text21_3_5_sublevelSet, text21_3_5_f2] at hx hy ⊢
    have hx' : Real.sqrt ((x 1) ^ 2 + 1) ≤ x 0 + ε := by
      linarith
    have hy' : Real.sqrt ((y 1) ^ 2 + 1) ≤ y 0 + ε := by
      linarith
    have hcoord0 : (a • x + b • y) 0 = a * x 0 + b * y 0 := by
      simp [Pi.smul_apply]
    have hcoord1 : (a • x + b • y) 1 = a * x 1 + b * y 1 := by
      simp [Pi.smul_apply]
    have hax : a * Real.sqrt ((x 1) ^ 2 + 1) ≤ a * (x 0 + ε) :=
      mul_le_mul_of_nonneg_left hx' ha
    have hby : b * Real.sqrt ((y 1) ^ 2 + 1) ≤ b * (y 0 + ε) :=
      mul_le_mul_of_nonneg_left hy' hb
    have hadd :
        a * Real.sqrt ((x 1) ^ 2 + 1) + b * Real.sqrt ((y 1) ^ 2 + 1) ≤
          a * (x 0 + ε) + b * (y 0 + ε) :=
      add_le_add hax hby
    have htarget : Real.sqrt ((a * x 1 + b * y 1) ^ 2 + 1) ≤ a * x 0 + b * y 0 + ε := by
      calc
        Real.sqrt ((a * x 1 + b * y 1) ^ 2 + 1)
            ≤ a * Real.sqrt ((x 1) ^ 2 + 1) + b * Real.sqrt ((y 1) ^ 2 + 1) :=
          helperForText_21_3_5_scalarSqrtSqAddOne_convex (x 1) (y 1) a b ha hb hab
        _ ≤ a * (x 0 + ε) + b * (y 0 + ε) := hadd
        _ = a * x 0 + b * y 0 + ε := by
          calc
            a * (x 0 + ε) + b * (y 0 + ε) = a * x 0 + b * y 0 + (a + b) * ε := by ring
            _ = a * x 0 + b * y 0 + ε := by rw [hab]; ring
    simpa [add_comm, add_left_comm, add_assoc] using htarget

/-- Helper for Text 21.3.5: every finite subcollection of the family has a common diagonal
point. -/
lemma helperForText_21_3_5_finite_intersection_nonempty (s : Finset text21_3_5Index) :
    (⋂ i ∈ s, text21_3_5_familyMember i).Nonempty := by
  let T : ℝ := s.sum (fun j => 1 / j.2.1) + 1
  -- The witness is the diagonal point `![T, T]`.
  have hsum_nonneg : 0 ≤ s.sum (fun j => 1 / j.2.1) := by
    refine Finset.sum_nonneg ?_
    intro j hj
    exact le_of_lt (one_div_pos.mpr j.2.2)
  have hTpos : 0 < T := by
    dsimp [T]
    linarith
  refine ⟨![T, T], ?_⟩
  refine Set.mem_iInter₂.mpr ?_
  intro i hi
  rcases i with ⟨k, εsub⟩
  rcases εsub with ⟨ε, hε⟩
  have hsumLower : 1 / ε ≤ s.sum (fun j => 1 / j.2.1) := by
    exact Finset.single_le_sum (fun j hj => le_of_lt (one_div_pos.mpr j.2.2)) hi
  have hTge : 1 / ε ≤ T := by
    dsimp [T]
    linarith
  have hInvLe : 1 / T ≤ ε := by
    have hmul : 1 ≤ ε * T := by
      have hmul' := mul_le_mul_of_nonneg_left hTge (le_of_lt hε)
      have hεne : ε ≠ 0 := ne_of_gt hε
      simpa [hεne, mul_comm, mul_left_comm, mul_assoc] using hmul'
    simpa [one_div] using (inv_le_iff_one_le_mul₀ hTpos).2 hmul
  have hdiag := helperForText_21_3_5_diagonal_gap_bound T hTpos
  rcases hdiag with ⟨hf1, hf2, hbound⟩
  fin_cases k
  · -- In the `f₁` branch, the diagonal estimate is below every threshold in the finite set.
    simpa [text21_3_5_familyMember, text21_3_5_sublevelSet, hf1] using le_trans hbound hInvLe
  · -- The `f₂` branch is identical on the diagonal.
    simpa [text21_3_5_familyMember, text21_3_5_sublevelSet, hf2] using le_trans hbound hInvLe

/-- Helper for Text 21.3.5: every real number lies strictly below `√(a² + 1)`. -/
lemma helperForText_21_3_5_strict_coordinate_gap (a : ℝ) : a < Real.sqrt (a ^ 2 + 1) := by
  by_cases ha : a < 0
  · -- Negative numbers are automatically below the nonnegative square root.
    exact lt_of_lt_of_le ha (Real.sqrt_nonneg _)
  · -- For `a ≥ 0`, compare squares.
    have ha0 : 0 ≤ a := le_of_not_gt ha
    have hsq : (Real.sqrt (a ^ 2 + 1)) ^ 2 = a ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have hsqrt_nonneg : 0 ≤ Real.sqrt (a ^ 2 + 1) := Real.sqrt_nonneg _
    nlinarith

-- Proof sketch: show each `C_{k, ε}` is a nonempty closed convex sublevel set of a convex
-- function; verify directly that any three members of the family intersect, while the full
-- intersection is empty because simultaneous bounds for both square-root inequalities force
-- incompatible coordinate inequalities as `ε → 0+`.
/-- Text 21.3.5: for the family `𝒞 = {C_{k, ε} | k ∈ {1, 2}, ε > 0}` in `ℝ²`, where
`C_{k, ε}` is the `ε`-sublevel set of `f₁(x) = √(ξ₁² + 1) - ξ₂` or
`f₂(x) = √(ξ₂² + 1) - ξ₁`, each member is nonempty, closed, and convex; every subcollection
of at most `3 (= n + 1)` sets has nonempty intersection; but the intersection of the entire
family is empty. This gives a Helly counterexample without a suitable no-common-recession
hypothesis. -/
theorem text21_3_5_helly_counterexample_without_common_recession :
    (∀ i : text21_3_5Index,
      (text21_3_5_familyMember i).Nonempty ∧
        IsClosed (text21_3_5_familyMember i) ∧
          Convex ℝ (text21_3_5_familyMember i)) ∧
      (∀ s : Finset text21_3_5Index,
        s.card ≤ 3 → (⋂ i ∈ s, text21_3_5_familyMember i).Nonempty) ∧
      (⋂ i : text21_3_5Index, text21_3_5_familyMember i) = (∅ : Set (Fin 2 → ℝ)) :=
by
  constructor
  · intro i
    -- Reuse the finite-intersection helper on the singleton family for nonemptiness.
    refine ⟨?_, ?_⟩
    · have hsingle := helperForText_21_3_5_finite_intersection_nonempty ({i} : Finset text21_3_5Index)
      simpa [text21_3_5_familyMember] using hsingle
    · exact ⟨
        by
          -- Closedness comes from continuity of the defining function.
          simpa [text21_3_5_familyMember] using
            helperForText_21_3_5_sublevelSet_closed i.1 i.2.1,
        by
          -- Convexity is inherited from the convex square-root profile.
          simpa [text21_3_5_familyMember] using
            helperForText_21_3_5_sublevelSet_convex i.1 i.2.1
      ⟩
  constructor
  · intro s hs
    -- We prove the stronger statement that every finite subcollection intersects.
    exact helperForText_21_3_5_finite_intersection_nonempty s
  · -- The full intersection is empty because it would force the impossible chain
    -- `x 0 < x 1 < x 0`.
    apply Set.eq_empty_iff_forall_notMem.2
    intro x hx
    have hF1_nonpos : text21_3_5_f1 x ≤ 0 := by
      -- Otherwise choose a smaller positive threshold and violate membership.
      by_contra hpos
      have hε : 0 < text21_3_5_f1 x / 2 := by
        linarith
      have hxε : x ∈ text21_3_5_familyMember ((0 : Fin 2), ⟨text21_3_5_f1 x / 2, hε⟩) := by
        exact Set.mem_iInter.mp hx ((0 : Fin 2), ⟨text21_3_5_f1 x / 2, hε⟩)
      have hxineq : text21_3_5_f1 x ≤ text21_3_5_f1 x / 2 := by
        simpa [text21_3_5_familyMember, text21_3_5_sublevelSet] using hxε
      linarith
    have hF2_nonpos : text21_3_5_f2 x ≤ 0 := by
      -- The symmetric argument treats the second family.
      by_contra hpos
      have hε : 0 < text21_3_5_f2 x / 2 := by
        linarith
      have hxε : x ∈ text21_3_5_familyMember ((1 : Fin 2), ⟨text21_3_5_f2 x / 2, hε⟩) := by
        exact Set.mem_iInter.mp hx ((1 : Fin 2), ⟨text21_3_5_f2 x / 2, hε⟩)
      have hxineq : text21_3_5_f2 x ≤ text21_3_5_f2 x / 2 := by
        simpa [text21_3_5_familyMember, text21_3_5_sublevelSet] using hxε
      linarith
    have h01 : Real.sqrt ((x 0) ^ 2 + 1) ≤ x 1 := by
      simpa [text21_3_5_f1] using hF1_nonpos
    have h10 : Real.sqrt ((x 1) ^ 2 + 1) ≤ x 0 := by
      simpa [text21_3_5_f2] using hF2_nonpos
    have hx0_lt_x1 : x 0 < x 1 := by
      exact lt_of_lt_of_le (helperForText_21_3_5_strict_coordinate_gap (x 0)) h01
    have hx1_lt_x0 : x 1 < x 0 := by
      exact lt_of_lt_of_le (helperForText_21_3_5_strict_coordinate_gap (x 1)) h10
    exact (lt_irrefl (x 0)) (lt_trans hx0_lt_x1 hx1_lt_x0)

-- Proof sketch: under the weaker `C = ℝⁿ` recession hypothesis, reduce to the univ-case
-- versions of Theorem 21.3 and Corollary 21.3.1 by showing that any common recession
-- direction can only survive on a finite affine block and is constant on the remaining
-- functions, which is enough for Rockafellar's separation argument to go through unchanged.
/-- Helper for Theorem 21.4: an affine real-valued map on `ℝⁿ` expands linearly along a
ray, so global monotonicity forces a nonpositive slope and zero slope forces constancy. -/
lemma helperForTheorem_21_4_affineMonotone_and_constant_characterization
    {n : ℕ}
    (a : AffineMap ℝ (Fin n → ℝ) ℝ)
    (d : Fin n → ℝ) :
    (∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
      ((a (x + t • d) : ℝ) : EReal) = ((a x + t * a.linear d : ℝ) : EReal)) ∧
    ((∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
      ((a (x + t • d) : ℝ) : EReal) ≤ (a x : EReal)) →
      a.linear d ≤ 0) ∧
    (a.linear d = 0 →
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        ((a (x + t • d) : ℝ) : EReal) = (a x : EReal)) := by
  have hExpand :
      ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        ((a (x + t • d) : ℝ) : EReal) = ((a x + t * a.linear d : ℝ) : EReal) := by
    intro x t ht
    -- Expand the affine map on the translated point `x + t • d`.
    have hmap : a (x + t • d) = a x + t * a.linear d := by
      simpa [vadd_eq_add, LinearMap.map_smul, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using a.map_vadd x (t • d)
    exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hmap
  have hMonotoneForcesSlope :
      (∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        ((a (x + t • d) : ℝ) : EReal) ≤ (a x : EReal)) →
        a.linear d ≤ 0 := by
    intro hmono
    -- Read the slope from the special case `x = 0`, `t = 1`.
    have hAtOne := hmono 0 1 (by norm_num)
    rw [hExpand 0 1 (by norm_num)] at hAtOne
    have hreal : a 0 + 1 * a.linear d ≤ a 0 := EReal.coe_le_coe_iff.mp hAtOne
    linarith
  have hZeroSlopeGivesConstancy :
      a.linear d = 0 →
        ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
          ((a (x + t • d) : ℝ) : EReal) = (a x : EReal) := by
    intro hlin x t ht
    -- Once the slope vanishes, the ray-expansion collapses to equality.
    rw [hExpand x t ht]
    simp [hlin]
  exact ⟨hExpand, hMonotoneForcesSlope, hZeroSlopeGivesConstancy⟩

end Section21
end Chap04
