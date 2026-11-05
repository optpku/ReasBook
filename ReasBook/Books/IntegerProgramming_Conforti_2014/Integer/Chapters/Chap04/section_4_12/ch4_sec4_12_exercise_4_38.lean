/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_20
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_corollary_3_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_lemma_3_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_example_3_29
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38.FacetTransport
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Convex.KreinMilman

universe u

open Set

-- This exercise is source-facing. It reuses the chapter/project owners `permutahedron`,
-- `ascending_vector`, `MixedRealPoint`, `Set.IsPolytope`, and `IsFacetOf` directly.
-- Semantic recall note: the Chapter 3 face owner is `IsExposed`, so this exercise counts
-- nonempty exposed faces directly. For polytopes this matches the textbook face notion, and it
-- keeps the projection and prefix-facet arguments on the canonical project API.

/-- Helper for Exercise 4.38: `faceCount Q` counts the nonempty faces of `Q` in the canonical
`IsExposed` sense, so the empty face `∅` is excluded. -/
noncomputable def faceCount
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) : Nat :=
  {F : Set E | IsExposed ℝ Q F ∧ F.Nonempty}.ncard

/-- Unfolding equation for the nonempty-face counting convention used in Exercise 4.38. -/
theorem faceCount_eq
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : Set E) :
    faceCount Q = {F : Set E | IsExposed ℝ Q F ∧ F.Nonempty}.ncard :=
  rfl

/-- Helper for Exercise 4.38: flattening by `Fin.appendEquiv` is linear on mixed real points. -/
lemma appendEquivIsLinearMap
    {n p : ℕ} :
    IsLinearMap ℝ (Fin.appendEquiv (α := ℝ) n p) := by
  refine ⟨?_, ?_⟩
  · -- Route correction: the flattening map should be treated as a linear equivalence, not as an
    -- ad hoc coordinate bijection inside the face-count proof.
    intro x y
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]
  · -- Scalar multiplication is again checked blockwise on the two coordinate ranges.
    intro a x
    ext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [Fin.appendEquiv]
    · intro j
      simp [Fin.appendEquiv]

/-- Helper for Exercise 4.38: flattening by `Fin.appendEquiv` preserves the number of nonempty
exposed faces counted by `faceCount`. -/
lemma faceCount_appendEquiv_eq
    {n p : ℕ} (Q : Set (MixedRealPoint n p)) :
    faceCount Q = faceCount ((Fin.appendEquiv n p) '' Q) := by
  let eL :
      MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e :
      MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
    eL.toContinuousLinearEquiv
  let countedFaces :
      Set (Set (MixedRealPoint n p)) := {F | IsExposed ℝ Q F ∧ F.Nonempty}
  let countedFacesFlat :
      Set (Set (Fin (n + p) → ℝ)) :=
    {F | IsExposed ℝ (e '' Q) F ∧ F.Nonempty}
  have hImage :
      (fun F : Set (MixedRealPoint n p) ↦ e '' F) '' countedFaces = countedFacesFlat := by
    ext F
    constructor
    · rintro ⟨G, hG, rfl⟩
      rcases hG with ⟨hG_exposed, hG_nonempty⟩
      constructor
      · -- Push the exposing functional through the flattening equivalence.
        exact isExposed_image_continuousLinearEquiv e hG_exposed
      · rcases hG_nonempty with ⟨x, hx⟩
        exact ⟨e x, ⟨x, hx, rfl⟩⟩
    · intro hF
      refine ⟨e.symm '' F, ?_, ?_⟩
      · rcases hF with ⟨hF_exposed, hF_nonempty⟩
        constructor
        · -- Pull the flattened exposed face back along the inverse equivalence.
          simpa using isExposed_image_continuousLinearEquiv e.symm hF_exposed
        · rcases hF_nonempty with ⟨u, hu⟩
          exact ⟨e.symm u, ⟨u, hu, by simp⟩⟩
      · -- The inverse-image witness lands exactly on the original flat face.
        simp
  have hInj : Function.Injective (fun F : Set (MixedRealPoint n p) ↦ e '' F) := by
    intro F₁ F₂ hEq
    exact (Equiv.image_eq_iff_eq e.toEquiv F₁ F₂).mp hEq
  -- Compare the two counted face families through the flattening equivalence on subsets.
  calc
    faceCount Q = countedFaces.ncard := by rfl
    _ = ((fun F : Set (MixedRealPoint n p) ↦ e '' F) '' countedFaces).ncard := by
          symm
          exact Set.ncard_image_of_injective countedFaces hInj
    _ = countedFacesFlat.ncard := by rw [hImage]
    _ = faceCount ((Fin.appendEquiv n p) '' Q) := by rfl

/-- Helper for Exercise 4.38: flattening by `Fin.appendEquiv` preserves the facet count after
transporting facets to the flat ambient space. -/
lemma facetCount_appendEquiv_eq
    {n p : ℕ}
    {Q : Set (MixedRealPoint n p)}
    :
    {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard =
      {H : Set (Fin (n + p) → ℝ) |
        IsFacetOf (((Fin.appendEquiv n p) : MixedRealPoint n p → _) '' Q) H}.ncard := by
  let eL :
      MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e :
      MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
    eL.toContinuousLinearEquiv
  let countedFacets :
      Set (Set (MixedRealPoint n p)) := {F | IsFacetOf Q F}
  let countedFacetsFlat :
      Set (Set (Fin (n + p) → ℝ)) := {F | IsFacetOf ((e : MixedRealPoint n p → _) '' Q) F}
  have hImage :
      (fun F : Set (MixedRealPoint n p) ↦ e '' F) '' countedFacets = countedFacetsFlat := by
    ext F
    constructor
    · rintro ⟨G, hG, rfl⟩
      simpa using (isFacetOf_image_continuousLinearEquiv e).1 hG
    · intro hF
      refine ⟨e.symm '' F, ?_, ?_⟩
      · simpa using (isFacetOf_image_continuousLinearEquiv e.symm).1 hF
      · simp
  have hInj : Function.Injective (fun F : Set (MixedRealPoint n p) ↦ e '' F) := by
    intro F₁ F₂ hEq
    exact (Equiv.image_eq_iff_eq e.toEquiv F₁ F₂).mp hEq
  -- Compare the two facet families through the flattening equivalence on subsets.
  calc
    {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard = countedFacets.ncard := by rfl
    _ = ((fun F : Set (MixedRealPoint n p) ↦ e '' F) '' countedFacets).ncard := by
          symm
          exact Set.ncard_image_of_injective countedFacets hInj
    _ = countedFacetsFlat.ncard := by rw [hImage]
    _ = {H : Set (Fin (n + p) → ℝ) |
          IsFacetOf (((Fin.appendEquiv n p) : MixedRealPoint n p → _) '' Q) H}.ncard := by
          rfl

/-- Helper for Exercise 4.38: an exposed face downstairs lifts to an exposed face upstairs by
maximizing the same functional on the `x`-coordinates. -/
lemma lifted_exposed_face_of_projection
    {n p : ℕ}
    (P : Set (Fin n → ℝ))
    (Q : Set (MixedRealPoint n p))
    (hproj : P = Prod.fst '' Q)
    {F : Set (Fin n → ℝ)}
    (hF : IsExposed ℝ P F) :
    ∃ G : Set (MixedRealPoint n p), IsExposed ℝ Q G ∧ Prod.fst '' G = F := by
  by_cases hFn : F.Nonempty
  · obtain ⟨l, rfl⟩ := hF hFn
    let lQ : StrongDual ℝ (MixedRealPoint n p) :=
      l.comp (ContinuousLinearMap.fst ℝ (Fin n → ℝ) (Fin p → ℝ))
    -- Lift the exposing functional through the first-coordinate projection.
    refine ⟨lQ.toExposed Q, ContinuousLinearMap.toExposed.isExposed, ?_⟩
    ext x
    constructor
    · rintro ⟨xy, hxy, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [hproj]
        exact ⟨xy, hxy.1, rfl⟩
      · intro z hz
        rw [hproj] at hz
        rcases hz with ⟨zw, hzwQ, rfl⟩
        exact hxy.2 zw hzwQ
    · intro hx
      rcases (show x ∈ Prod.fst '' Q from by simpa [hproj] using hx.1) with ⟨xy, hxyQ, hxyx⟩
      refine ⟨xy, ?_, hxyx⟩
      subst hxyx
      -- Any lift of a maximizing `x` also maximizes the lifted functional upstairs.
      refine ⟨hxyQ, ?_⟩
      intro zw hzwQ
      have hz : zw.1 ∈ P := by
        rw [hproj]
        exact ⟨zw, hzwQ, rfl⟩
      exact hx.2 zw.1 hz
  · -- The empty face lifts to the empty face.
    refine ⟨∅, isExposed_empty, ?_⟩
    rw [Set.not_nonempty_iff_eq_empty.mp hFn]
    simp

/-- Helper for Exercise 4.38: the ordered vertex `ascending_vector n` has pairwise distinct
coordinates, so composing it with a permutation determines that permutation uniquely. -/
lemma ascendingVector_injective (n : ℕ) : Function.Injective (ascending_vector n) := by
  intro i j hij
  apply Fin.ext
  -- Compare the strictly increasing coordinate values after coercing to `ℝ`.
  have hij' : ((i : ℕ) : ℝ) + 1 = ((j : ℕ) : ℝ) + 1 := by
    simpa [ascending_vector] using hij
  have hij'' : (i : ℕ) + 1 = (j : ℕ) + 1 := by
    exact_mod_cast hij'
  omega

/-- Helper for Exercise 4.38: part (1) shows that if `P` and `Q` are polytopes with
`P = proj_x(Q)`, then `Q` has at least as many faces as `P`. -/
theorem projection_face_count_le
    {n p : ℕ}
    (P : Set (Fin n → ℝ))
    (Q : Set (MixedRealPoint n p))
    (hP : P.IsPolytope ℝ)
    (hQ : Q.IsPolytope ℝ)
    (hproj : P = Prod.fst '' Q) :
    faceCount P ≤ faceCount Q := by
  classical
  let _ := hP
  let downstairs : Set (Set (Fin n → ℝ)) := {F | IsExposed ℝ P F ∧ F.Nonempty}
  let upstairs : Set (Set (MixedRealPoint n p)) := {F | IsExposed ℝ Q F ∧ F.Nonempty}
  let liftFace : Set (Fin n → ℝ) → Set (MixedRealPoint n p) := fun F ↦
    if hF : IsExposed ℝ P F then
      Classical.choose (lifted_exposed_face_of_projection P Q hproj hF)
    else
      ∅
  have hu_finite : upstairs.Finite := by
    -- The counted faces upstairs are a finite subfamily of all exposed faces of the polytope `Q`.
    refine (polytope_finite_exposed_faces hQ).subset ?_
    intro F hF
    exact hF.1
  have hlift_mapsTo : ∀ F ∈ downstairs, liftFace F ∈ upstairs := by
    intro F hF
    rcases hF with ⟨hF_exposed, hF_nonempty⟩
    have hspec :=
      Classical.choose_spec (lifted_exposed_face_of_projection P Q hproj hF_exposed)
    change IsExposed ℝ Q (liftFace F) ∧ (liftFace F).Nonempty
    constructor
    · simpa [liftFace, hF_exposed] using hspec.1
    rcases hF_nonempty with ⟨x, hx⟩
    have hx_image : x ∈ Prod.fst '' liftFace F := by
      simpa [liftFace, hF_exposed, hspec.2] using hx
    rcases hx_image with ⟨xy, hxy, rfl⟩
    exact ⟨xy, hxy⟩
  have hlift_inj : Set.InjOn liftFace downstairs := by
    intro F₁ hF₁ F₂ hF₂ hEq
    rcases hF₁ with ⟨hF₁_exposed, -⟩
    rcases hF₂ with ⟨hF₂_exposed, -⟩
    have hspec₁ :=
      Classical.choose_spec (lifted_exposed_face_of_projection P Q hproj hF₁_exposed)
    have hspec₂ :=
      Classical.choose_spec (lifted_exposed_face_of_projection P Q hproj hF₂_exposed)
    calc
      F₁ = Prod.fst '' liftFace F₁ := by
        simpa [liftFace, hF₁_exposed] using hspec₁.2.symm
      _ = Prod.fst '' liftFace F₂ := by rw [hEq]
      _ = F₂ := by
        simpa [liftFace, hF₂_exposed] using hspec₂.2
  -- Compare the two finite face families through the injective lift map.
  simpa [faceCount_eq, downstairs, upstairs] using
    Set.ncard_le_ncard_of_injOn liftFace hlift_mapsTo hlift_inj hu_finite

/-- Helper for Exercise 4.38: once `faceCount Q` is bounded by `2 ^ (# facets of Q)`, part (2)
follows by combining that estimate with part (1). -/
lemma log_face_count_le_facet_count_of_face_bound
    {n p : ℕ}
    (P : Set (Fin n → ℝ))
    (Q : Set (MixedRealPoint n p))
    (hQ : Q.IsPolytope ℝ)
    (hproj : P = Prod.fst '' Q)
    (hfaceBound : faceCount Q ≤
      2 ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard) :
    Real.logb 2 (faceCount P) ≤
      ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
  classical
  rcases hQ with ⟨V, hV, hQ_eq⟩
  have hQ_poly : Q.IsPolytope ℝ := ⟨V, hV, hQ_eq⟩
  have hP : P.IsPolytope ℝ := by
    refine ⟨Prod.fst '' V, hV.image Prod.fst, ?_⟩
    -- The projection of a finite convex-hull presentation is again a finite convex hull.
    calc
      P = Prod.fst '' Q := hproj
      _ = Prod.fst '' convexHull ℝ V := by rw [hQ_eq]
      _ = convexHull ℝ (Prod.fst '' V) := by
        simpa using
          (LinearMap.image_convexHull (LinearMap.fst ℝ (Fin n → ℝ) (Fin p → ℝ)) V)
  have hcount_le :
      faceCount P ≤ 2 ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard := by
    -- Part (1) transfers the face count downstairs, then the assumed face bound closes the step.
    exact le_trans (projection_face_count_le P Q hP hQ_poly hproj) hfaceBound
  by_cases hzero : faceCount P = 0
  · -- When the downstairs face count vanishes, `logb 2` collapses to `0`.
    have hnonneg : (0 : ℝ) ≤ ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
      positivity
    have hlog_zero : Real.logb 2 (faceCount P) = 0 := by
      simp [hzero]
    rw [hlog_zero]
    exact hnonneg
  · have hpos_nat : 0 < faceCount P := Nat.pos_of_ne_zero hzero
    have hpos : (0 : ℝ) < faceCount P := by
      exact_mod_cast hpos_nat
    calc
      Real.logb 2 (faceCount P)
          ≤ Real.logb 2 (2 ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard) := by
            exact Real.logb_le_logb_of_le (by norm_num) hpos (by exact_mod_cast hcount_le)
      _ = Real.logb 2 ((2 : ℝ) ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard) := by
            norm_num
      _ = ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) * Real.logb 2 2 := by
            rw [Real.logb_pow]
      _ = ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
            norm_num

/-- Helper for Exercise 4.38: a nonempty exposed face of `polyhedron_le_set A b` is recovered from
the remaining rows that are active on every point of the face. -/
lemma exposedFace_eq_activeConstraintFace_activeRemainingRows
    {m k : ℕ}
    {P F : Set (Fin k → ℝ)}
    {A : Matrix (Fin m) (Fin k) ℝ}
    {b : Fin m → ℝ}
    (hP_eq : P = polyhedron_le_set A b)
    (hF : IsExposed ℝ P F)
    (hF_nonempty : F.Nonempty) :
    F =
      active_constraint_face A b
        {i : Fin m |
          i ∈ remaining_inequality_indices A b ∧
            ∀ x ∈ F, (Matrix.mulVec A x) i = b i} := by
  classical
  subst hP_eq
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF hF_nonempty
  ext x
  constructor
  · intro hxF
    have hxI : x ∈ active_constraint_face A b I := by
      simpa [hI] using hxF
    have hxP : x ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hxI
    -- Every point of the face satisfies the canonical remaining-row equalities and stays feasible
    -- on the inactive rows.
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      exact hi.2 x hxF
    · intro i hi
      exact hxP i
  · intro hxActive
    have hxP : x ∈ polyhedron_le_set A b :=
      mem_polyhedron_of_mem_active_constraint_face hxActive
    have hxI : x ∈ active_constraint_face A b I := by
      -- Route correction: rows outside the remaining subsystem are implicit equalities, so the
      -- original active set `I` can be rebuilt from the canonical remaining-row owner.
      refine (mem_active_constraint_face_iff).2 ?_
      constructor
      · intro i hiI
        by_cases hi_remaining : i ∈ remaining_inequality_indices A b
        · have hi_active :
            i ∈
              {j : Fin m |
                j ∈ remaining_inequality_indices A b ∧
                  ∀ y ∈ F, (Matrix.mulVec A y) j = b j} := by
            refine ⟨hi_remaining, ?_⟩
            intro y hyF
            have hyI : y ∈ active_constraint_face A b I := by
              simpa [hI] using hyF
            exact (mem_active_constraint_face_iff.mp hyI).1 i hiI
          exact (mem_active_constraint_face_iff.mp hxActive).1 i hi_active
        · have hi_implicit : is_implicit_equality A b i := by
            by_contra hi_not_implicit
            exact hi_remaining ((mem_remaining_inequality_indices_iff A b i).2 hi_not_implicit)
          exact hi_implicit hxP
      · intro i hiI
        exact hxP i
    simpa [hI] using hxI

/-- Helper for Exercise 4.38: once a flat polytope is written as `polyhedron_le_set A b`, every
counted nonempty exposed face is encoded by the subset of remaining rows that are active on it. -/
lemma faceCount_le_two_pow_remainingRowsOfPolyhedron
    {m k : ℕ}
    {P : Set (Fin k → ℝ)}
    {A : Matrix (Fin m) (Fin k) ℝ}
    {b : Fin m → ℝ}
    (hP_eq : P = polyhedron_le_set A b) :
    faceCount P ≤ 2 ^ (remaining_inequality_indices A b).ncard := by
  classical
  subst hP_eq
  let rowsType := {i // i ∈ remaining_inequality_indices A b}
  let countedFaces : Set (Set (Fin k → ℝ)) :=
    {F | IsExposed ℝ (polyhedron_le_set A b) F ∧ F.Nonempty}
  let faceRowsSet : Set (Fin k → ℝ) → Set rowsType :=
    fun F ↦ {i | ∀ x ∈ F, (Matrix.mulVec A x) i.1 = b i.1}
  let faceRows : Set (Fin k → ℝ) → Finset rowsType :=
    fun F ↦ (faceRowsSet F).toFinite.toFinset
  let faceRowsAmbient : Set (Fin k → ℝ) → Set (Fin m) :=
    fun F ↦
      {i : Fin m |
        i ∈ remaining_inequality_indices A b ∧
          ∀ x ∈ F, (Matrix.mulVec A x) i = b i}
  have hcountedFaces_finite : countedFaces.Finite := by
    -- The canonical exposed-face family of a polyhedron is finite, so the nonempty subfamily is
    -- finite as well.
    exact
      (polyhedron_finite_faces
        (P := polyhedron_le_set A b)
        (by exact (is_polyhedron_iff).2 ⟨m, A, b, rfl⟩)).subset
        (fun F hF ↦ hF.1)
  have hfaceRows_inj : Set.InjOn faceRows countedFaces := by
    intro F₁ hF₁ F₂ hF₂ hEq
    rcases hF₁ with ⟨hF₁_exposed, hF₁_nonempty⟩
    rcases hF₂ with ⟨hF₂_exposed, hF₂_nonempty⟩
    have hRowsSubtypeEq : faceRowsSet F₁ = faceRowsSet F₂ := by
      ext i
      have hi_mem :
          i ∈ faceRows F₁ ↔ i ∈ faceRows F₂ := by
        simpa [faceRows] using congrArg (fun s : Finset rowsType ↦ i ∈ s) hEq
      simpa [faceRows, faceRowsSet] using hi_mem
    have hRowsAmbientEq : faceRowsAmbient F₁ = faceRowsAmbient F₂ := by
      ext i
      constructor
      · intro hi
        refine ⟨hi.1, ?_⟩
        have hiSubtype : (⟨i, hi.1⟩ : rowsType) ∈ faceRowsSet F₁ := hi.2
        have hiSubtype' : (⟨i, hi.1⟩ : rowsType) ∈ faceRowsSet F₂ := by
          rw [← hRowsSubtypeEq]
          exact hiSubtype
        exact hiSubtype'
      · intro hi
        refine ⟨hi.1, ?_⟩
        have hiSubtype : (⟨i, hi.1⟩ : rowsType) ∈ faceRowsSet F₂ := hi.2
        have hiSubtype' : (⟨i, hi.1⟩ : rowsType) ∈ faceRowsSet F₁ := by
          rw [hRowsSubtypeEq]
          exact hiSubtype
        exact hiSubtype'
    have hF₁_eq :
        F₁ = active_constraint_face A b (faceRowsAmbient F₁) :=
      exposedFace_eq_activeConstraintFace_activeRemainingRows rfl hF₁_exposed hF₁_nonempty
    have hF₂_eq :
        F₂ = active_constraint_face A b (faceRowsAmbient F₂) :=
      exposedFace_eq_activeConstraintFace_activeRemainingRows rfl hF₂_exposed hF₂_nonempty
    calc
      F₁ = active_constraint_face A b (faceRowsAmbient F₁) := hF₁_eq
      _ = active_constraint_face A b (faceRowsAmbient F₂) := by rw [hRowsAmbientEq]
      _ = F₂ := hF₂_eq.symm
  -- Compare the finite counted face family with the full powerset of the remaining-row type.
  have huniv_card :
      (Set.univ : Set (Finset rowsType)).ncard =
        2 ^ (remaining_inequality_indices A b).ncard := by
    calc
      (Set.univ : Set (Finset rowsType)).ncard = Fintype.card (Finset rowsType) := by
            rw [Set.ncard_univ, Nat.card_eq_fintype_card]
      _ = 2 ^ Fintype.card rowsType := by
            rw [Fintype.card_finset]
      _ = 2 ^ (remaining_inequality_indices A b).ncard := by
            have hrows_card : Fintype.card rowsType = (remaining_inequality_indices A b).ncard := by
              simpa [rowsType] using
                (Set.fintypeCard_eq_ncard (s := remaining_inequality_indices A b))
            rw [hrows_card]
  calc
    faceCount (polyhedron_le_set A b) = countedFaces.ncard := by rfl
    _ ≤ (Set.univ : Set (Finset rowsType)).ncard := by
          exact
            Set.ncard_le_ncard_of_injOn
              faceRows
              (by intro F hF; simp)
              hfaceRows_inj
              (Set.toFinite _)
    _ ≤ 2 ^ (remaining_inequality_indices A b).ncard := by
          rw [huniv_card]

/-- Helper for Exercise 4.38: an irredundant remaining row cuts out a codimension-one singleton
active face. -/
lemma finrank_direction_affineSpan_add_one_eq_of_irredundantSingleton
    {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m)
    (hj : j ∈ remaining_inequality_indices A b)
    (hj_irredundant : is_irredundant_row A b j) :
    Module.finrank ℝ
        (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction + 1 =
      Module.finrank ℝ
        (affineSpan ℝ (polyhedron_le_set A b)).direction := by
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b j hj with
    ⟨x, hxP, hxlt⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x, hxP⟩
  have hj_not_implicit : ¬ is_implicit_equality A b j :=
    (mem_remaining_inequality_indices_iff A b j).1 hj
  have hdim :
      Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction =
        Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction - 1 :=
    finrank_direction_affineSpan_active_constraint_face_singleton_eq_sub_one
      A b j hP_nonempty hj_not_implicit hj_irredundant
  obtain ⟨xhat, hxhat_face, _⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b j hP_nonempty hj_irredundant
  have hxhatP : xhat ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hxhat_face
  have hxhat_row : (Matrix.mulVec A xhat) j = b j :=
    (mem_active_constraint_face_iff.mp hxhat_face).1 j (by simp)
  have hxhat_ne_x : xhat ≠ x := by
    intro hEq
    have hx_row : (Matrix.mulVec A x) j = b j := by
      simpa [hEq] using hxhat_row
    exact (ne_of_lt hxlt) hx_row
  let v : Fin k → ℝ := xhat - x
  have hv_mem :
      v ∈ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    have hx_aff :
        x ∈ affineSpan ℝ (polyhedron_le_set A b) :=
      subset_affineSpan ℝ (polyhedron_le_set A b) hxP
    have hxhat_aff :
        xhat ∈ affineSpan ℝ (polyhedron_le_set A b) :=
      subset_affineSpan ℝ (polyhedron_le_set A b) hxhatP
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx_aff]
    refine ⟨xhat, hxhat_aff, ?_⟩
    simp [v, vsub_eq_sub]
  have hv_ne : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr hxhat_ne_x
  have hP_dim_pos :
      0 < Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨v, hv_mem⟩, by simpa using hv_ne⟩
  have hP_dim_ge :
      1 ≤ Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction :=
    Nat.succ_le_of_lt hP_dim_pos
  have hdim_rev :
      Module.finrank ℝ
          (affineSpan ℝ (polyhedron_le_set A b)).direction - 1 =
        Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction :=
    hdim.symm
  have hcodim :
      Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction =
        Module.finrank ℝ
          (affineSpan ℝ (active_constraint_face A b ({j} : Set (Fin m)))).direction + 1 :=
    (Nat.sub_eq_iff_eq_add hP_dim_ge).mp hdim_rev
  -- Rewrite the subtraction form from Lemma 3.26 as the codimension-one identity used here.
  simpa [Nat.add_comm] using hcodim.symm

/-- Helper for Exercise 4.38: under irredundancy, different remaining rows define different
singleton active faces. -/
lemma activeConstraintFaceSingleton_injective_ofIrredundantPresentation
    {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) ℝ)
    (b : Fin m → ℝ)
    (hminimal :
      ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    Function.Injective
      (fun i : {i // i ∈ remaining_inequality_indices A b} ↦
        active_constraint_face A b ({i.1} : Set (Fin m))) := by
  intro i j hij
  by_contra hij_ne
  have hi_not_implicit : ¬ is_implicit_equality A b i.1 :=
    (mem_remaining_inequality_indices_iff A b i.1).1 i.2
  have hi_irredundant : is_irredundant_row A b i.1 := hminimal i.1 hi_not_implicit
  rcases exists_mem_polyhedron_le_set_lt_of_mem_remaining_inequality_indices A b i.1 i.2 with
    ⟨x, hxP, _⟩
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x, hxP⟩
  obtain ⟨xhat, hxhat_face, hhat_strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A b i.1 hP_nonempty hi_irredundant
  have hxhat_face' : xhat ∈ active_constraint_face A b ({j.1} : Set (Fin m)) := by
    simpa [hij] using hxhat_face
  have hji : j.1 ≠ i.1 := by
    intro hji_eq
    apply hij_ne
    exact Subtype.ext hji_eq.symm
  have hj_not_implicit : ¬ is_implicit_equality A b j.1 :=
    (mem_remaining_inequality_indices_iff A b j.1).1 j.2
  have hxhat_lt :
      (Matrix.mulVec A xhat) j.1 < b j.1 :=
    hhat_strict j.1 hji hj_not_implicit
  have hxhat_eq :
      (Matrix.mulVec A xhat) j.1 = b j.1 :=
    (mem_active_constraint_face_iff.mp hxhat_face').1 j.1 (by simp)
  exact (ne_of_lt hxhat_lt) hxhat_eq

/-- Helper for Exercise 4.38: on an irredundant flat presentation, the remaining rows inject into
the current file's `IsFacetOf` family. -/
lemma cardRemainingRows_le_facetCountOfIrredundantPolyhedron
    {m k : ℕ}
    {P : Set (Fin k → ℝ)}
    {A : Matrix (Fin m) (Fin k) ℝ}
    {b : Fin m → ℝ}
    (hP_eq : P = polyhedron_le_set A b)
    (hP_nonempty : P.Nonempty)
    (hminimal :
      ∀ i : Fin m, ¬ is_implicit_equality A b i → is_irredundant_row A b i) :
    (remaining_inequality_indices A b).ncard ≤
      {F : Set (Fin k → ℝ) | IsFacetOf P F}.ncard := by
  classical
  subst hP_eq
  let rowFacet :
      {i // i ∈ remaining_inequality_indices A b} → Set (Fin k → ℝ) :=
    fun i ↦ active_constraint_face A b ({i.1} : Set (Fin m))
  have hfacet_maps :
      Set.MapsTo rowFacet Set.univ
        {F : Set (Fin k → ℝ) | IsFacetOf (polyhedron_le_set A b) F} := by
    intro i _
    have hi_not_implicit : ¬ is_implicit_equality A b i.1 :=
      (mem_remaining_inequality_indices_iff A b i.1).1 i.2
    have hi_irredundant : is_irredundant_row A b i.1 := hminimal i.1 hi_not_implicit
    obtain ⟨xhat, hxhat_face, _⟩ :=
      exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
        A b i.1 hP_nonempty hi_irredundant
    have hcodim :
        Module.finrank ℝ
            (affineSpan ℝ (active_constraint_face A b ({i.1} : Set (Fin m)))).direction + 1 =
          Module.finrank ℝ
            (affineSpan ℝ (polyhedron_le_set A b)).direction :=
      finrank_direction_affineSpan_add_one_eq_of_irredundantSingleton
        A b i.1 i.2 hi_irredundant
    exact (isFacetOf_iff).2
      ⟨⟨xhat, hxhat_face⟩, active_constraint_face_isExposed A b ({i.1} : Set (Fin m)), hcodim⟩
  have hfacet_finite :
      {F : Set (Fin k → ℝ) | IsFacetOf (polyhedron_le_set A b) F}.Finite := by
    exact
      (polyhedron_finite_faces (P := polyhedron_le_set A b)
        ((is_polyhedron_iff).2 ⟨m, A, b, rfl⟩)).subset fun F hF ↦ hF.2.1
  have hRowsCard :
      (remaining_inequality_indices A b).ncard = (Set.range rowFacet).ncard := by
    calc
      (remaining_inequality_indices A b).ncard =
          Fintype.card {i // i ∈ remaining_inequality_indices A b} := by
            simpa using
              (Set.fintypeCard_eq_ncard (s := remaining_inequality_indices A b)).symm
      _ = (Set.range rowFacet).ncard := by
            simpa [rowFacet] using
              (Set.ncard_range_of_injective
                (activeConstraintFaceSingleton_injective_ofIrredundantPresentation
                  A b hminimal)).symm
  have hrange_le :
      (Set.range rowFacet).ncard ≤
        {F : Set (Fin k → ℝ) | IsFacetOf (polyhedron_le_set A b) F}.ncard := by
    exact Set.ncard_le_ncard (by
      intro F hF
      rcases hF with ⟨i, rfl⟩
      simpa using hfacet_maps (x := i) (by simp : i ∈ Set.univ)) hfacet_finite
  exact hRowsCard.le.trans hrange_le

/-- Helper for Exercise 4.38: deleting row `j` via `Fin.succAbove` keeps exactly the inequalities
indexed by rows different from `j`. -/
lemma mem_deleteRow_mulVec_le_iff
    {m k : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin k) ℝ}
    {b : Fin (m + 1) → ℝ}
    (j : Fin (m + 1))
    (x : Fin k → ℝ) :
    Matrix.mulVec (A.submatrix (Fin.succAbove j) id) x ≤ b ∘ Fin.succAbove j ↔
      ∀ i : Fin (m + 1), i ≠ j → (Matrix.mulVec A x) i ≤ b i := by
  constructor
  · intro hx i hij
    rcases (Fin.eq_self_or_eq_succAbove j i) with rfl | ⟨r, rfl⟩
    · exact False.elim (hij rfl)
    · -- A row away from `j` is exactly one of the deleted-system rows.
      simpa [Matrix.mulVec] using hx r
  · intro hx r
    -- Every row in the deleted system comes from an ambient row different from `j`.
    simpa [Matrix.mulVec] using hx (j.succAbove r) (Fin.succAbove_ne j r)

/-- Helper for Exercise 4.38: if row `j` is not irredundant, removing it does not change the
polyhedron. -/
lemma deleteNonirredundantRow_preservesPolyhedron
    {m k : ℕ}
    {A : Matrix (Fin (m + 1)) (Fin k) ℝ}
    {b : Fin (m + 1) → ℝ}
    (j : Fin (m + 1))
    (hj : ¬ is_irredundant_row A b j) :
    polyhedron_le_set (A.submatrix (Fin.succAbove j) id) (b ∘ Fin.succAbove j) =
      polyhedron_le_set A b := by
  ext x
  constructor
  · intro hx
    have hdeleted :
        ∀ i : Fin (m + 1), i ≠ j → (Matrix.mulVec A x) i ≤ b i :=
      (mem_deleteRow_mulVec_le_iff j x).1 hx
    intro i
    by_cases hij : i = j
    · subst i
      -- Route correction: the missing row bound comes from the negation of irredundancy, not from
      -- any transport through remaining-row indices.
      have hnot_strict : ¬ (b j < (Matrix.mulVec A x) j) := by
        intro hj_strict
        exact hj ⟨x, hdeleted, hj_strict⟩
      exact le_of_not_gt hnot_strict
    · exact hdeleted i hij
  · intro hx
    -- Feasibility for the full system obviously restricts to the deleted subsystem.
    exact (mem_deleteRow_mulVec_le_iff j x).2 fun i hi ↦ hx i

/-- Helper for Exercise 4.38: every nonempty flat polyhedron admits an equivalent presentation in
which every non-implicit row is irredundant. -/
lemma existsIrredundantPresentationOfNonemptyPolyhedron
    {m k : ℕ}
    {A : Matrix (Fin m) (Fin k) ℝ}
    {b : Fin m → ℝ}
    (h_nonempty : (polyhedron_le_set A b).Nonempty) :
    ∃ m' : ℕ, ∃ A' : Matrix (Fin m') (Fin k) ℝ, ∃ b' : Fin m' → ℝ,
      polyhedron_le_set A' b' = polyhedron_le_set A b ∧
        ∀ i : Fin m', ¬ is_implicit_equality A' b' i → is_irredundant_row A' b' i := by
  classical
  induction m with
  | zero =>
      refine ⟨0, A, b, rfl, ?_⟩
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      by_cases hminimal :
          ∀ i : Fin (m + 1), ¬ is_implicit_equality A b i → is_irredundant_row A b i
      · -- If the current presentation is already minimal on non-implicit rows, keep it.
        exact ⟨m + 1, A, b, rfl, hminimal⟩
      · -- Otherwise choose a non-implicit row that is not irredundant and delete it.
        have hbad :
            ∃ j : Fin (m + 1),
              ¬ (¬ is_implicit_equality A b j → is_irredundant_row A b j) := by
          simpa using not_forall.mp hminimal
        rcases hbad with ⟨j, hj_bad⟩
        have hj_not_implicit : ¬ is_implicit_equality A b j := by
          intro hj_implicit
          exact hj_bad (by
            intro hj_nonimplicit
            exact False.elim (hj_nonimplicit hj_implicit))
        have hj_not_irredundant : ¬ is_irredundant_row A b j := by
          intro hj_irredundant
          exact hj_bad (by intro _; exact hj_irredundant)
        let ADel : Matrix (Fin m) (Fin k) ℝ := A.submatrix (Fin.succAbove j) id
        let bDel : Fin m → ℝ := b ∘ Fin.succAbove j
        have hdelete :
            polyhedron_le_set ADel bDel = polyhedron_le_set A b :=
          deleteNonirredundantRow_preservesPolyhedron j hj_not_irredundant
        have hDel_nonempty : (polyhedron_le_set ADel bDel).Nonempty := by
          rw [hdelete]
          exact h_nonempty
        rcases ih (A := ADel) (b := bDel) hDel_nonempty with
          ⟨m', A', b', hEq, hA'⟩
        refine ⟨m', A', b', ?_, hA'⟩
        -- The recursive presentation is equivalent to the original one through the deleted system.
        exact hEq.trans hdelete

/-- Helper for Exercise 4.38: the remaining counting argument is purely flat, with both faces and
facets already transported to `Set (Fin k → ℝ)`. -/
lemma polytopeFacesLeTwoPowFacetsFlat
    {k : ℕ}
    {P : Set (Fin k → ℝ)}
    (hP : P.IsPolytope ℝ) :
    faceCount P ≤ 2 ^ {F : Set (Fin k → ℝ) | IsFacetOf P F}.ncard := by
  classical
  -- Route correction: the mixed-space theorem should first be normalized to the flat ambient
  -- space before any counting-by-signatures argument is attempted.
  by_cases hP_empty : P = ∅
  · -- The empty polytope has no counted nonempty faces, so the bound is immediate.
    subst hP_empty
    have hcounted_empty :
        {F : Set (Fin k → ℝ) | IsExposed ℝ (∅ : Set (Fin k → ℝ)) F ∧ F.Nonempty} = ∅ := by
      ext F
      constructor
      · intro hF
        rcases hF with ⟨hF_exposed, hF_nonempty⟩
        rcases hF_nonempty with ⟨x, hxF⟩
        simpa using hF_exposed.subset hxF
      · simp
    simp [faceCount_eq, hcounted_empty]
  have hP_polyhedron : is_polyhedron P := (polytope_iff_bounded_polyhedron P).1 hP |>.1
  rcases is_polyhedron_iff.mp hP_polyhedron with ⟨m, A, b, hP_eq⟩
  have hP_nonempty : P.Nonempty := by
    exact Set.nonempty_iff_ne_empty.mpr hP_empty
  have hPoly_nonempty : (polyhedron_le_set A b).Nonempty := by
    simpa [hP_eq] using hP_nonempty
  obtain ⟨m', A', b', hA', hminimal⟩ :=
    existsIrredundantPresentationOfNonemptyPolyhedron (A := A) (b := b) hPoly_nonempty
  have hP_eq' : P = polyhedron_le_set A' b' := by
    calc
      P = polyhedron_le_set A b := hP_eq
      _ = polyhedron_le_set A' b' := hA'.symm
  -- First count nonempty exposed faces by active remaining rows in the irredundant presentation,
  -- then rewrite that row count as the facet count of `P`.
  calc
    faceCount P ≤ 2 ^ (remaining_inequality_indices A' b').ncard := by
      simpa [hP_eq'] using
        faceCount_le_two_pow_remainingRowsOfPolyhedron (A := A') (b := b') hP_eq'
    _ ≤ 2 ^ {F : Set (Fin k → ℝ) | IsFacetOf P F}.ncard := by
      exact Nat.pow_le_pow_right (by decide)
        (cardRemainingRows_le_facetCountOfIrredundantPolyhedron
          (A := A') (b := b') hP_eq' hP_nonempty hminimal)

/-- Helper for Exercise 4.38: a polytope has at most `2 ^ (# facets)` nonempty faces under
`faceCount`. -/
lemma polytope_faces_le_two_pow_facets
    {n p : ℕ}
    {Q : Set (MixedRealPoint n p)} (hQ : Q.IsPolytope ℝ) :
    faceCount Q ≤ 2 ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard := by
  let eL :
      MixedRealPoint n p ≃ₗ[ℝ] (Fin (n + p) → ℝ) :=
    (Fin.appendEquiv (α := ℝ) n p).toLinearEquiv appendEquivIsLinearMap
  let e :
      MixedRealPoint n p ≃L[ℝ] (Fin (n + p) → ℝ) :=
    eL.toContinuousLinearEquiv
  have hQflat : (e '' Q).IsPolytope ℝ := isPolytope_image_continuousLinearEquiv e hQ
  -- Normalize the mixed-space face bound to the flat Chapter 3 owner before the remaining
  -- counting argument.
  calc
    faceCount Q = faceCount ((Fin.appendEquiv n p) '' Q) := faceCount_appendEquiv_eq Q
    _ ≤ 2 ^ {F : Set (Fin (n + p) → ℝ) | IsFacetOf ((Fin.appendEquiv n p) '' Q) F}.ncard := by
          simpa [e] using polytopeFacesLeTwoPowFacetsFlat hQflat
    _ = 2 ^ {F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard := by
          rw [← facetCount_appendEquiv_eq]

/-- Helper for Exercise 4.38: part (2) shows that if `P` and `Q` are polytopes with
`P = proj_x(Q)`, then the number of facets of `Q` is at least the logarithm of the number of
faces of `P`. -/
theorem log_face_count_le_facet_count
    {n p : ℕ}
    (P : Set (Fin n → ℝ))
    (Q : Set (MixedRealPoint n p))
    (hP : P.IsPolytope ℝ)
    (hQ : Q.IsPolytope ℝ)
    (hproj : P = Prod.fst '' Q) :
    Real.logb 2 (faceCount P) ≤
      ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
  -- Part (2) is the projection monotonicity from part (1) combined with the polytope face bound.
  let _ := hP
  exact log_face_count_le_facet_count_of_face_bound P Q hQ hproj
    (polytope_faces_le_two_pow_facets hQ)

/-- Helper for Exercise 4.38: the top half of the factors in `n!` each contribute at least
`n / 2`. -/
lemma half_pow_half_le_factorial (n : ℕ) : (n / 2) ^ (n / 2) ≤ Nat.factorial n := by
  let k := n / 2
  have htwo_k_le_n : k + k ≤ n := by
    calc
      k + k = 2 * (n / 2) := by simp [k, two_mul]
      _ ≤ 2 * (n / 2) + n % 2 := Nat.le_add_right _ _
      _ = n := by exact Nat.div_add_mod n 2
  have hk_pow_le_fact_two_k : k ^ k ≤ Nat.factorial (k + k) := by
    calc
      k ^ k ≤ Nat.factorial k * (k + 1) ^ k := by
        have hfactorial_ge_one : 1 ≤ Nat.factorial k := Nat.succ_le_of_lt (Nat.factorial_pos k)
        have hpow_mono : k ^ k ≤ (k + 1) ^ k := by
          exact Nat.pow_le_pow_left (Nat.le_succ k) k
        exact le_trans hpow_mono (by
          simpa [one_mul] using Nat.mul_le_mul_right ((k + 1) ^ k) hfactorial_ge_one)
      _ ≤ Nat.factorial (k + k) := by
        have hfactorial :
            Nat.factorial k * (k + 1) ^ k ≤ Nat.factorial (k + k) :=
          Nat.factorial_mul_pow_le_factorial
        simpa [k, Nat.two_mul] using hfactorial
  -- Monotonicity of the factorial extends the bound from `2 * (n / 2)` to all of `n`.
  exact le_trans hk_pow_le_fact_two_k (Nat.factorial_le htwo_k_le_n)

/-- Helper for Exercise 4.38: the real half-power bound `((n : ℝ) / 2) ^ ((n : ℝ) / 2)` is still
dominated by `n!`. -/
lemma halfRpow_le_factorial (n : ℕ) :
    ((n : ℝ) / 2) ^ ((n : ℝ) / 2) ≤ Nat.factorial n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- The even case is exactly the integer half-power estimate.
    norm_num [Real.rpow_natCast]
    have hdiv : (k + k) / 2 = k := by omega
    have hnat : k ^ k ≤ Nat.factorial (k + k) := by
      simpa [hdiv] using half_pow_half_le_factorial (k + k)
    exact_mod_cast hnat
  · -- In the odd case, round the half-power up to `(k + 1)^(k + 1)` and compare with `(2k + 1)!`.
    have hhalf_eq : (((2 * k + 1 : ℕ) : ℝ) / 2) = (k : ℝ) + 1 / 2 := by
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      field_simp [htwo]
      norm_num [Nat.cast_add, Nat.cast_mul]
    have hbase_nonneg : 0 ≤ (((2 * k + 1 : ℕ) : ℝ) / 2) := by positivity
    have hbase_le :
        (((2 * k + 1 : ℕ) : ℝ) / 2) ≤ (k + 1 : ℝ) := by
      nlinarith [hhalf_eq]
    have hexp_nonneg : 0 ≤ (((2 * k + 1 : ℕ) : ℝ) / 2) := by positivity
    have hpow_base :
        ((((2 * k + 1 : ℕ) : ℝ) / 2) ^ (((2 * k + 1 : ℕ) : ℝ) / 2)) ≤
          (k + 1 : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) := by
      exact Real.rpow_le_rpow hbase_nonneg hbase_le hexp_nonneg
    have hbase_ge_one : 1 ≤ (k + 1 : ℝ) := by nlinarith
    have hexp_le :
        (((2 * k + 1 : ℕ) : ℝ) / 2) ≤ (k + 1 : ℝ) := by
      nlinarith [hhalf_eq]
    have hpow_exp :
        (k + 1 : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) ≤ (k + 1 : ℝ) ^ (k + 1 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
    have hnat :
        (k + 1) ^ (k + 1) ≤ Nat.factorial (2 * k + 1) := by
      have hfactorial_ge_one : 1 ≤ Nat.factorial k :=
        Nat.succ_le_of_lt (Nat.factorial_pos k)
      have hmul :
          Nat.factorial k * (k + 1) ^ (k + 1) ≤ Nat.factorial (k + (k + 1)) :=
        Nat.factorial_mul_pow_le_factorial
      have hpow_le :
          (k + 1) ^ (k + 1) ≤ Nat.factorial k * (k + 1) ^ (k + 1) := by
        simpa [one_mul] using
          Nat.mul_le_mul_right ((k + 1) ^ (k + 1)) hfactorial_ge_one
      exact le_trans hpow_le (by simpa [Nat.add_assoc, Nat.two_mul] using hmul)
    -- The natural-number factorial estimate closes the odd branch after rewriting the exponent.
    calc
      ((((2 * k + 1 : ℕ) : ℝ) / 2) ^ (((2 * k + 1 : ℕ) : ℝ) / 2))
          ≤ (k + 1 : ℝ) ^ (((2 * k + 1 : ℕ) : ℝ) / 2) := hpow_base
      _ ≤ (k + 1 : ℝ) ^ (k + 1 : ℝ) := hpow_exp
      _ = ((k + 1) ^ (k + 1) : ℕ) := by
        have hcast : (k + 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by exact_mod_cast rfl
        rw [hcast, Real.rpow_natCast, Nat.cast_pow]
      _ ≤ Nat.factorial (2 * k + 1) := by exact_mod_cast hnat

/-- Helper for Exercise 4.38: the factorial lower bound implies the textbook real-valued
`((n : ℝ) / 2) * log_2 ((n : ℝ) / 2)` bound after applying the base-two logarithm. -/
lemma half_mul_log2_half_le_log2_factorial (n : ℕ) :
    ((n : ℝ) / 2) * Real.logb 2 ((n : ℝ) / 2) ≤
      Real.logb 2 (Nat.factorial n) := by
  by_cases hn : n = 0
  · -- The zero case collapses both sides to `0`.
    simp [hn]
  · have hhalf_pos : 0 < (n : ℝ) / 2 := by
      positivity
    have hhalf_rpow_pos : 0 < ((n : ℝ) / 2) ^ ((n : ℝ) / 2) := by
      exact Real.rpow_pos_of_pos hhalf_pos ((n : ℝ) / 2)
    have hlog :
        Real.logb 2 (((n : ℝ) / 2) ^ ((n : ℝ) / 2)) ≤ Real.logb 2 (Nat.factorial n) := by
      -- Apply monotonicity of `logb` to the half-power bound.
      exact Real.logb_le_logb_of_le (by norm_num) hhalf_rpow_pos (halfRpow_le_factorial n)
    -- Rewrite the left-hand logarithm as the expected product.
    calc
      ((n : ℝ) / 2) * Real.logb 2 ((n : ℝ) / 2)
          = Real.logb 2 (((n : ℝ) / 2) ^ ((n : ℝ) / 2)) := by
              symm
              exact Real.logb_rpow_eq_mul_logb_of_pos hhalf_pos
      _ ≤ Real.logb 2 (Nat.factorial n) := hlog

/-- Helper for Exercise 4.38: `ascending_vector n` is strictly increasing in the coordinate
index. -/
lemma ascendingVector_strictMono (n : ℕ) : StrictMono (ascending_vector n) := by
  intro i j hij
  have hij' : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by
    exact_mod_cast hij
  simpa [ascending_vector] using add_lt_add_right hij' (1 : ℝ)

/-- Helper for Exercise 4.38: reindexing the dot product of two permutation vertices by `σ`
rewrites it as a rearrangement sum for `τ * σ.symm`. -/
lemma dotProduct_permutedAscendingVector_eq_sum_mul_comp_perm
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ) =
      ∑ i : Fin n, ascending_vector n i * ascending_vector n ((τ * σ.symm) i) := by
  calc
    dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ)
        = ∑ i : Fin n, ascending_vector n (σ i) * ascending_vector n (τ i) := by
            simp [dotProduct]
    _ = ∑ i : Fin n,
          ascending_vector n (σ (σ.symm i)) * ascending_vector n (τ (σ.symm i)) := by
            symm
            simpa using
              (Equiv.sum_comp (e := σ.symm)
                (g := fun i : Fin n ↦ ascending_vector n (σ i) * ascending_vector n (τ i)))
    _ = ∑ i : Fin n, ascending_vector n i * ascending_vector n ((τ * σ.symm) i) := by
          simp [Equiv.Perm.mul_apply]

/-- Helper for Exercise 4.38: among permutation vertices, the dot product with
`ascending_vector n ∘ σ` is maximized at the same vertex. -/
lemma permutahedronPermutationVertex_dotProduct_le
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ) ≤
      dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ σ) := by
  calc
    dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ)
        = ∑ i : Fin n, ascending_vector n i * ascending_vector n ((τ * σ.symm) i) := by
            exact dotProduct_permutedAscendingVector_eq_sum_mul_comp_perm n σ τ
    _ ≤ ∑ i : Fin n, ascending_vector n i * ascending_vector n i := by
          exact Monovary.sum_mul_comp_perm_le_sum_mul
            (σ := τ * σ.symm)
            (f := ascending_vector n)
            (g := ascending_vector n)
            (monovary_self (ascending_vector n))
    _ = dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ σ) := by
          simpa using
            (dotProduct_permutedAscendingVector_eq_sum_mul_comp_perm n σ σ).symm

/-- Helper for Exercise 4.38: equality in the rearrangement bound forces the same permutation
vertex. -/
lemma permutahedronPermutationVertex_dotProduct_eq_iff
    (n : ℕ) (σ τ : Equiv.Perm (Fin n)) :
    dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ) =
      dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ σ) ↔
        τ = σ := by
  constructor
  · intro hEq
    have hsumEq :
        ∑ i : Fin n, ascending_vector n i * ascending_vector n ((τ * σ.symm) i) =
          ∑ i : Fin n, ascending_vector n i * ascending_vector n i := by
      calc
        ∑ i : Fin n, ascending_vector n i * ascending_vector n ((τ * σ.symm) i)
            = dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ) := by
                simpa using
                  (dotProduct_permutedAscendingVector_eq_sum_mul_comp_perm n σ τ).symm
        _ = dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ σ) := hEq
        _ = ∑ i : Fin n, ascending_vector n i * ascending_vector n i := by
              simpa using dotProduct_permutedAscendingVector_eq_sum_mul_comp_perm n σ σ
    let ρ : Equiv.Perm (Fin n) := τ * σ.symm
    have hmonovary :
        Monovary (ascending_vector n) (ascending_vector n ∘ ρ) := by
      exact
        (Monovary.sum_mul_comp_perm_eq_sum_mul_iff
          (σ := ρ)
          (f := ascending_vector n)
          (g := ascending_vector n)
          (monovary_self (ascending_vector n))).1 hsumEq
    have hmonovary' :
        Monovary (ascending_vector n ∘ ρ) (ascending_vector n) := by
      exact (monovary_comm).1 hmonovary
    have hmonoComp : Monotone (ascending_vector n ∘ ρ) :=
      (ascendingVector_strictMono n).trans_monovary hmonovary'
    have hmonoPerm : Monotone ρ := by
      intro i j hij
      exact (ascendingVector_strictMono n).le_iff_le.mp (hmonoComp hij)
    have hmul_eq_one : τ * σ.symm = 1 :=
      (Equiv.Perm.monotone_iff (τ * σ.symm)).1 hmonoPerm
    apply Equiv.ext
    intro i
    have happly :
        (τ * σ.symm) (σ i) = (1 : Equiv.Perm (Fin n)) (σ i) := by
      simpa using congrArg (fun e : Equiv.Perm (Fin n) ↦ e (σ i)) hmul_eq_one
    simpa [Equiv.Perm.mul_apply] using happly
  · intro hEq
    subst hEq
    rfl

/-- Helper for Exercise 4.38: the support functional `dotProductStrongDual (ascending_vector n ∘ σ)`
is maximized on `permutahedron n` at the permutation vertex `ascending_vector n ∘ σ`. -/
lemma permutahedronPermutationVertex_mem_toExposed
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ascending_vector n ∘ σ ∈
      (dotProductStrongDual (ascending_vector n ∘ σ)).toExposed (permutahedron n) := by
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let l : StrongDual ℝ (Fin n → ℝ) := dotProductStrongDual x
  have hx_perm : x ∈ permutahedron n := by
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr ⟨σ, rfl⟩)
  refine ⟨hx_perm, ?_⟩
  intro y hy_perm
  have hy_hull : y ∈ convexHull ℝ (permutahedron_vertices n) := by
    simpa [permutahedron_eq_convexHull] using hy_perm
  obtain ⟨z, hz_vertex, hy_le⟩ :=
    ConvexOn.exists_ge_of_mem_convexHull
      (LinearMap.convexOn l.toLinearMap convex_univ)
      (by intro z hz; simp)
      hy_hull
  rcases mem_permutahedron_vertices_iff.mp hz_vertex with ⟨τ, rfl⟩
  have hz_le : l (ascending_vector n ∘ τ) ≤ l x := by
    simpa [l, x, dotProductStrongDual_apply] using
      permutahedronPermutationVertex_dotProduct_le n σ τ
  exact le_trans hy_le hz_le

/-- Helper for Exercise 4.38: the support face cut out by
`dotProductStrongDual (ascending_vector n ∘ σ)` has no extreme points other than
`ascending_vector n ∘ σ`. -/
lemma permutahedronSupportFace_extremePoints_subset_singleton
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ((dotProductStrongDual (ascending_vector n ∘ σ)).toExposed (permutahedron n)).extremePoints ℝ ⊆
      {ascending_vector n ∘ σ} := by
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let l : StrongDual ℝ (Fin n → ℝ) := dotProductStrongDual x
  let F : Set (Fin n → ℝ) := l.toExposed (permutahedron n)
  have hF_exposed : IsExposed ℝ (permutahedron n) F :=
    ContinuousLinearMap.toExposed.isExposed
  have hx_perm : x ∈ permutahedron n := by
    rw [permutahedron_eq_convexHull]
    exact subset_convexHull ℝ (permutahedron_vertices n)
      (mem_permutahedron_vertices_iff.mpr ⟨σ, rfl⟩)
  have hxF : x ∈ F := by
    simpa [F, l, x] using permutahedronPermutationVertex_mem_toExposed n σ
  intro z hz_extreme
  have hzF : z ∈ F := extremePoints_subset hz_extreme
  have hz_perm_extreme : z ∈ (permutahedron n).extremePoints ℝ :=
    hF_exposed.isExtreme.extremePoints_subset_extremePoints hz_extreme
  have hz_vertex : z ∈ permutahedron_vertices n := by
    rw [permutahedron_eq_convexHull] at hz_perm_extreme
    exact extremePoints_convexHull_subset hz_perm_extreme
  rcases mem_permutahedron_vertices_iff.mp hz_vertex with ⟨τ, rfl⟩
  have hz_le : l (ascending_vector n ∘ τ) ≤ l x := by
    exact hxF.2 _ hzF.1
  have hx_le : l x ≤ l (ascending_vector n ∘ τ) := by
    exact hzF.2 _ hx_perm
  have hEq :
      dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ τ) =
        dotProduct (ascending_vector n ∘ σ) (ascending_vector n ∘ σ) := by
    simpa [l, x, dotProductStrongDual_apply] using le_antisymm hz_le hx_le
  have hτσ : τ = σ := (permutahedronPermutationVertex_dotProduct_eq_iff n σ τ).1 hEq
  simp [hτσ]

/-- Helper for Exercise 4.38: each permutation vertex of the permutahedron is an exposed point,
because its supporting face has no other extreme points. -/
lemma permutahedronPermutationVertex_isExposed
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    IsExposed ℝ (permutahedron n) {ascending_vector n ∘ σ} := by
  let x : Fin n → ℝ := ascending_vector n ∘ σ
  let l : StrongDual ℝ (Fin n → ℝ) := dotProductStrongDual x
  let F : Set (Fin n → ℝ) := l.toExposed (permutahedron n)
  have hperm_polytope : (permutahedron n).IsPolytope ℝ := by
    refine ⟨permutahedron_vertices n, ?_, permutahedron_eq_convexHull n⟩
    simpa [permutahedron_vertices] using
      (Set.finite_range (fun τ : Equiv.Perm (Fin n) ↦ ascending_vector n ∘ τ))
  have hF_exposed : IsExposed ℝ (permutahedron n) F :=
    ContinuousLinearMap.toExposed.isExposed
  have hxF : x ∈ F := by
    simpa [F, l, x] using permutahedronPermutationVertex_mem_toExposed n σ
  have hF_subset : F ⊆ {x} := by
    have hExtreme_subset : F.extremePoints ℝ ⊆ {x} := by
      simpa [F, l, x] using permutahedronSupportFace_extremePoints_subset_singleton n σ
    have hHull_subset : convexHull ℝ (F.extremePoints ℝ) ⊆ {x} :=
      convexHull_min hExtreme_subset (convex_singleton x)
    intro z hzF
    have hzHull : z ∈ convexHull ℝ (F.extremePoints ℝ) := by
      rw [exposed_face_eq_convexHull_extremePoints hperm_polytope hF_exposed] at hzF
      exact hzF
    exact hHull_subset hzHull
  have hF_eq_singleton : F = {x} := by
    ext z
    constructor
    · intro hz
      exact hF_subset hz
    · intro hz
      rcases Set.mem_singleton_iff.mp hz with rfl
      exact hxF
  simpa [F, x, hF_eq_singleton] using hF_exposed

/-- Helper for Exercise 4.38: the permutahedron route needs a factorial-sized family of distinct
faces contributing to `faceCount`. -/
lemma permutahedron_face_count_ge_factorial (n : ℕ) :
    Nat.factorial n ≤ faceCount (permutahedron n) := by
  classical
  have hperm_polytope : (permutahedron n).IsPolytope ℝ := by
    refine ⟨permutahedron_vertices n, ?_, permutahedron_eq_convexHull n⟩
    -- The permutahedron is the convex hull of finitely many permutation vertices.
    simpa [permutahedron_vertices] using
      (Set.finite_range (fun σ : Equiv.Perm (Fin n) ↦ ascending_vector n ∘ σ))
  let countedFaces : Set (Set (Fin n → ℝ)) :=
    {F : Set (Fin n → ℝ) | IsExposed ℝ (permutahedron n) F ∧ F.Nonempty}
  let permutationFace : Equiv.Perm (Fin n) → Set (Fin n → ℝ) :=
    fun σ ↦ {ascending_vector n ∘ σ}
  have hcounted_finite : countedFaces.Finite := by
    refine (polytope_finite_exposed_faces hperm_polytope).subset ?_
    intro F hF
    exact hF.1
  have hmaps :
      Set.range permutationFace ⊆ countedFaces := by
    intro F hF
    rcases hF with ⟨σ, rfl⟩
    constructor
    · -- The remaining blocker is exactly the singleton-exposed-face bridge.
      exact permutahedronPermutationVertex_isExposed n σ
    · exact Set.singleton_nonempty (ascending_vector n ∘ σ)
  have hinj : Function.Injective permutationFace := by
    intro σ τ hστ
    ext i
    have hpoint :
        ascending_vector n (σ i) = ascending_vector n (τ i) := by
      have hfun :
          ascending_vector n ∘ σ = ascending_vector n ∘ τ := by
        simpa using Set.singleton_injective hστ
      simpa [Function.comp_apply] using congrArg (fun f : Fin n → ℝ ↦ f i) hfun
    simpa using congrArg Fin.val (ascendingVector_injective n hpoint)
  have hrange :
      (Set.range permutationFace).ncard = Nat.factorial n := by
    calc
      (Set.range permutationFace).ncard = Fintype.card (Equiv.Perm (Fin n)) := by
        simpa [permutationFace, Nat.card_eq_fintype_card] using
          Set.ncard_range_of_injective hinj
      _ = Nat.factorial n := by
        simpa using
          (show Fintype.card (Equiv.Perm (Fin n)) = Nat.factorial (Fintype.card (Fin n)) from
            Fintype.card_perm)
  -- Count the injective family of exposed singleton faces inside the ambient face family.
  calc
    Nat.factorial n = (Set.range permutationFace).ncard := hrange.symm
    _ ≤ countedFaces.ncard := by
      exact Set.ncard_le_ncard hmaps hcounted_finite
    _ = faceCount (permutahedron n) := by
      simp [countedFaces, faceCount_eq]

/-- Exercise 4.38 (3). If the projection `proj_x(Q)` is the permutahedron `Π_n`, then `Q` has at
least `((n : ℝ) / 2) * log_2 ((n : ℝ) / 2)` facets. -/
theorem permutahedron_projection_facet_lower_bound
    {n p : ℕ}
    (Q : Set (MixedRealPoint n p))
    (hQ : Q.IsPolytope ℝ)
    (hproj : Prod.fst '' Q = permutahedron n) :
    ((n : ℝ) / 2) * Real.logb 2 ((n : ℝ) / 2) ≤
      ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
  have hperm_polytope : (permutahedron n).IsPolytope ℝ := by
    refine ⟨permutahedron_vertices n, ?_, permutahedron_eq_convexHull n⟩
    -- The permutahedron is the convex hull of the finitely many permutation vertices.
    simpa [permutahedron_vertices] using
      (Set.finite_range (fun σ : Equiv.Perm (Fin n) ↦ ascending_vector n ∘ σ))
  have hfactorial_log :
      Real.logb 2 (Nat.factorial n) ≤
        ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
    calc
      Real.logb 2 (Nat.factorial n) ≤ Real.logb 2 (faceCount (permutahedron n)) := by
        have hfactorial_pos : 0 < Nat.factorial n := Nat.factorial_pos n
        exact Real.logb_le_logb_of_le (by norm_num)
          (Nat.cast_pos.mpr hfactorial_pos)
          (by exact_mod_cast permutahedron_face_count_ge_factorial n)
      _ ≤ ({F : Set (MixedRealPoint n p) | IsFacetOf Q F}.ncard : ℝ) := by
        exact log_face_count_le_facet_count (permutahedron n) Q hperm_polytope hQ hproj.symm
  -- Combine the factorial-size face family with the logarithmic factorial estimate.
  exact le_trans (half_mul_log2_half_le_log2_factorial n) hfactorial_log
