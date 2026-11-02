import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_11
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_12
import Mathlib.Analysis.Normed.Affine.Isometry

-- Declarations for this item will be appended below by the statement pipeline.

open scoped IntegerVectorNotation Matrix

-- This exercise reuses the triangle-specific owner `has_integral_triangle_vertices` from
-- Exercise 6.11 together with the canonical Chapter 6 lattice-free owner
-- `is_maximal_lattice_free`, the canonical facet owner `IsFacetOf`, and mathlib's canonical
-- affine-map owner `AffineMap`.

section Exercise613

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The standard maximal lattice-free triangle in `ℝ²` with vertices `(0, 0)`, `(2, 0)`, and
`(0, 2)`. -/
def exercise_6_13_standard_triangle : Affine.Triangle ℝ R2 :=
  ⟨![(![(0 : ℝ), 0] : R2), ![2, 0], ![0, 2]], by
    -- The first two vertices lie on the horizontal affine line through `(0, 0)` and `(2, 0)`.
    -- The third vertex has second coordinate `2`, so it cannot lie on that line.
    refine
      affineIndependent_of_ne_of_mem_of_mem_of_notMem
        (s := affineSpan ℝ ({(![(0 : ℝ), 0] : R2), ![2, 0]} : Set R2)) ?_ ?_ ?_ ?_
    · simp
    · exact left_mem_affineSpan_pair ℝ (![(0 : ℝ), 0] : R2) ![2, 0]
    · exact right_mem_affineSpan_pair ℝ (![(0 : ℝ), 0] : R2) ![2, 0]
    · intro hline
      rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hline with ⟨r, hr⟩
      have hcoord :
          AffineMap.lineMap (![(0 : ℝ), 0] : R2) ![2, 0] r 1 = (![0, 2] : R2) 1 := by
        simpa using congrFun hr 1
      norm_num [AffineMap.lineMap_apply_module] at hcoord
  ⟩

/-- The closed triangular region cut out by `exercise_6_13_standard_triangle`. -/
def exercise_6_13_standard_triangle_region : Set R2 :=
  exercise_6_13_standard_triangle.closedInterior

/-- The standard triangle region is realized by `exercise_6_13_standard_triangle`. -/
theorem has_triangle_vertices_exercise_6_13_standard_triangle_region :
    has_triangle_vertices exercise_6_13_standard_triangle_region
      exercise_6_13_standard_triangle :=
  rfl

/-- The affine map on `ℝ²` given by an integer matrix and an integral translation vector. -/
def integerAffineMap (c : Z2) (M : Matrix (Fin 2) (Fin 2) ℤ) : R2 →ᵃ[ℝ] R2 :=
  ((Matrix.toLin' fun i j ↦ (M i j : ℝ)).toAffineMap) +ᵥ
    AffineMap.const ℝ R2 (fun i ↦ (c i : ℝ))

/-- Helper for Exercise 6.13: expanding `integerAffineMap` yields the expected matrix-vector
formula plus the integral translation term. -/
theorem integerAffineMap_apply
    (c : Z2) (M : Matrix (Fin 2) (Fin 2) ℤ) (x : R2) :
    integerAffineMap c M x =
      fun i ↦ ((M i 0 : ℤ) : ℝ) * x 0 + ((M i 1 : ℤ) : ℝ) * x 1 + (c i : ℝ) := by
  -- Expand the affine map to isolate the concrete coordinate formula used in later normal forms.
  funext i
  fin_cases i
  · simp [integerAffineMap, Matrix.toLin'_apply]
  · simp [integerAffineMap, Matrix.toLin'_apply]

/-- Helper for Exercise 6.13: evaluating `integerAffineMap` on an embedded integer vector is the
same as applying the underlying integer affine transformation before casting to `ℝ²`. -/
theorem integerAffineMap_apply_integerVector
    (c : Z2) (M : Matrix (Fin 2) (Fin 2) ℤ) (z : Z2) :
    integerAffineMap c M (Int.cast ∘ z) = Int.cast ∘ (M *ᵥ z + c) := by
  -- Collapse the real-side coordinate formula back to the corresponding integer matrix product.
  funext i
  fin_cases i <;>
    simp [integerAffineMap_apply, Matrix.mulVec, dotProduct]

/-- Helper for Exercise 6.13: if both coordinates of an integer vector are even, then its
coordinate gcd is divisible by `2`. -/
lemma two_dvd_coefficientGcd_of_even
    (z : Z2)
    (hz : ∀ i : Fin 2, Even (z i)) :
    (2 : ℤ) ∣ coefficientGcd z := by
  -- The coordinate gcd is divisible by every common divisor of the two displayed coordinates.
  rw [coefficientGcd]
  refine Finset.dvd_gcd ?_
  intro i hi
  fin_cases i
  · simpa using (hz 0).two_dvd
  · simpa using (hz 1).two_dvd

/-- Helper for Exercise 6.13: an opposite facet of a triangle is the segment joining the other
two vertices. -/
lemma triangleOppositeFacet_eq_segment
    (t : Affine.Triangle ℝ R2) (i : Fin 3) :
    triangle_opposite_facet t i =
      segment ℝ (t.points (Fin.succAbove i 0)) (t.points (Fin.succAbove i 1)) := by
  -- Rewrite the `1`-simplex closed interior using the standard `Wbtw` descriptions of both sets.
  ext x
  simpa [triangle_opposite_facet, Affine.Simplex.faceOpposite_point_eq_point_succAbove,
    mem_segment_iff_wbtw] using
    (Affine.Simplex.mem_closedInterior_iff_wbtw (s := t.faceOpposite i) (p := x))

/-- Helper for Exercise 6.13: a strict line parameter on a triangle edge is an intrinsic-interior
point of the corresponding explicit segment. -/
lemma triangleEdge_lineMap_mem_intrinsicInterior
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap (t.points (Fin.succAbove i 0))
        (t.points (Fin.succAbove i 1)) r ∈
      intrinsicInterior ℝ
        (segment ℝ (t.points (Fin.succAbove i 0)) (t.points (Fin.succAbove i 1))) := by
  -- Read the opposite-edge intrinsic-interior lemma through the explicit segment model.
  simpa [triangleOppositeFacet_eq_segment] using
    (triangleOppositeFacet_lineMap_mem_intrinsicInterior (t := t) (i := i) hr)

/-- Helper for Exercise 6.13: a triangle witness forces the realized set to span the ambient
plane. This local copy avoids depending on a broken upstream build edge while keeping the canonical
triangle realization surface. -/
lemma triangleAffineSpan_eq_top_of_has_triangle_vertices_local
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t) :
    affineSpan ℝ T = ⊤ := by
  have hrank : Module.finrank ℝ R2 = 2 := by
    simpa using (show Module.finrank ℝ (Fin 2 → ℝ) = 2 by simp)
  have hspan : affineSpan ℝ (Set.range t.points) = ⊤ :=
    Affine.Simplex.span_eq_top t hrank
  have hsubset : Set.range t.points ⊆ t.closedInterior := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact t.point_mem_closedInterior i
  refine top_unique ?_
  rw [ht]
  simpa [hspan] using (affineSpan_mono ℝ hsubset)

/-- Helper for Exercise 6.13: each opposite edge of a realized triangle is a facet of the closed
triangle. This local copy keeps the current item independent of an unavailable upstream theorem
export. -/
lemma triangleOppositeFacet_isFacetOf_local
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (i : Fin 3) :
    IsFacetOf T (triangle_opposite_facet t i) := by
  have hrank : Module.finrank ℝ R2 = 2 := by
    simpa using (show Module.finrank ℝ (Fin 2 → ℝ) = 2 by simp)
  let b : AffineBasis (Fin 3) ℝ R2 :=
    ⟨t.points, t.independent, Affine.Simplex.span_eq_top t hrank⟩
  let l : StrongDual ℝ R2 :=
    ⟨-(b.coord i).linear, (-(b.coord i).linear).continuous_of_finiteDimensional⟩
  let x0 : R2 := t.points (Fin.succAbove i 0)
  have hcoord_sum : ∀ x : R2, ∑ j, b.coord j x = 1 := by
    intro x
    simpa [b] using b.sum_coord_apply_eq_one x
  have hcoord_repr :
      ∀ x : R2, Finset.univ.affineCombination ℝ t.points (fun j ↦ b.coord j x) = x := by
    intro x
    rw [Finset.affineCombination_eq_linear_combination _ _ _ (hcoord_sum x)]
    change ∑ j, b.coord j x • b j = x
    exact b.linear_combination_coord_eq_self x
  have hcoord_linear : ∀ x : R2, b.coord i x = (b.coord i).linear x + b.coord i 0 := by
    intro x
    simpa using (b.coord i).map_vadd 0 x
  have hcoord_nonneg : ∀ {x : R2} {j : Fin 3}, x ∈ T → 0 ≤ b.coord j x := by
    intro x j hx
    rw [ht] at hx
    rw [← hcoord_repr x] at hx
    exact ((t.affineCombination_mem_closedInterior_iff (hcoord_sum x)).mp hx j).1
  have hcoord_zero_of_face :
      ∀ {x : R2}, x ∈ triangle_opposite_facet t i → b.coord i x = 0 := by
    intro x hx
    have hx' : x ∈ (t.faceOpposite i).closedInterior := by
      simpa [triangle_opposite_facet] using hx
    rw [Affine.Simplex.faceOpposite, ← hcoord_repr x] at hx'
    exact
      ((t.affineCombination_mem_closedInterior_face_iff_nonneg
          (fs := ({i}ᶜ : Finset (Fin 3)))
          (h := by simp [Finset.card_compl, NeZero.one_le])
          (hw := hcoord_sum x)).mp hx').2 i (by simp)
  have hx0_face : x0 ∈ triangle_opposite_facet t i := by
    simpa [triangle_opposite_facet, x0] using
      (t.point_mem_closedInterior_faceOpposite_iff (i := i) (j := Fin.succAbove i 0)).2 (by simp)
  have hface_subset : triangle_opposite_facet t i ⊆ T := by
    intro x hx
    rw [ht]
    exact t.closedInterior_faceOpposite_subset_closedInterior i
      (by simpa [triangle_opposite_facet] using hx)
  have h_exposed_eq : triangle_opposite_facet t i = l.toExposed T := by
    ext x
    constructor
    · intro hx
      refine ⟨hface_subset hx, ?_⟩
      intro y hy
      have hy_nonneg : 0 ≤ b.coord i y := hcoord_nonneg hy
      have hx_zero : b.coord i x = 0 := hcoord_zero_of_face hx
      change -(b.coord i).linear y ≤ -(b.coord i).linear x
      linarith [hcoord_linear x, hcoord_linear y]
    · intro hx
      have hx_nonneg : 0 ≤ b.coord i x := hcoord_nonneg hx.1
      have hx0_zero : b.coord i x0 = 0 := hcoord_zero_of_face hx0_face
      have hx_nonpos : b.coord i x ≤ 0 := by
        have hmax := hx.2 x0 (hface_subset hx0_face)
        change -(b.coord i).linear x0 ≤ -(b.coord i).linear x at hmax
        linarith [hcoord_linear x, hcoord_linear x0]
      have hx_zero : b.coord i x = 0 := le_antisymm hx_nonpos hx_nonneg
      rw [ht] at hx
      rw [triangle_opposite_facet, Affine.Simplex.faceOpposite, ← hcoord_repr x]
      refine
        (t.affineCombination_mem_closedInterior_face_iff_nonneg
          (fs := ({i}ᶜ : Finset (Fin 3)))
          (h := by simp [Finset.card_compl, NeZero.one_le])
          (hw := hcoord_sum x)).mpr ?_
      refine ⟨?_, ?_⟩
      · intro j hj
        have hxT : x ∈ T := by
          rw [ht]
          exact hx.1
        exact hcoord_nonneg hxT
      · intro j hj
        have hj' : j = i := by simpa using hj
        simpa [hj'] using hx_zero
  have hface_nonempty : (triangle_opposite_facet t i).Nonempty := ⟨x0, hx0_face⟩
  have hface_dim :
      Module.finrank ℝ (affineSpan ℝ (triangle_opposite_facet t i)).direction = 1 := by
    have hface_aff :
        affineSpan ℝ (triangle_opposite_facet t i) =
          affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
      apply le_antisymm
      · rw [triangle_opposite_facet]
        exact affineSpan_le.2 fun x hx ↦ (t.faceOpposite i).closedInterior_subset_affineSpan hx
      · refine affineSpan_mono ℝ ?_
        intro x hx
        rcases hx with ⟨j, rfl⟩
        exact (t.faceOpposite i).point_mem_closedInterior j
    rw [hface_aff, direction_affineSpan]
    have hcard :
        Module.finrank ℝ (vectorSpan ℝ (Set.range (t.faceOpposite i).points)) + 1 = 2 := by
      simpa using
        (AffineIndependent.finrank_vectorSpan_add_one
          (k := ℝ) (p := (t.faceOpposite i).points) (t.faceOpposite i).independent)
    omega
  have hT_dim :
      Module.finrank ℝ (affineSpan ℝ T).direction = 2 := by
    rw [triangleAffineSpan_eq_top_of_has_triangle_vertices_local ht]
    rw [AffineSubspace.direction_top]
    simpa using hrank
  -- Expose the opposite edge as one codimension-one exposed face of the realized triangle.
  refine (isFacetOf_iff).2 ⟨hface_nonempty, ?_, ?_⟩
  · rw [h_exposed_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  · rw [hface_dim, hT_dim]

/-- Helper for Exercise 6.13: the facet-uniqueness hypothesis can be read directly on each
explicit edge segment of the realized triangle. -/
lemma facetUniqueIntegerPoint_of_triangleOppositeFacet
    {t : Affine.Triangle ℝ R2}
    (i : Fin 3) :
    facet_has_unique_integer_point_in_intrinsicInterior (triangle_opposite_facet t i) →
    facet_has_unique_integer_point_in_intrinsicInterior
      (segment ℝ (t.points (Fin.succAbove i 0)) (t.points (Fin.succAbove i 1))) := by
  -- This is the pure rewrite bridge from the chapter's facet owner to the concrete segment model.
  intro hfacet
  simpa [triangleOppositeFacet_eq_segment] using hfacet

/-- Helper for Exercise 6.13: the three explicit triangle edges inherit the facet-uniqueness
hypothesis from the ambient triangle. -/
lemma triangleEdge_uniqueIntegerPoint
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_facets : facets_have_unique_integer_point_in_intrinsicInterior T) :
    facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ (t.points 0) (t.points 1)) ∧
      facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ (t.points 0) (t.points 2)) ∧
        facet_has_unique_integer_point_in_intrinsicInterior
          (segment ℝ (t.points 1) (t.points 2)) := by
  -- Read each abstract facet condition on `T` through the explicit opposite-edge model.
  have h01 :
      facet_has_unique_integer_point_in_intrinsicInterior
        (segment ℝ (t.points 0) (t.points 1)) := by
    apply facetUniqueIntegerPoint_of_triangleOppositeFacet (t := t) 2
    exact hT_facets _ (triangleOppositeFacet_isFacetOf_local ht 2)
  have h02 :
      facet_has_unique_integer_point_in_intrinsicInterior
        (segment ℝ (t.points 0) (t.points 2)) := by
    apply facetUniqueIntegerPoint_of_triangleOppositeFacet (t := t) 1
    exact hT_facets _ (triangleOppositeFacet_isFacetOf_local ht 1)
  have h12 :
      facet_has_unique_integer_point_in_intrinsicInterior
        (segment ℝ (t.points 1) (t.points 2)) := by
    apply facetUniqueIntegerPoint_of_triangleOppositeFacet (t := t) 0
    exact hT_facets _ (triangleOppositeFacet_isFacetOf_local ht 0)
  exact ⟨h01, h02, h12⟩

/-- Helper for Exercise 6.13: an integral segment with a unique intrinsic-interior lattice point
has an integer half-edge, so its endpoint difference is twice an integer vector. -/
lemma segmentHalfEdge_eq_two_integer_of_uniqueInteriorIntegerPoint
    {p q : R2}
    (hp : p ∈ ℤ^2)
    (hq : q ∈ ℤ^2)
    (hseg : facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ p q)) :
    ∃ u : Z2, q - p = fun i ↦ (2 : ℝ) * (u i : ℝ) := by
  classical
  rcases hseg with ⟨x, hx, huniq⟩
  let m : R2 := midpoint ℝ p q
  let σ : R2 ≃ᵃⁱ[ℝ] R2 := AffineIsometryEquiv.pointReflection ℝ m
  have hσseg : σ '' segment ℝ p q = segment ℝ p q := by
    -- Reflection in the segment midpoint swaps the endpoints and preserves the whole segment.
    calc
      σ '' segment ℝ p q = segment ℝ (σ p) (σ q) := by
        simpa [σ] using image_segment ℝ σ.toAffineMap p q
      _ = segment ℝ q p := by
        simp [σ, m]
      _ = segment ℝ p q := by
        rw [segment_symm]
  have hσx_mem :
      σ x ∈ intrinsicInterior ℝ (segment ℝ p q) := by
    -- Intrinsic interior is preserved by the midpoint reflection, so the reflected witness is
    -- still an intrinsic-interior point of the same segment.
    have himage :
        σ x ∈ intrinsicInterior ℝ (σ.toAffineIsometry '' segment ℝ p q) := by
      rw [AffineIsometry.image_intrinsicInterior (φ := σ.toAffineIsometry)
        (s := segment ℝ p q)]
      exact ⟨x, hx.1, rfl⟩
    simpa [hσseg] using himage
  have hσx_int : σ x ∈ ℤ^2 := by
    -- On an integral segment, midpoint reflection is the coordinatewise map `z ↦ p + q - z`,
    -- which preserves the embedded integer lattice.
    rcases (mem_integerVectors_iff).1 hp with ⟨zp, rfl⟩
    rcases (mem_integerVectors_iff).1 hq with ⟨zq, rfl⟩
    rcases (mem_integerVectors_iff).1 hx.2 with ⟨zx, rfl⟩
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨fun i ↦ zp i + zq i - zx i, ?_⟩
    funext i
    fin_cases i <;>
      simp [σ, m, AffineIsometryEquiv.pointReflection_apply, midpoint,
        AffineMap.lineMap_apply_module] <;>
      ring
  have hfix : σ x = x := huniq (σ x) ⟨hσx_mem, hσx_int⟩
  have hxmid : x = m := by
    simpa [σ, m] using
      (AffineIsometryEquiv.pointReflection_fixed_iff (𝕜 := ℝ) (x := m) (y := x)).mp hfix
  have hm_int : m ∈ ℤ^2 := by
    simpa [hxmid] using hx.2
  rcases (mem_integerVectors_iff).1 hp with ⟨zp, hp_eq⟩
  rcases (mem_integerVectors_iff).1 hm_int with ⟨zm, hm_eq⟩
  refine ⟨fun i ↦ zm i - zp i, ?_⟩
  -- Rewriting the midpoint equation coordinatewise exposes the desired doubled half-edge.
  funext i
  have hm_coord : (m i) = (zm i : ℝ) := by
    simpa [hm_eq] using congrFun hm_eq i
  have hp_coord : p i = (zp i : ℝ) := by
    simpa [hp_eq] using congrFun hp_eq i
  have hmid_coord : m i = (p i + q i) / 2 := by
    simp [m, midpoint, AffineMap.lineMap_apply_module]
    ring
  calc
    q i - p i = (2 : ℝ) * ((zm i : ℝ) - (zp i : ℝ)) := by
      linarith [hm_coord, hp_coord, hmid_coord]
    _ = (2 : ℝ) * ((zm i - zp i : ℤ) : ℝ) := by
      rw [Int.cast_sub]

/-- Helper for Exercise 6.13: a chosen doubled half-edge on one triangle edge is primitive, since
any nontrivial common divisor would create a second integral point in the relative interior of that
edge. -/
lemma chosenHalfEdge_coefficientGcd_eq_one
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {u : Z2}
    (hverts : ∀ j : Fin 3, t.points j ∈ ℤ^2)
    (hu :
      t.points (Fin.succAbove i 1) - t.points (Fin.succAbove i 0) =
        fun j ↦ (2 : ℝ) * (u j : ℝ))
    (hseg :
      facet_has_unique_integer_point_in_intrinsicInterior
        (segment ℝ (t.points (Fin.succAbove i 0)) (t.points (Fin.succAbove i 1)))) :
    coefficientGcd u = 1 := by
  let p : R2 := t.points (Fin.succAbove i 0)
  let q : R2 := t.points (Fin.succAbove i 1)
  have hp_int : p ∈ ℤ^2 := by
    simpa [p] using hverts (Fin.succAbove i 0)
  have hq_int : q ∈ ℤ^2 := by
    simpa [q] using hverts (Fin.succAbove i 1)
  have hpq_ne : p ≠ q := by
    simpa [p, q, Affine.Simplex.faceOpposite_point_eq_point_succAbove] using
      (t.faceOpposite i).independent.injective.ne (by decide : (0 : Fin 2) ≠ 1)
  have hu_nonzero : u ≠ 0 := by
    intro hu_zero
    apply hpq_ne
    ext j
    have huj := congrFun hu j
    simp [p, q, hu_zero] at huj
    linarith
  have hmid_eq :
      midpoint ℝ p q = fun j ↦ p j + (u j : ℝ) := by
    funext j
    have huj := congrFun hu j
    simp [p, q, midpoint, AffineMap.lineMap_apply_module] at huj ⊢
    linarith
  have hmid_int : midpoint ℝ p q ∈ ℤ^2 := by
    rcases (mem_integerVectors_iff).1 hp_int with ⟨zp, hp_eq⟩
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨fun j ↦ zp j + u j, ?_⟩
    funext j
    have hpj : p j = (zp j : ℝ) := by
      simpa [p, hp_eq] using congrFun hp_eq j
    rw [hmid_eq, hpj, Int.cast_add]
  have hmid_intr :
      midpoint ℝ p q ∈ intrinsicInterior ℝ (segment ℝ p q) := by
    -- The midpoint is the edge line-map value at parameter `1 / 2`.
    simpa [p, q, midpoint, AffineMap.lineMap_apply_module] using
      (triangleEdge_lineMap_mem_intrinsicInterior (t := t) (i := i)
        (r := (1 / 2 : ℝ)) (by constructor <;> norm_num))
  rcases hseg with ⟨x, hx, huniq⟩
  have hmid_unique : midpoint ℝ p q = x := huniq _ ⟨hmid_intr, hmid_int⟩
  by_contra hg_one
  have hg_eq :
      coefficientGcd u = (Int.gcd (u 0) (u 1) : ℤ) := by
    rw [← Fin.cons_self_tail u, coefficientGcd_cons]
    simp
  have hg_nonneg : 0 ≤ coefficientGcd u := by
    rw [hg_eq]
    exact_mod_cast Nat.zero_le (Int.gcd (u 0) (u 1))
  have hg_ne_zero : coefficientGcd u ≠ 0 := coefficientGcd_ne_zero_of_nonzero u hu_nonzero
  have hg_gt_one : 1 < coefficientGcd u := by
    omega
  rcases coefficientGcd_dvd u 0 with ⟨z0, hz0⟩
  rcases coefficientGcd_dvd u 1 with ⟨z1, hz1⟩
  let z : Z2 := ![z0, z1]
  have hu_div : u = fun j ↦ coefficientGcd u * z j := by
    funext j
    fin_cases j
    · simp [z, hz0]
    · simp [z, hz1]
  let y : R2 := fun j ↦ p j + (z j : ℝ)
  have hy_int : y ∈ ℤ^2 := by
    rcases (mem_integerVectors_iff).1 hp_int with ⟨zp, hp_eq⟩
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨fun j ↦ zp j + z j, ?_⟩
    funext j
    have hpj : p j = (zp j : ℝ) := by
      simpa [p, hp_eq] using congrFun hp_eq j
    simp [y, hpj, Int.cast_add]
  have hden_pos : 0 < (2 * coefficientGcd u : ℝ) := by
    exact_mod_cast (show (0 : ℤ) < 2 * coefficientGcd u by omega)
  have hr :
      ((2 * coefficientGcd u : ℝ)⁻¹) ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · simpa [one_div] using
        (inv_lt_one_of_one_lt₀ (show (1 : ℝ) < 2 * coefficientGcd u by
          exact_mod_cast (show (1 : ℤ) < 2 * coefficientGcd u by omega)))
  have hy_line :
      y = AffineMap.lineMap p q ((2 * coefficientGcd u : ℝ)⁻¹) := by
    ext j
    have huj := congrFun hu j
    have hzj := congrFun hu_div j
    have hdiff :
        q j - p j = (2 * coefficientGcd u : ℝ) * (z j : ℝ) := by
      calc
        q j - p j = (2 : ℝ) * (u j : ℝ) := huj
        _ = (2 : ℝ) * (((coefficientGcd u * z j : ℤ)) : ℝ) := by rw [hzj]
        _ = (2 * coefficientGcd u : ℝ) * (z j : ℝ) := by
              push_cast
              ring
    have hden_ne : (2 * coefficientGcd u : ℝ) ≠ 0 := by positivity
    calc
      y j = p j + (z j : ℝ) := by simp [y]
      _ = p j + ((2 * coefficientGcd u : ℝ)⁻¹ * ((2 * coefficientGcd u : ℝ) * (z j : ℝ))) := by
            field_simp [hden_ne]
      _ = p j + ((2 * coefficientGcd u : ℝ)⁻¹ * (q j - p j)) := by rw [hdiff]
      _ = AffineMap.lineMap p q ((2 * coefficientGcd u : ℝ)⁻¹) j := by
            simp [AffineMap.lineMap_apply_module]
            ring
  have hy_intr : y ∈ intrinsicInterior ℝ (segment ℝ p q) := by
    rw [hy_line]
    simpa [p, q] using
      (triangleEdge_lineMap_mem_intrinsicInterior (t := t) (i := i) hr)
  have hy_ne_mid : y ≠ midpoint ℝ p q := by
    intro hy_mid
    have hu_nonzero_coord : u 0 ≠ 0 ∨ u 1 ≠ 0 := by
      by_contra hu_zero
      apply hu_nonzero
      ext j
      fin_cases j
      · simpa using not_or.mp hu_zero |>.1
      · simpa using not_or.mp hu_zero |>.2
    rcases hu_nonzero_coord with h0 | h1
    · have hzu : z 0 = u 0 := by
        have hcoord := congrFun hy_mid 0
        simpa [y, hmid_eq] using hcoord
      have hgu : coefficientGcd u * u 0 = u 0 := by
        calc
          coefficientGcd u * u 0 = coefficientGcd u * z 0 := by rw [hzu]
          _ = u 0 := (congrFun hu_div 0).symm
      have hmul : (coefficientGcd u - 1) * u 0 = 0 := by
        calc
          (coefficientGcd u - 1) * u 0 = coefficientGcd u * u 0 - u 0 := by ring
          _ = u 0 - u 0 := by rw [hgu]
          _ = 0 := by ring
      rcases mul_eq_zero.mp hmul with hg_sub | hu0
      · exact hg_one (by linarith)
      · exact h0 hu0
    · have hzu : z 1 = u 1 := by
        have hcoord := congrFun hy_mid 1
        simpa [y, hmid_eq] using hcoord
      have hgu : coefficientGcd u * u 1 = u 1 := by
        calc
          coefficientGcd u * u 1 = coefficientGcd u * z 1 := by rw [hzu]
          _ = u 1 := (congrFun hu_div 1).symm
      have hmul : (coefficientGcd u - 1) * u 1 = 0 := by
        calc
          (coefficientGcd u - 1) * u 1 = coefficientGcd u * u 1 - u 1 := by ring
          _ = u 1 - u 1 := by rw [hgu]
          _ = 0 := by ring
      rcases mul_eq_zero.mp hmul with hg_sub | hu1
      · exact hg_one (by linarith)
      · exact h1 hu1
  have hy_eq_x : y = x := huniq _ ⟨hy_intr, hy_int⟩
  exact hy_ne_mid (hy_eq_x.trans hmid_unique.symm)

/-- Helper for Exercise 6.13: if both `![k, r]` and `![k - 1, r]` are primitive, then the shared
second coordinate must be odd. -/
lemma odd_of_coprime_pair_and_coprime_successor_pair
    (k r : ℤ)
    (hkr : coefficientGcd ![k, r] = 1)
    (hk1r : coefficientGcd ![k - 1, r] = 1) :
    Odd r := by
  rcases Int.even_or_odd r with hr_even | hr_odd
  · rcases Int.even_or_odd k with hk_even | hk_odd
    · have htwo_dvd : (2 : ℤ) ∣ coefficientGcd ![k, r] := by
        rw [coefficientGcd]
        refine Finset.dvd_gcd ?_
        intro j hj
        fin_cases j
        · simpa using hk_even.two_dvd
        · simpa using hr_even.two_dvd
      rw [hkr] at htwo_dvd
      norm_num at htwo_dvd
    · rcases hk_odd with ⟨m, hm⟩
      have hk1_even : Even (k - 1) := by
        refine ⟨m, ?_⟩
        omega
      have htwo_dvd : (2 : ℤ) ∣ coefficientGcd ![k - 1, r] := by
        rw [coefficientGcd]
        refine Finset.dvd_gcd ?_
        intro j hj
        fin_cases j
        · simpa using hk1_even.two_dvd
        · simpa using hr_even.two_dvd
      rw [hk1r] at htwo_dvd
      norm_num at htwo_dvd
  · exact hr_odd

/-- Helper for Exercise 6.13: once an injective affine map sends the three vertices of a triangle
to the standard vertices, its image of the whole triangle region is the standard triangle region.
-/
lemma triangleImage_eq_standard_of_vertex_images
    {t : Affine.Triangle ℝ R2} {f : R2 →ᵃ[ℝ] R2}
    (hf : Function.Injective f)
    (h0 : f (t.points 0) = (![0, 0] : R2))
    (h1 : f (t.points 1) = (![2, 0] : R2))
    (h2 : f (t.points 2) = (![0, 2] : R2)) :
    f '' t.closedInterior = exercise_6_13_standard_triangle_region := by
  -- Identify the image simplex by its three vertex images, then use the standard simplex image
  -- formula for closed interiors.
  have hmap : t.map f hf = exercise_6_13_standard_triangle := by
    ext i j
    fin_cases i <;> fin_cases j
    · simpa using congrFun h0 0
    · simpa using congrFun h0 1
    · simpa using congrFun h1 0
    · simpa using congrFun h1 1
    · simpa using congrFun h2 0
    · simpa using congrFun h2 1
  calc
    f '' t.closedInterior = (t.map f hf).closedInterior := by
      symm
      simpa using (Affine.Simplex.closedInterior_map (s := t) (hf := hf))
    _ = exercise_6_13_standard_triangle_region := by
      simpa [exercise_6_13_standard_triangle_region, hmap]

/-- Exercise 6.13. Let `T` be a maximal lattice-free triangle in `ℝ²` whose vertices are integral
and such that each facet contains exactly one integral point in its relative interior. Then there
exists an integral translation and a unimodular integer matrix sending `T` to the triangle with
vertices `(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
theorem exercise_6_13_exists_unimodular_integer_affine_image_of_maximal_lattice_free_triangle
    (T : Set R2)
    (hT_triangle : has_integral_triangle_vertices T)
    (hT_max : is_maximal_lattice_free T)
    (hT_facets : facets_have_unique_integer_point_in_intrinsicInterior T) :
    ∃ c : Z2, ∃ M : Matrix (Fin 2) (Fin 2) ℤ,
      IsUnit M.det ∧
        integerAffineMap c M '' T = exercise_6_13_standard_triangle_region :=
by
  classical
  rcases hT_triangle with ⟨t, ht, hverts⟩
  let v0 : R2 := t.points 0
  let v1 : R2 := t.points 1
  let v2 : R2 := t.points 2
  have hedges :
      facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ v0 v1) ∧
        facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ v0 v2) ∧
          facet_has_unique_integer_point_in_intrinsicInterior (segment ℝ v1 v2) := by
    -- Freeze the three vertex-edge hypotheses once so the remaining arithmetic can stay on the
    -- explicit segment surface.
    simpa [v0, v1, v2] using triangleEdge_uniqueIntegerPoint ht hT_facets
  have hv0_int : v0 ∈ ℤ^2 := by simpa [v0] using hverts 0
  have hv1_int : v1 ∈ ℤ^2 := by simpa [v1] using hverts 1
  have hv2_int : v2 ∈ ℤ^2 := by simpa [v2] using hverts 2
  have hfree : is_lattice_free T := is_maximal_lattice_free.lattice_free hT_max
  have h01_half : ∃ u : Z2, v1 - v0 = fun i ↦ (2 : ℝ) * (u i : ℝ) := by
    -- The first edge's unique intrinsic-interior lattice point is its midpoint, giving the first
    -- doubled integer half-edge used by the normalization route.
    exact segmentHalfEdge_eq_two_integer_of_uniqueInteriorIntegerPoint hv0_int hv1_int hedges.1
  have h02_half : ∃ u : Z2, v2 - v0 = fun i ↦ (2 : ℝ) * (u i : ℝ) := by
    -- The same midpoint-reflection argument supplies the second adjacent doubled half-edge.
    exact segmentHalfEdge_eq_two_integer_of_uniqueInteriorIntegerPoint hv0_int hv2_int hedges.2.1
  have h12_half : ∃ u : Z2, v2 - v1 = fun i ↦ (2 : ℝ) * (u i : ℝ) := by
    -- The opposite edge also has a doubled integer half-edge, which is the remaining arithmetic
    -- input needed for the primitive-parity route.
    exact segmentHalfEdge_eq_two_integer_of_uniqueInteriorIntegerPoint hv1_int hv2_int hedges.2.2
  rcases h01_half with ⟨u, hu⟩
  rcases h02_half with ⟨w, hw⟩
  rcases h12_half with ⟨s, hs⟩
  have hu_gcd : coefficientGcd u = 1 := by
    -- Upgrade the chosen base half-edge to a primitive vector before normalizing it.
    simpa [v0, v1] using
      (chosenHalfEdge_coefficientGcd_eq_one (t := t) (i := 2) hverts hu hedges.1)
  have hw_gcd : coefficientGcd w = 1 := by
    -- The second adjacent half-edge is primitive for the same unique-segment reason.
    simpa [v0, v2] using
      (chosenHalfEdge_coefficientGcd_eq_one (t := t) (i := 1) hverts hw hedges.2.1)
  have hs_gcd : coefficientGcd s = 1 := by
    -- The third edge contributes the second primitive pair needed for the later odd-height step.
    simpa [v1, v2] using
      (chosenHalfEdge_coefficientGcd_eq_one (t := t) (i := 0) hverts hs hedges.2.2)
  rcases (mem_integerVectors_iff).1 hv0_int with ⟨z0, hz0⟩
  rcases (mem_integerVectors_iff).1 hv1_int with ⟨z1, hz1⟩
  rcases (mem_integerVectors_iff).1 hv2_int with ⟨z2, hz2⟩
  let b : Z2 := z0 + 2 • u
  let c' : Z2 := z0 + 2 • w
  have hz1_eq : z1 = b := by
    -- Compare the first doubled half-edge identity in integer coordinates.
    funext i
    have hi := congrFun hu i
    have hi' : z1 i - z0 i = 2 * u i := by
      exact_mod_cast hi
    simp [b]
    omega
  have hz2_eq : z2 = c' := by
    -- The second doubled half-edge gives the same coordinate formula for `z2`.
    funext i
    have hi := congrFun hw i
    have hi' : z2 i - z0 i = 2 * w i := by
      exact_mod_cast hi
    simp [c']
    omega
  let aSmall : Z2 := z0
  let bSmall : Z2 := z0 + u
  let cSmall : Z2 := z0 + w
  let smallVerts : Fin 3 → R2 := ![
    (Int.cast ∘ aSmall : R2),
    (Int.cast ∘ bSmall : R2),
    (Int.cast ∘ cSmall : R2)]
  have hsmall_only :
      ∀ p : Z2,
        (Int.cast ∘ p : R2) ∈ convexHull ℝ (Set.range smallVerts) →
          p = aSmall ∨ p = bSmall ∨ p = cSmall := by
    intro p hp
    let S : R2 →ᵃ[ℝ] R2 := AffineMap.homothety (Int.cast ∘ z0 : R2) (2 : ℝ)
    let q : Z2 := fun i ↦ 2 * p i - z0 i
    have hqCast : (Int.cast ∘ q : R2) = S (Int.cast ∘ p : R2) := by
      -- Doubling the small triangle about `z0` sends an integral point `p` to the corresponding
      -- integral point `q` in the original triangle.
      funext i
      fin_cases i <;>
        simp [q, S, AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply_module]
    have hSsmall :
        S '' Set.range smallVerts = Set.range t.points := by
      -- The homothety doubles the half-edge triangle back to the original triangle vertices.
      rw [← Set.range_comp]
      apply congrArg Set.range
      funext i
      fin_cases i
      · simpa [S, smallVerts, aSmall, hz0, AffineMap.homothety_eq_lineMap,
          AffineMap.lineMap_apply_module]
      · ext j
        fin_cases j <;>
          simp [S, smallVerts, bSmall, v1, hz0, hz1_eq, b, AffineMap.homothety_eq_lineMap,
            AffineMap.lineMap_apply_module] <;>
          ring
      · ext j
        fin_cases j <;>
          simp [S, smallVerts, cSmall, v2, hz0, hz2_eq, c', AffineMap.homothety_eq_lineMap,
            AffineMap.lineMap_apply_module] <;>
          ring
    have hqT : S (Int.cast ∘ p : R2) ∈ T := by
      -- Membership in the small convex hull transports to membership in the original triangle.
      have himage : S (Int.cast ∘ p : R2) ∈ S '' convexHull ℝ (Set.range smallVerts) :=
        ⟨Int.cast ∘ p, hp, rfl⟩
      rw [S.image_convexHull] at himage
      rw [ht, ← t.convexHull_eq_closedInterior]
      rwa [hSsmall] at himage
    have hqInt : S (Int.cast ∘ p : R2) ∈ ℤ^2 := by
      rw [← hqCast]
      exact (mem_integerVectors_iff).2 ⟨q, rfl⟩
    by_cases hp0 : p = aSmall
    · exact Or.inl hp0
    by_cases hp1 : p = bSmall
    · exact Or.inr (Or.inl hp1)
    by_cases hp2 : p = cSmall
    · exact Or.inr (Or.inr hp2)
    have hq_not_vertex : ∀ i : Fin 3, S (Int.cast ∘ p : R2) ≠ t.points i := by
      -- A small-triangle nonvertex cannot double to an original-triangle vertex.
      intro i
      fin_cases i
      · intro hq0
        apply hp0
        funext j
        have hj := congrFun (hqCast.trans hq0) j
        exact_mod_cast hj
      · intro hq1
        apply hp1
        funext j
        have hj := congrFun (hqCast.trans hq1) j
        have hj' : 2 * p j - z0 j = z1 j := by exact_mod_cast hj
        simp [bSmall, hz1_eq, b]
        omega
      · intro hq2
        apply hp2
        funext j
        have hj := congrFun (hqCast.trans hq2) j
        have hj' : 2 * p j - z0 j = z2 j := by exact_mod_cast hj
        simp [cSmall, hz2_eq, c']
        omega
    have hq_not_interior : S (Int.cast ∘ p : R2) ∉ t.interior := by
      -- Any interior lattice point of the original triangle contradicts lattice-freeness.
      intro hqInt'
      have hqInteriorT : S (Int.cast ∘ p : R2) ∈ interior T := by
        rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
        exact hqInt'
      exact hfree.not_mem_interior hqInt hqInteriorT
    have hq_edge :
        ∃ i : Fin 3, S (Int.cast ∘ p : R2) ∈ triangle_opposite_facet t i :=
      boundaryPoint_mem_someTriangleOppositeFacet ht hqT hq_not_interior
    rcases hq_edge with ⟨i, hqi⟩
    have hq_face :
        S (Int.cast ∘ p : R2) ∈ (t.faceOpposite i).interior :=
      triangleOppositeFacet_nonvertex_mem_faceInterior hqi hq_not_vertex
    have hq_intr :
        S (Int.cast ∘ p : R2) ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) := by
      rw [triangleOppositeFacet_intrinsicInterior_eq_faceInterior]
      exact hq_face
    exfalso
    fin_cases i
    · have hq_seg :
          S (Int.cast ∘ p : R2) ∈ intrinsicInterior ℝ (segment ℝ v1 v2) := by
        simpa [v1, v2, triangleOppositeFacet_eq_segment] using hq_intr
      have hmid_intr :
          (Int.cast ∘ (z0 + u + w) : R2) ∈ intrinsicInterior ℝ (segment ℝ v1 v2) := by
        simpa [v1, v2, midpoint, hz1_eq, hz2_eq, b, c', AffineMap.lineMap_apply_module] using
          (triangleEdge_lineMap_mem_intrinsicInterior (t := t) (i := 0) (r := (1 / 2 : ℝ))
            (by constructor <;> norm_num))
      have hmid_int : (Int.cast ∘ (z0 + u + w) : R2) ∈ ℤ^2 := by
        exact (mem_integerVectors_iff).2 ⟨z0 + u + w, rfl⟩
      have hq_mid :
          S (Int.cast ∘ p : R2) = (Int.cast ∘ (z0 + u + w) : R2) := by
        rcases hedges.2.2 with ⟨x, hx, huniq⟩
        exact huniq _ ⟨hq_seg, hqInt⟩
      have hs_even : ∀ j : Fin 2, Even (s j) := by
        intro j
        have hj := congrFun (hqCast.trans hq_mid) j
        refine ⟨p j - z0 j - u j, ?_⟩
        have hj' : 2 * p j - z0 j = z0 j + u j + w j := by
          exact_mod_cast hj
        omega
      have htwo := two_dvd_coefficientGcd_of_even s hs_even
      rw [hs_gcd] at htwo
      norm_num at htwo
    · have hq_seg :
          S (Int.cast ∘ p : R2) ∈ intrinsicInterior ℝ (segment ℝ v0 v2) := by
        simpa [v0, v2, triangleOppositeFacet_eq_segment] using hq_intr
      have hq_mid :
          S (Int.cast ∘ p : R2) = (Int.cast ∘ cSmall : R2) := by
        rcases hedges.2.1 with ⟨x, hx, huniq⟩
        have hmid_intr :
            (Int.cast ∘ cSmall : R2) ∈ intrinsicInterior ℝ (segment ℝ v0 v2) := by
          simpa [v0, v2, cSmall, midpoint, hz0, hz2_eq, c', AffineMap.lineMap_apply_module] using
            (triangleEdge_lineMap_mem_intrinsicInterior (t := t) (i := 1) (r := (1 / 2 : ℝ))
              (by constructor <;> norm_num))
        have hmid_int : (Int.cast ∘ cSmall : R2) ∈ ℤ^2 := by
          exact (mem_integerVectors_iff).2 ⟨cSmall, rfl⟩
        exact huniq _ ⟨hq_seg, hqInt⟩
      have hw_even : ∀ j : Fin 2, Even (w j) := by
        intro j
        have hj := congrFun (hqCast.trans hq_mid) j
        refine ⟨p j - z0 j, ?_⟩
        have hj' : 2 * p j - z0 j = z0 j + w j := by
          exact_mod_cast hj
        omega
      have htwo := two_dvd_coefficientGcd_of_even w hw_even
      rw [hw_gcd] at htwo
      norm_num at htwo
    · have hq_seg :
          S (Int.cast ∘ p : R2) ∈ intrinsicInterior ℝ (segment ℝ v0 v1) := by
        simpa [v0, v1, triangleOppositeFacet_eq_segment] using hq_intr
      have hq_mid :
          S (Int.cast ∘ p : R2) = (Int.cast ∘ bSmall : R2) := by
        rcases hedges.1 with ⟨x, hx, huniq⟩
        have hmid_intr :
            (Int.cast ∘ bSmall : R2) ∈ intrinsicInterior ℝ (segment ℝ v0 v1) := by
          simpa [v0, v1, bSmall, midpoint, hz0, hz1_eq, b, AffineMap.lineMap_apply_module] using
            (triangleEdge_lineMap_mem_intrinsicInterior (t := t) (i := 2) (r := (1 / 2 : ℝ))
              (by constructor <;> norm_num))
        have hmid_int : (Int.cast ∘ bSmall : R2) ∈ ℤ^2 := by
          exact (mem_integerVectors_iff).2 ⟨bSmall, rfl⟩
        exact huniq _ ⟨hq_seg, hqInt⟩
      have hu_even : ∀ j : Fin 2, Even (u j) := by
        intro j
        have hj := congrFun (hqCast.trans hq_mid) j
        refine ⟨p j - z0 j, ?_⟩
        have hj' : 2 * p j - z0 j = z0 j + u j := by
          exact_mod_cast hj
        omega
      have htwo := two_dvd_coefficientGcd_of_even u hu_even
      rw [hu_gcd] at htwo
      norm_num at htwo
  have hsmall_det_ne :
      triangle_determinant2 (Int.cast ∘ aSmall : R2) (Int.cast ∘ bSmall : R2)
        (Int.cast ∘ cSmall : R2) ≠ 0 := by
    -- The half-edge triangle is nondegenerate because doubling it recovers the original triangle.
    intro hzero
    have hbig_aff : AffineIndependent ℝ ![v0, v1, v2] := by
      simpa [v0, v1, v2] using t.independent
    have hbig_not_collinear : ¬ Collinear ℝ ({v0, v1, v2} : Set R2) :=
      (affineIndependent_iff_not_collinear_set).1 hbig_aff
    have hbig_det_ne : triangle_determinant2 v0 v1 v2 ≠ 0 :=
      triangle_determinant2_ne_zero_of_not_collinear hbig_not_collinear
    have hbig_det :
        triangle_determinant2 v0 v1 v2 =
          (4 : ℝ) * triangle_determinant2 (Int.cast ∘ aSmall : R2)
            (Int.cast ∘ bSmall : R2) (Int.cast ∘ cSmall : R2) := by
      simp [triangle_determinant2, v0, v1, v2, aSmall, bSmall, cSmall, hz0, hz1_eq, hz2_eq, b,
        c']
      ring
    apply hbig_det_ne
    rw [hbig_det, hzero]
    ring
  have hdet_abs :
      |triangle_determinant2 (Int.cast ∘ aSmall : R2) (Int.cast ∘ bSmall : R2)
        (Int.cast ∘ cSmall : R2)| = 1 :=
    emptyLatticeTriangle_absDeterminant_eq_one aSmall bSmall cSmall hsmall_det_ne hsmall_only
  let D : ℤ := u 0 * w 1 - u 1 * w 0
  have hDreal :
      ((D : ℤ) : ℝ) =
        triangle_determinant2 (Int.cast ∘ aSmall : R2) (Int.cast ∘ bSmall : R2)
          (Int.cast ∘ cSmall : R2) := by
    -- On the half-edge triangle, the signed area is the determinant of the two primitive
    -- half-edge columns.
    simp [triangle_determinant2, D, aSmall, bSmall, cSmall]
    push_cast
    ring
  have hDabs : |(D : ℝ)| = 1 := by
    simpa [hDreal] using hdet_abs
  have hDne : D ≠ 0 := by
    intro hDzero
    have : ((D : ℤ) : ℝ) = 0 := by simp [hDzero]
    rw [hDreal] at this
    have : (0 : ℝ) = 1 := by simpa [this] using hDabs
    norm_num at this
  have hDlower : (-1 : ℤ) ≤ D := by
    have hAbsLe : |(D : ℝ)| ≤ 1 := by simpa [hDabs]
    exact_mod_cast (abs_le.mp hAbsLe).1
  have hDupper : D ≤ 1 := by
    have hAbsLe : |(D : ℝ)| ≤ 1 := by simpa [hDabs]
    exact_mod_cast (abs_le.mp hAbsLe).2
  have hDcases : D = 1 ∨ D = -1 := by
    interval_cases D <;> simp_all
  let M : Matrix (Fin 2) (Fin 2) ℤ := D • !![w 1, -w 0; -u 1, u 0]
  have hMu : M *ᵥ u = ![1, 0] := by
    -- The adjugate-style matrix sends the first primitive half-edge to the first basis vector.
    ext i
    fin_cases i
    · rcases hDcases with hD | hD <;> simp [M, D, hD, Matrix.mulVec, dotProduct] <;> ring
    · simp [M, Matrix.mulVec, dotProduct]
  have hMw : M *ᵥ w = ![0, 1] := by
    -- The same matrix sends the second primitive half-edge to the second basis vector.
    ext i
    fin_cases i
    · simp [M, Matrix.mulVec, dotProduct]
    · rcases hDcases with hD | hD <;> simp [M, D, hD, Matrix.mulVec, dotProduct] <;> ring
  have hMdet_eq : M.det = D := by
    -- The normalization matrix has determinant `D`, hence determinant `±1`.
    rw [Matrix.det_fin_two]
    simp [M, D]
    ring
  have hMdet : IsUnit M.det := by
    rw [hMdet_eq]
    rcases hDcases with hD | hD <;> simp [hD]
  let c : Z2 := fun i ↦ -(M *ᵥ z0) i
  have hfv0 : integerAffineMap c M v0 = (![0, 0] : R2) := by
    -- The chosen translation cancels the image of the base vertex.
    rw [hz0, integerAffineMap_apply_integerVector]
    ext i
    fin_cases i <;> simp [c]
  have hfv1 : integerAffineMap c M v1 = (![2, 0] : R2) := by
    -- The first doubled half-edge becomes the horizontal unit edge after normalization.
    rw [hz1, hz1_eq, integerAffineMap_apply_integerVector]
    simp [b, c, Matrix.mulVec_add, Matrix.mulVec_smul, hMu]
  have hfv2 : integerAffineMap c M v2 = (![0, 2] : R2) := by
    -- The second doubled half-edge becomes the vertical unit edge after normalization.
    rw [hz2, hz2_eq, integerAffineMap_apply_integerVector]
    simp [c', c, Matrix.mulVec_add, Matrix.mulVec_smul, hMw]
  let A : Matrix (Fin 2) (Fin 2) ℝ := (Int.castRingHom ℝ).mapMatrix M
  have hAunit : IsUnit A := by
    -- Over `ℝ`, unit determinant makes the cast matrix invertible.
    refine (Matrix.isUnit_iff_isUnit_det A).2 ?_
    have hmap : IsUnit ((Int.castRingHom ℝ) M.det) := hMdet.map (Int.castRingHom ℝ)
    simpa [A, RingHom.map_det] using hmap
  have hlinear_inj : Function.Injective A.mulVec :=
    (Matrix.mulVec_injective_iff_isUnit).2 hAunit
  have hf : Function.Injective (integerAffineMap c M) := by
    -- Injectivity of the affine map follows from injectivity of its linear part.
    refine (AffineMap.linear_injective_iff (integerAffineMap c M)).1 ?_
    simpa [integerAffineMap, A, Matrix.toLin'_apply] using hlinear_inj
  refine ⟨c, M, hMdet, ?_⟩
  -- Once the three vertices match the standard model, the whole closed triangle matches as well.
  rw [ht]
  simpa [v0, v1, v2] using
    (triangleImage_eq_standard_of_vertex_images (t := t) hf hfv0 hfv1 hfv2)

end Exercise613
