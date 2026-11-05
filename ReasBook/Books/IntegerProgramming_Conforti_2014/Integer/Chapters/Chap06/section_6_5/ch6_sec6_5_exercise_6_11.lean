/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_19

-- Declarations for this item will be appended below by the statement pipeline.
-- This exercise reuses the Chapter 6 lattice-free owner `is_maximal_lattice_free` from
-- Theorem 6.18, the Chapter 3 facet owner `IsFacetOf`, and the canonical lattice notation `ℤ^n`.

open scoped IntegerVectorNotation

section Exercise611

local notation "R2" => Fin 2 → ℝ

/-- Helper for Exercise 6.11: the ambient space `ℝ²` has affine dimension `2`. -/
lemma finrank_R2 : Module.finrank ℝ R2 = 2 := by
  simp

/-- Helper for Exercise 6.11: the three vertices of a realized triangle form an affine basis of
`ℝ²`. -/
abbrev triangleAffineBasis (t : Affine.Triangle ℝ R2) : AffineBasis (Fin 3) ℝ R2 :=
  ⟨t.points, t.independent, Affine.Simplex.span_eq_top t finrank_R2⟩

/-- `has_triangle_vertices T t` means that the planar triangle `t` realizes the set `T` as its
convex hull. -/
def has_triangle_vertices (T : Set R2) (t : Affine.Triangle ℝ R2) : Prop :=
  T = t.closedInterior

/-- A planar set is a triangle when it is the convex hull of three affinely independent vertices.
-/
def is_triangle (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2, has_triangle_vertices T t

/-- The facet opposite the vertex `t.points i` in the triangle `t`. -/
def triangle_opposite_facet
    (t : Affine.Triangle ℝ R2)
    (i : Fin 3) : Set R2 :=
  (t.faceOpposite i).closedInterior

/-- `has_integral_triangle_vertices T` means that `T` is a triangle whose three vertices are
integral lattice points. -/
def has_integral_triangle_vertices (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2, has_triangle_vertices T t ∧ ∀ i : Fin 3, t.points i ∈ ℤ^2

/-- The relative interior of the facet `F` contains exactly one embedded integer point. -/
def facet_has_unique_integer_point_in_intrinsicInterior (F : Set R2) : Prop :=
  ∃! x : R2, x ∈ intrinsicInterior ℝ F ∧ x ∈ ℤ^2

/-- The relative interior of the facet `F` contains at least two distinct embedded integer
points. -/
def facet_has_two_distinct_integer_points_in_intrinsicInterior (F : Set R2) : Prop :=
  ∃ x y : R2, x ≠ y ∧ x ∈ intrinsicInterior ℝ F ∩ ℤ^2 ∧ y ∈ intrinsicInterior ℝ F ∩ ℤ^2

/-- Every facet of `T` contains a unique embedded integer point in its relative interior. -/
def facets_have_unique_integer_point_in_intrinsicInterior (T : Set R2) : Prop :=
  ∀ F : Set R2, IsFacetOf T F → facet_has_unique_integer_point_in_intrinsicInterior F

/-- Case (a): the triangle has integral vertices and each facet contains exactly one embedded
integer point in its relative interior. -/
def exercise_6_11_case_a (T : Set R2) : Prop :=
  has_integral_triangle_vertices T ∧
    facets_have_unique_integer_point_in_intrinsicInterior T

/-- Case (b): some vertex of the triangle is nonintegral and the opposite facet is a facet of `T`
whose relative interior contains at least two distinct embedded integer points. -/
def exercise_6_11_case_b (T : Set R2) : Prop :=
  ∃ t : Affine.Triangle ℝ R2,
    has_triangle_vertices T t ∧
      ∃ i : Fin 3,
        t.points i ∉ ℤ^2 ∧
          IsFacetOf T (triangle_opposite_facet t i) ∧
            facet_has_two_distinct_integer_points_in_intrinsicInterior
              (triangle_opposite_facet t i)

/-- Case (c): the triangle contains exactly three embedded integer points, and each facet contains
exactly one of them in its relative interior. -/
def exercise_6_11_case_c (T : Set R2) : Prop :=
  (T ∩ ℤ^2).encard = 3 ∧
    facets_have_unique_integer_point_in_intrinsicInterior T

/-- Helper for Exercise 6.11: a triangle witness forces the realized set to be full-dimensional in
`ℝ²`. -/
lemma triangleAffineSpan_eq_top_of_has_triangle_vertices
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t) :
    affineSpan ℝ T = ⊤ := by
  rcases ht with rfl
  -- The three triangle vertices already span the ambient plane, and they all lie in the closed
  -- triangle.
  have hrank : Module.finrank ℝ R2 = 2 := finrank_R2
  have hspan : affineSpan ℝ (Set.range t.points) = ⊤ :=
    Affine.Simplex.span_eq_top t hrank
  have hsubset : Set.range t.points ⊆ t.closedInterior := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    exact t.point_mem_closedInterior i
  refine top_unique ?_
  simpa [hspan] using (affineSpan_mono ℝ hsubset)

/-- Helper for Exercise 6.11: each opposite edge of a realized triangle is a facet of the closed
triangle. -/
lemma triangleOppositeFacet_isFacetOf
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (i : Fin 3) :
    IsFacetOf T (triangle_opposite_facet t i) := by
  have hrank : Module.finrank ℝ R2 = 2 := finrank_R2
  let b : AffineBasis (Fin 3) ℝ R2 :=
    ⟨t.points, t.independent, Affine.Simplex.span_eq_top t hrank⟩
  let l : StrongDual ℝ R2 :=
    ⟨-(b.coord i).linear, (-(b.coord i).linear).continuous_of_finiteDimensional⟩
  let x0 : R2 := t.points (Fin.succAbove i 0)
  have hcoord_sum : ∀ x : R2, ∑ j, b.coord j x = 1 := by
    intro x
    simp [b]
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
  have hcoord_zero_of_face : ∀ {x : R2}, x ∈ triangle_opposite_facet t i → b.coord i x = 0 := by
    intro x hx
    have hx' : x ∈ (t.faceOpposite i).closedInterior := by
      simpa [triangle_opposite_facet] using hx
    rw [Affine.Simplex.faceOpposite, ← hcoord_repr x] at hx'
    exact
      ((t.affineCombination_mem_closedInterior_face_iff_nonneg
          (fs := ({i}ᶜ : Finset (Fin 3)))
          (h := by simp [Finset.card_compl])
          (hw := hcoord_sum x)).mp hx').2 i (by simp)
  have hx0_face : x0 ∈ triangle_opposite_facet t i := by
    simp [triangle_opposite_facet, x0]
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
          (h := by simp [Finset.card_compl])
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
    rw [triangleAffineSpan_eq_top_of_has_triangle_vertices ht]
    rw [AffineSubspace.direction_top]
    simp [hrank]
  -- Route correction: expose the opposite edge as the zero set of the omitted barycentric
  -- coordinate, then compute codimension from the 1-simplex face.
  refine (isFacetOf_iff).2 ⟨hface_nonempty, ?_, ?_⟩
  · rw [h_exposed_eq]
    exact ContinuousLinearMap.toExposed.isExposed
  · rw [hface_dim, hT_dim]

/-- Helper for Exercise 6.11: Theorem 6.18 provides an embedded lattice point in the relative
interior of each triangle edge. -/
lemma triangleFacetLatticeWitnesses
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T) :
    ∃ z : Fin 3 → R2,
      ∀ i : Fin 3,
        z i ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) ∧ z i ∈ ℤ^2 := by
  classical
  -- First convert maximality into the facet-witness package from Theorem 6.18.
  have hfull : affineSpan ℝ T = ⊤ :=
    triangleAffineSpan_eq_top_of_has_triangle_vertices ht
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp hT_maximal
    with ⟨_, _, hfacetWitness⟩
  refine ⟨fun i ↦ Int.cast ∘
      Classical.choose (hfacetWitness (triangle_opposite_facet t i)
        (triangleOppositeFacet_isFacetOf ht i)), ?_⟩
  intro i
  constructor
  · -- The chosen witness lies in the intrinsic interior of the corresponding opposite edge.
    exact Classical.choose_spec (hfacetWitness (triangle_opposite_facet t i)
      (triangleOppositeFacet_isFacetOf ht i))
  · -- Repackage the chosen integer vector as membership in the embedded lattice `ℤ²`.
    exact (mem_integerVectors_iff).2 ⟨Classical.choose
      (hfacetWitness (triangle_opposite_facet t i) (triangleOppositeFacet_isFacetOf ht i)), rfl⟩

/-- Helper for Exercise 6.11: each explicit opposite edge sits inside the realized triangle. -/
lemma triangleOppositeFacet_subset
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (i : Fin 3) :
    triangle_opposite_facet t i ⊆ T := by
  -- The opposite edge is a face of the simplex, so its closed interior lies in the whole triangle.
  intro x hx
  rw [ht]
  exact t.closedInterior_faceOpposite_subset_closedInterior i
    (by simpa [triangle_opposite_facet] using hx)

/-- Helper for Exercise 6.11: a point on an explicit opposite edge has vanishing omitted
barycentric coordinate in the triangle affine basis. -/
lemma triangleClosedInterior_zeroCoord_of_memOppositeFacet
    {t : Affine.Triangle ℝ R2} {x : R2} {i : Fin 3}
    (hx : x ∈ triangle_opposite_facet t i) :
    (triangleAffineBasis t).coord i x = 0 := by
  let b : AffineBasis (Fin 3) ℝ R2 := triangleAffineBasis t
  -- Rewrite the point in barycentric coordinates and then invoke the standard face-opposite
  -- affine-span criterion.
  have hx_aff : x ∈ affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
    exact (t.faceOpposite i).closedInterior_subset_affineSpan
      (by simpa [triangle_opposite_facet] using hx)
  have hrepr : Finset.univ.affineCombination ℝ t.points (fun j ↦ b.coord j x) = x := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ (b.sum_coord_apply_eq_one x)]
    change ∑ j, b.coord j x • b j = x
    exact b.linear_combination_coord_eq_self x
  have hx_aff' :
      Finset.univ.affineCombination ℝ t.points (fun j ↦ b.coord j x) ∈
        affineSpan ℝ (Set.range (t.faceOpposite i).points) := by
    simpa [hrepr] using hx_aff
  exact (t.affineCombination_mem_affineSpan_faceOpposite_iff
    (hw := b.sum_coord_apply_eq_one x)).mp hx_aff'

/-- Helper for Exercise 6.11: if two barycentric coordinates vanish, the point is the remaining
triangle vertex. -/
lemma triangleClosedInterior_twoZeroCoords_eq_vertex
    {t : Affine.Triangle ℝ R2} {x : R2} {i j : Fin 3}
    (hij : i ≠ j)
    (hi : (triangleAffineBasis t).coord i x = 0)
    (hj : (triangleAffineBasis t).coord j x = 0) :
    ∃ k : Fin 3, x = t.points k := by
  let b : AffineBasis (Fin 3) ℝ R2 := triangleAffineBasis t
  have hsum : ∑ l, b.coord l x = 1 := b.sum_coord_apply_eq_one x
  -- Route correction: only after the coordinate normal form is exposed do the `Fin 3` cases
  -- collapse to the remaining basis vector.
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · have h2 : b.coord 2 x = 1 := by
      have hi' : b.coord 0 x = 0 := by simpa [b] using hi
      have hj' : b.coord 1 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨2, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · have hi' : b.coord 0 x = 0 := by simpa [b] using hi
      change b.coord 0 x = b.coord 0 (b 2)
      simpa using hi'
    · have hj' : b.coord 1 x = 0 := by simpa [b] using hj
      change b.coord 1 x = b.coord 1 (b 2)
      simpa using hj'
    · change b.coord 2 x = b.coord 2 (b 2)
      simpa using h2
  · have h1 : b.coord 1 x = 1 := by
      have hi' : b.coord 0 x = 0 := by simpa [b] using hi
      have hj' : b.coord 2 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨1, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · have hi' : b.coord 0 x = 0 := by simpa [b] using hi
      change b.coord 0 x = b.coord 0 (b 1)
      simpa using hi'
    · change b.coord 1 x = b.coord 1 (b 1)
      simpa using h1
    · have hj' : b.coord 2 x = 0 := by simpa [b] using hj
      change b.coord 2 x = b.coord 2 (b 1)
      simpa using hj'
  · have h2 : b.coord 2 x = 1 := by
      have hi' : b.coord 1 x = 0 := by simpa [b] using hi
      have hj' : b.coord 0 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨2, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · have hj' : b.coord 0 x = 0 := by simpa [b] using hj
      change b.coord 0 x = b.coord 0 (b 2)
      simpa using hj'
    · have hi' : b.coord 1 x = 0 := by simpa [b] using hi
      change b.coord 1 x = b.coord 1 (b 2)
      simpa using hi'
    · change b.coord 2 x = b.coord 2 (b 2)
      simpa using h2
  · exact (hij rfl).elim
  · have h0 : b.coord 0 x = 1 := by
      have hi' : b.coord 1 x = 0 := by simpa [b] using hi
      have hj' : b.coord 2 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨0, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · change b.coord 0 x = b.coord 0 (b 0)
      simpa using h0
    · have hi' : b.coord 1 x = 0 := by simpa [b] using hi
      change b.coord 1 x = b.coord 1 (b 0)
      simpa using hi'
    · have hj' : b.coord 2 x = 0 := by simpa [b] using hj
      change b.coord 2 x = b.coord 2 (b 0)
      simpa using hj'
  · have h1 : b.coord 1 x = 1 := by
      have hi' : b.coord 2 x = 0 := by simpa [b] using hi
      have hj' : b.coord 0 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨1, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · have hj' : b.coord 0 x = 0 := by simpa [b] using hj
      change b.coord 0 x = b.coord 0 (b 1)
      simpa using hj'
    · change b.coord 1 x = b.coord 1 (b 1)
      simpa using h1
    · have hi' : b.coord 2 x = 0 := by simpa [b] using hi
      change b.coord 2 x = b.coord 2 (b 1)
      simpa using hi'
  · have h0 : b.coord 0 x = 1 := by
      have hi' : b.coord 2 x = 0 := by simpa [b] using hi
      have hj' : b.coord 1 x = 0 := by simpa [b] using hj
      have hsum' : b.coord 0 x + b.coord 1 x + b.coord 2 x = 1 := by
        have hsum'' := hsum
        rw [Fin.sum_univ_three] at hsum''
        exact hsum''
      linarith
    refine ⟨0, b.ext_elem ?_⟩
    intro l
    fin_cases l
    · change b.coord 0 x = b.coord 0 (b 0)
      simpa using h0
    · have hj' : b.coord 1 x = 0 := by simpa [b] using hj
      change b.coord 1 x = b.coord 1 (b 0)
      simpa using hj'
    · have hi' : b.coord 2 x = 0 := by simpa [b] using hi
      change b.coord 2 x = b.coord 2 (b 0)
      simpa using hi'
  · exact (hij rfl).elim

/-- Helper for Exercise 6.11: a point lying on two distinct explicit opposite edges must be one of
the triangle vertices. -/
lemma boundaryPoint_mem_twoTriangleOppositeFacets_imp_vertex
    {t : Affine.Triangle ℝ R2} {x : R2} {i j : Fin 3}
    (hxi : x ∈ triangle_opposite_facet t i)
    (hxj : x ∈ triangle_opposite_facet t j)
    (hij : i ≠ j) :
    ∃ k : Fin 3, x = t.points k := by
  -- Route correction: convert each edge membership to a zero barycentric coordinate, then the
  -- remaining coordinate must be `1`.
  have hi : (triangleAffineBasis t).coord i x = 0 :=
    triangleClosedInterior_zeroCoord_of_memOppositeFacet hxi
  have hj : (triangleAffineBasis t).coord j x = 0 :=
    triangleClosedInterior_zeroCoord_of_memOppositeFacet hxj
  exact triangleClosedInterior_twoZeroCoords_eq_vertex hij hi hj

/-- Helper for Exercise 6.11: a boundary point of the realized triangle lies on some explicit
opposite edge. -/
lemma boundaryPoint_mem_someTriangleOppositeFacet
    {T : Set R2} {t : Affine.Triangle ℝ R2} {x : R2}
    (ht : has_triangle_vertices T t)
    (hxT : x ∈ T)
    (hx_boundary : x ∉ t.interior) :
    ∃ i : Fin 3, x ∈ triangle_opposite_facet t i := by
  -- Rewrite the realized triangle to the simplex model and use the boundary decomposition.
  have hx_closed : x ∈ t.closedInterior := by
    rwa [ht] at hxT
  have hx_surface : x ∈ t.closedInterior \ t.interior := ⟨hx_closed, hx_boundary⟩
  rw [Affine.Simplex.closedInterior_diff_interior] at hx_surface
  exact Set.mem_iUnion.mp hx_surface

/-- Helper for Exercise 6.11: a boundary point of the realized triangle that is not a vertex lies
on exactly one explicit opposite edge. -/
lemma boundaryPoint_liesInUniqueOppositeFacet
    {T : Set R2} {t : Affine.Triangle ℝ R2} {x : R2}
    (ht : has_triangle_vertices T t)
    (hxT : x ∈ T)
    (hx_boundary : x ∉ t.interior)
    (hx_not_vertex : ∀ i : Fin 3, x ≠ t.points i) :
    ∃! i : Fin 3, x ∈ triangle_opposite_facet t i := by
  rcases boundaryPoint_mem_someTriangleOppositeFacet ht hxT hx_boundary with ⟨i, hxi⟩
  refine ⟨i, hxi, ?_⟩
  intro j hxj
  -- A second distinct opposite edge would force the point to be a vertex, contradicting the
  -- nonvertex hypothesis.
  by_contra hji
  have hij : i ≠ j := fun hij_eq ↦ hji hij_eq.symm
  rcases boundaryPoint_mem_twoTriangleOppositeFacets_imp_vertex hxi hxj hij with ⟨k, hk⟩
  exact hx_not_vertex k hk

/-- Helper for Exercise 6.11: a nonvertex point on an explicit opposite edge lies in the
1-simplex interior of that edge. -/
lemma triangleOppositeFacet_nonvertex_mem_faceInterior
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {x : R2}
    (hx : x ∈ triangle_opposite_facet t i)
    (hx_not_vertex : ∀ j : Fin 3, x ≠ t.points j) :
    x ∈ (t.faceOpposite i).interior := by
  -- Route correction: first upgrade closed-edge membership to `Wbtw`, then use the nonvertex
  -- hypotheses to strengthen it to `Sbtw` on the 1-simplex endpoints.
  have hx_wbtw :
      Wbtw ℝ ((t.faceOpposite i).points 0) x ((t.faceOpposite i).points 1) := by
    simpa [triangle_opposite_facet] using
      (Affine.Simplex.mem_closedInterior_iff_wbtw (s := t.faceOpposite i) (p := x)).1 hx
  have hx_ne_left : x ≠ (t.faceOpposite i).points 0 := by
    simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using
      hx_not_vertex (Fin.succAbove i 0)
  have hx_ne_right : x ≠ (t.faceOpposite i).points 1 := by
    simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using
      hx_not_vertex (Fin.succAbove i 1)
  have hx_sbtw :
      Sbtw ℝ ((t.faceOpposite i).points 0) x ((t.faceOpposite i).points 1) :=
    ⟨hx_wbtw, hx_ne_left, hx_ne_right⟩
  simpa using
    (Affine.Simplex.mem_interior_iff_sbtw (s := t.faceOpposite i) (p := x)).2 hx_sbtw

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the intrinsic interior of an
opposite edge is the ordinary simplex interior of that edge. -/
lemma triangleOppositeFacet_intrinsicInterior_eq_faceInterior
    (t : Affine.Triangle ℝ R2) (i : Fin 3) :
    intrinsicInterior ℝ (triangle_opposite_facet t i) = (t.faceOpposite i).interior := by
  let s : Affine.Simplex ℝ R2 1 := t.faceOpposite i
  let S : AffineSubspace ℝ R2 := affineSpan ℝ (triangle_opposite_facet t i)
  have hvertices_subset : Set.range s.points ⊆ s.closedInterior := by
    intro x hx
    rcases hx with ⟨j, rfl⟩
    exact s.point_mem_closedInterior j
  have hS_eq : S = affineSpan ℝ s.closedInterior := by
    simp [S, s, triangle_opposite_facet]
  have hpoints : affineSpan ℝ (Set.range s.points) ≤ S := by
    rw [hS_eq]
    exact affineSpan_mono ℝ hvertices_subset
  -- Local instance justification (torsor witness): restricting the edge simplex to its affine
  -- span needs one point in that span, supplied by either endpoint of the edge.
  letI : Nonempty S := Nonempty.map (AffineSubspace.inclusion hpoints) inferInstance
  let sr : Affine.Simplex ℝ S 1 := s.restrict S hpoints
  have hclosed : sr.closedInterior = S.subtype ⁻¹' s.closedInterior := by
    simpa [sr] using s.closedInterior_restrict hpoints
  have hinterior : sr.interior = S.subtype ⁻¹' s.interior := by
    simpa [sr] using s.interior_restrict hpoints
  have hinterior_closed : interior sr.closedInterior = sr.interior := by
    let e : S ≃ᵃⁱ[ℝ] S.direction := AffineIsometryEquiv.constVSub ℝ (sr.points 0)
    let sv : Affine.Simplex ℝ S.direction 1 := sr.map e.toAffineMap e.injective
    have hSdim : Module.finrank ℝ S.direction = 1 := by
      have hedge_dim := (triangleOppositeFacet_isFacetOf
        (T := t.closedInterior) (t := t) rfl i).2.2
      have htriangle_dim :
          Module.finrank ℝ (affineSpan ℝ t.closedInterior).direction = 2 := by
        rw [triangleAffineSpan_eq_top_of_has_triangle_vertices (T := t.closedInterior) rfl]
        rw [AffineSubspace.direction_top]
        simp
      rw [htriangle_dim] at hedge_dim
      have hedge_dim' : Module.finrank ℝ S.direction + 1 = 2 := by
        simpa [S] using hedge_dim
      omega
    have hspanv : affineSpan ℝ (Set.range sv.points) = ⊤ := by
      exact Affine.Simplex.span_eq_top sv hSdim
    let b : AffineBasis (Fin 2) ℝ S.direction := ⟨sv.points, sv.independent, hspanv⟩
    have hbInterior :
        interior (convexHull ℝ (Set.range sv.points)) =
          {y | ∀ j, 0 < b.coord j y} := by
      have hb := b.interior_convexHull
      change interior (convexHull ℝ (Set.range sv.points)) =
        {y | ∀ j, 0 < b.coord j y} at hb
      exact hb
    have hvectorInterior : interior sv.closedInterior = sv.interior := by
      rw [← sv.convexHull_eq_closedInterior, hbInterior]
      ext y
      constructor
      · intro hy
        have hsum : ∑ j, b.coord j y = 1 := b.sum_coord_apply_eq_one y
        have hweights : ∀ j, b.coord j y ∈ Set.Ioo (0 : ℝ) 1 := by
          intro j
          constructor
          · exact hy j
          · fin_cases j
            · have hother : 0 < b.coord 1 y := hy 1
              rw [Fin.sum_univ_two] at hsum
              have hself : 0 < b.coord 0 y := hy 0
              have hlt : b.coord 0 y < 1 := by linarith
              simpa using hlt
            · have hother : 0 < b.coord 0 y := hy 0
              rw [Fin.sum_univ_two] at hsum
              have hself : 0 < b.coord 1 y := hy 1
              have hlt : b.coord 1 y < 1 := by linarith
              simpa using hlt
        have hrepr : Finset.univ.affineCombination ℝ sv.points (fun j ↦ b.coord j y) = y := by
          rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
          change ∑ j, b.coord j y • b j = y
          exact b.linear_combination_coord_eq_self y
        rw [← hrepr]
        exact (sv.affineCombination_mem_interior_iff hsum).2 hweights
      · intro hy
        rcases hy with ⟨w, hw, hwIoo, rfl⟩
        intro j
        change 0 < b.coord j (Finset.univ.affineCombination ℝ b w)
        rw [b.coord_apply_combination_of_mem (Finset.mem_univ j) hw]
        exact (hwIoo j).1
    have hmapClosed : sv.closedInterior = e '' sr.closedInterior := by
      simpa [sv] using sr.closedInterior_map e.injective
    have hmapInterior : sv.interior = e '' sr.interior := by
      simpa [sv] using sr.interior_map e.injective
    apply e.injective.image_injective
    calc
      e '' interior sr.closedInterior = interior (e '' sr.closedInterior) := by
        simpa only [AffineIsometryEquiv.coe_toHomeomorph] using
          e.toHomeomorph.image_interior sr.closedInterior
      _ = interior sv.closedInterior := by rw [hmapClosed]
      _ = sv.interior := hvectorInterior
      _ = e '' sr.interior := hmapInterior
  have hfacet_closed : triangle_opposite_facet t i = s.closedInterior := by
    simp [s, triangle_opposite_facet]
  have hpreimage : S.subtype ⁻¹' triangle_opposite_facet t i = sr.closedInterior := by
    calc
      S.subtype ⁻¹' triangle_opposite_facet t i = S.subtype ⁻¹' s.closedInterior := by
        rw [hfacet_closed]
      _ = sr.closedInterior := hclosed.symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hyS : y ∈ interior (S.subtype ⁻¹' triangle_opposite_facet t i) := by
      simpa [S] using hy
    rw [hpreimage] at hyS
    rw [hinterior_closed] at hyS
    have hy_preimage : y ∈ S.subtype ⁻¹' s.interior := by
      rw [← hinterior]
      exact hyS
    simpa [S, s] using hy_preimage
  · intro hx
    refine ⟨⟨x, subset_affineSpan ℝ _ ?_⟩, ?_, rfl⟩
    · exact s.interior_subset_closedInterior hx
    · have hxS :
          (⟨x, subset_affineSpan ℝ _ (s.interior_subset_closedInterior hx)⟩ : S) ∈
            interior (S.subtype ⁻¹' triangle_opposite_facet t i) := by
        rw [hpreimage, hinterior_closed, hinterior]
        exact hx
      simpa [S] using hxS

/-- Helper for Exercise 6.11: a nonvertex point on an explicit opposite edge lies in the
intrinsic interior of that edge. -/
lemma triangleOppositeFacet_nonvertex_mem_intrinsicInterior
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {x : R2}
    (hx : x ∈ triangle_opposite_facet t i)
    (hx_not_vertex : ∀ j : Fin 3, x ≠ t.points j) :
    x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) := by
  -- The edge-interface lemma hides the affine-span restriction and leaves the already proved
  -- one-simplex interior fact as the only geometric obligation.
  rw [triangleOppositeFacet_intrinsicInterior_eq_faceInterior]
  exact triangleOppositeFacet_nonvertex_mem_faceInterior hx hx_not_vertex

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the simplex interior of a
realized triangle is its ambient topological interior. -/
lemma interior_eq_triangleInterior_of_has_triangle_vertices
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t) :
    interior T = t.interior := by
  let b : AffineBasis (Fin 3) ℝ R2 := triangleAffineBasis t
  have hbInterior :
      interior (convexHull ℝ (Set.range t.points)) =
        {x | ∀ j, 0 < b.coord j x} := by
    have hb := b.interior_convexHull
    change interior (convexHull ℝ (Set.range t.points)) =
      {x | ∀ j, 0 < b.coord j x} at hb
    exact hb
  rw [ht, ← t.convexHull_eq_closedInterior, hbInterior]
  ext x
  constructor
  · intro hx
    have hsum : ∑ j, b.coord j x = 1 := b.sum_coord_apply_eq_one x
    have hweights : ∀ j, b.coord j x ∈ Set.Ioo (0 : ℝ) 1 := by
      intro j
      constructor
      · exact hx j
      · fin_cases j
        · have hother : 0 < b.coord 1 x := hx 1
          have hother' : 0 < b.coord 2 x := hx 2
          rw [Fin.sum_univ_three] at hsum
          have hself : 0 < b.coord 0 x := hx 0
          have hlt : b.coord 0 x < 1 := by linarith
          simpa using hlt
        · have hother : 0 < b.coord 0 x := hx 0
          have hother' : 0 < b.coord 2 x := hx 2
          rw [Fin.sum_univ_three] at hsum
          have hself : 0 < b.coord 1 x := hx 1
          have hlt : b.coord 1 x < 1 := by linarith
          simpa using hlt
        · have hother : 0 < b.coord 0 x := hx 0
          have hother' : 0 < b.coord 1 x := hx 1
          rw [Fin.sum_univ_three] at hsum
          have hself : 0 < b.coord 2 x := hx 2
          have hlt : b.coord 2 x < 1 := by linarith
          simpa using hlt
    have hrepr : Finset.univ.affineCombination ℝ t.points (fun j ↦ b.coord j x) = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      change ∑ j, b.coord j x • b j = x
      exact b.linear_combination_coord_eq_self x
    rw [← hrepr]
    exact (t.affineCombination_mem_interior_iff hsum).2 hweights
  · intro hx
    rcases hx with ⟨w, hw, hwIoo, rfl⟩
    intro j
    change 0 < b.coord j (Finset.univ.affineCombination ℝ b w)
    rw [b.coord_apply_combination_of_mem (Finset.mem_univ j) hw]
    exact (hwIoo j).1

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: distinct omitted vertices
determine distinct opposite edges. -/
lemma triangleOppositeFacet_injective
    (t : Affine.Triangle ℝ R2) :
    Function.Injective (triangle_opposite_facet t) := by
  intro i j hij
  by_contra hne
  have hmemj : t.points i ∈ triangle_opposite_facet t j := by
    simpa [triangle_opposite_facet] using
      (t.point_mem_closedInterior_faceOpposite_iff (i := j) (j := i)).2 hne
  have hnotmemi : t.points i ∉ triangle_opposite_facet t i := by
    simp [triangle_opposite_facet]
  rw [← hij] at hmemj
  exact hnotmemi hmemj

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: a face is contained in an
extreme face whenever an intrinsic-interior point of the first face belongs to the second. -/
lemma intrinsicInteriorFace_subset_extremeFace
    {K F G : Set R2} {x : R2}
    (hFK : F ⊆ K)
    (hxF : x ∈ intrinsicInterior ℝ F)
    (hG : IsExtreme ℝ K G)
    (hxG : x ∈ G) :
    F ⊆ G := by
  intro y hyF
  rcases mem_intrinsicInterior.mp hxF with ⟨xAff, hxAffInterior, hxAff_eq⟩
  -- Local instance justification (torsor witness): the intrinsic-interior representative supplies
  -- the basepoint required on the affine-span subtype.
  letI : Nonempty ↥(affineSpan ℝ F) := ⟨xAff⟩
  have hyAff_mem : y ∈ affineSpan ℝ F := subset_affineSpan ℝ F hyF
  let yAff : affineSpan ℝ F := ⟨y, hyAff_mem⟩
  have hhom :
      ∀ᶠ δ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
        AffineMap.homothety yAff δ xAff ∈
          ((↑) ⁻¹' F : Set (affineSpan ℝ F)) := by
    exact
      (eventually_homothety_mem_of_mem_interior ℝ yAff hxAffInterior).filter_mono
        nhdsWithin_le_nhds
  rcases (hhom.and self_mem_nhdsWithin).exists with ⟨δ, hδF, hδgt⟩
  have hδgt' : 1 < δ := by
    simpa using hδgt
  have hz_eq :
      ((AffineMap.homothety yAff δ xAff : affineSpan ℝ F) : R2) =
        AffineMap.homothety y δ x := by
    ext k
    simp [yAff, hxAff_eq, AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply]
  have hzF : AffineMap.homothety y δ x ∈ F := by
    rw [← hz_eq]
    exact hδF
  have hδpos : 0 < δ := zero_lt_one.trans hδgt'
  have hδinv : δ⁻¹ ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨inv_pos.mpr hδpos, inv_lt_one_of_one_lt₀ hδgt'⟩
  have hline :
      AffineMap.lineMap y (AffineMap.homothety y δ x) δ⁻¹ = x := by
    rw [← AffineMap.homothety_eq_lineMap, ← AffineMap.homothety_mul_apply]
    simp [hδpos.ne']
  have hx_segment : x ∈ openSegment ℝ y (AffineMap.homothety y δ x) := by
    have hline_mem :=
      lineMap_mem_openSegment (𝕜 := ℝ) y (AffineMap.homothety y δ x) hδinv
    rwa [hline] at hline_mem
  exact hG.left_mem_of_mem_openSegment (hFK hyF) (hFK hzF) hxG hx_segment

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: two facets of a polyhedron are
equal if one contains the other. -/
lemma isFacetOf_eq_of_subset_of_polyhedron
    {K F G : Set R2}
    (hpoly : is_polyhedron K)
    (hF : IsFacetOf K F)
    (hG : IsFacetOf K G)
    (hFG : F ⊆ G) :
    F = G := by
  rcases hpoly with ⟨m, A, b, rfl⟩
  have hF_facet : is_facet (polyhedron_le_set A b) F :=
    isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
      A b F hF.2.1 hF.1 hF.2.2
  have hG_facet : is_facet (polyhedron_le_set A b) G :=
    isFacet_of_nonempty_finrank_direction_affineSpan_add_one_eq
      A b G hG.2.1 hG.1 hG.2.2
  exact (is_facet_maximal hF_facet (is_facet_to_is_proper_face hG_facet) hFG).symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: every facet of a maximal
lattice-free realized triangle is one of its three explicit opposite edges. -/
lemma triangleFacet_eq_oppositeFacet
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    {F : Set R2}
    (hF : IsFacetOf T F) :
    ∃ i : Fin 3, F = triangle_opposite_facet t i := by
  classical
  have hfull : affineSpan ℝ T = ⊤ :=
    triangleAffineSpan_eq_top_of_has_triangle_vertices ht
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp hT_maximal
    with ⟨hpoly, hfree, hfacetWitness⟩
  let z : Fin 2 → ℤ := Classical.choose (hfacetWitness F hF)
  let x : R2 := Int.cast ∘ z
  have hxF : x ∈ intrinsicInterior ℝ F := by
    simpa [x, z] using Classical.choose_spec (hfacetWitness F hF)
  have hxInt : x ∈ ℤ^2 := (mem_integerVectors_iff).2 ⟨z, rfl⟩
  have hxT : x ∈ T := hF.2.1.subset (intrinsicInterior_subset hxF)
  have hx_not_interior : x ∉ t.interior := by
    intro hx
    have hx' : x ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact hx
    exact hfree.not_mem_interior hxInt hx'
  have hx_not_vertex : ∀ k : Fin 3, x ≠ t.points k := by
    intro k hxk
    let j0 : Fin 3 := Fin.succAbove k 0
    let j1 : Fin 3 := Fin.succAbove k 1
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have hj_ne : j0 ≠ j1 := by
      intro hj
      exact h01 (Fin.succAbove_right_injective hj)
    have hk0 : k ≠ j0 := Fin.ne_succAbove k 0
    have hk1 : k ≠ j1 := Fin.ne_succAbove k 1
    have hxj0 : x ∈ triangle_opposite_facet t j0 := by
      rw [hxk]
      simpa [triangle_opposite_facet] using
        (t.point_mem_closedInterior_faceOpposite_iff (i := j0) (j := k)).2 hk0
    have hxj1 : x ∈ triangle_opposite_facet t j1 := by
      rw [hxk]
      simpa [triangle_opposite_facet] using
        (t.point_mem_closedInterior_faceOpposite_iff (i := j1) (j := k)).2 hk1
    have hsubset0 : F ⊆ triangle_opposite_facet t j0 :=
      intrinsicInteriorFace_subset_extremeFace hF.2.1.subset hxF
        (triangleOppositeFacet_isFacetOf ht j0).2.1.isExtreme hxj0
    have hsubset1 : F ⊆ triangle_opposite_facet t j1 :=
      intrinsicInteriorFace_subset_extremeFace hF.2.1.subset hxF
        (triangleOppositeFacet_isFacetOf ht j1).2.1.isExtreme hxj1
    have hEq0 : F = triangle_opposite_facet t j0 :=
      isFacetOf_eq_of_subset_of_polyhedron hpoly hF
        (triangleOppositeFacet_isFacetOf ht j0) hsubset0
    have hEq1 : F = triangle_opposite_facet t j1 :=
      isFacetOf_eq_of_subset_of_polyhedron hpoly hF
        (triangleOppositeFacet_isFacetOf ht j1) hsubset1
    apply hj_ne
    apply triangleOppositeFacet_injective t
    exact hEq0.symm.trans hEq1
  rcases boundaryPoint_mem_someTriangleOppositeFacet ht hxT hx_not_interior with ⟨i, hxi⟩
  have hsubset : F ⊆ triangle_opposite_facet t i :=
    intrinsicInteriorFace_subset_extremeFace hF.2.1.subset hxF
      (triangleOppositeFacet_isFacetOf ht i).2.1.isExtreme hxi
  exact ⟨i, isFacetOf_eq_of_subset_of_polyhedron hpoly hF
    (triangleOppositeFacet_isFacetOf ht i) hsubset⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: an intrinsic point of an
opposite edge has a unique open-segment parameter between the two remaining vertices. -/
lemma triangleOppositeFacet_point_eq_lineMap
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {x : R2}
    (hx : x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i)) :
    ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      x = AffineMap.lineMap (t.points (Fin.succAbove i 0))
        (t.points (Fin.succAbove i 1)) r := by
  -- Pass through the one-simplex interface and then read strict betweenness as a line parameter.
  rw [triangleOppositeFacet_intrinsicInterior_eq_faceInterior] at hx
  have hsbtw := (Affine.Simplex.mem_interior_iff_sbtw.mp hx)
  rw [sbtw_iff_mem_image_Ioo_and_ne] at hsbtw
  rcases hsbtw.1 with ⟨r, hr, hrx⟩
  refine ⟨r, hr, ?_⟩
  simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using hrx.symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: a strict line parameter between
the two retained vertices gives an intrinsic point of the opposite edge. -/
lemma triangleOppositeFacet_lineMap_mem_intrinsicInterior
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {r : ℝ}
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap (t.points (Fin.succAbove i 0))
        (t.points (Fin.succAbove i 1)) r ∈
      intrinsicInterior ℝ (triangle_opposite_facet t i) := by
  rw [triangleOppositeFacet_intrinsicInterior_eq_faceInterior]
  rw [Affine.Simplex.mem_interior_iff_sbtw, sbtw_iff_mem_image_Ioo_and_ne]
  refine ⟨⟨r, hr, ?_⟩, ?_⟩
  · simp [Affine.Simplex.faceOpposite_point_eq_point_succAbove]
  · exact (t.faceOpposite i).independent.injective.ne (by decide)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the embedded integer lattice is
closed under adding two points and subtracting a third. -/
lemma integerVectors_add_sub_mem
    {x y z : R2}
    (hx : x ∈ ℤ^2) (hy : y ∈ ℤ^2) (hz : z ∈ ℤ^2) :
    x + y - z ∈ ℤ^2 := by
  rcases (mem_integerVectors_iff.mp hx) with ⟨u, rfl⟩
  rcases (mem_integerVectors_iff.mp hy) with ⟨v, rfl⟩
  rcases (mem_integerVectors_iff.mp hz) with ⟨w, rfl⟩
  -- Integer addition and subtraction can now be performed before coercing coordinatewise.
  refine mem_integerVectors_iff.mpr ⟨fun k ↦ u k + v k - w k, ?_⟩
  funext k
  simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: an integral point remains
integral after an integral dilation about an integral basepoint. -/
lemma integerVectors_natDilation_mem
    {p x : R2} (hp : p ∈ ℤ^2) (hx : x ∈ ℤ^2) (n : ℕ) :
    p + (n : ℝ) • (x - p) ∈ ℤ^2 := by
  rcases (mem_integerVectors_iff.mp hp) with ⟨u, rfl⟩
  rcases (mem_integerVectors_iff.mp hx) with ⟨v, rfl⟩
  -- The dilated point has the integer representative `u + n • (v - u)`.
  refine mem_integerVectors_iff.mpr ⟨fun k ↦ u k + (n : ℤ) * (v k - u k), ?_⟩
  funext k
  simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: reflecting an integral
open-segment point across the midpoint of integral endpoints normalizes its parameter to the first
half of the segment. -/
lemma integralSegmentPoint_normalize_le_half
    {p q x : R2} {r : ℝ}
    (hp : p ∈ ℤ^2) (hq : q ∈ ℤ^2) (hx : x ∈ ℤ^2)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hxline : x = AffineMap.lineMap p q r) :
    ∃ x' : R2, ∃ r' : ℝ,
      x' ∈ ℤ^2 ∧ r' ∈ Set.Ioo (0 : ℝ) 1 ∧ r' ≤ (1 : ℝ) / 2 ∧
        x' = AffineMap.lineMap p q r' := by
  by_cases hrhalf : r ≤ (1 : ℝ) / 2
  · exact ⟨x, r, hx, hr, hrhalf, hxline⟩
  · let x' : R2 := p + q - x
    let r' : ℝ := 1 - r
    have hr' : r' ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> dsimp [r'] <;> linarith [hr.1, hr.2]
    have hr'half : r' ≤ (1 : ℝ) / 2 := by
      dsimp [r']
      linarith
    have hx'int : x' ∈ ℤ^2 := integerVectors_add_sub_mem hp hq hx
    have hx'line : x' = AffineMap.lineMap p q r' := by
      simp only [x']
      rw [hxline]
      ext k
      simp [r', AffineMap.lineMap_apply_module]
      ring
    exact ⟨x', r', hx'int, hr', hr'half, hx'line⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: two distinct integral points
inside a segment with integral endpoints yield an integral point strictly before its midpoint. -/
lemma integralSegmentPoints_normalize_lt_half
    {p q x y : R2} {r s : ℝ}
    (hp : p ∈ ℤ^2) (hq : q ∈ ℤ^2)
    (hx : x ∈ ℤ^2) (hy : y ∈ ℤ^2) (hxy : x ≠ y)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (hxline : x = AffineMap.lineMap p q r)
    (hyline : y = AffineMap.lineMap p q s) :
    ∃ x' : R2, ∃ r' : ℝ,
      x' ∈ ℤ^2 ∧ r' ∈ Set.Ioo (0 : ℝ) ((1 : ℝ) / 2) ∧
        x' = AffineMap.lineMap p q r' := by
  have hpq : p ≠ q := by
    intro hpq
    rw [hpq] at hxline hyline
    simp at hxline hyline
    exact hxy (hxline.trans hyline.symm)
  by_cases hrlt : r < (1 : ℝ) / 2
  · exact ⟨x, r, hx, ⟨hr.1, hrlt⟩, hxline⟩
  by_cases hrgt : (1 : ℝ) / 2 < r
  · let x' : R2 := p + q - x
    let r' : ℝ := 1 - r
    have hr' : r' ∈ Set.Ioo (0 : ℝ) ((1 : ℝ) / 2) := by
      constructor <;> dsimp [r'] <;> linarith [hr.2]
    have hx'int : x' ∈ ℤ^2 := integerVectors_add_sub_mem hp hq hx
    have hx'line : x' = AffineMap.lineMap p q r' := by
      simp only [x']
      rw [hxline]
      ext k
      simp [r', AffineMap.lineMap_apply_module]
      ring
    exact ⟨x', r', hx'int, hr', hx'line⟩
  have hrequal : r = (1 : ℝ) / 2 := by linarith
  have hsr : s ≠ r := by
    intro hsr
    apply hxy
    rw [hxline, hyline, hsr]
  by_cases hslt : s < (1 : ℝ) / 2
  · exact ⟨y, s, hy, ⟨hs.1, hslt⟩, hyline⟩
  have hsgt : (1 : ℝ) / 2 < s := by
    rcases lt_trichotomy s ((1 : ℝ) / 2) with h | h | h
    · exact (hslt h).elim
    · exact (hsr (h.trans hrequal.symm)).elim
    · exact h
  let y' : R2 := p + q - y
  let s' : ℝ := 1 - s
  have hs' : s' ∈ Set.Ioo (0 : ℝ) ((1 : ℝ) / 2) := by
    constructor <;> dsimp [s'] <;> linarith [hs.2]
  have hy'int : y' ∈ ℤ^2 := integerVectors_add_sub_mem hp hq hy
  have hy'line : y' = AffineMap.lineMap p q s' := by
    simp only [y']
    rw [hyline]
    ext k
    simp [s', AffineMap.lineMap_apply_module]
    ring
  exact ⟨y', s', hy'int, hs', hy'line⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: an integral point strictly
inside a segment from an integral to a nonintegral endpoint can be dilated to lie beyond the
midpoint while remaining strictly inside and integral. -/
lemma integerSegmentPoint_normalize_gt_half
    {p q x : R2} {r : ℝ}
    (hp : p ∈ ℤ^2) (hq : q ∉ ℤ^2) (hx : x ∈ ℤ^2)
    (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hxline : x = AffineMap.lineMap p q r) :
    ∃ x' : R2, ∃ r' : ℝ,
      x' ∈ ℤ^2 ∧ r' ∈ Set.Ioo ((1 : ℝ) / 2) 1 ∧
        x' = AffineMap.lineMap p q r' := by
  rcases exists_nat_pow_near_of_lt_one hr.1 hr.2.le
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1) with
    ⟨n, hnlow, hnhigh⟩
  let r' : ℝ := (2 : ℝ) ^ n * r
  let x' : R2 := p + ((2 : ℕ) ^ n : ℝ) • (x - p)
  have hpow : (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  have hpowSucc : (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (n + 1) = (1 : ℝ) / 2 := by
    calc
      (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (n + 1) =
          ((2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ n) * ((1 : ℝ) / 2) := by
            rw [pow_succ]
            ring
      _ = (1 : ℝ) / 2 := by rw [hpow]; norm_num
  have hpowpos : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) n
  have hr'le : r' ≤ 1 := by
    dsimp [r']
    nlinarith
  have hr'gt : (1 : ℝ) / 2 < r' := by
    dsimp [r']
    nlinarith
  have hx'int : x' ∈ ℤ^2 := by
    simpa [x'] using integerVectors_natDilation_mem hp hx ((2 : ℕ) ^ n)
  have hx'line : x' = AffineMap.lineMap p q r' := by
    simp only [x']
    rw [hxline]
    ext k
    simp [r', AffineMap.lineMap_apply_module]
    ring
  have hr'ne : r' ≠ 1 := by
    intro hr'one
    apply hq
    have hx'q : x' = q := by
      rw [hx'line, hr'one]
      simp
    rwa [← hx'q]
  have hr'lt : r' < 1 := lt_of_le_of_ne hr'le hr'ne
  exact ⟨x', r', hx'int, ⟨hr'gt, hr'lt⟩, hx'line⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: positive barycentric weights
summing to one determine a point in the interior of a triangle. -/
lemma triangleAffineCombination_mem_interior_of_pos
    (t : Affine.Triangle ℝ R2) {w : Fin 3 → ℝ}
    (hsum : ∑ i, w i = 1) (hpos : ∀ i, 0 < w i) :
    Finset.univ.affineCombination ℝ t.points w ∈ t.interior := by
  have hweights : ∀ i, w i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i
    constructor
    · exact hpos i
    · fin_cases i
      · have h1 := hpos 1
        have h2 := hpos 2
        rw [Fin.sum_univ_three] at hsum
        change w 0 < 1
        linarith
      · have h0 := hpos 0
        have h2 := hpos 2
        rw [Fin.sum_univ_three] at hsum
        change w 1 < 1
        linarith
      · have h0 := hpos 0
        have h1 := hpos 1
        rw [Fin.sum_univ_three] at hsum
        change w 2 < 1
        linarith
  exact (t.affineCombination_mem_interior_iff hsum).2 hweights

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: adding points on the two edges
from a common vertex and subtracting that vertex lands in the triangle interior when the two edge
parameters have sum less than one. -/
lemma triangle_edgePair_add_sub_mem_interior
    (t : Affine.Triangle ℝ R2) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s < 1) :
    AffineMap.lineMap (t.points 0) (t.points 1) r +
        AffineMap.lineMap (t.points 0) (t.points 2) s - t.points 0 ∈ t.interior := by
  let w : Fin 3 → ℝ := ![1 - r - s, r, s]
  have hsum : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_three]
    ring
  have hpos : ∀ i, 0 < w i := by
    intro i
    fin_cases i <;> simp [w] <;> linarith
  have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
  have heq :
      Finset.univ.affineCombination ℝ t.points w =
        AffineMap.lineMap (t.points 0) (t.points 1) r +
          AffineMap.lineMap (t.points 0) (t.points 2) s - t.points 0 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    ext k
    simp [w, Fin.sum_univ_three, AffineMap.lineMap_apply_module]
    ring
  rwa [heq] at hmem

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the two-edge interior
construction based at vertex `1` has positive barycentric coordinates. -/
lemma triangle_edgePairAtOne_add_sub_mem_interior
    (t : Affine.Triangle ℝ R2) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s < 1) :
    AffineMap.lineMap (t.points 1) (t.points 2) r +
        AffineMap.lineMap (t.points 1) (t.points 0) s - t.points 1 ∈ t.interior := by
  let w : Fin 3 → ℝ := ![s, 1 - r - s, r]
  have hsum : ∑ i, w i = 1 := by
    simp [w, Fin.sum_univ_three]
  have hpos : ∀ i, 0 < w i := by
    intro i
    fin_cases i <;> simp [w] <;> linarith
  have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
  have heq :
      Finset.univ.affineCombination ℝ t.points w =
        AffineMap.lineMap (t.points 1) (t.points 2) r +
          AffineMap.lineMap (t.points 1) (t.points 0) s - t.points 1 := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    ext k
    simp [w, Fin.sum_univ_three, AffineMap.lineMap_apply_module]
    ring
  rwa [heq] at hmem

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: swapping the two outgoing
edges in the vertex-`0` interior construction does not affect its conclusion. -/
lemma triangle_edgePairAtZero_swap_add_sub_mem_interior
    (t : Affine.Triangle ℝ R2) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r + s < 1) :
    AffineMap.lineMap (t.points 0) (t.points 2) r +
        AffineMap.lineMap (t.points 0) (t.points 1) s - t.points 0 ∈ t.interior := by
  -- Commute the two edge points and apply the vertex-`0` construction.
  simpa [add_comm] using triangle_edgePair_add_sub_mem_interior t hs hr (by linarith)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the midpoint of a vertex and an
intrinsic point of its opposite edge lies in the triangle interior. -/
lemma triangleMidpoint_vertex_oppositeFacet_mem_interior
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {x : R2}
    (hx : x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i)) :
    midpoint ℝ (t.points i) x ∈ t.interior := by
  rcases triangleOppositeFacet_point_eq_lineMap hx with ⟨r, hr, rfl⟩
  -- There are only three choices of omitted vertex; in each case the midpoint has three strictly
  -- positive barycentric weights.
  fin_cases i
  · let w : Fin 3 → ℝ := ![(1 : ℝ) / 2, (1 - r) / 2, r / 2]
    have hsum : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ j, 0 < w j := by
      intro j
      fin_cases j <;> simp [w] <;> linarith [hr.1, hr.2]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq :
        midpoint ℝ (t.points 0)
            (AffineMap.lineMap (t.points 1) (t.points 2) r) =
          Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [w, Fin.sum_univ_three, midpoint, AffineMap.lineMap_apply_module]
      ring
    exact heq.symm ▸ hmem
  · let w : Fin 3 → ℝ := ![(1 - r) / 2, (1 : ℝ) / 2, r / 2]
    have hsum : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ j, 0 < w j := by
      intro j
      fin_cases j <;> simp [w] <;> linarith [hr.1, hr.2]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq :
        midpoint ℝ (t.points 1)
            (AffineMap.lineMap (t.points 0) (t.points 2) r) =
          Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [w, Fin.sum_univ_three, midpoint, AffineMap.lineMap_apply_module]
      ring
    exact heq.symm ▸ hmem
  · let w : Fin 3 → ℝ := ![(1 - r) / 2, r / 2, (1 : ℝ) / 2]
    have hsum : ∑ j, w j = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ j, 0 < w j := by
      intro j
      fin_cases j <;> simp [w] <;> linarith [hr.1, hr.2]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq :
        midpoint ℝ (t.points 2)
            (AffineMap.lineMap (t.points 0) (t.points 1) r) =
          Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [w, Fin.sum_univ_three, midpoint, AffineMap.lineMap_apply_module]
      ring
    exact heq.symm ▸ hmem

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: the midpoint of either endpoint
of an opposite edge with an intrinsic point remains intrinsic to that edge and differs from the
original intrinsic point. -/
lemma triangleMidpoint_edgeEndpoint_mem_intrinsicInterior_ne
    {t : Affine.Triangle ℝ R2} {i : Fin 3} {x : R2} (j : Fin 2)
    (hx : x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i)) :
    midpoint ℝ (t.points (Fin.succAbove i j)) x ∈
        intrinsicInterior ℝ (triangle_opposite_facet t i) ∧
      midpoint ℝ (t.points (Fin.succAbove i j)) x ≠ x := by
  rcases triangleOppositeFacet_point_eq_lineMap hx with ⟨r, hr, hxline⟩
  rw [triangleOppositeFacet_intrinsicInterior_eq_faceInterior]
  rw [Affine.Simplex.mem_interior_iff_sbtw, sbtw_iff_mem_image_Ioo_and_ne]
  have hendpoints :
      (t.faceOpposite i).points 0 ≠ (t.faceOpposite i).points 1 :=
    (t.faceOpposite i).independent.injective.ne (by decide)
  fin_cases j
  · have hparameter : r / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hr.1, hr.2]
    have hmidline :
        AffineMap.lineMap (t.points (Fin.succAbove i 0))
            (t.points (Fin.succAbove i 1)) (r / 2) =
          midpoint ℝ (t.points (Fin.succAbove i 0)) x := by
      rw [hxline]
      ext k
      simp [midpoint, AffineMap.lineMap_apply_module]
      ring
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ⟨r / 2, hparameter, ?_⟩
      simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using hmidline
    · exact hendpoints
    · intro heq
      have hlineeq :
          AffineMap.lineMap (t.points (Fin.succAbove i 0))
              (t.points (Fin.succAbove i 1)) (r / 2) =
            AffineMap.lineMap (t.points (Fin.succAbove i 0))
              (t.points (Fin.succAbove i 1)) r :=
        hmidline.trans (heq.trans hxline)
      have hparam := (AffineMap.lineMap_injective ℝ
        (by simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using hendpoints)) hlineeq
      linarith [hr.1]
  · have hparameter : (1 + r) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hr.1, hr.2]
    have hmidline :
        AffineMap.lineMap (t.points (Fin.succAbove i 0))
            (t.points (Fin.succAbove i 1)) ((1 + r) / 2) =
          midpoint ℝ (t.points (Fin.succAbove i 1)) x := by
      rw [hxline]
      ext k
      simp [midpoint, AffineMap.lineMap_apply_module]
      ring
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine ⟨(1 + r) / 2, hparameter, ?_⟩
      simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using hmidline
    · exact hendpoints
    · intro heq
      have hlineeq :
          AffineMap.lineMap (t.points (Fin.succAbove i 0))
              (t.points (Fin.succAbove i 1)) ((1 + r) / 2) =
            AffineMap.lineMap (t.points (Fin.succAbove i 0))
              (t.points (Fin.succAbove i 1)) r :=
        hmidline.trans (heq.trans hxline)
      have hparam := (AffineMap.lineMap_injective ℝ
        (by simpa [Affine.Simplex.faceOpposite_point_eq_point_succAbove] using hendpoints)) hlineeq
      linarith [hr.2]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: four pairwise distinct parity
classes in `ℤ²` have an even coordinatewise sum, so their real average by two is integral. -/
lemma fourDistinctParities_halfSum_mem_integerVectors
    (u : Fin 4 → Fin 2 → ℤ)
    (hinj : Function.Injective (fun j : Fin 4 ↦ fun k : Fin 2 ↦ (u j k : ZMod 2))) :
    (fun k : Fin 2 ↦ ((u 0 k : ℝ) + (u 1 k : ℝ) + (u 2 k : ℝ) + (u 3 k : ℝ)) / 2) ∈
      ℤ^2 := by
  let parity : Fin 4 → Fin 2 → ZMod 2 :=
    fun j k ↦ (u j k : ZMod 2)
  have hcard : Fintype.card (Fin 4) = Fintype.card (Fin 2 → ZMod 2) := by
    simp [ZMod.card]
  have hbij : Function.Bijective parity :=
    (Fintype.bijective_iff_injective_and_card parity).2 ⟨hinj, hcard⟩
  let e : Fin 4 ≃ (Fin 2 → ZMod 2) := Equiv.ofBijective parity hbij
  have hsumParity : ∑ j : Fin 4, parity j = 0 := by
    calc
      ∑ j : Fin 4, parity j = ∑ q : Fin 2 → ZMod 2, q := e.sum_comp id
      _ = 0 := by decide
  have heven : ∀ k : Fin 2, Even (u 0 k + u 1 k + u 2 k + u 3 k) := by
    intro k
    rw [← ZMod.intCast_eq_zero_iff_even]
    have hk := congrFun hsumParity k
    simpa [parity, Fin.sum_univ_four] using hk
  refine mem_integerVectors_iff.mpr ⟨
    fun k ↦ (u 0 k + u 1 k + u 2 k + u 3 k) / 2, ?_⟩
  funext k
  have htwo_ne : ((2 : ℤ) : ℝ) ≠ 0 := by norm_num
  simpa [Int.cast_add] using (Int.cast_div (even_iff_two_dvd.mp (heven k)) htwo_ne).symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: four integral points whose
pairwise midpoints are nonintegral have an integral coordinatewise half-sum. -/
lemma fourIntegralPoints_halfSum_mem_integerVectors
    (x : Fin 4 → R2)
    (hx : ∀ i, x i ∈ ℤ^2)
    (hmid : ∀ i j, i ≠ j → midpoint ℝ (x i) (x j) ∉ ℤ^2) :
    (fun k : Fin 2 ↦ (x 0 k + x 1 k + x 2 k + x 3 k) / 2) ∈ ℤ^2 := by
  classical
  choose u hu using fun i ↦ mem_integerVectors_iff.mp (hx i)
  have hparity : Function.Injective
      (fun i : Fin 4 ↦ fun k : Fin 2 ↦ (u i k : ZMod 2)) := by
    intro i j hij
    by_contra hne
    have hmidInt := sameParity_midpoint_memIntegerLattice
      (z := u i) (z' := u j) (fun k ↦ congrFun hij k)
    apply hmid i j hne
    simpa [hu i, hu j] using hmidInt
  have hhalf := fourDistinctParities_halfSum_mem_integerVectors u hparity
  simpa [hu 0, hu 1, hu 2, hu 3] using hhalf

/-- Helper for Exercise 6.11: once the facet-uniqueness argument is supplied, integral vertices
place `T` in case (a). -/
lemma integralVertices_force_caseA
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    (hverts : ∀ i : Fin 3, t.points i ∈ ℤ^2) :
    exercise_6_11_case_a T := by
  classical
  refine ⟨⟨t, ht, hverts⟩, ?_⟩
  rcases triangleFacetLatticeWitnesses ht hT_maximal with ⟨z, hz⟩
  intro F hF
  rcases triangleFacet_eq_oppositeFacet ht hT_maximal hF with ⟨i, rfl⟩
  refine ⟨z i, hz i, ?_⟩
  intro y hy
  by_contra hyz
  have hfull : affineSpan ℝ T = ⊤ :=
    triangleAffineSpan_eq_top_of_has_triangle_vertices ht
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp
        hT_maximal with
    ⟨_, hfree, _⟩
  -- On each concrete edge, reflect one of the two alleged points into the strict first half and
  -- an adjacent witness into the weak first half. Their translated sum has positive barycentric
  -- coordinates and is integral, contradicting lattice-freeness.
  fin_cases i
  · rcases triangleOppositeFacet_point_eq_lineMap hy.1 with ⟨r, hr, hyr⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 0).1 with ⟨r', hr', hzr'⟩
    rcases integralSegmentPoints_normalize_lt_half (hverts 1) (hverts 2)
        hy.2 (hz 0).2 hyz hr hr' hyr hzr' with ⟨x, a, hxInt, ha, hxa⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 2).1 with ⟨s, hs, hzs⟩
    have hzs' : z 2 = AffineMap.lineMap (t.points 0) (t.points 1) s := by
      simpa using hzs
    have hzsRev : z 2 = AffineMap.lineMap (t.points 1) (t.points 0) (1 - s) := by
      rw [hzs']
      ext k
      simp [AffineMap.lineMap_apply_module]
      ring
    have hsRev : 1 - s ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [hs.1, hs.2]
    rcases integralSegmentPoint_normalize_le_half (hverts 1) (hverts 0)
        (hz 2).2 hsRev hzsRev with ⟨x', b, hx'Int, hb, hbhalf, hx'b⟩
    have hab : a + b < 1 := by linarith [ha.2, hbhalf]
    have hinside : x + x' - t.points 1 ∈ t.interior := by
      rw [hxa, hx'b]
      exact triangle_edgePairAtOne_add_sub_mem_interior t ha.1 hb.1 hab
    have hinsideT : x + x' - t.points 1 ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact hinside
    exact hfree.not_mem_interior
      (integerVectors_add_sub_mem hxInt hx'Int (hverts 1)) hinsideT
  · rcases triangleOppositeFacet_point_eq_lineMap hy.1 with ⟨r, hr, hyr⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 1).1 with ⟨r', hr', hzr'⟩
    rcases integralSegmentPoints_normalize_lt_half (hverts 0) (hverts 2)
        hy.2 (hz 1).2 hyz hr hr' hyr hzr' with ⟨x, a, hxInt, ha, hxa⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 2).1 with ⟨s, hs, hzs⟩
    rcases integralSegmentPoint_normalize_le_half (hverts 0) (hverts 1)
        (hz 2).2 hs hzs with ⟨x', b, hx'Int, hb, hbhalf, hx'b⟩
    have hab : a + b < 1 := by linarith [ha.2, hbhalf]
    have hinside : x + x' - t.points 0 ∈ t.interior := by
      rw [hxa, hx'b]
      exact triangle_edgePairAtZero_swap_add_sub_mem_interior t ha.1 hb.1 hab
    have hinsideT : x + x' - t.points 0 ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact hinside
    exact hfree.not_mem_interior
      (integerVectors_add_sub_mem hxInt hx'Int (hverts 0)) hinsideT
  · rcases triangleOppositeFacet_point_eq_lineMap hy.1 with ⟨r, hr, hyr⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 2).1 with ⟨r', hr', hzr'⟩
    rcases integralSegmentPoints_normalize_lt_half (hverts 0) (hverts 1)
        hy.2 (hz 2).2 hyz hr hr' hyr hzr' with ⟨x, a, hxInt, ha, hxa⟩
    rcases triangleOppositeFacet_point_eq_lineMap (hz 1).1 with ⟨s, hs, hzs⟩
    rcases integralSegmentPoint_normalize_le_half (hverts 0) (hverts 2)
        (hz 1).2 hs hzs with ⟨x', b, hx'Int, hb, hbhalf, hx'b⟩
    have hab : a + b < 1 := by linarith [ha.2, hbhalf]
    have hinside : x + x' - t.points 0 ∈ t.interior := by
      rw [hxa, hx'b]
      exact triangle_edgePair_add_sub_mem_interior t ha.1 hb.1 hab
    have hinsideT : x + x' - t.points 0 ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact hinside
    exact hfree.not_mem_interior
      (integerVectors_add_sub_mem hxInt hx'Int (hverts 0)) hinsideT

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: reindexing a triangle carries
an opposite edge to the edge opposite the corresponding original vertex. -/
lemma triangleOppositeFacet_reindex
    (t : Affine.Triangle ℝ R2) (e : Fin 3 ≃ Fin 3) (i : Fin 3) :
    triangle_opposite_facet (t.reindex e) i =
      triangle_opposite_facet t (e.symm i) := by
  -- Both closed edges are convex hulls of the same reindexed pair of vertices.
  unfold triangle_opposite_facet
  rw [← ((t.reindex e).faceOpposite i).convexHull_eq_closedInterior]
  rw [← (t.faceOpposite (e.symm i)).convexHull_eq_closedInterior]
  rw [Affine.Simplex.range_faceOpposite_reindex]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: reindexing preserves a
triangle realization of a set. -/
lemma hasTriangleVertices_reindex
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t) (e : Fin 3 ≃ Fin 3) :
    has_triangle_vertices T (t.reindex e) := by
  -- The closed simplex depends only on the vertex set, not on its enumeration.
  simpa [has_triangle_vertices] using ht

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: a maximal lattice-free
triangle cannot have exactly vertices `0` and `1` integral when the edge opposite vertex `2`
has at most one intrinsic lattice point. -/
lemma triangle_twoIntegralVerticesZeroOne_impossible
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    (h0 : t.points 0 ∈ ℤ^2)
    (h1 : t.points 1 ∈ ℤ^2)
    (h2 : t.points 2 ∉ ℤ^2)
    (hno2 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
      (triangle_opposite_facet t 2)) :
    False := by
  classical
  rcases triangleFacetLatticeWitnesses ht hT_maximal with ⟨z, hz⟩
  rcases triangleOppositeFacet_point_eq_lineMap (hz 2).1 with ⟨a, ha, hza⟩
  have hza' : z 2 = AffineMap.lineMap (t.points 0) (t.points 1) a := by
    simpa using hza
  let zr : R2 := t.points 0 + t.points 1 - z 2
  let ar : ℝ := 1 - a
  have hzrInt : zr ∈ ℤ^2 := integerVectors_add_sub_mem h0 h1 (hz 2).2
  have har : ar ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [ar]
      linarith [ha.2]
    · dsimp [ar]
      linarith [ha.1]
  have hzrLine : zr = AffineMap.lineMap (t.points 0) (t.points 1) ar := by
    simp only [zr]
    rw [hza']
    ext k
    simp [ar, AffineMap.lineMap_apply_module]
    ring
  have hzrIntr : zr ∈ intrinsicInterior ℝ (triangle_opposite_facet t 2) := by
    rw [hzrLine]
    exact triangleOppositeFacet_lineMap_mem_intrinsicInterior har
  have hzrEq : zr = z 2 := by
    by_contra hne
    apply hno2
    exact ⟨zr, z 2, hne, ⟨hzrIntr, hzrInt⟩, hz 2⟩
  have haHalf : a = (1 : ℝ) / 2 := by
    have hlineeq :
        AffineMap.lineMap (t.points 0) (t.points 1) ar =
          AffineMap.lineMap (t.points 0) (t.points 1) a := by
      calc
        AffineMap.lineMap (t.points 0) (t.points 1) ar = zr := hzrLine.symm
        _ = z 2 := hzrEq
        _ = AffineMap.lineMap (t.points 0) (t.points 1) a := hza'
    have hp01 : t.points 0 ≠ t.points 1 := t.independent.injective.ne (by decide)
    have harEq : ar = a := (AffineMap.lineMap_injective ℝ hp01) hlineeq
    dsimp [ar] at harEq
    linarith
  have hz2Half : z 2 = AffineMap.lineMap (t.points 0) (t.points 1) ((1 : ℝ) / 2) := by
    rw [hza', haHalf]
  rcases triangleOppositeFacet_point_eq_lineMap (hz 1).1 with ⟨b₀, hb₀, hzb⟩
  rcases integerSegmentPoint_normalize_gt_half h0 h2 (hz 1).2 hb₀ hzb with
    ⟨x₀, b, hx₀Int, hb, hx₀Line⟩
  rcases triangleOppositeFacet_point_eq_lineMap (hz 0).1 with ⟨c₀, hc₀, hzc⟩
  rcases integerSegmentPoint_normalize_gt_half h1 h2 (hz 0).2 hc₀ hzc with
    ⟨x₁, c, hx₁Int, hc, hx₁Line⟩
  have hfull : affineSpan ℝ T = ⊤ :=
    triangleAffineSpan_eq_top_of_has_triangle_vertices ht
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp
        hT_maximal with
    ⟨_, hfree, _⟩
  -- Compare the two normalized edge parameters. A strict inequality produces an integral
  -- interior point; equality produces a second integral point on the integral edge.
  rcases lt_trichotomy b c with hbc | hbc | hcb
  · let q : R2 := x₁ + z 2 - x₀
    have hqInt : q ∈ ℤ^2 := by
      exact integerVectors_add_sub_mem hx₁Int (hz 2).2 hx₀Int
    let w : Fin 3 → ℝ := ![b - 1 / 2, 3 / 2 - c, c - b]
    have hsum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    have hpos : ∀ i, 0 < w i := by
      intro i
      fin_cases i <;> simp [w] <;> linarith [hb.1, hc.2]
    have hqEq : q = Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [q, w, hz2Half, hx₀Line, hx₁Line, Fin.sum_univ_three,
        AffineMap.lineMap_apply_module]
      ring
    have hqInside : q ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      rw [hqEq]
      exact triangleAffineCombination_mem_interior_of_pos t hsum hpos
    exact hfree.not_mem_interior hqInt hqInside
  · let q : R2 := x₀ + z 2 - x₁
    let d : ℝ := b - 1 / 2
    have hd : d ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · dsimp [d]
        linarith [hb.1]
      · dsimp [d]
        linarith [hb.2]
    have hqInt : q ∈ ℤ^2 :=
      integerVectors_add_sub_mem hx₀Int (hz 2).2 hx₁Int
    have hqLine : q = AffineMap.lineMap (t.points 0) (t.points 1) d := by
      ext k
      simp [q, d, hz2Half, hx₀Line, hx₁Line, hbc,
        AffineMap.lineMap_apply_module]
      ring
    have hqIntr : q ∈ intrinsicInterior ℝ (triangle_opposite_facet t 2) := by
      rw [hqLine]
      exact triangleOppositeFacet_lineMap_mem_intrinsicInterior hd
    have hqNe : q ≠ z 2 := by
      intro hqz
      rw [hqLine, hz2Half] at hqz
      have hp01 : t.points 0 ≠ t.points 1 := t.independent.injective.ne (by decide)
      have hdHalf := (AffineMap.lineMap_injective ℝ hp01) hqz
      dsimp [d] at hdHalf
      linarith [hb.2]
    apply hno2
    exact ⟨q, z 2, hqNe, ⟨hqIntr, hqInt⟩, hz 2⟩
  · let q : R2 := x₀ + z 2 - x₁
    have hqInt : q ∈ ℤ^2 :=
      integerVectors_add_sub_mem hx₀Int (hz 2).2 hx₁Int
    let w : Fin 3 → ℝ := ![3 / 2 - b, c - 1 / 2, b - c]
    have hsum : ∑ i, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    have hpos : ∀ i, 0 < w i := by
      intro i
      fin_cases i <;> simp [w] <;> linarith [hb.2, hc.1]
    have hqEq : q = Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [q, w, hz2Half, hx₀Line, hx₁Line, Fin.sum_univ_three,
        AffineMap.lineMap_apply_module]
      ring
    have hqInside : q ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      rw [hqEq]
      exact triangleAffineCombination_mem_interior_of_pos t hsum hpos
    exact hfree.not_mem_interior hqInt hqInside

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: a maximal lattice-free
triangle cannot have only its vertex `0` integral when the two facets incident to that vertex
each have at most one intrinsic lattice point. -/
lemma triangle_oneIntegralVertexZero_impossible
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    (h0 : t.points 0 ∈ ℤ^2)
    (h1 : t.points 1 ∉ ℤ^2)
    (h2 : t.points 2 ∉ ℤ^2)
    (hno1 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
      (triangle_opposite_facet t 1))
    (hno2 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
      (triangle_opposite_facet t 2)) :
    False := by
  classical
  rcases triangleFacetLatticeWitnesses ht hT_maximal with ⟨z, hz⟩
  rcases triangleOppositeFacet_point_eq_lineMap (hz 0).1 with ⟨a, ha, hza⟩
  rcases triangleOppositeFacet_point_eq_lineMap (hz 1).1 with ⟨b₀, hb₀, hzb⟩
  rcases integerSegmentPoint_normalize_gt_half h0 h2 (hz 1).2 hb₀ hzb with
    ⟨x₁, b, hx₁Int, hb, hx₁Line⟩
  rcases triangleOppositeFacet_point_eq_lineMap (hz 2).1 with ⟨c₀, hc₀, hzc⟩
  rcases integerSegmentPoint_normalize_gt_half h0 h1 (hz 2).2 hc₀ hzc with
    ⟨x₂, c, hx₂Int, hc, hx₂Line⟩
  have hx₁Intr : x₁ ∈ intrinsicInterior ℝ (triangle_opposite_facet t 1) := by
    rw [hx₁Line]
    exact triangleOppositeFacet_lineMap_mem_intrinsicInterior ⟨by linarith [hb.1], hb.2⟩
  have hx₂Intr : x₂ ∈ intrinsicInterior ℝ (triangle_opposite_facet t 2) := by
    rw [hx₂Line]
    exact triangleOppositeFacet_lineMap_mem_intrinsicInterior ⟨by linarith [hc.1], hc.2⟩
  have hfull : affineSpan ℝ T = ⊤ :=
    triangleAffineSpan_eq_top_of_has_triangle_vertices ht
  rcases
      (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp
        hT_maximal with
    ⟨hpoly, hfree, _⟩
  have hconv : Convex ℝ T := is_maximal_lattice_free.convex hT_maximal
  have hmidDistinct :
      ∀ {i j : Fin 3} {x y : R2}, i ≠ j →
        x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) →
        y ∈ intrinsicInterior ℝ (triangle_opposite_facet t j) →
        midpoint ℝ x y ∉ ℤ^2 := by
    intro i j x y hij hxi hyj hmidInt
    have hfacets : triangle_opposite_facet t i ≠ triangle_opposite_facet t j := by
      intro heq
      exact hij (triangleOppositeFacet_injective t heq)
    have hmidInterior : midpoint ℝ x y ∈ interior T :=
      midpoint_memInterior_of_distinctFacetInteriorPoints hpoly hconv hfull
        (triangleOppositeFacet_isFacetOf ht i) (triangleOppositeFacet_isFacetOf ht j)
        hfacets hxi hyj
    exact hfree.not_mem_interior hmidInt hmidInterior
  have hmid0z : midpoint ℝ (t.points 0) (z 0) ∉ ℤ^2 := by
    intro hmidInt
    have hmidInterior : midpoint ℝ (t.points 0) (z 0) ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact triangleMidpoint_vertex_oppositeFacet_mem_interior (hz 0).1
    exact hfree.not_mem_interior hmidInt hmidInterior
  have hmid0x₁ : midpoint ℝ (t.points 0) x₁ ∉ ℤ^2 := by
    intro hmidInt
    have hm := triangleMidpoint_edgeEndpoint_mem_intrinsicInterior_ne (i := 1) (j := 0) hx₁Intr
    apply hno1
    exact ⟨midpoint ℝ (t.points 0) x₁, x₁, hm.2, ⟨hm.1, hmidInt⟩, ⟨hx₁Intr, hx₁Int⟩⟩
  have hmid0x₂ : midpoint ℝ (t.points 0) x₂ ∉ ℤ^2 := by
    intro hmidInt
    have hm := triangleMidpoint_edgeEndpoint_mem_intrinsicInterior_ne (i := 2) (j := 0) hx₂Intr
    apply hno2
    exact ⟨midpoint ℝ (t.points 0) x₂, x₂, hm.2, ⟨hm.1, hmidInt⟩, ⟨hx₂Intr, hx₂Int⟩⟩
  let p : Fin 4 → R2 := ![t.points 0, z 0, x₁, x₂]
  have hpInt : ∀ i, p i ∈ ℤ^2 := by
    intro i
    fin_cases i
    · exact h0
    · exact (hz 0).2
    · exact hx₁Int
    · exact hx₂Int
  have hpMid : ∀ i j, i ≠ j → midpoint ℝ (p i) (p j) ∉ ℤ^2 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hmid0z
    · exact hmid0x₁
    · exact hmid0x₂
    · have hmid0z' := hmid0z
      rw [midpoint_comm] at hmid0z'
      simpa [p] using hmid0z'
    · exact (hij rfl).elim
    · exact hmidDistinct (by decide) (hz 0).1 hx₁Intr
    · exact hmidDistinct (by decide) (hz 0).1 hx₂Intr
    · have hmid0x₁' := hmid0x₁
      rw [midpoint_comm] at hmid0x₁'
      simpa [p] using hmid0x₁'
    · have hmidDistinct' := hmidDistinct (by decide) (hz 0).1 hx₁Intr
      rw [midpoint_comm] at hmidDistinct'
      simpa [p] using hmidDistinct'
    · exact (hij rfl).elim
    · exact hmidDistinct (by decide) hx₁Intr hx₂Intr
    · have hmid0x₂' := hmid0x₂
      rw [midpoint_comm] at hmid0x₂'
      simpa [p] using hmid0x₂'
    · have hmidDistinct' := hmidDistinct (by decide) (hz 0).1 hx₂Intr
      rw [midpoint_comm] at hmidDistinct'
      simpa [p] using hmidDistinct'
    · have hmidDistinct' := hmidDistinct (by decide) hx₁Intr hx₂Intr
      rw [midpoint_comm] at hmidDistinct'
      simpa [p] using hmidDistinct'
    · exact (hij rfl).elim
  let H : R2 := fun k ↦
    (t.points 0 k + z 0 k + x₁ k + x₂ k) / 2
  have hHInt : H ∈ ℤ^2 := by
    simpa [H, p] using fourIntegralPoints_halfSum_mem_integerVectors p hpInt hpMid
  have hsubInt : ∀ {x : R2}, x ∈ ℤ^2 → H - x ∈ ℤ^2 := by
    intro x hx
    have hzero_cast : (0 : R2) = Int.cast ∘ (0 : Fin 2 → ℤ) := by
      funext k
      simp
    have hzero : (0 : R2) ∈ ℤ^2 :=
      (mem_integerVectors_iff).2 ⟨0, hzero_cast⟩
    simpa using integerVectors_add_sub_mem hHInt hzero hx
  have hminusX₂Interior (hac : a + c < 1) : H - x₂ ∈ t.interior := by
    let w : Fin 3 → ℝ := ![(1 - b + c) / 2, (1 - a - c) / 2, (a + b) / 2]
    have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ i, 0 < w i := by
      intro i
      fin_cases i <;> simp [w] <;> linarith [ha.1, hb.1, hb.2, hc.1]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq : H - x₂ = Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [H, w, hza, hx₁Line, hx₂Line, Fin.sum_univ_three,
        AffineMap.lineMap_apply_module]
      ring
    rwa [heq]
  have hminusZInterior (hac : 1 < a + c) (hab : a < b) : H - z 0 ∈ t.interior := by
    let w : Fin 3 → ℝ := ![(3 - b - c) / 2, (a + c - 1) / 2, (b - a) / 2]
    have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ i, 0 < w i := by
      intro i
      fin_cases i <;> simp [w] <;> linarith [hb.2, hc.2]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq : H - z 0 = Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [H, w, hza, hx₁Line, hx₂Line, Fin.sum_univ_three,
        AffineMap.lineMap_apply_module]
      ring
    rwa [heq]
  have hminusX₁Interior (hba : b < a) : H - x₁ ∈ t.interior := by
    let w : Fin 3 → ℝ := ![(1 + b - c) / 2, (1 - a + c) / 2, (a - b) / 2]
    have hsum : ∑ i, w i = 1 := by simp [w, Fin.sum_univ_three]; ring
    have hpos : ∀ i, 0 < w i := by
      intro i
      fin_cases i <;> simp [w] <;> linarith [ha.1, ha.2, hb.1, hc.1, hc.2]
    have hmem := triangleAffineCombination_mem_interior_of_pos t hsum hpos
    have heq : H - x₁ = Finset.univ.affineCombination ℝ t.points w := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
      ext k
      simp [H, w, hza, hx₁Line, hx₂Line, Fin.sum_univ_three,
        AffineMap.lineMap_apply_module]
      ring
    rwa [heq]
  by_cases hac : a + c < 1
  · have hinside : H - x₂ ∈ interior T := by
      rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
      exact hminusX₂Interior hac
    exact hfree.not_mem_interior (hsubInt hx₂Int) hinside
  · have hacge : 1 ≤ a + c := le_of_not_gt hac
    by_cases hab : a < b
    · by_cases haceq : a + c = 1
      · let d : ℝ := (a + b) / 2
        have hd : d ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor <;> dsimp [d] <;> linarith [ha.1, ha.2, hb.1, hb.2]
        have heqLine : H - x₂ = AffineMap.lineMap (t.points 0) (t.points 2) d := by
          have hc_eq : c = 1 - a := by linarith
          ext k
          simp [H, d, hza, hx₁Line, hx₂Line, hc_eq,
            AffineMap.lineMap_apply_module]
          ring
        have hIntr : H - x₂ ∈ intrinsicInterior ℝ (triangle_opposite_facet t 1) := by
          rw [heqLine]
          exact triangleOppositeFacet_lineMap_mem_intrinsicInterior hd
        have hne : H - x₂ ≠ x₁ := by
          intro heq
          rw [heqLine, hx₁Line] at heq
          have hp02 : t.points 0 ≠ t.points 2 := t.independent.injective.ne (by decide)
          have hdEq := (AffineMap.lineMap_injective ℝ hp02) heq
          dsimp [d] at hdEq
          linarith
        apply hno1
        exact ⟨H - x₂, x₁, hne, ⟨hIntr, hsubInt hx₂Int⟩, ⟨hx₁Intr, hx₁Int⟩⟩
      · have hacgt : 1 < a + c := lt_of_le_of_ne hacge (Ne.symm haceq)
        have hinside : H - z 0 ∈ interior T := by
          rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
          exact hminusZInterior hacgt hab
        exact hfree.not_mem_interior (hsubInt (hz 0).2) hinside
    · have hba : b ≤ a := le_of_not_gt hab
      by_cases habeq : a = b
      · let d : ℝ := (1 - a + c) / 2
        have hd : d ∈ Set.Ioo (0 : ℝ) 1 := by
          constructor <;> dsimp [d] <;> linarith [ha.1, ha.2, hc.1, hc.2]
        have heqLine : H - x₁ = AffineMap.lineMap (t.points 0) (t.points 1) d := by
          ext k
          simp [H, d, hza, hx₁Line, hx₂Line, habeq,
            AffineMap.lineMap_apply_module]
          ring
        have hIntr : H - x₁ ∈ intrinsicInterior ℝ (triangle_opposite_facet t 2) := by
          rw [heqLine]
          exact triangleOppositeFacet_lineMap_mem_intrinsicInterior hd
        have hne : H - x₁ ≠ x₂ := by
          intro heq
          rw [heqLine, hx₂Line] at heq
          have hp01 : t.points 0 ≠ t.points 1 := t.independent.injective.ne (by decide)
          have hdEq := (AffineMap.lineMap_injective ℝ hp01) heq
          dsimp [d] at hdEq
          linarith [hacge, hb.1, hc.1]
        apply hno2
        exact ⟨H - x₁, x₂, hne, ⟨hIntr, hsubInt hx₁Int⟩, ⟨hx₂Intr, hx₂Int⟩⟩
      · have hbagt : b < a := lt_of_le_of_ne hba (Ne.symm habeq)
        have hinside : H - x₁ ∈ interior T := by
          rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
          exact hminusX₁Interior hbagt
        exact hfree.not_mem_interior (hsubInt hx₁Int) hinside

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean: if both an integral and a
nonintegral vertex occur, then some nonintegral vertex has two intrinsic lattice points on its
opposite edge. -/
lemma triangle_mixedVertices_force_twoPoints
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    (hfrac : ∃ i : Fin 3, t.points i ∉ ℤ^2)
    (hint : ∃ j : Fin 3, t.points j ∈ ℤ^2) :
    ∃ i : Fin 3,
      t.points i ∉ ℤ^2 ∧
        facet_has_two_distinct_integer_points_in_intrinsicInterior
          (triangle_opposite_facet t i) := by
  classical
  by_contra hnone
  have hno : ∀ i : Fin 3, t.points i ∉ ℤ^2 →
      ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
        (triangle_opposite_facet t i) := by
    intro i hi htwo
    exact hnone ⟨i, hi, htwo⟩
  have hnotall : ¬ ∀ i : Fin 3, t.points i ∈ ℤ^2 := by
    intro hall
    rcases hfrac with ⟨i, hi⟩
    exact hi (hall i)
  have hone (e : Fin 3 ≃ Fin 3)
      (h0 : t.points (e.symm 0) ∈ ℤ^2)
      (h1 : t.points (e.symm 1) ∉ ℤ^2)
      (h2 : t.points (e.symm 2) ∉ ℤ^2)
      (hno1 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
        (triangle_opposite_facet t (e.symm 1)))
      (hno2 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
        (triangle_opposite_facet t (e.symm 2))) : False := by
    -- Reindex so the sole integral vertex is vertex `0`, then use the fixed-index parity lemma.
    apply triangle_oneIntegralVertexZero_impossible
      (t := t.reindex e) (hasTriangleVertices_reindex ht e) hT_maximal
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa [triangleOppositeFacet_reindex] using hno1
    · simpa [triangleOppositeFacet_reindex] using hno2
  have htwo (e : Fin 3 ≃ Fin 3)
      (h0 : t.points (e.symm 0) ∈ ℤ^2)
      (h1 : t.points (e.symm 1) ∈ ℤ^2)
      (h2 : t.points (e.symm 2) ∉ ℤ^2)
      (hno2 : ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
        (triangle_opposite_facet t (e.symm 2))) : False := by
    -- Reindex so the two integral vertices are `0` and `1`, then use the edge-midpoint lemma.
    apply triangle_twoIntegralVerticesZeroOne_impossible
      (t := t.reindex e) (hasTriangleVertices_reindex ht e) hT_maximal
    · simpa using h0
    · simpa using h1
    · simpa using h2
    · simpa [triangleOppositeFacet_reindex] using hno2
  rcases hint with ⟨j, hj⟩
  -- There are only three possible positions of the known integral vertex. In each position the
  -- other two integrality tests select one of the two normalized fixed-index contradictions.
  fin_cases j
  · by_cases h1 : t.points 1 ∈ ℤ^2
    · by_cases h2 : t.points 2 ∈ ℤ^2
      · apply hnotall
        intro i
        fin_cases i
        · exact hj
        · exact h1
        · exact h2
      · exact htwo (Equiv.refl (Fin 3)) hj h1 h2 (hno 2 h2)
    · by_cases h2 : t.points 2 ∈ ℤ^2
      · refine htwo (Equiv.swap 1 2) ?_ ?_ ?_ ?_
        · simpa using hj
        · simpa using h2
        · simpa using h1
        · simpa using hno 1 h1
      · exact hone (Equiv.refl (Fin 3)) hj h1 h2 (hno 1 h1) (hno 2 h2)
  · by_cases h0 : t.points 0 ∈ ℤ^2
    · by_cases h2 : t.points 2 ∈ ℤ^2
      · apply hnotall
        intro i
        fin_cases i
        · exact h0
        · exact hj
        · exact h2
      · exact htwo (Equiv.refl (Fin 3)) h0 hj h2 (hno 2 h2)
    · by_cases h2 : t.points 2 ∈ ℤ^2
      · refine htwo (Equiv.swap 0 2) ?_ ?_ ?_ ?_
        · simpa using h2
        · simpa using hj
        · simpa using h0
        · simpa using hno 0 h0
      · refine hone (Equiv.swap 0 1) ?_ ?_ ?_ ?_ ?_
        · simpa using hj
        · simpa using h0
        · simpa using h2
        · simpa using hno 0 h0
        · simpa using hno 2 h2
  · by_cases h0 : t.points 0 ∈ ℤ^2
    · by_cases h1 : t.points 1 ∈ ℤ^2
      · apply hnotall
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact hj
      · refine htwo (Equiv.swap 1 2) ?_ ?_ ?_ ?_
        · simpa using h0
        · simpa using hj
        · simpa using h1
        · simpa using hno 1 h1
    · by_cases h1 : t.points 1 ∈ ℤ^2
      · refine htwo (Equiv.swap 0 2) ?_ ?_ ?_ ?_
        · simpa using hj
        · simpa using h1
        · simpa using h0
        · simpa using hno 0 h0
      · refine hone (Equiv.swap 0 2) ?_ ?_ ?_ ?_ ?_
        · simpa using hj
        · simpa using h1
        · simpa using h0
        · simpa using hno 1 h1
        · simpa using hno 0 h0

/-- Helper for Exercise 6.11: a nonintegral vertex leads either to the type-(b) branch directly
or, after ruling that out, to the type-(c) exhaustion argument. -/
lemma nonintegralVertex_force_caseB_or_caseC
    {T : Set R2} {t : Affine.Triangle ℝ R2}
    (ht : has_triangle_vertices T t)
    (hT_maximal : is_maximal_lattice_free T)
    (hfrac : ∃ i : Fin 3, t.points i ∉ ℤ^2) :
    exercise_6_11_case_b T ∨ exercise_6_11_case_c T := by
  by_cases hcaseb :
      ∃ i : Fin 3,
        t.points i ∉ ℤ^2 ∧
          facet_has_two_distinct_integer_points_in_intrinsicInterior
            (triangle_opposite_facet t i)
  · -- This is exactly case (b) once the opposite edge is recorded as a facet of `T`.
    left
    rcases hcaseb with ⟨i, hi_nonint, hi_two⟩
    exact ⟨t, ht, i, hi_nonint, triangleOppositeFacet_isFacetOf ht i, hi_two⟩
  · -- Once case (b) is excluded, first rule out mixed vertex integrality and then enumerate the
    -- lattice points from the three unique edge witnesses.
    by_cases hint : ∃ j : Fin 3, t.points j ∈ ℤ^2
    · -- Route correction: the mixed-vertex branch should be isolated before the all-nonintegral
      -- counting argument for case (c).
      exfalso
      exact hcaseb (triangle_mixedVertices_force_twoPoints ht hT_maximal hfrac hint)
    · right
      have hall : ∀ i : Fin 3, t.points i ∉ ℤ^2 := by
        intro i
        by_contra hi
        exact hint ⟨i, hi⟩
      have hnoCaseB :
          ∀ i : Fin 3,
            ¬ facet_has_two_distinct_integer_points_in_intrinsicInterior
              (triangle_opposite_facet t i) := by
        intro i hi_two
        exact hcaseb ⟨i, hall i, hi_two⟩
      have hz : ∃ z : Fin 3 → R2,
          ∀ i : Fin 3,
            z i ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) ∧ z i ∈ ℤ^2 :=
        triangleFacetLatticeWitnesses ht hT_maximal
      rcases hz with ⟨z, hz⟩
      have hfull : affineSpan ℝ T = ⊤ :=
        triangleAffineSpan_eq_top_of_has_triangle_vertices ht
      rcases
          (maximal_lattice_free_iff_is_polyhedron_and_facets_meet_integer_lattice hfull).mp
            hT_maximal with
        ⟨hpoly, hfree, _⟩
      have hconv : Convex ℝ T := is_maximal_lattice_free.convex hT_maximal
      -- Lattice-freeness makes every lattice point a nonvertex boundary point; unique edge
      -- membership then identifies it with one of the three chosen facet witnesses.
      have hpoints : T ∩ ℤ^2 = Set.range z := by
        ext x
        constructor
        · rintro ⟨hxT, hxInt⟩
          have hx_not_interior : x ∉ t.interior := by
            intro hx
            have hx' : x ∈ interior T := by
              rw [interior_eq_triangleInterior_of_has_triangle_vertices ht]
              exact hx
            exact hfree.not_mem_interior hxInt hx'
          have hx_not_vertex : ∀ i : Fin 3, x ≠ t.points i := by
            intro i hxi
            apply hall i
            rw [← hxi]
            exact hxInt
          rcases boundaryPoint_liesInUniqueOppositeFacet ht hxT hx_not_interior hx_not_vertex with
            ⟨i, hxi, _⟩
          have hxIntrinsic : x ∈ intrinsicInterior ℝ (triangle_opposite_facet t i) :=
            triangleOppositeFacet_nonvertex_mem_intrinsicInterior hxi hx_not_vertex
          have hxeq : x = z i := by
            by_contra hxne
            apply hnoCaseB i
            exact ⟨x, z i, hxne, ⟨hxIntrinsic, hxInt⟩, hz i⟩
          exact ⟨i, hxeq.symm⟩
        · rintro ⟨i, rfl⟩
          exact ⟨triangleOppositeFacet_subset ht i (intrinsicInterior_subset (hz i).1), (hz i).2⟩
      have hz_injective : Function.Injective z := by
        intro i j hzij
        by_contra hij
        have hfacets_ne :
            triangle_opposite_facet t i ≠ triangle_opposite_facet t j := by
          intro hfacets
          exact hij (triangleOppositeFacet_injective t hfacets)
        have hmidInterior : midpoint ℝ (z i) (z j) ∈ interior T :=
          midpoint_memInterior_of_distinctFacetInteriorPoints hpoly hconv hfull
            (triangleOppositeFacet_isFacetOf ht i) (triangleOppositeFacet_isFacetOf ht j)
            hfacets_ne (hz i).1 (hz j).1
        have hziInterior : z i ∈ interior T := by
          simpa [hzij] using hmidInterior
        exact hfree.not_mem_interior (hz i).2 hziInterior
      -- The range description and injectivity give exactly three points; the facet classifier
      -- transports edgewise uniqueness to every abstract facet.
      constructor
      · rw [hpoints, ← Set.image_univ]
        rw [hz_injective.encard_image, Set.encard_univ]
        simp
      · intro F hF
        rcases triangleFacet_eq_oppositeFacet ht hT_maximal hF with ⟨i, rfl⟩
        refine ⟨z i, hz i, ?_⟩
        intro y hy
        by_contra hyz
        apply hnoCaseB i
        exact ⟨z i, y, Ne.symm hyz, hz i, hy⟩

/-- remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_11.lean
Exercise 6.11. Let `T` be a maximal lattice-free convex set in `ℝ²` which is a triangle.
Then `T` satisfies one of the following three alternatives: it has integral vertices and exactly
one embedded integer point in the relative interior of each facet, or some nonintegral vertex has
an opposite facet with at least two embedded integer points in its relative interior, or `T`
contains exactly three embedded integer points with one in the relative interior of each facet. -/
theorem exercise_6_11_triangle_satisfies_one_of_three_integral_point_configurations
    (T : Set R2)
    (hT_maximal : is_maximal_lattice_free T)
    (hT_triangle : is_triangle T) :
    exercise_6_11_case_a T ∨ exercise_6_11_case_b T ∨ exercise_6_11_case_c T := by
  rcases hT_triangle with ⟨t, ht⟩
  by_cases hverts : ∀ i : Fin 3, t.points i ∈ ℤ^2
  · -- The integral-vertex branch is delegated to the case-(a) helper.
    left
    exact integralVertices_force_caseA ht hT_maximal hverts
  · -- Otherwise some vertex is nonintegral, so the remaining work is the case-(b)/(c) split.
    right
    have hfrac : ∃ i : Fin 3, t.points i ∉ ℤ^2 := by
      by_contra hno
      apply hverts
      intro i
      by_contra hi
      exact hno ⟨i, hi⟩
    exact nonintegralVertex_force_caseB_or_caseC ht hT_maximal hfrac

end Exercise611

#print axioms exercise_6_11_triangle_satisfies_one_of_three_integral_point_configurations
