import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_2

open scoped BigOperators

noncomputable section

section Lemma64Comparison

variable {I : Type} {n : ℕ}

/-- Helper for `ch6_sec6_1_lemma_6_4`: the projection from tableau coordinates to the nonbasic
coordinate block. -/
def gomory_corner_nonbasic_projection : (Sum I (Fin n) → ℝ) → Fin n → ℝ :=
  fun x j ↦ x (Sum.inr j)

/-- Helper for `ch6_sec6_1_lemma_6_4`: the ambient tableau point determined by the nonbasic
coefficient vector `μ`. -/
def gomory_corner_nonbasic_point
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (μ : Fin n → ℝ) : Sum I (Fin n) → ℝ :=
  tableauCornerBasePoint bbar + ∑ j : Fin n, μ j • tableauCornerRay abar j

/-- The raw nonnegative coefficient
vectors whose associated tableau points lie in the mixed-integer lattice. -/
def gomory_corner_nonbasic_generators
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ) : Set (Fin n → ℝ) :=
  {μ |
    (∀ j : Fin n, 0 ≤ μ j) ∧
      gomory_corner_nonbasic_point abar bbar μ ∈ tableau_mixed_integer_lattice}

/-- Helper for `ch6_sec6_1_lemma_6_4`: the nonbasic-coordinate realization of `corner(B)`,
recorded directly in the coefficient space `ℝ^N`. -/
def gomory_corner_nonbasic_polyhedron
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ) : Set (Fin n → ℝ) :=
  convexHull ℝ (gomory_corner_nonbasic_generators abar bbar)

/-- Membership in `gomory_corner_nonbasic_polyhedron abar bbar` means membership in the convex
hull of its nonnegative mixed-integer coefficient generators. -/
theorem mem_gomory_corner_nonbasic_polyhedron_iff
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (μ : Fin n → ℝ) :
    μ ∈ gomory_corner_nonbasic_polyhedron abar bbar ↔
      μ ∈ convexHull ℝ (gomory_corner_nonbasic_generators abar bbar) := by
  -- Unfold the coefficient-space owner to expose its defining convex hull.
  rfl

/-- Projection to the nonbasic block
recovers every coefficient vector from its associated tableau point. -/
theorem gomoryCornerNonbasicProjection_nonbasicPoint
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (μ : Fin n → ℝ) :
    gomory_corner_nonbasic_projection (gomory_corner_nonbasic_point abar bbar μ) = μ := by
  -- Evaluate the apex-plus-rays representation on each nonbasic coordinate.
  funext j
  simp only [gomory_corner_nonbasic_projection, gomory_corner_nonbasic_point, Pi.add_apply,
    tableauCornerBasePoint, Sum.elim_inr, zero_add,
    sum_smul_tableauCornerRay_apply_inr]

/-- Rebuilding a feasible tableau point
from its nonbasic coordinates returns the original point. -/
theorem gomoryCornerNonbasicPoint_projection_of_mem
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ)
    (x : Sum I (Fin n) → ℝ)
    (hx : x ∈ rationalTableauCornerRelaxation abar bbar) :
    gomory_corner_nonbasic_point abar bbar (gomory_corner_nonbasic_projection x) = x := by
  -- Put the feasible point in its unique apex-plus-rays normal form.
  rcases
      (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar x).1 hx with
    ⟨μ, hμ, hxμ⟩
  have hxμPoint : x = gomory_corner_nonbasic_point abar bbar μ := hxμ
  rw [hxμPoint, gomoryCornerNonbasicProjection_nonbasicPoint]

/-- Projecting the ambient
mixed-integer tableau generators gives exactly the nonbasic coefficient generators. -/
theorem gomoryCornerNonbasicProjection_image_generators
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ) :
    gomory_corner_nonbasic_projection ''
        (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice) =
      gomory_corner_nonbasic_generators abar bbar := by
  -- Match image witnesses in both directions using the two projection/reconstruction laws.
  ext μ
  constructor
  · rintro ⟨x, ⟨hxP, hxZ⟩, rfl⟩
    constructor
    · exact ((mem_rationalTableauCornerRelaxation_iff abar bbar x).1 hxP).2
    · rw [gomoryCornerNonbasicPoint_projection_of_mem abar bbar x hxP]
      exact hxZ
  · rintro ⟨hμ, hμZ⟩
    refine ⟨gomory_corner_nonbasic_point abar bbar μ, ?_, ?_⟩
    · constructor
      · refine
          (mem_rationalTableauCornerRelaxation_iff_exists_nonneg_rayCombination abar bbar _).2 ?_
        refine ⟨μ, hμ, ?_⟩
        rfl
      · exact hμZ
    · exact gomoryCornerNonbasicProjection_nonbasicPoint abar bbar μ

/-- Comparison theorem for Lemma 6.4.

The coefficient-space owner `gomory_corner_nonbasic_polyhedron abar bbar` agrees with the
projection of the established Section 6.1 ambient owner `gomory_corner_polyhedron abar bbar` to
the nonbasic-coordinate block. -/
theorem gomory_corner_nonbasic_polyhedron_eq_projection_image
    (abar : I → Fin n → ℚ)
    (bbar : I → ℚ) :
    gomory_corner_nonbasic_polyhedron abar bbar =
      gomory_corner_nonbasic_projection '' gomory_corner_polyhedron abar bbar := by
  -- First identify the raw projected generators, then commute the linear projection through the
  -- convex hull defining the ambient corner polyhedron.
  rw [gomory_corner_nonbasic_polyhedron, gomory_corner_polyhedron_eq_convexHull]
  rw [← gomoryCornerNonbasicProjection_image_generators]
  let proj : (Sum I (Fin n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.funLeft ℝ ℝ (Sum.inr : Fin n → Sum I (Fin n))
  simpa only [proj, gomory_corner_nonbasic_projection, LinearMap.funLeft_apply] using
    (LinearMap.image_convexHull proj
      (rationalTableauCornerRelaxation abar bbar ∩ tableau_mixed_integer_lattice)).symm

end Lemma64Comparison
