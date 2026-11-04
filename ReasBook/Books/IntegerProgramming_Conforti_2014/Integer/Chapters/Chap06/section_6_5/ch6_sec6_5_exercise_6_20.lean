/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_4.ch6_sec6_3_4_remark_6_36

-- This exercise reuses the Section 6.2 lattice-free owner `is_maximal_lattice_free` together
-- with the Chapter 6 mixed-integer lifting owners from Remark 6.36.

section Exercise620

local notation "R2" => Fin 2 → ℝ
local notation "Z2" => Fin 2 → ℤ

/-- The triangle `K` of Exercise 6.20 with vertices `(-1 / 2, 0)`, `(3 / 2, 0)`, and
`(1 / 2, 2)`. -/
def exercise_6_20_triangle : Set R2 :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(-((1 / 2 : ℝ))), (0 : ℝ)]
      | 1 => ![(3 / 2 : ℝ), (0 : ℝ)]
      | _ => ![(1 / 2 : ℝ), (2 : ℝ)])

/-- The point `f = (1 / 2, 1 / 2)` from Exercise 6.20, written in `ℝ²`. -/
noncomputable def exercise_6_20_f : R2 :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- The translated set `K - f` from Exercise 6.20, written as `{r | r + f ∈ K}`. -/
def exercise_6_20_shifted_triangle : Set R2 :=
  {r : R2 | r + exercise_6_20_f ∈ exercise_6_20_triangle}

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the triangle is the intersection of its three facet halfspaces. -/
lemma exercise_6_20_triangle_eq_halfspaces :
    exercise_6_20_triangle =
      {x : R2 |
        0 ≤ x 1 ∧
          (-2 : ℝ) * x 0 + x 1 ≤ 1 ∧
            (2 : ℝ) * x 0 + x 1 ≤ 3} := by
  apply Set.Subset.antisymm
  · -- Each vertex satisfies the inequalities, and their intersection is convex.
    apply convexHull_min
    · rintro x ⟨i, rfl⟩
      fin_cases i
      · norm_num
      · norm_num
      · norm_num
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨hx0, hx1, hx2⟩
      rcases hy with ⟨hy0, hy1, hy2⟩
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply]
      refine ⟨add_nonneg (mul_nonneg ha hx0) (mul_nonneg hb hy0), ?_, ?_⟩
      · calc
          (-2 : ℝ) * (a * x 0 + b * y 0) + (a * x 1 + b * y 1) =
              a * ((-2 : ℝ) * x 0 + x 1) + b * ((-2 : ℝ) * y 0 + y 1) := by ring
          _ ≤ a * 1 + b * 1 :=
            add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
          _ = 1 := by rw [mul_one, mul_one, hab]
      · calc
          (2 : ℝ) * (a * x 0 + b * y 0) + (a * x 1 + b * y 1) =
              a * ((2 : ℝ) * x 0 + x 1) + b * ((2 : ℝ) * y 0 + y 1) := by ring
          _ ≤ a * 3 + b * 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hx2 ha) (mul_le_mul_of_nonneg_left hy2 hb)
          _ = 3 := by rw [← add_mul, hab, one_mul]
  · intro x hx
    -- The facet inequalities are precisely nonnegativity of the three barycentric weights.
    let w : Fin 3 → ℝ := fun i ↦
      match i.1 with
      | 0 => (3 - 2 * x 0 - x 1) / 4
      | 1 => (2 * x 0 + 1 - x 1) / 4
      | _ => x 1 / 2
    let z : Fin 3 → R2 := fun i ↦
      match i.1 with
      | 0 => ![(-((1 / 2 : ℝ))), (0 : ℝ)]
      | 1 => ![(3 / 2 : ℝ), (0 : ℝ)]
      | _ => ![(1 / 2 : ℝ), (2 : ℝ)]
    refine mem_convexHull_of_exists_fintype w z ?_ ?_ ?_ ?_
    · intro i
      fin_cases i
      · simp [w]
        linarith [hx.1, hx.2.1, hx.2.2]
      · simp [w]
        linarith [hx.1, hx.2.1, hx.2.2]
      · simp [w]
        linarith [hx.1, hx.2.1, hx.2.2]
    · simp [w, Fin.sum_univ_succ]
      ring
    · intro i
      exact Set.mem_range_self i
    · ext i
      fin_cases i
      · simp [w, z, Fin.sum_univ_succ, Pi.smul_apply]
        ring
      · simp [w, z, Fin.sum_univ_succ, Pi.smul_apply]

/-- `exercise_6_20_shifted_triangle` is exactly the translate `K - f`, written by its three
facet inequalities. -/
theorem exercise_6_20_shifted_triangle_eq :
    exercise_6_20_shifted_triangle =
      {r : R2 |
        (-2 : ℝ) * r 1 ≤ 1 ∧
          (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ 1 ∧
            (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ 1} := by
  ext r
  -- Translate the facet description by the fixed point `f = (1/2,1/2)`.
  rw [exercise_6_20_shifted_triangle, exercise_6_20_triangle_eq_halfspaces]
  simp only [Set.mem_setOf_eq, Pi.add_apply]
  dsimp [exercise_6_20_f]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the maximum of the three normalized facet functionals. -/
noncomputable def exercise_6_20_facetMax (r : R2) : ℝ :=
  max
    (max ((-2 : ℝ) * r 1) ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1))
    ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the facet maximum is nonnegative. -/
lemma exercise_6_20_facetMax_nonnegative (r : R2) :
    0 ≤ exercise_6_20_facetMax r := by
  -- Negativity of all three branches would force contradictory signs on the coordinates.
  by_contra h
  have hmax : exercise_6_20_facetMax r < 0 := lt_of_not_ge h
  have h0 : (-2 : ℝ) * r 1 < 0 :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have h1 : (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 < 0 :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have h2 : (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 < 0 :=
    lt_of_le_of_lt (le_max_right _ _) hmax
  linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the facet maximum is subadditive. -/
lemma exercise_6_20_facetMax_add_le (r s : R2) :
    exercise_6_20_facetMax (r + s) ≤
      exercise_6_20_facetMax r + exercise_6_20_facetMax s := by
  have hr0 : (-2 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hr1 : (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hr2 : (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
    le_max_right _ _
  have hs0 : (-2 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hs1 : (-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hs2 : (4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
    le_max_right _ _
  -- Bound each linear branch separately by the sum of the two maxima.
  unfold exercise_6_20_facetMax
  refine max_le (max_le ?_ ?_) ?_
  · calc
      (-2 : ℝ) * (r + s) 1 = (-2 : ℝ) * r 1 + (-2 : ℝ) * s 1 := by
        simp only [Pi.add_apply]
        ring
      _ ≤ exercise_6_20_facetMax r + exercise_6_20_facetMax s := add_le_add hr0 hs0
  · calc
      (-((4 / 3 : ℝ))) * (r + s) 0 + (2 / 3 : ℝ) * (r + s) 1 =
          ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1) +
            ((-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1) := by
        simp only [Pi.add_apply]
        ring
      _ ≤ exercise_6_20_facetMax r + exercise_6_20_facetMax s := add_le_add hr1 hs1
  · calc
      (4 / 3 : ℝ) * (r + s) 0 + (2 / 3 : ℝ) * (r + s) 1 =
          ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1) +
            ((4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1) := by
        simp only [Pi.add_apply]
        ring
      _ ≤ exercise_6_20_facetMax r + exercise_6_20_facetMax s := add_le_add hr2 hs2

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the facet maximum is positively homogeneous. -/
lemma exercise_6_20_facetMax_smul
    (r : R2) (c : ℝ) (hc : 0 < c) :
    exercise_6_20_facetMax (c • r) = c * exercise_6_20_facetMax r := by
  -- Linearity of each branch and monotonicity of multiplication pull `c` through both maxima.
  simp only [exercise_6_20_facetMax, Pi.smul_apply, smul_eq_mul]
  have hfirst :
      max (c * ((-2 : ℝ) * r 1))
          (c * ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1)) =
        c * max ((-2 : ℝ) * r 1)
          ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1) := by
    symm
    exact mul_max_of_nonneg _ _ hc.le
  have hbranch0 : (-2 : ℝ) * (c * r 1) = c * ((-2 : ℝ) * r 1) := by ring
  have hbranch1 :
      (-((4 / 3 : ℝ))) * (c * r 0) + (2 / 3 : ℝ) * (c * r 1) =
        c * ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1) := by ring
  have hbranch2 :
      (4 / 3 : ℝ) * (c * r 0) + (2 / 3 : ℝ) * (c * r 1) =
        c * ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1) := by ring
  rw [hbranch0, hbranch1, hbranch2, hfirst]
  exact (mul_max_of_nonneg _ _ hc.le).symm

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the facet maximum is a sublinear function. -/
lemma exercise_6_20_facetMax_sublinear :
    exercise_6_20_facetMax.Sublinear := by
  -- Package the two structural properties required by the Chapter 6 gauge API.
  exact ⟨exercise_6_20_facetMax_add_le, exercise_6_20_facetMax_smul⟩

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the translated triangle is the unit sublevel set of its facet maximum. -/
lemma exercise_6_20_shifted_triangle_eq_unitSublevel :
    exercise_6_20_shifted_triangle = sublinear_unit_sublevel_set exercise_6_20_facetMax := by
  -- A nested maximum is at most one exactly when all three facet inequalities hold.
  rw [exercise_6_20_shifted_triangle_eq]
  ext r
  simp [sublinear_unit_sublevel_set, exercise_6_20_facetMax, and_assoc]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the interior of the shifted triangle is described by strict facet inequalities. -/
lemma exercise_6_20_mem_interior_shifted_triangle_iff (r : R2) :
    r ∈ interior exercise_6_20_shifted_triangle ↔
      (-2 : ℝ) * r 1 < 1 ∧
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 < 1 ∧
          (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 < 1 := by
  have hconv : Convex ℝ exercise_6_20_shifted_triangle := by
    rw [exercise_6_20_shifted_triangle_eq_unitSublevel]
    exact convex_sublinear_unit_sublevel_set exercise_6_20_facetMax_sublinear
  have hzero : (0 : R2) ∈ interior exercise_6_20_shifted_triangle := by
    rw [exercise_6_20_shifted_triangle_eq_unitSublevel]
    exact zero_mem_interior_sublinear_unit_sublevel_set exercise_6_20_facetMax_sublinear
  -- The gauge criterion turns interior membership into strict bounds on all max branches.
  calc
    r ∈ interior exercise_6_20_shifted_triangle ↔
        gauge exercise_6_20_shifted_triangle r < 1 := by
      exact (gauge_lt_one_iff_mem_interior_of_convex_of_zero_mem_interior hconv hzero).symm
    _ ↔ exercise_6_20_facetMax r < 1 := by
      rw [exercise_6_20_shifted_triangle_eq_unitSublevel]
      rw [gauge_sublinear_unit_sublevel_set_eq exercise_6_20_facetMax_sublinear
        exercise_6_20_facetMax_nonnegative]
    _ ↔ _ := by
      simp [exercise_6_20_facetMax, and_assoc]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the interior of the original triangle is described by strict facet inequalities. -/
lemma exercise_6_20_mem_interior_triangle_iff (x : R2) :
    x ∈ interior exercise_6_20_triangle ↔
      0 < x 1 ∧
        (-2 : ℝ) * x 0 + x 1 < 1 ∧
          (2 : ℝ) * x 0 + x 1 < 3 := by
  have htranslate :
      exercise_6_20_shifted_triangle =
        {r : R2 | exercise_6_20_f + r ∈ exercise_6_20_triangle} := by
    ext r
    simp [exercise_6_20_shifted_triangle, add_comm]
  have hmembership :
      x ∈ interior exercise_6_20_triangle ↔
        x - exercise_6_20_f ∈ interior exercise_6_20_shifted_triangle := by
    rw [htranslate]
    have h := memInterior_setOf_add_mem_iff exercise_6_20_triangle exercise_6_20_f
      (x - exercise_6_20_f)
    simpa [sub_eq_add_neg] using h.symm
  rw [hmembership, exercise_6_20_mem_interior_shifted_triangle_iff]
  dsimp [exercise_6_20_f]
  constructor
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith
  · rintro ⟨h0, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · linarith
    · linarith
    · linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the triangle contains no embedded integer point in its interior. -/
lemma exercise_6_20_triangle_is_lattice_free :
    is_lattice_free exercise_6_20_triangle := by
  rw [is_lattice_free_iff]
  intro z hz
  rcases (exercise_6_20_mem_interior_triangle_iff (Int.cast ∘ z)).1 hz with
    ⟨hz0, hz1, hz2⟩
  have hz0Real : (0 : ℝ) < (z 1 : ℝ) := by simpa [Function.comp_apply] using hz0
  have hz1Real : (-2 : ℝ) * (z 0 : ℝ) + (z 1 : ℝ) < 1 := by
    simpa [Function.comp_apply] using hz1
  have hz2Real : (2 : ℝ) * (z 0 : ℝ) + (z 1 : ℝ) < 3 := by
    simpa [Function.comp_apply] using hz2
  have hz0' : (0 : ℤ) < z 1 := by exact_mod_cast hz0Real
  have hz1' : (-2 : ℤ) * z 0 + z 1 < 1 := by exact_mod_cast hz1Real
  have hz2' : (2 : ℤ) * z 0 + z 1 < 3 := by exact_mod_cast hz2Real
  omega

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the triangle is closed. -/
lemma exercise_6_20_triangle_isClosed :
    IsClosed exercise_6_20_triangle := by
  rw [exercise_6_20_triangle_eq_halfspaces]
  have hcoord1 : Continuous (fun x : R2 ↦ x 1) := continuous_apply 1
  have hleft : Continuous (fun x : R2 ↦ (-2 : ℝ) * x 0 + x 1) :=
    (continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)
  have hright : Continuous (fun x : R2 ↦ (2 : ℝ) * x 0 + x 1) :=
    (continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)
  -- Each defining affine halfspace is closed.
  apply IsClosed.inter
  · exact isClosed_le continuous_const hcoord1
  · apply IsClosed.inter
    · exact isClosed_le hleft continuous_const
    · exact isClosed_le hright continuous_const

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the distinguished point lies in the interior of the triangle. -/
lemma exercise_6_20_f_mem_interior_triangle :
    exercise_6_20_f ∈ interior exercise_6_20_triangle := by
  -- Substitute `f = (1/2,1/2)` in the strict facet description.
  rw [exercise_6_20_mem_interior_triangle_iff]
  norm_num [exercise_6_20_f]

/-- The function `ψ_K` from Exercise 6.20, defined as the gauge of `K - f`. -/
noncomputable def exercise_6_20_psi : R2 → ℝ :=
  gauge exercise_6_20_shifted_triangle

/-- Exercise 6.20 (2). For the translated triangle `K - f`, the function `ψ_K` is the gauge
`max {-2 r₂, -(4 / 3) r₁ + (2 / 3) r₂, (4 / 3) r₁ + (2 / 3) r₂}`. -/
theorem exercise_6_20_psi_apply
    (r : R2) :
    exercise_6_20_psi r =
      max
        (max ((-2 : ℝ) * r 1) ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1))
        ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1) := by
  -- Identify the gauge of the unit sublevel set with its nonnegative sublinear function.
  rw [exercise_6_20_psi, exercise_6_20_shifted_triangle_eq_unitSublevel]
  exact gauge_sublinear_unit_sublevel_set_eq exercise_6_20_facetMax_sublinear
    exercise_6_20_facetMax_nonnegative r

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the gauge of the shifted triangle is valid for the continuous relaxation. -/
lemma exercise_6_20_psi_is_continuousValid :
    IsValidFunctionForContinuousInfiniteRelaxation exercise_6_20_f exercise_6_20_psi := by
  -- Apply the general gauge-validity theorem to the closed lattice-free triangle.
  simpa [exercise_6_20_psi, exercise_6_20_shifted_triangle, add_comm] using
    lemma_6_28_gauge_is_valid_function exercise_6_20_triangle exercise_6_20_f
      exercise_6_20_triangle_isClosed (convex_convexHull ℝ _)
      exercise_6_20_triangle_is_lattice_free exercise_6_20_f_mem_interior_triangle

/-- The four boundary lattice points of `K`, listed as `(0, 0)`, `(1, 0)`, `(0, 1)`, and
`(1, 1)`. -/
def exercise_6_20_boundary_point : Fin 4 → R2 :=
  fun i ↦
    match i.1 with
    | 0 => ![(0 : ℝ), 0]
    | 1 => ![1, 0]
    | 2 => ![0, 1]
    | _ => ![1, 1]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the four real boundary points are casts of integer vectors. -/
def exercise_6_20_boundary_integerPoint : Fin 4 → Z2 :=
  fun i ↦
    match i.1 with
    | 0 => ![0, 0]
    | 1 => ![1, 0]
    | 2 => ![0, 1]
    | _ => ![1, 1]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
casting an integer boundary point gives the corresponding real boundary point. -/
lemma exercise_6_20_cast_boundary_integerPoint (i : Fin 4) :
    (Int.cast ∘ exercise_6_20_boundary_integerPoint i : R2) =
      exercise_6_20_boundary_point i := by
  -- Both sides are the same two-coordinate vector in each of the four cases.
  ext j
  fin_cases i
  · fin_cases j
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]
    · norm_num [exercise_6_20_boundary_integerPoint,
        exercise_6_20_boundary_point, Matrix.vecHead, Matrix.vecTail]

/-- Expanding `exercise_6_20_boundary_point` recovers the four displayed boundary lattice
points. -/
theorem exercise_6_20_boundary_point_apply
    (i : Fin 4) :
    exercise_6_20_boundary_point i =
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![1, 0]
      | 2 => ![0, 1]
      | _ => ![1, 1] :=
  rfl

/-- The spindle in the lifting region attached to the `i`-th boundary lattice point of
`exercise_6_20_boundary_point`, written in the canonical Chapter 6 spindle form. -/
def exercise_6_20_lifting_region_at
    (i : Fin 4) : Set R2 :=
  {r : R2 |
    exercise_6_20_psi r +
        exercise_6_20_psi (exercise_6_20_boundary_point i - exercise_6_20_f - r) =
      1}

/-- Membership in `exercise_6_20_lifting_region_at i` is exactly the standard spindle equality
for the boundary lattice point `exercise_6_20_boundary_point i`. -/
theorem exercise_6_20_mem_lifting_region_at_iff
    {i : Fin 4} {r : R2} :
    r ∈ exercise_6_20_lifting_region_at i ↔
      exercise_6_20_psi r +
        exercise_6_20_psi (exercise_6_20_boundary_point i - exercise_6_20_f - r) =
        1 :=
  Iff.rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the bottom-facet functional is active exactly on its two comparison halfspaces. -/
lemma exercise_6_20_facetMax_eq_bottom_iff (r : R2) :
    exercise_6_20_facetMax r = (-2 : ℝ) * r 1 ↔
      0 ≤ r 0 - 2 * r 1 ∧ r 0 + 2 * r 1 ≤ 0 := by
  constructor
  · intro h
    have hleft :
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ (-2 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        _ = _ := h
    have hright :
        (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ (-2 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r := le_max_right _ _
        _ = _ := h
    constructor
    · linarith
    · linarith
  · rintro ⟨hleft, hright⟩
    -- Both competing facet forms lie below the bottom-facet form.
    have hleft' :
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ (-2 : ℝ) * r 1 := by
      linarith
    have hright' :
        (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ (-2 : ℝ) * r 1 := by
      linarith
    unfold exercise_6_20_facetMax
    rw [max_eq_left hleft', max_eq_left hright']

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the left-facet functional is active exactly on its two comparison halfspaces. -/
lemma exercise_6_20_facetMax_eq_left_iff (r : R2) :
    exercise_6_20_facetMax r =
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ↔
      r 0 - 2 * r 1 ≤ 0 ∧ r 0 ≤ 0 := by
  constructor
  · intro h
    have hbottom : (-2 : ℝ) * r 1 ≤
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        _ = _ := h
    have hright : (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r := le_max_right _ _
        _ = _ := h
    constructor
    · linarith
    · linarith
  · rintro ⟨hbottom, hright⟩
    -- Both competing facet forms lie below the left-facet form.
    have hbottom' : (-2 : ℝ) * r 1 ≤
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 := by
      linarith
    have hright' : (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 := by
      linarith
    unfold exercise_6_20_facetMax
    rw [max_eq_right hbottom', max_eq_left hright']

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the right-facet functional is active exactly on its two comparison halfspaces. -/
lemma exercise_6_20_facetMax_eq_right_iff (r : R2) :
    exercise_6_20_facetMax r =
        (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ↔
      0 ≤ r 0 ∧ 0 ≤ r 0 + 2 * r 1 := by
  constructor
  · intro h
    have hleft :
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤
          (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r :=
          le_trans (le_max_right _ _) (le_max_left _ _)
        _ = _ := h
    have hbottom : (-2 : ℝ) * r 1 ≤
        (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 := by
      calc
        _ ≤ exercise_6_20_facetMax r :=
          le_trans (le_max_left _ _) (le_max_left _ _)
        _ = _ := h
    constructor
    · linarith
    · linarith
  · rintro ⟨hleft, hbottom⟩
    -- The right-facet form dominates both other branches.
    have hleft' :
        (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤
          (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 := by
      linarith
    have hbottom' : (-2 : ℝ) * r 1 ≤
        (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 := by
      linarith
    unfold exercise_6_20_facetMax
    rw [max_eq_right (max_le hbottom' hleft')]

/-- The spindle inequalities for the boundary lattice point `(0, 0)` in Exercise 6.20. -/
def exercise_6_20_lifting_region_at_point00 : Set R2 :=
  {r : R2 |
    0 ≤ r 0 - (2 : ℝ) * r 1 ∧
      r 0 - (2 : ℝ) * r 1 ≤ (1 / 2 : ℝ) ∧
        (-(3 / 2 : ℝ)) ≤ r 0 + (2 : ℝ) * r 1 ∧
          r 0 + (2 : ℝ) * r 1 ≤ 0}

/-- The spindle inequalities for the boundary lattice point `(1, 0)` in Exercise 6.20. -/
def exercise_6_20_lifting_region_at_point10 : Set R2 :=
  {r : R2 |
    0 ≤ r 0 - (2 : ℝ) * r 1 ∧
      r 0 - (2 : ℝ) * r 1 ≤ (3 / 2 : ℝ) ∧
        (-(1 / 2 : ℝ)) ≤ r 0 + (2 : ℝ) * r 1 ∧
          r 0 + (2 : ℝ) * r 1 ≤ 0}

/-- The spindle inequalities for the boundary lattice point `(0, 1)` in Exercise 6.20. -/
def exercise_6_20_lifting_region_at_point01 : Set R2 :=
  {r : R2 |
    (-(3 / 2 : ℝ)) ≤ r 0 - (2 : ℝ) * r 1 ∧
      r 0 - (2 : ℝ) * r 1 ≤ 0 ∧
        (-(1 / 2 : ℝ)) ≤ r 0 ∧
          r 0 ≤ 0}

/-- The spindle inequalities for the boundary lattice point `(1, 1)` in Exercise 6.20. -/
def exercise_6_20_lifting_region_at_point11 : Set R2 :=
  {r : R2 |
    0 ≤ r 0 ∧
      r 0 ≤ (1 / 2 : ℝ) ∧
        0 ≤ r 0 + (2 : ℝ) * r 1 ∧
          r 0 + (2 : ℝ) * r 1 ≤ (3 / 2 : ℝ)}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean

Unfolding `exercise_6_20_lifting_region_at i` recovers the displayed spindle inequalities for
the `i`-th boundary lattice point. -/
theorem exercise_6_20_lifting_region_at_apply
    (i : Fin 4) :
    exercise_6_20_lifting_region_at i =
      match i.1 with
      | 0 => exercise_6_20_lifting_region_at_point00
      | 1 => exercise_6_20_lifting_region_at_point10
      | 2 => exercise_6_20_lifting_region_at_point01
      | _ => exercise_6_20_lifting_region_at_point11 := by
  fin_cases i
  · ext r
    simp only [exercise_6_20_lifting_region_at, exercise_6_20_lifting_region_at_point00,
      Set.mem_setOf_eq]
    let s : R2 := exercise_6_20_boundary_point 0 - exercise_6_20_f - r
    change exercise_6_20_psi r + exercise_6_20_psi s = 1 ↔ _
    rw [exercise_6_20_psi_apply, exercise_6_20_psi_apply]
    change exercise_6_20_facetMax r + exercise_6_20_facetMax s = 1 ↔ _
    have hlinear : (-2 : ℝ) * r 1 + (-2 : ℝ) * s 1 = 1 := by
      simp [s, exercise_6_20_boundary_point, exercise_6_20_f, Matrix.vecHead, Matrix.vecTail]
      ring
    constructor
    · intro hsum
      have hrLower : (-2 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hsLower : (-2 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hrActive : exercise_6_20_facetMax r = (-2 : ℝ) * r 1 := by linarith
      have hsActive : exercise_6_20_facetMax s = (-2 : ℝ) * s 1 := by linarith
      rcases (exercise_6_20_facetMax_eq_bottom_iff r).1 hrActive with ⟨hr0, hr1⟩
      rcases (exercise_6_20_facetMax_eq_bottom_iff s).1 hsActive with ⟨hs0, hs1⟩
      dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f] at hs0 hs1
      refine ⟨hr0, ?_, ?_, hr1⟩
      · linarith
      · linarith
    · rintro ⟨hr0, hr0', hr1', hr1⟩
      have hrActive := (exercise_6_20_facetMax_eq_bottom_iff r).2 ⟨hr0, hr1⟩
      have hsActive : exercise_6_20_facetMax s = (-2 : ℝ) * s 1 := by
        apply (exercise_6_20_facetMax_eq_bottom_iff s).2
        dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f]
        constructor
        · linarith
        · linarith
      rw [hrActive, hsActive, hlinear]
  · ext r
    simp only [exercise_6_20_lifting_region_at, exercise_6_20_lifting_region_at_point10,
      Set.mem_setOf_eq]
    let s : R2 := exercise_6_20_boundary_point 1 - exercise_6_20_f - r
    change exercise_6_20_psi r + exercise_6_20_psi s = 1 ↔ _
    rw [exercise_6_20_psi_apply, exercise_6_20_psi_apply]
    change exercise_6_20_facetMax r + exercise_6_20_facetMax s = 1 ↔ _
    have hlinear : (-2 : ℝ) * r 1 + (-2 : ℝ) * s 1 = 1 := by
      simp [s, exercise_6_20_boundary_point, exercise_6_20_f, Matrix.vecHead, Matrix.vecTail]
      ring
    constructor
    · intro hsum
      have hrLower : (-2 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hsLower : (-2 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      have hrActive : exercise_6_20_facetMax r = (-2 : ℝ) * r 1 := by linarith
      have hsActive : exercise_6_20_facetMax s = (-2 : ℝ) * s 1 := by linarith
      rcases (exercise_6_20_facetMax_eq_bottom_iff r).1 hrActive with ⟨hr0, hr1⟩
      rcases (exercise_6_20_facetMax_eq_bottom_iff s).1 hsActive with ⟨hs0, hs1⟩
      dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f] at hs0 hs1
      refine ⟨hr0, ?_, ?_, hr1⟩
      · linarith
      · linarith
    · rintro ⟨hr0, hr0', hr1', hr1⟩
      have hrActive := (exercise_6_20_facetMax_eq_bottom_iff r).2 ⟨hr0, hr1⟩
      have hsActive : exercise_6_20_facetMax s = (-2 : ℝ) * s 1 := by
        apply (exercise_6_20_facetMax_eq_bottom_iff s).2
        dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f]
        constructor
        · linarith
        · linarith
      rw [hrActive, hsActive, hlinear]
  · ext r
    simp only [exercise_6_20_lifting_region_at, exercise_6_20_lifting_region_at_point01,
      Set.mem_setOf_eq]
    let s : R2 := exercise_6_20_boundary_point 2 - exercise_6_20_f - r
    change exercise_6_20_psi r + exercise_6_20_psi s = 1 ↔ _
    rw [exercise_6_20_psi_apply, exercise_6_20_psi_apply]
    change exercise_6_20_facetMax r + exercise_6_20_facetMax s = 1 ↔ _
    have hlinear :
        ((-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1) +
            ((-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1) = 1 := by
      simp [s, exercise_6_20_boundary_point, exercise_6_20_f, Matrix.vecHead, Matrix.vecTail]
      ring
    constructor
    · intro hsum
      have hrLower :
          (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hsLower :
          (-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      have hrActive : exercise_6_20_facetMax r =
          (-((4 / 3 : ℝ))) * r 0 + (2 / 3 : ℝ) * r 1 := by linarith
      have hsActive : exercise_6_20_facetMax s =
          (-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1 := by linarith
      rcases (exercise_6_20_facetMax_eq_left_iff r).1 hrActive with ⟨hr0, hr1⟩
      rcases (exercise_6_20_facetMax_eq_left_iff s).1 hsActive with ⟨hs0, hs1⟩
      dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f] at hs0 hs1
      refine ⟨?_, hr0, ?_, hr1⟩
      · linarith
      · linarith
    · rintro ⟨hr0', hr0, hr1', hr1⟩
      have hrActive := (exercise_6_20_facetMax_eq_left_iff r).2 ⟨hr0, hr1⟩
      have hsActive : exercise_6_20_facetMax s =
          (-((4 / 3 : ℝ))) * s 0 + (2 / 3 : ℝ) * s 1 := by
        apply (exercise_6_20_facetMax_eq_left_iff s).2
        dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f]
        constructor
        · linarith
        · linarith
      rw [hrActive, hsActive, hlinear]
  · ext r
    simp only [exercise_6_20_lifting_region_at, exercise_6_20_lifting_region_at_point11,
      Set.mem_setOf_eq]
    let s : R2 := exercise_6_20_boundary_point 3 - exercise_6_20_f - r
    change exercise_6_20_psi r + exercise_6_20_psi s = 1 ↔ _
    rw [exercise_6_20_psi_apply, exercise_6_20_psi_apply]
    change exercise_6_20_facetMax r + exercise_6_20_facetMax s = 1 ↔ _
    have hlinear :
        ((4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1) +
            ((4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1) = 1 := by
      simp [s, exercise_6_20_boundary_point, exercise_6_20_f, Matrix.vecHead, Matrix.vecTail]
      ring
    constructor
    · intro hsum
      have hrLower :
          (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 ≤ exercise_6_20_facetMax r :=
        le_max_right _ _
      have hsLower :
          (4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1 ≤ exercise_6_20_facetMax s :=
        le_max_right _ _
      have hrActive : exercise_6_20_facetMax r =
          (4 / 3 : ℝ) * r 0 + (2 / 3 : ℝ) * r 1 := by linarith
      have hsActive : exercise_6_20_facetMax s =
          (4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1 := by linarith
      rcases (exercise_6_20_facetMax_eq_right_iff r).1 hrActive with ⟨hr0, hr1⟩
      rcases (exercise_6_20_facetMax_eq_right_iff s).1 hsActive with ⟨hs0, hs1⟩
      dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f] at hs0 hs1
      refine ⟨hr0, ?_, hr1, ?_⟩
      · linarith
      · linarith
    · rintro ⟨hr0, hr0', hr1, hr1'⟩
      have hrActive := (exercise_6_20_facetMax_eq_right_iff r).2 ⟨hr0, hr1⟩
      have hsActive : exercise_6_20_facetMax s =
          (4 / 3 : ℝ) * s 0 + (2 / 3 : ℝ) * s 1 := by
        apply (exercise_6_20_facetMax_eq_right_iff s).2
        dsimp [s, exercise_6_20_boundary_point, exercise_6_20_f]
        constructor
        · linarith
        · linarith
      rw [hrActive, hsActive, hlinear]

/-- The region on which every minimal lifting of `ψ_K` agrees with `ψ_K`. -/
def exercise_6_20_lifting_region : Set R2 :=
  {r : R2 | ∃ i : Fin 4, r ∈ exercise_6_20_lifting_region_at i}

/-- Membership in `exercise_6_20_lifting_region` means membership in one of the four spindles
attached to the boundary lattice points of `K`. -/
theorem exercise_6_20_mem_lifting_region_iff
    {r : R2} :
    r ∈ exercise_6_20_lifting_region ↔
      ∃ i : Fin 4, r ∈ exercise_6_20_lifting_region_at i :=
  Iff.rfl

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the singleton integer and continuous assignments associated to a touching sum are feasible. -/
lemma exercise_6_20_touchingSingleton_mem_mixedIntegerRelaxation
    (f r : R2) (z : Z2) :
    (Finsupp.single r 1,
        Finsupp.single ((fun i ↦ (z i : ℝ)) - f - r) (1 : NNReal)) ∈
      mixed_integer_relaxation_set f := by
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨z, ?_⟩
  -- The two singleton balances add to the chosen integer vector.
  ext i
  simp [Pi.add_apply, Pi.sub_apply]

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
a minimal lifting agrees with the gauge at every point of a spindle. -/
lemma exercise_6_20_minimalLifting_eq_psi_of_mem_liftingRegionAt
    (π : R2 → ℝ)
    (hπ : IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi)
    {i : Fin 4} {r : R2}
    (hr : r ∈ exercise_6_20_lifting_region_at i) :
    π r = exercise_6_20_psi r := by
  have hπUpper : π r ≤ trivial_lifting exercise_6_20_psi r :=
    minimal_lifting_le_trivial_lifting exercise_6_20_f exercise_6_20_psi π hπ r
  have htrivialUpper : trivial_lifting exercise_6_20_psi r ≤ exercise_6_20_psi r := by
    rw [trivial_lifting_apply]
    refine csInf_le ?_ ?_
    · -- Continuous validity makes every integer translate nonnegative.
      use 0
      rintro _ ⟨w, rfl⟩
      exact continuousValidFunctionNonnegative
        hπ.toIsValidGomoryJohnsonPair.toContinuousValidFunction _
    · refine ⟨0, ?_⟩
      simp
  have honeLower :
      1 ≤ π r + exercise_6_20_psi
        ((fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) -
          exercise_6_20_f - r) := by
    -- The singleton mixed assignment at `r` and the complementary continuous column is feasible.
    simpa using hπ.toIsValidGomoryJohnsonPair.one_le
      (exercise_6_20_touchingSingleton_mem_mixedIntegerRelaxation exercise_6_20_f r
        (exercise_6_20_boundary_integerPoint i))
  have htouch :
      exercise_6_20_psi r +
          exercise_6_20_psi
            ((fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) -
              exercise_6_20_f - r) = 1 := by
    have hcast :
        (fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) =
          exercise_6_20_boundary_point i := by
      simpa [Function.comp_def] using exercise_6_20_cast_boundary_integerPoint i
    rw [hcast]
    exact hr
  linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
crossing the bottom facet admits a positive push-off from `(0,0)` into the triangle interior. -/
lemma exercise_6_20_exists_bottomFacet_pushOff_mem_interior
    (x : R2) (hx : x 1 < 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (![0, 0] + δ • (![0, 0] - x) : R2) ∈ interior exercise_6_20_triangle := by
  let C : ℝ := 2 * |x 0| + |x 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (exercise_6_20_mem_interior_triangle_iff _).2 ?_⟩
  have hx0Upper : x 0 ≤ |x 0| := le_abs_self (x 0)
  have hx0Lower : -x 0 ≤ |x 0| := neg_le_abs (x 0)
  have hx1Upper : x 1 ≤ |x 1| := le_abs_self (x 1)
  have hx1Lower : -x 1 ≤ |x 1| := neg_le_abs (x 1)
  have hleftBound : 2 * x 0 - x 1 ≤ C := by
    dsimp [C]
    linarith
  have hrightBound : -2 * x 0 - x 1 ≤ C := by
    dsimp [C]
    linarith
  have hleftSmall : δ * (2 * x 0 - x 1) < 1 := by
    calc
      δ * (2 * x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hleftBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hrightSmall : δ * (-2 * x 0 - x 1) < 1 := by
    calc
      δ * (-2 * x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hrightBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The crossed facet becomes strict, while the small multiplier preserves the other margins.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
crossing the left facet admits a positive push-off from `(0,1)` into the triangle interior. -/
lemma exercise_6_20_exists_leftFacet_pushOff_mem_interior
    (x : R2) (hx : 1 < (-2 : ℝ) * x 0 + x 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (![0, 1] + δ • (![0, 1] - x) : R2) ∈ interior exercise_6_20_triangle := by
  let C : ℝ := |x 1 - 1| + |1 - 2 * x 0 - x 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (exercise_6_20_mem_interior_triangle_iff _).2 ?_⟩
  have hcoordBound : x 1 - 1 ≤ C := by
    have h := le_abs_self (x 1 - 1)
    have hnonneg := abs_nonneg (1 - 2 * x 0 - x 1)
    dsimp [C]
    linarith
  have hrightBound : 1 - 2 * x 0 - x 1 ≤ C := by
    have h := le_abs_self (1 - 2 * x 0 - x 1)
    have hnonneg := abs_nonneg (x 1 - 1)
    dsimp [C]
    linarith
  have hcoordSmall : δ * (x 1 - 1) < 1 := by
    calc
      δ * (x 1 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hcoordBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hrightSmall : δ * (1 - 2 * x 0 - x 1) < 1 := by
    calc
      δ * (1 - 2 * x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hrightBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The active left inequality is strict by `hx`; the other two retain positive slack.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
crossing the right facet admits a positive push-off from `(1,1)` into the triangle interior. -/
lemma exercise_6_20_exists_rightFacet_pushOff_mem_interior
    (x : R2) (hx : 3 < (2 : ℝ) * x 0 + x 1) :
    ∃ δ : ℝ, 0 < δ ∧
      (![1, 1] + δ • (![1, 1] - x) : R2) ∈ interior exercise_6_20_triangle := by
  let C : ℝ := |x 1 - 1| + |-1 + 2 * x 0 - x 1| + 1
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt zero_lt_one C
  refine ⟨δ, hδ, (exercise_6_20_mem_interior_triangle_iff _).2 ?_⟩
  have hcoordBound : x 1 - 1 ≤ C := by
    have h := le_abs_self (x 1 - 1)
    have hnonneg := abs_nonneg (-1 + 2 * x 0 - x 1)
    dsimp [C]
    linarith
  have hleftBound : -1 + 2 * x 0 - x 1 ≤ C := by
    have h := le_abs_self (-1 + 2 * x 0 - x 1)
    have hnonneg := abs_nonneg (x 1 - 1)
    dsimp [C]
    linarith
  have hcoordSmall : δ * (x 1 - 1) < 1 := by
    calc
      δ * (x 1 - 1) ≤ δ * C := mul_le_mul_of_nonneg_left hcoordBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  have hleftSmall : δ * (-1 + 2 * x 0 - x 1) < 1 := by
    calc
      δ * (-1 + 2 * x 0 - x 1) ≤ δ * C := mul_le_mul_of_nonneg_left hleftBound hδ.le
      _ = C * δ := mul_comm _ _
      _ < 1 := hsmall
  -- The active right inequality is strict by `hx`; the other two retain positive slack.
  norm_num [Matrix.vecHead, Matrix.vecTail, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · nlinarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
a boundary point is interior to a convex enlargement when its push-off is interior. -/
lemma exercise_6_20_boundary_mem_interior_of_pushOff
    {L : Set R2} (hLconv : Convex ℝ L) {x z : R2} (hx : x ∈ L)
    {δ : ℝ} (hδ : 0 < δ)
    (hpush : z + δ • (z - x) ∈ interior L) :
    z ∈ interior L := by
  have hone : 0 < 1 + δ := by linarith
  have hweight0 : 0 < 1 / (1 + δ) := one_div_pos.mpr hone
  have hweight1 : 0 ≤ δ / (1 + δ) := div_nonneg hδ.le hone.le
  have hweights : 1 / (1 + δ) + δ / (1 + δ) = 1 := by
    field_simp [hone.ne']
  rw [eq_convexCombo_pushOff x z hδ]
  exact hLconv.combo_interior_self_mem_interior hpush hx hweight0 hweight1 hweights

/-- Exercise 6.20 (1). The triangle with vertices `(-1 / 2, 0)`, `(3 / 2, 0)`, and `(1 / 2, 2)`
is a maximal lattice-free convex set. -/
theorem exercise_6_20_triangle_is_maximal_lattice_free :
    is_maximal_lattice_free exercise_6_20_triangle := by
  rw [is_maximal_lattice_free_iff]
  refine ⟨convex_convexHull ℝ _, exercise_6_20_triangle_is_lattice_free, ?_⟩
  intro L hKL hLconv hLfree
  apply Set.Subset.antisymm
  · intro x hxL
    by_contra hxK
    rw [exercise_6_20_triangle_eq_halfspaces] at hxK
    by_cases hbottom : 0 ≤ x 1
    · by_cases hleft : (-2 : ℝ) * x 0 + x 1 ≤ 1
      · have hright : 3 < (2 : ℝ) * x 0 + x 1 := by
          by_contra h
          exact hxK ⟨hbottom, hleft, le_of_not_gt h⟩
        obtain ⟨δ, hδ, hy⟩ :=
          exercise_6_20_exists_rightFacet_pushOff_mem_interior x hright
        have hyL :
            (![1, 1] + δ • (![1, 1] - x) : R2) ∈ interior L :=
          interior_mono hKL hy
        have hzL : (![1, 1] : R2) ∈ interior L :=
          exercise_6_20_boundary_mem_interior_of_pushOff hLconv hxL hδ hyL
        have hzNot := (is_lattice_free_iff.mp hLfree) (![1, 1] : Z2)
        have hcast : (Int.cast ∘ (![1, 1] : Z2) : R2) = (![1, 1] : R2) := by
          ext j
          fin_cases j
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        rw [hcast] at hzNot
        exact hzNot hzL
      · have hleft' : 1 < (-2 : ℝ) * x 0 + x 1 := lt_of_not_ge hleft
        obtain ⟨δ, hδ, hy⟩ :=
          exercise_6_20_exists_leftFacet_pushOff_mem_interior x hleft'
        have hyL :
            (![0, 1] + δ • (![0, 1] - x) : R2) ∈ interior L :=
          interior_mono hKL hy
        have hzL : (![0, 1] : R2) ∈ interior L :=
          exercise_6_20_boundary_mem_interior_of_pushOff hLconv hxL hδ hyL
        have hzNot := (is_lattice_free_iff.mp hLfree) (![0, 1] : Z2)
        have hcast : (Int.cast ∘ (![0, 1] : Z2) : R2) = (![0, 1] : R2) := by
          ext j
          fin_cases j
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
          · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        rw [hcast] at hzNot
        exact hzNot hzL
    · have hbottom' : x 1 < 0 := lt_of_not_ge hbottom
      obtain ⟨δ, hδ, hy⟩ :=
        exercise_6_20_exists_bottomFacet_pushOff_mem_interior x hbottom'
      have hyL :
          (![0, 0] + δ • (![0, 0] - x) : R2) ∈ interior L :=
        interior_mono hKL hy
      have hzL : (![0, 0] : R2) ∈ interior L :=
        exercise_6_20_boundary_mem_interior_of_pushOff hLconv hxL hδ hyL
      have hzNot := (is_lattice_free_iff.mp hLfree) (![0, 0] : Z2)
      have hcast : (Int.cast ∘ (![0, 0] : Z2) : R2) = (![0, 0] : R2) := by
        ext j
        fin_cases j
        · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
        · norm_num [Function.comp_def, Matrix.vecHead, Matrix.vecTail]
      rw [hcast] at hzNot
      exact hzNot hzL
  · exact hKL

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the gauge at every translated integer point is at least one. -/
lemma exercise_6_20_one_le_psi_sub_integerPoint (z : Z2) :
    1 ≤ exercise_6_20_psi ((fun i ↦ (z i : ℝ)) - exercise_6_20_f) := by
  have hz : (fun i ↦ (z i : ℝ)) ∈ integerVectors 2 :=
    (mem_integerVectors_iff).2 ⟨z, rfl⟩
  have h := one_le_gauge_sub_of_integerPoint
    (B := exercise_6_20_triangle) (f := exercise_6_20_f)
    (convex_convexHull ℝ _) exercise_6_20_triangle_is_lattice_free
    exercise_6_20_f_mem_interior_triangle hz
  -- The project translate uses `r + f`; commute the sum to match the general theorem.
  simpa [exercise_6_20_psi, exercise_6_20_shifted_triangle, add_comm] using h

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the gauge is subadditive. -/
lemma exercise_6_20_psi_add_le (r s : R2) :
    exercise_6_20_psi (r + s) ≤ exercise_6_20_psi r + exercise_6_20_psi s := by
  -- Rewrite to the facet maximum and use its established subadditivity.
  simpa only [exercise_6_20_psi_apply] using exercise_6_20_facetMax_add_le r s

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
membership in a spindle makes `ψ` minimal along every integer translate. -/
lemma exercise_6_20_psi_le_integerTranslate_of_mem_liftingRegion
    {r : R2} (hr : r ∈ exercise_6_20_lifting_region) (w : Z2) :
    exercise_6_20_psi r ≤ exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) := by
  rcases (exercise_6_20_mem_lifting_region_iff).1 hr with ⟨i, hi⟩
  let s : R2 := fun j ↦ r j + (w j : ℝ)
  let t : R2 := exercise_6_20_boundary_point i - exercise_6_20_f - r
  let z : Z2 := fun j ↦ exercise_6_20_boundary_integerPoint i j + w j
  have hcast :
      (fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) =
        exercise_6_20_boundary_point i := by
    simpa [Function.comp_def] using exercise_6_20_cast_boundary_integerPoint i
  have hsum : s + t = (fun j ↦ (z j : ℝ)) - exercise_6_20_f := by
    ext j
    have hcastj := congrFun hcast j
    simp [s, t, z, Pi.add_apply, Pi.sub_apply]
    rw [hcastj]
    ring
  have hone : 1 ≤ exercise_6_20_psi (s + t) := by
    rw [hsum]
    exact exercise_6_20_one_le_psi_sub_integerPoint z
  have hadd : exercise_6_20_psi (s + t) ≤
      exercise_6_20_psi s + exercise_6_20_psi t :=
    exercise_6_20_psi_add_le s t
  have htouch : exercise_6_20_psi r + exercise_6_20_psi t = 1 := hi
  -- The integer-point lower bound and subadditivity compare the translated value with `ψ r`.
  dsimp only [s] at hadd ⊢
  linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the only integer points with translated gauge at most one are the four listed boundary points. -/
lemma exercise_6_20_integerPoint_eq_boundary_of_psi_le_one
    (z : Z2)
    (hz : exercise_6_20_psi ((fun i ↦ (z i : ℝ)) - exercise_6_20_f) ≤ 1) :
    ∃ i : Fin 4, (fun j ↦ (z j : ℝ)) = exercise_6_20_boundary_point i := by
  rw [exercise_6_20_psi_apply] at hz
  have hbottom :
      (-2 : ℝ) * (((fun i ↦ (z i : ℝ)) - exercise_6_20_f) 1) ≤ 1 :=
    (le_trans (le_max_left _ _) (le_max_left _ _)).trans hz
  have hleft :
      (-((4 / 3 : ℝ))) * (((fun i ↦ (z i : ℝ)) - exercise_6_20_f) 0) +
          (2 / 3 : ℝ) * (((fun i ↦ (z i : ℝ)) - exercise_6_20_f) 1) ≤ 1 :=
    (le_trans (le_max_right _ _) (le_max_left _ _)).trans hz
  have hright :
      (4 / 3 : ℝ) * (((fun i ↦ (z i : ℝ)) - exercise_6_20_f) 0) +
          (2 / 3 : ℝ) * (((fun i ↦ (z i : ℝ)) - exercise_6_20_f) 1) ≤ 1 :=
    (le_max_right _ _).trans hz
  have hz1NonnegReal : (0 : ℝ) ≤ (z 1 : ℝ) := by
    dsimp [exercise_6_20_f] at hbottom
    norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply] at hbottom
    linarith
  have hleftReal : (-2 : ℝ) * (z 0 : ℝ) + (z 1 : ℝ) ≤ 1 := by
    dsimp [exercise_6_20_f] at hleft
    norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply] at hleft
    linarith
  have hrightReal : (2 : ℝ) * (z 0 : ℝ) + (z 1 : ℝ) ≤ 3 := by
    dsimp [exercise_6_20_f] at hright
    norm_num [Matrix.vecHead, Matrix.vecTail, Pi.sub_apply] at hright
    linarith
  have hz1Nonneg : (0 : ℤ) ≤ z 1 := by exact_mod_cast hz1NonnegReal
  have hleftInt : (-2 : ℤ) * z 0 + z 1 ≤ 1 := by exact_mod_cast hleftReal
  have hrightInt : (2 : ℤ) * z 0 + z 1 ≤ 3 := by exact_mod_cast hrightReal
  have hcases :
      (z 0 = 0 ∧ z 1 = 0) ∨ (z 0 = 1 ∧ z 1 = 0) ∨
        (z 0 = 0 ∧ z 1 = 1) ∨ (z 0 = 1 ∧ z 1 = 1) := by
    omega
  rcases hcases with h00 | h10 | h01 | h11
  · refine ⟨0, ?_⟩
    ext j
    fin_cases j
    · simp [h00, exercise_6_20_boundary_point]
    · simp [h00, exercise_6_20_boundary_point]
  · refine ⟨1, ?_⟩
    ext j
    fin_cases j
    · simp [h10, exercise_6_20_boundary_point]
    · simp [h10, exercise_6_20_boundary_point]
  · refine ⟨2, ?_⟩
    ext j
    fin_cases j
    · simp [h01, exercise_6_20_boundary_point]
    · simp [h01, exercise_6_20_boundary_point]
  · refine ⟨3, ?_⟩
    ext j
    fin_cases j
    · simp [h11, exercise_6_20_boundary_point]
    · simp [h11, exercise_6_20_boundary_point]

/-- Integer translates of the lifting region of Exercise 6.20 cover the whole plane. -/
theorem exercise_6_20_lifting_region_covers_plane
    (r : R2) :
    ∃ w : Z2, (fun i : Fin 2 ↦ r i + (w i : ℝ)) ∈ exercise_6_20_lifting_region := by
  let m : ℤ := ⌊r 0⌋
  let n : ℤ := ⌊r 1⌋
  let a : ℝ := r 0 - (m : ℝ)
  let b : ℝ := r 1 - (n : ℝ)
  have ha0 : 0 ≤ a := by
    dsimp [a, m]
    exact sub_nonneg.mpr (Int.floor_le (r 0))
  have ha1 : a < 1 := by
    have h := Int.lt_floor_add_one (r 0)
    change r 0 < (m : ℝ) + 1 at h
    dsimp only [a]
    linarith
  have hb0 : 0 ≤ b := by
    dsimp [b, n]
    exact sub_nonneg.mpr (Int.floor_le (r 1))
  have hb1 : b < 1 := by
    have h := Int.lt_floor_add_one (r 1)
    change r 1 < (n : ℝ) + 1 at h
    dsimp only [b]
    linarith
  -- Place the fractional part in one of the four explicit spindle regions.
  by_cases haHalf : a ≤ (1 / 2 : ℝ)
  · by_cases habThreeHalves : a + 2 * b ≤ (3 / 2 : ℝ)
    · refine ⟨![-m, -n], ?_⟩
      rw [exercise_6_20_mem_lifting_region_iff]
      refine ⟨3, ?_⟩
      rw [exercise_6_20_lifting_region_at_apply]
      simp only [exercise_6_20_lifting_region_at_point11, Set.mem_setOf_eq]
      norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · linarith
    · by_cases habTwo : a + 2 * b ≤ 2
      · refine ⟨![-m, -n - 1], ?_⟩
        rw [exercise_6_20_mem_lifting_region_iff]
        refine ⟨1, ?_⟩
        rw [exercise_6_20_lifting_region_at_apply]
        simp only [exercise_6_20_lifting_region_at_point10, Set.mem_setOf_eq]
        norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
        refine ⟨?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
      · refine ⟨![-m, -n - 1], ?_⟩
        rw [exercise_6_20_mem_lifting_region_iff]
        refine ⟨3, ?_⟩
        rw [exercise_6_20_lifting_region_at_apply]
        simp only [exercise_6_20_lifting_region_at_point11, Set.mem_setOf_eq]
        norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
        refine ⟨?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
  · have haHalf' : (1 / 2 : ℝ) < a := lt_of_not_ge haHalf
    by_cases hbLow : 2 * b ≤ a + (1 / 2 : ℝ)
    · refine ⟨![-m - 1, -n], ?_⟩
      rw [exercise_6_20_mem_lifting_region_iff]
      refine ⟨2, ?_⟩
      rw [exercise_6_20_lifting_region_at_apply]
      simp only [exercise_6_20_lifting_region_at_point01, Set.mem_setOf_eq]
      norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
      refine ⟨?_, ?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
      · linarith
    · have hbLow' : a + (1 / 2 : ℝ) < 2 * b := lt_of_not_ge hbLow
      by_cases habTwo : a + 2 * b ≤ 2
      · refine ⟨![-m, -n - 1], ?_⟩
        rw [exercise_6_20_mem_lifting_region_iff]
        refine ⟨1, ?_⟩
        rw [exercise_6_20_lifting_region_at_apply]
        simp only [exercise_6_20_lifting_region_at_point10, Set.mem_setOf_eq]
        norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
        refine ⟨?_, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
        · linarith
      · have habTwo' : 2 < a + 2 * b := lt_of_not_ge habTwo
        by_cases hbMiddle : 2 * b ≤ a + 1
        · refine ⟨![-m - 1, -n - 1], ?_⟩
          rw [exercise_6_20_mem_lifting_region_iff]
          refine ⟨0, ?_⟩
          rw [exercise_6_20_lifting_region_at_apply]
          simp only [exercise_6_20_lifting_region_at_point00, Set.mem_setOf_eq]
          norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
          refine ⟨?_, ?_, ?_, ?_⟩
          · linarith
          · linarith

          · linarith
          · linarith
        · have hbMiddle' : a + 1 < 2 * b := lt_of_not_ge hbMiddle
          refine ⟨![-m - 1, -n - 1], ?_⟩
          rw [exercise_6_20_mem_lifting_region_iff]
          refine ⟨2, ?_⟩
          rw [exercise_6_20_lifting_region_at_apply]
          simp only [exercise_6_20_lifting_region_at_point01, Set.mem_setOf_eq]
          norm_num [a, b, m, n, Matrix.vecHead, Matrix.vecTail]
          refine ⟨?_, ?_, ?_, ?_⟩
          · linarith
          · linarith
          · linarith
          · linarith

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the lifting region is exactly the set of integer-translate minimizers of `ψ`. -/
lemma exercise_6_20_mem_lifting_region_iff_le_integerTranslates {r : R2} :
    r ∈ exercise_6_20_lifting_region ↔
      ∀ w : Z2, exercise_6_20_psi r ≤
        exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) := by
  constructor
  · intro hr w
    exact exercise_6_20_psi_le_integerTranslate_of_mem_liftingRegion hr w
  · intro hminimal
    let s : R2 := fun j ↦ r j + ((Classical.choose
      (exercise_6_20_lifting_region_covers_plane r)) j : ℝ)
    let w : Z2 := Classical.choose (exercise_6_20_lifting_region_covers_plane r)
    have hsRegion : s ∈ exercise_6_20_lifting_region := by
      simpa [s, w] using Classical.choose_spec (exercise_6_20_lifting_region_covers_plane r)
    have hrLe : exercise_6_20_psi r ≤ exercise_6_20_psi s := by
      simpa [s, w] using hminimal w
    have hsLe : exercise_6_20_psi s ≤ exercise_6_20_psi r := by
      have h := exercise_6_20_psi_le_integerTranslate_of_mem_liftingRegion hsRegion
        (fun j ↦ -w j)
      simpa [s, w] using h
    have heq : exercise_6_20_psi r = exercise_6_20_psi s := le_antisymm hrLe hsLe
    rcases (exercise_6_20_mem_lifting_region_iff).1 hsRegion with ⟨i, hi⟩
    let z : Z2 := fun j ↦ exercise_6_20_boundary_integerPoint i j - w j
    have hcast :
        (fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) =
          exercise_6_20_boundary_point i := by
      simpa [Function.comp_def] using exercise_6_20_cast_boundary_integerPoint i
    have hcomplement :
        (fun j ↦ (z j : ℝ)) - exercise_6_20_f - r =
          exercise_6_20_boundary_point i - exercise_6_20_f - s := by
      ext j
      have hcastj := congrFun hcast j
      simp [z, s, w, Pi.sub_apply]
      rw [hcastj]
      ring
    have htouch :
        exercise_6_20_psi r +
          exercise_6_20_psi ((fun j ↦ (z j : ℝ)) - exercise_6_20_f - r) = 1 := by
      rw [heq, hcomplement]
      exact hi
    have hsum :
        r + ((fun j ↦ (z j : ℝ)) - exercise_6_20_f - r) =
          (fun j ↦ (z j : ℝ)) - exercise_6_20_f := by
      ext j
      simp [Pi.add_apply, Pi.sub_apply]
    have hpsiUpper :
        exercise_6_20_psi ((fun j ↦ (z j : ℝ)) - exercise_6_20_f) ≤ 1 := by
      rw [← hsum]
      exact (exercise_6_20_psi_add_le r _).trans_eq htouch
    obtain ⟨k, hk⟩ := exercise_6_20_integerPoint_eq_boundary_of_psi_le_one z hpsiUpper
    rw [exercise_6_20_mem_lifting_region_iff]
    refine ⟨k, ?_⟩
    change exercise_6_20_psi r +
      exercise_6_20_psi (exercise_6_20_boundary_point k - exercise_6_20_f - r) = 1
    rw [← hk]
    exact htouch

/-- Exercise 6.20 (3). If `π_K` is any minimal lifting of `ψ_K`, then the region
`{r ∈ ℝ² | π_K(r) = ψ_K(r)}` is the union of the four spindles attached to the boundary lattice
points `(0, 0)`, `(1, 0)`, `(0, 1)`, and `(1, 1)` of `K`. -/
theorem exercise_6_20_eq_set_of_minimal_lifting_eq_psi
    (π : R2 → ℝ)
    (hπ : IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi) :
    {r : R2 | π r = exercise_6_20_psi r} = exercise_6_20_lifting_region := by
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hπr
    apply exercise_6_20_mem_lifting_region_iff_le_integerTranslates.mpr
    intro w
    have hπUpper : π r ≤ trivial_lifting exercise_6_20_psi r :=
      minimal_lifting_le_trivial_lifting exercise_6_20_f exercise_6_20_psi π hπ r
    have htrivialUpper :
        trivial_lifting exercise_6_20_psi r ≤
          exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) := by
      rw [trivial_lifting_apply]
      refine csInf_le ?_ ⟨w, rfl⟩
      use 0
      rintro _ ⟨v, rfl⟩
      exact continuousValidFunctionNonnegative
        hπ.toIsValidGomoryJohnsonPair.toContinuousValidFunction _
    rw [← hπr]
    exact hπUpper.trans htrivialUpper
  · intro hr
    rcases (exercise_6_20_mem_lifting_region_iff).1 hr with ⟨i, hi⟩
    -- On each spindle, mixed validity and the universal trivial-lifting bound give equality.
    exact exercise_6_20_minimalLifting_eq_psi_of_mem_liftingRegionAt π hπ hi

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
the singleton mixed assignment remains feasible when its continuous column is shifted by an
integer translate of the integer column. -/
lemma exercise_6_20_integerTranslateTouching_mem_mixedIntegerRelaxation
    (f r : R2) (w z : Z2) :
    (Finsupp.single r 1,
        Finsupp.single
          ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) (1 : NNReal)) ∈
      mixed_integer_relaxation_set f := by
  rw [mem_mixed_integer_relaxation_set_iff]
  refine ⟨fun i ↦ z i - w i, ?_⟩
  -- The integer shift in the continuous column is absorbed into the balance witness.
  ext i
  simp [Pi.add_apply, Pi.sub_apply]
  ring

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_20.lean:
a touching integer translate of `ψ` bounds any valid lifting coefficient from below. -/
lemma exercise_6_20_psi_le_validLifting_of_integerTranslate_touching
    {f : R2} {ρ ψ : R2 → ℝ}
    (hρ : IsValidGomoryJohnsonPair f ρ ψ)
    (r : R2) (w z : Z2)
    (htouch :
      ψ (fun i ↦ r i + (w i : ℝ)) +
          ψ ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) = 1) :
    ψ (fun i ↦ r i + (w i : ℝ)) ≤ ρ r := by
  have hone :
      1 ≤ ρ r +
        ψ ((fun i ↦ (z i : ℝ)) - f - (fun i ↦ r i + (w i : ℝ))) := by
    simpa using hρ.one_le
      (exercise_6_20_integerTranslateTouching_mem_mixedIntegerRelaxation f r w z)
  -- Validity and the touching equality squeeze the translated gauge below `ρ r`.
  linarith

/-- Because the lifting region covers `ℝ²` modulo integer translations, the trivial lifting of
`ψ_K` is a minimal lifting of `ψ_K`. -/
instance exercise_6_20_trivial_lifting_is_minimal_lifting :
    IsMinimalLiftingOf exercise_6_20_f (trivial_lifting exercise_6_20_psi) exercise_6_20_psi :=
  by
    refine
      { toIsValidGomoryJohnsonPair :=
          trivial_lifting_is_lifting exercise_6_20_f exercise_6_20_psi
            exercise_6_20_psi_is_continuousValid
        eq_of_le := ?_ }
    intro ρ hρ hρUpper
    funext r
    obtain ⟨w, hwRegion⟩ := exercise_6_20_lifting_region_covers_plane r
    rcases (exercise_6_20_mem_lifting_region_iff).1 hwRegion with ⟨i, hi⟩
    have hcast :
        (fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) =
          exercise_6_20_boundary_point i := by
      simpa [Function.comp_def] using exercise_6_20_cast_boundary_integerPoint i
    have htouch :
        exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) +
            exercise_6_20_psi
              ((fun j ↦ ((exercise_6_20_boundary_integerPoint i) j : ℝ)) -
                exercise_6_20_f - (fun j ↦ r j + (w j : ℝ))) = 1 := by
      rw [hcast]
      exact hi
    have hpsiLower :
        exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) ≤ ρ r :=
      exercise_6_20_psi_le_validLifting_of_integerTranslate_touching hρ r w
        (exercise_6_20_boundary_integerPoint i) htouch
    have htrivialLower :
        trivial_lifting exercise_6_20_psi r ≤
          exercise_6_20_psi (fun j ↦ r j + (w j : ℝ)) := by
      rw [trivial_lifting_apply]
      refine csInf_le ?_ ⟨w, rfl⟩
      use 0
      rintro _ ⟨v, rfl⟩
      exact continuousValidFunctionNonnegative exercise_6_20_psi_is_continuousValid _
    exact le_antisymm (hρUpper r) (htrivialLower.trans hpsiLower)

/-- Every minimal lifting of `ψ_K` coincides with the trivial lifting of `ψ_K`; equivalently, the
trivial lifting is the unique minimal lifting. -/
theorem exercise_6_20_eq_trivial_lifting_of_minimal_lifting
    {π : R2 → ℝ}
    (hπ : IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi) :
    π = trivial_lifting exercise_6_20_psi := by
  -- Minimality of the trivial lifting turns the universal upper bound into equality.
  exact exercise_6_20_trivial_lifting_is_minimal_lifting.eq_of_le
    hπ.toIsValidGomoryJohnsonPair
    (minimal_lifting_le_trivial_lifting exercise_6_20_f exercise_6_20_psi π hπ)

/-- Exercise 6.20 (4). The function `ψ_K` has a unique minimal lifting. -/
theorem exercise_6_20_existsUnique_minimal_lifting :
    ∃! π : R2 → ℝ, IsMinimalLiftingOf exercise_6_20_f π exercise_6_20_psi := by
  -- The trivial lifting is minimal, and the preceding comparison proves uniqueness.
  refine ExistsUnique.intro (trivial_lifting exercise_6_20_psi)
    exercise_6_20_trivial_lifting_is_minimal_lifting ?_
  intro π hπ
  exact exercise_6_20_eq_trivial_lifting_of_minimal_lifting hπ

end Exercise620
