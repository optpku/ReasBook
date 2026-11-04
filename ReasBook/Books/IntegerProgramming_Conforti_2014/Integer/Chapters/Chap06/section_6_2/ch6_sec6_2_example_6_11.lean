/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_3.ch5_sec5_1_3_definition_5_1_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_3.ch5_sec5_1_3_example_5_11
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free
import Mathlib.Analysis.Convex.Combination

open scoped Matrix

-- This example reuses the Chapter 5 Example 5.11 owners
-- `example_5_11_polyhedron`, `example_5_11_mixed_integer_set`,
-- `example_5_11_integer_indices`, and `mixed_split_closure`, together with the
-- split-rank owner `is_split_rank_of_inequality` and the Chapter 6 owner
-- `is_lattice_free`.

section Example611

/-- The triangle `K = conv{(0, 0), (2, 0), (0, 2)}` from Example 6.11. -/
def example_6_11_triangle : Set (Fin 2 → ℝ) :=
  convexHull ℝ
    (Set.range fun i : Fin 3 ↦
      match i.1 with
      | 0 => ![(0 : ℝ), 0]
      | 1 => ![2, 0]
      | _ => ![0, 2])

/-- `example_6_11_triangle` is exactly the convex hull of the three vertices
`(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
theorem example_6_11_triangle_eq :
    example_6_11_triangle =
      convexHull ℝ
        (Set.range fun i : Fin 3 ↦
          match i.1 with
          | 0 => ![(0 : ℝ), 0]
          | 1 => ![2, 0]
          | _ => ![0, 2]) :=
  rfl

/-- The apex `(1/2, 1/2)` of the corner polyhedron tableau in Example 6.11. -/
noncomputable def example_6_11_corner_apex : Fin 2 → ℝ :=
  ![(1 / 2 : ℝ), 1 / 2]

/-- `example_6_11_corner_apex` is the tableau apex `(1/2, 1/2)`. -/
theorem example_6_11_corner_apex_def :
    example_6_11_corner_apex = ![(1 / 2 : ℝ), 1 / 2] :=
  rfl

/-- The three extreme rays of the corner polyhedron tableau from Example 6.11. -/
noncomputable def example_6_11_corner_rays : Fin 3 → Fin 2 → ℝ :=
  ![![(3 / 4 : ℝ), -(1 / 4 : ℝ)],
    ![-(1 / 4 : ℝ), (3 / 4 : ℝ)],
    ![-(1 / 4 : ℝ), -(1 / 4 : ℝ)]]

/-- `example_6_11_corner_rays` is exactly the displayed family of three tableau rays. -/
theorem example_6_11_corner_rays_def :
    example_6_11_corner_rays =
      ![![(3 / 4 : ℝ), -(1 / 4 : ℝ)],
        ![-(1 / 4 : ℝ), (3 / 4 : ℝ)],
        ![-(1 / 4 : ℝ), -(1 / 4 : ℝ)]] :=
  rfl

/-- The normalized coefficient vector `(1/2, 1/2, 1/2)` of the Example 6.11 intersection cut. -/
noncomputable def example_6_11_intersection_cut_coeffs : Fin 3 → ℝ :=
  ![(1 / 2 : ℝ), 1 / 2, 1 / 2]

/-- `example_6_11_intersection_cut_coeffs` is the coefficient vector `(1/2, 1/2, 1/2)`. -/
theorem example_6_11_intersection_cut_coeffs_def :
    example_6_11_intersection_cut_coeffs = ![(1 / 2 : ℝ), 1 / 2, 1 / 2] :=
  rfl

/-- The computed intersection cut in the slack variables `s₁`, `s₂`, `s₃` from Example 6.11. -/
def example_6_11_intersection_cut : Set (Fin 3 → ℝ) :=
  {s : Fin 3 → ℝ | 1 ≤ (1 / 2 : ℝ) * s 0 + (1 / 2 : ℝ) * s 1 + (1 / 2 : ℝ) * s 2}

/-- Membership in `example_6_11_intersection_cut` is exactly the inequality
`(1/2) s₁ + (1/2) s₂ + (1/2) s₃ ≥ 1`. -/
theorem mem_example_6_11_intersection_cut_iff
    {s : Fin 3 → ℝ} :
    s ∈ example_6_11_intersection_cut ↔
      1 ≤ (1 / 2 : ℝ) * s 0 + (1 / 2 : ℝ) * s 1 + (1 / 2 : ℝ) * s 2 :=
  Iff.rfl

/-- The tableau expression for the continuous basic variable `y` in Example 6.11. -/
noncomputable def example_6_11_tableau_y (s : Fin 3 → ℝ) : ℝ :=
  (1 / 2 : ℝ) - (1 / 4 : ℝ) * s 0 - (1 / 4 : ℝ) * s 1 - (1 / 4 : ℝ) * s 2

/-- `example_6_11_tableau_y` is the affine form
`1/2 - (1/4) s₁ - (1/4) s₂ - (1/4) s₃`. -/
theorem example_6_11_tableau_y_eq
    (s : Fin 3 → ℝ) :
    example_6_11_tableau_y s =
      (1 / 2 : ℝ) - (1 / 4 : ℝ) * s 0 - (1 / 4 : ℝ) * s 1 - (1 / 4 : ℝ) * s 2 :=
  rfl

/-- Helper for Example 6.11: the convex-hull description of `K` agrees with the standard right
triangle inequalities `0 ≤ x 0`, `0 ≤ x 1`, and `x 0 + x 1 ≤ 2`. -/
lemma example_6_11_triangle_eq_standard :
    example_6_11_triangle =
      {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} := by
  let verts : Fin 3 → Fin 2 → ℝ := fun i ↦
    match i.1 with
    | 0 => ![(0 : ℝ), 0]
    | 1 => ![2, 0]
    | _ => ![0, 2]
  ext x
  change x ∈ convexHull ℝ (Set.range verts) ↔
    x ∈ {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)}
  constructor
  · intro hx
    -- Every vertex already satisfies the three defining inequalities, and the standard triangle
    -- is convex, so the whole convex hull stays inside it.
    refine (convexHull_min ?_ ?_) hx
    · intro y hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i <;> simp [verts]
    · intro y hy z hz a b ha hb hab
      rcases hy with ⟨hy0, hy1, hysum⟩
      rcases hz with ⟨hz0, hz1, hzsum⟩
      refine ⟨?_, ?_, ?_⟩
      · have h0 : 0 ≤ a * y 0 + b * z 0 := by
          nlinarith
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          using h0
      · have h1 : 0 ≤ a * y 1 + b * z 1 := by
          nlinarith
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
          using h1
      · have hsum' : a * (y 0 + y 1) + b * (z 0 + z 1) ≤ 2 := by
          nlinarith
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, mul_comm, mul_left_comm,
          mul_assoc, add_assoc, add_left_comm, add_comm] using hsum'
  · intro hx
    let w : Fin 3 → ℝ := ![1 - (x 0 + x 1) / 2, x 0 / 2, x 1 / 2]
    have hw_nonneg : ∀ i ∈ Finset.univ, 0 ≤ w i := by
      intro i hi
      rcases hx with ⟨hx0, hx1, hxsum⟩
      fin_cases i <;> simp [w] <;> linarith
    have hw_sum : ∑ i ∈ Finset.univ, w i = 1 := by
      simp [w, Fin.sum_univ_three]
      ring
    -- The explicit barycentric coordinates reconstruct `x`, so `x` lies in the convex hull of
    -- the three displayed vertices.
    rw [convexHull_eq]
    refine ⟨Fin 3, Finset.univ, w, verts, hw_nonneg, hw_sum, ?_, ?_⟩
    · intro i hi
      exact ⟨i, rfl⟩
    · rw [Finset.centerMass_eq_of_sum_1 (t := Finset.univ) (w := w) (z := verts) hw_sum]
      ext i
      fin_cases i <;> simp [w, verts, Fin.sum_univ_three]

/-- Helper for Example 6.11: a point lies in the interior of `K` exactly when the three standard
triangle inequalities are strict. -/
lemma example_6_11_mem_interior_triangle_iff
    (x : Fin 2 → ℝ) :
    x ∈ interior example_6_11_triangle ↔
      0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < (2 : ℝ) := by
  rw [example_6_11_triangle_eq_standard]
  constructor
  · intro hx
    -- Small perturbations inside an interior neighborhood force each defining inequality to hold
    -- strictly.
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ε, hεpos, hεsubset⟩
    let y0 : Fin 2 → ℝ := ![x 0 - ε / 2, x 1]
    let y1 : Fin 2 → ℝ := ![x 0, x 1 - ε / 2]
    let ys : Fin 2 → ℝ := ![x 0 + ε / 4, x 1 + ε / 4]
    have hy0_ball : y0 ∈ Metric.ball x ε := by
      have hhalf : ε / 2 < ε := by linarith
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i
        · calc
            dist (y0 0) (x 0) = ε / 2 := by
              have hneg : -(ε / 2 : ℝ) < 0 := by linarith
              dsimp [y0]
              rw [Real.dist_eq]
              calc
                |x 0 - ε / 2 - x 0| = |-(ε / 2 : ℝ)| := by ring_nf
                _ = -(-(ε / 2 : ℝ)) := abs_of_neg hneg
                _ = ε / 2 := by ring
            _ < ε := hhalf
        · simpa [y0, Real.dist_eq] using hεpos
      · exact hεpos
    have hy1_ball : y1 ∈ Metric.ball x ε := by
      have hhalf : ε / 2 < ε := by linarith
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i
        · simpa [y1, Real.dist_eq] using hεpos
        · calc
            dist (y1 1) (x 1) = ε / 2 := by
              have hneg : -(ε / 2 : ℝ) < 0 := by linarith
              dsimp [y1]
              rw [Real.dist_eq]
              calc
                |x 1 - ε / 2 - x 1| = |-(ε / 2 : ℝ)| := by ring_nf
                _ = -(-(ε / 2 : ℝ)) := abs_of_neg hneg
                _ = ε / 2 := by ring
            _ < ε := hhalf
      · exact hεpos
    have hys_ball : ys ∈ Metric.ball x ε := by
      have hquarter : ε / 4 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hεpos
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i <;> simpa [ys, Real.dist_eq, hεabs] using hquarter
      · exact hεpos
    have hy0_mem :
        y0 ∈ {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
      hεsubset hy0_ball
    have hy1_mem :
        y1 ∈ {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
      hεsubset hy1_ball
    have hys_mem :
        ys ∈ {x : Fin 2 → ℝ | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
      hεsubset hys_ball
    refine ⟨?_, ?_, ?_⟩
    · have : 0 ≤ x 0 - ε / 2 := hy0_mem.1
      linarith
    · have : 0 ≤ x 1 - ε / 2 := hy1_mem.2.1
      linarith
    · have : x 0 + ε / 4 + (x 1 + ε / 4) ≤ (2 : ℝ) := hys_mem.2.2
      linarith
  · rintro ⟨hx0, hx1, hxsum⟩
    let ε : ℝ := min (x 0 / 2) (min (x 1 / 2) ((2 - x 0 - x 1) / 2))
    have hε0 : ε ≤ x 0 / 2 := by
      exact min_le_left _ _
    have hε1 : ε ≤ x 1 / 2 := by
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hεsum : ε ≤ (2 - x 0 - x 1) / 2 := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hεpos : 0 < ε := by
      -- The minimum of the three positive margins stays positive.
      refine lt_min ?_ ?_
      · linarith
      · refine lt_min ?_ ?_ <;> linarith
    -- A small enough metric ball preserves all three strict inequalities.
    refine mem_interior_iff_mem_nhds.2 <| Metric.mem_nhds_iff.2 ⟨ε, hεpos, ?_⟩
    intro y hy
    rw [Metric.mem_ball, dist_pi_lt_iff] at hy
    · have hy0_abs : |y 0 - x 0| < ε := by
        simpa using hy 0
      have hy1_abs : |y 1 - x 1| < ε := by
        simpa using hy 1
      have hy0_lower : x 0 - ε < y 0 := by
        have h := abs_lt.mp hy0_abs
        linarith
      have hy1_lower : x 1 - ε < y 1 := by
        have h := abs_lt.mp hy1_abs
        linarith
      have hy0_upper : y 0 < x 0 + ε := by
        have h := abs_lt.mp hy0_abs
        linarith
      have hy1_upper : y 1 < x 1 + ε := by
        have h := abs_lt.mp hy1_abs
        linarith
      refine ⟨?_, ?_, ?_⟩ <;> linarith
    · exact hεpos

/-- Helper for Example 6.11: the ENNReal image of `Set.Icc 0 a` has supremum `ENNReal.ofReal a`
whenever `a` is nonnegative. -/
lemma example_6_11_sSup_ofReal_image_Icc
    {a : ℝ}
    (ha : 0 ≤ a) :
    sSup (ENNReal.ofReal '' Set.Icc (0 : ℝ) a) = ENNReal.ofReal a := by
  -- The right endpoint lies in the image and dominates every other point of the image.
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨t, ht, rfl⟩
    exact ENNReal.ofReal_le_ofReal ht.2
  · exact le_sSup ⟨a, ⟨ha, le_rfl⟩, rfl⟩

/-- Helper for Example 6.11: along each tableau ray, the admissible parameters for staying inside
`K` are exactly the interval `Set.Icc 0 2`. -/
lemma example_6_11_rayAdmissibleParameters_eq_Icc
    (j : Fin 3) :
    IntersectionCut.ray_admissible_parameters
        example_6_11_triangle
        example_6_11_corner_apex
        example_6_11_corner_rays
        j = Set.Icc (0 : ℝ) 2 := by
  -- Route correction: rewrite each ray case into the standard triangle inequalities, then solve
  -- the resulting one-dimensional arithmetic directly.
  fin_cases j <;>
    ext t <;>
    rw [IntersectionCut.mem_ray_admissible_parameters_iff, Set.mem_Icc,
      example_6_11_triangle_eq_standard, example_6_11_corner_apex_def, example_6_11_corner_rays_def]
  · constructor
    · intro ht
      rcases ht with ⟨ht0, htmem⟩
      have htmem' :
          0 ≤ (1 / 2 : ℝ) + t * (3 / 4 : ℝ) ∧
            0 ≤ (1 / 2 : ℝ) + t * (-(1 / 4 : ℝ)) ∧
            ((1 / 2 : ℝ) + t * (3 / 4 : ℝ)) + ((1 / 2 : ℝ) + t * (-(1 / 4 : ℝ))) ≤ 2 := by
        simpa using htmem
      refine ⟨ht0, ?_⟩
      linarith [htmem'.2.1]
    · rintro ⟨ht0, ht2⟩
      refine ⟨ht0, ?_⟩
      simp
      constructor
      · linarith
      constructor
      · linarith
      · linarith
  · constructor
    · intro ht
      rcases ht with ⟨ht0, htmem⟩
      have htmem' :
          0 ≤ (1 / 2 : ℝ) + t * (-(1 / 4 : ℝ)) ∧
            0 ≤ (1 / 2 : ℝ) + t * (3 / 4 : ℝ) ∧
            ((1 / 2 : ℝ) + t * (-(1 / 4 : ℝ))) + ((1 / 2 : ℝ) + t * (3 / 4 : ℝ)) ≤ 2 := by
        simpa using htmem
      refine ⟨ht0, ?_⟩
      linarith [htmem'.1]
    · rintro ⟨ht0, ht2⟩
      refine ⟨ht0, ?_⟩
      simp
      constructor
      · linarith
      constructor
      · linarith
      · linarith
  · constructor
    · intro ht
      rcases ht with ⟨ht0, htmem⟩
      have htmem' :
          0 ≤ (1 / 2 : ℝ) + t * (-(1 / 4 : ℝ)) ∧
            0 ≤ (1 / 2 : ℝ) + t * (-(1 / 4 : ℝ)) ∧
            ((1 / 2 : ℝ) + t * (-(1 / 4 : ℝ))) + ((1 / 2 : ℝ) + t * (-(1 / 4 : ℝ))) ≤ 2 := by
        simpa using htmem
      refine ⟨ht0, ?_⟩
      linarith [htmem'.1]
    · rintro ⟨ht0, ht2⟩
      refine ⟨ht0, ?_⟩
      simp
      constructor
      · linarith
      · linarith

/-- Helper for Example 6.11: every ray-intersection parameter of the chosen lattice-free triangle
equals `2`. -/
lemma example_6_11_rayParameter_toReal_eq_two
    (j : Fin 3) :
    (IntersectionCut.ray_intersection_parameter
        example_6_11_triangle
        example_6_11_corner_apex
        example_6_11_corner_rays
        j).toReal = 2 := by
  have hparam :
      IntersectionCut.ray_intersection_parameter
          example_6_11_triangle
          example_6_11_corner_apex
          example_6_11_corner_rays
          j =
        ENNReal.ofReal 2 := by
    rw [IntersectionCut.ray_intersection_parameter_def,
      example_6_11_rayAdmissibleParameters_eq_Icc j]
    simpa using example_6_11_sSup_ofReal_image_Icc (a := 2) (by norm_num)
  -- After the admissible-parameter set is identified, the ENNReal-to-real conversion is
  -- immediate.
  calc
    (IntersectionCut.ray_intersection_parameter
        example_6_11_triangle
        example_6_11_corner_apex
        example_6_11_corner_rays
        j).toReal = (ENNReal.ofReal 2).toReal := by rw [hparam]
    _ = 2 := by simp

/-- Example 6.11 (1). The triangle `K = conv{(0, 0), (2, 0), (0, 2)}` used to define the
intersection cut is lattice-free. -/
theorem example_6_11_triangle_is_lattice_free :
    is_lattice_free example_6_11_triangle := by
  rw [is_lattice_free_iff]
  intro z hz
  rcases (example_6_11_mem_interior_triangle_iff (Int.cast ∘ z)).1 hz with
    ⟨hz0, hz1, hzsum⟩
  -- Two positive integer coordinates force their sum to be at least `2`, contradicting the
  -- strict interior inequality.
  have hz0_real : (0 : ℝ) < (z 0 : ℝ) := by
    simpa using hz0
  have hz1_real : (0 : ℝ) < (z 1 : ℝ) := by
    simpa using hz1
  have hz0_int : 0 < z 0 := by
    exact_mod_cast hz0_real
  have hz1_int : 0 < z 1 := by
    exact_mod_cast hz1_real
  have hsum_ge_int : (2 : ℤ) ≤ z 0 + z 1 := by
    linarith
  have hsum_ge : (2 : ℝ) ≤ ((z 0 : ℝ) + (z 1 : ℝ)) := by
    exact_mod_cast hsum_ge_int
  have hzsum_real : ((z 0 : ℝ) + (z 1 : ℝ)) < 2 := by
    simpa using hzsum
  linarith

/-- Example 6.11 (2). The intersection cut
`(1/2) s₁ + (1/2) s₂ + (1/2) s₃ ≥ 1` is equivalent, via
`y = 1/2 - (1/4) s₁ - (1/4) s₂ - (1/4) s₃`, to the inequality `y ≤ 0`. -/
theorem example_6_11_intersection_cut_iff_tableau_y_nonpositive
    (s : Fin 3 → ℝ) :
    s ∈ example_6_11_intersection_cut ↔ example_6_11_tableau_y s ≤ 0 := by
  rw [mem_example_6_11_intersection_cut_iff, example_6_11_tableau_y_eq]
  constructor <;> intro h <;> linarith

/-- The explicit triangle `K = conv{(0, 0), (2, 0), (0, 2)}` from Example 6.11 yields the
intersection-cut coefficient vector `(1/2, 1/2, 1/2)` for the displayed corner tableau. -/
theorem example_6_11_triangle_intersection_cut_coeff_eq :
    IntersectionCut.intersection_cut_coeff
        example_6_11_triangle
        example_6_11_corner_apex
        example_6_11_corner_rays =
      example_6_11_intersection_cut_coeffs := by
  -- Compute each coefficient as the reciprocal of the corresponding ray-intersection parameter.
  ext j
  fin_cases j <;>
    rw [IntersectionCut.intersection_cut_coeff_eq_inv_ray_intersection_parameter,
      example_6_11_intersection_cut_coeffs_def,
      example_6_11_rayParameter_toReal_eq_two] <;>
    norm_num

/-- ch6_sec6_2_example_6_11

Example 6.11. (Intersection Cuts Can Have an Arbitrarily Large Split Rank)

For the corner polyhedron determined by the tableau at `(1/2, 1/2)`, the explicit lattice-free
triangle `K = conv{(0, 0), (2, 0), (0, 2)}` yields the intersection-cut coefficient vector
`(1/2, 1/2, 1/2)`; together with
`example_6_11_intersection_cut_iff_tableau_y_nonpositive`, this is exactly the inequality
`y ≤ 0` with right-hand side `1`. -/
theorem ch6_sec6_2_example_6_11
    :
    IntersectionCut.intersection_cut_coeff
        example_6_11_triangle
        example_6_11_corner_apex
        example_6_11_corner_rays
      = example_6_11_intersection_cut_coeffs := by
  -- The main statement is exactly the explicit coefficient computation already established above.
  simpa using example_6_11_triangle_intersection_cut_coeff_eq

/-- Companion to Example 6.11: the resulting inequality `y ≤ 0` still has no finite mixed split
rank relative to the integer coordinates `{x₁, x₂}`, as already shown in Example 5.11. -/
theorem example_6_11_y_nonpositive_has_no_finite_mixed_split_rank
    (k : ℕ) :
    ¬ is_split_rank_of_inequality
        (mixed_split_closure example_5_11_integer_indices)
        example_5_11_polyhedron
        example_5_11_mixed_integer_set
        ![(0 : ℝ), 0, 1]
        0
        k := by
  intro hk
  let w : Fin 3 → ℝ := ![(1 / 2 : ℝ), (1 / 2 : ℝ), (1 / 2 : ℝ) / (3 : ℝ) ^ k]
  have hw_mem :
      w ∈
        (mixed_split_closure example_5_11_integer_indices)^[k]
          example_5_11_polyhedron := by
    simpa [w, example_5_11_iterated_split_closure] using
      example_5_11_witness_mem_iterated_split_closure k
  have hvalid : (![(0 : ℝ), 0, 1] : Fin 3 → ℝ) ⬝ᵥ w ≤ 0 :=
    hk.valid_on_iterate hw_mem
  have hdot : (![(0 : ℝ), 0, 1] : Fin 3 → ℝ) ⬝ᵥ w = (1 / 2 : ℝ) / (3 : ℝ) ^ k := by
    simp [w, dotProduct, Fin.sum_univ_three]
  have hpos : 0 < (1 / 2 : ℝ) / (3 : ℝ) ^ k := by
    positivity
  rw [hdot] at hvalid
  linarith

end Example611
