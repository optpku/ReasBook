/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Gauge
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_lattice_free

open scoped Matrix Pointwise

-- This example reuses the Chapter 6 lattice-free owner `is_lattice_free` from the local API file
-- and keeps mathlib's canonical gauge owner `gauge` as the public surface.

section Example621

local notation "R2" => Fin 2 → ℝ

/-- The triangle `B` from Example 6.21, with vertices `(0, 0)`, `(2, 0)`, and `(0, 2)`. -/
def example_6_21_triangle : Set R2 :=
  {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)}

/-- Helper for Example 6.21: the triangle `B` is the standard right triangle
`{x | 0 ≤ x₁, 0 ≤ x₂, x₁ + x₂ ≤ 2}`. -/
lemma example_6_21_triangle_eq_standard :
    example_6_21_triangle =
      {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} := by
  rfl

/-- `example_6_21_triangle` is exactly the set
`{x | -2 * (x 0 - 1/2) ≤ 1, -2 * (x 1 - 1/2) ≤ 1, (x 0 - 1/2) + (x 1 - 1/2) ≤ 1}`. -/
theorem example_6_21_triangle_eq :
    example_6_21_triangle =
      {x : R2 |
        (-2 : ℝ) * (x 0 - (1 / 2 : ℝ)) ≤ 1 ∧
        (-2 : ℝ) * (x 1 - (1 / 2 : ℝ)) ≤ 1 ∧
        (x 0 - (1 / 2 : ℝ)) + (x 1 - (1 / 2 : ℝ)) ≤ 1} := by
  -- Rewrite the triangle into its standard nonnegative-coordinate description first.
  rw [example_6_21_triangle_eq_standard]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx0, hx1, hxsum⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  · intro hx
    rcases hx with ⟨hx0, hx1, hxsum⟩
    refine ⟨?_, ?_, ?_⟩ <;> linarith

/-- The point `bbar = (1/2, 1/2)` from Example 6.21. -/
noncomputable def example_6_21_bbar : R2 :=
  ![(1 / 2 : ℝ), (1 / 2 : ℝ)]

/-- `example_6_21_bbar` is the point `(1/2, 1/2)` in `ℝ²`. -/
theorem example_6_21_bbar_eq :
    example_6_21_bbar = ![(1 / 2 : ℝ), (1 / 2 : ℝ)] :=
  rfl

/-- The translated set `K = B - bbar` used to define the gauge in Example 6.21. -/
def example_6_21_shifted_triangle : Set R2 :=
  {rho : R2 | rho + example_6_21_bbar ∈ example_6_21_triangle}

/-- `example_6_21_shifted_triangle` is exactly the translated inequality set
`{rho | -2 rho₁ ≤ 1, -2 rho₂ ≤ 1, rho₁ + rho₂ ≤ 1}`. -/
theorem example_6_21_shifted_triangle_eq :
    example_6_21_shifted_triangle =
      {rho : R2 |
        (-2 : ℝ) * rho 0 ≤ 1 ∧
        (-2 : ℝ) * rho 1 ≤ 1 ∧
        rho 0 + rho 1 ≤ 1} := by
  ext rho
  constructor
  · intro hrho
    -- Translating by `bbar` converts the shifted set back to the original triangle inequalities.
    change rho + example_6_21_bbar ∈ example_6_21_triangle at hrho
    rw [example_6_21_triangle_eq, example_6_21_bbar_eq] at hrho
    simpa using hrho
  · intro hrho
    -- The same arithmetic reverses the translation.
    change rho + example_6_21_bbar ∈ example_6_21_triangle
    rw [example_6_21_triangle_eq, example_6_21_bbar_eq]
    simpa using hrho

/-- Helper for Example 6.21: a point lies in the interior of `B` exactly when the three standard
triangle inequalities are strict. -/
lemma example_6_21_mem_interior_triangle_iff
    (x : R2) :
    x ∈ interior example_6_21_triangle ↔
      0 < x 0 ∧ 0 < x 1 ∧ x 0 + x 1 < (2 : ℝ) := by
  rw [example_6_21_triangle_eq_standard]
  constructor
  · intro hx
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ε, hεpos, hεsubset⟩
    let y0 : R2 := ![x 0 - ε / 2, x 1]
    let y1 : R2 := ![x 0, x 1 - ε / 2]
    let ys : R2 := ![x 0 + ε / 4, x 1 + ε / 4]
    have hy0_ball : y0 ∈ Metric.ball x ε := by
      -- A small negative perturbation in the first coordinate stays in the ball.
      have hhalf : ε / 2 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hεpos
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i
        · calc
            dist (y0 0) (x 0) = ε / 2 := by
              have hneg : -ε / 2 < 0 := by linarith
              have hneg' : -(ε / 2 : ℝ) < 0 := by linarith
              dsimp [y0]
              rw [Real.dist_eq]
              calc
                |x 0 - ε / 2 - x 0| = |-(ε / 2 : ℝ)| := by ring_nf
                _ = -(-(ε / 2 : ℝ)) := abs_of_neg hneg'
                _ = ε / 2 := by ring
            _ < ε := hhalf
        · simpa [y0, Real.dist_eq] using hεpos
      · exact hεpos
    have hy1_ball : y1 ∈ Metric.ball x ε := by
      -- A small negative perturbation in the second coordinate stays in the ball.
      have hhalf : ε / 2 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hεpos
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i
        · simpa [y1, Real.dist_eq] using hεpos
        · calc
            dist (y1 1) (x 1) = ε / 2 := by
              have hneg : -ε / 2 < 0 := by linarith
              have hneg' : -(ε / 2 : ℝ) < 0 := by linarith
              dsimp [y1]
              rw [Real.dist_eq]
              calc
                |x 1 - ε / 2 - x 1| = |-(ε / 2 : ℝ)| := by ring_nf
                _ = -(-(ε / 2 : ℝ)) := abs_of_neg hneg'
                _ = ε / 2 := by ring
            _ < ε := hhalf
      · exact hεpos
    have hys_ball : ys ∈ Metric.ball x ε := by
      -- A small positive perturbation of both coordinates still stays inside the ball.
      have hquarter : ε / 4 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hεpos
      rw [Metric.mem_ball, dist_pi_lt_iff]
      · intro i
        fin_cases i <;> simpa [ys, Real.dist_eq, hεabs] using hquarter
      · exact hεpos
    have hy0_mem : y0 ∈ {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
      hεsubset hy0_ball
    have hy1_mem : y1 ∈ {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
      hεsubset hy1_ball
    have hys_mem : ys ∈ {x : R2 | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ (2 : ℝ)} :=
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
      -- The radius is bounded by the three positive margins from the strict inequalities.
      refine lt_min ?_ ?_
      · linarith
      · refine lt_min ?_ ?_ <;> linarith
    refine mem_interior_iff_mem_nhds.2 <| Metric.mem_nhds_iff.2 ⟨ε, hεpos, ?_⟩
    intro y hy
    rw [Metric.mem_ball, dist_pi_lt_iff] at hy
    · have hy0_abs : |y 0 - x 0| < ε := by simpa using hy 0
      have hy1_abs : |y 1 - x 1| < ε := by simpa using hy 1
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
      refine ⟨?_, ?_, ?_⟩
      · linarith
      · linarith
      · linarith
    · exact hεpos

/-- Example 6.21 (1). The triangle `B` from the example is lattice-free. -/
theorem example_6_21_triangle_is_lattice_free :
    is_lattice_free example_6_21_triangle := by
  rw [is_lattice_free_iff]
  intro z hz
  rcases (example_6_21_mem_interior_triangle_iff (Int.cast ∘ z)).1 hz with
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

/-- Example 6.21 (2). The point `bbar = (1/2, 1/2)` lies in the interior of `B`. -/
theorem example_6_21_bbar_mem_interior_triangle :
    example_6_21_bbar ∈ interior example_6_21_triangle := by
  -- All three strict triangle inequalities hold at the midpoint `(1/2, 1/2)`.
  rw [example_6_21_bbar_eq]
  have hstrict :
      0 < (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 0 ∧
        0 < (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 1 ∧
        (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 0 + (![(1 / 2 : ℝ), (1 / 2 : ℝ)] : R2) 1 <
          (2 : ℝ) := by
    norm_num
  exact (example_6_21_mem_interior_triangle_iff ![(1 / 2 : ℝ), (1 / 2 : ℝ)]).2 hstrict

/-- Helper for Example 6.21: the gauge candidate is the maximum of the three facet functionals. -/
def example_6_21_psi (rho : R2) : ℝ :=
  max (max ((-2 : ℝ) * rho 0) ((-2 : ℝ) * rho 1)) (rho 0 + rho 1)

/-- Helper for Example 6.21: the gauge candidate is always nonnegative. -/
lemma example_6_21_psi_nonnegative
    (rho : R2) :
    0 ≤ example_6_21_psi rho := by
  -- If all three branches were negative, the first two would force positive coordinates, which
  -- contradicts negativity of their sum.
  by_contra hneg
  have hmax : example_6_21_psi rho < 0 := lt_of_not_ge hneg
  have h0 : (-2 : ℝ) * rho 0 < 0 := by
    exact lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hmax
  have h1 : (-2 : ℝ) * rho 1 < 0 := by
    exact lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hmax
  have hsum : rho 0 + rho 1 < 0 := by
    exact lt_of_le_of_lt (le_max_right _ _) hmax
  linarith

/-- Helper for Example 6.21: multiplying a maximum by a nonnegative scalar may be pulled out. -/
lemma example_6_21_mul_max_of_nonneg
    {a b c : ℝ}
    (hc : 0 ≤ c) :
    max (c * a) (c * b) = c * max a b := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, max_eq_right]
    exact mul_le_mul_of_nonneg_left hab hc
  · rw [max_eq_left hba, max_eq_left]
    exact mul_le_mul_of_nonneg_left hba hc

/-- Helper for Example 6.21: the facet-max function `ψ` is subadditive. -/
lemma example_6_21_psi_add_le
    (rho sigma : R2) :
    example_6_21_psi (rho + sigma) ≤ example_6_21_psi rho + example_6_21_psi sigma := by
  have hρ0 : (-2 : ℝ) * rho 0 ≤ example_6_21_psi rho := by
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hρ1 : (-2 : ℝ) * rho 1 ≤ example_6_21_psi rho := by
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hρs : rho 0 + rho 1 ≤ example_6_21_psi rho := by
    exact le_max_right _ _
  have hσ0 : (-2 : ℝ) * sigma 0 ≤ example_6_21_psi sigma := by
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hσ1 : (-2 : ℝ) * sigma 1 ≤ example_6_21_psi sigma := by
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hσs : sigma 0 + sigma 1 ≤ example_6_21_psi sigma := by
    exact le_max_right _ _
  -- Each branch of the maximum is bounded separately by the sum of the two branch maxima.
  unfold example_6_21_psi
  refine max_le ?_ ?_
  · refine max_le ?_ ?_
    · calc
        (-2 : ℝ) * (rho + sigma) 0
            = (-2 : ℝ) * (rho 0 + sigma 0) := by
              rfl
        _ = (-2 : ℝ) * rho 0 + (-2 : ℝ) * sigma 0 := by
              ring
        _ ≤ example_6_21_psi rho + example_6_21_psi sigma :=
          add_le_add hρ0 hσ0
    · calc
        (-2 : ℝ) * (rho + sigma) 1
            = (-2 : ℝ) * (rho 1 + sigma 1) := by
              rfl
        _ = (-2 : ℝ) * rho 1 + (-2 : ℝ) * sigma 1 := by
              ring
        _ ≤ example_6_21_psi rho + example_6_21_psi sigma :=
          add_le_add hρ1 hσ1
  · calc
      (rho + sigma) 0 + (rho + sigma) 1
          = (rho 0 + sigma 0) + (rho 1 + sigma 1) := by
              rfl
      _ = (rho 0 + rho 1) + (sigma 0 + sigma 1) := by
              ring
      _ ≤ example_6_21_psi rho + example_6_21_psi sigma :=
        add_le_add hρs hσs

/-- Helper for Example 6.21: the facet-max function `ψ` is positively homogeneous for
nonnegative scalars. -/
lemma example_6_21_psi_smul_nonneg
    (rho : R2)
    {c : ℝ}
    (hc : 0 ≤ c) :
    example_6_21_psi (c • rho) = c * example_6_21_psi rho := by
  have h0 : (-2 : ℝ) * (c • rho) 0 = c * ((-2 : ℝ) * rho 0) := by
    simp [Pi.smul_apply, mul_left_comm]
  have h1 : (-2 : ℝ) * (c • rho) 1 = c * ((-2 : ℝ) * rho 1) := by
    simp [Pi.smul_apply, mul_left_comm]
  have hsum : (c • rho) 0 + (c • rho) 1 = c * (rho 0 + rho 1) := by
    simp [Pi.smul_apply, mul_add]
  -- Pull the nonnegative scalar out of the nested maxima one layer at a time.
  rw [example_6_21_psi, h0, h1, hsum, example_6_21_mul_max_of_nonneg hc,
    example_6_21_mul_max_of_nonneg hc]
  simp [example_6_21_psi]

/-- Helper for Example 6.21: the translated triangle `K = B - bbar` is the unit sublevel set of
the facet-max function `ψ`. -/
lemma example_6_21_shifted_triangle_eq_unit_sublevel_set :
    example_6_21_shifted_triangle = {rho : R2 | example_6_21_psi rho ≤ 1} := by
  -- Expanding the nested maximum turns the unit sublevel condition into the three facet
  -- inequalities defining the shifted triangle.
  rw [example_6_21_shifted_triangle_eq]
  ext rho
  constructor <;> intro h <;> simpa [example_6_21_psi, max_le_iff, and_assoc] using h

/-- Helper for Example 6.21: positive dilates of `K = B - bbar` scale the right-hand sides of its
three facet inequalities. -/
lemma example_6_21_mem_smul_shifted_triangle_iff
    {a : ℝ}
    (ha : 0 < a)
    (rho : R2) :
    rho ∈ a • example_6_21_shifted_triangle ↔
      (-2 : ℝ) * rho 0 ≤ a ∧
      (-2 : ℝ) * rho 1 ≤ a ∧
      rho 0 + rho 1 ≤ a := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne', example_6_21_shifted_triangle_eq]
  constructor
  · intro h
    have h' :
        (-2 : ℝ) * (a⁻¹ * rho 0) ≤ 1 ∧
          (-2 : ℝ) * (a⁻¹ * rho 1) ≤ 1 ∧
          a⁻¹ * rho 0 + a⁻¹ * rho 1 ≤ 1 := by
      simpa [
        Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm,
        add_comm, add_left_comm, add_assoc
      ] using h
    rcases h' with ⟨h0, h1, hsum⟩
    refine ⟨?_, ?_, ?_⟩
    · have hmul := mul_le_mul_of_nonneg_left h0 ha.le
      simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    · have hmul := mul_le_mul_of_nonneg_left h1 ha.le
      simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm] using hmul
    · have hmul := mul_le_mul_of_nonneg_left hsum ha.le
      simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm, mul_add] using hmul
  · intro h
    rcases h with ⟨h0, h1, hsum⟩
    have h0' := mul_le_mul_of_nonneg_left h0 (inv_nonneg.2 ha.le)
    have h1' := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ha.le)
    have hsum' := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 ha.le)
    have h'' :
        (-2 : ℝ) * (a⁻¹ * rho 0) ≤ 1 ∧
          (-2 : ℝ) * (a⁻¹ * rho 1) ≤ 1 ∧
          a⁻¹ * rho 0 + a⁻¹ * rho 1 ≤ 1 := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm] using h0'
      · simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm] using h1'
      · simpa [ha.ne', mul_assoc, mul_left_comm, mul_comm, mul_add] using hsum'
    simpa [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, add_comm, add_left_comm,
      add_assoc] using h''

/-- Helper for Example 6.21: the origin lies in the interior of `K = B - bbar`. -/
lemma example_6_21_zero_mem_interior_shifted_triangle :
    (0 : R2) ∈ interior example_6_21_shifted_triangle := by
  refine mem_interior_iff_mem_nhds.2 ?_
  apply Metric.mem_nhds_iff.2
  refine ⟨(1 / 4 : ℝ), by norm_num, ?_⟩
  intro rho hrho
  rw [Metric.mem_ball, dist_pi_lt_iff] at hrho
  · rw [example_6_21_shifted_triangle_eq]
    refine ⟨?_, ?_, ?_⟩
    · have h0 : |rho 0| < (1 / 4 : ℝ) := by simpa using hrho 0
      linarith [abs_lt.1 h0 |>.1]
    · have h1 : |rho 1| < (1 / 4 : ℝ) := by simpa using hrho 1
      linarith [abs_lt.1 h1 |>.1]
    · have h0 : |rho 0| < (1 / 4 : ℝ) := by simpa using hrho 0
      have h1 : |rho 1| < (1 / 4 : ℝ) := by simpa using hrho 1
      linarith [abs_lt.1 h0 |>.2, abs_lt.1 h1 |>.2]
  · norm_num

/-- Example 6.21 (3). The gauge of `K = B - bbar` is
`psi rho = max {-2 rho_1, -2 rho_2, rho_1 + rho_2}`. -/
theorem example_6_21_gauge_formula
    (rho : R2) :
    gauge example_6_21_shifted_triangle rho =
      max (max ((-2 : ℝ) * rho 0) ((-2 : ℝ) * rho 1)) (rho 0 + rho 1) := by
  have hsublinear : example_6_21_psi.Sublinear := by
    -- The max-of-facets function is sublinear by the two structural lemmas above.
    refine ⟨example_6_21_psi_add_le, ?_⟩
    intro r c hc
    exact example_6_21_psi_smul_nonneg r hc.le
  rw [example_6_21_shifted_triangle_eq_unit_sublevel_set]
  simpa [example_6_21_psi, sublinear_unit_sublevel_set] using
    gauge_sublinear_unit_sublevel_set_eq
      (g := example_6_21_psi) hsublinear example_6_21_psi_nonnegative rho

/-- Helper for Example 6.21: the translated triangle has strict interior description matching its
three facet inequalities. -/
lemma example_6_21_mem_interior_shifted_triangle_iff
    (rho : R2) :
    rho ∈ interior example_6_21_shifted_triangle ↔
      (-2 : ℝ) * rho 0 < 1 ∧
      (-2 : ℝ) * rho 1 < 1 ∧
      rho 0 + rho 1 < 1 := by
  have hsublinear : example_6_21_psi.Sublinear := by
    -- The unit sublevel-set route gives the convexity needed for the gauge/interior criterion.
    refine ⟨example_6_21_psi_add_le, ?_⟩
    intro r c hc
    exact example_6_21_psi_smul_nonneg r hc.le
  have hconv : Convex ℝ example_6_21_shifted_triangle := by
    rw [example_6_21_shifted_triangle_eq_unit_sublevel_set]
    simpa [sublinear_unit_sublevel_set] using
      convex_sublinear_unit_sublevel_set (g := example_6_21_psi) hsublinear
  -- Interior membership is equivalent to strict gauge inequality, then to strict branch bounds.
  calc
    rho ∈ interior example_6_21_shifted_triangle ↔
        gauge example_6_21_shifted_triangle rho < 1 := by
          exact
            (gauge_lt_one_iff_mem_interior_of_convex_of_zero_mem_interior hconv
              example_6_21_zero_mem_interior_shifted_triangle).symm
    _ ↔ example_6_21_psi rho < 1 := by
      rw [example_6_21_gauge_formula]
      simp [example_6_21_psi]
    _ ↔ (-2 : ℝ) * rho 0 < 1 ∧ (-2 : ℝ) * rho 1 < 1 ∧ rho 0 + rho 1 < 1 := by
      simp [example_6_21_psi, and_assoc]

/-- Helper for Example 6.21: embedded integer points do not lie in the interior of the triangle
`B`. -/
lemma example_6_21_integer_point_not_mem_interior
    (z : Fin 2 → ℤ) :
    (Int.cast ∘ z : R2) ∉ interior example_6_21_triangle := by
  -- Lattice-freeness exactly excludes embedded integer points from the interior.
  exact (is_lattice_free_iff.mp example_6_21_triangle_is_lattice_free) z

/-- Example 6.21 (4). For the tableau
`x1 = 1/2 + (1/4) x3 - (3/4) x4 - (1/4) x5 + x6`,
`x2 = 1/2 + (3/4) x3 - (1/4) x4 + (3/4) x5 - (3/4) x6`
with `x1, x2` integral and `x3, x4, x5, x6 >= 0`, the intersection cut defined by `B` is
`x3 + (3/2) x4 + (1/2) x5 + (3/2) x6 >= 1`. -/
theorem example_6_21_intersection_cut_valid
    {x1 x2 x3 x4 x5 x6 : ℝ}
    (hx1 :
      x1 = (1 / 2 : ℝ) + (1 / 4 : ℝ) * x3 - (3 / 4 : ℝ) * x4 - (1 / 4 : ℝ) * x5 + x6)
    (hx2 :
      x2 = (1 / 2 : ℝ) + (3 / 4 : ℝ) * x3 - (1 / 4 : ℝ) * x4 + (3 / 4 : ℝ) * x5 -
        (3 / 4 : ℝ) * x6)
    (hx1_int : ∃ z1 : ℤ, x1 = z1)
    (hx2_int : ∃ z2 : ℤ, x2 = z2)
    (hx3_nonneg : 0 ≤ x3)
    (hx4_nonneg : 0 ≤ x4)
    (hx5_nonneg : 0 ≤ x5)
    (hx6_nonneg : 0 ≤ x6) :
    x3 + (3 / 2 : ℝ) * x4 + (1 / 2 : ℝ) * x5 + (3 / 2 : ℝ) * x6 ≥ 1 := by
  rcases hx1_int with ⟨z1, hz1⟩
  rcases hx2_int with ⟨z2, hz2⟩
  let rho : R2 := ![x1 - (1 / 2 : ℝ), x2 - (1 / 2 : ℝ)]
  let rho3 : R2 := ![(1 / 4 : ℝ), (3 / 4 : ℝ)]
  let rho4 : R2 := ![(-3 / 4 : ℝ), (-1 / 4 : ℝ)]
  let rho5 : R2 := ![(-1 / 4 : ℝ), (3 / 4 : ℝ)]
  let rho6 : R2 := ![(1 : ℝ), (-3 / 4 : ℝ)]
  let r3 : R2 := x3 • rho3
  let r4 : R2 := x4 • rho4
  let r5 : R2 := x5 • rho5
  let r6 : R2 := x6 • rho6
  have hrho_decomp : rho = r3 + r4 + r5 + r6 := by
    -- Subtracting the tableau midpoint exposes the standard ray decomposition.
    ext i
    fin_cases i
    · calc
        rho 0 = x1 - (1 / 2 : ℝ) := by simp [rho]
        _ = (1 / 4 : ℝ) * x3 - (3 / 4 : ℝ) * x4 - (1 / 4 : ℝ) * x5 + x6 := by
          linarith
        _ = (r3 + r4 + r5 + r6) 0 := by
          ring_nf
          simp [r3, r4, r5, r6, rho3, rho4, rho5, rho6, smul_eq_mul, add_assoc]
    · calc
        rho 1 = x2 - (1 / 2 : ℝ) := by simp [rho]
        _ = (3 / 4 : ℝ) * x3 - (1 / 4 : ℝ) * x4 + (3 / 4 : ℝ) * x5 - (3 / 4 : ℝ) * x6 := by
          linarith
        _ = (r3 + r4 + r5 + r6) 1 := by
          ring_nf
          simp [r3, r4, r5, r6, rho3, rho4, rho5, rho6, smul_eq_mul, add_assoc]
  have hrho_decomp' : rho = (r3 + r4) + (r5 + r6) := by
    simpa [add_assoc] using hrho_decomp
  have hpsi3 : example_6_21_psi rho3 = 1 := by
    norm_num [example_6_21_psi, rho3]
  have hpsi4 : example_6_21_psi rho4 = (3 / 2 : ℝ) := by
    norm_num [example_6_21_psi, rho4]
  have hpsi5 : example_6_21_psi rho5 = (1 / 2 : ℝ) := by
    norm_num [example_6_21_psi, rho5]
  have hpsi6 : example_6_21_psi rho6 = (3 / 2 : ℝ) := by
    norm_num [example_6_21_psi, rho6]
  have hrho_not_mem_interior : rho ∉ interior example_6_21_shifted_triangle := by
    intro hrho_int
    have hrho_strict := (example_6_21_mem_interior_shifted_triangle_iff rho).1 hrho_int
    have hpoint_int : ![x1, x2] ∈ interior example_6_21_triangle := by
      -- Shifting back by `bbar` turns the strict shifted inequalities into the strict triangle
      -- inequalities.
      rcases hrho_strict with ⟨h0, h1, hsum⟩
      have hx1_pos : 0 < x1 := by
        have : (-2 : ℝ) * (x1 - (1 / 2 : ℝ)) < 1 := by simpa [rho] using h0
        linarith
      have hx2_pos : 0 < x2 := by
        have : (-2 : ℝ) * (x2 - (1 / 2 : ℝ)) < 1 := by simpa [rho] using h1
        linarith
      have hsum_pos : x1 + x2 < 2 := by
        have : (x1 - (1 / 2 : ℝ)) + (x2 - (1 / 2 : ℝ)) < 1 := by simpa [rho] using hsum
        linarith
      apply (example_6_21_mem_interior_triangle_iff ![x1, x2]).2
      exact ⟨hx1_pos, hx2_pos, hsum_pos⟩
    have hz_not :
        (Int.cast ∘ (![z1, z2] : Fin 2 → ℤ) : R2) ∉ interior example_6_21_triangle :=
      example_6_21_integer_point_not_mem_interior ![z1, z2]
    have hcast_eq : (Int.cast ∘ (![z1, z2] : Fin 2 → ℤ) : R2) = ![x1, x2] := by
      ext i
      fin_cases i <;> simp [hz1, hz2]
    exact hz_not <| by simpa [hcast_eq] using hpoint_int
  have hgauge_ge : 1 ≤ gauge example_6_21_shifted_triangle rho := by
    by_contra hgauge_lt
    have hgauge_lt' : gauge example_6_21_shifted_triangle rho < 1 := lt_of_not_ge hgauge_lt
    have hpsi_lt : example_6_21_psi rho < 1 := by
      rw [example_6_21_gauge_formula rho] at hgauge_lt'
      exact hgauge_lt'
    have hrho_int : rho ∈ interior example_6_21_shifted_triangle := by
      exact (example_6_21_mem_interior_shifted_triangle_iff rho).2 <| by
        simpa [example_6_21_psi, max_lt_iff, and_assoc] using hpsi_lt
    exact hrho_not_mem_interior hrho_int
  have hsubadd :
      example_6_21_psi rho ≤
        example_6_21_psi r3 + example_6_21_psi r4 + example_6_21_psi r5 + example_6_21_psi r6 := by
    have h34 := example_6_21_psi_add_le r3 r4
    have h56 := example_6_21_psi_add_le r5 r6
    have hall := example_6_21_psi_add_le (r3 + r4) (r5 + r6)
    have hall' :
        example_6_21_psi rho ≤
          example_6_21_psi (r3 + r4) + example_6_21_psi (r5 + r6) := by
      calc
        example_6_21_psi rho = example_6_21_psi ((r3 + r4) + (r5 + r6)) := by
          rw [hrho_decomp']
        _ ≤ example_6_21_psi (r3 + r4) + example_6_21_psi (r5 + r6) := hall
    linarith
  have hr3 : example_6_21_psi r3 = x3 * example_6_21_psi rho3 := by
    simpa [r3] using example_6_21_psi_smul_nonneg rho3 hx3_nonneg
  have hr4 : example_6_21_psi r4 = x4 * example_6_21_psi rho4 := by
    simpa [r4] using example_6_21_psi_smul_nonneg rho4 hx4_nonneg
  have hr5 : example_6_21_psi r5 = x5 * example_6_21_psi rho5 := by
    simpa [r5] using example_6_21_psi_smul_nonneg rho5 hx5_nonneg
  have hr6 : example_6_21_psi r6 = x6 * example_6_21_psi rho6 := by
    simpa [r6] using example_6_21_psi_smul_nonneg rho6 hx6_nonneg
  have hgauge_le :
      gauge example_6_21_shifted_triangle rho ≤
        x3 + (3 / 2 : ℝ) * x4 + (1 / 2 : ℝ) * x5 + (3 / 2 : ℝ) * x6 := by
    -- Subadditivity over the ray decomposition bounds the gauge by the weighted sum of the four
    -- ray gauges.
    calc
      gauge example_6_21_shifted_triangle rho = example_6_21_psi rho :=
        example_6_21_gauge_formula rho
      _ ≤ example_6_21_psi r3 + example_6_21_psi r4 + example_6_21_psi r5 + example_6_21_psi r6 :=
        hsubadd
      _ = x3 * example_6_21_psi rho3 + x4 * example_6_21_psi rho4 +
            x5 * example_6_21_psi rho5 + x6 * example_6_21_psi rho6 := by
          rw [hr3, hr4, hr5, hr6]
      _ = x3 + (3 / 2 : ℝ) * x4 + (1 / 2 : ℝ) * x5 + (3 / 2 : ℝ) * x6 := by
          rw [hpsi3, hpsi4, hpsi5, hpsi6]
          ring
  linarith

end Example621
