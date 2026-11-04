/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2

open scoped BigOperators Matrix

section Proposition721

variable {i n : ℕ}

/-- A point `ybar` lies in `convexHull ℝ (Set.range y)` exactly when it admits the primal
local-cut barycentric weights `u`. -/
theorem mem_convexHull_iff_exists_local_cut_primal_weights
    {y : Fin i → Fin n → ℝ}
    {ybar : Fin n → ℝ} :
    ybar ∈ convexHull ℝ (Set.range y) ↔
      ∃ u : Fin i → ℝ,
        (∑ h : Fin i, u h • y h) = ybar ∧
          (∑ h : Fin i, u h) = 1 ∧
          0 ≤ u := by
  rw [mem_convexHull_range_iff_exists_barycentric_weights]
  constructor
  · rintro ⟨u, hu_nonneg, hu_sum, hu_repr⟩
    exact ⟨u, hu_repr.symm, hu_sum, hu_nonneg⟩
  · rintro ⟨u, hu_repr, hu_sum, hu_nonneg⟩
    exact ⟨u, hu_nonneg, hu_sum, hu_repr.symm⟩

/-- If the inequality `a ⬝ᵥ x ≤ b` is valid on the sampled points `y¹, ..., yⁱ`, then it is
valid on their convex hull. -/
theorem is_valid_inequality_convexHull_of_local_cut_sample_bounds
    {y : Fin i → Fin n → ℝ}
    {a : Fin n → ℝ}
    {b : ℝ}
    (hvalid : ∀ h : Fin i, a ⬝ᵥ y h ≤ b) :
    is_valid_inequality (convexHull ℝ (Set.range y)) a b := by
  rw [is_valid_inequality_iff]
  intro x hx
  -- Rewrite a point of the convex hull as a barycentric combination of the sampled points.
  rcases (mem_convexHull_iff_exists_local_cut_primal_weights).mp hx with
    ⟨u, rfl, hu_sum, hu_nonneg⟩
  have hsum_le :
      ∑ h : Fin i, u h * (a ⬝ᵥ y h) ≤ ∑ h : Fin i, u h * b := by
    -- Each sample bound is preserved by multiplication with the nonnegative primal weight.
    refine Finset.sum_le_sum ?_
    intro h hh
    exact mul_le_mul_of_nonneg_left (hvalid h) (hu_nonneg h)
  calc
    a ⬝ᵥ ∑ h : Fin i, u h • y h = ∑ h : Fin i, a ⬝ᵥ (u h • y h) := by
      simpa using (dotProduct_sum a Finset.univ (fun h : Fin i ↦ u h • y h))
    _ = ∑ h : Fin i, u h * (a ⬝ᵥ y h) := by
      simp [dotProduct_smul]
    _ ≤ ∑ h : Fin i, u h * b := hsum_le
    _ = (∑ h : Fin i, u h) * b := by
      rw [Finset.sum_mul]
    _ = b := by
      simp [hu_sum]

/-- Helper for Proposition 7.21: a strict separator of `convexHull ℝ (Set.range y)` induces the
sample-wise dual feasibility inequalities `a ⬝ᵥ y h ≤ b`. -/
lemma localCutSampleBounds_ofSeparatingFunctional
    {y : Fin i → Fin n → ℝ}
    {f : StrongDual ℝ (Fin n → ℝ)}
    {a : Fin n → ℝ}
    {b : ℝ}
    (hsep : ∀ z ∈ convexHull ℝ (Set.range y), f z < b)
    (hrep : ∀ x : Fin n → ℝ, f x = a ⬝ᵥ x) :
    ∀ h : Fin i, a ⬝ᵥ y h ≤ b := by
  intro h
  -- Each sampled point lies in the convex hull, so the separator yields a strict sample bound.
  have hstrict : f (y h) < b := by
    exact hsep (y h) (subset_convexHull ℝ (Set.range y) (Set.mem_range_self h))
  calc
    a ⬝ᵥ y h = f (y h) := by
      rw [hrep]
    _ ≤ b := le_of_lt hstrict

/-- A valid inequality on `convexHull ℝ (Set.range y)` is valid on each sampled point. -/
theorem local_cut_sample_bounds_of_is_valid_inequality_convexHull
    {y : Fin i → Fin n → ℝ}
    {a : Fin n → ℝ}
    {b : ℝ}
    (hvalid : is_valid_inequality (convexHull ℝ (Set.range y)) a b) :
    ∀ h : Fin i, a ⬝ᵥ y h ≤ b := by
  intro h
  exact hvalid (subset_convexHull ℝ (Set.range y) (Set.mem_range_self h))

/-- The dual sample-wise feasibility conditions are equivalent to validity on
`convexHull ℝ (Set.range y)`. -/
theorem local_cut_sample_bounds_iff_is_valid_inequality_convexHull
    {y : Fin i → Fin n → ℝ}
    {a : Fin n → ℝ}
    {b : ℝ} :
    (∀ h : Fin i, a ⬝ᵥ y h ≤ b) ↔
      is_valid_inequality (convexHull ℝ (Set.range y)) a b := by
  constructor
  · exact is_valid_inequality_convexHull_of_local_cut_sample_bounds
  · exact local_cut_sample_bounds_of_is_valid_inequality_convexHull

/-- Positivity of the dual objective `a ⬝ᵥ ybar - b` is the same as strict separation of `ybar`
from the inequality right-hand side `b`. -/
theorem local_cut_positive_objective_iff_rhs_lt_dotProduct
    {ybar : Fin n → ℝ}
    {a : Fin n → ℝ}
    {b : ℝ} :
    0 < a ⬝ᵥ ybar - b ↔ b < a ⬝ᵥ ybar := by
  simp [sub_pos]

/-- A dual-feasible inequality with positive objective value is a strict separating inequality for
`ybar` against `convexHull ℝ (Set.range y)`. -/
theorem local_cut_dual_solution_separates
    {y : Fin i → Fin n → ℝ}
    {ybar : Fin n → ℝ}
    {a : Fin n → ℝ}
    {b : ℝ}
    (hvalid : ∀ h : Fin i, a ⬝ᵥ y h ≤ b)
    (hobj : 0 < a ⬝ᵥ ybar - b) :
    is_valid_inequality (convexHull ℝ (Set.range y)) a b ∧
      b < a ⬝ᵥ ybar := by
  exact
    ⟨is_valid_inequality_convexHull_of_local_cut_sample_bounds hvalid,
      (local_cut_positive_objective_iff_rhs_lt_dotProduct).1 hobj⟩

/-- Proposition 7.21. If `ybar ∉ conv(S_i)`, represented here as
`ybar ∉ convexHull ℝ (Set.range y)` for the sampled points `y¹, ..., yⁱ`, then the dual
local-cut linear program produces coefficients `a, b` with positive objective value
`a ⬝ᵥ ybar - b`. -/
theorem local_cut_dual_solution_exists_of_not_mem_convexHull
    (y : Fin i → Fin n → ℝ)
    (ybar : Fin n → ℝ)
    (hnotmem : ybar ∉ convexHull ℝ (Set.range y)) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      (∀ h : Fin i, a ⬝ᵥ y h ≤ b) ∧
        0 < a ⬝ᵥ ybar - b := by
  let S : Set (Fin n → ℝ) := convexHull ℝ (Set.range y)
  have hconv : Convex ℝ S := by
    -- The finite sample hull is convex by construction.
    simpa [S] using convex_convexHull ℝ (Set.range y)
  have hclosed : IsClosed S := by
    -- A convex hull of finitely many sampled points is closed.
    simpa [S] using (Set.finite_range y).isClosed_convexHull ℝ
  -- Route correction: obtain a separating functional first, then rewrite it as a dot product.
  obtain ⟨f, b, hsep, hybar_sep⟩ :=
    geometric_hahn_banach_closed_point
      (s := S) (x := ybar) hconv hclosed (by simpa [S] using hnotmem)
  obtain ⟨a, hrep⟩ := strongDual_eq_dotProduct_fin f
  refine ⟨a, b, ?_, ?_⟩
  · -- Convert the separating functional into the sample-wise dual feasibility constraints.
    simpa [S] using localCutSampleBounds_ofSeparatingFunctional (y := y) hsep hrep
  · -- The strict separation of `ybar` is exactly positivity of the dual objective.
    have hybar_dot : b < a ⬝ᵥ ybar := by
      simpa [S, hrep ybar] using hybar_sep
    exact (local_cut_positive_objective_iff_rhs_lt_dotProduct).2 hybar_dot

/-- Companion form of Proposition 7.21 in the Chapter 3 valid-inequality owner: if
`ybar ∉ convexHull ℝ (Set.range y)`, then there is a strict separating inequality valid on the
whole convex hull of the sampled points. -/
theorem exists_valid_local_cut_separating_inequality_of_not_mem_convexHull
    (y : Fin i → Fin n → ℝ)
    (ybar : Fin n → ℝ)
    (hnotmem : ybar ∉ convexHull ℝ (Set.range y)) :
    ∃ a : Fin n → ℝ, ∃ b : ℝ,
      is_valid_inequality (convexHull ℝ (Set.range y)) a b ∧
        b < a ⬝ᵥ ybar := by
  rcases local_cut_dual_solution_exists_of_not_mem_convexHull y ybar hnotmem with
    ⟨a, b, hvalid, hobj⟩
  exact ⟨a, b, local_cut_dual_solution_separates hvalid hobj⟩

end Proposition721
