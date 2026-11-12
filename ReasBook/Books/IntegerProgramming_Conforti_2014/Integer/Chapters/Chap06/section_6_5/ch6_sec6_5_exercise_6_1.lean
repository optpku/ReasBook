/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_6.ch5_sec5_6_exercise_5_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_definition_6_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_example_6_10

open scoped BigOperators Matrix

/-
Domain-style sampling for this refine pass:
* primary domain: one-row Gomory mixed-integer cuts for a tableau row of a corner polyhedron
* core/canonical owner: `gomory_mixed_integer_inequality`
* source-facing owner: `exercise_6_1_row_gomory_mixed_integer_cut`
* bridge/view layer here: the tableau row is extended off the nonbasic support by
  `Finset.piecewise`
-/

noncomputable section

section Exercise61

variable {n p : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: an integral shift of the
right-hand side does not change validity of the associated Gomory mixed-integer inequality. -/
private lemma gomory_mixed_integer_inequality_valid_of_integer_shifted_equation
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (x : Fin n → ℝ)
    (hβ : 0 < Int.fract β)
    (z : ℤ)
    (hx_eq : α ⬝ᵥ x = β - (z : ℝ))
    (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ I, ∃ k : ℤ, x j = (k : ℝ)) :
    x ∈ gomory_mixed_integer_inequality I α β hβ := by
  have hfract : Int.fract (β - (z : ℝ)) = Int.fract β :=
    Int.fract_sub_intCast β z
  have hβ_shift : 0 < Int.fract (β - (z : ℝ)) := by
    rwa [hfract]
  -- Apply the Chapter 5 theorem before transporting its coefficient formula across the shift.
  have hx_shift :=
    gomory_mixed_integer_inequality_valid_of_aggregated_equation I α (β - (z : ℝ)) x
      hβ_shift hx_eq hx_nonneg hx_int
  rw [mem_gomory_mixed_integer_inequality_iff] at hx_shift ⊢
  simpa only [gomory_mixed_integer_inequality_coefficient_eq, hfract] using hx_shift

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: a zero row entry has zero
coefficient in the associated Gomory mixed-integer inequality. -/
private lemma gomory_mixed_integer_inequality_coefficient_eq_zero_of_eq_zero
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (j : Fin n)
    (hα : α j = 0) :
    gomory_mixed_integer_inequality_coefficient I α β hβ j = 0 := by
  -- Both the integer and continuous coefficient cases vanish at a zero row entry.
  rw [gomory_mixed_integer_inequality_coefficient_eq]
  simp [hα]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: dotting a zero-extended row
with a vector is the sum over the row support. -/
private lemma piecewiseZero_dotProduct_eq_sum
    (s : Finset (Fin n))
    (a x : Fin n → ℝ) :
    (s.piecewise a 0) ⬝ᵥ x = ∑ j ∈ s, a j * x j := by
  -- Split the full finite sum according to membership in the support.
  rw [dotProduct]
  calc
    ∑ j : Fin n, s.piecewise a 0 j * x j =
        ∑ j ∈ s, s.piecewise a 0 j * x j := by
      symm
      refine Finset.sum_subset (Finset.subset_univ s) ?_
      intro j _ hj
      simp only [Finset.piecewise, hj, ↓reduceIte, Pi.zero_apply, zero_mul]
    _ = ∑ j ∈ s, a j * x j := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      simp only [Finset.piecewise, hj, ↓reduceIte]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: every canonical Gomory
mixed-integer inequality is a convex halfspace. -/
private lemma gomory_mixed_integer_inequality_convex
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β) :
    Convex ℝ (gomory_mixed_integer_inequality I α β hβ) := by
  let c : Fin n → ℝ :=
    gomory_mixed_integer_inequality_coefficient I α β hβ
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductEquiv ℝ (Fin n)) c
  -- Identify the defining coefficient sum with the canonical dot-product linear form.
  simpa only [gomory_mixed_integer_inequality, f, c, dotProductEquiv_apply_apply,
    dotProduct] using
    convex_halfSpace_ge f.isLinear (1 : ℝ)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: zeroing arbitrary
coordinates preserves integrality on the first `p` coordinates. -/
private lemma piecewiseZero_integralOnPrefix
    (hp : p ≤ n)
    (s : Finset (Fin n))
    (x : Fin n → ℝ)
    (hx : x ∈ mixed_integer_prefix_lattice hp)
    (j : Fin n)
    (hj : j.1 < p) :
    ∃ z : ℤ, s.piecewise x 0 j = (z : ℝ) := by
  by_cases hjs : j ∈ s
  · let k : Fin p := ⟨j.1, hj⟩
    obtain ⟨z, hz⟩ := (mem_mixed_integer_prefix_lattice_iff hp x).mp hx k
    have hk : Fin.castLE hp k = j := by
      apply Fin.ext
      rfl
    -- On the support, identify `j` with its corresponding prefix coordinate.
    refine ⟨z, ?_⟩
    simpa only [Finset.piecewise, hjs, ↓reduceIte, hk] using hz
  · -- Off the support, the zeroed coordinate is the integer zero.
    refine ⟨0, ?_⟩
    simp only [Finset.piecewise, hjs, ↓reduceIte, Pi.zero_apply, Int.cast_zero]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean`: zeroing coordinates
where the aggregated row vanishes leaves its Gomory mixed-integer inequality unchanged. -/
private lemma mem_gomory_mixed_integer_inequality_piecewiseZero_iff
    (I s : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (x : Fin n → ℝ)
    (hα : ∀ j, j ∉ s → α j = 0) :
    s.piecewise x 0 ∈ gomory_mixed_integer_inequality I α β hβ ↔
      x ∈ gomory_mixed_integer_inequality I α β hβ := by
  rw [mem_gomory_mixed_integer_inequality_iff,
    mem_gomory_mixed_integer_inequality_iff]
  have hsum :
      ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I α β hβ j * s.piecewise x 0 j =
        ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    by_cases hjs : j ∈ s
    · simp only [Finset.piecewise, hjs, ↓reduceIte]
    · have hcoefficient :
          gomory_mixed_integer_inequality_coefficient I α β hβ j = 0 :=
        gomory_mixed_integer_inequality_coefficient_eq_zero_of_eq_zero I α β hβ j
          (hα j hjs)
      rw [hcoefficient]
      simp
  -- Both membership conditions are the same scalar inequality after the supported-sum rewrite.
  rw [hsum]

/-- The tableau-row Gomory mixed-integer cut of Exercise 6.1, formed from row `i` by extending
the nonbasic coefficients by zero outside `corner_nonbasic_indices hp B`. -/
def exercise_6_1_row_gomory_mixed_integer_cut
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (i : Fin p)
    (hfrac : 0 < Int.fract (barb i : ℝ)) : Set (Fin n → ℝ) :=
  gomory_mixed_integer_cut p
    ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
    (barb i : ℝ)
    hfrac

/-- The row-cut owner of Exercise 6.1 is exactly the Chapter 5 canonical owner
`gomory_mixed_integer_inequality` specialized to the first `p` integer coordinates and the
zero-extended tableau row. -/
theorem exercise_6_1_row_gomory_mixed_integer_cut_eq_gomory_mixed_integer_inequality
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    (i : Fin p)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    exercise_6_1_row_gomory_mixed_integer_cut hp B barA barb i hfrac =
      gomory_mixed_integer_inequality
        (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
        ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
        (barb i : ℝ)
        hfrac := by
  let row : Fin n → ℝ :=
    (corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0
  let I : Finset (Fin n) := Finset.univ.filter fun j : Fin n ↦ j.1 < p
  have hrow :
      0 < gomory_row_fraction (barb i : ℝ) := hfrac
  ext x
  change
      (1 ≤ ∑ j : Fin n,
          gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j * x j) ↔
        1 ≤ ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j * x j
  have hcoeff :
      ∀ j : Fin n,
        gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j =
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j := by
    intro j
    by_cases hj : j.1 < p
    · simp [gomory_mixed_integer_cut_coefficient, gomory_mixed_integer_inequality_coefficient,
        row, I, hj]
    · by_cases hpos : 0 < row j
      · simp [gomory_mixed_integer_cut_coefficient, gomory_mixed_integer_inequality_coefficient,
          row, I, hj, le_of_lt hpos]
      · by_cases hneg : row j < 0
        · simp [gomory_mixed_integer_cut_coefficient,
            gomory_mixed_integer_inequality_coefficient, row, I, hj, not_le.mpr hneg]
        · have hzero : row j = 0 := by linarith
          simp [gomory_mixed_integer_cut_coefficient,
            gomory_mixed_integer_inequality_coefficient, row, I, hj, hzero]
  have hsum :
      ∑ j : Fin n, gomory_mixed_integer_cut_coefficient p row (barb i : ℝ) hrow j * x j =
        ∑ j : Fin n,
          gomory_mixed_integer_inequality_coefficient I row (barb i : ℝ) hfrac j * x j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hcoeff j]
  simp [hsum]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_1.lean

Exercise 6.1. If `i ∈ B` indexes a tableau row of (6.2) with fractional right-hand side,
then the tableau-row Gomory mixed-integer cut generated from that row is valid for the corner
polyhedron `corner_polyhedron hp B barA barb`. -/
theorem exercise_6_1_row_gomory_mixed_integer_cut_valid_for_corner
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    {i : Fin p}
    (hi : i ∈ B)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    corner_polyhedron hp B barA barb ⊆
      exercise_6_1_row_gomory_mixed_integer_cut hp B barA barb i hfrac := by
  rw [corner_polyhedron_eq_convexHull,
    exercise_6_1_row_gomory_mixed_integer_cut_eq_gomory_mixed_integer_inequality]
  refine convexHull_min ?_ (gomory_mixed_integer_inequality_convex _ _ _ hfrac)
  intro x hx
  rw [mem_gomory_corner_relaxation_iff] at hx
  rcases hx with ⟨hx_equations, hx_integral, hx_nonnegative⟩
  let N : Finset (Fin n) := corner_nonbasic_indices hp B
  let I : Finset (Fin n) := Finset.univ.filter fun j : Fin n ↦ j.1 < p
  let row : Fin n → ℝ := N.piecewise (fun j ↦ (barA i j : ℝ)) 0
  let xN : Fin n → ℝ := N.piecewise x 0
  obtain ⟨z, hz⟩ := (mem_mixed_integer_prefix_lattice_iff hp x).mp hx_integral i
  have hxN_equation : row ⬝ᵥ xN = (barb i : ℝ) - (z : ℝ) := by
    have hsupported :
        row ⬝ᵥ xN = ∑ j ∈ N, (barA i j : ℝ) * xN j := by
      simpa only [row] using
        piecewiseZero_dotProduct_eq_sum N (fun j ↦ (barA i j : ℝ)) xN
    have hprojected_sum :
        ∑ j ∈ N, (barA i j : ℝ) * xN j =
          ∑ j ∈ N, (barA i j : ℝ) * x j := by
      refine Finset.sum_congr rfl fun j hj ↦ ?_
      simp only [xN, Finset.piecewise, hj, ↓reduceIte]
    have htableau := hx_equations i hi
    have htableau' :
        x (Fin.castLE hp i) =
          (barb i : ℝ) - ∑ j ∈ N, (barA i j : ℝ) * x j := by
      simpa only [N] using htableau
    -- The selected tableau row now has the integer-shifted normal form required by Chapter 5.
    linarith [hsupported, hprojected_sum, htableau']
  have hxN_nonnegative : 0 ≤ xN := by
    intro j
    by_cases hj : j ∈ N
    · have hj' : j ∈ corner_nonbasic_indices hp B := by
        simpa only [N] using hj
      simpa only [xN, Finset.piecewise, hj, ↓reduceIte] using hx_nonnegative j hj'
    · simp only [xN, Finset.piecewise, hj, ↓reduceIte, Pi.zero_apply, le_refl]
  have hxN_integral : ∀ j ∈ I, ∃ k : ℤ, xN j = (k : ℝ) := by
    intro j hj
    have hj' : j ∈ Finset.univ.filter (fun k : Fin n ↦ k.1 < p) := by
      simpa only [I] using hj
    have hjlt : j.1 < p := (Finset.mem_filter.mp hj').2
    simpa only [xN] using
      piecewiseZero_integralOnPrefix hp N x hx_integral j hjlt
  have hxN_cut : xN ∈ gomory_mixed_integer_inequality I row (barb i : ℝ) hfrac :=
    gomory_mixed_integer_inequality_valid_of_integer_shifted_equation I row (barb i : ℝ) xN
      hfrac z hxN_equation hxN_nonnegative hxN_integral
  have hrow_zero : ∀ j, j ∉ N → row j = 0 := by
    intro j hj
    simp only [row, Finset.piecewise, hj, ↓reduceIte, Pi.zero_apply]
  have hxN_cut' :
      N.piecewise x 0 ∈ gomory_mixed_integer_inequality I row (barb i : ℝ) hfrac := by
    simpa only [xN] using hxN_cut
  -- The Gomory functional ignores every coordinate removed by the nonbasic projection.
  have hx_cut : x ∈ gomory_mixed_integer_inequality I row (barb i : ℝ) hfrac :=
    (mem_gomory_mixed_integer_inequality_piecewiseZero_iff I N row (barb i : ℝ) hfrac x
      hrow_zero).mp hxN_cut'
  simpa only [I, row, N] using hx_cut

/-- Exercise 6.1. If `i ∈ B` indexes a tableau row of (6.2) with fractional right-hand side,
then the canonical Chapter 5 owner `gomory_mixed_integer_inequality` generated from that row is
valid for the corner polyhedron `corner_polyhedron hp B barA barb`. The row coefficients are
extended by zero outside the nonbasic index set using `Finset.piecewise`, and the integer block
is the first `p` coordinates of `Fin n`. -/
theorem exercise_6_1_gomory_mixed_integer_inequality_valid_for_corner
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    {i : Fin p}
    (hi : i ∈ B)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    corner_polyhedron hp B barA barb ⊆
      gomory_mixed_integer_inequality
        (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
        ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
        (barb i : ℝ)
        hfrac := by
  simpa [exercise_6_1_row_gomory_mixed_integer_cut_eq_gomory_mixed_integer_inequality hp B barA
    barb i hfrac] using
    exercise_6_1_row_gomory_mixed_integer_cut_valid_for_corner hp B barA barb hi hfrac

/-- Exercise 6.1. If `i ∈ B` indexes a tableau row of (6.2) with fractional right-hand side,
then the Gomory mixed-integer inequality generated from that row is valid for the corner
polyhedron `corner_polyhedron hp B barA barb`. -/
theorem ch6_sec6_5_exercise_6_1
    (hp : p ≤ n)
    (B : Finset (Fin p))
    (barA : Matrix (Fin p) (Fin n) ℚ)
    (barb : Fin p → ℚ)
    {i : Fin p}
    (hi : i ∈ B)
    (hfrac : 0 < Int.fract (barb i : ℝ)) :
    corner_polyhedron hp B barA barb ⊆
      gomory_mixed_integer_inequality
        (Finset.univ.filter fun j : Fin n ↦ j.1 < p)
        ((corner_nonbasic_indices hp B).piecewise (fun j ↦ (barA i j : ℝ)) 0)
        (barb i : ℝ)
        hfrac := by
  -- The canonical row formulation established above is exactly the stated exercise.
  exact exercise_6_1_gomory_mixed_integer_inequality_valid_for_corner
    hp B barA barb hi hfrac

end Exercise61

#print axioms exercise_6_1_row_gomory_mixed_integer_cut_valid_for_corner
