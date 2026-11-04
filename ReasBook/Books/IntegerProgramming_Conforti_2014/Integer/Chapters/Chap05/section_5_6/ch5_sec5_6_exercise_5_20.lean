/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_2_2.ch5_sec5_2_2_definition_5_2_2_extra_1

open scoped IntegerVectorNotation Matrix

-- Exercise 5.20 introduces only the source-facing polyhedron.
-- The Chapter 5 owners for Chvatal closure, iterates, and polyhedral Chvatal rank are reused
-- directly from Section 5.2.2 through the generic iterate-rank owner.

section Exercise520

/-
Domain-style sampling for this file:
* primary domain: Chapter 5 Chvatal closures and Chvatal rank of polyhedra in `Fin 2 → ℝ`;
* core/canonical owners inspected upstream: `pure_integer_hull`,
  `pure_integer_chvatal_closure`, `(pure_integer_chvatal_closure^[k]) P`,
  `is_iterate_rank_of_polyhedron`;
* primitive source-facing data here: the explicit Exercise 5.20 polyhedron;
* derived API here: its membership lemma, the source-facing Chvátal-rank lower bound, and the
  resulting early-iterate obstruction.
-/

/-- The polyhedron `P = {x ∈ ℝ² : t x₁ + x₂ ≤ 1 + t, -t x₁ + x₂ ≤ 1}` from Exercise 5.20. -/
def exercise_5_20_polyhedron (t : ℕ) : Set (Fin 2 → ℝ) :=
  {x : Fin 2 → ℝ |
    (t : ℝ) * x 0 + x 1 ≤ 1 + t ∧
      -((t : ℝ) * x 0) + x 1 ≤ 1}

/-- Membership in `exercise_5_20_polyhedron t` is exactly the pair of inequalities
`t x₁ + x₂ ≤ 1 + t` and `-t x₁ + x₂ ≤ 1`. -/
theorem mem_exercise_5_20_polyhedron_iff
    {t : ℕ} {x : Fin 2 → ℝ} :
    x ∈ exercise_5_20_polyhedron t ↔
      (t : ℝ) * x 0 + x 1 ≤ 1 + t ∧
        -((t : ℝ) * x 0) + x 1 ≤ 1 :=
  Iff.rfl

/-- Helper for Exercise 5.20: the two source inequalities are the rows of a `2 × 2` matrix
presentation of the wedge. -/
def exercise_5_20_constraintMatrix (t : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(t : ℝ), 1;
    -((t : ℝ)), 1]

/-- Helper for Exercise 5.20: after `j` rounds, the comparison wedge lowers both right-hand sides
by `j / 2`. -/
noncomputable def exercise_5_20_shiftedConstraintRhs (t j : ℕ) : Fin 2 → ℝ :=
  ![1 + t - (j : ℝ) / 2, 1 - (j : ℝ) / 2]

/-- Helper for Exercise 5.20: the shifted comparison wedge used to track surviving points through
successive Chvátal closures. -/
def exercise_5_20_shiftedPolyhedron (t j : ℕ) : Set (Fin 2 → ℝ) :=
  polyhedron_le_set
    (exercise_5_20_constraintMatrix t)
    (exercise_5_20_shiftedConstraintRhs t j)

/-- Helper for Exercise 5.20: membership in the shifted comparison wedge is exactly the pair of
shifted source inequalities. -/
theorem mem_exercise_5_20_shiftedPolyhedron_iff
    {t j : ℕ} {x : Fin 2 → ℝ} :
    x ∈ exercise_5_20_shiftedPolyhedron t j ↔
      (t : ℝ) * x 0 + x 1 ≤ 1 + t - (j : ℝ) / 2 ∧
        -((t : ℝ) * x 0) + x 1 ≤ 1 - (j : ℝ) / 2 := by
  -- Unfold the two-row matrix description into the original pair of inequalities.
  rw [exercise_5_20_shiftedPolyhedron, polyhedron_le_set]
  constructor
  · intro hx
    have h0 : (t : ℝ) * x 0 + x 1 ≤ 1 + t - (j : ℝ) / 2 := by
      simpa [exercise_5_20_constraintMatrix, exercise_5_20_shiftedConstraintRhs,
        dotProduct, Fin.sum_univ_two] using hx 0
    have h1 : -((t : ℝ) * x 0) + x 1 ≤ 1 - (j : ℝ) / 2 := by
      simpa [exercise_5_20_constraintMatrix, exercise_5_20_shiftedConstraintRhs,
        dotProduct, Fin.sum_univ_two] using hx 1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simpa [exercise_5_20_constraintMatrix, exercise_5_20_shiftedConstraintRhs,
        dotProduct, Fin.sum_univ_two] using h0
    · simpa [exercise_5_20_constraintMatrix, exercise_5_20_shiftedConstraintRhs,
        dotProduct, Fin.sum_univ_two] using h1

/-- Helper for Exercise 5.20: the original source polyhedron is the zero-shift member of the
comparison family. -/
theorem exercise_5_20_shiftedPolyhedron_zero_eq
    (t : ℕ) :
    exercise_5_20_shiftedPolyhedron t 0 = exercise_5_20_polyhedron t := by
  ext x
  -- The `j = 0` shifted system is exactly the original pair of inequalities.
  rw [mem_exercise_5_20_shiftedPolyhedron_iff, mem_exercise_5_20_polyhedron_iff]
  simp

/-- Helper for Exercise 5.20: the second coefficient of a row multiplier is the sum of the two
multiplier coordinates, because both source rows have `x₂`-coefficient `1`. -/
lemma exercise_5_20_vecMul_second
    {t : ℕ} (u : Fin 2 → ℝ) :
    (u ᵥ* exercise_5_20_constraintMatrix t) 1 = u 0 + u 1 := by
  -- Normalize the second column of the row product.
  simp [exercise_5_20_constraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

/-- Helper for Exercise 5.20: the first coefficient of a row multiplier records the signed
imbalance between the two source rows. -/
lemma exercise_5_20_vecMul_first
    {t : ℕ} (u : Fin 2 → ℝ) :
    (u ᵥ* exercise_5_20_constraintMatrix t) 0 = (t : ℝ) * u 0 - (t : ℝ) * u 1 := by
  -- Normalize the first column of the row product.
  simp [exercise_5_20_constraintMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for Exercise 5.20: the pure-integer Chvátal closure is monotone with respect to set
inclusion. -/
lemma pure_integer_chvatal_closure_mono
    {P Q : Set (Fin 2 → ℝ)}
    (hPQ : P ⊆ Q) :
    pure_integer_chvatal_closure P ⊆ pure_integer_chvatal_closure Q := by
  intro x hx
  rw [mem_pure_integer_chvatal_closure_iff] at hx ⊢
  refine ⟨hPQ hx.1, ?_⟩
  -- Any inequality valid on the larger set stays valid when restricted to the smaller one.
  intro c d hvalid
  exact hx.2 c d (fun y hyP ↦ hvalid (hPQ hyP))

/-- Helper for Exercise 5.20: the multiplier bound against the shifted right-hand side is always a
half-integer determined by the two integral row-product coefficients. -/
lemma exercise_5_20_shiftedBound_eq_halfInteger
    (t j : ℕ)
    (u : Fin 2 → ℝ)
    {a0 a1 : ℤ}
    (ha0 : (u ᵥ* exercise_5_20_constraintMatrix t) 0 = (a0 : ℝ))
    (ha1 : (u ᵥ* exercise_5_20_constraintMatrix t) 1 = (a1 : ℝ)) :
    u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j =
      ((a0 + (Int.ofNat t + 2 - Int.ofNat j) * a1 : ℤ) : ℝ) / 2 := by
  -- Rewrite the doubled bound in terms of the two row-product coefficients.
  have htwo :
      2 * (u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j) =
        (a0 : ℝ) + (((t : ℝ) + 2 - j) * (a1 : ℝ)) := by
    calc
      2 * (u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j)
          = 2 * (u 0 * (1 + t - (j : ℝ) / 2) + u 1 * (1 - (j : ℝ) / 2)) := by
              simp [exercise_5_20_shiftedConstraintRhs, dotProduct, Fin.sum_univ_two]
      _ = ((t : ℝ) * u 0 - (t : ℝ) * u 1) +
            (((t : ℝ) + 2 - j) * (u 0 + u 1)) := by ring
      _ = (u ᵥ* exercise_5_20_constraintMatrix t) 0 +
            (((t : ℝ) + 2 - j) * (u ᵥ* exercise_5_20_constraintMatrix t) 1) := by
              rw [exercise_5_20_vecMul_first, exercise_5_20_vecMul_second]
      _ = (a0 : ℝ) + (((t : ℝ) + 2 - j) * (a1 : ℝ)) := by rw [ha0, ha1]
  have hcast :
      (((a0 + (Int.ofNat t + 2 - Int.ofNat j) * a1 : ℤ) : ℤ) : ℝ) =
        (a0 : ℝ) + (((t : ℝ) + 2 - j) * (a1 : ℝ)) := by
    norm_num
  linarith

/-- Helper for Exercise 5.20: the floor of a half-integer `(N : ℝ) / 2` is the integer division
`N / 2`. -/
lemma exercise_5_20_halfInteger_floor_eq
    (N : ℤ) :
    ((Int.floor ((N : ℝ) / 2) : ℤ) : ℝ) = ((N / 2 : ℤ) : ℝ) := by
  -- This is exactly `Int.floor_div_natCast` specialized to the real cast of `N`.
  simpa using congrArg (fun z : ℤ ↦ (z : ℝ))
    (Int.floor_div_natCast (a := (N : ℝ)) 2)

/-- Helper for Exercise 5.20: shifting the right-hand side from `j` to `j + 1` decreases every
multiplier bound enough to pass below the previous rounded bound. -/
lemma exercise_5_20_shiftedBound_succ_le_floor
    (t j : ℕ)
    (u : Fin 2 → ℝ)
    (hu_nonneg : ∀ i : Fin 2, 0 ≤ u i)
    {a0 a1 : ℤ}
    (ha0 : (u ᵥ* exercise_5_20_constraintMatrix t) 0 = (a0 : ℝ))
    (ha1 : (u ᵥ* exercise_5_20_constraintMatrix t) 1 = (a1 : ℝ)) :
    u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) ≤
      ((Int.floor (u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j) : ℤ) : ℝ) := by
  let N : ℤ := a0 + (Int.ofNat t + 2 - Int.ofNat j) * a1
  have hdelta :
      u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j = (N : ℝ) / 2 := by
    simpa [N] using exercise_5_20_shiftedBound_eq_halfInteger t j u ha0 ha1
  have ha1_eq_sum : (a1 : ℝ) = u 0 + u 1 := by
    rw [← ha1, exercise_5_20_vecMul_second]
  by_cases ha1_zero : a1 = 0
  · -- Zero second coefficient forces the whole nonnegative multiplier to vanish.
    have hsum_zero : u 0 + u 1 = 0 := by
      simpa [ha1_zero] using ha1_eq_sum.symm
    have hu0_zero : u 0 = 0 := by
      nlinarith [hu_nonneg 0, hu_nonneg 1, hsum_zero]
    have hu1_zero : u 1 = 0 := by
      nlinarith [hu_nonneg 0, hu_nonneg 1, hsum_zero]
    have hsucc_zero : u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) = 0 := by
      simp [exercise_5_20_shiftedConstraintRhs, dotProduct, Fin.sum_univ_two, hu0_zero, hu1_zero]
    have hzero : u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j = 0 := by
      simp [exercise_5_20_shiftedConstraintRhs, dotProduct, Fin.sum_univ_two, hu0_zero, hu1_zero]
    rw [hsucc_zero, hzero]
    norm_num
  · have ha1_nonneg : 0 ≤ a1 := by
      have hsum_nonneg : 0 ≤ u 0 + u 1 := by
        nlinarith [hu_nonneg 0, hu_nonneg 1]
      rw [← ha1_eq_sum] at hsum_nonneg
      exact_mod_cast hsum_nonneg
    have ha1_one : 1 ≤ a1 := by
      omega
    have hdelta_succ :
        u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) =
          ((N - a1 : ℤ) : ℝ) / 2 := by
      -- Advancing the shift lowers the multiplier bound by `(u 0 + u 1) / 2 = a1 / 2`.
      calc
        u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1)
            = u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j - (u 0 + u 1) / 2 := by
                simp [exercise_5_20_shiftedConstraintRhs, dotProduct, Fin.sum_univ_two]
                ring
        _ = (N : ℝ) / 2 - (a1 : ℝ) / 2 := by rw [hdelta, ha1_eq_sum]
        _ = (((N - a1 : ℤ) : ℝ) / 2) := by
              norm_num
              ring
    have hdiv_int : N - a1 ≤ 2 * (N / 2) := by
      omega
    have hdiv_real : ((N - a1 : ℤ) : ℝ) ≤ 2 * ((N / 2 : ℤ) : ℝ) := by
      exact_mod_cast hdiv_int
    rw [hdelta_succ, hdelta, exercise_5_20_halfInteger_floor_eq]
    linarith

/-- Helper for Exercise 5.20: one Chvátal step from the `j`th shifted wedge still contains the
`(j + 1)`st shifted wedge. -/
lemma exercise_5_20_shiftedPolyhedron_succ_subset_closure
    (t j : ℕ) :
    exercise_5_20_shiftedPolyhedron t (j + 1) ⊆
      pure_integer_chvatal_closure (exercise_5_20_shiftedPolyhedron t j) := by
  intro x hx
  rw [exercise_5_20_shiftedPolyhedron] at hx ⊢
  rw [pure_integer_chvatal_closure_eq_chvatalClosure_polyhedron_le_set
    (exercise_5_20_constraintMatrix t)
    (exercise_5_20_shiftedConstraintRhs t j)]
  rw [mem_chvatalClosure_iff]
  refine ⟨?_, ?_⟩
  · -- The `(j + 1)`st wedge is visibly contained in the `j`th wedge.
    have hx_shifted : x ∈ exercise_5_20_shiftedPolyhedron t (j + 1) := by
      simpa [exercise_5_20_shiftedPolyhedron] using hx
    have hx_pair := mem_exercise_5_20_shiftedPolyhedron_iff.mp hx_shifted
    have hx_prev : x ∈ exercise_5_20_shiftedPolyhedron t j := by
      rw [mem_exercise_5_20_shiftedPolyhedron_iff]
      constructor
      · have hshift :
            1 + (t : ℝ) - ((j + 1 : ℕ) : ℝ) / 2 ≤
              1 + (t : ℝ) - (j : ℝ) / 2 := by
            have hsucc :
                (((j + 1 : ℕ) : ℝ) / 2) = (j : ℝ) / 2 + 1 / 2 := by
              norm_num
              ring
            rw [hsucc]
            nlinarith
        exact hx_pair.1.trans hshift
      · have hshift :
            1 - ((j + 1 : ℕ) : ℝ) / 2 ≤
              1 - (j : ℝ) / 2 := by
            have hsucc :
                (((j + 1 : ℕ) : ℝ) / 2) = (j : ℝ) / 2 + 1 / 2 := by
              norm_num
              ring
            rw [hsucc]
            nlinarith
        exact hx_pair.2.trans hshift
    simpa [exercise_5_20_shiftedPolyhedron] using hx_prev
  · intro u hu
    rcases (isChvatalMultiplier_univ_iff
        (exercise_5_20_constraintMatrix t) u).1 hu with
      ⟨hu_nonneg, hu_int⟩
    let a0 : ℤ := Classical.choose (hu_int 0)
    let a1 : ℤ := Classical.choose (hu_int 1)
    have ha0 : (u ᵥ* exercise_5_20_constraintMatrix t) 0 = (a0 : ℝ) := by
      exact Classical.choose_spec (hu_int 0)
    have ha1 : (u ᵥ* exercise_5_20_constraintMatrix t) 1 = (a1 : ℝ) := by
      exact Classical.choose_spec (hu_int 1)
    have hx_mem :
        x ∈ polyhedron_le_set
          (exercise_5_20_constraintMatrix t)
          (exercise_5_20_shiftedConstraintRhs t (j + 1)) := hx
    have hx_bound :
        (u ᵥ* exercise_5_20_constraintMatrix t) ⬝ᵥ x ≤
          u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) := by
      -- Validity on the smaller shifted wedge comes from the nonnegative row multiplier itself.
      have hrow :
          (exercise_5_20_constraintMatrix t) *ᵥ x ≤
            exercise_5_20_shiftedConstraintRhs t (j + 1) := hx_mem
      calc
        (u ᵥ* exercise_5_20_constraintMatrix t) ⬝ᵥ x =
            u ⬝ᵥ ((exercise_5_20_constraintMatrix t) *ᵥ x) := by
              rw [Matrix.dotProduct_mulVec]
        _ ≤ u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) :=
          dotProduct_le_dotProduct_of_nonneg_left hrow hu_nonneg
    have hhalf_step :
        u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t (j + 1) ≤
          ((Int.floor (u ⬝ᵥ exercise_5_20_shiftedConstraintRhs t j) : ℤ) : ℝ) :=
      exercise_5_20_shiftedBound_succ_le_floor t j u hu_nonneg ha0 ha1
    exact hx_bound.trans hhalf_step

/-- Helper for Exercise 5.20: every shifted comparison wedge survives through the corresponding
number of Chvátal rounds of the original polyhedron. -/
lemma exercise_5_20_shiftedPolyhedron_subset_iterate
    (t j : ℕ) :
    exercise_5_20_shiftedPolyhedron t j ⊆
      (pure_integer_chvatal_closure^[j]) (exercise_5_20_polyhedron t) := by
  induction j with
  | zero =>
      -- The base comparison wedge is exactly the original polyhedron.
      simpa [exercise_5_20_shiftedPolyhedron_zero_eq]
  | succ j ih =>
      intro x hx
      -- First move one round using the shifted comparison lemma, then transport along monotonicity.
      have hx_closure :
          x ∈ pure_integer_chvatal_closure (exercise_5_20_shiftedPolyhedron t j) :=
        exercise_5_20_shiftedPolyhedron_succ_subset_closure t j hx
      have hmono :
          pure_integer_chvatal_closure (exercise_5_20_shiftedPolyhedron t j) ⊆
            pure_integer_chvatal_closure
              ((pure_integer_chvatal_closure^[j]) (exercise_5_20_polyhedron t)) :=
        pure_integer_chvatal_closure_mono ih
      simpa [Function.iterate_succ_apply'] using hmono hx_closure

/-- Helper for Exercise 5.20: every integer point of the source polyhedron already satisfies
`x₂ ≤ 1`. -/
lemma exercise_5_20_integerPoint_second_le_one
    {t : ℕ} {x : Fin 2 → ℝ}
    (hx : x ∈ exercise_5_20_polyhedron t)
    (hx_int : x ∈ ℤ^2) :
    x 1 ≤ 1 := by
  rw [mem_exercise_5_20_polyhedron_iff] at hx
  rw [mem_integerVectors_iff_forall] at hx_int
  obtain ⟨z, hz⟩ := hx_int 0
  have hz_cases : z ≤ 0 ∨ 1 ≤ z := by
    omega
  -- Split on the integral first coordinate and use the row whose slack becomes nonpositive.
  cases hz_cases with
  | inl hz_nonpos =>
      have hx0_nonpos : x 0 ≤ 0 := by
        rw [← hz]
        exact_mod_cast hz_nonpos
      have htx_nonpos : (t : ℝ) * x 0 ≤ 0 := by
        nlinarith
      linarith [hx.2, htx_nonpos]
  | inr hz_one =>
      have hx0_one : 1 ≤ x 0 := by
        rw [← hz]
        exact_mod_cast hz_one
      have htx_ge_t : (t : ℝ) ≤ (t : ℝ) * x 0 := by
        nlinarith
      linarith [hx.1, htx_ge_t]

/-- Helper for Exercise 5.20: the pure-integer hull of the source polyhedron lies in the halfspace
`x₂ ≤ 1`. -/
lemma exercise_5_20_pure_integer_hull_subset_second_le_one
    (t : ℕ) :
    pure_integer_hull (exercise_5_20_polyhedron t) ⊆ {x : Fin 2 → ℝ | x 1 ≤ 1} := by
  rw [pure_integer_hull_eq_convexHull]
  refine convexHull_min ?_ ?_
  · intro x hx
    exact exercise_5_20_integerPoint_second_le_one hx.1 hx.2
  · -- The coordinate halfspace is convex because the second coordinate is affine.
    intro x hx y hy a b ha hb hab
    dsimp at hx hy ⊢
    have hcomb : a * x 1 + b * y 1 ≤ 1 := by
      nlinarith
    simpa [Pi.smul_apply, Pi.add_apply] using hcomb

/-- Exercise 5.20. If `k` is the Chvátal rank of
`exercise_5_20_polyhedron t = {x ∈ ℝ² : t x₁ + x₂ ≤ 1 + t, -t x₁ + x₂ ≤ 1}`,
then `t ≤ k`. -/
theorem exercise_5_20_chvatal_rank_at_least
    {t k : ℕ}
    (hk : is_iterate_rank_of_polyhedron
      pure_integer_chvatal_closure (exercise_5_20_polyhedron t) k) :
    t ≤ k := by
  by_contra htk
  have hlt : k < t := Nat.not_le.mp htk
  let w : Fin 2 → ℝ := ![(1 / 2 : ℝ), 1 + ((t - k : ℝ) / 2)]
  have hw_shifted : w ∈ exercise_5_20_shiftedPolyhedron t k := by
    -- The midpoint witness lies on both boundary lines of the `k`th shifted wedge.
    rw [mem_exercise_5_20_shiftedPolyhedron_iff]
    constructor
    · simp [w]
      ring_nf
      linarith
    · simp [w]
      ring_nf
      linarith
  have hw_iter :
      w ∈ (pure_integer_chvatal_closure^[k]) (exercise_5_20_polyhedron t) :=
    exercise_5_20_shiftedPolyhedron_subset_iterate t k hw_shifted
  have hw_second_gt_one : 1 < w 1 := by
    -- The branch `k < t` makes the witness strictly above the integer-hull halfspace.
    have htk_pos : 0 < (t - k : ℕ) := Nat.sub_pos_of_lt hlt
    have htk_pos_real : (0 : ℝ) < ((t - k : ℕ) : ℝ) := by
      exact_mod_cast htk_pos
    simp [w]
    linarith
  have hw_not_hull : w ∉ pure_integer_hull (exercise_5_20_polyhedron t) := by
    intro hw_hull
    have hw_second_le_one :
        w 1 ≤ 1 :=
      exercise_5_20_pure_integer_hull_subset_second_le_one t hw_hull
    linarith
  have hw_hull : w ∈ pure_integer_hull (exercise_5_20_polyhedron t) := by
    simpa [hk.eq_integer_hull] using hw_iter
  exact hw_not_hull hw_hull

/-- If `k` is the Chvátal rank of `exercise_5_20_polyhedron t`, then every earlier iterate
strictly before the source lower bound `t` still differs from the pure-integer hull. -/
theorem exercise_5_20_iterate_ne_pure_integer_hull_of_lt
    {t k j : ℕ}
    (hk : is_iterate_rank_of_polyhedron
      pure_integer_chvatal_closure (exercise_5_20_polyhedron t) k)
    (hj : j < t) :
    (pure_integer_chvatal_closure^[j]) (exercise_5_20_polyhedron t) ≠
      pure_integer_hull (exercise_5_20_polyhedron t) := by
  exact hk.not_eq_integer_hull <| lt_of_lt_of_le hj (exercise_5_20_chvatal_rank_at_least hk)

end Exercise520
