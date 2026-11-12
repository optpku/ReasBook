/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_32
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_theorem_4_47

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix Pointwise

/-- The number of strictly positive coordinates of `x`. -/
noncomputable def positive_entry_count {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i ↦ 0 < x i).card

/-- The points of `P` with at least `k` strictly positive coordinates. -/
def points_with_at_least_k_positive_entries
    {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ k ≤ positive_entry_count x}

/-- The points of `P` with at most `k` strictly positive coordinates. -/
def points_with_at_most_k_positive_entries
    {n : ℕ} (P : Set (Fin n → ℝ)) (k : ℕ) : Set (Fin n → ℝ) :=
  {x | x ∈ P ∧ positive_entry_count x ≤ k}

/-- Helper for Exercise 4.34: extend a finite-support affine combination to all of `Fin p` by
setting the outside coefficients to zero. -/
lemma polytope_barycentric_indicator_extension
    {n p : ℕ}
    {vertex : Fin p → Fin n → ℚ}
    {s : Finset (Fin p)}
    {w : Fin p → ℝ}
    {x : Fin n → ℝ}
    (hx : s.affineCombination ℝ (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) w = x)
    (hw_nonneg : ∀ j ∈ s, 0 ≤ w j)
    (hw_sum : s.sum w = 1) :
    ∃ coeff : Fin p → ℝ,
      (∀ j, 0 ≤ coeff j) ∧
        (∑ j, coeff j = 1) ∧
        (∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) = x) := by
  classical
  let coeff : Fin p → ℝ := Set.indicator (↑s) w
  refine ⟨coeff, ?_, ?_, ?_⟩
  · -- The indicator extension keeps the original weights on `s` and vanishes elsewhere.
    intro j
    by_cases hj : j ∈ s
    · simp [coeff, hj, hw_nonneg j hj]
    · simp [coeff, hj]
  · -- The full-index sum of the indicator extension matches the original affine normalization.
    have hsum_indicator :
        ∑ j, coeff j = s.sum w := by
      simpa [coeff] using
        (Finset.sum_indicator_subset w (Finset.subset_univ s))
    exact hsum_indicator.trans hw_sum
  · have hs :
        s.affineCombination ℝ (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) w =
          Finset.univ.affineCombination ℝ
            (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) coeff := by
      simpa [coeff] using
        (Finset.affineCombination_indicator_subset
          (k := ℝ)
          (w := w)
          (p := fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ))
          (h := Finset.subset_univ s))
    have hcoeff_sum : ∑ j, coeff j = 1 := by
      have hsum_indicator :
          ∑ j, coeff j = s.sum w := by
        simpa [coeff] using
          (Finset.sum_indicator_subset w (Finset.subset_univ s))
      exact hsum_indicator.trans hw_sum
    have hlinear :
        Finset.univ.affineCombination ℝ
            (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) coeff =
          ∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) := by
      rw [Finset.affineCombination_eq_linear_combination
        Finset.univ
        (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ))
        coeff
        hcoeff_sum]
    -- Rewrite the owner affine-combination witness into the linear-combination form used here.
    calc
      ∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) =
          Finset.univ.affineCombination ℝ
            (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) coeff := hlinear.symm
      _ = s.affineCombination ℝ (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ)) w := hs.symm
      _ = x := hx

/-- Helper for Exercise 4.34: a nonnegative rational polytope admits a fixed finite barycentric
parametrization, and the same rational vertex family yields coordinatewise big-`M` bounds. -/
lemma polytope_barycentric_data_with_coordinate_bounds
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (hP_rational : P.IsRationalPolytope)
    (hP_nonneg : P ⊆ Set.Ici (0 : Fin n → ℝ))
    :
    ∃ p : ℕ, ∃ vertex : Fin p → Fin n → ℚ, ∃ M : Fin n → ℚ,
      (∀ i j, 0 ≤ vertex j i ∧ vertex j i ≤ M i) ∧
      P = convexHull ℝ (Set.range fun j : Fin p ↦ fun i : Fin n ↦ (vertex j i : ℝ)) ∧
      (∀ x, x ∈ P ↔
        ∃ coeff : Fin p → ℝ,
          (∀ j, 0 ≤ coeff j) ∧
            (∑ j, coeff j = 1) ∧
            (∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) = x)) := by
  rcases hP_rational with ⟨p, vertex, hP_eq⟩
  let pts : Fin p → Fin n → ℝ := fun j i ↦ (vertex j i : ℝ)
  let M : Fin n → ℚ := fun i ↦ ∑ j, vertex j i
  refine ⟨p, vertex, M, ?_, hP_eq, ?_⟩
  · -- Each listed vertex already lies in `P`, so nonnegativity of `P` gives coordinate bounds.
    intro i j
    have hvertex_mem : pts j ∈ P := by
      rw [hP_eq]
      exact subset_convexHull ℝ (Set.range pts) (Set.mem_range_self j)
    have hvertex_nonneg_real : 0 ≤ pts j i := by
      exact (hP_nonneg hvertex_mem) i
    have hvertex_nonneg : 0 ≤ vertex j i := by
      have hcast_nonneg : (0 : ℝ) ≤ (vertex j i : ℝ) := by
        simpa [pts] using hvertex_nonneg_real
      exact_mod_cast hcast_nonneg
    have hsum_nonneg : ∀ l : Fin p, 0 ≤ vertex l i := by
      intro l
      have hl_mem : pts l ∈ P := by
        rw [hP_eq]
        exact subset_convexHull ℝ (Set.range pts) (Set.mem_range_self l)
      have hl_nonneg_real : 0 ≤ pts l i := by
        exact (hP_nonneg hl_mem) i
      have hcast_nonneg : (0 : ℝ) ≤ (vertex l i : ℝ) := by
        simpa [pts] using hl_nonneg_real
      exact_mod_cast hcast_nonneg
    have hvertex_le_M : vertex j i ≤ M i := by
      dsimp [M]
      exact Finset.single_le_sum (fun l _hl ↦ hsum_nonneg l) (Finset.mem_univ j)
    exact ⟨hvertex_nonneg, hvertex_le_M⟩
  · intro x
    constructor
    · intro hxP
      rw [hP_eq, convexHull_range_eq_exists_affineCombination] at hxP
      rcases hxP with ⟨s, w, hw_nonneg, hw_sum, hx⟩
      exact polytope_barycentric_indicator_extension hx hw_nonneg hw_sum
    · rintro ⟨coeff, hcoeff_nonneg, hcoeff_sum, hcoeff_eq⟩
      rw [hP_eq, convexHull_range_eq_exists_affineCombination]
      refine ⟨Finset.univ, coeff, ?_, hcoeff_sum, ?_⟩
      · simpa using hcoeff_nonneg
      · -- Route correction: package the full-index linear combination back into the owner
        -- affine-combination normal form instead of unfolding the convex hull further.
        rw [Finset.affineCombination_eq_linear_combination
          Finset.univ
          (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ))
          coeff
          hcoeff_sum]
        exact hcoeff_eq

/-- Helper for Exercise 4.34: on a nonnegative vector, counting strictly positive entries agrees
with Exercise 2.32's owner notion counting nonzero entries. -/
lemma positive_entry_count_eq_nonzero_coordinate_count_of_nonneg
    {n : ℕ}
    (x : Fin n → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i) :
    positive_entry_count x = nonzero_coordinate_count x := by
  -- Under coordinatewise nonnegativity, `x i ≠ 0` is equivalent to `0 < x i`.
  unfold positive_entry_count nonzero_coordinate_count
  have hfilter :
      Finset.univ.filter (fun i : Fin n ↦ 0 < x i) =
        Finset.univ.filter (fun i : Fin n ↦ x i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact ne_of_gt hi
    · intro hi
      exact lt_of_le_of_ne (hx_nonneg i) (Ne.symm hi)
  simp [hfilter]

/-- Helper for Exercise 4.34: under coordinatewise bounds, the positive-entry condition is exactly
Exercise 2.32's bounded-cardinality feasibility predicate. -/
lemma positive_entry_count_le_iff_bounded_nonzero_cardinality_feasible
    {n : ℕ}
    (x : Fin n → ℝ)
    (k : ℕ)
    (M : Fin n → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_le_M : ∀ i, x i ≤ M i) :
    positive_entry_count x ≤ k ↔
      bounded_nonzero_cardinality_feasible M k x := by
  -- Rewrite the support count, then the remaining data are exactly the Chapter 2 bounds.
  rw [bounded_nonzero_cardinality_feasible,
    positive_entry_count_eq_nonzero_coordinate_count_of_nonneg x hx_nonneg]
  constructor
  · intro hx_count
    exact ⟨fun i ↦ ⟨hx_nonneg i, hx_le_M i⟩, hx_count⟩
  · intro hx
    exact hx.2

/-- Helper for Exercise 4.34: the bounded-cardinality owner from Exercise 2.32 gives the standard
binary-activation formulation for the at-most-`k` positive-entry condition. -/
lemma positive_entry_count_le_iff_exists_bounded_nonzero_cardinality_milp
    {n : ℕ}
    (x : Fin n → ℝ)
    (k : ℕ)
    (M : Fin n → ℝ)
    (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_le_M : ∀ i, x i ≤ M i) :
    positive_entry_count x ≤ k ↔
      ∃ z : Fin n → ℝ, bounded_nonzero_cardinality_milp M k z x := by
  -- Exercise 2.32 applies once the upper bounds are known to be nonnegative.
  have hM_nonneg : ∀ i, 0 ≤ M i := fun i ↦ le_trans (hx_nonneg i) (hx_le_M i)
  rw [positive_entry_count_le_iff_bounded_nonzero_cardinality_feasible x k M hx_nonneg hx_le_M]
  exact exercise_2_32 M hM_nonneg k x

/-- Helper for Exercise 4.34: a real `0/1` vector can be recast as an integer `0/1` vector
without changing its real coordinates. -/
lemma exists_integer_cast_of_real_binary_vector
    {n : ℕ}
    (z : Fin n → ℝ)
    (hz : ∀ i, z i = 0 ∨ z i = 1) :
    ∃ w : Fin n → ℤ, ∀ i, (w i : ℝ) = z i := by
  -- Choose the matching integral value coordinatewise.
  refine ⟨fun i ↦ if z i = 0 then 0 else 1, ?_⟩
  intro i
  rcases hz i with hiz | hiz
  · simp [hiz]
  · simp [hiz]

/-- Helper for Exercise 4.34: an integer whose real cast lies in `[0,1]` is either `0` or `1`. -/
lemma int_eq_zero_or_one_of_cast_between_zero_and_one
    (z : ℤ)
    (hz_nonneg : 0 ≤ (z : ℝ))
    (hz_le_one : (z : ℝ) ≤ 1) :
    z = 0 ∨ z = 1 := by
  -- Move the interval bounds back to `ℤ` and close the two-point interval arithmetically.
  have hz_nonneg' : 0 ≤ z := by
    exact_mod_cast hz_nonneg
  have hz_le_one' : z ≤ 1 := by
    exact_mod_cast hz_le_one
  omega

/-- Helper for Exercise 4.34: the constraint rows for the explicit at-most-`k` support MILP. -/
private inductive AtMostSupportRow (n p : ℕ)
  | lambda_nonneg (j : Fin p)
  | lambda_sum_upper
  | lambda_sum_lower
  | x_eq_upper (i : Fin n)
  | x_eq_lower (i : Fin n)
  | z_upper (i : Fin n)
  | z_lower (i : Fin n)
  | big_m (i : Fin n)
  | z_sum
deriving DecidableEq, Fintype

/-- Helper for Exercise 4.34: on `Fin 1`, membership in `(0,1]` is exactly positivity of the
unique coordinate together with the upper bound `≤ 1`. -/
lemma fin1_Ioc_positive_coordinate_iff
    (x : Fin 1 → ℝ) :
    x ∈ Set.Ioc (0 : Fin 1 → ℝ) 1 ↔ 0 < x 0 ∧ x 0 ≤ 1 := by
  rw [Set.mem_Ioc]
  constructor
  · intro hx
    rcases (Pi.lt_def.1 hx.1) with ⟨hx_nonneg, i, hi_pos⟩
    fin_cases i
    exact ⟨hi_pos, hx.2 0⟩
  · rintro ⟨hx_pos, hx_le_one⟩
    refine ⟨?_, ?_⟩
    · refine Pi.lt_def.2 ⟨?_, 0, hx_pos⟩
      intro i
      fin_cases i
      exact hx_pos.le
    · intro i
      fin_cases i
      exact hx_le_one

/-- Helper for Exercise 4.34: on the one-dimensional unit interval, requiring at least one
positive coordinate gives the half-open interval `(0,1]`. -/
lemma interval_counterexample_for_at_least_one_positive_entry :
    points_with_at_least_k_positive_entries (Set.Icc (0 : Fin 1 → ℝ) 1) 1 =
      Set.Ioc (0 : Fin 1 → ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨hxIcc, hx_count⟩
    have hx_nonneg : 0 ≤ x 0 := by
      exact hxIcc.1 0
    have hx_le_one : x 0 ≤ 1 := by
      exact hxIcc.2 0
    have hx_pos : 0 < x 0 := by
      by_contra hx_not_pos
      have hx_eq_zero : x 0 = 0 := by
        exact le_antisymm (le_of_not_gt hx_not_pos) hx_nonneg
      have hcount_zero : positive_entry_count x = 0 := by
        unfold positive_entry_count
        simp [hx_eq_zero]
      omega
    exact (fin1_Ioc_positive_coordinate_iff x).2 ⟨hx_pos, hx_le_one⟩
  · intro hxIoc
    rcases (fin1_Ioc_positive_coordinate_iff x).1 hxIoc with ⟨hx_pos, hx_le_one⟩
    have hxIcc : x ∈ Set.Icc (0 : Fin 1 → ℝ) 1 := by
      rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
      constructor
      · intro i
        fin_cases i
        exact hx_pos.le
      · intro i
        fin_cases i
        exact hx_le_one
    have hcount_one : positive_entry_count x = 1 := by
      have hfilter :
          Finset.univ.filter (fun i : Fin 1 ↦ 0 < x i) = {0} := by
        ext i
        fin_cases i
        simp [hx_pos]
      unfold positive_entry_count
      rw [hfilter]
      simp
    refine ⟨hxIcc, ?_⟩
    omega

/-- Helper for Exercise 4.34: the integral cone generated by zero directions is exactly `{0}`. -/
lemma integral_intcone_eq_singleton_zero_of_generators_eq_zero
    {n t : ℕ}
    {r : Fin t → Fin n → ℤ}
    (hr : ∀ j, (fun i : Fin n ↦ (r j i : ℝ)) = 0) :
    integral_intcone r = ({0} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff]
    rcases (mem_integral_intcone_iff).1 hx with ⟨a, rfl⟩
    -- Once every generator is zero, every integer-cone combination collapses to the zero vector.
    simp [hr]
  · rintro rfl
    exact (mem_integral_intcone_iff).2 ⟨0, by simp⟩

/-- Helper for Exercise 4.34: translating by a nonzero discrete ray eventually leaves every closed
ball. -/
lemma unbounded_nat_ray_not_bounded_in_closedBall
    {n : ℕ}
    (q v : Fin n → ℝ)
    (hv : v ≠ 0)
    (R : ℝ) :
    ∃ m : ℕ, R < ‖q + (m : ℝ) • v‖ := by
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨m, hm⟩ := exists_nat_gt ((R + ‖q‖) / ‖v‖)
  refine ⟨m, ?_⟩
  have hm_real : ((R + ‖q‖) / ‖v‖ : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hv_norm_ne : ‖v‖ ≠ 0 := ne_of_gt hv_norm_pos
  have hscale :
      R + ‖q‖ < (m : ℝ) * ‖v‖ := by
    -- Multiply the chosen lower bound by the positive ray norm.
    have hmul := mul_lt_mul_of_pos_right hm_real hv_norm_pos
    calc
      R + ‖q‖ = ((R + ‖q‖) / ‖v‖) * ‖v‖ := by
        field_simp [hv_norm_ne]
      _ < (m : ℝ) * ‖v‖ := hmul
  have hsmul_norm : ‖(m : ℝ) • v‖ = (m : ℝ) * ‖v‖ := by
    calc
      ‖(m : ℝ) • v‖ = ‖(m : ℝ)‖ * ‖v‖ := norm_smul _ _
      _ = (m : ℝ) * ‖v‖ := by
        rw [Real.norm_of_nonneg]
        positivity
  have htriangle :
      ‖(m : ℝ) • v‖ ≤ ‖q + (m : ℝ) • v‖ + ‖q‖ := by
    -- Compare the ray point to the translated point by one reverse-triangle step.
    have := norm_add_le (q + (m : ℝ) • v) (-q)
    simpa [sub_eq_add_neg, add_assoc] using this
  have hlarge :
      R + ‖q‖ < ‖q + (m : ℝ) • v‖ + ‖q‖ := by
    calc
      R + ‖q‖ < (m : ℝ) * ‖v‖ := hscale
      _ = ‖(m : ℝ) • v‖ := hsmul_norm.symm
      _ ≤ ‖q + (m : ℝ) • v‖ + ‖q‖ := htriangle
  linarith

/-- Helper for Exercise 4.34: a bounded Minkowski sum with a nonempty base set cannot contain a
nonzero integral-cone generator direction. -/
lemma integral_intcone_generators_eq_zero_of_bounded_nonempty_sum
    {n t : ℕ}
    {U : Set (Fin n → ℝ)}
    {r : Fin t → Fin n → ℤ}
    (hbounded : Bornology.IsBounded (U + integral_intcone r))
    (hU : U.Nonempty) :
    ∀ j, (fun i : Fin n ↦ (r j i : ℝ)) = 0 := by
  intro j
  rcases hU with ⟨q, hqU⟩
  let ray : Fin n → ℝ := fun i ↦ (r j i : ℝ)
  by_contra hj
  have hjray : ray ≠ 0 := by
    simpa [ray] using hj
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : Fin n → ℝ)
  have hray_mem : ∀ m : ℕ, q + (m : ℝ) • ray ∈ U + integral_intcone r := by
    intro m
    have hcone_mem : (m : ℝ) • ray ∈ integral_intcone r := by
      refine (mem_integral_intcone_iff).2 ?_
      refine ⟨fun l ↦ if l = j then m else 0, ?_⟩
      -- The one-hot coefficient family recovers exactly the `j`th ray.
      ext i
      have honehot :
          (∑ l : Fin t, (((if l = j then m else 0 : ℕ) : ℝ)) •
              (fun i : Fin n ↦ (r l i : ℝ))) i =
            ((m : ℝ) • ray) i := by
        rw [Finset.sum_apply]
        calc
          ∑ l : Fin t,
              ((((if l = j then m else 0 : ℕ) : ℝ)) •
                (fun i : Fin n ↦ (r l i : ℝ))) i
              = ∑ l : Fin t, if l = j then (m : ℝ) * (r j i : ℝ) else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro l hl
                  by_cases hlj : l = j
                  · subst hlj
                    simp [Pi.smul_apply]
                  · simp [hlj, Pi.smul_apply]
          _ = (m : ℝ) * (r j i : ℝ) := by
                simp
          _ = ((m : ℝ) • ray) i := by
                simp [ray, Pi.smul_apply]
      exact honehot.symm
    exact Set.mem_add.mpr ⟨q, hqU, (m : ℝ) • ray, hcone_mem, rfl⟩
  obtain ⟨m, hm⟩ := unbounded_nat_ray_not_bounded_in_closedBall q ray hjray R
  have hmem_ball : q + (m : ℝ) • ray ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
    exact hR (hray_mem m)
  have hnorm_le : ‖q + (m : ℝ) • ray‖ ≤ R := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hmem_ball
  linarith

/-- Helper for Exercise 4.34: a finite union of rational polytopes is closed. -/
lemma isClosed_iUnion_rational_polytopes
    {n k : ℕ}
    (P : Fin k → Set (Fin n → ℝ))
    (hP : ∀ i, (P i).IsRationalPolytope) :
    IsClosed (⋃ i, P i) := by
  classical
  refine isClosed_iUnion_of_finite fun i ↦ ?_
  rcases hP i with ⟨m, vertex, hPi⟩
  rw [hPi]
  simpa using
    (Set.finite_range
      (fun j : Fin m ↦ fun t : Fin n ↦ (vertex j t : ℝ))).isClosed_convexHull (𝕜 := ℝ)

/-- Helper for Exercise 4.34: the convex hull of a finitely indexed rational vertex family is a
rational polytope. -/
lemma isRationalPolytope_convexHull_range_of_fintype
    {n : ℕ}
    {ι : Type*}
    [Fintype ι]
    (vertex : ι → Fin n → ℚ) :
    (convexHull ℝ (Set.range fun j : ι ↦ fun i : Fin n ↦ (vertex j i : ℝ))).IsRationalPolytope := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun j i ↦ vertex (e j) i, ?_⟩
  ext x
  constructor
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin n ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin n ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx
  · intro hx
    have hrange :
        Set.range (fun j : Fin (Fintype.card ι) ↦ fun i : Fin n ↦ ((vertex (e j) i : ℚ) : ℝ)) =
          Set.range (fun j : ι ↦ fun i : Fin n ↦ (vertex j i : ℝ)) := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨e j, rfl⟩
      · rintro ⟨j, rfl⟩
        exact ⟨e.symm j, by simp [e]⟩
    simpa [hrange] using hx

/-- Helper for Exercise 4.34: if every listed vertex vanishes outside `T`, then every point of
their convex hull vanishes outside `T` as well. -/
lemma support_restricted_convex_hull_zero_outside
    {n : ℕ}
    {ι : Type*}
    [Fintype ι]
    (T : Finset (Fin n))
    (vertex : ι → Fin n → ℚ)
    (hvertex : ∀ j i, i ∉ T → vertex j i = 0)
    {x : Fin n → ℝ}
    (hx : x ∈ convexHull ℝ (Set.range fun j : ι ↦ fun i : Fin n ↦ (vertex j i : ℝ))) :
    ∀ i, i ∉ T → x i = 0 := by
  let Z : Set (Fin n → ℝ) := {y | ∀ i, i ∉ T → y i = 0}
  have hvertex_subset : Set.range (fun j : ι ↦ fun i : Fin n ↦ (vertex j i : ℝ)) ⊆ Z := by
    rintro _ ⟨j, rfl⟩ i hi
    simpa [Z] using congrArg (fun q : ℚ ↦ (q : ℝ)) (hvertex j i hi)
  have hZ_convex : Convex ℝ Z := by
    intro y hy z hz a b ha hb hab i hi
    simp [Z, hy i hi, hz i hi]
  -- The coordinate-vanishing set is convex, so the convex hull stays inside it.
  exact (convexHull_min hvertex_subset hZ_convex hx)

/-- Helper for Exercise 4.34: the one-dimensional half-open unit interval is bounded. -/
lemma fin1_Ioc_unit_interval_isBounded :
    Bornology.IsBounded (Set.Ioc (0 : Fin 1 → ℝ) 1) := by
  refine
    (show Bornology.IsBounded (Metric.ball (0 : Fin 1 → ℝ) 2) from Metric.isBounded_ball).subset
      ?_
  intro x hx
  rcases (fin1_Ioc_positive_coordinate_iff x).1 hx with ⟨hx_pos, hx_le_one⟩
  -- On `Fin 1`, the sup norm is the absolute value of the unique coordinate.
  rw [Metric.mem_ball, dist_eq_norm]
  have hnorm_le_one : ‖x‖ ≤ 1 := by
    rw [Pi.norm_def]
    simpa [abs_of_nonneg hx_pos.le] using hx_le_one
  have hnorm_lt_two : ‖x‖ < (2 : ℝ) := by
    exact lt_of_le_of_lt hnorm_le_one (by norm_num)
  simpa using hnorm_lt_two

/-- Helper for Exercise 4.34: the origin is a limit point of the half-open unit interval
`(0, 1] ⊆ ℝ`. -/
lemma zero_mem_closure_fin1_Ioc_unit_interval :
    (0 : Fin 1 → ℝ) ∈ closure (Set.Ioc (0 : Fin 1 → ℝ) 1) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let y : Fin 1 → ℝ := fun _ ↦ min (ε / 2) (1 / 2)
  refine ⟨y, ?_, ?_⟩
  · -- The truncated midpoint stays inside `(0, 1]`.
    refine (fin1_Ioc_positive_coordinate_iff y).2 ?_
    constructor
    · have hy_pos : 0 < min (ε / 2) (1 / 2) := by
        refine lt_min ?_ (by norm_num)
        linarith
      simpa [y] using hy_pos
    · have hy_le_half : min (ε / 2) (1 / 2) ≤ (1 / 2 : ℝ) := by
        exact min_le_right _ _
      have hy_le_one : min (ε / 2) (1 / 2) ≤ (1 : ℝ) := by
        linarith
      simpa [y] using hy_le_one
  · -- Its norm is at most `ε / 2`, hence strictly less than `ε`.
    have hy_nonneg : 0 ≤ y 0 := by
      dsimp [y]
      exact le_min (by linarith) (by norm_num)
    have hy_lt_eps : y 0 < ε := by
      have hy_le_half : y 0 ≤ ε / 2 := by
        dsimp [y]
        exact min_le_left _ _
      linarith
    have hy_norm_lt_eps : ‖y‖ < ε := by
      have hy_abs_lt_eps : |y 0| < ε := by
        simpa [abs_of_nonneg hy_nonneg] using hy_lt_eps
      rw [Pi.norm_def]
      simpa using hy_abs_lt_eps
    simpa [dist_eq_norm] using hy_norm_lt_eps

/-- Helper for Exercise 4.34: a vanishing nonnegative weighted coordinate sum forces every weight
on a strictly positive coordinate to be zero. -/
lemma zero_coordinate_sum_forces_zero_weight_on_positive_vertex
    {p : ℕ}
    {coeff coord : Fin p → ℝ}
    (hcoeff_nonneg : ∀ j, 0 ≤ coeff j)
    (hcoord_nonneg : ∀ j, 0 ≤ coord j)
    (hsum_zero : ∑ j, coeff j * coord j = 0) :
    ∀ j, 0 < coord j → coeff j = 0 := by
  intro j hj_pos
  have hterm_zero :
      coeff j * coord j = 0 := by
    -- Every nonnegative summand in a zero total sum must itself vanish.
    exact
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _hi ↦ mul_nonneg (hcoeff_nonneg i) (hcoord_nonneg i))).1 hsum_zero j
        (Finset.mem_univ j)
  exact (mul_eq_zero.mp hterm_zero).resolve_right (ne_of_gt hj_pos)

/-- Helper for Exercise 4.34: if the positive-weight vertices all vanish outside `T`, then the
same full barycentric witness already places `x` in the support-restricted hull indexed by `T`. -/
lemma mem_support_restricted_hull_of_full_barycentric
    {n p : ℕ}
    {vertex : Fin p → Fin n → ℚ}
    {T : Finset (Fin n)}
    {x : Fin n → ℝ}
    {coeff : Fin p → ℝ}
    (hcoeff_nonneg : ∀ j, 0 ≤ coeff j)
    (hcoeff_sum : ∑ j, coeff j = 1)
    (hcoeff_eq : ∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) = x)
    (hactive : ∀ j, coeff j ≠ 0 → ∀ i, i ∉ T → vertex j i = 0) :
    x ∈ convexHull ℝ
      (Set.range fun a : {j : Fin p // ∀ i, i ∉ T → vertex j i = 0} ↦
        fun i : Fin n ↦ (vertex a.1 i : ℝ)) := by
  classical
  let pred : Fin p → Prop := fun j ↦ ∀ i, i ∉ T → vertex j i = 0
  rw [convexHull_range_eq_exists_affineCombination]
  refine ⟨Finset.univ.subtype pred, fun a ↦ coeff a.1, ?_, ?_, ?_⟩
  · -- The restricted coefficient family inherits nonnegativity from the full witness.
    intro a ha
    exact hcoeff_nonneg a.1
  · -- Inactive vertices have zero weight, so the restricted weights still sum to `1`.
    have hsum_filter :
        (Finset.univ.filter pred).sum coeff = 1 := by
      rw [Finset.sum_filter_of_ne]
      · exact hcoeff_sum
      · intro j hj hne
        exact hactive j hne
    rw [Finset.sum_subtype_eq_sum_filter]
    exact hsum_filter
  · -- Route correction: move from the full index type to the active subtype by using the
    -- filter/subtype affine-combination identities instead of unfolding the hull further.
    calc
      (Finset.univ.subtype pred).affineCombination ℝ
          (fun a : {j : Fin p // pred j} ↦
            fun i : Fin n ↦ (vertex a.1 i : ℝ))
          (fun a ↦ coeff a.1) =
        (Finset.univ.filter pred).affineCombination ℝ
          (fun j : Fin p ↦ fun i : Fin n ↦ (vertex j i : ℝ))
          coeff := by
            simpa [pred] using
              (Finset.affineCombination_subtype_eq_filter
                (s := Finset.univ)
                (w := coeff)
                (p := fun j : Fin p ↦ fun i : Fin n ↦ (vertex j i : ℝ))
                (pred := pred))
      _ = Finset.univ.affineCombination ℝ
            (fun j : Fin p ↦ fun i : Fin n ↦ (vertex j i : ℝ))
            coeff := by
              rw [Finset.affineCombination_filter_of_ne]
              intro j hj hne
              exact hactive j hne
      _ = x := by
            rw [Finset.affineCombination_eq_linear_combination
              Finset.univ
              (fun j ↦ fun i : Fin n ↦ (vertex j i : ℝ))
              coeff
              hcoeff_sum]
            exact hcoeff_eq

/-- Helper for Exercise 4.34: once a rational vertex presentation of `P` is fixed, the points of
`P` with at most `k` positive coordinates are exactly the union of the support-restricted convex
hulls indexed by supports of size at most `k`. -/
lemma points_with_at_most_k_positive_entries_eq_iUnion_support_restricted_hulls
    {n p : ℕ}
    (P : Set (Fin n → ℝ))
    (k : ℕ)
    (vertex : Fin p → Fin n → ℚ)
    (hP_nonneg : P ⊆ Set.Ici (0 : Fin n → ℝ))
    (hvertex_nonneg : ∀ i j, 0 ≤ vertex j i)
    (hP_eq : P = convexHull ℝ (Set.range fun j : Fin p ↦ fun i : Fin n ↦ (vertex j i : ℝ)))
    (hbary : ∀ x, x ∈ P ↔
      ∃ coeff : Fin p → ℝ,
        (∀ j, 0 ≤ coeff j) ∧
          (∑ j, coeff j = 1) ∧
          (∑ j, coeff j • (fun i : Fin n ↦ (vertex j i : ℝ)) = x)) :
    points_with_at_most_k_positive_entries P k =
      ⋃ T : {T : Finset (Fin n) // T.card ≤ k},
        convexHull ℝ
          (Set.range fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦
            fun i : Fin n ↦ (vertex a.1 i : ℝ)) := by
  classical
  let SupportFamily : Type := {T : Finset (Fin n) // T.card ≤ k}
  let Q : SupportFamily → Set (Fin n → ℝ) := fun T ↦
    convexHull ℝ
      (Set.range fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦
        fun i : Fin n ↦ (vertex a.1 i : ℝ))
  ext x
  constructor
  · rintro ⟨hxP, hx_count⟩
    let T0 : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ 0 < x i
    let T : SupportFamily := ⟨T0, by simpa [positive_entry_count, T0] using hx_count⟩
    rcases (hbary x).1 hxP with ⟨coeff, hcoeff_nonneg, hcoeff_sum, hcoeff_eq⟩
    have hactive :
        ∀ j, coeff j ≠ 0 → ∀ i, i ∉ T0 → vertex j i = 0 := by
      intro j hcoeff_ne i hi_out
      have hxi_not_pos : ¬ 0 < x i := by
        simpa [T0] using hi_out
      have hxi_zero : x i = 0 := by
        exact le_antisymm (le_of_not_gt hxi_not_pos) ((hP_nonneg hxP) i)
      have hcoord_nonneg : ∀ l : Fin p, 0 ≤ (vertex l i : ℝ) := by
        intro l
        exact_mod_cast hvertex_nonneg i l
      have hsum_zero : ∑ l : Fin p, coeff l * (vertex l i : ℝ) = 0 := by
        have hcoord_eq := congrFun hcoeff_eq i
        simpa [Finset.sum_apply, Pi.smul_apply, hxi_zero, mul_comm, mul_left_comm, mul_assoc] using
          hcoord_eq
      have hnot_pos : ¬ 0 < (vertex j i : ℝ) := by
        intro hj_pos
        exact hcoeff_ne
          ((zero_coordinate_sum_forces_zero_weight_on_positive_vertex
            hcoeff_nonneg hcoord_nonneg hsum_zero) j hj_pos)
      have hcoord_zero_real : (vertex j i : ℝ) = 0 := by
        exact le_antisymm (le_of_not_gt hnot_pos) (hcoord_nonneg j)
      exact_mod_cast hcoord_zero_real
    have hxQ0 :
        x ∈ convexHull ℝ
          (Set.range fun a : {j : Fin p // ∀ i, i ∉ T0 → vertex j i = 0} ↦
            fun i : Fin n ↦ (vertex a.1 i : ℝ)) := by
      -- The source barycentric witness already uses only vertices supported on `T0`.
      exact mem_support_restricted_hull_of_full_barycentric
        hcoeff_nonneg hcoeff_sum hcoeff_eq hactive
    have hxQ : x ∈ Q T := by
      simpa [Q, T, T0] using hxQ0
    exact Set.mem_iUnion.2 ⟨T, hxQ⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨T, hxT⟩
    have hxT' :
        x ∈ convexHull ℝ
          (Set.range fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦
            fun i : Fin n ↦ (vertex a.1 i : ℝ)) := by
      simpa [Q] using hxT
    have hxP : x ∈ P := by
      -- Every support-restricted vertex is one of the original vertices, so its hull stays in `P`.
      rw [hP_eq]
      refine (convexHull_mono ?_) hxT'
      rintro _ ⟨a, rfl⟩
      exact ⟨a.1, rfl⟩
    have hx_zero_outside : ∀ i, i ∉ T.1 → x i = 0 := by
      -- Coordinates outside `T.1` vanish on each active vertex and hence on the whole hull.
      exact support_restricted_convex_hull_zero_outside
        T.1
        (fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦ fun i : Fin n ↦ vertex a.1 i)
        (fun a i hi ↦ a.2 i hi)
        hxT'
    have hpositive_subset : Finset.univ.filter (fun i : Fin n ↦ 0 < x i) ⊆ T.1 := by
      intro i hi
      by_contra hi_out
      have hxi_zero := hx_zero_outside i hi_out
      have hxi_pos : 0 < x i := by
        exact (Finset.mem_filter.mp hi).2
      exact (ne_of_gt hxi_pos) hxi_zero
    have hcount_le : positive_entry_count x ≤ T.1.card := by
      unfold positive_entry_count
      exact Finset.card_le_card hpositive_subset
    exact ⟨hxP, le_trans hcount_le T.2⟩

/-- Helper for Exercise 4.34: a finite union of rational polytopes is mixed integer linear
representable by taking the common integer cone to be `{0}`. -/
lemma iUnion_fintype_is_mixed_integer_linear_representable_of_rational_polytopes
    {n : ℕ}
    {ι : Type*}
    [Fintype ι]
    (Q : ι → Set (Fin n → ℝ))
    (hQ : ∀ i, (Q i).IsRationalPolytope) :
    is_mixed_integer_linear_representable (⋃ i, Q i) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let Pfin : Fin (Fintype.card ι) → Set (Fin n → ℝ) := fun i ↦ Q (e i)
  let r : Fin 1 → Fin n → ℤ := fun _ _ ↦ 0
  have hPfin : ∀ i, (Pfin i).IsRationalPolytope := by
    intro i
    simpa [Pfin] using hQ (e i)
  have hiUnion_eq : (⋃ i : Fin (Fintype.card ι), Pfin i) = ⋃ i : ι, Q i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨e i, hi⟩
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨e.symm i, by simpa [Pfin, e] using hi⟩
  have hr_zero : ∀ j, (fun i : Fin n ↦ (r j i : ℝ)) = 0 := by
    intro j
    ext i
    simp [r]
  have hcone_zero :
      integral_intcone r = ({0} : Set (Fin n → ℝ)) :=
    integral_intcone_eq_singleton_zero_of_generators_eq_zero hr_zero
  have hadd_zero :
      (⋃ i : Fin (Fintype.card ι), Pfin i) + ({0} : Set (Fin n → ℝ)) =
        ⋃ i : Fin (Fintype.card ι), Pfin i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_add.mp hx with ⟨u, hu, z, hz, hsum⟩
      have hz_zero : z = 0 := Set.mem_singleton_iff.mp hz
      have hx_eq : u = x := by
        simpa [hz_zero] using hsum
      simpa [hx_eq] using hu
    · intro hx
      exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  refine
    (mixed_integer_linear_representable_iff_union_rational_polytopes_add_integral_intcone
      (⋃ i, Q i)).2 ?_
  refine ⟨Fintype.card ι, 1, Pfin, r, hPfin, ?_⟩
  calc
    ⋃ i : ι, Q i = ⋃ i : Fin (Fintype.card ι), Pfin i := hiUnion_eq.symm
    _ = (⋃ i : Fin (Fintype.card ι), Pfin i) + ({0} : Set (Fin n → ℝ)) := hadd_zero.symm
    _ = (⋃ i : Fin (Fintype.card ι), Pfin i) + integral_intcone r := by rw [hcone_zero]

/-- Exercise 4.34 (1). The one-dimensional nonnegative polytope `[0,1]` already gives a
counterexample: the subset of points with at least one positive entry is not mixed integer linear
representable. -/
theorem interval_at_least_one_positive_entry_subset_not_mixed_integer_linear_representable :
    ¬ is_mixed_integer_linear_representable
      (points_with_at_least_k_positive_entries (Set.Icc (0 : Fin 1 → ℝ) 1) 1) := by
  rw [interval_counterexample_for_at_least_one_positive_entry]
  intro hmilr
  rcases
      (mixed_integer_linear_representable_iff_union_rational_polytopes_add_integral_intcone
        (Set.Ioc (0 : Fin 1 → ℝ) 1)).1 hmilr with
    ⟨k, t, P, r, hP_rational, hrepr⟩
  have hbounded_repr : Bornology.IsBounded ((⋃ i : Fin k, P i) + integral_intcone r) := by
    simpa [hrepr] using fin1_Ioc_unit_interval_isBounded
  have hunion_nonempty : (⋃ i : Fin k, P i).Nonempty := by
    have hone_mem : (1 : Fin 1 → ℝ) ∈ Set.Ioc (0 : Fin 1 → ℝ) 1 := by
      exact (fin1_Ioc_positive_coordinate_iff 1).2 (by simp)
    have hone_repr : (1 : Fin 1 → ℝ) ∈ (⋃ i : Fin k, P i) + integral_intcone r := by
      simpa [hrepr] using hone_mem
    rcases Set.mem_add.mp hone_repr with ⟨u, hu, z, hz, huz⟩
    exact ⟨u, hu⟩
  have hr_zero :
      ∀ j, (fun i : Fin 1 ↦ (r j i : ℝ)) = 0 :=
    integral_intcone_generators_eq_zero_of_bounded_nonempty_sum hbounded_repr hunion_nonempty
  have hcone_zero :
      integral_intcone r = ({0} : Set (Fin 1 → ℝ)) :=
    integral_intcone_eq_singleton_zero_of_generators_eq_zero hr_zero
  have hadd_zero :
      (⋃ i : Fin k, P i) + ({0} : Set (Fin 1 → ℝ)) = ⋃ i : Fin k, P i := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_add.mp hx with ⟨u, hu, z, hz, hsum⟩
      have hz_zero : z = 0 := Set.mem_singleton_iff.mp hz
      have hx_eq : u = x := by
        simpa [hz_zero] using hsum
      simpa [hx_eq] using hu
    · intro hx
      exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  have hrepr_union : Set.Ioc (0 : Fin 1 → ℝ) 1 = ⋃ i : Fin k, P i := by
    calc
      Set.Ioc (0 : Fin 1 → ℝ) 1 = (⋃ i : Fin k, P i) + integral_intcone r := hrepr
      _ = (⋃ i : Fin k, P i) + ({0} : Set (Fin 1 → ℝ)) := by rw [hcone_zero]
      _ = ⋃ i : Fin k, P i := hadd_zero
  have hclosed_ioc : IsClosed (Set.Ioc (0 : Fin 1 → ℝ) 1) := by
    simpa [hrepr_union] using isClosed_iUnion_rational_polytopes P hP_rational
  have hzero_mem : (0 : Fin 1 → ℝ) ∈ closure (Set.Ioc (0 : Fin 1 → ℝ) 1) :=
    zero_mem_closure_fin1_Ioc_unit_interval
  have hzero_not_mem : (0 : Fin 1 → ℝ) ∉ Set.Ioc (0 : Fin 1 → ℝ) 1 := by
    rw [fin1_Ioc_positive_coordinate_iff]
    simp
  have hzero_in_set : (0 : Fin 1 → ℝ) ∈ Set.Ioc (0 : Fin 1 → ℝ) 1 := by
    simpa [hclosed_ioc.closure_eq] using hzero_mem
  exact hzero_not_mem hzero_in_set

/-- Exercise 4.34 (1), existential form. Hence there exists a nonnegative polytope `P` and
`k > 0` for which the subset of points of `P` with at least `k` positive entries is not mixed
integer linear representable. -/
theorem
    exists_counterexample_for_at_least_k_positive_entry_representability :
    ∃ n : ℕ, ∃ P : Set (Fin n → ℝ), ∃ k : ℕ,
      0 < k ∧
      P ⊆ Set.Ici (0 : Fin n → ℝ) ∧
      (∃ V : Finset (Fin n → ℝ), P = convexHull ℝ (V : Set (Fin n → ℝ))) ∧
      ¬ is_mixed_integer_linear_representable
        (points_with_at_least_k_positive_entries P k) := by
  refine ⟨1, Set.Icc (0 : Fin 1 → ℝ) 1, 1, ?_, ?_, ?_, ?_⟩
  · norm_num
  · intro x hx
    exact hx.1
  · refine ⟨{(0 : Fin 1 → ℝ), 1}, ?_⟩
    -- The unit interval is the segment between its two endpoints.
    have hpair :
        Set.Icc (0 : Fin 1 → ℝ) 1 =
          convexHull ℝ ({(0 : Fin 1 → ℝ), 1} : Set (Fin 1 → ℝ)) := by
      rw [convexHull_pair, segment_eq_image_lineMap]
      ext x
      constructor
      · intro hx
        refine ⟨x 0, ⟨hx.1 0, hx.2 0⟩, ?_⟩
        ext i
        fin_cases i
        simp [AffineMap.lineMap_apply]
      · rintro ⟨t, ht, rfl⟩
        rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
        constructor
        · intro i
          fin_cases i
          simpa [AffineMap.lineMap_apply] using ht.1
        · intro i
          fin_cases i
          simpa [AffineMap.lineMap_apply] using ht.2
    simpa [Finset.coe_insert, Finset.coe_singleton] using hpair
  · simpa using interval_at_least_one_positive_entry_subset_not_mixed_integer_linear_representable

/-- Exercise 4.34 (2). For a nonnegative rational polytope `P`, the subset of points of `P` with
at most `k` positive entries is mixed integer linear representable. -/
theorem subset_with_at_most_k_positive_entries_is_mixed_integer_linear_representable
    {n : ℕ}
    (P : Set (Fin n → ℝ))
    (k : ℕ)
    (hP_nonneg : P ⊆ Set.Ici (0 : Fin n → ℝ))
    (hP_rational : P.IsRationalPolytope) :
    is_mixed_integer_linear_representable
      (points_with_at_most_k_positive_entries P k) := by
  classical
  rcases polytope_barycentric_data_with_coordinate_bounds P hP_rational hP_nonneg with
    ⟨p, vertex, M, hbounds, hP_eq, hbary⟩
  let SupportFamily : Type := {T : Finset (Fin n) // T.card ≤ k}
  let Q : SupportFamily → Set (Fin n → ℝ) := fun T ↦
    convexHull ℝ
      (Set.range fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦
        fun i : Fin n ↦ (vertex a.1 i : ℝ))
  have hdecomp : points_with_at_most_k_positive_entries P k = ⋃ T : SupportFamily, Q T := by
    -- Route correction: follow the source proof by fixing one vertex family for `P`, then
    -- decompose the at-most-`k` set by the support of its positive coordinates.
    simpa [SupportFamily, Q] using
      points_with_at_most_k_positive_entries_eq_iUnion_support_restricted_hulls
        P
        k
        vertex
        hP_nonneg
        (fun i j ↦ (hbounds i j).1)
        hP_eq
        hbary
  have hQ_rational : ∀ T : SupportFamily, (Q T).IsRationalPolytope := by
    intro T
    -- Each support-restricted hull is still a convex hull of finitely many rational vertices.
    simpa [Q] using
      isRationalPolytope_convexHull_range_of_fintype
        (vertex := fun a : {j : Fin p // ∀ i, i ∉ T.1 → vertex j i = 0} ↦
          fun i : Fin n ↦ vertex a.1 i)
  rw [hdecomp]
  exact iUnion_fintype_is_mixed_integer_linear_representable_of_rational_polytopes Q hQ_rational
