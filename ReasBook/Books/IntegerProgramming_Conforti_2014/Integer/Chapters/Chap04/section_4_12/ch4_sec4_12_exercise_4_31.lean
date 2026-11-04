/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_46

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * source-facing parity optimizer owner reused from `ch3_sec3_18_exercise_3_4`:
--   `exercise_3_4_even_parity_optimizer`
-- * source-facing parity/odd-set owners reused from `ch4_sec4_9_theorem_4_46`:
--   `is_zero_one_vector`, `one_coordinate_count`, `even_zero_one_vectors`, `odd_subset`,
--   `odd_set_inequality`, `odd_set_polyhedron`
-- * core/canonical owner reused from mathlib/project for linear evaluation: `dotProduct` / `⬝ᵥ`
-- * source-facing exercise-specific owners kept here: the LP-duality predicates

/-- The dual objective value
`∑_{S ∈ 𝒮} (|S| - 1) y_S + ∑_{i ∈ N} z_i`. -/
def exercise_4_31_dual_objective {n : ℕ}
    (y : odd_subset n → ℝ) (z : Fin n → ℝ) : ℝ :=
  (∑ S, ((S.1.card : ℝ) - 1) * y S) + ∑ i, z i

/-- Dual feasibility for the odd-set linear description:
`y ≥ 0`, `z ≥ 0`, and
`∑_{S ∈ 𝒮, i ∈ S} y_S - ∑_{S ∈ 𝒮, i ∉ S} y_S + z_i ≥ c_i` for every `i`. -/
def exercise_4_31_dual_feasible {n : ℕ}
    (c : Fin n → ℝ) (y : odd_subset n → ℝ) (z : Fin n → ℝ) : Prop :=
  (∀ S, 0 ≤ y S) ∧
    (∀ i, 0 ≤ z i) ∧
      ∀ i,
        c i ≤ (∑ S, (if i ∈ S.1 then (1 : ℝ) else -1) * y S) + z i

/-- Helper for Exercise 4.31: negating the cost vector negates the dot product. -/
lemma exercise_4_31_neg_dotProduct {n : ℕ} (c x : Fin n → ℝ) :
    (-c) ⬝ᵥ x = -(c ⬝ᵥ x) := by
  -- Rewrite the dot product coordinatewise and pull the negation outside the finite sum.
  unfold dotProduct
  simp [Pi.neg_apply, Finset.sum_neg_distrib]

/-- Helper for Exercise 4.31: the Chapter 3 optimizer value for `-c` is the positive-part sum,
with the minimum-absolute-cost correction in the odd case. -/
lemma exercise_4_31_optimizerValue
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
    c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j =
      if Even P.card then P.sum c else P.sum c - |c j| := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
  let xopt := exercise_3_4_even_parity_optimizer (-c) j
  have hDotNeg :
      (-c) ⬝ᵥ xopt = Finset.sum (exercise_3_4_even_parity_indices (-c) j) (-c) := by
    -- Rewrite the Chapter 3 optimizer objective as the sum over its `1`-coordinates.
    rw [dotProduct_eq_sum_one_coordinates_of_mem_zero_one_cube (-c)
        (exercise_3_4_even_parity_optimizer_mem_zero_one_cube (-c) j),
      exercise_3_4_even_parity_optimizer_one_coordinates (-c) j]
  have hIndexSum :
      Finset.sum (exercise_3_4_even_parity_indices (-c) j) (-c) =
        if Even P.card then -(P.sum c) else -(P.sum c) + |c j| := by
    -- The negative-cost support for `-c` is exactly the positive-cost support for `c`.
    simpa [P, Finset.sum_neg_distrib, abs_neg] using
      exercise_3_4_even_parity_indices_sum (-c) j
  have hNegDot : (-c) ⬝ᵥ xopt = -(c ⬝ᵥ xopt) := by
    -- This is the sign-change bridge from the Chapter 3 minimization statement.
    exact exercise_4_31_neg_dotProduct c xopt
  have hOptNeg :
      (-c) ⬝ᵥ xopt = if Even P.card then -(P.sum c) else -(P.sum c) + |c j| := by
    rw [hDotNeg]
    exact hIndexSum
  by_cases hEvenP : Even P.card
  · -- In the even branch the positive coordinates are taken without a parity penalty.
    have hneg : (-c) ⬝ᵥ xopt = -(P.sum c) := by
      simpa [hEvenP] using hOptNeg
    have hneg' : -(c ⬝ᵥ xopt) = -(P.sum c) := by
      simpa [hNegDot] using hneg
    have hEq : c ⬝ᵥ xopt = P.sum c := by
      linarith
    simpa [P, xopt, hEvenP] using hEq
  · -- In the odd branch exactly one minimum-absolute-cost toggle is lost.
    have hneg : (-c) ⬝ᵥ xopt = -(P.sum c) + |c j| := by
      simpa [hEvenP] using hOptNeg
    have hneg' : -(c ⬝ᵥ xopt) = -(P.sum c) + |c j| := by
      simpa [hNegDot] using hneg
    have hEq : c ⬝ᵥ xopt = P.sum c - |c j| := by
      linarith
    simpa [P, xopt, hEvenP] using hEq

/-- Helper for Exercise 4.31: the even-cardinality branch has a dual certificate supported only by
the nonnegative `z`-variables on the positive coordinates. -/
lemma exercise_4_31_evenDualCertificate
    {n : ℕ} (c : Fin n → ℝ) :
    ∃ y : odd_subset n → ℝ,
      ∃ z : Fin n → ℝ,
        exercise_4_31_dual_feasible c y z ∧
          exercise_4_31_dual_objective y z =
            (Finset.univ.filter fun i : Fin n ↦ 0 < c i).sum c := by
  classical
  let y : odd_subset n → ℝ := fun _ ↦ 0
  let z : Fin n → ℝ := fun i ↦ if 0 < c i then c i else 0
  refine ⟨y, z, ?_, ?_⟩
  · -- The zero `y`-vector and positive-part `z`-vector satisfy the dual inequalities directly.
    constructor
    · intro S
      simp [y]
    constructor
    · intro i
      by_cases hci : 0 < c i
      · simp [z, hci, le_of_lt hci]
      · simp [z, hci]
    · intro i
      by_cases hci : 0 < c i
      · simp [y, z, hci]
      · have hci' : c i ≤ 0 := le_of_not_gt hci
        simp [y, z, hci, hci']
  · -- The objective is exactly the sum of the positive coordinates of `c`.
    unfold exercise_4_31_dual_objective
    simp [y, z, Finset.sum_filter]

/-- Helper for Exercise 4.31: in the odd-cardinality branch, one odd-set row with weight `|c j|`
and the remaining positive slack in `z` form a dual certificate. -/
lemma exercise_4_31_oddDualCertificate
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n)
    (hj : ∀ i, |c j| ≤ |c i|)
    (hOddP : Odd ((Finset.univ.filter fun i : Fin n ↦ 0 < c i).card)) :
    ∃ y : odd_subset n → ℝ,
      ∃ z : Fin n → ℝ,
        exercise_4_31_dual_feasible c y z ∧
          exercise_4_31_dual_objective y z =
            (Finset.univ.filter fun i : Fin n ↦ 0 < c i).sum c - |c j| := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
  have hPodd : Odd P.card := by
    simpa [P] using hOddP
  let S0 : odd_subset n := ⟨P, hPodd⟩
  let y : odd_subset n → ℝ := fun S ↦ if S = S0 then |c j| else 0
  let z : Fin n → ℝ := fun i ↦ if i ∈ P then c i - |c j| else 0
  refine ⟨y, z, ?_, ?_⟩
  · -- The single active odd-set row handles the parity correction, and `z` absorbs the rest.
    constructor
    · intro S
      by_cases hS : S = S0
      · simp [y, hS]
      · simp [y, hS]
    constructor
    · intro i
      by_cases hi : i ∈ P
      · have hci : 0 < c i := (Finset.mem_filter.mp hi).2
        have hji : |c j| ≤ c i := by
          calc
            |c j| ≤ |c i| := hj i
            _ = c i := abs_of_pos hci
        have hz : 0 ≤ c i - |c j| := by
          linarith
        simp [z, hi, hz]
      · simp [z, hi]
    · intro i
      by_cases hi : i ∈ P
      · -- On the positive support, the active odd-set row contributes `|c j|`.
        have hrow :
            (∑ S : odd_subset n, (if i ∈ S.1 then (1 : ℝ) else -1) * y S) = |c j| := by
          rw [Finset.sum_eq_single_of_mem S0 (Finset.mem_univ S0)]
          · simp [y, S0, hi]
          · intro S _ hne
            simp [y, hne]
        rw [hrow]
        simp [z, hi]
      · -- Outside the positive support, the active odd-set row contributes `-|c j|`.
        have hci_nonpos : c i ≤ 0 := by
          exact not_lt.mp fun hci ↦ hi (by simpa [P] using hci)
        have hji : |c j| ≤ -c i := by
          calc
            |c j| ≤ |c i| := hj i
            _ = -c i := abs_of_nonpos hci_nonpos
        have hci : c i ≤ -|c j| := by
          linarith
        have hrow :
            (∑ S : odd_subset n, (if i ∈ S.1 then (1 : ℝ) else -1) * y S) = -|c j| := by
          rw [Finset.sum_eq_single_of_mem S0 (Finset.mem_univ S0)]
          · simp [y, S0, hi]
          · intro S _ hne
            simp [y, hne]
        rw [hrow]
        simpa [z, hi] using hci
  · -- Evaluate the unique active odd-set term and the positive-support `z`-sum separately.
    unfold exercise_4_31_dual_objective
    have hySum :
        (∑ S : odd_subset n, ((S.1.card : ℝ) - 1) * y S) =
          ((P.card : ℝ) - 1) * |c j| := by
      rw [Finset.sum_eq_single_of_mem S0 (Finset.mem_univ S0)]
      · simp [y, S0]
      · intro S _ hne
        simp [y, hne]
    have hzSum :
        (∑ i, z i) = P.sum c - (P.card : ℝ) * |c j| := by
      have hzFilter : (∑ i, z i) = Finset.sum P (fun i ↦ c i - |c j|) := by
        simp [z]
      calc
        (∑ i, z i) = Finset.sum P (fun i ↦ c i - |c j|) := hzFilter
        _ = P.sum c - Finset.sum P (fun _ : Fin n ↦ |c j|) := by
          rw [Finset.sum_sub_distrib]
        _ = P.sum c - (P.card : ℝ) * |c j| := by
          simp
    calc
      (∑ S : odd_subset n, ((S.1.card : ℝ) - 1) * y S) + ∑ i, z i =
          P.sum c - |c j| := by
        rw [hySum, hzSum]
        ring
      _ = (Finset.univ.filter fun i : Fin n ↦ 0 < c i).sum c - |c j| := by
        simp [P]

/-- Characterization for Exercise 4.31: choosing all positive-cost coordinates and,
when their number is odd,
toggling a coordinate of minimum absolute cost yields an optimal solution of
`max {c x | x ∈ S_n^even}`; this is the Chapter 3 parity optimizer applied to `-c`. -/
theorem exercise_4_31_even_maximizer_spec
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) (hj : ∀ i, |c j| ≤ |c i|) :
    exercise_3_4_even_parity_optimizer (-c) j ∈ even_zero_one_vectors n ∧
      ∀ x ∈ even_zero_one_vectors n,
        c ⬝ᵥ x ≤ c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j := by
  classical
  let xopt := exercise_3_4_even_parity_optimizer (-c) j
  have hjNeg : ∀ i, |(-c) j| ≤ |(-c) i| := by
    -- The minimum-absolute-cost hypothesis is unchanged after negating the objective.
    simpa [Pi.neg_apply, abs_neg] using hj
  have hSpec := even_parity_zero_one_optimizer_spec (-c) j hjNeg
  dsimp only at hSpec
  rcases hSpec with ⟨hxoptS, hopt⟩
  refine ⟨?_, ?_⟩
  · -- Transport the Chapter 3 feasible-set description into `even_zero_one_vectors`.
    rcases hxoptS with ⟨hxCube, hxEven⟩
    constructor
    · exact (mem_zero_one_cube_iff.mp hxCube)
    · simpa [one_coordinate_count] using hxEven
  · intro x hx
    rcases hx with ⟨hxZeroOne, hxEven⟩
    have hxS :
        x ∈ {x ∈ zero_one_cube n |
          Even ((Finset.univ.filter fun i : Fin n ↦ x i = 1).card)} := by
      -- Translate the Exercise 4.31 feasible set back to the Chapter 3 formulation.
      refine ⟨(mem_zero_one_cube_iff.mpr hxZeroOne), ?_⟩
      simpa [one_coordinate_count] using hxEven
    have hoptx : (-c) ⬝ᵥ xopt ≤ (-c) ⬝ᵥ x := hopt x hxS
    have hNegOpt : (-c) ⬝ᵥ xopt = -(c ⬝ᵥ xopt) := by
      exact exercise_4_31_neg_dotProduct c xopt
    have hNegX : (-c) ⬝ᵥ x = -(c ⬝ᵥ x) := exercise_4_31_neg_dotProduct c x
    linarith

/-- Exercise 4.31 (2): for the optimal solution `x*` characterized above, the dual of the odd-set
linear description has a feasible solution `(y*, z*)` whose value is `c x*`. -/
theorem exercise_4_31_exists_dual_feasible_of_even_maximizer
    {n : ℕ} (c : Fin n → ℝ) (j : Fin n) (hj : ∀ i, |c j| ≤ |c i|) :
    ∃ y : odd_subset n → ℝ,
      ∃ z : Fin n → ℝ,
        exercise_4_31_dual_feasible c y z ∧
          exercise_4_31_dual_objective y z =
            c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
  have hValue :
      c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j =
        if Even P.card then P.sum c else P.sum c - |c j| := by
    simpa [P] using exercise_4_31_optimizerValue c j
  by_cases hEvenP : Even P.card
  · -- In the even branch, the positive-part `z`-vector already attains the optimizer value.
    rcases exercise_4_31_evenDualCertificate c with ⟨y, z, hFeas, hObj⟩
    refine ⟨y, z, hFeas, ?_⟩
    calc
      exercise_4_31_dual_objective y z = P.sum c := by
        simpa [P] using hObj
      _ = c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j := by
        simpa [hEvenP] using hValue.symm
  · -- In the odd branch, activate the unique odd-set row indexed by the positive support.
    have hOddP : Odd P.card := Nat.not_even_iff_odd.mp hEvenP
    have hOddP' : Odd ((Finset.univ.filter fun i : Fin n ↦ 0 < c i).card) := by
      simpa [P] using hOddP
    rcases exercise_4_31_oddDualCertificate c j hj hOddP' with ⟨y, z, hFeas, hObj⟩
    refine ⟨y, z, hFeas, ?_⟩
    calc
      exercise_4_31_dual_objective y z = P.sum c - |c j| := by
        simpa [P] using hObj
      _ = c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j := by
        simpa [hEvenP] using hValue.symm
