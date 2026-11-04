/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

open scoped BigOperators

-- Semantic search tooling was unavailable in this environment; the API choice here uses standard
-- `Fin`-indexed vectors, support counting by `Finset.filter`, and `convexHull` from mathlib.

/-- Counts the number of nonzero coordinates of a `Fin`-indexed real vector. -/
noncomputable def nonzero_coordinate_count {k : ℕ} (y : Fin k → ℝ) : ℕ :=
  (Finset.univ.filter fun j : Fin k ↦ y j ≠ 0).card

/-- The intended feasible set: each variable lies between `0` and its upper bound, and at most
`ℓ` variables are nonzero. -/
def bounded_nonzero_cardinality_feasible {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ) (y : Fin k → ℝ) :
    Prop :=
  (∀ j, 0 ≤ y j ∧ y j ≤ u j) ∧ nonzero_coordinate_count y ≤ ℓ

/-- The standard binary-activation mixed-integer formulation for imposing that at most `ℓ`
bounded continuous variables are nonzero. -/
def bounded_nonzero_cardinality_milp {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ) (x y : Fin k → ℝ) :
    Prop :=
  (∀ j, x j = 0 ∨ x j = 1) ∧
    (∀ j, 0 ≤ y j ∧ y j ≤ u j * x j) ∧
    (∑ j, x j) ≤ (ℓ : ℝ)

/-- The linear programming relaxation of the binary-activation formulation. -/
def bounded_nonzero_cardinality_relaxation {k : ℕ} (u : Fin k → ℝ) (ℓ : ℕ)
    (x y : Fin k → ℝ) : Prop :=
  (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
    (∀ j, 0 ≤ y j ∧ y j ≤ u j * x j) ∧
    (∑ j, x j) ≤ (ℓ : ℝ)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: implication
between coordinate supports gives the corresponding cardinality inequality. -/
lemma nonzero_coordinate_count_le_of_imp {k : ℕ} {x y : Fin k → ℝ}
    (hxy : ∀ j, x j ≠ 0 → y j ≠ 0) :
    nonzero_coordinate_count x ≤ nonzero_coordinate_count y := by
  -- Compare the two filtered universal finsets coordinate by coordinate.
  unfold nonzero_coordinate_count
  apply Finset.card_le_card
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hxy j

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the sum of a
binary real vector is the cardinality of its support. -/
lemma sum_eq_nonzero_coordinate_count_of_binary {k : ℕ} {x : Fin k → ℝ}
    (hx : ∀ j, x j = 0 ∨ x j = 1) :
    (∑ j, x j) = (nonzero_coordinate_count x : ℝ) := by
  -- Replace each binary coordinate by the indicator of its nonzero support.
  unfold nonzero_coordinate_count
  calc
    (∑ j, x j) = ∑ j : Fin k, if x j ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rcases hx j with hxj | hxj
      · simp [hxj]
      · simp [hxj]
    _ = ((Finset.univ.filter fun j : Fin k ↦ x j ≠ 0).card : ℝ) :=
      (Finset.natCast_card_filter (fun j : Fin k ↦ x j ≠ 0) Finset.univ).symm

/-- Part (1) of Exercise 2.32: the binary-activation constraints give an exact mixed-integer
formulation for the bounded vectors with at most `ℓ` nonzero coordinates. -/
theorem exercise_2_32 {k : ℕ} (u : Fin k → ℝ) (hu : ∀ j, 0 ≤ u j) (ℓ : ℕ) (y : Fin k → ℝ) :
    bounded_nonzero_cardinality_feasible u ℓ y ↔
      ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_milp u ℓ x y := by
  constructor
  · intro hy
    -- Activate precisely the nonzero coordinates of `y`.
    let x : Fin k → ℝ := fun j ↦ if y j = 0 then 0 else 1
    refine ⟨x, ?_, ?_, ?_⟩
    · intro j
      by_cases hyj : y j = 0
      · left
        simp [x, hyj]
      · right
        simp [x, hyj]
    · intro j
      refine ⟨hy.1 j |>.1, ?_⟩
      by_cases hyj : y j = 0
      · simp [x, hyj]
      · simpa [x, hyj] using hy.1 j |>.2
    · rw [sum_eq_nonzero_coordinate_count_of_binary]
      · have hxCount : nonzero_coordinate_count x = nonzero_coordinate_count y := by
          unfold nonzero_coordinate_count
          congr 1
          ext j
          simp [x]
        rw [hxCount]
        exact_mod_cast hy.2
      · intro j
        by_cases hyj : y j = 0
        · left
          simp [x, hyj]
        · right
          simp [x, hyj]
  · rintro ⟨x, hxBinary, hyBounds, hxSum⟩
    -- A nonzero `y`-coordinate forces its binary activator to be one.
    have hySupport : nonzero_coordinate_count y ≤ nonzero_coordinate_count x := by
      apply nonzero_coordinate_count_le_of_imp
      intro j hyj
      rcases hxBinary j with hxj | hxj
      · have hyjZero : y j = 0 := by
          have hyjNonpos : y j ≤ 0 := by
            simpa [hxj] using hyBounds j |>.2
          exact le_antisymm hyjNonpos (hyBounds j |>.1)
        exact (hyj hyjZero).elim
      · simp [hxj]
    have hxCount : nonzero_coordinate_count x ≤ ℓ := by
      have hxCountReal : (nonzero_coordinate_count x : ℝ) ≤ (ℓ : ℝ) := by
        rw [← sum_eq_nonzero_coordinate_count_of_binary hxBinary]
        exact hxSum
      exact_mod_cast hxCountReal
    refine ⟨?_, hySupport.trans hxCount⟩
    intro j
    refine ⟨hyBounds j |>.1, ?_⟩
    rcases hxBinary j with hxj | hxj
    · have hyjZero : y j = 0 := by
        have hyjNonpos : y j ≤ 0 := by
          simpa [hxj] using hyBounds j |>.2
        exact le_antisymm hyjNonpos (hyBounds j |>.1)
      simpa [hyjZero] using hu j
    · simpa [hxj] using hyBounds j |>.2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the normalized
cardinality-constrained points in the unit box. -/
def unitCardinalityFeasible {k : ℕ} (ℓ : ℕ) : Set (Fin k → ℝ) :=
  {z | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ nonzero_coordinate_count z ≤ ℓ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the normalized
continuous relaxation in the unit box. -/
def unitCardinalityRelaxation {k : ℕ} (ℓ : ℕ) : Set (Fin k → ℝ) :=
  {z | (∀ j, 0 ≤ z j ∧ z j ≤ 1) ∧ (∑ j, z j) ≤ (ℓ : ℝ)}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: coordinatewise
multiplication by the upper-bound vector, as a linear map. -/
noncomputable def coordinatewiseScale {k : ℕ} (u : Fin k → ℝ) :
    (Fin k → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi fun j ↦ (LinearMap.proj j).smulRight (u j)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: evaluation of
coordinatewise scaling. -/
@[simp] lemma coordinatewiseScale_apply {k : ℕ} (u z : Fin k → ℝ) (j : Fin k) :
    coordinatewiseScale u z j = u j * z j := by
  -- Unfold the canonical `LinearMap.pi` construction and commute scalar multiplication.
  simp [coordinatewiseScale, mul_comm]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: bounded feasible
vectors are exactly coordinatewise scalings of normalized feasible vectors. -/
lemma feasible_iff_exists_unitScaledPoint {k : ℕ} (u : Fin k → ℝ) (hu : ∀ j, 0 ≤ u j)
    (ℓ : ℕ) (y : Fin k → ℝ) :
    bounded_nonzero_cardinality_feasible u ℓ y ↔
      ∃ z : Fin k → ℝ, z ∈ unitCardinalityFeasible ℓ ∧ coordinatewiseScale u z = y := by
  constructor
  · intro hy
    -- Divide by positive upper bounds, and use zero at coordinates whose upper bound vanishes.
    let z : Fin k → ℝ := fun j ↦ if u j = 0 then 0 else y j / u j
    refine ⟨z, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j
        by_cases huj : u j = 0
        · simp [z, huj]
        · have hujPos : 0 < u j := lt_of_le_of_ne (hu j) (Ne.symm huj)
          constructor
          · simp [z, huj, div_nonneg (hy.1 j |>.1) hujPos.le]
          · simp only [z, huj, ↓reduceIte]
            rw [div_le_iff₀ hujPos]
            simpa using hy.1 j |>.2
      · refine (nonzero_coordinate_count_le_of_imp ?_).trans hy.2
        intro j hzj
        by_cases huj : u j = 0
        · simp [z, huj] at hzj
        · intro hyj
          simp [z, huj, hyj] at hzj
    · ext j
      by_cases huj : u j = 0
      · have hyj : y j = 0 := by
          have hyjNonpos : y j ≤ 0 := by
            simpa [huj] using hy.1 j |>.2
          exact le_antisymm hyjNonpos (hy.1 j |>.1)
        simp [z, huj, hyj]
      · simp only [coordinatewiseScale_apply, z, huj, ↓reduceIte]
        field_simp
  · rintro ⟨z, hz, rfl⟩
    -- Scaling preserves box bounds and can only delete support coordinates.
    refine ⟨?_, ?_⟩
    · intro j
      constructor
      · rw [coordinatewiseScale_apply]
        exact mul_nonneg (hu j) (hz.1 j |>.1)
      · rw [coordinatewiseScale_apply]
        nlinarith [hu j, hz.1 j |>.2]
    · refine (nonzero_coordinate_count_le_of_imp ?_).trans hz.2
      intro j hj hzj
      simp [hzj] at hj

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the projection of
the activation relaxation is the coordinatewise scaling of the normalized relaxation. -/
lemma relaxationProjection_iff_exists_unitScaledPoint {k : ℕ} (u : Fin k → ℝ)
    (hu : ∀ j, 0 ≤ u j) (ℓ : ℕ) (y : Fin k → ℝ) :
    (∃ x : Fin k → ℝ, bounded_nonzero_cardinality_relaxation u ℓ x y) ↔
      ∃ z : Fin k → ℝ, z ∈ unitCardinalityRelaxation ℓ ∧ coordinatewiseScale u z = y := by
  constructor
  · rintro ⟨x, hxBox, hyBounds, hxSum⟩
    -- Normalize `y`; its normalized coordinates are bounded above by the activation vector.
    let z : Fin k → ℝ := fun j ↦ if u j = 0 then 0 else y j / u j
    refine ⟨z, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j
        by_cases huj : u j = 0
        · simp [z, huj]
        · have hujPos : 0 < u j := lt_of_le_of_ne (hu j) (Ne.symm huj)
          constructor
          · simp [z, huj, div_nonneg (hyBounds j |>.1) hujPos.le]
          · simp only [z, huj, ↓reduceIte]
            rw [div_le_iff₀ hujPos]
            simpa [mul_comm] using
              (hyBounds j |>.2).trans (mul_le_mul_of_nonneg_left (hxBox j |>.2) hujPos.le)
      · calc
          (∑ j, z j) ≤ ∑ j, x j := by
            apply Finset.sum_le_sum
            intro j _
            by_cases huj : u j = 0
            · simpa [z, huj] using hxBox j |>.1
            · have hujPos : 0 < u j := lt_of_le_of_ne (hu j) (Ne.symm huj)
              simp only [z, huj, ↓reduceIte]
              rw [div_le_iff₀ hujPos]
              simpa [mul_comm] using hyBounds j |>.2
          _ ≤ (ℓ : ℝ) := hxSum
    · ext j
      by_cases huj : u j = 0
      · have hyj : y j = 0 := by
          have hyjNonpos : y j ≤ 0 := by
            simpa [huj] using hyBounds j |>.2
          exact le_antisymm hyjNonpos (hyBounds j |>.1)
        simp [z, huj, hyj]
      · simp only [coordinatewiseScale_apply, z, huj, ↓reduceIte]
        field_simp
  · rintro ⟨z, hz, rfl⟩
    -- The normalized point itself supplies a valid continuous activation vector.
    refine ⟨z, hz.1, ?_, hz.2⟩
    intro j
    rw [coordinatewiseScale_apply]
    exact ⟨mul_nonneg (hu j) (hz.1 j |>.1), le_rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: on a finite set,
the sum of binary coordinates is the cardinality of their nonzero coordinates. -/
lemma finset_sum_eq_card_filter_of_binary {k : ℕ} (s : Finset (Fin k)) (z : Fin k → ℝ)
    (hz : ∀ j ∈ s, z j = 0 ∨ z j = 1) :
    (∑ j ∈ s, z j) = ((s.filter fun j ↦ z j ≠ 0).card : ℝ) := by
  -- Rewrite each summand as its Boolean support indicator.
  calc
    (∑ j ∈ s, z j) = ∑ j ∈ s, if z j ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rcases hz j hj with hzj | hzj
      · simp [hzj]
      · simp [hzj]
    _ = ((s.filter fun j ↦ z j ≠ 0).card : ℝ) :=
      (Finset.natCast_card_filter (fun j : Fin k ↦ z j ≠ 0) s).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: a vector in the
unit box has total mass at most the cardinality of its support. -/
lemma sum_le_nonzero_coordinate_count_of_unitBox {k : ℕ} {z : Fin k → ℝ}
    (hz : ∀ j, 0 ≤ z j ∧ z j ≤ 1) :
    (∑ j, z j) ≤ (nonzero_coordinate_count z : ℝ) := by
  -- Bound every nonzero coordinate by one and every zero coordinate exactly by zero.
  unfold nonzero_coordinate_count
  calc
    (∑ j, z j) ≤ ∑ j : Fin k, if z j ≠ 0 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hzj : z j = 0
      · simp [hzj]
      · simpa [hzj] using hz j |>.2
    _ = ((Finset.univ.filter fun j : Fin k ↦ z j ≠ 0).card : ℝ) :=
      (Finset.natCast_card_filter (fun j : Fin k ↦ z j ≠ 0) Finset.univ).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: every normalized
cardinality-feasible point satisfies the normalized relaxation. -/
lemma unitCardinalityFeasible_subset_relaxation {k : ℕ} (ℓ : ℕ) :
    unitCardinalityFeasible (k := k) ℓ ⊆ unitCardinalityRelaxation ℓ := by
  intro z hz
  -- Combine the unit-box support estimate with the assumed support-cardinality bound.
  refine ⟨hz.1, ?_⟩
  calc
    (∑ j, z j) ≤ (nonzero_coordinate_count z : ℝ) :=
      sum_le_nonzero_coordinate_count_of_unitBox hz.1
    _ ≤ (ℓ : ℝ) := by exact_mod_cast hz.2

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the normalized
relaxation is convex. -/
lemma unitCardinalityRelaxation_convex {k : ℕ} (ℓ : ℕ) :
    Convex ℝ (unitCardinalityRelaxation (k := k) ℓ) := by
  rintro x hx y hy a b ha hb hab
  -- Check the box constraints coordinatewise and the cardinality inequality by linearity.
  refine ⟨?_, ?_⟩
  · intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 j |>.1)) (mul_nonneg hb (hy.1 j |>.1))
    · nlinarith [hx.1 j |>.2, hy.1 j |>.2]
  · calc
      (∑ j, (a • x + b • y) j) = a * (∑ j, x j) + b * (∑ j, y j) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ a * (ℓ : ℝ) + b * (ℓ : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = (ℓ : ℝ) := by
        rw [← add_mul, hab, one_mul]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the normalized
relaxation is compact. -/
lemma unitCardinalityRelaxation_isCompact {k : ℕ} (ℓ : ℕ) :
    IsCompact (unitCardinalityRelaxation (k := k) ℓ) := by
  have hsum : Continuous (fun z : Fin k → ℝ ↦ ∑ j, z j) := by
    fun_prop
  have hset :
      unitCardinalityRelaxation (k := k) ℓ =
        Set.Icc (0 : Fin k → ℝ) 1 ∩ {z | (∑ j, z j) ≤ (ℓ : ℝ)} := by
    ext z
    constructor
    · intro hz
      refine ⟨?_, hz.2⟩
      constructor
      · intro j
        exact hz.1 j |>.1
      · intro j
        exact hz.1 j |>.2
    · rintro ⟨hzBox, hzSum⟩
      refine ⟨?_, hzSum⟩
      intro j
      exact ⟨hzBox.1 j, hzBox.2 j⟩
  -- Intersect the compact unit box with the closed total-mass halfspace.
  rw [hset]
  exact isCompact_Icc.inter_right (isClosed_le hsum continuous_const)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: an extreme point
with slack in the total-mass constraint has binary coordinates. -/
lemma unitRelaxationExtremePoint_coordinate_binary_of_sum_lt {k : ℕ} (ℓ : ℕ)
    {z : Fin k → ℝ} (hzExtreme : z ∈ (unitCardinalityRelaxation ℓ).extremePoints ℝ)
    (i : Fin k) (hsum : (∑ j, z j) < (ℓ : ℝ)) : z i = 0 ∨ z i = 1 := by
  classical
  have hz : z ∈ unitCardinalityRelaxation ℓ := extremePoints_subset hzExtreme
  by_contra hi
  have hiZero : z i ≠ 0 := fun h ↦ hi (Or.inl h)
  have hiOne : z i ≠ 1 := fun h ↦ hi (Or.inr h)
  have hiPos : 0 < z i := lt_of_le_of_ne (hz.1 i |>.1) (Ne.symm hiZero)
  have hiLt : z i < 1 := lt_of_le_of_ne (hz.1 i |>.2) hiOne
  -- With slack in the sum inequality, perturb just the fractional coordinate.
  let ε : ℝ := min (z i) (min (1 - z i) ((ℓ : ℝ) - ∑ j, z j)) / 2
  have hεPos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεLeValue : ε ≤ z i := by
    dsimp [ε]
    nlinarith [min_le_left (z i) (min (1 - z i) ((ℓ : ℝ) - ∑ j, z j))]
  have hεLeGap : ε ≤ 1 - z i := by
    dsimp [ε]
    nlinarith [min_le_right (z i) (min (1 - z i) ((ℓ : ℝ) - ∑ j, z j)),
      min_le_left (1 - z i) ((ℓ : ℝ) - ∑ j, z j)]
  have hεLeSlack : ε ≤ (ℓ : ℝ) - ∑ j, z j := by
    dsimp [ε]
    nlinarith [min_le_right (z i) (min (1 - z i) ((ℓ : ℝ) - ∑ j, z j)),
      min_le_right (1 - z i) ((ℓ : ℝ) - ∑ j, z j)]
  let v : Fin k → ℝ := Pi.single i ε
  have hminus : z - v ∈ unitCardinalityRelaxation ℓ := by
    refine ⟨?_, ?_⟩
    · intro q
      by_cases hqi : q = i
      · subst q
        simp [v]
        constructor
        · linarith
        · linarith
      · simpa [v, hqi] using hz.1 q
    · calc
        (∑ q, (z - v) q) = (∑ q, z q) - ε := by
          simp [v, Finset.sum_sub_distrib]
        _ ≤ (ℓ : ℝ) := by linarith [hz.2]
  have hplus : z + v ∈ unitCardinalityRelaxation ℓ := by
    refine ⟨?_, ?_⟩
    · intro q
      by_cases hqi : q = i
      · subst q
        simp [v]
        constructor
        · linarith
        · linarith
      · simpa [v, hqi] using hz.1 q
    · calc
        (∑ q, (z + v) q) = (∑ q, z q) + ε := by
          simp [v, Finset.sum_add_distrib]
        _ ≤ (ℓ : ℝ) := by linarith
  have hminusNe : z - v ≠ z := by
    intro heq
    have hiEq := congrFun heq i
    simp [v, ne_of_gt hεPos] at hiEq
  exact hminusNe (hzExtreme.2 hminus hplus (mem_openSegment_sub_add z v))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: a fractional
coordinate on an integral total-mass hyperplane forces a second fractional coordinate. -/
lemma unitBox_sum_eq_nat_has_second_fractional_coordinate {k : ℕ} (ℓ : ℕ)
    {z : Fin k → ℝ} (i : Fin k) (hzBox : ∀ j, 0 ≤ z j ∧ z j ≤ 1)
    (hiZero : z i ≠ 0) (hiOne : z i ≠ 1) (hsumEq : (∑ j, z j) = (ℓ : ℝ)) :
    ∃ j, j ≠ i ∧ z j ≠ 0 ∧ z j ≠ 1 := by
  classical
  by_contra hNoJ
  have hiPos : 0 < z i := lt_of_le_of_ne (hzBox i |>.1) (Ne.symm hiZero)
  have hiLt : z i < 1 := lt_of_le_of_ne (hzBox i |>.2) hiOne
  have hOtherBinary : ∀ j ∈ Finset.univ.erase i, z j = 0 ∨ z j = 1 := by
    intro j hjMem
    have hji : j ≠ i := Finset.ne_of_mem_erase hjMem
    by_cases hjZero : z j = 0
    · exact Or.inl hjZero
    · by_cases hjOne : z j = 1
      · exact Or.inr hjOne
      · exact (hNoJ ⟨j, hji, hjZero, hjOne⟩).elim
  have hRest := finset_sum_eq_card_filter_of_binary (Finset.univ.erase i) z hOtherBinary
  have hDecomp :
      (∑ j, z j) =
        ((Finset.univ.erase i).filter fun j ↦ z j ≠ 0).card + z i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hRest]
  have hLowerReal :
      (((Finset.univ.erase i).filter fun j ↦ z j ≠ 0).card : ℝ) < (ℓ : ℝ) := by
    linarith
  have hUpperReal :
      (ℓ : ℝ) < (((Finset.univ.erase i).filter fun j ↦ z j ≠ 0).card : ℝ) + 1 := by
    linarith
  have hLowerNat :
      ((Finset.univ.erase i).filter fun j ↦ z j ≠ 0).card < ℓ := by
    exact_mod_cast hLowerReal
  have hUpperNat :
      ℓ < ((Finset.univ.erase i).filter fun j ↦ z j ≠ 0).card + 1 := by
    exact_mod_cast hUpperReal
  omega

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: an extreme point
on the total-mass boundary has binary coordinates. -/
lemma unitRelaxationExtremePoint_coordinate_binary_of_sum_eq {k : ℕ} (ℓ : ℕ)
    {z : Fin k → ℝ} (hzExtreme : z ∈ (unitCardinalityRelaxation ℓ).extremePoints ℝ)
    (i : Fin k) (hsumEq : (∑ j, z j) = (ℓ : ℝ)) : z i = 0 ∨ z i = 1 := by
  classical
  have hz : z ∈ unitCardinalityRelaxation ℓ := extremePoints_subset hzExtreme
  by_contra hi
  have hiZero : z i ≠ 0 := fun h ↦ hi (Or.inl h)
  have hiOne : z i ≠ 1 := fun h ↦ hi (Or.inr h)
  have hiPos : 0 < z i := lt_of_le_of_ne (hz.1 i |>.1) (Ne.symm hiZero)
  have hiLt : z i < 1 := lt_of_le_of_ne (hz.1 i |>.2) hiOne
  obtain ⟨j, hji, hjZero, hjOne⟩ :=
    unitBox_sum_eq_nat_has_second_fractional_coordinate ℓ i hz.1 hiZero hiOne hsumEq
  have hjPos : 0 < z j := lt_of_le_of_ne (hz.1 j |>.1) (Ne.symm hjZero)
  have hjLt : z j < 1 := lt_of_le_of_ne (hz.1 j |>.2) hjOne
  -- On the tight hyperplane, transfer a small amount between two fractional coordinates.
  let ε : ℝ := min (z i) (min (1 - z i) (min (z j) (1 - z j))) / 2
  have hεPos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεLeI : ε ≤ z i := by
    dsimp [ε]
    nlinarith [min_le_left (z i) (min (1 - z i) (min (z j) (1 - z j)))]
  have hεLeIGap : ε ≤ 1 - z i := by
    dsimp [ε]
    nlinarith [min_le_right (z i) (min (1 - z i) (min (z j) (1 - z j))),
      min_le_left (1 - z i) (min (z j) (1 - z j))]
  have hεLeJ : ε ≤ z j := by
    dsimp [ε]
    nlinarith [min_le_right (z i) (min (1 - z i) (min (z j) (1 - z j))),
      min_le_right (1 - z i) (min (z j) (1 - z j)),
      min_le_left (z j) (1 - z j)]
  have hεLeJGap : ε ≤ 1 - z j := by
    dsimp [ε]
    nlinarith [min_le_right (z i) (min (1 - z i) (min (z j) (1 - z j))),
      min_le_right (1 - z i) (min (z j) (1 - z j)),
      min_le_right (z j) (1 - z j)]
  let v : Fin k → ℝ := Pi.single i ε - Pi.single j ε
  have hsumV : (∑ q, v q) = 0 := by
    simp [v, Finset.sum_sub_distrib]
  have hminus : z - v ∈ unitCardinalityRelaxation ℓ := by
    refine ⟨?_, ?_⟩
    · intro q
      by_cases hqi : q = i
      · subst q
        simp [v, hji]
        constructor
        · linarith
        · linarith
      · by_cases hqj : q = j
        · subst q
          simp [v, hji]
          constructor
          · linarith
          · linarith
        · simpa [v, hqi, hqj] using hz.1 q
    · calc
        (∑ q, (z - v) q) = (∑ q, z q) - ∑ q, v q := by
          simp only [Pi.sub_apply, Finset.sum_sub_distrib]
        _ = (∑ q, z q) := by rw [hsumV, sub_zero]
        _ ≤ (ℓ : ℝ) := hz.2
  have hplus : z + v ∈ unitCardinalityRelaxation ℓ := by
    refine ⟨?_, ?_⟩
    · intro q
      by_cases hqi : q = i
      · subst q
        simp [v, hji]
        constructor
        · linarith
        · linarith
      · by_cases hqj : q = j
        · subst q
          simp [v, hji]
          constructor
          · linarith
          · linarith
        · simpa [v, hqi, hqj] using hz.1 q
    · calc
        (∑ q, (z + v) q) = (∑ q, z q) + ∑ q, v q := by
          simp only [Pi.add_apply, Finset.sum_add_distrib]
        _ = (∑ q, z q) := by rw [hsumV, add_zero]
        _ ≤ (ℓ : ℝ) := hz.2
  have hminusNe : z - v ≠ z := by
    intro heq
    have hiEq := congrFun heq i
    simp [v, hji, ne_of_gt hεPos] at hiEq
  exact hminusNe (hzExtreme.2 hminus hplus (mem_openSegment_sub_add z v))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: every extreme
point of the normalized relaxation is binary and hence cardinality-feasible. -/
lemma unitRelaxationExtremePoints_mem_unitFeasible {k : ℕ} (ℓ : ℕ) {z : Fin k → ℝ}
    (hzExtreme : z ∈ (unitCardinalityRelaxation ℓ).extremePoints ℝ) :
    (∀ j, z j = 0 ∨ z j = 1) ∧ z ∈ unitCardinalityFeasible ℓ := by
  have hz : z ∈ unitCardinalityRelaxation ℓ := extremePoints_subset hzExtreme
  have hzBinary : ∀ i, z i = 0 ∨ z i = 1 := by
    intro i
    by_cases hsum : (∑ j, z j) < (ℓ : ℝ)
    · exact unitRelaxationExtremePoint_coordinate_binary_of_sum_lt ℓ hzExtreme i hsum
    · have hsumEq : (∑ j, z j) = (ℓ : ℝ) := le_antisymm hz.2 (le_of_not_gt hsum)
      exact unitRelaxationExtremePoint_coordinate_binary_of_sum_eq ℓ hzExtreme i hsumEq
  -- Binary coordinates turn the relaxation's mass inequality into the support bound.
  refine ⟨hzBinary, ?_, ?_⟩
  · intro j
    rcases hzBinary j with hzj | hzj
    · simp [hzj]
    · simp [hzj]
  · have hCountReal : (nonzero_coordinate_count z : ℝ) ≤ (ℓ : ℝ) := by
      rw [← sum_eq_nonzero_coordinate_count_of_binary hzBinary]
      exact hz.2
    exact_mod_cast hCountReal

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: binary normalized
feasible vectors form a finite set. -/
lemma unitBinaryFeasible_finite {k : ℕ} (ℓ : ℕ) :
    ({z : Fin k → ℝ | (∀ j, z j = 0 ∨ z j = 1) ∧
      z ∈ unitCardinalityFeasible ℓ} : Set (Fin k → ℝ)).Finite := by
  have hCube :
      ({z : Fin k → ℝ | ∀ j, z j ∈ ({0, 1} : Set ℝ)} : Set (Fin k → ℝ)).Finite := by
    simpa [Set.pi] using
      (Set.Finite.pi (fun _ ↦ (Set.finite_singleton (1 : ℝ)).insert 0))
  -- The support restriction only cuts down the finite binary cube.
  apply hCube.subset
  intro z hz j
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz.1 j

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean`: the convex hull of
the normalized cardinality-feasible set is exactly its unit-box relaxation. -/
lemma unitRelaxation_convexHull_eq {k : ℕ} (ℓ : ℕ) :
    convexHull ℝ (unitCardinalityFeasible (k := k) ℓ) = unitCardinalityRelaxation ℓ := by
  apply Set.Subset.antisymm
  · -- Every sparse unit-box vector satisfies the relaxed mass inequality.
    exact convexHull_min (unitCardinalityFeasible_subset_relaxation ℓ)
      (unitCardinalityRelaxation_convex ℓ)
  · intro z hz
    let B : Set (Fin k → ℝ) :=
      {w | (∀ j, w j = 0 ∨ w j = 1) ∧ w ∈ unitCardinalityFeasible ℓ}
    have hBFinite : B.Finite := by
      simpa [B] using unitBinaryFeasible_finite (k := k) ℓ
    have hExtremeSubset :
        (unitCardinalityRelaxation ℓ).extremePoints ℝ ⊆ B := by
      intro w hw
      exact unitRelaxationExtremePoints_mem_unitFeasible ℓ hw
    have hClosureSubset :
        closure (convexHull ℝ ((unitCardinalityRelaxation ℓ).extremePoints ℝ)) ⊆
          convexHull ℝ B := by
      apply closure_minimal
      · exact convexHull_mono hExtremeSubset
      · exact hBFinite.isClosed_convexHull ℝ
    have hzClosure :
        z ∈ closure (convexHull ℝ ((unitCardinalityRelaxation ℓ).extremePoints ℝ)) := by
      rw [closure_convexHull_extremePoints (unitCardinalityRelaxation_isCompact ℓ)
        (unitCardinalityRelaxation_convex ℓ)]
      exact hz
    have hzBinaryHull : z ∈ convexHull ℝ B := hClosureSubset hzClosure
    -- The finite binary generators are a subset of the original sparse generating set.
    exact convexHull_mono (fun _ hw ↦ hw.2) hzBinaryHull

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_exercise_2_32.lean

The LP relaxation of the activation formulation projects to the convex hull of the intended
feasible set. -/
theorem bounded_nonzero_cardinality_relaxation_is_perfect {k : ℕ} (u : Fin k → ℝ)
    (hu : ∀ j, 0 ≤ u j) (ℓ : ℕ) :
    convexHull ℝ {y : Fin k → ℝ | bounded_nonzero_cardinality_feasible u ℓ y} =
      {y : Fin k → ℝ | ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_relaxation u ℓ x y} := by
  have hFeasibleImage :
      {y : Fin k → ℝ | bounded_nonzero_cardinality_feasible u ℓ y} =
        coordinatewiseScale u '' unitCardinalityFeasible ℓ := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := (feasible_iff_exists_unitScaledPoint u hu ℓ y).mp hy
      exact ⟨z, hz, hzy⟩
    · rintro ⟨z, hz, hzy⟩
      exact (feasible_iff_exists_unitScaledPoint u hu ℓ y).mpr ⟨z, hz, hzy⟩
  have hRelaxationImage :
      {y : Fin k → ℝ |
        ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_relaxation u ℓ x y} =
        coordinatewiseScale u '' unitCardinalityRelaxation ℓ := by
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ :=
        (relaxationProjection_iff_exists_unitScaledPoint u hu ℓ y).mp hy
      exact ⟨z, hz, hzy⟩
    · rintro ⟨z, hz, hzy⟩
      exact
        (relaxationProjection_iff_exists_unitScaledPoint u hu ℓ y).mpr ⟨z, hz, hzy⟩
  -- Transport the normalized convex-hull equality through the coordinatewise linear scaling.
  calc
    convexHull ℝ {y : Fin k → ℝ | bounded_nonzero_cardinality_feasible u ℓ y} =
        convexHull ℝ (coordinatewiseScale u '' unitCardinalityFeasible ℓ) := by
          rw [hFeasibleImage]
    _ = coordinatewiseScale u '' convexHull ℝ (unitCardinalityFeasible ℓ) :=
      (coordinatewiseScale u).image_convexHull (unitCardinalityFeasible ℓ) |>.symm
    _ = coordinatewiseScale u '' unitCardinalityRelaxation ℓ := by
      rw [unitRelaxation_convexHull_eq]
    _ = {y : Fin k → ℝ |
        ∃ x : Fin k → ℝ, bounded_nonzero_cardinality_relaxation u ℓ x y} :=
      hRelaxationImage.symm

#print axioms exercise_2_32
#print axioms bounded_nonzero_cardinality_relaxation_is_perfect
