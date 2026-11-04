/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_1_remark_7_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_12.ch4_sec4_12_exercise_4_38.FacetTransport

open scoped BigOperators Matrix

section Example76

/-- The weight vector `(5,4,3,2,1)` from Example 7.6. -/
def example_7_6_weights : Fin 5 → ℕ :=
  ![5, 4, 3, 2, 1]

/-- The `0,1` knapsack set
`K = {x ∈ {0,1}^5 : 5x₁ + 4x₂ + 3x₃ + 2x₄ + x₅ ≤ 5}` from Example 7.6. -/
def example_7_6_knapsack_set : Set (Fin 5 → ℝ) :=
  zero_one_knapsack_set (fun i ↦ (example_7_6_weights i : ℝ)) 5

/-- Membership in `example_7_6_knapsack_set` means being binary and satisfying the displayed
knapsack inequality. -/
theorem mem_example_7_6_knapsack_set_iff
    (x : Fin 5 → ℝ) :
    x ∈ example_7_6_knapsack_set ↔
      (∀ i, x i = 0 ∨ x i = 1) ∧
        ((5 : ℝ) * x 0 + 4 * x 1 + 3 * x 2 + 2 * x 3 + x 4 ≤ 5) := by
  -- Expand the finite dot product into the five displayed coordinates.
  rw [example_7_6_knapsack_set, mem_zero_one_knapsack_set_iff]
  constructor
  · rintro ⟨hbinary, hweight⟩
    refine ⟨hbinary, ?_⟩
    have hexpanded :
        5 * x 0 + (4 * x 1 + (3 * x 2 + (2 * x 3 + x 4))) ≤ 5 := by
      simpa [example_7_6_weights, Fin.sum_univ_succ] using hweight
    linarith
  · rintro ⟨hbinary, hweight⟩
    refine ⟨hbinary, ?_⟩
    have hexpanded :
        5 * x 0 + (4 * x 1 + (3 * x 2 + (2 * x 3 + x 4))) ≤ 5 := by
      linarith
    simpa [example_7_6_weights, Fin.sum_univ_succ] using hexpanded

/-- The knapsack polytope `conv(K)` attached to Example 7.6. -/
def example_7_6_knapsack_polytope : Set (Fin 5 → ℝ) :=
  zero_one_knapsack_polytope (fun i ↦ (example_7_6_weights i : ℝ)) 5

/-- `example_7_6_knapsack_polytope` is the convex hull of the Example 7.6 feasible set. -/
theorem example_7_6_knapsack_polytope_eq_convexHull :
    example_7_6_knapsack_polytope = convexHull ℝ example_7_6_knapsack_set := by
  -- Both named sets unfold to the same canonical convex hull.
  rw [example_7_6_knapsack_polytope, zero_one_knapsack_polytope_eq_convexHull,
    example_7_6_knapsack_set]

/-- The cover `C = {3,4,5}` from Example 7.6, written with zero-based indices as `{2,3,4}`. -/
def example_7_6_cover : Finset (Fin 5) :=
  {2, 3, 4}

/-- The values `μ₀ = 0`, `μ₁ = 3`, `μ₂ = 5`, and `μ₃ = 6` used in Example 7.6. -/
def example_7_6_mu : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | 2 => 5
  | 3 => 6
  | _ => 6

/-- The lifting profile used in Example 7.6 has coefficients `2` on item `1` and `1` on item `2`
outside the cover, and its values on the cover are ignored by `remark_7_5_lifting_coeff`. -/
def example_7_6_lifting_function : Fin 5 → ℕ :=
  ![2, 1, 0, 0, 0]

/-- The lifted cover inequality from Example 7.6 has coefficient vector `(2,1,1,1,1)`. -/
def example_7_6_lifted_vector : Fin 5 → ℝ :=
  remark_7_5_lifting_coeff example_7_6_cover example_7_6_lifting_function

/-- `example_7_6_lifted_vector` evaluates to the displayed coefficient vector `(2,1,1,1,1)`. -/
theorem example_7_6_lifted_vector_apply
    (j : Fin 5) :
    example_7_6_lifted_vector j =
      ![(2 : ℝ), 1, 1, 1, 1] j := by
  -- Evaluate the cover test and lifting profile at each of the five indices.
  fin_cases j
  · simp [example_7_6_lifted_vector, example_7_6_cover,
      example_7_6_lifting_function, Fin.ext_iff]
  · simp [example_7_6_lifted_vector, example_7_6_cover,
      example_7_6_lifting_function, Fin.ext_iff]
  · simp [example_7_6_lifted_vector, example_7_6_cover,
      example_7_6_lifting_function, Fin.ext_iff]
  · simp [example_7_6_lifted_vector, example_7_6_cover,
      example_7_6_lifting_function, Fin.ext_iff]
  · simp [example_7_6_lifted_vector, example_7_6_cover,
      example_7_6_lifting_function, Fin.ext_iff]

/-- Every item weight in Example 7.6 is at most the capacity `5`. -/
theorem example_7_6_weights_le_capacity
    (j : Fin 5) :
    example_7_6_weights j ≤ 5 := by
  -- The claim is the coordinatewise computation for `(5,4,3,2,1)`.
  fin_cases j
  · norm_num [example_7_6_weights]
  · norm_num [example_7_6_weights]
  · norm_num [example_7_6_weights]
  · norm_num [example_7_6_weights]
  · norm_num [example_7_6_weights]

/-- The first non-cover weight lies in the interval `μ₂ ≤ a₁ ≤ μ₃ - 1` used to read off
`α₁ = 2`. -/
theorem example_7_6_first_weight_interval :
    example_7_6_mu 2 ≤ example_7_6_weights 0 ∧
      example_7_6_weights 0 ≤ example_7_6_mu 3 - 1 := by
  -- Substitute the first weight and the two relevant partial sums.
  norm_num [example_7_6_mu, example_7_6_weights]

/-- The second non-cover weight lies in the interval `μ₁ ≤ a₂ ≤ μ₂ - 1` used to read off
`α₂ = 1`. -/
theorem example_7_6_second_weight_interval :
    example_7_6_mu 1 ≤ example_7_6_weights 1 ∧
      example_7_6_weights 1 ≤ example_7_6_mu 2 - 1 := by
  -- Substitute the second weight and the two relevant partial sums.
  norm_num [example_7_6_mu, example_7_6_weights]

/-- The non-cover items of Example 7.6 satisfy the interval hypothesis from Remark 7.5. -/
theorem example_7_6_interval_indices :
    remark_7_5_interval_indices
      example_7_6_weights
      example_7_6_cover
      example_7_6_mu
      example_7_6_lifting_function := by
  -- Only indices `0` and `1` lie outside the cover; compute both intervals directly.
  rw [remark_7_5_interval_indices_iff]
  intro j hj
  fin_cases j
  · norm_num [example_7_6_weights, example_7_6_mu, example_7_6_lifting_function]
  · norm_num [example_7_6_weights, example_7_6_mu, example_7_6_lifting_function]
  · simp [example_7_6_cover, Fin.ext_iff] at hj
  · simp [example_7_6_cover, Fin.ext_iff] at hj
  · simp [example_7_6_cover, Fin.ext_iff] at hj

/-- The strengthened upper bound `a_j ≤ μ_{h(j)+1} - 1` from Remark 7.5 holds for every non-cover
item in Example 7.6. -/
theorem example_7_6_strong_upper_bound :
    remark_7_5_strong_upper_bound
      example_7_6_weights
      example_7_6_cover
      example_7_6_mu
      example_7_6_lifting_function
      1 := by
  -- The two off-cover coordinates meet the strengthened bound with equality.
  rw [remark_7_5_strong_upper_bound_iff]
  intro j hj
  fin_cases j
  · norm_num [example_7_6_weights, example_7_6_mu, example_7_6_lifting_function]
  · norm_num [example_7_6_weights, example_7_6_mu, example_7_6_lifting_function]
  · simp [example_7_6_cover, Fin.ext_iff] at hj
  · simp [example_7_6_cover, Fin.ext_iff] at hj
  · simp [example_7_6_cover, Fin.ext_iff] at hj

/-- Example 7.6 (1). The set `C = {3,4,5}` is a minimal cover for the knapsack set
`K = {x ∈ {0,1}^5 : 5x₁ + 4x₂ + 3x₃ + 2x₄ + x₅ ≤ 5}`. -/
theorem example_7_6_cover_is_minimal :
    IsMinimalKnapsackCover example_7_6_weights 5 example_7_6_cover := by
  -- The cover has total weight six, while every one-element erasure has weight at most five.
  rw [isMinimalKnapsackCover_iff]
  constructor
  · rw [isKnapsackCover_iff]
    decide
  · intro i hi
    fin_cases i
    · simp [example_7_6_cover, Fin.ext_iff] at hi
    · simp [example_7_6_cover, Fin.ext_iff] at hi
    · decide
    · decide
    · decide

/-- Example 7.6 (2). The first lifted coefficient satisfies `α₁ = 2`. -/
theorem example_7_6_alpha_1_eq_two :
    example_7_6_lifting_function 0 = 2 := by
  -- Read the first entry of the concrete lifting profile.
  norm_num [example_7_6_lifting_function]

/-- Example 7.6 (3). The second lifted coefficient satisfies `α₂ = 1`. -/
theorem example_7_6_alpha_2_eq_one :
    example_7_6_lifting_function 1 = 1 := by
  -- Read the second entry of the concrete lifting profile.
  norm_num [example_7_6_lifting_function]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the cyclic permutation that
moves the three cover coordinates to the initial segment. -/
def example76Reindex : Equiv.Perm (Fin 5) :=
  finRotate 5 ^ 2

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coordinate equivalence
induced by the cyclic reindexing. -/
def example76CoordinateEquiv : (Fin 5 → ℝ) ≃L[ℝ] (Fin 5 → ℝ) :=
  (ContinuousLinearEquiv.piCongrLeft
    ℝ (fun _ : Fin 5 ↦ ℝ) example76Reindex.symm).symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the weights after cyclic
reindexing. -/
def example76ReindexedWeights : Fin 5 → ℕ :=
  fun i ↦ example_7_6_weights (example76Reindex i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the lifting profile after cyclic
reindexing. -/
def example76ReindexedLiftingFunction : Fin 5 → ℕ :=
  fun i ↦ example_7_6_lifting_function (example76Reindex i)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the prefix length three is at
most the ambient dimension five. -/
lemma example76ThreeLeFive : 3 ≤ 5 := by
  -- This fixed dimension side condition is numerical.
  norm_num

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the cyclic permutation sends
the new coordinates to old coordinates in the order `2,3,4,0,1`. -/
lemma example76Reindex_apply
    (i : Fin 5) :
    example76Reindex i = ![(2 : Fin 5), 3, 4, 0, 1] i := by
  -- Evaluate the two rotations at every coordinate.
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed weights are
`(3,2,1,5,4)`. -/
lemma example76ReindexedWeights_apply
    (i : Fin 5) :
    example76ReindexedWeights i = ![3, 2, 1, 5, 4] i := by
  -- Combine the permutation table with the original concrete weight vector.
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed lifting profile is
`(0,0,0,2,1)`. -/
lemma example76ReindexedLiftingFunction_apply
    (i : Fin 5) :
    example76ReindexedLiftingFunction i = ![0, 0, 0, 2, 1] i := by
  -- Combine the permutation table with the original concrete lifting profile.
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: each weight in the reindexed
three-coordinate prefix is `3 - i`. -/
lemma example76ReindexedCoverWeight_apply
    (i : Fin 3) :
    example76ReindexedWeights (i.castLE example76ThreeLeFive) = 3 - i.1 := by
  -- Evaluate the three prefix coordinates using the reindexed weight table.
  fin_cases i
  · decide
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed first-three cover
is minimal. -/
lemma example76ReindexedCoverIsMinimal :
    IsMinimalKnapsackCover
      example76ReindexedWeights 5 (remark_7_5_cover (n := 5) 3) := by
  -- All cover and single-erasure inequalities are decidable finite computations.
  rw [isMinimalKnapsackCover_iff, isKnapsackCover_iff]
  constructor
  · decide
  · intro i hi
    fin_cases i
    · decide
    · decide
    · decide
    · simp [remark_7_5_cover] at hi
    · simp [remark_7_5_cover] at hi

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed data satisfy the
Theorem 7.4 context used by Remark 7.5. -/
lemma example76ReindexedContext :
    remark_7_5_theorem_7_4_context
      example76ReindexedWeights
      5
      (remark_7_5_cover (n := 5) 3)
      (remark_7_5_mu example76ReindexedWeights 3 example76ThreeLeFive)
      1 := by
  -- Package the decreasing prefix weights, positivity, capacity bounds, and minimality.
  refine ⟨3, example76ThreeLeFive, rfl, ?_, ?_, ?_,
    example76ReindexedCoverIsMinimal, rfl, ?_⟩
  · unfold remark_7_5_cover_weights_descending remark_7_5_cover_weight
    intro i j hij
    change example76ReindexedWeights (j.castLE example76ThreeLeFive) ≤
      example76ReindexedWeights (i.castLE example76ThreeLeFive)
    rw [example76ReindexedCoverWeight_apply, example76ReindexedCoverWeight_apply]
    omega
  · intro j
    fin_cases j
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
  · intro j
    fin_cases j
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
    · norm_num [example76ReindexedWeights_apply]
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed non-cover weights
lie in their Remark 7.5 partial-sum intervals. -/
lemma example76ReindexedIntervalIndices :
    remark_7_5_interval_indices
      example76ReindexedWeights
      (remark_7_5_cover (n := 5) 3)
      (remark_7_5_mu example76ReindexedWeights 3 example76ThreeLeFive)
      example76ReindexedLiftingFunction := by
  -- Only the last two reindexed coordinates are outside the prefix cover.
  rw [remark_7_5_interval_indices_iff]
  intro j hj
  fin_cases j
  · simp [remark_7_5_cover] at hj
  · simp [remark_7_5_cover] at hj
  · simp [remark_7_5_cover] at hj
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed weights satisfy
the strengthened Remark 7.5 upper bound with excess one. -/
lemma example76ReindexedStrongUpperBound :
    remark_7_5_strong_upper_bound
      example76ReindexedWeights
      (remark_7_5_cover (n := 5) 3)
      (remark_7_5_mu example76ReindexedWeights 3 example76ThreeLeFive)
      example76ReindexedLiftingFunction
      1 := by
  -- Both off-cover inequalities are decidable computations in the concrete data.
  rw [remark_7_5_strong_upper_bound_iff]
  intro j hj
  fin_cases j
  · simp [remark_7_5_cover] at hj
  · simp [remark_7_5_cover] at hj
  · simp [remark_7_5_cover] at hj
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: membership in the prefix cover
is carried to membership in the original cover by the cyclic permutation. -/
lemma example76Reindex_mem_cover_iff
    (i : Fin 5) :
    example76Reindex i ∈ example_7_6_cover ↔
      i ∈ remark_7_5_cover (n := 5) 3 := by
  -- Check the cover correspondence using the five-entry permutation table.
  fin_cases i
  · decide
  · decide
  · decide
  · decide
  · decide

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: both three-element covers have
the same cover-inequality right-hand side. -/
lemma example76CoverRhs_eq :
    cover_inequality_rhs (remark_7_5_cover (n := 5) 3) =
      cover_inequality_rhs example_7_6_cover := by
  -- Each concrete cover has cardinality three.
  have hcard : example_7_6_cover.card = 3 := by
    decide
  rw [cover_inequality_rhs_eq, cover_inequality_rhs_eq,
    remark_7_5_cover_card 3 example76ThreeLeFive, hcard]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coordinate equivalence
places the old coordinate `example76Reindex i` at new coordinate `i`. -/
lemma example76CoordinateEquiv_apply_reindex
    (x : Fin 5 → ℝ)
    (i : Fin 5) :
    example76CoordinateEquiv x (example76Reindex i) = x i := by
  -- This is the computation rule for `ContinuousLinearEquiv.piCongrLeft`.
  change
    (Equiv.piCongrLeft (fun _ : Fin 5 ↦ ℝ) example76Reindex.symm).symm x
        (example76Reindex i) = x i
  simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: dot products are invariant under
the paired coefficient and coordinate reindexing. -/
lemma example76_dotProduct_reindex
    (α x : Fin 5 → ℝ) :
    (fun i ↦ α (example76Reindex i)) ⬝ᵥ x =
      α ⬝ᵥ example76CoordinateEquiv x := by
  -- Reindex the finite sum and use the coordinate-equivalence computation rule.
  rw [dotProduct, dotProduct]
  refine Fintype.sum_equiv example76Reindex _ _ ?_
  intro i
  rw [example76CoordinateEquiv_apply_reindex]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: binary knapsack-set membership is
preserved by the cyclic coordinate equivalence. -/
lemma example76_mem_knapsackSet_reindex_iff
    (x : Fin 5 → ℝ) :
    x ∈ zero_one_knapsack_set (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 ↔
      example76CoordinateEquiv x ∈
        zero_one_knapsack_set (fun i ↦ (example_7_6_weights i : ℝ)) 5 := by
  rw [mem_zero_one_knapsack_set_iff, mem_zero_one_knapsack_set_iff]
  constructor
  · rintro ⟨hbinary, hweight⟩
    constructor
    · intro j
      have hcoordinate := hbinary (example76Reindex.symm j)
      have hindex : example76Reindex (example76Reindex.symm j) = j :=
        example76Reindex.apply_symm_apply j
      rw [← hindex, example76CoordinateEquiv_apply_reindex]
      exact hcoordinate
    · have hsum :=
        example76_dotProduct_reindex (fun i ↦ (example_7_6_weights i : ℝ)) x
      have hsum' :
          (∑ i, (example76ReindexedWeights i : ℝ) * x i) =
            ∑ i, (example_7_6_weights i : ℝ) * example76CoordinateEquiv x i := by
        simpa only [dotProduct, example76ReindexedWeights] using hsum
      calc
        ∑ i, (example_7_6_weights i : ℝ) * example76CoordinateEquiv x i =
            ∑ i, (example76ReindexedWeights i : ℝ) * x i := hsum'.symm
        _ ≤ 5 := hweight
  · rintro ⟨hbinary, hweight⟩
    constructor
    · intro i
      simpa [example76CoordinateEquiv_apply_reindex] using
        hbinary (example76Reindex i)
    · have hsum :=
        example76_dotProduct_reindex (fun i ↦ (example_7_6_weights i : ℝ)) x
      have hsum' :
          (∑ i, (example76ReindexedWeights i : ℝ) * x i) =
            ∑ i, (example_7_6_weights i : ℝ) * example76CoordinateEquiv x i := by
        simpa only [dotProduct, example76ReindexedWeights] using hsum
      calc
        ∑ i, (example76ReindexedWeights i : ℝ) * x i =
            ∑ i, (example_7_6_weights i : ℝ) * example76CoordinateEquiv x i := hsum'
        _ ≤ 5 := hweight

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coordinate equivalence sends
the reindexed binary knapsack set onto the original one. -/
lemma example76KnapsackSet_reindex_image :
    example76CoordinateEquiv ''
        zero_one_knapsack_set (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 =
      zero_one_knapsack_set (fun i ↦ (example_7_6_weights i : ℝ)) 5 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (example76_mem_knapsackSet_reindex_iff x).mp hx
  · intro hy
    refine ⟨example76CoordinateEquiv.symm y, ?_, ?_⟩
    · apply (example76_mem_knapsackSet_reindex_iff _).mpr
      simpa using hy
    · exact example76CoordinateEquiv.apply_symm_apply y

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coordinate equivalence sends
the reindexed knapsack polytope onto the original one. -/
lemma example76KnapsackPolytope_reindex_image :
    example76CoordinateEquiv ''
        zero_one_knapsack_polytope
          (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 =
      zero_one_knapsack_polytope
        (fun i ↦ (example_7_6_weights i : ℝ)) 5 := by
  -- Linear maps commute with convex hull, and the generating binary sets correspond.
  rw [zero_one_knapsack_polytope_eq_convexHull,
    zero_one_knapsack_polytope_eq_convexHull]
  calc
    example76CoordinateEquiv ''
          convexHull ℝ
            (zero_one_knapsack_set (fun i ↦ (example76ReindexedWeights i : ℝ)) 5) =
        convexHull ℝ
          (example76CoordinateEquiv ''
            zero_one_knapsack_set (fun i ↦ (example76ReindexedWeights i : ℝ)) 5) := by
              exact LinearMap.image_convexHull example76CoordinateEquiv.toLinearMap _
    _ = convexHull ℝ
        (zero_one_knapsack_set (fun i ↦ (example_7_6_weights i : ℝ)) 5) := by
          rw [example76KnapsackSet_reindex_image]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: pointwise membership in the two
knapsack polytopes is equivalent under reindexing. -/
lemma example76_mem_knapsackPolytope_reindex_iff
    (x : Fin 5 → ℝ) :
    x ∈ zero_one_knapsack_polytope
        (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 ↔
      example76CoordinateEquiv x ∈
        zero_one_knapsack_polytope
          (fun i ↦ (example_7_6_weights i : ℝ)) 5 := by
  constructor
  · intro hx
    have himage :
        example76CoordinateEquiv x ∈
          example76CoordinateEquiv ''
            zero_one_knapsack_polytope
              (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 :=
      ⟨x, hx, rfl⟩
    rwa [example76KnapsackPolytope_reindex_image] at himage
  · intro hx
    have himage :
        example76CoordinateEquiv x ∈
          example76CoordinateEquiv ''
            zero_one_knapsack_polytope
              (fun i ↦ (example76ReindexedWeights i : ℝ)) 5 := by
      rwa [example76KnapsackPolytope_reindex_image]
    rcases himage with ⟨y, hy, hyx⟩
    have hy_eq_x : y = x := example76CoordinateEquiv.injective hyx
    simpa [hy_eq_x] using hy

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: lifted-cover coefficient vectors
commute with the cover-preserving cyclic reindexing. -/
lemma example76LiftedCoverCoeff_reindex
    (α : Fin 5 → ℝ) :
    lifted_cover_inequality_coeff (remark_7_5_cover (n := 5) 3)
        (fun i ↦ α (example76Reindex i)) =
      fun i ↦ lifted_cover_inequality_coeff example_7_6_cover α
        (example76Reindex i) := by
  ext i
  rw [lifted_cover_inequality_coeff_apply, lifted_cover_inequality_coeff_apply]
  simp only [example76Reindex_mem_cover_iff]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the reindexed lifted-cover
functional agrees with the original functional after the coordinate equivalence. -/
lemma example76LiftedCoverDot_reindex
    (α x : Fin 5 → ℝ) :
    lifted_cover_inequality_coeff (remark_7_5_cover (n := 5) 3)
          (fun i ↦ α (example76Reindex i)) ⬝ᵥ x =
      lifted_cover_inequality_coeff example_7_6_cover α ⬝ᵥ
        example76CoordinateEquiv x := by
  calc
    lifted_cover_inequality_coeff (remark_7_5_cover (n := 5) 3)
          (fun i ↦ α (example76Reindex i)) ⬝ᵥ x =
        (fun i ↦ lifted_cover_inequality_coeff example_7_6_cover α
          (example76Reindex i)) ⬝ᵥ x := by
            rw [example76LiftedCoverCoeff_reindex]
    _ = lifted_cover_inequality_coeff example_7_6_cover α ⬝ᵥ
        example76CoordinateEquiv x := example76_dotProduct_reindex _ _

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: membership in the corresponding
lifted faces is preserved by the coordinate equivalence. -/
lemma example76_mem_liftedCoverFace_reindex_iff
    (α x : Fin 5 → ℝ) :
    x ∈ lifted_cover_face
        (fun i ↦ (example76ReindexedWeights i : ℝ))
        5
        (remark_7_5_cover (n := 5) 3)
        (fun i ↦ α (example76Reindex i)) ↔
      example76CoordinateEquiv x ∈ lifted_cover_face
        (fun i ↦ (example_7_6_weights i : ℝ))
        5
        example_7_6_cover
        α := by
  rw [lifted_cover_face, lifted_cover_face, mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hx, heq⟩
    refine ⟨(example76_mem_knapsackPolytope_reindex_iff x).mp hx, ?_⟩
    rw [← example76LiftedCoverDot_reindex, ← example76CoverRhs_eq]
    exact heq
  · rintro ⟨hx, heq⟩
    refine ⟨(example76_mem_knapsackPolytope_reindex_iff x).mpr hx, ?_⟩
    rw [example76LiftedCoverDot_reindex, example76CoverRhs_eq]
    exact heq

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coordinate equivalence sends
the reindexed lifted face onto the original lifted face. -/
lemma example76LiftedCoverFace_reindex_image
    (α : Fin 5 → ℝ) :
    example76CoordinateEquiv ''
        lifted_cover_face
          (fun i ↦ (example76ReindexedWeights i : ℝ))
          5
          (remark_7_5_cover (n := 5) 3)
          (fun i ↦ α (example76Reindex i)) =
      lifted_cover_face
        (fun i ↦ (example_7_6_weights i : ℝ))
        5
        example_7_6_cover
        α := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (example76_mem_liftedCoverFace_reindex_iff α x).mp hx
  · intro hy
    refine ⟨example76CoordinateEquiv.symm y, ?_, ?_⟩
    · apply (example76_mem_liftedCoverFace_reindex_iff α _).mpr
      simpa using hy
    · exact example76CoordinateEquiv.apply_symm_apply y

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: valid lifted inequalities are
preserved and reflected by the cyclic reindexing. -/
lemma example76ValidLiftingReindex_iff
    (α : Fin 5 → ℝ) :
    α ∈ valid_liftings_of_minimal_cover_inequality
        example_7_6_weights 5 example_7_6_cover ↔
      (fun i ↦ α (example76Reindex i)) ∈
        valid_liftings_of_minimal_cover_inequality
          example76ReindexedWeights 5 (remark_7_5_cover (n := 5) 3) := by
  rw [mem_valid_liftings_of_minimal_cover_inequality_iff,
    mem_valid_liftings_of_minimal_cover_inequality_iff]
  constructor
  · rintro ⟨hcover, hvalid⟩
    constructor
    · intro i hi
      exact hcover (example76Reindex i) ((example76Reindex_mem_cover_iff i).mpr hi)
    · rw [is_valid_inequality_iff] at hvalid ⊢
      intro x hx
      have hineq := hvalid ((example76_mem_knapsackPolytope_reindex_iff x).mp hx)
      rw [example76_dotProduct_reindex, example76CoverRhs_eq]
      exact hineq
  · rintro ⟨hcover, hvalid⟩
    constructor
    · intro j hj
      have hindex : example76Reindex (example76Reindex.symm j) = j :=
        example76Reindex.apply_symm_apply j
      have himage : example76Reindex (example76Reindex.symm j) ∈ example_7_6_cover := by
        simpa [hindex] using hj
      have hprefix := (example76Reindex_mem_cover_iff _).mp himage
      have hcoeff := hcover (example76Reindex.symm j) hprefix
      simpa using hcoeff
    · rw [is_valid_inequality_iff] at hvalid ⊢
      intro y hy
      have hyimage :
          example76CoordinateEquiv (example76CoordinateEquiv.symm y) ∈
            zero_one_knapsack_polytope
              (fun i ↦ (example_7_6_weights i : ℝ)) 5 := by
        simpa using hy
      have hpreimage :=
        (example76_mem_knapsackPolytope_reindex_iff
          (example76CoordinateEquiv.symm y)).mpr hyimage
      have hineq := hvalid hpreimage
      rw [example76_dotProduct_reindex, example76CoverRhs_eq] at hineq
      simpa using hineq

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: facet ownership of a lifted cover
face is preserved and reflected by the cyclic coordinate equivalence. -/
lemma example76FacetOwnerReindex_iff
    (α : Fin 5 → ℝ) :
    α ∈ facet_defining_liftings_of_cover_inequality
        (fun i ↦ (example_7_6_weights i : ℝ)) 5 example_7_6_cover ↔
      (fun i ↦ α (example76Reindex i)) ∈
        facet_defining_liftings_of_cover_inequality
          (fun i ↦ (example76ReindexedWeights i : ℝ))
          5
          (remark_7_5_cover (n := 5) 3) := by
  rw [mem_facet_defining_liftings_of_cover_inequality_iff,
    mem_facet_defining_liftings_of_cover_inequality_iff]
  have htransport :=
    isFacetOf_image_continuousLinearEquiv
      example76CoordinateEquiv
      (A := zero_one_knapsack_polytope
        (fun i ↦ (example76ReindexedWeights i : ℝ)) 5)
      (B := lifted_cover_face
        (fun i ↦ (example76ReindexedWeights i : ℝ))
        5
        (remark_7_5_cover (n := 5) 3)
        (fun i ↦ α (example76Reindex i)))
  rw [example76KnapsackPolytope_reindex_image,
    example76LiftedCoverFace_reindex_image] at htransport
  exact htransport.symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: membership in the full owner of
facet-defining minimal-cover liftings is invariant under cyclic reindexing. -/
lemma example76FacetDefiningReindex_iff
    (α : Fin 5 → ℝ) :
    α ∈ facet_defining_liftings_of_minimal_cover_inequality
        example_7_6_weights 5 example_7_6_cover ↔
      (fun i ↦ α (example76Reindex i)) ∈
        facet_defining_liftings_of_minimal_cover_inequality
          example76ReindexedWeights 5 (remark_7_5_cover (n := 5) 3) := by
  rw [mem_facet_defining_liftings_of_minimal_cover_inequality_iff,
    mem_facet_defining_liftings_of_minimal_cover_inequality_iff]
  constructor
  · rintro ⟨hvalid, hfacet⟩
    exact ⟨(example76ValidLiftingReindex_iff α).mp hvalid,
      (example76FacetOwnerReindex_iff α).mp hfacet⟩
  · rintro ⟨hvalid, hfacet⟩
    exact ⟨(example76ValidLiftingReindex_iff α).mpr hvalid,
      (example76FacetOwnerReindex_iff α).mpr hfacet⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean: the coefficient vector supplied
by Remark 7.5 is the reindexing of the displayed Example 7.6 vector. -/
lemma example76ReindexedLiftedVector_eq :
    remark_7_5_lifting_coeff
        (remark_7_5_cover (n := 5) 3)
        example76ReindexedLiftingFunction =
      fun i ↦ example_7_6_lifted_vector (example76Reindex i) := by
  -- Specialize the general lifted-coefficient transport to the concrete lifting profile.
  simpa [example76ReindexedLiftingFunction, example_7_6_lifted_vector,
    remark_7_5_lifting_coeff] using
      (example76LiftedCoverCoeff_reindex
        (fun i ↦ (example_7_6_lifting_function i : ℝ)))

/-- Example 7.6 (4). By Remark 7.5, the lifted inequality
`2x₁ + x₂ + x₃ + x₄ + x₅ ≤ 2` defines a facet of `conv(K)`. -/
theorem example_7_6_lifted_inequality_is_facet_defining :
    example_7_6_lifted_vector ∈
      facet_defining_liftings_of_minimal_cover_inequality
        example_7_6_weights
        5
        example_7_6_cover := by
  -- Apply Remark 7.5 in prefix coordinates, then transport its facet back.
  have hprefix :=
    remark_7_5_lifted_cover_inequality_is_facet_defining
      example76ReindexedWeights
      5
      (remark_7_5_cover (n := 5) 3)
      (remark_7_5_mu example76ReindexedWeights 3 example76ThreeLeFive)
      example76ReindexedLiftingFunction
      1
      example76ReindexedContext
      example76ReindexedIntervalIndices
      example76ReindexedStrongUpperBound
  have hreindexed :
      (fun i ↦ example_7_6_lifted_vector (example76Reindex i)) ∈
        facet_defining_liftings_of_minimal_cover_inequality
          example76ReindexedWeights 5 (remark_7_5_cover (n := 5) 3) := by
    rw [← example76ReindexedLiftedVector_eq]
    exact hprefix
  exact (example76FacetDefiningReindex_iff example_7_6_lifted_vector).mpr hreindexed

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_2/ch7_sec7_2_1_example_7_6.lean
Example 7.6 (5). By Remark 7.5, `2x₁ + x₂ + x₃ + x₄ + x₅ ≤ 2` is the unique
facet-defining lifting of the minimal cover inequality attached to `C = {3,4,5}`. -/
theorem example_7_6_unique_facet_defining_lifting
    {α : Fin 5 → ℝ}
    (hα : α ∈
      facet_defining_liftings_of_minimal_cover_inequality
        example_7_6_weights
        5
        example_7_6_cover) :
    α = example_7_6_lifted_vector := by
  -- Move to prefix coordinates, use Remark 7.5 uniqueness, and invert the permutation.
  have hreindexed := (example76FacetDefiningReindex_iff α).mp hα
  have heq :=
    remark_7_5_eq_of_mem_facet_defining_liftings
      example76ReindexedWeights
      5
      (remark_7_5_cover (n := 5) 3)
      (remark_7_5_mu example76ReindexedWeights 3 example76ThreeLeFive)
      example76ReindexedLiftingFunction
      1
      example76ReindexedContext
      example76ReindexedIntervalIndices
      example76ReindexedStrongUpperBound
      hreindexed
  have hreindexed_eq :
      (fun i ↦ α (example76Reindex i)) =
        fun i ↦ example_7_6_lifted_vector (example76Reindex i) :=
    heq.trans example76ReindexedLiftedVector_eq
  ext j
  have hcoordinate := congrFun hreindexed_eq (example76Reindex.symm j)
  simpa using hcoordinate

end Example76

#print axioms example_7_6_lifted_inequality_is_facet_defining
#print axioms example_7_6_unique_facet_defining_lifting
