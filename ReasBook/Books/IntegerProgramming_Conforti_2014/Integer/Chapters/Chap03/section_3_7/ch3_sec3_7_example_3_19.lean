import Mathlib.Analysis.Convex.Hull
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

/-- The `0,1` knapsack polytope is the convex hull of the corresponding `0,1` knapsack set. -/
def zero_one_knapsack_polytope {n : ℕ} (a : Fin n → ℝ) (b : ℝ) : Set (Fin n → ℝ) :=
  convexHull ℝ (zero_one_knapsack_set a b)

/-- The `0,1` knapsack polytope is defined as the convex hull of the corresponding feasible set. -/
theorem zero_one_knapsack_polytope_eq_convexHull {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    zero_one_knapsack_polytope a b = convexHull ℝ (zero_one_knapsack_set a b) := by
  -- This is the defining equation of the polytope.
  rfl

/-- The set of overweight indices consists of those coordinates whose weight exceeds the
capacity. -/
noncomputable def zero_one_knapsack_overweight_indices {n : ℕ} (a : Fin n → ℝ) (b : ℝ) :
    Finset (Fin n) :=
  Finset.univ.filter fun j ↦ b < a j

/-- Every point of the `0,1` knapsack polytope has zero coordinates on the overweight indices. -/
theorem zero_one_knapsack_polytope_subset_zero_on_overweight {n : ℕ}
    (a : Fin n → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j) :
    zero_one_knapsack_polytope a b ⊆
      {x : Fin n → ℝ | ∀ j ∈ zero_one_knapsack_overweight_indices a b, x j = 0} := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  refine convexHull_min ?_ ?_
  · intro x hx j hj
    rw [mem_zero_one_knapsack_set_iff] at hx
    rcases hx with ⟨hbin, hweight⟩
    have hj_weight : b < a j := by
      simpa [zero_one_knapsack_overweight_indices] using hj
    obtain hxj | hxj := hbin j
    · exact hxj
    · -- If the overweight coordinate were `1`, its weight would already exceed the capacity.
      have hterm_nonneg : ∀ i, 0 ≤ a i * x i := by
        intro i
        obtain hxi | hxi := hbin i
        · simp [hxi]
        · simp [hxi, ha i]
      have hle_sum : a j * x j ≤ ∑ i, a i * x i := by
        exact Finset.single_le_sum (fun i _ ↦ hterm_nonneg i) (Finset.mem_univ j)
      rw [hxj, mul_one] at hle_sum
      have hle_b : a j ≤ b := by
        linarith
      exact False.elim <| (not_le.mpr hj_weight) hle_b
  · -- Vanishing of fixed coordinates is preserved under convex combinations.
    intro x hx y hy α β hα hβ hsum j hj
    simp [Pi.add_apply, Pi.smul_apply, hx j hj, hy j hj]

/-- The origin belongs to the `0,1` knapsack polytope whenever the capacity is nonnegative. -/
theorem zero_mem_zero_one_knapsack_polytope {n : ℕ} (a : Fin n → ℝ) {b : ℝ} (hb : 0 ≤ b) :
    (0 : Fin n → ℝ) ∈ zero_one_knapsack_polytope a b := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  -- The origin is itself a feasible binary point.
  apply subset_convexHull ℝ (zero_one_knapsack_set a b)
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    left
    simp
  · simpa using hb

/-- If the weight of coordinate `j` does not exceed the capacity, then the `j`th unit vector
belongs to the `0,1` knapsack polytope. -/
theorem single_one_mem_zero_one_knapsack_polytope {n : ℕ} (a : Fin n → ℝ) {b : ℝ} (j : Fin n)
    (hj : j ∉ zero_one_knapsack_overweight_indices a b) :
    Pi.single j (1 : ℝ) ∈ zero_one_knapsack_polytope a b := by
  rw [zero_one_knapsack_polytope_eq_convexHull]
  -- The `j`th unit vector is binary and its weight is exactly `a j`.
  apply subset_convexHull ℝ (zero_one_knapsack_set a b)
  rw [mem_zero_one_knapsack_set_iff]
  constructor
  · intro i
    by_cases hij : i = j
    · right
      subst hij
      simp
    · left
      simp [hij]
  · have hj_le : a j ≤ b := by
      refine not_lt.mp ?_
      simpa [zero_one_knapsack_overweight_indices] using hj
    simpa [Pi.single_apply] using hj_le

/-- Helper for Example 3.19: the knapsack polytope lies in the coordinate subspace supported on
the non-overweight indices. -/
lemma zero_one_knapsack_polytope_subset_spanSubset_nonoverweight {n : ℕ}
    (a : Fin n → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j) :
    zero_one_knapsack_polytope a b ⊆
      (Pi.spanSubset ℝ
        (↑(Finset.univ \ zero_one_knapsack_overweight_indices a b) : Set (Fin n)) :
          Set (Fin n → ℝ)) := by
  intro x hx
  change x ∈
    Pi.spanSubset ℝ (↑(Finset.univ \ zero_one_knapsack_overweight_indices a b) : Set (Fin n))
  rw [Pi.mem_spanSubset_iff]
  intro j hj
  -- A coordinate outside the non-overweight support is overweight, so it must vanish on `P`.
  have hj_over : j ∈ zero_one_knapsack_overweight_indices a b := by
    by_contra hj_not
    exact hj (by simp [hj_not])
  exact zero_one_knapsack_polytope_subset_zero_on_overweight a b ha hx j hj_over

/-- Helper for Example 3.19: the linear span of the knapsack polytope is exactly the supported
coordinate submodule on the non-overweight indices. -/
lemma zero_one_knapsack_polytope_span_eq_spanSubset_nonoverweight {n : ℕ}
    (a : Fin n → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j) :
    Submodule.span ℝ (zero_one_knapsack_polytope a b) =
      Pi.spanSubset ℝ (↑(Finset.univ \ zero_one_knapsack_overweight_indices a b) :
        Set (Fin n)) := by
  let K : Set (Fin n) := ↑(Finset.univ \ zero_one_knapsack_overweight_indices a b)
  refine le_antisymm ?_ ?_
  · -- The polytope already lies in the supported-coordinate submodule.
    exact Submodule.span_le.mpr (zero_one_knapsack_polytope_subset_spanSubset_nonoverweight a b ha)
  · -- Each basis vector in a non-overweight direction belongs to the polytope, hence to its span.
    rw [Pi.spanSubset]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, hjK, rfl⟩
    have hj_not_over : j ∉ zero_one_knapsack_overweight_indices a b := by
      simpa [K] using hjK
    have hsingle : Pi.single j (1 : ℝ) ∈ zero_one_knapsack_polytope a b :=
      single_one_mem_zero_one_knapsack_polytope a j hj_not_over
    simpa [Pi.basisFun_apply] using Submodule.subset_span hsingle

/-- Example 3.19. The `0,1` knapsack polytope
`conv ({x ∈ {0,1}^n | ∑ i, a i * x i ≤ b})` has dimension `n - |J|`, where
`J = {j | a j > b}`. -/
theorem zero_one_knapsack_polytope_finrank_direction_affineSpan {n : ℕ}
    (a : Fin n → ℝ) (b : ℝ) (ha : ∀ j, 0 ≤ a j) (hb : 0 ≤ b) :
    Module.finrank ℝ (affineSpan ℝ (zero_one_knapsack_polytope a b)).direction =
      n - (zero_one_knapsack_overweight_indices a b).card := by
  let P := zero_one_knapsack_polytope a b
  let J := zero_one_knapsack_overweight_indices a b
  let K : Set (Fin n) := ↑(Finset.univ \ J)
  have h0 : (0 : Fin n → ℝ) ∈ P := by
    simpa [P] using zero_mem_zero_one_knapsack_polytope a hb
  have h_direction : (affineSpan ℝ P).direction = Submodule.span ℝ P := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [vsub_eq_sub]
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp [vsub_eq_sub]
  have h_span : Submodule.span ℝ P = Pi.spanSubset ℝ K := by
    simpa [P, J, K] using zero_one_knapsack_polytope_span_eq_spanSubset_nonoverweight a b ha
  have hcard : (Finset.univ \ J).card = n - J.card := by
    simpa using Finset.card_sdiff_of_subset (Finset.subset_univ J)
  -- The source proof computes the dimension from the supported-coordinate subspace.
  calc
    Module.finrank ℝ (affineSpan ℝ P).direction
        = Module.finrank ℝ (Submodule.span ℝ P) := by
            rw [h_direction]
    _ = Module.finrank ℝ (Pi.spanSubset ℝ K) := by
      rw [h_span]
    _ = Set.ncard K := by
      rw [Pi.dim_spanSubset]
    _ = (Finset.univ \ J).card := by
      simpa [K] using (Set.ncard_coe_finset (Finset.univ \ J))
    _ = n - J.card := hcard
    _ = n - (zero_one_knapsack_overweight_indices a b).card := by
      rfl
