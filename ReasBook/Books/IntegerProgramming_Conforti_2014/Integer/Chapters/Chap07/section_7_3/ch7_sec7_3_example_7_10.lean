import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

open scoped BigOperators

section Example710

variable {n : ℕ}

/-- The knapsack-cover excess `λ = ∑_{j ∈ C} a_j - b` from Example 7.10, viewed through the
single-node flow-cover owner from Theorem 7.9 after the standard coercion from natural weights
and capacity to real data. -/
abbrev knapsack_cover_excess
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n)) : ℝ :=
  flow_cover_excess (fun i ↦ (a i : ℝ)) (b : ℝ) C

/-- Expanding `knapsack_cover_excess a b C` recovers the Chapter 7 flow-cover excess on the
coerced knapsack data. -/
theorem knapsack_cover_excess_eq_flow_cover_excess
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n)) :
    knapsack_cover_excess a b C =
      flow_cover_excess (fun i ↦ (a i : ℝ)) (b : ℝ) C :=
  rfl

namespace IsMinimalKnapsackCover

/-- A minimal knapsack cover becomes a flow cover after coercing the weights and capacity to the
single-node flow-cover setting. -/
theorem toIsFlowCover
    {a : Fin n → ℕ} {b : ℕ} {C : Finset (Fin n)}
    (hC : IsMinimalKnapsackCover a b C) :
    IsFlowCover (fun i ↦ (a i : ℝ)) (b : ℝ) C := by
  refine ⟨?_⟩
  exact_mod_cast hC.sum_gt_capacity

end IsMinimalKnapsackCover

/-- Helper for Example 7.10: substituting `y_j = a_j x_j` sends any binary knapsack point to the
associated single-node flow set. -/
theorem knapsack_point_mem_single_node_flow
    (a : Fin n → ℕ) (b : ℕ)
    (x : Fin n → ℝ)
    (hx : x ∈ zero_one_knapsack_set (fun i ↦ (a i : ℝ)) (b : ℝ)) :
    (x, fun j ↦ (a j : ℝ) * x j) ∈
      single_node_flow_set (fun j ↦ (a j : ℝ)) (b : ℝ) := by
  rw [mem_single_node_flow_set_iff]
  rcases (mem_zero_one_knapsack_set_iff (fun i ↦ (a i : ℝ)) (b : ℝ) x).mp hx with
      ⟨hx_binary, hx_capacity⟩
  refine ⟨hx_binary, ?_, ?_, ?_⟩
  · -- Binary knapsack points make the substituted flow nonnegative coordinatewise.
    intro j
    rcases hx_binary j with hzero | hone
    · simp [hzero]
    · simp [hone]
  · -- The single-node capacity row is exactly the original knapsack inequality.
    simpa using hx_capacity
  · -- The upper bounds hold at equality after the substitution `y_j = a_j x_j`.
    intro j
    exact le_rfl

/-- For a minimal knapsack cover, each selected weight is at least the corresponding flow-cover
excess `λ = ∑_{j ∈ C} a_j - b`. -/
theorem minimal_knapsack_cover_excess_le_weight
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (j : Fin n) (hj : j ∈ C) :
    knapsack_cover_excess a b C ≤ a j := by
  -- Rewrite the full cover sum as the erased sum plus the selected weight.
  have hsum_le : C.sum a ≤ b + a j := by
    calc
      C.sum a = (C.erase j).sum a + a j := by
        rw [(Finset.sum_erase_add (s := C) (a := j) (f := a) hj).symm]
      _ ≤ b + a j := Nat.add_le_add_right (hC.erase_sum_le j hj) (a j)
  have hsum_le_real : (∑ i ∈ C, (a i : ℝ)) ≤ (b : ℝ) + a j := by
    exact_mod_cast hsum_le
  -- Rearranging gives the desired comparison between the excess and `a_j`.
  rw [knapsack_cover_excess_eq_flow_cover_excess, flow_cover_excess_eq_sum_sub]
  linarith

/-- Example 7.10. If `C` is a minimal cover for the `0,1` knapsack set
`K = {x ∈ {0,1}^n | ∑ j, a j * x j ≤ b}`, then substituting `y_j = a_j x_j` in the flow-cover
inequality yields the specialized valid inequality
`∑ j ∈ C, a j * x j + ∑ j ∈ C, (a j - λ) * (1 - x j) ≤ b`, where
`λ = ∑ j ∈ C, a j - b`. -/
theorem example_7_10_flow_cover_specialization
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (x : Fin n → ℝ)
    (hx : x ∈ zero_one_knapsack_set (fun i ↦ (a i : ℝ)) (b : ℝ)) :
    C.sum (fun j ↦ a j * x j) +
        C.sum (fun j ↦
          (a j - knapsack_cover_excess a b C) * (1 - x j)) ≤
      b := by
  -- Move the knapsack point onto the single-node flow face used in Theorem 7.9.
  have hPoint : (x, fun j ↦ (a j : ℝ) * x j) ∈
      single_node_flow_set (fun j ↦ (a j : ℝ)) (b : ℝ) :=
    knapsack_point_mem_single_node_flow a b x hx
  have hFlow :
      flow_cover_value (fun i ↦ (a i : ℝ)) (b : ℝ) C
        (x, fun j ↦ (a j : ℝ) * x j) ≤ b := by
    -- Apply the valid flow-cover inequality to the substituted point.
    exact single_node_flow_cover_inequality_valid
      (a := fun i ↦ (a i : ℝ))
      (b := (b : ℝ))
      (C := C)
      (ha_nonneg := fun i ↦ by
        have hnonneg : (0 : ℝ) ≤ (a i : ℝ) := by
          exact_mod_cast Nat.zero_le (a i)
        exact hnonneg)
      (hC := hC.toIsFlowCover)
      (p := (x, fun j ↦ (a j : ℝ) * x j))
      hPoint
  rw [flow_cover_value_eq, ← knapsack_cover_excess_eq_flow_cover_excess a b C] at hFlow
  -- Minimality makes every coefficient `a_j - λ` nonnegative, so the `max` terms disappear.
  have hMaxSum :
      (∑ j ∈ C, max ((a j : ℝ) - knapsack_cover_excess a b C) 0 * (1 - x j)) =
        C.sum (fun j ↦ (a j - knapsack_cover_excess a b C) * (1 - x j)) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hcoeff : 0 ≤ (a j : ℝ) - knapsack_cover_excess a b C := by
      exact sub_nonneg.mpr (minimal_knapsack_cover_excess_le_weight a b C hC j hj)
    simp [max_eq_left hcoeff]
  rw [hMaxSum] at hFlow
  simpa using hFlow

/-- Helper for Example 7.10: the specialized flow-cover left-hand side rearranges to the
capacity plus the cover-excess times the cover-gap. -/
theorem specialized_flow_cover_lhs_eq_capacity_add_excess_gap
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n))
    (x : Fin n → ℝ) :
    C.sum (fun j ↦ a j * x j) +
        C.sum (fun j ↦
          (a j - knapsack_cover_excess a b C) * (1 - x j)) =
      (b : ℝ) + knapsack_cover_excess a b C * (C.sum x - cover_inequality_rhs C) := by
  let lam : ℝ := knapsack_cover_excess a b C
  have hsum :
      (∑ j ∈ C, (a j : ℝ)) = (b : ℝ) + lam := by
    -- Rewrite the excess to the defining sum-minus-capacity form.
    rw [show lam = flow_cover_excess (fun i ↦ (a i : ℝ)) (b : ℝ) C by
      rfl]
    rw [flow_cover_excess_eq_sum_sub]
    ring
  -- First merge the two sums so each cover index contributes a single affine term.
  calc
    C.sum (fun j ↦ a j * x j) +
        C.sum (fun j ↦ (a j - knapsack_cover_excess a b C) * (1 - x j))
      = C.sum (fun j ↦ a j * x j) +
          C.sum (fun j ↦ (a j - lam) * (1 - x j)) := by
          simp [lam]
    _ = C.sum (fun j ↦ (a j : ℝ) * x j + (((a j : ℝ) - lam) * (1 - x j))) := by
          rw [← Finset.sum_add_distrib]
    _ = C.sum (fun j ↦ ((a j : ℝ) - lam) + lam * x j) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j ∈ C, ((a j : ℝ) - lam)) + ∑ j ∈ C, lam * x j := by
          rw [Finset.sum_add_distrib]
    _ = ((∑ j ∈ C, (a j : ℝ)) - (C.card : ℝ) * lam) + lam * C.sum x := by
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum]
          simp
    _ = ((b : ℝ) + lam - (C.card : ℝ) * lam) + lam * C.sum x := by
          rw [hsum]
    _ = (b : ℝ) + lam * (C.sum x - cover_inequality_rhs C) := by
          rw [cover_inequality_rhs_eq]
          ring

/-- Helper for Example 7.10: a minimal cover has strictly positive cover excess. -/
theorem minimal_knapsack_cover_excess_pos
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C) :
    0 < knapsack_cover_excess a b C := by
  have hsum_gt : (b : ℝ) < ∑ j ∈ C, (a j : ℝ) := by
    exact_mod_cast hC.sum_gt_capacity
  -- The excess is exactly `∑_{j ∈ C} a_j - b`, so positivity is the cover inequality itself.
  rw [knapsack_cover_excess_eq_flow_cover_excess, flow_cover_excess_eq_sum_sub]
  linarith

/-- Example 7.10. For a minimal knapsack cover, the specialized flow-cover inequality recovers
the usual cover inequality `∑ j ∈ C, x j ≤ |C| - 1`, stated with the chapter's canonical
right-hand side owner `cover_inequality_rhs C`. -/
theorem example_7_10_cover_inequality
    (a : Fin n → ℕ) (b : ℕ) (C : Finset (Fin n))
    (hC : IsMinimalKnapsackCover a b C)
    (x : Fin n → ℝ)
    (hx : x ∈ zero_one_knapsack_set (fun i ↦ (a i : ℝ)) (b : ℝ)) :
    C.sum x ≤ cover_inequality_rhs C := by
  have hSpecial := example_7_10_flow_cover_specialization a b C hC x hx
  rw [specialized_flow_cover_lhs_eq_capacity_add_excess_gap a b C x] at hSpecial
  by_contra hCover
  -- A strict violation of the cover inequality makes the excess term strictly positive.
  have hGap : 0 < C.sum x - cover_inequality_rhs C := by
    exact sub_pos.mpr (lt_of_not_ge hCover)
  have hExcess :
      0 < knapsack_cover_excess a b C * (C.sum x - cover_inequality_rhs C) := by
    exact mul_pos (minimal_knapsack_cover_excess_pos a b C hC) hGap
  linarith

end Example710
