/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

section Exercise717

variable {n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean`: the row whose two blocks
encode the normalized flow-cover slacks. -/
noncomputable def flowCoverGomoryRow
    (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ) : Fin (n + n) → ℝ :=
  Fin.append
    (fun j ↦ if j ∈ C then (1 / 2 : ℝ) * (min (a j) lam / lam) else 0)
    (fun j ↦ if j ∈ C then (1 / 2 : ℝ) * (1 / lam) else 0)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean`: the flow-cover inequality is
equivalent to its normalization by the positive cover excess. -/
lemma flowCoverNormalizedSlack_iff
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (p : (Fin n → ℝ) × (Fin n → ℝ))
    (hlam : 0 < flow_cover_excess a b C) :
    flow_cover_value a b C p ≤ b ↔
      1 ≤
        (∑ j ∈ C,
            (min (a j) (flow_cover_excess a b C) / flow_cover_excess a b C) *
              (1 - p.1 j)) +
          ∑ j ∈ C, (1 / flow_cover_excess a b C) * (a j * p.1 j - p.2 j) := by
  have hmin_add_max (j : Fin n) :
      min (a j) (flow_cover_excess a b C) +
          max (a j - flow_cover_excess a b C) 0 =
        a j := by
    -- Split at the excess to identify the complementary `min` and `max` terms.
    rcases le_total (a j) (flow_cover_excess a b C) with haj | haj
    · rw [min_eq_left haj, max_eq_right (sub_nonpos.mpr haj)]
      ring
    · rw [min_eq_right haj, max_eq_left (sub_nonneg.mpr haj)]
      ring
  have hflow_sum :
      flow_cover_value a b C p =
        ∑ j ∈ C,
          (p.2 j +
            max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j)) := by
    -- Put both parts of the flow-cover left-hand side under one finite sum.
    rw [flow_cover_value_eq, Finset.sum_add_distrib]
  have hslack_sum :
      (∑ j ∈ C,
          min (a j) (flow_cover_excess a b C) * (1 - p.1 j)) +
          ∑ j ∈ C, (a j * p.1 j - p.2 j) =
        ∑ j ∈ C,
          (min (a j) (flow_cover_excess a b C) * (1 - p.1 j) +
            (a j * p.1 j - p.2 j)) := by
    -- Likewise, collect the two unnormalized slack blocks pointwise.
    rw [Finset.sum_add_distrib]
  have hbalance :
      flow_cover_value a b C p +
          ((∑ j ∈ C,
              min (a j) (flow_cover_excess a b C) * (1 - p.1 j)) +
            ∑ j ∈ C, (a j * p.1 j - p.2 j)) =
        ∑ j ∈ C, a j := by
    -- At each cover index, the flow term and the two slacks add back to the capacity.
    rw [hflow_sum, hslack_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    calc
      p.2 j + max (a j - flow_cover_excess a b C) 0 * (1 - p.1 j) +
            (min (a j) (flow_cover_excess a b C) * (1 - p.1 j) +
              (a j * p.1 j - p.2 j)) =
          (min (a j) (flow_cover_excess a b C) +
              max (a j - flow_cover_excess a b C) 0) +
            (a j -
                (min (a j) (flow_cover_excess a b C) +
                  max (a j - flow_cover_excess a b C) 0)) * p.1 j := by
        ring
      _ = a j := by rw [hmin_add_max j]; ring
  have hnormalized_first :
      (∑ j ∈ C,
          (min (a j) (flow_cover_excess a b C) / flow_cover_excess a b C) *
            (1 - p.1 j)) =
        (∑ j ∈ C,
            min (a j) (flow_cover_excess a b C) * (1 - p.1 j)) /
          flow_cover_excess a b C := by
    -- Division by the fixed excess commutes with the first finite sum.
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  have hnormalized_second :
      (∑ j ∈ C, (1 / flow_cover_excess a b C) * (a j * p.1 j - p.2 j)) =
        (∑ j ∈ C, (a j * p.1 j - p.2 j)) / flow_cover_excess a b C := by
    -- The continuous slack block has the same common denominator.
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  have hnormalized :
      (∑ j ∈ C,
          (min (a j) (flow_cover_excess a b C) / flow_cover_excess a b C) *
            (1 - p.1 j)) +
          ∑ j ∈ C, (1 / flow_cover_excess a b C) * (a j * p.1 j - p.2 j) =
        ((∑ j ∈ C,
            min (a j) (flow_cover_excess a b C) * (1 - p.1 j)) +
          ∑ j ∈ C, (a j * p.1 j - p.2 j)) /
            flow_cover_excess a b C := by
    -- Pull the common reciprocal of the positive excess outside both finite sums.
    rw [hnormalized_first, hnormalized_second, add_div]
  have hflow_iff :
      flow_cover_value a b C p ≤ b ↔
        flow_cover_excess a b C ≤
          (∑ j ∈ C,
              min (a j) (flow_cover_excess a b C) * (1 - p.1 j)) +
            ∑ j ∈ C, (a j * p.1 j - p.2 j) := by
    -- The balance identity and `lambda = sum a - b` move the inequality to total slack.
    have hexcess : flow_cover_excess a b C = (∑ j ∈ C, a j) - b :=
      flow_cover_excess_eq_sum_sub a b C
    constructor <;> intro h <;> linarith [hbalance, hexcess]
  -- Positive division converts the unnormalized lower bound by `lambda` into right-hand side one.
  rw [hflow_iff, hnormalized, le_div_iff₀ hlam]
  ring_nf

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean`: on the integer block, the
explicit row produces the normalized capped-capacity coefficient. -/
lemma flowCoverGomoryCoefficient_castAdd
    (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 < lam) (ha_nonneg : ∀ j, 0 ≤ a j)
    (hhalf : 0 < Int.fract (1 / 2 : ℝ)) (j : Fin n) :
    gomory_mixed_integer_inequality_coefficient
        (Finset.univ.image (Fin.castAdd n)) (flowCoverGomoryRow a C lam)
        (1 / 2 : ℝ) hhalf (Fin.castAdd n j) =
      if j ∈ C then min (a j) lam / lam else 0 := by
  have hmem : Fin.castAdd n j ∈ Finset.univ.image (Fin.castAdd n) := by
    simp
  have hfract_half : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
    exact Int.fract_eq_self.mpr (by norm_num)
  by_cases hj : j ∈ C
  · have hratio_nonneg : 0 ≤ min (a j) lam / lam :=
      div_nonneg (le_min (ha_nonneg j) hlam.le) hlam.le
    have hratio_le_one : min (a j) lam / lam ≤ 1 :=
      (div_le_one hlam).mpr (min_le_right (a j) lam)
    have halpha_nonneg : 0 ≤ (1 / 2 : ℝ) * (min (a j) lam / lam) :=
      mul_nonneg (by norm_num) hratio_nonneg
    have halpha_lt_one : (1 / 2 : ℝ) * (min (a j) lam / lam) < 1 := by
      nlinarith
    have hfract_alpha :
        Int.fract ((1 / 2 : ℝ) * (min (a j) lam / lam)) =
          (1 / 2 : ℝ) * (min (a j) lam / lam) :=
      Int.fract_eq_self.mpr ⟨halpha_nonneg, halpha_lt_one⟩
    have hbranch :
        Int.fract ((1 / 2 : ℝ) * (min (a j) lam / lam)) ≤
          Int.fract (1 / 2 : ℝ) := by
      rw [hfract_alpha, hfract_half]
      nlinarith
    -- Both fractional parts are explicit, so the first integer coefficient branch cancels `1/2`.
    rw [gomory_mixed_integer_inequality_coefficient_eq, if_pos hmem]
    simp only [flowCoverGomoryRow, Fin.append_left, if_pos hj, hfract_alpha, hfract_half]
    rw [if_pos (by nlinarith [hratio_le_one])]
    ring
  · -- Off the cover the chosen row entry, hence its GMI coefficient, is zero.
    rw [gomory_mixed_integer_inequality_coefficient_eq, if_pos hmem]
    simp only [flowCoverGomoryRow, Fin.append_left, if_neg hj, Int.fract_zero, hfract_half,
      zero_div]
    norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean`: on the continuous block, the
explicit row produces the reciprocal-excess coefficient. -/
lemma flowCoverGomoryCoefficient_natAdd
    (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (hlam : 0 < lam) (hhalf : 0 < Int.fract (1 / 2 : ℝ)) (j : Fin n) :
    gomory_mixed_integer_inequality_coefficient
        (Finset.univ.image (Fin.castAdd n)) (flowCoverGomoryRow a C lam)
        (1 / 2 : ℝ) hhalf (Fin.natAdd n j) =
      if j ∈ C then 1 / lam else 0 := by
  have hnotmem : Fin.natAdd n j ∉ Finset.univ.image (Fin.castAdd n) := by
    intro hjmem
    rcases Finset.mem_image.mp hjmem with ⟨i, hi, hij⟩
    have hval := congrArg Fin.val hij
    simp only [Fin.val_natAdd, Fin.val_castAdd] at hval
    omega
  have hfract_half : Int.fract (1 / 2 : ℝ) = 1 / 2 := by
    exact Int.fract_eq_self.mpr (by norm_num)
  by_cases hj : j ∈ C
  · have hrow_nonneg : 0 ≤ (1 / 2 : ℝ) * (1 / lam) :=
      mul_nonneg (by norm_num) (one_div_nonneg.mpr hlam.le)
    -- The second block is continuous and nonnegative, so its coefficient divides by `1/2`.
    rw [gomory_mixed_integer_inequality_coefficient_eq, if_neg hnotmem]
    simp only [flowCoverGomoryRow, Fin.append_right, if_pos hj, if_pos hrow_nonneg, hfract_half]
    ring
  · -- Off the cover the continuous row entry is zero as well.
    rw [gomory_mixed_integer_inequality_coefficient_eq, if_neg hnotmem]
    simp only [flowCoverGomoryRow, Fin.append_right, if_neg hj, zero_div]
    norm_num

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean`: splitting the encoded vector
into its two blocks turns the complete GMI sum into the two normalized slack sums. -/
lemma flowCoverGomoryWeightedSum_eq
    (a : Fin n → ℝ) (C : Finset (Fin n)) (lam : ℝ)
    (u v : Fin n → ℝ) (hlam : 0 < lam) (ha_nonneg : ∀ j, 0 ≤ a j)
    (hhalf : 0 < Int.fract (1 / 2 : ℝ)) :
    (∑ i : Fin (n + n),
        gomory_mixed_integer_inequality_coefficient
            (Finset.univ.image (Fin.castAdd n)) (flowCoverGomoryRow a C lam)
            (1 / 2 : ℝ) hhalf i * Fin.append u v i) =
      (∑ j ∈ C, (min (a j) lam / lam) * u j) +
        ∑ j ∈ C, (1 / lam) * v j := by
  classical
  -- Split `Fin (n+n)`, apply the two block formulas, and discard the zero terms off `C`.
  rw [Fin.sum_univ_add]
  simp only [flowCoverGomoryCoefficient_castAdd a C lam hlam ha_nonneg hhalf,
    flowCoverGomoryCoefficient_natAdd a C lam hlam hhalf, Fin.append_left, Fin.append_right,
    ite_mul, zero_mul]
  simp

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_17.lean

Exercise 7.17. Every flow cover inequality `(7.14)` for the single-node flow set can be realized
as a Gomory mixed integer inequality after encoding `(x,y)` as a mixed-integer vector in which the
`x`-coordinates are the integer variables. -/
theorem exercise_7_17_flow_cover_inequality_is_gomory_mixed_integer
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n))
    (ha_nonneg : ∀ j, 0 ≤ a j) (hb_nonneg : 0 ≤ b)
    (hC : IsFlowCover a b C) :
    ∃ α : Fin (n + n) → ℝ, ∃ β : ℝ, ∃ hβ : 0 < Int.fract β,
      ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
        flow_cover_value a b C p ≤ b ↔
          Fin.append (fun j ↦ 1 - p.1 j) (fun j ↦ a j * p.1 j - p.2 j) ∈
            gomory_mixed_integer_inequality (Finset.univ.image (Fin.castAdd n)) α β hβ := by
  have hlam : 0 < flow_cover_excess a b C := flow_cover_excess_pos a b C hC
  have hhalf : 0 < Int.fract (1 / 2 : ℝ) := by
    rw [Int.fract_eq_self.mpr (by norm_num)]
    norm_num
  refine ⟨flowCoverGomoryRow a C (flow_cover_excess a b C), (1 / 2 : ℝ), hhalf, ?_⟩
  intro p
  -- Membership reduces to the weighted normalized slack, which is exactly the flow-cover bound.
  rw [mem_gomory_mixed_integer_inequality_iff]
  rw [flowCoverGomoryWeightedSum_eq a C (flow_cover_excess a b C)
    (fun j ↦ 1 - p.1 j) (fun j ↦ a j * p.1 j - p.2 j) hlam ha_nonneg hhalf]
  exact flowCoverNormalizedSlack_iff a b C p hlam

end Exercise717
