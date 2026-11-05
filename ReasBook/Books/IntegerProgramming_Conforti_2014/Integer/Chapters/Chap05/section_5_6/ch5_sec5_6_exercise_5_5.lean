/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_4.ch5_sec5_1_4_definition_5_1_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_definition_3_14_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped BigOperators Matrix

section Exercise55

variable {m n : ℕ}

/-- Helper for Exercise 5.5: the split vector built from the aggregated row has integral dot
product against every point whose `I`-coordinates are integral. -/
lemma gomory_mixed_integer_split_vector_dot_integral
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (x : Fin n → ℝ)
    (hx_int : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)) :
    ∃ z : ℤ,
      ∑ j : Fin n, (gomory_mixed_integer_split_vector I α β j : ℝ) * x j = (z : ℝ) := by
  classical
  by_cases hzero : gomory_mixed_integer_split_vector I α β = 0
  · -- If the split vector vanishes identically, its dot product is the integer `0`.
    refine ⟨0, by simp [hzero]⟩
  · let s : Split I := gomory_mixed_integer_split I α β hzero
    -- Otherwise we can use the existing split-integrality theorem for the supported split.
    obtain ⟨z, hz⟩ := split_dot_integral_of_integral_coordinates I s hx_int
    refine ⟨z, ?_⟩
    simpa [s, split_dot_eq_sum]

/-- Helper for Exercise 5.5: every coefficient in the Gomory mixed integer inequality is the
maximum of the two normalized residual gauges attached to the split vector. -/
lemma gomory_mixed_integer_coefficient_eq_max_residual_ratio
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (hβ : 0 < Int.fract β)
    (j : Fin n) :
    gomory_mixed_integer_inequality_coefficient I α β hβ j =
      max ((α j - gomory_mixed_integer_split_vector I α β j) / Int.fract β)
        (-(α j - gomory_mixed_integer_split_vector I α β j) / (1 - Int.fract β)) := by
  by_cases hj : j ∈ I
  · -- On integer-variable coordinates, the residual is either the fractional part or its
    -- negative complement according to the defining MIR case split.
    rw [gomory_mixed_integer_inequality_coefficient_eq I α β hβ j, if_pos hj]
    by_cases hfract : Int.fract (α j) ≤ Int.fract β
    · rw [if_pos hfract]
      have hresidual :
          α j - gomory_mixed_integer_split_vector I α β j = Int.fract (α j) := by
        rw [gomory_mixed_integer_split_vector, if_pos hj, if_pos hfract]
        linarith [Int.floor_add_fract (α j)]
      rw [hresidual]
      have hleft_nonneg : 0 ≤ Int.fract (α j) / Int.fract β := by
        exact div_nonneg (Int.fract_nonneg _) hβ.le
      have hright_nonpos : -(Int.fract (α j)) / (1 - Int.fract β) ≤ 0 := by
        have hden_nonneg : 0 ≤ 1 - Int.fract β := sub_nonneg.mpr (Int.fract_lt_one β).le
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Int.fract_nonneg _))
          hden_nonneg
      exact (max_eq_left (le_trans hright_nonpos hleft_nonneg)).symm
    · rw [if_neg hfract]
      have hfract_ne : Int.fract (α j) ≠ 0 := by
        intro hzero
        have : Int.fract (α j) ≤ Int.fract β := by
          exact hzero ▸ Int.fract_nonneg β
        exact hfract this
      have hresidual :
          α j - gomory_mixed_integer_split_vector I α β j = -(1 - Int.fract (α j)) := by
        rw [gomory_mixed_integer_split_vector, if_pos hj, if_neg hfract]
        have hceil :
            ((⌈α j⌉ : ℤ) : ℝ) - α j = 1 - Int.fract (α j) := by
          simpa using Int.ceil_sub_self_eq (a := α j) hfract_ne
        linarith
      rw [hresidual, neg_neg]
      have hleft_nonpos : -(1 - Int.fract (α j)) / Int.fract β ≤ 0 := by
        have hnum_nonpos : -(1 - Int.fract (α j)) ≤ 0 := by
          have hnum_nonneg : 0 ≤ 1 - Int.fract (α j) := by
            exact sub_nonneg.mpr (Int.fract_lt_one (α j)).le
          exact neg_nonpos.mpr hnum_nonneg
        exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hβ.le
      have hright_nonneg : 0 ≤ (1 - Int.fract (α j)) / (1 - Int.fract β) := by
        have hnum_nonneg : 0 ≤ 1 - Int.fract (α j) := by
          exact sub_nonneg.mpr (Int.fract_lt_one (α j)).le
        have hden_nonneg : 0 ≤ 1 - Int.fract β := by
          exact sub_nonneg.mpr (Int.fract_lt_one β).le
        exact div_nonneg hnum_nonneg hden_nonneg
      exact (max_eq_right (le_trans hleft_nonpos hright_nonneg)).symm
  · -- On continuous-variable coordinates, the split vector vanishes and the coefficient only
    -- depends on the sign of the aggregated row entry.
    rw [gomory_mixed_integer_inequality_coefficient_eq I α β hβ j, if_neg hj]
    have hsplit_zero : gomory_mixed_integer_split_vector I α β j = 0 :=
      gomory_mixed_integer_split_vector_eq_zero_of_not_mem I α β hj
    rw [hsplit_zero]
    by_cases hα : 0 ≤ α j
    · rw [if_pos hα]
      have hleft_nonneg : 0 ≤ α j / Int.fract β := by
        exact div_nonneg hα hβ.le
      have hright_nonpos : -α j / (1 - Int.fract β) ≤ 0 := by
        have hden_nonneg : 0 ≤ 1 - Int.fract β := by
          exact sub_nonneg.mpr (Int.fract_lt_one β).le
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) hden_nonneg
      simpa using (max_eq_left (le_trans hright_nonpos hleft_nonneg)).symm
    · rw [if_neg hα]
      have hα_nonpos : α j ≤ 0 := le_of_not_ge hα
      have hleft_nonpos : α j / Int.fract β ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hα_nonpos hβ.le
      have hright_nonneg : 0 ≤ -α j / (1 - Int.fract β) := by
        have hden_nonneg : 0 ≤ 1 - Int.fract β := by
          exact sub_nonneg.mpr (Int.fract_lt_one β).le
        exact div_nonneg (neg_nonneg.mpr hα_nonpos) hden_nonneg
      simpa using (max_eq_right (le_trans hleft_nonpos hright_nonneg)).symm

/-- Helper for Exercise 5.5: an integer shift of the right-hand side fractional part always
forces at least one of the two MIR gauges to be at least `1`. -/
lemma one_le_max_residual_ratio_of_integer_shift
    (f : ℝ)
    (hf_pos : 0 < f)
    (hf_lt : f < 1)
    (k : ℤ) :
    1 ≤ max (((k : ℝ) + f) / f) (-((k : ℝ) + f) / (1 - f)) := by
  by_cases hk : 0 ≤ k
  · -- Nonnegative integer shifts make the positive residual gauge large enough on their own.
    have hk_real : 0 ≤ (k : ℝ) := by exact_mod_cast hk
    have hdiv_nonneg : 0 ≤ (k : ℝ) / f := by
      exact div_nonneg hk_real hf_pos.le
    have hfirst : 1 ≤ ((k : ℝ) + f) / f := by
      have hf_ne : f ≠ 0 := ne_of_gt hf_pos
      have hrewrite : ((k : ℝ) + f) / f = (k : ℝ) / f + 1 := by
        field_simp [hf_ne]
      rw [hrewrite]
      linarith
    exact le_trans hfirst (le_max_left _ _)
  · -- Negative integer shifts are at most `-1`, so the negative residual gauge is large enough.
    have hk_le : k ≤ -1 := by omega
    have hk_real : (k : ℝ) ≤ -1 := by exact_mod_cast hk_le
    have hden_pos : 0 < 1 - f := by linarith
    have hsecond : 1 ≤ -((k : ℝ) + f) / (1 - f) := by
      rw [one_le_div hden_pos]
      linarith
    exact le_trans hsecond (le_max_right _ _)

/-- Helper for Exercise 5.5: every nonnegative mixed-integer point satisfying the aggregated row
equation also satisfies the associated Gomory mixed integer inequality. -/
lemma gomory_mixed_integer_inequality_valid_of_aggregated_equation
    (I : Finset (Fin n))
    (α : Fin n → ℝ)
    (β : ℝ)
    (x : Fin n → ℝ)
    (hβ : 0 < Int.fract β)
    (hx_eq : α ⬝ᵥ x = β)
    (hx_nonneg : 0 ≤ x)
    (hx_int : ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)) :
    x ∈ gomory_mixed_integer_inequality I α β hβ := by
  rw [mem_gomory_mixed_integer_inequality_iff I α β hβ x]
  let π : Fin n → ℤ := gomory_mixed_integer_split_vector I α β
  let f : ℝ := Int.fract β
  have hf_pos : 0 < f := hβ
  have hf_lt : f < 1 := by
    simpa [f] using Int.fract_lt_one β
  obtain ⟨z, hz⟩ := gomory_mixed_integer_split_vector_dot_integral I α β x hx_int
  have hresidual_sum : ∑ j : Fin n, (α j - π j) * x j = β - (z : ℝ) := by
    -- Separate the aggregated row into its split-integer part and its residual part.
    calc
      ∑ j : Fin n, (α j - π j) * x j
          = ∑ j : Fin n, α j * x j - ∑ j : Fin n, (π j : ℝ) * x j := by
              simp [sub_mul, Finset.sum_sub_distrib]
      _ = α ⬝ᵥ x - (z : ℝ) := by
            simp [dotProduct, π, hz]
      _ = β - (z : ℝ) := by rw [hx_eq]
  let k : ℤ := Int.floor β - z
  have hshift : β - (z : ℝ) = (k : ℝ) + f := by
    -- The residual sum has the same fractional part as `β`, shifted by an integer.
    have hdecomp' : (Int.floor β : ℝ) + Int.fract β = β := Int.floor_add_fract β
    have hdecomp : β = (Int.floor β : ℝ) + f := by
      dsimp [f]
      exact hdecomp'.symm
    calc
      β - (z : ℝ) = (Int.floor β : ℝ) + f - z := by
        conv_lhs => rw [hdecomp]
      _ = (Int.floor β : ℝ) - (z : ℝ) + f := by ring
      _ = ((Int.floor β - z : ℤ) : ℝ) + f := by
            rw [Int.cast_sub]
      _ = (k : ℝ) + f := by
            simp [k]
  have hleft_component :
      ∀ j : Fin n,
        ((α j - π j) / f) * x j ≤
          gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    intro j
    -- Each coefficient dominates the positive residual gauge, and `x_j` is nonnegative.
    have hcoeff :
        (α j - π j) / f ≤ gomory_mixed_integer_inequality_coefficient I α β hβ j := by
      rw [gomory_mixed_integer_coefficient_eq_max_residual_ratio I α β hβ j]
      change
        (α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / Int.fract β ≤
          max ((α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / Int.fract β)
            (-(α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / (1 - Int.fract β))
      exact le_max_left _ _
    exact mul_le_mul_of_nonneg_right hcoeff (hx_nonneg j)
  have hright_component :
      ∀ j : Fin n,
        (-(α j - π j) / (1 - f)) * x j ≤
          gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    intro j
    -- The same coefficient also dominates the negative residual gauge.
    have hcoeff :
        -(α j - π j) / (1 - f) ≤ gomory_mixed_integer_inequality_coefficient I α β hβ j := by
      rw [gomory_mixed_integer_coefficient_eq_max_residual_ratio I α β hβ j]
      change
        -(α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / (1 - Int.fract β) ≤
          max ((α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / Int.fract β)
            (-(α j - (gomory_mixed_integer_split_vector I α β j : ℝ)) / (1 - Int.fract β))
      exact le_max_right _ _
    exact mul_le_mul_of_nonneg_right hcoeff (hx_nonneg j)
  have hleft_sum :
      (β - (z : ℝ)) / f ≤
        ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    -- Summing the pointwise lower bounds controls the positive residual gauge of the row.
    calc
      (β - (z : ℝ)) / f = (∑ j : Fin n, (α j - π j) * x j) / f := by
        rw [← hresidual_sum]
      _ = ∑ j : Fin n, ((α j - π j) / f) * x j := by
            rw [div_eq_mul_inv, Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [div_eq_mul_inv]
            ring
      _ ≤ ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
            exact Finset.sum_le_sum fun j _ ↦ hleft_component j
  have hright_sum :
      -((β - (z : ℝ)) / (1 - f)) ≤
        ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    -- Summing the pointwise lower bounds also controls the negative residual gauge.
    calc
      -((β - (z : ℝ)) / (1 - f))
          = -((∑ j : Fin n, (α j - π j) * x j) / (1 - f)) := by
              rw [← hresidual_sum]
      _ = ∑ j : Fin n, -((α j - π j) * x j * (1 - f)⁻¹) := by
            rw [div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_neg_distrib]
      _ = ∑ j : Fin n, (-(α j - π j) / (1 - f)) * x j := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [div_eq_mul_inv]
            ring
      _ ≤ ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
            exact Finset.sum_le_sum fun j _ ↦ hright_component j
  have hmax :
      max ((β - (z : ℝ)) / f) (-((β - (z : ℝ)) / (1 - f))) ≤
        ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := by
    exact max_le_iff.mpr ⟨hleft_sum, hright_sum⟩
  -- The residual sum is an integer shift of `f`, so one of the MIR gauges is at least `1`.
  calc
    1 ≤ max (((k : ℝ) + f) / f) (-((k : ℝ) + f) / (1 - f)) := by
          exact one_le_max_residual_ratio_of_integer_shift f hf_pos hf_lt k
    _ = max (((k : ℝ) + f) / f) (-(((k : ℝ) + f) / (1 - f))) := by
          rw [neg_div]
    _ = max ((β - (z : ℝ)) / f) (-((β - (z : ℝ)) / (1 - f))) := by
          rw [hshift]
    _ ≤ ∑ j : Fin n, gomory_mixed_integer_inequality_coefficient I α β hβ j * x j := hmax

/-- Exercise 5.5. Let `P = {x ∈ ℝ_+^n | A x = b}` and let `α x = β` be a linear combination of
the equations in `A x = b`, with `I` recording the integer-variable coordinates. If the
right-hand side is fractional, then the normalized inequality obtained by the Gomory mixed
integer coefficient formula is valid for every point of the mixed-integer feasible set. -/
theorem exercise_5_5_gomory_mixed_integer_inequality
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Finset (Fin n))
    (u : Fin m → ℝ)
    (hβ : 0 < Int.fract (u ⬝ᵥ b)) :
    standard_equality_form A b ∩ {x : Fin n → ℝ | ∀ j ∈ I, ∃ z : ℤ, x j = (z : ℝ)} ⊆
      gomory_mixed_integer_inequality I (u ᵥ* A) (u ⬝ᵥ b) hβ := by
  intro x hx
  rcases (mem_standard_equality_form_inter_integral_iff A b I x).1 hx with
    ⟨hAx, hx_nonneg, hx_int⟩
  -- Apply the generic one-row MIR validity lemma to the aggregated equation `u * A x = u * b`.
  refine gomory_mixed_integer_inequality_valid_of_aggregated_equation I (u ᵥ* A) (u ⬝ᵥ b) x
    hβ ?_ hx_nonneg hx_int
  -- The aggregated row equality follows from `A x = b` by associativity of matrix-vector
  -- multiplication with the row-vector dot product.
  calc
    (u ᵥ* A) ⬝ᵥ x = u ⬝ᵥ (A *ᵥ x) := by
      symm
      exact Matrix.dotProduct_mulVec u A x
    _ = u ⬝ᵥ b := by rw [hAx]

end Exercise55
