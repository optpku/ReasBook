/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Topology.Algebra.Order.Archimedean
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_lemma_6_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3.ch6_sec6_3_remark_6_3_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma629

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch` in this environment, so this file follows the local Chapter 6 convention of
-- representing `ℝ^q` by `Fin q → ℝ` and finitely supported coefficient families by `Finsupp`.

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "Qq" => Fin q → ℚ
local notation "ContAssignment" => Rq →₀ NNReal

open Set
open scoped IntegerVectorNotation

/-- Helper for Lemma 6.29: if two coefficient functions agree on `y.support`, then they yield the
same cut sum against `y`. -/
lemma continuousAssignmentSumEqOfEqOnSupport
    {y : ContAssignment} {ρ ψ : Rq → ℝ}
    (h_eq : ∀ s ∈ y.support, ρ s = ψ s) :
    y.sum (fun s a ↦ ρ s * (a : ℝ)) = y.sum (fun s a ↦ ψ s * (a : ℝ)) := by
  -- Rewrite both sums over the same finite support and compare pointwise.
  rw [Finsupp.sum, Finsupp.sum]
  exact Finset.sum_congr rfl (fun s hs ↦ by rw [h_eq s hs])

/-- Helper for Lemma 6.29: resetting only the value at the origin to zero preserves validity for
the continuous infinite relaxation. -/
lemma continuousInfiniteValidFunctionResetZero
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ) :
    IsValidFunctionForContinuousInfiniteRelaxation f (fun r ↦ if r = 0 then 0 else ψ r) := by
  classical
  refine { one_le := ?_ }
  intro x hx
  have hx_lattice : continuous_infinite_balance f x ∈ ℤ^q :=
    hx.balance_mem_integerVectors
  have herase_balance :
      continuous_infinite_balance f (x.erase 0) = continuous_infinite_balance f x := by
    -- Erasing the origin preserves the balance because the origin contributes zero.
    ext i
    rw [continuous_infinite_balance_apply, continuous_infinite_balance_apply]
    have hsum :
        (x.erase 0).sum (fun r a ↦ (a : ℝ) * r i) =
          x.sum (fun r a ↦ (a : ℝ) * r i) := by
      rw [← Finsupp.add_sum_erase' x 0 (fun r a ↦ (a : ℝ) * r i) (fun r ↦ by simp)]
      simp
    rw [hsum]
  have herase_feasible : IsContinuousInfiniteRelaxationFeasible f (x.erase 0) := by
    refine ⟨?_⟩
    simpa [herase_balance] using hx_lattice
  have herase_sum :
      (x.erase 0).sum (fun r a ↦ (if r = 0 then 0 else ψ r) * (a : ℝ)) =
        (x.erase 0).sum (fun r a ↦ ψ r * (a : ℝ)) :=
    continuousAssignmentSumEqOfEqOnSupport (y := x.erase 0)
      (ρ := fun r ↦ if r = 0 then 0 else ψ r) (ψ := ψ) <| by
        intro r hr
        have hr0 : r ≠ 0 := by
          intro hr0
          subst hr0
          simp at hr
        simp [hr0]
  have hsum_eq :
      x.sum (fun r a ↦ (if r = 0 then 0 else ψ r) * (a : ℝ)) =
        (x.erase 0).sum (fun r a ↦ ψ r * (a : ℝ)) := by
    -- Split off the origin coefficient and then discard it because the reset value is zero.
    calc
      x.sum (fun r a ↦ (if r = 0 then 0 else ψ r) * (a : ℝ)) =
          (x.erase 0).sum (fun r a ↦ (if r = 0 then 0 else ψ r) * (a : ℝ)) := by
            rw [← Finsupp.add_sum_erase' x 0
              (fun r a ↦ (if r = 0 then 0 else ψ r) * (a : ℝ)) (fun r ↦ by simp)]
            simp
      _ = (x.erase 0).sum (fun r a ↦ ψ r * (a : ℝ)) := herase_sum
  rw [hsum_eq]
  exact continuous_infinite_valid_function_one_le hψ herase_feasible

/-- Helper for Lemma 6.29: a minimal valid function for the continuous infinite relaxation
vanishes at the origin. -/
lemma continuousInfiniteMinimalValidFunctionMapZero
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ 0 = 0 := by
  -- Minimality forbids lowering the origin value to `0`.
  have hreset :
      IsValidFunctionForContinuousInfiniteRelaxation f (fun r ↦ if r = 0 then 0 else ψ r) :=
    continuousInfiniteValidFunctionResetZero hψ.toIsValidFunctionForContinuousInfiniteRelaxation
  have hzero_nonneg : 0 ≤ ψ 0 := by
    -- Add arbitrarily much mass at the origin; validity then forces `ψ 0` to be nonnegative.
    by_contra hneg
    have hneg' : ψ 0 < 0 := lt_of_not_ge hneg
    obtain ⟨M, hM⟩ :=
      exists_nat_cutViolation_of_negativeSlope
        (a := ψ (-f)) (b := ψ 0) (D := 1) hneg' Nat.succ_pos'
    have hy :
        Finsupp.single (-f) (1 : NNReal) + Finsupp.single 0 (M : NNReal) ∈
          continuous_infinite_relaxation_feasible_set f := by
      rw [mem_continuous_infinite_relaxation_feasible_set_iff]
      refine (mem_integerVectors_iff).2 ?_
      refine ⟨0, ?_⟩
      ext i
      rw [continuous_infinite_balance_apply, Finsupp.sum_add_index]
      · simp
      · simp
      · intro s a b₁ b₂
        simp [NNReal.coe_add, add_mul]
    have hvalid :
        1 ≤
          (Finsupp.single (-f) (1 : NNReal) + Finsupp.single 0 (M : NNReal)).sum
            (fun s a ↦ ψ s * (a : ℝ)) := by
      exact continuous_infinite_valid_function_one_le
        hψ.toIsValidFunctionForContinuousInfiniteRelaxation hy
    have hsum :
        (Finsupp.single (-f) (1 : NNReal) + Finsupp.single 0 (M : NNReal)).sum
          (fun s a ↦ ψ s * (a : ℝ)) =
            ψ (-f) + ψ 0 * (M : ℝ) := by
      rw [Finsupp.sum_add_index]
      · simp
      · simp
      · intro s a b₁ b₂
        simp [NNReal.coe_add, left_distrib]
    rw [hsum] at hvalid
    have hvalid' : 1 ≤ ψ (-f) + ψ 0 * ((M * 1 : ℕ) : ℝ) := by
      simpa using hvalid
    linarith
  have hle : ∀ r : Rq, (if r = 0 then 0 else ψ r) ≤ ψ r := by
    intro r
    by_cases hr : r = 0
    · simpa [hr] using hzero_nonneg
    · simp [hr]
  have heq :=
    continuous_infinite_minimal_valid_function_eq_of_le hψ hreset hle
  have hpoint := congrArg (fun ρ : Rq → ℝ ↦ ρ 0) heq
  simpa using hpoint.symm

/-- Helper for Lemma 6.29: splitting the coefficient at `r₁ + r₂` into coefficients at `r₁` and
`r₂` changes the weighted sum by the expected correction term. -/
lemma continuousInfiniteSplitWeightedSum
    {ρ : Rq → ℝ} {x : ContAssignment} {r₁ r₂ : Rq} :
    let a := x (r₁ + r₂)
    let y := x.erase (r₁ + r₂) + Finsupp.single r₁ a + Finsupp.single r₂ a
    y.sum (fun s b ↦ ρ s * (b : ℝ)) =
      x.sum (fun s b ↦ ρ s * (b : ℝ)) +
        (a : ℝ) * (ρ r₁ + ρ r₂ - ρ (r₁ + r₂)) := by
  -- Expose the two added singleton terms, then recover the erased source coefficient from `x`.
  dsimp
  rw [Finsupp.sum_add_index]
  · rw [Finsupp.sum_add_index]
    · rw [← Finsupp.add_sum_erase' x (r₁ + r₂) (fun s b ↦ ρ s * (b : ℝ)) (fun s ↦ by simp)]
      simp
      ring
    · simp
    · intro s b₁ b₂
      simp [NNReal.coe_add, left_distrib]
  · simp
  · intro s b₁ b₂
    simp [NNReal.coe_add, left_distrib]

/-- Helper for Lemma 6.29: splitting the coefficient at `r₁ + r₂` into coefficients at `r₁` and
`r₂` preserves the balance vector. -/
lemma continuousInfiniteSplitBalance
    {f : Rq} {x : ContAssignment} {r₁ r₂ : Rq} :
    let a := x (r₁ + r₂)
    let y := x.erase (r₁ + r₂) + Finsupp.single r₁ a + Finsupp.single r₂ a
    continuous_infinite_balance f y = continuous_infinite_balance f x := by
  -- Evaluate coordinates and reuse the split weighted-sum normal form once.
  ext i
  have hsum :=
    continuousInfiniteSplitWeightedSum (ρ := fun s : Rq ↦ s i) (x := x) (r₁ := r₁) (r₂ := r₂)
  calc
    continuous_infinite_balance f
        (x.erase (r₁ + r₂) + Finsupp.single r₁ (x (r₁ + r₂)) +
          Finsupp.single r₂ (x (r₁ + r₂))) i =
        f i + ((x.erase (r₁ + r₂) + Finsupp.single r₁ (x (r₁ + r₂)) +
          Finsupp.single r₂ (x (r₁ + r₂))).sum (fun s b ↦ s i * (b : ℝ))) := by
          rw [continuous_infinite_balance_apply]
          simp [mul_comm]
    _ = f i + (x.sum (fun s b ↦ s i * (b : ℝ)) +
          (x (r₁ + r₂) : ℝ) * (r₁ i + r₂ i - (r₁ + r₂) i)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z : ℝ ↦ f i + z) hsum
    _ = continuous_infinite_balance f x i := by
          rw [continuous_infinite_balance_apply]
          simp [mul_comm]

/-- Helper for Lemma 6.29: lowering the value at `r₁ + r₂` to `ψ r₁ + ψ r₂` preserves validity for
the continuous infinite relaxation. -/
lemma continuousInfiniteValidFunctionLowerAtSum
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (r₁ r₂ : Rq) :
    IsValidFunctionForContinuousInfiniteRelaxation f
      (fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r) := by
  classical
  let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r
  refine { one_le := ?_ }
  intro x hx
  let a : NNReal := x (r₁ + r₂)
  let y : ContAssignment :=
    x.erase (r₁ + r₂) + Finsupp.single r₁ a + Finsupp.single r₂ a
  have hx_lattice : continuous_infinite_balance f x ∈ ℤ^q :=
    hx.balance_mem_integerVectors
  have hy_balance : continuous_infinite_balance f y = continuous_infinite_balance f x := by
    -- Route correction: use the split balance bridge instead of redoing `erase` bookkeeping here.
    simpa [y, a] using
      continuousInfiniteSplitBalance (f := f) (x := x) (r₁ := r₁) (r₂ := r₂)
  have hy_feasible : IsContinuousInfiniteRelaxationFeasible f y := by
    refine ⟨?_⟩
    simpa [hy_balance] using hx_lattice
  have hsum_support :
      x.sum (fun s b ↦ ρ s * (b : ℝ)) =
        x.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (ψ r₁ + ψ r₂ - ψ (r₁ + r₂)) := by
    -- Isolate the changed coefficient before comparing `ρ` and `ψ`.
    rw [← Finsupp.add_sum_erase' x (r₁ + r₂) (fun s b ↦ ρ s * (b : ℝ)) (fun s ↦ by simp)]
    rw [← Finsupp.add_sum_erase' x (r₁ + r₂) (fun s b ↦ ψ s * (b : ℝ)) (fun s ↦ by simp)]
    have herase_eq :
        (x.erase (r₁ + r₂)).sum (fun s b ↦ ρ s * (b : ℝ)) =
          (x.erase (r₁ + r₂)).sum (fun s b ↦ ψ s * (b : ℝ)) :=
      continuousAssignmentSumEqOfEqOnSupport (y := x.erase (r₁ + r₂))
        (ρ := ρ) (ψ := ψ) <| by
          intro s hs
          have hs_ne : s ≠ r₁ + r₂ := by
            intro hs_eq
            subst hs_eq
            simp at hs
          simp [ρ, hs_ne]
    rw [herase_eq]
    simp [ρ, a]
    ring
  have hy_sum :
      y.sum (fun s b ↦ ψ s * (b : ℝ)) =
        x.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (ψ r₁ + ψ r₂ - ψ (r₁ + r₂)) := by
    -- The split weighted-sum bridge puts the moved assignment in the same normal form.
    simpa [y, a, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      continuousInfiniteSplitWeightedSum (ρ := ψ) (x := x) (r₁ := r₁) (r₂ := r₂)
  calc
    1 ≤ y.sum (fun s b ↦ ψ s * (b : ℝ)) :=
      continuous_infinite_valid_function_one_le hψ hy_feasible
    _ = x.sum (fun s b ↦ ρ s * (b : ℝ)) := by
      rw [hy_sum, hsum_support]

/-- Helper for Lemma 6.29: moving the coefficient at `r` to `λ • r` with scale `λ⁻¹` changes the
weighted sum by the expected correction term. -/
lemma continuousInfiniteScaledTransferWeightedSum
    {ρ : Rq → ℝ} {x : ContAssignment} {r : Rq} {c : ℝ}
    (hc : 0 < c) (_hfix : c • r ≠ r) :
    let a : NNReal := x r
    let cInv : NNReal := ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩
    let t : Rq := c • r
    let y : ContAssignment := x.erase r + Finsupp.single t (cInv * a)
    y.sum (fun s b ↦ ρ s * (b : ℝ)) =
      x.sum (fun s b ↦ ρ s * (b : ℝ)) +
        (a : ℝ) * (c⁻¹ * ρ (c • r) - ρ r) := by
  -- Expose the moved singleton and recover the erased source coefficient from `x`.
  dsimp
  rw [Finsupp.sum_add_index]
  · have hsingle :
        (Finsupp.single (c • r) (⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩ * x r)).sum
          (fun s b ↦ ρ s * (b : ℝ)) =
          c⁻¹ * (x r : ℝ) * ρ (c • r) := by
      rw [Finsupp.sum_single_index]
      · change ρ (c • r) * (((⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩ : NNReal) : ℝ) * (x r : ℝ)) =
            c⁻¹ * (x r : ℝ) * ρ (c • r)
        simp [mul_comm, mul_left_comm]
      · simp
    rw [hsingle]
    rw [← Finsupp.add_sum_erase' x r (fun s b ↦ ρ s * (b : ℝ)) (fun s ↦ by simp)]
    ring
  · simp
  · intro s b₁ b₂
    simp [NNReal.coe_add, left_distrib]

/-- Helper for Lemma 6.29: moving the coefficient at `r` to `c • r` with scale `c⁻¹` changes the
balance by the expected displacement term. -/
lemma continuousInfiniteScaledTransferBalance
    {f : Rq} {x : ContAssignment} {r : Rq} {c : ℝ}
    (hc : 0 < c) (hfix : c • r ≠ r) :
    let a : NNReal := x r
    let cInv : NNReal := ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩
    let y : ContAssignment := x.erase r + Finsupp.single (c • r) (cInv * a)
    continuous_infinite_balance f y =
      continuous_infinite_balance f x + (a : ℝ) • (c⁻¹ • (c • r) - r) := by
  -- Evaluate coordinates and reuse the scaled weighted-sum normal form once.
  ext i
  have hsum :=
    continuousInfiniteScaledTransferWeightedSum
      (ρ := fun s : Rq ↦ s i) (x := x) (r := r) (c := c) hc hfix
  calc
    continuous_infinite_balance f
        (x.erase r + Finsupp.single (c • r)
          (⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩ * x r)) i =
        f i + ((x.erase r + Finsupp.single (c • r)
          (⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩ * x r)).sum (fun s b ↦ s i * (b : ℝ))) := by
          rw [continuous_infinite_balance_apply]
          simp [mul_comm]
    _ = f i + (x.sum (fun s b ↦ s i * (b : ℝ)) +
          (x r : ℝ) * (c⁻¹ * (c • r) i - r i)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using congrArg (fun z : ℝ ↦ f i + z) hsum
    _ = (continuous_infinite_balance f x + (x r : ℝ) • (c⁻¹ • (c • r) - r)) i := by
          simp [continuous_infinite_balance, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
            Finsupp.sum_apply', mul_comm, mul_assoc]
          ring

/-- Helper for Lemma 6.29: lowering the value at `r` to `λ⁻¹ ψ (λ • r)` preserves validity when
`λ • r ≠ r`. -/
lemma continuousInfiniteValidFunctionLowerAtSmul
    {f : Rq} {ψ : Rq → ℝ} {r : Rq} {c : ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (hc : 0 < c) (hfix : c • r ≠ r) :
    IsValidFunctionForContinuousInfiniteRelaxation f
      (fun s ↦ if s = r then c⁻¹ * ψ (c • r) else ψ s) := by
  classical
  let ρ : Rq → ℝ := fun s ↦ if s = r then c⁻¹ * ψ (c • r) else ψ s
  refine { one_le := ?_ }
  intro x hx
  let a : NNReal := x r
  let cInv : NNReal := ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩
  let y : ContAssignment := x.erase r + Finsupp.single (c • r) (cInv * a)
  have hx_lattice : continuous_infinite_balance f x ∈ ℤ^q :=
    hx.balance_mem_integerVectors
  have hy_balance :
      continuous_infinite_balance f y =
        continuous_infinite_balance f x + (a : ℝ) • (c⁻¹ • (c • r) - r) := by
    -- Route correction: use the scaled-transfer balance bridge instead of redoing coordinate
    -- transport inside the validity proof.
    simpa [y, a, cInv] using
      continuousInfiniteScaledTransferBalance (f := f) (x := x) (r := r) (c := c) hc hfix
  have hscale : c⁻¹ • (c • r) = r := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hy_feasible : IsContinuousInfiniteRelaxationFeasible f y := by
    refine ⟨?_⟩
    simpa [hy_balance, hscale] using hx_lattice
  have hsum_support :
      x.sum (fun s b ↦ ρ s * (b : ℝ)) =
        x.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (c⁻¹ * ψ (c • r) - ψ r) := by
    -- Isolate the changed source coefficient before comparing `ρ` and `ψ`.
    rw [← Finsupp.add_sum_erase' x r (fun s b ↦ ρ s * (b : ℝ)) (fun s ↦ by simp)]
    rw [← Finsupp.add_sum_erase' x r (fun s b ↦ ψ s * (b : ℝ)) (fun s ↦ by simp)]
    have herase_eq :
        (x.erase r).sum (fun s b ↦ ρ s * (b : ℝ)) =
          (x.erase r).sum (fun s b ↦ ψ s * (b : ℝ)) :=
      continuousAssignmentSumEqOfEqOnSupport (y := x.erase r) (ρ := ρ) (ψ := ψ) <| by
        intro s hs
        have hs_ne : s ≠ r := by
          intro hs_eq
          subst hs_eq
          simp at hs
        simp [ρ, hs_ne]
    rw [herase_eq]
    simp [ρ, a]
    ring
  have hy_sum :
      y.sum (fun s b ↦ ψ s * (b : ℝ)) =
        x.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (c⁻¹ * ψ (c • r) - ψ r) := by
    -- The scaled weighted-sum bridge records the exact cut-value correction term.
    simpa [y, a, cInv, mul_comm, mul_left_comm, mul_assoc] using
      continuousInfiniteScaledTransferWeightedSum
        (ρ := ψ) (x := x) (r := r) (c := c) hc hfix
  calc
    1 ≤ y.sum (fun s b ↦ ψ s * (b : ℝ)) :=
      continuous_infinite_valid_function_one_le hψ hy_feasible
    _ = x.sum (fun s b ↦ ρ s * (b : ℝ)) := by
      rw [hy_sum, hsum_support]

/-- Helper for Lemma 6.29: every minimal valid function for the continuous infinite relaxation is
subadditive. -/
lemma continuousInfiniteMinimalValidFunctionSubadditive
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ.Subadditive := by
  intro r₁ r₂
  by_contra hlt
  let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r
  have hρvalid :
      IsValidFunctionForContinuousInfiniteRelaxation f ρ := by
    simpa [ρ] using
      continuousInfiniteValidFunctionLowerAtSum
        hψ.toIsValidFunctionForContinuousInfiniteRelaxation r₁ r₂
  have hle : ∀ r : Rq, ρ r ≤ ψ r := by
    intro r
    by_cases hr : r = r₁ + r₂
    · have hlt' : ψ r₁ + ψ r₂ < ψ (r₁ + r₂) := lt_of_not_ge hlt
      exact le_of_lt <| by simpa [ρ, hr] using hlt'
    · simp [ρ, hr]
  have heq :=
    continuous_infinite_minimal_valid_function_eq_of_le hψ hρvalid hle
  have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ (r₁ + r₂)) heq
  have hcontr : ψ r₁ + ψ r₂ = ψ (r₁ + r₂) := by
    simpa [ρ] using hpoint
  linarith

/-- Helper for Lemma 6.29: every minimal valid function for the continuous infinite relaxation is
positively homogeneous. -/
lemma continuousInfiniteMinimalValidFunctionPositivelyHomogeneous
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ.PositivelyHomogeneous := by
  intro r c hc
  by_cases hr : r = 0
  · -- The origin case reduces to the already established value `ψ 0 = 0`.
    simp [hr, continuousInfiniteMinimalValidFunctionMapZero hψ]
  by_cases hc1 : c = 1
  · simp [hc1]
  have hfix : c • r ≠ r := by
    intro hfix
    apply hr
    ext i
    have hi := congrArg (fun u : Rq ↦ u i) hfix
    have hi' : c * r i = r i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hi
    have hmul : (c - 1) * r i = 0 := by
      calc
        (c - 1) * r i = c * r i - r i := by ring
        _ = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hc1)
  let t : Rq := c • r
  let ρ₁ : Rq → ℝ := fun s ↦ if s = r then c⁻¹ * ψ t else ψ s
  have hρ₁valid :
      IsValidFunctionForContinuousInfiniteRelaxation f ρ₁ := by
    -- Route correction: the first perturbation lowers the value at `r`.
    simpa [ρ₁, t] using
      continuousInfiniteValidFunctionLowerAtSmul
        hψ.toIsValidFunctionForContinuousInfiniteRelaxation (r := r) (c := c) hc hfix
  have hfirst : ψ r ≤ c⁻¹ * ψ t := by
    by_contra hlt
    have hle : ∀ s : Rq, ρ₁ s ≤ ψ s := by
      intro s
      by_cases hs : s = r
      · have hstrict : c⁻¹ * ψ t < ψ r := lt_of_not_ge hlt
        simpa [ρ₁, hs] using le_of_lt hstrict
      · simp [ρ₁, hs]
    have heq :=
      continuous_infinite_minimal_valid_function_eq_of_le hψ hρ₁valid hle
    have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ r) heq
    have hcontr : c⁻¹ * ψ t = ψ r := by
      simpa [ρ₁] using hpoint
    exact (lt_of_not_ge hlt).ne hcontr
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hfixInv : c⁻¹ • t ≠ t := by
    intro h
    have hr_eq_t : r = t := by
      calc
        r = c⁻¹ • t := by
          simp [t, smul_smul, inv_mul_cancel₀ (ne_of_gt hc)]
        _ = t := h
    exact hfix hr_eq_t.symm
  let ρ₂ : Rq → ℝ := fun s ↦ if s = t then c * ψ r else ψ s
  have hρ₂valid :
      IsValidFunctionForContinuousInfiniteRelaxation f ρ₂ := by
    -- Apply the same perturbation at `t = c • r` with scalar `c⁻¹`.
    have hscaleInv : c⁻¹ • t = r := by
      simp [t, smul_smul, inv_mul_cancel₀ (ne_of_gt hc)]
    simpa [ρ₂, t, inv_inv, hscaleInv] using
      continuousInfiniteValidFunctionLowerAtSmul
        hψ.toIsValidFunctionForContinuousInfiniteRelaxation (r := t) (c := c⁻¹) hcinv hfixInv
  have hsecond : ψ t ≤ c * ψ r := by
    by_contra hlt
    have hle : ∀ s : Rq, ρ₂ s ≤ ψ s := by
      intro s
      by_cases hs : s = t
      · have hstrict : c * ψ r < ψ t := lt_of_not_ge hlt
        simpa [ρ₂, hs] using le_of_lt hstrict
      · simp [ρ₂, hs]
    have heq :=
      continuous_infinite_minimal_valid_function_eq_of_le hψ hρ₂valid hle
    have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ t) heq
    have hcontr : c * ψ r = ψ t := by
      simpa [ρ₂] using hpoint
    exact (lt_of_not_ge hlt).ne hcontr
  have hfirst' : c * ψ r ≤ ψ t := by
    -- Multiply the first inequality by the positive scalar `c`.
    calc
      c * ψ r ≤ c * (c⁻¹ * ψ t) :=
        mul_le_mul_of_nonneg_left hfirst (le_of_lt hc)
      _ = ψ t := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  simpa [t, mul_comm] using le_antisymm hsecond hfirst'

/-- Helper for Lemma 6.29: a minimal valid function for the continuous infinite relaxation is
sublinear. -/
lemma continuousInfiniteMinimalValidFunctionSublinear
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ.Sublinear := by
  -- Package the two structural pieces into the chapter's `Sublinear` owner.
  refine ⟨?_, ?_⟩
  · exact continuousInfiniteMinimalValidFunctionSubadditive hψ
  · exact continuousInfiniteMinimalValidFunctionPositivelyHomogeneous hψ

/-- Helper for Lemma 6.29: the denominator-cleared rational test point is feasible for the
continuous infinite relaxation. -/
lemma continuousInfiniteRationalSliceTestPointFeasible
    (f : Rq) (r : Qq) (M : ℕ) :
    Finsupp.single (-f) (1 : NNReal) +
        Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r : NNReal) ∈
      continuous_infinite_relaxation_feasible_set f := by
  rw [mem_continuous_infinite_relaxation_feasible_set_iff]
  refine (mem_integerVectors_iff).2 ?_
  refine ⟨fun i ↦ (M : ℤ) * common_denominator_scaled_vector r i, ?_⟩
  have hbase :
      (Finsupp.single (-f) (1 : NNReal)).sum (fun s a ↦ (a : ℝ) • s) = -f := by
    -- The base singleton contributes exactly one copy of `-f`.
    rw [Finsupp.sum_single_index]
    · ext i
      simp
    · ext i
      simp
  have hdir :
      (Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r : NNReal)).sum
        (fun s a ↦ (a : ℝ) • s) =
        (((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
          (fun i ↦ (r i : ℝ)) := by
    -- The directional singleton contributes the expected scalar multiple of the rational slice.
    rw [Finsupp.sum_single_index]
    · ext i
      simp [Pi.smul_apply, smul_eq_mul]
    · ext i
      simp
  have hscaled :
      (((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
          (fun i ↦ (r i : ℝ)) =
        fun i ↦ (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
    -- Reuse the denominator-clearing identity from Remark 6.3-extra-2.
    ext i
    have hi :
        ((common_denominator_scaled_vector r i : ℤ) : ℝ) =
          (rational_vector_common_denominator r : ℝ) * (r i : ℝ) := by
      simpa [Pi.smul_apply, smul_eq_mul] using
        congrFun (commonDenominatorScaledVector_eq_smulReal r) i
    calc
      ((((M * rational_vector_common_denominator r : ℕ) : ℝ)) • (fun i ↦ (r i : ℝ))) i =
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) * (r i : ℝ) := by
            simp [Pi.smul_apply, smul_eq_mul]
      _ = (M : ℝ) * ((rational_vector_common_denominator r : ℝ) * (r i : ℝ)) := by
            simp [Nat.cast_mul, mul_assoc]
      _ = (M : ℝ) * ((common_denominator_scaled_vector r i : ℤ) : ℝ) := by
            rw [hi.symm]
      _ = (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
            simp
  ext i
  have hsum :
      (Finsupp.single (-f) (1 : NNReal) +
          Finsupp.single (fun j ↦ (r j : ℝ))
            (M * rational_vector_common_denominator r : NNReal)).sum
        (fun s a ↦ (a : ℝ) • s) =
        -f +
          fun j ↦ (((M : ℤ) * common_denominator_scaled_vector r j : ℤ) : ℝ) := by
    calc
      (Finsupp.single (-f) (1 : NNReal) +
            Finsupp.single (fun j ↦ (r j : ℝ))
              (M * rational_vector_common_denominator r : NNReal)).sum
          (fun s a ↦ (a : ℝ) • s) =
          (Finsupp.single (-f) (1 : NNReal)).sum (fun s a ↦ (a : ℝ) • s) +
            (Finsupp.single (fun j ↦ (r j : ℝ))
              (M * rational_vector_common_denominator r : NNReal)).sum
              (fun s a ↦ (a : ℝ) • s) := by
            rw [Finsupp.sum_add_index]
            · intro a ha
              simp
            · intro a ha b₁ b₂
              simp [NNReal.coe_add, add_smul]
      _ = -f + ((((M * rational_vector_common_denominator r : ℕ) : ℝ)) •
            (fun j ↦ (r j : ℝ))) := by
            rw [hbase, hdir]
      _ = -f + fun j ↦ (((M : ℤ) * common_denominator_scaled_vector r j : ℤ) : ℝ) := by
            rw [hscaled]
  have hi :
      ((Finsupp.single (-f) (1 : NNReal) +
            Finsupp.single (fun j ↦ (r j : ℝ))
              (M * rational_vector_common_denominator r : NNReal)).sum
          (fun s a ↦ (a : ℝ) • s)) i =
        -f i + (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
    simpa [Pi.add_apply] using congrArg (fun u : Rq ↦ u i) hsum
  calc
    continuous_infinite_balance f
        (Finsupp.single (-f) (1 : NNReal) +
          Finsupp.single (fun j ↦ (r j : ℝ))
            (M * rational_vector_common_denominator r : NNReal)) i =
        (f +
          (Finsupp.single (-f) (1 : NNReal) +
            Finsupp.single (fun j ↦ (r j : ℝ))
              (M * rational_vector_common_denominator r : NNReal)).sum
            (fun s a ↦ (a : ℝ) • s)) i := by
          rw [continuous_infinite_balance]
    _ = f i + (-f i + (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ)) := by
          rw [Pi.add_apply, hi]
    _ = (((M : ℤ) * common_denominator_scaled_vector r i : ℤ) : ℝ) := by
          ring

/-- Helper for Lemma 6.29: the cut value of the rational test point splits into the base value
`ψ (-f)` and the rational-direction contribution. -/
lemma continuousInfiniteRationalSliceTestPointCutValue
    (f : Rq) (ψ : Rq → ℝ) (r : Qq) (M : ℕ) :
    (Finsupp.single (-f) (1 : NNReal) +
        Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r : NNReal)).sum
      (fun s a ↦ ψ s * (a : ℝ)) =
      ψ (-f) +
        ψ (fun i ↦ (r i : ℝ)) *
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
  have hbase :
      (Finsupp.single (-f) (1 : NNReal)).sum (fun s a ↦ ψ s * (a : ℝ)) = ψ (-f) := by
    -- The base singleton contributes a single copy of `ψ (-f)`.
    rw [Finsupp.sum_single_index]
    · simp
    · simp
  have hdir :
      (Finsupp.single (fun i ↦ (r i : ℝ))
          (M * rational_vector_common_denominator r : NNReal)).sum
        (fun s a ↦ ψ s * (a : ℝ)) =
        ψ (fun i ↦ (r i : ℝ)) *
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
    -- The directional singleton contributes the slope times the chosen step size.
    rw [Finsupp.sum_single_index]
    · simp
    · simp
  calc
    (Finsupp.single (-f) (1 : NNReal) +
          Finsupp.single (fun i ↦ (r i : ℝ))
            (M * rational_vector_common_denominator r : NNReal)).sum
        (fun s a ↦ ψ s * (a : ℝ)) =
        (Finsupp.single (-f) (1 : NNReal)).sum (fun s a ↦ ψ s * (a : ℝ)) +
          (Finsupp.single (fun i ↦ (r i : ℝ))
            (M * rational_vector_common_denominator r : NNReal)).sum
            (fun s a ↦ ψ s * (a : ℝ)) := by
          rw [Finsupp.sum_add_index]
          · simp
          · simp [NNReal.coe_add, left_distrib]
    _ = ψ (-f) + ψ (fun i ↦ (r i : ℝ)) *
          (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
          rw [hbase, hdir]

/-- Helper for Lemma 6.29: every valid function for the continuous infinite relaxation is
nonnegative on rational vectors. -/
lemma continuousInfiniteValidFunctionNonnegOnRationalVectors
    {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsValidFunctionForContinuousInfiniteRelaxation f ψ)
    (r : Qq) :
    0 ≤ ψ (fun i ↦ (r i : ℝ)) := by
  -- Route correction: use the continuous rational-slice test point instead of redoing the
  -- contradiction argument from scratch.
  by_contra hnonneg
  have hneg : ψ (fun i ↦ (r i : ℝ)) < 0 := lt_of_not_ge hnonneg
  have hDpos : 0 < rational_vector_common_denominator r := by
    exact Nat.pos_of_ne_zero (rationalVectorCommonDenominator_ne_zero r)
  obtain ⟨M, hM⟩ :=
    exists_nat_cutViolation_of_negativeSlope
      (a := ψ (-f))
      (b := ψ (fun i ↦ (r i : ℝ)))
      (D := rational_vector_common_denominator r)
      hneg hDpos
  have hvalidM :
      1 ≤
        (Finsupp.single (-f) (1 : NNReal) +
            Finsupp.single (fun i ↦ (r i : ℝ))
              (M * rational_vector_common_denominator r : NNReal)).sum
          (fun s a ↦ ψ s * (a : ℝ)) := by
    exact continuous_infinite_valid_function_one_le hψ
      (continuousInfiniteRationalSliceTestPointFeasible (f := f) (r := r) (M := M))
  rw [continuousInfiniteRationalSliceTestPointCutValue
    (f := f) (ψ := ψ) (r := r) (M := M)] at hvalidM
  have hvalidM' :
      1 ≤
        ψ (-f) +
          ψ (fun i ↦ (r i : ℝ)) *
            (((M * rational_vector_common_denominator r : ℕ) : ℝ)) := by
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hvalidM
  nlinarith

/-- Lemma 6.29 (1). If `ψ : ℝ^q → ℝ` is a minimal valid function for `R_f`, then `ψ` is
pointwise nonnegative. -/
theorem minimal_valid_function_for_continuous_infinite_relaxation_nonnegative
    (f : Rq) (ψ : Rq → ℝ)
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ)
    (r : Rq) :
    0 ≤ ψ r := by
  -- First obtain the structural `Sublinear` package needed for continuity.
  have hsublinear : ψ.Sublinear :=
    continuousInfiniteMinimalValidFunctionSublinear hψ
  have hcont : Continuous ψ :=
    Function.Sublinear.continuous hsublinear
  let φ : Qq → Rq := fun s i ↦ (s i : ℝ)
  have hDense : DenseRange φ := DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  have hClosed : IsClosed {s : Rq | 0 ≤ ψ s} := by
    simpa using isClosed_Ici.preimage hcont
  have hSubset : Set.range φ ⊆ {s : Rq | 0 ≤ ψ s} := by
    rintro _ ⟨s, rfl⟩
    exact continuousInfiniteValidFunctionNonnegOnRationalVectors
      hψ.toIsValidFunctionForContinuousInfiniteRelaxation s
  have hClosureSubset : closure (Set.range φ) ⊆ {s : Rq | 0 ≤ ψ s} :=
    closure_minimal hSubset hClosed
  have hr_closure : r ∈ closure (Set.range φ) := by
    simp [hDense.closure_range]
  exact hClosureSubset hr_closure

/-- Lemma 6.29 (2). If `ψ : ℝ^q → ℝ` is a minimal valid function for `R_f`, then `ψ` is
sublinear. -/
theorem minimal_valid_function_for_continuous_infinite_relaxation_sublinear
    (f : Rq) (ψ : Rq → ℝ)
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ.Sublinear := by
  -- The public theorem is the packaged form of the local subadditivity and homogeneity helpers.
  exact continuousInfiniteMinimalValidFunctionSublinear hψ

/-- A minimal valid function for `R_f` inherits the canonical `Sublinear` structure. -/
instance instIsMinimalValidFunctionForContinuousInfiniteRelaxationToSublinear
    {f : Rq} {ψ : Rq → ℝ}
    [hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ] :
    ψ.Sublinear :=
  minimal_valid_function_for_continuous_infinite_relaxation_sublinear f ψ hψ

namespace IsMinimalValidFunctionForContinuousInfiniteRelaxation

/-- A minimal valid function for `R_f` is pointwise nonnegative. -/
theorem nonnegative {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) (r : Rq) :
    0 ≤ ψ r :=
  minimal_valid_function_for_continuous_infinite_relaxation_nonnegative f ψ hψ r

/-- A minimal valid function for `R_f` is sublinear. -/
theorem sublinear {f : Rq} {ψ : Rq → ℝ}
    (hψ : IsMinimalValidFunctionForContinuousInfiniteRelaxation f ψ) :
    ψ.Sublinear :=
  minimal_valid_function_for_continuous_infinite_relaxation_sublinear f ψ hψ

end IsMinimalValidFunctionForContinuousInfiniteRelaxation

end Lemma629
