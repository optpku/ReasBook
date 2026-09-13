/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Pairing

/-!
# The continuous dual of `C0Seq`

This module constructs the canonical `L1Seq` representation of continuous
linear functionals on `C0Seq`.
-/

public section

noncomputable section

namespace C0Seq

/-- Finite sums of the absolute values of a functional on the standard coordinate vectors
are bounded by its operator norm. -/
private theorem sum_abs_apply_c0Single_le_norm (φ : StrongDual ℝ C0Seq) (s : Finset ℕ) :
    ∑ n ∈ s, |φ (c0Single n 1)| ≤ ‖φ‖ := by
  classical
  -- Test the functional on the finite vector whose coordinates are the corresponding signs.
  let y : C0Seq :=
    ∑ n ∈ s, (SignType.sign (φ (c0Single n 1)) : ℝ) • c0Single n 1
  have hy_apply (m : ℕ) :
      y m = if m ∈ s then (SignType.sign (φ (c0Single m 1)) : ℝ) else 0 := by
    by_cases hm : m ∈ s
    · rw [if_pos hm]
      simp only [y, ← evalCLM_apply, map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single m]
      · rw [evalCLM_apply, c0Single_apply, if_pos rfl, mul_one]
      · intro n hn hnm
        rw [evalCLM_apply, c0Single_apply, if_neg (Ne.symm hnm), mul_zero]
      · exact fun hms ↦ (hms hm).elim
    · rw [if_neg hm]
      simp only [y, ← evalCLM_apply, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hmn : m ≠ n := by
        intro h
        subst n
        exact hm hn
      rw [evalCLM_apply, c0Single_apply, if_neg hmn, mul_zero]
  have hy_norm : ‖y‖ ≤ 1 := by
    -- Every coordinate of the sign vector has absolute value at most one.
    rw [norm_eq_iSup_abs]
    refine ciSup_le fun m ↦ ?_
    rw [hy_apply]
    split_ifs
    · cases SignType.sign (φ (c0Single m 1)) <;> norm_num
    · simp only [abs_zero, zero_le_one]
  have hφy : φ y = ∑ n ∈ s, |φ (c0Single n 1)| := by
    -- Linearity turns evaluation of the test vector into the desired absolute-value sum.
    simp only [y, map_sum, map_smul, smul_eq_mul, sign_mul_self]
  -- Apply the operator-norm bound to the norm-one test vector.
  calc
    ∑ n ∈ s, |φ (c0Single n 1)| = |φ y| := by
      rw [hφy, abs_of_nonneg]
      exact Finset.sum_nonneg fun n _ ↦ abs_nonneg (φ (c0Single n 1))
    _ = ‖φ y‖ := (Real.norm_eq_abs (φ y)).symm
    _ ≤ ‖φ‖ * ‖y‖ := φ.le_opNorm y
    _ ≤ ‖φ‖ * 1 := mul_le_mul_of_nonneg_left hy_norm (norm_nonneg φ)
    _ = ‖φ‖ := mul_one ‖φ‖

/-- C0Seq.norm_pairingL_flip: The flipped `C0Seq`–`L1Seq` pairing preserves the
`L1Seq` norm. -/
theorem norm_pairingL_flip (a : L1Seq) : ‖pairingL.flip a‖ = ‖a‖ := by
  -- The bundled bilinear norm estimate gives the easy inequality.
  have hUpper : ‖pairingL.flip a‖ ≤ ‖a‖ := by
    calc
      ‖pairingL.flip a‖ ≤ ‖pairingL.flip‖ * ‖a‖ := pairingL.flip.le_opNorm a
      _ = ‖pairingL‖ * ‖a‖ := by rw [ContinuousLinearMap.opNorm_flip]
      _ ≤ 1 * ‖a‖ :=
        mul_le_mul_of_nonneg_right norm_pairingL_le (norm_nonneg a)
      _ = ‖a‖ := one_mul ‖a‖
  have hLower : ‖a‖ ≤ ‖pairingL.flip a‖ := by
    -- Finite sign-vector tests bound every partial absolute-coordinate sum.
    rw [L1Seq.norm_eq_tsum_abs]
    refine Real.tsum_le_of_sum_le (fun n ↦ abs_nonneg (a n)) fun s ↦ ?_
    simpa only [ContinuousLinearMap.flip_apply, pairingL_c0Single_apply, one_mul] using
      sum_abs_apply_c0Single_le_norm (pairingL.flip a) s
  exact le_antisymm hUpper hLower

/-- The isometric linear embedding of `L1Seq` into the strong dual of `C0Seq`
defined by the coordinatewise pairing. -/
noncomputable def l1ToDual : L1Seq →ₗᵢ[ℝ] StrongDual ℝ C0Seq where
  toLinearMap := pairingL.flip.toLinearMap
  norm_map' := norm_pairingL_flip

/-- Evaluating `l1ToDual` gives the coordinatewise `C0Seq`–`L1Seq` pairing. -/
@[simp]
theorem l1ToDual_apply (a : L1Seq) (x : C0Seq) :
    l1ToDual a x = ∑' n : ℕ, x n * a n := by
  -- Reduce the isometry to the flipped pairing's public evaluation formula.
  calc
    l1ToDual a x = pairingL.flip a x := by rfl
    _ = ∑' n : ℕ, x n * a n := pairingL_flip_apply a x

/-- The continuous linear map underlying `l1ToDual` is the flipped bundled pairing. -/
theorem l1ToDual_toContinuousLinearMap :
    l1ToDual.toContinuousLinearMap = pairingL.flip := by
  -- Equality follows pointwise from the shared pairing formula.
  ext a x
  rfl

/-- The values of a continuous functional on the standard coordinate vectors form an
absolutely summable sequence. -/
theorem dualCoefficients_memℓp (φ : StrongDual ℝ C0Seq) :
    Memℓp (fun n : ℕ ↦ φ (c0Single n 1)) 1 := by
  -- The finite-sum criterion at exponent one is exactly the sign-vector estimate.
  refine memℓp_gen' (C := ‖φ‖) fun s ↦ ?_
  simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
    sum_abs_apply_c0Single_le_norm φ s

/-- The summable sequence of values of a continuous functional on the standard coordinate
vectors. -/
def dualCoefficients (φ : StrongDual ℝ C0Seq) : L1Seq :=
  ⟨fun n ↦ φ (c0Single n 1), dualCoefficients_memℓp φ⟩

/-- Each coordinate of `dualCoefficients φ` is the value of `φ` on the corresponding
standard coordinate vector. -/
@[simp]
theorem dualCoefficients_apply (φ : StrongDual ℝ C0Seq) (n : ℕ) :
    dualCoefficients φ n = φ (c0Single n 1) := by
  -- Project the defining coordinate function of the bundled `L1Seq`.
  rfl

/-- Every finite absolute-coordinate sum of `dualCoefficients φ` is bounded by the
operator norm of `φ`. -/
private theorem sum_abs_dualCoefficients_le_norm (φ : StrongDual ℝ C0Seq) (s : Finset ℕ) :
    ∑ n ∈ s, |dualCoefficients φ n| ≤ ‖φ‖ := by
  -- Rewrite bundled coefficients as evaluations and apply the sign-vector estimate.
  simpa only [dualCoefficients_apply] using sum_abs_apply_c0Single_le_norm φ s

/-- The norm of the coefficient sequence of a continuous functional on `C0Seq` is at most
the operator norm of the functional. -/
theorem norm_dualCoefficients_le (φ : StrongDual ℝ C0Seq) :
    ‖dualCoefficients φ‖ ≤ ‖φ‖ := by
  -- Rewrite the `L1Seq` norm and pass the uniform finite-sum bound to the total sum.
  rw [L1Seq.norm_eq_tsum_abs]
  refine Real.tsum_le_of_sum_le (fun n ↦ abs_nonneg (dualCoefficients φ n)) fun s ↦ ?_
  exact sum_abs_dualCoefficients_le_norm φ s

/-- The finite sums of the standard coordinate expansion of a `C0Seq` converge to the
original sequence. -/
private theorem tendsto_sum_range_smul_c0Single (x : C0Seq) :
    Filter.Tendsto (fun N ↦ ∑ n ∈ Finset.range N, x n • c0Single n 1)
      Filter.atTop (nhds x) := by
  classical
  have hPrefixApply (N k : ℕ) :
      (∑ n ∈ Finset.range N, x n • c0Single n 1) k = if k < N then x k else 0 := by
    -- At a fixed coordinate, the finite sum either contains its unique singleton or vanishes.
    by_cases hk : k < N
    · rw [if_pos hk]
      simp only [← evalCLM_apply, map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_eq_single k]
      · rw [evalCLM_apply, evalCLM_apply, c0Single_apply, if_pos rfl, mul_one]
      · intro n hn hnk
        simp only [evalCLM_apply, c0Single_apply, if_neg (Ne.symm hnk), mul_zero]
      · intro hkNotMem
        exact (hkNotMem (Finset.mem_range.mpr hk)).elim
    · rw [if_neg hk]
      simp only [← evalCLM_apply, map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun n hn ↦ ?_
      have hkn : k ≠ n := by
        intro h
        subst n
        exact hk (Finset.mem_range.mp hn)
      simp only [evalCLM_apply, c0Single_apply, if_neg hkn, mul_zero]
  -- Vanishing of the tail gives a single index controlling every remaining coordinate.
  rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
  refine Metric.tendstoUniformly_iff.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_zero x) ε hε
  refine Filter.eventually_atTop.mpr ⟨N, fun M hNM k ↦ ?_⟩
  rw [hPrefixApply]
  by_cases hk : k < M
  · simp only [if_pos hk, dist_self, hε]
  · have hMk : M ≤ k := Nat.le_of_not_gt hk
    simpa only [if_neg hk] using hN k (hNM.trans hMk)

/-- Applying a continuous functional to the finite coordinate truncations converges to its
value on the original sequence. -/
private theorem tendsto_apply_sum_range_smul_c0Single (φ : StrongDual ℝ C0Seq) (x : C0Seq) :
    Filter.Tendsto
      (fun N ↦ φ (∑ n ∈ Finset.range N, x n • c0Single n 1))
      Filter.atTop (nhds (φ x)) := by
  -- Compose coordinate-truncation convergence with continuity of the functional.
  exact φ.continuous.continuousAt.tendsto.comp (tendsto_sum_range_smul_c0Single x)

/-- A continuous functional on `C0Seq` is recovered by pairing with its coefficient
sequence. -/
theorem apply_eq_tsum_dualCoefficients (φ : StrongDual ℝ C0Seq) (x : C0Seq) :
    φ x = ∑' n : ℕ, x n * dualCoefficients φ n := by
  -- Continuity transports convergence of the coordinate truncations through `φ`.
  have hFunctionalLimit :
      Filter.Tendsto
        (fun N ↦ φ (∑ n ∈ Finset.range N, x n • c0Single n 1))
        Filter.atTop (nhds (φ x)) :=
    tendsto_apply_sum_range_smul_c0Single φ x
  have hPartialSum (N : ℕ) :
      φ (∑ n ∈ Finset.range N, x n • c0Single n 1) =
        ∑ n ∈ Finset.range N, x n * dualCoefficients φ n := by
    -- Linearity identifies each mapped truncation with the scalar series partial sum.
    simp only [map_sum, map_smul, smul_eq_mul, dualCoefficients_apply]
  have hSeriesLimit :
      Filter.Tendsto
        (fun N ↦ ∑ n ∈ Finset.range N, x n * dualCoefficients φ n)
        Filter.atTop (nhds (∑' n : ℕ, x n * dualCoefficients φ n)) :=
    (summable_mul x (dualCoefficients φ)).hasSum.tendsto_sum_nat
  -- The rewritten functional limit and the series limit must agree.
  exact tendsto_nhds_unique (hFunctionalLimit.congr' (Filter.Eventually.of_forall hPartialSum))
    hSeriesLimit

/-- The coefficient map from the strong dual of `C0Seq` to `L1Seq` preserves addition. -/
@[simp]
theorem dualCoefficients_add (φ ψ : StrongDual ℝ C0Seq) :
    dualCoefficients (φ + ψ) = dualCoefficients φ + dualCoefficients ψ := by
  -- Equality of summable sequences follows from pointwise linearity of evaluation.
  ext n
  simp only [dualCoefficients_apply, lp.coeFn_add, Pi.add_apply, add_apply]

/-- The coefficient map from the strong dual of `C0Seq` to `L1Seq` preserves real
scalar multiplication. -/
@[simp]
theorem dualCoefficients_smul (r : ℝ) (φ : StrongDual ℝ C0Seq) :
    dualCoefficients (r • φ) = r • dualCoefficients φ := by
  -- Equality of summable sequences follows from pointwise compatibility with scalars.
  ext n
  simp only [dualCoefficients_apply, lp.coeFn_smul, Pi.smul_apply, smul_apply]

/-- Reconstructing a functional from its coefficient sequence recovers the functional. -/
@[simp]
theorem l1ToDual_dualCoefficients (φ : StrongDual ℝ C0Seq) :
    l1ToDual (dualCoefficients φ) = φ := by
  -- The coordinate expansion reconstructs both functionals on every sequence.
  ext x
  simpa only [l1ToDual_apply] using (apply_eq_tsum_dualCoefficients φ x).symm

/-- Extracting coefficients from the functional associated to an `L1Seq` recovers the
sequence. -/
@[simp]
theorem dualCoefficients_l1ToDual (a : L1Seq) :
    dualCoefficients (l1ToDual a) = a := by
  -- Injectivity of the isometric embedding reduces this to the reconstruction identity.
  apply l1ToDual.injective
  exact l1ToDual_dualCoefficients (l1ToDual a)

/-- The coefficient sequence of a functional has the same norm as the functional. -/
theorem norm_dualCoefficients (φ : StrongDual ℝ C0Seq) :
    ‖dualCoefficients φ‖ = ‖φ‖ := by
  -- Transport the norm through the isometry and then use functional reconstruction.
  calc
    ‖dualCoefficients φ‖ = ‖l1ToDual (dualCoefficients φ)‖ :=
      (l1ToDual.norm_map (dualCoefficients φ)).symm
    _ = ‖φ‖ := congrArg norm (l1ToDual_dualCoefficients φ)

/-- The canonical real-linear isometric equivalence from the strong dual of `C0Seq` to
`L1Seq`, with inverse given by the coordinatewise pairing. -/
noncomputable def dualEquivL1 : StrongDual ℝ C0Seq ≃ₗᵢ[ℝ] L1Seq where
  toFun := dualCoefficients
  invFun := l1ToDual
  left_inv := l1ToDual_dualCoefficients
  right_inv := dualCoefficients_l1ToDual
  map_add' := dualCoefficients_add
  map_smul' := dualCoefficients_smul
  norm_map' := norm_dualCoefficients

/-- Applying `dualEquivL1` extracts the coefficient sequence of a functional. -/
@[simp]
theorem dualEquivL1_apply (φ : StrongDual ℝ C0Seq) :
    dualEquivL1 φ = dualCoefficients φ := by
  -- The forward function is coefficient extraction by construction.
  rfl

/-- Each coordinate of `dualEquivL1 φ` is the value of `φ` on the corresponding standard
coordinate vector. -/
@[simp]
theorem dualEquivL1_apply_apply (φ : StrongDual ℝ C0Seq) (n : ℕ) :
    dualEquivL1 φ n = φ (c0Single n 1) := by
  -- Expose the forward map and then evaluate the selected coefficient.
  rw [dualEquivL1_apply, dualCoefficients_apply]

/-- The inverse linear isometry of `dualEquivL1` is the coordinatewise pairing map. -/
@[simp]
theorem dualEquivL1_symm_toLinearIsometry :
    dualEquivL1.symm.toLinearIsometry = l1ToDual := by
  -- The inverse isometry has the specified inverse function of the equivalence.
  ext a
  rfl

/-- Applying the inverse of `dualEquivL1` gives the functional associated to an `L1Seq`. -/
@[simp]
theorem dualEquivL1_symm_apply (a : L1Seq) :
    dualEquivL1.symm a = l1ToDual a := by
  -- Evaluate the equality of the two bundled inverse isometries at `a`.
  have h := congrArg (fun f : L1Seq →ₗᵢ[ℝ] StrongDual ℝ C0Seq ↦ f a)
    dualEquivL1_symm_toLinearIsometry
  exact h

/-- Evaluating the inverse of `dualEquivL1` gives the coordinatewise `C0Seq`–`L1Seq`
pairing. -/
@[simp]
theorem dualEquivL1_symm_apply_apply (a : L1Seq) (x : C0Seq) :
    dualEquivL1.symm a x = ∑' n : ℕ, x n * a n := by
  -- Normalize the inverse to `l1ToDual` and apply its coordinate formula.
  rw [dualEquivL1_symm_apply, l1ToDual_apply]

end C0Seq
