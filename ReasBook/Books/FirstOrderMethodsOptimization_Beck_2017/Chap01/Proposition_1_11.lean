/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42

open scoped BigOperators

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]

/-- The coordinatewise pairing functional associated to a finite family of linear functionals on
the product `∏ i, E i`. -/
def piDualPairing
    (v : ∀ i, Module.Dual ℝ (E i)) : Module.Dual ℝ (∀ i, E i) :=
  ∑ i, (v i).comp (LinearMap.proj i)

/-- Evaluation of `piDualPairing` is the coordinatewise sum of the factor
functionals. -/
@[simp] theorem piDualPairing_apply
    (v : ∀ i, Module.Dual ℝ (E i)) (u : ∀ i, E i) :
    piDualPairing v u = ∑ i, v i (u i) := by
  simp [piDualPairing]

/-- The underlying real-valued weight carried by a strictly positive weight family. -/
abbrev positiveWeight (ω : ι → Set.Ioi (0 : ℝ)) (i : ι) : ℝ := ω i

omit [Fintype ι] in
/-- Each `positiveWeight ω i` is strictly positive. -/
theorem positiveWeight_pos (ω : ι → Set.Ioi (0 : ℝ)) (i : ι) :
    0 < positiveWeight ω i :=
  (ω i).2

/-- Thin bridge: transfer `piDualPairing` to `PiLp (2 : ENNReal) E` through the canonical weighted
rescaling equivalence from Definition 1.37. -/
abbrev compositeWeightedL2PiLpPairing
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    Module.Dual ℝ (PiLp (2 : ENNReal) E) :=
  (piDualPairing (fun i ↦ (Real.sqrt (positiveWeight ω i))⁻¹ • v i)).comp
    (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ E).toLinearEquiv.toLinearMap

/-- Evaluation of `compositeWeightedL2PiLpPairing` is the inverse-square-root-weighted sum of the
factor pairings. -/
@[simp] theorem compositeWeightedL2PiLpPairing_apply
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) (x : PiLp (2 : ENNReal) E) :
    compositeWeightedL2PiLpPairing ω v x =
      ∑ i, (Real.sqrt (positiveWeight ω i))⁻¹ * v i (x i) := by
  simp [compositeWeightedL2PiLpPairing, piDualPairing_apply]

/-- The `PiLp` pairing agrees with the coordinatewise pairing after the canonical weighted bridge
from `∏ i, E i` to `PiLp (2 : ENNReal) E`. -/
@[simp] theorem compositeWeightedL2PiLpPairing_apply_bridge
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) (u : ∀ i, E i) :
    compositeWeightedL2PiLpPairing ω v (compositeWeightedL2LinearEquivToPiLp ω u) =
      piDualPairing v u := by
  rw [compositeWeightedL2PiLpPairing_apply, piDualPairing_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs : Real.sqrt (positiveWeight ω i) ≠ 0 := (Real.sqrt_pos.2 (positiveWeight_pos ω i)).ne'
  simp [compositeWeightedL2LinearEquivToPiLp, PiLp.toLp_apply, map_smul, hs]

/-- The source-facing weighted-unit-ball supremum is the unit-ball realization of the dual norm of
`compositeWeightedL2PiLpPairing ω v` on the canonical owner `PiLp (2 : ENNReal) E`. -/
theorem unit_piDualPairing_sSup_eq_dualNorm_compositeWeightedL2PiLpPairing
    [FiniteDimensional ℝ (PiLp (2 : ENNReal) E)]
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    sSup ((fun u : ∀ i, E i ↦ |piDualPairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}) =
      dualNorm (compositeWeightedL2PiLpPairing ω v) := by
  let S : Set ℝ :=
    (fun u : ∀ i, E i ↦ |piDualPairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}
  let T : Set ℝ :=
    (fun x : PiLp (2 : ENNReal) E ↦ |compositeWeightedL2PiLpPairing ω v x|) ''
      Metric.closedBall (0 : PiLp (2 : ENNReal) E) 1
  have hST : S = T := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨compositeWeightedL2LinearEquivToPiLp ω u, ?_, ?_⟩
      · exact mem_closedBall_zero_iff.mpr <| by
          simpa [norm_compositeWeightedL2LinearEquivToPiLp_eq ω u] using hu
      · exact congrArg abs (compositeWeightedL2PiLpPairing_apply_bridge ω v u)
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(compositeWeightedL2LinearEquivToPiLp ω).symm x, ?_, ?_⟩
      · simpa [compositeWeightedL2Norm_linearEquivToPiLp_symm_eq ω x] using
          (mem_closedBall_zero_iff.mp hx)
      · have hbridge :=
          compositeWeightedL2PiLpPairing_apply_bridge ω v
            ((compositeWeightedL2LinearEquivToPiLp ω).symm x)
        simpa using congrArg abs hbridge.symm
  calc
    sSup S = sSup T := by rw [hST]
    _ = ‖(compositeWeightedL2PiLpPairing ω v).toContinuousLinearMap‖ := by
      simpa [T, Real.norm_eq_abs] using
        ContinuousLinearMap.sSup_unitClosedBall_eq_norm
          ((compositeWeightedL2PiLpPairing ω v).toContinuousLinearMap)
    _ = dualNorm (compositeWeightedL2PiLpPairing ω v) := by
      rw [dualNorm_eq_toContinuousLinearMap_norm]

end

section

variable {ι : Type u} [Fintype ι]
variable {E : ι → Type u}
variable [∀ i, NormedAddCommGroup (E i)]
variable [∀ i, NormedSpace ℝ (E i)]

/-- A weighted `l_2` unit vector realizes the inverse-weighted quadratic dual-norm sum. -/
private lemma exists_compositeWeightedL2UnitBall_piDualPairing_eq_weightedDualNormSum
    [∀ i, FiniteDimensional ℝ (E i)]
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    let A := √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ))
    ∃ u : ∀ i, E i, compositeWeightedL2Norm ω u ≤ 1 ∧ piDualPairing v u = A := by
  classical
  let A := √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ))
  by_cases hA : A = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [compositeWeightedL2Norm_def]
      simp
    · simp [A, hA, piDualPairing_apply]
  · choose x hxball hxdual using fun i ↦ exists_dualNorm_eq_apply (v i)
    let u : ∀ i, E i := fun i ↦ (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) • x i
    have hA_pos : 0 < A := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hA)
    have hcoeff_nonneg : ∀ i : ι, 0 ≤ ((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A := by
      intro i
      have hω_nonneg : 0 ≤ (positiveWeight ω i)⁻¹ := inv_nonneg.mpr (positiveWeight_pos ω i).le
      have hv_nonneg : 0 ≤ dualNorm (v i) := by
        rw [dualNorm_eq_toContinuousLinearMap_norm]
        exact norm_nonneg _
      exact div_nonneg (mul_nonneg hω_nonneg hv_nonneg) hA_pos.le
    have hu_norm_le : ∀ i : ι, ‖u i‖ ≤ ((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A := by
      intro i
      have hcoeff_abs :
          |((positiveWeight ω i)⁻¹ * dualNorm (v i) / A)| =
            ((positiveWeight ω i)⁻¹ * dualNorm (v i) / A) := abs_of_nonneg (hcoeff_nonneg i)
      calc
        ‖u i‖ = |((positiveWeight ω i)⁻¹ * dualNorm (v i) / A)| * ‖x i‖ := by
          change ‖(((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) • x i‖ =
              |((positiveWeight ω i)⁻¹ * dualNorm (v i) / A)| * ‖x i‖
          rw [norm_smul, Real.norm_eq_abs]
        _ = (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) * ‖x i‖ := by rw [hcoeff_abs]
        _ ≤ (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) * 1 := by
          exact mul_le_mul_of_nonneg_left (hxball i) (hcoeff_nonneg i)
        _ = ((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A := by ring
    have hsum_nonneg : 0 ≤ ∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ) := by
      refine Finset.sum_nonneg fun i _ ↦ ?_
      exact mul_nonneg (inv_nonneg.mpr (positiveWeight_pos ω i).le) (sq_nonneg _)
    have hsum_eq :
        ∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ) = A ^ (2 : ℕ) := by
      dsimp [A]
      symm
      exact Real.sq_sqrt hsum_nonneg
    have hu_sq_le_one : ∑ i, (ω i : ℝ) * ‖u i‖ ^ (2 : ℕ) ≤ 1 := by
      calc
        ∑ i, (ω i : ℝ) * ‖u i‖ ^ (2 : ℕ) ≤
            ∑ i, positiveWeight ω i *
              ((((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) ^ (2 : ℕ)) := by
              refine Finset.sum_le_sum fun i _ ↦ ?_
              have hsq :
                  ‖u i‖ ^ (2 : ℕ) ≤
                    (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) ^ (2 : ℕ) := by
                have hnorm_nonneg : 0 ≤ ‖u i‖ := norm_nonneg _
                have hcoeff_nonneg' : 0 ≤ ((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A :=
                  hcoeff_nonneg i
                nlinarith [hu_norm_le i]
              exact mul_le_mul_of_nonneg_left hsq (positiveWeight_pos ω i).le
        _ = (A⁻¹ * A⁻¹) * ∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ) := by
              calc
                ∑ i, positiveWeight ω i *
                    ((((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) ^ (2 : ℕ)) =
                    ∑ i, (A⁻¹ * A⁻¹) * ((positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := by
                      refine Finset.sum_congr rfl fun i _ ↦ ?_
                      have hω0 : positiveWeight ω i ≠ 0 := (positiveWeight_pos ω i).ne'
                      rw [div_eq_mul_inv, pow_two, pow_two]
                      field_simp [hω0]
                _ = (A⁻¹ * A⁻¹) * ∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ) := by
                      rw [Finset.mul_sum]
        _ = (A⁻¹ * A⁻¹) * A ^ (2 : ℕ) := by rw [hsum_eq]
        _ = 1 := by
              rw [pow_two]
              calc
                (A⁻¹ * A⁻¹) * (A * A) = A⁻¹ * (A⁻¹ * A) * A := by ac_rfl
                _ = A⁻¹ * 1 * A := by rw [inv_mul_cancel₀ hA]
                _ = 1 := by rw [mul_one, inv_mul_cancel₀ hA]
    have hu_ball : compositeWeightedL2Norm ω u ≤ 1 := by
      rw [compositeWeightedL2Norm_def]
      refine (Real.sqrt_le_iff.2 ?_)
      constructor
      · norm_num
      · simpa using hu_sq_le_one
    have hpair : piDualPairing v u = A := by
      calc
        piDualPairing v u =
            ∑ i, (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) * v i (x i) := by
              rw [piDualPairing_apply]
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              simp [u, map_smul]
        _ = ∑ i, (((positiveWeight ω i)⁻¹ * dualNorm (v i)) / A) * dualNorm (v i) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [hxdual i]
        _ = ∑ i, A⁻¹ * ((positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [div_eq_mul_inv, pow_two]
              ring
        _ = A⁻¹ * ∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ) := by
              rw [Finset.mul_sum]
        _ = A⁻¹ * A ^ (2 : ℕ) := by rw [hsum_eq]
        _ = A := by
              rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hA, one_mul]
    exact ⟨u, hu_ball, hpair⟩

-- Proof sketch: for the upper bound, apply the defining inequality for each factor
-- dual norm and then Cauchy-Schwarz to the weighted sequences
-- `(dualNorm (v i) / sqrt (ω i))` and `(sqrt (ω i) * ‖u i‖)`. For the reverse
-- bound, choose exact maximizers for each factor dual norm and scale them by
-- `dualNorm (v i) / (ω i * A)`, where `A` is the right-hand side.
/-- Auxiliary bridge: on the canonical owner `PiLp (2 : ENNReal) E`, the transferred
weighted-product pairing has dual norm equal to the square root of the inverse-weighted sum of
the squared factor dual norms. -/
theorem dualNorm_compositeWeightedL2PiLpPairing_eq_sqrt_sum_invWeight_mul_sq
    [∀ i, FiniteDimensional ℝ (E i)]
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    dualNorm (compositeWeightedL2PiLpPairing ω v) =
      √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := by
  let A := √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ))
  let S : Set ℝ :=
    (fun u : ∀ i, E i ↦ |piDualPairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ?_, ?_⟩
    · simp [Set.mem_setOf_eq, compositeWeightedL2Norm_def]
    · simp [piDualPairing_apply]
  have hupper_bound :
      ∀ u : ∀ i, E i, compositeWeightedL2Norm ω u ≤ 1 → |piDualPairing v u| ≤ A := by
    intro u hu
    have htermwise :
        ∑ i, dualNorm (v i) * ‖u i‖ ≤
          √(∑ i, (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) ^ (2 : ℕ)) *
            √(∑ i, (Real.sqrt (positiveWeight ω i) * ‖u i‖) ^ (2 : ℕ)) := by
      calc
        ∑ i, dualNorm (v i) * ‖u i‖ =
            ∑ i,
              (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) *
                (Real.sqrt (positiveWeight ω i) * ‖u i‖) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              have hs : Real.sqrt (positiveWeight ω i) ≠ 0 := by
                exact (Real.sqrt_pos.2 (positiveWeight_pos ω i)).ne'
              have hterm :
                  (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) *
                    (Real.sqrt (positiveWeight ω i) * ‖u i‖) =
                    dualNorm (v i) * ‖u i‖ := by
                calc
                  (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) *
                      (Real.sqrt (positiveWeight ω i) * ‖u i‖) =
                      dualNorm (v i) *
                        ((Real.sqrt (positiveWeight ω i))⁻¹ *
                          Real.sqrt (positiveWeight ω i)) * ‖u i‖ := by
                          rw [div_eq_mul_inv]
                          ac_rfl
                  _ = dualNorm (v i) * 1 * ‖u i‖ := by rw [inv_mul_cancel₀ hs]
                  _ = dualNorm (v i) * ‖u i‖ := by ring
              simpa using hterm.symm
        _ ≤ √(∑ i, (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) ^ (2 : ℕ)) *
              √(∑ i, (Real.sqrt (positiveWeight ω i) * ‖u i‖) ^ (2 : ℕ)) := by
              simpa using
                Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
                  (fun i ↦ dualNorm (v i) / Real.sqrt (positiveWeight ω i))
                  (fun i ↦ Real.sqrt (positiveWeight ω i) * ‖u i‖)
    have hfirst :
        √(∑ i, (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) ^ (2 : ℕ)) = A := by
      unfold A
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hs : Real.sqrt (positiveWeight ω i) ≠ 0 := by
        exact (Real.sqrt_pos.2 (positiveWeight_pos ω i)).ne'
      have hω0 : positiveWeight ω i ≠ 0 := (positiveWeight_pos ω i).ne'
      rw [div_eq_mul_inv, pow_two, pow_two]
      field_simp [hs, hω0]
      rw [Real.sq_sqrt (positiveWeight_pos ω i).le]
    have hsecond :
        √(∑ i, (Real.sqrt (positiveWeight ω i) * ‖u i‖) ^ (2 : ℕ)) =
          compositeWeightedL2Norm ω u := by
      rw [compositeWeightedL2Norm_def]
      congr 1
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      calc
        (Real.sqrt (positiveWeight ω i) * ‖u i‖) ^ (2 : ℕ) =
            (Real.sqrt (positiveWeight ω i)) ^ (2 : ℕ) * ‖u i‖ ^ (2 : ℕ) := by
              rw [mul_pow]
        _ = positiveWeight ω i * ‖u i‖ ^ (2 : ℕ) := by
              rw [Real.sq_sqrt (positiveWeight_pos ω i).le]
    have hpair_le : |piDualPairing v u| ≤ ∑ i, dualNorm (v i) * ‖u i‖ := by
      calc
        |piDualPairing v u| = |∑ i, v i (u i)| := by
          rw [piDualPairing_apply]
        _ ≤ ∑ i, |v i (u i)| := by
          simpa using (Finset.abs_sum_le_sum_abs (fun i ↦ v i (u i)) Finset.univ)
        _ ≤ ∑ i, dualNorm (v i) * ‖u i‖ := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          exact abs_apply_le_dual_norm_mul_norm (v i) (u i)
    calc
      |piDualPairing v u| ≤
          √(∑ i, (dualNorm (v i) / Real.sqrt (positiveWeight ω i)) ^ (2 : ℕ)) *
            √(∑ i, (Real.sqrt (positiveWeight ω i) * ‖u i‖) ^ (2 : ℕ)) := by
              exact le_trans hpair_le htermwise
      _ = A * compositeWeightedL2Norm ω u := by rw [hfirst, hsecond]
      _ ≤ A := by
            have hA_nonneg : 0 ≤ A := Real.sqrt_nonneg _
            nlinarith
  have hS_bdd : BddAbove S := by
    refine ⟨A, ?_⟩
    rintro z ⟨u, hu, rfl⟩
    exact hupper_bound u hu
  have hupper : sSup S ≤ A := by
    refine csSup_le hS_nonempty ?_
    rintro z ⟨u, hu, rfl⟩
    exact hupper_bound u hu
  have hlower : A ≤ sSup S := by
    obtain ⟨u, hu_ball, hpair⟩ :=
      exists_compositeWeightedL2UnitBall_piDualPairing_eq_weightedDualNormSum ω v
    refine le_csSup hS_bdd ?_
    refine ⟨u, hu_ball, ?_⟩
    calc
      |piDualPairing v u| = |A| := by rw [hpair]
      _ = A := abs_of_nonneg (Real.sqrt_nonneg _)
  have hsSup_eq : sSup S = A := le_antisymm hupper hlower
  calc
    dualNorm (compositeWeightedL2PiLpPairing ω v) = sSup S := by
      symm
      simpa [S] using
        unit_piDualPairing_sSup_eq_dualNorm_compositeWeightedL2PiLpPairing ω v
    _ = A := hsSup_eq
    _ = √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := rfl

-- Proof sketch: combine the weighted product supremum characterization with the owner-level
-- inverse-weighted dual-norm formula.
/-- Proposition 1.11: the supremum of the coordinatewise pairing over the weighted `l_2` unit ball
is the square root of the inverse-weighted sum of the squared factor dual norms. -/
theorem unit_piDualPairing_sSup_eq_sqrt_sum_invWeight_mul_sq
    [∀ i, FiniteDimensional ℝ (E i)]
    (ω : ι → Set.Ioi (0 : ℝ)) (v : ∀ i, Module.Dual ℝ (E i)) :
    sSup ((fun u : ∀ i, E i ↦ |piDualPairing v u|) ''
      {u | compositeWeightedL2Norm ω u ≤ 1}) =
      √(∑ i, (positiveWeight ω i)⁻¹ * dualNorm (v i) ^ (2 : ℕ)) := by
  rw [unit_piDualPairing_sSup_eq_dualNorm_compositeWeightedL2PiLpPairing,
    dualNorm_compositeWeightedL2PiLpPairing_eq_sqrt_sum_invWeight_mul_sq]

end
