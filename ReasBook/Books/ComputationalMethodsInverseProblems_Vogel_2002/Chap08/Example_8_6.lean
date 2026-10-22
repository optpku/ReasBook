/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4.Conjugate
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Example_8_6.Penalty

public section

noncomputable section

namespace VariationalRegularization

/-- Helper for Example 8.6: every integrand value on the closed unit ball is
bounded above by the Huber penalty. -/
private lemma integrandLeHuberPenaltyOfMemClosedUnitBall {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (x y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    inner ℝ x y - (ε / 2) * ‖y‖ ^ 2 ≤ huberPenalty ε x := by
  have hy_norm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.1 hy
  have hinner : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  by_cases hx : ‖x‖ ≤ ε
  · -- On the quadratic branch, complete the square after bounding the inner product.
    rw [huberPenalty_of_norm_le ε x hx]
    have hquad :
        ‖x‖ * ‖y‖ - (ε / 2) * ‖y‖ ^ 2 ≤ ‖x‖ ^ 2 / (2 * ε) := by
      have hεne : ε ≠ 0 := ne_of_gt hε
      field_simp [hεne]
      nlinarith [sq_nonneg (‖x‖ - ε * ‖y‖)]
    nlinarith
  · -- On the affine branch, the closed-unit-ball constraint gives the needed bound.
    have hx' : ε < ‖x‖ := lt_of_not_ge hx
    rw [huberPenalty_of_lt_norm ε x hx']
    have haffine :
        ‖x‖ * ‖y‖ - (ε / 2) * ‖y‖ ^ 2 ≤ ‖x‖ - ε / 2 := by
      nlinarith [sq_nonneg (‖y‖ - 1), hε, hx', hy_norm]
    nlinarith

/-- Helper for Example 8.6: in the quadratic branch, the scaled point
`(1 / ε) • x` lies in the closed unit ball and attains `huberPenalty ε x`. -/
private lemma quadraticBranchWitnessAttainsHuberPenalty {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ ≤ ε) :
    (1 / ε) • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      inner ℝ x ((1 / ε) • x) - (ε / 2) * ‖(1 / ε) • x‖ ^ 2 = huberPenalty ε x := by
  have hy_norm : ‖(1 / ε) • x‖ ≤ 1 := by
    -- The quadratic witness scales `x` down by at most the unit-ball radius.
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hε)]
    have hscaled :
        (1 / ε) * ‖x‖ ≤ (1 / ε) * ε := by
      exact mul_le_mul_of_nonneg_left hx (by positivity)
    simpa [div_eq_mul_inv, hε.ne'] using hscaled
  constructor
  · -- The norm estimate is exactly the closed-unit-ball membership test.
    exact mem_closedBall_zero_iff.2 hy_norm
  · -- Evaluate the integrand at the quadratic-branch optimizer.
    rw [huberPenalty_of_norm_le ε x hx]
    calc
      inner ℝ x ((1 / ε) • x) - (ε / 2) * ‖(1 / ε) • x‖ ^ 2
          = (1 / ε) * ‖x‖ ^ 2 - (ε / 2) * ‖(1 / ε) • x‖ ^ 2 := by
              rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      _ = (1 / ε) * ‖x‖ ^ 2 - (ε / 2) * (((1 / ε) * ‖x‖) ^ 2) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hε)]
      _ = ‖x‖ ^ 2 / (2 * ε) := by
            have hεne : ε ≠ 0 := ne_of_gt hε
            field_simp [hεne]
            ring

/-- Helper for Example 8.6: in the affine branch, the unit-direction witness
`‖x‖⁻¹ • x` lies in the closed unit ball and attains `huberPenalty ε x`. -/
private lemma affineBranchWitnessAttainsHuberPenalty {d : ℕ}
    (ε : ℝ) (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin d)) (hx : ε < ‖x‖) :
    ‖x‖⁻¹ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ∧
      inner ℝ x (‖x‖⁻¹ • x) - (ε / 2) * ‖‖x‖⁻¹ • x‖ ^ 2 = huberPenalty ε x := by
  have hx_norm_pos : 0 < ‖x‖ := lt_trans hε hx
  have hx_norm_ne : ‖x‖ ≠ 0 := ne_of_gt hx_norm_pos
  have hy_norm_eq : ‖‖x‖⁻¹ • x‖ = 1 := by
    -- The affine witness is the unit vector in the direction of `x`.
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hx_norm_pos))]
    rw [inv_mul_cancel₀ hx_norm_ne]
  constructor
  · -- The unit-direction witness lands exactly on the boundary of the closed ball.
    exact mem_closedBall_zero_iff.2 hy_norm_eq.le
  · -- Evaluate the integrand at the affine-branch optimizer.
    rw [huberPenalty_of_lt_norm ε x hx]
    calc
      inner ℝ x (‖x‖⁻¹ • x) - (ε / 2) * ‖‖x‖⁻¹ • x‖ ^ 2
          = ‖x‖⁻¹ * ‖x‖ ^ 2 - (ε / 2) * ‖‖x‖⁻¹ • x‖ ^ 2 := by
              rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      _ = ‖x‖⁻¹ * ‖x‖ ^ 2 - (ε / 2) * 1 ^ 2 := by
            rw [hy_norm_eq]
      _ = ‖x‖⁻¹ * ‖x‖ ^ 2 - ε / 2 := by simp
      _ = ‖x‖ - ε / 2 := by
            rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hx_norm_ne, one_mul]

/-- Example 8.6. For `0 < ε`, the Huber-type penalty on `EuclideanSpace ℝ (Fin d)`
is the supremum of `y ↦ inner ℝ x y - (ε / 2) * ‖y‖ ^ 2` over the closed unit
ball `Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1`. -/
theorem huberPenalty_eq_sSup_closedUnitBall {d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d)) :
    huberPenalty ε x =
      sSup ((fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ x y - (ε / 2) * ‖y‖ ^ 2) ''
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  let s : Set ℝ :=
    ((fun y : EuclideanSpace ℝ (Fin d) ↦ inner ℝ x y - (ε / 2) * ‖y‖ ^ 2) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
  change huberPenalty ε x = sSup s
  have hs_nonempty : s.Nonempty := by
    -- The zero vector gives an explicit point in the image set.
    refine ⟨0, ?_⟩
    refine ⟨0, Metric.mem_closedBall_self zero_le_one, ?_⟩
    simp
  have hs_bdd : BddAbove s := by
    -- The global upper-bound helper provides the supremum bound.
    refine ⟨huberPenalty ε x, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact integrandLeHuberPenaltyOfMemClosedUnitBall ε hε x y hy
  refine le_antisymm ?_ ?_
  · -- Use the branch-specific optimizer to realize the supremum value.
    by_cases hx : ‖x‖ ≤ ε
    · rcases quadraticBranchWitnessAttainsHuberPenalty ε hε x hx with ⟨hy, hvalue⟩
      refine le_csSup hs_bdd ?_
      exact ⟨(1 / ε) • x, hy, hvalue⟩
    · have hx' : ε < ‖x‖ := lt_of_not_ge hx
      rcases affineBranchWitnessAttainsHuberPenalty ε hε x hx' with ⟨hy, hvalue⟩
      refine le_csSup hs_bdd ?_
      exact ⟨‖x‖⁻¹ • x, hy, hvalue⟩
  · -- Every value in the image is bounded above by `huberPenalty ε x`.
    refine csSup_le hs_nonempty ?_
    rintro z ⟨y, hy, rfl⟩
    exact integrandLeHuberPenaltyOfMemClosedUnitBall ε hε x y hy

/-- The Example 8.6 supremum is the closed-unit-ball conjugate functional of
`y ↦ (ε / 2) * ‖y‖ ^ 2`, viewed in `EReal`. -/
theorem huberPenalty_eq_conjugateFunctional_closedUnitBall {d : ℕ} (ε : ℝ) (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin d)) :
    ((huberPenalty ε x : ℝ) : EReal) =
      conjugateFunctional
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
        (fun y : EuclideanSpace ℝ (Fin d) ↦ (ε / 2) * ‖y‖ ^ 2)
        x := by
  rw [conjugateFunctional_def]
  refine le_antisymm ?_ ?_
  · -- The same branch-specific optimizer gives an `EReal` witness for the supremum.
    by_cases hx : ‖x‖ ≤ ε
    · rcases quadraticBranchWitnessAttainsHuberPenalty ε hε x hx with ⟨hy, hvalue⟩
      refine le_sSup ?_
      refine ⟨(1 / ε) • x, hy, ?_⟩
      exact EReal.coe_eq_coe_iff.2 <| by simpa [real_inner_comm] using hvalue
    · have hx' : ε < ‖x‖ := lt_of_not_ge hx
      rcases affineBranchWitnessAttainsHuberPenalty ε hε x hx' with ⟨hy, hvalue⟩
      refine le_sSup ?_
      refine ⟨‖x‖⁻¹ • x, hy, ?_⟩
      exact EReal.coe_eq_coe_iff.2 <| by simpa [real_inner_comm] using hvalue
  · -- The real upper-bound helper transfers directly to the `EReal` supremum.
    refine sSup_le ?_
    rintro z ⟨y, hy, rfl⟩
    exact EReal.coe_le_coe <|
      by simpa [real_inner_comm] using
        integrandLeHuberPenaltyOfMemClosedUnitBall ε hε x y hy

end VariationalRegularization
