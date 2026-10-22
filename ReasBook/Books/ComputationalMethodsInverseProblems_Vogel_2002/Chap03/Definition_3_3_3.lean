/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_3.Update

public section

noncomputable section

namespace BFGS

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Definition 3.3-extra-3 (1). Equation `(3.23)` is formalized by the BFGS
Hessian-approximation update `BFGS.update`. -/
#check BFGS.update

/-- Helper for Definition 3.3-extra-3: the rank-one projector used to remove the `s_v`
direction from the old quadratic form. -/
def updateProjector (H_v : H →L[ℝ] H) (s_v : H) : H →L[ℝ] H :=
  1 - (1 / inner ℝ (H_v s_v) s_v) • InnerProductSpace.rankOne ℝ s_v (H_v s_v)

omit [CompleteSpace H] in
/-- Helper for Definition 3.3-extra-3: `updateProjector` acts by subtracting the `H_v s_v`
component along `s_v`. -/
lemma updateProjector_apply (H_v : H →L[ℝ] H) (s_v x : H) :
    updateProjector H_v s_v x =
      x - (inner ℝ (H_v s_v) x / inner ℝ (H_v s_v) s_v) • s_v := by
  -- Expand the rank-one projector once and collect the scalar coefficient.
  simp [updateProjector, InnerProductSpace.rankOne_apply, sub_eq_add_neg, smul_smul, div_eq_mul_inv,
    mul_comm]

/-- Helper for Definition 3.3-extra-3: the BFGS update splits into a conjugated old operator plus
the positive rank-one curvature correction. -/
lemma update_eq_adjointConj_add_rankOne
    (H_v : H →L[ℝ] H) (s_v y_v : H) (hSelf : IsSelfAdjoint H_v) :
    BFGS.update H_v s_v y_v =
      (updateProjector H_v s_v).adjoint ∘L H_v ∘L updateProjector H_v s_v
        + (1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v := by
  ext x
  let a := inner ℝ (H_v s_v) s_v
  let α := inner ℝ (H_v s_v) x / a
  let z := updateProjector H_v s_v x
  have hz : z = x - α • s_v := by
    -- Put the projector output into the stable `x - α • s_v` normal form.
    simpa [a, α, z] using updateProjector_apply H_v s_v x
  have hadj_apply :
      (updateProjector H_v s_v).adjoint (H_v z) = H_v z := by
    -- The conjugated term drops the `s_v` component after one projector application.
    by_cases ha : a = 0
    · simp [updateProjector, a, ha, z]
    · have hz_orth : inner ℝ s_v (H_v z) = 0 := by
        have hsymx : inner ℝ s_v (H_v x) = inner ℝ (H_v s_v) x := by
          simpa using (hSelf.isSymmetric s_v x).symm
        have hsyms : inner ℝ s_v (H_v s_v) = a := by
          simpa [a] using (hSelf.isSymmetric s_v s_v).symm
        have hα' : (inner ℝ (H_v s_v) x / a) * a = inner ℝ (H_v s_v) x := by
          field_simp [ha]
        have hα : α * a = inner ℝ (H_v s_v) x := by
          simpa [α, mul_comm] using hα'
        rw [hz, map_sub, map_smul, inner_sub_right, inner_smul_right, hsymx, hsyms]
        nlinarith
      simp [updateProjector, InnerProductSpace.adjoint_rankOne, InnerProductSpace.rankOne_apply,
        hz_orth]
  -- Compare the pointwise formulas of the two operator expressions.
  calc
    BFGS.update H_v s_v y_v x
        = H_v x - α • H_v s_v + (inner ℝ y_v x / inner ℝ y_v s_v) • y_v := by
            have happly := BFGS.update_apply H_v s_v y_v x
            have hsymx : inner ℝ s_v (H_v x) = inner ℝ (H_v s_v) x := by
              simpa using (hSelf.isSymmetric s_v x).symm
            rw [hsymx] at happly
            simpa [a, α] using happly
    _ = H_v z + (inner ℝ y_v x / inner ℝ y_v s_v) • y_v := by
          rw [hz, map_sub, map_smul]
    _ = (updateProjector H_v s_v).adjoint (H_v z) + (inner ℝ y_v x / inner ℝ y_v s_v) • y_v := by
          rw [hadj_apply]
    _ = ((updateProjector H_v s_v).adjoint ∘L H_v ∘L updateProjector H_v s_v
          + (1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v) x := by
          simp [z, InnerProductSpace.rankOne_apply, smul_smul, div_eq_mul_inv, mul_comm]

/-- Helper for Definition 3.3-extra-3: the BFGS update remains self-adjoint once the old operator
is self-adjoint. -/
lemma update_isSelfAdjoint (H_v : H →L[ℝ] H) (s_v y_v : H)
    (hH : ContinuousLinearMap.SelfAdjointStronglyPositive H_v) :
    IsSelfAdjoint (BFGS.update H_v s_v y_v) := by
  -- Rewrite to a sum of two manifestly self-adjoint summands.
  rw [update_eq_adjointConj_add_rankOne H_v s_v y_v hH.isSelfAdjoint]
  have hconj :
      IsSelfAdjoint ((updateProjector H_v s_v).adjoint ∘L H_v ∘L updateProjector H_v s_v) := by
    simpa using hH.isSelfAdjoint.adjoint_conj (updateProjector H_v s_v)
  have hrank :
      IsSelfAdjoint ((1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    simp
  exact hconj.add hrank

omit [CompleteSpace H] in
/-- Helper for Definition 3.3-extra-3: if `x = z + α • s_v` and the curvature observable
`inner ℝ y_v x` records the missing `s_v` component, then `‖x‖²` is controlled by
`‖z‖²` and `(inner ℝ y_v x)²`. -/
lemma normSq_le_splitComponents
    (s_v y_v x z : H) (α : ℝ)
    (hcurv : 0 < inner ℝ y_v s_v)
    (hx : x = z + α • s_v)
    (hy : inner ℝ y_v x = inner ℝ y_v z + α * inner ℝ y_v s_v) :
    ‖x‖ ^ 2 ≤
      (2 + 4 * ‖s_v‖ ^ 2 * ‖y_v‖ ^ 2 / (inner ℝ y_v s_v) ^ 2) * ‖z‖ ^ 2
        + (4 * ‖s_v‖ ^ 2 / (inner ℝ y_v s_v) ^ 2) * (inner ℝ y_v x) ^ 2 := by
  let b := inner ℝ y_v s_v
  have hb : 0 < b := by
    simpa [b] using hcurv
  have hb_sq : 0 < b ^ 2 := by
    positivity
  have hsplit : α * b = inner ℝ y_v x - inner ℝ y_v z := by
    nlinarith [hy]
  have hyz_sq : (inner ℝ y_v z) ^ 2 ≤ ‖y_v‖ ^ 2 * ‖z‖ ^ 2 := by
    simpa [pow_two, real_inner_self_eq_norm_sq, mul_comm, mul_left_comm, mul_assoc] using
      real_inner_mul_inner_self_le y_v z
  have hα_sq_num : α ^ 2 * b ^ 2 ≤ 2 * ((inner ℝ y_v x) ^ 2 + (inner ℝ y_v z) ^ 2) := by
    -- Square the recovery identity `α * b = inner y_v x - inner y_v z`.
    have hsplit_sq : (α * b) ^ 2 = (inner ℝ y_v x - inner ℝ y_v z) ^ 2 := by
      simpa using congrArg (fun t : ℝ ↦ t ^ 2) hsplit
    have hdiff_sq :
        (inner ℝ y_v x - inner ℝ y_v z) ^ 2 ≤ 2 * ((inner ℝ y_v x) ^ 2 + (inner ℝ y_v z) ^ 2) := by
      nlinarith [sq_nonneg (inner ℝ y_v x + inner ℝ y_v z),
        sq_nonneg (inner ℝ y_v x - inner ℝ y_v z)]
    nlinarith [hsplit_sq, hdiff_sq]
  have hα_sq : α ^ 2 ≤ (2 * ((inner ℝ y_v x) ^ 2 + (inner ℝ y_v z) ^ 2)) / b ^ 2 := by
    -- Divide by the strictly positive curvature denominator.
    exact (le_div_iff₀ hb_sq).2 hα_sq_num
  have hα_sq' : α ^ 2 ≤ (2 * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2)) / b ^ 2 := by
    refine le_trans hα_sq ?_
    have hnum :
        2 * ((inner ℝ y_v x) ^ 2 + (inner ℝ y_v z) ^ 2) ≤
          2 * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2) := by
      nlinarith [hyz_sq]
    exact div_le_div_of_nonneg_right hnum (sq_nonneg b)
  have hnorm : ‖x‖ ≤ ‖z‖ + |α| * ‖s_v‖ := by
    -- The decomposition `x = z + α • s_v` converts the norm estimate into triangle inequality.
    rw [hx]
    calc
      ‖z + α • s_v‖ ≤ ‖z‖ + ‖α • s_v‖ := norm_add_le _ _
      _ = ‖z‖ + |α| * ‖s_v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have hnorm_sq :
      ‖x‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * α ^ 2 * ‖s_v‖ ^ 2 := by
    have hsquare : ‖x‖ ^ 2 ≤ (‖z‖ + |α| * ‖s_v‖) ^ 2 := by
      have hrhs_nonneg : 0 ≤ ‖z‖ + |α| * ‖s_v‖ := by
        positivity
      nlinarith [hnorm, norm_nonneg x]
    have hsum :
        (‖z‖ + |α| * ‖s_v‖) ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * (|α| * ‖s_v‖) ^ 2 := by
      nlinarith [sq_nonneg (‖z‖ - |α| * ‖s_v‖)]
    have habs_sq : (|α| * ‖s_v‖) ^ 2 = α ^ 2 * ‖s_v‖ ^ 2 := by
      calc
        (|α| * ‖s_v‖) ^ 2 = |α| ^ 2 * ‖s_v‖ ^ 2 := by ring
        _ = α ^ 2 * ‖s_v‖ ^ 2 := by rw [sq_abs]
    nlinarith [hsquare, hsum, habs_sq]
  have hα_term :
      2 * α ^ 2 * ‖s_v‖ ^ 2 ≤
        (4 * ‖s_v‖ ^ 2 / b ^ 2) * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2) := by
    have hs_nonneg : 0 ≤ 2 * ‖s_v‖ ^ 2 := by
      positivity
    have hmul : (2 * ‖s_v‖ ^ 2) * α ^ 2 ≤
        (2 * ‖s_v‖ ^ 2) * ((2 * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2)) / b ^ 2) :=
      mul_le_mul_of_nonneg_left hα_sq' hs_nonneg
    have hmul' := hmul
    ring_nf at hmul' ⊢
    exact hmul'
  -- Substitute the `α²` bound into the norm estimate and collect the `‖z‖²` and `(inner y_v x)²`
  -- coefficients.
  have hnorm' :
      ‖x‖ ^ 2 ≤
        2 * ‖z‖ ^ 2 +
          (4 * ‖s_v‖ ^ 2 / b ^ 2) * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2) := by
    nlinarith [hnorm_sq, hα_term]
  calc
    ‖x‖ ^ 2 ≤
        2 * ‖z‖ ^ 2 +
          (4 * ‖s_v‖ ^ 2 / b ^ 2) * ((inner ℝ y_v x) ^ 2 + ‖y_v‖ ^ 2 * ‖z‖ ^ 2) := hnorm'
    _ =
        (2 + 4 * ‖s_v‖ ^ 2 * ‖y_v‖ ^ 2 / b ^ 2) * ‖z‖ ^ 2
          + (4 * ‖s_v‖ ^ 2 / b ^ 2) * (inner ℝ y_v x) ^ 2 := by
          ring

/-- Helper for Definition 3.3-extra-3: the BFGS quadratic form splits into the old quadratic form
evaluated on the projected vector plus the positive curvature correction. -/
lemma updateQuadraticFormSplit
    (H_v : H →L[ℝ] H) (s_v y_v x : H)
    (hSelf : IsSelfAdjoint H_v) :
    inner ℝ (BFGS.update H_v s_v y_v x) x =
      inner ℝ (H_v (updateProjector H_v s_v x)) (updateProjector H_v s_v x)
        + (inner ℝ y_v x) ^ 2 / inner ℝ y_v s_v := by
  -- Rewrite the operator once, then evaluate the two summands separately.
  rw [update_eq_adjointConj_add_rankOne H_v s_v y_v hSelf]
  calc
    inner ℝ
        (((updateProjector H_v s_v).adjoint ∘L H_v ∘L updateProjector H_v s_v
          + (1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v) x) x
        =
          inner ℝ (((updateProjector H_v s_v).adjoint ∘L H_v ∘L updateProjector H_v s_v) x) x
            + inner ℝ (((1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v) x) x := by
            rw [add_apply, inner_add_left]
    _ = inner ℝ (H_v (updateProjector H_v s_v x)) (updateProjector H_v s_v x)
          + inner ℝ (((1 / inner ℝ y_v s_v) • InnerProductSpace.rankOne ℝ y_v y_v) x) x := by
            rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
              ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℝ (H_v (updateProjector H_v s_v x)) (updateProjector H_v s_v x)
          + (inner ℝ y_v x) ^ 2 / inner ℝ y_v s_v := by
            congr 1
            rw [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_left]
            simp
            ring_nf

/-- Helper for Definition 3.3-extra-3: the BFGS update satisfies a uniform quadratic lower bound
under the usual curvature condition. -/
lemma update_exists_inner_lowerBound
    (H_v : H →L[ℝ] H) (s_v y_v : H)
    (hH : ContinuousLinearMap.SelfAdjointStronglyPositive H_v)
    (hcurv : 0 < inner ℝ y_v s_v) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : H, c * ‖x‖ ^ 2 ≤ inner ℝ (BFGS.update H_v s_v y_v x) x := by
  obtain ⟨c0, hc0, hc0_bound⟩ := hH.exists_inner_lowerBound
  let b := inner ℝ y_v s_v
  let C1 := 2 + 4 * ‖s_v‖ ^ 2 * ‖y_v‖ ^ 2 / b ^ 2
  let C2 := 4 * ‖s_v‖ ^ 2 / b ^ 2
  let C := C1 / c0 + C2 * b
  have hb : 0 < b := by
    simpa [b] using hcurv
  have hC_pos : 0 < C := by
    -- The comparison constant is positive because the coercive part already contributes.
    have hC1_pos : 0 < C1 := by
      positivity
    positivity
  refine ⟨1 / C, by positivity, ?_⟩
  intro x
  let a := inner ℝ (H_v s_v) s_v
  let α := inner ℝ (H_v s_v) x / a
  let z := updateProjector H_v s_v x
  have hz : z = x - α • s_v := by
    -- Normalize the projector output before applying the norm-control helper.
    simpa [a, α, z] using updateProjector_apply H_v s_v x
  have hx_split : x = z + α • s_v := by
    rw [hz]
    abel
  have hyz : inner ℝ y_v z = inner ℝ y_v x - α * b := by
    simpa [b] using by
      rw [hz, inner_sub_right, inner_smul_right]
  have hy_split : inner ℝ y_v x = inner ℝ y_v z + α * b := by
    nlinarith [hyz]
  have hnorm :
      ‖x‖ ^ 2 ≤ C1 * ‖z‖ ^ 2 + C2 * (inner ℝ y_v x) ^ 2 := by
    simpa [b, C1, C2] using normSq_le_splitComponents s_v y_v x z α hcurv hx_split hy_split
  have hquad :
      inner ℝ (BFGS.update H_v s_v y_v x) x =
        inner ℝ (H_v z) z + (1 / b) * (inner ℝ y_v x) ^ 2 := by
    simpa [b, z, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      updateQuadraticFormSplit H_v s_v y_v x hH.isSelfAdjoint
  have hlower :
      c0 * ‖z‖ ^ 2 + (1 / b) * (inner ℝ y_v x) ^ 2
        ≤ inner ℝ (BFGS.update H_v s_v y_v x) x := by
    nlinarith [hc0_bound z, hquad]
  have hmajor1 : C1 ≤ C * c0 := by
    have hC2_nonneg : 0 ≤ C2 := by
      positivity
    have htail : 0 ≤ C2 * b * c0 := by
      positivity
    have hC_expand : C * c0 = C1 + c0 * C2 * b := by
      dsimp [C]
      field_simp [hc0.ne']
    nlinarith [hC_expand, htail]
  have hmajor2 : C2 ≤ C * (1 / b) := by
    have hhead : 0 ≤ C1 / (c0 * b) := by
      positivity
    have hC_expand : C * (1 / b) = C1 / (c0 * b) + C2 := by
      dsimp [C]
      field_simp [hc0.ne', hb.ne']
    nlinarith [hC_expand, hhead]
  have hmiddle :
      C1 * ‖z‖ ^ 2 + C2 * (inner ℝ y_v x) ^ 2 ≤
        C * (c0 * ‖z‖ ^ 2 + (1 / b) * (inner ℝ y_v x) ^ 2) := by
    nlinarith [hmajor1, hmajor2]
  have hscaled :
      ‖x‖ ^ 2 ≤ C * inner ℝ (BFGS.update H_v s_v y_v x) x := by
    exact le_trans hnorm <| le_trans hmiddle <|
      mul_le_mul_of_nonneg_left hlower (le_of_lt hC_pos)
  have hscaled' :
      (1 / C) * ‖x‖ ^ 2 ≤ (1 / C) * (C * inner ℝ (BFGS.update H_v s_v y_v x) x) := by
    exact mul_le_mul_of_nonneg_left hscaled (by positivity)
  calc
    (1 / C) * ‖x‖ ^ 2 ≤ (1 / C) * (C * inner ℝ (BFGS.update H_v s_v y_v x) x) := hscaled'
    _ = inner ℝ (BFGS.update H_v s_v y_v x) x := by
          field_simp [hC_pos.ne']

/-- Definition 3.3-extra-3 (2). The BFGS update preserves self-adjoint strong positivity under
the curvature condition `0 < inner ℝ y_v s_v`. -/
theorem update_selfAdjointStronglyPositive (H_v : H →L[ℝ] H) (s_v y_v : H)
    (hH : ContinuousLinearMap.SelfAdjointStronglyPositive H_v)
    (hcurv : 0 < inner ℝ y_v s_v) :
    ContinuousLinearMap.SelfAdjointStronglyPositive (BFGS.update H_v s_v y_v) := by
  -- Assemble the structural self-adjointness and the explicit coercive lower bound.
  refine ContinuousLinearMap.SelfAdjointStronglyPositive.ofSelfAdjoint_isStronglyPositive
    (update_isSelfAdjoint H_v s_v y_v hH) ?_
  rw [ContinuousLinearMap.isStronglyPositive_iff]
  exact update_exists_inner_lowerBound H_v s_v y_v hH hcurv

end BFGS
