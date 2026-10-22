/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_4

public section

noncomputable section

universe u v

namespace GeneralizedTikhonov

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

/-- The normal operator `K†K + αL` for quadratic generalized Tikhonov regularization. -/
def normalOperator (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) : H₁ →L[ℝ] H₁ :=
  K.adjoint.comp K + α • L

/-- Applying `normalOperator` to `f` gives `K† (K f) + α • L f`. -/
theorem normalOperator_apply (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) (f : H₁) :
    normalOperator K L α f = K.adjoint (K f) + α • (L f) := by
  simp [normalOperator]

/-- If `L` is strongly positive and `α > 0`, then the quadratic form of
`normalOperator K L α` dominates `(α * c₀) * ‖f‖ ^ 2` for a suitable `c₀ > 0`. -/
theorem normalOperator_exists_inner_lowerBound
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : L.IsStronglyPositive) {α : ℝ} (hα : 0 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : H₁, c * ‖f‖ ^ 2 ≤ inner ℝ (normalOperator K L α f) f := by
  obtain ⟨c0, hc0, hc0_bound⟩ := hL.exists_inner_lowerBound
  refine ⟨α * c0, mul_pos hα hc0, fun f ↦ ?_⟩
  have hK_nonneg : 0 ≤ inner ℝ (K.adjoint (K f)) f := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_self_nonneg (x := K f)
  calc
    (α * c0) * ‖f‖ ^ 2 = α * (c0 * ‖f‖ ^ 2) := by rw [mul_assoc]
    _ ≤ α * inner ℝ (L f) f := by
      exact mul_le_mul_of_nonneg_left (hc0_bound f) (le_of_lt hα)
    _ ≤ inner ℝ (normalOperator K L α f) f := by
      rw [normalOperator_apply, inner_add_left, inner_smul_left]
      exact le_add_of_nonneg_left hK_nonneg

/-- If `L` is strongly positive and `α > 0`, then the normal operator `K†K + αL`
is invertible. -/
theorem normalOperator_isUnit
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : L.IsStronglyPositive) {α : ℝ} (hα : 0 < α) :
    IsUnit (normalOperator K L α) := by
  obtain ⟨c, hc, hc_bound⟩ := normalOperator_exists_inner_lowerBound K L hL hα
  let cNN : NNReal := ⟨c, le_of_lt hc⟩
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (f := normalOperator K L α) (c := cNN) hc ?_
  intro f
  have hnonneg : 0 ≤ inner ℝ (normalOperator K L α f) f := by
    exact le_trans (mul_nonneg (le_of_lt hc) (sq_nonneg ‖f‖)) (hc_bound f)
  have hc_bound' : ‖f‖ ^ 2 * c ≤ inner ℝ (normalOperator K L α f) f := by
    simpa [mul_comm] using hc_bound f
  change ‖f‖ ^ 2 * (cNN : ℝ) ≤ ‖inner ℝ (normalOperator K L α f) f‖
  have hcNN_coe : (cNN : ℝ) = c := rfl
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hcNN_coe]
  exact hc_bound'

/-- The ring-theoretic inverse of `normalOperator K L α`. Under the assumptions of Theorem 2.44,
this is the inverse of the normal operator. -/
def normalOperatorInverse
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) : H₁ →L[ℝ] H₁ :=
  Ring.inverse (normalOperator K L α)

/-- When `normalOperator K L α` is invertible, `normalOperatorInverse K L α` is its inverse. -/
theorem normalOperatorInverse_eq_inv
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ)
    (hA : IsUnit (normalOperator K L α)) :
    normalOperatorInverse K L α = hA.unit⁻¹ := by
  simpa [normalOperatorInverse, hA.unit_spec] using
    (Ring.inverse_unit hA.unit :
      Ring.inverse (((hA.unit : (H₁ →L[ℝ] H₁)ˣ) : H₁ →L[ℝ] H₁)) =
        ↑(hA.unit⁻¹ : (H₁ →L[ℝ] H₁)ˣ))

/-- The canonical reconstruction operator attached to `K`, `L`, and `α`. -/
def reconstructionOperator
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) : H₂ →L[ℝ] H₁ :=
  (normalOperatorInverse K L α).comp K.adjoint

/-- Evaluating `reconstructionOperator` applies the inverse normal operator to `K† g`. -/
theorem reconstructionOperator_apply
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) (g : H₂) :
    reconstructionOperator K L α g = normalOperatorInverse K L α (K.adjoint g) := by
  simp [reconstructionOperator]

/-- A map `Rα` is a reconstruction at parameter `α` when each output datum `Rα g`
minimizes the quadratic Tikhonov functional with datum `g`. -/
def IsReconstruction (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) (Rα : H₂ → H₁) : Prop :=
  ∀ g : H₂, K.IsTikhonovMinimizer L Set.univ g α (Rα g)

/-- The defining characterization of `IsReconstruction`. -/
theorem isReconstruction_iff
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) (Rα : H₂ → H₁) :
    IsReconstruction K L α Rα ↔
      ∀ g : H₂, IsMinOn (K.tikhonovFunctional L g α) Set.univ (Rα g) := by
  simp [IsReconstruction, ContinuousLinearMap.isTikhonovMinimizer_iff]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- A reconstruction operator yields Tikhonov minimizers pointwise. -/
theorem IsReconstruction.isTikhonovMinimizer
    {K : H₁ →L[ℝ] H₂} {L : H₁ →L[ℝ] H₁} {α : ℝ} {Rα : H₂ → H₁}
    (hR : IsReconstruction K L α Rα) (g : H₂) :
    K.IsTikhonovMinimizer L Set.univ g α (Rα g) :=
  hR g

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- A reconstruction operator minimizes the Tikhonov functional pointwise. -/
theorem IsReconstruction.isMinOn
    {K : H₁ →L[ℝ] H₂} {L : H₁ →L[ℝ] H₁} {α : ℝ} {Rα : H₂ → H₁}
    (hR : IsReconstruction K L α Rα) (g : H₂) :
    IsMinOn (K.tikhonovFunctional L g α) Set.univ (Rα g) := by
  exact (hR.isTikhonovMinimizer g).isMinOn

/-- The canonical reconstruction operator is continuous. -/
theorem reconstructionOperator_continuous
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (α : ℝ) :
    Continuous (reconstructionOperator K L α : H₂ → H₁) :=
  (reconstructionOperator K L α).continuous

/-- Helper for Theorem 2.44: unfold the quadratic Tikhonov objective to its explicit
residual-plus-penalty formula. -/
lemma tikhonovFunctional_eq
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (g : H₂) (α : ℝ) (f : H₁) :
    K.tikhonovFunctional L g α f = ‖K f - g‖ ^ 2 / 2 + α * inner ℝ (L f) f := by
  -- The imported owner theorem records the explicit residual-plus-penalty formula.
  simpa using ContinuousLinearMap.tikhonovFunctional_def K L g α f

/-- Helper for Theorem 2.44: self-adjointness lets us swap the penalty cross term across the
inner product. -/
lemma selfAdjointPenaltyCross
    (L : H₁ →L[ℝ] H₁) (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L)
    (f h : H₁) :
    inner ℝ (L h) f = inner ℝ (L f) h := by
  -- Move `L` across the inner product through the adjoint, then use self-adjointness.
  calc
    inner ℝ (L h) f = inner ℝ h (L.adjoint f) := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ h (L f) := by
      rw [hL.isSelfAdjoint.adjoint_eq]
    _ = inner ℝ (L f) h := by
      rw [real_inner_comm]

/-- Helper for Theorem 2.44: the scaled reconstruction operator at parameter `2 * α`
satisfies the normal equation matching the current normalization of
`K.tikhonovFunctional L g α`. -/
lemma scaledReconstructionNormalEquation
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ} (hα : 0 < α)
    (g : H₂) :
    normalOperator K L (2 * α) (reconstructionOperator K L (2 * α) g) = K.adjoint g := by
  have h2α : 0 < 2 * α := by positivity
  have hA : IsUnit (normalOperator K L (2 * α)) :=
    normalOperator_isUnit K L hL.stronglyPositive h2α
  -- Route correction: the minimizer equation matches the objective after scaling the operator
  -- parameter to `2 * α`, so we prove the normal equation directly at that scale.
  calc
    normalOperator K L (2 * α) (reconstructionOperator K L (2 * α) g)
        = (normalOperator K L (2 * α) * normalOperatorInverse K L (2 * α)) (K.adjoint g) := by
          rw [reconstructionOperator_apply, mul_apply_eq_comp]
    _ = (normalOperator K L (2 * α) * hA.unit⁻¹) (K.adjoint g) := by
      rw [normalOperatorInverse_eq_inv K L (2 * α) hA]
    _ = (((hA.unit : (H₁ →L[ℝ] H₁)ˣ) : H₁ →L[ℝ] H₁) * hA.unit⁻¹) (K.adjoint g) := by
      rw [hA.unit_spec]
    _ = K.adjoint g := by
      have hMul :
          (((hA.unit : (H₁ →L[ℝ] H₁)ˣ) : H₁ →L[ℝ] H₁) * ↑hA.unit⁻¹) = (1 : H₁ →L[ℝ] H₁) := by
        exact Units.mul_inv hA.unit
      calc
        ((((hA.unit : (H₁ →L[ℝ] H₁)ˣ) : H₁ →L[ℝ] H₁) * ↑hA.unit⁻¹) (K.adjoint g))
            = (1 : H₁ →L[ℝ] H₁) (K.adjoint g) := by
                exact congrArg (fun A : H₁ →L[ℝ] H₁ => A (K.adjoint g)) hMul
        _ = K.adjoint g := by
          simp

/-- Helper for Theorem 2.44: the mixed first-order term in the objective expansion vanishes
when the base point satisfies the scaled normal equation. -/
lemma scaledNormalEquationMixedTermVanishes
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ}
    {g : H₂} {f₀ h : H₁}
    (hEq : normalOperator K L (2 * α) f₀ = K.adjoint g) :
    inner ℝ (K f₀ - g) (K h) + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀) = 0 := by
  have hEq' : K.adjoint (K f₀ - g) + (2 * α) • L f₀ = 0 := by
    -- Rewrite the normal equation so its left-hand side is exactly the mixed derivative term.
    rw [normalOperator_apply] at hEq
    have hSub : K.adjoint (K f₀) + (2 * α) • L f₀ - K.adjoint g = 0 :=
      sub_eq_zero.mpr hEq
    simpa [ContinuousLinearMap.map_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hSub
  have hInner := congrArg (fun x : H₁ ↦ inner ℝ x h) hEq'
  have hNormal :
      inner ℝ (K f₀ - g) (K h) + (2 * α) * inner ℝ (L f₀) h = 0 := by
    -- Turn the operator equation into a scalar identity and move `K†` across the inner product.
    simpa [inner_add_left, inner_smul_left, inner_sub_left, ContinuousLinearMap.map_sub,
      ContinuousLinearMap.adjoint_inner_left] using hInner
  have hCross : inner ℝ (L h) f₀ = inner ℝ (L f₀) h :=
    selfAdjointPenaltyCross L hL f₀ h
  -- Compare the scalar identity coming from the normal equation with the expanded mixed term.
  calc
    inner ℝ (K f₀ - g) (K h) + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀)
        = inner ℝ (K f₀ - g) (K h) + (2 * α) * inner ℝ (L f₀) h := by
            rw [hCross]
            ring
    _ = 0 := by
      exact hNormal

/-- Helper for Theorem 2.44: expanding the objective at a point satisfying the scaled
normal equation leaves only a nonnegative quadratic remainder. -/
lemma tikhonovFunctionalAddDisplacement
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ}
    {g : H₂} {f₀ h : H₁}
    (hEq : normalOperator K L (2 * α) f₀ = K.adjoint g) :
    K.tikhonovFunctional L g α (f₀ + h)
      = K.tikhonovFunctional L g α f₀ + ‖K h‖ ^ 2 / 2 + α * inner ℝ (L h) h := by
  have hResidual :
      ‖K (f₀ + h) - g‖ ^ 2 / 2
        = ‖K f₀ - g‖ ^ 2 / 2 + inner ℝ (K f₀ - g) (K h) + ‖K h‖ ^ 2 / 2 := by
    have hMap : K (f₀ + h) - g = (K f₀ - g) + K h := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    -- Expand the residual norm square at the displaced point.
    rw [hMap, ← real_inner_self_eq_norm_sq, real_inner_add_add_self,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hPenalty :
      α * inner ℝ (L (f₀ + h)) (f₀ + h)
        = α * inner ℝ (L f₀) f₀
            + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀)
            + α * inner ℝ (L h) h := by
    have hPenaltyInner :
        inner ℝ (L (f₀ + h)) (f₀ + h)
          = inner ℝ (L f₀) f₀ + inner ℝ (L f₀) h + inner ℝ (L h) f₀ + inner ℝ (L h) h := by
      -- Expand the penalty term before distributing the scalar factor `α`.
      simp [map_add, inner_add_left, inner_add_right]
      ring
    calc
      α * inner ℝ (L (f₀ + h)) (f₀ + h)
          = α * (inner ℝ (L f₀) f₀ + inner ℝ (L f₀) h + inner ℝ (L h) f₀
              + inner ℝ (L h) h) := by
                rw [hPenaltyInner]
      _ = α * inner ℝ (L f₀) f₀
            + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀)
            + α * inner ℝ (L h) h := by
              ring
  have hMixed :
      inner ℝ (K f₀ - g) (K h) + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀) = 0 :=
    scaledNormalEquationMixedTermVanishes K L hL hEq
  -- Combine the residual and penalty expansions, then eliminate the mixed term.
  rw [tikhonovFunctional_eq, tikhonovFunctional_eq, hResidual, hPenalty]
  calc
    ‖K f₀ - g‖ ^ 2 / 2 + inner ℝ (K f₀ - g) (K h) + ‖K h‖ ^ 2 / 2
        + (α * inner ℝ (L f₀) f₀ + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀)
            + α * inner ℝ (L h) h)
        = (‖K f₀ - g‖ ^ 2 / 2 + α * inner ℝ (L f₀) f₀)
            + (inner ℝ (K f₀ - g) (K h)
                + α * (inner ℝ (L f₀) h + inner ℝ (L h) f₀))
            + (‖K h‖ ^ 2 / 2 + α * inner ℝ (L h) h) := by
              ring
    _ = (‖K f₀ - g‖ ^ 2 / 2 + α * inner ℝ (L f₀) f₀) + 0
          + (‖K h‖ ^ 2 / 2 + α * inner ℝ (L h) h) := by
            rw [hMixed]
    _ = (‖K f₀ - g‖ ^ 2 / 2 + α * inner ℝ (L f₀) f₀)
          + ‖K h‖ ^ 2 / 2 + α * inner ℝ (L h) h := by
            ring

/-- Helper for Theorem 2.44: the scaled reconstruction point minimizes the Tikhonov functional
for each datum `g`. -/
lemma scaledReconstruction_isMinOn
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ} (hα : 0 < α)
    (g : H₂) :
    IsMinOn (K.tikhonovFunctional L g α) Set.univ (reconstructionOperator K L (2 * α) g) := by
  rw [isMinOn_univ_iff]
  intro f
  let f₀ : H₁ := reconstructionOperator K L (2 * α) g
  have hEq : normalOperator K L (2 * α) f₀ = K.adjoint g :=
    scaledReconstructionNormalEquation K L hL hα g
  have hExpand :
      K.tikhonovFunctional L g α f
        = K.tikhonovFunctional L g α f₀
            + ‖K (f - f₀)‖ ^ 2 / 2
            + α * inner ℝ (L (f - f₀)) (f - f₀) := by
    -- Rewrite `f` as `f₀ + (f - f₀)` before applying the quadratic remainder formula.
    simpa [f₀, sub_eq_add_neg, add_left_comm, add_comm] using
      tikhonovFunctionalAddDisplacement K L hL (g := g) (f₀ := f₀) (h := f - f₀) hEq
  obtain ⟨c₀, hc₀, hc₀_bound⟩ := hL.exists_inner_lowerBound
  have hPenalty_nonneg : 0 ≤ α * inner ℝ (L (f - f₀)) (f - f₀) := by
    -- Assumption A2 gives nonnegativity of the penalty quadratic form.
    have hInner_nonneg : 0 ≤ inner ℝ (L (f - f₀)) (f - f₀) := by
      exact le_trans (mul_nonneg (le_of_lt hc₀) (sq_nonneg ‖f - f₀‖)) (hc₀_bound (f - f₀))
    exact mul_nonneg (le_of_lt hα) hInner_nonneg
  have hResidual_nonneg : 0 ≤ ‖K (f - f₀)‖ ^ 2 / 2 := by positivity
  -- The expansion expresses every competitor value as the base value plus two nonnegative terms.
  change K.tikhonovFunctional L g α f₀ ≤ K.tikhonovFunctional L g α f
  rw [hExpand]
  have hRemainder_nonneg :
      0 ≤ ‖K (f - f₀)‖ ^ 2 / 2 + α * inner ℝ (L (f - f₀)) (f - f₀) :=
    add_nonneg hResidual_nonneg hPenalty_nonneg
  linarith

/-- Theorem 2.44. Under the standing real-Hilbert-space assumptions on `K` and the
self-adjoint strongly positive penalty operator `L`, for every `α > 0` there exists a
continuous reconstruction map `Rα` such that each `Rα g` minimizes
`K.tikhonovFunctional L g α` on all of `H₁`. -/
theorem exists_continuous_reconstruction
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁)
    (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) {α : ℝ} (hα : 0 < α) :
    ∃ Rα : H₂ → H₁, Continuous Rα ∧ IsReconstruction K L α Rα := by
  -- Choose the explicit reconstruction operator with the scaled parameter matching the
  -- normalization of the quadratic objective, then prove pointwise minimality directly.
  refine ⟨reconstructionOperator K L (2 * α), reconstructionOperator_continuous K L (2 * α), ?_⟩
  rw [isReconstruction_iff]
  intro g
  exact scaledReconstruction_isMinOn K L hL hα g

end GeneralizedTikhonov
