/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_1.QuadraticModel
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Definition_3_3_1.Step
public import Mathlib.Analysis.Calculus.LocalExtr.LineDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace Newton

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Definition 3.3-extra-1 (1). Equation `(3.15)` is formalized by the Newton
quadratic model `Newton.quadraticModel`. -/
#check Newton.quadraticModel

/-- Helper for Definition 3.3-extra-1: a self-adjoint strongly positive bounded
operator on `H` is invertible. -/
lemma hessianIsUnit_of_selfAdjointStronglyPositive
    {L : H →L[ℝ] H} (hL : ContinuousLinearMap.SelfAdjointStronglyPositive L) :
    IsUnit L := by
  -- Convert the coercive quadratic lower bound into mathlib's invertibility criterion.
  obtain ⟨c, hc, hc_bound⟩ := hL.exists_inner_lowerBound
  let cNN : NNReal := ⟨c, le_of_lt hc⟩
  refine ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (f := L) (c := cNN) hc ?_
  intro f
  have hnonneg : 0 ≤ inner ℝ (L f) f := by
    exact le_trans (mul_nonneg (le_of_lt hc) (sq_nonneg ‖f‖)) (hc_bound f)
  have hcNN : (cNN : ℝ) = c := rfl
  change ‖f‖ ^ 2 * (cNN : ℝ) ≤ ‖inner ℝ (L f) f‖
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg, hcNN]
  simpa [mul_comm] using hc_bound f

/-- Helper for Definition 3.3-extra-1: translating the Newton quadratic model by
a stationary step leaves only the pure quadratic remainder. -/
lemma quadraticModel_translate_eq_base_add_half_inner
    (J : H → ℝ) (f_v s0 h : H)
    (hSelfAdjoint : IsSelfAdjoint (hessian J f_v))
    (hstep : gradient J f_v + hessian J f_v s0 = 0) :
    quadraticModel J f_v (s0 + h) =
      quadraticModel J f_v s0 + (1 / 2 : ℝ) * inner ℝ (hessian J f_v h) h := by
  let L := hessian J f_v
  let g := gradient J f_v
  have hg : g = -L s0 := by
    -- Rewrite the stationarity equation as the explicit linear term cancellation.
    exact eq_neg_of_add_eq_zero_left <| by simpa [g, L] using hstep
  have hcross1 : inner ℝ (L s0) h = inner ℝ s0 (L h) := by
    exact hSelfAdjoint.isSymmetric s0 h
  have hcross2 : inner ℝ (L h) s0 = inner ℝ (L s0) h := by
    calc
      inner ℝ (L h) s0 = inner ℝ h (L s0) := by
        exact hSelfAdjoint.isSymmetric h s0
      _ = inner ℝ (L s0) h := by
        rw [real_inner_comm]
  -- Expand both quadratic models and cancel the cross terms using self-adjointness.
  rw [quadraticModel_apply, quadraticModel_apply]
  simp only [L, g, hg, ContinuousLinearMap.map_add, inner_add_left, inner_add_right, hcross1,
    hcross2, inner_neg_left]
  ring

/-- Helper for Definition 3.3-extra-1: along any direction `h`, the line
derivative of the Newton quadratic model at `s` is `⟪gradient J f_v + hessian J f_v s, h⟫`. -/
lemma hasLineDerivAt_quadraticModel_of_isSelfAdjoint
    (J : H → ℝ) (f_v s h : H)
    (hSelfAdjoint : IsSelfAdjoint (hessian J f_v)) :
    HasLineDerivAt ℝ (quadraticModel J f_v)
      (inner ℝ (gradient J f_v + hessian J f_v s) h) s h := by
  let g := gradient J f_v
  let L := hessian J f_v
  have hId : HasDerivAt (fun t : ℝ ↦ t) 1 0 := hasDerivAt_id' (x := (0 : ℝ))
  have hs : HasDerivAt (fun t : ℝ ↦ s + t • h) h 0 := by
    -- The affine line through `s` in direction `h` has derivative `h`.
    simpa [one_smul] using (hId.smul_const h).const_add s
  have hLinear : HasDerivAt (fun t : ℝ ↦ t * inner ℝ g h) (inner ℝ g h) 0 := by
    -- After expanding the inner product, the linear term is affine in `t`.
    simpa [one_mul] using (hId.mul_const (inner ℝ g h))
  have hLs : HasDerivAt (fun t : ℝ ↦ L (s + t • h)) (L h) 0 := by
    -- Linearity turns the Hessian action on the affine line into another affine line.
    simpa [L, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, one_smul] using
      (hId.smul_const (L h)).const_add (L s)
  have hQuadraticCore :
      HasDerivAt (fun t : ℝ ↦ inner ℝ (L s + t • L h) (s + t • h))
        (inner ℝ (L s) h + inner ℝ (L h) s) 0 := by
    -- Differentiate the quadratic term by the product rule for the inner product.
    simpa [L, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, one_smul] using
      hLs.inner ℝ hs
  have hcross : inner ℝ (L h) s = inner ℝ (L s) h := by
    calc
      inner ℝ (L h) s = inner ℝ h (L s) := by
        exact hSelfAdjoint.isSymmetric h s
      _ = inner ℝ (L s) h := by
        rw [real_inner_comm]
  have hQuadratic :
      HasDerivAt
        (fun t : ℝ ↦ (1 / 2 : ℝ) * inner ℝ (L s + t • L h) (s + t • h))
        (inner ℝ (L s) h) 0 := by
    -- Scale the derivative of the quadratic core by `1 / 2`.
    have hQuadraticRaw :
        HasDerivAt
          (fun t : ℝ ↦ (1 / 2 : ℝ) * inner ℝ (L s + t • L h) (s + t • h))
          ((1 / 2 : ℝ) * (inner ℝ (L s) h + inner ℝ (L h) s)) 0 :=
      hQuadraticCore.const_mul (1 / 2 : ℝ)
    have hQuadraticVal :
        (1 / 2 : ℝ) * (inner ℝ (L s) h + inner ℝ (L h) s) = inner ℝ (L s) h := by
      rw [hcross]
      ring
    rw [hQuadraticVal] at hQuadraticRaw
    exact hQuadraticRaw
  -- Assemble the constant, linear, and quadratic pieces of the model on the line.
  have hConst : HasDerivAt (fun t : ℝ ↦ J f_v + inner ℝ g s) 0 0 := by
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := J f_v + inner ℝ g s))
  have hTotalRaw :
      HasDerivAt
        ((fun t : ℝ ↦ J f_v + inner ℝ g s) +
          ((fun t : ℝ ↦ t * inner ℝ g h) +
            fun t : ℝ ↦ (1 / 2 : ℝ) * inner ℝ (L s + t • L h) (s + t • h)))
        (0 + (inner ℝ g h + inner ℝ (L s) h)) 0 :=
    hConst.add (hLinear.add hQuadratic)
  have hTotal :
      HasDerivAt
        (fun t : ℝ ↦
          (J f_v + inner ℝ g s) +
            (t * inner ℝ g h +
              (1 / 2 : ℝ) * inner ℝ (L s + t • L h) (s + t • h))
          )
        (inner ℝ (g + L s) h) 0 := by
    convert hTotalRaw using 1
    · funext t
      rfl
    · simp [inner_add_left]
  have hEq :
      (fun t : ℝ ↦ quadraticModel J f_v (s + t • h)) =ᶠ[nhds (0 : ℝ)]
        (fun t : ℝ ↦
          (J f_v + inner ℝ g s) +
            (t * inner ℝ g h +
              (1 / 2 : ℝ) * inner ℝ (L s + t • L h) (s + t • h))
          ) := by
    -- Expand the quadratic model along the line to the explicit scalar expression.
    exact Filter.Eventually.of_forall fun t ↦ by
      simp [quadraticModel_apply, g, L, inner_add_left, inner_add_right, add_assoc,
        add_left_comm, add_comm, ContinuousLinearMap.map_add]
  unfold HasLineDerivAt
  exact hTotal.congr_of_eventuallyEq hEq

/-- Definition 3.3-extra-1 (2). If `hessian J f_v` is self-adjoint strongly
positive, then `quadraticModel J f_v` has a unique minimizer on
`Set.univ`. -/
theorem existsUnique_isMinOn_quadraticModel_of_selfAdjointStronglyPositive
    (J : H → ℝ) (f_v : H)
    (hHess : ContinuousLinearMap.SelfAdjointStronglyPositive (hessian J f_v)) :
    ∃! s : H, IsMinOn (quadraticModel J f_v) Set.univ s := by
  let L := hessian J f_v
  let g := gradient J f_v
  have hLUnit : IsUnit L := hessianIsUnit_of_selfAdjointStronglyPositive hHess
  let s0 : H := -Ring.inverse L g
  have hstep0 : g + L s0 = 0 := by
    -- The explicit Newton step solves the stationary equation by inverse cancellation.
    calc
      g + L s0 = g - L (Ring.inverse L g) := by
        simp [s0, sub_eq_add_neg]
      _ = g - (L * Ring.inverse L) g := by
        rfl
      _ = g - (1 : H →L[ℝ] H) g := by
        rw [Ring.mul_inverse_cancel L hLUnit]
      _ = g - g := by
        simp
      _ = 0 := by
        simp
  have hmin0 : IsMinOn (quadraticModel J f_v) Set.univ s0 := by
    -- Every point is obtained from `s0` by a displacement whose quadratic remainder is nonnegative.
    rw [isMinOn_univ_iff]
    intro t
    let d : H := t - s0
    have ht_eq : t = s0 + d := by
      simp [d, sub_eq_add_neg, add_left_comm]
    -- Rewrite every comparison against `s0` as a nonnegative quadratic remainder.
    rw [ht_eq, quadraticModel_translate_eq_base_add_half_inner J f_v s0 d hHess.isSelfAdjoint
      (by simpa [g, L] using hstep0)]
    have hnonneg : 0 ≤ inner ℝ (L d) d := by
      exact hHess.isPositive.inner_nonneg_left d
    nlinarith
  refine ⟨s0, hmin0, ?_⟩
  intro t ht
  have hmin0' : ∀ x : H, quadraticModel J f_v s0 ≤ quadraticModel J f_v x :=
    (isMinOn_univ_iff.mp hmin0)
  have ht' : ∀ x : H, quadraticModel J f_v t ≤ quadraticModel J f_v x :=
    (isMinOn_univ_iff.mp ht)
  let d : H := t - s0
  have ht_eq : t = s0 + d := by
    simp [d, sub_eq_add_neg, add_left_comm]
  have hcompare : quadraticModel J f_v t = quadraticModel J f_v s0 := by
    exact le_antisymm (ht' s0) (hmin0' t)
  have htranslate :=
    quadraticModel_translate_eq_base_add_half_inner J f_v s0 d hHess.isSelfAdjoint
      (by simpa [g, L] using hstep0)
  have hquadraticZero : (1 / 2 : ℝ) * inner ℝ (L d) d = 0 := by
    -- Equality of the two model values forces the translated quadratic remainder to vanish.
    rw [← ht_eq] at htranslate
    linarith
  have hdzero : d = 0 := by
    by_contra hd
    have hpos : 0 < inner ℝ (L d) d := hHess.inner_pos hd
    nlinarith
  -- The only minimizer is the explicit Newton step `s0`.
  simpa [d] using sub_eq_zero.mp hdzero

/-- Definition 3.3-extra-1 (3). If the Hessian coefficient in the Newton
quadratic model is self-adjoint and `s` minimizes `quadraticModel J f_v`
on `Set.univ`, then `s` satisfies the Newton step equation. -/
theorem isStep_of_isMinOn_quadraticModel
    (J : H → ℝ) (f_v s : H)
    (hSelfAdjoint : IsSelfAdjoint (hessian J f_v))
    (hmin : IsMinOn (quadraticModel J f_v) Set.univ s) :
    IsStep J f_v s := by
  let v := gradient J f_v + hessian J f_v s
  -- Differentiate the quadratic model along the candidate stationary direction `v`.
  have hline :
      HasLineDerivAt ℝ (quadraticModel J f_v) (inner ℝ v v) s v := by
    simpa [v] using
      hasLineDerivAt_quadraticModel_of_isSelfAdjoint J f_v s v hSelfAdjoint
  have hzero : inner ℝ v v = 0 := by
    -- A global minimizer has zero line derivative in every direction, hence in direction `v`.
    exact hmin.hasLineDerivAt_eq_zero hline <| Filter.Eventually.of_forall fun _ ↦ by simp
  have hv : v = 0 := by
    simpa [v] using (inner_self_eq_zero.mp hzero)
  -- Unfold the Newton step predicate back to the normal equation.
  exact (isStep_iff J f_v s).2 <| by simpa [v] using hv

/-- Definition 3.3-extra-1 (3). If the Hessian coefficient in the Newton
quadratic model is self-adjoint and `s` minimizes `quadraticModel J f_v`
on `Set.univ`, then the stationary equation
`gradient J f_v + hessian J f_v s = 0` holds. -/
theorem normalEq_of_isMinOn_quadraticModel
    (J : H → ℝ) (f_v s : H)
    (hSelfAdjoint : IsSelfAdjoint (hessian J f_v))
    (hmin : IsMinOn (quadraticModel J f_v) Set.univ s) :
    gradient J f_v + hessian J f_v s = 0 :=
  (isStep_iff J f_v s).mp <|
    isStep_of_isMinOn_quadraticModel J f_v s hSelfAdjoint hmin

end Newton
