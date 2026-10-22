/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_18

open scoped Gradient lp StrongConvexSmooth

noncomputable section

local notation "ℝ∞" => ℓ²(ℕ, ℝ)
local notation "I∞" => ContinuousLinearMap.id ℝ ℝ∞
local notation "e1" => (lp.single 2 0 (1 : ℝ) : ℝ∞)

/-- Helper for Proposition 2.7: the one-step successor shift on `ℓ₂(ℕ, ℝ)`. -/
private def successor_shift_fn (x : ℝ∞) : ℕ → ℝ := fun n ↦ x (n + 1)

/-- Helper for Proposition 2.7: the successor shift preserves square summability. -/
private theorem successor_shift_mem (x : ℝ∞) :
    Memℓp (successor_shift_fn x) 2 := by
  -- The tail of a square-summable sequence is square-summable.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  exact memℓp_gen (by
    simpa [successor_shift_fn] using hx.comp_injective Nat.succ_injective)

/-- Helper for Proposition 2.7: the successor shift as an `ℓ₂(ℕ, ℝ)` vector. -/
private def successor_shift (x : ℝ∞) : ℝ∞ :=
  ⟨successor_shift_fn x, successor_shift_mem x⟩

/-- Helper for Proposition 2.7: the predecessor shift inserts a zero head. -/
private def predecessor_shift_fn (x : ℝ∞) : ℕ → ℝ
  | 0 => 0
  | n + 1 => x n

/-- Helper for Proposition 2.7: the predecessor shift preserves square summability. -/
private theorem predecessor_shift_mem (x : ℝ∞) :
    Memℓp (predecessor_shift_fn x) 2 := by
  -- Recover the shifted series from the original square-summable series.
  have hx : Summable (fun n : ℕ => ‖x n‖ ^ (2 : ℝ)) := by
    simpa using (lp.memℓp x).summable (by norm_num)
  have htail :
      Summable (fun n : ℕ => ‖predecessor_shift_fn x (n + 1)‖ ^ (2 : ℝ)) := by
    simpa [predecessor_shift_fn] using hx
  exact memℓp_gen ((summable_nat_add_iff 1).1 htail)

/-- Helper for Proposition 2.7: the predecessor shift as an `ℓ₂(ℕ, ℝ)` vector. -/
private def predecessor_shift (x : ℝ∞) : ℝ∞ :=
  ⟨predecessor_shift_fn x, predecessor_shift_mem x⟩

/-- Helper for Proposition 2.7: the successor and predecessor shifts are adjoint in the real
`ℓ₂` pairing. -/
private theorem inner_successor_shift_eq_inner_predecessor_shift (x y : ℝ∞) :
    inner ℝ (successor_shift x) y = inner ℝ x (predecessor_shift y) := by
  -- Expand the successor-shift pairing coordinatewise and match it with the predecessor tail.
  have hpred : Summable (fun n : ℕ => inner ℝ (x n) (predecessor_shift y n)) := by
    simpa using (lp.summable_inner (𝕜 := ℝ) x (predecessor_shift y))
  calc
    inner ℝ (successor_shift x) y
        = ∑' n : ℕ, inner ℝ (successor_shift x n) (y n) :=
          lp.inner_eq_tsum (𝕜 := ℝ) (successor_shift x) y
    _ = ∑' n : ℕ, inner ℝ (x (n + 1)) (y n) := by
          refine tsum_congr ?_
          intro n
          simp [successor_shift, successor_shift_fn]
    _ = inner ℝ (x 0) (predecessor_shift y 0) +
          ∑' n : ℕ, inner ℝ (x (n + 1)) (predecessor_shift y (n + 1)) := by
          simp [predecessor_shift, predecessor_shift_fn]
    _ = ∑' n : ℕ, inner ℝ (x n) (predecessor_shift y n) := by
          simpa using (hpred.sum_add_tsum_nat_add 1)
    _ = inner ℝ x (predecessor_shift y) := by
          symm
          exact lp.inner_eq_tsum (𝕜 := ℝ) x (predecessor_shift y)

/-- Helper for Proposition 2.7: the tridiagonal operator has the coordinate form `2I - S - S*`
on the underlying sequence. -/
private theorem nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts_fn (x : ℝ∞) :
    (fun n : ℕ ↦ nesterovLowerBoundTridiagonalOperator x n) =
      (2 : ℝ) • (x : ℕ → ℝ) - successor_shift_fn x - predecessor_shift_fn x := by
  -- Check the raw sequence identity at the head and at every successor coordinate.
  funext n
  cases n with
  | zero =>
      simp [successor_shift_fn, predecessor_shift_fn, sub_eq_add_neg,
        nesterovLowerBoundTridiagonalOperator_apply_zero]
  | succ n =>
      simp [successor_shift_fn, predecessor_shift_fn, sub_eq_add_neg,
        nesterovLowerBoundTridiagonalOperator_apply_succ]
      ring

/-- Helper for Proposition 2.7: the tridiagonal operator is `2I - S - S*` in terms of the local
successor and predecessor shifts. -/
private theorem nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts (x : ℝ∞) :
    nesterovLowerBoundTridiagonalOperator x =
      (2 : ℝ) • x - successor_shift x - predecessor_shift x := by
  -- Lift the already-checked coordinate identity to an equality in `ℓ₂(ℕ, ℝ)`.
  ext n
  simpa [successor_shift, predecessor_shift] using
    congrArg (fun f : ℕ → ℝ => f n)
      (nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts_fn x)

/-- Helper for Proposition 2.7: the tridiagonal lower-bound operator is self-adjoint. -/
private theorem nesterovLowerBoundTridiagonalOperator_isSelfAdjoint :
    IsSelfAdjoint nesterovLowerBoundTridiagonalOperator := by
  -- Route correction: prove symmetry from the `2I - S - S*` decomposition, then convert to
  -- self-adjointness.
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hpred :
      inner ℝ (predecessor_shift x) y = inner ℝ x (successor_shift y) := by
    calc
      inner ℝ (predecessor_shift x) y = inner ℝ y (predecessor_shift x) := by
        rw [real_inner_comm]
      _ = inner ℝ (successor_shift y) x :=
        (inner_successor_shift_eq_inner_predecessor_shift y x).symm
      _ = inner ℝ x (successor_shift y) := by
        rw [real_inner_comm]
  calc
    inner ℝ (nesterovLowerBoundTridiagonalOperator x) y
        = inner ℝ ((2 : ℝ) • x - successor_shift x - predecessor_shift x) y := by
          rw [nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts]
    _ = 2 * inner ℝ x y - inner ℝ (successor_shift x) y - inner ℝ (predecessor_shift x) y := by
          simp [inner_sub_left, inner_smul_left]
    _ = 2 * inner ℝ x y - inner ℝ x (predecessor_shift y) - inner ℝ x (successor_shift y) := by
          rw [inner_successor_shift_eq_inner_predecessor_shift, hpred]
    _ = inner ℝ x ((2 : ℝ) • y - successor_shift y - predecessor_shift y) := by
          simp [inner_sub_right, inner_smul_right]
          ring_nf
    _ = inner ℝ x (nesterovLowerBoundTridiagonalOperator y) := by
          rw [nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts]

/-- Helper for Proposition 2.7: the Riesz map identifies `innerSL ℝ z` with `z`. -/
private theorem toDual_symm_innerSL_eq (z : ℝ∞) :
    (InnerProductSpace.toDual ℝ ℝ∞).symm ((innerSL ℝ) z) = z := by
  -- Check equality against every test vector through the real inner product.
  apply ext_inner_right ℝ
  intro y
  simp [InnerProductSpace.toDual_symm_apply]

/-- Helper for Proposition 2.7: a continuous linear functional has constant gradient given by its
Riesz representative. -/
private theorem hasGradientAt_continuousLinearMap
    (ell : ℝ∞ →L[ℝ] ℝ) (x : ℝ∞) :
    HasGradientAt (fun y : ℝ∞ ↦ ell y) ((InnerProductSpace.toDual ℝ ℝ∞).symm ell) x := by
  -- Convert the gradient claim to the Fréchet-derivative statement for the linear functional.
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using (ell.hasFDerivAt : HasFDerivAt ell ell x)

/-- Helper for Proposition 2.7: subtracting a continuous linear functional shifts the gradient by
its constant Riesz representative. -/
private theorem gradient_sub_continuousLinearMap
    {f : ℝ∞ → ℝ} (hcont : ContDiff ℝ 1 f) (ell : ℝ∞ →L[ℝ] ℝ) :
    ∇ (fun x : ℝ∞ ↦ f x - ell x) =
      fun x ↦ ∇ f x - (InnerProductSpace.toDual ℝ ℝ∞).symm ell := by
  -- Build the gradient pointwise from the gradient of `f` and the constant gradient of `ell`.
  refine gradient_eq ?_
  intro x
  have hfx : HasGradientAt f (∇ f x) x := (hcont.differentiable_one x).hasGradientAt
  have hlin := hasGradientAt_continuousLinearMap ell x
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hfx.hasFDerivAt.sub hlin.hasFDerivAt).hasGradientAt

/-- Helper for Proposition 2.7: subtracting a continuous linear functional preserves the
`(μ, L)` strong-convexity and smoothness owner bounds. -/
private theorem isStrongConvexSmoothObjective_sub_continuousLinearMap
    {μ L : ℝ} {f : ℝ∞ → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (ell : ℝ∞ →L[ℝ] ℝ) :
    IsStrongConvexSmoothObjective μ L (fun x : ℝ∞ ↦ f x - ell x) := by
  -- The affine perturbation changes the gradient by a constant vector, so all gradient-difference
  -- bounds from the owner predicate are unchanged.
  rw [IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono] at hf ⊢
  rcases hf with ⟨hμ, hcont, hmono, hlip⟩
  have hgrad_sub := gradient_sub_continuousLinearMap hcont ell
  have hgrad_sub_apply (x : ℝ∞) :
      ∇ (fun z : ℝ∞ ↦ f z - ell z) x =
        ∇ f x - (InnerProductSpace.toDual ℝ ℝ∞).symm ell := by
    simpa using congrArg (fun g : ℝ∞ → ℝ∞ => g x) hgrad_sub
  refine ⟨hμ, hcont.sub ell.contDiff, ?_, ?_⟩
  · intro x y
    rw [hgrad_sub_apply x, hgrad_sub_apply y]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmono x y
  · intro x y
    rw [hgrad_sub_apply x, hgrad_sub_apply y]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlip x y

/-- Helper for Proposition 2.7: the successor-shift pairing is the textbook cross series. -/
private theorem successor_shift_inner_eq_cross_series (x : ℝ∞) :
    inner ℝ x (successor_shift x) = ∑' n : ℕ, x n * x (n + 1) := by
  -- Expand the `ℓ₂` inner product coordinatewise and identify each term with the cross term.
  calc
    inner ℝ x (successor_shift x) = ∑' n : ℕ, inner ℝ (x n) (successor_shift x n) :=
      lp.inner_eq_tsum (𝕜 := ℝ) x (successor_shift x)
    _ = ∑' n : ℕ, x n * x (n + 1) := by
          refine tsum_congr ?_
          intro n
          have hcoord :
              inner ℝ (x n) (successor_shift x n) =
                successor_shift x n * (starRingEnd ℝ) (x n) :=
            RCLike.inner_apply (x n) (successor_shift x n)
          simpa [successor_shift, successor_shift_fn, mul_comm] using hcoord

/-- Helper for Proposition 2.7: the predecessor-shift pairing is the same textbook cross
series. -/
private theorem predecessor_shift_inner_eq_cross_series (x : ℝ∞) :
    inner ℝ x (predecessor_shift x) = ∑' n : ℕ, x n * x (n + 1) := by
  -- Split off the zero head and reindex the shifted tail back to the common cross series.
  have hpred : Summable (fun n : ℕ => inner ℝ (x n) (predecessor_shift x n)) := by
    simpa using (lp.summable_inner (𝕜 := ℝ) x (predecessor_shift x))
  calc
    inner ℝ x (predecessor_shift x) = ∑' n : ℕ, inner ℝ (x n) (predecessor_shift x n) :=
      lp.inner_eq_tsum (𝕜 := ℝ) x (predecessor_shift x)
    _ = inner ℝ (x 0) (predecessor_shift x 0) +
          ∑' n : ℕ, inner ℝ (x (n + 1)) (predecessor_shift x (n + 1)) := by
          symm
          simpa using (hpred.sum_add_tsum_nat_add 1)
    _ = 0 + ∑' n : ℕ, inner ℝ (x (n + 1)) (x n) := by
          simp only [predecessor_shift, predecessor_shift_fn, inner_zero_right]
    _ = ∑' n : ℕ, x n * x (n + 1) := by
          rw [zero_add]
          refine tsum_congr ?_
          intro n
          have hcoord :
              inner ℝ (x (n + 1)) (x n) =
                x n * (starRingEnd ℝ) (x (n + 1)) :=
            RCLike.inner_apply (x (n + 1)) (x n)
          simpa [mul_comm] using hcoord

/-- Helper for Proposition 2.7: splitting the square series at the head recovers the full
`ℓ₂` square sum. -/
private theorem head_add_tail_square_series_eq (x : ℝ∞) :
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, x (n + 1) ^ (2 : ℕ) = ∑' n : ℕ, x n ^ (2 : ℕ) := by
  -- Split the square series of `x` into its first term and the shifted tail.
  have hxSq : Summable (fun n : ℕ => x n ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using (lp.memℓp x).summable (by norm_num)
  simpa using (hxSq.sum_add_tsum_nat_add 1)

/-- Helper for Proposition 2.7: the plus-chain square series is the normal form of `⟪x, (4I-A)x⟫`.
-/
private theorem plus_chain_series_eq_normal_form (x : ℝ∞) :
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, (x n + x (n + 1)) ^ (2 : ℕ) =
      2 * (∑' n : ℕ, x n ^ (2 : ℕ)) + 2 * (∑' n : ℕ, x n * x (n + 1)) := by
  -- Expand the square termwise, then replace the shifted square tail by the head-plus-tail
  -- identity.
  have hxSq : Summable (fun n : ℕ => x n ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using (lp.memℓp x).summable (by norm_num)
  have htailSq : Summable (fun n : ℕ => x (n + 1) ^ (2 : ℕ)) := by
    simpa using hxSq.comp_injective Nat.succ_injective
  have hcross : Summable (fun n : ℕ => x n * x (n + 1)) := by
    have hs : Summable (fun n : ℕ => inner ℝ (x n) (successor_shift x n)) := by
      simpa using (lp.summable_inner (𝕜 := ℝ) x (successor_shift x))
    refine hs.congr ?_
    intro n
    have hcoord :
        inner ℝ (x n) (successor_shift x n) =
          successor_shift x n * (starRingEnd ℝ) (x n) :=
      RCLike.inner_apply (x n) (successor_shift x n)
    simpa [successor_shift, successor_shift_fn, mul_comm] using hcoord
  have hscaled : Summable (fun n : ℕ => (2 : ℝ) * (x n * x (n + 1))) :=
    Summable.mul_left (2 : ℝ) hcross
  have hadd :
      Summable (fun n : ℕ => x n ^ (2 : ℕ) + (2 : ℝ) * (x n * x (n + 1))) :=
    hxSq.add hscaled
  have htail :
      ∑' n : ℕ, x (n + 1) ^ (2 : ℕ) = ∑' n : ℕ, x n ^ (2 : ℕ) - x 0 ^ (2 : ℕ) := by
    linarith [head_add_tail_square_series_eq x]
  calc
    x 0 ^ (2 : ℕ) + ∑' n : ℕ, (x n + x (n + 1)) ^ (2 : ℕ)
        = x 0 ^ (2 : ℕ) +
            ∑' n : ℕ, (x n ^ (2 : ℕ) + (2 : ℝ) * (x n * x (n + 1)) +
              x (n + 1) ^ (2 : ℕ)) := by
          congr 1
          refine tsum_congr ?_
          intro n
          ring
    _ = x 0 ^ (2 : ℕ) +
          (∑' n : ℕ, (x n ^ (2 : ℕ) + (2 : ℝ) * (x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [hadd.tsum_add htailSq]
    _ = x 0 ^ (2 : ℕ) +
          (((∑' n : ℕ, x n ^ (2 : ℕ)) + ∑' n : ℕ, (2 : ℝ) * (x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [hxSq.tsum_add hscaled]
    _ = x 0 ^ (2 : ℕ) +
          (((∑' n : ℕ, x n ^ (2 : ℕ)) + (2 : ℝ) * (∑' n : ℕ, x n * x (n + 1))) +
            ∑' n : ℕ, x (n + 1) ^ (2 : ℕ)) := by
          rw [tsum_mul_left]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) + 2 * (∑' n : ℕ, x n * x (n + 1)) := by
          rw [htail]
          ring

/-- Helper for Proposition 2.7: the quadratic form of `4I - A` is the textbook plus-chain
series. -/
private theorem four_smul_id_sub_nesterovLowerBoundTridiagonalOperator_inner_eq_series
    (x : ℝ∞) :
    inner ℝ x (((4 : ℝ) • I∞ - nesterovLowerBoundTridiagonalOperator) x) =
      x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i + x (i + 1)) ^ (2 : ℕ) := by
  -- Rewrite `4I - A` as `2I + S + S*`, then normalize to the textbook plus-chain series.
  have hself :
      inner ℝ x x = ∑' n : ℕ, x n ^ (2 : ℕ) := by
    calc
      inner ℝ x x = ∑' n : ℕ, inner ℝ (x n) (x n) := lp.inner_eq_tsum (𝕜 := ℝ) x x
      _ = ∑' n : ℕ, x n ^ (2 : ℕ) := by
            refine tsum_congr ?_
            intro n
            have hcoord :
                inner ℝ (x n) (x n) = x n * (starRingEnd ℝ) (x n) :=
              RCLike.inner_apply (x n) (x n)
            calc
              inner ℝ (x n) (x n) = x n * x n := by
                simpa using hcoord
              _ = x n ^ (2 : ℕ) := by
                ring
  calc
    inner ℝ x (((4 : ℝ) • I∞ - nesterovLowerBoundTridiagonalOperator) x)
        = inner ℝ x ((2 : ℝ) • x + successor_shift x + predecessor_shift x) := by
          change inner ℝ x ((4 : ℝ) • x - nesterovLowerBoundTridiagonalOperator x) =
            inner ℝ x ((2 : ℝ) • x + successor_shift x + predecessor_shift x)
          rw [nesterovLowerBoundTridiagonalOperator_eq_two_smul_sub_shifts]
          have hvec_fn :
              (4 : ℝ) • (x : ℕ → ℝ) +
                  -((2 : ℝ) • (x : ℕ → ℝ) + -successor_shift_fn x + -predecessor_shift_fn x) =
                (2 : ℝ) • (x : ℕ → ℝ) + successor_shift_fn x + predecessor_shift_fn x := by
            funext n
            simp [successor_shift_fn, predecessor_shift_fn]
            ring
          have hvec :
              (4 : ℝ) • x + -((2 : ℝ) • x + -successor_shift x + -predecessor_shift x) =
                (2 : ℝ) • x + successor_shift x + predecessor_shift x := by
            ext n
            simpa [successor_shift, predecessor_shift] using
              congrArg (fun f : ℕ → ℝ => f n) hvec_fn
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            congrArg (fun v : ℝ∞ => inner ℝ x v) hvec
    _ = 2 * inner ℝ x x + inner ℝ x (successor_shift x) + inner ℝ x (predecessor_shift x) := by
          simp [inner_add_right, inner_smul_right]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) +
          inner ℝ x (successor_shift x) + inner ℝ x (predecessor_shift x) := by
          rw [hself]
    _ = 2 * (∑' n : ℕ, x n ^ (2 : ℕ)) + 2 * (∑' n : ℕ, x n * x (n + 1)) := by
          rw [successor_shift_inner_eq_cross_series, predecessor_shift_inner_eq_cross_series]
          ring
    _ = x 0 ^ (2 : ℕ) + ∑' i : ℕ, (x i + x (i + 1)) ^ (2 : ℕ) :=
          (plus_chain_series_eq_normal_form x).symm

/-- Helper for Proposition 2.7: the hard-instance objective has the expected affine gradient
formula. -/
private theorem nesterovLowerBoundOperatorObjective_gradient_formula
    (μ Q_f : ℝ) :
    ∇ (nesterovLowerBoundOperatorObjective μ Q_f) =
      fun x : ℝ∞ ↦
        (((μ * (Q_f - 1) / 4) • nesterovLowerBoundTridiagonalOperator) +
            μ • I∞) x -
          (μ * (Q_f - 1) / 4) • e1 := by
  -- Route correction: differentiate the quadratic owner and the linear perturbation separately,
  -- then collapse `A + A†` to `2A` using self-adjointness of the tridiagonal operator.
  let c : ℝ := μ * (Q_f - 1) / 4
  have hquad_contDiff :
      ContDiff ℝ 1 (nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator) := by
    -- The quadratic owner is `C¹` because both the bilinear quadratic core and the norm-square
    -- regularizer are `C¹`.
    have hcont_quad :
        ContDiff ℝ 1
          (fun x : ℝ∞ ↦
            μ * (Q_f - 1) / 8 * inner ℝ x (nesterovLowerBoundTridiagonalOperator x)) := by
      simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        contDiff_const.mul (contDiff_id.inner ℝ nesterovLowerBoundTridiagonalOperator.contDiff)
    have hcont_reg : ContDiff ℝ 1 (fun x : ℝ∞ ↦ (μ / 2) * ‖x‖ ^ (2 : ℕ)) := by
      simpa [smul_eq_mul] using (contDiff_norm_sq ℝ).const_smul (μ / 2)
    convert hcont_quad.add hcont_reg using 1
    funext x
    rw [nesterovQuadraticObjective_apply]
  refine gradient_eq ?_
  intro x
  have hself := nesterovLowerBoundTridiagonalOperator_isSelfAdjoint
  have hquad :
      HasGradientAt (nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator)
        ((((μ * (Q_f - 1) / 4) • nesterovLowerBoundTridiagonalOperator) + μ • I∞) x) x := by
    -- Specialize the quadratic-owner gradient and collapse the symmetric part to `2A`.
    have hx :
        HasGradientAt
          (nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator)
          (∇ (nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator) x) x :=
      (hquad_contDiff.differentiable_one x).hasGradientAt
    let a : ℝ := μ * (Q_f - 1) / 8
    have hpair :
        a • nesterovLowerBoundTridiagonalOperator x +
            a • nesterovLowerBoundTridiagonalOperator x =
          (a + a) • nesterovLowerBoundTridiagonalOperator x := by
      rw [← add_smul]
    have hcollapse_apply :
        μ • x +
            (a • nesterovLowerBoundTridiagonalOperator x +
              a • nesterovLowerBoundTridiagonalOperator x) =
          μ • x + (μ * (Q_f - 1) / 4) • nesterovLowerBoundTridiagonalOperator x := by
      rw [hpair]
      congr 1
      simp [a]
      ring_nf
    simpa [nesterovQuadraticObjective_gradient_eq, hself.adjoint_eq, two_smul,
      add_assoc, add_left_comm, add_comm, a, hcollapse_apply] using hx
  have hlin : HasGradientAt (fun y : ℝ∞ ↦ c * inner ℝ e1 y) (c • e1) x := by
    -- The linear perturbation has the constant gradient `c e₁`.
    have hclm := hasGradientAt_continuousLinearMap ((c • innerSL ℝ e1 : ℝ∞ →L[ℝ] ℝ)) x
    simpa [c, ContinuousLinearMap.smul_apply, innerSL_apply_apply, toDual_symm_innerSL_eq] using
      hclm
  -- Combine the quadratic and linear pieces and rewrite back to the textbook objective.
  simpa [nesterovLowerBoundOperatorObjective, c, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using (hquad.hasFDerivAt.sub hlin.hasFDerivAt).hasGradientAt

/-- The hard-instance objective lies in the Hilbert-space owner class
`𝓢^{∞,1}_{μ,μ Q_f}(ℝ∞)`. -/
-- Proof sketch: the affine perturbation `x ↦ -μ (Q_f - 1) / 4 * ⟪e₁, x⟫` has constant gradient
-- and zero Hessian, so `nesterovLowerBoundOperatorObjective μ Q_f` has the same Hessian bounds as
-- the owner quadratic from `Proposition_2_6`. Apply
-- `mem_S11_iff.mp (nesterovQuadraticObjective_mem_S11 ...)` using the canonical operator-order
-- bounds `0 ≤ nesterovLowerBoundTridiagonalOperator` and
-- `nesterovLowerBoundTridiagonalOperator ≤ 4 • I∞`.
theorem nesterovLowerBoundOperatorObjective_mem_S11
    (μ Q_f : ℝ) (hμ : 0 < μ) (hQf : 1 ≤ Q_f) :
    nesterovLowerBoundOperatorObjective μ Q_f ∈ 𝓢[μ, μ * Q_f]¹¹ := by
  -- Route correction: package the two series identities as the Loewner bounds `0 ≤ A ≤ 4I`,
  -- reuse the quadratic-owner theorem from Proposition 2.6, and transport it across the affine
  -- linear perturbation.
  let c : ℝ := μ * (Q_f - 1) / 4
  let ell : ℝ∞ →L[ℝ] ℝ := c • innerSL ℝ e1
  have hA_nonneg : 0 ≤ nesterovLowerBoundTridiagonalOperator := by
    -- The chain-series formula shows `⟪Ax, x⟫ ≥ 0` for every `x`.
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff']
    refine ⟨nesterovLowerBoundTridiagonalOperator_isSelfAdjoint, ?_⟩
    intro x
    rw [real_inner_comm, nesterovLowerBoundTridiagonalOperator_inner_eq_series]
    have hhead : 0 ≤ x 0 ^ (2 : ℕ) := by positivity
    have htail : 0 ≤ ∑' i : ℕ, (x i - x (i + 1)) ^ (2 : ℕ) := by
      exact tsum_nonneg (fun i ↦ by positivity)
    linarith
  have hA_le : nesterovLowerBoundTridiagonalOperator ≤ (4 : ℝ) • I∞ := by
    -- The plus-chain formula is exactly the positivity of `4I - A`.
    rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff']
    refine ⟨?_, ?_⟩
    · have hI_self : IsSelfAdjoint ((4 : ℝ) • I∞ : ℝ∞ →L[ℝ] ℝ∞) := by
        have hI_pos : (((4 : ℝ) • I∞ : ℝ∞ →L[ℝ] ℝ∞)).IsPositive :=
          ContinuousLinearMap.isPositive_id.smul_of_nonneg (show 0 ≤ (4 : ℝ) by norm_num)
        rw [ContinuousLinearMap.isPositive_iff'] at hI_pos
        exact hI_pos.1
      simpa using hI_self.sub nesterovLowerBoundTridiagonalOperator_isSelfAdjoint
    · intro x
      rw [real_inner_comm, four_smul_id_sub_nesterovLowerBoundTridiagonalOperator_inner_eq_series]
      have hhead : 0 ≤ x 0 ^ (2 : ℕ) := by positivity
      have htail : 0 ≤ ∑' i : ℕ, (x i + x (i + 1)) ^ (2 : ℕ) := by
        exact tsum_nonneg (fun i ↦ by positivity)
      linarith
  have hquad :
      IsStrongConvexSmoothObjective μ (μ * Q_f)
        (nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator) :=
    mem_S11_iff.mp <|
      nesterovQuadraticObjective_mem_S11 (μ := μ) (Q_f := Q_f)
        (A := nesterovLowerBoundTridiagonalOperator) hμ hQf hA_nonneg hA_le
  have hobj :
      IsStrongConvexSmoothObjective μ (μ * Q_f)
        (nesterovLowerBoundOperatorObjective μ Q_f) := by
    -- Rewrite the objective as `quadratic owner - ell` and invoke the affine-transfer helper.
    have hrewrite :
        nesterovLowerBoundOperatorObjective μ Q_f =
          fun x : ℝ∞ ↦ nesterovQuadraticObjective μ Q_f nesterovLowerBoundTridiagonalOperator x -
            ell x := by
      funext x
      simp [nesterovLowerBoundOperatorObjective, ell, c]
    rw [hrewrite]
    exact isStrongConvexSmoothObjective_sub_continuousLinearMap hquad ell
  exact mem_S11_iff.mpr hobj

/-- The gradient of the operator-form lower-bound objective is the affine expression from
Proposition 2.7. -/
-- Proof sketch: differentiate the quadratic term using self-adjointness of the tridiagonal
-- operator, differentiate the norm-square term, and differentiate the linear functional
-- `x ↦ ⟪e₁, x⟫`.
theorem nesterovLowerBoundOperatorObjective_gradient_eq (μ Q_f : ℝ) (x : ℝ∞) :
    ∇ (nesterovLowerBoundOperatorObjective μ Q_f) x =
      (((μ * (Q_f - 1) / 4) • nesterovLowerBoundTridiagonalOperator) +
          μ • I∞) x -
        (μ * (Q_f - 1) / 4) • e1 := by
  -- Specialize the owner-level gradient helper at the chosen point.
  simpa using congrArg (fun g : ℝ∞ → ℝ∞ => g x)
    (nesterovLowerBoundOperatorObjective_gradient_formula μ Q_f)

/-- The vanishing of the gradient is equivalent to the stationary linear system. -/
-- Proof sketch: rewrite the gradient with
-- `nesterovLowerBoundOperatorObjective_gradient_eq`, use `hμ` and `hQf` to divide by the nonzero
-- scalar `μ (Q_f - 1) / 4`, and rearrange the resulting linear equation.
theorem nesterovLowerBoundOperatorObjective_gradient_eq_zero_iff_linear_system
    (μ Q_f : ℝ) (hμ : 0 < μ) (hQf : 1 < Q_f) (xStar : ℝ∞) :
    ∇ (nesterovLowerBoundOperatorObjective μ Q_f) xStar = 0 ↔
      (nesterovLowerBoundTridiagonalOperator +
          (4 / (Q_f - 1)) • I∞) xStar =
        e1 := by
  -- Normalize the affine stationary equation by the nonzero scalar `μ (Q_f - 1) / 4`.
  let c : ℝ := μ * (Q_f - 1) / 4
  have hc : c ≠ 0 := by
    have hQf_ne : Q_f - 1 ≠ 0 := sub_ne_zero.mpr hQf.ne'
    simp [c, hμ.ne', hQf_ne]
  have hμ_eq : c * (4 / (Q_f - 1)) = μ := by
    have hQf_ne : Q_f - 1 ≠ 0 := sub_ne_zero.mpr hQf.ne'
    calc
      c * (4 / (Q_f - 1)) = (μ * (Q_f - 1) / 4) * (4 / (Q_f - 1)) := by
        rfl
      _ = μ := by
            field_simp [hQf_ne]
  have hop :
      ((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞ : ℝ∞ →L[ℝ] ℝ∞) =
        c • (nesterovLowerBoundTridiagonalOperator + (4 / (Q_f - 1)) • I∞) := by
    -- Factor out the common scalar `c`.
    calc
      ((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞ : ℝ∞ →L[ℝ] ℝ∞)
          = ((c • nesterovLowerBoundTridiagonalOperator) +
              (c * (4 / (Q_f - 1))) • I∞) := by
                rw [hμ_eq]
      _ = c • (nesterovLowerBoundTridiagonalOperator + (4 / (Q_f - 1)) • I∞) := by
            rw [smul_add, smul_smul]
  rw [nesterovLowerBoundOperatorObjective_gradient_eq]
  constructor
  · intro hgrad
    have heq :
        (((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞) xStar) = c • e1 := by
      simpa [c] using sub_eq_zero.mp hgrad
    have hscaled :
        c • ((nesterovLowerBoundTridiagonalOperator + (4 / (Q_f - 1)) • I∞) xStar) = c • e1 := by
      simpa [hop] using heq
    have hinv := congrArg (fun v : ℝ∞ => c⁻¹ • v) hscaled
    simpa [smul_smul, hc] using hinv
  · intro hsystem
    have hscaled :
        c • ((nesterovLowerBoundTridiagonalOperator + (4 / (Q_f - 1)) • I∞) xStar) = c • e1 := by
      exact congrArg (fun v : ℝ∞ => c • v) hsystem
    have heq :
        (((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞) xStar) = c • e1 := by
      simpa [hop] using hscaled
    exact sub_eq_zero.mpr (by simpa [c] using heq)

/-- Proposition 2.7: for `μ > 0` and `1 ≤ Q_f`, a point `x*` minimizes the quadratic lower-bound
objective on `ℓ₂` exactly when its gradient vanishes. -/
-- Proof sketch: place the hard instance in the owner class
-- `𝓢[μ, μ * Q_f]¹¹` via
-- `nesterovLowerBoundOperatorObjective_mem_S11`, then specialize the generic
-- owner equivalence `IsStrongConvexSmoothObjective.isMinOn_iff_gradient_eq_zero` through
-- `mem_S11_iff`.
theorem nesterovLowerBoundOperatorObjective_isMinOn_iff_gradient_eq_zero
    (μ Q_f : ℝ) (hμ : 0 < μ) (hQf : 1 ≤ Q_f) (xStar : ℝ∞) :
    IsMinOn (nesterovLowerBoundOperatorObjective μ Q_f) Set.univ xStar ↔
      ∇ (nesterovLowerBoundOperatorObjective μ Q_f) xStar = 0 := by
  let hf :
      IsStrongConvexSmoothObjective
        μ
        (μ * Q_f)
        (nesterovLowerBoundOperatorObjective μ Q_f) :=
    mem_S11_iff.mp (nesterovLowerBoundOperatorObjective_mem_S11 μ Q_f hμ hQf)
  simpa using hf.isMinOn_iff_gradient_eq_zero xStar
