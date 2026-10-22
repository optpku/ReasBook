/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_13

noncomputable section

-- Domain sampling for this refine pass:
-- * Primary domain: terminal-step trust-region geometry for the Chapter 6 owner
--   `SteihaugCGAlgorithm`.
-- * Inspected owner/data declarations:
--   `SteihaugCGAlgorithm.step_next_eq`,
--   `SteihaugCGAlgorithm.stepZero`,
--   `SteihaugCGAlgorithm.initialStop`,
--   `SteihaugCGAlgorithm.residualStop`,
--   `SteihaugCGAlgorithm.boundaryReturnedStep`,
--   `SteihaugCGAlgorithm.negativeCurvatureReturnedStep`,
--   and `SteihaugCGAlgorithm.quadraticModel_step_succ_eq_sub`.
-- * Core/canonical owner: `SteihaugCGAlgorithm`; primitive data is already the algorithm record
--   together with its terminal-branch fields.
-- * Source-facing layer: Theorem 6.1.14 records monotonicity and terminal-step consequences of
--   that owner.
-- * Bridge/view layer: use direct disjunctions of the existing owner branch hypotheses instead of
--   exporting a parallel terminal-case wrapper.
-- * This file therefore keeps only the source-facing Theorem 6.1.14 consequences on the
--   `SteihaugCGAlgorithm` owner surface.

section

variable {n : ℕ}

namespace SteihaugCGAlgorithm

/-- The interior residual-stop terminal branch at stage `j` of Algorithm `6.1.12`. -/
abbrev residualStopAt
    (A : SteihaugCGAlgorithm n) (j : ℕ) : Prop :=
  A.continuingIteration j ∧
    ‖A.step (j + 1)‖_A.weightMatrix < A.Δ ∧
    A.residualNorm (j + 1) < A.residualThreshold

/-- The boundary-overshoot terminal branch at stage `j` of Algorithm `6.1.12`. -/
abbrev boundaryStopAt
    (A : SteihaugCGAlgorithm n) (j : ℕ) : Prop :=
  A.continuingIteration j ∧
    A.Δ ≤ ‖A.step (j + 1)‖_A.weightMatrix

/-- The negative-curvature terminal branch at stage `j` of Algorithm `6.1.12`. -/
abbrev negativeCurvatureStopAt
    (A : SteihaugCGAlgorithm n) (j : ℕ) : Prop :=
  A.activeIteration j ∧
    matrixQuadratic A.hessianApprox (A.searchDirection j) ≤ 0

/-- A non-initial terminal branch of Algorithm `6.1.12` at stage `j`. -/
abbrev terminalStopAt
    (A : SteihaugCGAlgorithm n) (j : ℕ) : Prop :=
  A.residualStopAt j ∨ A.boundaryStopAt j ∨ A.negativeCurvatureStopAt j

/-- Either the initial residual stop occurs, or a non-initial terminal branch occurs at stage
`j`. -/
abbrev initialOrTerminalStopAt
    (A : SteihaugCGAlgorithm n) (j : ℕ) : Prop :=
  A.initialResidualNorm < A.residualThreshold ∨ A.terminalStopAt j

/-- Helper for Chapter06 Theorem 6.1.14: positive curvature on a continuing iteration forces the
current search direction to be nonzero. -/
private theorem searchDirection_ne_zero_of_continuing
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j) :
    A.searchDirection j ≠ 0 := by
  -- A zero search direction would make the curvature term vanish, contradicting continuation.
  intro hZero
  have hCurvaturePos :
      0 < matrixQuadratic A.hessianApprox (A.searchDirection j) :=
    A.continuingCurvaturePos j hContinue
  have hCurvatureZero :
      matrixQuadratic A.hessianApprox (A.searchDirection j) = 0 := by
    simp [matrixQuadratic, hZero]
  linarith

/-- Helper for Chapter06 Theorem 6.1.14: at the initial continuing iterate, the residual
pairing `g₀ᵀ v₀` is strictly positive. -/
private theorem residualPairing_pos_at_zero
    (A : SteihaugCGAlgorithm n)
    (hContinue : A.continuingIteration 0) :
    0 < A.residualPairing 0 := by
  -- Step `0` has `d₀ = -v₀`, so positive curvature forces `v₀ ≠ 0`.
  have hDirectionNe : A.searchDirection 0 ≠ 0 :=
    searchDirection_ne_zero_of_continuing A hContinue
  have hPreconditionedNe : (A.preconditionedGradient 0).ofLp ≠ 0 := by
    intro hZero
    have hPreconditionedZero : A.preconditionedGradient 0 = 0 := by
      simpa using hZero
    apply hDirectionNe
    rw [A.searchDirectionZero, hPreconditionedZero]
    simp
  have hBridge :
      A.weightMatrix.mulVec (A.preconditionedGradient 0).ofLp = (A.gradient 0).ofLp := by
    -- The owner stores `v₀ = W⁻¹ g₀`, so one multiplication by `W` recovers `g₀`.
    rw [A.preconditionedGradientZero, A.gradientZero]
    simp [Matrix.mulVec_mulVec, A.weightMatrixMulInv, Matrix.one_mulVec]
  have hPositive :
      0 <
        dotProduct (A.preconditionedGradient 0).ofLp
          (A.weightMatrix.mulVec (A.preconditionedGradient 0).ofLp) :=
    A.weightMatrixPosDef.dotProduct_mulVec_pos hPreconditionedNe
  -- Rewrite the positive-definite form back into the residual pairing.
  calc
    0 <
        dotProduct (A.preconditionedGradient 0).ofLp
          (A.weightMatrix.mulVec (A.preconditionedGradient 0).ofLp) := hPositive
    _ = A.residualPairing 0 := by
        rw [hBridge]
        simp [SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt,
          steihaugResidualPairing, dotProduct_comm]

/-- Helper for Chapter06 Theorem 6.1.14: every continuing iterate carries a strictly positive
residual pairing `g_jᵀ v_j`. -/
private theorem residualPairing_pos_of_continuing
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j) :
    0 < A.residualPairing j := by
  cases j with
  | zero =>
      -- The first continuing iterate is handled directly from `d₀ = -v₀`.
      exact residualPairing_pos_at_zero A hContinue
  | succ j =>
      -- For later iterates, the residual lower bound at the previous step gives positivity.
      have hContinueZero : A.continuingIteration 0 :=
        hHistory 0 (Nat.succ_pos j)
      have hResidualZeroPos : 0 < A.residualPairing 0 :=
        residualPairing_pos_at_zero A hContinueZero
      have hInitialNormPos : 0 < A.initialResidualNorm := by
        have hInitialSqrtPos : 0 < Real.sqrt (A.residualPairing 0) :=
          Real.sqrt_pos.2 hResidualZeroPos
        simpa [SteihaugCGAlgorithm.initialResidualNorm, steihaugInitialResidualNorm,
          SteihaugCGAlgorithm.residualNorm, steihaugResidualNormAt, steihaugResidualNorm,
          SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt] using hInitialSqrtPos
      have hThresholdPos : 0 < A.residualThreshold := by
        -- The trust-region tolerance is `ε > 0` times the strictly positive initial norm.
        simpa [SteihaugCGAlgorithm.residualThreshold, steihaugResidualThreshold] using
          mul_pos A.epsilonPos hInitialNormPos
      have hResidualNormPos : 0 < A.residualNorm (j + 1) :=
        lt_of_lt_of_le hThresholdPos (hResidual j (Nat.lt_succ_self j))
      have hSqrtPos : 0 < Real.sqrt (A.residualPairing (j + 1)) := by
        simpa [SteihaugCGAlgorithm.residualNorm, steihaugResidualNormAt, steihaugResidualNorm,
          SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt]
          using hResidualNormPos
      simpa using (Real.sqrt_pos.1 hSqrtPos)

/-- Helper for Chapter06 Theorem 6.1.14: the Step `2` coefficient `α_j` is strictly positive on
every continuing iteration. -/
private theorem alpha_pos_of_continuing
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j) :
    0 < A.α j := by
  -- The owner formula for `α_j` has a positive numerator and denominator.
  rw [A.alphaUpdate j hContinue]
  exact div_pos
    (residualPairing_pos_of_continuing A hHistory hInterior hResidual hContinue)
    (A.continuingCurvaturePos j hContinue)

/-- Helper for Chapter06 Theorem 6.1.14: every iterate reached through a continuing history is
the sum of the previous Steihaug-CG step updates. -/
private theorem step_eq_sum_searchDirections
    (A : SteihaugCGAlgorithm n) (j : ℕ)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k) :
    A.step j = Finset.sum (Finset.range j) (fun k ↦ A.α k • A.searchDirection k) := by
  induction j with
  | zero =>
      -- The initial iterate is the empty sum because `s₀ = 0`.
      simp [A.stepZero]
  | succ j ih =>
      have hContinue : A.continuingIteration j := hHistory j (Nat.lt_succ_self j)
      have ih' := ih (fun k hk => hHistory k (Nat.lt_trans hk (Nat.lt_succ_self j)))
      -- Append the current `α_j d_j` update to the previous partial sum.
      calc
        A.step (j + 1) = A.step j + A.α j • A.searchDirection j := by
          rw [A.step_next_eq hContinue]
        _ = Finset.sum (Finset.range j) (fun k ↦ A.α k • A.searchDirection k) +
              A.α j • A.searchDirection j := by
          rw [ih']
        _ = Finset.sum (Finset.range (j + 1)) (fun k ↦ A.α k • A.searchDirection k) := by
          rw [Finset.sum_range_succ]

/-- Helper for Chapter06 Theorem 6.1.14: the mixed weighted pairing `s_jᵀ W d_j` is
nonnegative along the continuing Steihaug-CG history. -/
private theorem step_searchDirection_weightMatrix_nonneg
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j) :
    0 ≤ dotProduct (A.step j) (A.weightMatrix.mulVec (A.searchDirection j)) := by
  cases j with
  | zero =>
      -- The initial step is zero, so the mixed pairing vanishes.
      simp [A.stepZero]
  | succ j =>
      have hResidualPos :
          0 < A.residualPairing (j + 1) :=
        residualPairing_pos_of_continuing A hHistory hInterior hResidual hContinue
      have hStepSumOfLp :
          (A.step (j + 1)).ofLp =
            Finset.sum (Finset.range (j + 1))
              (fun k ↦ (A.α k • A.searchDirection k).ofLp) := by
        simpa using congrArg WithLp.ofLp
          (step_eq_sum_searchDirections A (j + 1) hHistory)
      change
        0 ≤
          (A.step (j + 1)).ofLp ⬝ᵥ
            Matrix.mulVec A.weightMatrix (A.searchDirection (j + 1)).ofLp
      rw [hStepSumOfLp, sum_dotProduct]
      -- Expand `s_(j+1)` as a sum of previous directions and prove each term is nonnegative.
      refine Finset.sum_nonneg ?_
      intro k hk
      have hklt : k < j + 1 := Finset.mem_range.mp hk
      have hContinueK : A.continuingIteration k := hHistory k hklt
      have hHistoryK : ∀ t : ℕ, t < k → A.continuingIteration t := fun t ht =>
        hHistory t (Nat.lt_trans ht hklt)
      have hInteriorK : ∀ t : ℕ, t < k → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ := fun t ht =>
        hInterior t (Nat.lt_trans ht hklt)
      have hResidualK : ∀ t : ℕ, t < k → A.residualThreshold ≤ A.residualNorm (t + 1) := fun t ht =>
        hResidual t (Nat.lt_trans ht hklt)
      have hAlphaPosK : 0 < A.α k :=
        alpha_pos_of_continuing A hHistoryK hInteriorK hResidualK hContinueK
      have hResidualPosK : 0 < A.residualPairing k :=
        residualPairing_pos_of_continuing A hHistoryK hInteriorK hResidualK hContinueK
      have hSelfPos :
          0 <
            dotProduct (A.searchDirection k).ofLp
              (A.weightMatrix.mulVec (A.searchDirection k).ofLp) :=
        A.weightMatrixPosDef.dotProduct_mulVec_pos
          (by simpa using searchDirection_ne_zero_of_continuing A hContinueK)
      have hRatio :
          dotProduct (A.searchDirection k) (A.weightMatrix.mulVec (A.searchDirection (j + 1))) =
            (A.residualPairing (j + 1) / A.residualPairing k) *
              dotProduct (A.searchDirection k) (A.weightMatrix.mulVec (A.searchDirection k)) :=
        A.searchDirection_weightMatrix_eq_ratio hSymm (Nat.le_of_lt hklt) hHistory hInterior
          hResidual (ne_of_gt (A.continuingCurvaturePos k hContinueK))
      have hTermEq :
          (A.α k • A.searchDirection k).ofLp ⬝ᵥ
              Matrix.mulVec A.weightMatrix (A.searchDirection (j + 1)).ofLp =
            A.α k *
              ((A.searchDirection k).ofLp ⬝ᵥ
                Matrix.mulVec A.weightMatrix (A.searchDirection (j + 1)).ofLp) := by
        simp [smul_dotProduct, smul_eq_mul]
      -- Each summand is `α_k` times a positive ratio times a positive self-pairing.
      rw [hTermEq, hRatio]
      exact mul_nonneg hAlphaPosK.le <|
        mul_nonneg (div_pos hResidualPos hResidualPosK).le hSelfPos.le

/-- First monotonicity consequence for Chapter06 Theorem 6.1.14: along a genuine Steihaug-CG
history that continues through all
earlier indices needed to reach `j`, stays inside the trust region on those earlier steps, and
does not trigger the residual stopping test there, the quadratic model strictly decreases at the
next continuing iterate:
`q(s_(j + 1)) < q(s_j)`. -/
theorem quadraticModel_step_succ_lt
    (A : SteihaugCGAlgorithm n) (f : ℝ) {j : ℕ}
    (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j) :
    A.quadraticModel f (A.step (j + 1)) < A.quadraticModel f (A.step j) := by
  have hStepEq :=
    A.quadraticModel_step_succ_eq_sub f j hSymm hHistory hInterior hResidual hContinue
  have hResidualPos :
      0 < A.residualPairing j :=
    residualPairing_pos_of_continuing A hHistory hInterior hResidual hContinue
  have hCurvaturePos :
      0 < matrixQuadratic A.hessianApprox (A.searchDirection j) :=
    A.continuingCurvaturePos j hContinue
  have hDecrementPos :
      0 <
        (1 / 2 : ℝ) * (A.residualPairing j) ^ (2 : ℕ) /
          matrixQuadratic A.hessianApprox (A.searchDirection j) := by
    -- The imported decrement formula is strict because both the residual pairing and curvature
    -- denominator are strictly positive.
    exact div_pos (mul_pos (by norm_num) (pow_pos hResidualPos 2)) hCurvaturePos
  -- Convert the exact decrement formula into the strict inequality.
  calc
    A.quadraticModel f (A.step (j + 1))
        = A.quadraticModel f (A.step j) -
            (1 / 2 : ℝ) * (A.residualPairing j) ^ (2 : ℕ) /
              matrixQuadratic A.hessianApprox (A.searchDirection j) := hStepEq
    _ < A.quadraticModel f (A.step j) := sub_lt_self _ hDecrementPos

/-- The initial PCG iterate is the zero step, so `‖s₀‖_W = 0`. -/
@[simp] theorem weightedNorm_step_zero
    (A : SteihaugCGAlgorithm n) :
    ‖A.step 0‖_A.weightMatrix = 0 := by
  -- The owner stores `s₀ = 0`, so the weighted norm is the square root of zero.
  simp [steihaugWeightedNorm, matrixQuadratic, A.stepZero]

/-- Helper for Chapter06 Theorem 6.1.14: the iterate reached after a continuing history remains
strictly inside the trust-region radius recorded by that history. -/
private theorem step_lt_radius_of_history
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ) :
    ‖A.step j‖_A.weightMatrix < A.Δ := by
  cases j with
  | zero =>
      -- The initial step has zero weighted norm, and the trust-region radius is positive.
      rw [A.weightedNorm_step_zero]
      exact A.radiusPos
  | succ j =>
      -- Later iterates use the stored interior history at the predecessor.
      exact hInterior j (Nat.lt_succ_self j)

/-- Second monotonicity consequence for Chapter06 Theorem 6.1.14: along a genuine Steihaug-CG
history that continues through all
earlier indices needed to reach `j`, stays inside the trust region on those earlier steps, and
does not trigger the residual stopping test there, the weighted norms of the iterates are
strictly increasing:
`‖s_j‖_W < ‖s_(j + 1)‖_W`. -/
theorem weightedNorm_step_succ_lt
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j) :
    ‖A.step j‖_A.weightMatrix < ‖A.step (j + 1)‖_A.weightMatrix := by
  have hAlphaPos : 0 < A.α j :=
    alpha_pos_of_continuing A hHistory hInterior hResidual hContinue
  have hCrossNonneg :
      0 ≤ dotProduct (A.step j) (A.weightMatrix.mulVec (A.searchDirection j)) :=
    step_searchDirection_weightMatrix_nonneg A hSymm hHistory hInterior hResidual hContinue
  have hSelfPos :
      0 < dotProduct (A.searchDirection j).ofLp
        (A.weightMatrix.mulVec (A.searchDirection j).ofLp) :=
    A.weightMatrixPosDef.dotProduct_mulVec_pos
      (by simpa using searchDirection_ne_zero_of_continuing A hContinue)
  have hWeightSymm : A.weightMatrix.IsSymm := by
    simpa using A.weightMatrixPosDef.1
  have hCrossEq :
      dotProduct (A.searchDirection j) (A.weightMatrix.mulVec (A.step j)) =
        dotProduct (A.step j) (A.weightMatrix.mulVec (A.searchDirection j)) := by
    -- Symmetry of `W` turns the two mixed quadratic terms into the same pairing.
    simpa [hWeightSymm.eq, dotProduct_comm] using
      (Matrix.dotProduct_transpose_mulVec (A := A.weightMatrix)
        (x := A.step j) (y := A.searchDirection j)).symm
  have hExpand :
      matrixQuadratic A.weightMatrix (A.step (j + 1)) =
        matrixQuadratic A.weightMatrix (A.step j) +
          2 * A.α j * dotProduct (A.step j) (A.weightMatrix.mulVec (A.searchDirection j)) +
          (A.α j) ^ (2 : ℕ) *
            dotProduct (A.searchDirection j) (A.weightMatrix.mulVec (A.searchDirection j)) := by
    -- Expand the weighted norm square of `s_(j+1) = s_j + α_j d_j`.
    rw [A.step_next_eq hContinue]
    simp [matrixQuadratic, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, hCrossEq]
    ring
  have hQuadraticNonneg :
      0 ≤ matrixQuadratic A.weightMatrix (A.step j) := by
    simpa [matrixQuadratic] using
      A.weightMatrixPosDef.posSemidef.dotProduct_mulVec_nonneg (A.step j)
  have hQuadraticStrict :
      matrixQuadratic A.weightMatrix (A.step j) <
        matrixQuadratic A.weightMatrix (A.step (j + 1)) := by
    have hCrossTermNonneg :
        0 ≤
          2 * A.α j * dotProduct (A.step j) (A.weightMatrix.mulVec (A.searchDirection j)) := by
      have hTwoAlphaNonneg : 0 ≤ 2 * A.α j := by
        nlinarith
      exact mul_nonneg hTwoAlphaNonneg hCrossNonneg
    have hSelfTermPos :
        0 <
          (A.α j) ^ (2 : ℕ) *
            dotProduct (A.searchDirection j) (A.weightMatrix.mulVec (A.searchDirection j)) := by
      exact mul_pos (pow_pos hAlphaPos 2) hSelfPos
    -- The self term is strictly positive, so the new weighted quadratic form strictly grows.
    rw [hExpand]
    linarith
  -- Convert strict growth of the weighted quadratic form into strict growth of weighted norms.
  simpa [SteihaugCGAlgorithm.weightedNorm, steihaugWeightedNorm] using
    Real.sqrt_lt_sqrt hQuadraticNonneg hQuadraticStrict

/-- If all earlier indices needed to reach `j` are genuine Steihaug-CG iterations that stay
inside the trust region and do not trigger the residual stopping test, and iteration `j` is a
continuing Steihaug-CG step that stays inside the trust region and triggers the residual stopping
test at `s_(j + 1)`, then `s_j` has strictly smaller weighted norm than the returned step, and
the returned step remains in the weighted trust region. -/
theorem step_lt_returned_and_le_radius_of_residualStop
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInteriorHistory : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidualHistory : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j)
    (hInterior : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ)
    (hResidualStop : A.residualNorm (j + 1) < A.residualThreshold) :
    ‖A.step j‖_A.weightMatrix < ‖A.returnedStep‖_A.weightMatrix ∧
      ‖A.returnedStep‖_A.weightMatrix ≤ A.Δ := by
  -- The residual-stop branch returns exactly the interior iterate `s_(j+1)`.
  rw [A.residualStop j hContinue hInterior hResidualStop]
  refine ⟨?_, le_of_lt hInterior⟩
  exact A.weightedNorm_step_succ_lt hSymm hHistory hInteriorHistory hResidualHistory hContinue

/-- If all earlier indices `k < j` are genuine continuing Steihaug-CG steps that stay inside the
trust region and do not trigger the residual stopping test, and iteration `j` is a continuing
Steihaug-CG step whose trial step reaches or overshoots the trust-region boundary, then `s_j`
has strictly smaller weighted norm than the returned boundary step, and the returned step lies
exactly on the boundary of the weighted trust region. -/
theorem step_lt_returned_and_eq_radius_of_boundary
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (_hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration j)
    (hOvershoot : A.Δ ≤ ‖A.step (j + 1)‖_A.weightMatrix) :
    ‖A.step j‖_A.weightMatrix < ‖A.returnedStep‖_A.weightMatrix ∧
      ‖A.returnedStep‖_A.weightMatrix = A.Δ := by
  have hStepLtRadius : ‖A.step j‖_A.weightMatrix < A.Δ :=
    step_lt_radius_of_history A hHistory hInterior
  have hReturnedRadius :
      ‖A.returnedStep‖_A.weightMatrix = A.Δ := by
    -- The boundary branch replaces the overshoot by the unique boundary point on the same ray.
    rw [A.boundaryReturnedStep j hContinue hOvershoot]
    exact A.boundaryOnSphere j hContinue hOvershoot
  exact ⟨by simpa [hReturnedRadius] using hStepLtRadius, hReturnedRadius⟩

/-- If all earlier indices `k < j` are genuine continuing Steihaug-CG steps that stay inside the
trust region and do not trigger the residual stopping test, and the Steihaug-CG run reaches
active iteration `j` with nonpositive curvature along the search direction, then `s_j` has
strictly smaller weighted norm than the returned negative-curvature boundary step, and the
returned step lies exactly on the weighted trust-region boundary. -/
theorem step_lt_returned_and_eq_radius_of_negativeCurvature
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (_hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hActive : A.activeIteration j)
    (hNonpositiveCurvature :
      matrixQuadratic A.hessianApprox (A.searchDirection j) ≤ 0) :
    ‖A.step j‖_A.weightMatrix < ‖A.returnedStep‖_A.weightMatrix ∧
      ‖A.returnedStep‖_A.weightMatrix = A.Δ := by
  have hStepLtRadius : ‖A.step j‖_A.weightMatrix < A.Δ :=
    step_lt_radius_of_history A hHistory hInterior
  have hReturnedRadius :
      ‖A.returnedStep‖_A.weightMatrix = A.Δ := by
    -- The negative-curvature exit also returns the boundary point on the current ray.
    rw [A.negativeCurvatureReturnedStep j hActive hNonpositiveCurvature]
    exact A.negativeCurvatureBoundary j hActive hNonpositiveCurvature
  exact ⟨by simpa [hReturnedRadius] using hStepLtRadius, hReturnedRadius⟩

/-- Returned-step comparison for Chapter06 Theorem 6.1.14: if all earlier indices `k < j` are
genuine continuing
Steihaug-CG iterations that stay inside the trust region and do not trigger the residual stopping
test, and one of the three non-initial terminal branches of Algorithm `6.1.12` occurs at stage
`j`, namely the interior residual-stop branch, the boundary overshoot branch after a continuing
iteration, or the negative-curvature boundary branch at an active iteration, then the current
iterate has strictly smaller weighted norm than the returned step:
`‖s_j‖_W < ‖s‖_W`. -/
theorem weightedNorm_step_lt_returnedStep
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hTerminal : A.terminalStopAt j) :
    ‖A.step j‖_A.weightMatrix < ‖A.returnedStep‖_A.weightMatrix := by
  rcases hTerminal with hResidualStop | hBoundaryStop | hNegativeCurvature
  · rcases hResidualStop with ⟨hContinue, hInteriorStep, hResidualStop⟩
    exact (A.step_lt_returned_and_le_radius_of_residualStop hSymm hHistory hInterior hResidual
      hContinue hInteriorStep hResidualStop).1
  · rcases hBoundaryStop with ⟨hContinue, hOvershoot⟩
    exact (A.step_lt_returned_and_eq_radius_of_boundary hHistory hInterior hResidual hContinue
      hOvershoot).1
  · rcases hNegativeCurvature with ⟨hActive, hNonpositiveCurvature⟩
    exact (A.step_lt_returned_and_eq_radius_of_negativeCurvature hHistory hInterior hResidual
      hActive hNonpositiveCurvature).1

/-- If the Steihaug-CG algorithm terminates immediately by the initial residual test, then the
returned step is the zero step and therefore lies in the weighted trust region. -/
theorem returnedStep_le_radius_of_initialStop
    (A : SteihaugCGAlgorithm n)
    (hInitialStop : A.initialResidualNorm < A.residualThreshold) :
    ‖A.returnedStep‖_A.weightMatrix ≤ A.Δ := by
  -- Immediate termination returns the initial step `s₀ = 0`.
  rw [A.initialStop hInitialStop, A.weightedNorm_step_zero]
  exact le_of_lt A.radiusPos

/-- Chapter06 Theorem 6.1.14 (4): whenever the Steihaug-CG algorithm returns either from the
initial residual stopping test or from one of the three terminal branches at stage `j`, the
returned step remains feasible for the weighted trust region:
`‖s‖_W ≤ Δ`. -/
theorem returnedStep_le_radius
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hTerminal : A.initialOrTerminalStopAt j) :
    ‖A.returnedStep‖_A.weightMatrix ≤ A.Δ := by
  rcases hTerminal with hInitialStop | hTerminalStop
  · exact A.returnedStep_le_radius_of_initialStop hInitialStop
  · rcases hTerminalStop with hResidualStop | hBoundaryStop | hNegativeCurvature
    · rcases hResidualStop with ⟨hContinue, hInterior, hResidualStop⟩
      rw [A.residualStop j hContinue hInterior hResidualStop]
      exact le_of_lt hInterior
    · rcases hBoundaryStop with ⟨hContinue, hOvershoot⟩
      rw [A.boundaryReturnedStep j hContinue hOvershoot]
      simp [A.boundaryOnSphere j hContinue hOvershoot]
    · rcases hNegativeCurvature with ⟨hActive, hNonpositiveCurvature⟩
      rw [A.negativeCurvatureReturnedStep j hActive hNonpositiveCurvature]
      simp [A.negativeCurvatureBoundary j hActive hNonpositiveCurvature]

end SteihaugCGAlgorithm

end
