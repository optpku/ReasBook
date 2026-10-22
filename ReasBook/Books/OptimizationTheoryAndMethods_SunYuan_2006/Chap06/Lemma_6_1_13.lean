/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_12

noncomputable section

section

variable {n : ℕ}

namespace SteihaugCGAlgorithm

/-- Helper for Chapter06 Lemma 6.1.13: the step update in coordinate form. -/
private lemma step_next_eq_ofLp
    (A : SteihaugCGAlgorithm n) {j : ℕ} (hContinue : A.continuingIteration j) :
    (A.step (j + 1)).ofLp = (A.step j).ofLp + A.α j • (A.searchDirection j).ofLp := by
  -- Pass to coordinate form once so later `mulVec` calculations stay in one spelling world.
  simpa using congrArg WithLp.ofLp (A.step_next_eq hContinue)

/-- Helper for Chapter06 Lemma 6.1.13: the gradient update in coordinate form. -/
private lemma gradient_next_eq_ofLp
    (A : SteihaugCGAlgorithm n) {j : ℕ}
    (hContinue : A.continuingIteration j)
    (hInterior : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ) :
    (A.gradient (j + 1)).ofLp = (A.gradient j).ofLp +
      A.α j • A.hessianApprox.mulVec (A.searchDirection j).ofLp := by
  -- This is the owner recurrence from Step 3, rewritten on `ofLp` coordinates.
  simpa using A.gradient_next_eq hContinue hInterior

/-- Helper for Chapter06 Lemma 6.1.13: along the admitted history, the gradient equals
`g₀ + B s_j`. -/
private lemma gradient_eq_initialGradient_add_hessian_mulVec_step
    (A : SteihaugCGAlgorithm n) (j : ℕ)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ) :
    (A.gradient j).ofLp = A.initialGradient.ofLp + A.hessianApprox.mulVec (A.step j).ofLp := by
  induction j with
  | zero =>
      -- At the initial iterate, both `s₀` and `g₀` are part of the owner data.
      simp [A.gradientZero, A.stepZero]
  | succ j ih =>
      have hContinue : A.continuingIteration j := hHistory j (Nat.lt_succ_self j)
      have hInt : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ := hInterior j (Nat.lt_succ_self j)
      have ih' := ih
        (fun k hk => hHistory k (Nat.lt_trans hk (Nat.lt_succ_self j)))
        (fun k hk => hInterior k (Nat.lt_trans hk (Nat.lt_succ_self j)))
      -- Advance both `g_j` and `s_j` by their owner recurrences and reassemble the same shape.
      calc
        (A.gradient (j + 1)).ofLp
            = (A.gradient j).ofLp + A.α j • A.hessianApprox.mulVec (A.searchDirection j).ofLp := by
                simpa using A.gradient_next_eq_ofLp hContinue hInt
        _ = A.initialGradient.ofLp + A.hessianApprox.mulVec (A.step j).ofLp +
              A.α j • A.hessianApprox.mulVec (A.searchDirection j).ofLp := by
              rw [ih']
        _ = A.initialGradient.ofLp +
              (A.hessianApprox.mulVec (A.step j).ofLp + A.α j • A.hessianApprox.mulVec (A.searchDirection j).ofLp) := by
              abel
        _ = A.initialGradient.ofLp + A.hessianApprox.mulVec ((A.step j).ofLp + A.α j • (A.searchDirection j).ofLp) := by
              rw [Matrix.mulVec_add, Matrix.mulVec_smul]
        _ = A.initialGradient.ofLp + A.hessianApprox.mulVec (A.step (j + 1)).ofLp := by
              rw [A.step_next_eq_ofLp hContinue]

/-- Helper for Chapter06 Lemma 6.1.13: each current search direction satisfies
`g_jᵀ d_j = -g_jᵀ v_j`. -/
private lemma gradient_searchDirection_eq_neg_residualPairing_self
    (A : SteihaugCGAlgorithm n) (j : ℕ)
    (hHistory : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1)) :
    (A.gradient j).ofLp ⬝ᵥ (A.searchDirection j).ofLp = -A.residualPairing j := by
  induction j with
  | zero =>
      -- The initial direction is exactly `-v₀`.
      rw [A.searchDirectionZero]
      simp [SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt, steihaugResidualPairing]
  | succ j ih =>
      have hContinue : A.continuingIteration j := hHistory j (Nat.lt_succ_self j)
      have hInt : ‖A.step (j + 1)‖_A.weightMatrix < A.Δ := hInterior j (Nat.lt_succ_self j)
      have hRes : A.residualThreshold ≤ A.residualNorm (j + 1) := hResidual j (Nat.lt_succ_self j)
      have ih' := ih
        (fun k hk => hHistory k (Nat.lt_trans hk (Nat.lt_succ_self j)))
        (fun k hk => hInterior k (Nat.lt_trans hk (Nat.lt_succ_self j)))
        (fun k hk => hResidual k (Nat.lt_trans hk (Nat.lt_succ_self j)))
      have hCurvPos : 0 < matrixQuadratic A.hessianApprox (A.searchDirection j) :=
        A.continuingCurvaturePos j hContinue
      have hAlpha : A.α j = A.residualPairing j / matrixQuadratic A.hessianApprox (A.searchDirection j) :=
        A.alphaUpdate j hContinue
      have hOrth : (A.gradient (j + 1)).ofLp ⬝ᵥ (A.searchDirection j).ofLp = 0 := by
        -- The Step 3 update plus the `α_j` formula kills the old search direction.
        calc
          (A.gradient (j + 1)).ofLp ⬝ᵥ (A.searchDirection j).ofLp
              = ((A.gradient j).ofLp + A.α j • A.hessianApprox.mulVec (A.searchDirection j).ofLp) ⬝ᵥ
                  (A.searchDirection j).ofLp := by
                    rw [A.gradient_next_eq_ofLp hContinue hInt]
          _ = (A.gradient j).ofLp ⬝ᵥ (A.searchDirection j).ofLp +
                A.α j * matrixQuadratic A.hessianApprox (A.searchDirection j) := by
                rw [add_dotProduct, smul_dotProduct]
                simp [matrixQuadratic, dotProduct_comm, smul_eq_mul]
          _ = -A.residualPairing j +
                (A.residualPairing j / matrixQuadratic A.hessianApprox (A.searchDirection j)) *
                  matrixQuadratic A.hessianApprox (A.searchDirection j) := by
                rw [ih', hAlpha]
          _ = 0 := by
                field_simp [ne_of_gt hCurvPos]
                ring
      -- Then the new search-direction recurrence leaves only the `-g_(j+1)ᵀ v_(j+1)` term.
      calc
        (A.gradient (j + 1)).ofLp ⬝ᵥ (A.searchDirection (j + 1)).ofLp
            = (A.gradient (j + 1)).ofLp ⬝ᵥ
                (-(A.preconditionedGradient (j + 1)).ofLp + A.β j • (A.searchDirection j).ofLp) := by
                  rw [A.searchDirection_next_eq hContinue hInt hRes]
                  simp
        _ = -(A.gradient (j + 1)).ofLp ⬝ᵥ (A.preconditionedGradient (j + 1)).ofLp +
              A.β j * ((A.gradient (j + 1)).ofLp ⬝ᵥ (A.searchDirection j).ofLp) := by
              rw [dotProduct_add, dotProduct_smul, dotProduct_neg]
              simp [smul_eq_mul]
        _ = -A.residualPairing (j + 1) := by
              simp [SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt,
                steihaugResidualPairing, hOrth]

/-- Helper for Chapter06 Lemma 6.1.13: whenever the preconditioned gradient at index `k`
is available, multiplying it by `W` recovers the gradient `g_k`. -/
private lemma weightMatrix_mulVec_preconditionedGradient_eq_gradient
    (A : SteihaugCGAlgorithm n) (k : ℕ)
    (hContinue : ∀ t : ℕ, t < k → A.continuingIteration t)
    (hInterior : ∀ t : ℕ, t < k → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ) :
    A.weightMatrix.mulVec (A.preconditionedGradient k).ofLp = (A.gradient k).ofLp := by
  cases k with
  | zero =>
      -- At the initial iterate, `v₀ = W⁻¹ g₀`, so one multiplication by `W` recovers `g₀`.
      rw [A.preconditionedGradientZero]
      simp [Matrix.mulVec_mulVec, A.weightMatrixMulInv, Matrix.one_mulVec]
  | succ k =>
      have hContinueK : A.continuingIteration k := hContinue k (Nat.lt_succ_self k)
      have hInteriorK : ‖A.step (k + 1)‖_A.weightMatrix < A.Δ :=
        hInterior k (Nat.lt_succ_self k)
      -- Step `4` stores `v_(k+1) = W⁻¹ g_(k+1)`, so the same recovery works at the next index.
      rw [A.preconditionedGradient_next_eq hContinueK hInteriorK]
      simp [Matrix.mulVec_mulVec, A.weightMatrixMulInv, Matrix.one_mulVec]

/-- Helper for Chapter06 Lemma 6.1.13: symmetry of the positive definite weight matrix swaps the
mixed pairings `g_iᵀ v_k` and `g_kᵀ v_i`. -/
private lemma gradient_preconditionedGradient_swap
    (A : SteihaugCGAlgorithm n) {i k : ℕ}
    (hBridgeI :
      A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp = (A.gradient i).ofLp)
    (hBridgeK :
      A.weightMatrix.mulVec (A.preconditionedGradient k).ofLp = (A.gradient k).ofLp) :
    (A.gradient i).ofLp ⬝ᵥ (A.preconditionedGradient k).ofLp =
      (A.gradient k).ofLp ⬝ᵥ (A.preconditionedGradient i).ofLp := by
  have hWsymm : A.weightMatrix.IsSymm := by
    simpa using A.weightMatrixPosDef.1
  -- Move both mixed pairings to the symmetric `W`-bilinear form and compare them there.
  calc
    (A.gradient i).ofLp ⬝ᵥ (A.preconditionedGradient k).ofLp
        = A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp ⬝ᵥ
            (A.preconditionedGradient k).ofLp := by
              rw [hBridgeI]
    _ = A.weightMatrix.mulVec (A.preconditionedGradient k).ofLp ⬝ᵥ
          (A.preconditionedGradient i).ofLp := by
            simpa [hWsymm.eq, dotProduct_comm] using
              (Matrix.dotProduct_transpose_mulVec (A := A.weightMatrix)
                (x := (A.preconditionedGradient k).ofLp)
                (y := (A.preconditionedGradient i).ofLp))
    _ = (A.gradient k).ofLp ⬝ᵥ (A.preconditionedGradient i).ofLp := by
          rw [hBridgeK]

/-- Helper for Chapter06 Lemma 6.1.13: at a fixed right index `k`, the Steihaug-CG history
packages the cross-index pairing, residual orthogonality, old-direction orthogonality, and
`B`-conjugacy relations used in `(6.1.73)` and `(6.1.74)`. -/
private lemma prefixPairingInvariants
    (A : SteihaugCGAlgorithm n) (k : ℕ) (hSymm : A.hessianApprox.IsSymm)
    (hContinue : ∀ t : ℕ, t < k → A.continuingIteration t)
    (hInterior : ∀ t : ℕ, t < k → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ t : ℕ, t < k → A.residualThreshold ≤ A.residualNorm (t + 1)) :
    (∀ i ≤ k, (A.gradient i).ofLp ⬝ᵥ (A.searchDirection k).ofLp = -A.residualPairing k) ∧
      (∀ i < k, (A.gradient i).ofLp ⬝ᵥ (A.preconditionedGradient k).ofLp = 0) ∧
      (∀ i < k, (A.gradient k).ofLp ⬝ᵥ (A.searchDirection i).ofLp = 0) ∧
      (∀ i < k,
        (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.searchDirection k).ofLp = 0) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro i hi
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        -- The diagonal identity is exactly the already-proved base case.
        simpa using A.gradient_searchDirection_eq_neg_residualPairing_self 0
          (fun t ht => False.elim (Nat.not_lt_zero _ ht))
          (fun t ht => False.elim (Nat.not_lt_zero _ ht))
          (fun t ht => False.elim (Nat.not_lt_zero _ ht))
      · refine ⟨?_, ?_⟩
        · intro i hi
          exact False.elim (Nat.not_lt_zero _ hi)
        · refine ⟨?_, ?_⟩
          · intro i hi
            exact False.elim (Nat.not_lt_zero _ hi)
          · intro i hi
            exact False.elim (Nat.not_lt_zero _ hi)
  | succ k ih =>
      have hContinueK : A.continuingIteration k := hContinue k (Nat.lt_succ_self k)
      have hInteriorK : ‖A.step (k + 1)‖_A.weightMatrix < A.Δ := hInterior k (Nat.lt_succ_self k)
      have hResidualK : A.residualThreshold ≤ A.residualNorm (k + 1) :=
        hResidual k (Nat.lt_succ_self k)
      have hPrev := ih
        (fun t ht => hContinue t (Nat.lt_trans ht (Nat.lt_succ_self k)))
        (fun t ht => hInterior t (Nat.lt_trans ht (Nat.lt_succ_self k)))
        (fun t ht => hResidual t (Nat.lt_trans ht (Nat.lt_succ_self k)))
      rcases hPrev with ⟨hk1, hk2, hk3, hk4⟩
      have hCurvPosK : 0 < matrixQuadratic A.hessianApprox (A.searchDirection k) :=
        A.continuingCurvaturePos k hContinueK
      have hBetaDenomNeK : A.residualPairing k ≠ 0 :=
        A.betaDenominatorNeZero k hContinueK hInteriorK hResidualK
      have hBridgeNext :
          A.weightMatrix.mulVec (A.preconditionedGradient (k + 1)).ofLp =
            (A.gradient (k + 1)).ofLp :=
        A.weightMatrix_mulVec_preconditionedGradient_eq_gradient (k + 1) hContinue hInterior
      have hOrth :
          (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection k).ofLp = 0 := by
        -- Step `3` and the `α_k` update annihilate the previous search direction.
        calc
          (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection k).ofLp
              = ((A.gradient k).ofLp + A.α k • A.hessianApprox.mulVec (A.searchDirection k).ofLp) ⬝ᵥ
                  (A.searchDirection k).ofLp := by
                    rw [A.gradient_next_eq_ofLp hContinueK hInteriorK]
          _ = (A.gradient k).ofLp ⬝ᵥ (A.searchDirection k).ofLp +
                A.α k * matrixQuadratic A.hessianApprox (A.searchDirection k) := by
                rw [add_dotProduct, smul_dotProduct]
                simp [matrixQuadratic, dotProduct_comm, smul_eq_mul]
          _ = -A.residualPairing k +
                (A.residualPairing k / matrixQuadratic A.hessianApprox (A.searchDirection k)) *
                  matrixQuadratic A.hessianApprox (A.searchDirection k) := by
                rw [hk1 k (Nat.le_refl k), A.alphaUpdate k hContinueK]
          _ = 0 := by
                field_simp [hBetaDenomNeK, ne_of_gt hCurvPosK]
                ring
      have hOldDirectionOrth :
          ∀ i < k + 1, (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection i).ofLp = 0 := by
        intro i hi
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hi) with rfl | hik
        · -- The previous direction is the Step `3` orthogonality just established.
          simpa using hOrth
        · -- Older directions stay orthogonal because the new `B d_k` term is conjugate to them.
          calc
            (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection i).ofLp
                = ((A.gradient k).ofLp + A.α k • A.hessianApprox.mulVec (A.searchDirection k).ofLp) ⬝ᵥ
                    (A.searchDirection i).ofLp := by
                      rw [A.gradient_next_eq_ofLp hContinueK hInteriorK]
            _ = (A.gradient k).ofLp ⬝ᵥ (A.searchDirection i).ofLp +
                  A.α k * (A.hessianApprox.mulVec (A.searchDirection k).ofLp ⬝ᵥ
                    (A.searchDirection i).ofLp) := by
                    rw [add_dotProduct, smul_dotProduct]
                    simp [smul_eq_mul]
            _ = (A.gradient k).ofLp ⬝ᵥ (A.searchDirection i).ofLp +
                  A.α k * ((A.searchDirection i).ofLp ⬝ᵥ
                    A.hessianApprox.mulVec (A.searchDirection k).ofLp) := by
                    congr 1
                    rw [dotProduct_comm]
            _ = 0 := by
                    rw [hk3 i hik, hk4 i hik]
                    ring
      have hOldPreconditionedOrth :
          ∀ i < k + 1, (A.gradient (k + 1)).ofLp ⬝ᵥ (A.preconditionedGradient i).ofLp = 0 := by
        intro i hi
        cases i with
        | zero =>
            have hZeroDir :
                (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection 0).ofLp = 0 :=
              hOldDirectionOrth 0 (Nat.succ_pos k)
            -- At index `0`, the search direction is exactly `-v₀`.
            rw [A.searchDirectionZero] at hZeroDir
            simpa [dotProduct_neg] using hZeroDir
        | succ i =>
            have hiPrev : i < k + 1 := Nat.lt_trans (Nat.lt_succ_self i) hi
            have hiStep : i < k := Nat.lt_of_succ_lt_succ hi
            have hContinueI : A.continuingIteration i := hContinue i hiPrev
            have hInteriorI : ‖A.step (i + 1)‖_A.weightMatrix < A.Δ := hInterior i hiPrev
            have hResidualI : A.residualThreshold ≤ A.residualNorm (i + 1) := hResidual i hiPrev
            have hDirSucc :
                (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection (i + 1)).ofLp = 0 :=
              hOldDirectionOrth (i + 1) hi
            have hDirPrev :
                (A.gradient (k + 1)).ofLp ⬝ᵥ (A.searchDirection i).ofLp = 0 :=
              hOldDirectionOrth i hiPrev
            -- Rewrite `d_(i+1)` through Step `4`; the already-known old-direction orthogonality
            -- removes the `β_i d_i` term and leaves `g_(k+1)ᵀ v_(i+1) = 0`.
            rw [A.searchDirection_next_eq hContinueI hInteriorI hResidualI] at hDirSucc
            have hNeg :
                -((A.gradient (k + 1)).ofLp ⬝ᵥ (A.preconditionedGradient (i + 1)).ofLp) = 0 := by
              simpa [dotProduct_add, dotProduct_smul, dotProduct_neg, smul_eq_mul, hDirPrev]
                using hDirSucc
            linarith
      have hPairNext :
          ∀ i ≤ k + 1, (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp =
            -A.residualPairing (k + 1) := by
        intro i hi
        rcases Nat.eq_or_lt_of_le hi with rfl | hik
        · -- The diagonal case stays on the already-proved owner recurrence.
          simpa using A.gradient_searchDirection_eq_neg_residualPairing_self (k + 1)
            hContinue hInterior hResidual
        · have hik' : i ≤ k := Nat.le_of_lt_succ hik
          -- Expand the new direction only once and use the vanished mixed pairing.
          calc
            (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp
                = (A.gradient i).ofLp ⬝ᵥ
                    (-(A.preconditionedGradient (k + 1)).ofLp + A.β k • (A.searchDirection k).ofLp) := by
                      rw [A.searchDirection_next_eq hContinueK hInteriorK hResidualK]
                      simp
            _ = -((A.gradient i).ofLp ⬝ᵥ (A.preconditionedGradient (k + 1)).ofLp) +
                  A.β k * ((A.gradient i).ofLp ⬝ᵥ (A.searchDirection k).ofLp) := by
                    rw [dotProduct_add, dotProduct_smul, dotProduct_neg]
                    simp [smul_eq_mul]
            _ = A.β k * (-A.residualPairing k) := by
                    have hBridgeI :
                        A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp =
                          (A.gradient i).ofLp :=
                      A.weightMatrix_mulVec_preconditionedGradient_eq_gradient i
                        (fun t ht => hContinue t (Nat.lt_trans ht hik))
                        (fun t ht => hInterior t (Nat.lt_trans ht hik))
                    rw [A.gradient_preconditionedGradient_swap hBridgeI hBridgeNext]
                    simp [hOldPreconditionedOrth i hik, hk1 i hik']
            _ = -A.residualPairing (k + 1) := by
                    rw [A.betaUpdate k hContinueK hInteriorK hResidualK]
                    field_simp [hBetaDenomNeK]
      have hConjugacyNext :
          ∀ i < k + 1,
            (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.searchDirection (k + 1)).ofLp =
              0 := by
        intro i hi
        have hiLe : i ≤ k := Nat.le_of_lt_succ hi
        have hContinueI : A.continuingIteration i := hContinue i hi
        have hInteriorI : ‖A.step (i + 1)‖_A.weightMatrix < A.Δ := hInterior i hi
        have hResidualI : A.residualThreshold ≤ A.residualNorm (i + 1) := hResidual i hi
        have hCurvPosI : 0 < matrixQuadratic A.hessianApprox (A.searchDirection i) :=
          A.continuingCurvaturePos i hContinueI
        have hResidualNeI : A.residualPairing i ≠ 0 :=
          A.betaDenominatorNeZero i hContinueI hInteriorI hResidualI
        have hAlphaNeI : A.α i ≠ 0 := by
          rw [A.alphaUpdate i hContinueI]
          exact div_ne_zero hResidualNeI (ne_of_gt hCurvPosI)
        have hSwap :
            A.hessianApprox.mulVec (A.searchDirection i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp =
              (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.searchDirection (k + 1)).ofLp := by
          simpa [hSymm.eq, dotProduct_comm] using
            (Matrix.dotProduct_transpose_mulVec (A := A.hessianApprox)
              (x := (A.searchDirection (k + 1)).ofLp)
              (y := (A.searchDirection i).ofLp))
        have hDiff :
            (A.gradient (i + 1)).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp =
              (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp +
                A.α i * ((A.searchDirection i).ofLp ⬝ᵥ
                  A.hessianApprox.mulVec (A.searchDirection (k + 1)).ofLp) := by
          -- Compare the pairings with `g_(i+1)` and `g_i`; the difference is exactly `α_i d_iᵀ B d_(k+1)`.
          calc
            (A.gradient (i + 1)).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp
                = ((A.gradient i).ofLp + A.α i • A.hessianApprox.mulVec (A.searchDirection i).ofLp) ⬝ᵥ
                    (A.searchDirection (k + 1)).ofLp := by
                      rw [A.gradient_next_eq_ofLp hContinueI hInteriorI]
            _ = (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp +
                  A.α i * (A.hessianApprox.mulVec (A.searchDirection i).ofLp ⬝ᵥ
                    (A.searchDirection (k + 1)).ofLp) := by
                    rw [add_dotProduct, smul_dotProduct]
                    simp [smul_eq_mul]
            _ = (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp +
                  A.α i * ((A.searchDirection i).ofLp ⬝ᵥ
                    A.hessianApprox.mulVec (A.searchDirection (k + 1)).ofLp) := by
                    rw [hSwap]
        have hSame :
            (A.gradient (i + 1)).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp =
              (A.gradient i).ofLp ⬝ᵥ (A.searchDirection (k + 1)).ofLp := by
          rw [hPairNext (i + 1) (Nat.succ_le_succ hiLe), hPairNext i (Nat.le_of_lt hi)]
        have hMulZero :
            A.α i * ((A.searchDirection i).ofLp ⬝ᵥ
              A.hessianApprox.mulVec (A.searchDirection (k + 1)).ofLp) = 0 := by
          linarith [hDiff, hSame]
        exact (mul_eq_zero.mp hMulZero).resolve_left hAlphaNeI
      have hResidualOrthNext :
          ∀ i < k + 1, (A.gradient i).ofLp ⬝ᵥ (A.preconditionedGradient (k + 1)).ofLp = 0 := by
        intro i hi
        have hBridgeI :
            A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp = (A.gradient i).ofLp :=
          A.weightMatrix_mulVec_preconditionedGradient_eq_gradient i
            (fun t ht => hContinue t (Nat.lt_trans ht hi))
            (fun t ht => hInterior t (Nat.lt_trans ht hi))
        -- Swap the mixed pairing through the symmetric `W`-form and reuse the old-index orthogonality.
        rw [A.gradient_preconditionedGradient_swap hBridgeI hBridgeNext]
        exact hOldPreconditionedOrth i hi
      exact ⟨hPairNext, hResidualOrthNext, hOldDirectionOrth, hConjugacyNext⟩

/-- Helper for Chapter06 Lemma 6.1.13: if `d_iᵀ B d_i ≠ 0`, then the residual pairing
`g_iᵀ v_i` cannot vanish. -/
private lemma residualPairing_ne_zero_of_searchDirectionCurvature
    (A : SteihaugCGAlgorithm n) {i : ℕ}
    (hContinue : ∀ t : ℕ, t < i → A.continuingIteration t)
    (hInterior : ∀ t : ℕ, t < i → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ t : ℕ, t < i → A.residualThreshold ≤ A.residualNorm (t + 1))
    (hCurvatureNeZero :
      matrixQuadratic A.hessianApprox (A.searchDirection i) ≠ 0) :
    A.residualPairing i ≠ 0 := by
  intro hResidualZero
  have hBridge :
      A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp = (A.gradient i).ofLp :=
    A.weightMatrix_mulVec_preconditionedGradient_eq_gradient i hContinue hInterior
  have hPreconditionedZero : (A.preconditionedGradient i).ofLp = 0 := by
    by_contra hNonzero
    have hPos :
        0 < (A.preconditionedGradient i).ofLp ⬝ᵥ
          A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp :=
      A.weightMatrixPosDef.dotProduct_mulVec_pos hNonzero
    have hPairZero :
        (A.preconditionedGradient i).ofLp ⬝ᵥ
          A.weightMatrix.mulVec (A.preconditionedGradient i).ofLp = 0 := by
      rw [hBridge]
      simpa [SteihaugCGAlgorithm.residualPairing, steihaugResidualPairingAt,
        steihaugResidualPairing, dotProduct_comm] using hResidualZero
    exact (not_lt_of_ge (le_of_eq hPairZero)) hPos
  cases i with
  | zero =>
      have hDirectionZero : (A.searchDirection 0).ofLp = 0 := by
        rw [A.searchDirectionZero]
        simpa using congrArg Neg.neg hPreconditionedZero
      -- If `v₀ = 0`, then also `d₀ = 0`, contradicting the curvature hypothesis.
      apply hCurvatureNeZero
      simp [matrixQuadratic, hDirectionZero]
  | succ i =>
      have hContinueI : A.continuingIteration i := hContinue i (Nat.lt_succ_self i)
      have hInteriorI : ‖A.step (i + 1)‖_A.weightMatrix < A.Δ := hInterior i (Nat.lt_succ_self i)
      have hResidualI : A.residualThreshold ≤ A.residualNorm (i + 1) :=
        hResidual i (Nat.lt_succ_self i)
      have hDenomNe : A.residualPairing i ≠ 0 :=
        A.betaDenominatorNeZero i hContinueI hInteriorI hResidualI
      have hBetaZero : A.β i = 0 := by
        rw [A.betaUpdate i hContinueI hInteriorI hResidualI]
        simp [SteihaugCGAlgorithm.residualPairing, hResidualZero, hDenomNe]
      have hDirectionZero : (A.searchDirection (i + 1)).ofLp = 0 := by
        -- The successor search direction is `-v_(i+1) + β_i d_i`, and both terms now vanish.
        rw [A.searchDirection_next_eq hContinueI hInteriorI hResidualI, hBetaZero]
        simp [hPreconditionedZero]
      apply hCurvatureNeZero
      simp [matrixQuadratic, hDirectionZero]

/-- Helper for Chapter06 Lemma 6.1.13: once the right index advances by one Step `4` update,
the weighted pairing with a fixed older search direction picks up exactly one factor `β_k`. -/
private lemma searchDirectionWeightPairing_succ
    (A : SteihaugCGAlgorithm n) {i k : ℕ} (hSymm : A.hessianApprox.IsSymm)
    (hik : i < k + 1)
    (hContinue : ∀ t : ℕ, t < k + 1 → A.continuingIteration t)
    (hInterior : ∀ t : ℕ, t < k + 1 → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ t : ℕ, t < k + 1 → A.residualThreshold ≤ A.residualNorm (t + 1)) :
    (A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection (k + 1)).ofLp =
      A.β k * ((A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection k).ofLp) := by
  have hContinueK : A.continuingIteration k := hContinue k (Nat.lt_succ_self k)
  have hInteriorK : ‖A.step (k + 1)‖_A.weightMatrix < A.Δ := hInterior k (Nat.lt_succ_self k)
  have hResidualK : A.residualThreshold ≤ A.residualNorm (k + 1) := hResidual k (Nat.lt_succ_self k)
  have hBridgeNext :
      A.weightMatrix.mulVec (A.preconditionedGradient (k + 1)).ofLp =
        (A.gradient (k + 1)).ofLp :=
    A.weightMatrix_mulVec_preconditionedGradient_eq_gradient (k + 1) hContinue hInterior
  have hPack := A.prefixPairingInvariants (k + 1) hSymm hContinue hInterior hResidual
  rcases hPack with ⟨_, _, hOldDirectionOrth, _⟩
  have hOrth :
      (A.searchDirection i).ofLp ⬝ᵥ (A.gradient (k + 1)).ofLp = 0 := by
    simpa [dotProduct_comm] using hOldDirectionOrth i hik
  -- Expand only the new direction; the old-gradient term vanishes by the invariant package.
  calc
    (A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection (k + 1)).ofLp
        = (A.searchDirection i).ofLp ⬝ᵥ
            A.weightMatrix.mulVec
              (-(A.preconditionedGradient (k + 1)).ofLp + A.β k • (A.searchDirection k).ofLp) := by
                rw [A.searchDirection_next_eq hContinueK hInteriorK hResidualK]
                simp
    _ = (A.searchDirection i).ofLp ⬝ᵥ
          (-(A.gradient (k + 1)).ofLp + A.β k • A.weightMatrix.mulVec (A.searchDirection k).ofLp) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul, hBridgeNext]
    _ = -((A.searchDirection i).ofLp ⬝ᵥ (A.gradient (k + 1)).ofLp) +
          A.β k * ((A.searchDirection i).ofLp ⬝ᵥ
            A.weightMatrix.mulVec (A.searchDirection k).ofLp) := by
            rw [dotProduct_add, dotProduct_smul, dotProduct_neg]
            simp [smul_eq_mul]
    _ = A.β k * ((A.searchDirection i).ofLp ⬝ᵥ
          A.weightMatrix.mulVec (A.searchDirection k).ofLp) := by
            simp [hOrth]

/-- Helper for Chapter06 Lemma 6.1.13: the weighted pairing formula follows by induction on the
gap `m`, once the one-step `β`-recurrence is isolated. -/
private lemma searchDirection_weightMatrix_eq_ratio_aux
    (A : SteihaugCGAlgorithm n) (i m : ℕ) (hSymm : A.hessianApprox.IsSymm)
    (hContinue : ∀ t : ℕ, t < i + m → A.continuingIteration t)
    (hInterior : ∀ t : ℕ, t < i + m → ‖A.step (t + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ t : ℕ, t < i + m → A.residualThreshold ≤ A.residualNorm (t + 1))
    (hCurvatureNeZero :
      matrixQuadratic A.hessianApprox (A.searchDirection i) ≠ 0) :
    (A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection (i + m)).ofLp =
      (A.residualPairing (i + m) / A.residualPairing i) *
        ((A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection i).ofLp) := by
  induction m with
  | zero =>
      have hResidualNe :
          A.residualPairing i ≠ 0 :=
        A.residualPairing_ne_zero_of_searchDirectionCurvature hContinue hInterior hResidual
          hCurvatureNeZero
      -- The diagonal case is just the identity factor `r_i / r_i = 1`.
      simp [Nat.add_zero, hResidualNe]
  | succ m ih =>
      have hResidualNeInitial :
          A.residualPairing i ≠ 0 := by
        have hiBound : i < i + m + 1 := Nat.lt_add_of_pos_right (Nat.succ_pos m)
        exact A.residualPairing_ne_zero_of_searchDirectionCurvature (i := i)
          (hContinue := fun t ht => hContinue t (Nat.lt_trans ht hiBound))
          (hInterior := fun t ht => hInterior t (Nat.lt_trans ht hiBound))
          (hResidual := fun t ht => hResidual t (Nat.lt_trans ht hiBound))
          hCurvatureNeZero
      have hContinueK : A.continuingIteration (i + m) := hContinue (i + m) (Nat.lt_succ_self (i + m))
      have hInteriorK : ‖A.step (i + m + 1)‖_A.weightMatrix < A.Δ :=
        hInterior (i + m) (Nat.lt_succ_self (i + m))
      have hResidualK : A.residualThreshold ≤ A.residualNorm (i + m + 1) :=
        hResidual (i + m) (Nat.lt_succ_self (i + m))
      have hResidualNeK : A.residualPairing (i + m) ≠ 0 :=
        A.betaDenominatorNeZero (i + m) hContinueK hInteriorK hResidualK
      have hStep :
          (A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection (i + m + 1)).ofLp =
            A.β (i + m) * ((A.searchDirection i).ofLp ⬝ᵥ
              A.weightMatrix.mulVec (A.searchDirection (i + m)).ofLp) := by
        have hik : i < i + m + 1 := Nat.lt_add_of_pos_right (Nat.succ_pos m)
        exact A.searchDirectionWeightPairing_succ hSymm hik hContinue hInterior hResidual
      have hPrev := ih
        (fun t ht => hContinue t (Nat.lt_trans ht (Nat.lt_succ_self (i + m))))
        (fun t ht => hInterior t (Nat.lt_trans ht (Nat.lt_succ_self (i + m))))
        (fun t ht => hResidual t (Nat.lt_trans ht (Nat.lt_succ_self (i + m))))
      -- Replace one `β_(i+m)` factor by the ratio `r_(i+m+1) / r_(i+m)` and cancel.
      calc
        (A.searchDirection i).ofLp ⬝ᵥ A.weightMatrix.mulVec (A.searchDirection (i + m + 1)).ofLp
            = A.β (i + m) * ((A.searchDirection i).ofLp ⬝ᵥ
                A.weightMatrix.mulVec (A.searchDirection (i + m)).ofLp) := hStep
        _ = A.β (i + m) *
              ((A.residualPairing (i + m) / A.residualPairing i) *
                ((A.searchDirection i).ofLp ⬝ᵥ
                  A.weightMatrix.mulVec (A.searchDirection i).ofLp)) := by
              rw [hPrev]
        _ = (A.residualPairing (i + m + 1) / A.residualPairing (i + m)) *
              ((A.residualPairing (i + m) / A.residualPairing i) *
                ((A.searchDirection i).ofLp ⬝ᵥ
                  A.weightMatrix.mulVec (A.searchDirection i).ofLp)) := by
              rw [A.betaUpdate (i + m) hContinueK hInteriorK hResidualK]
        _ = (A.residualPairing (i + m + 1) / A.residualPairing i) *
              ((A.searchDirection i).ofLp ⬝ᵥ
                A.weightMatrix.mulVec (A.searchDirection i).ofLp) := by
              field_simp [hResidualNeInitial, hResidualNeK]

/-- Helper for Chapter06 Lemma 6.1.13: the quadratic model increment along `s + t d`
separates into a linear term and a curvature term. -/
private lemma quadraticModel_increment_eq
    (f : ℝ) (A : SteihaugCGAlgorithm n) (s d : Point n) (t : ℝ)
    (hSymm : A.hessianApprox.IsSymm) :
    A.quadraticModel f (s + t • d) - A.quadraticModel f s =
      t * dotProduct A.initialGradient d +
        t * dotProduct d (A.hessianApprox.mulVec s) +
        (1 / 2 : ℝ) * t ^ (2 : ℕ) * dotProduct d (A.hessianApprox.mulVec d) := by
  have hCross :
      dotProduct s (A.hessianApprox.mulVec d) = dotProduct d (A.hessianApprox.mulVec s) := by
    -- Symmetry of `B` lets the mixed quadratic terms match.
    simpa [hSymm.eq] using
      (Matrix.dotProduct_transpose_mulVec (A := A.hessianApprox) (x := s) (y := d))
  -- Expand `q(s + t d)` once and collect the linear and quadratic pieces.
  simp [SteihaugCGAlgorithm.quadraticModel, matrixQuadratic, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, Matrix.mulVec_add, Matrix.mulVec_smul, hCross]
  ring

/-- Chapter06 Lemma 6.1.13 (1): along a genuine Steihaug-CG history that continues through all
earlier indices needed to reach `j`, stays inside the trust region, and does not trigger the
residual stopping test on those earlier steps, if the Hessian approximation `B` is symmetric and
`i ≤ j`, and `d_iᵀ B d_i ≠ 0`, then
`g_iᵀ d_j = -g_jᵀ v_j`. This is the source identity `(6.1.73)`. -/
theorem gradient_searchDirection_eq_neg_gradient_preconditionedGradient
    (A : SteihaugCGAlgorithm n) {i j : ℕ} (hSymm : A.hessianApprox.IsSymm) (hij : i ≤ j)
    (hContinue : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hCurvatureNeZero :
      matrixQuadratic A.hessianApprox (A.searchDirection i) ≠ 0) :
    dotProduct (A.gradient i) (A.searchDirection j) =
      -A.residualPairing j := by
  -- Route correction: instead of re-expanding `d_j` directly, project the cross-index invariant
  -- package at the target right index `j`.
  let _ := hCurvatureNeZero
  exact (A.prefixPairingInvariants j hSymm hContinue hInterior hResidual).1 i hij

/-- Chapter06 Lemma 6.1.13 (2): along a genuine Steihaug-CG history that continues through all
earlier indices needed to reach `j`, stays inside the trust region, and does not trigger the
residual stopping test on those earlier steps, if the Hessian approximation `B` is symmetric,
`i ≤ j`, and `d_iᵀ B d_i ≠ 0`, then
`d_iᵀ W d_j = ((g_jᵀ v_j) / (g_iᵀ v_i)) * d_iᵀ W d_i`. This keeps the source assumption at
index `i` explicit, so the diagonal case `j = i` does not force continuation past `i`.
This is the source identity `(6.1.74)`. -/
theorem searchDirection_weightMatrix_eq_ratio
    (A : SteihaugCGAlgorithm n) {i j : ℕ} (hSymm : A.hessianApprox.IsSymm) (hij : i ≤ j)
    (hContinue : ∀ k : ℕ, k < j → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < j → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < j → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hCurvatureNeZero :
      matrixQuadratic A.hessianApprox (A.searchDirection i) ≠ 0) :
    dotProduct (A.searchDirection i) (A.weightMatrix.mulVec (A.searchDirection j)) =
      (A.residualPairing j / A.residualPairing i) *
        dotProduct (A.searchDirection i) (A.weightMatrix.mulVec (A.searchDirection i)) := by
  -- Route correction: isolate the one-step `β`-recurrence first, then induct on the gap
  -- `j - i` instead of trying to telescope products inside the final theorem.
  rcases Nat.exists_eq_add_of_le hij with ⟨m, rfl⟩
  simpa [Nat.add_assoc] using
    A.searchDirection_weightMatrix_eq_ratio_aux i m hSymm hContinue hInterior hResidual
      hCurvatureNeZero

/-- Chapter06 Lemma 6.1.13 (3): along a genuine Steihaug-CG history that continues through all
earlier indices needed to reach `i`, stays inside the trust region, and does not trigger the
residual stopping test on those earlier steps, if the Hessian approximation `B` is symmetric and
iteration `i` is a continuing Steihaug-CG step, then the quadratic model decreases by
`(1 / 2) * (g_iᵀ v_i)^2 / (d_iᵀ B d_i)` after one step:
`q(s_(i+1)) = q(s_i) - (1 / 2) * (g_iᵀ v_i)^2 / (d_iᵀ B d_i)`. The continuing hypothesis at `i`
already supplies the positive-curvature denominator. This is the source identity `(6.1.75)`. -/
theorem quadraticModel_step_succ_eq_sub
    (f : ℝ) (A : SteihaugCGAlgorithm n) (i : ℕ) (hSymm : A.hessianApprox.IsSymm)
    (hHistory : ∀ k : ℕ, k < i → A.continuingIteration k)
    (hInterior : ∀ k : ℕ, k < i → ‖A.step (k + 1)‖_A.weightMatrix < A.Δ)
    (hResidual : ∀ k : ℕ, k < i → A.residualThreshold ≤ A.residualNorm (k + 1))
    (hContinue : A.continuingIteration i) :
    A.quadraticModel f (A.step (i + 1)) =
      A.quadraticModel f (A.step i) -
        (1 / 2 : ℝ) *
          (A.residualPairing i) ^ (2 : ℕ) /
            matrixQuadratic A.hessianApprox (A.searchDirection i) := by
  have hGradStep := A.gradient_eq_initialGradient_add_hessian_mulVec_step i hHistory hInterior
  have hPair := A.gradient_searchDirection_eq_neg_residualPairing_self i hHistory hInterior hResidual
  have hCurvPos : 0 < matrixQuadratic A.hessianApprox (A.searchDirection i) :=
    A.continuingCurvaturePos i hContinue
  have hAlpha : A.α i = A.residualPairing i / matrixQuadratic A.hessianApprox (A.searchDirection i) :=
    A.alphaUpdate i hContinue
  have hGradTerm :
      A.initialGradient.ofLp ⬝ᵥ (A.searchDirection i).ofLp +
        (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp =
          (A.gradient i).ofLp ⬝ᵥ (A.searchDirection i).ofLp := by
    -- Rewrite the linear plus mixed Hessian term as `g_iᵀ d_i`.
    calc
      A.initialGradient.ofLp ⬝ᵥ (A.searchDirection i).ofLp +
          (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp
          = (A.searchDirection i).ofLp ⬝ᵥ A.initialGradient.ofLp +
              (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp := by
                rw [dotProduct_comm]
      _ = (A.searchDirection i).ofLp ⬝ᵥ
            (A.initialGradient.ofLp + A.hessianApprox.mulVec (A.step i).ofLp) := by
              rw [dotProduct_add]
      _ = (A.searchDirection i).ofLp ⬝ᵥ (A.gradient i).ofLp := by
            rw [hGradStep]
      _ = (A.gradient i).ofLp ⬝ᵥ (A.searchDirection i).ofLp := by
            rw [dotProduct_comm]
  have hInc :
      A.quadraticModel f (A.step (i + 1)) - A.quadraticModel f (A.step i) =
        A.α i * A.initialGradient.ofLp ⬝ᵥ (A.searchDirection i).ofLp +
          A.α i * ((A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp) +
          (1 / 2 : ℝ) * A.α i ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) := by
    -- Specialize the generic quadratic increment formula to the actual Steihaug step.
    simpa [A.step_next_eq hContinue, matrixQuadratic] using
      A.quadraticModel_increment_eq f (A.step i) (A.searchDirection i) (A.α i) hSymm
  have hInc' :
      A.quadraticModel f (A.step (i + 1)) - A.quadraticModel f (A.step i) =
        A.α i * ((A.gradient i).ofLp ⬝ᵥ (A.searchDirection i).ofLp) +
          (1 / 2 : ℝ) * (A.α i) ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) := by
    -- Collapse the linear and mixed terms into the single quantity `g_iᵀ d_i`.
    calc
      A.quadraticModel f (A.step (i + 1)) - A.quadraticModel f (A.step i)
          = A.α i * A.initialGradient.ofLp ⬝ᵥ (A.searchDirection i).ofLp +
              A.α i * ((A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp) +
              (1 / 2 : ℝ) * A.α i ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) := hInc
      _ = A.α i *
            (A.initialGradient.ofLp ⬝ᵥ (A.searchDirection i).ofLp +
              (A.searchDirection i).ofLp ⬝ᵥ A.hessianApprox.mulVec (A.step i).ofLp) +
            (1 / 2 : ℝ) * A.α i ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) := by
              ring
      _ = A.α i * ((A.gradient i).ofLp ⬝ᵥ (A.searchDirection i).ofLp) +
            (1 / 2 : ℝ) * A.α i ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) := by
              rw [hGradTerm]
  have hDecrease :
      A.α i * ((A.gradient i).ofLp ⬝ᵥ (A.searchDirection i).ofLp) +
          (1 / 2 : ℝ) * (A.α i) ^ (2 : ℕ) * matrixQuadratic A.hessianApprox (A.searchDirection i) =
        -(1 / 2 : ℝ) * (A.residualPairing i) ^ (2 : ℕ) /
          matrixQuadratic A.hessianApprox (A.searchDirection i) := by
    -- Substitute `g_iᵀ d_i = -g_iᵀ v_i` and the Step 2 formula for `α_i`.
    rw [hPair, hAlpha]
    field_simp [ne_of_gt hCurvPos]
    ring
  -- Reassemble the difference formula as the claimed one-step decrease.
  calc
    A.quadraticModel f (A.step (i + 1))
        = A.quadraticModel f (A.step i) +
            (A.quadraticModel f (A.step (i + 1)) - A.quadraticModel f (A.step i)) := by
              ring
    _ = A.quadraticModel f (A.step i) -
          (1 / 2 : ℝ) * (A.residualPairing i) ^ (2 : ℕ) /
            matrixQuadratic A.hessianApprox (A.searchDirection i) := by
          rw [hInc', hDecrease]
          ring

end SteihaugCGAlgorithm

end
