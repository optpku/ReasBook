/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Algorithm_2_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_1_5

open Matrix

noncomputable section

-- Domain sampling for this exercise:
-- * owner declarations inspected: `IsExactLineSearchStepOnNonnegativeRay`,
--   `GeneralUnconstrainedOptimizationMethod`, `quadraticObjective`, and
--   `ellipsoidNorm`.
-- * source-facing: the two explicit diagonal matrices from the exercise and their stated linear
--   rates;
-- * core/canonical: `quadraticObjective`, `GeneralUnconstrainedOptimizationMethod`,
--   `posDefEigenvalues`, and `ellipsoidNorm`;
-- * bridge/view: the centered specialization `quadraticObjective G 0 0`.

/-- The diagonal matrix `diag(1, 9)` attached to the first quadratic in Exercise 3.2. -/
def diagMatrixOneNine : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![(1 : ℝ), 9]

/-- The matrix `diag(1, 9)` is positive definite. -/
theorem diagMatrixOneNine_posDef : diagMatrixOneNine.PosDef := by
  -- Positive diagonal entries let us apply the canonical diagonal positive-definite criterion.
  refine Matrix.PosDef.diagonal ?_
  intro i
  fin_cases i <;> norm_num

/-- The largest eigenvalue of `diagMatrixOneNine` is `9`. -/
theorem diagMatrixOneNine_eigenvalueMax :
    IsGreatest (Set.range (posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef)) 9 :=
  by
  -- Rewrite membership through the real spectrum of the diagonal matrix.
  have hMemSpec : (9 : ℝ) ∈ spectrum ℝ diagMatrixOneNine := by
    rw [diagMatrixOneNine, spectrum_diagonal]
    refine ⟨1, ?_⟩
    simp
  have hMem :
      (9 : ℝ) ∈ Set.range (posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef) := by
    simpa [posDefEigenvalues_def,
      diagMatrixOneNine_posDef.isHermitian.spectrum_real_eq_range_eigenvalues] using hMemSpec
  refine (isGreatest_posDefEigenvalues_iff diagMatrixOneNine diagMatrixOneNine_posDef 9).2 ?_
  refine ⟨hMem, ?_⟩
  intro i
  have hiSpec :
      posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef i ∈
        spectrum ℝ diagMatrixOneNine := by
    simpa [posDefEigenvalues_def] using
      diagMatrixOneNine_posDef.isHermitian.eigenvalues_mem_spectrum_real i
  have hiRange :
      posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef i ∈
        Set.range (![ (1 : ℝ), 9] : Fin 2 → ℝ) := by
    simpa [diagMatrixOneNine] using hiSpec
  rcases hiRange with ⟨j, hj⟩
  fin_cases j <;> simp at hj ⊢ <;> linarith

/-- The smallest eigenvalue of `diagMatrixOneNine` is `1`. -/
theorem diagMatrixOneNine_eigenvalueMin :
    IsLeast (Set.range (posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef)) 1 := by
  -- Rewrite membership through the real spectrum of the diagonal matrix.
  have hMemSpec : (1 : ℝ) ∈ spectrum ℝ diagMatrixOneNine := by
    rw [diagMatrixOneNine, spectrum_diagonal]
    refine ⟨0, ?_⟩
    simp
  have hMem :
      (1 : ℝ) ∈ Set.range (posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef) := by
    simpa [posDefEigenvalues_def,
      diagMatrixOneNine_posDef.isHermitian.spectrum_real_eq_range_eigenvalues] using hMemSpec
  refine (isLeast_posDefEigenvalues_iff diagMatrixOneNine diagMatrixOneNine_posDef 1).2 ?_
  refine ⟨hMem, ?_⟩
  intro i
  have hiSpec :
      posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef i ∈
        spectrum ℝ diagMatrixOneNine := by
    simpa [posDefEigenvalues_def] using
      diagMatrixOneNine_posDef.isHermitian.eigenvalues_mem_spectrum_real i
  have hiRange :
      posDefEigenvalues diagMatrixOneNine diagMatrixOneNine_posDef i ∈
        Set.range (![ (1 : ℝ), 9] : Fin 2 → ℝ) := by
    simpa [diagMatrixOneNine] using hiSpec
  rcases hiRange with ⟨j, hj⟩
  fin_cases j <;> simp at hj ⊢ <;> linarith

/-- The diagonal matrix `diag(1, 10000)` attached to the second quadratic in Exercise 3.2. -/
def diagMatrixOneTenThousand : Matrix (Fin 2) (Fin 2) ℝ :=
  diagonal ![(1 : ℝ), 10000]

/-- The matrix `diag(1, 10000)` is positive definite. -/
theorem diagMatrixOneTenThousand_posDef : diagMatrixOneTenThousand.PosDef := by
  -- Positive diagonal entries let us apply the canonical diagonal positive-definite criterion.
  refine Matrix.PosDef.diagonal ?_
  intro i
  fin_cases i <;> norm_num

/-- The largest eigenvalue of `diagMatrixOneTenThousand` is `10000`. -/
theorem diagMatrixOneTenThousand_eigenvalueMax :
    IsGreatest
      (Set.range (posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef))
      10000 := by
  -- Rewrite membership through the real spectrum of the diagonal matrix.
  have hMemSpec : (10000 : ℝ) ∈ spectrum ℝ diagMatrixOneTenThousand := by
    rw [diagMatrixOneTenThousand, spectrum_diagonal]
    refine ⟨1, ?_⟩
    simp
  have hMem :
      (10000 : ℝ) ∈
        Set.range (posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef) := by
    simpa [posDefEigenvalues_def,
      diagMatrixOneTenThousand_posDef.isHermitian.spectrum_real_eq_range_eigenvalues] using
      hMemSpec
  refine
    (isGreatest_posDefEigenvalues_iff
      diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef 10000).2 ?_
  refine ⟨hMem, ?_⟩
  intro i
  have hiSpec :
      posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef i ∈
        spectrum ℝ diagMatrixOneTenThousand := by
    simpa [posDefEigenvalues_def] using
      diagMatrixOneTenThousand_posDef.isHermitian.eigenvalues_mem_spectrum_real i
  have hiRange :
      posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef i ∈
        Set.range (![ (1 : ℝ), 10000] : Fin 2 → ℝ) := by
    simpa [diagMatrixOneTenThousand] using hiSpec
  rcases hiRange with ⟨j, hj⟩
  fin_cases j <;> simp at hj ⊢ <;> linarith

/-- The smallest eigenvalue of `diagMatrixOneTenThousand` is `1`. -/
theorem diagMatrixOneTenThousand_eigenvalueMin :
    IsLeast
      (Set.range (posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef))
      1 := by
  -- Rewrite membership through the real spectrum of the diagonal matrix.
  have hMemSpec : (1 : ℝ) ∈ spectrum ℝ diagMatrixOneTenThousand := by
    rw [diagMatrixOneTenThousand, spectrum_diagonal]
    refine ⟨0, ?_⟩
    simp
  have hMem :
      (1 : ℝ) ∈
        Set.range (posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef) := by
    simpa [posDefEigenvalues_def,
      diagMatrixOneTenThousand_posDef.isHermitian.spectrum_real_eq_range_eigenvalues] using
      hMemSpec
  refine
    (isLeast_posDefEigenvalues_iff
      diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef 1).2 ?_
  refine ⟨hMem, ?_⟩
  intro i
  have hiSpec :
      posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef i ∈
        spectrum ℝ diagMatrixOneTenThousand := by
    simpa [posDefEigenvalues_def] using
      diagMatrixOneTenThousand_posDef.isHermitian.eigenvalues_mem_spectrum_real i
  have hiRange :
      posDefEigenvalues diagMatrixOneTenThousand diagMatrixOneTenThousand_posDef i ∈
        Set.range (![ (1 : ℝ), 10000] : Fin 2 → ℝ) := by
    simpa [diagMatrixOneTenThousand] using hiSpec
  rcases hiRange with ⟨j, hj⟩
  fin_cases j <;> simp at hj ⊢ <;> linarith

/-- Helper for Chapter03 Exercise 3.2: a Chapter 2 exact-line-search method whose directions are
the canonical steepest-descent directions cannot hit the stationary point `0` on a centered
positive-definite quadratic. -/
theorem generalMethod_iterate_ne_zero
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G.PosDef)
    (A : GeneralUnconstrainedOptimizationMethod 2 (quadraticObjective G 0 0))
    (h_direction :
      ∀ k,
        A.d k = steepestDescentDirection (quadraticObjective G 0 0) (A k))
    (k : ℕ) :
    A k ≠ 0 := by
  intro hk
  have hGsymm : G.IsSymm := posDef_isSymm hG
  have hGradZero :
      gradient (quadraticObjective G 0 0) (A k) = 0 := by
    rw [hk]
    simpa using gradient_quadraticObjective G 0 0 hGsymm (0 : EuclideanSpace ℝ (Fin 2))
  have hStoredGradZero : A.g k = 0 := by
    rw [← A.gradient_eq k]
    exact hGradZero
  have hDirZero : A.d k = 0 := by
    rw [h_direction k, steepestDescentDirection, hGradZero]
    simp
  -- The stored descent-direction axiom forbids the zero direction at a stationary iterate.
  have hImpossible : ¬ inner ℝ (A.g k) (A.d k) < 0 := by
    simp [hStoredGradZero, hDirZero]
  exact hImpossible (A.descentDirection k)

/-- Helper for Chapter03 Exercise 3.2: on a nonzero iterate of a centered positive-definite
quadratic, the Chapter 2 step size agrees with the closed-form exact steepest-descent step. -/
theorem generalMethod_stepSize_eq_closedForm_of_ne_zero
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G.PosDef)
    (A : GeneralUnconstrainedOptimizationMethod 2 (quadraticObjective G 0 0))
    (h_direction :
      ∀ k,
        A.d k = steepestDescentDirection (quadraticObjective G 0 0) (A k))
    {k : ℕ} (hk : A k ≠ 0) :
    A.α k =
      dotProduct (G.mulVec (A k)) (G.mulVec (A k)) /
        dotProduct (G.mulVec (A k)) (G.mulVec (G.mulVec (A k))) := by
  let f := quadraticObjective G 0 0
  let g : EuclideanSpace ℝ (Fin 2) := Matrix.toEuclideanLin G (A k)
  let a : ℝ := dotProduct g g
  let c : ℝ := dotProduct g (G.mulVec g)
  let αcf : ℝ := a / c
  let _ : Invertible G := hG.isUnit.invertible
  have hClosedForm :
      IsExactLineSearchStepOnNonnegativeRay
        f
        (A k)
        (steepestDescentDirection f (A k))
        αcf := by
    -- The closed-form textbook step is exact on every nonstationary centered quadratic iterate.
    simpa [f, g, a, c, αcf] using
      centeredQuadraticObjective_closedForm_exactLineSearch (G := G) hG hk
  have hAlphaCf_nonneg : 0 ≤ αcf := hClosedForm.nonneg
  have hAlphaCf_mem : αcf ∈ Set.Ici (0 : ℝ) := by
    simpa [Set.mem_Ici] using hAlphaCf_nonneg
  have hOptimal :
      lineSearchObjective f (A k) (steepestDescentDirection f (A k)) (A.α k) ≤
        lineSearchObjective f (A k) (steepestDescentDirection f (A k)) αcf := by
    -- The Chapter 2 step is optimal among all nonnegative trial steps, so in particular against
    -- the closed-form candidate.
    have hMinOn :
        ∀ β ∈ Set.Ici (0 : ℝ),
          lineSearchObjective f (A k) (A.d k) (A.α k) ≤
            lineSearchObjective f (A k) (A.d k) β := by
      exact isMinOn_iff.mp (A.exactLineSearch k)
    simpa [h_direction k] using hMinOn αcf hAlphaCf_mem
  have hg_ne : g ≠ 0 := by
    -- Positive definiteness makes `G` invertible, so `G (A k) = 0` would force `A k = 0`.
    intro hg_zero
    apply hk
    have h0 := congrArg (Matrix.toEuclideanLin G⁻¹) hg_zero
    simpa [g, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] using h0
  have hc_pos : 0 < c := by
    -- The completed-square coefficient is strictly positive away from the stationary point.
    simpa [c, g] using hG.dotProduct_mulVec_pos (x := g.ofLp) (by simpa using hg_ne)
  have hProfileAtAlpha :
      lineSearchObjective f (A k) (steepestDescentDirection f (A k)) (A.α k) =
        quadraticObjective G 0 0 (A k) - a ^ (2 : ℕ) / (2 * c) +
          (c / 2) * (A.α k - αcf) ^ (2 : ℕ) := by
    -- The line-search profile is a completed square centered at the closed-form step.
    simpa [f, g, a, c, αcf] using
      centeredQuadraticObjective_lineSearchProfile_eq_completedSquare
        (G := G) hG hk (A.α k)
  have hProfileAtClosedForm :
      lineSearchObjective f (A k) (steepestDescentDirection f (A k)) αcf =
        quadraticObjective G 0 0 (A k) - a ^ (2 : ℕ) / (2 * c) := by
    have hc_ne : c ≠ 0 := hc_pos.ne'
    -- At the center of the completed square, the correction term vanishes.
    calc
      lineSearchObjective f (A k) (steepestDescentDirection f (A k)) αcf
          = quadraticObjective G 0 0 (A k) - a ^ (2 : ℕ) / (2 * c) +
              (c / 2) * (αcf - αcf) ^ (2 : ℕ) := by
                simpa [f, g, a, c, αcf] using
                  centeredQuadraticObjective_lineSearchProfile_eq_completedSquare
                    (G := G) hG hk αcf
      _ = quadraticObjective G 0 0 (A k) - a ^ (2 : ℕ) / (2 * c) := by
            simp [hc_ne]
  have hCorrection_nonpos : (c / 2) * (A.α k - αcf) ^ (2 : ℕ) ≤ 0 := by
    -- Comparing the accepted step against the closed-form step leaves only the square term.
    rw [hProfileAtAlpha, hProfileAtClosedForm] at hOptimal
    nlinarith
  have hCorrection_nonneg : 0 ≤ (c / 2) * (A.α k - αcf) ^ (2 : ℕ) := by
    have hSquare_nonneg : 0 ≤ (A.α k - αcf) ^ (2 : ℕ) := by
      positivity
    nlinarith [hc_pos, hSquare_nonneg]
  have hCorrection_zero : (c / 2) * (A.α k - αcf) ^ (2 : ℕ) = 0 := by
    linarith
  have hSquareZero : (A.α k - αcf) ^ (2 : ℕ) = 0 := by
    nlinarith [hc_pos, hCorrection_zero]
  have hAlphaEq : A.α k = αcf := by
    nlinarith [hSquareZero]
  simpa [g, a, c, αcf, Matrix.toEuclideanLin_apply] using hAlphaEq

/-- Helper for Chapter03 Exercise 3.2: a Chapter 2 exact-line-search method that already uses the
steepest-descent direction is a genuine steepest-descent sequence for the centered quadratic. -/
theorem generalMethod_isSteepestDescentSequence
    {G : Matrix (Fin 2) (Fin 2) ℝ} (hG : G.PosDef)
    (A : GeneralUnconstrainedOptimizationMethod 2 (quadraticObjective G 0 0))
    (h_direction :
      ∀ k,
        A.d k = steepestDescentDirection (quadraticObjective G 0 0) (A k)) :
    IsSteepestDescentSequence (quadraticObjective G 0 0) A A.α := by
  intro k
  have hk : A k ≠ 0 := generalMethod_iterate_ne_zero hG A h_direction k
  have hAlpha :
      A.α k =
        dotProduct (G.mulVec (A k)) (G.mulVec (A k)) /
          dotProduct (G.mulVec (A k)) (G.mulVec (G.mulVec (A k))) := by
    simpa using generalMethod_stepSize_eq_closedForm_of_ne_zero hG A h_direction hk
  refine ⟨?_, ?_⟩
  · -- Replace the Chapter 2 step by the closed-form exact line-search step from Chapter 3.
    simpa [hAlpha] using centeredQuadraticObjective_closedForm_exactLineSearch (G := G) hG hk
  · -- The Chapter 2 iterate update is exactly the steepest-descent update after rewriting the
    -- stored direction.
    calc
      A (k + 1) = A k + A.α k • A.d k := by
        simpa using A.update k
      _ = steepestDescentStep (quadraticObjective G 0 0) (A k) (A.α k) := by
        rw [h_direction k, steepestDescentStep]

/-- Chapter03 Exercise 3.2 (1): for `f(x) = (1 / 2) * (x 0 ^ 2 + 9 * x 1 ^ 2)`, the
steepest-descent specialization of a Chapter 2 exact-line-search method with canonical search
direction `steepestDescentDirection` satisfies the explicit linear `G`-energy bound with
contraction factor `4 / 5`. -/
theorem steepestDescent_diagQuadraticOneNine_energyLinearRate
    (A :
      GeneralUnconstrainedOptimizationMethod 2
        (quadraticObjective diagMatrixOneNine 0 0))
    (h_direction :
      ∀ k,
        A.d k =
          steepestDescentDirection (quadraticObjective diagMatrixOneNine 0 0) (A k))
    (k : ℕ) :
    ellipsoidNorm diagMatrixOneNine (A k) ≤
      (((4 : ℝ) / 5) ^ k) * ellipsoidNorm diagMatrixOneNine (A 0) := by
  have hSeq :
      IsSteepestDescentSequence (quadraticObjective diagMatrixOneNine 0 0) A A.α := by
    -- Convert the Chapter 2 run to the Chapter 3 steepest-descent interface once and for all.
    exact generalMethod_isSteepestDescentSequence diagMatrixOneNine_posDef A h_direction
  have hCore :
      ellipsoidNorm diagMatrixOneNine (A.x k).ofLp ≤
        ((((9 : ℝ) - 1) / (9 + 1)) ^ k) * ellipsoidNorm diagMatrixOneNine (A.x 0).ofLp := by
    exact
      steepestDescentQuadratic_energy_geometric_bound_core
        (G := diagMatrixOneNine) (lambdaMax := 9) (lambdaMin := 1)
        diagMatrixOneNine_posDef diagMatrixOneNine_eigenvalueMax diagMatrixOneNine_eigenvalueMin
        hSeq k
  have hRate :
      (((9 : ℝ) - 1) / (9 + 1)) = (4 : ℝ) / 5 := by
    norm_num
  -- The imported geometric bound specializes to the textbook contraction factor `4 / 5`.
  change
    ellipsoidNorm diagMatrixOneNine (A.x k).ofLp ≤
      (((4 : ℝ) / 5) ^ k) * ellipsoidNorm diagMatrixOneNine (A.x 0).ofLp
  calc
    ellipsoidNorm diagMatrixOneNine (A.x k).ofLp ≤
        ((((9 : ℝ) - 1) / (9 + 1)) ^ k) * ellipsoidNorm diagMatrixOneNine (A.x 0).ofLp := hCore
    _ = (((4 : ℝ) / 5) ^ k) * ellipsoidNorm diagMatrixOneNine (A.x 0).ofLp := by
          rw [hRate]

/-- Chapter03 Exercise 3.2 (2): for `f(x) = (1 / 2) * (x 0 ^ 2 + 10000 * x 1 ^ 2)`, the
steepest-descent specialization of a Chapter 2 exact-line-search method with canonical search
direction `steepestDescentDirection` satisfies the explicit linear `G`-energy bound with
contraction factor `9999 / 10001`. -/
theorem steepestDescent_diagQuadraticOneTenThousand_energyLinearRate
    (A :
      GeneralUnconstrainedOptimizationMethod 2
        (quadraticObjective diagMatrixOneTenThousand 0 0))
    (h_direction :
      ∀ k,
        A.d k =
          steepestDescentDirection
            (quadraticObjective diagMatrixOneTenThousand 0 0)
            (A k))
    (k : ℕ) :
    ellipsoidNorm diagMatrixOneTenThousand (A k) ≤
      (((9999 : ℝ) / 10001) ^ k) * ellipsoidNorm diagMatrixOneTenThousand (A 0) := by
  have hSeq :
      IsSteepestDescentSequence
        (quadraticObjective diagMatrixOneTenThousand 0 0) A A.α := by
    -- Convert the Chapter 2 run to the Chapter 3 steepest-descent interface once and for all.
    exact
      generalMethod_isSteepestDescentSequence
        diagMatrixOneTenThousand_posDef A h_direction
  have hCore :
      ellipsoidNorm diagMatrixOneTenThousand (A.x k).ofLp ≤
        ((((10000 : ℝ) - 1) / (10000 + 1)) ^ k) *
          ellipsoidNorm diagMatrixOneTenThousand (A.x 0).ofLp := by
    exact
      steepestDescentQuadratic_energy_geometric_bound_core
        (G := diagMatrixOneTenThousand) (lambdaMax := 10000) (lambdaMin := 1)
        diagMatrixOneTenThousand_posDef diagMatrixOneTenThousand_eigenvalueMax
        diagMatrixOneTenThousand_eigenvalueMin hSeq k
  have hRate :
      (((10000 : ℝ) - 1) / (10000 + 1)) = (9999 : ℝ) / 10001 := by
    norm_num
  -- The imported geometric bound specializes to the textbook contraction factor `9999 / 10001`.
  change
    ellipsoidNorm diagMatrixOneTenThousand (A.x k).ofLp ≤
      (((9999 : ℝ) / 10001) ^ k) * ellipsoidNorm diagMatrixOneTenThousand (A.x 0).ofLp
  calc
    ellipsoidNorm diagMatrixOneTenThousand (A.x k).ofLp ≤
        ((((10000 : ℝ) - 1) / (10000 + 1)) ^ k) *
          ellipsoidNorm diagMatrixOneTenThousand (A.x 0).ofLp := hCore
    _ = (((9999 : ℝ) / 10001) ^ k) * ellipsoidNorm diagMatrixOneTenThousand (A.x 0).ofLp := by
          rw [hRate]
