module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_4_Counterexample_in_every_dimension_n_ge2
public import ReasLib.Optimization.DFP.GlobalConvergence
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedTransport
public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedIdentityInitialization
public import ReasLib.Optimization.DFP.WolfeCounterexample.AutomaticMatrixIdentityLiminf

public section

namespace DFP

/-- TASK-11: The paper-range strong-Wolfe counterexample is available in every
finite dimension `n` with `2 ≤ n`, while retaining the exact Hessian bounds
`(1 / 2, 3 / 2)`. -/
theorem existsStrongWolfeCounterexample_of_parameterRange
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    Nonempty (StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂) := by
  exact existsStrongWolfeCounterexample_of_dimension_ge_two n hn
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-11 Main theorem: for every pair in the paper's Wolfe range, the
global weak-Wolfe convergence predicate is false. -/
theorem main_not_globalWeakWolfeConvergence_of_parameterRange
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁)
    (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ¬ GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange 2 hdimension
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_globalWeakWolfeConvergenceAt_of_counterexample
    counterexample.toWolfeCounterexample hdimension hlower hupper

/-- TASK-11: The preceding negative convergence theorem is uniform over all
coefficient pairs satisfying `0 < c₁ < 2 / 3` and `2 / 3 ≤ c₂ < 1`. -/
theorem main_not_globalWeakWolfeConvergence_forall_parameterRange :
    ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
      (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
      ¬ GlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro c₁ c₂ hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact main_not_globalWeakWolfeConvergence_of_parameterRange
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-15: The same paper-range counterexample refutes the level-set version
of the fixed-coefficient global-convergence predicate.  The explicit
containment field is supplied by the Armijo/DFP descent bridge. -/
theorem main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁)
    (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ¬ LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange 2 hdimension
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_levelSetGlobalWeakWolfeConvergenceAt_of_counterexample
    counterexample.toWolfeCounterexample hdimension hlower hupper

/-- TASK-15: The level-set global-convergence predicate is false for every
coefficient pair in the paper's stated range. -/
theorem main_not_levelSetGlobalWeakWolfeConvergence_forall_parameterRange :
    ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
      (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
      ¬ LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂ := by
  intro c₁ c₂ hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/-- TASK-15: A named positive predicate for convergence under the paper's
coefficient range, included so the final theorem can be checked directly in
the same negation form as the mathematical question. -/
def PaperRangeGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
    (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
    GlobalWeakWolfeConvergenceAt c₁ c₂

/-- TASK-15: A direct negation of the positive convergence predicate
quantified over the paper's coefficient range. -/
theorem not_PaperRangeGlobalWeakWolfeConvergence :
    ¬ PaperRangeGlobalWeakWolfeConvergence := by
  intro hGlobal
  have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁Upper : (1 / 4 : ℝ) < 2 / 3 := by norm_num
  have hc₂Lower : (2 / 3 : ℝ) ≤ 3 / 4 := by norm_num
  have hc₂Upper : (3 / 4 : ℝ) < 1 := by norm_num
  exact main_not_globalWeakWolfeConvergence_of_parameterRange
    hc₁ hc₁Upper hc₂Lower hc₂Upper (hGlobal _ _ hc₁ hc₁Upper hc₂Lower hc₂Upper)

/-- TASK-15: The level-set formulation also has a direct paper-range
negation predicate. -/
def PaperRangeLevelSetGlobalWeakWolfeConvergence : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → c₁ < 2 / 3 →
    (2 / 3 : ℝ) ≤ c₂ → c₂ < 1 →
    LevelSetGlobalWeakWolfeConvergenceAt c₁ c₂

/-- TASK-15: The level-set paper-range convergence predicate is false. -/
theorem not_PaperRangeLevelSetGlobalWeakWolfeConvergence :
    ¬ PaperRangeLevelSetGlobalWeakWolfeConvergence := by
  intro hGlobal
  have hc₁ : (0 : ℝ) < 1 / 4 := by norm_num
  have hc₁Upper : (1 / 4 : ℝ) < 2 / 3 := by norm_num
  have hc₂Lower : (2 / 3 : ℝ) ≤ 3 / 4 := by norm_num
  have hc₂Upper : (3 / 4 : ℝ) < 1 := by norm_num
  exact main_not_levelSetGlobalWeakWolfeConvergence_of_parameterRange
    hc₁ hc₁Upper hc₂Lower hc₂Upper
    (hGlobal _ _ hc₁ hc₁Upper hc₂Lower hc₂Upper)

/-- TASK-11: The identity-initialized strong-Wolfe corollary is exposed with
the explicit witness, factorization, and Loewner/gradient bounds required by
the operator-level normalization theorem. -/
theorem identityInitializedStrongWolfe_of_parameterRange
    (n : ℕ) {c₁ c₂ a b q : ℝ}
    (counterexample : StrongWolfeCounterexample
      (Fin n) (1 / 2) (3 / 2) c₁ c₂)
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (factor : (Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
        (counterexample.iteration.inverseHessian 0) =
      L.toContinuousLinearMap.pushforward 1)
    (lowerMap : a • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pullback 1)
    (upperMap : L.toContinuousLinearMap.pullback 1 ≤
      b • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hq : 0 < q)
    (gradientMapLower : q • (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) ≤ L.toContinuousLinearMap.pushforward 1) :
    Nonempty (WolfeCounterexample.IdentityInitializedStrongWolfeOperatorCertificate
      (Fin n) ((1 / 2 : ℝ) * a) ((3 / 2 : ℝ) * b) c₁ c₂) := by
  exact WolfeCounterexample.identityInitializedStrongWolfe_of_dimension_ge_two
    n counterexample hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
    L factor lowerMap upperMap hq gradientMapLower

/-- TASK-15: For every pair in the paper's coefficient range and every
dimension `n ≥ 2`, the identity-initialization corollary has a genuine
matrix `InverseIteration` presentation.  The positive ordered Hessian bounds
and the `liminf` conclusion are generated automatically from the initial
positive-definite matrix. -/
theorem existsMatrixIdentityLiminfStrongWolfe_of_parameterRange
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      Nonempty (WolfeCounterexample.MatrixIdentityLiminfStrongWolfeCertificate
        n m M c₁ c₂) := by
  obtain ⟨counterexample⟩ :=
    existsStrongWolfeCounterexample_of_parameterRange n hn
      hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  exact WolfeCounterexample.exists_matrixIdentityLiminfStrongWolfe_of_initialPosDef
    hn counterexample hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one

/- Legacy fixed-parameter weak-Wolfe aliases below remain available for
compatibility; the released paper-range statements are declared above. -/
/-- TASK-06 helper: the fixed-parameter weak-Wolfe certificate is available in
every finite dimension `n` with `2 ≤ n`. -/
theorem existsWeakWolfeCounterexample_fixedParameters (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WeakWolfeCounterexample (Fin n)) :=
  existsWeakWolfeCounterexample n hn

/-- TASK-06 Main theorem: at the fixed weak-Wolfe coefficients `(1 / 4, 3 / 4)`,
the global convergence predicate is false. -/
theorem main_not_globalWeakWolfeConvergence_fixedParameters :
    ¬ GlobalWeakWolfeConvergenceAt (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ := existsWeakWolfeCounterexample 2 hdimension
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact not_globalWeakWolfeConvergenceAt_of_counterexample
    counterexample hdimension hlower hupper

/-- TASK-06 corollary: one fixed weak-Wolfe counterexample refutes the universal
global convergence claim over all admissible coefficient pairs. -/
theorem not_universalGlobalWeakWolfeConvergence_fixedParameters :
    ¬ UniversalGlobalWeakWolfeConvergence := by
  have hdimension : 2 ≤ (2 : ℕ) := by
    norm_num
  obtain ⟨counterexample⟩ := existsWeakWolfeCounterexample 2 hdimension
  have hlower : (0 : ℝ) < 1 / 2 := by
    norm_num
  have hupper : (1 / 2 : ℝ) ≤ 3 / 2 := by
    norm_num
  have hc₁ : (0 : ℝ) < 1 / 4 := by
    norm_num
  have hc₁₂ : (1 / 4 : ℝ) < 3 / 4 := by
    norm_num
  have hc₂ : (3 / 4 : ℝ) < 1 := by
    norm_num
  exact not_universalGlobalWeakWolfeConvergence_of_counterexample
    counterexample hdimension hlower hupper hc₁ hc₁₂ hc₂

end DFP
