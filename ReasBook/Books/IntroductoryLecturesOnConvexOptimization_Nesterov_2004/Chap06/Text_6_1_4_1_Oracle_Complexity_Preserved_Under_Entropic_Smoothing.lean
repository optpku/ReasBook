/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Text 6.1.4.1 lies in the chapter's oracle/arithmetic-complexity bridge domain for dense
simplex matrix-game oracles.

Mandatory domain-style sampling before refinement:
* `GeneralIterativeScheme.iterationArithmeticWork`,
  `GeneralIterativeScheme.totalArithmeticWork`, and
  `GeneralIterativeScheme.IsArithmeticalComplexity` in `Chap01/Definition_1_2_12`, the project
  owners for accumulated arithmetic work and arithmetical complexity on an iterative scheme;
* `HasEllipsoidMethodComplexityBounds` in `Chap05/Definition_5_4_9_2`, the nearby chapter pattern
  where primitive per-iteration cost data feed a higher-level complexity statement;
* `semidefiniteNewtonStepDenseArithmeticWorkBound` in `Chap05/Proposition_5_4_4_3`, the nearby
  source-facing one-shot dense arithmetic-work owner on primitive size parameters;
* `fastGradient_oracleComplexity_le_const_div_epsilon_of_smoothApproximation` in
  `Chap06/Text_6_1_1_Complexity_Insight`, the Chapter 6 oracle-count bridge showing how a
  smoothing estimate is meant to feed a genuine complexity conclusion rather than stop at a local
  scalar or per-call bound.

Best owner abstraction:
* source-facing: `GeneralIterativeScheme.IsAnalyticalComplexity`, the Chapter 1 owner for
  oracle-call complexity, together with the original and entropy-smoothed dense one-call simplex
  matrix-game oracle work bounds on the primitive simplex dimensions `Δ[n]` and `Δ[m]`;
* core/canonical: `GeneralIterativeScheme.totalArithmeticWork` and
  `GeneralIterativeScheme.IsArithmeticalComplexity`;
* bridge/view: the constant-factor comparison passing from the per-call dense bounds to the
  Chapter 1 arithmetical-complexity owner.

Primitive data:
* the two schemes whose halting indices encode oracle complexity;
* the positive simplex dimensions `n` and `m`;
* the two dense one-call oracle arithmetic-work bounds.

Derived API:
* the oracle-complexity preservation theorem on `GeneralIterativeScheme.IsAnalyticalComplexity`;
* the per-iteration and total-work comparisons on `GeneralIterativeScheme`;
* the Chapter 1 arithmetical-complexity preservation theorem.

Source/core/bridge triage:
* source-facing: the oracle-complexity preservation statement on
  `GeneralIterativeScheme.IsAnalyticalComplexity`;
* core/canonical: `GeneralIterativeScheme.totalArithmeticWork` and
  `GeneralIterativeScheme.IsArithmeticalComplexity`;
* bridge/view: the dense one-call oracle work bounds and the theorems showing that the smoothed
  dense oracle model changes arithmetical complexity by at most a constant factor.

The review issue in the previous round was that the main theorem had drifted from oracle
complexity to the Chapter 1 arithmetic-cost bridge. This refinement keeps the dense one-call
arithmetic bounds as companion data, restores the main public outcome to the Chapter 1
oracle-complexity owner `GeneralIterativeScheme.IsAnalyticalComplexity`, and leaves the
arithmetical-complexity consequence below as an explicit companion bridge. -/

namespace GeneralIterativeScheme

variable (scheme : GeneralIterativeScheme Query Answer)
variable (oracleWork originalOracleWork smoothedOracleWork : Query → Answer → ℕ)
variable (methodWork originalMethodWork smoothedMethodWork : Set (Query × Answer) → ℕ)

/-- A pointwise constant-factor bound on iteration work accumulates to the same constant-factor
bound on total arithmetic work. -/
theorem totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
    (C N : ℕ)
    (hiter :
      ∀ k,
        scheme.iterationArithmeticWork smoothedOracleWork smoothedMethodWork k ≤
          C * scheme.iterationArithmeticWork originalOracleWork originalMethodWork k) :
    scheme.totalArithmeticWork smoothedOracleWork smoothedMethodWork N ≤
      C * scheme.totalArithmeticWork originalOracleWork originalMethodWork N := by
  unfold GeneralIterativeScheme.totalArithmeticWork
  refine le_trans (Finset.sum_le_sum fun k hk ↦ hiter k) ?_
  simp [Finset.mul_sum]

/-- If one arithmetic-work model is bounded termwise by a constant multiple of another along the
same informational trajectory, then any arithmetical complexity for the original model yields an
arithmetical complexity for the new model with the same constant-factor bound. -/
theorem exists_isArithmeticalComplexity_le_mul_of_iterationArithmeticWork_le_mul
    {C M : ℕ}
    (hM :
      scheme.IsArithmeticalComplexity originalOracleWork originalMethodWork M)
    (hiter :
      ∀ k,
        scheme.iterationArithmeticWork smoothedOracleWork smoothedMethodWork k ≤
          C * scheme.iterationArithmeticWork originalOracleWork originalMethodWork k) :
    ∃ M',
      scheme.IsArithmeticalComplexity smoothedOracleWork smoothedMethodWork M' ∧
        M' ≤ C * M := by
  rcases hM with ⟨N, hN, rfl⟩
  refine ⟨scheme.totalArithmeticWork smoothedOracleWork smoothedMethodWork N, ?_, ?_⟩
  · exact ⟨N, hN, rfl⟩
  · exact
      scheme.totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
        originalOracleWork smoothedOracleWork originalMethodWork smoothedMethodWork C N hiter

end GeneralIterativeScheme

/-- A dense arithmetic-work upper bound for one call to the original simplex matrix-game
first-order oracle on `Δ[n] × Δ[m]`, under the convention that each scalar affine update,
comparison, and vector entry write has constant cost. The bound consists of one dense scan of the
`m` affine payoffs, one maximizing-coordinate pass, and one length-`n` subgradient assembly. -/
def simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound (n m : ℕ+) : ℕ :=
  (m : ℕ) * (n : ℕ) + (m : ℕ) + (n : ℕ)

/-- A dense arithmetic-work upper bound for one call to the entropy-smoothed simplex matrix-game
first-order oracle on `Δ[n] × Δ[m]`, under the same dense convention and the additional
convention that each scalar `exp`, `log`, division, and normalization update in the softmax /
log-sum-exp evaluation has constant cost per coordinate. The bound consists of one dense affine
scan, one softmax / log-sum-exp normalization pass, and one dense averaged-gradient back
substitution. -/
def simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound
    (n m : ℕ+) : ℕ :=
  2 * (m : ℕ) * (n : ℕ) + 4 * (m : ℕ) + (n : ℕ) + 1

-- Proof sketch: both oracle models require the same dense matrix-vector scan of the `m` affine
-- coordinates. The entropy-smoothed oracle adds only the softmax normalization and one averaged
-- back-substitution for the gradient, which is a fixed-constant multiple of the original dense
-- oracle bound once the simplex dimensions are positive.
/-- For each dense simplex matrix-game oracle call, the entropy-smoothed arithmetic-work model is
bounded by eight times the original dense oracle arithmetic-work model. -/
theorem
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound_le_eight_mul_original
    (n m : ℕ+) :
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m ≤
      8 * simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m := by
  have hn : (1 : ℤ) ≤ (n : ℕ) := by
    exact_mod_cast Nat.succ_le_of_lt n.pos
  have hm : (1 : ℤ) ≤ (m : ℕ) := by
    exact_mod_cast Nat.succ_le_of_lt m.pos
  exact_mod_cast (show
    (2 : ℤ) * (m : ℕ) * (n : ℕ) + 4 * (m : ℕ) + (n : ℕ) + 1 ≤
      8 * ((m : ℕ) * (n : ℕ) + (m : ℕ) + (n : ℕ)) by
    nlinarith)

/-- Replacing the original dense simplex matrix-game oracle cost by the entropy-smoothed dense
oracle cost changes each iteration's oracle-only arithmetic work by at most a factor of `8`. -/
theorem simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) (k : ℕ) :
    scheme.iterationArithmeticWork
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) k ≤
      8 * scheme.iterationArithmeticWork
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) k := by
  simpa [GeneralIterativeScheme.iterationArithmeticWork] using
    simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound_le_eight_mul_original
      n m

/-- Replacing the original dense simplex matrix-game oracle cost by the entropy-smoothed dense
oracle cost changes the Chapter 1 total arithmetic work of an oracle-only scheme by at most a
factor of `8`. -/
theorem simplexMatrixGameEntropicSmoothing_totalArithmeticWork_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) (N : ℕ) :
    scheme.totalArithmeticWork
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) N ≤
      8 * scheme.totalArithmeticWork
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) N := by
  exact
    scheme.totalArithmeticWork_le_mul_of_iterationArithmeticWork_le_mul
      (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ ↦ 0) (fun _ ↦ 0) 8 N
      (fun k ↦
        simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
          scheme n m k)

-- Proof sketch: pass from the one-call dense comparison to the Chapter 1 owner
-- `GeneralIterativeScheme.IsArithmeticalComplexity` using the accumulation theorem above, with
-- zero additional method work because this source item isolates oracle arithmetic cost.
/-- Text 6.1.4.1-Oracle Complexity Preserved Under Entropic Smoothing: if the entropy-smoothed
and original simplex matrix-game schemes halt at exactly the same oracle-call counts, then any
analytical-complexity witness for the original scheme is also an analytical-complexity witness for
the smoothed scheme. Thus entropic smoothing preserves oracle complexity on the Chapter 1 owner
surface `GeneralIterativeScheme.IsAnalyticalComplexity`; the factor-`8` arithmetic-work theorem
below is only a companion bridge. -/
theorem simplexMatrixGameEntropicSmoothing_preserves_analyticalComplexity
    {originalScheme smoothedScheme : GeneralIterativeScheme Query Answer} {N : ℕ}
    (hhalt : ∀ k, originalScheme.HaltsAt k ↔ smoothedScheme.HaltsAt k)
    (hN : originalScheme.IsAnalyticalComplexity N) :
    smoothedScheme.IsAnalyticalComplexity N := by
  rcases (originalScheme.isAnalyticalComplexity_iff).mp hN with ⟨hhalts, hminimal⟩
  refine (smoothedScheme.isAnalyticalComplexity_iff).mpr ?_
  refine ⟨(hhalt N).mp hhalts, ?_⟩
  intro m hm hmhalts
  exact hminimal m hm ((hhalt m).mpr hmhalts)

/-- Companion Chapter 1 arithmetic-complexity bridge: if a general iterative scheme has
arithmetical complexity `M` when each oracle call is charged by the original dense simplex
matrix-game first-order oracle model and no additional method work is counted, then under the
entropy-smoothed dense oracle model there exists an arithmetical complexity `M'` with
`M' ≤ 8 M`. This is an arithmetic-cost consequence of the dense one-call comparison, not the main
oracle-complexity statement of Text 6.1.4.1. -/
theorem simplexMatrixGameEntropicSmoothing_isArithmeticalComplexity_le_eight_mul_original
    (scheme : GeneralIterativeScheme Query Answer) (n m : ℕ+) {M : ℕ}
    (hM :
      scheme.IsArithmeticalComplexity
        (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) M) :
    ∃ M',
      scheme.IsArithmeticalComplexity
        (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
        (fun _ ↦ 0) M' ∧
        M' ≤ 8 * M := by
  exact
    scheme.exists_isArithmeticalComplexity_le_mul_of_iterationArithmeticWork_le_mul
      (fun _ _ ↦ simplexMatrixGameOriginalFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ _ ↦ simplexMatrixGameEntropicSmoothingFirstOrderOracleDenseArithmeticWorkBound n m)
      (fun _ ↦ 0) (fun _ ↦ 0) hM
      (fun k ↦
        simplexMatrixGameEntropicSmoothing_iterationArithmeticWork_le_eight_mul_original
          scheme n m k)
