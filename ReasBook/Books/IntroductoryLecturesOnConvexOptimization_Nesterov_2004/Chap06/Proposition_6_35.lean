/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open NormedSpace
open RealSymmetricMatrixSpace
open scoped BigOperators RealSymmetricMatrixSpace
open scoped RightActions

/- Proposition 6.35 lies in the chapter's symmetric-matrix spectral-smoothing / log-sum-exp
domain.

Sampled owner-style declarations:
- Chapter 5 `𝕊^n` and `RealSymmetricMatrixSpace.eigenvalues`, the canonical real symmetric-matrix
  carrier and ordered eigenvalue owner;
- Chapter 5 `RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup`,
  `RealSymmetricMatrixSpace.symmetricMatrixNormedSpace`, and
  `RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace`, the inherited normed-space structure on
  `𝕊^n`;
- Chapter 5 `logSumExp`, the intrinsic finite-family log-sum-exp owner, specialized here to
  `EuclideanSpace ℝ (Fin n)`;
- mathlib's scoped `Matrix.Norms.L2Operator` norm, the canonical ambient matrix operator norm;
- mathlib `Matrix.IsHermitian.eigenvalues`, already packaged by the Chapter 5 owner `eigenvalues`.

Best owner abstraction:
- source-facing: the entropy smoothing on `𝕊^n` and the Hessian quadratic-form bound;
- core/canonical: `𝕊^n`, `RealSymmetricMatrixSpace.eigenvalues`, `logSumExp`, and the ambient
  matrix `L²` operator norm;
- bridge/view: the spectral-`∞` interpretation of that ambient operator norm for symmetric
  matrices, and the `n = 0` reduction of log-sum-exp to the empty sum.

Primitive data:
- `n : ℕ`
- `X : 𝕊^n`

Derived API:
- the entropy smoothing `X ↦ log (∑ i, exp (λᵢ(X)))`;
- Proposition 6.35's smoothness and Hessian bound.

Source/core/bridge triage:
- source-facing: `entropySmoothing` and the Hessian quadratic-form estimate;
- core/canonical: `𝕊^n`, `eigenvalues`, `logSumExp`, and the ambient matrix `L²` operator norm;
- bridge/view: the textbook spectral interpretation of that operator norm on symmetric matrices.

The previous version also rebuilt finite-dimensional `ℓ_p` and spectral-norm owners locally.
Those are already owned by the chapter's `EuclideanSpace` / `WithLp` norm layer and by the
canonical ambient matrix operator norm, so this file now keeps only the new Chapter 6
entropy-smoothing owner and uses the established norm surfaces directly.
-/

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 6.35: use the Frobenius normed-group structure on ambient matrices
when differentiating matrix-valued maps. -/
local instance proposition635AmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 6.35: scalar multiplication on ambient matrices is measured with the
Frobenius norm during the local calculus arguments. -/
local instance proposition635AmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 6.35: the ambient matrix ring carries the Frobenius-compatible normed
ring structure used by the matrix-exponential calculus API. -/
local instance proposition635AmbientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Proposition 6.35: the ambient matrix algebra over `ℝ` carries the Frobenius
normed-algebra structure used in the local analytic arguments. -/
local instance proposition635AmbientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/-- The entropy-smoothing spectral function `E(X) = log (∑ᵢ exp (λᵢ(X)))` on `𝕊^n`. -/
def entropySmoothing (X : 𝕊^n) : ℝ :=
  logSumExp (WithLp.toLp 2 (eigenvalues X))

/-- Evaluating `entropySmoothing` at `X` gives `log (∑ᵢ exp (λᵢ(X)))`. -/
theorem entropySmoothing_apply (X : 𝕊^n) :
    entropySmoothing X =
      Real.log (∑ i : Fin n, Real.exp (eigenvalues X i)) := by
  rw [entropySmoothing, logSumExp_apply]

-- Proof sketch: diagonalize the symmetric matrix `X`, rewrite the ambient matrix exponential as
-- the real functional calculus of `Real.exp`, and then evaluate the trace on the diagonal model.
/-- Helper for Proposition 6.35: the trace of the matrix exponential is the sum of the
exponentials of the ordered eigenvalues. -/
theorem trace_exp_eq_sum_exp_eigenvalues (X : SymmMat) :
    Matrix.trace (exp (X : Mat)) =
      ∑ i : Fin n, Real.exp (eigenvalues X i) := by
  let hX := RealSymmetricMatrixSpace.isHermitian X
  have hself : IsSelfAdjoint (X : Mat) := by
    simpa [Matrix.IsSelfAdjoint, Matrix.IsHermitian] using hX
  -- Rewrite the matrix exponential through the real functional calculus and evaluate it on the
  -- diagonal spectral model of `X`.
  conv_lhs =>
    rw [← CFC.real_exp_eq_normedSpace_exp (a := (X : Mat)) hself]
    rw [hX.cfc_eq Real.exp, Matrix.IsHermitian.cfc,
      Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
      Matrix.trace_diagonal]
  simp

-- Proof sketch: combine the source-facing eigenvalue formula for `entropySmoothing` with the
-- trace-exponential bridge just proved above.
/-- Helper for Proposition 6.35: `entropySmoothing` agrees with the textbook trace-exponential
formula `log (Trace (exp X))`. -/
theorem entropySmoothing_eq_log_trace_exp (X : SymmMat) :
    entropySmoothing X = Real.log (Matrix.trace (exp (X : Mat))) := by
  -- Replace the eigenvalue sum by the canonical trace of the matrix exponential.
  rw [entropySmoothing_apply, trace_exp_eq_sum_exp_eigenvalues]

/-- Helper for Proposition 6.35: in dimension `0`, the entropy smoothing is the constant zero
map. -/
theorem entropySmoothing_zero_dim_eq_zero :
    (entropySmoothing : 𝕊^0 → ℝ) = fun _ ↦ (0 : ℝ) := by
  -- In dimension `0`, the spectral sum is empty, so `logSumExp` reduces to `Real.log 0 = 0`.
  funext X
  simp [entropySmoothing, logSumExp]

/-- Helper for Proposition 6.35: the dimension-zero branch of the Hessian bound is trivial because
the source map is constant. -/
theorem entropySmoothing_contDiff_and_hessianQuadraticForm_le_zero :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^0 → ℝ) ∧
      ∀ X H : 𝕊^0,
        (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^0 → ℝ) X) ![H, H] ≤
          (‖((H : Matrix (Fin 0) (Fin 0) ℝ))‖) ^ (2 : ℕ) := by
  constructor
  · -- Rewriting to the constant map puts the smoothness claim on the standard `C²` surface.
    rw [entropySmoothing_zero_dim_eq_zero]
    simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : 𝕊^0 ↦ (0 : ℝ)))
  · intro X H
    -- The Hessian of a constant map vanishes, and the ambient operator norm is nonnegative.
    rw [entropySmoothing_zero_dim_eq_zero]
    simp

-- Proof sketch: after rewriting the trace as a sum of positive exponential eigenvalue terms,
-- one positive summand forces the whole trace to be positive in positive dimension.
/-- Helper for Proposition 6.35: in positive dimension, the trace of the matrix exponential is
strictly positive. -/
theorem trace_exp_pos
    {n : ℕ} (hn : 0 < n) (X : 𝕊^n) :
    0 < Matrix.trace (exp (X : Matrix (Fin n) (Fin n) ℝ)) := by
  let i0 : Fin n := ⟨0, hn⟩
  -- Rewrite the trace as the eigenvalue exponential sum and keep one positive summand.
  rw [trace_exp_eq_sum_exp_eigenvalues]
  have hterm : 0 < Real.exp (eigenvalues X i0) := Real.exp_pos _
  exact lt_of_lt_of_le hterm <|
    Finset.single_le_sum
      (fun i _ ↦ (Real.exp_pos (eigenvalues X i)).le)
      (Finset.mem_univ i0)

/-- Helper for Proposition 6.35: in positive dimension, the trace-exponential argument of the
logarithm never vanishes. -/
theorem trace_exp_ne_zero
    {n : ℕ} (hn : 0 < n) (X : 𝕊^n) :
    Matrix.trace (exp (X : Matrix (Fin n) (Fin n) ℝ)) ≠ 0 := by
  -- The positive trace estimate is exactly the nonvanishing branch condition for `Real.log`.
  exact (trace_exp_pos hn X).ne'

/-- Helper for Proposition 6.35: in positive dimension, the finite-family log-sum-exp map is
`C²`. -/
theorem logSumExp_contDiff_two
    {n : ℕ} [Nonempty (Fin n)] :
    ContDiff ℝ 2 (logSumExp : EuclideanSpace ℝ (Fin n) → ℝ) := by
  -- The finite sum of exponentials is `C²`, and positivity of one summand keeps `log`
  -- on its smooth branch.
  refine ContDiff.log ?_ ?_
  · refine ContDiff.sum ?_
    intro i hi
    simpa using
      (Real.contDiff_exp.comp (EuclideanSpace.proj i).contDiff)
  · intro x
    let i0 : Fin n := Classical.choice ‹Nonempty (Fin n)›
    have hsum_pos :
        0 < ∑ i : Fin n, Real.exp (x i) := by
      refine Finset.sum_pos' ?_ ?_
      · intro i hi
        exact Real.exp_nonneg (x i)
      · exact ⟨i0, Finset.mem_univ i0, Real.exp_pos (x i0)⟩
    exact hsum_pos.ne'

/-- Helper for Proposition 6.35: a weighted second moment is bounded by the squared largest
absolute coordinate. -/
theorem weighted_variance_le_sup_sq
    {n : ℕ} [Nonempty (Fin n)]
    (p : Fin n → ℝ) (h : EuclideanSpace ℝ (Fin n))
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) :
    (∑ i : Fin n, p i * (h i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * h i) ^ (2 : ℕ) ≤
      (Finset.univ.sup' Finset.univ_nonempty fun i : Fin n ↦ |h i|) ^ (2 : ℕ) := by
  -- The variance term is controlled by the second moment, and each squared coordinate is
  -- bounded by the squared maximal absolute coordinate.
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty fun i : Fin n ↦ |h i|
  have hvar_le :
      (∑ i : Fin n, p i * (h i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * h i) ^ (2 : ℕ) ≤
        ∑ i : Fin n, p i * (h i) ^ (2 : ℕ) := by
    nlinarith
  have hmoment_le :
      ∑ i : Fin n, p i * (h i) ^ (2 : ℕ) ≤ ∑ i : Fin n, p i * M ^ (2 : ℕ) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : |h i| ≤ M := by
      exact Finset.le_sup' (fun j : Fin n ↦ |h j|) (Finset.mem_univ i)
    have hM_nonneg : 0 ≤ M := by
      exact le_trans (abs_nonneg (h i)) hi_le
    have habs_sq_le : |h i| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      have hmul :
          |h i| * |h i| ≤ M * M := by
        exact mul_le_mul hi_le hi_le (abs_nonneg (h i)) hM_nonneg
      simpa [pow_two] using hmul
    have hsquare_eq : (h i) ^ (2 : ℕ) = |h i| ^ (2 : ℕ) := by
      simp [pow_two]
    have hsquare_le : (h i) ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      rw [hsquare_eq]
      exact habs_sq_le
    exact mul_le_mul_of_nonneg_left hsquare_le (hp_nonneg i)
  have hmoment_eq :
      ∑ i : Fin n, p i * M ^ (2 : ℕ) = M ^ (2 : ℕ) := by
    calc
      ∑ i : Fin n, p i * M ^ (2 : ℕ) = (∑ i : Fin n, p i) * M ^ (2 : ℕ) := by
        rw [Finset.sum_mul]
      _ = M ^ (2 : ℕ) := by
        rw [hp_sum, one_mul]
  calc
    (∑ i : Fin n, p i * (h i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * h i) ^ (2 : ℕ)
        ≤ ∑ i : Fin n, p i * (h i) ^ (2 : ℕ) := hvar_le
    _ ≤ ∑ i : Fin n, p i * M ^ (2 : ℕ) := hmoment_le
    _ = M ^ (2 : ℕ) := hmoment_eq

section L2OperatorSlice

open scoped Matrix.Norms.L2Operator

attribute [local instance 3000] Matrix.instL2OpMetricSpace
attribute [local instance 3000] Matrix.instL2OpNormedAddCommGroup
attribute [local instance 3000] Matrix.instL2OpNormedSpace
attribute [local instance 3000] Matrix.instL2OpNormedRing
attribute [local instance 3000] Matrix.instL2OpNormedAlgebra
attribute [local instance 3000] Matrix.instCStarRing

/-- Helper for Proposition 6.35: the squared Euclidean norm of each column is bounded by the
squared ambient Euclidean operator norm. -/
theorem column_sq_sum_le_l2OperatorNorm_sq
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    ∑ j : Fin n, (K j i) ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Pi.single i (1 : ℝ))
  have hxnorm : ‖x‖ = 1 := by
    -- The basis vector `e_i` has Euclidean norm `1`.
    simp [x]
  have hbound :
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm <| Matrix.mulVec K x‖ ≤ ‖K‖ := by
    -- Applying the matrix to `e_i` turns the operator norm bound into a column bound.
    simpa [hxnorm, x] using K.l2_opNorm_mulVec x
  have hsquare :
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm <| Matrix.mulVec K x‖ ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
    -- Squaring both sides identifies the squared output norm with the column energy.
    simpa [pow_two] using
      (mul_le_mul hbound hbound (norm_nonneg _) (norm_nonneg _))
  have hcolumn_norm :
      ‖WithLp.toLp 2 (K.col i)‖ ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
    simpa [x] using hsquare
  -- `K.mulVec e_i` is exactly the `i`th column, whose Euclidean squared norm is the column energy.
  calc
    ∑ j : Fin n, (K j i) ^ (2 : ℕ) = ‖WithLp.toLp 2 (K.col i)‖ ^ (2 : ℕ) := by
      symm
      simpa using EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (K.col i))
    _ ≤ ‖K‖ ^ (2 : ℕ) := hcolumn_norm

-- Proof sketch: each column energy is already bounded by the squared operator norm, and averaging
-- those bounds with nonnegative weights summing to `1` preserves the same upper bound.
/-- Helper for Proposition 6.35: a softmax-weighted average of the column energies is bounded by
the squared ambient Euclidean operator norm. -/
theorem softmax_weighted_column_sq_sum_le_l2OperatorNorm_sq
    {n : ℕ} (p : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) :
    ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
  have hweighted_le :
      ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) ≤
        ∑ i : Fin n, p i * (‖K‖ ^ (2 : ℕ)) := by
    -- Apply the column estimate entrywise before taking the weighted sum.
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left
      (column_sq_sum_le_l2OperatorNorm_sq K i)
      (hp_nonneg i)
  calc
    ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ)
        ≤ ∑ i : Fin n, p i * (‖K‖ ^ (2 : ℕ)) := hweighted_le
    _ = (∑ i : Fin n, p i) * (‖K‖ ^ (2 : ℕ)) := by
      rw [Finset.sum_mul]
    _ = ‖K‖ ^ (2 : ℕ) := by
      rw [hp_sum, one_mul]

/-- Helper for Proposition 6.35: every diagonal entry of a real matrix is bounded in absolute value
by the ambient Euclidean operator norm. -/
theorem diagonal_entry_sq_le_l2OperatorNorm_sq
    {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    |K i i| ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) := by
  -- The diagonal term is one summand in the squared norm of the `i`th column.
  have hdiag_le_column :
      (K i i) ^ (2 : ℕ) ≤ ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (K j i))
        (Finset.mem_univ i))
  have habs_sq :
      |K i i| ^ (2 : ℕ) = (K i i) ^ (2 : ℕ) := by
    simp [pow_two]
  -- The stronger column estimate closes the entrywise bound immediately.
  calc
    |K i i| ^ (2 : ℕ) = (K i i) ^ (2 : ℕ) := habs_sq
    _ ≤ ∑ j : Fin n, (K j i) ^ (2 : ℕ) := hdiag_le_column
    _ ≤ ‖K‖ ^ (2 : ℕ) := column_sq_sum_le_l2OperatorNorm_sq K i

-- Proof sketch: cyclicity of the trace collapses every insertion term in the derivative of
-- `A^(m + 1)` to the same ambient trace `Trace (H A^m)`, so the full insertion sum is just
-- `(m + 1)` copies of that common value.
/-- Helper for Proposition 6.35: after collapsing the insertion terms in the derivative of a power
under the trace, the whole sum becomes `(m + 1) * Trace (H A^m)`. -/
theorem trace_sum_insertions_eq_nsmul_trace_mul_pow
    {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) :
    Matrix.trace ((Finset.range (m + 1)).sum fun i ↦ A ^ (m - i) * H * A ^ i) =
      (m + 1 : ℝ) * Matrix.trace (H * A ^ m) := by
  -- Move the trace through the finite sum and show every summand has the same cyclic trace.
  rw [Matrix.trace_sum]
  have hsum :
      (Finset.range (m + 1)).sum (fun i ↦ Matrix.trace (A ^ (m - i) * H * A ^ i)) =
        (Finset.range (m + 1)).sum (fun _ ↦ Matrix.trace (H * A ^ m)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_le : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc
      Matrix.trace (A ^ (m - i) * H * A ^ i)
        = Matrix.trace ((A ^ i * A ^ (m - i)) * H) := by
            simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle (A ^ (m - i)) H (A ^ i)
      _ = Matrix.trace (H * (A ^ i * A ^ (m - i))) := by
            simpa using Matrix.trace_mul_comm (A ^ i * A ^ (m - i)) H
      _ = Matrix.trace (H * A ^ m) := by
            have hpow : A ^ i * A ^ (m - i) = A ^ m := by
              simpa [Nat.add_sub_of_le hi_le] using (pow_add A i (m - i)).symm
            simp [hpow]
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

end L2OperatorSlice

-- Proof sketch: view `X ↦ Trace (exp X)` as the composition of the subtype inclusion
-- `𝕊^n ↪ Mat`, the ambient Banach-algebra exponential, and the continuous linear trace map.
/-- Helper for Proposition 6.35: the trace-exponential presentation is an equality of functions. -/
theorem entropySmoothing_eq_log_trace_exp_fun
    {n : ℕ} :
    (entropySmoothing : 𝕊^n → ℝ) =
      fun X : 𝕊^n ↦ Real.log (Matrix.trace (exp (X : Matrix (Fin n) (Fin n) ℝ))) := by
  -- Package the pointwise rewrite as a function equality so later smoothness/derivative steps
  -- can work on a single target surface.
  funext X
  exact entropySmoothing_eq_log_trace_exp X

section traceExpContDiffBridge

/-- Helper for Proposition 6.35: the ambient matrix trace packaged as a continuous linear map on
the Frobenius matrix space. -/
private def traceContinuousLinearMap : Mat →L[ℝ] ℝ :=
  { toLinearMap := Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)
    cont := (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.35: evaluating the packaged ambient trace map recovers the ordinary
matrix trace. -/
@[simp] private theorem traceContinuousLinearMap_apply (M : Mat) :
    traceContinuousLinearMap (n := n) M = Matrix.trace M :=
  rfl

/-- Helper for Proposition 6.35: bundle the canonical inclusion `𝕊^n ↪ Mat` on the stabilized
Frobenius owner surface. -/
private def symmetricInclusionContinuousLinearMap : SymmMat →L[ℝ] Mat :=
  { toLinearMap :=
      { toFun := fun X ↦ (X : Mat)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := by
      exact
        ({ toFun := fun X : SymmMat ↦ (X : Mat)
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl } : SymmMat →ₗ[ℝ] Mat).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.35: evaluating the bundled inclusion recovers the ambient matrix
representative of a symmetric matrix. -/
@[simp] private theorem symmetricInclusionContinuousLinearMap_apply (X : SymmMat) :
    symmetricInclusionContinuousLinearMap (n := n) X = (X : Mat) :=
  rfl

/-- Helper for Proposition 6.35: on the ambient Frobenius matrix space, `A ↦ Trace (exp A)` is
`C²`. -/
private theorem traceExpAmbient_contDiffTwo :
    ContDiff ℝ 2 (fun A : Mat ↦ Matrix.trace (exp A)) := by
  -- Route correction: the ambient `Trace ∘ exp` bridge still needs to be rebuilt on the exact
  -- Frobenius owner inherited from `RealSymmetricMatrixSpace`, not on the default matrix surface.
  have hexpAnalytic : AnalyticOnNhd ℝ (exp : Mat → Mat) Set.univ := by
    intro A hA
    exact NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := Mat) A
  have hexpContDiff : ContDiff ℝ 2 (exp : Mat → Mat) := hexpAnalytic.contDiff
  -- Compose the ambient matrix exponential with the packaged trace map on the same owner.
  simpa [Function.comp, traceContinuousLinearMap_apply] using
    (traceContinuousLinearMap (n := n)).contDiff.comp hexpContDiff

/-- Helper for Proposition 6.35: the ambient diagonal affine slice
`t ↦ Trace (exp (diagonal eig + t • K))` is `C²` at `0`. -/
private theorem diagTraceExpLine_contDiffAtTwo
    (eig : Fin n → ℝ) (K : Mat) :
    ContDiffAt ℝ 2
      (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K)))
      0 := by
  -- TODO: after the owner-stable ambient `Trace ∘ exp` bridge is repaired, this is immediate by
  -- composition with the affine line `t ↦ Matrix.diagonal eig + t • K`.
  have hline : ContDiff ℝ 2 (fun t : ℝ ↦ Matrix.diagonal eig + t • K) := by
    -- The diagonal slice is an affine line in the ambient matrix space.
    fun_prop
  -- Restrict the repaired ambient `C²` bridge along the affine line.
  simpa [Function.comp] using
    ((traceExpAmbient_contDiffTwo (n := n)).comp hline).contDiffAt

-- Proof sketch: compose the ambient `C²` trace-exponential map with the canonical inclusion
-- `𝕊^n ↪ Mat` while staying on the same local matrix owner stack.
/-- Helper for Proposition 6.35: the ambient trace-exponential surface is `C²` on `𝕊^n`. -/
theorem traceExp_contDiffTwo
    :
    ContDiff ℝ 2
      (fun X : 𝕊^n ↦ Matrix.trace (exp (X : Matrix (Fin n) (Fin n) ℝ))) := by
  -- TODO: once the ambient bridge is rebuilt on the same Frobenius owner as `𝕊^n`, compose it
  -- with the bundled symmetric inclusion to recover the intrinsic `𝕊^n` surface.
  -- Stay on the same owner surface and compose with the bundled symmetric inclusion.
  have hincl :
      ContDiff ℝ 2
        (fun X : SymmMat ↦ symmetricInclusionContinuousLinearMap (n := n) X) := by
    simpa using
      ((symmetricInclusionContinuousLinearMap (n := n)).contDiff.of_le
        (by simp : (2 : WithTop ℕ∞) ≤ ⊤))
  simpa [Function.comp, symmetricInclusionContinuousLinearMap_apply] using
    (traceExpAmbient_contDiffTwo (n := n)).comp hincl

/-- Helper for Proposition 6.35: on any real normed space, an affine line has derivative equal
to its direction. -/
private lemma affineLineHasDerivAt_generic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • d) d t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul, add_comm] using ((hasDerivAt_id t).smul_const d).const_add x

/-- Helper for Proposition 6.35: on any real normed space, an affine line has vanishing second
iterated derivative. -/
private lemma affineLineIteratedDerivTwo_generic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x d : E) :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ (0 : E) := by
  -- Differentiate the affine line once to a constant and then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • d) = fun _ : ℝ ↦ d := by
    funext s
    exact (affineLineHasDerivAt_generic x d s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Proposition 6.35: a `C²` scalar-valued map has its repeated second Fréchet
derivative on a repeated direction equal to the Chapter 5 second directional derivative. -/
private lemma iteratedFDerivTwo_apply_eqSecondDirectionalDerivative_of_contDiffAtTwo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x h : E} (hcont : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x ![h, h] = secondDirectionalDerivative f x h := by
  let line : ℝ → E := fun t ↦ x + t • h
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hcomp :
      iteratedDeriv 2 (f ∘ line) 0 =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := by
    simpa [line] using (iteratedDeriv_vcomp_two (by simpa [line] using hcont) hline₂)
  have hline_deriv : deriv line 0 = h := by
    simpa [line] using (affineLineHasDerivAt_generic x h 0).deriv
  rw [secondDirectionalDerivative]
  symm
  calc
    iteratedDeriv 2 (directionalSlice f x h) 0 = iteratedDeriv 2 (f ∘ line) 0 := by
      rfl
    _ =
        (iteratedFDeriv ℝ 2 f (line 0)) (fun _ ↦ deriv line 0) +
          (fderiv ℝ f (line 0)) (iteratedDeriv 2 line 0) := hcomp
    _ = iteratedFDeriv ℝ 2 f x ![h, h] := by
      rw [affineLineIteratedDerivTwo_generic]
      simp [line, hline_deriv, iteratedFDeriv_two_apply]

end traceExpContDiffBridge

-- Proof sketch: rewrite `entropySmoothing` as `log (Trace (exp X))`, use the `C²`
-- trace-exponential core above, and keep `Real.log` on its smooth branch by `trace_exp_pos`.
/-- Helper for Proposition 6.35: in positive dimension, the entropy smoothing is `C²`. -/
theorem entropySmoothing_contDiff_two_pos
    {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^n → ℝ) := by
  -- Rewrite to the trace-exponential surface so the only remaining work is the `Real.log`
  -- chain rule on a positive argument.
  rw [entropySmoothing_eq_log_trace_exp_fun]
  refine ContDiff.log traceExp_contDiffTwo ?_
  intro X
  exact trace_exp_ne_zero hn X

/-- Helper for Proposition 6.35: the affine scalar slice of a `C²` function on `𝕊^n` has second
derivative at `0` equal to the repeated-direction second Fréchet derivative. -/
theorem sliceSecondDeriv_eq_iteratedFDerivTwo
    {n : ℕ} {f : 𝕊^n → ℝ} {X H : 𝕊^n} (hcont : ContDiffAt ℝ 2 f X) :
    iteratedDeriv 2 (fun t : ℝ ↦ f (X + t • H)) 0 =
      (iteratedFDeriv ℝ 2 f X) ![H, H] := by
  -- Unfold the scalar slice to the Chapter 5 directional derivative owner and rewrite it back
  -- through the repeated-direction Hessian bridge.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ f (X + t • H)) 0 = secondDirectionalDerivative f X H := by
      rw [secondDirectionalDerivative]
      rfl
    _ = (iteratedFDeriv ℝ 2 f X) ![H, H] := by
      exact (iteratedFDerivTwo_apply_eqSecondDirectionalDerivative_of_contDiffAtTwo hcont).symm

section L2OperatorSlice

open scoped Matrix.Norms.L2Operator

attribute [local instance 3000] Matrix.instL2OpMetricSpace
attribute [local instance 3000] Matrix.instL2OpNormedAddCommGroup
attribute [local instance 3000] Matrix.instL2OpNormedSpace
attribute [local instance 3000] Matrix.instL2OpNormedRing
attribute [local instance 3000] Matrix.instL2OpNormedAlgebra
attribute [local instance 3000] Matrix.instCStarRing

-- Proof sketch: the variance term is bounded by the weighted diagonal second moment, and adding
-- only the off-diagonal column energy exactly reconstructs the full weighted column-energy average
-- already controlled by `softmax_weighted_column_sq_sum_le_l2OperatorNorm_sq`.
/-- Helper for Proposition 6.35: the weighted diagonal variance plus the weighted off-diagonal
column energy is bounded by the squared ambient Euclidean operator norm. -/
theorem weightedVarianceAddOffDiagColumnEnergy_le_l2OperatorNorm_sq
    {n : ℕ} [Nonempty (Fin n)]
    (p : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i : Fin n, p i = 1) :
    ((∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * K i i) ^ (2 : ℕ)) +
        ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) ≤
      ‖K‖ ^ (2 : ℕ) := by
  have hvariance_le :
      ((∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * K i i) ^ (2 : ℕ)) +
          ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) ≤
        (∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) +
          ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) := by
    -- Drop the nonnegative square of the weighted diagonal mean.
    nlinarith [sq_nonneg (∑ i : Fin n, p i * K i i)]
  have hcolumn_decomp :
      (∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) +
          ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) =
        ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
    -- Split each weighted column energy into its diagonal summand and the remaining off-diagonal
    -- part.
    calc
      (∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) +
          ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ))
        = ∑ i : Fin n,
            (p i * (K i i) ^ (2 : ℕ) +
              p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ))) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ i : Fin n,
            p i * ((K i i) ^ (2 : ℕ) +
              (Finset.univ.erase i).sum (fun j : Fin n ↦ (K j i) ^ (2 : ℕ))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_erase_add (s := Finset.univ) (a := i)
                (f := fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) (by simp)]
              ring
  -- Once the diagonal/off-diagonal split is recombined into the full column energy,
  -- the existing weighted column bound closes the estimate.
  calc
    ((∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) - (∑ i : Fin n, p i * K i i) ^ (2 : ℕ)) +
        ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ))
      ≤ (∑ i : Fin n, p i * (K i i) ^ (2 : ℕ)) +
          ∑ i : Fin n, p i * ((Finset.univ.erase i).sum fun j : Fin n ↦ (K j i) ^ (2 : ℕ)) :=
        hvariance_le
    _ = ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := hcolumn_decomp
    _ ≤ ‖K‖ ^ (2 : ℕ) := softmax_weighted_column_sq_sum_le_l2OperatorNorm_sq p K hp_nonneg hp_sum

-- Proof sketch: multiply on the right by the unitary and on the left by its adjoint, using the
-- C-star norm identities in operator-norm scope to remove both unitary factors one at a time.
/-- Helper for Proposition 6.35: unitary conjugation preserves the ambient Euclidean operator
norm. -/
theorem unitaryConj_l2OperatorNorm_eq
    {n : ℕ} [Nonempty (Fin n)]
    (U : Matrix.unitaryGroup (Fin n) ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖star (U : Matrix (Fin n) (Fin n) ℝ) * A * (U : Matrix (Fin n) (Fin n) ℝ)‖ = ‖A‖ := by
  calc
    ‖star (U : Matrix (Fin n) (Fin n) ℝ) * A * (U : Matrix (Fin n) (Fin n) ℝ)‖
        = ‖star (U : Matrix (Fin n) (Fin n) ℝ) * A‖ := by
            simpa [Matrix.mul_assoc] using
              (CStarRing.norm_mul_coe_unitary
                (A := star (U : Matrix (Fin n) (Fin n) ℝ) * A) (U := U))
    _ = ‖A‖ := by
          simpa using
            (CStarRing.norm_coe_unitary_mul
              (U := star U) (A := A))

-- Proof sketch: conjugate the affine slice into the fixed eigenbasis of `X`, where `X` becomes
-- diagonal and the direction becomes the single ambient matrix `K`; then use `map_exp` and
-- `trace_map` to transport the matrix exponential and trace through that ring automorphism.
/-- Helper for Proposition 6.35: conjugating the affine trace-exponential slice into the
eigenbasis of `X` rewrites it as the ambient diagonal slice. -/
theorem spectralSlice_eq_diagLogTraceExp
    {n : ℕ} (X H : 𝕊^n) :
    let hX : (X : Matrix (Fin n) (Fin n) ℝ).IsHermitian := RealSymmetricMatrixSpace.isHermitian X
    let U : Matrix.unitaryGroup (Fin n) ℝ := hX.eigenvectorUnitary
    let K : Matrix (Fin n) (Fin n) ℝ :=
      star (U : Matrix (Fin n) (Fin n) ℝ) * (H : Matrix (Fin n) (Fin n) ℝ) *
        (U : Matrix (Fin n) (Fin n) ℝ)
    (fun t : ℝ ↦ Real.log (Matrix.trace (exp (((X + t • H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ)))))
      =
    fun t : ℝ ↦ Real.log (Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K))) := by
  let hX : (X : Matrix (Fin n) (Fin n) ℝ).IsHermitian := RealSymmetricMatrixSpace.isHermitian X
  let U : Matrix.unitaryGroup (Fin n) ℝ := hX.eigenvectorUnitary
  let K : Matrix (Fin n) (Fin n) ℝ :=
    star (U : Matrix (Fin n) (Fin n) ℝ) * (H : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ)
  funext t
  let A : Matrix (Fin n) (Fin n) ℝ :=
    (((X + t • H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ))
  have hXdiag :
      ((Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)) (star U))
          (X : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (eigenvalues X) := by
    simpa [U] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hHconj :
      ((Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)) (star U))
          (H : Matrix (Fin n) (Fin n) ℝ) = K := by
    simp [K, U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc]
  have hslice :
      star (U : Matrix (Fin n) (Fin n) ℝ) * A * (U : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (eigenvalues X) + t • K := by
    have hsliceMap :
        ((Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)) (star U)) A =
          Matrix.diagonal (eigenvalues X) + t • K := by
      rw [show A =
        (X : Matrix (Fin n) (Fin n) ℝ) + t • (H : Matrix (Fin n) (Fin n) ℝ) by rfl]
      rw [map_add, map_smul, hXdiag, hHconj]
    simpa [A, U, Unitary.conjStarAlgAut_apply, Matrix.mul_assoc] using hsliceMap
  have hexpConj :
      exp (star (U : Matrix (Fin n) (Fin n) ℝ) * A * (U : Matrix (Fin n) (Fin n) ℝ)) =
        star (U : Matrix (Fin n) (Fin n) ℝ) * exp A * (U : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [Matrix.mul_assoc] using
      Matrix.exp_units_conj' (Unitary.toUnits U) A
  have htraceConj :
      Matrix.trace (star (U : Matrix (Fin n) (Fin n) ℝ) * exp A * (U : Matrix (Fin n) (Fin n) ℝ)) =
        Matrix.trace (exp A) := by
    simpa [Matrix.mul_assoc] using
      Matrix.trace_units_conj' (Unitary.toUnits U) (exp A)
  have htrace :
      Matrix.trace (exp A) =
        Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K)) := by
    calc
      Matrix.trace (exp A)
          = Matrix.trace
              (star (U : Matrix (Fin n) (Fin n) ℝ) * exp A * (U : Matrix (Fin n) (Fin n) ℝ)) := by
                  symm
                  exact htraceConj
      _ =
          Matrix.trace
            (exp (star (U : Matrix (Fin n) (Fin n) ℝ) * A * (U : Matrix (Fin n) (Fin n) ℝ))) := by
            rw [← hexpConj]
      _ = Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K)) := by
            simp [hslice]
  -- The scalar slice equality is exactly the trace equality transported through `Real.log`.
  simpa [A, hX, U, K] using congrArg Real.log htrace

/-- Helper for Proposition 6.35: the diagonal trace-exponential partition function is positive in
positive dimension. -/
private theorem diagTraceExpPartition_pos
    {n : ℕ} [Nonempty (Fin n)] (eig : Fin n → ℝ) :
    0 < ∑ i : Fin n, Real.exp (eig i) := by
  let i0 : Fin n := Classical.choice ‹Nonempty (Fin n)›
  -- Keep one strictly positive exponential summand and dominate it by the full finite sum.
  have hi0 : 0 < Real.exp (eig i0) := Real.exp_pos _
  exact lt_of_lt_of_le hi0 <|
    Finset.single_le_sum
      (fun i _ ↦ (Real.exp_pos (eig i)).le)
      (Finset.mem_univ i0)

/-- Helper for Proposition 6.35: the softmax weights built from the diagonal slice form a
probability vector. -/
private theorem softmaxWeights_nonneg_sum_one
    {n : ℕ} [Nonempty (Fin n)] (eig : Fin n → ℝ) :
    let Z := ∑ i : Fin n, Real.exp (eig i)
    let p : Fin n → ℝ := fun i ↦ Real.exp (eig i) / Z
    (∀ i, 0 ≤ p i) ∧ ∑ i : Fin n, p i = 1 := by
  let Z := ∑ i : Fin n, Real.exp (eig i)
  let p : Fin n → ℝ := fun i ↦ Real.exp (eig i) / Z
  have hZ : 0 < Z := diagTraceExpPartition_pos eig
  have hZinv : Z * Z⁻¹ = 1 := by
    field_simp [hZ.ne']
  constructor
  · -- Each softmax weight is a nonnegative exponential divided by the positive partition sum.
    intro i
    exact div_nonneg (Real.exp_nonneg (eig i)) hZ.le
  · -- Summing the weights collapses back to the partition sum and then to `1`.
    calc
      ∑ i : Fin n, p i = ∑ i : Fin n, Real.exp (eig i) * Z⁻¹ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [p, Z, div_eq_mul_inv]
      _ = (∑ i : Fin n, Real.exp (eig i)) * Z⁻¹ := by
        rw [Finset.sum_mul]
      _ = 1 := by
        simpa [Z] using hZinv

-- Proof sketch: expand `(a - b)^2 ≥ 0` and solve the resulting quadratic inequality for `ab`.
/-- Helper for Proposition 6.35: the product of two real numbers is bounded by the average of
their squares. -/
private theorem mul_le_avg_sq (a b : ℝ) :
    a * b ≤ ((a ^ (2 : ℕ)) + (b ^ (2 : ℕ))) / 2 := by
  -- Route correction: this is the scalar `2ab ≤ a² + b²` step needed for the off-diagonal
  -- cross-term estimate in the diagonal Hessian bound.
  have hsq : 0 ≤ (a - b) ^ (2 : ℕ) := sq_nonneg (a - b)
  nlinarith [hsq]

/-- Helper for Proposition 6.35: the second scalar derivative of `Real.log` is the negative
inverse square. -/
private theorem iteratedDerivTwo_log_eq_neg_inv_sq {s : ℝ} (_hs : s ≠ 0) :
    iteratedDeriv 2 Real.log s = -((s ^ (2 : ℕ))⁻¹) := by
  have hderiv_log : deriv Real.log = fun x : ℝ ↦ x⁻¹ := by
    ext x
    rw [Real.deriv_log]
  calc
    iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
      simp [iteratedDeriv_succ]
    _ = deriv (fun x : ℝ ↦ x⁻¹) s := by
      rw [hderiv_log]
    _ = -((s ^ (2 : ℕ))⁻¹) := by
      rw [deriv_inv]

/-- Helper for Proposition 6.35: the exponential-weighted quadratic trace is bounded by the
partition function times the squared ambient Euclidean operator norm. -/
private theorem traceExpSquareWeight_le_partition_mul_l2OperatorNorm_sq
    {n : ℕ} [Nonempty (Fin n)] (eig : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) :
    Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) ≤
      (∑ i : Fin n, Real.exp (eig i)) * ‖K‖ ^ (2 : ℕ) := by
  let Z : ℝ := ∑ i : Fin n, Real.exp (eig i)
  let p : Fin n → ℝ := fun i ↦ Real.exp (eig i) / Z
  have hZ : 0 < Z := diagTraceExpPartition_pos eig
  rcases softmaxWeights_nonneg_sum_one eig with ⟨hp_nonneg, hp_sum⟩
  have hsymm : ∀ i j : Fin n, K i j = K j i := by
    intro i j
    have hij : K j i = K i j := by
      simpa [Matrix.transpose_apply] using congrArg (fun M : Matrix (Fin n) (Fin n) ℝ ↦ M i j) hK
    exact hij.symm
  have htraceExpand :
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) =
        ∑ i : Fin n, Real.exp (eig i) * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
    -- Rewrite the weighted trace as the exponential-weighted column energy average.
    calc
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K)
          =
        Matrix.trace
          (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K *
            Matrix.diagonal (fun _ : Fin n ↦ (1 : ℝ)) * K) := by
              simp [Matrix.mul_assoc]
      _ =
        ∑ i : Fin n, ∑ j : Fin n, Real.exp (eig i) * (K i j) ^ (2 : ℕ) * (1 : ℝ) := by
          simpa using
            diagonal_weighted_trace_eq_sumSquares
              (fun i ↦ Real.exp (eig i))
              (fun _ : Fin n ↦ (1 : ℝ))
              K hK
      _ = ∑ i : Fin n, ∑ j : Fin n, Real.exp (eig i) * (K j i) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [hsymm i j]
            simp
      _ = ∑ i : Fin n, Real.exp (eig i) * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
            symm
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
  have htraceWeighted :
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) =
        Z * ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
    -- Normalize the exponential weights into the softmax probabilities.
    calc
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K)
          = ∑ i : Fin n, Real.exp (eig i) * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := htraceExpand
      _ = ∑ i : Fin n, (Z * p i) * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hiZ : Z * p i = Real.exp (eig i) := by
              dsimp [p, Z]
              field_simp [hZ.ne']
            rw [hiZ]
      _ = ∑ i : Fin n, Z * (p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = Z * ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := by
            symm
            rw [Finset.mul_sum]
  have hweighted :
      ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) ≤ ‖K‖ ^ (2 : ℕ) :=
    softmax_weighted_column_sq_sum_le_l2OperatorNorm_sq p K hp_nonneg hp_sum
  have hmul := mul_le_mul_of_nonneg_left hweighted hZ.le
  -- The weighted column-energy estimate closes the comparison after undoing the softmax scaling.
  calc
    Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K)
        = Z * ∑ i : Fin n, p i * ∑ j : Fin n, (K j i) ^ (2 : ℕ) := htraceWeighted
    _ ≤ Z * (‖K‖ ^ (2 : ℕ)) := hmul
    _ = (∑ i : Fin n, Real.exp (eig i)) * ‖K‖ ^ (2 : ℕ) := by
          simp [Z]

end L2OperatorSlice

/-- Helper for Proposition 6.35: adding a scalar to every diagonal entry is the same as adding a
scalar multiple of the identity matrix. -/
private theorem diagonal_add_const_eq_add_smul_one
    {n : ℕ} (eig : Fin n → ℝ) (c : ℝ) :
    Matrix.diagonal (fun i ↦ eig i + c) =
      Matrix.diagonal eig + c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Compare both matrices entrywise on and off the diagonal.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij]

/-- Helper for Proposition 6.35: shifting the diagonal slice by a scalar factor multiplies the
trace exponential by `exp c`. -/
private theorem traceExpDiagonalShift_eq_exp_mul_traceExp
    {n : ℕ} (eig : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) (c t : ℝ) :
    Matrix.trace (exp (Matrix.diagonal (fun i ↦ eig i + c) + t • K)) =
      Real.exp c * Matrix.trace (exp (Matrix.diagonal eig + t • K)) := by
  have hrewrite :
      Matrix.diagonal (fun i ↦ eig i + c) + t • K =
        (Matrix.diagonal eig + t • K) + c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [diagonal_add_const_eq_add_smul_one]
    simp [add_assoc, add_comm]
  have hscalarOne :
      c • (1 : Matrix (Fin n) (Fin n) ℝ) = Matrix.diagonal (fun _ : Fin n ↦ c) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hcomm :
      Commute (Matrix.diagonal eig + t • K) (c • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    rw [hscalarOne]
    simpa using
      (Matrix.scalar_commute
        (n := Fin n)
        c
        (Commute.all c)
        (Matrix.diagonal eig + t • K)).symm
  have hexpScalar :
      exp (c • (1 : Matrix (Fin n) (Fin n) ℝ)) =
        Real.exp c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    calc
      exp (c • (1 : Matrix (Fin n) (Fin n) ℝ))
          = exp (Matrix.diagonal (fun _ : Fin n ↦ c)) := by
              rw [hscalarOne]
      _ = Matrix.diagonal (fun _ : Fin n ↦ exp c) := by
            rw [Matrix.exp_diagonal]
            congr
            funext i
            simp
      _ = Matrix.diagonal (fun _ : Fin n ↦ Real.exp c) := by
            simp [Real.exp_eq_exp_ℝ]
      _ = Real.exp c • (1 : Matrix (Fin n) (Fin n) ℝ) := by
            ext i j
            by_cases hij : i = j
            · subst hij
              simp [Matrix.diagonal]
            · simp [Matrix.diagonal, hij]
  -- Commute the scalar identity shift through the matrix exponential and then factor out `exp c`.
  calc
    Matrix.trace (exp (Matrix.diagonal (fun i ↦ eig i + c) + t • K))
        =
          Matrix.trace
            (exp ((Matrix.diagonal eig + t • K) + c • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
            rw [hrewrite]
    _ =
        Matrix.trace
          (exp (Matrix.diagonal eig + t • K) * exp (c • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
          rw [Matrix.exp_add_of_commute _ _ hcomm]
    _ =
        Matrix.trace
          (exp (Matrix.diagonal eig + t • K) * (Real.exp c • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
          rw [hexpScalar]
    _ = Matrix.trace (Real.exp c • exp (Matrix.diagonal eig + t • K)) := by
          simp
    _ = Real.exp c * Matrix.trace (exp (Matrix.diagonal eig + t • K)) := by
          simp [Matrix.trace_smul, mul_comm]

/-- Helper for Proposition 6.35: shifting the exponential diagonal weights by a scalar factor
multiplies the weighted quadratic trace by `exp c`. -/
private theorem traceExpSquareWeight_shift_eq_exp_mul
    {n : ℕ} (eig : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i + c)) * K * K) =
      Real.exp c * Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
  have hdiag :
      Matrix.diagonal (fun i ↦ Real.exp (eig i + c)) =
        Real.exp c • Matrix.diagonal (fun i ↦ Real.exp (eig i)) := by
    -- Pull the scalar `exp c` out of the diagonal matrix entrywise.
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal, Real.exp_add, mul_comm]
    · simp [Matrix.diagonal, hij]
  calc
    Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i + c)) * K * K)
        = Matrix.trace ((Real.exp c • Matrix.diagonal (fun i ↦ Real.exp (eig i))) * K * K) := by
            rw [hdiag]
    _ = Matrix.trace (Real.exp c • (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K)) := by
          simp [Matrix.mul_assoc]
    _ = Real.exp c * Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
          simp [Matrix.trace_smul]

-- Proof sketch: differentiate the affine matrix power term first, then push the derivative
-- through the continuous trace map and collapse the insertion sum by cyclicity of trace.
/-- Helper for Proposition 6.35: the affine-slice power coefficient has derivative
`Trace (B * (A + t • B)^m) / m!`. -/
private theorem traceExpAffineSliceTerm_hasDerivAt
    (A B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        Matrix.trace ((A + s • B) ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ))
      (Matrix.trace (B * (A + t • B) ^ m) / ((Nat.factorial m) : ℝ))
      t := by
  let line : ℝ → Mat := fun s : ℝ ↦ A + s • B
  have hpow :
      HasFDerivAt
        (fun M : Mat ↦ M ^ (m + 1))
        (∑ i ∈ Finset.range (m + 1),
          (line t) ^ ((m + 1).pred - i) •> ContinuousLinearMap.id ℝ Mat <• (line t) ^ i)
        (line t) := by
    -- Differentiate the ambient power map at the affine-slice base point.
    simpa [line] using (hasFDerivAt_pow' (𝕜 := ℝ) (n := m + 1) (x := line t))
  have hpowLine :
      HasDerivAt
        (fun s : ℝ ↦ line s ^ (m + 1))
        ((Finset.range (m + 1)).sum fun i ↦ (line t) ^ (m - i) * B * (line t) ^ i)
        t := by
    have hline : HasDerivAt line B t := by
      -- The affine line `s ↦ A + s • B` has derivative equal to its direction `B`.
      simpa [line, one_smul, add_comm] using ((hasDerivAt_id t).smul_const B).const_add A
    -- Compose the ambient power derivative with the affine slice.
    simpa [line, ContinuousLinearMap.sum_apply, Matrix.mul_assoc] using
      hpow.comp_hasDerivAt t hline
  have htrace :
      HasDerivAt
        (fun s : ℝ ↦ Matrix.trace (line s ^ (m + 1)))
        ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i))
        t := by
    -- Apply the bundled trace map to the differentiated power slice.
    simpa [traceContinuousLinearMap_apply] using
      (traceContinuousLinearMap (n := n)).hasFDerivAt.comp_hasDerivAt t hpowLine
  have hcollapse :
      ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i)) =
        (m + 1 : ℝ) * Matrix.trace (B * (line t) ^ m) := by
    -- Cyclicity of trace collapses the insertion sum to `(m + 1)` copies of one term.
    simpa [line] using
      trace_sum_insertions_eq_nsmul_trace_mul_pow (A := line t) (H := B) m
  have hscaled :
      HasDerivAt
        (fun s : ℝ ↦ (((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹) * Matrix.trace (line s ^ (m + 1)))
        ((((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹) *
          ((Finset.range (m + 1)).sum fun i ↦ Matrix.trace ((line t) ^ (m - i) * B * (line t) ^ i)))
        t := by
    -- Scale the derivative by the reciprocal factorial from the power-series coefficient.
    simpa [line, mul_comm, mul_assoc] using
      htrace.const_mul ((((Nat.factorial (m + 1) : ℕ) : ℝ)⁻¹))
  -- Rewrite the scaled derivative into the source-facing factorial denominator.
  convert hscaled using 1
  · ext s
    simp [line, div_eq_mul_inv, mul_comm]
  · simp [div_eq_mul_inv, hcollapse]
    field_simp
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

-- Proof sketch: bound the affine slice uniformly on `(-1, 1)` by a fixed radius
-- `‖A‖ + ‖B‖`, then apply the operator norm of the bundled trace map.
/-- Helper for Proposition 6.35: the raw affine-slice trace term is bounded by a factorial-free
ambient majorant on `(-1, 1)`. -/
private theorem traceExpAffineSliceTraceNormMajorant
    (A B : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖Matrix.trace (B * (A + t • B) ^ m)‖ ≤
      ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by
  have ht_abs : |t| ≤ 1 := by
    exact (abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩).le
  have hsmul_norm : ‖t • B‖ ≤ ‖B‖ := by
    rw [norm_smul]
    calc
      |t| * ‖B‖ ≤ 1 * ‖B‖ := by
        exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
      _ = ‖B‖ := by ring
  have hline_norm : ‖A + t • B‖ ≤ ‖A‖ + ‖B‖ := by
    calc
      ‖A + t • B‖ ≤ ‖A‖ + ‖t • B‖ := norm_add_le _ _
      _ ≤ ‖A‖ + ‖B‖ := by gcongr
  have hradius_nonneg : 0 ≤ ‖A‖ + ‖B‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hpow_bound : ‖(A + t • B) ^ m‖ ≤ ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by
    induction m with
    | zero =>
        simp
    | succ k ih =>
        calc
          ‖(A + t • B) ^ (k + 1)‖ = ‖(A + t • B) ^ k * (A + t • B)‖ := by
              rw [pow_succ]
          _ ≤ ‖(A + t • B) ^ k‖ * ‖A + t • B‖ := norm_mul_le _ _
          _ ≤ (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ k) * ‖A + t • B‖ := by
              exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
          _ ≤ (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ k) * (‖A‖ + ‖B‖) := by
              exact mul_le_mul_of_nonneg_left hline_norm
                (mul_nonneg (norm_nonneg _) (pow_nonneg hradius_nonneg _))
          _ = ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ (k + 1) := by
              rw [pow_succ]
              ring
  -- Control the trace by the operator norm of the packaged trace map and then bound the power.
  calc
    ‖Matrix.trace (B * (A + t • B) ^ m)‖
      ≤ ‖traceContinuousLinearMap (n := n)‖ * ‖B * (A + t • B) ^ m‖ := by
          simpa [traceContinuousLinearMap_apply] using
            (ContinuousLinearMap.le_opNorm
              (traceContinuousLinearMap (n := n))
              (B * (A + t • B) ^ m))
    _ ≤ ‖traceContinuousLinearMap (n := n)‖ * (‖B‖ * ‖(A + t • B) ^ m‖) := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ ‖traceContinuousLinearMap (n := n)‖ * (‖B‖ * (‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m)) := by
          gcongr
    _ = ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m := by
          ring

-- Proof sketch: divide the ambient majorant by the positive factorial coefficient to package a
-- summable bound for the differentiated affine-slice series.
/-- Helper for Proposition 6.35: the differentiated affine-slice series admits a summable
uniform majorant on `(-1, 1)`. -/
private theorem traceExpAffineSliceDerivBound
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ m t, t ∈ Set.Ioo (-1 : ℝ) 1 →
        ‖Matrix.trace (B * (A + t • B) ^ m) / ((Nat.factorial m) : ℝ)‖ ≤ u m := by
  let C : ℝ := ‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖
  let u : ℕ → ℝ := fun m ↦ C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ))
  refine ⟨u, ?_, ?_⟩
  · have hpow :
        Summable (fun m : ℕ ↦ (‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) :=
      Real.summable_pow_div_factorial (‖A‖ + ‖B‖)
    -- The factorial-decaying scalar series remains summable after multiplying by the fixed
    -- trace-direction constant.
    simpa [u, C, mul_assoc] using hpow.mul_left C
  · intro m t ht
    have hfactorial_pos : 0 < ((Nat.factorial m) : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hmajorant :=
      traceExpAffineSliceTraceNormMajorant (n := n) (A := A) (B := B) (m := m) ht
    have hdiv :
        ‖Matrix.trace (B * (A + t • B) ^ m)‖ / ((Nat.factorial m) : ℝ) ≤
          C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) := by
      -- Divide the raw estimate by the positive factorial coefficient only at the end.
      calc
        ‖Matrix.trace (B * (A + t • B) ^ m)‖ / ((Nat.factorial m) : ℝ)
          ≤ (‖traceContinuousLinearMap (n := n)‖ * ‖B‖ * ‖(1 : Mat)‖ * (‖A‖ + ‖B‖) ^ m) /
              ((Nat.factorial m) : ℝ) := by
                exact div_le_div_of_nonneg_right hmajorant hfactorial_pos.le
        _ = C * ((‖A‖ + ‖B‖) ^ m / ((Nat.factorial m) : ℝ)) := by
              field_simp [C, hfactorial_pos.ne']
              ring
    simpa [u, norm_div, Real.norm_natCast] using hdiv

-- Proof sketch: rewrite the matrix exponential as its power series and separate the `k = 0`
-- term so the remaining series starts at exponent `m + 1`.
/-- Helper for Proposition 6.35: the trace of the affine-slice exponential has the stable normal
form `Trace 1 + ∑' m, Trace ((A + t • B) ^ (m + 1)) / (m + 1)!`. -/
private theorem traceExpAffineSlice_eq_traceOne_add_tsum
    (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix.trace (exp (A + t • B)) =
      Matrix.trace (1 : Mat) +
        ∑' m : ℕ,
          Matrix.trace ((A + t • B) ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ) := by
  letI : CompleteSpace Mat := FiniteDimensional.complete ℝ Mat
  let X : Mat := A + t • B
  have hsum :
      Summable
        (fun m : ℕ ↦ Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m)) := by
    -- The ambient exponential series stays summable after applying the continuous trace map.
    simpa [traceContinuousLinearMap_apply] using
      (expSeries_summable' (𝕂 := ℝ) X).mapL (traceContinuousLinearMap (n := n))
  have hexp :
      exp X = ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m := by
    simpa using
      (congrArg (fun f : Mat → Mat ↦ f X) (exp_eq_tsum (𝕂 := ℝ) (𝔸 := Mat)))
  -- Rewrite `trace (exp X)` as the trace of the exponential power series and split off `m = 0`.
  calc
    Matrix.trace (exp (A + t • B))
      = Matrix.trace (exp X) := by
          simp [X]
    _ = Matrix.trace (∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m) := by
          rw [hexp]
    _ = ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m) := by
          simpa [traceContinuousLinearMap_apply] using
            (traceContinuousLinearMap (n := n)).map_tsum (expSeries_summable' (𝕂 := ℝ) X)
    _ = Matrix.trace (1 : Mat) +
          ∑' m : ℕ, Matrix.trace (X ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ) := by
          simpa [div_eq_mul_inv, Matrix.trace_smul, mul_comm, mul_left_comm, mul_assoc] using
            (hsum.sum_add_tsum_nat_add 1).symm

/-- Helper for Proposition 6.35: the trace of the affine-slice exponential splits into the
constant term, the affine term, and the degree-`m + 2` exponential tail. -/
private theorem traceExpAffineSlice_eq_traceOne_add_traceLine_add_tsumTail
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix.trace (exp (A + t • B)) =
      Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) +
        Matrix.trace (A + t • B) +
        ∑' m : ℕ,
          Matrix.trace ((A + t • B) ^ (m + 2)) / ((Nat.factorial (m + 2)) : ℝ) := by
  letI : CompleteSpace (Matrix (Fin n) (Fin n) ℝ) :=
    FiniteDimensional.complete ℝ (Matrix (Fin n) (Fin n) ℝ)
  let X : Matrix (Fin n) (Fin n) ℝ := A + t • B
  let a : ℕ → ℝ := fun m ↦ Matrix.trace (X ^ (m + 1)) / ((Nat.factorial (m + 1)) : ℝ)
  have hsummable :
      Summable a := by
    have hsum :
        Summable
          (fun m : ℕ ↦ Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m)) := by
      -- The ambient exponential series stays summable after applying the continuous trace map.
      simpa [traceContinuousLinearMap_apply] using
        (expSeries_summable' (𝕂 := ℝ) X).mapL (traceContinuousLinearMap (n := n))
    -- Dropping the constant term leaves the shifted exponential trace series.
    simpa [a, div_eq_mul_inv, Matrix.trace_smul, mul_comm, mul_left_comm, mul_assoc] using
      hsum.comp_injective Nat.succ_injective
  have hsplit :
      ∑' m : ℕ, a m = a 0 + ∑' m : ℕ, a (m + 1) := by
    simpa using (hsummable.sum_add_tsum_nat_add 1).symm
  -- Split the repaired `Trace 1 + tsum` normal form into the affine term and the degree-`m + 2`
  -- tail needed later.
  calc
    Matrix.trace (exp (A + t • B))
        = Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) + ∑' m : ℕ, a m := by
            simpa [X, a] using traceExpAffineSlice_eq_traceOne_add_tsum (n := n) A B t
    _ = Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) + (a 0 + ∑' m : ℕ, a (m + 1)) := by
          rw [hsplit]
    _ = Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) +
          Matrix.trace (A + t • B) +
          ∑' m : ℕ, Matrix.trace ((A + t • B) ^ (m + 2)) / ((Nat.factorial (m + 2)) : ℝ) := by
            simp [X, a, add_assoc]

/-- Helper for Proposition 6.35: the degree-`m + 2` tail coefficient has second derivative equal
to the exact mixed-trace sum supplied by Proposition 6.33. -/
private theorem powerTraceTailCoeff_iteratedDerivTwo_eq_mixedTraceSum
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (m : ℕ) :
    iteratedDeriv 2
        (fun t : ℝ ↦
          Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
            ((Nat.factorial (m + 2)) : ℝ)) 0 =
      ((((Nat.factorial (m + 1)) : ℝ)⁻¹) *
        (Finset.sum (Finset.range (m + 1)) fun p ↦
          Matrix.trace
            ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))) := by
  let Xs : SymmMat :=
    ⟨Matrix.diagonal lam, by
      rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
      exact Matrix.isSymm_diagonal _⟩
  let Hs : SymmMat :=
    ⟨K, by
      rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
      exact hK⟩
  let c : ℝ := (((Nat.factorial (m + 2)) : ℕ) : ℝ)⁻¹
  have hk : 1 ≤ m + 2 := by omega
  have hpowerTraceContDiffAt : ContDiffAt ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs := by
    simpa using (powerTrace_contDiff (n := n) (m + 2) hk).contDiffAt
  have hslice :
      iteratedDeriv 2 (fun t : ℝ ↦ π[m + 2] (Xs + t • Hs)) 0 =
        (iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs] :=
    sliceSecondDeriv_eq_iteratedFDerivTwo
      (n := n) (f := (π[m + 2] : SymmMat → ℝ)) (X := Xs) (H := Hs)
      hpowerTraceContDiffAt
  have hpower :
      (iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs] =
        (m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam) ^ (m - p) * (K * ((Matrix.diagonal lam) ^ p * K)))) := by
    simpa [Xs, Hs, Matrix.transpose_mul, Matrix.mul_assoc, hK] using
      powerTrace_iteratedFDeriv_two_eq_frobenius_sum
        (n := n) (k := m + 2) hk Xs Hs
  have hterm :
      ∀ p : ℕ,
        Matrix.trace ((Matrix.diagonal lam) ^ (m - p) * (K * ((Matrix.diagonal lam) ^ p * K))) =
          Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K) := by
    intro p
    -- Cyclicity of trace swaps the two diagonal-power/K blocks.
    have hswap :=
      Matrix.trace_mul_comm
        ((Matrix.diagonal lam) ^ (m - p) * K)
        ((Matrix.diagonal lam) ^ p * K)
    simpa [Matrix.mul_assoc] using hswap
  have hcoeff :
      c * (m + 2 : ℝ) = (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
    -- Normalize the factorial coefficient after Proposition 6.33 contributes the factor `m + 2`.
    have hm2 : (m + 2 : ℝ) ≠ 0 := by positivity
    have hfac :
        ((Nat.factorial (m + 2)) : ℝ) =
          (m + 2 : ℝ) * ((Nat.factorial (m + 1)) : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (m + 1))
    calc
      c * (m + 2 : ℝ) = ((Nat.factorial (m + 2) : ℝ)⁻¹) * (m + 2 : ℝ) := by rfl
      _ = ((((m + 2 : ℝ) * ((Nat.factorial (m + 1)) : ℝ)))⁻¹) * (m + 2 : ℝ) := by rw [hfac]
      _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
            field_simp [hm2]
  -- Rewrite the scalar slice through Proposition 6.33 and simplify the symmetric trace term.
  calc
    iteratedDeriv 2
        (fun t : ℝ ↦
          Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
            ((Nat.factorial (m + 2)) : ℝ)) 0
      = iteratedDeriv 2 (fun t : ℝ ↦ c * π[m + 2] (Xs + t • Hs)) 0 := by
          congr 1
          funext t
          simp [c, Xs, Hs, RealSymmetricMatrixSpace.powerTrace_def,
            div_eq_mul_inv, mul_comm]
    _ = c * iteratedDeriv 2 (fun t : ℝ ↦ π[m + 2] (Xs + t • Hs)) 0 := by
          rw [iteratedDeriv_const_mul_field]
    _ = c * ((iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs]) := by
          rw [hslice]
    _ = c * ((m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam) ^ (m - p) * (K * ((Matrix.diagonal lam) ^ p * K))))) := by
          rw [hpower]
    _ = c * ((m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))) := by
          congr 2
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hterm p
    _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
          (Finset.sum (Finset.range (m + 1)) fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)) := by
          calc
            c * ((m + 2 : ℝ) *
                Finset.sum (Finset.range (m + 1)) (fun p ↦
                  Matrix.trace
                    ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)))
              = (c * (m + 2 : ℝ)) *
                  Finset.sum (Finset.range (m + 1)) (fun p ↦
                    Matrix.trace
                      ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)) := by
                        ring
            _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
                  Finset.sum (Finset.range (m + 1)) (fun p ↦
                    Matrix.trace
                      ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)) := by
                        rw [hcoeff]

/-- Helper for Proposition 6.35: the diagonal affine slice stays symmetric when the direction is
symmetric. -/
private theorem diagonalAffineSlice_transpose_eq_self
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (t : ℝ) :
    Matrix.transpose (Matrix.diagonal lam + t • K) = Matrix.diagonal lam + t • K := by
  -- The diagonal term is symmetric, and the direction keeps that symmetry after scalar scaling.
  simp [Matrix.transpose_add, hK]

/-- Helper for Proposition 6.35: every within-iterated derivative of a tail coefficient is
ordinary differentiable at interior points of `(-1, 1)`. -/
private theorem differentiableAt_iteratedDerivWithin_traceExpTailCoeff
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (m a : ℕ) {t : ℝ} (_ha : a ≤ 2) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    DifferentiableAt ℝ
      (iteratedDerivWithin a
        (fun s : ℝ ↦
          Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
            ((Nat.factorial (m + 2)) : ℝ))
        (Set.Ioo (-1 : ℝ) 1))
      t := by
  -- TODO: after the affine-slice calculus layer is repaired, this follows from smoothness of the
  -- polynomial tail coefficient on the open interval `(-1, 1)`.
  let f : ℝ → ℝ := fun s : ℝ ↦
    Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
      ((Nat.factorial (m + 2)) : ℝ)
  have hcont : ContDiff ℝ ⊤ f := by
    have htrace : ContDiff ℝ ⊤ (fun M : Mat ↦ Matrix.trace M) := by
      -- The bundled ambient trace map is smooth of all orders on the Frobenius owner.
      simpa [Function.comp, traceContinuousLinearMap_apply] using
        (traceContinuousLinearMap (n := n)).contDiff
    have hline : ContDiff ℝ ⊤ (fun s : ℝ ↦ Matrix.diagonal lam + s • K) := by
      -- The coefficient slice is an affine line in ambient matrix space.
      fun_prop
    have hpow : ContDiff ℝ ⊤ (fun M : Mat ↦ M ^ (m + 2)) := by
      -- Matrix powers are polynomial, hence smooth of all orders.
      fun_prop
    have htracePow : ContDiff ℝ ⊤
        (fun s : ℝ ↦ Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2))) := by
      -- First compose the affine slice with the power map, then evaluate the trace.
      simpa [Function.comp] using htrace.comp (hpow.comp hline)
    have hconst : ContDiff ℝ ⊤ (fun _ : ℝ ↦ (((Nat.factorial (m + 2)) : ℝ)⁻¹)) :=
      contDiff_const
    simpa [f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hconst.mul htracePow)
  have hcontOn : ContDiffOn ℝ ⊤ f (Set.Ioo (-1 : ℝ) 1) := hcont.contDiffOn
  have hdiffWithin :
      DifferentiableWithinAt ℝ
        (iteratedDerivWithin a f (Set.Ioo (-1 : ℝ) 1))
        (Set.Ioo (-1 : ℝ) 1) t := by
    -- On the open interval, smooth coefficient slices have differentiable iterated derivatives.
    exact
      hcontOn t ht |>.differentiableWithinAt_iteratedDerivWithin
        (by simp)
        (by simpa [Set.insert_eq_of_mem ht] using uniqueDiffOn_Ioo (-1 : ℝ) 1)
  -- Interior differentiability upgrades the within-derivative to an ordinary derivative.
  exact hdiffWithin.differentiableAt (isOpen_Ioo.mem_nhds ht)

/-- Helper for Proposition 6.35: the first within-derivatives of the degree-`m + 2` tail
coefficients are summable locally uniformly on `(-1, 1)`. -/
private theorem summableLocallyUniformlyOn_iteratedDerivWithin_one_traceExpTailCoeff
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    SummableLocallyUniformlyOn
      (fun m : ℕ ↦
        iteratedDerivWithin 1
          (fun t : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1))
      (Set.Ioo (-1 : ℝ) 1) := by
  rcases
      traceExpAffineSliceDerivBound (n := n) (A := Matrix.diagonal lam) (B := K) with
    ⟨u, hu, hu_bound⟩
  let v : ℕ → ℝ := fun m ↦ u (m + 1)
  -- Package the global affine-slice derivative majorant as a locally uniform bound on every
  -- compact subset of `(-1, 1)`.
  refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_Ioo ?_
  intro Kc hKc hKc_compact
  refine ⟨v, ?_, ?_⟩
  · -- Shifting the summable majorant by one index keeps it summable.
    simpa [v] using hu.comp_injective Nat.succ_injective
  · intro m t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := hKc ht
    have hderiv :
        iteratedDerivWithin 1
            (fun s : ℝ ↦
              Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
                ((Nat.factorial (m + 2)) : ℝ))
            (Set.Ioo (-1 : ℝ) 1) t =
          Matrix.trace (K * (Matrix.diagonal lam + t • K) ^ (m + 1)) /
            ((Nat.factorial (m + 1)) : ℝ) := by
      -- On the open interval, the first within-derivative is the ordinary derivative supplied by
      -- the affine-slice power-term differentiation lemma.
      rw [iteratedDerivWithin_one]
      exact
        (traceExpAffineSliceTerm_hasDerivAt
          (n := n) (A := Matrix.diagonal lam) (B := K) (m := m + 1) t
        ).hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ioo (-1 : ℝ) 1).uniqueDiffWithinAt ht')
    calc
      ‖iteratedDerivWithin 1
          (fun s : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1) t‖
        =
          ‖Matrix.trace (K * (Matrix.diagonal lam + t • K) ^ (m + 1)) /
            ((Nat.factorial (m + 1)) : ℝ)‖ := by
              rw [hderiv]
      _ ≤ u (m + 1) := hu_bound (m + 1) t ht'
      _ = v m := rfl

/-- Helper for Proposition 6.35: each tail coefficient is `C²` along the diagonal affine slice. -/
private theorem traceExpTailCoeff_contDiffAtTwo
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) (m : ℕ) (t : ℝ) :
    ContDiffAt ℝ 2
      (fun s : ℝ ↦
        Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
          ((Nat.factorial (m + 2)) : ℝ))
      t := by
  let f : ℝ → ℝ := fun s : ℝ ↦
    Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
      ((Nat.factorial (m + 2)) : ℝ)
  have hcont : ContDiff ℝ ⊤ f := by
    have htrace : ContDiff ℝ ⊤ (fun M : Mat ↦ Matrix.trace M) := by
      -- The bundled trace map is smooth on the ambient Frobenius matrix surface.
      simpa [Function.comp, traceContinuousLinearMap_apply] using
        (traceContinuousLinearMap (n := n)).contDiff
    have hline : ContDiff ℝ ⊤ (fun s : ℝ ↦ Matrix.diagonal lam + s • K) := by
      -- The coefficient slice is an affine line in the ambient matrix algebra.
      fun_prop
    have hpow : ContDiff ℝ ⊤ (fun M : Mat ↦ M ^ (m + 2)) := by
      -- Matrix powers are polynomial, so they are smooth of all orders.
      fun_prop
    have htracePow : ContDiff ℝ ⊤
        (fun s : ℝ ↦ Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2))) := by
      -- Compose the affine slice with the power map before applying trace.
      simpa [Function.comp] using htrace.comp (hpow.comp hline)
    have hconst : ContDiff ℝ ⊤ (fun _ : ℝ ↦ (((Nat.factorial (m + 2)) : ℝ)⁻¹)) :=
      contDiff_const
    simpa [f, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hconst.mul htracePow)
  exact (hcont.of_le (by simp : (2 : WithTop ℕ∞) ≤ ⊤)).contDiffAt

/-- Helper for Proposition 6.35: the degree-`m + 2` exponential tail coefficients form a
pointwise summable series. -/
private theorem summable_traceExpTailCoeff
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Summable
      (fun m : ℕ ↦
        Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
          ((Nat.factorial (m + 2)) : ℝ)) := by
  letI : CompleteSpace Mat := FiniteDimensional.complete ℝ Mat
  let X : Mat := Matrix.diagonal lam + t • K
  have hsum :
      Summable
        (fun m : ℕ ↦ Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • X ^ m)) := by
    -- The ambient exponential series stays summable after applying the continuous trace map.
    simpa [traceContinuousLinearMap_apply] using
      (expSeries_summable' (𝕂 := ℝ) X).mapL (traceContinuousLinearMap (n := n))
  have hshift : Function.Injective (fun m : ℕ ↦ m + 2) := by
    intro a b hab
    exact Nat.succ.inj <| Nat.succ.inj hab
  -- The tail series is the doubly shifted exponential trace series.
  simpa [X, div_eq_mul_inv, Matrix.trace_smul, mul_comm, mul_left_comm, mul_assoc] using
    hsum.comp_injective hshift

/-- Helper for Proposition 6.35: at interior points of `(-1, 1)`, the second within-derivative
of a tail coefficient matches the Proposition 6.33 Frobenius insertion sum at the translated
base point. -/
private theorem iteratedDerivWithin_two_traceExpTailCoeff_eq_frobeniusSum
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (m : ℕ) {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    iteratedDerivWithin 2
        (fun s : ℝ ↦
          Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
            ((Nat.factorial (m + 2)) : ℝ))
        (Set.Ioo (-1 : ℝ) 1) t =
      ((((Nat.factorial (m + 1)) : ℝ)⁻¹) *
        (Finset.sum (Finset.range (m + 1)) fun p ↦
          Matrix.trace
            ((((Matrix.diagonal lam + t • K) ^ p * K *
                (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))) := by
  let f : ℝ → ℝ := fun s : ℝ ↦
    Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
      ((Nat.factorial (m + 2)) : ℝ)
  let Xs : SymmMat :=
    ⟨Matrix.diagonal lam + t • K, by
      rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
      exact diagonalAffineSlice_transpose_eq_self lam K hK t⟩
  let Hs : SymmMat :=
    ⟨K, by
      rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
      exact hK⟩
  let c : ℝ := (((Nat.factorial (m + 2)) : ℕ) : ℝ)⁻¹
  have hk : 1 ≤ m + 2 := by omega
  have hpowerTraceContDiffAt : ContDiffAt ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs := by
    simpa using (powerTrace_contDiff (n := n) (m + 2) hk).contDiffAt
  have hwithin :
      iteratedDerivWithin 2 f (Set.Ioo (-1 : ℝ) 1) t = iteratedDeriv 2 f t := by
    -- Interior points of the open interval may be treated with the ordinary iterated derivative.
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Ioo (-1 : ℝ) 1)
        (traceExpTailCoeff_contDiffAtTwo lam K m t)
        ht
  have hshift :
      iteratedDeriv 2 f t = iteratedDeriv 2 (fun s : ℝ ↦ f (t + s)) 0 := by
    -- Shift the scalar variable so the second derivative is evaluated at the origin.
    have hshift' :
        iteratedDeriv 2 (fun s : ℝ ↦ f (t + s)) 0 = iteratedDeriv 2 f t := by
      simpa using congrArg (fun h : ℝ → ℝ ↦ h 0) (iteratedDeriv_comp_const_add 2 f t)
    exact hshift'.symm
  have hslice :
      iteratedDeriv 2 (fun s : ℝ ↦ π[m + 2] (Xs + s • Hs)) 0 =
        (iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs] := by
    -- Proposition 6.33 already identifies the scalar slice Hessian with the repeated
    -- Fréchet derivative on the intrinsic symmetric-matrix carrier.
    simpa using
      sliceSecondDeriv_eq_iteratedFDerivTwo
        (n := n) (f := (π[m + 2] : SymmMat → ℝ)) (X := Xs) (H := Hs)
        hpowerTraceContDiffAt
  have hpower :
      (iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs] =
        (m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam + t • K) ^ (m - p) *
                (K * (((Matrix.diagonal lam + t • K) ^ p) * K)))) := by
    -- Rewrite the Proposition 6.33 Frobenius sum back to ambient matrix powers at the shifted
    -- diagonal base point.
    simpa [Xs, Hs, Matrix.transpose_mul, Matrix.mul_assoc, hK] using
      powerTrace_iteratedFDeriv_two_eq_frobenius_sum
        (n := n) (k := m + 2) hk Xs Hs
  have hcoeff :
      c * (m + 2 : ℝ) = (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
    -- Normalize the factorial coefficient after the second derivative contributes `m + 2`.
    have hm2 : (m + 2 : ℝ) ≠ 0 := by positivity
    have hfac :
        ((Nat.factorial (m + 2)) : ℝ) =
          (m + 2 : ℝ) * ((Nat.factorial (m + 1)) : ℝ) := by
      exact_mod_cast (Nat.factorial_succ (m + 1))
    calc
      c * (m + 2 : ℝ) = ((Nat.factorial (m + 2) : ℝ)⁻¹) * (m + 2 : ℝ) := by rfl
      _ = ((((m + 2 : ℝ) * ((Nat.factorial (m + 1)) : ℝ)))⁻¹) * (m + 2 : ℝ) := by rw [hfac]
      _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
            field_simp [hm2]
  have hsliceTerm :
      ∀ p : ℕ,
        Matrix.trace
            ((Matrix.diagonal lam + t • K) ^ (m - p) *
              (K * (((Matrix.diagonal lam + t • K) ^ p) * K))) =
          Matrix.trace
            ((((Matrix.diagonal lam + t • K) ^ p * K *
                (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K) := by
    intro p
    have hA :
        Matrix.transpose (Matrix.diagonal lam + t • K) =
          Matrix.diagonal lam + t • K :=
      diagonalAffineSlice_transpose_eq_self lam K hK t
    simp [Matrix.transpose_mul, Matrix.mul_assoc, hA, hK]
  calc
    iteratedDerivWithin 2 f (Set.Ioo (-1 : ℝ) 1) t = iteratedDeriv 2 f t := hwithin
    _ = iteratedDeriv 2 (fun s : ℝ ↦ f (t + s)) 0 := hshift
    _ = iteratedDeriv 2 (fun s : ℝ ↦ c * π[m + 2] (Xs + s • Hs)) 0 := by
          congr 1
          funext s
          simp [f, c, Xs, Hs, RealSymmetricMatrixSpace.powerTrace_def,
            div_eq_mul_inv, add_smul, add_assoc, add_left_comm, add_comm,
            mul_comm]
    _ = c * iteratedDeriv 2 (fun s : ℝ ↦ π[m + 2] (Xs + s • Hs)) 0 := by
          rw [iteratedDeriv_const_mul_field]
    _ = c * ((iteratedFDeriv ℝ 2 (π[m + 2] : SymmMat → ℝ) Xs) ![Hs, Hs]) := by
          rw [hslice]
    _ =
        c * ((m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((Matrix.diagonal lam + t • K) ^ (m - p) *
                (K * (((Matrix.diagonal lam + t • K) ^ p) * K))))) := by
          rw [hpower]
    _ =
        c * ((m + 2 : ℝ) *
          Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((((Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))) := by
          congr 2
          refine Finset.sum_congr rfl ?_
          intro p hp
          exact hsliceTerm p
    _ =
        (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
          (Finset.sum (Finset.range (m + 1)) fun p ↦
            Matrix.trace
              ((((Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)) := by
          calc
            c * ((m + 2 : ℝ) *
                Finset.sum (Finset.range (m + 1)) (fun p ↦
                  Matrix.trace
                    ((((Matrix.diagonal lam + t • K) ^ p * K *
                        (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)))
              = (c * (m + 2 : ℝ)) *
                  Finset.sum (Finset.range (m + 1)) (fun p ↦
                    Matrix.trace
                      ((((Matrix.diagonal lam + t • K) ^ p * K *
                          (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)) := by
                        ring
            _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
                  Finset.sum (Finset.range (m + 1)) (fun p ↦
                    Matrix.trace
                      ((((Matrix.diagonal lam + t • K) ^ p * K *
                          (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)) := by
                        rw [hcoeff]

/-- Helper for Proposition 6.35: the second within-derivatives of the degree-`m + 2` tail
coefficients are summable locally uniformly on `(-1, 1)`. -/
private theorem summableLocallyUniformlyOn_iteratedDerivWithin_two_traceExpTailCoeff
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) :
    SummableLocallyUniformlyOn
      (fun m : ℕ ↦
        iteratedDerivWithin 2
          (fun t : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1))
      (Set.Ioo (-1 : ℝ) 1) := by
  let C : ℝ :=
    ‖traceContinuousLinearMap (n := n)‖ * ‖K‖ * ‖K‖ * ‖(1 : Mat)‖ * ‖(1 : Mat)‖
  let R : ℝ := ‖Matrix.diagonal lam‖ + ‖K‖
  let v : ℕ → ℝ := fun m ↦ C * (R ^ m / ((Nat.factorial m) : ℝ))
  -- Package the global factorial-decaying majorant as a locally uniform order-2 estimate.
  refine SummableLocallyUniformlyOn_of_locally_bounded isOpen_Ioo ?_
  intro Kc hKc hKc_compact
  refine ⟨v, ?_, ?_⟩
  · -- The majorant is a scalar multiple of the exponential series.
    have hpow : Summable (fun m : ℕ ↦ R ^ m / ((Nat.factorial m) : ℝ)) :=
      Real.summable_pow_div_factorial R
    simpa [v, C, R, mul_assoc] using hpow.mul_left C
  · intro m t ht
    have ht' : t ∈ Set.Ioo (-1 : ℝ) 1 := hKc ht
    have ht_abs : |t| ≤ 1 := by
      exact (abs_lt.mpr ⟨by linarith [ht'.1], by linarith [ht'.2]⟩).le
    have hsmul_norm : ‖t • K‖ ≤ ‖K‖ := by
      rw [norm_smul]
      calc
        |t| * ‖K‖ ≤ 1 * ‖K‖ := by
          exact mul_le_mul_of_nonneg_right ht_abs (norm_nonneg _)
        _ = ‖K‖ := by ring
    have hline_norm : ‖Matrix.diagonal lam + t • K‖ ≤ R := by
      calc
        ‖Matrix.diagonal lam + t • K‖ ≤ ‖Matrix.diagonal lam‖ + ‖t • K‖ := norm_add_le _ _
        _ ≤ ‖Matrix.diagonal lam‖ + ‖K‖ := by gcongr
        _ = R := rfl
    have hR_nonneg : 0 ≤ R := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hpow_bound :
        ∀ k : ℕ,
          ‖(Matrix.diagonal lam + t • K) ^ k‖ ≤ ‖(1 : Mat)‖ * R ^ k := by
      intro k
      induction k with
      | zero =>
          simp
      | succ j ih =>
          calc
            ‖(Matrix.diagonal lam + t • K) ^ (j + 1)‖
                = ‖(Matrix.diagonal lam + t • K) ^ j * (Matrix.diagonal lam + t • K)‖ := by
                    rw [pow_succ]
            _ ≤ ‖(Matrix.diagonal lam + t • K) ^ j‖ * ‖Matrix.diagonal lam + t • K‖ := by
                  exact norm_mul_le _ _
            _ ≤ (‖(1 : Mat)‖ * R ^ j) * ‖Matrix.diagonal lam + t • K‖ := by
                  exact mul_le_mul_of_nonneg_right ih (norm_nonneg _)
            _ ≤ (‖(1 : Mat)‖ * R ^ j) * R := by
                  exact mul_le_mul_of_nonneg_left hline_norm
                    (mul_nonneg (norm_nonneg _) (pow_nonneg hR_nonneg _))
            _ = ‖(1 : Mat)‖ * R ^ (j + 1) := by
                  rw [pow_succ]
                  ring
    have hterm_bound :
        ∀ p ∈ Finset.range (m + 1),
          ‖Matrix.trace
              ((((Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)‖
            ≤ C * R ^ m := by
      intro p hp
      have hp_le : p ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hpow_split : R ^ p * R ^ (m - p) = R ^ m := by
        simpa [Nat.add_sub_of_le hp_le] using (pow_add R p (m - p)).symm
      calc
        ‖Matrix.trace
            ((((Matrix.diagonal lam + t • K) ^ p * K *
                (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)‖
          ≤ ‖traceContinuousLinearMap (n := n)‖ *
              ‖(((Matrix.diagonal lam + t • K) ^ p * K *
                    (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K‖ := by
                simpa [traceContinuousLinearMap_apply] using
                  (ContinuousLinearMap.le_opNorm
                    (traceContinuousLinearMap (n := n))
                    ((((Matrix.diagonal lam + t • K) ^ p * K *
                        (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))
        _ ≤ ‖traceContinuousLinearMap (n := n)‖ *
              (‖((Matrix.diagonal lam + t • K) ^ p * K *
                    (Matrix.diagonal lam + t • K) ^ (m - p)).transpose‖ * ‖K‖) := by
                gcongr
                exact norm_mul_le _ _
        _ = ‖traceContinuousLinearMap (n := n)‖ *
              (‖(Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)‖ * ‖K‖) := by
                have hnorm :
                    ‖((Matrix.diagonal lam + t • K) ^ p * K *
                        (Matrix.diagonal lam + t • K) ^ (m - p)).transpose‖ =
                      ‖(Matrix.diagonal lam + t • K) ^ p * K *
                        (Matrix.diagonal lam + t • K) ^ (m - p)‖ := by
                  simpa [proposition635AmbientMatrixNormedRing] using
                    (Matrix.frobenius_norm_transpose
                      ((Matrix.diagonal lam + t • K) ^ p * K *
                        (Matrix.diagonal lam + t • K) ^ (m - p)))
                rw [hnorm]
        _ ≤ ‖traceContinuousLinearMap (n := n)‖ *
              (((‖(Matrix.diagonal lam + t • K) ^ p‖ * ‖K‖) *
                  ‖(Matrix.diagonal lam + t • K) ^ (m - p)‖) * ‖K‖) := by
                gcongr
                calc
                  ‖(Matrix.diagonal lam + t • K) ^ p * K *
                      (Matrix.diagonal lam + t • K) ^ (m - p)‖
                    ≤ ‖(Matrix.diagonal lam + t • K) ^ p * K‖ *
                        ‖(Matrix.diagonal lam + t • K) ^ (m - p)‖ := norm_mul_le _ _
                  _ ≤ (‖(Matrix.diagonal lam + t • K) ^ p‖ * ‖K‖) *
                        ‖(Matrix.diagonal lam + t • K) ^ (m - p)‖ := by
                        gcongr
                        exact norm_mul_le _ _
        _ ≤ ‖traceContinuousLinearMap (n := n)‖ *
              (((‖(1 : Mat)‖ * R ^ p) * ‖K‖) *
                  (‖(1 : Mat)‖ * R ^ (m - p)) * ‖K‖) := by
                have hpowp := hpow_bound p
                have hpowmp := hpow_bound (m - p)
                have hleft :
                    (‖(Matrix.diagonal lam + t • K) ^ p‖ * ‖K‖) ≤
                      ((‖(1 : Mat)‖ * R ^ p) * ‖K‖) := by
                  exact mul_le_mul_of_nonneg_right hpowp (norm_nonneg _)
                have hmid :
                    ((‖(Matrix.diagonal lam + t • K) ^ p‖ * ‖K‖) *
                        ‖(Matrix.diagonal lam + t • K) ^ (m - p)‖) ≤
                      (((‖(1 : Mat)‖ * R ^ p) * ‖K‖) *
                        (‖(1 : Mat)‖ * R ^ (m - p))) := by
                  exact mul_le_mul hleft hpowmp (norm_nonneg _) <|
                    mul_nonneg
                      (mul_nonneg (norm_nonneg _) (pow_nonneg hR_nonneg _))
                      (norm_nonneg _)
                have hright :
                    (((‖(Matrix.diagonal lam + t • K) ^ p‖ * ‖K‖) *
                        ‖(Matrix.diagonal lam + t • K) ^ (m - p)‖) * ‖K‖) ≤
                      ((((‖(1 : Mat)‖ * R ^ p) * ‖K‖) *
                        (‖(1 : Mat)‖ * R ^ (m - p))) * ‖K‖) := by
                  exact mul_le_mul_of_nonneg_right hmid (norm_nonneg _)
                exact mul_le_mul_of_nonneg_left hright (norm_nonneg _)
        _ = ‖traceContinuousLinearMap (n := n)‖ *
              (‖K‖ * ‖K‖ * ‖(1 : Mat)‖ * ‖(1 : Mat)‖ * (R ^ p * R ^ (m - p))) := by
              ring
        _ = C * R ^ m := by
              rw [hpow_split]
              ring
    have hsum_bound :
        ‖Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((((Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))‖
          ≤ (m + 1 : ℝ) * (C * R ^ m) := by
      calc
        ‖Finset.sum (Finset.range (m + 1)) (fun p ↦
            Matrix.trace
              ((((Matrix.diagonal lam + t • K) ^ p * K *
                  (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))‖
          ≤ Finset.sum (Finset.range (m + 1)) (fun p ↦
              ‖Matrix.trace
                  ((((Matrix.diagonal lam + t • K) ^ p * K *
                      (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K)‖) := by
                exact norm_sum_le _ _
        _ ≤ Finset.sum (Finset.range (m + 1)) (fun _ : ℕ ↦ C * R ^ m) := by
              exact Finset.sum_le_sum fun p hp ↦ hterm_bound p hp
        _ = (m + 1 : ℝ) * (C * R ^ m) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    have hfactor_nonneg : 0 ≤ (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    have hfactorial_pos : 0 < ((Nat.factorial m) : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.factorial_pos m)
    calc
      ‖iteratedDerivWithin 2
          (fun s : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + s • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1) t‖
        =
          ‖(((Nat.factorial (m + 1)) : ℝ)⁻¹) *
            Finset.sum (Finset.range (m + 1)) (fun p ↦
              Matrix.trace
                ((((Matrix.diagonal lam + t • K) ^ p * K *
                    (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))‖ := by
              rw [iteratedDerivWithin_two_traceExpTailCoeff_eq_frobeniusSum lam K hK m ht']
      _ = (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
            ‖Finset.sum (Finset.range (m + 1)) (fun p ↦
                Matrix.trace
                  ((((Matrix.diagonal lam + t • K) ^ p * K *
                      (Matrix.diagonal lam + t • K) ^ (m - p)).transpose) * K))‖ := by
              rw [norm_mul, Real.norm_of_nonneg hfactor_nonneg]
      _ ≤ (((Nat.factorial (m + 1)) : ℝ)⁻¹) * ((m + 1 : ℝ) * (C * R ^ m)) := by
            exact mul_le_mul_of_nonneg_left hsum_bound hfactor_nonneg
      _ = C * (R ^ m / ((Nat.factorial m) : ℝ)) := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp [hfactorial_pos.ne']
      _ = v m := by
            simp [v, C, R]

/-- Helper for Proposition 6.35: the full range of mixed trace terms at total degree `m` is
bounded by `(m + 1)` copies of the pure diagonal power weight. -/
private theorem mixedTraceSum_le_diagonalPowerWeight
    [Nonempty (Fin n)] (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (hlam : ∀ i : Fin n, 0 ≤ lam i) (m : ℕ) :
    (Finset.sum (Finset.range (m + 1)) fun p ↦
      Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))
      ≤ (m + 1 : ℝ) * Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) := by
  have hpointwise :
      ∀ p ∈ Finset.range (m + 1),
        Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K) ≤
          Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) := by
    intro r hr
    have hr_le : r ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hsum_nat : r + (m - r) = m := Nat.add_sub_of_le hr_le
    have hdiagPow (k : ℕ) :
        Matrix.diagonal (lam ^ k) = Matrix.diagonal (fun i ↦ lam i ^ k) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal]
      · simp [Matrix.diagonal, hij]
    have hmixed :
        Matrix.trace ((Matrix.diagonal lam) ^ r * K * (Matrix.diagonal lam) ^ (m - r) * K) =
          ∑ i : Fin n, ∑ j : Fin n, lam i ^ r * (K i j) ^ (2 : ℕ) * lam j ^ (m - r) := by
      -- Expand the mixed trace term as a weighted square sum with diagonal weights.
      calc
        Matrix.trace ((Matrix.diagonal lam) ^ r * K * (Matrix.diagonal lam) ^ (m - r) * K)
          = Matrix.trace
              (Matrix.diagonal (fun i ↦ lam i ^ r) * K *
                Matrix.diagonal (fun j ↦ lam j ^ (m - r)) * K) := by
                rw [Matrix.diagonal_pow, Matrix.diagonal_pow, hdiagPow r, hdiagPow (m - r)]
        _ = ∑ i : Fin n, ∑ j : Fin n, lam i ^ r * (K i j) ^ (2 : ℕ) * lam j ^ (m - r) := by
              simpa using
                diagonal_weighted_trace_eq_sumSquares
                  (fun i ↦ lam i ^ r)
                  (fun j ↦ lam j ^ (m - r))
                  K hK
    have hweighted :
        ∑ i : Fin n, ∑ j : Fin n, lam i ^ r * (K i j) ^ (2 : ℕ) * lam j ^ (m - r)
          ≤
            ∑ i : Fin n, ∑ j : Fin n, lam i ^ m * (K i j) ^ (2 : ℕ) := by
      -- Lemma 6.14 compares each mixed diagonal weight to the pure power weight `lam^m`.
      let pnn : NNReal := ((m - r : ℕ) : NNReal)
      let qnn : NNReal := ((r : ℕ) : NNReal)
      have hpnn : (pnn : ℝ) = (m - r : ℕ) := rfl
      have hqnn : (qnn : ℝ) = (r : ℕ) := rfl
      have hpq : ((pnn + qnn : NNReal) : ℝ) = m := by
        change ((m - r : ℕ) : ℝ) + r = m
        exact_mod_cast (show (m - r) + r = m by omega)
      have hcore :=
        weightedMixedSquares_le_powerSquares
          (p := pnn)
          (q := qnn)
          hK hlam
      convert hcore using 1
      · simp [hpnn, hqnn, Real.rpow_natCast]
      · simp [hpq, Real.rpow_natCast]
    have hpair :
        Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) =
          ∑ i : Fin n, ∑ j : Fin n, lam i ^ m * (K i j) ^ (2 : ℕ) := by
      -- Expand the pure diagonal power weight in the same weighted-square normal form.
      calc
        Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)
          = Matrix.trace
              (Matrix.diagonal (fun i ↦ lam i ^ m) * K *
                Matrix.diagonal (fun _ : Fin n ↦ (1 : ℝ)) * K) := by
                simp [Matrix.mul_assoc]
        _ = ∑ i : Fin n, ∑ j : Fin n, lam i ^ m * (K i j) ^ (2 : ℕ) * (1 : ℝ) := by
              simpa using
                diagonal_weighted_trace_eq_sumSquares
                  (fun i ↦ lam i ^ m)
                  (fun _ : Fin n ↦ (1 : ℝ))
                  K hK
        _ = ∑ i : Fin n, ∑ j : Fin n, lam i ^ m * (K i j) ^ (2 : ℕ) := by
              simp
    -- Compare the mixed weighted-square expansion to the pure one and then return to trace form.
    calc
      Matrix.trace ((Matrix.diagonal lam) ^ r * K * (Matrix.diagonal lam) ^ (m - r) * K)
        = ∑ i : Fin n, ∑ j : Fin n, lam i ^ r * (K i j) ^ (2 : ℕ) * lam j ^ (m - r) := hmixed
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, lam i ^ m * (K i j) ^ (2 : ℕ) := hweighted
      _ = Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) := hpair.symm
  -- Sum the pointwise diagonal-power bound over all `p = 0, ..., m`.
  calc
    (Finset.sum (Finset.range (m + 1)) fun p ↦
      Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))
      ≤
        Finset.sum (Finset.range (m + 1)) fun _ : ℕ ↦
          Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) := by
            exact Finset.sum_le_sum fun p hp ↦ hpointwise p hp
    _ = (m + 1 : ℝ) * Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

/-- Helper for Proposition 6.35: every factorial-normalized mixed trace coefficient at a
nonnegative diagonal base point is nonnegative. -/
private theorem mixedTraceSum_nonneg
    [Nonempty (Fin n)] (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (hlam : ∀ i : Fin n, 0 ≤ lam i) (m : ℕ) :
    0 ≤
      ((((Nat.factorial (m + 1)) : ℝ)⁻¹) *
        (Finset.sum (Finset.range (m + 1)) fun p ↦
          Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))) := by
  have hterm_nonneg :
      ∀ p ∈ Finset.range (m + 1),
        0 ≤ Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K) := by
    intro p hp
    have hp_le : p ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    have hdiagPow (k : ℕ) :
        Matrix.diagonal (lam ^ k) = Matrix.diagonal (fun i ↦ lam i ^ k) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal]
      · simp [Matrix.diagonal, hij]
    have hmixed :
        Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K) =
          ∑ i : Fin n, ∑ j : Fin n, lam i ^ p * (K i j) ^ (2 : ℕ) * lam j ^ (m - p) := by
      -- Expand the mixed trace term into its weighted square-sum normal form.
      calc
        Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)
          = Matrix.trace
              (Matrix.diagonal (fun i ↦ lam i ^ p) * K *
                Matrix.diagonal (fun j ↦ lam j ^ (m - p)) * K) := by
                rw [Matrix.diagonal_pow, Matrix.diagonal_pow, hdiagPow p, hdiagPow (m - p)]
        _ = ∑ i : Fin n, ∑ j : Fin n, lam i ^ p * (K i j) ^ (2 : ℕ) * lam j ^ (m - p) := by
              simpa using
                diagonal_weighted_trace_eq_sumSquares
                  (fun i ↦ lam i ^ p)
                  (fun j ↦ lam j ^ (m - p))
                  K hK
    have hsum_nonneg :
        0 ≤ ∑ i : Fin n, ∑ j : Fin n, lam i ^ p * (K i j) ^ (2 : ℕ) * lam j ^ (m - p) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      refine Finset.sum_nonneg ?_
      intro j hj
      have hi_nonneg : 0 ≤ lam i ^ p := pow_nonneg (hlam i) _
      have hj_nonneg : 0 ≤ lam j ^ (m - p) := pow_nonneg (hlam j) _
      have hk_nonneg : 0 ≤ (K i j) ^ (2 : ℕ) := by
        exact sq_nonneg (K i j)
      exact mul_nonneg (mul_nonneg hi_nonneg hk_nonneg) hj_nonneg
    rw [hmixed]
    exact hsum_nonneg
  have hsum_nonneg :
      0 ≤
        Finset.sum (Finset.range (m + 1)) fun p ↦
          Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K) := by
    exact Finset.sum_nonneg fun p hp ↦ hterm_nonneg p hp
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) hsum_nonneg

/-- Helper for Proposition 6.35: the diagonal power-weight series against `K * K` is summable. -/
private theorem summable_diagonalPowerWeight
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    Summable
      (fun m : ℕ ↦ (((Nat.factorial m) : ℝ)⁻¹) *
        Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)) := by
  letI : CompleteSpace Mat := FiniteDimensional.complete ℝ Mat
  let D : Mat := Matrix.diagonal lam
  let rightMul : Mat →L[ℝ] Mat :=
    ⟨LinearMap.mulRight ℝ (K * K), (LinearMap.mulRight ℝ (K * K)).continuous_of_finiteDimensional⟩
  have hdiagPow (m : ℕ) :
      Matrix.diagonal (lam ^ m) = Matrix.diagonal (fun i ↦ lam i ^ m) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hrightSummable :
      Summable (fun m : ℕ ↦ ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) * (K * K)) := by
    -- Right multiplication preserves summability of the exponential power series on `D`.
    simpa [rightMul, Matrix.mul_assoc] using (expSeries_summable' (𝕂 := ℝ) D).mapL rightMul
  -- Apply the continuous trace map termwise to the right-multiplied exponential series.
  simpa [D, Matrix.diagonal_pow, hdiagPow, div_eq_mul_inv, Matrix.trace_smul, Matrix.mul_assoc]
    using hrightSummable.mapL (traceContinuousLinearMap (n := n))

/-- Helper for Proposition 6.35: resumming the diagonal power weights against the exponential
series recovers the exponential diagonal weight exactly. -/
private theorem tsum_diagonalPowerWeight_eq_traceExpSquareWeight
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ) :
    ∑' m : ℕ, (((Nat.factorial m) : ℝ)⁻¹) *
        Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) =
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) := by
  letI : CompleteSpace Mat := FiniteDimensional.complete ℝ Mat
  let D : Mat := Matrix.diagonal lam
  let rightMul : Mat →L[ℝ] Mat :=
    ⟨LinearMap.mulRight ℝ (K * K), (LinearMap.mulRight ℝ (K * K)).continuous_of_finiteDimensional⟩
  have hdiagPow (m : ℕ) :
      Matrix.diagonal (lam ^ m) = Matrix.diagonal (fun i ↦ lam i ^ m) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hdiagExp :
      Matrix.diagonal (exp lam) = Matrix.diagonal (fun i ↦ Real.exp (lam i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Real.exp_eq_exp_ℝ]
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  have hrightSummable :
      Summable (fun m : ℕ ↦ ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) * (K * K)) := by
    -- Right multiplication by the fixed matrix `K * K` preserves summability of the exponential
    -- power series on the diagonal matrix `D`.
    simpa [rightMul, Matrix.mul_assoc] using (expSeries_summable' (𝕂 := ℝ) D).mapL rightMul
  have hexp :
      exp D = ∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m := by
    simpa using
      (congrArg (fun f : Mat → Mat ↦ f D) (exp_eq_tsum (𝕂 := ℝ) (𝔸 := Mat)))
  have hrightTsum :
      ∑' m : ℕ, ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) * (K * K) =
        exp D * (K * K) := by
    -- Evaluate the mapped exponential series after pushing it through right multiplication.
    calc
      ∑' m : ℕ, ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) * (K * K)
        = rightMul (∑' m : ℕ, (((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) := by
            symm
            simpa [rightMul, Matrix.mul_assoc] using
              rightMul.map_tsum (expSeries_summable' (𝕂 := ℝ) D)
      _ = exp D * (K * K) := by
            rw [hexp]
            rfl
  have htraceTsum :
      ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m * (K * K)) =
        Matrix.trace (exp D * (K * K)) := by
    -- Apply the continuous trace functional termwise to the right-multiplied exponential series.
    calc
      ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m * (K * K))
        = traceContinuousLinearMap (n := n)
            (∑' m : ℕ, ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m) * (K * K)) := by
              symm
              simpa [traceContinuousLinearMap_apply] using
                (traceContinuousLinearMap (n := n)).map_tsum hrightSummable
      _ = Matrix.trace (exp D * (K * K)) := by
            rw [hrightTsum, traceContinuousLinearMap_apply]
  calc
    ∑' m : ℕ, (((Nat.factorial m) : ℝ)⁻¹) *
        Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)
      = ∑' m : ℕ, Matrix.trace ((((Nat.factorial m : ℕ) : ℝ)⁻¹) • D ^ m * (K * K)) := by
          -- Rewrite each diagonal power-weight term as a traced scalar multiple of `D^m * K * K`.
          apply tsum_congr
          intro m
          simp [D, Matrix.diagonal_pow, hdiagPow m, Matrix.trace_smul, Matrix.mul_assoc]
    _ = Matrix.trace (exp D * (K * K)) := htraceTsum
    _ = Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) := by
          -- Evaluate the exponential of a diagonal matrix entrywise.
          rw [Matrix.exp_diagonal, hdiagExp]
          simp [Matrix.mul_assoc]

/-- Helper for Proposition 6.35: the second derivative of the diagonal trace-exponential slice is
the tsum of the second derivatives of the degree-`m + 2` tail coefficients. -/
private theorem diagTraceExpLine_iteratedDerivTwo_eq_tsumTailSecondDeriv
    (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) :
    iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0 =
      ∑' m : ℕ,
        iteratedDerivWithin 2
          (fun t : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1) 0 := by
  let g : ℝ → ℝ := fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))
  let q : ℝ → ℝ := fun t : ℝ ↦
    Matrix.trace (1 : Mat) + Matrix.trace (Matrix.diagonal lam + t • K)
  let tail : ℝ → ℝ := fun t : ℝ ↦
    ∑' m : ℕ,
      Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
        ((Nat.factorial (m + 2)) : ℝ)
  have h0I : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    norm_num
  have hsum :
      ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        Summable (fun m : ℕ ↦
          Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
            ((Nat.factorial (m + 2)) : ℝ)) := by
    intro t ht
    exact summable_traceExpTailCoeff lam K t
  have hlocal :
      ∀ k, 1 ≤ k → k ≤ 2 →
        SummableLocallyUniformlyOn
          (fun m : ℕ ↦
            iteratedDerivWithin k
              (fun t : ℝ ↦
                Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
                  ((Nat.factorial (m + 2)) : ℝ))
              (Set.Ioo (-1 : ℝ) 1))
          (Set.Ioo (-1 : ℝ) 1) := by
    intro k hk1 hk2
    interval_cases k
    · simpa using summableLocallyUniformlyOn_iteratedDerivWithin_one_traceExpTailCoeff lam K
    · simpa using summableLocallyUniformlyOn_iteratedDerivWithin_two_traceExpTailCoeff lam K hK
  have hf2 :
      ∀ m k r, k ≤ 2 → r ∈ Set.Ioo (-1 : ℝ) 1 →
        DifferentiableAt ℝ
          (iteratedDerivWithin k
            (fun t : ℝ ↦
              Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
                ((Nat.factorial (m + 2)) : ℝ))
            (Set.Ioo (-1 : ℝ) 1))
          r := by
    intro m k r hk hr
    exact differentiableAt_iteratedDerivWithin_traceExpTailCoeff lam K m k hk hr
  have htail_tsum :
      iteratedDerivWithin 2 tail (Set.Ioo (-1 : ℝ) 1) 0 =
        ∑' m : ℕ,
          iteratedDerivWithin 2
            (fun t : ℝ ↦
              Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
                ((Nat.factorial (m + 2)) : ℝ))
            (Set.Ioo (-1 : ℝ) 1) 0 := by
    -- The repaired first- and second-derivative local-uniform bounds justify termwise
    -- differentiation of the tail series on the open interval.
    simpa [tail] using
      iteratedDerivWithin_tsum
        (m := 2) (hs := isOpen_Ioo) (x := 0) h0I hsum hlocal hf2
  have htail_eq :
      tail = fun t : ℝ ↦ g t - q t := by
    funext t
    have hsplit :=
      traceExpAffineSlice_eq_traceOne_add_traceLine_add_tsumTail
        (n := n) (A := Matrix.diagonal lam) (B := K) t
    linarith
  have hgWithin : ContDiffWithinAt ℝ 2 g (Set.Ioo (-1 : ℝ) 1) 0 := by
    exact (diagTraceExpLine_contDiffAtTwo lam K).contDiffWithinAt
  have hqEq :
      q = fun t : ℝ ↦
        (Matrix.trace (1 : Mat) + Matrix.trace (Matrix.diagonal lam)) + t * Matrix.trace K := by
    funext t
    simp [q, Matrix.trace_add, Matrix.trace_smul, add_assoc, add_left_comm, add_comm]
  have hqWithin : ContDiffWithinAt ℝ 2 q (Set.Ioo (-1 : ℝ) 1) 0 := by
    -- Rewrite the remainder as an explicit affine scalar function before differentiating it.
    rw [hqEq]
    have hqCont : ContDiff ℝ 2
        (fun t : ℝ ↦
          (Matrix.trace (1 : Mat) + Matrix.trace (Matrix.diagonal lam)) + t * Matrix.trace K) := by
      fun_prop
    exact hqCont.contDiffAt.contDiffWithinAt
  have hqZero :
      iteratedDerivWithin 2 q (Set.Ioo (-1 : ℝ) 1) 0 = 0 := by
    -- The second derivative of an affine scalar function vanishes.
    have hqOrd :
        iteratedDerivWithin 2 q (Set.Ioo (-1 : ℝ) 1) 0 = iteratedDeriv 2 q 0 := by
      exact
        iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Ioo (-1 : ℝ) 1)
          (hqWithin.contDiffAt (isOpen_Ioo.mem_nhds h0I))
          h0I
    rw [hqOrd, hqEq]
    have hAffine :
        iteratedDeriv 2
            (fun t : ℝ ↦
              (Matrix.trace (1 : Mat) + Matrix.trace (Matrix.diagonal lam)) +
                t * Matrix.trace K) 0 =
          0 := by
      have hfun := affineLineIteratedDerivTwo_generic
        (x := Matrix.trace (1 : Mat) + Matrix.trace (Matrix.diagonal lam))
        (d := Matrix.trace K)
      simpa [smul_eq_mul] using congrArg (fun g : ℝ → ℝ ↦ g 0) hfun
    simpa using hAffine
  have htail_within :
      iteratedDerivWithin 2 tail (Set.Ioo (-1 : ℝ) 1) 0 =
        iteratedDerivWithin 2 g (Set.Ioo (-1 : ℝ) 1) 0 := by
    -- Subtracting the affine part does not change the second derivative.
    rw [htail_eq]
    change iteratedDerivWithin 2 (g - q) (Set.Ioo (-1 : ℝ) 1) 0 =
      iteratedDerivWithin 2 g (Set.Ioo (-1 : ℝ) 1) 0
    rw [iteratedDerivWithin_sub h0I (uniqueDiffOn_Ioo (-1 : ℝ) 1) hgWithin hqWithin, hqZero,
      sub_zero]
  calc
    iteratedDeriv 2 g 0 = iteratedDerivWithin 2 g (Set.Ioo (-1 : ℝ) 1) 0 := by
      symm
      exact
        iteratedDerivWithin_eq_iteratedDeriv
          (uniqueDiffOn_Ioo (-1 : ℝ) 1)
          (diagTraceExpLine_contDiffAtTwo lam K)
          h0I
    _ = iteratedDerivWithin 2 tail (Set.Ioo (-1 : ℝ) 1) 0 := htail_within.symm
    _ =
        ∑' m : ℕ,
          iteratedDerivWithin 2
            (fun t : ℝ ↦
              Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
                ((Nat.factorial (m + 2)) : ℝ))
            (Set.Ioo (-1 : ℝ) 1) 0 := htail_tsum

/-- Helper for Proposition 6.35: once the shifted diagonal entries are nonnegative, the diagonal
trace-exponential slice has the direct second-derivative bound by the exponential-weighted
quadratic trace. -/
private theorem diagTraceExpLine_secondDeriv_le_traceExpSquareWeight_nonneg
    [Nonempty (Fin n)] (lam : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) (hlam : ∀ i : Fin n, 0 ≤ lam i) :
    iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0 ≤
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) := by
  let term : ℕ → ℝ := fun m ↦
    iteratedDerivWithin 2
      (fun t : ℝ ↦
        Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
          ((Nat.factorial (m + 2)) : ℝ))
      (Set.Ioo (-1 : ℝ) 1) 0
  let bound : ℕ → ℝ := fun m ↦
    (((Nat.factorial m) : ℝ)⁻¹) *
      Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)
  have h0I : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
    norm_num
  have htermEq :
      ∀ m : ℕ,
        term m =
          (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
            (Finset.sum (Finset.range (m + 1)) fun p ↦
              Matrix.trace
                ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K)) := by
    intro m
    -- Normalize the tail coefficient once so the order-2 comparison can reuse the same
    -- Proposition 6.33 expansion in both the upper-bound and nonnegativity branches.
    rw [show term m =
        iteratedDerivWithin 2
          (fun t : ℝ ↦
            Matrix.trace ((Matrix.diagonal lam + t • K) ^ (m + 2)) /
              ((Nat.factorial (m + 2)) : ℝ))
          (Set.Ioo (-1 : ℝ) 1) 0 by rfl]
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Ioo (-1 : ℝ) 1)
      (traceExpTailCoeff_contDiffAtTwo lam K m 0) h0I]
    simpa using powerTraceTailCoeff_iteratedDerivTwo_eq_mixedTraceSum lam K hK m
  have hterm :
      ∀ m : ℕ, term m ≤ bound m := by
    intro m
    -- Rewrite the coefficient at `0` with Proposition 6.33 and then apply the diagonal
    -- power-weight majorization.
    rw [htermEq m]
    have hfactor_nonneg : 0 ≤ (((Nat.factorial (m + 1)) : ℝ)⁻¹) := by
      exact inv_nonneg.mpr (Nat.cast_nonneg _)
    have hfactorial_pos : 0 < ((Nat.factorial m) : ℝ) := by
      exact Nat.cast_pos.mpr (Nat.factorial_pos m)
    have hmain :
        (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
            (Finset.sum (Finset.range (m + 1)) fun p ↦
              Matrix.trace ((Matrix.diagonal lam) ^ p * K * (Matrix.diagonal lam) ^ (m - p) * K))
          ≤
            (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
              ((m + 1 : ℝ) *
                Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)) := by
      exact mul_le_mul_of_nonneg_left
        (mixedTraceSum_le_diagonalPowerWeight lam K hK hlam m)
        hfactor_nonneg
    have hcoeff :
        (((Nat.factorial (m + 1)) : ℝ)⁻¹) *
            ((m + 1 : ℝ) * Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K)) =
          bound m := by
      rw [show bound m =
          (((Nat.factorial m) : ℝ)⁻¹) *
            Matrix.trace (Matrix.diagonal (fun i ↦ lam i ^ m) * K * K) by rfl]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      field_simp [hfactorial_pos.ne']
    exact hmain.trans_eq hcoeff
  have hnonneg :
      ∀ m : ℕ, 0 ≤ term m := by
    intro m
    rw [htermEq m]
    exact mixedTraceSum_nonneg lam K hK hlam m
  have hboundSummable : Summable bound := by
    exact summable_diagonalPowerWeight lam K
  have htermSummable : Summable term := by
    exact Summable.of_nonneg_of_le hnonneg hterm hboundSummable
  -- Route correction: the second-derivative exchange is now isolated in the tail-tsum rewrite,
  -- so the closing step is purely coefficientwise comparison and exponential resummation.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0
      = ∑' m : ℕ, term m := by
          simpa [term] using diagTraceExpLine_iteratedDerivTwo_eq_tsumTailSecondDeriv lam K hK
    _ ≤ ∑' m : ℕ, bound m := by
          exact htermSummable.tsum_le_tsum hterm hboundSummable
    _ = Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) := by
          simpa [bound] using tsum_diagonalPowerWeight_eq_traceExpSquareWeight lam K

/-- Helper for Proposition 6.35: the diagonal trace-exponential slice satisfies the weighted
quadratic-trace upper bound after shifting the diagonal into the nonnegative cone. -/
private theorem diagTraceExpLine_secondDeriv_le_traceExpSquareWeight
    {n : ℕ} [Nonempty (Fin n)] (eig : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) :
    iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K))) 0 ≤
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
  let c : ℝ := ∑ i : Fin n, |eig i|
  let lam : Fin n → ℝ := fun i ↦ eig i + c
  have hlam : ∀ i : Fin n, 0 ≤ lam i := by
    -- The absolute-value shift dominates every negative diagonal entry.
    intro i
    have hi : |eig i| ≤ c := by
      dsimp [c]
      exact Finset.single_le_sum (fun j _ ↦ abs_nonneg (eig j)) (Finset.mem_univ i)
    dsimp [lam]
    linarith [neg_abs_le (eig i), hi]
  have hcore :
      iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0 ≤
        Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) :=
    diagTraceExpLine_secondDeriv_le_traceExpSquareWeight_nonneg lam K hK hlam
  have hsecondScale :
      iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0 =
        Real.exp c *
          iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K))) 0 := by
    have hfun :
        (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) =
          fun t : ℝ ↦ Real.exp c * Matrix.trace (exp (Matrix.diagonal eig + t • K)) := by
      funext t
      simpa [lam] using traceExpDiagonalShift_eq_exp_mul_traceExp eig K c t
    -- Differentiate the shifted-slice equality after pulling out the constant scalar factor.
    calc
      iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal lam + t • K))) 0
          =
            iteratedDeriv 2
              (fun t : ℝ ↦ Real.exp c * Matrix.trace (exp (Matrix.diagonal eig + t • K))) 0 := by
              rw [hfun]
      _ = Real.exp c *
            iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K))) 0 := by
              rw [iteratedDeriv_const_mul_field]
  have htraceScale :
      Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (lam i)) * K * K) =
        Real.exp c * Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
    simpa [lam] using traceExpSquareWeight_shift_eq_exp_mul eig K c
  have hscaled :
      Real.exp c *
          iteratedDeriv 2 (fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K))) 0 ≤
        Real.exp c * Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
    simpa [hsecondScale, htraceScale] using hcore
  -- Cancel the positive scalar factor introduced by the shift.
  nlinarith [Real.exp_pos c, hscaled]

section L2OperatorFinal

open scoped Matrix.Norms.L2Operator

attribute [local instance 3000] Matrix.instL2OpMetricSpace
attribute [local instance 3000] Matrix.instL2OpNormedAddCommGroup
attribute [local instance 3000] Matrix.instL2OpNormedSpace
attribute [local instance 3000] Matrix.instL2OpNormedRing
attribute [local instance 3000] Matrix.instL2OpNormedAlgebra
attribute [local instance 3000] Matrix.instCStarRing

/-- Helper for Proposition 6.35: in the operator-norm final section, package `Matrix.trace` as a
continuous linear map on ambient matrices. -/
private def traceContinuousLinearMapL2 : Mat →L[ℝ] ℝ :=
  { toLinearMap := Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)
    cont := (Matrix.traceLinearMap (n := Fin n) (α := ℝ) (R := ℝ)).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.35: evaluating the operator-norm trace package recovers `Matrix.trace`.
-/
@[simp] private theorem traceContinuousLinearMapL2_apply (M : Mat) :
    traceContinuousLinearMapL2 (n := n) M = Matrix.trace M :=
  rfl

/-- Helper for Proposition 6.35: in the operator-norm final section, bundle the canonical
inclusion `𝕊^n ↪ Mat`. -/
private def symmetricInclusionContinuousLinearMapL2 : SymmMat →L[ℝ] Mat :=
  { toLinearMap :=
      { toFun := fun X ↦ (X : Mat)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    cont := by
      exact
        ({ toFun := fun X : SymmMat ↦ (X : Mat)
           map_add' := fun _ _ ↦ rfl
           map_smul' := fun _ _ ↦ rfl } : SymmMat →ₗ[ℝ] Mat).continuous_of_finiteDimensional }

/-- Helper for Proposition 6.35: evaluating the bundled operator-norm inclusion recovers the
ambient matrix representative. -/
@[simp] private theorem symmetricInclusionContinuousLinearMapL2_apply (X : SymmMat) :
    symmetricInclusionContinuousLinearMapL2 (n := n) X = (X : Mat) :=
  rfl

/-- Helper for Proposition 6.35: under the operator norm, `A ↦ Trace (exp A)` is `C²` on ambient
matrices. -/
private theorem traceExpAmbient_contDiffTwo_l2 :
    ContDiff ℝ 2 (fun A : Mat ↦ Matrix.trace (exp A)) := by
  have hexpAnalytic : AnalyticOnNhd ℝ (exp : Mat → Mat) Set.univ := by
    intro A hA
    exact NormedSpace.exp_analytic (𝕂 := ℝ) (𝔸 := Mat) A
  have hexpContDiff : ContDiff ℝ 2 (exp : Mat → Mat) := hexpAnalytic.contDiff
  simpa [Function.comp, traceContinuousLinearMapL2_apply] using
    (traceContinuousLinearMapL2 (n := n)).contDiff.comp hexpContDiff

/-- Helper for Proposition 6.35: under the operator norm, the trace-exponential surface is `C²`
on `𝕊^n`. -/
private theorem traceExp_contDiffTwo_l2 :
    ContDiff ℝ 2 (fun X : 𝕊^n ↦ Matrix.trace (exp (X : Matrix (Fin n) (Fin n) ℝ))) := by
  have hincl :
      ContDiff ℝ 2
        (fun X : SymmMat ↦ symmetricInclusionContinuousLinearMapL2 (n := n) X) := by
    simpa using
      ((symmetricInclusionContinuousLinearMapL2 (n := n)).contDiff.of_le
        (by simp : (2 : WithTop ℕ∞) ≤ ⊤))
  simpa [Function.comp, symmetricInclusionContinuousLinearMapL2_apply] using
    (traceExpAmbient_contDiffTwo_l2 (n := n)).comp hincl

/-- Helper for Proposition 6.35: in positive dimension, `entropySmoothing` is `C²` on `𝕊^n` with
the operator-norm-induced symmetric-matrix structure used in the final theorem. -/
private theorem entropySmoothing_contDiff_two_pos_l2
    {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^n → ℝ) := by
  rw [entropySmoothing_eq_log_trace_exp_fun]
  refine ContDiff.log (traceExp_contDiffTwo_l2 (n := n)) ?_
  intro X
  exact trace_exp_ne_zero hn X

/-- Helper for Proposition 6.35: the diagonal trace-exponential slice still carries the core
second-derivative estimate needed for the source Hessian bound. -/
theorem diagLogTraceExp_secondDeriv_le_l2OperatorNorm_sq
    {n : ℕ} [Nonempty (Fin n)] (eig : Fin n → ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (hK : Matrix.transpose K = K) :
    iteratedDeriv 2
      (fun t : ℝ ↦ Real.log (Matrix.trace (exp (Matrix.diagonal eig + t • K)))) 0 ≤
        ‖K‖ ^ (2 : ℕ) := by
  let g : ℝ → ℝ := fun t : ℝ ↦ Matrix.trace (exp (Matrix.diagonal eig + t • K))
  let Z : ℝ := ∑ i : Fin n, Real.exp (eig i)
  have hZ : 0 < Z := diagTraceExpPartition_pos eig
  have hg0 : g 0 = Z := by
    -- Evaluate the partition function on the diagonal model at the base point.
    calc
      g 0 = Matrix.trace (exp (Matrix.diagonal eig)) := by
        simp [g]
      _ = ∑ i : Fin n, exp (eig i) := by
        simp [Matrix.exp_diagonal]
      _ = Z := by
        simp [Z, Real.exp_eq_exp_ℝ]
  have hcont_g : ContDiffAt ℝ 2 g 0 := by
    -- Route correction: use the dedicated ambient diagonal-line bridge so the scalar chain rule
    -- never leaves the Frobenius matrix surface.
    simpa [g] using diagTraceExpLine_contDiffAtTwo eig K
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log (g t)) 0 =
        iteratedDeriv 2 Real.log (g 0) * deriv g 0 ^ (2 : ℕ) +
          deriv Real.log (g 0) * iteratedDeriv 2 g 0 := by
    -- Apply the scalar second-order chain rule once the trace-exponential slice is known to be
    -- `C²`.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (g := Real.log)
        (f := g)
        (x := 0)
        (show ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) (g 0) by
          simpa using
            (Real.contDiffAt_log.2 (show g 0 ≠ 0 by rw [hg0]; exact hZ.ne') :
              ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) (g 0)))
        hcont_g)
  have hlog₂ :
      iteratedDeriv 2 Real.log (g 0) = -((g 0 ^ (2 : ℕ))⁻¹) := by
    exact iteratedDerivTwo_log_eq_neg_inv_sq (show g 0 ≠ 0 by rw [hg0]; exact hZ.ne')
  have hlog' : deriv Real.log (g 0) = (g 0)⁻¹ := by
    rw [Real.deriv_log]
  have hg''bound :
      iteratedDeriv 2 g 0 ≤ g 0 * (‖K‖ ^ (2 : ℕ)) := by
    have hg''trace :
        iteratedDeriv 2 g 0 ≤
          Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) := by
      -- Route correction: first prove the direct weighted-trace bound for `g''(0)`.
      simpa [g] using diagTraceExpLine_secondDeriv_le_traceExpSquareWeight eig K hK
    have htraceBound :
        Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K) ≤
          g 0 * (‖K‖ ^ (2 : ℕ)) := by
      -- The weighted quadratic trace is at most the partition function times `‖K‖²`.
      calc
        Matrix.trace (Matrix.diagonal (fun i ↦ Real.exp (eig i)) * K * K)
            ≤ (∑ i : Fin n, Real.exp (eig i)) * ‖K‖ ^ (2 : ℕ) :=
              traceExpSquareWeight_le_partition_mul_l2OperatorNorm_sq eig K hK
        _ = g 0 * (‖K‖ ^ (2 : ℕ)) := by
              rw [hg0]
    exact hg''trace.trans htraceBound
  have hdropSquare :
      iteratedDeriv 2 (fun t : ℝ ↦ Real.log (g t)) 0 ≤ (g 0)⁻¹ * iteratedDeriv 2 g 0 := by
    rw [hcomp, hlog₂, hlog']
    have hsq_nonneg : 0 ≤ deriv g 0 ^ (2 : ℕ) := sq_nonneg (deriv g 0)
    have hsqInv_nonneg : 0 ≤ (g 0 ^ (2 : ℕ))⁻¹ := by
      exact inv_nonneg.mpr (sq_nonneg (g 0))
    have hneg :
        -((g 0 ^ (2 : ℕ))⁻¹) * deriv g 0 ^ (2 : ℕ) ≤ 0 := by
      nlinarith
    have hadd :=
      add_le_add_right hneg ((g 0)⁻¹ * iteratedDeriv 2 g 0)
    simpa [add_assoc, add_comm, add_left_comm] using hadd
  have hnorm :
      (g 0)⁻¹ * iteratedDeriv 2 g 0 ≤ ‖K‖ ^ (2 : ℕ) := by
    have hginv_nonneg : 0 ≤ (g 0)⁻¹ := by
      rw [hg0]
      exact inv_nonneg.mpr hZ.le
    have hmul := mul_le_mul_of_nonneg_left hg''bound hginv_nonneg
    calc
      (g 0)⁻¹ * iteratedDeriv 2 g 0 ≤ (g 0)⁻¹ * (g 0 * ‖K‖ ^ (2 : ℕ)) := hmul
      _ = ((g 0)⁻¹ * g 0) * ‖K‖ ^ (2 : ℕ) := by ring
      _ = ‖K‖ ^ (2 : ℕ) := by
            rw [inv_mul_cancel₀ (show g 0 ≠ 0 by rw [hg0]; exact hZ.ne'), one_mul]
  simpa [g] using hdropSquare.trans hnorm

-- Route correction: the smoothness half is closed intrinsically on `𝕊^n`, so the
-- remaining source-faithful work is only the diagonal-slice Hessian estimate.
/-- Helper for Proposition 6.35: the remaining positive-dimensional obligation is the Hessian
quadratic-form bound from the source diagonal-slice argument. -/
theorem entropySmoothing_hessianQuadraticForm_le_l2OperatorNorm_sq_pos
    {n : ℕ} (hn : 0 < n) (X H : 𝕊^n) :
    (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H] ≤
      (‖((H : Matrix (Fin n) (Fin n) ℝ))‖) ^ (2 : ℕ) := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let hX : (X : Matrix (Fin n) (Fin n) ℝ).IsHermitian := RealSymmetricMatrixSpace.isHermitian X
  let U : Matrix.unitaryGroup (Fin n) ℝ := hX.eigenvectorUnitary
  let K : Matrix (Fin n) (Fin n) ℝ :=
    star (U : Matrix (Fin n) (Fin n) ℝ) * (H : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ)
  have hcont : ContDiffAt ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X := by
    exact (entropySmoothing_contDiff_two_pos_l2 hn).contDiffAt
  have hslice :
      (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H] =
        iteratedDeriv 2 (fun t : ℝ ↦ entropySmoothing (X + t • H)) 0 := by
    -- Replace the Hessian quadratic form by the scalar second derivative along the affine line.
    calc
      (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H]
          = secondDirectionalDerivative (entropySmoothing : 𝕊^n → ℝ) X H := by
              exact
                iteratedFDerivTwo_apply_eqSecondDirectionalDerivative_of_contDiffAtTwo
                  (f := (entropySmoothing : 𝕊^n → ℝ)) (x := X) (h := H) hcont
      _ = iteratedDeriv 2 (fun t : ℝ ↦ entropySmoothing (X + t • H)) 0 := by
            rw [secondDirectionalDerivative]
            rfl
  have htraceSlice :
      iteratedDeriv 2 (fun t : ℝ ↦ entropySmoothing (X + t • H)) 0 =
        iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log
              (Matrix.trace (exp (((X + t • H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ))))) 0 := by
    -- Rewrite the scalar slice pointwise through the trace-exponential presentation.
    congr 1
    ext t
    simpa using entropySmoothing_eq_log_trace_exp (X + t • H)
  have hdiagSlice :
      iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log
              (Matrix.trace (exp (((X + t • H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ))))) 0 =
        iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log (Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K)))) 0 := by
    -- Diagonalize the whole scalar slice in the fixed eigenbasis of `X`.
    simpa [hX, U, K] using
      congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 2 f 0)
        (spectralSlice_eq_diagLogTraceExp (X := X) (H := H))
  have hdiagBound :
      iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log (Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K)))) 0 ≤
        ‖K‖ ^ (2 : ℕ) := by
    -- The remaining source core is now isolated entirely in the diagonal model.
    simpa using
      diagLogTraceExp_secondDeriv_le_l2OperatorNorm_sq
        (eig := eigenvalues X) K
        (by
          -- The conjugated direction stays symmetric in the chosen eigenbasis of `X`.
          simpa [K, U] using conjugatedDirection_transpose_eq_self U H)
  have hnormK : ‖K‖ = ‖((H : Matrix (Fin n) (Fin n) ℝ))‖ := by
    -- Unitary conjugation preserves the ambient operator norm.
    simpa [K, U] using
      unitaryConj_l2OperatorNorm_eq U (H : Matrix (Fin n) (Fin n) ℝ)
  calc
    (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H]
        = iteratedDeriv 2 (fun t : ℝ ↦ entropySmoothing (X + t • H)) 0 := hslice
    _ =
        iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log
              (Matrix.trace (exp (((X + t • H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ))))) 0 :=
        htraceSlice
    _ =
        iteratedDeriv 2
          (fun t : ℝ ↦
            Real.log (Matrix.trace (exp (Matrix.diagonal (eigenvalues X) + t • K)))) 0 :=
        hdiagSlice
    _ ≤ ‖K‖ ^ (2 : ℕ) := hdiagBound
    _ = (‖((H : Matrix (Fin n) (Fin n) ℝ))‖) ^ (2 : ℕ) := by
        rw [hnormK]

-- Route correction: the zero-dimensional branch is handled directly, so the only remaining
-- unresolved part is the positive-dimensional spectral-Hessian argument from the source proof.
/-- Helper for Proposition 6.35: in positive dimension, the entropy smoothing is `C²` and its
Hessian quadratic form is bounded by the squared ambient matrix operator norm. -/
theorem entropySmoothing_contDiff_and_hessianQuadraticForm_le_pos
    {n : ℕ} (hn : 0 < n) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^n → ℝ) ∧
      ∀ X H : 𝕊^n,
        (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H] ≤
          (‖((H : Matrix (Fin n) (Fin n) ℝ))‖) ^ (2 : ℕ) :=
    by
  constructor
  · -- The smoothness half is already isolated through the trace-exponential representation.
    exact entropySmoothing_contDiff_two_pos_l2 hn
  · -- The remaining source-faithful work is the Hessian slice estimate packaged above.
    intro X H
    exact entropySmoothing_hessianQuadraticForm_le_l2OperatorNorm_sq_pos hn X H

-- Proof sketch: regard `entropySmoothing` as the spectral function attached to the scalar
-- log-sum-exp map on `ℝⁿ`; smoothness follows from smooth spectral calculus, and the Hessian bound
-- is obtained by diagonalizing `X`, reducing to the scalar Hessian
-- `Diag(p) - p pᵀ`, and comparing the spectral Hessian with commuting directions.
/-- Proposition 6.35: the entropy-smoothing function
`E(X) = log (∑ᵢ exp (λᵢ(X)))` on `𝕊^n` is twice Fréchet differentiable, and its Hessian quadratic
form in any symmetric direction `H` is bounded above by the square of the ambient matrix `L²`
operator norm, i.e. by the square of the spectral norm of `H`. -/
theorem entropySmoothing_contDiff_and_hessianQuadraticForm_le (n : ℕ) :
    ContDiff ℝ 2 (entropySmoothing : 𝕊^n → ℝ) ∧
      ∀ X H : 𝕊^n,
        (iteratedFDeriv ℝ 2 (entropySmoothing : 𝕊^n → ℝ) X) ![H, H] ≤
          (‖((H : Matrix (Fin n) (Fin n) ℝ))‖) ^ (2 : ℕ) := by
  by_cases h0 : n = 0
  · -- The `n = 0` branch is the constant-map case proved above.
    subst h0
    constructor
    · rw [entropySmoothing_zero_dim_eq_zero]
      simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : 𝕊^0 ↦ (0 : ℝ)))
    · intro X H
      rw [entropySmoothing_zero_dim_eq_zero]
      simp
  · -- Positive dimension is exactly the spectral-Hessian case isolated in the helper above.
    exact entropySmoothing_contDiff_and_hessianQuadraticForm_le_pos
      (hn := Nat.pos_iff_ne_zero.mpr h0)

end L2OperatorFinal

end
