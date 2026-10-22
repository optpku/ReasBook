/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_70
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_71
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open ProbabilityTheory
open scoped Pointwise MatrixOrder RealSymmetricMatrixSpace

variable {n : ℕ}

local notation "Mₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.33 lies in Chapter 7's Boolean quadratic / semidefinite-relaxation domain.

Sampled owner-style declarations:
- `booleanQuadraticOptimalValue` in `Definition_7_70`, the chapter owner for the Boolean
  quadratic optimum;
- `diagonalSemidefiniteRelaxationOptimalValue` in `Definition_7_71`, the chapter owner for the
  semidefinite-relaxation value `ψ⋆` on the intrinsic symmetric carrier `𝕊^n`;
- `SemidefiniteOptimizationProblem` and `SemidefiniteOptimizationProblem.feasibleSet` in
  `Chap05/Definition_5_4_4_4`, the project owner for SDP data, the intrinsic feasible set in
  `𝕊^n`, and the trace/Frobenius objective;
- `𝕊^n` and `𝕊^n₊` in `Chap05/Definition_5_4_4_1` and `Chap05/Definition_5_4_4_3`, the
  intrinsic symmetric-matrix and positive-semidefinite cone owners.

Best owner abstraction:
- source-facing: Proposition 7.33's comparison between the Boolean quadratic optimum and the
  chapter semidefinite-relaxation value `ψ⋆`;
- core/canonical: `booleanQuadraticOptimalValue` and
  `diagonalSemidefiniteRelaxationOptimalValue`, both specialized to the intrinsic symmetric
  carrier `𝕊^n`;
- bridge/view: the unit-diagonal SDP representation of
  `diagonalSemidefiniteRelaxationOptimalValue`.

Primitive data:
- `A : 𝕊^n`.

Derived API:
- the chapter owner `diagonalSemidefiniteRelaxationOptimalValue A`;
- the private SDP view used to express its primal trace-maximization representation;
- the bridge theorem recovering the textbook `sSup` formula over unit-diagonal
  positive-semidefinite matrices.

Source/core/bridge triage:
- source-facing: the approximation theorem below;
- core/canonical: `booleanQuadraticOptimalValue` and
  `diagonalSemidefiniteRelaxationOptimalValue`;
- bridge/view: the unit-diagonal feasible-set characterization, the trace-form objective theorem,
  and the `sSup` expansion of `diagonalSemidefiniteRelaxationOptimalValue`.

This refinement deletes the duplicate public semidefinite-relaxation owners
`booleanQuadraticSemidefiniteProblem` and `booleanQuadraticSemidefiniteOptimalValue`. The public
surface now reuses the chapter owner `diagonalSemidefiniteRelaxationOptimalValue` on `𝕊^n`,
while any explicit SDP packaging remains private bridge data. The main approximation theorem is
therefore stated directly on the intrinsic cone owner `𝕊^n₊`, with only the Boolean quadratic
objective viewed through the ambient matrix coercion.
-/

private def diagonalSemidefiniteRelaxationConstraint
    (i : Fin n) : 𝕊^n :=
  ⟨Matrix.diagonal fun j : Fin n ↦ if j = i then (1 : ℝ) else 0, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    simp [Matrix.IsSymm]
  ⟩

private def diagonalSemidefiniteRelaxationProblem
    (A : 𝕊^n) : SemidefiniteOptimizationProblem n n where
  costMatrix := A
  constraintMatrices := diagonalSemidefiniteRelaxationConstraint
  rhs := (EuclideanSpace.equiv (Fin n) ℝ).symm fun _ ↦ (1 : ℝ)

-- Proof sketch: unfold `diagonalSemidefiniteRelaxationProblem` and
-- `SemidefiniteOptimizationProblem.mem_feasibleSet_iff`; the constraint matrices are the
-- diagonal matrix units, so the Frobenius equations are exactly the unit-diagonal conditions on
-- `X`.
private theorem mem_diagonalSemidefiniteRelaxationProblem_feasibleSet_iff
    (A : 𝕊^n) (X : 𝕊^n) :
    X ∈ (diagonalSemidefiniteRelaxationProblem A).feasibleSet ↔
      X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1) := by
  -- Expand the SDP owner feasibility condition into positivity plus the diagonal constraints.
  rw [SemidefiniteOptimizationProblem.mem_feasibleSet_iff]
  constructor
  · intro hX
    rcases hX with ⟨hpsd, hdiag⟩
    refine ⟨hpsd, ?_⟩
    ext i
    specialize hdiag i
    rw [RealSymmetricMatrixSpace.frobeniusInner_def] at hdiag
    have htrace :
        ((Matrix.diagonal fun j : Fin n ↦ if j = i then (1 : ℝ) else 0) * (X : Mₙ)).trace =
          (X : Mₙ) i i := by
      simp [Matrix.trace]
    simpa [diagonalSemidefiniteRelaxationProblem, diagonalSemidefiniteRelaxationConstraint, htrace]
      using hdiag
  · intro hX
    rcases hX with ⟨hpsd, hdiag⟩
    refine ⟨hpsd, ?_⟩
    intro i
    have hdiag_i : ((X : Mₙ).diag) i = 1 := by
      simpa using congrArg (fun d : Fin n → ℝ ↦ d i) hdiag
    rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    simpa [diagonalSemidefiniteRelaxationProblem, diagonalSemidefiniteRelaxationConstraint,
      Matrix.trace] using hdiag_i

-- Proof sketch: the SDP owner objective is the Frobenius pairing with the symmetric cost matrix
-- `A`; on `𝕊^n` this is exactly the textbook trace formula `trace (A X)`.
private theorem diagonalSemidefiniteRelaxationProblem_objective_eq_trace
    (A : 𝕊^n) (X : 𝕊^n) :
    (diagonalSemidefiniteRelaxationProblem A).objective X = trace ((A : Mₙ) * (X : Mₙ)) := by
  -- Reduce the local objective to the Chapter 5 owner-level trace formula.
  simpa [diagonalSemidefiniteRelaxationProblem] using
    SemidefiniteOptimizationProblem.objective_eq_trace
      (diagonalSemidefiniteRelaxationProblem A) X

/-- Helper for Proposition 7.33: the outer product `σ σᵀ` is symmetric. -/
private theorem sign_outerProduct_isSymm
    (σ : Fin n → ℝ) :
    (Matrix.vecMulVec σ σ : Mₙ).IsSymm := by
  -- Entrywise symmetry is immediate because both factors are the same sign vector.
  ext i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- Helper for Proposition 7.33: the outer product `σ σᵀ` belongs to the symmetric matrix
carrier. -/
private theorem sign_outerProduct_mem_symmSpace
    (σ : Fin n → ℝ) :
    (Matrix.vecMulVec σ σ : Mₙ) ∈ 𝕊^n := by
  -- Repackage the entrywise symmetry into the Chapter 5 symmetric carrier.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  exact sign_outerProduct_isSymm σ

/-- Helper for Proposition 7.33: the outer product `σ σᵀ` canonically defines an element of the
real symmetric matrix space. -/
private def signOuterProductSymm
    (σ : Fin n → ℝ) : 𝕊^n :=
  ⟨Matrix.vecMulVec σ σ, sign_outerProduct_mem_symmSpace σ⟩

/-- Helper for Proposition 7.33: the rank-one matrix `σ σᵀ` of a sign vector is feasible for the
unit-diagonal primal semidefinite relaxation. -/
private theorem sign_outerProduct_mem_unitDiagonalFeasibleSet
    (σ : Fin n → ℝ) (hσ : σ ∈ signVectorSet (Fin n)) :
    let X : 𝕊^n := signOuterProductSymm σ
    X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1) := by
  -- Package the rank-one outer product as a symmetric matrix once and reuse that witness.
  dsimp
  have hsq : ∀ i : Fin n, σ i * σ i = 1 := by
    intro i
    rcases (mem_signVectorSet_iff.mp hσ i) with hneg | hpos
    · simp [hneg]
    · simp [hpos]
  refine ⟨?_, ?_⟩
  · -- Positive semidefiniteness is the standard rank-one `xxᵀ ⪰ 0` fact.
    simpa [signOuterProductSymm] using (Matrix.posSemidef_vecMulVec_self_star σ)
  · -- The diagonal entries are `σ i ^ 2 = 1` because `σ` is a sign vector.
    ext i
    simp [signOuterProductSymm, Matrix.vecMulVec_apply, hsq i]

/-- Helper for Proposition 7.33: the diagonal semidefinite-relaxation feasible set is nonempty,
because the operator-norm multiple of the identity dominates every symmetric matrix. -/
private theorem diagonalSemidefiniteRelaxationFeasibleSet_nonempty
    (A : 𝕊^n) :
    (diagonalSemidefiniteRelaxationFeasibleSet A).Nonempty := by
  open scoped Matrix.Norms.L2Operator in
  let c : ℝ := ‖(A : Mₙ)‖
  refine ⟨WithLp.toLp 2 (fun _ : Fin n ↦ c), ?_⟩
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff]
  change (A : Mₙ) ≤ Matrix.diagonal (fun _ : Fin n ↦ c)
  suffices hslack : (0 : Mₙ) ≤ Matrix.diagonal (fun _ : Fin n ↦ c) - (A : Mₙ) by
    exact sub_nonneg.mp hslack
  rw [Matrix.nonneg_iff_posSemidef]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- The slack matrix stays Hermitian because both the scalar diagonal and `A` are symmetric.
    refine Matrix.IsHermitian.ext fun i j ↦ ?_
    have hA_symm : (A : Mₙ).IsSymm := by
      exact (RealSymmetricMatrixSpace.mem_iff_isSymm).mp A.2
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · have hji : ¬ j = i := fun h ↦ hij h.symm
      simp [Matrix.diagonal, hij, hji, hA_symm.apply i j]
  · intro x
    -- Rewrite the diagonal part as `c ‖x‖²` and bound the quadratic part by the operator norm.
    let T : Eₙ →L[ℝ] Eₙ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) (A : Mₙ)
    have hdiag :
        x ⬝ᵥ (Matrix.diagonal (fun _ : Fin n ↦ c) *ᵥ x) =
          c * ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        x ⬝ᵥ (Matrix.diagonal (fun _ : Fin n ↦ c) *ᵥ x)
            = ∑ i : Fin n, x i * (c * x i) := by
                simp [dotProduct, Matrix.mulVec, Matrix.diagonal]
        _ = c * ∑ i : Fin n, x i ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        _ = c * ‖WithLp.toLp 2 x‖ ^ 2 := by
          simpa using congrArg (fun t : ℝ ↦ c * t)
            (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)).symm
    have hquad :
        x ⬝ᵥ ((A : Mₙ) *ᵥ x) =
          inner ℝ (WithLp.toLp 2 x) (T (WithLp.toLp 2 x)) := by
      symm
      simpa using
        Matrix.inner_toEuclideanCLM (A := (A : Mₙ)) (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have hclm :
        ‖T (WithLp.toLp 2 x)‖ ≤
          c * ‖WithLp.toLp 2 x‖ := by
      simpa [T, c] using Matrix.l2_opNorm_mulVec (A := (A : Mₙ)) (x := WithLp.toLp 2 x)
    have hA_bound :
        x ⬝ᵥ ((A : Mₙ) *ᵥ x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        x ⬝ᵥ ((A : Mₙ) *ᵥ x)
            = inner ℝ (WithLp.toLp 2 x) (T (WithLp.toLp 2 x)) := hquad
        _ ≤ ‖WithLp.toLp 2 x‖ * ‖T (WithLp.toLp 2 x)‖ := by
          exact real_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 x‖ * (c * ‖WithLp.toLp 2 x‖) := by
          exact mul_le_mul_of_nonneg_left hclm (norm_nonneg _)
        _ = c * ‖WithLp.toLp 2 x‖ ^ 2 := by
          ring
    have hc : 0 ≤ c := by
      simp [c]
    have hnorm_sq : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [dotProduct, pow_two]
    have hnonneg :
        0 ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 - x ⬝ᵥ ((A : Mₙ) *ᵥ x) := by
      nlinarith
    -- The operator-norm estimate makes the slack quadratic form nonnegative.
    simpa [sub_mulVec, dotProduct_sub, hdiag, hnorm_sq] using hnonneg

/-- Helper for Proposition 7.33: the trace pairing of two positive-semidefinite real symmetric
matrices is nonnegative. -/
private theorem trace_mul_nonneg_of_posSemidef
    {S X : Mₙ} (hS : S.PosSemidef) (hX : X.PosSemidef) :
    0 ≤ Matrix.trace (S * X) := by
  let B : Mₙ := CFC.sqrt X
  have hB_psd : B.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    change (0 : Mₙ) ≤ CFC.sqrt X
    exact CFC.sqrt_nonneg X
  have hB_symm : B.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hB_psd.isHermitian
  have hconj_psd : (B * S * Bᵀ).PosSemidef := by
    simpa [B] using hS.mul_mul_conjTranspose_same B
  have htrace_eq :
      Matrix.trace (B * S * Bᵀ) = Matrix.trace (S * X) := by
    calc
      Matrix.trace (B * S * Bᵀ) = Matrix.trace (Bᵀ * B * S) := by
        rw [Matrix.trace_mul_cycle B S Bᵀ]
      _ = Matrix.trace (S * Bᵀ * B) := by
        rw [Matrix.trace_mul_comm (Bᵀ * B) S, Matrix.mul_assoc]
      _ = Matrix.trace (S * B * B) := by
        rw [hB_symm.eq]
      _ = Matrix.trace (S * (B * B)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace (S * X) := by
        rw [show B * B = X by
          simpa [B] using CFC.sqrt_mul_sqrt_self X hX.nonneg]
  rw [← htrace_eq]
  exact hconj_psd.trace_nonneg

/-- Helper for Proposition 7.33: every feasible diagonal majorant bounds the trace objective on
the unit-diagonal positive-semidefinite slice. -/
private theorem trace_le_sum_diagonal_of_unitDiagonalFeasible
    (A : 𝕊^n) {y : Eₙ} {X : 𝕊^n}
    (hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet A)
    (hX : X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)) :
    trace ((A : Mₙ) * (X : Mₙ)) ≤ ∑ i : Fin n, y i := by
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff] at hy
  rcases hX with ⟨hX_psd_mem, hX_diag⟩
  have hslack_psd :
      ((Matrix.diagonal fun i : Fin n ↦ y i) - (A : Mₙ)).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hy)
  have hX_psd : (X : Mₙ).PosSemidef := by
    simpa [mem_positiveSemidefiniteCone_iff] using hX_psd_mem
  have hslack_nonneg :
      0 ≤ Matrix.trace (((Matrix.diagonal fun i : Fin n ↦ y i) - (A : Mₙ)) * (X : Mₙ)) := by
    exact trace_mul_nonneg_of_posSemidef hslack_psd hX_psd
  have htrace_diag :
      Matrix.trace ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ)) =
        ∑ i : Fin n, y i := by
    calc
      Matrix.trace ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ))
          = ∑ i : Fin n, ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ)) i i := by
              simp [Matrix.trace]
      _ = ∑ i : Fin n, y i * (X : Mₙ) i i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [Matrix.mul_apply, Matrix.diagonal]
      _ = ∑ i : Fin n, y i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hdiag_i : ((X : Mₙ).diag) i = 1 := by
          simpa using congrArg (fun d : Fin n → ℝ ↦ d i) hX_diag
        simpa using congrArg (fun t : ℝ ↦ y i * t) hdiag_i
  have hslack_trace :
      Matrix.trace (((Matrix.diagonal fun i : Fin n ↦ y i) - (A : Mₙ)) * (X : Mₙ)) =
        ∑ i : Fin n, y i - Matrix.trace ((A : Mₙ) * (X : Mₙ)) := by
    rw [sub_mul, Matrix.trace_sub, htrace_diag]
  linarith [hslack_nonneg]

/-- Helper for Proposition 7.33: the trace image of the unit-diagonal positive-semidefinite slice
is bounded above by any feasible diagonal majorant. -/
private theorem unitDiagonalTraceImage_bddAbove
    (A : 𝕊^n) :
    BddAbove
      ((fun X : 𝕊^n ↦ trace ((A : Mₙ) * (X : Mₙ))) ''
        {X : 𝕊^n | X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)}) := by
  -- Reuse one feasible diagonal majorant as a uniform weak-duality bound on the trace image.
  rcases diagonalSemidefiniteRelaxationFeasibleSet_nonempty A with ⟨y, hy⟩
  refine ⟨∑ i : Fin n, y i, ?_⟩
  rintro _ ⟨X, hX, rfl⟩
  exact trace_le_sum_diagonal_of_unitDiagonalFeasible A hy hX

/-- Helper for Proposition 7.33: a unit-diagonal symmetric matrix pairs with a diagonal matrix by
summing the diagonal coefficients. -/
private theorem trace_mul_diagonal_eq_sum_of_unitDiagonal
    {X : 𝕊^n} (hX_diag : ((X : Mₙ).diag = 1)) (y : Eₙ) :
    Matrix.trace ((X : Mₙ) * Matrix.diagonal (fun i : Fin n ↦ y i)) =
      ∑ i : Fin n, y i := by
  -- Cycle the trace so that the diagonal matrix acts on the left, where the unit-diagonal
  -- condition can be read entrywise.
  calc
    Matrix.trace ((X : Mₙ) * Matrix.diagonal (fun i : Fin n ↦ y i))
        = Matrix.trace ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ)) := by
            rw [Matrix.trace_mul_comm]
    _ = ∑ i : Fin n, y i := by
      calc
        Matrix.trace ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ))
            = ∑ i : Fin n, ((Matrix.diagonal fun i : Fin n ↦ y i) * (X : Mₙ)) i i := by
                simp [Matrix.trace]
        _ = ∑ i : Fin n, y i * (X : Mₙ) i i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [Matrix.mul_apply, Matrix.diagonal]
        _ = ∑ i : Fin n, y i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hdiag_i : ((X : Mₙ).diag) i = 1 := by
                simpa using congrArg (fun d : Fin n → ℝ ↦ d i) hX_diag
              simpa using congrArg (fun t : ℝ ↦ y i * t) hdiag_i

/-- Helper for Proposition 7.33: the diagonal slack `diag(y) - A` is symmetric. -/
private theorem diagonalSlack_mem_symm
    (A : 𝕊^n) (y : Eₙ) :
    (Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ) : Mₙ) ∈ 𝕊^n := by
  -- Both the diagonal matrix and `A` are symmetric, so their difference stays in `𝕊^n`.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
  simpa using (Matrix.isSymm_diagonal (fun i : Fin n ↦ y i)).sub
    (RealSymmetricMatrixSpace.isSymm A)

/-- Helper for Proposition 7.33: package the diagonal slack `diag(y) - A` as an intrinsic
symmetric matrix. -/
private def diagonalSlackSymm
    (A : 𝕊^n) (y : Eₙ) : 𝕊^n :=
  ⟨Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ), diagonalSlack_mem_symm A y⟩

/-- Helper for Proposition 7.33: coercing `diagonalSlackSymm A y` back to matrices recovers the
explicit diagonal slack `diag(y) - A`. -/
private theorem diagonalSlackSymm_coe
    (A : 𝕊^n) (y : Eₙ) :
    ((diagonalSlackSymm A y : 𝕊^n) : Mₙ) =
      Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ) :=
  rfl

/-- Helper for Proposition 7.33: the coordinate constraint matrix extracts the corresponding
diagonal entry under the trace pairing. -/
private theorem trace_mul_diagonalSemidefiniteRelaxationConstraint
    (Z : 𝕊^n) (i : Fin n) :
    Matrix.trace ((Z : Mₙ) * ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ)) =
      ((Z : Mₙ).diag) i := by
  -- The constraint matrix is the diagonal projector `Eᵢᵢ`, so only the `i`-th diagonal term
  -- survives in the trace.
  simp [diagonalSemidefiniteRelaxationConstraint, Matrix.trace, Matrix.mul_apply, Matrix.diagonal]

/-- Helper for Proposition 7.33: there is a strict diagonal majorant of `A`, so the diagonal
majorant value region has interior points. -/
private theorem diagonalSemidefiniteRelaxationStrictFeasiblePoint
    (A : 𝕊^n) :
    ∃ y0 : Eₙ, (Matrix.diagonal (fun i : Fin n ↦ y0 i) - (A : Mₙ)).PosDef := by
  open scoped Matrix.Norms.L2Operator in
  let c : ℝ := ‖(A : Mₙ)‖ + 1
  refine ⟨WithLp.toLp 2 (fun _ : Fin n ↦ c), ?_⟩
  -- Strengthen the earlier operator-norm witness from semidefinite to definite positivity by
  -- keeping one full `‖x‖²` of slack.
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · refine Matrix.IsHermitian.ext fun i j ↦ ?_
    have hA_symm : (A : Mₙ).IsSymm := RealSymmetricMatrixSpace.isSymm A
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal]
    · have hji : ¬ j = i := fun h ↦ hij h.symm
      simp [Matrix.diagonal, hij, hji, hA_symm.apply i j]
  · intro x hx
    let T : Eₙ →L[ℝ] Eₙ := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n)) (A : Mₙ)
    have hdiag :
        x ⬝ᵥ (Matrix.diagonal (fun _ : Fin n ↦ c) *ᵥ x) =
          c * ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        x ⬝ᵥ (Matrix.diagonal (fun _ : Fin n ↦ c) *ᵥ x)
            = ∑ i : Fin n, x i * (c * x i) := by
                simp [dotProduct, Matrix.mulVec, Matrix.diagonal]
        _ = c * ∑ i : Fin n, x i ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = c * ‖WithLp.toLp 2 x‖ ^ 2 := by
              simpa using congrArg (fun t : ℝ ↦ c * t)
                (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)).symm
    have hquad :
        x ⬝ᵥ ((A : Mₙ) *ᵥ x) =
          inner ℝ (WithLp.toLp 2 x) (T (WithLp.toLp 2 x)) := by
      symm
      simpa using
        Matrix.inner_toEuclideanCLM (A := (A : Mₙ)) (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have hclm :
        ‖T (WithLp.toLp 2 x)‖ ≤
          ‖(A : Mₙ)‖ * ‖WithLp.toLp 2 x‖ := by
      simpa [T] using Matrix.l2_opNorm_mulVec (A := (A : Mₙ)) (x := WithLp.toLp 2 x)
    have hA_bound :
        x ⬝ᵥ ((A : Mₙ) *ᵥ x) ≤ ‖(A : Mₙ)‖ * ‖WithLp.toLp 2 x‖ ^ 2 := by
      calc
        x ⬝ᵥ ((A : Mₙ) *ᵥ x)
            = inner ℝ (WithLp.toLp 2 x) (T (WithLp.toLp 2 x)) := hquad
        _ ≤ ‖WithLp.toLp 2 x‖ * ‖T (WithLp.toLp 2 x)‖ := by
              exact real_inner_le_norm _ _
        _ ≤ ‖WithLp.toLp 2 x‖ * (‖(A : Mₙ)‖ * ‖WithLp.toLp 2 x‖) := by
              exact mul_le_mul_of_nonneg_left hclm (norm_nonneg _)
        _ = ‖(A : Mₙ)‖ * ‖WithLp.toLp 2 x‖ ^ 2 := by
              ring
    have hxLp : WithLp.toLp 2 x ≠ 0 := by
      simpa using hx
    have hnorm_sq_pos : 0 < ‖WithLp.toLp 2 x‖ ^ 2 := by
      exact sq_pos_iff.mpr (norm_ne_zero_iff.mpr hxLp)
    have hstrict :
        0 < c * ‖WithLp.toLp 2 x‖ ^ 2 - x ⬝ᵥ ((A : Mₙ) *ᵥ x) := by
      dsimp [c]
      nlinarith [hA_bound, hnorm_sq_pos]
    have hnorm_sq : ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [dotProduct, pow_two]
    simpa [sub_mulVec, dotProduct_sub, hdiag, hnorm_sq] using hstrict

/-- Helper for Proposition 7.33: the diagonal-majorant value region stores matrix slacks lying
below `diag(y) - A` together with scalar upper bounds on `∑ i, y i`. -/
private def diagonalSemidefiniteRelaxationValueRegion
    (A : 𝕊^n) : Set (𝕊^n × ℝ) :=
  {p | ∃ y : Eₙ,
      (((p.1 : 𝕊^n) : Mₙ) ≤ Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ)) ∧
        (∑ i : Fin n, y i) ≤ p.2}

/-- Helper for Proposition 7.33: the diagonal-majorant value region is convex because the matrix
slack and the scalar cost are both affine in the diagonal witness `y`. -/
private theorem convex_diagonalSemidefiniteRelaxationValueRegion
    (A : 𝕊^n) :
    Convex ℝ (diagonalSemidefiniteRelaxationValueRegion A) := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨y, hp_mat, hp_cost⟩
  rcases hq with ⟨z, hq_mat, hq_cost⟩
  let w : Eₙ := WithLp.toLp 2 (fun i : Fin n ↦ a * y i + b * z i)
  refine ⟨w, ?_, ?_⟩
  · have hdiag :
        Matrix.diagonal (fun i : Fin n ↦ w i) =
          a • Matrix.diagonal (fun i : Fin n ↦ y i) +
            b • Matrix.diagonal (fun i : Fin n ↦ z i) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [w]
      · simp [Matrix.diagonal, hij, w]
    have hp_scaled :
        a • (((p.1 : 𝕊^n) : Mₙ)) ≤
          a • (Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ)) := by
      gcongr
    have hq_scaled :
        b • (((q.1 : 𝕊^n) : Mₙ)) ≤
          b • (Matrix.diagonal (fun i : Fin n ↦ z i) - (A : Mₙ)) := by
      gcongr
    calc
      ((((a • p + b • q).1 : 𝕊^n) : Mₙ))
          = a • (((p.1 : 𝕊^n) : Mₙ)) + b • (((q.1 : 𝕊^n) : Mₙ)) := by
              simp
      _ ≤ a • (Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ)) +
            b • (Matrix.diagonal (fun i : Fin n ↦ z i) - (A : Mₙ)) := by
              exact add_le_add hp_scaled hq_scaled
      _ = (a • Matrix.diagonal (fun i : Fin n ↦ y i) +
            b • Matrix.diagonal (fun i : Fin n ↦ z i)) -
            ((a + b) • (A : Mₙ)) := by
              calc
                a • (Matrix.diagonal (fun i : Fin n ↦ y i) - (A : Mₙ)) +
                    b • (Matrix.diagonal (fun i : Fin n ↦ z i) - (A : Mₙ))
                    =
                      (a • Matrix.diagonal (fun i : Fin n ↦ y i) +
                        b • Matrix.diagonal (fun i : Fin n ↦ z i)) +
                        (-(a • (A : Mₙ)) + -(b • (A : Mₙ))) := by
                          simp [sub_eq_add_neg, add_left_comm, add_assoc]
                _ =
                    (a • Matrix.diagonal (fun i : Fin n ↦ y i) +
                      b • Matrix.diagonal (fun i : Fin n ↦ z i)) -
                      ((a + b) • (A : Mₙ)) := by
                        simp [sub_eq_add_neg, add_smul, add_assoc, add_comm]
      _ = Matrix.diagonal (fun i : Fin n ↦ w i) - (A : Mₙ) := by
            rw [hdiag, hab]
            simp
  · calc
      ∑ i : Fin n, w i
          = a * ∑ i : Fin n, y i + b * ∑ i : Fin n, z i := by
              simp [w, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ a * p.2 + b * q.2 := by
            exact add_le_add (mul_le_mul_of_nonneg_left hp_cost ha)
              (mul_le_mul_of_nonneg_left hq_cost hb)
      _ = (a • p + b • q).2 := by
            simp

/-- Helper for Proposition 7.33: testing a separator against every positive-semidefinite matrix
forces the separator matrix itself to be positive semidefinite. -/
private theorem separatorNonnegativeOnPsdCone_iff_psdLocal
    (Z : 𝕊^n)
    (hZ :
      ∀ P : 𝕊^n, P ∈ 𝕊^n₊ →
        0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ))) :
    Z ∈ 𝕊^n₊ := by
  -- Rank-one PSD tests recover the quadratic-form characterization of the PSD cone.
  rw [mem_positiveSemidefiniteCone_iff, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨RealSymmetricMatrixSpace.isHermitian Z, ?_⟩
  intro x
  have hx_symm : (Matrix.vecMulVec x x : Mₙ).IsSymm := by
    ext i j
    simp [Matrix.vecMulVec_apply, mul_comm]
  have hx_mem : (Matrix.vecMulVec x x : Mₙ) ∈ 𝕊^n := by
    rwa [RealSymmetricMatrixSpace.mem_iff_isSymm]
  let P : 𝕊^n := ⟨Matrix.vecMulVec x x, hx_mem⟩
  have hP : P ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff]
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := ℝ) x)
  have htrace_nonneg : 0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := hZ P hP
  calc
    0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := htrace_nonneg
    _ = Matrix.trace ((Z : Mₙ) * Matrix.vecMulVec x x) := by rfl
    _ = Matrix.trace (Matrix.vecMulVec ((Z : Mₙ) *ᵥ x) x) := by
          rw [Matrix.mul_vecMulVec]
    _ = ((Z : Mₙ) *ᵥ x) ⬝ᵥ x := by
          rw [Matrix.trace_vecMulVec]
    _ = x ⬝ᵥ ((Z : Mₙ) *ᵥ x) := by
          rw [dotProduct_comm]

/-- Helper for Proposition 7.33: the strict diagonal-majorant witness leaves room in both the
matrix and scalar coordinates, so the value region has nonempty interior. -/
private theorem diagonalSemidefiniteRelaxationValueRegion_interior_nonempty
    (A : 𝕊^n) :
    (interior (diagonalSemidefiniteRelaxationValueRegion A)).Nonempty := by
  obtain ⟨y0, hslack0_posdef⟩ := diagonalSemidefiniteRelaxationStrictFeasiblePoint A
  let S0 : 𝕊^n := diagonalSlackSymm A y0
  let c0 : ℝ := ∑ i : Fin n, y0 i
  let U : Set (𝕊^n × ℝ) :=
    {p | S0 - p.1 ∈ (𝕊^n₊₊ : Set 𝕊^n) ∧ c0 < p.2}
  have hU_open : IsOpen U := by
    -- The strict-cone margin is open in the matrix coordinate, and the scalar epigraph margin
    -- is an open half-line.
    have hstrict_open : IsOpen (𝕊^n₊₊ : Set 𝕊^n) := by
      exact (isOpen_interior : IsOpen (interior (𝕊^n₊ : Set 𝕊^n)))
    have hmatrix_open :
        IsOpen ((fun p : 𝕊^n × ℝ ↦ S0 - p.1) ⁻¹' (𝕊^n₊₊ : Set 𝕊^n)) :=
      hstrict_open.preimage (continuous_const.sub continuous_fst)
    have hscalar_open :
        IsOpen ((fun p : 𝕊^n × ℝ ↦ p.2) ⁻¹' Set.Ioi c0) :=
      isOpen_Ioi.preimage continuous_snd
    simpa [U, Set.preimage, Set.setOf_and] using hmatrix_open.inter hscalar_open
  have hU_subset : U ⊆ diagonalSemidefiniteRelaxationValueRegion A := by
    intro p hp
    rcases hp with ⟨hp_mat, hp_cost⟩
    have hp_psd : S0 - p.1 ∈ (𝕊^n₊ : Set 𝕊^n) := interior_subset hp_mat
    have hp_le :
        (((p.1 : 𝕊^n) : Mₙ)) ≤ (S0 : Mₙ) := by
      rw [mem_positiveSemidefiniteCone_iff] at hp_psd
      exact sub_nonneg.mp <| by
        simpa using (Matrix.nonneg_iff_posSemidef).mpr hp_psd
    refine ⟨y0, ?_, hp_cost.le⟩
    simpa [S0, diagonalSlackSymm] using hp_le
  let p0 : 𝕊^n × ℝ := ((0 : 𝕊^n), c0 + 1)
  have hp0_mem : p0 ∈ U := by
    refine ⟨?_, by simp [p0, c0]⟩
    simpa [p0, S0, diagonalSlackSymm] using
      (mem_strictPositiveSemidefiniteCone_of_posDef hslack0_posdef : S0 ∈ 𝕊^n₊₊)
  refine ⟨p0, ?_⟩
  -- The explicit open neighborhood `U` around `p0` sits inside the value region.
  refine mem_interior_iff_mem_nhds.2 ?_
  exact Filter.mem_of_superset (hU_open.mem_nhds hp0_mem) hU_subset

/-- Helper for Proposition 7.33: any zero-matrix fiber point in the diagonal-majorant value
region sits above the infimum value `ψ⋆`. -/
private theorem diagonalSemidefiniteRelaxationZeroFiberLowerBound
    (A : 𝕊^n) {c : ℝ}
    (hc : ((0 : 𝕊^n), c) ∈ diagonalSemidefiniteRelaxationValueRegion A) :
    diagonalSemidefiniteRelaxationOptimalValue A ≤ c := by
  rcases hc with ⟨y, hy_mat, hy_cost⟩
  let σ : Fin n → ℝ := fun _ ↦ 1
  have hσ : σ ∈ signVectorSet (Fin n) := by
    rw [mem_signVectorSet_iff]
    intro i
    exact Or.inr rfl
  let X : 𝕊^n := signOuterProductSymm σ
  have hX : X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1) := by
    simpa [X, σ] using sign_outerProduct_mem_unitDiagonalFeasibleSet σ hσ
  have hBddBelow :
      BddBelow
        ((fun y : Eₙ ↦ ∑ i : Fin n, y i) ''
          diagonalSemidefiniteRelaxationFeasibleSet A) := by
    refine ⟨trace ((A : Mₙ) * (X : Mₙ)), ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact trace_le_sum_diagonal_of_unitDiagonalFeasible A hz hX
  -- Read the zero-fiber witness as one feasible diagonal majorant and compare its value with the
  -- defining infimum.
  rw [diagonalSemidefiniteRelaxationOptimalValue_eq_sInf]
  refine (csInf_le ?_ ?_).trans hy_cost
  · exact hBddBelow
  · refine ⟨y, ?_, rfl⟩
    rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff]
    simpa using hy_mat

/-- Helper for Proposition 7.33: on symmetric matrices, the inherited Frobenius pairing is the
ambient trace pairing. -/
private theorem frobeniusInner_eq_trace_mulLocal
    (X U : 𝕊^n) :
    ⟪X, U⟫_F = Matrix.trace ((X : Mₙ) * (U : Mₙ)) := by
  have htranspose : ((X : Mₙ)ᵀ) = (X : Mₙ) := by
    simpa [Matrix.IsSymm] using (RealSymmetricMatrixSpace.isSymm X).eq
  calc
    ⟪X, U⟫_F = Matrix.trace (((X : Mₙ)ᵀ) * (U : Mₙ)) := by
      rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    _ = Matrix.trace ((X : Mₙ) * (U : Mₙ)) := by
      rw [htranspose]

/-- Helper for Proposition 7.33: every separator on `𝕊^n × ℝ` can be written as one trace pairing
minus a scalar multiple of the last coordinate. -/
private theorem diagonalSemidefiniteRelaxationSeparatorRepresentation
    (f : StrongDual ℝ (𝕊^n × ℝ)) :
    ∃ Z : 𝕊^n, ∃ a : ℝ,
      ∀ p : 𝕊^n × ℝ,
        f p = Matrix.trace ((Z : Mₙ) * ((p.1 : 𝕊^n) : Mₙ)) - a * p.2 := by
  let gMatrix : StrongDual ℝ 𝕊^n := f.comp (ContinuousLinearMap.inl ℝ 𝕊^n ℝ)
  let b := stdOrthonormalBasis ℝ 𝕊^n
  let Z : 𝕊^n := ∑ i, gMatrix (b i) • b i
  let a : ℝ := -f ((0 : 𝕊^n), (1 : ℝ))
  refine ⟨Z, a, ?_⟩
  intro p
  rcases p with ⟨S, c⟩
  have hrepr :
      gMatrix S = ∑ i, inner ℝ (b i) S * gMatrix (b i) := by
    have hsum := congrArg gMatrix (b.sum_repr' S)
    simpa [map_sum, map_smul, mul_comm] using hsum.symm
  have hinner :
      inner ℝ Z S = ∑ i, gMatrix (b i) * inner ℝ (b i) S := by
    simp [Z, sum_inner, real_inner_smul_left]
  have hinner' :
      inner ℝ Z S = ∑ i, inner ℝ (b i) S * gMatrix (b i) := by
    rw [hinner]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [mul_comm]
  have hsplit : f (S, c) = f (S, 0) + f (0, c) := by
    rw [show (S, c) = (S, 0) + (0, c) by ext <;> simp, map_add]
  have hmatrix :
      f (S, 0) = Matrix.trace ((Z : Mₙ) * (S : Mₙ)) := by
    calc
      f (S, 0) = gMatrix S := by
        rfl
      _ = inner ℝ Z S := by
        rw [hinner', hrepr]
      _ = Matrix.trace ((Z : Mₙ) * (S : Mₙ)) := by
        rw [RealSymmetricMatrixSpace.inner_eq_frobeniusInner,
          frobeniusInner_eq_trace_mulLocal]
  have hscalar :
      f (0, c) = -a * c := by
    calc
      f (0, c) = f (c • ((0 : 𝕊^n), (1 : ℝ))) := by
        congr 1
        ext <;> simp [smul_eq_mul]
      _ = c * f ((0 : 𝕊^n), (1 : ℝ)) := by
        rw [map_smul]
        simp [smul_eq_mul]
      _ = -a * c := by
        simp [a, mul_comm]
  -- Split the product-space functional into its matrix and scalar components once and for all.
  rw [hsplit, hmatrix, hscalar]
  ring

/-- Helper for Proposition 7.33: a separating functional for the diagonal-majorant value region
has positive scalar coefficient, positive-semidefinite matrix part, and constant diagonal. -/
private theorem diagonalSemidefiniteRelaxationSeparatorNormalized
    (A : 𝕊^n) (α : ℝ)
    (f : StrongDual ℝ (𝕊^n × ℝ)) (hf_ne : f ≠ 0)
    {Z : 𝕊^n} {a : ℝ}
    (hf_eval : ∀ p : 𝕊^n × ℝ,
      f p = Matrix.trace ((Z : Mₙ) * ((p.1 : 𝕊^n) : Mₙ)) - a * p.2)
    (hf_sep :
      ∀ p ∈ diagonalSemidefiniteRelaxationValueRegion A, f p ≤ -a * α) :
    0 < a ∧ Z ∈ 𝕊^n₊ ∧ ∀ i : Fin n, ((Z : Mₙ).diag) i = a := by
  obtain ⟨y0, hslack0_posdef⟩ := diagonalSemidefiniteRelaxationStrictFeasiblePoint A
  let slack0M : Mₙ := Matrix.diagonal (fun i : Fin n ↦ y0 i) - (A : Mₙ)
  let c0 : ℝ := ∑ i : Fin n, y0 i
  let p0 : 𝕊^n × ℝ := ((0 : 𝕊^n), c0 + 1)
  have hslack0_nonneg : (0 : Mₙ) ≤ slack0M := by
    exact sub_nonneg.mp <| by
      simpa [slack0M] using (Matrix.nonneg_iff_posSemidef).mpr hslack0_posdef.posSemidef
  have hp0_mem : p0 ∈ diagonalSemidefiniteRelaxationValueRegion A := by
    refine ⟨y0, ?_, ?_⟩
    · simpa [p0, slack0M] using hslack0_nonneg
    · simp [p0, c0]
  -- Every recession direction of the value region must pair nonpositively with the separator,
  -- otherwise translating far enough along that direction would violate the separating bound.
  have hrecession_nonpos :
      ∀ {p d : 𝕊^n × ℝ}, p ∈ diagonalSemidefiniteRelaxationValueRegion A →
        (∀ t : ℝ, 0 ≤ t → p + t • d ∈ diagonalSemidefiniteRelaxationValueRegion A) →
        f d ≤ 0 := by
    intro p d hp hdir
    by_contra hd_pos
    have hfd_pos : 0 < f d := lt_of_not_ge hd_pos
    let t : ℝ := ((-a * α) - f p + 1) / f d
    have ht_nonneg : 0 ≤ t := by
      refine div_nonneg ?_ hfd_pos.le
      have hp_sep : f p ≤ -a * α := hf_sep p hp
      linarith
    have hsep_t : f (p + t • d) ≤ -a * α := hf_sep _ (hdir t ht_nonneg)
    have hlin :
        f (p + t • d) = f p + t * f d := by
      rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul]
      simp [smul_eq_mul, mul_comm]
    rw [hlin] at hsep_t
    have hfd_ne : f d ≠ 0 := ne_of_gt hfd_pos
    have htd : t * f d = 1 + (-a * α) - f p := by
      dsimp [t]
      field_simp [t, hfd_ne]
      ring
    linarith
  -- Testing the separator on the pure scalar direction shows that its scalar coefficient is
  -- nonnegative.
  have hup_dir :
      f ((0 : 𝕊^n), (1 : ℝ)) ≤ 0 := by
    refine hrecession_nonpos hp0_mem ?_
    intro t ht
    refine ⟨y0, ?_, ?_⟩
    · simpa [p0, slack0M] using hslack0_nonneg
    · have hcost : c0 ≤ (p0 + t • ((0 : 𝕊^n), (1 : ℝ))).2 := by
        simp [p0, c0]
        linarith
      exact hcost
  have ha_nonneg : 0 ≤ a := by
    rw [hf_eval] at hup_dir
    have hneg : -a ≤ 0 := by
      simpa using hup_dir
    linarith
  -- Testing all negative PSD directions forces the matrix part of the separator to be PSD.
  have htrace_nonneg :
      ∀ P : 𝕊^n, P ∈ 𝕊^n₊ → 0 ≤ Matrix.trace ((Z : Mₙ) * (P : Mₙ)) := by
    intro P hP
    have hPpsd : (P : Mₙ).PosSemidef := by
      rw [mem_positiveSemidefiniteCone_iff] at hP
      exact hP
    have hneg_dir :
        f ((-P : 𝕊^n), (0 : ℝ)) ≤ 0 := by
      refine hrecession_nonpos hp0_mem ?_
      intro t ht
      refine ⟨y0, ?_, ?_⟩
      · exact sub_nonneg.mp <| by
          have hsum_psd : (slack0M + t • (P : Mₙ)).PosSemidef :=
            hslack0_posdef.posSemidef.add (hPpsd.smul ht)
          simpa [p0, slack0M, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_neg] using
            (Matrix.nonneg_iff_posSemidef).mpr hsum_psd
      · simp [p0, c0]
    have hneg_trace : -Matrix.trace ((Z : Mₙ) * (P : Mₙ)) ≤ 0 := by
      rw [hf_eval] at hneg_dir
      simpa [Matrix.mul_neg] using hneg_dir
    linarith
  have hZ_psd : Z ∈ 𝕊^n₊ := separatorNonnegativeOnPsdCone_iff_psdLocal Z htrace_nonneg
  -- The strict feasible slack gives an explicit interior point with zero matrix coordinate.
  have hp0_int :
      p0 ∈ interior (diagonalSemidefiniteRelaxationValueRegion A) := by
    let S0 : 𝕊^n := diagonalSlackSymm A y0
    let U : Set (𝕊^n × ℝ) :=
      {p | S0 - p.1 ∈ (𝕊^n₊₊ : Set 𝕊^n) ∧ c0 < p.2}
    have hU_open : IsOpen U := by
      have hstrict_open : IsOpen (𝕊^n₊₊ : Set 𝕊^n) := by
        exact (isOpen_interior : IsOpen (interior (𝕊^n₊ : Set 𝕊^n)))
      have hmatrix_open :
          IsOpen ((fun p : 𝕊^n × ℝ ↦ S0 - p.1) ⁻¹' (𝕊^n₊₊ : Set 𝕊^n)) :=
        hstrict_open.preimage (continuous_const.sub continuous_fst)
      have hscalar_open :
          IsOpen ((fun p : 𝕊^n × ℝ ↦ p.2) ⁻¹' Set.Ioi c0) :=
        isOpen_Ioi.preimage continuous_snd
      simpa [U, Set.preimage, Set.setOf_and] using hmatrix_open.inter hscalar_open
    have hU_subset : U ⊆ diagonalSemidefiniteRelaxationValueRegion A := by
      intro p hp
      rcases hp with ⟨hp_mat, hp_cost⟩
      have hp_psd : S0 - p.1 ∈ (𝕊^n₊ : Set 𝕊^n) := interior_subset hp_mat
      have hp_le :
          (((p.1 : 𝕊^n) : Mₙ)) ≤ (S0 : Mₙ) := by
        rw [mem_positiveSemidefiniteCone_iff] at hp_psd
        exact sub_nonneg.mp <| by
          simpa using (Matrix.nonneg_iff_posSemidef).mpr hp_psd
      refine ⟨y0, ?_, hp_cost.le⟩
      simpa [S0, diagonalSlackSymm] using hp_le
    have hp0_memU : p0 ∈ U := by
      refine ⟨?_, by simp [p0, c0]⟩
      simpa [p0, S0, diagonalSlackSymm] using
        (mem_strictPositiveSemidefiniteCone_of_posDef hslack0_posdef : S0 ∈ 𝕊^n₊₊)
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (hU_open.mem_nhds hp0_memU) hU_subset
  -- If the scalar coefficient vanished, the separator would be zero on a full ball around the
  -- interior point `p0`, hence zero everywhere.
  have ha_ne : a ≠ 0 := by
    intro ha_zero
    have hf_p0_zero : f p0 = 0 := by
      rw [hf_eval, ha_zero]
      simp [p0]
    have hf_zero_eval : ∀ v : 𝕊^n × ℝ, f v = 0 := by
      intro v
      let γ : ℝ → 𝕊^n × ℝ := fun t ↦ p0 + t • v
      have hγ_cont : Continuous γ := by
        exact continuous_const.add (continuous_id.smul continuous_const)
      have hpre :
          {t : ℝ | γ t ∈ interior (diagonalSemidefiniteRelaxationValueRegion A)} ∈
            nhds (0 : ℝ) := by
        have hγ0_mem : γ 0 ∈ interior (diagonalSemidefiniteRelaxationValueRegion A) := by
          simpa [γ] using hp0_int
        exact hγ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hγ0_mem)
      rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
      let t : ℝ := ε / (2 * (‖v‖ + 1))
      have ht_pos : 0 < t := by
        dsimp [t]
        positivity
      have ht_lt : t < ε := by
        dsimp [t]
        have hden_pos : 0 < 2 * (‖v‖ + 1) := by positivity
        rw [div_lt_iff₀ hden_pos]
        nlinarith [norm_nonneg v, hε_pos]
      have hplus_mem : p0 + t • v ∈ diagonalSemidefiniteRelaxationValueRegion A := by
        exact interior_subset <| hε_sub <| by
          rw [Metric.mem_ball, Real.dist_eq]
          simpa [t, abs_of_nonneg ht_pos.le] using ht_lt
      have hminus_mem : p0 - t • v ∈ diagonalSemidefiniteRelaxationValueRegion A := by
        exact interior_subset <| by
          have hball_mem : -t ∈ Metric.ball (0 : ℝ) ε := by
            rw [Metric.mem_ball, Real.dist_eq]
            have hneg_t : -t < 0 := by linarith
            simpa [t, abs_of_neg hneg_t] using ht_lt
          simpa [γ, sub_eq_add_neg] using hε_sub hball_mem
      have hplus_le : f (p0 + t • v) ≤ 0 := by
        have hplus_raw : f (p0 + t • v) ≤ -a * α := hf_sep _ hplus_mem
        simpa [ha_zero] using hplus_raw
      have hminus_le : f (p0 - t • v) ≤ 0 := by
        have hminus_raw : f (p0 - t • v) ≤ -a * α := hf_sep _ hminus_mem
        simpa [ha_zero] using hminus_raw
      have hplus_eq : f (p0 + t • v) = t * f v := by
        rw [ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul, hf_p0_zero]
        ring
      have hminus_eq : f (p0 - t • v) = -t * f v := by
        rw [sub_eq_add_neg, ContinuousLinearMap.map_add, ContinuousLinearMap.map_neg,
          ContinuousLinearMap.map_smul, hf_p0_zero]
        ring
      rw [hplus_eq] at hplus_le
      rw [hminus_eq] at hminus_le
      have htv_nonpos : t * f v ≤ 0 := hplus_le
      have htv_nonneg : 0 ≤ t * f v := by linarith
      have htv_zero : t * f v = 0 := le_antisymm htv_nonpos htv_nonneg
      exact (mul_eq_zero.mp htv_zero).resolve_left ht_pos.ne'
    have hf_zero : f = 0 := by
      exact ContinuousLinearMap.ext fun v ↦ hf_zero_eval v
    exact hf_ne hf_zero
  have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg ha_ne.symm
  -- The paired diagonal directions force every diagonal entry of `Z` to equal `a`.
  have hdiagZ : ∀ i : Fin n, ((Z : Mₙ).diag) i = a := by
    intro i
    let dPlus : 𝕊^n × ℝ :=
      (diagonalSemidefiniteRelaxationConstraint i, (1 : ℝ))
    have hdPlus_nonpos : f dPlus ≤ 0 := by
      refine hrecession_nonpos hp0_mem ?_
      intro t ht
      let yPlus : Eₙ :=
        WithLp.toLp 2 (fun j : Fin n ↦ y0 j + if j = i then t else 0)
      refine ⟨yPlus, ?_, ?_⟩
      · calc
          (((p0 + t • dPlus).1 : 𝕊^n) : Mₙ)
              = t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ) := by
                  simp [p0, dPlus]
          _ ≤ t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ) + slack0M := by
                simpa using add_le_add_left hslack0_nonneg
                  (t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ))
          _ = Matrix.diagonal (fun j : Fin n ↦ yPlus j) - (A : Mₙ) := by
                ext j k
                by_cases hjk : j = k
                · subst hjk
                  by_cases hji : j = i
                  · subst hji
                    simp [yPlus, slack0M, diagonalSemidefiniteRelaxationConstraint]
                    ring
                  · simp [yPlus, slack0M, diagonalSemidefiniteRelaxationConstraint, hji]
                · simp [yPlus, slack0M, diagonalSemidefiniteRelaxationConstraint, hjk]
      · have hyPlus_sum : ∑ j : Fin n, yPlus j = c0 + t := by
          simp [yPlus, c0, Finset.sum_add_distrib]
        rw [show (p0 + t • dPlus).2 = c0 + 1 + t by simp [p0, dPlus, c0]]
        rw [hyPlus_sum]
        linarith
    have hdiag_le : ((Z : Mₙ).diag) i ≤ a := by
      rw [hf_eval] at hdPlus_nonpos
      simpa [dPlus, trace_mul_diagonalSemidefiniteRelaxationConstraint] using hdPlus_nonpos
    let dMinus : 𝕊^n × ℝ :=
      (-diagonalSemidefiniteRelaxationConstraint i, (-1 : ℝ))
    have hdMinus_nonpos : f dMinus ≤ 0 := by
      refine hrecession_nonpos hp0_mem ?_
      intro t ht
      let yMinus : Eₙ :=
        WithLp.toLp 2 (fun j : Fin n ↦ y0 j - if j = i then t else 0)
      refine ⟨yMinus, ?_, ?_⟩
      · calc
          (((p0 + t • dMinus).1 : 𝕊^n) : Mₙ)
              = -(t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ)) := by
                  simp [p0, dMinus]
          _ ≤ -(t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ)) + slack0M := by
                simpa using add_le_add_left hslack0_nonneg
                  (-(t • ((diagonalSemidefiniteRelaxationConstraint i : 𝕊^n) : Mₙ)))
          _ = Matrix.diagonal (fun j : Fin n ↦ yMinus j) - (A : Mₙ) := by
                ext j k
                by_cases hjk : j = k
                · subst hjk
                  by_cases hji : j = i
                  · subst hji
                    simp [yMinus, slack0M, diagonalSemidefiniteRelaxationConstraint]
                    ring
                  · simp [yMinus, slack0M, diagonalSemidefiniteRelaxationConstraint, hji]
                · simp [yMinus, slack0M, diagonalSemidefiniteRelaxationConstraint, hjk]
      · have hyMinus_sum : ∑ j : Fin n, yMinus j = c0 - t := by
          simp [yMinus, c0]
        have hp0_dMinus :
            (p0 + t • dMinus).2 = c0 + 1 - t := by
          simp [p0, dMinus, c0, sub_eq_add_neg]
        rw [hp0_dMinus]
        rw [hyMinus_sum]
        linarith
    have ha_le_diag : a ≤ ((Z : Mₙ).diag) i := by
      rw [hf_eval] at hdMinus_nonpos
      have haux : -((Z : Mₙ).diag) i + a ≤ 0 := by
        simpa [dMinus, trace_mul_diagonalSemidefiniteRelaxationConstraint, Matrix.mul_neg] using
          hdMinus_nonpos
      linarith
    exact le_antisymm hdiag_le ha_le_diag
  exact ⟨ha_pos, hZ_psd, hdiagZ⟩

/-- Helper for Proposition 7.33: a normalized separator yields a unit-diagonal positive-
semidefinite certificate whose trace against `A` dominates the separated value `α`. -/
private theorem unitDiagonalCertificate_ofDiagonalValueRegionSeparator
    (A : 𝕊^n) (α : ℝ) (Z : 𝕊^n) (a : ℝ)
    (ha_pos : 0 < a) (hZ_psd : Z ∈ 𝕊^n₊)
    (hdiagZ : ∀ i : Fin n, ((Z : Mₙ).diag) i = a)
    {f : StrongDual ℝ (𝕊^n × ℝ)}
    (hf_eval : ∀ p : 𝕊^n × ℝ,
      f p = Matrix.trace ((Z : Mₙ) * ((p.1 : 𝕊^n) : Mₙ)) - a * p.2)
    (hf_sep :
      ∀ p ∈ diagonalSemidefiniteRelaxationValueRegion A, f p ≤ -a * α) :
    ∃ Y : 𝕊^n, Y ∈ 𝕊^n₊ ∧ ((Y : Mₙ).diag = 1) ∧
      α ≤ Matrix.trace ((A : Mₙ) * (Y : Mₙ)) := by
  let Y : 𝕊^n := a⁻¹ • Z
  have hY_psd : Y ∈ 𝕊^n₊ := by
    rw [mem_positiveSemidefiniteCone_iff] at hZ_psd ⊢
    simpa [Y] using hZ_psd.smul (inv_nonneg.mpr ha_pos.le)
  have hY_diag : ((Y : Mₙ).diag = 1) := by
    ext i
    calc
      ((Y : Mₙ).diag) i = a⁻¹ * ((Z : Mₙ).diag) i := by
        simp [Y]
      _ = a⁻¹ * a := by
        rw [hdiagZ i]
      _ = 1 := by
        exact inv_mul_cancel₀ ha_pos.ne'
  have hZ_eq : (Z : Mₙ) = a • (Y : Mₙ) := by
    ext i j
    simp [Y, ha_pos.ne']
  let p : 𝕊^n × ℝ := (diagonalSlackSymm A (0 : Eₙ), (0 : ℝ))
  have hp : p ∈ diagonalSemidefiniteRelaxationValueRegion A := by
    refine ⟨(0 : Eₙ), ?_, ?_⟩
    · simp [p, diagonalSlackSymm_coe]
    · simp [p]
  have halphaZ : a * α ≤ Matrix.trace ((A : Mₙ) * (Z : Mₙ)) := by
    have hp_sep : f p ≤ -a * α := hf_sep p hp
    rw [hf_eval] at hp_sep
    have htrace_slack :
        Matrix.trace ((Z : Mₙ) * ((diagonalSlackSymm A (0 : Eₙ) : 𝕊^n) : Mₙ)) =
          -Matrix.trace ((A : Mₙ) * (Z : Mₙ)) := by
      calc
        Matrix.trace ((Z : Mₙ) * ((diagonalSlackSymm A (0 : Eₙ) : 𝕊^n) : Mₙ))
            = Matrix.trace ((Z : Mₙ) *
                (Matrix.diagonal (fun i : Fin n ↦ (0 : Eₙ) i) - (A : Mₙ))) := by
                  rw [diagonalSlackSymm_coe]
        _ = Matrix.trace ((Z : Mₙ) * Matrix.diagonal (fun i : Fin n ↦ (0 : Eₙ) i)) -
              Matrix.trace ((Z : Mₙ) * (A : Mₙ)) := by
                rw [Matrix.mul_sub, Matrix.trace_sub]
        _ = -Matrix.trace ((A : Mₙ) * (Z : Mₙ)) := by
              rw [show Matrix.diagonal (fun i : Fin n ↦ (0 : Eₙ) i) = (0 : Mₙ) by
                ext i j
                by_cases hij : i = j
                · subst hij
                  simp [Matrix.diagonal]
                · simp [Matrix.diagonal]]
              rw [Matrix.mul_zero, Matrix.trace_zero, Matrix.trace_mul_comm]
              simp
    rw [htrace_slack] at hp_sep
    linarith
  have hAZ :
      a * Matrix.trace ((A : Mₙ) * (Y : Mₙ)) =
        Matrix.trace ((A : Mₙ) * (Z : Mₙ)) := by
    calc
      a * Matrix.trace ((A : Mₙ) * (Y : Mₙ))
          = Matrix.trace (a • ((A : Mₙ) * (Y : Mₙ))) := by
              simp [Matrix.trace_smul]
      _ = Matrix.trace ((A : Mₙ) * (a • (Y : Mₙ))) := by
            simp
      _ = Matrix.trace ((A : Mₙ) * (Z : Mₙ)) := by
            rw [← hZ_eq]
  have halphaY_scaled :
      a * α ≤ a * Matrix.trace ((A : Mₙ) * (Y : Mₙ)) := by
    simpa [hAZ] using halphaZ
  have halphaY : α ≤ Matrix.trace ((A : Mₙ) * (Y : Mₙ)) := by
    nlinarith
  exact ⟨Y, hY_psd, hY_diag, halphaY⟩

/-- Helper for Proposition 7.33: separating the diagonal-majorant value region at
`((0), ψ⋆)` yields a unit-diagonal positive-semidefinite certificate whose trace against `A`
dominates `ψ⋆`. -/
private theorem diagonalSemidefiniteRelaxationOptimalValue_le_sSup_trace_viaSeparation
    (A : 𝕊^n) :
    diagonalSemidefiniteRelaxationOptimalValue A ≤
      sSup ((fun X : 𝕊^n ↦ trace ((A : Mₙ) * (X : Mₙ))) ''
        {X : 𝕊^n | X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)}) := by
  -- Route correction: the weak-duality half is already isolated, so the remaining work is only
  -- the reverse inequality. The intended proof separates the diagonal-majorant value region at
  -- `((0), ψ⋆)`, reads off a PSD separator matrix with unit diagonal from recession directions,
  -- and then evaluates that separator on an exact slack point `(diag(y) - A, ∑ y)`.
  let α : ℝ := diagonalSemidefiniteRelaxationOptimalValue A
  let xα : 𝕊^n × ℝ := ((0 : 𝕊^n), α)
  have hxα_not_mem_interior :
      xα ∉ interior (diagonalSemidefiniteRelaxationValueRegion A) := by
    intro hxα_mem
    let γ : ℝ → 𝕊^n × ℝ := fun t ↦ xα + t • ((0 : 𝕊^n), (1 : ℝ))
    have hγ_cont : Continuous γ := by
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hpre :
        {t : ℝ | γ t ∈ interior (diagonalSemidefiniteRelaxationValueRegion A)} ∈ nhds (0 : ℝ) := by
      have hγ0_mem : γ 0 ∈ interior (diagonalSemidefiniteRelaxationValueRegion A) := by
        simpa [γ, xα] using hxα_mem
      exact hγ_cont.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds hγ0_mem)
    rcases Metric.mem_nhds_iff.mp hpre with ⟨ε, hε_pos, hε_sub⟩
    have hhalf_mem : (-(ε / 2) : ℝ) ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hneg_half : (-(ε / 2) : ℝ) < 0 := by
        nlinarith
      simpa [abs_of_neg hneg_half] using half_lt_self hε_pos
    have hbelow_mem :
        ((0 : 𝕊^n), α - ε / 2) ∈ diagonalSemidefiniteRelaxationValueRegion A := by
      exact interior_subset <| by
        have hmem : γ (-(ε / 2)) ∈ interior (diagonalSemidefiniteRelaxationValueRegion A) :=
          hε_sub hhalf_mem
        simpa [γ, xα, sub_eq_add_neg] using hmem
    have hα_le :
        α ≤ α - ε / 2 := by
      simpa [α] using diagonalSemidefiniteRelaxationZeroFiberLowerBound A hbelow_mem
    linarith
  obtain ⟨f, hf_ne, hf_sep_raw⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point
      (convex_diagonalSemidefiniteRelaxationValueRegion A)
      hxα_not_mem_interior
      (diagonalSemidefiniteRelaxationValueRegion_interior_nonempty A)
  obtain ⟨Z, a, hf_eval⟩ :=
    diagonalSemidefiniteRelaxationSeparatorRepresentation f
  have hf_sep :
      ∀ p ∈ diagonalSemidefiniteRelaxationValueRegion A, f p ≤ -a * α := by
    intro p hp
    calc
      f p ≤ f xα := hf_sep_raw p hp
      _ = -a * α := by
            simpa [xα] using hf_eval xα
  obtain ⟨ha_pos, hZ_psd, hdiagZ⟩ :=
    diagonalSemidefiniteRelaxationSeparatorNormalized A α f hf_ne hf_eval hf_sep
  obtain ⟨Y, hY_psd, hY_diag, hα_le⟩ :=
    unitDiagonalCertificate_ofDiagonalValueRegionSeparator
      A α Z a ha_pos hZ_psd hdiagZ hf_eval hf_sep
  -- The normalized separator itself is a feasible point of the trace image, so `α` is below the
  -- supremum of that image.
  exact hα_le.trans <|
    le_csSup (unitDiagonalTraceImage_bddAbove A) ⟨Y, ⟨hY_psd, hY_diag⟩, rfl⟩

/-- The chapter semidefinite-relaxation value `ψ⋆` from Definition 7.71 admits the standard
unit-diagonal SDP representation as a trace supremum over positive-semidefinite symmetric
matrices. -/
theorem diagonalSemidefiniteRelaxationOptimalValue_eq_sSup_trace
    (A : 𝕊^n) :
    diagonalSemidefiniteRelaxationOptimalValue A =
      sSup ((fun X : 𝕊^n ↦ trace ((A : Mₙ) * (X : Mₙ))) ''
        {X : 𝕊^n | X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)}) := by
  let traceImage : Set ℝ :=
    ((fun X : 𝕊^n ↦ trace ((A : Mₙ) * (X : Mₙ))) ''
      {X : 𝕊^n | X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1)})
  have hTraceImage_nonempty : traceImage.Nonempty := by
    let σ : Fin n → ℝ := fun _ ↦ 1
    have hσ : σ ∈ signVectorSet (Fin n) := by
      rw [mem_signVectorSet_iff]
      intro i
      exact Or.inr rfl
    let X : 𝕊^n := signOuterProductSymm σ
    have hX : X ∈ 𝕊^n₊ ∧ ((X : Mₙ).diag = 1) := by
      -- Reuse the rank-one all-ones sign matrix as a unit-diagonal primal witness.
      simpa [X, σ] using sign_outerProduct_mem_unitDiagonalFeasibleSet σ hσ
    exact ⟨trace ((A : Mₙ) * (X : Mₙ)), ⟨X, hX, rfl⟩⟩
  have hWeak :
      sSup traceImage ≤ diagonalSemidefiniteRelaxationOptimalValue A := by
    -- Weak duality: every unit-diagonal PSD matrix is bounded by every feasible diagonal majorant.
    rw [diagonalSemidefiniteRelaxationOptimalValue_eq_sInf]
    refine csSup_le hTraceImage_nonempty ?_
    rintro _ ⟨X, hX, rfl⟩
    refine le_csInf ?_ ?_
    · exact Set.Nonempty.image _ (diagonalSemidefiniteRelaxationFeasibleSet_nonempty A)
    · rintro _ ⟨y, hy, rfl⟩
      exact trace_le_sum_diagonal_of_unitDiagonalFeasible A hy hX
  have hReverse :
      diagonalSemidefiniteRelaxationOptimalValue A ≤ sSup traceImage := by
    -- Route correction: replace the stalled maximizer route by separating the diagonal-majorant
    -- value region at `((0), ψ⋆)` and reading off the resulting unit-diagonal PSD certificate.
    simpa [traceImage] using
      diagonalSemidefiniteRelaxationOptimalValue_le_sSup_trace_viaSeparation A
  exact le_antisymm hReverse hWeak

/-- Helper for Proposition 7.33: the scalar identity matrix, viewed in the symmetric carrier. -/
private def scalarIdentitySymm
    (ε : ℝ) : 𝕊^n :=
  ⟨ε • (1 : Mₙ), by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    exact (Matrix.isSymm_one : (1 : Mₙ).IsSymm).smul ε
  ⟩

/-- Helper for Proposition 7.33: subtracting a scalar from every diagonal entry subtracts the same
scalar multiple of the identity matrix. -/
private theorem diagonal_sub_scalar_identity
    (y : Eₙ) (ε : ℝ) :
    Matrix.diagonal (fun i : Fin n ↦ y i - ε) =
      Matrix.diagonal (fun i : Fin n ↦ y i) - ε • (1 : Mₙ) := by
  -- Check the diagonal and off-diagonal entries separately.
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal]
  · simp [Matrix.diagonal, hij]

/-- Helper for Proposition 7.33: adding `ε I` to the coefficient matrix is equivalent to
subtracting `ε` from every feasible diagonal majorant coordinate. -/
private theorem mem_diagonalSemidefiniteRelaxationFeasibleSet_add_scalarIdentity_iff
    (A : 𝕊^n) (ε : ℝ) (y : Eₙ) :
    y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A + scalarIdentitySymm ε) ↔
      WithLp.toLp 2 (fun i : Fin n ↦ y i - ε) ∈ diagonalSemidefiniteRelaxationFeasibleSet A := by
  -- Expand both feasible-set conditions into matrix-order inequalities and rewrite the shifted
  -- diagonal matrix in canonical form.
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff,
    mem_diagonalSemidefiniteRelaxationFeasibleSet_iff]
  constructor
  · intro hy
    rw [diagonal_sub_scalar_identity, le_sub_iff_add_le]
    simpa [scalarIdentitySymm, add_comm, add_left_comm, add_assoc] using hy
  · intro hy
    rw [diagonal_sub_scalar_identity, le_sub_iff_add_le] at hy
    simpa [scalarIdentitySymm, add_comm, add_left_comm, add_assoc] using hy

/-- Helper for Proposition 7.33: adding `ε I` shifts every Boolean quadratic value by the exact
constant `ε n` on sign vectors. -/
private theorem quadratic_form_add_scalar_identity_of_signVector
    (A : Mₙ) {σ : Fin n → ℝ} (hσ : σ ∈ signVectorSet (Fin n)) (ε : ℝ) :
    (A + ε • (1 : Mₙ)).toQuadraticMap' σ =
      A.toQuadraticMap' σ + ε * n := by
  -- A sign vector has `σ i ^ 2 = 1` in every coordinate, so the identity contribution is exactly
  -- `ε * n`.
  have hsq : ∀ i : Fin n, σ i * σ i = 1 := by
    intro i
    rcases (mem_signVectorSet_iff.mp hσ i) with hneg | hpos
    · simp [hneg]
    · simp [hpos]
  have hA :
      σ ⬝ᵥ (A *ᵥ σ) = A.toQuadraticMap' σ := by
    simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  have hmul_identity :
      (ε • (1 : Mₙ)) *ᵥ σ = fun i : Fin n ↦ ε * σ i := by
    -- The scalar identity acts coordinatewise on every vector.
    simpa [Pi.smul_apply, Matrix.one_mulVec] using
      (Matrix.smul_mulVec ε (1 : Mₙ) σ)
  have hId :
      σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ) = ε * n := by
    calc
      σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ)
          = σ ⬝ᵥ (ε • σ) := by
              rw [hmul_identity]
              rfl
      _ = ε * (σ ⬝ᵥ σ) := by
        calc
          σ ⬝ᵥ (ε • σ) = ∑ i : Fin n, ε * (σ i * σ i) := by
            simp only [dotProduct, Pi.smul_apply]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
          _ = ε * (σ ⬝ᵥ σ) := by
            rw [dotProduct, Finset.mul_sum]
      _ = ε * ∑ i : Fin n, (1 : ℝ) := by
        refine congrArg (fun t : ℝ ↦ ε * t) ?_
        simp [dotProduct, hsq]
      _ = ε * n := by
        simp
  have hquad_shift :
      (A + ε • (1 : Mₙ)).toQuadraticMap' σ =
        σ ⬝ᵥ (A *ᵥ σ) + σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ) := by
    rw [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply', Matrix.add_mulVec, dotProduct_add]
  have hsplit :
      σ ⬝ᵥ (((A + ε • (1 : Mₙ)) *ᵥ σ)) =
        σ ⬝ᵥ (A *ᵥ σ) + σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ) := by
    calc
      σ ⬝ᵥ (((A + ε • (1 : Mₙ)) *ᵥ σ))
          = σ ⬝ᵥ (A *ᵥ σ + (ε • (1 : Mₙ)) *ᵥ σ) := by
              rw [Matrix.add_mulVec]
      _ = σ ⬝ᵥ (A *ᵥ σ) + σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ) := by
        rw [dotProduct_add]
  -- Split the shifted quadratic form into the original part and the identity contribution.
  calc
    (A + ε • (1 : Mₙ)).toQuadraticMap' σ
        = σ ⬝ᵥ (A *ᵥ σ) + σ ⬝ᵥ ((ε • (1 : Mₙ)) *ᵥ σ) := hquad_shift
    _ = A.toQuadraticMap' σ + ε * n := by
      rw [hA, hId]

/-- Helper for Proposition 7.33: every feasible diagonal majorant bounds the Boolean quadratic
form of every sign vector. -/
private theorem quadratic_form_le_diagonal_majorant_sum_of_feasible
    (A : 𝕊^n) {y : Eₙ} {σ : Fin n → ℝ}
    (hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet A)
    (hσ : σ ∈ signVectorSet (Fin n)) :
    (A : Mₙ).toQuadraticMap' σ ≤ ∑ i : Fin n, y i := by
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff] at hy
  -- Apply positive-semidefinite nonnegativity to the slack matrix `diag y - A`.
  have hpsd : ((Matrix.diagonal fun i : Fin n ↦ y i) - (A : Mₙ)).PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hy)
  have hnonneg := hpsd.dotProduct_mulVec_nonneg σ
  have hsq : ∀ i : Fin n, σ i * σ i = 1 := by
    intro i
    rcases (mem_signVectorSet_iff.mp hσ i) with hneg | hpos
    · simp [hneg]
    · simp [hpos]
  have hdiag :
      σ ⬝ᵥ (Matrix.diagonal (fun i : Fin n ↦ y i) *ᵥ σ) = ∑ i : Fin n, y i := by
    calc
      σ ⬝ᵥ (Matrix.diagonal (fun i : Fin n ↦ y i) *ᵥ σ)
          = ∑ i : Fin n, σ i * (y i * σ i) := by
              simp [dotProduct, Matrix.mulVec, Matrix.diagonal]
      _ = ∑ i : Fin n, y i * (σ i * σ i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = ∑ i : Fin n, y i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [hsq i]
        ring
  have hquad :
      σ ⬝ᵥ ((A : Mₙ) *ᵥ σ) = (A : Mₙ).toQuadraticMap' σ := by
    simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply']
  -- Rewrite the slack quadratic form as `∑ᵢ yᵢ - σᵀAσ`.
  have hineq : 0 ≤ ∑ i : Fin n, y i - (A : Mₙ).toQuadraticMap' σ := by
    calc
    0 ≤ σ ⬝ᵥ (((Matrix.diagonal fun i : Fin n ↦ y i) - (A : Mₙ)) *ᵥ σ) := hnonneg
    _ = ∑ i : Fin n, y i - (A : Mₙ).toQuadraticMap' σ := by
      rw [sub_mulVec, dotProduct_sub, hdiag, hquad]
  linarith

/-- Helper for Proposition 7.33: the Boolean quadratic optimum is bounded above by the diagonal
semidefinite-relaxation value. -/
private theorem booleanQuadraticOptimalValue_le_diagonalSemidefiniteRelaxationOptimalValue
    (A : 𝕊^n) :
    booleanQuadraticOptimalValue (A : Mₙ) ≤ diagonalSemidefiniteRelaxationOptimalValue A := by
  -- Compare the `sSup` over sign vectors with the `sInf` over feasible diagonal majorants
  -- pointwise, then package the comparison through conditional completeness.
  rw [booleanQuadraticOptimalValue_eq_sSup_image]
  rw [diagonalSemidefiniteRelaxationOptimalValue_eq_sInf]
  refine csSup_le ?_ ?_
  · refine Set.Nonempty.image _ ?_
    refine ⟨fun _ : Fin n ↦ 1, ?_⟩
    rw [mem_signVectorSet_iff]
    intro i
    exact Or.inr rfl
  · rintro _ ⟨σ, hσ, rfl⟩
    refine le_csInf ?_ ?_
    · refine Set.Nonempty.image _ (diagonalSemidefiniteRelaxationFeasibleSet_nonempty A)
    · rintro _ ⟨y, hy, rfl⟩
      exact quadratic_form_le_diagonal_majorant_sum_of_feasible A hy hσ

/-- Helper for Proposition 7.33: if `A` is strict positive definite and `diag(y) ⪰ A`, then each
coordinate of `y` is strictly positive. -/
private theorem diagonal_majorant_coordinate_pos_of_posDef
    (A : 𝕊^n₊₊) {y : Eₙ}
    (hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n))
    (i : Fin n) :
    0 < y i := by
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff] at hy
  have hA : (((A : 𝕊^n) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
  have hA_diag : 0 < (((A : 𝕊^n) : Mₙ) i i) := hA.diag_pos
  have hslack :
      ((Matrix.diagonal fun j : Fin n ↦ y j) - (((A : 𝕊^n) : Mₙ))).PosSemidef := by
    -- Convert the Loewner-order inequality into positivity of the slack matrix `diag(y) - A`.
    exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hy)
  have hdiag_nonneg :
      0 ≤ ((Matrix.diagonal fun j : Fin n ↦ y j) - (((A : 𝕊^n) : Mₙ))) i i := by
    simpa using hslack.diag_nonneg (i := i)
  have hdiag_nonneg' : 0 ≤ y i - (((A : 𝕊^n) : Mₙ) i i) := by
    simpa [Matrix.diagonal] using hdiag_nonneg
  linarith

/-- Helper for Proposition 7.33: the reciprocal substitution in the strict-PD route keeps all
coordinates positive. -/
private theorem diagonal_majorant_reciprocal_pos_of_posDef
    (A : 𝕊^n₊₊) {y : Eₙ}
    (hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n))
    (i : Fin n) :
    0 < (y i)⁻¹ := by
  -- The reciprocal is positive because the previous lemma already identifies `y i` as positive.
  exact inv_pos.mpr (diagonal_majorant_coordinate_pos_of_posDef A hy i)

/-- Helper for Proposition 7.33: under the strict-PD reciprocal substitution `u i = (y i)⁻¹`,
the source objective `∑ i, y i` is recovered from `∑ i, (u i)⁻¹`. -/
private theorem diagonal_majorant_sum_eq_sum_inv_reciprocal_of_posDef
    (A : 𝕊^n₊₊) {y : Eₙ}
    (_hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n)) :
    (∑ i : Fin n, (((y i)⁻¹)⁻¹)) = ∑ i : Fin n, y i := by
  -- Rewrite each summand with `inv_inv`; positivity of the feasible diagonal entries supplies the
  -- required nonvanishing hypotheses.
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [inv_inv]

/-- Helper for Proposition 7.33: positive-definite matrix inversion reverses the Loewner order. -/
private theorem posDef_inv_antitone
    {A B : Mₙ} (hA : A.PosDef) (hB : B.PosDef) (hAB : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  letI : Invertible A := hA.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hBlock : (fromBlocks B (1 : Mₙ) (1 : Mₙ)ᴴ A⁻¹).PosSemidef := by
    -- The Schur complement with respect to the lower-right block is exactly `B - A`.
    refine (Matrix.PosDef.fromBlocks₂₂ (A := B) (B := (1 : Mₙ)) (D := A⁻¹) hA.inv).2 ?_
    simpa using (Matrix.le_iff).mp hAB
  have hSchur :
      (A⁻¹ - (1 : Mₙ)ᴴ * B⁻¹ * (1 : Mₙ)).PosSemidef := by
    -- Re-read the same positive block matrix through the upper-left Schur complement.
    exact (Matrix.PosDef.fromBlocks₁₁ (A := B) (B := (1 : Mₙ)) (D := A⁻¹) hB).1 hBlock
  -- Normalize the identity factors to recover the target inverse-order inequality.
  exact (Matrix.le_iff).2 <| by simpa using hSchur

/-- Helper for Proposition 7.33: the theorem-local inverse-diagonal feasible set used by the
source strict-PD reformulation. -/
private def factorizationDiagonalInverseFeasibleSet_local
    (A : 𝕊^n₊₊) : Set Eₙ :=
  {u |
    Matrix.diagonal (fun i : Fin n ↦ u i) ≤ (((A : 𝕊^n) : Mₙ)⁻¹) ∧
      ∀ i : Fin n, 0 < u i}

/-- Helper for Proposition 7.33: membership in the theorem-local inverse-diagonal feasible set is
exactly the ambient inverse-diagonal majorant condition together with coordinatewise positivity.
-/
private theorem mem_factorizationDiagonalInverseFeasibleSet_local_iff
    (A : 𝕊^n₊₊) (u : Eₙ) :
    u ∈ factorizationDiagonalInverseFeasibleSet_local A ↔
      Matrix.diagonal (fun i : Fin n ↦ u i) ≤ (((A : 𝕊^n) : Mₙ)⁻¹) ∧
        ∀ i : Fin n, 0 < u i :=
  Iff.rfl

/-- Helper for Proposition 7.33: the theorem-local inverse-diagonal relaxation value from the
source strict-PD route. -/
private def factorizationDiagonalInverseRelaxationValue_local
    (A : 𝕊^n₊₊) : ℝ :=
  sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) ''
    factorizationDiagonalInverseFeasibleSet_local A)

/-- Helper for Proposition 7.33: expanding the theorem-local inverse-diagonal value recovers its
defining `sInf`. -/
private theorem factorizationDiagonalInverseRelaxationValue_local_eq_sInf
    (A : 𝕊^n₊₊) :
    factorizationDiagonalInverseRelaxationValue_local A =
      sInf ((fun u : Eₙ ↦ ∑ i : Fin n, (u i)⁻¹) ''
        factorizationDiagonalInverseFeasibleSet_local A) :=
  rfl

/-- Helper for Proposition 7.33: an `Eₙ` point in the theorem-local inverse-diagonal feasible set
corresponds to its coordinate function in the canonical Chapter 7 owner. -/
private theorem mem_factorizationDiagonalInverseFeasibleSet_local_iff_owner
    (A : 𝕊^n₊₊) (u : Eₙ) :
    u ∈ factorizationDiagonalInverseFeasibleSet_local A ↔
      u.ofLp ∈ factorizationDiagonalInverseFeasibleSet A := by
  -- Both feasible sets encode the same inverse-diagonal majorant inequality with the same
  -- coordinatewise positivity side condition; only the `WithLp` wrapper differs.
  rw [mem_factorizationDiagonalInverseFeasibleSet_local_iff,
    mem_factorizationDiagonalInverseFeasibleSet_iff]

/-- Helper for Proposition 7.33: the theorem-local inverse-diagonal relaxation value agrees with
the canonical owner from Lemma 7.15. -/
private theorem factorizationDiagonalInverseRelaxationValue_local_eq_owner
    (A : 𝕊^n₊₊) :
    factorizationDiagonalInverseRelaxationValue_local A =
      factorizationDiagonalInverseRelaxationValue A := by
  -- Rewrite both sides to the defining `sInf`; then transport witnesses through `WithLp.ofLp`
  -- and `WithLp.toLp`.
  rw [factorizationDiagonalInverseRelaxationValue_local_eq_sInf,
    factorizationDiagonalInverseRelaxationValue_eq_sInf]
  congr 1
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.ofLp, ?_, by simp⟩
    exact (mem_factorizationDiagonalInverseFeasibleSet_local_iff_owner A u).mp hu
  · rintro ⟨u, hu, rfl⟩
    refine ⟨WithLp.toLp 2 u, ?_, by simp⟩
    simpa using
      (mem_factorizationDiagonalInverseFeasibleSet_local_iff_owner A (WithLp.toLp 2 u)).mpr hu

/-- Helper for Proposition 7.33: after the reciprocal substitution `u i = (y i)⁻¹`, the
theorem-local inverse-diagonal objective agrees with the original diagonal-majorant objective.
-/
private theorem factorizationDiagonalInverse_objective_eq_diagonal_majorant_sum_of_posDef
    (A : 𝕊^n₊₊) {y : Eₙ}
    (_hy : y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n)) :
    (∑ i : Fin n, (((WithLp.toLp 2 fun j : Fin n ↦ (y j)⁻¹) i)⁻¹)) =
      ∑ i : Fin n, y i := by
  -- Evaluate the reciprocal substitution coordinatewise and reuse the source-side sum identity.
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

/-- Helper for Proposition 7.33: a diagonal matrix with nonzero diagonal entries in every
coordinate inverts entrywise. -/
private theorem inv_diagonal_eq_diagonal_inv
    (d : Fin n → ℝ) (hd : ∀ i : Fin n, d i ≠ 0) :
    (Matrix.diagonal d : Mₙ)⁻¹ = Matrix.diagonal (fun i : Fin n ↦ (d i)⁻¹) := by
  -- The function-valued diagonal data is a unit because each coordinate is nonzero.
  have hd_unit : IsUnit d := Pi.isUnit_iff.mpr fun i ↦ isUnit_iff_ne_zero.mpr (hd i)
  rw [Matrix.inv_diagonal, Ring.inverse_of_isUnit hd_unit]
  ext i j
  by_cases hij : i = j
  · subst hij
    -- On the diagonal, evaluate the Pi-unit inverse at the chosen coordinate.
    simp [Matrix.diagonal, IsUnit.val_inv_apply]
  · -- Off the diagonal, both diagonal matrices vanish entrywise.
    simp [Matrix.diagonal, hij]

/-- Helper for Proposition 7.33: the theorem-local reciprocal substitution is involutive on each
coordinate. -/
private theorem doubleReciprocalCoordinate_eq
    (u : Eₙ) (i : Fin n) :
    (((WithLp.toLp 2 (fun j : Fin n ↦ (u j)⁻¹)) i)⁻¹) = u i := by
  -- The theorem-local wrapper does not change coordinates, so `inv_inv` closes the computation.
  simp

/-- Helper for Proposition 7.33: the strict-PD reciprocal substitution identifies the diagonal
majorant feasible set with the theorem-local inverse-diagonal feasible set. -/
private theorem reciprocalDiagonalMajorant_mem_factorizationDiagonalInverseFeasibleSetLocal_iff
    (A : 𝕊^n₊₊) (y : Eₙ) :
    y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n) ↔
      WithLp.toLp 2 (fun i : Fin n ↦ (y i)⁻¹) ∈
        factorizationDiagonalInverseFeasibleSet_local A := by
  rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff,
    mem_factorizationDiagonalInverseFeasibleSet_local_iff]
  constructor
  · intro hy
    have hA : (((A : 𝕊^n) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
    have hy_pos : ∀ i : Fin n, 0 < y i := by
      intro i
      exact diagonal_majorant_coordinate_pos_of_posDef A hy i
    have hdiag : (Matrix.diagonal fun i : Fin n ↦ y i).PosDef := Matrix.PosDef.diagonal hy_pos
    refine ⟨?_, fun i ↦ diagonal_majorant_reciprocal_pos_of_posDef A hy i⟩
    -- Compare the strict-positive matrices by inverting the diagonal majorant inequality.
    have hInv :
        (Matrix.diagonal fun i : Fin n ↦ y i)⁻¹ ≤ (((A : 𝕊^n) : Mₙ)⁻¹) :=
      posDef_inv_antitone hA hdiag hy
    simpa using
      (inv_diagonal_eq_diagonal_inv (fun i : Fin n ↦ y i) (fun i ↦ (hy_pos i).ne')).symm ▸ hInv
  · rintro ⟨hu_diag, hu_pos⟩
    have hA : (((A : 𝕊^n) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
    have hu_diag_pos :
        (Matrix.diagonal fun i : Fin n ↦
          (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i).PosDef :=
      Matrix.PosDef.diagonal hu_pos
    -- Invert the inverse-diagonal inequality back to the original diagonal-majorant inequality.
    have hMajorant :
        ((((A : 𝕊^n) : Mₙ)⁻¹)⁻¹) ≤
          ((Matrix.diagonal fun i : Fin n ↦
            (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i)⁻¹) :=
      posDef_inv_antitone hu_diag_pos hA.inv hu_diag
    letI : Invertible (((A : 𝕊^n) : Mₙ)) := hA.isUnit.invertible
    letI : Invertible
        (Matrix.diagonal fun i : Fin n ↦
          (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i) := hu_diag_pos.isUnit.invertible
    have hdiag_inv :
        ((Matrix.diagonal fun i : Fin n ↦
            (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i)⁻¹) =
          Matrix.diagonal (fun i : Fin n ↦ y i) := by
      calc
        ((Matrix.diagonal fun i : Fin n ↦
            (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i)⁻¹)
            = Matrix.diagonal (fun i : Fin n ↦
                (((WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i)⁻¹)) := by
                  rw [inv_diagonal_eq_diagonal_inv
                    (fun i : Fin n ↦ (WithLp.toLp 2 (fun j : Fin n ↦ (y j)⁻¹)) i)
                    (fun i ↦ (hu_pos i).ne')]
        _ = Matrix.diagonal (fun i : Fin n ↦ y i) := by
              congr 1
              funext i
              exact doubleReciprocalCoordinate_eq y i
    simpa [hdiag_inv] using hMajorant

/-- Helper for Proposition 7.33: the theorem-local factorization feasible set consists of
positive-semidefinite symmetric matrices with trace `1`. -/
private def localFactorizationSemidefiniteFeasibleSet : Set 𝕊^n :=
  {X | X ∈ 𝕊^n₊ ∧ Matrix.trace (X : Mₙ) = 1}

/-- Helper for Proposition 7.33: membership in the theorem-local factorization feasible set is
the expected PSD-plus-trace condition. -/
private theorem mem_localFactorizationSemidefiniteFeasibleSet_iff
    (X : 𝕊^n) :
    X ∈ localFactorizationSemidefiniteFeasibleSet ↔
      X ∈ 𝕊^n₊ ∧ Matrix.trace (X : Mₙ) = 1 :=
  Iff.rfl

/-- Helper for Proposition 7.33: the theorem-local trace-one PSD feasible set is exactly the
canonical factorization feasible set from Lemma 7.15. -/
private theorem localFactorizationSemidefiniteFeasibleSet_eq_owner :
    localFactorizationSemidefiniteFeasibleSet =
      (factorizationSemidefiniteFeasibleSet : Set 𝕊^n) := by
  -- The only difference is the owner used for the PSD condition, and
  -- `mem_positiveSemidefiniteCone_iff` identifies those two views.
  ext X
  constructor
  · intro hX
    rcases hX with ⟨hpsd, htrace⟩
    rw [mem_positiveSemidefiniteCone_iff] at hpsd
    rw [mem_factorizationSemidefiniteFeasibleSet_iff]
    exact ⟨hpsd, htrace⟩
  · intro hX
    rw [mem_factorizationSemidefiniteFeasibleSet_iff] at hX
    rcases hX with ⟨hpsd, htrace⟩
    refine ⟨?_, htrace⟩
    rw [mem_positiveSemidefiniteCone_iff]
    exact hpsd

/-- Helper for Proposition 7.33: the theorem-local factorization objective from the source proof.
-/
private def localFactorizationSemidefiniteObjective
    (L : Mₙ) (X : 𝕊^n) : ℝ :=
  (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)

/-- Helper for Proposition 7.33: the theorem-local factorization objective is definitionally the
canonical factorization objective. -/
private theorem localFactorizationSemidefiniteObjective_eq_owner
    (L : Mₙ) (X : 𝕊^n) :
    localFactorizationSemidefiniteObjective L X =
      factorizationSemidefiniteObjective L X :=
  rfl

/-- Helper for Proposition 7.33: the theorem-local factorization relaxation value is the supremum
of the factorization objective over the trace-one PSD slice. -/
private def localFactorizationSemidefiniteRelaxationValue
    (L : Mₙ) : ℝ :=
  sSup (localFactorizationSemidefiniteObjective L '' localFactorizationSemidefiniteFeasibleSet)

/-- Helper for Proposition 7.33: expanding the theorem-local factorization relaxation value gives
its defining `sSup`. -/
private theorem localFactorizationSemidefiniteRelaxationValue_eq_sSup
    (L : Mₙ) :
    localFactorizationSemidefiniteRelaxationValue L =
      sSup (localFactorizationSemidefiniteObjective L ''
        localFactorizationSemidefiniteFeasibleSet) :=
  rfl

/-- Helper for Proposition 7.33: the theorem-local factorization relaxation value agrees with the
canonical owner from Lemma 7.15. -/
private theorem localFactorizationSemidefiniteRelaxationValue_eq_owner
    (L : Mₙ) :
    localFactorizationSemidefiniteRelaxationValue L =
      factorizationSemidefiniteRelaxationValue L := by
  -- Rewrite both values to the defining `sSup`; after that, the objective and feasible-set
  -- owners are already identified by the previous helper lemmas.
  simp [localFactorizationSemidefiniteRelaxationValue_eq_sSup,
    factorizationSemidefiniteRelaxationValue_eq_sSup,
    localFactorizationSemidefiniteFeasibleSet_eq_owner,
    localFactorizationSemidefiniteObjective_eq_owner]

/-- Helper for Proposition 7.33: choose the coordinatewise sign of a vector, sending zero to `1`.
-/
private def coordinateSignChoice
    (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if w i < 0 then -1 else 1

/-- Helper for Proposition 7.33: the coordinatewise sign choice is always a sign vector. -/
private theorem coordinateSignChoice_mem_signVectorSet
    (w : Fin n → ℝ) :
    coordinateSignChoice w ∈ signVectorSet (Fin n) := by
  -- Each coordinate of `coordinateSignChoice w` is definitionally either `-1` or `1`.
  rw [mem_signVectorSet_iff]
  intro i
  by_cases hneg : w i < 0
  · left
    simp [coordinateSignChoice, hneg]
  · right
    simp [coordinateSignChoice, hneg]

/-- Helper for Proposition 7.33: pairing a vector with its coordinatewise sign choice sums the
absolute values of its coordinates. -/
private theorem coordinateSignChoice_dot_eq_sum_abs
    (w : Fin n → ℝ) :
    coordinateSignChoice w ⬝ᵥ w = ∑ i : Fin n, |w i| := by
  -- Check each summand separately: the chosen sign exactly converts `w i` to `|w i|`.
  rw [dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hneg : w i < 0
  · calc
      coordinateSignChoice w i * w i = (-1 : ℝ) * w i := by
        simp [coordinateSignChoice, hneg]
      _ = |w i| := by
        rw [abs_of_neg hneg]
        ring
  · have hnonneg : 0 ≤ w i := le_of_not_gt hneg
    calc
      coordinateSignChoice w i * w i = (1 : ℝ) * w i := by
        simp [coordinateSignChoice, hneg]
      _ = |w i| := by
        rw [abs_of_nonneg hnonneg]
        simp

/-- Helper for Proposition 7.33: `Lᵀ L` canonically defines a symmetric matrix. -/
private def gramSymm
    (L : Mₙ) : 𝕊^n :=
  ⟨Lᵀ * L, by
    rw [RealSymmetricMatrixSpace.mem_iff_isSymm]
    exact Matrix.isSymm_transpose_mul_self L
  ⟩

/-- Helper for Proposition 7.33: the Boolean quadratic objective attached to a Gram matrix is
bounded above because the diagonal-relaxation feasible set is nonempty. -/
private theorem gram_booleanQuadratic_image_bddAbove
    (L : Mₙ) :
    BddAbove ((Lᵀ * L).toQuadraticMap' '' signVectorSet (Fin n)) := by
  let A : 𝕊^n := gramSymm L
  rcases diagonalSemidefiniteRelaxationFeasibleSet_nonempty A with ⟨y, hy⟩
  refine ⟨∑ i : Fin n, y i, ?_⟩
  rintro _ ⟨σ, hσ, rfl⟩
  exact quadratic_form_le_diagonal_majorant_sum_of_feasible A hy hσ

/-- Helper for Proposition 7.33: every Gram matrix has a nonnegative quadratic form. -/
private theorem quadraticForm_nonneg_of_gram
    (L : Mₙ) (x : Fin n → ℝ) :
    0 ≤ (Lᵀ * L).toQuadraticMap' x := by
  have hpsd : (Lᵀ * L).PosSemidef := by
    simpa using (Matrix.posSemidef_conjTranspose_mul_self L)
  -- Evaluate the quadratic form through the standard PSD inequality `xᵀ(LᵀL)x ≥ 0`.
  simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply'] using hpsd.dotProduct_mulVec_nonneg x

/-- Helper for Proposition 7.33: the Boolean quadratic optimum of a Gram matrix is nonnegative,
because every sign vector gives a nonnegative quadratic value. -/
private theorem booleanQuadraticOptimalValue_nonneg_of_gram
    (L : Mₙ) :
    0 ≤ booleanQuadraticOptimalValue (Lᵀ * L) := by
  rw [booleanQuadraticOptimalValue_eq_sSup_image]
  let σ : Fin n → ℝ := fun _ ↦ 1
  have hσ : σ ∈ signVectorSet (Fin n) := by
    rw [mem_signVectorSet_iff]
    intro i
    exact Or.inr rfl
  have hσ_nonneg : 0 ≤ (Lᵀ * L).toQuadraticMap' σ := by
    -- The new Gram-quadratic helper isolates the PSD positivity used at the witness sign vector.
    exact quadraticForm_nonneg_of_gram L σ
  exact hσ_nonneg.trans <|
    le_csSup (gram_booleanQuadratic_image_bddAbove L) ⟨σ, hσ, rfl⟩

/-- Helper for Proposition 7.33: the coordinatewise sign choice turns the absolute row-sum
kernel of `Lᵀ * z` into one Boolean quadratic witness for the Gram matrix `Lᵀ L`. -/
private theorem sumAbs_transposeMulVec_sq_le_booleanQuadraticOptimalValue_mul_dotProduct
    (L : Mₙ) (z : Eₙ) :
    (∑ i : Fin n, |(Lᵀ *ᵥ z) i|) ^ (2 : ℕ) ≤
      booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z) := by
  let σ : Fin n → ℝ := coordinateSignChoice (Lᵀ *ᵥ z)
  have hσ : σ ∈ signVectorSet (Fin n) := coordinateSignChoice_mem_signVectorSet (Lᵀ *ᵥ z)
  have hsumAbs :
      ∑ i : Fin n, |(Lᵀ *ᵥ z) i| = σ ⬝ᵥ (Lᵀ *ᵥ z) := by
    -- The chosen sign vector makes the signed sum equal the absolute-value sum coordinatewise.
    simpa [σ] using (coordinateSignChoice_dot_eq_sum_abs (Lᵀ *ᵥ z)).symm
  have htransposePairing :
      σ ⬝ᵥ (Lᵀ *ᵥ z) = (L *ᵥ σ) ⬝ᵥ z := by
    -- Rewrite the signed sum through the transpose so that Cauchy-Schwarz sees the Gram vector
    -- `L * σ`.
    rw [dotProduct_mulVec, vecMul_transpose]
  have hcauchy :
      (σ ⬝ᵥ (Lᵀ *ᵥ z)) ^ (2 : ℕ) ≤ ((Lᵀ * L).toQuadraticMap' σ) * (z ⬝ᵥ z) := by
    -- Apply Euclidean Cauchy-Schwarz to the pair `(L * σ, z)` after rewriting both inner terms
    -- back to matrix quadratic forms.
    have hinner :=
      real_inner_mul_inner_self_le (WithLp.toLp 2 (L *ᵥ σ)) (WithLp.toLp 2 z.ofLp)
    have hleft :
        inner ℝ (WithLp.toLp 2 (L *ᵥ σ)) z = σ ⬝ᵥ (Lᵀ *ᵥ z) := by
      calc
        inner ℝ (WithLp.toLp 2 (L *ᵥ σ)) z
            = (L *ᵥ σ) ⬝ᵥ z := by
                simpa [dotProduct_comm] using
                  (EuclideanSpace.inner_toLp_toLp (L *ᵥ σ) z.ofLp)
        _ = σ ⬝ᵥ (Lᵀ *ᵥ z) := htransposePairing.symm
    have hgramPairing :
        ((Lᵀ * L).toQuadraticMap' σ) = (L *ᵥ σ) ⬝ᵥ (L *ᵥ σ) := by
      simp [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
        Matrix.toLinearMap₂'_apply', dotProduct_mulVec, vecMul_transpose, ← mulVec_mulVec]
    have hgramNorm :
        ‖WithLp.toLp 2 (L *ᵥ σ)‖ * ‖WithLp.toLp 2 (L *ᵥ σ)‖ =
          ((Lᵀ * L).toQuadraticMap' σ) := by
      calc
        ‖WithLp.toLp 2 (L *ᵥ σ)‖ * ‖WithLp.toLp 2 (L *ᵥ σ)‖
            = (L *ᵥ σ) ⬝ᵥ (L *ᵥ σ) := by
                simpa [pow_two, dotProduct] using
                  (EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (L *ᵥ σ)))
        _ = ((Lᵀ * L).toQuadraticMap' σ) := hgramPairing.symm
    have hself :
        ‖z‖ * ‖z‖ = z ⬝ᵥ z := by
      simpa [pow_two, dotProduct] using (EuclideanSpace.real_norm_sq_eq z)
    simpa [pow_two, hleft, hgramNorm, hself] using hinner
  have hgramWitness :
      (Lᵀ * L).toQuadraticMap' σ ≤ booleanQuadraticOptimalValue (Lᵀ * L) := by
    -- The signed witness belongs to the Boolean feasible set defining `f⋆`.
    rw [booleanQuadraticOptimalValue_eq_sSup_image]
    exact le_csSup (gram_booleanQuadratic_image_bddAbove L) ⟨σ, hσ, rfl⟩
  have hdot_nonneg : 0 ≤ z ⬝ᵥ z := by
    -- The Euclidean self-pairing is always nonnegative.
    have hself :
        z ⬝ᵥ z = ‖z‖ * ‖z‖ := by
      simpa [pow_two, dotProduct] using (EuclideanSpace.real_norm_sq_eq z).symm
    have hnormsq : 0 ≤ ‖z‖ * ‖z‖ := by positivity
    simpa [hself] using hnormsq
  have hscale :
      ((Lᵀ * L).toQuadraticMap' σ) * (z ⬝ᵥ z) ≤
        booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z) := by
    exact mul_le_mul_of_nonneg_right hgramWitness hdot_nonneg
  -- Assemble the sign-identity, Cauchy-Schwarz, and the Boolean witness bound.
  calc
    (∑ i : Fin n, |(Lᵀ *ᵥ z) i|) ^ (2 : ℕ)
        = (σ ⬝ᵥ (Lᵀ *ᵥ z)) ^ (2 : ℕ) := by rw [hsumAbs]
    _ ≤ ((Lᵀ * L).toQuadraticMap' σ) * (z ⬝ᵥ z) := hcauchy
    _ ≤ booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z) := hscale

/-- Helper for Proposition 7.33: the square root of a strict positive-definite matrix gives the
Gram factorization needed by the source proof. -/
private theorem sqrt_factorization_eq_of_posDef
    (A : 𝕊^n₊₊) :
    ((A : 𝕊^n) : Mₙ) =
      (CFC.sqrt (((A : 𝕊^n) : Mₙ)))ᵀ * CFC.sqrt (((A : 𝕊^n) : Mₙ)) := by
  have hA : (((A : 𝕊^n) : Mₙ)).PosDef := strictPositiveSemidefiniteCone_posDef A
  have hsqrt_symm : (CFC.sqrt (((A : 𝕊^n) : Mₙ))).IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using
      (CFC.sqrt_nonneg (((A : 𝕊^n) : Mₙ))).posSemidef.isHermitian
  have hsqrt_transpose :
      (CFC.sqrt (((A : 𝕊^n) : Mₙ)))ᵀ = CFC.sqrt (((A : 𝕊^n) : Mₙ)) := by
    simpa [Matrix.IsSymm] using hsqrt_symm
  -- Rewrite `A` as `sqrt(A)^T * sqrt(A)` so the lower bound can consume the factorization API.
  calc
    ((A : 𝕊^n) : Mₙ)
        = CFC.sqrt (((A : 𝕊^n) : Mₙ)) * CFC.sqrt (((A : 𝕊^n) : Mₙ)) := by
            symm
            rw [CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg]
    _ = (CFC.sqrt (((A : 𝕊^n) : Mₙ)))ᵀ * CFC.sqrt (((A : 𝕊^n) : Mₙ)) := by
      simp [hsqrt_transpose]

/-- Helper for Proposition 7.33: the positive-definite diagonal relaxation is rewritten into the
theorem-local factorization relaxation by the source reciprocal substitution. -/
private theorem
    diagonalValue_eq_localFactorizationValue_of_posDef
    (A : 𝕊^n₊₊) :
    diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) =
      localFactorizationSemidefiniteRelaxationValue (CFC.sqrt (((A : 𝕊^n) : Mₙ))) := by
  -- Route correction: the older trace-supremum route obscures the source proof. We now isolate
  -- the strict-PD bridge into the two source steps that still matter: the reciprocal `sInf`
  -- reformulation and the theorem-local Lemma 7.15 factorization bridge.
  have hreciprocal :
      diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) =
        factorizationDiagonalInverseRelaxationValue_local A := by
    -- Transport the two `sInf` images through the reciprocal substitution `y ↦ y⁻¹`.
    rw [diagonalSemidefiniteRelaxationOptimalValue_eq_sInf,
      factorizationDiagonalInverseRelaxationValue_local_eq_sInf]
    congr 1
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨WithLp.toLp 2 (fun i : Fin n ↦ (y i)⁻¹), ?_, ?_⟩
      · exact
          (reciprocalDiagonalMajorant_mem_factorizationDiagonalInverseFeasibleSetLocal_iff
            A y).mp hy
      · -- The reciprocal objective is exactly the original diagonal-majorant objective.
        have hobjective :
            (∑ i : Fin n, (((WithLp.toLp 2 fun j : Fin n ↦ (y j)⁻¹) i)⁻¹)) =
              ∑ i : Fin n, y i :=
          factorizationDiagonalInverse_objective_eq_diagonal_majorant_sum_of_posDef A hy
        exact hobjective
    · rintro ⟨u, hu, rfl⟩
      refine ⟨WithLp.toLp 2 (fun i : Fin n ↦ (u i)⁻¹), ?_, ?_⟩
      · -- Apply the reciprocal feasible-set equivalence in the reverse direction.
        have hu_recip :
            WithLp.toLp 2 (fun i : Fin n ↦
              (((WithLp.toLp 2 (fun j : Fin n ↦ (u j)⁻¹)) i)⁻¹)) ∈
                factorizationDiagonalInverseFeasibleSet_local A := by
          -- Normalize the double reciprocal witness back to the original feasible point `u`.
          have hvec :
              WithLp.toLp 2 (fun i : Fin n ↦
                (((WithLp.toLp 2 (fun j : Fin n ↦ (u j)⁻¹)) i)⁻¹)) = u := by
            ext i
            exact doubleReciprocalCoordinate_eq u i
          simpa [hvec] using hu
        have htransport :=
          (reciprocalDiagonalMajorant_mem_factorizationDiagonalInverseFeasibleSetLocal_iff A
            (WithLp.toLp 2 (fun i : Fin n ↦ (u i)⁻¹))).mpr
        simpa using htransport hu_recip
      · -- The inverse of the reciprocal substitution recovers the original objective.
        simp
  have hfactorization :
      factorizationDiagonalInverseRelaxationValue_local A =
        localFactorizationSemidefiniteRelaxationValue (CFC.sqrt (((A : 𝕊^n) : Mₙ))) := by
    -- Route correction: instead of extending a theorem-local Lemma 7.15 clone, pass through the
    -- canonical owner theorem and rewrite the theorem-local owners away on both ends.
    calc
      factorizationDiagonalInverseRelaxationValue_local A
          = factorizationDiagonalInverseRelaxationValue A := by
              rw [factorizationDiagonalInverseRelaxationValue_local_eq_owner]
      _ =
          factorizationSemidefiniteRelaxationValue
            (CFC.sqrt (((A : 𝕊^n) : Mₙ))) := by
              exact factorizationDiagonalInverseRelaxationValue_eq_semidefiniteRelaxationValue
                A (CFC.sqrt (((A : 𝕊^n) : Mₙ))) (sqrt_factorization_eq_of_posDef A)
      _ =
          localFactorizationSemidefiniteRelaxationValue
            (CFC.sqrt (((A : 𝕊^n) : Mₙ))) := by
              rw [localFactorizationSemidefiniteRelaxationValue_eq_owner]
  exact hreciprocal.trans hfactorization

/-- Helper for Proposition 7.33: the centered unit-variance real Gaussian has first absolute
moment `√(2 / π)`. -/
private theorem gaussianReal_absIntegral_eq_sqrtTwoDivPi :
    ∫ x, |x| ∂ ProbabilityTheory.gaussianReal 0 1 = Real.sqrt (2 / Real.pi) := by
  have hhalfMoment :
      ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) = 1 := by
    -- Rewrite the real integral as a complex integral of `Complex.ofReal`, then reuse the
    -- primitive Gaussian half-line identity.
    have hcomplex :
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
            ((x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : ℂ) = 1 := by
      calc
        ∫ x : ℝ in Set.Ioi (0 : ℝ),
            ((x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) : ℝ) : ℂ)
            =
              ∫ x : ℝ in Set.Ioi (0 : ℝ),
                (x : ℂ) * Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ (2 : ℕ)) := by
                  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                  intro x hx
                  simp [pow_two, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
        _ = 1 := by
              simpa using integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
    have hcomplex' :
        ((∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ))) : ℂ) = 1 := by
      simpa [Complex.ofReal_mul] using hcomplex
    exact_mod_cast hcomplex'
  have hsplit :
      ∫ x, ProbabilityTheory.gaussianPDFReal 0 1 x * |x| =
        2 * ∫ x in Set.Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 x * x := by
    -- The density times `|x|` is an even function, so `integral_comp_abs` reduces the integral
    -- to twice the positive half-line.
    calc
      ∫ x, ProbabilityTheory.gaussianPDFReal 0 1 x * |x|
          = ∫ x, ProbabilityTheory.gaussianPDFReal 0 1 |x| * |x| := by
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              simp [ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv]
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 x * x := by
            simpa using
              (integral_comp_abs
                (f := fun x : ℝ => ProbabilityTheory.gaussianPDFReal 0 1 x * x))
  have hdensityHalf :
      ∫ x in Set.Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 x * x =
        (Real.sqrt (2 * Real.pi))⁻¹ := by
    -- Pull out the Gaussian normalization constant and reuse the primitive computation above.
    calc
      ∫ x in Set.Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 x * x
          =
            ∫ x in Set.Ioi (0 : ℝ),
              (Real.sqrt (2 * Real.pi))⁻¹ *
                (x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ))) := by
                  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                  intro x hx
                  simp [ProbabilityTheory.gaussianPDFReal, div_eq_mul_inv, pow_two, mul_assoc,
                    mul_left_comm, mul_comm]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℕ)) := by
              rw [MeasureTheory.integral_const_mul]
      _ = (Real.sqrt (2 * Real.pi))⁻¹ := by rw [hhalfMoment, mul_one]
  have hconst :
      2 * (Real.sqrt (2 * Real.pi))⁻¹ = Real.sqrt (2 / Real.pi) := by
    have hsq_left :
        (2 * (Real.sqrt (2 * Real.pi))⁻¹) ^ (2 : ℕ) = 2 / Real.pi := by
      rw [pow_two]
      field_simp [Real.pi_ne_zero]
      rw [Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)]
    have hsq_right :
        (Real.sqrt (2 / Real.pi)) ^ (2 : ℕ) = 2 / Real.pi := by
      rw [Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)]
    exact (sq_eq_sq₀ (by positivity) (by positivity)).mp <| by
      rw [hsq_left, hsq_right]
  -- Assemble the density rewrite, the even-function reduction, and the constant simplification.
  rw [ProbabilityTheory.integral_gaussianReal_eq_integral_smul (v := 1) one_ne_zero]
  simp only [smul_eq_mul]
  calc
    ∫ x, ProbabilityTheory.gaussianPDFReal 0 1 x * |x|
        = 2 * ∫ x in Set.Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal 0 1 x * x := hsplit
    _ = 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by rw [hdensityHalf]
    _ = Real.sqrt (2 / Real.pi) := hconst

/-- Helper for Proposition 7.33: the first absolute moment of a centered real Gaussian with
variance `v` is `√(2 / π) * √v`. -/
private theorem gaussianReal_absIntegral_eq_sqrtTwoDivPi_mul_sqrtVariance
    (v : NNReal) :
    ∫ x, |x| ∂ ProbabilityTheory.gaussianReal 0 v =
      Real.sqrt (2 / Real.pi) * Real.sqrt v := by
  let c : ℝ := Real.sqrt v
  have hc_nonneg : 0 ≤ c := Real.sqrt_nonneg _
  have hmap :
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal)).map (fun x : ℝ ↦ c * x) =
        ProbabilityTheory.gaussianReal 0 v := by
    -- The centered variance-`v` Gaussian is the pushforward of the unit Gaussian by `x ↦ √v x`.
    calc
      (ProbabilityTheory.gaussianReal 0 (1 : NNReal)).map (fun x : ℝ ↦ c * x)
          =
            ProbabilityTheory.gaussianReal (c * 0)
              (.mk (c ^ 2) (sq_nonneg _) * (1 : NNReal)) := by
                simpa [c] using
                  (ProbabilityTheory.gaussianReal_map_const_mul
                    (μ := (0 : ℝ)) (v := (1 : NNReal)) c)
      _ = ProbabilityTheory.gaussianReal 0 v := by
            congr 1
            · simp
            · ext
              simp [c, Real.sq_sqrt, mul_comm]
  -- Transport the unit-variance identity through the scaling map.
  rw [← hmap, MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  calc
    ∫ x, |c * x| ∂ ProbabilityTheory.gaussianReal 0 (1 : NNReal)
        = ∫ x, c * |x| ∂ ProbabilityTheory.gaussianReal 0 (1 : NNReal) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            simp [abs_mul, hc_nonneg]
    _ = c * ∫ x, |x| ∂ ProbabilityTheory.gaussianReal 0 (1 : NNReal) := by
          rw [MeasureTheory.integral_const_mul]
    _ = c * Real.sqrt (2 / Real.pi) := by rw [gaussianReal_absIntegral_eq_sqrtTwoDivPi]
    _ = Real.sqrt (2 / Real.pi) * Real.sqrt v := by
          simp [c, mul_comm]

/-- Helper for Proposition 7.33: every theorem-local factorization-feasible matrix has trace `1`.
-/
private theorem trace_eq_one_of_mem_localFactorizationSemidefiniteFeasibleSet
    {X : 𝕊^n} (hX : X ∈ localFactorizationSemidefiniteFeasibleSet) :
    Matrix.trace (X : Mₙ) = 1 := by
  -- The trace normalization is part of the theorem-local feasible-set definition.
  exact (mem_localFactorizationSemidefiniteFeasibleSet_iff X).mp hX |>.2

/-- Helper for Proposition 7.33: the Gaussian second moment of a trace-one PSD covariance is the
trace of that covariance matrix. -/
private theorem integral_dotProduct_multivariateGaussian_eq_trace
    {X : 𝕊^n} (hX : X ∈ localFactorizationSemidefiniteFeasibleSet) :
    ∫ z, z ⬝ᵥ z ∂ ProbabilityTheory.multivariateGaussian 0 (X : Mₙ) =
      Matrix.trace (X : Mₙ) := by
  let μ := ProbabilityTheory.multivariateGaussian 0 (X : Mₙ)
  have hpsd : (X : Mₙ).PosSemidef := by
    -- The covariance matrix is positive semidefinite by feasibility.
    simpa [mem_positiveSemidefiniteCone_iff] using
      (mem_localFactorizationSemidefiniteFeasibleSet_iff X).mp hX |>.1
  calc
    ∫ z, z ⬝ᵥ z ∂ μ = ∫ z, ∑ i : Fin n, z i ^ (2 : ℕ) ∂ μ := by
      -- Expand the Euclidean self-pairing into the sum of coordinate squares.
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with z
      simp [dotProduct, pow_two]
    _ = ∑ i : Fin n, ∫ z, z i ^ (2 : ℕ) ∂ μ := by
          have hcoord_sq_integrable :
              ∀ i : Fin n, MeasureTheory.Integrable (fun z : Eₙ ↦ z i ^ (2 : ℕ)) μ := by
            intro i
            have hsqGaussian :
                MeasureTheory.Integrable (fun x : ℝ ↦ x ^ (2 : ℕ))
                  (ProbabilityTheory.gaussianReal 0 (((X : Mₙ) i i).toNNReal)) := by
              exact
                MeasureTheory.MemLp.integrable_sq
                  (ProbabilityTheory.memLp_id_gaussianReal (μ := 0)
                    (v := ((X : Mₙ) i i).toNNReal) 2)
            have hmap_eq :
                MeasureTheory.Measure.map (fun z : Eₙ ↦ z i) μ =
                  ProbabilityTheory.gaussianReal 0 (((X : Mₙ) i i).toNNReal) := by
              simpa [μ] using
                (ProbabilityTheory.measurePreserving_eval_multivariateGaussian
                  (μ := (0 : Eₙ)) (S := (X : Mₙ)) hpsd (i := i)).map_eq
            have hsqMap :
                MeasureTheory.Integrable (fun x : ℝ ↦ x ^ (2 : ℕ))
                  (MeasureTheory.Measure.map (fun z : Eₙ ↦ z i) μ) := by
              simpa [hmap_eq] using hsqGaussian
            simpa using
              (MeasureTheory.integrable_map_measure
                (g := fun x : ℝ ↦ x ^ (2 : ℕ))
                (f := fun z : Eₙ ↦ z i)
                (by fun_prop) (by fun_prop)).mp hsqMap
          rw [MeasureTheory.integral_finset_sum]
          intro i hi
          exact hcoord_sq_integrable i
    _ = ∑ i : Fin n, (X : Mₙ) i i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hmean_zero : ∫ z, z i ∂ μ = 0 := by
            -- Every coordinate has mean zero because the Gaussian is centered.
            calc
              ∫ z, z i ∂ μ = (EuclideanSpace.proj i) (∫ z, z ∂ μ) := by
                  simpa [EuclideanSpace.coe_proj] using
                    (ContinuousLinearMap.integral_comp_id_comm
                      (μ := μ)
                      ProbabilityTheory.IsGaussian.integrable_id
                      (EuclideanSpace.proj i))
              _ = 0 := by
                  simp [μ, ProbabilityTheory.integral_id_multivariateGaussian]
          have hsquare :
              ∫ z, z i ^ (2 : ℕ) ∂ μ =
                ProbabilityTheory.variance (fun z : Eₙ ↦ z i) μ := by
            -- For a centered coordinate, the second moment is its variance.
            symm
            exact ProbabilityTheory.variance_of_integral_eq_zero
              (Measurable.aemeasurable <| by fun_prop) hmean_zero
          rw [hsquare, ProbabilityTheory.variance_eval_multivariateGaussian hpsd]
    _ = Matrix.trace (X : Mₙ) := by
          simp [Matrix.trace]

/-- Helper for Proposition 7.33: each row linear form of `Lᵀ` under the centered Gaussian with
covariance `X` has first absolute moment `√(2 / π)` times the square root of its variance
quadratic form. -/
private theorem integral_abs_transposeMulVec_eval_multivariateGaussian
    (L : Mₙ) {X : 𝕊^n} (hX : X ∈ localFactorizationSemidefiniteFeasibleSet) (i : Fin n) :
    ∫ z, |(Lᵀ *ᵥ z) i| ∂ ProbabilityTheory.multivariateGaussian 0 (X : Mₙ) =
      Real.sqrt (2 / Real.pi) * Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
  let μ := ProbabilityTheory.multivariateGaussian 0 (X : Mₙ)
  let row : Eₙ := WithLp.toLp 2 (Lᵀ i)
  let rowDual : StrongDual ℝ Eₙ := InnerProductSpace.toDualMap ℝ Eₙ row
  have hpsd : (X : Mₙ).PosSemidef := by
    -- The covariance matrix is positive semidefinite on the factorization-feasible slice.
    simpa [mem_positiveSemidefiniteCone_iff] using
      (mem_localFactorizationSemidefiniteFeasibleSet_iff X).mp hX |>.1
  have hrow_apply :
      (fun z : Eₙ ↦ rowDual z) = fun z : Eₙ ↦ (Lᵀ *ᵥ z) i := by
    -- The chosen continuous linear form is exactly the `i`-th row pairing of `Lᵀ`.
    ext z
    calc
      rowDual z = inner ℝ row z := by
        rfl
      _ = (Lᵀ i) ⬝ᵥ z := by
        simpa [row, dotProduct_comm] using
          (EuclideanSpace.inner_toLp_toLp (Lᵀ i) z.ofLp)
      _ = (Lᵀ *ᵥ z) i := by
        simp [Matrix.mulVec, dotProduct]
  have hmean_zero : μ[rowDual] = 0 := by
    -- The Gaussian is centered, so every continuous linear form also has mean zero.
    calc
      μ[rowDual] = rowDual (∫ z, z ∂ μ) := by
        rw [rowDual.integral_comp_id_comm ProbabilityTheory.IsGaussian.integrable_id]
      _ = 0 := by
        simp [μ, ProbabilityTheory.integral_id_multivariateGaussian]
  have hquadratic_nonneg :
      0 ≤ ((X : Mₙ).toQuadraticMap') (Lᵀ i) := by
    -- Positive semidefiniteness makes the row variance quadratic form nonnegative.
    simpa [Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply'] using hpsd.dotProduct_mulVec_nonneg (Lᵀ i)
  have hvariance :
      Var[rowDual; μ] = ((X : Mₙ).toQuadraticMap') (Lᵀ i) := by
    -- The covariance bilinear form evaluated on the row vector is exactly the textbook variance.
    calc
      Var[rowDual; μ] = ProbabilityTheory.covarianceBilin μ row row := by
        symm
        simpa [rowDual, InnerProductSpace.toDualMap_apply_apply] using
          (ProbabilityTheory.covarianceBilin_self
            (μ := μ) ProbabilityTheory.IsGaussian.memLp_two_id row)
      _ = row ⬝ᵥ (X : Mₙ) *ᵥ row := by
        rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hpsd]
      _ = ((X : Mₙ).toQuadraticMap') (Lᵀ i) := by
        simp [row, Matrix.toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply,
          Matrix.toLinearMap₂'_apply']
  have hmap :
      μ.map rowDual =
        ProbabilityTheory.gaussianReal 0
          ((((X : Mₙ).toQuadraticMap') (Lᵀ i)).toNNReal) := by
    -- Push the multivariate Gaussian through the row functional, then rewrite its mean/variance.
    rw [ProbabilityTheory.IsGaussian.map_eq_gaussianReal]
    simp [hmean_zero, hvariance]
  have habs_apply :
      (fun z : Eₙ ↦ |rowDual z|) = fun z : Eₙ ↦ |(Lᵀ *ᵥ z) i| := by
    ext z
    simp [hrow_apply]
  have hmapIntegral :
      ∫ x, |x| ∂ μ.map rowDual = ∫ z, |rowDual z| ∂ μ := by
    simpa using
      (MeasureTheory.integral_map
        (μ := μ) (φ := rowDual) (f := fun x : ℝ ↦ |x|)
        rowDual.continuous.aemeasurable
        (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x : ℝ ↦ |x|)))
  -- Transport the scalar Gaussian absolute-moment identity through the row pushforward law.
  calc
    ∫ z, |(Lᵀ *ᵥ z) i| ∂ ProbabilityTheory.multivariateGaussian 0 (X : Mₙ)
        = ∫ z, |rowDual z| ∂ μ := by
            simp [μ, habs_apply]
    _ = ∫ x, |x| ∂ μ.map rowDual := by
          rw [← hmapIntegral]
    _ = ∫ x, |x| ∂
          ProbabilityTheory.gaussianReal 0 ((((X : Mₙ).toQuadraticMap') (Lᵀ i)).toNNReal) := by
            rw [hmap]
    _ = Real.sqrt (2 / Real.pi) *
          Real.sqrt ↑((((X : Mₙ).toQuadraticMap') (Lᵀ i)).toNNReal) := by
            simpa using
              gaussianReal_absIntegral_eq_sqrtTwoDivPi_mul_sqrtVariance
                ((((X : Mₙ).toQuadraticMap') (Lᵀ i)).toNNReal)
    _ = Real.sqrt (2 / Real.pi) * Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
          simp [Real.toNNReal_of_nonneg hquadratic_nonneg]

/-- Helper for Proposition 7.33: summing the rowwise absolute Gaussian moments recovers the
factorization objective's square-root sum. -/
private theorem integral_sumAbs_transposeMulVec_multivariateGaussian
    (L : Mₙ) {X : 𝕊^n} (hX : X ∈ localFactorizationSemidefiniteFeasibleSet) :
    ∫ z, (∑ i : Fin n, |(Lᵀ *ᵥ z) i|) ∂ ProbabilityTheory.multivariateGaussian 0 (X : Mₙ) =
      Real.sqrt (2 / Real.pi) *
        ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
  let μ := ProbabilityTheory.multivariateGaussian 0 (X : Mₙ)
  have habs_integrable :
      ∀ i : Fin n, MeasureTheory.Integrable (fun z : Eₙ ↦ |(Lᵀ *ᵥ z) i|) μ := by
    intro i
    let row : Eₙ := WithLp.toLp 2 (Lᵀ i)
    let rowDual : StrongDual ℝ Eₙ := InnerProductSpace.toDualMap ℝ Eₙ row
    have hrow_apply :
        (fun z : Eₙ ↦ rowDual z) = fun z : Eₙ ↦ (Lᵀ *ᵥ z) i := by
      -- The row functional is just the `i`-th coordinate of `Lᵀ * z`.
      ext z
      calc
        rowDual z = inner ℝ row z := by
          rfl
        _ = (Lᵀ i) ⬝ᵥ z := by
          simpa [row, dotProduct_comm] using
            (EuclideanSpace.inner_toLp_toLp (Lᵀ i) z.ofLp)
        _ = (Lᵀ *ᵥ z) i := by
          simp [Matrix.mulVec, dotProduct]
    have hrow_integrable :
        MeasureTheory.Integrable (fun z : Eₙ ↦ rowDual z) μ :=
      ProbabilityTheory.IsGaussian.integrable_dual μ rowDual
    simpa [hrow_apply] using hrow_integrable.norm
  -- Integrate the finite sum termwise, then insert the rowwise Gaussian-moment formula.
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ∑ i : Fin n, ∫ z, |(Lᵀ *ᵥ z) i| ∂ μ
          = ∑ i : Fin n,
              (Real.sqrt (2 / Real.pi) * Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simpa [μ] using
                  integral_abs_transposeMulVec_eval_multivariateGaussian L hX i
      _ = Real.sqrt (2 / Real.pi) *
            ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
              rw [Finset.mul_sum]
  · intro i hi
    exact habs_integrable i

/-- Helper for Proposition 7.33: the Gaussian-sign rounding step is first proved pointwise on one
trace-one PSD matrix in the factorization relaxation. -/
private theorem
    two_div_pi_mul_localFactorizationObjective_le_booleanValue_of_feasible
    (L : Mₙ) {X : 𝕊^n}
    (hX : X ∈ localFactorizationSemidefiniteFeasibleSet) :
    (2 / Real.pi) * localFactorizationSemidefiniteObjective L X ≤
      booleanQuadraticOptimalValue (Lᵀ * L) := by
  let μ := ProbabilityTheory.multivariateGaussian 0 (X : Mₙ)
  let Y : Eₙ → ℝ := fun z ↦ ∑ i : Fin n, |(Lᵀ *ᵥ z) i|
  have hbool_nonneg : 0 ≤ booleanQuadraticOptimalValue (Lᵀ * L) :=
    booleanQuadraticOptimalValue_nonneg_of_gram L
  have hdot_integrable : MeasureTheory.Integrable (fun z : Eₙ ↦ z ⬝ᵥ z) μ := by
    -- The centered Gaussian with covariance `X` has finite second moment.
    have hid_memLp : MeasureTheory.MemLp (fun z : Eₙ ↦ z) 2 μ :=
      ProbabilityTheory.IsGaussian.memLp_two_id
    have hnorm_sq_integrable :
        MeasureTheory.Integrable (fun z : Eₙ ↦ ‖z‖ ^ (2 : ℕ)) μ := by
      simpa [pow_two] using hid_memLp.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
    refine hnorm_sq_integrable.congr ?_
    filter_upwards with z
    simpa [pow_two, dotProduct] using (EuclideanSpace.real_norm_sq_eq z)
  have hkernel_integrable :
      MeasureTheory.Integrable
        (fun z : Eₙ ↦ booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z)) μ := by
    -- The right-hand side of the deterministic kernel bound is integrable by the second moment.
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      hdot_integrable.const_mul (booleanQuadraticOptimalValue (Lᵀ * L))
  have hkernel_sq_integrable :
      MeasureTheory.Integrable (fun z : Eₙ ↦ Y z ^ (2 : ℕ)) μ := by
    -- The pointwise Boolean witness bound controls the Gaussian square moment of `Y`.
    refine MeasureTheory.Integrable.mono' hkernel_integrable (by fun_prop) ?_
    filter_upwards with z
    have hz_le := sumAbs_transposeMulVec_sq_le_booleanQuadraticOptimalValue_mul_dotProduct L z
    have hdot_nonneg : 0 ≤ z ⬝ᵥ z := by
      have hself : ‖z‖ ^ (2 : ℕ) = z.ofLp ⬝ᵥ z.ofLp := by
        simpa [dotProduct, pow_two] using EuclideanSpace.real_norm_sq_eq z
      nlinarith [sq_nonneg ‖z‖]
    have hz_rhs_nonneg :
        0 ≤ booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z) := by
      exact mul_nonneg hbool_nonneg hdot_nonneg
    have hy_sq_nonneg : 0 ≤ Y z ^ (2 : ℕ) := by
      positivity
    simpa [Y, Real.norm_of_nonneg hy_sq_nonneg,
      Real.norm_of_nonneg hz_rhs_nonneg] using hz_le
  have hY_memLp : MeasureTheory.MemLp Y 2 μ := by
    -- Square-integrability of `Y` is the exact hypothesis needed for the variance identity.
    refine (MeasureTheory.memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
    simpa [Y] using hkernel_sq_integrable
  have hmean_sq_le :
      (∫ z, Y z ∂ μ) ^ (2 : ℕ) ≤ ∫ z, Y z ^ (2 : ℕ) ∂ μ := by
    -- Variance is nonnegative, so `E[Y]^2 ≤ E[Y^2]` under the Gaussian probability measure.
    have hvar_nonneg : 0 ≤ Var[Y; μ] := by
      exact ProbabilityTheory.variance_nonneg _ _
    rw [ProbabilityTheory.variance_eq_sub hY_memLp] at hvar_nonneg
    exact sub_nonneg.mp hvar_nonneg
  have hkernel_integral_le :
      ∫ z, Y z ^ (2 : ℕ) ∂ μ ≤ booleanQuadraticOptimalValue (Lᵀ * L) := by
    -- Integrate the deterministic kernel bound and use `trace X = 1`.
    have hmono :=
      MeasureTheory.integral_mono_ae hkernel_sq_integrable hkernel_integrable
        (Filter.Eventually.of_forall fun z ↦
          sumAbs_transposeMulVec_sq_le_booleanQuadraticOptimalValue_mul_dotProduct L z)
    calc
      ∫ z, Y z ^ (2 : ℕ) ∂ μ
          ≤ ∫ z, booleanQuadraticOptimalValue (Lᵀ * L) * (z ⬝ᵥ z) ∂ μ := hmono
      _ = booleanQuadraticOptimalValue (Lᵀ * L) * Matrix.trace (X : Mₙ) := by
            rw [MeasureTheory.integral_const_mul]
            rw [integral_dotProduct_multivariateGaussian_eq_trace hX]
      _ = booleanQuadraticOptimalValue (Lᵀ * L) := by
            rw [trace_eq_one_of_mem_localFactorizationSemidefiniteFeasibleSet hX, mul_one]
  have hmoment :
      ∫ z, Y z ∂ μ =
        Real.sqrt (2 / Real.pi) *
          ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
    -- The Gaussian absolute moments of the row linear forms sum to the factorization square root.
    simpa [Y, μ] using integral_sumAbs_transposeMulVec_multivariateGaussian L hX
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i)) := by
    -- Every summand is a square root of a nonnegative quadratic form.
    exact Finset.sum_nonneg fun i _ ↦ Real.sqrt_nonneg _
  have hscaled_sq_le :
      (Real.sqrt (2 / Real.pi) *
          ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ) ≤
        booleanQuadraticOptimalValue (Lᵀ * L) := by
    -- Combine the expectation identity with the variance/Jensen control and the kernel integral.
    calc
      (Real.sqrt (2 / Real.pi) *
          ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)
          = (∫ z, Y z ∂ μ) ^ (2 : ℕ) := by rw [hmoment]
      _ ≤ ∫ z, Y z ^ (2 : ℕ) ∂ μ := hmean_sq_le
      _ ≤ booleanQuadraticOptimalValue (Lᵀ * L) := hkernel_integral_le
  -- Rewrite the squared Gaussian moment exactly as `(2 / π)` times the factorization objective.
  calc
    (2 / Real.pi) * localFactorizationSemidefiniteObjective L X
        = (Real.sqrt (2 / Real.pi) *
            ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ) := by
              rw [localFactorizationSemidefiniteObjective]
              calc
                (2 / Real.pi) *
                    (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ)
                    = (Real.sqrt (2 / Real.pi)) ^ (2 : ℕ) *
                        (∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ) := by
                            rw [Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)]
                _ = (Real.sqrt (2 / Real.pi) *
                      ∑ i : Fin n, Real.sqrt (((X : Mₙ).toQuadraticMap') (Lᵀ i))) ^ (2 : ℕ) := by
                      ring
    _ ≤ booleanQuadraticOptimalValue (Lᵀ * L) := hscaled_sq_le

/-- Helper for Proposition 7.33: once the pointwise Gaussian-sign kernel is available, the source
`sSup` packaging gives the factorization lower bound. -/
private theorem
    two_div_pi_mul_localFactorizationValue_le_booleanValue_of_factor
    (L : Mₙ) :
    (2 / Real.pi) * localFactorizationSemidefiniteRelaxationValue L ≤
      booleanQuadraticOptimalValue (Lᵀ * L) := by
  have htwo_pi_nonneg : 0 ≤ 2 / Real.pi := by
    positivity
  by_cases hfeas : Set.Nonempty
      (localFactorizationSemidefiniteFeasibleSet : Set 𝕊^n)
  · have hscaled_sSup :
        (2 / Real.pi) * localFactorizationSemidefiniteRelaxationValue L =
          sSup ((fun X : 𝕊^n ↦
            (2 / Real.pi) * localFactorizationSemidefiniteObjective L X) ''
              localFactorizationSemidefiniteFeasibleSet) := by
      rw [localFactorizationSemidefiniteRelaxationValue_eq_sSup]
      calc
        (2 / Real.pi) *
            sSup (localFactorizationSemidefiniteObjective L ''
              localFactorizationSemidefiniteFeasibleSet)
            =
              sSup ((2 / Real.pi : ℝ) •
                (localFactorizationSemidefiniteObjective L ''
                  localFactorizationSemidefiniteFeasibleSet)) := by
                simpa [smul_eq_mul] using
                  (Real.sSup_smul_of_nonneg htwo_pi_nonneg
                    (localFactorizationSemidefiniteObjective L ''
                      localFactorizationSemidefiniteFeasibleSet)).symm
        _ =
            sSup ((fun X : 𝕊^n ↦
              (2 / Real.pi) * localFactorizationSemidefiniteObjective L X) ''
                localFactorizationSemidefiniteFeasibleSet) := by
              congr 1
              ext z
              constructor
              · rintro ⟨w, hw, rfl⟩
                rcases hw with ⟨X, hX, rfl⟩
                exact ⟨X, hX, by simp⟩
              · rintro ⟨X, hX, rfl⟩
                refine ⟨localFactorizationSemidefiniteObjective L X, ?_, by simp⟩
                exact ⟨X, hX, rfl⟩
    rw [hscaled_sSup]
    refine csSup_le ?_ ?_
    · rcases hfeas with ⟨X, hX⟩
      exact ⟨(2 / Real.pi) * localFactorizationSemidefiniteObjective L X, ⟨X, hX, rfl⟩⟩
    · rintro _ ⟨X, hX, rfl⟩
      -- Reduce the `sSup` bound to the pointwise Gaussian-sign kernel.
      exact
        two_div_pi_mul_localFactorizationObjective_le_booleanValue_of_feasible
          L hX
  · have hfeas_empty :
        localFactorizationSemidefiniteFeasibleSet = (∅ : Set 𝕊^n) :=
      Set.not_nonempty_iff_eq_empty.mp hfeas
    -- If the trace-one feasible set is empty, the local factorization value is `0`, so only the
    -- nonnegativity of the Boolean Gram optimum remains.
    simpa [localFactorizationSemidefiniteRelaxationValue_eq_sSup, hfeas_empty] using
      booleanQuadraticOptimalValue_nonneg_of_gram L

/-- Helper for Proposition 7.33: in the strict positive-definite case, the lower bound follows
once `ψ⋆` is rewritten into the factorization relaxation and the Gaussian-sign package is applied.
-/
private theorem
    two_div_pi_mul_diagonalValue_le_booleanValue_of_posDef
    (A : 𝕊^n₊₊) :
    (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
      booleanQuadraticOptimalValue (((A : 𝕊^n) : Mₙ)) := by
  -- Rewrite `ψ⋆` to the factorization value and then consume the packaged pointwise kernel.
  rw [diagonalValue_eq_localFactorizationValue_of_posDef]
  have hfactor :
      (2 / Real.pi) * localFactorizationSemidefiniteRelaxationValue
          (CFC.sqrt (((A : 𝕊^n) : Mₙ))) ≤
        booleanQuadraticOptimalValue
          ((CFC.sqrt (((A : 𝕊^n) : Mₙ)))ᵀ * CFC.sqrt (((A : 𝕊^n) : Mₙ))) := by
    exact
      two_div_pi_mul_localFactorizationValue_le_booleanValue_of_factor
        (CFC.sqrt (((A : 𝕊^n) : Mₙ)))
  have hgram :
      (CFC.sqrt (((A : 𝕊^n) : Mₙ)))ᵀ * CFC.sqrt (((A : 𝕊^n) : Mₙ)) =
        ((A : 𝕊^n) : Mₙ) := by
    exact (sqrt_factorization_eq_of_posDef A).symm
  simpa [hgram] using hfactor

/-- Helper for Proposition 7.33: the strict positive-definite lower bound is lifted to the
positive-semidefinite theorem statement by the existing `ε I` shift lemmas. -/
private theorem two_div_pi_mul_diagonalValue_le_booleanValue_via_eps
    (A : 𝕊^n₊) :
    (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
      booleanQuadraticOptimalValue (A : Mₙ) := by
  -- Route correction: instead of waiting for an exact shift identity for `ψ⋆`, it is enough to
  -- compare `A` with the strict perturbation `A + t I`, apply the strict-PD theorem there, and
  -- then let `t` tend to `0`.
  suffices happrox :
      ∀ δ : ℝ, 0 < δ →
        (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
          booleanQuadraticOptimalValue (A : Mₙ) + δ by
    exact le_of_forall_pos_le_add happrox
  intro δ hδ
  let t : ℝ := δ / ((n : ℝ) + 1)
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have hApsd : (A : Mₙ).PosSemidef := by
    exact A.2
  have htI_posSemidef : (t • (1 : Mₙ)).PosSemidef := by
    simpa using (Matrix.PosDef.one : (1 : Mₙ).PosDef).posSemidef.smul ht.le
  have htI_nonneg : (0 : Mₙ) ≤ t • (1 : Mₙ) := by
    exact (Matrix.nonneg_iff_posSemidef).mpr htI_posSemidef
  have htI_posDef : (t • (1 : Mₙ)).PosDef := by
    simpa using (Matrix.PosDef.one : (1 : Mₙ).PosDef).smul ht
  have hshift_posDef : ((A : Mₙ) + t • (1 : Mₙ)).PosDef := by
    simpa [add_comm] using htI_posDef.add_posSemidef hApsd
  have hshift_mem :
      ((A : 𝕊^n) + scalarIdentitySymm t) ∈ 𝕊^n₊₊ := by
    -- The positive scalar shift moves every PSD matrix into the strict cone.
    simpa [scalarIdentitySymm] using mem_strictPositiveSemidefiniteCone_of_posDef hshift_posDef
  let AShift : 𝕊^n₊₊ := ⟨(A : 𝕊^n) + scalarIdentitySymm t, hshift_mem⟩
  have hstrict :
      (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue ((AShift : 𝕊^n₊₊) : 𝕊^n) ≤
        booleanQuadraticOptimalValue ((((AShift : 𝕊^n₊₊) : 𝕊^n) : Mₙ)) := by
    -- The strict-PD theorem is applied exactly at the regularized matrix.
    exact
      two_div_pi_mul_diagonalValue_le_booleanValue_of_posDef
        AShift
  have hpsi_mono :
      diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
        diagonalSemidefiniteRelaxationOptimalValue ((AShift : 𝕊^n₊₊) : 𝕊^n) := by
    -- Every diagonal majorant of `A + t I` is automatically a diagonal majorant of `A`.
    rw [diagonalSemidefiniteRelaxationOptimalValue_eq_sInf,
      diagonalSemidefiniteRelaxationOptimalValue_eq_sInf]
    refine le_csInf ?_ ?_
    · exact Set.Nonempty.image _
        (diagonalSemidefiniteRelaxationFeasibleSet_nonempty ((AShift : 𝕊^n₊₊) : 𝕊^n))
    · rintro _ ⟨y, hy, rfl⟩
      have hyA : y ∈ diagonalSemidefiniteRelaxationFeasibleSet (A : 𝕊^n) := by
        rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff] at hy ⊢
        have hA_le_shift :
            (A : Mₙ) ≤ ((((AShift : 𝕊^n₊₊) : 𝕊^n) : Mₙ)) := by
          rw [Matrix.le_iff]
          simpa [AShift, scalarIdentitySymm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using htI_posSemidef
        exact hA_le_shift.trans hy
      have hyA_image :
          (∑ i : Fin n, y i) ∈
            ((fun y' : Eₙ ↦ ∑ i : Fin n, y' i) '' diagonalSemidefiniteRelaxationFeasibleSet
              (A : 𝕊^n)) := by
        exact ⟨y, hyA, rfl⟩
      have hA_image_bddBelow :
          BddBelow
            (((fun y' : Eₙ ↦ ∑ i : Fin n, y' i) '' diagonalSemidefiniteRelaxationFeasibleSet
              (A : 𝕊^n)) : Set ℝ) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        rw [mem_diagonalSemidefiniteRelaxationFeasibleSet_iff] at hz
        have hz_nonneg : ∀ i : Fin n, 0 ≤ z i := by
          intro i
          have hslack :
              (Matrix.diagonal (fun j : Fin n ↦ z j) - (A : Mₙ)).PosSemidef := by
            exact (Matrix.nonneg_iff_posSemidef).mp (sub_nonneg.mpr hz)
          have hslack_diag : 0 ≤
              (Matrix.diagonal (fun j : Fin n ↦ z j) - (A : Mₙ)) i i := by
            simpa using hslack.diag_nonneg (i := i)
          have hA_diag : 0 ≤ (A : Mₙ) i i := by
            simpa using hApsd.diag_nonneg (i := i)
          have hz_shift : 0 ≤ z i - (A : Mₙ) i i := by
            simpa [Matrix.diagonal] using hslack_diag
          linarith
        exact Finset.sum_nonneg fun i _ ↦ hz_nonneg i
      exact csInf_le hA_image_bddBelow hyA_image
  have hAimage_bdd :
      BddAbove (((A : Mₙ).toQuadraticMap' '' signVectorSet (Fin n)) : Set ℝ) := by
    rcases diagonalSemidefiniteRelaxationFeasibleSet_nonempty (A : 𝕊^n) with ⟨y, hy⟩
    refine ⟨∑ i : Fin n, y i, ?_⟩
    rintro _ ⟨σ, hσ, rfl⟩
    exact quadratic_form_le_diagonal_majorant_sum_of_feasible (A : 𝕊^n) hy hσ
  have hbool_shift :
      booleanQuadraticOptimalValue ((((AShift : 𝕊^n₊₊) : 𝕊^n) : Mₙ)) ≤
        booleanQuadraticOptimalValue (A : Mₙ) + t * n := by
    -- The identity perturbation adds the constant `t * n` to every Boolean quadratic value.
    rw [booleanQuadraticOptimalValue_eq_sSup_image]
    refine csSup_le ?_ ?_
    · refine Set.Nonempty.image _ ?_
      refine ⟨fun _ : Fin n ↦ 1, ?_⟩
      rw [mem_signVectorSet_iff]
      intro i
      exact Or.inr rfl
    · rintro _ ⟨σ, hσ, rfl⟩
      have hσ_le :
          (A : Mₙ).toQuadraticMap' σ ≤ booleanQuadraticOptimalValue (A : Mₙ) := by
        rw [booleanQuadraticOptimalValue_eq_sSup_image]
        exact le_csSup hAimage_bdd ⟨σ, hσ, rfl⟩
      have hshift_quad :
          ((((AShift : 𝕊^n₊₊) : 𝕊^n) : Mₙ)).toQuadraticMap' σ =
            (A : Mₙ).toQuadraticMap' σ + t * n := by
        simpa [AShift, scalarIdentitySymm, add_comm, add_left_comm, add_assoc] using
          quadratic_form_add_scalar_identity_of_signVector (A := (A : Mₙ)) hσ t
      linarith
  have hscaled_mono :
      (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
        (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue
          ((AShift : 𝕊^n₊₊) : 𝕊^n) := by
    exact mul_le_mul_of_nonneg_left hpsi_mono (by positivity)
  have ht_bound : t * n ≤ δ := by
    have hden : 0 < ((n : ℝ) + 1) := by
      positivity
    have hratio :
        ((n : ℝ) / ((n : ℝ) + 1)) ≤ 1 := by
      exact (_root_.div_le_iff₀ hden).2 (by nlinarith)
    calc
      t * n = δ * ((n : ℝ) / ((n : ℝ) + 1)) := by
        dsimp [t]
        field_simp [hden.ne']
      _ ≤ δ * 1 := by
        exact mul_le_mul_of_nonneg_left hratio hδ.le
      _ = δ := by
        ring
  calc
    (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n)
        ≤ (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue
            ((AShift : 𝕊^n₊₊) : 𝕊^n) := hscaled_mono
    _ ≤ booleanQuadraticOptimalValue ((((AShift : 𝕊^n₊₊) : 𝕊^n) : Mₙ)) := hstrict
    _ ≤ booleanQuadraticOptimalValue (A : Mₙ) + t * n := hbool_shift
    _ ≤ booleanQuadraticOptimalValue (A : Mₙ) + δ := by
      linarith

-- Proof sketch: the upper bound comes from sending a sign vector `x ∈ {±1}ⁿ` to the feasible
-- rank-one symmetric matrix `x xᵀ`. The lower bound depends only on the intrinsic symmetric
-- positive-semidefinite coefficient matrix, so the source-facing proposition is stated directly
-- on the Chapter 7 relaxation owner `diagonalSemidefiniteRelaxationOptimalValue`.
/-- Proposition 7.33: for a positive-semidefinite symmetric matrix `A`, the Boolean quadratic
optimum `f⋆` from Definition 7.70 and the chapter semidefinite-relaxation value `ψ⋆` from
Definition 7.71 satisfy `(2 / π) ψ⋆ ≤ f⋆ ≤ ψ⋆`. -/
theorem booleanQuadraticOptimalValue_two_div_pi_mul_diagonalSemidefiniteRelaxation_le_and_le
    (A : 𝕊^n₊) :
    (2 / Real.pi) * diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) ≤
        booleanQuadraticOptimalValue (A : Mₙ) ∧
      booleanQuadraticOptimalValue (A : Mₙ) ≤
        diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n) := by
  constructor
  · -- The lower bound is now reduced to the single epsilon-regularization adapter.
    exact two_div_pi_mul_diagonalValue_le_booleanValue_via_eps A
  · -- The upper bound is the weak-duality comparison proved above.
    exact booleanQuadraticOptimalValue_le_diagonalSemidefiniteRelaxationOptimalValue (A : 𝕊^n)

end
