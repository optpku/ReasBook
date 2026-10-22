/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LpApproximationBoxProblem
open LpApproximationEpigraphPoint
open scoped BigOperators Gradient RealInnerProductSpace LpBarrierNewtonSystem

variable {n m : ℕ}

/-- The Euclidean coordinate index for the private ambient bridge used to evaluate the Chapter 5
barrier gradient and Hessian. -/
private abbrev LpBarrierOracleAmbientIndex (n m : ℕ) :=
  Fin n ⊕ Option (Fin m)

/-- The Euclidean carrier for the private ambient bridge behind the public oracle on
`LpApproximationEpigraphPoint n m`. -/
private abbrev LpBarrierOracleAmbientPoint (n m : ℕ) :=
  EuclideanSpace ℝ (LpBarrierOracleAmbientIndex n m)

/-- Convert the chapter's canonical lifted decision point to the private Euclidean ambient bridge
used internally by `gradient` and `hessian`. -/
private def toLpBarrierOracleAmbientPoint
    (decision : LpApproximationEpigraphPoint n m) :
    LpBarrierOracleAmbientPoint n m :=
  (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).symm fun i ↦
    match i with
    | Sum.inl j => decision.point j
    | Sum.inr none => decision.objectiveSlack
    | Sum.inr (some j) => decision.residualSlack j

/-- Convert the private Euclidean ambient bridge point back to the chapter's canonical lifted
decision carrier. -/
private def ofLpBarrierOracleAmbientPoint
    (decision : LpBarrierOracleAmbientPoint n m) :
    LpApproximationEpigraphPoint n m :=
  let coords := EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ decision
  ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦ coords (Sum.inl i),
    coords (Sum.inr none),
    fun i ↦ coords (Sum.inr (some i)))

private def lpBarrierOracleAmbientLinearEquiv (n m : ℕ) :
    LpApproximationEpigraphPoint n m ≃ₗ[ℝ] LpBarrierOracleAmbientPoint n m where
  toFun := toLpBarrierOracleAmbientPoint
  invFun := ofLpBarrierOracleAmbientPoint
  map_add' x y := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j with
        | none =>
            rfl
        | some j =>
            rfl
  map_smul' c x := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j with
        | none =>
            rfl
        | some j =>
            rfl
  left_inv x := by
    ext
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    · simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
  right_inv x := by
    apply (EuclideanSpace.equiv (LpBarrierOracleAmbientIndex n m) ℝ).injective
    ext i
    cases i with
    | inl j =>
        simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
    | inr j =>
        cases j <;> simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]

private abbrev lpBarrierOracleAmbientEquiv (n m : ℕ) :
    LpApproximationEpigraphPoint n m ≃L[ℝ] LpBarrierOracleAmbientPoint n m :=
  (lpBarrierOracleAmbientLinearEquiv n m).toContinuousLinearEquiv

/-- Helper for Theorem 5.4.9.2: the inverse ambient bridge as a continuous linear map back to the
canonical lifted decision carrier. -/
private abbrev ambientLiftedCLM (n m : ℕ) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] LpApproximationEpigraphPoint n m :=
  (lpBarrierOracleAmbientEquiv n m).symm.toContinuousLinearMap

/-- Helper for Theorem 5.4.9.2: the point projection transported through the ambient Euclidean
bridge. -/
private abbrev ambientPointCLM (n m : ℕ) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (ℝ × (Fin m → ℝ))).comp
    (ambientLiftedCLM n m)

/-- Helper for Theorem 5.4.9.2: the slack-pair projection transported through the ambient
Euclidean bridge. -/
private abbrev ambientSlackPairCLM (n m : ℕ) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] (ℝ × (Fin m → ℝ)) :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (ℝ × (Fin m → ℝ))).comp
    (ambientLiftedCLM n m)

/-- Helper for Theorem 5.4.9.2: the objective-slack projection transported through the ambient
Euclidean bridge. -/
private abbrev ambientObjectiveSlackCLM (n m : ℕ) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ (Fin m → ℝ)).comp (ambientSlackPairCLM n m)

/-- Helper for Theorem 5.4.9.2: the residual-slack vector projection transported through the
ambient Euclidean bridge. -/
private abbrev ambientResidualVectorCLM (n m : ℕ) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] (Fin m → ℝ) :=
  (ContinuousLinearMap.snd ℝ ℝ (Fin m → ℝ)).comp (ambientSlackPairCLM n m)

/-- Helper for Theorem 5.4.9.2: the `i`-th residual-slack projection transported through the
ambient Euclidean bridge. -/
private abbrev ambientResidualSlackCLM (n m : ℕ) (i : Fin m) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ambientResidualVectorCLM n m)

/-- Helper for Theorem 5.4.9.2: the `j`-th point-coordinate projection transported through the
ambient Euclidean bridge. -/
private abbrev ambientPointCoordinateCLM (n m : ℕ) (j : Fin n) :
    LpBarrierOracleAmbientPoint n m →L[ℝ] ℝ :=
  (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin n ↦ ℝ) j).comp
    (ambientPointCLM n m)

@[simp] private theorem ambientLiftedCLM_apply
    (n m : ℕ) (z : LpBarrierOracleAmbientPoint n m) :
    ambientLiftedCLM n m z = ofLpBarrierOracleAmbientPoint z :=
  rfl

@[simp] private theorem ambientPointCLM_apply
    (n m : ℕ) (z : LpBarrierOracleAmbientPoint n m) :
    ambientPointCLM n m z = (ofLpBarrierOracleAmbientPoint z).point :=
  rfl

@[simp] private theorem ambientSlackPairCLM_apply
    (n m : ℕ) (z : LpBarrierOracleAmbientPoint n m) :
    ambientSlackPairCLM n m z =
      ((ofLpBarrierOracleAmbientPoint z).objectiveSlack,
        (ofLpBarrierOracleAmbientPoint z).residualSlack) :=
  rfl

@[simp] private theorem ambientObjectiveSlackCLM_apply
    (n m : ℕ) (z : LpBarrierOracleAmbientPoint n m) :
    ambientObjectiveSlackCLM n m z = (ofLpBarrierOracleAmbientPoint z).objectiveSlack :=
  rfl

@[simp] private theorem ambientResidualVectorCLM_apply
    (n m : ℕ) (z : LpBarrierOracleAmbientPoint n m) :
    ambientResidualVectorCLM n m z = (ofLpBarrierOracleAmbientPoint z).residualSlack :=
  rfl

@[simp] private theorem ambientResidualSlackCLM_apply
    (n m : ℕ) (i : Fin m) (z : LpBarrierOracleAmbientPoint n m) :
    ambientResidualSlackCLM n m i z = (ofLpBarrierOracleAmbientPoint z).residualSlack i :=
  rfl

@[simp] private theorem ambientPointCoordinateCLM_apply
    (n m : ℕ) (j : Fin n) (z : LpBarrierOracleAmbientPoint n m) :
    ambientPointCoordinateCLM n m j z = (ofLpBarrierOracleAmbientPoint z).point j :=
  by
    simp [ambientPointCoordinateCLM, lpBarrierOracleAmbientLinearEquiv,
      ofLpBarrierOracleAmbientPoint]

/-- Helper for Theorem 5.4.9.2: the Riesz functional of an ambient bridge vector expands as the
sum of its point, objective-slack, and residual-slack coordinate projections. -/
private theorem innerSL_toLpBarrierOracleAmbientPoint_eq_sum
    (point : EuclideanSpace ℝ (Fin n))
    (objectiveSlack : ℝ)
    (residualSlack : Fin m → ℝ) :
    innerSL ℝ (toLpBarrierOracleAmbientPoint (point, objectiveSlack, residualSlack)) =
      (∑ j : Fin n, point j • ambientPointCoordinateCLM n m j) +
        objectiveSlack • ambientObjectiveSlackCLM n m +
        ∑ i : Fin m, residualSlack i • ambientResidualSlackCLM n m i := by
  ext z
  -- Proof comment: evaluate both linear forms on an arbitrary ambient tangent vector and read the
  -- Euclidean inner product as the sum of point, objective, and residual coordinates.
  rw [innerSL_apply_apply, PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_option]
  -- Proof comment: after expanding the ambient bridge, the remaining scalar inner products live
  -- in `ℝ`, so we rewrite them through `real_inner_eq_re_inner` and `RCLike.inner_apply` before
  -- the final ring normalization.
  simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp_rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp [lpBarrierOracleAmbientLinearEquiv, ofLpBarrierOracleAmbientPoint, mul_comm, add_assoc,
    add_left_comm, add_comm]
  -- Proof comment: the point and residual scalar products only differ by commuting factors inside
  -- their finite sums, so record those two finite-sum identities and then normalize the outer
  -- addition.
  have hpoint :
      ∑ x, z.ofLp (Sum.inl x) * point.ofLp x =
        ∑ x, point.ofLp x * z.ofLp (Sum.inl x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [mul_comm]
  have hresidual :
      ∑ x, z.ofLp (Sum.inr (some x)) * residualSlack x =
        ∑ x, residualSlack x * z.ofLp (Sum.inr (some x)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [mul_comm]
  have hobjective :
      z.ofLp (Sum.inr none) * objectiveSlack =
        objectiveSlack *
          LpApproximationEpigraphPoint.objectiveSlack
            (WithLp.toLp 2 fun i ↦ z.ofLp (Sum.inl i), z.ofLp (Sum.inr none),
              fun i ↦ z.ofLp (Sum.inr (some i))) := by
    simp [mul_comm]
  simpa [hpoint, hresidual, hobjective, add_assoc, add_left_comm, add_comm]

/-- The canonical output type of the actual second-order oracle for the Chapter 5 barrier
`problem.barrierModelBarrier`: the barrier gradient together with the Hessian operator on the
canonical lifted decision carrier `LpApproximationEpigraphPoint n m`. -/
abbrev LpBarrierSecondOrderOracleOutput (n m : ℕ) :=
  LpApproximationEpigraphPoint n m ×
    (LpApproximationEpigraphPoint n m →L[ℝ] LpApproximationEpigraphPoint n m)

/-- A primitive evaluator for the Chapter 5 barrier second-order oracle across all box-constrained
`ℓ_p` approximation instances. -/
abbrev LpBarrierSecondOrderOracleEvaluator :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m),
    problem.StrictBarrierModelPoint → LpBarrierSecondOrderOracleOutput n m

/-- A primitive arithmetic-work model for evaluating the Chapter 5 barrier second-order oracle. -/
abbrev LpBarrierSecondOrderOracleWork :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m),
    problem.StrictBarrierModelPoint → ℕ

/-- The dense-model work bound for one second-order oracle call to the actual barrier
`problem.barrierModelBarrier`, written in terms of primitive per-index arithmetic costs for the
source-facing block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂`. -/
def barrierSecondOrderOracleDenseArithmeticWorkBound
    (m n : ℕ)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : ℕ :=
  m * (g1Work m n + n) +
    (m * g2Work m n + n) +
    (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n))

/-- Expanding `barrierSecondOrderOracleDenseArithmeticWorkBound m n g1Work g2Work h11Work h12Work
h22Work` recovers the dense-model arithmetic template for one second-order oracle call to the
barrier `problem.barrierModelBarrier`, expressed in terms of the primitive per-index block costs.
-/
theorem barrierSecondOrderOracleDenseArithmeticWorkBound_eq
    (m n : ℕ)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) :
    barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work =
      m * (g1Work m n + n) +
        (m * g2Work m n + n) +
        (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n)) :=
  rfl

/- Theorem 5.4.9.2 lies in the Chapter 5 box-constrained `ℓ_p` approximation / barrier-oracle
arithmetic-complexity domain.

Sampled owner declarations:
* `problem.barrierModelBarrier` and `problem.StrictBarrierModelPoint` in `Definition_5_4_9_5`,
  the chapter owners for the actual logarithmic barrier `F(x, ξ, τ)` and its strict barrier
  domain;
* `auxiliaryGradient` and `auxiliaryTimeDerivative` in `Definition_5_4_9_7`, the source-facing
  first-order block owners `g₁` and `g₂`;
* `secondOrderDerivativeBlock11`, `secondOrderDerivativeBlock12`, and
  `secondOrderDerivativeBlock22` in `Definition_5_4_9_8`, the source-facing second-order block
  owners `h₁₁`, `h₁₂`, and `h₂₂`;
* `κ[decision]`, `Λ₀[decision]`, `Λ₁[decision]`, `Λ₂[decision]`, and `D[decision]` in
  `Definition_5_4_9_9`, the chapter owners for the Hessian blocks of the actual barrier.

Best owner abstraction:
* source-facing: `decision.barrierSecondOrderOracleGradient` and `problem.barrierSecondOrderOracle`,
  the actual gradient/Hessian oracle for the barrier `problem.barrierModelBarrier`;
* core/canonical: the strict-domain owner `problem.StrictBarrierModelPoint` together with the
  existing Chapter 5 block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, `h₂₂`, `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`,
  `A`, and the canonical oracle predicate `HasSecondOrderOracleAt`;
* bridge/view: the Euclidean ambient formula `problem.barrierModelBarrierAmbient`, the dense block
  decomposition `problem.barrierSecondOrderOracleDenseBlocks`, and the dense-assembly work bound
  relating an arbitrary arithmetic-work model to that actual oracle.

Primitive data:
* the primitive per-index cost functions for evaluating `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂`.

Derived API:
* `decision.barrierSecondOrderOracleGradient`;
* `problem.barrierSecondOrderOracle`;
* `problem.barrierSecondOrderOracleDenseBlocks`;
* `EvaluatesLpBarrierSecondOrderOracle`;
* `LpBarrierSecondOrderOracleDenseAssemblyBound`;
* `HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound`;
* `hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound`;
* the theorem `barrierSecondOrderOracleDenseArithmeticComplexity_bound`.

This refinement keeps the asymptotic arithmetic statement `O(m n^2)`, but moves the public
source-facing layer onto the actual barrier oracle instead of leaving the file centered on five
ad hoc work functions and a point-ignored synthetic family. The concrete oracle now exposes the
actual gradient/Hessian data of `problem.barrierModelBarrier` at a strict point, while the dense
block decomposition and the abstract comparison from an arbitrary implementation to that oracle
remain only as bridges. -/

namespace LpApproximationBoxProblem

/-- The private ambient bridge formula whose restriction to the strict barrier domain is
`problem.barrierModelBarrier`. The public oracle stays on `LpApproximationEpigraphPoint n m`,
while this Euclidean realization is used internally for `gradient` and `hessian`. -/
private def barrierModelBarrierAmbient
    (problem : LpApproximationBoxProblem n m) :
    LpBarrierOracleAmbientPoint n m → ℝ :=
  fun decision ↦
    let lifted := ofLpBarrierOracleAmbientPoint decision
    (∑ i : Fin m,
      separableLogBarrierF4 (problem.p : ℝ)
        (⟪problem.a i, lifted.point⟫ - problem.b i, lifted.residualSlack i)) -
      Real.log (lifted.objectiveSlack - ∑ i : Fin m, lifted.residualSlack i) -
      ∑ j : Fin n,
        (Real.log (lifted.point j - problem.α j) +
          Real.log (problem.β j - lifted.point j))

/-- Evaluating `problem.barrierModelBarrierAmbient` gives the textbook ambient barrier formula in
the lifted coordinates `(x, ξ, τ)`. -/
@[simp] private theorem barrierModelBarrierAmbient_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : LpBarrierOracleAmbientPoint n m) :
    problem.barrierModelBarrierAmbient decision =
      let lifted := ofLpBarrierOracleAmbientPoint decision
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, lifted.point⟫ - problem.b i, lifted.residualSlack i)) -
        Real.log (lifted.objectiveSlack - ∑ i : Fin m, lifted.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (lifted.point j - problem.α j) +
            Real.log (problem.β j - lifted.point j)) :=
  rfl

/-- Restricting the ambient bridge formula `problem.barrierModelBarrierAmbient` to the strict
domain recovers the actual barrier owner `problem.barrierModelBarrier`. -/
private theorem barrierModelBarrier_eq_barrierModelBarrierAmbient
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierModelBarrier decision =
      problem.barrierModelBarrierAmbient (toLpBarrierOracleAmbientPoint decision.1) := by
  -- Proof comment: both owners expand to the same textbook formula once the ambient coordinates
  -- are pulled back through the round-trip `of ∘ to`.
  rw [problem.barrierModelBarrier_apply, problem.barrierModelBarrierAmbient_apply]
  simp [toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]

/-- Helper for Theorem 5.4.9.2: strict barrier-domain membership gives a positive coupling gap
`ξ - ∑ i, τ⁽ⁱ⁾`. -/
theorem strictBarrierGap_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    0 < decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i := by
  -- Proof comment: the middle conjunct of the strict-domain characterization is exactly the
  -- coupling-gap inequality.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨_, hgap, _⟩
  exact sub_pos.mpr hgap

/-- Helper for Theorem 5.4.9.2: strict barrier-domain membership gives positive residual slacks.
-/
private theorem strictBarrierResidualSlack_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    0 < decision.1.residualSlack i := by
  -- Proof comment: the first conjunct of the strict-domain characterization records the
  -- positivity of every residual slack.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨hresidual, _, _⟩
  exact (hresidual i).1

/-- Helper for Theorem 5.4.9.2: strict barrier-domain membership gives the strict box bounds on
the primal point. -/
private theorem strictBarrierPoint_mem_box
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (j : Fin n) :
    problem.α j < decision.1.point j ∧ decision.1.point j < problem.β j := by
  -- Proof comment: the box inequalities are the last conjunct of the strict-domain
  -- characterization.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨_, _, hbox⟩
  exact hbox j

/-- Helper for Theorem 5.4.9.2: each strict residual block has positive gap
`τᵢ^(2 / p) - sᵢ^2`. -/
private theorem strictBarrierResidualGap_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    0 <
      Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
        (decision.newtonSystemResidual i) ^ (2 : ℕ) := by
  -- Proof comment: this is the strict residual inequality from the barrier-domain
  -- characterization rewritten as a positive gap.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨hresidual, _, _⟩
  exact sub_pos.mpr (hresidual i).2

/-- Helper for Theorem 5.4.9.2: the Chapter 5 constraint matrix acts on a coefficient vector by
the expected sum of column scalings. -/
private theorem newtonSystemConstraintMatrix_toEuclideanLin_eq_sum_smul
    (problem : LpApproximationBoxProblem n m)
    (w : EuclideanSpace ℝ (Fin m)) :
    (A[problem]).toEuclideanLin w = ∑ i : Fin m, (w i) • problem.a i := by
  -- Proof comment: compare the two vectors coordinatewise; both sides have the same `j`-th entry
  -- `∑ i, problem.a i j * w i`.
  ext j
  rw [Matrix.toLpLin_apply]
  simp [LpApproximationBoxProblem.newtonSystemConstraintMatrix, Matrix.mulVec, dotProduct,
    mul_comm]

/-- Helper for Theorem 5.4.9.2: differentiating `-log ∘ σ` at a positive value produces the
usual quotient formula. -/
private theorem negLogCompDerivAt
    {σ : ℝ → ℝ} {x value sigma' : ℝ}
    (hσ : HasDerivAt σ sigma' x)
    (hvalue : σ x = value)
    (hpos : 0 < value) :
    deriv (fun a : ℝ ↦ -Real.log (σ a)) x = -sigma' / value := by
  -- Proof comment: compose the derivative of `-log` at the positive base value with the scalar
  -- derivative of `σ`, then rewrite the product as a quotient.
  have hlog :
      HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(value⁻¹)) value := by
    simpa using (Real.hasDerivAt_log hpos.ne').neg
  have hlog' :
      HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(value⁻¹)) (σ x) := by
    simpa [hvalue] using hlog
  have hcomp :
      HasDerivAt (fun a : ℝ ↦ -Real.log (σ a)) (-(value⁻¹) * sigma') x := by
    simpa [Function.comp, hvalue] using hlog'.comp x hσ
  calc
    deriv (fun a : ℝ ↦ -Real.log (σ a)) x = -(value⁻¹) * sigma' := hcomp.deriv
    _ = -sigma' / value := by field_simp [hpos.ne']

/-- Helper for Theorem 5.4.9.2: the residual-slack pair of a strict barrier-model point has the
explicit frozen-`τᵢ` scalar gradient formula for `F₄`. -/
private theorem residualBlock_auxiliaryGradient_formula
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    auxiliaryGradient (separableLogBarrierF4 problem.p)
        (decision.newtonSystemResidual i) (decision.1.residualSlack i) =
      2 * decision.newtonSystemResidual i /
        (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
          (decision.newtonSystemResidual i) ^ (2 : ℕ)) := by
  -- Proof comment: differentiate the frozen residual block directly at the strict point, using
  -- the strict barrier gap to justify the logarithmic chain rule.
  have hgap := strictBarrierResidualGap_pos problem decision i
  have hσ :
      HasDerivAt
        (fun y : ℝ ↦
          Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) - y ^ (2 : ℕ))
        (-(2 * decision.newtonSystemResidual i))
        (decision.newtonSystemResidual i) := by
    simpa [two_mul] using
      (hasDerivAt_pow 2 (decision.newtonSystemResidual i)).const_sub
        (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)))
  rw [auxiliaryGradient, gradient_eq_deriv']
  calc
    deriv
        (fun y : ℝ ↦
          separableLogBarrierF4 problem.p (y, decision.1.residualSlack i))
        (decision.newtonSystemResidual i)
        =
      deriv
        (fun y : ℝ ↦
          -Real.log (decision.1.residualSlack i) +
            -Real.log
              (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) - y ^ (2 : ℕ)))
        (decision.newtonSystemResidual i) := by
          simp [separableLogBarrierF4_apply, sub_eq_add_neg]
    _ =
      deriv
        (fun y : ℝ ↦
          -Real.log
            (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) - y ^ (2 : ℕ)))
        (decision.newtonSystemResidual i) := by
          rw [deriv_const_add]
    _ =
      -(-(2 * decision.newtonSystemResidual i)) /
        (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
          (decision.newtonSystemResidual i) ^ (2 : ℕ)) := by
          exact
            negLogCompDerivAt
              (σ := fun y : ℝ ↦
                Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
                  y ^ (2 : ℕ))
              (x := decision.newtonSystemResidual i)
              (value :=
                Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
                  (decision.newtonSystemResidual i) ^ (2 : ℕ))
              (sigma' := -(2 * decision.newtonSystemResidual i))
              hσ
              rfl
              hgap
    _ =
      2 * decision.newtonSystemResidual i /
        (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
          (decision.newtonSystemResidual i) ^ (2 : ℕ)) := by
          ring

/-- Helper for Theorem 5.4.9.2: the residual-slack pair of a strict barrier-model point has the
explicit frozen-`sᵢ` time-derivative formula for `F₄`. -/
private theorem residualBlock_auxiliaryTimeDerivative_formula
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
        (decision.newtonSystemResidual i) (decision.1.residualSlack i) =
      -(1 / decision.1.residualSlack i) -
        ((2 / (problem.p : ℝ)) *
            Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ) - 1)) /
          (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
            (decision.newtonSystemResidual i) ^ (2 : ℕ)) := by
  -- Proof comment: the strict residual slack positivity and strict barrier gap keep both
  -- logarithmic arguments positive, so the frozen-`sᵢ` time derivative is the direct scalar
  -- chain-rule computation.
  have hτ := strictBarrierResidualSlack_pos problem decision i
  have hgap := strictBarrierResidualGap_pos problem decision i
  have hσ :
      HasDerivAt
        (fun t' : ℝ ↦
          Real.rpow t' (2 / (problem.p : ℝ)) - (decision.newtonSystemResidual i) ^ (2 : ℕ))
        ((2 / (problem.p : ℝ)) *
          Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ) - 1))
        (decision.1.residualSlack i) := by
    simpa using
      ((Real.hasDerivAt_rpow_const
          (x := decision.1.residualSlack i)
          (p := 2 / (problem.p : ℝ))
          (Or.inl hτ.ne')).sub_const ((decision.newtonSystemResidual i) ^ (2 : ℕ)))
  have hlogτ' :
      HasDerivAt (fun t' : ℝ ↦ -Real.log t')
        (-(1 / decision.1.residualSlack i))
        (decision.1.residualSlack i) := by
    simpa [one_div] using (Real.hasDerivAt_log hτ.ne').neg
  have hlogGap' :
      HasDerivAt
        (fun t' : ℝ ↦
          -Real.log
            (Real.rpow t' (2 / (problem.p : ℝ)) - (decision.newtonSystemResidual i) ^ (2 : ℕ)))
        (-((2 / (problem.p : ℝ)) *
            Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ) - 1)) /
          (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
            (decision.newtonSystemResidual i) ^ (2 : ℕ)))
        (decision.1.residualSlack i) := by
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      ((Real.hasDerivAt_log hgap.ne').neg.comp (decision.1.residualSlack i) hσ)
  rw [auxiliaryTimeDerivative]
  calc
    deriv
        (fun t' : ℝ ↦
          separableLogBarrierF4 problem.p (decision.newtonSystemResidual i, t'))
        (decision.1.residualSlack i)
        = deriv
            (fun t' : ℝ ↦
              -Real.log t' +
                -Real.log
                  (Real.rpow t' (2 / (problem.p : ℝ)) -
                    (decision.newtonSystemResidual i) ^ (2 : ℕ)))
            (decision.1.residualSlack i) := by
              simp [separableLogBarrierF4_apply, sub_eq_add_neg]
    _ = -(1 / decision.1.residualSlack i) +
          (-((2 / (problem.p : ℝ)) *
              Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ) - 1)) /
            (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
              (decision.newtonSystemResidual i) ^ (2 : ℕ))) := by
          exact (hlogτ'.add hlogGap').deriv
    _ = -(1 / decision.1.residualSlack i) -
          ((2 / (problem.p : ℝ)) *
              Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ) - 1)) /
            (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
              (decision.newtonSystemResidual i) ^ (2 : ℕ)) := by
          ring

/-- Helper for Theorem 5.4.9.2: on the strict logarithmic domain, the scalar barrier `F₄` has
the explicit product-space Fréchet derivative obtained by differentiating its two logarithmic
summands. -/
private theorem separableLogBarrierF4_hasFDerivAt
    {p s τ : ℝ}
    (hτ : 0 < τ)
    (hgap : 0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ)) :
    HasFDerivAt (separableLogBarrierF4 p)
      ((2 * s / (Real.rpow τ (2 / p) - s ^ (2 : ℕ))) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (-(1 / τ) -
            ((2 / p) * Real.rpow τ (2 / p - 1)) /
              (Real.rpow τ (2 / p) - s ^ (2 : ℕ))) •
          ContinuousLinearMap.snd ℝ ℝ ℝ)
      (s, τ) := by
  let gap : ℝ := Real.rpow τ (2 / p) - s ^ (2 : ℕ)
  let gradS : ℝ := 2 * s / gap
  let gradT : ℝ := -(1 / τ) - ((2 / p) * Real.rpow τ (2 / p - 1)) / gap
  have hfst :
      HasFDerivAt (fun z : ℝ × ℝ ↦ z.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (s, τ) := by
    -- Proof comment: the first coordinate is a fixed continuous linear projection.
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have hsnd :
      HasFDerivAt (fun z : ℝ × ℝ ↦ z.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (s, τ) := by
    -- Proof comment: the second coordinate is the companion continuous linear projection.
    simpa using (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  have hsq :
      HasFDerivAt
        (fun z : ℝ × ℝ ↦ z.1 ^ (2 : ℕ))
        (((2 : ℝ) * s) • ContinuousLinearMap.fst ℝ ℝ ℝ)
        (s, τ) := by
    -- Proof comment: the square term only depends on the first coordinate, so the chain rule
    -- attaches the scalar derivative `2s` to `fst`.
    simpa using
      ((hasDerivAt_pow 2 s).comp_hasFDerivAt (s, τ) hfst)
  have hrpow :
      HasFDerivAt
        (fun z : ℝ × ℝ ↦ Real.rpow z.2 (2 / p))
        (((2 / p) * Real.rpow τ (2 / p - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (s, τ) := by
    -- Proof comment: the `rpow` block only sees the second coordinate, so its derivative is the
    -- scalar `rpow` derivative times `snd`.
    simpa using
      ((Real.hasDerivAt_rpow_const (x := τ) (p := 2 / p) (Or.inl hτ.ne')).comp_hasFDerivAt
        (s, τ) hsnd)
  have hgapDeriv :
      HasFDerivAt
        (fun z : ℝ × ℝ ↦ Real.rpow z.2 (2 / p) - z.1 ^ (2 : ℕ))
        ((((2 / p) * Real.rpow τ (2 / p - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
          (((2 : ℝ) * s) • ContinuousLinearMap.fst ℝ ℝ ℝ))
        (s, τ) := by
    -- Proof comment: subtract the square derivative from the `rpow` derivative before entering
    -- the outer logarithm.
    simpa [sub_eq_add_neg, gap] using hrpow.sub hsq
  have hlogτ :
      HasFDerivAt
        (fun z : ℝ × ℝ ↦ -Real.log z.2)
        (-(1 / τ) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (s, τ) := by
    -- Proof comment: compose the derivative of `-log` at the positive slack `τ` with `snd`.
    simpa [one_div] using
      ((Real.hasDerivAt_log hτ.ne').neg.comp_hasFDerivAt (s, τ) hsnd)
  have hgapLogBase :
      HasDerivAt (fun y : ℝ ↦ -Real.log y) (-(gap⁻¹)) gap := by
    -- Proof comment: the strict residual gap keeps the logarithm on its smooth positive branch.
    simpa [gap] using (Real.hasDerivAt_log hgap.ne').neg
  have hlogGap :
      HasFDerivAt
        (fun z : ℝ × ℝ ↦ -Real.log (Real.rpow z.2 (2 / p) - z.1 ^ (2 : ℕ)))
        ((-(gap⁻¹)) •
          ((((2 / p) * Real.rpow τ (2 / p - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
            (((2 : ℝ) * s) • ContinuousLinearMap.fst ℝ ℝ ℝ)))
        (s, τ) := by
    -- Proof comment: compose the positive-gap logarithm derivative with the gap derivative map.
    simpa [gap, sub_eq_add_neg] using hgapLogBase.comp_hasFDerivAt (s, τ) hgapDeriv
  have hsum :
      HasFDerivAt
        (separableLogBarrierF4 p)
        (-(1 / τ) • ContinuousLinearMap.snd ℝ ℝ ℝ +
          (-(gap⁻¹)) •
            ((((2 / p) * Real.rpow τ (2 / p - 1)) • ContinuousLinearMap.snd ℝ ℝ ℝ) -
              (((2 : ℝ) * s) • ContinuousLinearMap.fst ℝ ℝ ℝ)))
        (s, τ) := by
    -- Proof comment: after expanding `F₄`, the two logarithmic branches differentiate
    -- independently and add.
    convert hlogτ.add hlogGap using 1
    funext z
    rcases z with ⟨z1, z2⟩
    simp [separableLogBarrierF4_apply, sub_eq_add_neg]
  -- Proof comment: identify the explicit derivative map with the announced `fst`/`snd`
  -- combination by extensionality on tangent directions.
  convert hsum using 1
  apply ContinuousLinearMap.ext
  intro w
  rcases w with ⟨w1, w2⟩
  simp [gap, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply]
  ring

/-- Helper for Theorem 5.4.9.2: on the strict logarithmic domain, the scalar barrier `F₄` is
`C²` at the current residual-slack pair. -/
private theorem separableLogBarrierF4_contDiffAt
    {p s τ : ℝ}
    (hτ : 0 < τ)
    (hgap : 0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ)) :
    ContDiffAt ℝ 2 (separableLogBarrierF4 p) (s, τ) := by
  have hfst :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ z.1) (s, τ) := by
    -- Proof comment: the first coordinate is a fixed continuous linear projection.
    simpa using (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff.contDiffAt
  have hsnd :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ z.2) (s, τ) := by
    -- Proof comment: the second coordinate is the companion continuous linear projection.
    simpa using (ContinuousLinearMap.snd ℝ ℝ ℝ).contDiff.contDiffAt
  have hsq :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ z.1 ^ (2 : ℕ)) (s, τ) := by
    -- Proof comment: the square term is a polynomial in the first coordinate.
    simpa using hfst.pow 2
  have hrpow :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ Real.rpow z.2 (2 / p)) (s, τ) := by
    -- Proof comment: the `rpow` factor is smooth at positive slack values.
    have hscalar :
        ContDiffAt ℝ 2 (fun t' : ℝ ↦ Real.rpow t' (2 / p)) τ := by
      simpa using
        (Real.contDiffAt_rpow_const (x := τ) (p := 2 / p) (n := 2) (Or.inl hτ.ne'))
    simpa using hscalar.comp (s, τ) hsnd
  have hgapCont :
      ContDiffAt ℝ 2
        (fun z : ℝ × ℝ ↦ Real.rpow z.2 (2 / p) - z.1 ^ (2 : ℕ))
        (s, τ) := by
    -- Proof comment: the logarithmic gap is the smooth difference between the `rpow` and square
    -- factors.
    simpa using hrpow.sub hsq
  have hlogτ :
      ContDiffAt ℝ 2 (fun z : ℝ × ℝ ↦ -Real.log z.2) (s, τ) := by
    -- Proof comment: positivity of `τ` keeps the first logarithm on its smooth branch.
    have hscalar : ContDiffAt ℝ 2 (fun t' : ℝ ↦ -Real.log t') τ := by
      simpa using (Real.contDiffAt_log.2 hτ.ne').neg
    simpa using hscalar.comp (s, τ) hsnd
  have hlogGap :
      ContDiffAt ℝ 2
        (fun z : ℝ × ℝ ↦ -Real.log (Real.rpow z.2 (2 / p) - z.1 ^ (2 : ℕ)))
        (s, τ) := by
    -- Proof comment: the strict residual gap keeps the second logarithm on its smooth branch.
    have hscalar :
        ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y)
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
      simpa using (Real.contDiffAt_log.2 hgap.ne').neg
    simpa using hscalar.comp (s, τ) hgapCont
  have hsum :
      ContDiffAt ℝ 2
        (fun z : ℝ × ℝ ↦
          -Real.log z.2 + -Real.log (Real.rpow z.2 (2 / p) - z.1 ^ (2 : ℕ)))
        (s, τ) := by
    -- Proof comment: after expanding `F₄`, the two logarithmic branches are independently `C²`
    -- and then recombine by addition.
    exact hlogτ.add hlogGap
  convert hsum using 1
  funext z
  rcases z with ⟨z1, z2⟩
  simp [separableLogBarrierF4_apply, sub_eq_add_neg, add_comm]

namespace StrictBarrierModelPoint

/-- The gradient of the actual barrier `problem.barrierModelBarrier` at a strict-domain point,
written in the Chapter 5 coordinates `(x, ξ, τ)` and assembled from the source-facing block
owners `g₁` and `g₂`. -/
def barrierSecondOrderOracleGradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    LpApproximationEpigraphPoint n m :=
  let barrierScalar := separableLogBarrierF4 problem.p
  let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
  let g1Vector : EuclideanSpace ℝ (Fin m) :=
    (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
      auxiliaryGradient barrierScalar (decision.newtonSystemResidual i)
        (decision.1.residualSlack i)
  let g2Vector : Fin m → ℝ := fun i ↦
    auxiliaryTimeDerivative barrierScalar (decision.newtonSystemResidual i)
      (decision.1.residualSlack i)
  let boxGradient : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm fun j ↦
      -(1 / (decision.1.point j - problem.α j)) +
        1 / (problem.β j - decision.1.point j)
  ((A[problem]).toEuclideanLin g1Vector + boxGradient,
    -1 / gap,
    fun i ↦ g2Vector i + 1 / gap)

/-- Expanding `decision.barrierSecondOrderOracleGradient` recovers the Chapter 5 dense gradient
formula for `problem.barrierModelBarrier`, assembled from `g₁`, `g₂`, and the logarithmic box
terms. -/
theorem barrierSecondOrderOracleGradient_def
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient =
      let barrierScalar := separableLogBarrierF4 problem.p
      let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
      let g1Vector : EuclideanSpace ℝ (Fin m) :=
        (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
          auxiliaryGradient barrierScalar (decision.newtonSystemResidual i)
            (decision.1.residualSlack i)
      let g2Vector : Fin m → ℝ := fun i ↦
        auxiliaryTimeDerivative barrierScalar (decision.newtonSystemResidual i)
          (decision.1.residualSlack i)
      let boxGradient : EuclideanSpace ℝ (Fin n) :=
        (EuclideanSpace.equiv (Fin n) ℝ).symm fun j ↦
          -(1 / (decision.1.point j - problem.α j)) +
            1 / (problem.β j - decision.1.point j)
      ((A[problem]).toEuclideanLin g1Vector + boxGradient,
        -1 / gap,
        fun i ↦ g2Vector i + 1 / gap) :=
  rfl

/-- The `x`-component of `decision.barrierSecondOrderOracleGradient` is the dense sum of the
`g₁` evaluations and the box-logarithm gradient terms. -/
@[simp] theorem barrierSecondOrderOracleGradient_point
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient.point =
      (A[problem]).toEuclideanLin
          ((EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
            auxiliaryGradient (separableLogBarrierF4 problem.p) (decision.newtonSystemResidual i)
              (decision.1.residualSlack i)) +
        (EuclideanSpace.equiv (Fin n) ℝ).symm
          (fun j ↦
            -(1 / (decision.1.point j - problem.α j)) +
              1 / (problem.β j - decision.1.point j)) :=
  rfl

/-- The `ξ`-component of `decision.barrierSecondOrderOracleGradient` is the derivative of the
coupling logarithm `- log (ξ - ∑ i, τ⁽ⁱ⁾)`. -/
@[simp] theorem barrierSecondOrderOracleGradient_objectiveSlack
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    decision.barrierSecondOrderOracleGradient.objectiveSlack =
      -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) :=
  rfl

/-- The `τ⁽ⁱ⁾`-component of `decision.barrierSecondOrderOracleGradient` is the sum of the
source-facing `g₂` contribution and the coupling-logarithm derivative. -/
@[simp] theorem barrierSecondOrderOracleGradient_residualSlack
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    decision.barrierSecondOrderOracleGradient.residualSlack i =
      auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
          (decision.newtonSystemResidual i) (decision.1.residualSlack i) +
        1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j) :=
  rfl

/-- Helper for Theorem 5.4.9.2: the ambient residual pair map differentiates through the ambient
Euclidean bridge with the expected constant derivative. -/
private theorem residualPair_hasFDerivAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    HasFDerivAt
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
          (ofLpBarrierOracleAmbientPoint z).residualSlack i))
      ((((innerSL ℝ (problem.a i)).comp (ambientPointCLM n m)).prod
          (ambientResidualSlackCLM n m i)))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  have hresidual :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i)
        ((innerSL ℝ (problem.a i)).comp (ambientPointCLM n m))
        (toLpBarrierOracleAmbientPoint decision.1) := by
    -- Proof comment: the residual affine coordinate is the ambient point projection followed by
    -- the fixed inner-product functional `⟪aᵢ, ·⟫`, with the constant `bᵢ` dropped by `sub_const`.
    simpa [Function.comp] using
      ((((innerSL ℝ (problem.a i)).comp (ambientPointCLM n m)).hasFDerivAt).sub_const
        (problem.b i))
  have hslack :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          (ofLpBarrierOracleAmbientPoint z).residualSlack i)
        (ambientResidualSlackCLM n m i)
        (toLpBarrierOracleAmbientPoint decision.1) := by
    -- Proof comment: the residual-slack coordinate is itself a fixed ambient continuous linear
    -- projection.
    simpa using (ambientResidualSlackCLM n m i).hasFDerivAt
  -- Proof comment: pair the two scalar ambient derivatives into the residual-pair derivative.
  simpa using hresidual.prodMk hslack

/-- Helper for Theorem 5.4.9.2: each residual-block summand of the ambient barrier is `C²` at a
strict barrier-model point once the residual pair is viewed through the ambient bridge. -/
private theorem residualBlock_contDiffAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    ContDiffAt ℝ 2
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
            (ofLpBarrierOracleAmbientPoint z).residualSlack i))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  have hpair :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
            (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        (toLpBarrierOracleAmbientPoint decision.1) := by
    have hresidual :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            ⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i)
          (toLpBarrierOracleAmbientPoint decision.1) := by
      -- Proof comment: the residual affine coordinate is a continuous linear functional followed
      -- by a constant subtraction, hence it is smooth of every order.
      simpa [Function.comp] using
        (((((innerSL ℝ (problem.a i)).comp (ambientPointCLM n m)).contDiff.contDiffAt).sub
            contDiffAt_const))
    have hslack :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            (ofLpBarrierOracleAmbientPoint z).residualSlack i)
          (toLpBarrierOracleAmbientPoint decision.1) := by
      -- Proof comment: the residual-slack coordinate is itself a continuous linear projection, so
      -- it is also smooth of every order.
      simpa using (ambientResidualSlackCLM n m i).contDiff.contDiffAt
    -- Proof comment: combine the two scalar ambient coordinate maps into the residual-pair map.
    simpa using hresidual.prodMk hslack
  have hscalar :=
    separableLogBarrierF4_contDiffAt
      (p := problem.p)
      (s := decision.newtonSystemResidual i)
      (τ := decision.1.residualSlack i)
      (strictBarrierResidualSlack_pos problem decision i)
      (strictBarrierResidualGap_pos problem decision i)
  -- Proof comment: compose the scalar `F₄` regularity at the strict residual pair with the
  -- ambient residual-pair map.
  simpa [Function.comp, decision.newtonSystemResidual_apply] using
    hscalar.comp (toLpBarrierOracleAmbientPoint decision.1) hpair

/-- Helper for Theorem 5.4.9.2: one residual-block summand differentiates to the ambient vector
whose point and residual-slack coordinates are the corresponding `g₁` and `g₂` contributions. -/
private theorem residualBlock_hasFDerivAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem)
    (i : Fin m) :
    HasFDerivAt
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
            (ofLpBarrierOracleAmbientPoint z).residualSlack i))
      (innerSL ℝ (toLpBarrierOracleAmbientPoint
        (((auxiliaryGradient (separableLogBarrierF4 problem.p) (decision.newtonSystemResidual i)
              (decision.1.residualSlack i)) • problem.a i),
          0,
          Pi.single i
            (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
              (decision.newtonSystemResidual i) (decision.1.residualSlack i)))))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  let g1 :=
    auxiliaryGradient (separableLogBarrierF4 problem.p)
      (decision.newtonSystemResidual i) (decision.1.residualSlack i)
  let g2 :=
    auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
      (decision.newtonSystemResidual i) (decision.1.residualSlack i)
  have hscalar :
      HasFDerivAt
        (separableLogBarrierF4 (problem.p : ℝ))
        (g1 • ContinuousLinearMap.fst ℝ ℝ ℝ + g2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
        (decision.newtonSystemResidual i, decision.1.residualSlack i) := by
    -- Proof comment: the scalar `F₄` gradient formula was already computed explicitly at the
    -- strict residual pair, so only the naming of the two coefficients remains.
    simpa [g1, g2,
      residualBlock_auxiliaryGradient_formula, residualBlock_auxiliaryTimeDerivative_formula] using
      (separableLogBarrierF4_hasFDerivAt
        (p := problem.p)
        (s := decision.newtonSystemResidual i)
        (τ := decision.1.residualSlack i)
        (strictBarrierResidualSlack_pos problem decision i)
        (strictBarrierResidualGap_pos problem decision i))
  have hcomp :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          separableLogBarrierF4 (problem.p : ℝ)
            (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
              (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        (g1 • ((innerSL ℝ (problem.a i)).comp (ambientPointCLM n m)) +
          g2 • ambientResidualSlackCLM n m i)
        (toLpBarrierOracleAmbientPoint decision.1) := by
    -- Proof comment: compose the scalar `F₄` derivative with the ambient residual-pair map.
    simpa [Function.comp, decision.newtonSystemResidual_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_comp,
      ContinuousLinearMap.smul_comp] using
      hscalar.comp
        (toLpBarrierOracleAmbientPoint decision.1)
        (residualPair_hasFDerivAtAmbient (decision := decision) i)
  -- Proof comment: the composed derivative acts only on the point coordinates through `aᵢ` and
  -- on the `i`-th residual-slack coordinate, which is exactly the announced ambient vector.
  convert hcomp using 1
  ext w
  rw [innerSL_toLpBarrierOracleAmbientPoint_eq_sum
    (point := g1 • problem.a i)
    (objectiveSlack := 0)
    (residualSlack := Pi.single i g2)]
  simp [g1, g2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    Pi.single_apply, PiLp.inner_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hcoord :
      ((lpBarrierOracleAmbientLinearEquiv n m).symm w).1.ofLp x =
        (ofLpBarrierOracleAmbientPoint w).point.ofLp x := by
    rfl
  rw [hcoord]
  rw [show ⟪(problem.a i).ofLp x, (ofLpBarrierOracleAmbientPoint w).1.ofLp x⟫ =
      (ofLpBarrierOracleAmbientPoint w).1.ofLp x * (problem.a i).ofLp x by rfl]
  ring

/-- Helper for Theorem 5.4.9.2: the coupling logarithm differentiates to the ambient vector with
objective-slack coefficient `-1 / gap` and uniform residual-slack coefficient `1 / gap`. -/
private theorem couplingLog_hasFDerivAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasFDerivAt
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        -Real.log
          ((ofLpBarrierOracleAmbientPoint z).objectiveSlack -
            ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i))
      (innerSL ℝ (toLpBarrierOracleAmbientPoint
        (0,
          -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i),
          fun _ : Fin m ↦
            1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j))))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  let x := toLpBarrierOracleAmbientPoint decision.1
  let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
  have hsumResidual :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i)
        (∑ i : Fin m, ambientResidualSlackCLM n m i)
        x := by
    classical
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin m)),
          HasFDerivAt
            (fun z : LpBarrierOracleAmbientPoint n m ↦
              (ofLpBarrierOracleAmbientPoint z).residualSlack i)
            (ambientResidualSlackCLM n m i)
            x := by
      intro i hi
      -- Proof comment: every residual-slack coordinate is a fixed ambient projection.
      simpa using (ambientResidualSlackCLM n m i).hasFDerivAt
    -- Proof comment: finite-sum differentiation packages the residual-slack coordinates into the
    -- scalar coupling gap `∑ τᵢ`.
    convert HasFDerivAt.sum hterms using 1
    funext z
    simp
  have hgap :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          (ofLpBarrierOracleAmbientPoint z).objectiveSlack -
            ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i)
        (ambientObjectiveSlackCLM n m - ∑ i : Fin m, ambientResidualSlackCLM n m i)
        x := by
    -- Proof comment: the coupling gap is the objective-slack projection minus the residual-slack
    -- sum, so its derivative is the corresponding difference of ambient projections.
    simpa using (ambientObjectiveSlackCLM n m).hasFDerivAt.sub hsumResidual
  have hlog :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          -Real.log
            ((ofLpBarrierOracleAmbientPoint z).objectiveSlack -
              ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        ((-(gap⁻¹ : ℝ)) •
          (ambientObjectiveSlackCLM n m - ∑ i : Fin m, ambientResidualSlackCLM n m i))
        x := by
    -- Proof comment: the strict coupling gap keeps the logarithm on its positive branch, so the
    -- derivative is the scalar `-1 / gap` times the gap derivative.
    simpa [Function.comp, gap] using
      (Real.hasDerivAt_log (strictBarrierGap_pos problem decision).ne').neg.comp_hasFDerivAt x hgap
  -- Proof comment: expand the ambient Riesz functional of the coupling vector and compare both
  -- maps on an arbitrary tangent direction.
  convert hlog using 1
  ext w
  rw [innerSL_toLpBarrierOracleAmbientPoint_eq_sum
    (point := 0)
    (objectiveSlack := -1 / gap)
    (residualSlack := fun _ : Fin m ↦ 1 / gap)]
  simp [gap, ContinuousLinearMap.smul_apply, Finset.mul_sum, Finset.sum_apply,
    sub_eq_add_neg, mul_comm]
  ring

/-- Helper for Theorem 5.4.9.2: the total box-logarithm branch differentiates to the ambient
vector supported on the point coordinates with the usual reciprocal box coefficients. -/
private theorem boxLogs_hasFDerivAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasFDerivAt
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        -∑ j : Fin n,
          (Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
            Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
      (innerSL ℝ (toLpBarrierOracleAmbientPoint
        (((EuclideanSpace.equiv (Fin n) ℝ).symm
            (fun j ↦
              -(1 / (decision.1.point j - problem.α j)) +
                1 / (problem.β j - decision.1.point j))),
          0,
          0)))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  let x := toLpBarrierOracleAmbientPoint decision.1
  let boxCoeff : Fin n → ℝ := fun j ↦
    -(1 / (decision.1.point j - problem.α j)) +
      1 / (problem.β j - decision.1.point j)
  let boxGradient : EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm boxCoeff
  have hsumBox :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ j : Fin n,
            (-Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
        (∑ j : Fin n, boxCoeff j • ambientPointCoordinateCLM n m j)
        x := by
    classical
    have hterms :
        ∀ j ∈ (Finset.univ : Finset (Fin n)),
          HasFDerivAt
            (fun z : LpBarrierOracleAmbientPoint n m ↦
              -Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
                -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j))
            (boxCoeff j • ambientPointCoordinateCLM n m j)
            x := by
      intro j hj
      rcases strictBarrierPoint_mem_box problem decision j with ⟨hlower_box, hupper_box⟩
      have hlower_pos : 0 < decision.1.point j - problem.α j := sub_pos.mpr hlower_box
      have hupper_pos : 0 < problem.β j - decision.1.point j := sub_pos.mpr hupper_box
      have hlower_base :
          (ambientPointCoordinateCLM n m j) x - problem.α j =
            decision.1.point j - problem.α j := by
        simp [x, toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
      have hupper_base :
          problem.β j - (ambientPointCoordinateCLM n m j) x =
            problem.β j - decision.1.point j := by
        simp [x, toLpBarrierOracleAmbientPoint, ofLpBarrierOracleAmbientPoint]
      have hlogLower :
          HasDerivAt (fun y : ℝ ↦ -Real.log y)
            (-(1 / (decision.1.point j - problem.α j)))
            ((ambientPointCoordinateCLM n m j) x - problem.α j) := by
        simpa [hlower_base, one_div] using (Real.hasDerivAt_log hlower_pos.ne').neg
      have hlogUpper :
          HasDerivAt (fun y : ℝ ↦ -Real.log y)
            (-(1 / (problem.β j - decision.1.point j)))
            (problem.β j - (ambientPointCoordinateCLM n m j) x) := by
        simpa [hupper_base, one_div] using (Real.hasDerivAt_log hupper_pos.ne').neg
      have hlower :
          HasFDerivAt
            (fun z : LpBarrierOracleAmbientPoint n m ↦
              -Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j))
            (-(1 / (decision.1.point j - problem.α j)) • ambientPointCoordinateCLM n m j)
            x := by
        -- Proof comment: differentiate the lower box slack before applying the smooth branch of
        -- `-log`.
        simpa [Function.comp, ambientPointCoordinateCLM_apply, one_div] using
          (hlogLower.comp_hasFDerivAt x
            ((ambientPointCoordinateCLM n m j).hasFDerivAt.sub_const (problem.α j)))
      have hupper :
          HasFDerivAt
            (fun z : LpBarrierOracleAmbientPoint n m ↦
              -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j))
            ((1 / (problem.β j - decision.1.point j)) • ambientPointCoordinateCLM n m j)
            x := by
        -- Proof comment: the derivative of `βⱼ - xⱼ` is the negative coordinate projection, so the
        -- outer minus from `-log` cancels that sign.
        simpa [Function.comp, ambientPointCoordinateCLM_apply, one_div, smul_smul,
          mul_assoc, mul_left_comm, mul_comm] using
          (hlogUpper.comp_hasFDerivAt x
            ((hasFDerivAt_const (x := x) (c := problem.β j)).sub
              (ambientPointCoordinateCLM n m j).hasFDerivAt))
      -- Proof comment: add the lower and upper box contributions for the `j`-th coordinate.
      simpa [boxCoeff, sub_eq_add_neg, add_smul, neg_smul] using
        hlower.add hupper
    -- Proof comment: the full box branch is the finite sum of the coordinatewise box terms.
    convert HasFDerivAt.sum hterms using 1
    funext z
    simp
  have hbox :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          -∑ j : Fin n,
            (Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
        (∑ j : Fin n, boxCoeff j • ambientPointCoordinateCLM n m j)
        x := by
    -- Proof comment: rewrite the box block as the finite sum of the already differentiated
    -- coordinatewise negative logarithms.
    convert hsumBox using 1
    funext z
    simp [sub_eq_add_neg, add_comm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  -- Proof comment: the coefficient sum on point coordinates is exactly the ambient Riesz
  -- functional of the announced box-gradient vector.
  convert hbox using 1
  ext w
  rw [innerSL_toLpBarrierOracleAmbientPoint_eq_sum
    (point := boxGradient)
    (objectiveSlack := 0)
    (residualSlack := 0)]
  simp [boxGradient, boxCoeff, Finset.sum_apply]

/-- Helper for Theorem 5.4.9.2: the oracle gradient vector is the sum of the ambient residual,
coupling, and box contribution vectors. -/
private theorem barrierSecondOrderOracleGradient_eq_residualCouplingBox_sum
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient =
      (∑ i : Fin m,
        toLpBarrierOracleAmbientPoint
          (((auxiliaryGradient (separableLogBarrierF4 problem.p) (decision.newtonSystemResidual i)
                (decision.1.residualSlack i)) • problem.a i),
            0,
            Pi.single i
              (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
                (decision.newtonSystemResidual i) (decision.1.residualSlack i)))) +
        toLpBarrierOracleAmbientPoint
          (0,
            -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i),
            fun _ : Fin m ↦
              1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j)) +
        toLpBarrierOracleAmbientPoint
          (((EuclideanSpace.equiv (Fin n) ℝ).symm
              (fun j ↦
                -(1 / (decision.1.point j - problem.α j)) +
                  1 / (problem.β j - decision.1.point j))),
            0,
            0) := by
  let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
  let residualCoeff : Fin m → ℝ := fun i ↦
    auxiliaryGradient (separableLogBarrierF4 problem.p)
      (decision.newtonSystemResidual i) (decision.1.residualSlack i)
  let boxCoeff : Fin n → ℝ := fun j ↦
    -(1 / (decision.1.point j - problem.α j)) +
      1 / (problem.β j - decision.1.point j)
  -- Route correction: compare both sides after transporting back through the inverse ambient
  -- equivalence, so the goal lives again in the canonical product carrier.
  apply (lpBarrierOracleAmbientLinearEquiv n m).symm.injective
  apply Prod.ext
  · -- Proof comment: after simplifying the inverse ambient bridge on the point component, the
    -- residual matrix term is matched coordinatewise with the named Chapter 5 column-sum
    -- interface, and the box branch is already in the same normal form on both sides.
    ext j
    have hconstraint :=
      congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v j)
        (newtonSystemConstraintMatrix_toEuclideanLin_eq_sum_smul
          (problem := problem)
          (w := (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦
            auxiliaryGradient (separableLogBarrierF4 problem.p)
              (decision.newtonSystemResidual i) (decision.1.residualSlack i)))
    simp [lpBarrierOracleAmbientLinearEquiv, toLpBarrierOracleAmbientPoint,
      ofLpBarrierOracleAmbientPoint, Finset.sum_apply, Matrix.toLpLin_apply, Pi.smul_apply,
      decision.newtonSystemResidual_apply] at hconstraint ⊢
    rw [hconstraint]
    rw [show
      (point
            (0, -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i),
              fun i : Fin m ↦
                1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j))).ofLp
          j = 0 by
      rfl]
    rw [add_zero]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rfl
  · apply Prod.ext
    · -- Proof comment: only the coupling branch contributes to the objective-slack component.
      simp [lpBarrierOracleAmbientLinearEquiv, toLpBarrierOracleAmbientPoint,
        ofLpBarrierOracleAmbientPoint, Finset.sum_apply,
        barrierSecondOrderOracleGradient_objectiveSlack]
    · -- Proof comment: the residual-slack component is the residual `g₂` term together with the
      -- coupling contribution `1 / gap`.
      ext i
      simp [lpBarrierOracleAmbientLinearEquiv, toLpBarrierOracleAmbientPoint,
        ofLpBarrierOracleAmbientPoint, Finset.sum_apply,
        barrierSecondOrderOracleGradient_residualSlack]
      rfl

/-- Helper for Theorem 5.4.9.2: the coupling and box logarithm branches are `C²` at every strict
ambient barrier point. -/
private theorem nonResidualLogs_contDiffAtAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    ContDiffAt ℝ 2
      (fun z : LpBarrierOracleAmbientPoint n m ↦
        -Real.log
            ((ofLpBarrierOracleAmbientPoint z).objectiveSlack -
              ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i) -
          ∑ j : Fin n,
            (Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  let x := toLpBarrierOracleAmbientPoint decision.1
  let gap := decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i
  have hsumResidual :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i)
        x := by
    classical
    -- Proof comment: the residual-slack sum is a finite sum of ambient coordinate projections.
    refine ContDiffAt.sum ?_
    intro i hi
    simpa using (ambientResidualSlackCLM n m i).contDiff.contDiffAt
  have hgap :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          (ofLpBarrierOracleAmbientPoint z).objectiveSlack -
            ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i)
        x := by
    -- Proof comment: the coupling gap is an affine combination of ambient coordinate
    -- projections, hence smooth of every order.
    simpa using (ambientObjectiveSlackCLM n m).contDiff.contDiffAt.sub hsumResidual
  have hcoupling :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          -Real.log
            ((ofLpBarrierOracleAmbientPoint z).objectiveSlack -
              ∑ i : Fin m, (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        x := by
    have hscalar :
        ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) gap := by
      -- Proof comment: strict feasibility keeps the coupling logarithm on its smooth positive
      -- branch.
      simpa [gap] using (Real.contDiffAt_log.2 (strictBarrierGap_pos problem decision).ne').neg
    -- Proof comment: compose the scalar logarithm regularity with the affine coupling-gap map.
    simpa [Function.comp, gap] using hscalar.comp x hgap
  have hboxTerms :
      ∀ j : Fin n,
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            -Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j))
          x := by
    intro j
    rcases strictBarrierPoint_mem_box problem decision j with ⟨hlower_box, hupper_box⟩
    have hlower_pos : 0 < decision.1.point j - problem.α j := sub_pos.mpr hlower_box
    have hupper_pos : 0 < problem.β j - decision.1.point j := sub_pos.mpr hupper_box
    have hlowerMap :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            (ofLpBarrierOracleAmbientPoint z).point j - problem.α j)
          x := by
      -- Proof comment: the lower box slack is an affine point-coordinate map.
      simpa using (ambientPointCoordinateCLM n m j).contDiff.contDiffAt.sub contDiffAt_const
    have hupperMap :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)
          x := by
      -- Proof comment: the upper box slack is the companion affine point-coordinate map.
      simpa using contDiffAt_const.sub (ambientPointCoordinateCLM n m j).contDiff.contDiffAt
    have hlower :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            -Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j))
          x := by
      have hscalar :
          ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) (decision.1.point j - problem.α j) := by
        simpa using (Real.contDiffAt_log.2 hlower_pos.ne').neg
      -- Proof comment: strict lower-box positivity keeps the logarithm smooth after
      -- composition with the lower slack map.
      simpa [Function.comp] using hscalar.comp x hlowerMap
    have hupper :
        ContDiffAt ℝ 2
          (fun z : LpBarrierOracleAmbientPoint n m ↦
            -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j))
          x := by
      have hscalar :
          ContDiffAt ℝ 2 (fun y : ℝ ↦ -Real.log y) (problem.β j - decision.1.point j) := by
        simpa using (Real.contDiffAt_log.2 hupper_pos.ne').neg
      -- Proof comment: strict upper-box positivity gives the same smoothness for the upper
      -- logarithm branch.
      simpa [Function.comp] using hscalar.comp x hupperMap
    -- Proof comment: combine the two `C²` box logarithms for coordinate `j`.
    simpa [sub_eq_add_neg] using hlower.add hupper
  have hboxSum :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ j : Fin n,
            (-Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              -Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
        x := by
    classical
    -- Proof comment: the full box block is the finite sum of the coordinatewise box branches.
    exact ContDiffAt.sum fun j _ ↦ hboxTerms j
  have hbox :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          -∑ j : Fin n,
            (Real.log ((ofLpBarrierOracleAmbientPoint z).point j - problem.α j) +
              Real.log (problem.β j - (ofLpBarrierOracleAmbientPoint z).point j)))
        x := by
    -- Proof comment: rewrite the box branch into the negative-log sum normal form handled above.
    convert hboxSum using 1
    funext z
    simp [sub_eq_add_neg, add_comm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  -- Proof comment: the non-residual part of the barrier is the sum of the coupling log and the
  -- total box-log block.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcoupling.add hbox

/-- At a strict barrier-model point, the explicit vector
`decision.barrierSecondOrderOracleGradient` is genuine gradient data for the ambient bridge
formula of `problem.barrierModelBarrier`. -/
private theorem hasGradientAt_barrierModelBarrierAmbient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasGradientAt problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient)
      (toLpBarrierOracleAmbientPoint decision.1) := by
  -- Route correction: the ambient projection and residual-pair interfaces are now in place, so
  -- the remaining work is the final `HasFDerivAt` assembly and the vector-level identification
  -- of the summed branch contributions with the oracle gradient.
  rw [hasGradientAt_iff_hasFDerivAt]
  let x := toLpBarrierOracleAmbientPoint decision.1
  have hresidual :
      HasFDerivAt
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ i : Fin m,
            separableLogBarrierF4 (problem.p : ℝ)
              (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
                (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        (∑ i : Fin m,
          innerSL ℝ (toLpBarrierOracleAmbientPoint
            (((auxiliaryGradient (separableLogBarrierF4 problem.p) (decision.newtonSystemResidual i)
                  (decision.1.residualSlack i)) • problem.a i),
              0,
              Pi.single i
                (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
                  (decision.newtonSystemResidual i) (decision.1.residualSlack i)))))
        x := by
    classical
    have hterms :
        ∀ i ∈ (Finset.univ : Finset (Fin m)),
          HasFDerivAt
            (fun z : LpBarrierOracleAmbientPoint n m ↦
              separableLogBarrierF4 (problem.p : ℝ)
                (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
                  (ofLpBarrierOracleAmbientPoint z).residualSlack i))
            (innerSL ℝ (toLpBarrierOracleAmbientPoint
              (((auxiliaryGradient (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i)) • problem.a i),
                0,
                Pi.single i
                  (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i)))))
            x := by
      intro i hi
      exact residualBlock_hasFDerivAtAmbient (decision := decision) i
    -- Proof comment: the residual branch is a finite sum of the already packaged residual-block
    -- ambient derivatives.
    convert HasFDerivAt.sum hterms using 1
    funext z
    simp
  have hcoupling := couplingLog_hasFDerivAtAmbient (decision := decision)
  have hbox := boxLogs_hasFDerivAtAmbient (decision := decision)
  have hsum :
      HasFDerivAt
        problem.barrierModelBarrierAmbient
        ((∑ i : Fin m,
            innerSL ℝ (toLpBarrierOracleAmbientPoint
              (((auxiliaryGradient (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i)) • problem.a i),
                0,
                Pi.single i
                  (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i))))) +
          innerSL ℝ (toLpBarrierOracleAmbientPoint
            (0,
              -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i),
              fun i : Fin m ↦
                1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j))) +
          innerSL ℝ (toLpBarrierOracleAmbientPoint
            (((EuclideanSpace.equiv (Fin n) ℝ).symm
                (fun j ↦
                  -(1 / (decision.1.point j - problem.α j)) +
                    1 / (problem.β j - decision.1.point j))),
              0,
              0)))
        x := by
    -- Proof comment: the ambient barrier is the sum of the residual, coupling, and box branches,
    -- in that order, so their Fréchet derivatives add in the same order.
    convert hresidual.add (hcoupling.add hbox) using 1
    · funext z
      simp [LpApproximationBoxProblem.barrierModelBarrierAmbient, sub_eq_add_neg, add_assoc]
    · ext w
      simp [add_assoc]
  have hmap :
      (InnerProductSpace.toDual ℝ (LpBarrierOracleAmbientPoint n m))
          (toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient) =
        ((∑ i : Fin m,
            innerSL ℝ (toLpBarrierOracleAmbientPoint
              (((auxiliaryGradient (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i)) •
                  problem.a i),
                0,
                Pi.single i
                  (auxiliaryTimeDerivative (separableLogBarrierF4 problem.p)
                    (decision.newtonSystemResidual i) (decision.1.residualSlack i))))) +
          innerSL ℝ (toLpBarrierOracleAmbientPoint
            (0,
              -1 / (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i),
              fun i : Fin m ↦
                1 / (decision.1.objectiveSlack - ∑ j : Fin m, decision.1.residualSlack j))) +
          innerSL ℝ (toLpBarrierOracleAmbientPoint
            (((EuclideanSpace.equiv (Fin n) ℝ).symm
                (fun j ↦
                  -(1 / (decision.1.point j - problem.α j)) +
                    1 / (problem.β j - decision.1.point j))),
              0,
              0))) := by
    simpa [map_add, map_sum] using
      congrArg
        (InnerProductSpace.toDual ℝ (LpBarrierOracleAmbientPoint n m))
        (barrierSecondOrderOracleGradient_eq_residualCouplingBox_sum
          (problem := problem) decision)
  rw [hmap]
  exact hsum

/-- The explicit dense formula `decision.barrierSecondOrderOracleGradient` agrees with the
Euclidean gradient of the ambient bridge formula for `problem.barrierModelBarrier`. -/
private theorem barrierSecondOrderOracleGradient_eq_gradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    ∇ problem.barrierModelBarrierAmbient (toLpBarrierOracleAmbientPoint decision.1) =
      toLpBarrierOracleAmbientPoint decision.barrierSecondOrderOracleGradient := by
  -- Proof comment: once the explicit ambient gradient witness is available, the canonical
  -- gradient is forced to agree with that witness by uniqueness.
  exact (decision.hasGradientAt_barrierModelBarrierAmbient).gradient

/-- Helper for Theorem 5.4.9.2: the ambient barrier bridge is `C²` at every strict barrier-model
point. -/
private theorem barrierModelBarrierAmbient_contDiffAt
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    ContDiffAt ℝ 2 problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.1) := by
  -- Route correction: `separableLogBarrierF4_contDiffAt` and `residualBlock_contDiffAtAmbient`
  -- now discharge the residual branch, so the remaining work is the local `-log` regularity for
  -- the coupling and box affine coordinates and the final finite-sum recombination.
  let x := toLpBarrierOracleAmbientPoint decision.1
  have hresidual :
      ContDiffAt ℝ 2
        (fun z : LpBarrierOracleAmbientPoint n m ↦
          ∑ i : Fin m,
            separableLogBarrierF4 (problem.p : ℝ)
              (⟪problem.a i, (ofLpBarrierOracleAmbientPoint z).point⟫ - problem.b i,
                (ofLpBarrierOracleAmbientPoint z).residualSlack i))
        x := by
    classical
    -- Proof comment: the residual part is the finite sum of the already established `C²`
    -- residual-block branches.
    exact ContDiffAt.sum fun i _ ↦ residualBlock_contDiffAtAmbient (decision := decision) i
  have hnonResidual := nonResidualLogs_contDiffAtAmbient (decision := decision)
  -- Proof comment: the ambient barrier is the residual sum plus the coupling-and-box block, so
  -- the total `C²` regularity follows by addition.
  convert hnonResidual.add hresidual using 1
  funext z
  simp [LpApproximationBoxProblem.barrierModelBarrierAmbient, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

/-- The ambient bridge formula for `problem.barrierModelBarrier` also carries genuine second-order
oracle data at every strict barrier-model point. -/
private theorem hasFDerivAt_barrierModelBarrierAmbient_gradient
    {problem : LpApproximationBoxProblem n m}
    (decision : StrictBarrierModelPoint problem) :
    HasFDerivAt (∇ problem.barrierModelBarrierAmbient)
      (hessian problem.barrierModelBarrierAmbient
        (toLpBarrierOracleAmbientPoint decision.1))
      (toLpBarrierOracleAmbientPoint decision.1) := by
  let x := toLpBarrierOracleAmbientPoint decision.1
  let D : StrongDual ℝ (LpBarrierOracleAmbientPoint n m) →L[ℝ]
      LpBarrierOracleAmbientPoint n m :=
    (InnerProductSpace.toDual ℝ (LpBarrierOracleAmbientPoint n m)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  -- Proof comment: once the ambient barrier is `C²`, differentiate its Fréchet-derivative field
  -- once and then transport that derivative through the Riesz map defining `gradient`.
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ problem.barrierModelBarrierAmbient) x := by
    have hC1_fderiv :
        ContDiffAt ℝ 1 (fderiv ℝ problem.barrierModelBarrierAmbient) x :=
      (barrierModelBarrierAmbient_contDiffAt decision).fderiv_right
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact hC1_fderiv.differentiableAt one_ne_zero
  have hgradDiff :
      DifferentiableAt ℝ (∇ problem.barrierModelBarrierAmbient) x := by
    -- Proof comment: `gradient` is the Riesz transport of `fderiv`, so differentiability of the
    -- first derivative field transfers directly to the gradient field.
    simpa [gradient, D, x] using D.differentiableAt.comp x hfderiv
  -- Proof comment: the chapter Hessian owner is defined as the derivative of the gradient field.
  simpa [hessian, x] using hgradDiff.hasFDerivAt

end StrictBarrierModelPoint

/-- The Hessian part of the actual second-order oracle for `problem.barrierModelBarrier`,
transported from the private Euclidean ambient bridge back to the canonical lifted carrier
`LpApproximationEpigraphPoint n m`. -/
def StrictBarrierModelPoint.barrierSecondOrderOracleHessian
    {problem : LpApproximationBoxProblem n m}
    (decision : problem.StrictBarrierModelPoint) :
    LpApproximationEpigraphPoint n m →L[ℝ] LpApproximationEpigraphPoint n m :=
  let ambientEquiv := lpBarrierOracleAmbientEquiv n m
  ambientEquiv.symm.toContinuousLinearMap.comp
    ((hessian problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.1)).comp ambientEquiv.toContinuousLinearMap)

/-- Expanding `decision.barrierSecondOrderOracleHessian` recovers the Hessian of the private
ambient bridge formula, conjugated back to `LpApproximationEpigraphPoint n m`. -/
theorem StrictBarrierModelPoint.barrierSecondOrderOracleHessian_def
    {problem : LpApproximationBoxProblem n m}
    (decision : problem.StrictBarrierModelPoint) :
    decision.barrierSecondOrderOracleHessian =
      let ambientEquiv := lpBarrierOracleAmbientEquiv n m
      ambientEquiv.symm.toContinuousLinearMap.comp
        ((hessian problem.barrierModelBarrierAmbient
          (toLpBarrierOracleAmbientPoint decision.1)).comp ambientEquiv.toContinuousLinearMap) :=
  rfl

/-- The actual second-order oracle for the barrier `problem.barrierModelBarrier`: the explicit
gradient formula together with the Hessian operator on the canonical lifted decision carrier. -/
def barrierSecondOrderOracle
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    LpBarrierSecondOrderOracleOutput n m :=
  (decision.barrierSecondOrderOracleGradient,
    decision.barrierSecondOrderOracleHessian)

/-- Expanding `problem.barrierSecondOrderOracle decision` recovers the actual barrier gradient and
Hessian data at the strict point `decision`. -/
theorem barrierSecondOrderOracle_def
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierSecondOrderOracle decision =
      (decision.barrierSecondOrderOracleGradient,
        decision.barrierSecondOrderOracleHessian) :=
  rfl

/-- The dense block presentation of the Hessian part of `problem.barrierSecondOrderOracle`,
assembled from the Chapter 5 Newton blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, and `D`. -/
def barrierSecondOrderOracleDenseBlocks
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :=
  (decision.barrierSecondOrderOracleGradient,
    κ[decision],
    Λ₀[decision],
    Λ₁[decision],
    Λ₂[decision],
    D[decision])

/-- Expanding `problem.barrierSecondOrderOracleDenseBlocks decision` recovers the concrete dense
block data used to assemble the Hessian of `problem.barrierModelBarrier`. -/
theorem barrierSecondOrderOracleDenseBlocks_def
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierSecondOrderOracleDenseBlocks decision =
      (decision.barrierSecondOrderOracleGradient,
        κ[decision],
        Λ₀[decision],
        Λ₁[decision],
        Λ₂[decision],
        D[decision]) :=
  rfl

/-- The source-facing oracle `problem.barrierSecondOrderOracle` supplies genuine second-order
oracle data for the ambient bridge formula of `problem.barrierModelBarrier`. -/
private theorem barrierSecondOrderOracle_hasSecondOrderOracleAt
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    HasSecondOrderOracleAt problem.barrierModelBarrierAmbient
      (toLpBarrierOracleAmbientPoint decision.1) := by
  -- Proof comment: reuse the already-established ambient gradient and Hessian witnesses, rewriting
  -- the gradient component to the canonical `∇` owner only once.
  refine ⟨?_, decision.hasFDerivAt_barrierModelBarrierAmbient_gradient⟩
  rw [decision.barrierSecondOrderOracleGradient_eq_gradient]
  exact decision.hasGradientAt_barrierModelBarrierAmbient

end LpApproximationBoxProblem

/-- A primitive oracle evaluator computes the actual Chapter 5 second-order oracle when it agrees
pointwise with `problem.barrierSecondOrderOracle`. -/
def EvaluatesLpBarrierSecondOrderOracle
    (oracle : LpBarrierSecondOrderOracleEvaluator) : Prop :=
  ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint),
      oracle problem decision = problem.barrierSecondOrderOracle decision

/-- The primitive dense-model hypothesis that every per-index evaluation of the source-facing
block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` has uniformly bounded arithmetic cost. -/
def HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : Prop :=
  ∃ C_eval : ℕ,
    ∀ m n : ℕ, 0 < m → 0 < n →
      g1Work m n ≤ C_eval ∧
        g2Work m n ≤ C_eval ∧
        h11Work m n ≤ C_eval ∧
        h12Work m n ≤ C_eval ∧
        h22Work m n ≤ C_eval

section OracleWork

variable
  (oracle : LpBarrierSecondOrderOracleEvaluator)
  (oracleWork : LpBarrierSecondOrderOracleWork)

/-- The dense-assembly cost bound for one second-order oracle call to the actual barrier
`problem.barrierModelBarrier`: the arithmetic work is accounted for by evaluating the
primitive block owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` at each residual block and
assembling the resulting gradient and Hessian by dense vector and matrix bookkeeping. -/
def LpBarrierSecondOrderOracleDenseAssemblyBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) : Prop :=
  EvaluatesLpBarrierSecondOrderOracle oracle ∧
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (decision : problem.StrictBarrierModelPoint),
        oracleWork problem decision ≤
          barrierSecondOrderOracleDenseArithmeticWorkBound m n
            g1Work g2Work h11Work h12Work h22Work

/-- The source-facing `O(m n^2)` arithmetic-complexity owner for the second-order oracle of the
actual barrier `problem.barrierModelBarrier`. -/
def HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound
    : Prop :=
  EvaluatesLpBarrierSecondOrderOracle oracle ∧
    ∃ C_oracle : ℝ,
      0 < C_oracle ∧
        ∀ m n : ℕ, 0 < m → 0 < n →
          ∀ (problem : LpApproximationBoxProblem n m) (decision : problem.StrictBarrierModelPoint),
            (oracleWork problem decision : ℝ) ≤
              C_oracle * (m : ℝ) * (n : ℝ) ^ (2 : ℕ)

/-- Unfolding
`HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracleWork`
recovers the explicit constant-factor form of the dense-model bound `O(m n^2)` for the
second-order oracle of `problem.barrierModelBarrier`. -/
theorem hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_iff
    :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracle oracleWork ↔
      EvaluatesLpBarrierSecondOrderOracle oracle ∧
        ∃ C_oracle : ℝ,
          0 < C_oracle ∧
            ∀ m n : ℕ, 0 < m → 0 < n →
              ∀ (problem : LpApproximationBoxProblem n m)
                (decision : problem.StrictBarrierModelPoint),
                (oracleWork problem decision : ℝ) ≤
                  C_oracle * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := by
  rfl

end OracleWork

private theorem barrierSecondOrderOracleDenseArithmeticWorkBound_le
    {m n C_eval : ℕ}
    {g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ}
    (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hg1 : g1Work m n ≤ C_eval)
    (hg2 : g2Work m n ≤ C_eval)
    (hh11 : h11Work m n ≤ C_eval)
    (hh12 : h12Work m n ≤ C_eval)
    (hh22 : h22Work m n ≤ C_eval) :
    barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work ≤
      (5 * C_eval + 5) * m * n ^ 2 := by
  rw [barrierSecondOrderOracleDenseArithmeticWorkBound_eq]
  let M := m * n ^ 2
  have hn_sq : n ≤ n ^ 2 := by
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_left n hn
  have hn_sq_one : 1 ≤ n ^ 2 := le_trans hn hn_sq
  have hC_sq : C_eval ≤ C_eval * n ^ 2 := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left C_eval hn_sq_one
  have hmn_sq : m * n ≤ M := by
    simpa [M] using Nat.mul_le_mul_left m hn_sq
  have hm_sq : m ≤ m * n ^ 2 := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left m hn_sq_one
  have hnm_sq : n ≤ M := by
    calc
      n ≤ m * n := by
        simpa [Nat.one_mul, Nat.mul_comm] using Nat.mul_le_mul_right n hm
      _ ≤ M := hmn_sq
  have hterm1 :
      m * (g1Work m n + n) ≤ (C_eval + 1) * M := by
    calc
      m * (g1Work m n + n) ≤ m * (C_eval + n ^ 2) := by
        gcongr
      _ ≤ m * (C_eval * n ^ 2 + n ^ 2) := by
        gcongr
      _ = (C_eval + 1) * M := by
        dsimp [M]
        ring
  have hterm2 :
      m * g2Work m n + n ≤ (C_eval + 1) * M := by
    calc
      m * g2Work m n + n ≤ m * C_eval + M := by
        gcongr
      _ ≤ m * (C_eval * n ^ 2) + M := by
        gcongr
      _ = (C_eval + 1) * M := by
        dsimp [M]
        ring
  have hterm3_core :
      m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) ≤ 3 * C_eval * M := by
    have hh12' : n * h12Work m n ≤ n ^ 2 * C_eval := by
      calc
        n * h12Work m n ≤ n * C_eval := by
          gcongr
        _ ≤ n ^ 2 * C_eval := by
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
            Nat.mul_le_mul_right C_eval hn_sq
    have hh22' : h22Work m n ≤ n ^ 2 * C_eval := by
      calc
        h22Work m n ≤ C_eval := hh22
        _ ≤ n ^ 2 * C_eval := by
          simpa [Nat.mul_comm] using hC_sq
    calc
      m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n)
        ≤ m * (n ^ 2 * C_eval + n ^ 2 * C_eval + n ^ 2 * C_eval) := by
          gcongr
      _ = 3 * C_eval * M := by
        dsimp [M]
        ring
  have hterm3_overhead :
      m * n + m + n ≤ 3 * M := by
    calc
      m * n + m + n ≤ M + m + n := by
        gcongr
      _ ≤ M + M + n := by
        gcongr
      _ ≤ M + M + M := by
        gcongr
      _ = 3 * M := by
        ring
  calc
    m * (g1Work m n + n) +
        (m * g2Work m n + n) +
        (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n))
      = (m * (g1Work m n + n) + (m * g2Work m n + n)) +
          (m * (n ^ 2 * h11Work m n + n * h12Work m n + h22Work m n) + (m * n + m + n)) := by
            ring
    _ ≤ ((C_eval + 1) * M + (C_eval + 1) * M) + (3 * C_eval * M + 3 * M) := by
      gcongr
    _ = (5 * C_eval + 5) * M := by
      ring
    _ = (5 * C_eval + 5) * m * n ^ 2 := by
      simp [M, Nat.mul_assoc]

private theorem barrierSecondOrderOracleDenseArithmeticWorkBound_le_real
    {m n C_eval : ℕ}
    {g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hg1 : g1Work m n ≤ C_eval)
    (hg2 : g2Work m n ≤ C_eval)
    (hh11 : h11Work m n ≤ C_eval)
    (hh12 : h12Work m n ≤ C_eval)
    (hh22 : h22Work m n ≤ C_eval) :
    (barrierSecondOrderOracleDenseArithmeticWorkBound m n
        g1Work g2Work h11Work h12Work h22Work : ℝ) ≤
      (5 * C_eval + 5 : ℝ) * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := by
  exact_mod_cast
    barrierSecondOrderOracleDenseArithmeticWorkBound_le
      (Nat.succ_le_of_lt hm) (Nat.succ_le_of_lt hn) hg1 hg2 hh11 hh12 hh22

/-- If the arithmetic work of a second-order barrier oracle is bounded by the concrete dense
assembly template, then that work satisfies the source-facing owner
`HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound`. -/
theorem hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound
    (oracle : LpBarrierSecondOrderOracleEvaluator)
    (oracleWork : LpBarrierSecondOrderOracleWork)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ)
    (hassembly :
      LpBarrierSecondOrderOracleDenseAssemblyBound oracle oracleWork
        g1Work g2Work h11Work h12Work h22Work)
    (hblocks :
      HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
        g1Work g2Work h11Work h12Work h22Work) :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound oracle oracleWork := by
  rcases hassembly with ⟨horacle, hassembly⟩
  rcases hblocks with ⟨C_eval, hC_eval⟩
  refine ⟨horacle, (5 * C_eval + 5 : ℝ), by positivity, ?_⟩
  intro m n hm hn problem decision
  rcases hC_eval m n hm hn with ⟨hg1, hg2, hh11, hh12, hh22⟩
  have hwork := hassembly problem decision
  have hdense := barrierSecondOrderOracleDenseArithmeticWorkBound_le_real
    hm hn hg1 hg2 hh11 hh12 hh22
  calc
    (oracleWork problem decision : ℝ)
      ≤ barrierSecondOrderOracleDenseArithmeticWorkBound m n
          g1Work g2Work h11Work h12Work h22Work := by
            exact_mod_cast hwork
    _ ≤ (5 * C_eval + 5 : ℝ) * (m : ℝ) * (n : ℝ) ^ (2 : ℕ) := hdense

/-- The arithmetic work model attached to the concrete dense second-order oracle for
`problem.barrierModelBarrier` satisfies the corresponding dense assembly bound. -/
theorem barrierSecondOrderOracleDenseAssemblyBound
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ) :
    LpBarrierSecondOrderOracleDenseAssemblyBound
      (fun {_} {_} problem decision ↦ problem.barrierSecondOrderOracle decision)
      (fun {n} {m} _ _ ↦
        barrierSecondOrderOracleDenseArithmeticWorkBound m n
          g1Work g2Work h11Work h12Work h22Work)
      g1Work g2Work h11Work h12Work h22Work := by
  refine ⟨?_, ?_⟩
  · intro n m problem decision
    rfl
  · intro _ _ problem decision
    rfl

/-- Theorem 5.4.9.2: in the dense model, if each per-index evaluation of the source-facing block
owners `g₁`, `g₂`, `h₁₁`, `h₁₂`, and `h₂₂` has uniformly bounded arithmetic cost, then the
actual second-order oracle for `problem.barrierModelBarrier` has arithmetic complexity `O(m n^2)`
for every evaluator/work model whose outputs agree with `problem.barrierSecondOrderOracle` and
whose arithmetic work is bounded by the dense assembly template. -/
theorem barrierSecondOrderOracleDenseArithmeticComplexity_bound
    (oracle : LpBarrierSecondOrderOracleEvaluator)
    (oracleWork : LpBarrierSecondOrderOracleWork)
    (g1Work g2Work h11Work h12Work h22Work : ℕ → ℕ → ℕ)
    (hassembly :
      LpBarrierSecondOrderOracleDenseAssemblyBound oracle oracleWork
        g1Work g2Work h11Work h12Work h22Work)
    (hblocks :
      HasLpBarrierPerIndexSecondOrderBlockArithmeticBound
        g1Work g2Work h11Work h12Work h22Work) :
    HasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound
      oracle oracleWork :=
  hasLpBarrierSecondOrderOracleDenseArithmeticComplexityBound_of_denseAssemblyBound
    oracle oracleWork
    g1Work g2Work h11Work h12Work h22Work
    hassembly
    hblocks
