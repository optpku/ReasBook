/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_9_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.RealProdL2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Chap05RealProdL2.instSeminormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedAddCommGroupRealProd
attribute [local instance] Chap05RealProdL2.instNormedSpaceRealProd
attribute [local instance] Chap05RealProdL2.instInnerProductSpaceRealProd
attribute [local instance] Chap05RealProdL2.instCompleteSpaceRealProd

open Matrix
open scoped BigOperators Gradient RealInnerProductSpace LpBarrierNewtonSystem
open scoped SecondOrderDerivativeBlocks

variable {n m : ℕ}

open LpApproximationBoxProblem
open LpApproximationEpigraphPoint

local notation "Q₄[" p "]" =>
  constrainedEpigraph (Set.univ : Set ℝ)
    (fun x : ℝ ↦ ((|x| ^ p : ℝ) : WithTop ℝ))
local notation "Z₂" => WithLp 2 (ℝ × ℝ)
local notation "ofZ₂" => (WithLp.ofLp : Z₂ → ℝ × ℝ)

/- Theorem 5.4.9.3 lies in the Chapter 5 explicit-structure `ℓ_p`-barrier Newton-system /
short-step complexity domain.

Sampled owner-style declarations:
* `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemKappa`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda0`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda1`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda2`,
  `LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD`, and
  `LpApproximationBoxProblem.newtonSystemConstraintMatrix` in `Definition_5_4_9_9`, the chapter
  owners for the source-derived Newton blocks coming from `separableLogBarrierF4 problem.p`;
* `problem.StrictBarrierModelPoint` in `Definition_5_4_9_5`, the strict-domain owner already
  established for the logarithmic barrier and its interior points;
* `LpApproximationEpigraphPoint.point`, `objectiveSlack`, and `residualSlack` in
  `Theorem_5_4_8_9`, the chapter owner for the lifted increment variables `(Δx, Δξ, Δτ)`;
* `Matrix.mulVec`, the canonical owner for the vector form of the Newton equations;
* `HasLpBarrierShortStepIterationBound` in `Definition_5_4_9_6`, the chapter's source-facing
  owner for the short-step iteration count bound on the primitive function `N_it`.

Best owner abstraction:
* source-facing: the current `ℓ_p` approximation problem, the current strict barrier-model point,
  the displayed Newton system for the scalar barrier `separableLogBarrierF4 problem.p`, and the
  primitive per-step and total arithmetic-work functions;
* core/canonical: the derived Newton shorthand blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`, `A` from
  `Definition_5_4_9_9`, together with `Matrix.mulVec` and the nearby short-step iteration owner
  `HasLpBarrierShortStepIterationBound`;
* bridge/view: the coordinatewise expansion theorem
  `isLpBarrierNewtonSystemSolution_iff` and the asymptotic bridge from per-step work to total
  short-step work.

Primitive data:
* `problem : LpApproximationBoxProblem n m`;
* `decision : problem.StrictBarrierModelPoint`;
* the barrier parameter `t` and the actual barrier-gradient right-hand side at `decision`;
* the primitive uniform Newton solver family for that actual right-hand side
  `solver : ∀ {n m}, LpApproximationBoxProblem n m → ... → LpApproximationEpigraphPoint n m`;
* the primitive arithmetic-work family
  `arithmeticWork : ∀ {n m}, LpApproximationBoxProblem n m → ... → ℕ`;
* the primitive short-step iteration-count model `iterationCount : ℕ → ℕ → ℕ`.

Derived API:
* the Newton-system solution predicate at a strict barrier-model point, with the lifted increment
  `(Δx, Δξ, Δτ)` still carried by `LpApproximationEpigraphPoint n m`;
* the coordinatewise expansion theorem;
* the derived step-bound owner `LpBarrierNewtonStepBound`;
* the source-facing per-step owner `HasLpBarrierNewtonSystemArithmeticComplexityBound`;
* the explicit per-step arithmetic-budget witness attached to a constant `C_step`;
* the canonical total-work model induced from the iteration-count family and that uniform
  per-step budget, indexed only by `(m, n)`;
* the source-facing total-cost owner
  `HasLpBarrierShortStepTotalArithmeticComplexityBound`;
* the bridge theorem combining the per-step Newton cost with the chapter owner
  `HasLpBarrierShortStepIterationBound`.

This refinement keeps the Newton-system statement on the existing chapter owners, but anchors its
barrier Hessian data at the strict-domain owner `problem.StrictBarrierModelPoint` from
`Definition_5_4_9_5`. The lifted increment still uses the chapter's existing carrier
`LpApproximationEpigraphPoint n m`, and the complexity layer remains as predicates on primitive
solver/work or total-work data rather than on a bespoke wrapper structure. The per-step arithmetic
owner is factored into an explicit witness layer `HasLpBarrierNewtonSystemArithmeticBudget`, and
the short-step bridge now uses the canonical total-work model induced by `iterationCount` and
that uniform per-step budget instead of an unconstrained existential total-work family. -/

/-- The source-facing primal matrix from the first displayed Newton equation, packaged as the
canonical `n × n` operator `Λ₀ + A Λ₁ Aᵀ`. -/
def lpBarrierNewtonSystemPrimalMatrix
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    Matrix (Fin n) (Fin n) ℝ :=
  Λ₀[decision] + A[problem] * Λ₁[decision] * A[problem]ᵀ

/-- Expanding `lpBarrierNewtonSystemPrimalMatrix problem decision` recovers the canonical matrix
expression `Λ₀ + A Λ₁ Aᵀ` from the first Newton equation. -/
@[simp] theorem lpBarrierNewtonSystemPrimalMatrix_eq
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    lpBarrierNewtonSystemPrimalMatrix problem decision =
      Λ₀[decision] + A[problem] * Λ₁[decision] * A[problem]ᵀ :=
  rfl

/-- Applying the source-facing primal matrix to `Δx` expands to the customary matrix-vector form
`Λ₀ Δx + A (Λ₁ (Aᵀ Δx))`. -/
@[simp] theorem lpBarrierNewtonSystemPrimalMatrix_mulVec
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (deltaX : EuclideanSpace ℝ (Fin n)) :
    Matrix.mulVec (lpBarrierNewtonSystemPrimalMatrix problem decision) deltaX =
      Matrix.mulVec Λ₀[decision] deltaX +
        Matrix.mulVec A[problem] (Matrix.mulVec Λ₁[decision] (A[problem]ᵀ.mulVec deltaX)) :=
by
  -- Proof comment: expand the primal matrix once, then use the canonical matrix-vector
  -- distributivity lemmas to normalize the first Newton equation.
  rw [lpBarrierNewtonSystemPrimalMatrix_eq, Matrix.add_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp [Matrix.mul_assoc]

/-- The displayed Newton system for the explicit-structure `ℓ_p` approximation barrier, written
using the Chapter 5 source-derived blocks `κ`, `Λ₀`, `Λ₁`, `Λ₂`, `D`, and `A` attached to the
current `problem` and strict barrier-model point `decision`. The first line uses the source-facing
primal matrix `lpBarrierNewtonSystemPrimalMatrix problem decision = Λ₀ + A Λ₁ Aᵀ`. The step
variable lives in the canonical lifted carrier `LpApproximationEpigraphPoint n m`, with
`step.point = Δx`, `step.objectiveSlack = Δξ`, and `step.residualSlack = Δτ`. -/
def IsLpBarrierNewtonSystemSolution
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) : Prop :=
  let κ := κ[decision]
  let Λ₂ := Λ₂[decision]
  let D := D[decision]
  let A := A[problem]
  let primalMatrix := lpBarrierNewtonSystemPrimalMatrix problem decision
  let adjointX := Aᵀ.mulVec step.point
  let tauCoupling := κ * ((∑ i : Fin m, step.residualSlack i) - step.objectiveSlack)
  Matrix.mulVec primalMatrix step.point + Matrix.mulVec A (Matrix.mulVec Λ₂ step.residualSlack) =
    gradX ∧
    Matrix.mulVec Λ₂ adjointX +
        Matrix.mulVec D step.residualSlack +
        tauCoupling • (1 : Fin m → ℝ) =
      gradTau ∧
    κ * step.objectiveSlack - κ * (∑ i : Fin m, step.residualSlack i) = gradXi + t

-- Proof sketch: unfold `IsLpBarrierNewtonSystemSolution`; the definition is exactly the three
-- displayed equations of the Newton system, written coordinatewise in the `x`- and `τ`-blocks and
-- with the scalar coupling equation in the last line.
/-- Expanding `IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step`
recovers the three equations of the explicit-structure Newton system. -/
theorem isLpBarrierNewtonSystemSolution_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) :
    IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step ↔
      let κ := κ[decision]
      let Λ₂ := Λ₂[decision]
      let D := D[decision]
      let A := A[problem]
      let primalMatrix := lpBarrierNewtonSystemPrimalMatrix problem decision
      let adjointX := Aᵀ.mulVec step.point
      let tauCoupling := κ * ((∑ i : Fin m, step.residualSlack i) - step.objectiveSlack)
      (∀ i : Fin n,
        (Matrix.mulVec primalMatrix step.point) i +
            (Matrix.mulVec A (Matrix.mulVec Λ₂ step.residualSlack)) i =
          gradX i) ∧
        (∀ i : Fin m,
          (Matrix.mulVec Λ₂ adjointX) i +
              (Matrix.mulVec D step.residualSlack) i +
              tauCoupling =
            gradTau i) ∧
        κ * step.objectiveSlack - κ * (∑ i : Fin m, step.residualSlack i) = gradXi + t := by
  dsimp [IsLpBarrierNewtonSystemSolution]
  constructor
  · rintro ⟨hx, hTau, hXi⟩
    refine ⟨?_, ?_, hXi⟩
    · intro i
      simpa using congrFun hx i
    · intro i
      simpa using congrFun hTau i
  · rintro ⟨hx, hTau, hXi⟩
    refine ⟨?_, ?_, hXi⟩
    · simpa using funext hx
    · ext i
      simpa using hTau i

/-- Helper for the Newton-system arithmetic-complexity statement: bundle the three displayed
Newton equations into one affine
residual map on the lifted increment carrier. Vanishing of this map is equivalent to solving the
Newton system. -/
def lpBarrierNewtonResidual
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ) :
    LpApproximationEpigraphPoint n m → LpApproximationEpigraphPoint n m :=
  fun step ↦
    let κ := κ[decision]
    let Λ₂ := Λ₂[decision]
    let D := D[decision]
    let A := A[problem]
    let primalMatrix := lpBarrierNewtonSystemPrimalMatrix problem decision
    let adjointX := Aᵀ.mulVec step.point
    let tauCoupling := κ * ((∑ i : Fin m, step.residualSlack i) - step.objectiveSlack)
    ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦
        (Matrix.mulVec primalMatrix step.point) i +
          (Matrix.mulVec A (Matrix.mulVec Λ₂ step.residualSlack)) i - gradX i,
      κ * step.objectiveSlack - κ * (∑ i : Fin m, step.residualSlack i) - (gradXi + t),
      fun i ↦
        (Matrix.mulVec Λ₂ adjointX) i +
            (Matrix.mulVec D step.residualSlack) i +
            tauCoupling - gradTau i)

/-- Helper for the Newton-system arithmetic-complexity statement: solving the Newton system is
equivalent to making the bundled affine residual vanish. -/
theorem isLpBarrierNewtonSystemSolution_iff_residual_eq_zero
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) :
    IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step ↔
      lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step = 0 := by
  rw [isLpBarrierNewtonSystemSolution_iff]
  constructor
  · rintro ⟨hx, hTau, hXi⟩
    -- Proof comment: move each displayed right-hand side to the left and package the three zero
    -- equations in the canonical product carrier `(Δx, Δξ, Δτ)`.
    refine Prod.ext ?_ ?_
    · ext i
      have hzero :
          (Matrix.mulVec (lpBarrierNewtonSystemPrimalMatrix problem decision) step.point) i +
              (Matrix.mulVec A[problem] (Matrix.mulVec Λ₂[decision] step.residualSlack)) i -
              gradX i =
            0 := by
        rw [hx i, sub_self]
      simpa [lpBarrierNewtonResidual] using hzero
    · refine Prod.ext ?_ ?_
      · have hzero :
          κ[decision] * step.objectiveSlack -
              κ[decision] * (∑ i : Fin m, step.residualSlack i) - (gradXi + t) =
            0 := by
          rw [hXi, sub_self]
        simpa [lpBarrierNewtonResidual] using hzero
      · funext i
        have hzero :
            (Matrix.mulVec Λ₂[decision] (A[problem]ᵀ.mulVec step.point)) i +
                (Matrix.mulVec D[decision] step.residualSlack) i +
                κ[decision] *
                    ((∑ j : Fin m, step.residualSlack j) - step.objectiveSlack) -
                gradTau i =
              0 := by
          rw [hTau i, sub_self]
        simpa [lpBarrierNewtonResidual] using hzero
  · intro hresidual
    -- Proof comment: project the vanishing affine residual back to the `x`, `τ`, and `ξ`
    -- components to recover the three displayed Newton equations.
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hpointEq :
          (lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step).point = 0 := by
        simpa using congrArg LpApproximationEpigraphPoint.point hresidual
      have hpointZero :
          (lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step).point i = 0 :=
        congrArg (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) hpointEq
      exact sub_eq_zero.mp (by simpa [lpBarrierNewtonResidual] using hpointZero)
    · intro i
      have hTauEq :
          (lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step).residualSlack =
            0 := by
          simpa using congrArg LpApproximationEpigraphPoint.residualSlack hresidual
      have hTauZero :
          (lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step).residualSlack i =
            0 :=
        congrFun hTauEq i
      exact sub_eq_zero.mp (by simpa [lpBarrierNewtonResidual] using hTauZero)
    · have hXiZero :
        (lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step).objectiveSlack = 0 :=
        by
          simpa using congrArg LpApproximationEpigraphPoint.objectiveSlack hresidual
      exact sub_eq_zero.mp (by simpa [lpBarrierNewtonResidual] using hXiZero)

/-- Helper for Theorem 5.4.9.3: the homogeneous linear part of the bundled Newton residual. This
is the displayed Newton operator on the lifted carrier `(Δx, Δξ, Δτ)`. -/
def lpBarrierNewtonOperator
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    LpApproximationEpigraphPoint n m → LpApproximationEpigraphPoint n m :=
  fun step ↦
    let κ := κ[decision]
    let Λ₂ := Λ₂[decision]
    let D := D[decision]
    let A := A[problem]
    let primalMatrix := lpBarrierNewtonSystemPrimalMatrix problem decision
    let adjointX := Aᵀ.mulVec step.point
    let tauCoupling := κ * ((∑ i : Fin m, step.residualSlack i) - step.objectiveSlack)
    ((EuclideanSpace.equiv (Fin n) ℝ).symm fun i ↦
        (Matrix.mulVec primalMatrix step.point) i +
          (Matrix.mulVec A (Matrix.mulVec Λ₂ step.residualSlack)) i,
      κ * step.objectiveSlack - κ * (∑ i : Fin m, step.residualSlack i),
      fun i ↦
        (Matrix.mulVec Λ₂ adjointX) i +
        (Matrix.mulVec D step.residualSlack) i +
          tauCoupling)

/-- Helper for Theorem 5.4.9.3: the bundled right-hand side of the displayed Newton system. -/
def lpBarrierNewtonRhs
    (problem : LpApproximationBoxProblem n m)
    (_decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ) :
    LpApproximationEpigraphPoint n m :=
  (gradX, gradXi + t, gradTau)

/-- Helper for Theorem 5.4.9.3: the bundled affine residual is `L step - rhs` for the explicit
Newton operator `L` and bundled right-hand side `rhs`. -/
theorem lpBarrierNewtonResidual_eq_operator_sub_rhs
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) :
    lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step =
      lpBarrierNewtonOperator problem decision step -
        lpBarrierNewtonRhs problem decision gradX gradTau gradXi t := by
  -- Proof comment: unfold the two packaged owners once; the residual is definitionally the
  -- operator value with the bundled right-hand side moved to the left.
  ext i <;> rfl

/-- Helper for Theorem 5.4.9.3: vanishing of the bundled residual is equivalent to solving the
explicit linear equation `L step = rhs`. -/
theorem lpBarrierNewtonResidual_eq_zero_iff_operator_eq_rhs
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ)
    (step : LpApproximationEpigraphPoint n m) :
    lpBarrierNewtonResidual problem decision gradX gradTau gradXi t step = 0 ↔
      lpBarrierNewtonOperator problem decision step =
        lpBarrierNewtonRhs problem decision gradX gradTau gradXi t := by
  -- Proof comment: after rewriting the residual as `L step - rhs`, the claim is the standard
  -- `sub_eq_zero` equivalence in the product carrier.
  rw [lpBarrierNewtonResidual_eq_operator_sub_rhs]
  exact sub_eq_zero

/-- Helper for Theorem 5.4.9.3: strict barrier-domain membership gives a positive gap
`ξ - ∑ i, τ⁽ⁱ⁾`. -/
theorem strictBarrierGap_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    0 < decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i := by
  -- Proof comment: unpack the strict barrier-domain characterization and read off the gap
  -- inequality from its middle conjunct.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨_, hgap, _⟩
  exact sub_pos.mpr hgap

/-- Helper for Theorem 5.4.9.3: strict barrier-domain membership gives positive residual slacks.
-/
theorem strictBarrierResidualSlack_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    0 < decision.1.residualSlack i := by
  -- Proof comment: the strict-domain characterization records positivity of every residual slack
  -- in its first conjunct.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨hresidual, _, _⟩
  exact (hresidual i).1

/-- Helper for Theorem 5.4.9.3: strict barrier-domain membership gives the strict box bounds on
the primal point. -/
theorem strictBarrierPoint_mem_box
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (j : Fin n) :
    problem.α j < decision.1.point j ∧ decision.1.point j < problem.β j := by
  -- Proof comment: the box inequalities are the final conjunct of the barrier-domain
  -- characterization.
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨_, _, hbox⟩
  exact hbox j

/-- Helper for Theorem 5.4.9.3: every residual-slack pair `(sᵢ, τᵢ)` of a strict barrier-model
point lies in the interior domain of the scalar barrier `F₄`. -/
private theorem newtonSystemResidual_mem_f4Interior
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    (decision.newtonSystemResidual i, decision.1.residualSlack i) ∈
      interior Q₄[(problem.p : ℝ)] := by
  -- Proof comment: unpack the strict barrier-domain inequalities, rewrite the quadratic residual
  -- bound as `|sᵢ| < τᵢ^(1 / p)`, and then return to the canonical interior characterization of
  -- `Q₄`.
  have hp0 : 0 < (problem.p : ℝ) := lt_of_lt_of_le zero_lt_one problem.one_le_p
  rw [mem_interior_constrainedEpigraph_abs_pow_iff (p := (problem.p : ℝ)) hp0]
  rcases (LpApproximationBoxProblem.mem_barrierModelBarrierDomain_iff problem decision.1).1
      decision.2 with ⟨hresidual, _, _⟩
  obtain ⟨hτ, hresidual_lt⟩ := hresidual i
  have hp_ne : (problem.p : ℝ) ≠ 0 := by positivity
  have hsq :
      |decision.newtonSystemResidual i| ^ (2 : ℕ) <
        (Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹)) ^ (2 : ℕ) := by
    -- Proof comment: both sides of the residual inequality are already squares after rewriting
    -- `τ^(2 / p)` as `(τ^(1 / p))^2`.
    have hrewrite :
        Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) =
          (Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹)) ^ (2 : ℕ) := by
      calc
        Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) =
            Real.rpow (decision.1.residualSlack i) (((problem.p : ℝ)⁻¹) * 2) := by
              field_simp [hp_ne]
        _ = (Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹)) ^ (2 : ℕ) := by
              simpa using
                (Real.rpow_mul_natCast
                  (le_of_lt hτ)
                  ((problem.p : ℝ)⁻¹)
                  2)
    have hsq0 :
        (decision.newtonSystemResidual i) ^ (2 : ℕ) <
          (Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹)) ^ (2 : ℕ) := by
      rw [hrewrite] at hresidual_lt
      exact hresidual_lt
    have habs_sq :
        |decision.newtonSystemResidual i| ^ (2 : ℕ) =
          (decision.newtonSystemResidual i) ^ (2 : ℕ) := by
      simp [sq_abs]
    rw [habs_sq]
    exact hsq0
  have hroot_nonneg :
      0 ≤ Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹) := by
    exact Real.rpow_nonneg (le_of_lt hτ) _
  have habs_lt :
      |decision.newtonSystemResidual i| <
        Real.rpow (decision.1.residualSlack i) ((problem.p : ℝ)⁻¹) := by
    nlinarith [hsq, abs_nonneg (decision.newtonSystemResidual i), hroot_nonneg]
  -- Proof comment: convert the `1 / p` power inequality back to the source-facing form
  -- `|sᵢ|^p < τᵢ`.
  simpa [one_div] using
    (Real.lt_rpow_inv_iff_of_pos
      (abs_nonneg (decision.newtonSystemResidual i)) (le_of_lt hτ) hp0).mp habs_lt

/-- Helper for Theorem 5.4.9.3: each diagonal entry of `Λ₀[decision]` is strictly positive. -/
private theorem newtonSystemLambda0_diag_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (j : Fin n) :
    0 < Λ₀[decision] j j := by
  -- Proof comment: the strict box inequalities keep both reciprocal-square terms positive, so
  -- their diagonal sum in `Λ₀` is strictly positive.
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda0_eq_diagonal]
  simp only [Matrix.diagonal_apply]
  rcases strictBarrierPoint_mem_box problem decision j with ⟨hα, hβ⟩
  have hleft : 0 < 1 / (decision.1.point j - problem.α j) ^ (2 : ℕ) := by
    have hbase : 0 < decision.1.point j - problem.α j := sub_pos.mpr hα
    positivity
  have hright : 0 < 1 / (problem.β j - decision.1.point j) ^ (2 : ℕ) := by
    have hbase : 0 < problem.β j - decision.1.point j := sub_pos.mpr hβ
    positivity
  exact add_pos hleft hright

/-- Helper for Theorem 5.4.9.3: the coupling scalar `κ[decision]` is strictly positive on the
strict barrier domain. -/
private theorem newtonSystemKappa_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    0 < κ[decision] := by
  -- Proof comment: `κ[decision] = (ξ - Στ)⁻²`, and the strict barrier domain keeps the gap
  -- `ξ - Στ` strictly positive.
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemKappa_eq]
  exact one_div_pos.mpr (pow_pos (strictBarrierGap_pos problem decision) 2)

/-- Helper for Theorem 5.4.9.3: differentiating `-log ∘ σ` at a point with positive value
rewrites the derivative into the usual scalar quotient form. -/
private theorem negLogCompDerivAt
    {σ : ℝ → ℝ} {x value sigma' : ℝ}
    (hσ : HasDerivAt σ sigma' x)
    (hvalue : σ x = value)
    (hpos : 0 < value) :
    deriv (fun a : ℝ ↦ -Real.log (σ a)) x = -sigma' / value := by
  -- Proof comment: compose the derivative of `-log` at the positive base value with the
  -- derivative of `σ`, then rewrite the resulting product as a quotient.
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

/-- Helper for Theorem 5.4.9.3: points of `interior Q₄[p]` have positive time coordinate. -/
private theorem separableLogBarrierF4_time_pos
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    0 < τ := by
  -- Proof comment: interior membership is the strict epigraph inequality `|s|^p < τ`, and the
  -- left-hand side is always nonnegative.
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have htpow : |s| ^ p < τ :=
    (mem_interior_constrainedEpigraph_abs_pow_iff (p := p) hp0).mp hmem
  exact lt_of_le_of_lt (Real.rpow_nonneg (abs_nonneg s) p) htpow

/-- Helper for Theorem 5.4.9.3: points of `interior Q₄[p]` satisfy the strict barrier gap
`τ^(2 / p) - s² > 0`. -/
private theorem separableLogBarrierF4_gap_pos
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ) := by
  -- Proof comment: first rewrite the epigraph inequality as `|s| < τ^(1 / p)`, then square both
  -- sides and convert the square of the `rpow` term back to `τ^(2 / p)`.
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have htpow : |s| ^ p < τ :=
    (mem_interior_constrainedEpigraph_abs_pow_iff (p := p) hp0).mp hmem
  have habs_lt : |s| < Real.rpow τ (1 / p) := by
    simpa [one_div] using
      (Real.lt_rpow_inv_iff_of_pos (abs_nonneg s) (le_of_lt hτ) hp0).2 htpow
  have hroot_pos : 0 < Real.rpow τ (1 / p) := Real.rpow_pos_of_pos hτ _
  have hsq_abs_lt : |s| ^ (2 : ℕ) < (Real.rpow τ (1 / p)) ^ (2 : ℕ) := by
    nlinarith [habs_lt, abs_nonneg s, hroot_pos]
  have hsq_lt : s ^ (2 : ℕ) < (Real.rpow τ (1 / p)) ^ (2 : ℕ) := by
    simpa [sq_abs] using hsq_abs_lt
  have hpow_two :
      (Real.rpow τ (1 / p)) ^ (2 : ℕ) = Real.rpow τ (2 / p) := by
    calc
      (Real.rpow τ (1 / p)) ^ (2 : ℕ) = Real.rpow τ ((1 / p) * 2) := by
        symm
        simpa using (Real.rpow_mul_natCast (le_of_lt hτ) (1 / p) 2)
      _ = Real.rpow τ (2 / p) := by
        field_simp [hp0.ne']
  linarith

/-- Helper for Theorem 5.4.9.3: the frozen-`τ` gradient of the scalar barrier `F₄` is the
explicit rational function `2 s / (τ^(2 / p) - s²)`. -/
private theorem separableLogBarrierF4_auxiliaryGradient_formula
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    auxiliaryGradient (separableLogBarrierF4 p) s τ =
      2 * s / (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
  -- Route correction: instead of reopening the full ambient Hessian packaging, differentiate the
  -- frozen-`τ` scalar slice directly and package the logarithmic chain rule through
  -- `negLogCompDerivAt`.
  have hgap : 0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ) :=
    separableLogBarrierF4_gap_pos hp hmem
  have hσ :
      HasDerivAt
        (fun y : ℝ ↦ Real.rpow τ (2 / p) - y ^ (2 : ℕ))
        (-(2 * s))
        s := by
    -- Proof comment: the gap slice is a constant minus a square, so its derivative is `-2 s`.
    simpa [two_mul] using
      (hasDerivAt_pow 2 s).const_sub (Real.rpow τ (2 / p))
  rw [auxiliaryGradient, gradient_eq_deriv']
  calc
    deriv (fun y : ℝ ↦ separableLogBarrierF4 p (y, τ)) s
        = deriv
            (fun y : ℝ ↦
              -Real.log τ + -Real.log (Real.rpow τ (2 / p) - y ^ (2 : ℕ)))
            s := by
              simp [separableLogBarrierF4_apply, sub_eq_add_neg]
    _ = deriv (fun y : ℝ ↦ -Real.log (Real.rpow τ (2 / p) - y ^ (2 : ℕ))) s := by
          rw [deriv_const_add]
    _ = -(-(2 * s)) / (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
          exact
            negLogCompDerivAt
              (σ := fun y : ℝ ↦ Real.rpow τ (2 / p) - y ^ (2 : ℕ))
              (x := s)
              (value := Real.rpow τ (2 / p) - s ^ (2 : ℕ))
              (sigma' := -(2 * s))
              hσ
              rfl
              hgap
    _ = 2 * s / (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
          ring

/-- Helper for Theorem 5.4.9.3: the frozen-`s` time derivative of the scalar barrier `F₄` is the
sum of the explicit `-1 / τ` term and the time derivative of the gap logarithm. -/
private theorem separableLogBarrierF4_auxiliaryTimeDerivative_formula
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    auxiliaryTimeDerivative (separableLogBarrierF4 p) s τ =
      -(1 / τ) -
        ((2 / p) * Real.rpow τ (2 / p - 1)) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have hgap : 0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ) :=
    separableLogBarrierF4_gap_pos hp hmem
  have hσ :
      HasDerivAt
        (fun t' : ℝ ↦ Real.rpow t' (2 / p) - s ^ (2 : ℕ))
        ((2 / p) * Real.rpow τ (2 / p - 1))
        τ := by
    -- Proof comment: the frozen-`s` gap derivative is just the derivative of `τ ↦ τ^(2 / p)`.
    simpa using
      ((Real.hasDerivAt_rpow_const
          (x := τ)
          (p := 2 / p)
          (Or.inl hτ.ne')).sub_const (s ^ (2 : ℕ)))
  have hlogτ' :
      HasDerivAt (fun t' : ℝ ↦ -Real.log t') (-(1 / τ)) τ := by
    simpa [one_div] using (Real.hasDerivAt_log hτ.ne').neg
  have hgapLogBase :
      HasDerivAt
        (fun y : ℝ ↦ -Real.log y)
        (-((Real.rpow τ (2 / p) - s ^ (2 : ℕ))⁻¹))
        (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
    simpa using (Real.hasDerivAt_log hgap.ne').neg
  have hlogGap' :
      HasDerivAt
        (fun t' : ℝ ↦ -Real.log (Real.rpow t' (2 / p) - s ^ (2 : ℕ)))
        (-((2 / p) * Real.rpow τ (2 / p - 1)) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)))
        τ := by
    simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hgapLogBase.comp τ hσ
  rw [auxiliaryTimeDerivative]
  calc
    deriv (fun t' : ℝ ↦ separableLogBarrierF4 p (s, t')) τ
        = deriv
            (fun t' : ℝ ↦
              -Real.log t' + -Real.log (Real.rpow t' (2 / p) - s ^ (2 : ℕ)))
            τ := by
              simp [separableLogBarrierF4_apply, sub_eq_add_neg]
    _ = -(1 / τ) +
          (-((2 / p) * Real.rpow τ (2 / p - 1)) /
            (Real.rpow τ (2 / p) - s ^ (2 : ℕ))) := by
          exact (hlogτ'.add hlogGap').deriv
    _ = -(1 / τ) -
          ((2 / p) * Real.rpow τ (2 / p - 1)) /
            (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) := by
          ring

/-- Helper for Theorem 5.4.9.3: the `yy`-block of the scalar barrier `F₄` has the explicit
closed form used in the reduced Newton-system Schur complement. -/
private theorem separableLogBarrierF4_spaceBlock_formula
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    ((h₁₁[(separableLogBarrierF4 p)](s, τ)) 1) =
      2 * (Real.rpow τ (2 / p) + s ^ (2 : ℕ)) /
        (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
  let c : ℝ := Real.rpow τ (2 / p)
  let q : ℝ → ℝ := fun y' : ℝ ↦ 2 * y' / (c - y' ^ (2 : ℕ))
  have hslice :
      {y' : ℝ | (y', τ) ∈ interior Q₄[p]} ∈ nhds s := by
    -- Proof comment: interior membership is open, so the frozen-`τ` slice stays in the domain
    -- near `s`.
    simpa using
      (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_interior hmem)
  have hEventually :
      (fun y' : ℝ ↦ auxiliaryGradient (separableLogBarrierF4 p) y' τ) =ᶠ[nhds s] q := by
    -- Proof comment: near `s`, the explicit frozen-`τ` gradient formula is valid pointwise.
    filter_upwards [hslice] with y hy
    simpa [q, c] using
      separableLogBarrierF4_auxiliaryGradient_formula
        (p := p)
        (s := y)
        (τ := τ)
        hp
        hy
  have hgap : 0 < c - s ^ (2 : ℕ) := by
    simpa [c] using separableLogBarrierF4_gap_pos hp hmem
  have hnum :
      HasDerivAt (fun y' : ℝ ↦ 2 * y') 2 s := by
    simpa [two_mul] using HasDerivAt.const_mul 2 (hasDerivAt_id s)
  have hden :
      HasDerivAt (fun y' : ℝ ↦ c - y' ^ (2 : ℕ)) (-(2 * s)) s := by
    simpa [c, two_mul] using (hasDerivAt_pow 2 s).const_sub c
  have hq :
      HasDerivAt q
        ((2 * (c - s ^ (2 : ℕ)) - (2 * s) * (-(2 * s))) / (c - s ^ (2 : ℕ)) ^ (2 : ℕ))
        s := by
    -- Proof comment: differentiate the explicit quotient once using the scalar quotient rule.
    simpa [q] using hnum.div hden hgap.ne'
  rw [secondOrderDerivativeBlock11_def, fderiv_apply_one_eq_deriv]
  calc
    deriv (fun y' : ℝ ↦ auxiliaryGradient (separableLogBarrierF4 p) y' τ) s
        = deriv q s := hEventually.deriv_eq
    _ = (2 * (c - s ^ (2 : ℕ)) - (2 * s) * (-(2 * s))) / (c - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          exact hq.deriv
    _ = 2 * (Real.rpow τ (2 / p) + s ^ (2 : ℕ)) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          field_simp [c, hgap.ne']
          ring

/-- Helper for Theorem 5.4.9.3: the mixed `yt`-block of the scalar barrier `F₄` has the explicit
closed form used in the Schur complement. -/
private theorem separableLogBarrierF4_mixedBlock_formula
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    h₁₂[(separableLogBarrierF4 p)](s, τ) =
      -(2 * s * (2 / p) * Real.rpow τ (2 / p - 1)) /
        (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
  let q : ℝ → ℝ :=
    fun t' : ℝ ↦ 2 * s / (Real.rpow t' (2 / p) - s ^ (2 : ℕ))
  have hslice :
      {t' : ℝ | (s, t') ∈ interior Q₄[p]} ∈ nhds τ := by
    -- Proof comment: openness of the scalar barrier domain lets us differentiate the explicit
    -- time-slice formula near `τ`.
    simpa using
      (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_interior hmem)
  have hEventually :
      (fun t' : ℝ ↦ auxiliaryGradient (separableLogBarrierF4 p) s t') =ᶠ[nhds τ] q := by
    filter_upwards [hslice] with t' ht'
    simpa [q] using
      separableLogBarrierF4_auxiliaryGradient_formula
        (p := p)
        (s := s)
        (τ := t')
        hp
        ht'
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have hgap : 0 < Real.rpow τ (2 / p) - s ^ (2 : ℕ) :=
    separableLogBarrierF4_gap_pos hp hmem
  have hnum : HasDerivAt (fun _ : ℝ ↦ 2 * s) 0 τ := by
    simpa using (hasDerivAt_const τ (c := 2 * s))
  have hden :
      HasDerivAt
        (fun t' : ℝ ↦ Real.rpow t' (2 / p) - s ^ (2 : ℕ))
        ((2 / p) * Real.rpow τ (2 / p - 1))
        τ := by
    simpa using
      ((Real.hasDerivAt_rpow_const
          (x := τ)
          (p := 2 / p)
          (Or.inl hτ.ne')).sub_const (s ^ (2 : ℕ)))
  have hq :
      HasDerivAt q
        ((0 * (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) -
            (2 * s) * ((2 / p) * Real.rpow τ (2 / p - 1))) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ))
        τ := by
    -- Proof comment: differentiate the explicit `2 s / gap(τ)` quotient once in time.
    simpa [q] using hnum.div hden hgap.ne'
  rw [secondOrderDerivativeBlock12_def]
  calc
    deriv (fun t' : ℝ ↦ auxiliaryGradient (separableLogBarrierF4 p) s t') τ
        = deriv q τ := hEventually.deriv_eq
    _ = (0 * (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) -
            (2 * s) * ((2 / p) * Real.rpow τ (2 / p - 1))) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          exact hq.deriv
    _ = -(2 * s * (2 / p) * Real.rpow τ (2 / p - 1)) /
          (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          ring

/-- Helper for Theorem 5.4.9.3: the `tt`-block of the scalar barrier `F₄` has the explicit
closed form used in the reduced Newton-system Schur complement. -/
private theorem separableLogBarrierF4_timeBlock_formula
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    h₂₂[(separableLogBarrierF4 p)](s, τ) =
      1 / τ ^ (2 : ℕ) +
        ((2 / p) * Real.rpow τ (2 / p - 2) *
          (Real.rpow τ (2 / p) + (2 / p - 1) * s ^ (2 : ℕ))) /
        (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
  let a : ℝ := 2 / p
  let q : ℝ → ℝ :=
    fun t' : ℝ ↦
      -(1 / t') - (a * Real.rpow t' (a - 1)) / (Real.rpow t' a - s ^ (2 : ℕ))
  have hslice :
      {t' : ℝ | (s, t') ∈ interior Q₄[p]} ∈ nhds τ := by
    -- Proof comment: openness of the scalar barrier domain lets us differentiate the explicit
    -- frozen-`s` time-slice formula near `τ`.
    simpa using
      (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_interior hmem)
  have hEventually :
      (fun t' : ℝ ↦ auxiliaryTimeDerivative (separableLogBarrierF4 p) s t') =ᶠ[nhds τ] q := by
    -- Proof comment: near `τ`, the already-established first time derivative has the explicit
    -- rational form `q`.
    filter_upwards [hslice] with t' ht'
    simpa [q, a] using
      separableLogBarrierF4_auxiliaryTimeDerivative_formula
        (p := p)
        (s := s)
        (τ := t')
        hp
        ht'
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have hgap : 0 < Real.rpow τ a - s ^ (2 : ℕ) := by
    simpa [a] using separableLogBarrierF4_gap_pos hp hmem
  have hinv :
      HasDerivAt (fun t' : ℝ ↦ -(1 / t')) (1 / τ ^ (2 : ℕ)) τ := by
    -- Proof comment: differentiating the explicit `-log τ` contribution gives the `1 / τ^2`
    -- term in the `tt` block.
    simpa [one_div, pow_two] using (hasDerivAt_inv hτ.ne').neg
  have hnum :
      HasDerivAt
        (fun t' : ℝ ↦ a * Real.rpow t' (a - 1))
        (a * ((a - 1) * Real.rpow τ ((a - 1) - 1)))
        τ := by
    -- Proof comment: the numerator is a fixed scalar multiple of `τ ↦ τ^(a-1)`.
    simpa [a, mul_assoc, sub_eq_add_neg] using
      HasDerivAt.const_mul a
        (Real.hasDerivAt_rpow_const (x := τ) (p := a - 1) (Or.inl hτ.ne'))
  have hden :
      HasDerivAt
        (fun t' : ℝ ↦ Real.rpow t' a - s ^ (2 : ℕ))
        (a * Real.rpow τ (a - 1))
        τ := by
    -- Proof comment: the denominator is the positive gap slice `τ^a - s^2`.
    simpa [a, sub_eq_add_neg] using
      ((Real.hasDerivAt_rpow_const
          (x := τ)
          (p := a)
          (Or.inl hτ.ne')).sub_const (s ^ (2 : ℕ)))
  have hquot :
      HasDerivAt
        (fun t' : ℝ ↦ (a * Real.rpow t' (a - 1)) / (Real.rpow t' a - s ^ (2 : ℕ)))
        (((a * ((a - 1) * Real.rpow τ ((a - 1) - 1))) * (Real.rpow τ a - s ^ (2 : ℕ)) -
            (a * Real.rpow τ (a - 1)) * (a * Real.rpow τ (a - 1))) /
          (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ))
        τ := by
    -- Proof comment: differentiate the rational gap term once more by the scalar quotient rule.
    simpa using hnum.div hden hgap.ne'
  have hrpow_sq :
      Real.rpow τ (a - 1) * Real.rpow τ (a - 1) =
        Real.rpow τ (a - 2) * Real.rpow τ a := by
    -- Proof comment: factor the square `τ^(a-1) * τ^(a-1)` into the normal form used by the
    -- final Schur-complement expression.
    calc
      Real.rpow τ (a - 1) * Real.rpow τ (a - 1)
          = Real.rpow τ ((a - 1) + (a - 1)) := by
              simpa [sub_eq_add_neg] using (Real.rpow_add hτ (a - 1) (a - 1)).symm
      _ = Real.rpow τ ((a - 2) + a) := by ring
      _ = Real.rpow τ (a - 2) * Real.rpow τ a := by
            simpa [sub_eq_add_neg] using (Real.rpow_add hτ (a - 2) a)
  have hsquare :
      (a * Real.rpow τ (a - 1)) * (a * Real.rpow τ (a - 1)) =
        a * a * (Real.rpow τ (a - 2) * Real.rpow τ a) := by
    calc
      (a * Real.rpow τ (a - 1)) * (a * Real.rpow τ (a - 1))
          = a * a * (Real.rpow τ (a - 1) * Real.rpow τ (a - 1)) := by ring
      _ = a * a * (Real.rpow τ (a - 2) * Real.rpow τ a) := by rw [hrpow_sq]
  rw [secondOrderDerivativeBlock22_def]
  calc
    deriv (fun t' : ℝ ↦ auxiliaryTimeDerivative (separableLogBarrierF4 p) s t') τ
        = deriv q τ := hEventually.deriv_eq
    _ = 1 / τ ^ (2 : ℕ) -
          (((a * ((a - 1) * Real.rpow τ ((a - 1) - 1))) * (Real.rpow τ a - s ^ (2 : ℕ)) -
              (a * Real.rpow τ (a - 1)) * (a * Real.rpow τ (a - 1))) /
            (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ)) := by
          exact (hinv.sub hquot).deriv
    _ = 1 / τ ^ (2 : ℕ) +
          (a * Real.rpow τ (a - 2) * (Real.rpow τ a + (a - 1) * s ^ (2 : ℕ))) /
            (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          have hexp : (a - 1) - 1 = a - 2 := by ring
          rw [hexp, hsquare]
          have hnumerator :
              -((a * ((a - 1) * Real.rpow τ (a - 2))) * (Real.rpow τ a - s ^ (2 : ℕ)) -
                  a * a * (Real.rpow τ (a - 2) * Real.rpow τ a)) =
                a * Real.rpow τ (a - 2) * (Real.rpow τ a + (a - 1) * s ^ (2 : ℕ)) := by
            ring
          calc
            1 / τ ^ (2 : ℕ) -
                (((a * ((a - 1) * Real.rpow τ (a - 2))) * (Real.rpow τ a - s ^ (2 : ℕ)) -
                    a * a * (Real.rpow τ (a - 2) * Real.rpow τ a)) /
                  (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ))
                = 1 / τ ^ (2 : ℕ) +
                    (-((a * ((a - 1) * Real.rpow τ (a - 2))) *
                        (Real.rpow τ a - s ^ (2 : ℕ)) -
                        a * a * (Real.rpow τ (a - 2) * Real.rpow τ a))) /
                      (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
                    ring
            _ = 1 / τ ^ (2 : ℕ) +
                  (a * Real.rpow τ (a - 2) * (Real.rpow τ a + (a - 1) * s ^ (2 : ℕ))) /
                    (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
                  rw [hnumerator]
    _ = 1 / τ ^ (2 : ℕ) +
          ((2 / p) * Real.rpow τ (2 / p - 2) *
              (Real.rpow τ (2 / p) + (2 / p - 1) * s ^ (2 : ℕ))) /
            (Real.rpow τ (2 / p) - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
          simp [a]

/-- Helper for Theorem 5.4.9.3: composing `-log` with a positive scalar slack slice produces the
expected second iterated derivative at the base point. -/
private theorem negLogCompIteratedDerivTwo
    {σ : ℝ → ℝ} {s delta b : ℝ}
    (hσ3 : ContDiffAt ℝ 3 σ 0)
    (hσ0 : σ 0 = s)
    (hs : 0 < s)
    (hσ_deriv : deriv σ 0 = delta)
    (hσ_second : iteratedDeriv 2 σ 0 = -b) :
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0 =
      b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
  -- Proof comment: apply the scalar second-order chain rule to `log ∘ σ`, then substitute the
  -- explicit logarithm derivatives at the positive base point `s = σ 0`.
  have hlog_cont : ContDiffAt ℝ 3 Real.log (σ 0) := by
    simpa [hσ0] using (Real.contDiffAt_log.2 hs.ne')
  have hderiv_log : deriv Real.log = fun y : ℝ ↦ y⁻¹ := by
    ext y
    rw [Real.deriv_log]
  have hsecond_log :
      iteratedDeriv 2 Real.log s = -(s ^ (2 : ℕ))⁻¹ := by
    calc
      iteratedDeriv 2 Real.log s = deriv (deriv Real.log) s := by
        simp [iteratedDeriv_succ]
      _ = deriv (fun y : ℝ ↦ y⁻¹) s := by
        rw [hderiv_log]
      _ = -(s ^ (2 : ℕ))⁻¹ := by
        rw [deriv_inv]
  have hcomp_two :
      iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 =
        iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
          deriv Real.log (σ 0) * iteratedDeriv 2 σ 0 := by
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (g := Real.log)
        (f := σ)
        (x := 0)
        (hlog_cont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
        (hσ3.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)))
  calc
    iteratedDeriv 2 (fun a : ℝ ↦ -Real.log (σ a)) 0
        = -iteratedDeriv 2 (fun a : ℝ ↦ Real.log (σ a)) 0 := by
            simp
    _ = -(iteratedDeriv 2 Real.log (σ 0) * deriv σ 0 ^ (2 : ℕ) +
            deriv Real.log (σ 0) * iteratedDeriv 2 σ 0) := by
          rw [hcomp_two]
    _ = -(-(s ^ (2 : ℕ))⁻¹ * delta ^ (2 : ℕ) + s⁻¹ * (-b)) := by
          rw [hσ0, hsecond_log, hderiv_log, hσ_deriv, hσ_second]
    _ = b / s + delta ^ (2 : ℕ) / s ^ (2 : ℕ) := by
          field_simp [hs.ne']
          ring

/-- Helper for Theorem 5.4.9.3: the `tt`-block of the scalar barrier `separableLogBarrierF4 p`
dominates the explicit `-log τ` contribution `1 / τ^2` on `interior Q₄[p]`. -/
private theorem separableLogBarrierF4_timeBlock_lower_bound
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    1 / τ ^ (2 : ℕ) ≤ h₂₂[(separableLogBarrierF4 p)](s, τ) := by
  let a : ℝ := 2 / p
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have hgap : 0 < Real.rpow τ a - s ^ (2 : ℕ) := by
    simpa [a] using separableLogBarrierF4_gap_pos hp hmem
  have ha_pos : 0 < a := by
    -- Proof comment: `a = 2 / p` is positive because `p ≥ 1`.
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    dsimp [a]
    exact div_pos two_pos hp0
  have hfactor_nonneg :
      0 ≤ Real.rpow τ a + (a - 1) * s ^ (2 : ℕ) := by
    -- Proof comment: compare the factor with the already-positive gap `τ^a - s^2`; the
    -- difference is the nonnegative correction `a * s^2`.
    have hsq_nonneg : 0 ≤ s ^ (2 : ℕ) := sq_nonneg s
    nlinarith
  have hterm_nonneg :
      0 ≤
        (a * Real.rpow τ (a - 2) * (Real.rpow τ a + (a - 1) * s ^ (2 : ℕ))) /
          (Real.rpow τ a - s ^ (2 : ℕ)) ^ (2 : ℕ) := by
    -- Proof comment: every factor in the explicit second summand is nonnegative on the strict
    -- barrier domain.
    refine div_nonneg ?_ (pow_two_nonneg _)
    exact mul_nonneg (mul_nonneg ha_pos.le (Real.rpow_nonneg (le_of_lt hτ) _)) hfactor_nonneg
  rw [separableLogBarrierF4_timeBlock_formula (p := p) (s := s) (τ := τ) hp hmem]
  linarith

/-- Helper for Theorem 5.4.9.3: the normalized Schur-complement numerator is nonnegative on the
admissible scalar parameter range `0 < a ≤ 2` and `0 ≤ r < 1`. -/
private theorem schurComplementNumerator_nonneg
    {a r : ℝ} (ha_pos : 0 < a) (ha_le : a ≤ 2) (hr_nonneg : 0 ≤ r) (hr_lt : r < 1) :
    0 ≤ (1 - r) * (1 + r + a) + a * (2 - a) * r := by
  -- Proof comment: every factor in the two normalized summands is nonnegative on the admissible
  -- range, so the Schur-complement numerator is nonnegative termwise.
  have hfirst : 0 ≤ (1 - r) * (1 + r + a) := by
    have hleft : 0 ≤ 1 - r := by linarith
    have hright : 0 ≤ 1 + r + a := by linarith
    exact mul_nonneg hleft hright
  have hsecond : 0 ≤ a * (2 - a) * r := by
    have htwo_sub : 0 ≤ 2 - a := by linarith
    exact mul_nonneg (mul_nonneg ha_pos.le htwo_sub) hr_nonneg
  linarith

/-- Helper for Theorem 5.4.9.3: every diagonal entry of the Newton-system block `D[decision]` is
strictly positive. -/
private theorem newtonSystemD_diag_pos
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    0 < D[decision] i i := by
  -- Proof comment: the diagonal entry is the scalar `tt`-block `h₂₂(sᵢ, τᵢ)`, and the strict
  -- barrier-domain membership keeps the explicit `1 / τᵢ^2` lower bound positive.
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD_eq_diagonal]
  simp only [Matrix.diagonal_apply]
  have hlower :=
    separableLogBarrierF4_timeBlock_lower_bound
      (p := (problem.p : ℝ))
      (s := decision.newtonSystemResidual i)
      (τ := decision.1.residualSlack i)
      problem.one_le_p
      (newtonSystemResidual_mem_f4Interior problem decision i)
  have hτ : 0 < decision.1.residualSlack i :=
    strictBarrierResidualSlack_pos problem decision i
  have hbase : 0 < 1 / (decision.1.residualSlack i) ^ (2 : ℕ) := by
    positivity
  exact lt_of_lt_of_le hbase hlower

/-- Helper for Theorem 5.4.9.3: the scalar Schur complement
`h₁₁ - h₁₂² / h₂₂` of `separableLogBarrierF4 p` is nonnegative on `interior Q₄[p]`. -/
private theorem separableLogBarrierF4_schurComplement_nonneg
    {p s τ : ℝ} (hp : 1 ≤ p) (hmem : (s, τ) ∈ interior Q₄[p]) :
    0 ≤ ((h₁₁[(separableLogBarrierF4 p)](s, τ)) 1) -
      (h₁₂[(separableLogBarrierF4 p)](s, τ)) ^ (2 : ℕ) /
        h₂₂[(separableLogBarrierF4 p)](s, τ) := by
  let a : ℝ := 2 / p
  let u : ℝ := Real.rpow τ a
  let x : ℝ := s ^ (2 : ℕ)
  let H11 : ℝ := ((h₁₁[(separableLogBarrierF4 p)](s, τ)) 1)
  let H12 : ℝ := h₁₂[(separableLogBarrierF4 p)](s, τ)
  let H22 : ℝ := h₂₂[(separableLogBarrierF4 p)](s, τ)
  have hτ : 0 < τ := separableLogBarrierF4_time_pos hp hmem
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ha_pos : 0 < a := by
    -- Proof comment: `a = 2 / p` stays positive on the source range `p ≥ 1`.
    dsimp [a]
    exact div_pos two_pos hp0
  have ha_le : a ≤ 2 := by
    -- Proof comment: `a = 2 / p` is at most `2` because `p ≥ 1`.
    dsimp [a]
    field_simp [hp0.ne']
    nlinarith
  have hu_pos : 0 < u := by
    -- Proof comment: the normalized scale `u = τ^a` is positive because `τ > 0`.
    dsimp [u]
    exact Real.rpow_pos_of_pos hτ a
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact sq_nonneg s
  have hgap : 0 < u - x := by
    simpa [a, u, x] using separableLogBarrierF4_gap_pos hp hmem
  have hpow_sub_one : Real.rpow τ (a - 1) = u / τ := by
    -- Proof comment: rewrite the mixed block exponent `a - 1` back into the normalized scale
    -- `u = τ^a`.
    apply (eq_div_iff hτ.ne').2
    calc
      Real.rpow τ (a - 1) * τ
          = Real.rpow τ ((a - 1) + 1) := by
            simpa [sub_eq_add_neg] using (Real.rpow_add hτ (a - 1) (1 : ℝ)).symm
      _ = u := by
            dsimp [u]
            congr 1
            ring
  have hpow_sub_two : Real.rpow τ (a - 2) = u / τ ^ (2 : ℕ) := by
    -- Proof comment: the time-block exponent `a - 2` likewise reduces to `u / τ²`.
    apply (eq_div_iff (pow_ne_zero 2 hτ.ne')).2
    calc
      Real.rpow τ (a - 2) * τ ^ (2 : ℕ)
          = Real.rpow τ ((a - 2) + 2) := by
            simpa [sub_eq_add_neg] using (Real.rpow_add hτ (a - 2) (2 : ℝ)).symm
      _ = u := by
            dsimp [u]
            congr 1
            ring
  have hH22_pos : 0 < H22 := by
    -- Proof comment: the `tt` block dominates the explicit `1 / τ²` contribution.
    dsimp [H22]
    have hbase : 0 < 1 / τ ^ (2 : ℕ) := by positivity
    exact lt_of_lt_of_le hbase (separableLogBarrierF4_timeBlock_lower_bound hp hmem)
  have hmain_nonneg :
      0 ≤ (u - x) * (u + x + a * u) + a * (2 - a) * u * x := by
    -- Proof comment: after normalizing by `u = τ^a` and `x = s²`, the Schur numerator splits
    -- into two manifestly nonnegative summands.
    have hgap_nonneg : 0 ≤ u - x := le_of_lt hgap
    have hsum_pos : 0 < u + x + a * u := by positivity
    have hterm1 : 0 ≤ (u - x) * (u + x + a * u) := by
      exact mul_nonneg hgap_nonneg hsum_pos.le
    have htwo_sub_nonneg : 0 ≤ 2 - a := by linarith
    have hterm2 : 0 ≤ a * (2 - a) * u * x := by
      exact mul_nonneg (mul_nonneg (mul_nonneg ha_pos.le htwo_sub_nonneg) hu_pos.le) hx_nonneg
    linarith
  have hnumerator_nonneg : 0 ≤ H11 * H22 - H12 ^ (2 : ℕ) := by
    -- Proof comment: substitute the explicit `h₁₁`, `h₁₂`, `h₂₂` formulas and clear the
    -- positive denominators to expose the normalized numerator above.
    change 0 ≤
      ((h₁₁[(separableLogBarrierF4 p)](s, τ)) 1) * h₂₂[(separableLogBarrierF4 p)](s, τ) -
        (h₁₂[(separableLogBarrierF4 p)](s, τ)) ^ (2 : ℕ)
    rw [separableLogBarrierF4_spaceBlock_formula (p := p) (s := s) (τ := τ) hp hmem]
    rw [separableLogBarrierF4_mixedBlock_formula (p := p) (s := s) (τ := τ) hp hmem]
    rw [separableLogBarrierF4_timeBlock_formula (p := p) (s := s) (τ := τ) hp hmem]
    rw [hpow_sub_one, hpow_sub_two]
    have hden_pos : 0 < τ ^ (2 : ℕ) * (u - x) ^ (3 : ℕ) := by positivity
    have hnormalized :
        2 * (u + x) / (u - x) ^ (2 : ℕ) *
            (1 / τ ^ (2 : ℕ) +
              (a * (u / τ ^ (2 : ℕ)) * (u + (a - 1) * x)) / (u - x) ^ (2 : ℕ)) -
          (-(2 * s * a * (u / τ)) / (u - x) ^ (2 : ℕ)) ^ (2 : ℕ) =
            (2 * ((u - x) * (u + x + a * u) + a * (2 - a) * u * x)) /
              (τ ^ (2 : ℕ) * (u - x) ^ (3 : ℕ)) := by
      field_simp [hτ.ne', hgap.ne']
      ring
    rw [hnormalized]
    exact div_nonneg (by positivity) hden_pos.le
  apply sub_nonneg.mpr
  have hineq : H12 ^ (2 : ℕ) ≤ H11 * H22 := by
    linarith
  simpa [H11, H12, H22] using (div_le_iff₀ hH22_pos).2 hineq

/-- Helper for Theorem 5.4.9.3: the Schur-complement weight `μᵢ = Λ₁ᵢᵢ - Λ₂ᵢᵢ² / Dᵢᵢ` used to
eliminate the diagonal `τ`-block of the Newton system. -/
private def newtonSystemReducedWeight
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    Fin m → ℝ :=
  fun i ↦ Λ₁[decision] i i - (Λ₂[decision] i i) ^ (2 : ℕ) / D[decision] i i

/-- Helper for Theorem 5.4.9.3: the reduced primal matrix obtained after eliminating `Δτ` from
the displayed Newton equations. -/
private def newtonSystemReducedPrimalMatrix
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    Matrix (Fin n) (Fin n) ℝ :=
  Λ₀[decision] +
    A[problem] * Matrix.diagonal (newtonSystemReducedWeight problem decision) * A[problem]ᵀ

/-- Helper for Theorem 5.4.9.3: the Schur-complement weight `μᵢ` is nonnegative on the strict
barrier domain. -/
private theorem newtonSystemReducedWeight_nonneg
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (i : Fin m) :
    0 ≤ newtonSystemReducedWeight problem decision i := by
  -- Proof comment: the reduced weight is exactly the scalar Schur complement of the local `F₄`
  -- Hessian block at `(sᵢ, τᵢ)`, so the previously established scalar inequality applies.
  rw [newtonSystemReducedWeight]
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda1_eq_diagonal]
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda2_eq_diagonal]
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD_eq_diagonal]
  simp only [Matrix.diagonal_apply]
  exact
    separableLogBarrierF4_schurComplement_nonneg
      (p := (problem.p : ℝ))
      (s := decision.newtonSystemResidual i)
      (τ := decision.1.residualSlack i)
      problem.one_le_p
      (newtonSystemResidual_mem_f4Interior problem decision i)

/-- Helper for Theorem 5.4.9.3: expanding the reduced primal matrix recovers the Schur-complement
matrix `Λ₀ + A diag(μ) Aᵀ`. -/
@[simp] private theorem newtonSystemReducedPrimalMatrix_eq
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    newtonSystemReducedPrimalMatrix problem decision =
      Λ₀[decision] +
        A[problem] * Matrix.diagonal (newtonSystemReducedWeight problem decision) *
          A[problem]ᵀ :=
  rfl

/-- Helper for Theorem 5.4.9.3: applying the reduced primal matrix expands to the canonical
matrix-vector Schur-complement form. -/
@[simp] private theorem newtonSystemReducedPrimalMatrix_mulVec
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (deltaX : EuclideanSpace ℝ (Fin n)) :
    Matrix.mulVec (newtonSystemReducedPrimalMatrix problem decision) deltaX =
      Matrix.mulVec Λ₀[decision] deltaX +
        Matrix.mulVec A[problem]
          (Matrix.mulVec (Matrix.diagonal (newtonSystemReducedWeight problem decision))
            (A[problem]ᵀ.mulVec deltaX)) := by
  -- Proof comment: expand the reduced matrix once and normalize the resulting `A diag(μ) Aᵀ`
  -- term with the standard matrix-vector associativity lemmas.
  rw [newtonSystemReducedPrimalMatrix_eq, Matrix.add_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Matrix.mulVec_mulVec]
  simp [Matrix.mul_assoc]

/-- Helper for Theorem 5.4.9.3: the reduced primal Schur-complement matrix is positive definite,
so the reduced `Δx` equation admits an inverse-matrix solve. -/
private theorem newtonSystemReducedPrimalMatrix_posDef
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    (newtonSystemReducedPrimalMatrix problem decision).PosDef := by
  -- Proof comment: `Λ₀` is diagonal positive definite, and the congruence term
  -- `A diag(μ) Aᵀ` is positive semidefinite because each reduced weight `μᵢ` is nonnegative.
  have hLambda0 :
      (Λ₀[decision] : Matrix (Fin n) (Fin n) ℝ).PosDef := by
    rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda0_eq_diagonal]
    refine Matrix.PosDef.diagonal ?_
    intro j
    simpa [Matrix.diagonal_apply] using newtonSystemLambda0_diag_pos problem decision j
  have hDiagonal :
      (Matrix.diagonal (newtonSystemReducedWeight problem decision) :
        Matrix (Fin m) (Fin m) ℝ).PosSemidef := by
    exact
      Matrix.PosSemidef.diagonal fun i ↦
        newtonSystemReducedWeight_nonneg problem decision i
  have hCongruence :
      (A[problem] * Matrix.diagonal (newtonSystemReducedWeight problem decision) * A[problem]ᵀ :
        Matrix (Fin n) (Fin n) ℝ).PosSemidef := by
    simpa using hDiagonal.mul_mul_conjTranspose_same (A[problem])
  rw [newtonSystemReducedPrimalMatrix_eq]
  exact hLambda0.add_posSemidef hCongruence

/-- Helper for Theorem 5.4.9.3: dividing coordinatewise by the positive diagonal matrix
`D[decision]` solves the diagonal `τ`-block equation. -/
private theorem newtonSystemDiagonalSolve
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (rhs : Fin m → ℝ) :
    Matrix.mulVec D[decision] (fun i ↦ rhs i / D[decision] i i) = rhs := by
  -- Proof comment: after expanding `D` as a diagonal matrix, each coordinate is the scalar
  -- identity `Dᵢᵢ * (rhsᵢ / Dᵢᵢ) = rhsᵢ`.
  ext i
  rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD_eq_diagonal]
  simp [Matrix.mulVec_diagonal]
  have hDii :
      0 <
        deriv
          (fun t' ↦
            auxiliaryTimeDerivative
              (separableLogBarrierF4 (problem.p : ℝ))
              (⟪problem.a i, decision.1.point⟫ - problem.b i)
              t')
          (decision.1.residualSlack i) := by
    simpa [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemD_eq_diagonal,
      LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemResidual_apply,
      Matrix.diagonal_apply] using newtonSystemD_diag_pos problem decision i
  field_simp [hDii.ne']

/-- Helper for Theorem 5.4.9.3: every explicit Newton system with right-hand side
`(gradX, gradTau, gradXi, t)` has a solution obtained by Schur-complement elimination of the
`τ/ξ` block. -/
private theorem reducedNewtonSystemSolution
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (gradX : EuclideanSpace ℝ (Fin n))
    (gradTau : Fin m → ℝ)
    (gradXi t : ℝ) :
    ∃ step,
      IsLpBarrierNewtonSystemSolution problem decision gradX gradTau gradXi t step := by
  -- Route correction: solve the displayed equations directly. First solve the reduced `Δx`
  -- system, then recover `Δτ` from the positive diagonal block `D`, and finally recover `Δξ`
  -- from the scalar coupling equation.
  let eta : Fin m → ℝ :=
    fun i ↦ Λ₂[decision] i i * (gradTau i + gradXi + t) / D[decision] i i
  let reducedMatrix := newtonSystemReducedPrimalMatrix problem decision
  have hReducedPosDef : reducedMatrix.PosDef :=
    newtonSystemReducedPrimalMatrix_posDef problem decision
  let _ : Invertible reducedMatrix := hReducedPosDef.isUnit.invertible
  let reducedRhs : Fin n → ℝ := gradX.ofLp - Matrix.mulVec A[problem] eta
  let deltaX : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (reducedMatrix⁻¹ *ᵥ reducedRhs)
  let adjointX : Fin m → ℝ := A[problem]ᵀ.mulVec deltaX
  let deltaTau : Fin m → ℝ :=
    fun i ↦
      (gradTau i + gradXi + t - Λ₂[decision] i i * adjointX i) / D[decision] i i
  let deltaXi : ℝ := (∑ i : Fin m, deltaTau i) + (gradXi + t) / κ[decision]
  have hReducedSolve : Matrix.mulVec reducedMatrix deltaX = reducedRhs := by
    -- Proof comment: the reduced matrix is invertible by positive definiteness, so the chosen
    -- inverse formula solves the reduced `Δx` system exactly.
    dsimp [deltaX]
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have hDiagonalSolve :
      Matrix.mulVec D[decision] deltaTau =
        fun i ↦ gradTau i + gradXi + t - Λ₂[decision] i i * adjointX i := by
    -- Proof comment: this is the coordinatewise diagonal solve for the `τ`-block after fixing
    -- the coupling scalar through the third Newton equation.
    simpa [deltaTau] using
      newtonSystemDiagonalSolve
        problem
        decision
        (fun i ↦ gradTau i + gradXi + t - Λ₂[decision] i i * adjointX i)
  have hXiEquation :
      κ[decision] * deltaXi - κ[decision] * (∑ i : Fin m, deltaTau i) = gradXi + t := by
    -- Proof comment: the scalar equation is solved by construction of `Δξ`.
    have hKappaNe : κ[decision] ≠ 0 := (newtonSystemKappa_pos problem decision).ne'
    calc
      κ[decision] * deltaXi - κ[decision] * (∑ i : Fin m, deltaTau i) =
          κ[decision] * ((gradXi + t) / κ[decision]) := by
            dsimp [deltaXi]
            ring
      _ = gradXi + t := by
            field_simp [hKappaNe]
  have hCoupling :
      κ[decision] * ((∑ i : Fin m, deltaTau i) - deltaXi) = -(gradXi + t) := by
    -- Proof comment: rewrite the coupling scalar using the already-established third equation.
    linarith [hXiEquation]
  have hWeightDecomposition :
      Matrix.mulVec Λ₁[decision] adjointX + Matrix.mulVec Λ₂[decision] deltaTau =
        Matrix.mulVec (Matrix.diagonal (newtonSystemReducedWeight problem decision)) adjointX +
          eta := by
    -- Proof comment: on each coordinate, the diagonal algebra is exactly the Schur-complement
    -- identity `Λ₁ii adjointᵢ + Λ₂ii Δτᵢ = μᵢ adjointᵢ + ηᵢ`.
    ext i
    simp [newtonSystemReducedWeight, eta, deltaTau, Matrix.mulVec_diagonal]
    field_simp [(newtonSystemD_diag_pos problem decision i).ne']
    ring
  have hFirstEquation :
      Matrix.mulVec (lpBarrierNewtonSystemPrimalMatrix problem decision) deltaX +
        Matrix.mulVec A[problem] (Matrix.mulVec Λ₂[decision] deltaTau) =
          gradX := by
    -- Proof comment: substitute the diagonal `Δτ` formula into the first Newton equation and use
    -- the reduced matrix equation `M Δx = gradX - A η`.
    calc
      Matrix.mulVec (lpBarrierNewtonSystemPrimalMatrix problem decision) deltaX +
          Matrix.mulVec A[problem] (Matrix.mulVec Λ₂[decision] deltaTau)
          =
            Matrix.mulVec Λ₀[decision] deltaX +
              Matrix.mulVec A[problem]
                (Matrix.mulVec Λ₁[decision] adjointX + Matrix.mulVec Λ₂[decision] deltaTau) := by
              ext i
              simp [lpBarrierNewtonSystemPrimalMatrix_eq, Matrix.add_mulVec, Matrix.mulVec_mulVec,
                Matrix.mul_assoc, Matrix.mulVec_add, adjointX, add_assoc]
      _ =
            Matrix.mulVec Λ₀[decision] deltaX +
              Matrix.mulVec A[problem]
                (Matrix.mulVec (Matrix.diagonal (newtonSystemReducedWeight problem decision))
                    adjointX + eta) := by
              rw [hWeightDecomposition]
      _ =
            Matrix.mulVec Λ₀[decision] deltaX +
              (Matrix.mulVec A[problem]
                  (Matrix.mulVec (Matrix.diagonal (newtonSystemReducedWeight problem decision))
                    adjointX) +
                Matrix.mulVec A[problem] eta) := by
              rw [Matrix.mulVec_add]
      _ =
            Matrix.mulVec reducedMatrix deltaX +
              Matrix.mulVec A[problem] eta := by
              rw [newtonSystemReducedPrimalMatrix_mulVec]
              dsimp [adjointX]
              simp [add_assoc]
      _ = (gradX - Matrix.mulVec A[problem] eta) + Matrix.mulVec A[problem] eta := by
              rw [hReducedSolve]
      _ = gradX := by
              ext i
              simp
  refine ⟨(deltaX, deltaXi, deltaTau), ?_⟩
  rw [isLpBarrierNewtonSystemSolution_iff]
  refine ⟨?_, ?_, hXiEquation⟩
  · intro i
    simpa [adjointX] using congrFun hFirstEquation i
  · intro i
    -- Proof comment: the diagonal `τ` solve and the scalar coupling identity reconstruct the
    -- second displayed Newton equation coordinatewise.
    have hLambda2 :
        (Matrix.mulVec Λ₂[decision] adjointX) i = Λ₂[decision] i i * adjointX i := by
      rw [LpApproximationBoxProblem.StrictBarrierModelPoint.newtonSystemLambda2_eq_diagonal]
      simp [Matrix.mulVec_diagonal]
    have hD :
        (Matrix.mulVec D[decision] deltaTau) i =
          gradTau i + gradXi + t - Λ₂[decision] i i * adjointX i := by
      simpa using congrFun hDiagonalSolve i
    calc
      (Matrix.mulVec Λ₂[decision] adjointX) i +
          (Matrix.mulVec D[decision] deltaTau) i +
          κ[decision] * ((∑ j : Fin m, deltaTau j) - deltaXi)
          =
            Λ₂[decision] i i * adjointX i +
              (gradTau i + gradXi + t - Λ₂[decision] i i * adjointX i) +
              (-(gradXi + t)) := by
                rw [hLambda2, hD, hCoupling]
      _ = gradTau i := by ring

-- The repaired Newton system keeps the rank-one `τ`-coupling coming from
-- `-log (ξ - ∑ i, τ⁽ⁱ⁾)`, with gap variation `Δξ - ∑ i, Δτ⁽ⁱ⁾`, so the previous
-- coordinatewise elimination of `Δτ` through a shifted diagonal block is no longer the right
-- same-file statement shape.

/-- The Chapter 5 barrier formula `F(x, τ, ξ)` on the lifted carrier `(x, ξ, τ)`, written on the
ambient epigraph space so its gradient coordinates can supply the actual Newton right-hand side at
the current iterate. -/
def lpBarrierNewtonSystemBarrier
    (problem : LpApproximationBoxProblem n m) :
    LpApproximationEpigraphPoint n m → ℝ :=
  fun decision ↦
    (∑ i : Fin m,
      separableLogBarrierF4 (problem.p : ℝ)
        (⟪problem.a i, decision.point⟫ - problem.b i, decision.residualSlack i)) -
      Real.log (decision.objectiveSlack - ∑ i : Fin m, decision.residualSlack i) -
      ∑ j : Fin n,
        (Real.log (decision.point j - problem.α j) +
          Real.log (problem.β j - decision.point j))

/-- The actual barrier-derivative right-hand side of the Newton system at a strict barrier-model
point, packaged in the lifted carrier so its coordinates are `∇ₓ F`, `∂ξ F`, and `∂τ F`. -/
def lpBarrierNewtonSystemGradient
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    LpApproximationEpigraphPoint n m :=
  decision.barrierSecondOrderOracleGradient

section NewtonSystemArithmeticComplexity

variable
  (solver :
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (_ : problem.StrictBarrierModelPoint)
      (_ : ℝ),
      LpApproximationEpigraphPoint n m)
  (arithmeticWork :
    ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
      (_ : problem.StrictBarrierModelPoint)
      (_ : ℝ),
      ℕ)

/-- The arithmetic-work estimate for one execution of a primitive `ℓ_p`-barrier Newton solver. -/
def LpBarrierNewtonStepBound
    (C : ℝ)
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint)
    (t : ℝ) : Prop :=
  let grad := lpBarrierNewtonSystemGradient problem decision
  let step := solver problem decision t
  IsLpBarrierNewtonSystemSolution
      problem decision grad.point grad.residualSlack grad.objectiveSlack t step ∧
    (arithmeticWork problem decision t : ℝ) ≤
      C * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)

/-- A positive constant `C_step` is a valid uniform arithmetic budget for the primitive
`ℓ_p`-barrier Newton solver/work data when every Newton solve for the actual barrier derivatives at
the current iterate lies in
`O(n^3 + m n^2)` with that same constant and returns a genuine solution of the displayed Newton
system. The degenerate display case `n = 0` is handled internally by the bound itself. -/
def HasLpBarrierNewtonSystemArithmeticBudget
    (C_step : ℝ) : Prop :=
  0 < C_step ∧
    ∀ m n : ℕ,
      ∀ (problem : LpApproximationBoxProblem n m)
        (decision : problem.StrictBarrierModelPoint)
        (t : ℝ),
        LpBarrierNewtonStepBound solver arithmeticWork C_step problem decision t

/-- The source-facing per-step arithmetic-complexity owner for the explicit `ℓ_p`-barrier Newton
system. It records the existence of a positive uniform arithmetic budget
`HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step`. -/
def HasLpBarrierNewtonSystemArithmeticComplexityBound : Prop :=
  ∃ C_step : ℝ, HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step

-- Proof sketch: unfold `HasLpBarrierNewtonSystemArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the per-step arithmetic estimate `O(n^3 + m n^2)` on
-- primitive solver/work data.
/-- Unfolding `HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork` recovers
the explicit constant-factor form of the bound `O(n^3 + m n^2)` on primitive Newton solver/work
data. -/
theorem hasLpBarrierNewtonSystemArithmeticComplexityBound_iff
    : HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork ↔
      ∃ C_step : ℝ,
        HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step := by
  rfl

end NewtonSystemArithmeticComplexity

section ShortStepTotalArithmeticComplexity

variable (ε : ℝ)
  (iterationCount : ℕ → ℕ → ℕ)
  (totalArithmeticWork : ℕ → ℕ → ℕ)

/-- The canonical total arithmetic-work model induced by a short-step iteration-count family and
the uniform per-step arithmetic budget `C_step`. -/
def lpBarrierShortStepTotalArithmeticWork
    (C_step : ℝ) : ℕ → ℕ → ℕ :=
  fun m n ↦
    iterationCount m n *
      Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2))

/-- Expanding `lpBarrierShortStepTotalArithmeticWork iterationCount C_step` recovers the product
of the iteration count and the uniform step budget `⌈C_step (n^3 + m n^2)⌉`. -/
theorem lpBarrierShortStepTotalArithmeticWork_apply
    (C_step : ℝ) (m n : ℕ) :
    lpBarrierShortStepTotalArithmeticWork iterationCount C_step m n =
      iterationCount m n *
        Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) :=
  rfl

/-- The source-facing total arithmetic-complexity owner for the short-step `ℓ_p`-barrier method.
It records the source-facing `O(n^2 (m + n)^(3 / 2) log ((m + n) / ε))` bound on primitive total
arithmetic-work data for the full short-step algorithm at a fixed small accuracy `ε ∈ (0, 1)`. A
canonical such family is provided by `lpBarrierShortStepTotalArithmeticWork iterationCount C_step`
once a uniform per-step budget `C_step` is available. -/
class HasLpBarrierShortStepTotalArithmeticComplexityBound : Prop where
  accuracy_mem : ε ∈ Set.Ioo (0 : ℝ) 1
  exists_pos_bound :
    ∃ C_total : ℝ,
      0 < C_total ∧
        ∀ m n : ℕ,
          (totalArithmeticWork m n : ℝ) ≤
            C_total * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) *
              Real.log (((m + n : ℕ) : ℝ) / ε)

-- Proof sketch: unfold `HasLpBarrierShortStepTotalArithmeticComplexityBound`; this is exactly the
-- explicit constant-factor form of the total short-step arithmetic estimate on primitive total
-- arithmetic-work data.
/-- Unfolding
`HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork` recovers the explicit
constant-factor total arithmetic bound on primitive total arithmetic-work data, together with the
fixed small-accuracy hypothesis `ε ∈ (0, 1)`. -/
theorem hasLpBarrierShortStepTotalArithmeticComplexityBound_iff
    : HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork ↔
      ε ∈ Set.Ioo (0 : ℝ) 1 ∧
        ∃ C_total : ℝ,
          0 < C_total ∧
            ∀ m n : ℕ,
              (totalArithmeticWork m n : ℝ) ≤
                C_total * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) *
                  Real.log (((m + n : ℕ) : ℝ) / ε) := by
  constructor
  · intro h
    exact ⟨h.accuracy_mem, h.exists_pos_bound⟩
  · rintro ⟨hε, C_total, hC_total, hbound⟩
    exact ⟨hε, C_total, hC_total, hbound⟩

end ShortStepTotalArithmeticComplexity

/-- Helper for the total short-step arithmetic-complexity statement: the short-step accuracy
hypothesis forces the logarithmic factor in the total-work bound to be nonnegative whenever the
variable dimension is positive. -/
private theorem iteration_log_nonneg_of_short_step_accuracy
    {ε : ℝ}
    {iterationCount : ℕ → ℕ → ℕ}
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount)
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log (((m + n : ℕ) : ℝ) / ε) := by
  rcases hiter with ⟨hε, C_it, hC_it, hbound⟩
  have hone_le_sum : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ m + n by omega)
  have hε_le_sum : ε ≤ ((m + n : ℕ) : ℝ) := by
    exact le_trans (le_of_lt hε.2) hone_le_sum
  have hratio_ge_one : (1 : ℝ) ≤ ((m + n : ℕ) : ℝ) / ε := by
    exact (one_le_div₀ hε.1).2 hε_le_sum
  exact Real.log_nonneg hratio_ge_one

/-- Helper for the short-step complexity bridge: the uniform per-step Newton budget can be bounded
by a constant multiple of `n^2 (m + n)` after absorbing the ceiling. -/
private theorem ceil_step_budget_le_scaled_work
    {m n : ℕ}
    {C_step : ℝ}
    (hC_step : 0 < C_step)
    (hn : 0 < n) :
    (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) ≤
      (C_step + 1) * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) := by
  let scale : ℝ := (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ))
  have hshape : ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2) = scale := by
    dsimp [scale]
    ring
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hnsq_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hn_cast : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hsum_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
    exact_mod_cast (show 1 ≤ m + n by omega)
  have hscale_ge_one : (1 : ℝ) ≤ scale := by
    dsimp [scale]
    nlinarith
  have hceil_le :
      (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) ≤
        C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2) + 1 := by
    exact (Nat.ceil_lt_add_one (by positivity :
      0 ≤ C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2))).le
  calc
    (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ)
      ≤ C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2) + 1 := hceil_le
    _ = C_step * scale + 1 := by rw [hshape]
    _ ≤ (C_step + 1) * scale := by
      nlinarith
    _ = (C_step + 1) * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) := by
      dsimp [scale]
      ring

/-- Helper for the per-step arithmetic-complexity statement: once the actual Newton system
attached to each strict iterate and parameter `t` admits a genuine solution, the canonical ceiling
budget `⌈n^3 + m n^2⌉` yields a uniform arithmetic-budget witness for the source-facing per-step
complexity owner. -/
private theorem lpBarrierNewtonSystemArithmeticBudget_of_solution_exists
    (hsolve :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (decision : problem.StrictBarrierModelPoint)
        (t : ℝ),
          ∃ step,
            IsLpBarrierNewtonSystemSolution problem decision
              (lpBarrierNewtonSystemGradient problem decision).point
              (lpBarrierNewtonSystemGradient problem decision).residualSlack
              (lpBarrierNewtonSystemGradient problem decision).objectiveSlack
              t step) :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : ℝ),
            ℕ,
        ∃ C_step : ℝ,
          HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step := by
  classical
  let solver :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        LpApproximationEpigraphPoint n m :=
    fun {n} {m} problem decision t ↦
      Classical.choose (hsolve problem decision t)
  let arithmeticWork :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        ℕ :=
    fun {n} {m} _ _ _ ↦
      Nat.ceil (((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2))
  refine ⟨solver, arithmeticWork, 2, ?_⟩
  refine ⟨by norm_num, ?_⟩
  intro m n problem decision t
  dsimp [LpBarrierNewtonStepBound, solver, arithmeticWork]
  refine ⟨Classical.choose_spec (hsolve problem decision t), ?_⟩
  -- Proof comment: the work model is the canonical ceiling of `n^3 + m n^2`, and the
  -- previously established ceiling estimate places it under the uniform constant `C_step = 2`.
/-
Semantic recall note: `lean_leansearch` did not expose a reusable owner for this chapter-specific
total-cost predicate, so the local canonical owner remains
`HasLpBarrierShortStepTotalArithmeticComplexityBound`.
-/
  by_cases hn : 0 < n
  · have hceil :
        (Nat.ceil (((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) ≤
          2 * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) := by
      have hceil' :=
        @ceil_step_budget_le_scaled_work m n (1 : ℝ) (by norm_num) hn
      norm_num at hceil' ⊢
      exact hceil'
    calc
      (Nat.ceil (((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ)
        ≤ 2 * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) := hceil
      _ = 2 * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2) := by
        ring
  · have hn0 : n = 0 := by omega
    subst n
    norm_num

/-- Helper for the per-step arithmetic-complexity statement: the only nontrivial input needed for
the source-facing arithmetic-complexity statement is existence of a genuine Newton-system solution
for the actual barrier derivatives at each strict iterate. -/
private theorem lpBarrierNewtonSystemArithmeticComplexity_bound_of_solution_exists
    (hsolve :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (decision : problem.StrictBarrierModelPoint)
        (t : ℝ),
          ∃ step,
            IsLpBarrierNewtonSystemSolution problem decision
              (lpBarrierNewtonSystemGradient problem decision).point
              (lpBarrierNewtonSystemGradient problem decision).residualSlack
              (lpBarrierNewtonSystemGradient problem decision).objectiveSlack
              t step) :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : ℝ),
            ℕ,
        HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork := by
  obtain ⟨solver, arithmeticWork, C_step, hbudget⟩ :=
    lpBarrierNewtonSystemArithmeticBudget_of_solution_exists hsolve
  -- Proof comment: once the uniform budget witness is constructed, the public complexity owner is
  -- just the existential packaging of that same constant.
  exact ⟨solver, arithmeticWork, C_step, hbudget⟩

-- Proof sketch: eliminate `Δτ` and then `Δξ`, form the Schur complement in the `x`-variables,
-- and use the diagonal structure of `Λ₀`, `Λ₁`, `Λ₂`, and `D`. Forming the weighted matrices
-- costs `O(m n²)`, while the dense `n × n` factorization and solve cost `O(n³)`.
/-- First source conclusion: the explicit `ℓ_p`-barrier Newton system attached to the actual barrier
derivatives at the current strict iterate can be solved with arithmetic work `O(n^3 + m n^2)`.
The main public conclusion is the source-facing owner
`HasLpBarrierNewtonSystemArithmeticComplexityBound`; the positive budget constant remains internal
to that owner. -/
theorem lpBarrierNewtonSystemArithmeticComplexity_bound :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : ℝ),
            ℕ,
        HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork := by
  -- Route correction: the arithmetic packaging is now separated from the real obstruction. The
  -- remaining task is solely to show that the actual Newton system at each strict iterate has a
  -- genuine solution; once that exists, the public `O(n^3 + m n^2)` owner follows from the
  -- helper above.
  refine lpBarrierNewtonSystemArithmeticComplexity_bound_of_solution_exists ?_
  intro n m problem decision t
  -- Proof comment: all arithmetic work has already been packaged. The only remaining input is the
  -- existence of a genuine Newton step for the actual barrier-derivative right-hand side.
  -- Route correction: use the generic reduced Newton solver proved above, instantiated at the
  -- actual barrier gradient `lpBarrierNewtonSystemGradient problem decision`.
  simpa using
    reducedNewtonSystemSolution
      problem
      decision
      (lpBarrierNewtonSystemGradient problem decision).point
      (lpBarrierNewtonSystemGradient problem decision).residualSlack
      (lpBarrierNewtonSystemGradient problem decision).objectiveSlack
      t

-- Proof sketch: combine the explicit per-step budget witness
-- `HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step` with the short-step
-- iteration-count owner `HasLpBarrierShortStepIterationBound ε iterationCount`, and multiply the
-- iteration count by the induced uniform step budget.
/-- Combining the per-step Newton-system arithmetic bound with the Chapter 5 short-step
iteration-count owner yields the canonical total arithmetic-work model induced by the iteration
count and the same per-step budget witness. That induced total-work family satisfies the
corresponding source-facing total arithmetic-complexity bound. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound_of_budget
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (solver :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        LpApproximationEpigraphPoint n m)
    (arithmeticWork :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        ℕ)
    (C_step : ℝ)
    (hstep : HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    HasLpBarrierShortStepTotalArithmeticComplexityBound ε
      (lpBarrierShortStepTotalArithmeticWork iterationCount C_step) := by
  rcases hstep with ⟨hC_step, hbudget⟩
  let hiterFull := hiter
  rcases hiter with ⟨hε, C_it, hC_it, hiter_bound⟩
  refine ⟨hε, C_it * (C_step + 1), by positivity, ?_⟩
  intro m n
  by_cases hn : 0 < n
  · have hlog_nonneg :
        0 ≤ Real.log (((m + n : ℕ) : ℝ) / ε) :=
      iteration_log_nonneg_of_short_step_accuracy hiterFull m n hn
    have hsum_pos : 0 < (m : ℝ) + (n : ℝ) := by
      exact_mod_cast (show 0 < m + n by omega)
    have hstep_bound :
        (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) ≤
          (C_step + 1) * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ)) :=
      ceil_step_budget_le_scaled_work hC_step hn
    have hiter_nonneg :
        0 ≤ C_it * Real.sqrt ((m : ℝ) + (n : ℝ)) *
          Real.log (((m + n : ℕ) : ℝ) / ε) := by
      positivity
    have hproduct :
        (iterationCount m n : ℝ) *
            (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) ≤
          (C_it * Real.sqrt ((m : ℝ) + (n : ℝ)) *
              Real.log (((m + n : ℕ) : ℝ) / ε)) *
            ((C_step + 1) * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ))) := by
      exact mul_le_mul (hiter_bound m n hn) hstep_bound
        (by exact_mod_cast Nat.zero_le _)
        hiter_nonneg
    have hpow_three_halves :
        ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) =
          ((m : ℝ) + (n : ℝ)) * Real.sqrt ((m : ℝ) + (n : ℝ)) := by
      calc
        Real.rpow ((m : ℝ) + (n : ℝ)) (3 / 2 : ℝ)
            = Real.rpow ((m : ℝ) + (n : ℝ)) ((1 : ℝ) + 1 / 2) := by norm_num
        _ = Real.rpow ((m : ℝ) + (n : ℝ)) (1 : ℝ) *
              Real.rpow ((m : ℝ) + (n : ℝ)) (1 / 2 : ℝ) := by
            simpa using (Real.rpow_add hsum_pos (1 : ℝ) (1 / 2 : ℝ))
        _ = ((m : ℝ) + (n : ℝ)) * Real.sqrt ((m : ℝ) + (n : ℝ)) := by
            simp [Real.sqrt_eq_rpow]
    -- Proof comment: multiply the iteration bound by the uniform per-step budget and then rewrite
    -- the mixed factor `(m + n) * sqrt (m + n)` into the textbook exponent `(m + n)^(3/2)`.
    calc
      ((lpBarrierShortStepTotalArithmeticWork iterationCount C_step m n : ℕ) : ℝ)
        = (iterationCount m n : ℝ) *
            (Nat.ceil (C_step * ((n : ℝ) ^ 3 + (m : ℝ) * (n : ℝ) ^ 2)) : ℝ) := by
            rw [lpBarrierShortStepTotalArithmeticWork_apply]
            norm_num
      _ ≤ (C_it * Real.sqrt ((m : ℝ) + (n : ℝ)) *
              Real.log (((m + n : ℕ) : ℝ) / ε)) *
            ((C_step + 1) * (n : ℝ) ^ 2 * ((m : ℝ) + (n : ℝ))) := hproduct
      _ = (C_it * (C_step + 1)) * (n : ℝ) ^ 2 *
            (((m : ℝ) + (n : ℝ)) * Real.sqrt ((m : ℝ) + (n : ℝ))) *
              Real.log (((m + n : ℕ) : ℝ) / ε) := by ring
      _ = (C_it * (C_step + 1)) * (n : ℝ) ^ 2 *
            ((m : ℝ) + (n : ℝ)) ^ (3 / 2 : ℝ) *
              Real.log (((m + n : ℕ) : ℝ) / ε) := by
            rw [hpow_three_halves]
  · have hn0 : n = 0 := by omega
    subst n
    rw [lpBarrierShortStepTotalArithmeticWork_apply]
    norm_num

-- Proof sketch: unpack the per-step owner to recover a budget witness `C_step`, then apply
-- `lpBarrierShortStepTotalArithmeticComplexity_bound_of_budget` to the induced total-work model.
/-- Combining the per-step arithmetic-complexity owner with the Chapter 5 short-step iteration
owner yields a source-facing total arithmetic-work owner. The induced family
`lpBarrierShortStepTotalArithmeticWork iterationCount C_step` is retained only as bridge data,
through an accompanying budget witness `C_step`. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound_of_bounds
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (solver :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        LpApproximationEpigraphPoint n m)
    (arithmeticWork :
      ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
        (_ : problem.StrictBarrierModelPoint)
        (_ : ℝ),
        ℕ)
    (hstep : HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    ∃ totalArithmeticWork : ℕ → ℕ → ℕ,
      HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork ∧
        ∃ C_step : ℝ,
          HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step ∧
            totalArithmeticWork =
              lpBarrierShortStepTotalArithmeticWork iterationCount C_step := by
  rcases hstep with ⟨C_step, hbudget⟩
  refine ⟨lpBarrierShortStepTotalArithmeticWork iterationCount C_step, ?_, C_step, hbudget, rfl⟩
  -- Proof comment: keep the canonical induced total-work family and invoke the previous bridge
  -- theorem with the recovered uniform per-step budget witness.
  exact lpBarrierShortStepTotalArithmeticComplexity_bound_of_budget
    ε iterationCount solver arithmeticWork C_step hbudget hiter

-- Semantic recall note: `lean_leansearch` did not expose a reusable external owner for this
-- chapter-specific short-step complexity statement, so the repair stays on the local Chapter 5
-- owners `HasLpBarrierShortStepIterationBound` and
-- `HasLpBarrierShortStepTotalArithmeticComplexityBound`.
/-- Theorem 5.4.9.3: Cost of solving the Newton system and total complexity. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound :
    ∃ solver :
        ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
          (_ : problem.StrictBarrierModelPoint)
          (_ : ℝ),
          LpApproximationEpigraphPoint n m,
      ∃ arithmeticWork :
          ∀ {n m : ℕ} (problem : LpApproximationBoxProblem n m)
            (_ : problem.StrictBarrierModelPoint)
            (_ : ℝ),
            ℕ,
        HasLpBarrierNewtonSystemArithmeticComplexityBound solver arithmeticWork ∧
          ∀ ε : ℝ,
            ∀ iterationCount : ℕ → ℕ → ℕ,
              HasLpBarrierShortStepIterationBound ε iterationCount →
                ∃ totalArithmeticWork : ℕ → ℕ → ℕ,
                  HasLpBarrierShortStepTotalArithmeticComplexityBound ε
                    totalArithmeticWork ∧
                    ∃ C_step : ℝ,
                      HasLpBarrierNewtonSystemArithmeticBudget solver arithmeticWork C_step ∧
                        totalArithmeticWork =
                          lpBarrierShortStepTotalArithmeticWork iterationCount C_step := by
  rcases lpBarrierNewtonSystemArithmeticComplexity_bound with
    ⟨solver, arithmeticWork, hstep⟩
  refine ⟨solver, arithmeticWork, hstep, ?_⟩
  intro ε iterationCount hiter
  -- Proof comment: keep the solver/work pair produced by the per-step theorem and package the
  -- induced total-work family via the previously established short-step bridge.
  exact lpBarrierShortStepTotalArithmeticComplexity_bound_of_bounds
    ε iterationCount solver arithmeticWork hstep hiter

-- Proof sketch: keep the old existential-total-work bridge as an auxiliary consequence by
-- forgetting the explicit solver/work model and the canonical induced total-work family.
/-- Auxiliary bridge theorem: forgetting the explicit per-step Newton solver/work data and the
canonical induced total-work family recovers the weaker existential total arithmetic-work owner
used by transfer arguments. -/
theorem lpBarrierShortStepTotalArithmeticComplexity_bound_exists
    (ε : ℝ)
    (iterationCount : ℕ → ℕ → ℕ)
    (hiter : HasLpBarrierShortStepIterationBound ε iterationCount) :
    ∃ totalArithmeticWork : ℕ → ℕ → ℕ,
      HasLpBarrierShortStepTotalArithmeticComplexityBound ε totalArithmeticWork := by
  rcases lpBarrierNewtonSystemArithmeticComplexity_bound with
    ⟨solver, arithmeticWork, hstep⟩
  rcases lpBarrierShortStepTotalArithmeticComplexity_bound_of_bounds
      ε iterationCount solver arithmeticWork hstep hiter with
    ⟨totalArithmeticWork, htotal, C_step, hbudget, hwork⟩
  exact ⟨totalArithmeticWork, htotal⟩
