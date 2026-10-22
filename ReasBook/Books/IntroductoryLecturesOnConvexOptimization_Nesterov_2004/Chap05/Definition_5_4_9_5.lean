/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_10_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_9_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_12

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

namespace LpApproximationBoxProblem

open LpApproximationEpigraphPoint

/-
Definition 5.4.9.5 lies in the Chapter 5 box-constrained `ℓ_p` approximation / logarithmic
barrier domain.

Sampled owner declarations:
- `strictConstraintSet` and `logarithmicBarrier` in `Chap01/Proposition_1_10_17`, the project
  owner pattern for logarithmic barriers attached to finite continuous inequality families;
- `analyticBarrierDomain`, `AnalyticBarrierPoint`, and `analyticBarrier` in
  `Chap03/Definition_3_62`, the chapter precedent for keeping a logarithmic barrier on its strict
  domain and any ambient formula only as a bridge;
- `epigraphLogarithmicBarrier` and `StrictEpigraphFeasiblePoint` in
  `Chap05/Definition_5_4_3_5`, the adjacent Chapter 5 owner pattern for an epigraph barrier
  built from `strictConstraintSet` and `logarithmicBarrier`;
- `separableLogBarrierF4` in `Definition_5_4_8_12`, the Chapter 5 owner of the scalar barrier
  `f(y, t) = -log t - log (t^(2 / p) - y^2)`.

Best owner abstraction:
- source-facing: the strict barrier domain and logarithmic barrier attached to the box-constrained
  `ℓ_p` approximation barrier model;
- core/canonical: `strictConstraintSet` and `logarithmicBarrier` on the split continuous
  constraint family whose first two blocks recover the scalar owner `separableLogBarrierF4`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formula.

Primitive data:
- no new primitive data beyond `problem : LpApproximationBoxProblem n m`;
- the existing lifted decision variables `LpApproximationEpigraphPoint n m`.

Derived API:
- the internal split continuous constraint family;
- `problem.barrierModelBarrierDomain`;
- `problem.StrictBarrierModelPoint`;
- `problem.barrierModelBarrier`;
- the ambient evaluation theorems.

Source/core/bridge triage:
- source-facing: `problem.barrierModelBarrierDomain` and `problem.barrierModelBarrier`;
- core/canonical: the Chapter 1 owners `strictConstraintSet` and `logarithmicBarrier`;
- bridge/view: the ambient `(x, ξ, τ)` evaluation formulas.

The textbook barrier formula is only meaningful where every logarithmic argument is strictly
positive, so the public owner must live on that strict carrier rather than on all lifted points.
This refinement therefore keeps the same mathematical formula, but moves the public API to the
strict-domain logarithmic-barrier pattern already used elsewhere in the project.
-/

private abbrev residualArgument
    (problem : LpApproximationBoxProblem n m) (i : Fin m)
    (decision : LpApproximationEpigraphPoint n m) : ℝ :=
  ⟪problem.a i, decision.point⟫ - problem.b i

/-- Helper for Definition 5.4.9.5: the residual affine coordinate is continuous on the lifted
decision space. -/
private theorem continuous_residualArgument
    (problem : LpApproximationBoxProblem n m) (i : Fin m) :
    Continuous (residualArgument problem i) := by
  -- Proof comment: the residual coordinate is the continuous affine map
  -- `x ↦ ⟪aᵢ, x⟫ - bᵢ` composed with the point projection.
  simpa [residualArgument] using
    (((innerSL ℝ (problem.a i) : E →L[ℝ] ℝ).continuous.comp continuous_fst).sub
      continuous_const)

private def residualArgumentMap
    (problem : LpApproximationBoxProblem n m) (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := residualArgument problem i
  continuous_toFun := continuous_residualArgument problem i

/-- Helper for Definition 5.4.9.5: the objective-slack projection is continuous. -/
private theorem continuous_objectiveSlack :
    Continuous (objectiveSlack : LpApproximationEpigraphPoint n m → ℝ) := by
  -- Proof comment: `objectiveSlack` is the first coordinate of the slack pair projection.
  simpa using (continuous_snd.fst : Continuous fun decision : LpApproximationEpigraphPoint n m ↦
    decision.objectiveSlack)

private def objectiveSlackMap :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun := objectiveSlack
  continuous_toFun := continuous_objectiveSlack

/-- Helper for Definition 5.4.9.5: each residual-slack coordinate is continuous. -/
private theorem continuous_residualSlack (i : Fin m) :
    Continuous fun decision : LpApproximationEpigraphPoint n m ↦ decision.residualSlack i := by
  -- Proof comment: each residual slack is a coordinate projection from the residual-slack tuple.
  simpa using
    ((continuous_apply i).comp continuous_snd.snd :
      Continuous fun decision : LpApproximationEpigraphPoint n m ↦ decision.residualSlack i)

private def residualSlackMap (i : Fin m) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.residualSlack i
  continuous_toFun := continuous_residualSlack i

/-- Helper for Definition 5.4.9.5: each point coordinate is continuous on the lifted decision
space. -/
private theorem continuous_pointCoordinate (j : Fin n) :
    Continuous fun decision : LpApproximationEpigraphPoint n m ↦ decision.point j := by
  -- Proof comment: first pass from the `PiLp` point to its function representation, then project
  -- the `j`-th coordinate and compose with the decision-point projection.
  let hOfLp :
      Continuous (fun x : E ↦ x.ofLp) :=
    PiLp.continuous_ofLp 2 (fun _ : Fin n ↦ ℝ)
  have hcoord : Continuous fun x : E ↦ x j := (continuous_apply j).comp hOfLp
  simpa using hcoord.comp continuous_fst

private def pointCoordinateMap (j : Fin n) :
    C(LpApproximationEpigraphPoint n m, ℝ) where
  toFun decision := decision.point j
  continuous_toFun := continuous_pointCoordinate j

/-- Helper for Definition 5.4.9.5: the residual epigraph-gap block is continuous. -/
private theorem continuous_residual_power_gap
    (problem : LpApproximationBoxProblem n m) (i : Fin m) :
    Continuous fun decision : LpApproximationEpigraphPoint n m ↦
      (residualArgument problem i decision) ^ (2 : ℕ) -
        Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ)) := by
  -- Proof comment: combine continuity of the residual affine coordinate and of the residual-slack
  -- coordinate, then apply the power and `rpow` closure properties.
  have harg :
      Continuous fun decision : LpApproximationEpigraphPoint n m ↦
        residualArgument problem i decision :=
    continuous_residualArgument problem i
  have hτ :
      Continuous fun decision : LpApproximationEpigraphPoint n m ↦
        decision.residualSlack i :=
    continuous_residualSlack i
  have hp : 0 ≤ 2 / (problem.p : ℝ) := by
    exact div_nonneg (by norm_num) (le_trans zero_lt_one.le problem.one_le_p)
  exact (harg.pow 2).sub <| hτ.rpow_const fun _ ↦ Or.inr hp

private def barrierModelStrictConstraints
    (problem : LpApproximationBoxProblem n m) :
    Fin (m + (m + (1 + (n + n)))) → C(LpApproximationEpigraphPoint n m, ℝ) :=
  Fin.addCases
    (fun i ↦ -(residualSlackMap i))
    (Fin.addCases
      (fun i ↦
        { toFun := fun decision ↦
            (residualArgument problem i decision) ^ (2 : ℕ) -
              Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))
          continuous_toFun := continuous_residual_power_gap problem i })
      (Fin.addCases
        (fun _ ↦
          ∑ i : Fin m, residualSlackMap i - objectiveSlackMap)
        (Fin.addCases
          (fun j ↦ ContinuousMap.const _ (problem.α j) - pointCoordinateMap j)
          (fun j ↦ pointCoordinateMap j - ContinuousMap.const _ (problem.β j)))))

/-- The strict domain on which the box-constrained `ℓ_p` approximation barrier-model
logarithmic barrier is defined. -/
def barrierModelBarrierDomain
    (problem : LpApproximationBoxProblem n m) :
    Set (LpApproximationEpigraphPoint n m) :=
  strictConstraintSet problem.barrierModelStrictConstraints

/-- The subtype of points in the strict barrier-model barrier domain. This is the natural owner
carrier for the logarithmic barrier. -/
abbrev StrictBarrierModelPoint
    (problem : LpApproximationBoxProblem n m) :=
  {decision : LpApproximationEpigraphPoint n m // decision ∈ problem.barrierModelBarrierDomain}

/-- Membership in `problem.barrierModelBarrierDomain` means that every logarithmic argument in the
textbook barrier formula is strictly positive. -/
theorem mem_barrierModelBarrierDomain_iff
    (problem : LpApproximationBoxProblem n m)
    (decision : LpApproximationEpigraphPoint n m) :
    decision ∈ problem.barrierModelBarrierDomain ↔
      (∀ i : Fin m,
        0 < decision.residualSlack i ∧
          (⟪problem.a i, decision.point⟫ - problem.b i) ^ (2 : ℕ) <
            Real.rpow (decision.residualSlack i) (2 / (problem.p : ℝ))) ∧
        ∑ i : Fin m, decision.residualSlack i < decision.objectiveSlack ∧
        ∀ j : Fin n, problem.α j < decision.point j ∧ decision.point j < problem.β j := by
  rw [barrierModelBarrierDomain, mem_strictConstraintSet_iff]
  constructor
  · intro h
    -- Proof comment: read the five strict-slack blocks directly from the split constraint family.
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_⟩
      · exact neg_lt_zero.mp <| by
          simpa [barrierModelStrictConstraints] using
            h (Fin.castAdd (m + (1 + (n + n))) i)
      · exact sub_lt_zero.mp <| by
          simpa [barrierModelStrictConstraints, residualArgument] using
            h (Fin.natAdd m (Fin.castAdd (1 + (n + n)) i))
    · exact sub_lt_zero.mp <| by
        simpa [barrierModelStrictConstraints] using
          h (Fin.natAdd m (Fin.natAdd m (Fin.castAdd (n + n) (0 : Fin 1))))
    · intro j
      refine ⟨?_, ?_⟩
      · exact sub_lt_zero.mp <| by
          simpa [barrierModelStrictConstraints] using
            h (Fin.natAdd m (Fin.natAdd m (Fin.natAdd 1 (Fin.castAdd n j))))
      · have hj := h (Fin.natAdd m (Fin.natAdd m (Fin.natAdd 1 (Fin.natAdd n j))))
        dsimp [barrierModelStrictConstraints] at hj
        rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right, Fin.addCases_right] at hj
        simpa [pointCoordinateMap, sub_lt_zero] using hj
  · rintro ⟨hresidual, hsum, hbox⟩
    -- Proof comment: dispatch an arbitrary strict constraint by the same five-block
    -- `Fin.addCases` decomposition used to define the family.
    intro k
    induction k using Fin.addCases with
    | left i =>
        simpa [barrierModelStrictConstraints] using neg_lt_zero.mpr (hresidual i).1
    | right k =>
        induction k using Fin.addCases with
        | left i =>
            simpa [barrierModelStrictConstraints, residualArgument] using
              sub_lt_zero.mpr (hresidual i).2
        | right k =>
            induction k using Fin.addCases with
            | left _ =>
                simpa [barrierModelStrictConstraints] using sub_lt_zero.mpr hsum
            | right k =>
                induction k using Fin.addCases with
                | left j =>
                    simpa [barrierModelStrictConstraints] using
                      sub_lt_zero.mpr (hbox j).1
                | right j =>
                    dsimp [barrierModelStrictConstraints]
                    rw [Fin.addCases_right, Fin.addCases_right, Fin.addCases_right,
                      Fin.addCases_right]
                    simpa [pointCoordinateMap, sub_lt_zero] using sub_lt_zero.mpr (hbox j).2

/-- Definition 5.4.9.5: the logarithmic barrier attached to the box-constrained `ℓ_p`
approximation barrier model, kept on its strict domain and obtained by reusing the Chapter 1
owner `logarithmicBarrier` on the split continuous inequality family whose scalar blocks are the
Chapter 5 owner `separableLogBarrierF4 problem.p`. -/
def barrierModelBarrier
    (problem : LpApproximationBoxProblem n m) :
    C(problem.StrictBarrierModelPoint, ℝ) :=
  logarithmicBarrier problem.barrierModelStrictConstraints

/-- Helper for Definition 5.4.9.5: each residual-slack pair contributes the scalar Chapter 5
barrier `F₄`. -/
private theorem barrierModel_scalar_block_eq
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) (i : Fin m) :
    -Real.log (decision.1.residualSlack i) -
        Real.log
          (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
            (⟪problem.a i, decision.1.point⟫ - problem.b i) ^ (2 : ℕ)) =
      separableLogBarrierF4 (problem.p : ℝ)
        (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i) := by
  -- Proof comment: this is exactly the previously established coordinate formula for `F₄`.
  simpa using
    (separableLogBarrierF4_apply (problem.p : ℝ)
      (⟪problem.a i, decision.1.point⟫ - problem.b i)
      (decision.1.residualSlack i)).symm

/-- Helper for Definition 5.4.9.5: splitting the Chapter 1 logarithmic-barrier sum over the five
strict-constraint blocks recovers the textbook barrier formula. -/
private theorem barrierModel_logarithmicBarrier_split
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    -∑ k : Fin (m + (m + (1 + (n + n)))),
      Real.log (-(problem.barrierModelStrictConstraints k) decision.1) =
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i)) -
        Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (decision.1.point j - problem.α j) +
            Real.log (problem.β j - decision.1.point j)) := by
  -- Proof comment: split the global `Fin`-sum into the five source blocks coming from the
  -- strict barrier-model constraints.
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add]
  -- Proof comment: rewrite each block to its ambient slack formula and then regroup the additive
  -- terms into the scalar `F₄` sum, the coupling logarithm, and the two box-log sums.
  simp only [barrierModelStrictConstraints, residualArgument, Fin.addCases_right, Fin.addCases_left]
  simp only [ContinuousMap.neg_apply, ContinuousMap.sub_apply,
    ContinuousMap.coe_mk, ContinuousMap.const_apply, objectiveSlackMap,
    pointCoordinateMap]
  simp only [Fin.sum_univ_one]
  have hresidualSlack_apply (i : Fin m) :
      (residualSlackMap i) decision.1 = decision.1.residualSlack i := by
    rfl
  have hresidualSlack_sum_apply :
      (∑ i : Fin m, residualSlackMap i) decision.1 = ∑ i : Fin m, decision.1.residualSlack i := by
    simp [residualSlackMap]
  rw [hresidualSlack_sum_apply]
  simp_rw [hresidualSlack_apply]
  simp only [neg_sub, neg_neg]
  -- Proof comment: regroup the outer negation so the residual-slack pair and the box terms can
  -- be combined blockwise.
  have hregroup_main :
    -((∑ i : Fin m, Real.log (decision.1.residualSlack i)) +
        ((∑ i : Fin m,
            Real.log
              (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
                (⟪problem.a i, decision.1.point⟫ - problem.b i) ^ (2 : ℕ))) +
          (Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) +
            ((∑ j : Fin n, Real.log (decision.1.point j - problem.α j)) +
              ∑ j : Fin n, Real.log (problem.β j - decision.1.point j))))) =
      ((-(∑ i : Fin m, Real.log (decision.1.residualSlack i)) -
          ∑ i : Fin m,
            Real.log
              (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
                (⟪problem.a i, decision.1.point⟫ - problem.b i) ^ (2 : ℕ))) -
        Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
        ((∑ j : Fin n, Real.log (decision.1.point j - problem.α j)) +
          ∑ j : Fin n, Real.log (problem.β j - decision.1.point j))) := by
    ring
  rw [hregroup_main]
  -- Proof comment: combine the first two `Fin m` sums pointwise into the scalar owner `F₄`.
  have hregroup_scalar :
    (-(∑ i : Fin m, Real.log (decision.1.residualSlack i)) -
        (∑ i : Fin m,
          Real.log
            (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
              (⟪problem.a i, decision.1.point⟫ - problem.b i) ^ (2 : ℕ)))) =
      ∑ i : Fin m,
        (-Real.log (decision.1.residualSlack i) -
          Real.log
            (Real.rpow (decision.1.residualSlack i) (2 / (problem.p : ℝ)) -
              (⟪problem.a i, decision.1.point⟫ - problem.b i) ^ (2 : ℕ))) := by
    rw [← Finset.sum_neg_distrib]
    rw [← Finset.sum_sub_distrib]
  rw [hregroup_scalar]
  simp_rw [problem.barrierModel_scalar_block_eq]
  -- Proof comment: merge the two box-coordinate sums back into the textbook bracketed form.
  have hregroup_box :
    ∑ j : Fin n, Real.log (decision.1.point j - problem.α j) +
        ∑ j : Fin n, Real.log (problem.β j - decision.1.point j) =
      ∑ j : Fin n,
        (Real.log (decision.1.point j - problem.α j) +
          Real.log (problem.β j - decision.1.point j)) := by
    rw [← Finset.sum_add_distrib]
  rw [hregroup_box]

/-- Evaluating `problem.barrierModelBarrier` on a strict-domain point recovers its ambient bridge
formula. -/
@[simp] theorem barrierModelBarrier_apply
    (problem : LpApproximationBoxProblem n m)
    (decision : problem.StrictBarrierModelPoint) :
    problem.barrierModelBarrier decision =
      (∑ i : Fin m,
        separableLogBarrierF4 (problem.p : ℝ)
          (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i)) -
        Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
        ∑ j : Fin n,
          (Real.log (decision.1.point j - problem.α j) +
            Real.log (problem.β j - decision.1.point j)) := by
  -- Proof comment: the source-facing barrier is the Chapter 1 logarithmic barrier on the split
  -- strict-constraint family, so only the blockwise evaluation bridge remains.
  rw [barrierModelBarrier]
  let N := m + (m + (1 + (n + n)))
  have hlog_apply :=
    logarithmicBarrier_apply (f := problem.barrierModelStrictConstraints) (x := decision)
  let logSum : Finset (Fin N) → ℝ := fun s ↦
    -(Finset.sum s fun j ↦ Real.log (-(problem.barrierModelStrictConstraints j) decision.1))
  have huniv :
      @Finset.univ (Fin N) (Fintype.ofFinite (Fin N)) =
        @Finset.univ (Fin N) (Fin.fintype N) := by
    ext j
    simp
  have hsum_instance :
      logSum (@Finset.univ (Fin N) (Fintype.ofFinite (Fin N))) =
        logSum (@Finset.univ (Fin N) (Fin.fintype N)) := by
    exact congrArg logSum huniv
  calc
    (logarithmicBarrier problem.barrierModelStrictConstraints) decision =
        logSum (@Finset.univ (Fin N) (Fintype.ofFinite (Fin N))) := by
          convert hlog_apply using 1
    _ = logSum (@Finset.univ (Fin N) (Fin.fintype N)) := hsum_instance
    _ = (∑ i : Fin m,
          separableLogBarrierF4 (problem.p : ℝ)
            (⟪problem.a i, decision.1.point⟫ - problem.b i, decision.1.residualSlack i)) -
          Real.log (decision.1.objectiveSlack - ∑ i : Fin m, decision.1.residualSlack i) -
          ∑ j : Fin n,
            (Real.log (decision.1.point j - problem.α j) +
              Real.log (problem.β j - decision.1.point j)) := by
      simpa [logSum] using problem.barrierModel_logarithmicBarrier_split decision

/-- At a strict-domain tuple `(x, ξ, τ)`, the barrier-model logarithmic barrier is the textbook
formula
`F(x, ξ, τ) = \sum_i f(\langle a_i, x \rangle - b^{(i)}, τ_i)
  - \log (\xi - \sum_i τ_i)
  - \sum_j [\log (x_j - α_j) + \log (β_j - x_j)]`,
where `f = separableLogBarrierF4 problem.p`. -/
theorem barrierModelBarrier_apply_mk
    (problem : LpApproximationBoxProblem n m) (x : E) (ξ : ℝ) (τ : Fin m → ℝ)
    (h : (x, ξ, τ) ∈ problem.barrierModelBarrierDomain) :
    problem.barrierModelBarrier ⟨(x, ξ, τ), h⟩ =
      (∑ i : Fin m, separableLogBarrierF4 (problem.p : ℝ) (⟪problem.a i, x⟫ - problem.b i, τ i)) -
        Real.log (ξ - ∑ i : Fin m, τ i) -
        ∑ j : Fin n, (Real.log (x j - problem.α j) + Real.log (problem.β j - x j)) := by
  exact problem.barrierModelBarrier_apply ⟨(x, ξ, τ), h⟩

end LpApproximationBoxProblem

end
