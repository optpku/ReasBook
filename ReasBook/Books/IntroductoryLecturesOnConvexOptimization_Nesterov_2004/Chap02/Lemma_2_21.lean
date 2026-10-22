/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Primary domain: inequality-constrained Lagrangian problems and their auxiliary max-violation
value function.

Owner abstractions sampled before refining:
- `LagrangianProblem.feasibleSet`, `LagrangianProblem.primalOptimalValue`, and
  `LagrangianProblem.lagrangian` in Chapter 1's owner file
  `Nesterov/Items/Chap01/Definition_1_10_2.lean`;
- `GeneralMinimizationProblem.componentOnAmbient` in
  `Nesterov/Items/Chap01/Definition_1_1_4_3.lean`, which packages an objective together with its
  constraint family as a canonical `Fin (m + 1)`-indexed component map;
- the later Euclidean bridge
  `SmoothFunctionalConstraintsMinimizationProblem.toLagrangianProblem`, which reuses this same
  owner component family on `EuclideanSpace`;
- `maxTypeObjective` in `Nesterov/Items/Chap02/Lemma_2_18.lean`, the Euclidean finite-maximum
  owner that matches the same construction once the ambient space has specialized to `ℝⁿ`.

The best owner abstraction here is still the generic `LagrangianProblem Q m` itself: the later
Euclidean chapter API is a specialization, while this file needs the intrinsic max-violation
objective on an arbitrary ambient type `Q`.

Primitive data here are only the underlying `LagrangianProblem` and the scalar parameter `t`.
The canonical derived component family is indexed by `Fin (m + 1)`: index `0` is
`x ↦ f₀(x) - t`, and successor indices are the constraints. The public derived API then consists
of that component family, the auxiliary objective, and the corresponding unconstrained optimal
value from Chapter 1's owner `SetConstrainedMinimizationProblem.unconstrained` /
`optimalValue`.

Source/core/bridge triage:
- source-facing: the threshold sign statements of Lemma 2.21 itself;
- core/canonical: `problem.constrainedAuxiliaryComponents`,
  `problem.constrainedAuxiliaryObjective`, and
  `SetConstrainedMinimizationProblem.optimalValue`;
- bridge/view: the unconditional lower bounds by `min (tStar - t) 0`, which package the
feasible/infeasible case split into one inequality but are not the source-facing main statement.
-/

/-- The canonical `Fin (m + 1)` component family whose maximum is the auxiliary objective:
index `0` is the shifted objective gap `x ↦ f₀(x) - t`, and successor indices are the inequality
constraints. -/
def constrainedAuxiliaryComponents
    (problem : LagrangianProblem Q m) (t : ℝ) : Fin (m + 1) → Q → ℝ :=
  Fin.cases (fun x ↦ problem x - t) problem.constraints

@[simp] theorem constrainedAuxiliaryComponents_zero
    (problem : LagrangianProblem Q m) (t : ℝ) :
    problem.constrainedAuxiliaryComponents t 0 = fun x ↦ problem x - t :=
  rfl

@[simp] theorem constrainedAuxiliaryComponents_succ
    (problem : LagrangianProblem Q m) (t : ℝ) (i : Fin m) :
    problem.constrainedAuxiliaryComponents t i.succ = problem.constraints i :=
  rfl

/-- The auxiliary objective `f(t; x)`, defined as the maximum of the objective gap `f₀(x) - t`
and all inequality-constraint values. -/
def constrainedAuxiliaryObjective (problem : LagrangianProblem Q m) (t : ℝ) : Q → ℝ :=
  maxTypeObjective (problem.constrainedAuxiliaryComponents t)

/-- The objective residual `f₀(x) - t` is one of the terms contributing to the owner auxiliary
objective `f(t; x)`. -/
-- Proof sketch: in the finite-maximum formula for `problem.constrainedAuxiliaryObjective t x`,
-- the zero index contributes
-- exactly `problem.objective x - t`; apply `Finset.le_sup'` to that term.
theorem objective_sub_le_constrainedAuxiliaryObjective
    (problem : LagrangianProblem Q m) (t : ℝ) (x : Q) :
    problem x - t ≤ problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun j : Fin (m + 1) ↦ problem.constrainedAuxiliaryComponents t j x)
      (by simp : (0 : Fin (m + 1)) ∈ Finset.univ))

/-- Each individual constraint value `fᵢ(x)` is one of the terms contributing to the owner
auxiliary objective `f(t; x)`. -/
-- Proof sketch: in the finite-maximum formula for `problem.constrainedAuxiliaryObjective t x`,
-- the index `i.succ`
-- contributes exactly `problem.constraints i x`; apply `Finset.le_sup'` to that term.
theorem constraint_le_constrainedAuxiliaryObjective
    (problem : LagrangianProblem Q m) (t : ℝ) (x : Q) (i : Fin m) :
    problem.constraints i x ≤ problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply]
  simpa using
    (Finset.le_sup'
      (fun j : Fin (m + 1) ↦ problem.constrainedAuxiliaryComponents t j x)
      (by simp : i.succ ∈ Finset.univ))

/-- Increasing the parameter by a nonnegative amount can only decrease the auxiliary objective at
each point. -/
-- Proof sketch: in the finite maximum defining `problem.constrainedAuxiliaryObjective (t + Δ) x`,
-- the zero component drops from `problem x - t` to `problem x - (t + Δ)`, while every successor
-- component is unchanged.
theorem constrainedAuxiliaryObjective_shift_le
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) (x : Q) :
    problem.constrainedAuxiliaryObjective (t + Δ) x ≤
      problem.constrainedAuxiliaryObjective t x := by
  rw [constrainedAuxiliaryObjective, maxTypeObjective_apply,
    constrainedAuxiliaryObjective, maxTypeObjective_apply]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hobj : problem x - (t + Δ) ≤ problem.constrainedAuxiliaryObjective t x := by
        linarith [problem.objective_sub_le_constrainedAuxiliaryObjective t x]
      rw [← maxTypeObjective_apply, ← constrainedAuxiliaryObjective]
      simpa using hobj
  | succ i =>
      rw [← maxTypeObjective_apply, ← constrainedAuxiliaryObjective]
      simpa using problem.constraint_le_constrainedAuxiliaryObjective t x i

/-- Increasing the parameter by `Δ ≥ 0` lowers the auxiliary objective by at most `Δ` at each
point. -/
-- Proof sketch: the zero component changes by exactly `Δ`, while every constraint component is
-- unchanged, so the finite maximum can drop by no more than `Δ`.
theorem constrainedAuxiliaryObjective_sub_le_shift
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) (x : Q) :
    problem.constrainedAuxiliaryObjective t x - Δ ≤
      problem.constrainedAuxiliaryObjective (t + Δ) x := by
  rw [sub_le_iff_le_add, constrainedAuxiliaryObjective, maxTypeObjective_apply]
  refine Finset.sup'_le _ _ ?_
  intro j hj
  cases j using Fin.cases with
  | zero =>
      have hobj :
          problem x - t ≤ problem.constrainedAuxiliaryObjective (t + Δ) x + Δ := by
        linarith [problem.objective_sub_le_constrainedAuxiliaryObjective (t + Δ) x]
      simpa using hobj
  | succ i =>
      simpa using
        (problem.constraint_le_constrainedAuxiliaryObjective (t + Δ) x i).trans
          (le_add_of_nonneg_right hΔ)

/-- The auxiliary optimal value `f*(t)` is the extended-real infimum of the auxiliary objective
over the ambient domain `Q`, routed through the canonical unconstrained owner
`SetConstrainedMinimizationProblem.unconstrained`. -/
def constrainedAuxiliaryOptimalValue (problem : LagrangianProblem Q m) (t : ℝ) : EReal :=
  (SetConstrainedMinimizationProblem.unconstrained
    (problem.constrainedAuxiliaryObjective t)).optimalValue

/-- The auxiliary optimal value is the infimum of the range of the auxiliary objective. -/
-- Proof sketch: unfold `constrainedAuxiliaryOptimalValue`.
theorem constrainedAuxiliaryOptimalValue_eq_sInf (problem : LagrangianProblem Q m) (t : ℝ) :
    problem.constrainedAuxiliaryOptimalValue t =
      sInf (Set.range fun x : Q ↦ (problem.constrainedAuxiliaryObjective t x : EReal)) :=
  by
  simpa [constrainedAuxiliaryOptimalValue, Set.image_univ] using
    (SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image
      (SetConstrainedMinimizationProblem.unconstrained
        (problem.constrainedAuxiliaryObjective t)))

/-- An attained minimum of the auxiliary objective realizes the owner auxiliary optimal value. -/
-- Proof sketch: apply the Chapter 1 owner theorem `optimalValue_eq_of_isMinOn` to the canonical
-- unconstrained minimization problem with objective `problem.constrainedAuxiliaryObjective t`, and
-- simplify back to `problem.constrainedAuxiliaryOptimalValue t`.
theorem constrainedAuxiliaryOptimalValue_eq_of_isMinOn
    (problem : LagrangianProblem Q m) {t : ℝ} {x : Q}
    (hmin : IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x) :
    problem.constrainedAuxiliaryOptimalValue t =
      (problem.constrainedAuxiliaryObjective t x : EReal) := by
  simpa [constrainedAuxiliaryOptimalValue] using
    (SetConstrainedMinimizationProblem.unconstrained
      (problem.constrainedAuxiliaryObjective t)).optimalValue_eq_of_isMinOn
      (by simp)
      hmin

section ThresholdBounds

variable (problem : LagrangianProblem Q m) {tStar : ℝ}

/-- Auxiliary bridge: every auxiliary objective value is bounded below by `min (tStar - t) 0`.
Feasible points contribute the primal-gap lower bound `tStar - t`, while infeasible points
contribute a positive constraint violation and hence at least `0`. The source-facing
below-threshold statement of Lemma 2.21 is recorded separately at the owner value-function layer
by `constrainedAuxiliaryOptimalValue_pos_of_lt`, while this pointwise bound remains companion
bridge API. -/
-- Proof sketch: if `x` is feasible, apply the lower-bound part of `htStar` to the feasible point
-- `x`; if `x` is infeasible, some constraint is positive, so the finite maximum defining the
-- auxiliary objective is at least `0`.
theorem min_sub_zero_le_constrainedAuxiliaryObjective
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (x : Q) :
    min (tStar - t) 0 ≤ problem.constrainedAuxiliaryObjective t x := by
  by_cases hx : x ∈ problem.feasibleSet
  · -- On the feasible branch, the primal lower bound controls the zero component.
    have hbound : tStar ≤ problem x := by
      exact htStar.1 ⟨⟨x, hx⟩, rfl⟩
    have hgap : tStar - t ≤ problem x - t := sub_le_sub_right hbound t
    exact
      (min_le_left (tStar - t) 0).trans <|
        hgap.trans (problem.objective_sub_le_constrainedAuxiliaryObjective t x)
  · -- On the infeasible branch, some constraint is positive, so the maximum is at least `0`.
    rw [problem.mem_feasibleSet_iff] at hx
    push Not at hx
    rcases hx with ⟨i, hi⟩
    have hnonneg : 0 ≤ problem.constrainedAuxiliaryObjective t x := by
      exact (le_of_lt hi).trans (problem.constraint_le_constrainedAuxiliaryObjective t x i)
    exact (min_le_right (tStar - t) 0).trans hnonneg

/-- Auxiliary bridge: if `t < tStar`, then every auxiliary objective value is strictly positive.
This pointwise statement is the bridge input for the source-facing positivity result on
`problem.constrainedAuxiliaryOptimalValue t`. -/
-- Proof sketch: if `x` is feasible, then `htStar` gives `tStar ≤ problem x`, so the zero
-- component `problem x - t` is strictly positive. If `x` is infeasible, some constraint is
-- strictly positive, so the corresponding successor component makes the same finite maximum
-- strictly positive.
theorem constrainedAuxiliaryObjective_pos_of_lt
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : t < tStar) (x : Q) :
    0 < problem.constrainedAuxiliaryObjective t x := by
  by_cases hx : x ∈ problem.feasibleSet
  · -- Feasible points inherit `problem x ≥ tStar`, so the zero component is strictly positive.
    have hbound : tStar ≤ problem x := by
      exact htStar.1 ⟨⟨x, hx⟩, rfl⟩
    have hgap : 0 < problem x - t := by
      linarith
    exact hgap.trans_le (problem.objective_sub_le_constrainedAuxiliaryObjective t x)
  · -- Infeasible points have a strictly positive violated constraint component.
    rw [problem.mem_feasibleSet_iff] at hx
    push Not at hx
    rcases hx with ⟨i, hi⟩
    exact hi.trans_le (problem.constraint_le_constrainedAuxiliaryObjective t x i)

/-- Helper for Lemma 2.21: a feasible point whose objective value is below `t + ε` has auxiliary
value at most `ε`. -/
theorem constrainedAuxiliaryObjective_le_of_mem_feasibleSet_lt_add
    {t ε : ℝ} {x : Q} (hx : x ∈ problem.feasibleSet) (hε : 0 ≤ ε)
    (hobj : problem x < t + ε) :
    problem.constrainedAuxiliaryObjective t x ≤ ε := by
  -- Bound each component of the finite maximum by the same threshold `ε`.
  rw [constrainedAuxiliaryObjective]
  refine (maxTypeObjective_le_iff (problem.constrainedAuxiliaryComponents t) x ε).2 ?_
  intro j
  cases j using Fin.cases with
  | zero =>
      -- The objective-gap component is exactly the assumed bound `problem x - t < ε`.
      have hgap : problem x - t < ε := by
        linarith
      simpa using hgap.le
  | succ i =>
      -- Feasibility makes every constraint component nonpositive, hence at most `ε`.
      have hconstraint : problem.constraints i x ≤ 0 := (problem.mem_feasibleSet_iff.mp hx) i
      exact (hconstraint.trans hε)

/-- Lemma 2.21 (below-threshold side): if `t < tStar` and the auxiliary objective attains its
minimum, then the auxiliary optimal value is strictly positive. This is the source-facing
threshold-sign law for the owner value `problem.constrainedAuxiliaryOptimalValue t`; the explicit
attainment input keeps the infimum-to-minimum step faithful to the mathematics. -/
-- Proof sketch: choose a minimizer `x` from `hattained`. By
-- `constrainedAuxiliaryObjective_pos_of_lt`, the real value
-- `problem.constrainedAuxiliaryObjective t x` is strictly positive. The owner bridge theorem
-- `constrainedAuxiliaryOptimalValue_eq_of_isMinOn` then identifies the auxiliary optimal value
-- with that attained real minimum.
theorem constrainedAuxiliaryOptimalValue_pos_of_lt
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : t < tStar)
    (hattained : ∃ x : Q, IsMinOn (problem.constrainedAuxiliaryObjective t) Set.univ x) :
    (0 : EReal) < problem.constrainedAuxiliaryOptimalValue t := by
  rcases hattained with ⟨x, hx⟩
  have hpos : (0 : EReal) < (problem.constrainedAuxiliaryObjective t x : EReal) := by
    exact_mod_cast problem.constrainedAuxiliaryObjective_pos_of_lt htStar t ht x
  rw [problem.constrainedAuxiliaryOptimalValue_eq_of_isMinOn hx]
  exact hpos

/-- The auxiliary optimal value inherits the unconditional lower bound `min (tStar - t) 0` as an
extended-real inequality. -/
-- Proof sketch: apply `min_sub_zero_le_constrainedAuxiliaryObjective` pointwise and pass to the
-- infimum of the range.
theorem min_sub_zero_le_constrainedAuxiliaryOptimalValue
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) :
    ((min (tStar - t) 0 : ℝ) : EReal) ≤ problem.constrainedAuxiliaryOptimalValue t := by
  rw [problem.constrainedAuxiliaryOptimalValue_eq_sInf]
  refine le_sInf ?_
  rintro _ ⟨x, rfl⟩
  -- Lift the pointwise real lower bound to the extended-real infimum.
  change ((min (tStar - t) 0 : ℝ) : EReal) ≤
    (problem.constrainedAuxiliaryObjective t x : EReal)
  exact_mod_cast problem.min_sub_zero_le_constrainedAuxiliaryObjective htStar t x

/-- Lemma 2.21 (above-threshold side): if `tStar ≤ t`, then the auxiliary optimal value is at
most `0`. Together with `constrainedAuxiliaryOptimalValue_pos_of_lt`, this records the two
threshold sign regimes of the source statement in the canonical `EReal` owner API. -/
-- Proof sketch: use the `IsGLB` property of `tStar`, which already forces the feasible set to be
-- nonempty, to choose feasible points with objective values arbitrarily close to `tStar`. For
-- `tStar ≤ t`, the shifted objective values at those points are arbitrarily close to `0` from
-- above and the constraints are nonpositive, so the auxiliary infimum is at most `0`.
theorem constrainedAuxiliaryOptimalValue_nonpos_of_le
    (htStar : IsGLB (Set.range fun x : problem.feasibleSet ↦ problem x) tStar)
    (t : ℝ) (ht : tStar ≤ t) :
    problem.constrainedAuxiliaryOptimalValue t ≤ (0 : EReal) := by
  -- Route correction: make the primal `IsGLB` witness explicit in the theorem header, then use
  -- an `ε`-witness below the positive auxiliary infimum to contradict an arbitrarily good
  -- feasible point coming from `htStar.exists_between_self_add`.
  by_contra hnonpos
  have hpos : (0 : EReal) < problem.constrainedAuxiliaryOptimalValue t := lt_of_not_ge hnonpos
  rcases (EReal.lt_iff_exists_real_btwn).mp hpos with ⟨ε, hεposE, hεlt⟩
  have hεpos : 0 < ε := by
    exact_mod_cast hεposE
  rcases htStar.exists_between_self_add hεpos with ⟨_, ⟨x, rfl⟩, _, hxlt⟩
  have hxlt' : problem (x : Q) < t + ε := by
    exact lt_of_lt_of_le hxlt (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right ht ε)
  have haux_le : problem.constrainedAuxiliaryObjective t (x : Q) ≤ ε := by
    exact problem.constrainedAuxiliaryObjective_le_of_mem_feasibleSet_lt_add
      x.property
      (le_of_lt hεpos)
      hxlt'
  have hopt_le_point :
      problem.constrainedAuxiliaryOptimalValue t ≤
        (problem.constrainedAuxiliaryObjective t (x : Q) : EReal) := by
    simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet
        (problem := SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        (x := (x : Q))
        (by simp))
  have hopt_le_eps : problem.constrainedAuxiliaryOptimalValue t ≤ (ε : EReal) :=
    hopt_le_point.trans (by exact_mod_cast haux_le)
  exact (not_le_of_gt hεlt) hopt_le_eps

end ThresholdBounds

end LagrangianProblem
