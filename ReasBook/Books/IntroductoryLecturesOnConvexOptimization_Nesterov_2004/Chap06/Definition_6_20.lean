/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module
open scoped Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 6.20 lies in the affine variational-inequality / gap-function smoothing domain.

Mandatory domain-style sampling before refinement:
- `AffineVariationalInequalityProblem` in `Chap06/Definition_6_17`, the Chapter 6 owner of the
  primitive affine-VI data;
- `AffineVariationalInequalityProblem.gapFunction` in `Chap06/Definition_6_18`, the source-facing
  unsmoothed gap object already attached to that owner;
- `smoothedPrimalObjectiveMaximand` in `Chap06/Definition_6_30`, the chapter owner of the
  regularized supremum maximand;
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owner of the corresponding
  regularized supremum objective.

Best owner abstraction:
- source-facing: `AffineVariationalInequalityProblem.smoothedGapFunction`;
- core/canonical under stronger finite-dimensional hypotheses: `smoothedPrimalObjective`,
  specialized on the augmented ambient space `E × ℝ` so that the affine constant term of `B` is
  absorbed into the owner's linear coupling;
- bridge/view: the zero-smoothing specialization recovering `problem.gapFunction`, together with
  the stronger-assumption `StrongDual` realization.

Primitive data:
- `problem : AffineVariationalInequalityProblem E`;
- a prox-function `d : problem.feasibleSet → ℝ`;
- the smoothing weight `μ : ℝ`.

Derived API:
- the source-facing specialization `problem.smoothedGapFunction proxFunction μ`;
- the displayed supremum formula on the feasible subtype;
- the bridge theorem `smoothedGapFunction_zero` back to the canonical gap owner.
- under finite-dimensional continuity hypotheses, the stronger-assumption bridge to
  `smoothedPrimalObjective`, obtained by splitting the affine operator into its constant term and
  linear part and flipping that linear part into the canonical `StrongDual` owner.

Source/core/bridge triage:
- source-facing: `smoothedGapFunction`;
- core/canonical under stronger assumptions: `smoothedPrimalObjective`;
- bridge/view: `smoothedGapFunction_apply`, `smoothedGapFunction_zero`, and the stronger-assumption
  `smoothedGapFunction_eq_smoothedPrimalObjective`.

Because `AffineVariationalInequalityProblem` and `gapFunction` live over `Dual ℝ E`, while
`smoothedPrimalObjective` is formulated using `StrongDual`, the source-facing smoothed gap
function stays at the weaker ambient level. Any `StrongDual` realization is only a
stronger-assumption bridge and not the main public owner.
-/

namespace AffineVariationalInequalityProblem

/-- On finite-dimensional spaces, the linear part of the affine operator can be viewed as a
continuous dual-valued map. -/
def continuousLinearPart [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) : E →L[ℝ] StrongDual ℝ E := by
  let L : E →ₗ[ℝ] StrongDual ℝ E :=
    { toFun := fun x ↦
        { toLinearMap := problem.operator.linear x
          cont := (problem.operator.linear x).continuous_of_finiteDimensional }
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro a x
        ext z
        simp }
  exact
    { toLinearMap := L
      cont := L.continuous_of_finiteDimensional }

/-- The finite-dimensional strong-dual coupling map whose restriction to the slice
`{(v, 1) : v ∈ Q}` recovers the affine operator value `B(v)`. -/
def smoothedGapStrongDualMap [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E) : E →L[ℝ] StrongDual ℝ (E × ℝ) := by
  let L : E →ₗ[ℝ] StrongDual ℝ (E × ℝ) :=
    { toFun := fun w ↦
        ((problem.continuousLinearPart.flip w).comp (ContinuousLinearMap.fst ℝ E ℝ)) +
          (problem 0 w) • ContinuousLinearMap.snd ℝ E ℝ
      map_add' := by
        intro x y
        apply ContinuousLinearMap.ext
        intro p
        cases p
        simp [add_mul, add_assoc, add_left_comm]
      map_smul' := by
        intro a x
        apply ContinuousLinearMap.ext
        intro p
        cases p
        simp [mul_assoc] }
  exact
    { toLinearMap := L
      cont := L.continuous_of_finiteDimensional }

/-- Definition 6.20: for an affine variational inequality problem `VI(Q, B)`, a prox-function
`d : Q → ℝ`, and a smoothing weight `μ`, the smoothed gap function sends a feasible point `w` to
`max_{v ∈ Q} (\langle B(v), w - v \rangle - μ d(v))`, encoded in Lean as a supremum over the
feasible subtype. -/
abbrev smoothedGapFunction
    (problem : AffineVariationalInequalityProblem E)
    (proxFunction : problem.feasibleSet → ℝ) (μ : ℝ) :
    problem.feasibleSet → ℝ :=
  fun w ↦
    sSup
      (Set.range fun v : problem.feasibleSet ↦
        problem v ((w : E) - v) - μ * proxFunction v)

/-- Evaluating the smoothed gap function recovers the textbook supremum formula
`max_{v ∈ Q} (\langle B(v), w - v \rangle - μ d(v))`, encoded as a supremum over the feasible
subtype. -/
@[simp] theorem smoothedGapFunction_apply
    (problem : AffineVariationalInequalityProblem E)
    (proxFunction : problem.feasibleSet → ℝ) (μ : ℝ) (w : problem.feasibleSet) :
    problem.smoothedGapFunction proxFunction μ w =
      sSup
        (Set.range
          (fun v : problem.feasibleSet ↦
            problem v ((w : E) - v) - μ * proxFunction v)) :=
  rfl

/-- Setting the smoothing weight to `0` recovers the canonical affine-VI gap function. -/
@[simp] theorem smoothedGapFunction_zero
    (problem : AffineVariationalInequalityProblem E)
    (proxFunction : problem.feasibleSet → ℝ) :
    problem.smoothedGapFunction proxFunction 0 = problem.gapFunction := by
  funext w
  rw [problem.smoothedGapFunction_apply, problem.gapFunction_apply]
  refine congrArg (sSup : Set ℝ → ℝ) ?_
  ext r
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    ring_nf
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    ring_nf

/-- Pointwise, the zero-smoothing specialization of `smoothedGapFunction` agrees with the
canonical gap function. -/
@[simp] theorem smoothedGapFunction_zero_apply
    (problem : AffineVariationalInequalityProblem E)
    (proxFunction : problem.feasibleSet → ℝ) (w : problem.feasibleSet) :
    problem.smoothedGapFunction proxFunction 0 w = problem.gapFunction w := by
  exact congrArg (fun f : problem.feasibleSet → ℝ ↦ f w)
    (problem.smoothedGapFunction_zero proxFunction)

/-- Under a finite-dimensional strong-dual realization of the linear part of the affine operator
and an ambient extension of the prox-function, the source-facing smoothed gap function is the
chapter owner `smoothedPrimalObjective` specialized to the slice `Q × {1}`. -/
theorem smoothedGapFunction_eq_smoothedPrimalObjective
    [FiniteDimensional ℝ E]
    (problem : AffineVariationalInequalityProblem E)
    (proxFunction : problem.feasibleSet → ℝ) (proxExtension : E → ℝ)
    (hprox : ∀ v : problem.feasibleSet, proxExtension v = proxFunction v)
    (μ : ℝ) (w : problem.feasibleSet) :
    problem.smoothedGapFunction proxFunction μ w =
      smoothedPrimalObjective
        problem.smoothedGapStrongDualMap
        (Set.range fun v : problem.feasibleSet ↦ ((v : E), (1 : ℝ)))
        0
        (fun z : E × ℝ ↦ problem.operator.linear z.1 z.1 + z.2 * problem 0 z.1)
        (fun z : E × ℝ ↦ proxExtension z.1)
        μ
        (w : E) := by
  have hproblem_w (v : problem.feasibleSet) :
      problem v (w : E) =
        problem.operator.linear (v : E) (w : E) + problem 0 (w : E) := by
    simpa [Pi.add_apply] using
      congrArg (fun f : E → Dual ℝ E ↦ f (v : E) (w : E)) problem.operator.decomp
  have hproblem_v (v : problem.feasibleSet) :
      problem v (v : E) =
        problem.operator.linear (v : E) (v : E) + problem 0 (v : E) := by
    simpa [Pi.add_apply] using
      congrArg (fun f : E → Dual ℝ E ↦ f (v : E) (v : E)) problem.operator.decomp
  have hvalue (v : problem.feasibleSet) :
      smoothedPrimalObjectiveMaximand
          problem.smoothedGapStrongDualMap
          (fun z : E × ℝ ↦ problem.operator.linear z.1 z.1 + z.2 * problem 0 z.1)
          (fun z : E × ℝ ↦ proxExtension z.1)
          μ
          (w : E)
          ((v : E), (1 : ℝ)) =
        problem v ((w : E) - v) - μ * proxFunction v := by
    calc
      smoothedPrimalObjectiveMaximand
          problem.smoothedGapStrongDualMap
          (fun z : E × ℝ ↦ problem.operator.linear z.1 z.1 + z.2 * problem 0 z.1)
          (fun z : E × ℝ ↦ proxExtension z.1)
          μ
          (w : E)
          ((v : E), (1 : ℝ)) =
        problem.operator.linear (v : E) (w : E) + problem 0 (w : E) -
          (problem.operator.linear (v : E) (v : E) + problem 0 (v : E)) -
            μ * proxExtension (v : E) := by
          simp [smoothedPrimalObjectiveMaximand, smoothedGapStrongDualMap, continuousLinearPart,
            ContinuousLinearMap.flip_apply]
      _ = problem v (w : E) - problem v (v : E) - μ * proxExtension (v : E) := by
        rw [hproblem_w v, hproblem_v v]
      _ = problem v ((w : E) - v) - μ * proxExtension (v : E) := by
        rw [LinearMap.map_sub]
      _ = problem v ((w : E) - v) - μ * proxFunction v := by
        rw [hprox v]
  simp only [problem.smoothedGapFunction_apply, smoothedPrimalObjective_apply, Pi.zero_apply,
    zero_add]
  refine congrArg (sSup : Set ℝ → ℝ) ?_
  ext r
  constructor
  · rintro ⟨v, hvr⟩
    refine ⟨((v : E), (1 : ℝ)), ?_, ?_⟩
    · exact ⟨v, rfl⟩
    · exact (hvalue v).trans hvr
  · rintro ⟨z, hz, hzr⟩
    rcases hz with ⟨u, rfl⟩
    exact ⟨u, (hvalue u).symm.trans hzr⟩

end AffineVariationalInequalityProblem

end
