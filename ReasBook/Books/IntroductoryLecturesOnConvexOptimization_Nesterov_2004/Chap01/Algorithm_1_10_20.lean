/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set Topology

universe u

variable {α : Type u} [TopologicalSpace α]

/- Algorithm 1.10.20 lies in the barrier / sequential-unconstrained-minimization domain.

Sampled owner-style declarations:
* `SequentialUnconstrainedMinimizationScheme` in `Chap01/Definition_1_10_13`, the chapter owner
  for auxiliary-objective families together with minimizing iterates;
* `PenaltyFunctionMethod` in `Chap01/Algorithm_1_10_11`, the neighboring source-facing algorithm
  that reuses the same owner through a thin bridge;
* `SetConstrainedMinimizationProblem.mk Set.univ ...`, the canonical owner packaging for each
  auxiliary problem on the feasible subtype;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the source-facing barrier predicate on the
  intrinsic interior domain.

Best owner abstraction:
* source-facing: `BarrierFunctionMethod Q 𝓕 objective F`;
* core/canonical: `SequentialUnconstrainedMinimizationScheme ↥(Q ∩ interior 𝓕)`;
* bridge/view: `BarrierFunctionMethod.toSequentialUnconstrainedMinimizationScheme`.

Primitive data:
* the zero-based interior-feasible iterate sequence `xₖ : Q ∩ interior 𝓕`;
* the zero-based barrier parameters `tₖ`;
* the minimizing certificates for the derived auxiliary objectives.

Derived API:
* the method-attached auxiliary objective `method.auxiliaryObjective k`;
* the packaged zero-based auxiliary problem `method.auxiliaryProblem k`;
* the source-facing auxiliary optimal value `method.auxiliaryOptimalValue k`;
* the canonical bridge to `SequentialUnconstrainedMinimizationScheme`.

The file therefore keeps the source-facing zero-based data required by the textbook algorithm, but
attaches the auxiliary objective family to the method itself instead of leaving a free-standing
global wrapper. -/

/-- Algorithm 1.10.20: A barrier function method for `𝓕₀ = Q ∩ interior 𝓕` with barrier `F`
consists of an interior-feasible iterate sequence `xₖ ∈ 𝓕₀` and a strictly increasing parameter
sequence `tₖ > 0` with `tₖ → ∞`, such that for every `k` the next iterate `xₖ₊₁` minimizes
`x ↦ f₀(x) + (1 / tₖ) F(x)` over `𝓕₀`. -/
structure BarrierFunctionMethod
    (Q 𝓕 : Set α)
    (objective : ↥(Q ∩ interior 𝓕) → ℝ)
    (F : C(interior 𝓕, ℝ)) [IsBarrierFunctionOn 𝓕 F] where
  iterates : ℕ → ↥(Q ∩ interior 𝓕)
  barrierParameters : ℕ → ℝ
  barrierParameters_pos : ∀ k : ℕ, 0 < barrierParameters k
  barrierParameters_strictMono : StrictMono barrierParameters
  barrierParameters_tendsto_atTop : Tendsto barrierParameters atTop atTop
  isMinOn_auxiliaryObjective : ∀ k : ℕ,
    IsMinOn
      (fun x ↦ objective x + (1 / barrierParameters k) * F (inclusion inter_subset_right x))
      univ
      (iterates (k + 1))

namespace BarrierFunctionMethod

variable {Q 𝓕 : Set α}
variable {objective : ↥(Q ∩ interior 𝓕) → ℝ} {F : C(interior 𝓕, ℝ)}
variable [IsBarrierFunctionOn 𝓕 F]

local notation "Q₀" => {x // x ∈ Q ∩ interior 𝓕}

/-- The `k`-th auxiliary objective attached to a barrier function method. -/
noncomputable def auxiliaryObjective
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) :
    Q₀ → ℝ :=
  fun x ↦ objective x + (1 / method.barrierParameters k) * F (inclusion inter_subset_right x)

/-- A barrier function method can be used as its underlying sequence of iterates in
`Q ∩ interior 𝓕`. -/
instance :
    CoeFun (BarrierFunctionMethod Q 𝓕 objective F) (fun _ ↦ ℕ → Q₀) where
  coe method := method.iterates

/-- The generic sequential unconstrained minimization scheme attached to a barrier function
method. The owner abstraction uses positive indices, so the `k`-th scheme objective corresponds
to the barrier auxiliary objective with index `k - 1`. -/
noncomputable def toSequentialUnconstrainedMinimizationScheme
    (method : BarrierFunctionMethod Q 𝓕 objective F) :
    SequentialUnconstrainedMinimizationScheme Q₀ where
  auxiliaryObjectives k := method.auxiliaryObjective k.natPred
  iterates k := method (k.natPred + 1)
  isMinOn_auxiliaryObjective k := by
    change
      IsMinOn
        (fun x ↦
          objective x +
            (1 / method.barrierParameters k.natPred) * F (inclusion inter_subset_right x))
        univ
        (method.iterates (k.natPred + 1))
    simpa using method.isMinOn_auxiliaryObjective k.natPred

/-- The `k`-th auxiliary minimization problem `Ψₖ` attached to a barrier function method. -/
noncomputable abbrev auxiliaryProblem
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) :
    SetConstrainedMinimizationProblem Q₀ :=
  method.toSequentialUnconstrainedMinimizationScheme.auxiliaryProblem k.succPNat

/-- The optimal value `Ψₖ*` of the `k`-th auxiliary problem. -/
noncomputable abbrev auxiliaryOptimalValue
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) : EReal :=
  (method.auxiliaryProblem k).optimalValue

/-- The optimal value of the `k`-th auxiliary problem is attained at the selected iterate
`xₖ₊₁`. -/
theorem auxiliaryProblem_optimalValue_eq_iterateValue
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) :
    (method.auxiliaryProblem k).optimalValue =
      (method.auxiliaryObjective k (method (k + 1)) : EReal) :=
  by
    let scheme := method.toSequentialUnconstrainedMinimizationScheme
    simpa [BarrierFunctionMethod.auxiliaryProblem] using
      scheme.auxiliaryProblem_optimalValue_eq_iterateValue k.succPNat

/-- The textbook auxiliary optimal value `Ψₖ*` is the attained value of `Ψₖ` at `xₖ₊₁`. -/
theorem auxiliaryOptimalValue_eq_iterateValue
    (method : BarrierFunctionMethod Q 𝓕 objective F) (k : ℕ) :
    method.auxiliaryOptimalValue k =
      (method.auxiliaryObjective k (method (k + 1)) : EReal) :=
  method.auxiliaryProblem_optimalValue_eq_iterateValue k

end BarrierFunctionMethod
