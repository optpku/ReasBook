/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_22
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped WithTopConvexAnalysis

/- Definition 3.28 lies in the chapter's convex-concave max-representation domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem`
- `SetConstrainedMinimizationProblem.optimalValue`
- `pointwiseSupremumOn`
- the lower-value function `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`

Best owner abstraction:
- source-facing/core: `MaxRepresentationPrimalDualProblem E U`, extending the ambient owner
  `SetConstrainedMinimizationProblem E`
- bridge/view: the inherited owner projection together with
  `objective_eq_pointwiseSupremumOn`, `objective_closedConvex`,
  `objective_eq_kernel_of_isMaxOn`

Primitive data:
- the primal feasible set `P` and objective `f`, owned by
  `SetConstrainedMinimizationProblem E`
- the parameter set `S`
- convexity of the parameter set `S`
- the kernel `Ψ`
- closed-convexity of the primal slices `x ↦ Ψ(x, u)` on `P`
- closed-concavity of the dual slices `u ↦ Ψ(x, u)` on `S`, encoded as closed convexity of
  `u ↦ -Ψ(x, u)`
- the max-attainment representation `f(x) = max_{u ∈ S} Ψ(x, u)` recorded canonically by
  `IsGreatest ((fun u ↦ Ψ x u) '' S) (f x)`

Derived API:
- the inherited owner projection `toSetConstrainedMinimizationProblem`
- the induced convexity of `P`
- the induced nonemptiness of `S` from any feasible point, via `objective_isGreatest`
- the pointwise-supremum bridge for `f`
- the induced closed-convexity of `f`
- the Chapter 1 owner optimal value
  `problem.toSetConstrainedMinimizationProblem.optimalValue`
- the lower-value function
  `u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`

Source/core/bridge triage:
- source-facing: Definition 3.28's primal problem together with its max-representation by a
  convex-concave kernel
- core/canonical: the ambient primal owner plus the kernel-slice hypotheses
- bridge/view: the owner projection and the supremum bridge derived from that owner

This file therefore keeps the source `f` and `Ψ` primitive, but moves the public API away from a
supremum-only wrapper and routes optimal-value and lower-value access through the existing owner
declarations instead of adding parallel aliases. The dual-set convexity remains primitive, while
the primal-set convexity, owner bridges, and max-attainment consequences are kept derived. -/

/-- Definition 3.28, generalized from the textbook `ℝⁿ × ℝᵐ` setting: a convex optimization
problem with a max-representation consists of a convex primal owner on `E`, a convex parameter
set `S ⊆ U`, and a real-valued kernel `Ψ : E → U → ℝ` such that each primal slice
`x ↦ Ψ(x, u)` is closed and convex on `P`, each dual slice `u ↦ Ψ(x, u)` is closed and concave on
`S`, and for every `x ∈ P` the objective value `f(x)` is the maximum of `u ↦ Ψ(x, u)` over
`S`. The textbook `P ⊆ ℝⁿ`, `S ⊆ ℝᵐ` form is recovered by specializing `E` and `U` to Euclidean
spaces. -/
structure MaxRepresentationPrimalDualProblem
    (E : Type u) (U : Type v)
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]
    extends SetConstrainedMinimizationProblem E where
  /-- The parameter set `S ⊆ U` indexing the max-representation. -/
  dualSet : Set U
  /-- The parameter set `S` is convex. -/
  dualSet_convex : Convex ℝ dualSet
  /-- The real-valued kernel `Ψ(x, u)`. -/
  kernel : E → U → ℝ
  /-- Each primal slice `x ↦ Ψ(x, u)` is closed and convex on `P`. -/
  kernel_primal_closedConvex {u : U} (_ : u ∈ dualSet) :
    ClosedConvexOn feasibleSet (fun x ↦ (kernel x u : WithTop ℝ))
  /-- Each dual slice `u ↦ Ψ(x, u)` is closed and concave on `S`, encoded by closed convexity of
  `u ↦ -Ψ(x, u)`. -/
  kernel_dual_closedConcave {x : E} (_ : x ∈ feasibleSet) :
    ClosedConvexOn dualSet (fun u ↦ (-kernel x u : WithTop ℝ))
  /-- On `P`, the objective value is the maximum of `u ↦ Ψ(x, u)` over `S`. -/
  objective_isGreatest {x : E} (_ : x ∈ feasibleSet) :
    IsGreatest (kernel x '' dualSet) (objective x)

namespace MaxRepresentationPrimalDualProblem

variable {E : Type u} {U : Type v}
variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable [TopologicalSpace U] [AddCommMonoid U] [Module ℝ U]

/-- A max-representation primal-dual problem can be used as its primal objective function. -/
instance : CoeFun (MaxRepresentationPrimalDualProblem E U) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a max-representation primal-dual problem returns its primal objective value. -/
@[simp] theorem coe_apply (problem : MaxRepresentationPrimalDualProblem E U) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The primal feasible set is convex, derived from any primal slice when the feasible set is
nonempty and otherwise from `Convex ℝ ∅`. -/
theorem feasibleSet_convex
    (problem : MaxRepresentationPrimalDualProblem E U) :
    Convex ℝ problem.feasibleSet := by
  by_cases hfeasible : problem.feasibleSet.Nonempty
  · rcases hfeasible with ⟨x, hx⟩
    rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, _⟩
    exact (problem.kernel_primal_closedConvex hu).convex
  · rw [Set.not_nonempty_iff_eq_empty] at hfeasible
    simpa [hfeasible] using (convex_empty : Convex ℝ (∅ : Set E))

/-- The parameter set `S` is nonempty because every feasible `x` realizes `f(x)` as
`Ψ(x, u)` for some `u ∈ S`. -/
theorem dualSet_nonempty
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    problem.dualSet.Nonempty := by
  rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, _⟩
  exact ⟨u, hu⟩

/-- On the primal feasible set, the objective agrees with the corresponding pointwise supremum of
the kernel over `S`. This is the bridge from the source-facing max-attainment hypothesis to the
chapter owner `pointwiseSupremumOn`. -/
theorem objective_eq_pointwiseSupremumOn
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) :
    (problem x : WithTop ℝ) =
      pointwiseSupremumOn problem.dualSet
        (fun x' u ↦ (problem.kernel x' u : WithTop ℝ)) x := by
  rw [pointwiseSupremumOn_apply]
  have hobjective :
      IsGreatest
        ((fun u ↦ (problem.kernel x u : WithTop ℝ)) '' problem.dualSet)
        (problem x : WithTop ℝ) := by
    refine ⟨?_, ?_⟩
    · rcases (problem.objective_isGreatest hx).1 with ⟨u, hu, hux⟩
      refine ⟨u, hu, ?_⟩
      exact congrArg (fun t : ℝ ↦ (t : WithTop ℝ)) hux
    · intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      change ((problem.kernel x u : ℝ) : WithTop ℝ) ≤
        ((problem x : ℝ) : WithTop ℝ)
      exact_mod_cast (problem.objective_isGreatest hx).2 ⟨u, hu, rfl⟩
  exact hobjective.csSup_eq.symm

/-- The primal objective is closed and convex on `P`, derived from the primal-slice hypotheses via
the pointwise-supremum owner theorem. -/
theorem objective_closedConvex
    (problem : MaxRepresentationPrimalDualProblem E U) :
    ClosedConvexOn problem.feasibleSet (fun x ↦ (problem x : WithTop ℝ)) := by
  let Φ : E → U → WithTop ℝ := fun x u ↦ (problem.kernel x u : WithTop ℝ)
  by_cases hfeasible : problem.feasibleSet.Nonempty
  · rcases hfeasible with ⟨x₀, hx₀⟩
    have hsup :
        ClosedConvexOn
          (pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ)
          (pointwiseSupremumOn problem.dualSet Φ) :=
      ClosedConvexOn.pointwise_sSup (problem.dualSet_nonempty hx₀) fun u hu ↦
        problem.kernel_primal_closedConvex hu
    have heffective :
        pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ =
          problem.feasibleSet := by
      ext x
      rw [mem_pointwiseSupremumOnEffectiveDomain_iff]
      constructor
      · exact fun hx ↦ hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        rw [mem_withTopEffectiveDomain_iff, ← problem.objective_eq_pointwiseSupremumOn hx]
        exact WithTop.coe_lt_top (problem x)
    have hepigraph :
        constrainedEpigraph problem.feasibleSet (fun x ↦ (problem x : WithTop ℝ)) =
          constrainedEpigraph
            (pointwiseSupremumOnEffectiveDomain problem.feasibleSet problem.dualSet Φ)
            (pointwiseSupremumOn problem.dualSet Φ) := by
      ext p
      rw [mem_constrainedEpigraph_iff, mem_constrainedEpigraph_iff]
      constructor
      · rintro ⟨hp, hp₂⟩
        refine ⟨by simpa [heffective] using hp, ?_⟩
        simpa [Φ, problem.objective_eq_pointwiseSupremumOn hp] using hp₂
      · rintro ⟨hp, hp₂⟩
        have hp' : p.1 ∈ problem.feasibleSet := by
          simpa [heffective] using hp
        refine ⟨hp', ?_⟩
        simpa [Φ, problem.objective_eq_pointwiseSupremumOn hp'] using hp₂
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact
        (show (((problem x : ℝ) : WithTop ℝ) < (⊤ : WithTop ℝ)) from
          WithTop.coe_lt_top (problem x))
    · simpa [hepigraph] using hsup.2.1
    · simpa [hepigraph] using hsup.2.2
  · have hfeasible_eq : problem.feasibleSet = ∅ :=
        by
          ext x
          constructor
          · intro hx
            exact False.elim <| hfeasible ⟨x, hx⟩
          · intro hx
            exact False.elim hx
    refine ⟨?_, ?_, ?_⟩
    · exact by
        simp [hfeasible_eq]
    · exact by
        simp [constrainedEpigraph, hfeasible_eq]
    · simpa [constrainedEpigraph, hfeasible_eq] using
        (convex_empty : Convex ℝ (∅ : Set (E × ℝ)))

/-- If a feasible parameter `u ∈ S` maximizes the slice `Ψ(x, ·)` over `S` at a feasible point
`x ∈ P`, then it realizes the represented objective value `f(x)`. -/
theorem objective_eq_kernel_of_isMaxOn
    (problem : MaxRepresentationPrimalDualProblem E U)
    {x : E} (hx : x ∈ problem.feasibleSet) (u : problem.dualSet)
    (hu : IsMaxOn (problem.kernel x) problem.dualSet u) :
    problem x = problem.kernel x u := by
  rw [isMaxOn_iff] at hu
  have hkernel : IsGreatest (problem.kernel x '' problem.dualSet) (problem.kernel x u) := by
    refine ⟨⟨u, u.2, rfl⟩, ?_⟩
    intro y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact hu v hv
  exact (problem.objective_isGreatest hx).unique hkernel

/-
The relative-subgradient bridge needs the stronger inner-product-space owner used by
`subdifferentialWithin`, but the max-representation owner itself remains at the weaker
topological-module layer above.
-/
section SubgradientBridge

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a feasible point of a max-representation problem, any relative subgradient of an active
slice is also a relative subgradient of the represented objective over the primal feasible set,
written on the chapter's canonical relative-subdifferential surface `∂[Q] f(x)`. -/
theorem subgradient_mem_subdifferentialWithin_of_isMaxOn
    (problem : MaxRepresentationPrimalDualProblem E U) (x : problem.feasibleSet)
    (u : problem.dualSet)
    (hu : IsMaxOn (problem.kernel x) problem.dualSet u)
    {g : E}
    (hg :
      g ∈ ∂[problem.feasibleSet]
        (((fun y ↦ problem.kernel y (u : U)) : E → ℝ))
        ((x : E))) :
    g ∈ ∂[problem.feasibleSet] problem ((x : E)) := by
  rw [mem_subdifferentialWithin_iff] at hg ⊢
  refine ⟨x.2, ?_⟩
  intro y hy
  have hy_kernel :
      problem.kernel y u ≤ problem y :=
    (problem.objective_isGreatest hy).2 ⟨u, u.2, rfl⟩
  calc
    problem y
      ≥ problem.kernel y u := hy_kernel
    _ ≥ problem.kernel x u + inner ℝ g (y - x) := hg.2 hy
    _ = problem x + inner ℝ g (y - x) := by
      rw [problem.objective_eq_kernel_of_isMaxOn x.2 u hu]

/- The primal optimal value is the Chapter 1 owner
`problem.toSetConstrainedMinimizationProblem.optimalValue`, and the lower-value function
`u ↦ inf_{x ∈ P} Ψ(x, u)` is expressed directly as
`u ↦ sInf ((fun x ↦ problem.kernel x u) '' problem.feasibleSet)`.
No parallel aliases are kept here. -/

end SubgradientBridge

end MaxRepresentationPrimalDualProblem

end
