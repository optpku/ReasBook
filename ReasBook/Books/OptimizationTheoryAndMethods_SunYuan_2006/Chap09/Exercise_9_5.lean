/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Order.SaddlePoint
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_24
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_4_1

noncomputable section

section Chapter09Exercise95

variable {n m : ℕ}

local notation "Point" => Fin n → ℝ
local notation "Multiplier" => Fin m → ℝ
local notation "EMultiplier" => EuclideanSpace ℝ (Fin m)

-- Domain-style sampling:
-- * primary domain: convex programming duality for inequality-only constrained problems
-- * inspected owner declarations:
--   `ConstrainedOptimizationProblem.feasibleSet` from `Chapter01.Definition_1_1_extra_1`
--   `ConstrainedOptimizationProblem.IsGlobalMinimizer` from `Chapter08.Definition_8_1_2`
--   `ConstrainedOptimizationProblem.IsDualOptimalPair` and
--   `ConstrainedOptimizationProblem.admissibleMultiplierSet` from `Chapter08.Theorem_8_4_1`
--   `IsSaddlePointOn` from mathlib
-- * best owner abstraction: the Chapter 8 inequality-only constrained-problem owner
--   `ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ`
-- * primitive data vs. derived API:
--   the primitive data are already upstream in `ConstrainedOptimizationProblem`;
--   this file keeps only the derived Slater-condition predicate, the saddle-pair predicate,
--   and the exercise theorem
-- * layer triage:
--   source-facing: `problem.SatisfiesSlaterCondition` and `problem.IsSaddlePair`
--   core/canonical: `problem.IsGlobalMinimizer`, `problem.admissibleMultiplierSet`,
--   `𝓛[problem](x, lam)`, and `IsSaddlePointOn`
--   bridge/view: `problem.IsDualOptimalPair xStar lamStar` from Chapter 8

namespace ConstrainedOptimizationProblem

/-- `problem.SatisfiesSlaterCondition` means that `problem` has a strictly feasible point. -/
def SatisfiesSlaterCondition
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) : Prop :=
  ∃ x : Point, ∀ i : Fin m, 0 < problem.constraint i x

/-- `problem.IsSaddlePair xStar lamStar` means that `xStar` is feasible, `lamStar` is admissible,
and `(xStar, lamStar)` is a saddle point of `𝓛[problem]` on
`problem.feasibleSet × problem.admissibleMultiplierSet`. -/
def IsSaddlePair
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (lamStar : Multiplier) : Prop :=
  xStar ∈ problem ∧
    lamStar ∈ problem.admissibleMultiplierSet ∧
      IsSaddlePointOn problem.feasibleSet problem.admissibleMultiplierSet
        (fun x lam ↦ 𝓛[problem](x, lam)) xStar lamStar

/-- `problem.IsSaddlePair xStar lamStar` is equivalent to the saddle-point inequalities
`𝓛[problem](xStar, λ) ≤ 𝓛[problem](xStar, lamStar) ≤ 𝓛[problem](x, lamStar)` for all
`x ∈ problem` and all admissible `λ`. -/
theorem isSaddlePair_iff
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (lamStar : Multiplier) :
    problem.IsSaddlePair xStar lamStar ↔
      xStar ∈ problem ∧
        lamStar ∈ problem.admissibleMultiplierSet ∧
          (∀ lam ∈ problem.admissibleMultiplierSet,
            𝓛[problem](xStar, lam) ≤ 𝓛[problem](xStar, lamStar)) ∧
            ∀ x ∈ problem,
              𝓛[problem](xStar, lamStar) ≤ 𝓛[problem](x, lamStar) := by
  constructor
  · rintro ⟨hxStar, hlamStar, hsaddle⟩
    refine ⟨hxStar, hlamStar, ?_, ?_⟩
    · intro lam hlam
      exact hsaddle xStar hxStar lam hlam
    · intro x hx
      exact hsaddle x hx lamStar hlamStar
  · rintro ⟨hxStar, hlamStar, hleft, hright⟩
    refine ⟨hxStar, hlamStar, ?_⟩
    intro x hx lam hlam
    exact le_trans (hleft lam hlam) (hright x hx)

/-- Helper for Chapter09 Exercise 9.5: a saddle pair immediately yields a constrained global
minimizer because the saddle inequalities compare the primal objective to every feasible value. -/
theorem isGlobalMinimizer_of_isSaddlePair
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xStar : Point} {lamStar : Multiplier}
    (h_saddle : problem.IsSaddlePair xStar lamStar) :
    problem.IsGlobalMinimizer xStar := by
  rcases (problem.isSaddlePair_iff xStar lamStar).mp h_saddle with
    ⟨hxStar, hlamStar, hleft, hright⟩
  rw [problem.isGlobalMinimizer_iff]
  refine ⟨hxStar, ?_⟩
  rw [isMinOn_iff]
  intro x hx
  have h_zero_mem : (0 : Multiplier) ∈ problem.admissibleMultiplierSet := by
    -- The zero multiplier is admissible because every component is nonnegative.
    intro i
    simp
  have h_objective_eq_lagrangian_zero :
      problem.objective xStar = 𝓛[problem](xStar, (0 : Multiplier)) := by
    -- At the zero multiplier, the Lagrangian is exactly the primal objective.
    simp [ConstrainedOptimizationProblem.lagrangian]
  -- Compare through the saddle point and then return to the primal objective at the feasible point.
  calc
    problem.objective xStar = 𝓛[problem](xStar, (0 : Multiplier)) := h_objective_eq_lagrangian_zero
    _ ≤ 𝓛[problem](xStar, lamStar) := hleft 0 h_zero_mem
    _ ≤ 𝓛[problem](x, lamStar) := hright x hx
    _ ≤ problem.objective x :=
      problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet hx hlamStar

/-- Helper for Chapter09 Exercise 9.5: the Chapter 8 dual objective is definitionally the infimum
of the WithBot-valued Lagrangian family. -/
theorem dualObjective_eq_iInf_lagrangian
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lam : Multiplier) :
    problem.dualObjective lam = ⨅ x : Point, (((𝓛[problem](x, lam) : ℝ) : WithBot ℝ)) :=
  rfl

/-- Helper for Chapter09 Exercise 9.5: once an admissible multiplier attains the primal value in
the dual objective, the primal point and multiplier satisfy the saddle inequalities. -/
theorem isSaddlePair_of_dualObjective_eq_objective
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xStar : Point} {lamStar : Multiplier}
    (hxStar : xStar ∈ problem) (hlamStar : lamStar ∈ problem.admissibleMultiplierSet)
    (h_value : problem.dualObjective lamStar = ((problem.objective xStar : ℝ) : WithBot ℝ)) :
    problem.IsSaddlePair xStar lamStar := by
  have h_lagrangian_le_objective :
      𝓛[problem](xStar, lamStar) ≤ problem.objective xStar :=
    problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet hxStar hlamStar
  have h_objective_le_lagrangian :
      problem.objective xStar ≤ 𝓛[problem](xStar, lamStar) := by
    -- The dual-value equality and weak duality force equality at `(xStar, lamStar)`.
    have h_withBot :
        ((problem.objective xStar : ℝ) : WithBot ℝ) ≤
          ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := by
      calc
        ((problem.objective xStar : ℝ) : WithBot ℝ) = problem.dualObjective lamStar := h_value.symm
        _ ≤ ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) :=
          problem.dualObjective_le_lagrangian xStar lamStar
    exact_mod_cast h_withBot
  have h_lagrangian_eq_objective :
      𝓛[problem](xStar, lamStar) = problem.objective xStar :=
    le_antisymm h_lagrangian_le_objective h_objective_le_lagrangian
  have h_left :
      ∀ lam ∈ problem.admissibleMultiplierSet,
        𝓛[problem](xStar, lam) ≤ 𝓛[problem](xStar, lamStar) := by
    intro lam hlam
    -- The left saddle inequality comes from weak duality at the feasible point `xStar`.
    calc
      𝓛[problem](xStar, lam) ≤ problem.objective xStar :=
        problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet hxStar hlam
      _ = 𝓛[problem](xStar, lamStar) := h_lagrangian_eq_objective.symm
  have h_right :
      ∀ x ∈ problem, 𝓛[problem](xStar, lamStar) ≤ 𝓛[problem](x, lamStar) := by
    intro x hx
    -- The right saddle inequality comes from the dual objective lower bound at `lamStar`.
    have h_withBot :
        ((problem.objective xStar : ℝ) : WithBot ℝ) ≤
          ((𝓛[problem](x, lamStar) : ℝ) : WithBot ℝ) := by
      calc
        ((problem.objective xStar : ℝ) : WithBot ℝ) = problem.dualObjective lamStar := h_value.symm
        _ ≤ ((𝓛[problem](x, lamStar) : ℝ) : WithBot ℝ) :=
          problem.dualObjective_le_lagrangian x lamStar
    have h_objective_le_lagrangian_x : problem.objective xStar ≤ 𝓛[problem](x, lamStar) := by
      exact_mod_cast h_withBot
    calc
      𝓛[problem](xStar, lamStar) = problem.objective xStar := h_lagrangian_eq_objective
      _ ≤ 𝓛[problem](x, lamStar) := h_objective_le_lagrangian_x
  rw [problem.isSaddlePair_iff]
  exact ⟨hxStar, hlamStar, h_left, h_right⟩

/-- Helper for Chapter09 Exercise 9.5: the perturbation set records every pair consisting of a
lower bound on the inequality-constraint values and an upper bound on the objective value,
realized by some primal point. -/
def perturbationSet
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) :
    Set (EMultiplier × ℝ) :=
  {ur |
    ∃ x : Point,
      (∀ i : Fin m, ur.1.ofLp i ≤ problem.constraint i x) ∧
        problem.objective x ≤ ur.2}

/-- Helper for Chapter09 Exercise 9.5: the supporting-sunYuanHyperplane argument is carried out on the
`L²` lift of the perturbation set, so each plain perturbation pair is sent through `WithLp.toLp 2`.
-/
def liftedPerturbationSet
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) :
    Set (WithLp 2 (EMultiplier × ℝ)) :=
  (WithLp.toLp 2) '' problem.perturbationSet

/-- Helper for Chapter09 Exercise 9.5: the anchored frontier point in the lifted perturbation
space has zero perturbation component and scalar coordinate `problem.objective xStar`. -/
def liftedPrimalValuePair
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) : WithLp 2 (EMultiplier × ℝ) :=
  WithLp.toLp 2
    ((((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ))

/-- Helper for Chapter09 Exercise 9.5: membership in the perturbation set unfolds to the realizing
point together with the constraint and objective bounds. -/
theorem mem_perturbationSet_iff
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (ur : EMultiplier × ℝ) :
    ur ∈ problem.perturbationSet ↔
      ∃ x : Point,
        (∀ i : Fin m, ur.1.ofLp i ≤ problem.constraint i x) ∧
          problem.objective x ≤ ur.2 :=
  Iff.rfl

/-- Helper for Chapter09 Exercise 9.5: the perturbation set is convex because convex combinations
of realizing primal points preserve the upper objective bound and the lower constraint bounds. -/
theorem perturbation_set_convex
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    Convex ℝ problem.perturbationSet := by
  -- Follow the source proof route: realize both endpoints by primal points and combine them.
  refine convex_iff_segment_subset.2 ?_
  intro p hp q hq z hz
  rcases (problem.mem_perturbationSet_iff p).mp hp with ⟨x, hxineq, hxobj⟩
  rcases (problem.mem_perturbationSet_iff q).mp hq with ⟨y, hyineq, hyobj⟩
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  refine (problem.mem_perturbationSet_iff _).2 ?_
  refine ⟨a • x + b • y, ?_, ?_⟩
  · intro i
    -- The lower perturbation coordinates are preserved by concavity of each constraint.
    have h_concave :
        a * problem.constraint i x + b * problem.constraint i y ≤
          problem.constraint i (a • x + b • y) :=
      (h_constraint_concave i).2 (x := x) (by simp) (y := y) (by simp) ha hb hab
    have h_linear :
        (((a • p.1 + b • q.1).ofLp i : ℝ)) =
          a * p.1.ofLp i + b * q.1.ofLp i := by
      simp
    change (((a • p.1 + b • q.1).ofLp i : ℝ)) ≤ problem.constraint i (a • x + b • y)
    rw [h_linear]
    have hpx : a * p.1.ofLp i ≤ a * problem.constraint i x :=
      mul_le_mul_of_nonneg_left (hxineq i) ha
    have hqy : b * q.1.ofLp i ≤ b * problem.constraint i y :=
      mul_le_mul_of_nonneg_left (hyineq i) hb
    calc
      a * p.1.ofLp i + b * q.1.ofLp i
          ≤ a * problem.constraint i x + b * problem.constraint i y := by
            linarith
      _ ≤ problem.constraint i (a • x + b • y) := h_concave
  · -- The objective upper bound is preserved by convexity of the objective.
    have h_convex :
        problem.objective (a • x + b • y) ≤
          a * problem.objective x + b * problem.objective y :=
      h_objective_convex.2 (x := x) (by simp) (y := y) (by simp) ha hb hab
    have h_linear :
        ((a • p.2 + b • q.2 : ℝ)) =
          a * p.2 + b * q.2 := by
      ring
    change problem.objective (a • x + b • y) ≤ ((a • p.2 + b • q.2 : ℝ))
    rw [h_linear]
    have hxobj' : a * problem.objective x ≤ a * p.2 :=
      mul_le_mul_of_nonneg_left hxobj ha
    have hyobj' : b * problem.objective y ≤ b * q.2 :=
      mul_le_mul_of_nonneg_left hyobj hb
    calc
      problem.objective (a • x + b • y)
          ≤ a * problem.objective x + b * problem.objective y := h_convex
      _ ≤ a * p.2 + b * q.2 := by
            linarith

/-- Helper for Chapter09 Exercise 9.5: convexity of the plain perturbation set transports
through the `WithLp` linear equivalence to the Hilbert-space lift used for separation. -/
theorem lifted_perturbation_set_convex
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    Convex ℝ problem.liftedPerturbationSet := by
  simpa [ConstrainedOptimizationProblem.liftedPerturbationSet] using
    (problem.perturbation_set_convex h_objective_convex h_constraint_concave).linear_image
      ((WithLp.linearEquiv 2 ℝ (EMultiplier × ℝ)).symm.toLinearMap)

/-- Helper for Chapter09 Exercise 9.5: the perturbation pair with zero multiplier component and
the primal optimal value lies on the frontier of the perturbation set. -/
theorem primal_value_pair_mem_frontier_perturbation_set
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar) :
    (((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ) ∈
      frontier problem.perturbationSet := by
  refine ⟨?_, ?_⟩
  · -- Feasibility of `xStar` puts the primal-value pair directly in the perturbation set.
    refine subset_closure ?_
    refine (problem.mem_perturbationSet_iff _).2 ?_
    refine ⟨xStar, ?_, le_rfl⟩
    intro i
    have hxStar_feasible : xStar ∈ problem.feasibleSet := by
      simpa [problem.feasibleSet_eq_setOf_mem] using h_min.feasible
    have hxStar_nonneg :=
      (problem.mem_feasibleSet_iff xStar).mp hxStar_feasible |>.2 i
        (by simp [ConstrainedOptimizationProblem.ineqIndices])
    change (0 : ℝ) ≤ problem.constraint i xStar
    exact hxStar_nonneg
  · -- Lowering only the objective coordinate leaves every neighborhood of the point, so the
    -- pair cannot be interior.
    intro hInterior
    rw [mem_interior_iff_mem_nhds] at hInterior
    rcases Metric.mem_nhds_iff.mp hInterior with ⟨ε, hε, hball⟩
    let z : EMultiplier × ℝ :=
      (WithLp.toLp 2 (0 : Multiplier), problem.objective xStar - ε / 2)
    have hz_mem_ball :
        z ∈ Metric.ball
          (((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ) ε := by
      change dist z
          (((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ) < ε
      have hdist :
          dist z
              (((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ) =
            |ε| / 2 := by
        simp [z]
      rw [hdist]
      have habs : |ε| = ε := abs_of_pos hε
      nlinarith
    have hz_mem : z ∈ problem.perturbationSet := hball hz_mem_ball
    rcases (problem.mem_perturbationSet_iff z).mp hz_mem with ⟨x, hxineq, hxobj⟩
    have hx_feasible : x ∈ problem := by
      change x ∈ problem.feasibleSet
      rw [problem.mem_feasibleSet_iff]
      refine ⟨?_, ?_⟩
      · intro i hi
        simp [ConstrainedOptimizationProblem.eqIndices] at hi
      · intro i hi
        simpa [z] using hxineq i
    have h_opt := h_min.objective_le hx_feasible
    have : ¬ problem.objective x ≤ problem.objective xStar - ε / 2 := by
      have hhalf_pos : 0 < ε / 2 := by positivity
      linarith
    exact this hxobj

/-- Helper for Chapter09 Exercise 9.5: the frontier point of the plain perturbation set remains a
frontier point after transporting the set into the `WithLp` Hilbert space. -/
theorem lifted_primal_value_pair_mem_frontier_perturbation_set
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar) :
    problem.liftedPrimalValuePair xStar ∈ frontier problem.liftedPerturbationSet := by
  let e : (EMultiplier × ℝ) ≃L[ℝ] WithLp 2 (EMultiplier × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ EMultiplier ℝ).symm
  rw [show problem.liftedPerturbationSet = e '' problem.perturbationSet by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨w, hw, rfl⟩]
  change problem.liftedPrimalValuePair xStar ∈ frontier (e.toHomeomorph '' problem.perturbationSet)
  rw [← e.toHomeomorph.image_frontier problem.perturbationSet]
  refine ⟨
    (((WithLp.toLp 2 (0 : Multiplier)), problem.objective xStar) : EMultiplier × ℝ),
    problem.primal_value_pair_mem_frontier_perturbation_set xStar h_min,
    rfl⟩

/-- Helper for Chapter09 Exercise 9.5: once an admissible multiplier makes the primal value a
global lower bound for the Lagrangian, the Chapter 8 attained-dual API identifies the dual value
with that primal value. -/
theorem dualObjective_eq_objective_of_lagrangian_global_lower_bound
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xStar : Point} {lamStar : Multiplier}
    (hxStar : xStar ∈ problem) (hlamStar : lamStar ∈ problem.admissibleMultiplierSet)
    (h_lower : ∀ x : Point, problem.objective xStar ≤ 𝓛[problem](x, lamStar)) :
    problem.dualObjective lamStar = ((problem.objective xStar : ℝ) : WithBot ℝ) := by
  -- First package the lower bound as attainment of the Lagrangian infimum at `xStar`.
  have h_attain : IsMinOn (fun y : Point ↦ 𝓛[problem](y, lamStar)) Set.univ xStar := by
    have h_lagrangian_eq_objective :
        𝓛[problem](xStar, lamStar) = problem.objective xStar := by
      refine le_antisymm
        (problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet hxStar hlamStar)
        (h_lower xStar)
    rw [isMinOn_iff]
    intro y hy
    calc
      𝓛[problem](xStar, lamStar) = problem.objective xStar := h_lagrangian_eq_objective
      _ ≤ 𝓛[problem](y, lamStar) := h_lower y
  have h_attained : (xStar, lamStar) ∈ problem.attainedDualFeasibleSet := by
    exact ⟨h_attain, hlamStar⟩
  have h_dual_eq_lagrangian :
      problem.dualObjective lamStar = ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := by
    exact problem.dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet h_attained
  have h_lagrangian_eq_objective :
      𝓛[problem](xStar, lamStar) = problem.objective xStar := by
    -- Feasibility gives the upper inequality; the lower-bound hypothesis gives the reverse one.
    refine le_antisymm
      (problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet hxStar hlamStar)
      (h_lower xStar)
  calc
    problem.dualObjective lamStar = ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) :=
      h_dual_eq_lagrangian
    _ = ((problem.objective xStar : ℝ) : WithBot ℝ) := by
          exact_mod_cast h_lagrangian_eq_objective

/-- Helper for Chapter09 Exercise 9.5: a realized perturbation point in the supporting
half-space gives the scalar inequality relating the support vector to the perturbation data. -/
theorem supporting_vector_ineq_of_perturbation_realizer
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xStar x : Point} {mu : EMultiplier} {beta r : ℝ} {u : EMultiplier}
    (h_support :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar)))
    (hu : ∀ i : Fin m, u.ofLp i ≤ problem.constraint i x)
    (hr : problem.objective x ≤ r) :
    inner ℝ mu u + beta * (r - problem.objective xStar) ≤ 0 := by
  have hur_mem :
      WithLp.toLp 2 ((u, r) : EMultiplier × ℝ) ∈ problem.liftedPerturbationSet := by
    -- Package the realizing point `x` into the lifted perturbation-set definition.
    exact ⟨(u, r), (problem.mem_perturbationSet_iff _).2 ⟨x, hu, hr⟩, rfl⟩
  have hur_halfspace :
      WithLp.toLp 2 ((u, r) : EMultiplier × ℝ) ∈
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar)) :=
    h_support (subset_closure hur_mem)
  have hur_scalar :
      r * beta + inner ℝ mu u ≤ problem.objective xStar * beta := by
    simpa [ConstrainedOptimizationProblem.liftedPrimalValuePair, closedLowerHalfSpace,
      WithLp.prod_inner_apply, add_comm, add_left_comm, add_assoc] using hur_halfspace
  -- Scalarize the product half-space inequality at the anchored primal-value pair.
  nlinarith

/-- Helper for Chapter09 Exercise 9.5: evaluating the supporting inequality at the vertical
perturbation point `(0, f(xStar) + 1)` forces the scalar component `beta` to be nonpositive. -/
theorem supporting_vector_beta_nonpos
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar)
    {mu : EMultiplier} {beta : ℝ}
    (h_support :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar))) :
    beta ≤ 0 := by
  have hxStar_feasible : xStar ∈ problem.feasibleSet := by
    simpa [problem.feasibleSet_eq_setOf_mem] using h_min.feasible
  have hxStar_nonneg : ∀ i : Fin m, 0 ≤ problem.constraint i xStar := by
    intro i
    exact (problem.mem_feasibleSet_iff xStar).mp hxStar_feasible |>.2 i
      (by simp [ConstrainedOptimizationProblem.ineqIndices])
  have hscalar :=
    problem.supporting_vector_ineq_of_perturbation_realizer
      (xStar := xStar) (x := xStar) (mu := mu) (beta := beta)
      (u := WithLp.toLp 2 (0 : Multiplier)) (r := problem.objective xStar + 1)
      h_support
      (fun i ↦ by simpa using hxStar_nonneg i)
      (by linarith)
  -- The vertical test point leaves only the `beta` contribution.
  simpa using hscalar

/-- Helper for Chapter09 Exercise 9.5: evaluating the supporting inequality at the coordinate
perturbation point `(-e_i, f(xStar))` forces the `i`-th support coefficient to be nonnegative. -/
theorem supporting_vector_component_nonneg
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar)
    {mu : EMultiplier} {beta : ℝ}
    (h_support :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar)))
    (i : Fin m) :
    0 ≤ mu.ofLp i := by
  have hxStar_feasible : xStar ∈ problem.feasibleSet := by
    simpa [problem.feasibleSet_eq_setOf_mem] using h_min.feasible
  have hxStar_nonneg : ∀ j : Fin m, 0 ≤ problem.constraint j xStar := by
    intro j
    exact (problem.mem_feasibleSet_iff xStar).mp hxStar_feasible |>.2 j
      (by simp [ConstrainedOptimizationProblem.ineqIndices])
  have hscalar :=
    problem.supporting_vector_ineq_of_perturbation_realizer
      (xStar := xStar) (x := xStar) (mu := mu) (beta := beta)
      (u := WithLp.toLp 2 (-Pi.single i (1 : ℝ))) (r := problem.objective xStar)
      h_support
      (fun j ↦ by
        by_cases hji : j = i
        · have hnonneg := hxStar_nonneg j
          have hbound : (-1 : ℝ) ≤ problem.constraint j xStar := by
            linarith
          simpa [Pi.single_apply, hji] using hbound
        · simpa [Pi.single_apply, hji] using hxStar_nonneg j)
      le_rfl
  -- The coordinate test point isolates the `i`-th support coefficient.
  simpa [PiLp.inner_apply, dotProduct, Pi.single_apply, mul_comm] using hscalar

/-- Helper for Chapter09 Exercise 9.5: Slater's strictly feasible perturbation point upgrades
`beta ≤ 0` to `beta < 0`, so the support vector can be normalized into a multiplier. -/
theorem supporting_vector_beta_neg_of_slater
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    {xStar : Point} (h_slater : problem.SatisfiesSlaterCondition)
    {mu : EMultiplier} {beta : ℝ}
    (hp_ne : ((mu, beta) : EMultiplier × ℝ) ≠ 0)
    (h_support :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar)))
    (hbeta_nonpos : beta ≤ 0)
    (hmu_nonneg : ∀ i : Fin m, 0 ≤ mu.ofLp i) :
    beta < 0 := by
  by_contra hbeta_not_neg
  have hbeta_zero : beta = 0 := by linarith
  have hmu_ne : mu ≠ 0 := by
    intro hmu_zero
    apply hp_ne
    ext <;> simp [hmu_zero, hbeta_zero]
  have hmu_ofLp_ne : ∃ i : Fin m, mu.ofLp i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hmu_ne
    have hmu_ofLp_zero : mu.ofLp = (0 : Multiplier) := by
      funext i
      exact hnone i
    simpa using congrArg (WithLp.toLp 2) hmu_ofLp_zero
  rcases h_slater with ⟨x0, hx0⟩
  rcases hmu_ofLp_ne with ⟨i0, hi0⟩
  let u0 : Multiplier := fun i ↦ problem.constraint i x0 / 2
  have hu0_le : ∀ i : Fin m, (WithLp.toLp 2 u0).ofLp i ≤ problem.constraint i x0 := by
    intro i
    change u0 i ≤ problem.constraint i x0
    have hpos := hx0 i
    dsimp [u0]
    nlinarith
  have hscalar :=
    problem.supporting_vector_ineq_of_perturbation_realizer
      (xStar := xStar) (x := x0) (mu := mu) (beta := beta)
      (u := WithLp.toLp 2 u0) (r := problem.objective x0)
      h_support hu0_le le_rfl
  have hinner_nonpos : inner ℝ mu (WithLp.toLp 2 u0) ≤ 0 := by
    simpa [hbeta_zero] using hscalar
  have hmu_i0_pos : 0 < mu.ofLp i0 := by
    exact lt_of_le_of_ne (hmu_nonneg i0) (Ne.symm hi0)
  have hu0_pos : ∀ i : Fin m, 0 < u0 i := by
    intro i
    dsimp [u0]
    nlinarith [hx0 i]
  have hterm_nonneg : ∀ i : Fin m, 0 ≤ mu.ofLp i * u0 i := by
    intro i
    exact mul_nonneg (hmu_nonneg i) (le_of_lt (hu0_pos i))
  have hterm_pos : 0 < mu.ofLp i0 * u0 i0 := by
    exact mul_pos hmu_i0_pos (hu0_pos i0)
  have hsum_pos : 0 < ∑ i : Fin m, mu.ofLp i * u0 i := by
    have hsingle :
        mu.ofLp i0 * u0 i0 ≤ ∑ i : Fin m, mu.ofLp i * u0 i := by
      simpa using Finset.single_le_sum (fun j _ ↦ hterm_nonneg j) (Finset.mem_univ i0)
    exact lt_of_lt_of_le hterm_pos hsingle
  have hinner_pos : 0 < inner ℝ mu (WithLp.toLp 2 u0) := by
    -- The strictly feasible perturbation has every coordinate positive, so one positive support
    -- coefficient makes the whole inner product positive.
    simpa [u0, PiLp.inner_apply, dotProduct, mul_comm] using hsum_pos
  linarith

/-- Helper for Chapter09 Exercise 9.5: a supporting vector at the primal-value frontier point
normalizes to an admissible multiplier whose Lagrangian dominates the primal optimum globally. -/
theorem exists_multiplier_lagrangian_lower_bound_of_supporting_vector
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar)
    (h_slater : problem.SatisfiesSlaterCondition)
    {mu : EMultiplier} {beta : ℝ}
    (hp_ne : ((mu, beta) : EMultiplier × ℝ) ≠ 0)
    (h_support :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar))) :
    ∃ lamStar : Multiplier,
      lamStar ∈ problem.admissibleMultiplierSet ∧
        ∀ x : Point, problem.objective xStar ≤ 𝓛[problem](x, lamStar) := by
  -- Route correction: first scalarize the supporting half-space inequality, then extract signs,
  -- and only then divide by `-beta`.
  have hbeta_nonpos :
      beta ≤ 0 :=
    problem.supporting_vector_beta_nonpos xStar h_min h_support
  have hmu_nonneg : ∀ i : Fin m, 0 ≤ mu.ofLp i := by
    intro i
    exact problem.supporting_vector_component_nonneg xStar h_min h_support i
  have hbeta_neg :
      beta < 0 :=
    problem.supporting_vector_beta_neg_of_slater h_slater hp_ne h_support hbeta_nonpos hmu_nonneg
  let lamStar : Multiplier := fun i ↦ mu.ofLp i / (-beta)
  refine ⟨lamStar, ?_, ?_⟩
  · -- Normalize by the positive scalar `-beta` to get an admissible multiplier.
    rw [problem.mem_admissibleMultiplierSet_iff]
    intro i
    exact div_nonneg (hmu_nonneg i) (le_of_lt (by linarith [hbeta_neg]))
  · intro x
    have hscalar :=
      problem.supporting_vector_ineq_of_perturbation_realizer
        (xStar := xStar) (x := x) (mu := mu) (beta := beta)
        (u := WithLp.toLp 2 (fun i ↦ problem.constraint i x))
        (r := problem.objective x) h_support
        (fun i ↦ by simp)
        le_rfl
    have hbound :
        ∑ i : Fin m, mu.ofLp i * problem.constraint i x ≤
          (-beta) * (problem.objective x - problem.objective xStar) := by
      -- Rewrite the scalarized support inequality into a bound on the weighted constraint sum.
      have hscalar' :
          ∑ i : Fin m, mu.ofLp i * problem.constraint i x +
              beta * (problem.objective x - problem.objective xStar) ≤ 0 := by
        simpa [PiLp.inner_apply, dotProduct, mul_comm] using hscalar
      nlinarith
    have hdiv :
        (∑ i : Fin m, mu.ofLp i * problem.constraint i x) / (-beta) ≤
          problem.objective x - problem.objective xStar := by
      have hpos : 0 < -beta := by linarith [hbeta_neg]
      exact (div_le_iff₀ hpos).2 (by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hbound)
    have hlam_sum :
        ∑ i : Fin m, lamStar i * problem.constraint i x =
          (∑ i : Fin m, mu.ofLp i * problem.constraint i x) / (-beta) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [lamStar, div_eq_mul_inv, mul_assoc, mul_comm]
    rw [ConstrainedOptimizationProblem.lagrangian]
    -- Substitute the normalized weighted sum into the Lagrangian formula and compare with `f(xStar)`.
    have hlam_bound :
        ∑ i : Fin m, lamStar i * problem.constraint i x ≤
          problem.objective x - problem.objective xStar := by
      simpa [hlam_sum] using hdiv
    linarith [hlam_bound]

/-- Helper for Chapter09 Exercise 9.5: the unresolved strong-duality step is to show that Slater's
condition supplies an admissible multiplier whose dual value matches the primal minimum. -/
theorem exists_admissibleMultiplier_dualObjective_eq_objective_of_convex_of_slater
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (h_min : problem.IsGlobalMinimizer xStar)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i))
    (h_slater : problem.SatisfiesSlaterCondition) :
    ∃ lamStar : Multiplier,
      lamStar ∈ problem.admissibleMultiplierSet ∧
        problem.dualObjective lamStar = ((problem.objective xStar : ℝ) : WithBot ℝ) := by
  have h_perturbation_convex :
      Convex ℝ problem.liftedPerturbationSet :=
    problem.lifted_perturbation_set_convex h_objective_convex h_constraint_concave
  have hxbar_frontier :
      problem.liftedPrimalValuePair xStar ∈ frontier problem.liftedPerturbationSet :=
    problem.lifted_primal_value_pair_mem_frontier_perturbation_set xStar h_min
  obtain ⟨p, hp_ne, hp_support⟩ :=
    existsNonzeroSupportingVectorOnClosure
      problem.liftedPerturbationSet h_perturbation_convex
      (problem.liftedPrimalValuePair xStar) hxbar_frontier
  let mu : EMultiplier := p.ofLp.1
  let beta : ℝ := p.ofLp.2
  have hp_ne' : ((mu, beta) : EMultiplier × ℝ) ≠ 0 := by
    intro hzero
    have hp_fst_zero : p.ofLp.1 = 0 := by
      simpa [mu, beta] using congrArg Prod.fst hzero
    have hp_snd_zero : p.ofLp.2 = 0 := by
      simpa [mu, beta] using congrArg Prod.snd hzero
    have hp_ofLp_zero : p.ofLp = (0 : EMultiplier × ℝ) := by
      exact Prod.ext hp_fst_zero hp_snd_zero
    have hp_zero : p = 0 := by
      simpa using congrArg (WithLp.toLp 2) hp_ofLp_zero
    exact hp_ne hp_zero
  have hp_support' :
      closure problem.liftedPerturbationSet ⊆
        closedLowerHalfSpace (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
          (inner ℝ (WithLp.toLp 2 ((mu, beta) : EMultiplier × ℝ))
            (problem.liftedPrimalValuePair xStar)) := by
    intro z hz
    have hz_halfspace := hp_support hz
    simpa [mu, beta, ConstrainedOptimizationProblem.liftedPrimalValuePair,
      WithLp.prod_inner_apply, add_comm, add_left_comm, add_assoc] using hz_halfspace
  obtain ⟨lamStar, hlamStar, h_lower⟩ :=
    problem.exists_multiplier_lagrangian_lower_bound_of_supporting_vector
      xStar h_min h_slater hp_ne' hp_support'
  refine ⟨lamStar, hlamStar, ?_⟩
  exact
    problem.dualObjective_eq_objective_of_lagrangian_global_lower_bound
      h_min.feasible hlamStar h_lower

/-- Chapter09 Exercise 9.5: if `problem.objective` is convex, each `problem.constraint i` is
concave, and `problem` satisfies Slater's condition, then `xStar` is a global minimizer of
`problem` exactly when it can be paired with an admissible multiplier vector forming a saddle
point of the Lagrangian `𝓛[problem]`. -/
theorem isGlobalMinimizer_iff_exists_isSaddlePair_of_convex_of_slaterCondition
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) (xStar : Point)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i))
    (h_slater : problem.SatisfiesSlaterCondition) :
    problem.IsGlobalMinimizer xStar ↔ ∃ lamStar : Multiplier, problem.IsSaddlePair xStar lamStar :=
  by
  constructor
  · intro h_min
    -- The forward implication reduces to the strong-duality value-attainment step under Slater.
    obtain ⟨lamStar, hlamStar, h_value⟩ :=
      problem.exists_admissibleMultiplier_dualObjective_eq_objective_of_convex_of_slater
        xStar h_min h_objective_convex h_constraint_concave h_slater
    refine ⟨lamStar, ?_⟩
    exact problem.isSaddlePair_of_dualObjective_eq_objective h_min.feasible hlamStar h_value
  · rintro ⟨lamStar, h_saddle⟩
    -- The reverse implication is immediate from the saddle inequalities.
    exact problem.isGlobalMinimizer_of_isSaddlePair h_saddle

end ConstrainedOptimizationProblem

end Chapter09Exercise95
