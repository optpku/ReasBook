/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.Extr
import Mathlib.Order.WithBot
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_9
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Assumption_8_2_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Lemma_8_2_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Notation_8_2_extra_2

noncomputable section

section Chapter08Theorem841

variable {n m : ℕ}

local notation "Point" => Fin n → ℝ
local notation "EPoint" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => Fin m → ℝ

-- Domain-style sampling:
-- * source-facing theorem: dual-maximizer existence for the inequality-only convex primal
--   problem
-- * reused Chapter 8 owners:
--   `problem.IsGlobalMinimizer`, `problem.regularityAssumptionAt`, and the notation
--   `𝓛[problem](x, lam)`
-- * local dual owners kept here:
--   the multiplier-level extended-real dual objective `problem.dualObjective`, the admissible
--   multiplier set
--   `problem.admissibleMultiplierSet`, the derived dual-solution owner `problem.IsDualSolution`,
--   and the attained bridge `problem.attainedDualFeasibleSet`
-- * layer triage:
--   source-facing: `problem.IsDualOptimalPair xStar lamStar`
--   core/canonical: `problem.dualObjective` and `problem.IsDualSolution lamStar`
--   bridge/view: `problem.attainedDualFeasibleSet`

namespace ConstrainedOptimizationProblem

/-- The admissible multiplier set for `(8.4.2)` consists of the componentwise nonnegative
multiplier vectors. -/
def admissibleMultiplierSet
    (_ : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) :
    Set Multiplier :=
  {lam | ∀ i : Fin m, 0 ≤ lam i}

/-- Membership in `problem.admissibleMultiplierSet` means componentwise nonnegativity. -/
theorem mem_admissibleMultiplierSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lam : Multiplier) :
    lam ∈ problem.admissibleMultiplierSet ↔ ∀ i : Fin m, 0 ≤ lam i :=
  Iff.rfl

/-- The dual objective of `(8.4.2)` is the extended-real infimum over `x : Point` of
`𝓛[problem](x, λ)`, so the value `⊥ = -∞` is available when the Lagrangian is unbounded below.
-/
def dualObjective
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lam : Multiplier) : WithBot ℝ :=
  sInf (Set.range fun y : Point ↦ ((𝓛[problem](y, lam) : ℝ) : WithBot ℝ))

/-- Unfolding formula for `problem.dualObjective lam`. -/
theorem dualObjective_eq
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lam : Multiplier) :
    problem.dualObjective lam =
      sInf (Set.range fun y : Point ↦ ((𝓛[problem](y, lam) : ℝ) : WithBot ℝ)) :=
  rfl

/-- A multiplier vector is dual-feasible for `(8.4.2)` exactly when it is admissible. -/
abbrev IsDualFeasible
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lam : Multiplier) : Prop :=
  lam ∈ problem.admissibleMultiplierSet

/-- A dual solution of `(8.4.2)` is an admissible multiplier maximizing the dual objective over
the admissible multiplier set. -/
def IsDualSolution
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lamStar : Multiplier) : Prop :=
  problem.IsDualFeasible lamStar ∧
    IsMaxOn problem.dualObjective problem.admissibleMultiplierSet lamStar

/-- `problem.IsDualSolution lamStar` unfolds to admissibility together with maximality of the
dual objective on `problem.admissibleMultiplierSet`. -/
theorem isDualSolution_iff
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (lamStar : Multiplier) :
    problem.IsDualSolution lamStar ↔
      problem.IsDualFeasible lamStar ∧
        ∀ lam : Multiplier,
          problem.IsDualFeasible lam →
            problem.dualObjective lam ≤ problem.dualObjective lamStar := by
  rw [IsDualSolution]
  constructor
  · rintro ⟨hfeasible, hmax⟩
    exact ⟨hfeasible, isMaxOn_iff.mp hmax⟩
  · rintro ⟨hfeasible, hmax⟩
    exact ⟨hfeasible, isMaxOn_iff.mpr hmax⟩

/-- The attained bridge for `(8.4.2)` consists of the pairs `(x, λ)` such that `x` minimizes
`𝓛[problem](·, λ)` on `Set.univ` and `λ` is admissible. -/
def attainedDualFeasibleSet
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) :
    Set (Point × Multiplier) :=
  {p |
    IsMinOn (fun y : Point ↦ 𝓛[problem](y, p.2)) Set.univ p.1 ∧
      p.2 ∈ problem.admissibleMultiplierSet}

/-- Membership in `problem.attainedDualFeasibleSet` means that `x` realizes the dual infimum for
`λ` and that `λ` is admissible. -/
theorem mem_attainedDualFeasibleSet_iff
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (x : Point) (lam : Multiplier) :
    (x, lam) ∈ problem.attainedDualFeasibleSet ↔
      IsMinOn (fun y : Point ↦ 𝓛[problem](y, lam)) Set.univ x ∧
        lam ∈ problem.admissibleMultiplierSet :=
  Iff.rfl

/-- A pair `(xStar, lamStar)` is dual-optimal when `lamStar` solves the dual problem `(8.4.2)`,
`xStar` realizes the infimum defining `problem.dualObjective lamStar`, and the primal and dual
values coincide after coercing the primal value into `WithBot ℝ`. -/
@[mk_iff]
class IsDualOptimalPair
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (lamStar : Multiplier) : Prop where
  isDualSolution : problem.IsDualSolution lamStar
  attainsDualObjective : IsMinOn (fun y : Point ↦ 𝓛[problem](y, lamStar)) Set.univ xStar
  primal_eq_dual : ((problem.objective xStar : ℝ) : WithBot ℝ) = problem.dualObjective lamStar

/-- `problem.IsDualOptimalPair xStar lamStar` is a proposition. -/
instance instSubsingletonIsDualOptimalPair
    (problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ)
    (xStar : Point) (lamStar : Multiplier) :
    Subsingleton (problem.IsDualOptimalPair xStar lamStar) :=
  inferInstance

/-- An attained dual-feasible pair realizes the infimum of `𝓛[problem](·, λ)` for its multiplier
component. -/
theorem lagrangian_le_of_mem_attainedDualFeasibleSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {x y : Point} {lam : Multiplier} (h : (x, lam) ∈ problem.attainedDualFeasibleSet) :
    𝓛[problem](x, lam) ≤ 𝓛[problem](y, lam) :=
  (isMinOn_iff.mp h.1) y (by simp)

/-- An attained dual-feasible pair computes `problem.dualObjective` at its multiplier component. -/
theorem dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {x : Point} {lam : Multiplier} (h : (x, lam) ∈ problem.attainedDualFeasibleSet) :
    problem.dualObjective lam = ((𝓛[problem](x, lam) : ℝ) : WithBot ℝ) := by
  refine le_antisymm ?_ ?_
  · have hx :
        ((𝓛[problem](x, lam) : ℝ) : WithBot ℝ) ∈
          Set.range (fun y : Point ↦ ((𝓛[problem](y, lam) : ℝ) : WithBot ℝ)) :=
      ⟨x, rfl⟩
    simpa [dualObjective] using csInf_le' hx
  · rw [dualObjective]
    refine (le_csInf_iff'' ?_).2 ?_
    · exact ⟨_, ⟨x, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨y, rfl⟩
      simpa using
        (show ((𝓛[problem](x, lam) : ℝ) : WithBot ℝ) ≤
            ((𝓛[problem](y, lam) : ℝ) : WithBot ℝ) from
          by
            exact_mod_cast
              (lagrangian_le_of_mem_attainedDualFeasibleSet h :
                𝓛[problem](x, lam) ≤ 𝓛[problem](y, lam)))

/-- Helper for Chapter08 Theorem 8.4.1: the dual objective is bounded above by every realized
Lagrangian value in its defining infimum family. -/
theorem dualObjective_le_lagrangian
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    (x : Point) (lam : Multiplier) :
    problem.dualObjective lam ≤ ((𝓛[problem](x, lam) : ℝ) : WithBot ℝ) := by
  -- The dual objective is the infimum over all Lagrangian evaluations at this multiplier.
  rw [problem.dualObjective_eq]
  exact csInf_le' ⟨x, rfl⟩

/-- Helper for Chapter08 Theorem 8.4.1: at a primal-feasible point, every admissible multiplier
can only decrease the objective when forming the Lagrangian. -/
theorem lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {x : Point} {lam : Multiplier}
    (hx : x ∈ problem.feasibleSet) (hlam : lam ∈ problem.admissibleMultiplierSet) :
    𝓛[problem](x, lam) ≤ problem.objective x := by
  rcases (problem.mem_feasibleSet_iff x).mp hx with ⟨_, hxineq⟩
  have hlam_nonneg : ∀ i : Fin m, 0 ≤ lam i :=
    (problem.mem_admissibleMultiplierSet_iff lam).mp hlam
  have hsum_nonneg : 0 ≤ ∑ i : Fin m, lam i * problem.constraint i x := by
    -- Each multiplier term is nonnegative because both the multiplier and the feasible
    -- inequality value are nonnegative.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg
      (hlam_nonneg i)
      (hxineq i (by simp [ConstrainedOptimizationProblem.ineqIndices]))
  simpa [ConstrainedOptimizationProblem.lagrangian] using
    sub_le_self (problem.objective x) hsum_nonneg

/-- Helper for Chapter08 Theorem 8.4.1: fixing an admissible multiplier keeps the Chapter 8
Lagrangian convex in `x` because it is a convex objective minus a nonnegative combination of
concave constraints. -/
theorem concaveOn_weightedConstraintSum_of_mem_admissibleMultiplierSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {lam : Multiplier} (hlam : lam ∈ problem.admissibleMultiplierSet)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    ConcaveOn ℝ Set.univ (∑ i : Fin m, fun x : Point ↦ lam i • problem.constraint i x) := by
  have hlam_nonneg : ∀ i : Fin m, 0 ≤ lam i :=
    (problem.mem_admissibleMultiplierSet_iff lam).mp hlam
  -- Sum the concave weighted constraints one multiplier component at a time.
  refine Finset.induction ?_ ?_ (s := Finset.univ)
  · change ConcaveOn ℝ Set.univ (fun _ : Point ↦ (0 : ℝ))
    exact concaveOn_const (𝕜 := ℝ) (s := Set.univ) (c := (0 : ℝ)) convex_univ
  · intro i s hi hs
    have h_term : ConcaveOn ℝ Set.univ (fun x : Point ↦ lam i • problem.constraint i x) := by
      -- Each admissible multiplier preserves concavity of its corresponding constraint.
      exact (h_constraint_concave i).smul (hlam_nonneg i)
    -- Concavity is stable under finite sums, so insert the next weighted constraint.
    simpa [Finset.sum_insert hi, Pi.add_apply] using h_term.add hs

/-- Helper for Chapter08 Theorem 8.4.1: fixing an admissible multiplier keeps the Chapter 8
Lagrangian convex in `x` because it is a convex objective minus a nonnegative combination of
concave constraints. -/
theorem convexOn_lagrangian_of_mem_admissibleMultiplierSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {lam : Multiplier} (hlam : lam ∈ problem.admissibleMultiplierSet)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i)) :
    ConvexOn ℝ Set.univ (fun x : Point ↦ 𝓛[problem](x, lam)) := by
  have h_weighted_sum_concave :
      ConcaveOn ℝ Set.univ
        (∑ i : Fin m, fun x : Point ↦ lam i • problem.constraint i x) :=
    problem.concaveOn_weightedConstraintSum_of_mem_admissibleMultiplierSet
      hlam h_constraint_concave
  -- Route correction: isolate the weighted constraint sum first, then apply `ConvexOn.sub`.
  rw [show (fun x : Point ↦ 𝓛[problem](x, lam)) =
      problem.objective - ∑ i : Fin m, fun x : Point ↦ lam i • problem.constraint i x by
      ext x
      simp [ConstrainedOptimizationProblem.lagrangian, smul_eq_mul]]
  exact h_objective_convex.sub h_weighted_sum_concave

/-- Helper for Chapter08 Theorem 8.4.1: transporting the objective derivative through
`WithLp.toLp 2` preserves the directional derivative at the corresponding Chapter 8 point. -/
theorem euclideanObjective_fderiv_eq
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    (xStar d : Point) :
    fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) =
      fderiv ℝ problem.objective xStar d := by
  have hcoordPoint (x : Point) : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 x) = x := by
    change (WithLp.toLp 2 x).ofLp = x
    exact WithLp.ofLp_toLp 2 x
  have hcomp :
      fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) =
        (fderiv ℝ problem.objective xStar).comp
          ((EuclideanSpace.equiv (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] Point) := by
    have hcompEq :
        fderiv ℝ (problem.objective ∘ EuclideanSpace.equiv (Fin n) ℝ)
            (WithLp.toLp 2 xStar) =
          (fderiv ℝ problem.objective xStar).comp
            ((EuclideanSpace.equiv (Fin n) ℝ) : EuclideanSpace ℝ (Fin n) →L[ℝ] Point) :=
      (EuclideanSpace.equiv (Fin n) ℝ).comp_right_fderiv
    simpa [problem.euclideanObjective_eq] using hcompEq
  simpa [ContinuousLinearMap.comp_apply, hcoordPoint d] using
    congrArg
      (fun g : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ ↦ g (WithLp.toLp 2 d))
      hcomp

/-- Helper for Chapter08 Theorem 8.4.1: the Chapter 8 linearized pairing equals the Euclidean
gradient pairing of the transported constraint. -/
theorem linearizedConstraintPairing_eq_inner_euclideanConstraintGradient
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    (xStar d : Point) (i : Fin m) :
    problem.linearizedConstraintPairing xStar d i =
      inner ℝ (WithLp.toLp 2 d)
        (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) := by
  calc
    problem.linearizedConstraintPairing xStar d i
        = fderiv ℝ (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) := by
            exact problem.linearizedConstraintPairing_eq_euclideanConstraint xStar d i
    _ = inner ℝ (WithLp.toLp 2 d)
          (gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar)) := by
            exact
              (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanConstraint i)
                (x := WithLp.toLp 2 d) (y := WithLp.toLp 2 xStar)).symm

/-- Helper for Chapter08 Theorem 8.4.1: differentiability of the objective and constraints makes
the Euclidean transport of the Lagrangian differentiable at the base point. -/
theorem differentiableAt_transportedLagrangian_of_differentiableAt_of_hasConstraintGradientsAt
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {xStar : Point} {lam : Multiplier}
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    DifferentiableAt ℝ
      (problem.euclideanObjective -
        ∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
      (WithLp.toLp 2 xStar) := by
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) := by
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective
  have hsum :
      DifferentiableAt ℝ
        (∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
        (WithLp.toLp 2 xStar) := by
    exact DifferentiableAt.sum fun i _ ↦
      ((problem.differentiableAt_euclideanConstraint_iff i xStar).2 (h_constraints i)).const_mul
        (lam i)
  exact hobjectiveE.sub hsum

/-- Helper for Chapter08 Theorem 8.4.1: the Euclidean transport of the Lagrangian has gradient
equal to the objective gradient minus the multiplier-weighted constraint-gradient sum. -/
theorem gradient_transportedLagrangian_eq_objective_sub_sum
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    (xStar : Point) (lam : Multiplier)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar) :
    gradient
        (problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
        (WithLp.toLp 2 xStar) =
      gradient problem.euclideanObjective (WithLp.toLp 2 xStar) -
        ∑ i : Fin m, lam i • gradient (problem.euclideanConstraint i) (WithLp.toLp 2 xStar) := by
  let xStarE : EPoint := WithLp.toLp 2 xStar
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective xStarE := by
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective
  have hconstraintE :
      ∀ i : Fin m, DifferentiableAt ℝ (problem.euclideanConstraint i) xStarE := by
    intro i
    exact (problem.differentiableAt_euclideanConstraint_iff i xStar).2 (h_constraints i)
  have hsum :
      fderiv ℝ
          (∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
          xStarE =
        ∑ i : Fin m,
          fderiv ℝ (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) xStarE := by
    exact
      (fderiv_sum
        (u := Finset.univ)
        (A := fun i : Fin m ↦ fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
        (x := xStarE)
        (fun i _ ↦ (hconstraintE i).const_mul (lam i)))
  apply ext_inner_left ℝ
  intro y
  calc
    inner ℝ y
        (gradient
          (problem.euclideanObjective -
            ∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
          xStarE)
        = fderiv ℝ
            (problem.euclideanObjective -
              ∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
            xStarE y := by
              exact
                (inner_gradient_right (𝕜 := ℝ)
                  (f := problem.euclideanObjective -
                    ∑ i : Fin m, fun x : EPoint ↦ lam i * problem.euclideanConstraint i x)
                  (x := y) (y := xStarE))
    _ = (fderiv ℝ problem.euclideanObjective xStarE -
          ∑ i : Fin m,
            fderiv ℝ (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) xStarE) y := by
            rw [fderiv_sub hobjectiveE]
            · rw [hsum]
            · exact DifferentiableAt.sum fun i _ ↦ (hconstraintE i).const_mul (lam i)
    _ = inner ℝ y (gradient problem.euclideanObjective xStarE) -
          ∑ i : Fin m,
            inner ℝ y (lam i • gradient (problem.euclideanConstraint i) xStarE) := by
            rw [sub_apply]
            rw [show
              (∑ i : Fin m,
                  fderiv ℝ (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) xStarE) y =
                ∑ i : Fin m,
                  (fderiv ℝ (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) xStarE) y by
                simp]
            congr 1
            · exact
                (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanObjective)
                  (x := y) (y := xStarE)).symm
            · apply Finset.sum_congr rfl
              intro i hi
              have hfun :
                  (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) =
                    lam i • problem.euclideanConstraint i := by
                ext x
                simp [smul_eq_mul]
              have hterm :
                  fderiv ℝ (fun x : EPoint ↦ lam i * problem.euclideanConstraint i x) xStarE =
                    lam i • fderiv ℝ (problem.euclideanConstraint i) xStarE := by
                rw [hfun]
                simpa using
                  congrFun
                    (fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ) (c := lam i)
                      (f := problem.euclideanConstraint i))
                    xStarE
              rw [hterm, smul_apply, inner_smul_right]
              exact
                congrArg
                  (fun r : ℝ => lam i * r)
                  ((inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanConstraint i)
                    (x := y) (y := xStarE)).symm)
    _ = inner ℝ y
          (gradient problem.euclideanObjective xStarE -
            ∑ i : Fin m, lam i • gradient (problem.euclideanConstraint i) xStarE) := by
            rw [inner_sub_right, inner_sum]

/-- A dual-optimal pair is, in particular, an attained dual-feasible pair. -/
theorem IsDualOptimalPair.mem_attainedDualFeasibleSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsDualOptimalPair xStar lamStar) :
    (xStar, lamStar) ∈ problem.attainedDualFeasibleSet :=
  ⟨h.attainsDualObjective, h.isDualSolution.1⟩

/-- For a dual-optimal pair, the primal value agrees with the attained Lagrangian value. -/
theorem IsDualOptimalPair.primal_eq_lagrangian
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsDualOptimalPair xStar lamStar) :
    ((problem.objective xStar : ℝ) : WithBot ℝ) = 𝓛[problem](xStar, lamStar) := by
  rw [h.primal_eq_dual,
    dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet h.mem_attainedDualFeasibleSet]

/-- A dual-optimal pair maximizes the attained dual value on the attained bridge
`problem.attainedDualFeasibleSet`. -/
theorem IsDualOptimalPair.isMaxOn_attainedDualFeasibleSet
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsDualOptimalPair xStar lamStar) :
    IsMaxOn (fun p : Point × Multiplier ↦ 𝓛[problem](p.1, p.2))
      problem.attainedDualFeasibleSet (xStar, lamStar) := by
  rw [isMaxOn_iff]
  intro p hp
  have hp_eq :
      problem.dualObjective p.2 = ((𝓛[problem](p.1, p.2) : ℝ) : WithBot ℝ) :=
    dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet hp
  have hstar_eq :
      problem.dualObjective lamStar = ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) :=
    dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet h.mem_attainedDualFeasibleSet
  have hdual :
      ((𝓛[problem](p.1, p.2) : ℝ) : WithBot ℝ) ≤
        ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := by
    calc
      ((𝓛[problem](p.1, p.2) : ℝ) : WithBot ℝ) = problem.dualObjective p.2 := hp_eq.symm
      _ ≤ problem.dualObjective lamStar := (isMaxOn_iff.mp h.isDualSolution.2) _ hp.2
      _ = ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := hstar_eq
  exact_mod_cast hdual

/-- A dual-optimal pair dominates every attained dual-feasible pair in the attained dual
objective. -/
theorem IsDualOptimalPair.dualObjective_le
    {problem : _root_.ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ}
    {xStar : Point} {lamStar : Multiplier}
    (h : problem.IsDualOptimalPair xStar lamStar) :
    ∀ p ∈ problem.attainedDualFeasibleSet,
      𝓛[problem](p.1, p.2) ≤ 𝓛[problem](xStar, lamStar) :=
  isMaxOn_iff.mp h.isMaxOn_attainedDualFeasibleSet

end ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.4.1: let `xStar` be a global minimizer of the convex primal problem
`min problem.objective x` subject to `0 ≤ problem.constraint i x` for `i : Fin m`. If
`problem.objective` and every `problem.constraint i` are `C¹` and the regularity condition
`problem.regularityAssumptionAt xStar` holds, then there exists a multiplier vector `lamStar`
such that `lamStar` maximizes the dual objective `problem.dualObjective` on the admissible
multiplier set `problem.admissibleMultiplierSet`, `xStar` minimizes `𝓛[problem](·, lamStar)` on
`Set.univ`, and the primal value agrees with `problem.dualObjective lamStar` in `WithBot ℝ`. -/
theorem exists_dualMaximizer_of_isGlobalMinimizer_of_convexProblem
    (problem : ConstrainedOptimizationProblem n m (∅ : Set (Fin m)) Set.univ) (xStar : Point)
    (h_min : problem.IsGlobalMinimizer xStar)
    (h_objective_convex : ConvexOn ℝ Set.univ problem.objective)
    (h_constraint_concave : ∀ i, ConcaveOn ℝ Set.univ (problem.constraint i))
    (h_objective_contDiff : ContDiff ℝ 1 problem.objective)
    (h_constraint_contDiff : ∀ i, ContDiff ℝ 1 (problem.constraint i))
    (h_regularity : problem.regularityAssumptionAt xStar) :
    ∃ lamStar : Multiplier,
      problem.IsDualOptimalPair xStar lamStar := by
  classical
  have hxStar : xStar ∈ problem := h_min.feasible
  have h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar := by
    -- A global minimizer is automatically a local minimizer on the feasible set.
    exact h_min.isMinOn.localize
  have h_objective_diff : DifferentiableAt ℝ problem.objective xStar := by
    -- The `C¹` objective is differentiable at the candidate minimizer.
    exact h_objective_contDiff.contDiffAt.differentiableAt one_ne_zero
  have h_constraints_diff : problem.HasConstraintGradientsAt xStar := by
    -- The `C¹` constraint family gives the KKT differentiability hypothesis pointwise.
    intro i
    exact (h_constraint_contDiff i).contDiffAt.differentiableAt one_ne_zero
  let xStarE : EPoint := WithLp.toLp 2 xStar
  have h_no_tangent_euclidean :
      posTangentConeAt problem.feasibleSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        (∅ : Set Point) := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro d hd
    have hnonneg_within :
        0 ≤ fderivWithin ℝ problem.objective problem.feasibleSet xStar d :=
      h_localMin.fderivWithin_nonneg hd.1
    have hd_real : d ∈ tangentConeAt ℝ problem.feasibleSet xStar :=
      tangentConeAt_mono_field hd.1
    have hderiv_eq :
        fderiv ℝ problem.objective xStar d =
          fderivWithin ℝ problem.objective problem.feasibleSet xStar d := by
      simpa using
        (h_objective_diff.hasFDerivAt.hasFDerivWithinAt).unique_on
          (h_objective_diff.differentiableWithinAt.hasFDerivWithinAt) hd_real
    have hnonneg :
        0 ≤ fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) := by
      have hnonnegObj : 0 ≤ fderiv ℝ problem.objective xStar d := by
        rw [hderiv_eq]
        exact hnonneg_within
      simpa [problem.euclideanObjective_fderiv_eq xStar d] using hnonnegObj
    have hdesc :
        fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d) < 0 := by
      calc
        fderiv ℝ problem.euclideanObjective (WithLp.toLp 2 xStar) (WithLp.toLp 2 d)
            = inner ℝ (WithLp.toLp 2 d)
                (gradient problem.euclideanObjective (WithLp.toLp 2 xStar)) := by
                  exact
                    (inner_gradient_right (𝕜 := ℝ) (f := problem.euclideanObjective)
                      (x := WithLp.toLp 2 d) (y := WithLp.toLp 2 xStar)).symm
        _ < 0 := (mem_descentDirections_iff problem.euclideanObjective (WithLp.toLp 2 xStar)
          (WithLp.toLp 2 d)).1 hd.2
    exact not_lt_of_ge hnonneg hdesc
  have h_no_linearized_euclidean :
      problem.linearizedFeasibleDirectionSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        (∅ : Set Point) := by
    rw [← h_regularity]
    exact h_no_tangent_euclidean
  let gradC : Fin m → EPoint := fun i ↦ gradient (problem.euclideanConstraint i) xStarE
  have hobjectiveE : DifferentiableAt ℝ problem.euclideanObjective xStarE := by
    exact (problem.differentiableAt_euclideanObjective_iff xStar).2 h_objective_diff
  letI : Fintype (problem.activeIneqIndexSet xStar) := Fintype.ofFinite
    (problem.activeIneqIndexSet xStar)
  have hdisj :
      Disjoint problem.eqIndices (problem.activeIneqIndexSet xStar) := by
    simp [ConstrainedOptimizationProblem.eqIndices]
  have hEmpty :
      descentDirections problem.euclideanObjective xStarE ∩
          {u |
            (∀ i ∈ problem.eqIndices, inner ℝ u (gradC i) = 0) ∧
              ∀ i ∈ problem.activeIneqIndexSet xStar, 0 ≤ inner ℝ u (gradC i)} =
        (∅ : Set EPoint) := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro u hu
    let d : Point := u.ofLp
    have hd_linearized : d ∈ problem.linearizedFeasibleDirectionSet xStar := by
      rw [problem.mem_linearizedFeasibleDirectionSet_iff_explicit]
      refine ⟨hxStar, h_constraints_diff.hasActiveConstraintGradientsAt, ?_, ?_⟩
      · intro i hi
        simp [ConstrainedOptimizationProblem.eqIndices] at hi
      · intro i hi
        rw [problem.linearizedConstraintPairing_eq_inner_euclideanConstraintGradient xStar d i]
        simpa [d, xStarE, gradC] using hu.2.2 i hi
    have hd_preimage :
        d ∈ ((WithLp.toLp 2) ⁻¹'
          descentDirections problem.euclideanObjective xStarE) := by
      change WithLp.toLp 2 d ∈ descentDirections problem.euclideanObjective xStarE
      simpa [d, xStarE] using hu.1
    have : d ∈ (∅ : Set Point) := by
      rw [← h_no_linearized_euclidean]
      exact ⟨hd_linearized, hd_preimage⟩
    simp at this
  obtain ⟨lam, hlam_nonneg, hgrad_repr⟩ :=
    (descentDirections_inter_constraintGradientSystem_eq_empty_iff_exists_multiplier
      (X := EPoint) (ι := Fin m)
      problem.eqIndices (problem.activeIneqIndexSet xStar) hdisj
      problem.euclideanObjective xStarE (gradient problem.euclideanObjective xStarE) gradC
      hobjectiveE.hasGradientAt).1 hEmpty
  let lamStar : Multiplier :=
    fun i ↦ if i ∈ problem.activeIneqIndexSet xStar then lam i else 0
  have hlamStar : lamStar ∈ problem.admissibleMultiplierSet := by
    -- The multiplier vanishes off the active set and inherits nonnegativity on active indices.
    intro i
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · simpa [lamStar, hi_active] using hlam_nonneg i hi_active
    · simp [lamStar, hi_active]
  have hgrad_repr_full :
      gradient problem.euclideanObjective xStarE = ∑ i : Fin m, lamStar i • gradC i := by
    -- Rewrite the subtype-indexed multiplier representation as a full `Fin m` sum.
    calc
      gradient problem.euclideanObjective xStarE
          = ∑ c : problem.activeIneqIndexSet xStar, lam c • gradC c := by
              simpa [ConstrainedOptimizationProblem.eqIndices] using hgrad_repr
      _ = Finset.sum
            ((Finset.univ : Finset (problem.activeIneqIndexSet xStar)).map
              (Function.Embedding.subtype
                (fun c : Fin m => c ∈ problem.activeIneqIndexSet xStar)))
            (fun c ↦ lam c • gradC c) := by
            simp [Finset.sum_map]
      _ = Finset.sum
            (Finset.univ.filter (fun c : Fin m => c ∈ problem.activeIneqIndexSet xStar))
            (fun c ↦ lam c • gradC c) := by
            rw [Finset.univ_map_subtype]
      _ = ∑ c : Fin m, if c ∈ problem.activeIneqIndexSet xStar then lam c • gradC c else 0 := by
            simp [Finset.sum_filter]
      _ = ∑ i : Fin m, lamStar i • gradC i := by
            simp [lamStar]
  have h_lagrangian_convex :
      ConvexOn ℝ Set.univ (fun x : Point ↦ 𝓛[problem](x, lamStar)) := by
    -- Reuse the point-space convexity helper for the candidate multiplier.
    exact
      problem.convexOn_lagrangian_of_mem_admissibleMultiplierSet
        hlamStar h_objective_convex h_constraint_concave
  have hlagE_eq :
      (problem.euclideanObjective -
        ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x) =
        fun x : EPoint ↦ 𝓛[problem]((EuclideanSpace.equiv (Fin n) ℝ) x, lamStar) := by
    ext x
    simp [ConstrainedOptimizationProblem.lagrangian]
  have h_lagrangian_convex_euclidean :
      ConvexOn ℝ Set.univ
        (problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x) := by
    rw [hlagE_eq]
    simpa [Function.comp_def] using
      h_lagrangian_convex.comp_affineMap ((EuclideanSpace.equiv (Fin n) ℝ).toAffineMap)
  have h_lagrangian_diff_euclidean :
      DifferentiableAt ℝ
        (problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x)
        xStarE := by
    -- The `C¹` hypotheses make the Euclidean transport of the Lagrangian differentiable at `xStar`.
    exact
      problem.differentiableAt_transportedLagrangian_of_differentiableAt_of_hasConstraintGradientsAt
        h_objective_diff h_constraints_diff
  have h_lagrangian_stationary_euclidean :
      gradient
          (problem.euclideanObjective -
            ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x)
          xStarE = 0 := by
    -- The multiplier representation annihilates the transported Lagrangian gradient at `xStar`.
    rw [problem.gradient_transportedLagrangian_eq_objective_sub_sum xStar lamStar
      h_objective_diff h_constraints_diff, hgrad_repr_full, sub_self]
  have h_attain_euclidean :
      IsMinOn
        (problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x)
        Set.univ xStarE := by
    -- A convex differentiable Euclidean Lagrangian with zero gradient at `xStarE` is globally
    -- minimized there.
    exact
      (isMinOn_univ_iff_gradient_eq_zero_of_convex
        (problem.euclideanObjective -
          ∑ i : Fin m, fun x : EPoint ↦ lamStar i * problem.euclideanConstraint i x)
        xStarE h_lagrangian_convex_euclidean h_lagrangian_diff_euclidean).2
        h_lagrangian_stationary_euclidean
  have h_attain :
      IsMinOn (fun y : Point ↦ 𝓛[problem](y, lamStar)) Set.univ xStar := by
    rw [isMinOn_iff]
    intro y hy
    -- Pull the Euclidean minimizing property back to the original point model.
    have h_euclidean := (isMinOn_iff.mp h_attain_euclidean) (WithLp.toLp 2 y) (by simp)
    have hxcoord : (EuclideanSpace.equiv (Fin n) ℝ) xStarE = xStar := by
      change xStarE.ofLp = xStar
      exact WithLp.ofLp_toLp 2 xStar
    have hycoord : (EuclideanSpace.equiv (Fin n) ℝ) (WithLp.toLp 2 y) = y := by
      change (WithLp.toLp 2 y).ofLp = y
      exact WithLp.ofLp_toLp 2 y
    simpa [ConstrainedOptimizationProblem.lagrangian, xStarE, hxcoord, hycoord] using h_euclidean
  have h_attained : (xStar, lamStar) ∈ problem.attainedDualFeasibleSet := by
    exact ⟨h_attain, hlamStar⟩
  have h_dual_eq_lagrangian :
      problem.dualObjective lamStar = ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := by
    exact problem.dualObjective_eq_lagrangian_of_mem_attainedDualFeasibleSet h_attained
  have hsum_zero : ∑ i : Fin m, lamStar i * problem.constraint i xStar = 0 := by
    -- Active constraints vanish and inactive multipliers were defined to be `0`.
    refine Finset.sum_eq_zero ?_
    intro i hi
    by_cases hi_active : i ∈ problem.activeIneqIndexSet xStar
    · have hi_zero : problem.constraint i xStar = 0 :=
        (problem.mem_activeIneqIndexSet_iff xStar i).1 hi_active |>.2
      simp [lamStar, hi_active, hi_zero]
    · simp [lamStar, hi_active]
  have h_objective_eq_lagrangian :
      problem.objective xStar = 𝓛[problem](xStar, lamStar) := by
    calc
      problem.objective xStar = problem.objective xStar - 0 := by ring
      _ = problem.objective xStar -
          ∑ i : Fin m, lamStar i * problem.constraint i xStar := by rw [hsum_zero]
      _ = 𝓛[problem](xStar, lamStar) := by rw [ConstrainedOptimizationProblem.lagrangian]
  have h_primal_eq_dual :
      ((problem.objective xStar : ℝ) : WithBot ℝ) = problem.dualObjective lamStar := by
    -- The active-set construction identifies the primal value with the attained dual value.
    calc
      ((problem.objective xStar : ℝ) : WithBot ℝ) =
          ((𝓛[problem](xStar, lamStar) : ℝ) : WithBot ℝ) := by
            exact_mod_cast h_objective_eq_lagrangian
      _ = problem.dualObjective lamStar := h_dual_eq_lagrangian.symm
  have h_dualSolution : problem.IsDualSolution lamStar := by
    rw [problem.isDualSolution_iff]
    refine ⟨hlamStar, ?_⟩
    intro lam hlam
    -- The source proof chain is `dualObjective ≤ L(xStar, lam) ≤ f(xStar) = dualObjective lamStar`.
    calc
      problem.dualObjective lam ≤ ((𝓛[problem](xStar, lam) : ℝ) : WithBot ℝ) := by
        exact problem.dualObjective_le_lagrangian xStar lam
      _ ≤ ((problem.objective xStar : ℝ) : WithBot ℝ) := by
        exact_mod_cast
          (problem.lagrangian_le_objective_of_feasible_of_mem_admissibleMultiplierSet
            h_min.feasible hlam)
      _ = problem.dualObjective lamStar := h_primal_eq_dual
  refine ⟨lamStar, ?_⟩
  exact
    { isDualSolution := h_dualSolution
      attainsDualObjective := h_attain
      primal_eq_dual := h_primal_eq_dual }

end Chapter08Theorem841
