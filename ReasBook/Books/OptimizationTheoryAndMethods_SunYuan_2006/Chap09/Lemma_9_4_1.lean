/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_1
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian

noncomputable section

section Chapter09Lemma941

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "EqMultiplier" => EuclideanSpace ℝ (Fin me)
local notation "IneqMultiplier" => EuclideanSpace ℝ (Fin mi)
local notation "Multiplier" => EqMultiplier × IneqMultiplier
local notation "pointEquiv" => EuclideanSpace.equiv (Fin n) ℝ

open scoped BigOperators Gradient

-- Domain sampling:
-- * primary domain: quadratic-program active-set reduction and KKT transfer;
-- * inspected owner declarations:
--   `QuadraticProgram` from `Definition_9_1_extra_1`,
--   `QuadraticProgram.activeSet` from `Algorithm_9_4_2`,
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Chapter08.Theorem_8_2_7`,
--   and `IsLocalMinOn.on_subset` from mathlib;
-- * best owner abstraction: the Chapter 9 quadratic-program owner together with the canonical
--   Chapter 8 KKT owner on `P.toConstrainedOptimizationProblem`;
-- * source/core/bridge triage:
--   - source-facing layer here: the active-set feasible system and Lemma 9.4.1 itself;
--   - core/canonical layer: `P.toConstrainedOptimizationProblem.IsKKTPoint`;
--   - bridge/view: `P.activeSet xStar` and `pointEquiv`;
-- * primitive data vs derived API:
--   - primitive data already live in `QuadraticProgram`;
--   - the active-set equality system and its KKT transfer are derived API over that owner.

namespace QuadraticProgram

/-- The active-set equality system at `xStar` keeps the original equalities together with the
inequalities active at `xStar`, viewed as equalities. -/
def activeSetFeasibleSet
    (P : QuadraticProgram n me mi) (xStar : Point) : Set Point :=
  {x | P.Aeq.mulVec x = P.beq ∧ ∀ i ∈ P.activeSet xStar, (P.Aineq.mulVec x) i = P.bineq i}

/-- Membership in `P.activeSetFeasibleSet xStar` is exactly the equality system consisting of the
original equality constraints and the inequalities active at `xStar`. -/
theorem mem_activeSetFeasibleSet_iff
    (P : QuadraticProgram n me mi) (xStar x : Point) :
    x ∈ P.activeSetFeasibleSet xStar ↔
      P.Aeq.mulVec x = P.beq ∧
        ∀ i, i ∈ P.activeSet xStar → (P.Aineq.mulVec x) i = P.bineq i :=
  Iff.rfl

/-- An ambient multiplier pair satisfies the active-set equality-constrained KKT system at
`xStar` when the stationarity equation holds, `xStar` satisfies the active-set equality system,
and the inactive inequality multipliers vanish. -/
def SatisfiesActiveSetKKT
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier) : Prop :=
  P.g + Matrix.toEuclideanLin P.G xStar =
      P.Aeq.transpose.mulVec mult.1 + P.Aineq.transpose.mulVec mult.2 ∧
    xStar ∈ P.activeSetFeasibleSet xStar ∧
    ∀ i, i ∉ P.activeSet xStar → mult.2 i = 0

/-- Unfolding `P.SatisfiesActiveSetKKT xStar mult` gives the stationarity equation, the active-set
equality feasibility conditions, and the vanishing of inactive inequality multipliers. -/
theorem satisfiesActiveSetKKT_iff
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier) :
    P.SatisfiesActiveSetKKT xStar mult ↔
      P.g + Matrix.toEuclideanLin P.G xStar =
          P.Aeq.transpose.mulVec mult.1 + P.Aineq.transpose.mulVec mult.2 ∧
        xStar ∈ P.activeSetFeasibleSet xStar ∧
        ∀ i, i ∉ P.activeSet xStar → mult.2 i = 0 :=
  Iff.rfl

/-- Helper for Chapter09 Lemma 9.4.1: transporting `pointEquiv x` back to the Euclidean-space
model gives back `x`. -/
@[simp] theorem toLp_pointEquiv (x : Point) :
    WithLp.toLp 2 (pointEquiv x) = x := by
  exact WithLp.ofLp_toLp 2 x

/-- Helper for Chapter09 Lemma 9.4.1: near `xStar`, every point satisfying the active-set
equalities is feasible for the original quadratic program. -/
theorem eventuallyFeasibleOfMemActiveSetFeasibleSet
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hFeasible : xStar ∈ P.feasibleSet) :
    P.feasibleSet ∈ nhdsWithin xStar (P.activeSetFeasibleSet xStar) := by
  rcases (P.mem_feasibleSet_iff xStar).1 hFeasible with ⟨_, hIneqStar⟩
  have hInactiveEventually :
      ∀ i : Fin mi,
        i ∉ P.activeSet xStar →
          ∀ᶠ x : Point in nhds xStar, P.bineq i < (P.Aineq.mulVec x) i := by
    intro i hiInactive
    have hne : P.bineq i ≠ (P.Aineq.mulVec xStar) i := by
      intro hEq
      exact hiInactive ((P.mem_activeSet_iff xStar i).2 hEq.symm)
    have hlt : P.bineq i < (P.Aineq.mulVec xStar) i :=
      lt_of_le_of_ne (hIneqStar i) hne
    have hcont :
        ContinuousAt (fun x : Point ↦ (P.Aineq.mulVec x) i) xStar := by
      have hrow :
          (fun x : Point ↦ (P.Aineq.mulVec x) i) =
            fun x : Point ↦ inner ℝ (WithLp.toLp 2 (P.Aineq i)) x := by
        funext x
        calc
          (P.Aineq.mulVec x) i = P.Aineq i ⬝ᵥ x := by
            rfl
          _ = x ⬝ᵥ P.Aineq i := by
            rw [dotProduct_comm]
          _ = inner ℝ (WithLp.toLp 2 (P.Aineq i)) x := by
            symm
            simpa using (EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 (P.Aineq i)) x)
      rw [hrow]
      exact
        (((InnerProductSpace.toDual ℝ Point) (WithLp.toLp 2 (P.Aineq i))).continuous.continuousAt)
    have hconst : ContinuousAt (fun _ : Point ↦ P.bineq i) xStar := continuousAt_const
    simpa using hconst.eventually_lt hcont hlt
  have hStrictInactive :
      ∀ᶠ x : Point in nhds xStar,
        ∀ i : Fin mi, i ∉ P.activeSet xStar → P.bineq i < (P.Aineq.mulVec x) i := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : i ∈ P.activeSet xStar
    · exact Filter.Eventually.of_forall fun _ hx ↦ False.elim (hx hi)
    · exact (hInactiveEventually i hi).mono fun _ hx _ ↦ hx
  -- Combine the preserved active equalities with the nearby strict inactive inequalities.
  rw [nhdsWithin, Filter.mem_inf_principal]
  refine hStrictInactive.mono ?_
  intro x hxStrict hxActive
  rcases (P.mem_activeSetFeasibleSet_iff xStar x).1 hxActive with ⟨hEq, hActiveEq⟩
  refine (P.mem_feasibleSet_iff x).2 ⟨hEq, ?_⟩
  intro i
  by_cases hi : i ∈ P.activeSet xStar
  · simp [hActiveEq i hi]
  · exact le_of_lt (hxStrict i hi)


/-- First direction of Chapter09 Lemma 9.4.1: if `xStar` is a feasible local minimizer of the
quadratic program `P`, then `xStar` is also a local minimizer of the active-set
equality-constrained subproblem whose feasible set is `P.activeSetFeasibleSet xStar`. -/
theorem isLocalMinOn_activeSetFeasibleSet_of_feasible_of_isLocalMinOn
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hFeasible : xStar ∈ P.feasibleSet)
    (hLocalMin : IsLocalMinOn P.objective P.feasibleSet xStar) :
    IsLocalMinOn P.objective (P.activeSetFeasibleSet xStar) xStar := by
  have hFeasibleNear :
      P.feasibleSet ∈ nhdsWithin xStar (P.activeSetFeasibleSet xStar) :=
    P.eventuallyFeasibleOfMemActiveSetFeasibleSet xStar hFeasible
  -- Restrict the local minimum from the original feasible filter to the active-set feasible
  -- filter, using that the latter is locally contained in the former near `xStar`.
  exact hLocalMin.filter_mono <|
    le_inf inf_le_left (Filter.le_principal_iff.2 hFeasibleNear)

/-- Helper for Chapter09 Lemma 9.4.1: the Chapter 8 Euclidean objective transport of a quadratic
program is the explicit quadratic form on Euclidean points. -/
theorem activeSetEuclideanObjective_eq
    (P : QuadraticProgram n me mi) (x : Point) :
    P.toConstrainedOptimizationProblem.euclideanObjective x =
      (1 / 2 : ℝ) * inner ℝ x (Matrix.toEuclideanLin P.G x) + inner ℝ P.g x := by
  -- Collapse the Chapter 8 transport back to the original quadratic objective.
  calc
    P.toConstrainedOptimizationProblem.euclideanObjective x
        = P.objective (((EuclideanSpace.equiv (Fin n) ℝ).symm) (pointEquiv x)) := by
            rfl
    _ = P.objective x := by
          exact congrArg P.objective (toLp_pointEquiv x)
    _ = (1 / 2 : ℝ) * dotProduct x (P.G.mulVec x) + dotProduct P.g x := by
          rw [P.objective_eq]
    _ = (1 / 2 : ℝ) * inner ℝ x (Matrix.toEuclideanLin P.G x) + inner ℝ P.g x := by
          congr 1
          · congr 1
            calc
              dotProduct x (P.G.mulVec x) = dotProduct (P.G.mulVec x) x := by
                rw [dotProduct_comm]
              _ = inner ℝ x (Matrix.toEuclideanLin P.G x) := by
                    symm
                    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
                      (EuclideanSpace.inner_eq_star_dotProduct x (Matrix.toEuclideanLin P.G x))
          · symm
            simpa [dotProduct_comm] using
              (EuclideanSpace.inner_eq_star_dotProduct P.g x)

/-- Helper for Chapter09 Lemma 9.4.1: the quadratic core of the transported objective has
Fréchet derivative `G x` on the Euclidean model. -/
theorem activeSetEuclideanQuadraticCore_hasFDerivAt
    (P : QuadraticProgram n me mi) (x : Point) :
    HasFDerivAt
      (fun y : Point ↦ (1 / 2 : ℝ) * inner ℝ y (Matrix.toEuclideanLin P.G y))
      (InnerProductSpace.toDual ℝ Point (Matrix.toEuclideanLin P.G x))
      x := by
  let T : Point →L[ℝ] Point := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin P.G)
  have hHermitian : P.G.IsHermitian := by
    simpa [Matrix.isHermitian_iff_isSymm] using P.hG_symm
  have hSymmLin' : (Matrix.toEuclideanLin P.G).IsSymmetric := by
    exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P.G)).2 hHermitian
  have hSymmLin : (T : Point →ₗ[ℝ] Point).IsSymmetric := by
    simpa [T] using hSymmLin'
  -- Route correction: differentiate the symmetric quadratic core once at the Euclidean owner.
  have hCore :
      HasStrictFDerivAt
        (fun y : Point ↦ T.reApplyInnerSelf y)
        (2 • innerSL ℝ (T x))
        x :=
    hSymmLin.hasStrictFDerivAt_reApplyInnerSelf x
  have hScaled :
      HasFDerivAt
        (fun y : Point ↦ (1 / 2 : ℝ) * T.reApplyInnerSelf y)
        ((1 / 2 : ℝ) • (2 • innerSL ℝ (T x)))
        x :=
    hCore.hasFDerivAt.const_mul (1 / 2 : ℝ)
  -- Rewrite the abstract symmetric-operator form back to the quadratic expression used here.
  have hFun :
      (fun y : Point ↦ (1 / 2 : ℝ) * T.reApplyInnerSelf y) =
        (fun y : Point ↦ (1 / 2 : ℝ) * inner ℝ y (Matrix.toEuclideanLin P.G y)) := by
    funext y
    calc
      (1 / 2 : ℝ) * T.reApplyInnerSelf y
          = (1 / 2 : ℝ) * inner ℝ (T y) y := by
              simp [ContinuousLinearMap.reApplyInnerSelf_apply]
      _ = (1 / 2 : ℝ) * inner ℝ y (T y) := by
            rw [real_inner_comm]
      _ = (1 / 2 : ℝ) * inner ℝ y (Matrix.toEuclideanLin P.G y) := by
            simp [T]
  have hDeriv :
      ((1 / 2 : ℝ) • (2 • innerSL ℝ (T x))) =
        InnerProductSpace.toDual ℝ Point (Matrix.toEuclideanLin P.G x) := by
    ext y
    simp [T, InnerProductSpace.toDual_apply_apply]
  rw [hFun, hDeriv] at hScaled
  exact hScaled

/-- Helper for Chapter09 Lemma 9.4.1: the transported Chapter 8 Euclidean objective has gradient
`g + G xStar` at the active-set base point. -/
theorem activeSetObjectiveHasGradientAt
    (P : QuadraticProgram n me mi) (xStar : Point) :
    HasGradientAt
      P.toConstrainedOptimizationProblem.euclideanObjective
      (P.g + Matrix.toEuclideanLin P.G xStar)
      (WithLp.toLp 2 (pointEquiv xStar)) := by
  have hBase :
      HasGradientAt
        P.toConstrainedOptimizationProblem.euclideanObjective
        (P.g + Matrix.toEuclideanLin P.G xStar)
        xStar := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hQuadratic := P.activeSetEuclideanQuadraticCore_hasFDerivAt xStar
    have hLinear :
        HasFDerivAt
          (fun y : Point ↦ inner ℝ P.g y)
          (InnerProductSpace.toDual ℝ Point P.g)
          xStar := by
      -- The linear term is already the continuous linear functional induced by `g`.
      exact (InnerProductSpace.toDual ℝ Point P.g).hasFDerivAt
    -- Assemble the normalized quadratic and linear pieces of the transported objective.
    have hObjective :
        P.toConstrainedOptimizationProblem.euclideanObjective =
          (fun y : Point ↦ (1 / 2 : ℝ) * inner ℝ y (Matrix.toEuclideanLin P.G y)) +
            ((fun y : Point ↦ inner ℝ P.g y) + fun _ : Point ↦ 0) := by
      funext y
      rw [P.activeSetEuclideanObjective_eq]
      simp
    have hDeriv :
        InnerProductSpace.toDual ℝ Point (P.g + Matrix.toEuclideanLin P.G xStar) =
          InnerProductSpace.toDual ℝ Point (Matrix.toEuclideanLin P.G xStar) +
            (InnerProductSpace.toDual ℝ Point P.g + 0) := by
      ext y
      simp [InnerProductSpace.toDual_apply_apply, add_comm]
    rw [hObjective, hDeriv]
    exact hQuadratic.add (hLinear.add (hasFDerivAt_const (0 : ℝ) xStar))
  -- Return to the Chapter 8 base point spelling used by the KKT theorem.
  simpa [toLp_pointEquiv xStar, add_comm] using hBase

/-- Helper for Chapter09 Lemma 9.4.1: the Chapter 8 Euclidean objective gradient of the
quadratic-program bridge is the source quadratic gradient `g + G xStar`. -/
theorem activeSetObjectiveGradient_eq
    (P : QuadraticProgram n me mi) (xStar : Point) :
    gradient P.toConstrainedOptimizationProblem.euclideanObjective
      (WithLp.toLp 2 (pointEquiv xStar)) =
      P.g + Matrix.toEuclideanLin P.G xStar := by
  -- Route correction: use the local Euclidean objective-gradient bridge instead of the unstable
  -- external Chapter 4 import path.
  exact (P.activeSetObjectiveHasGradientAt xStar).gradient

/-- Helper for Chapter09 Lemma 9.4.1: the gradient of an equality-block constraint is the
corresponding equality row of `Aeq`. -/
theorem activeSetEqConstraintGradient_eq
    (P : QuadraticProgram n me mi) (xStar : Point) (i : Fin me) :
    gradient
        (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.castAdd mi i))
        (WithLp.toLp 2 (pointEquiv xStar)) =
      WithLp.toLp 2 (P.Aeq i) := by
  have hConstraint :
      P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.castAdd mi i) =
        fun x : Point ↦ inner ℝ (WithLp.toLp 2 (P.Aeq i)) x - P.beq i := by
    -- Rewrite the transported equality constraint into the affine row residual.
    ext x
    calc
      P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.castAdd mi i) x
          = P.standardConstraint (Fin.castAdd mi i)
              (((EuclideanSpace.equiv (Fin n) ℝ).symm) (pointEquiv x)) := by
              rfl
      _ = P.standardConstraint (Fin.castAdd mi i) x := by
            exact congrArg (P.standardConstraint (Fin.castAdd mi i)) (toLp_pointEquiv x)
      _ = (P.Aeq.mulVec x) i - P.beq i := P.standardConstraint_castAdd_eq i x
      _ = inner ℝ (WithLp.toLp 2 (P.Aeq i)) x - P.beq i := by
            congr 1
            calc
              (P.Aeq.mulVec x) i = P.Aeq i ⬝ᵥ x := by
                rfl
              _ = x ⬝ᵥ P.Aeq i := by
                rw [dotProduct_comm]
              _ = inner ℝ (WithLp.toLp 2 (P.Aeq i)) x := by
                symm
                simpa using (EuclideanSpace.inner_eq_star_dotProduct
                  (WithLp.toLp 2 (P.Aeq i)) x)
  -- Differentiate the affine row residual against arbitrary directions.
  apply ext_inner_left ℝ
  intro z
  calc
    inner ℝ z
        (gradient
          (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.castAdd mi i))
          (WithLp.toLp 2 (pointEquiv xStar)))
        = fderiv ℝ
            (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.castAdd mi i))
            (WithLp.toLp 2 (pointEquiv xStar)) z := by
              simp [inner_gradient_right]
    _ = inner ℝ z (WithLp.toLp 2 (P.Aeq i)) := by
          rw [hConstraint]
          rw [fderiv_sub_const]
          change
            (fderiv ℝ (InnerProductSpace.toDual ℝ Point (WithLp.toLp 2 (P.Aeq i)))
              (WithLp.toLp 2 (pointEquiv xStar))) z =
              inner ℝ z (WithLp.toLp 2 (P.Aeq i))
          rw [(InnerProductSpace.toDual ℝ Point (WithLp.toLp 2 (P.Aeq i))).fderiv]
          rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]

/-- Helper for Chapter09 Lemma 9.4.1: the gradient of an inequality-block constraint is the
corresponding inequality row of `Aineq`. -/
theorem activeSetIneqConstraintGradient_eq
    (P : QuadraticProgram n me mi) (xStar : Point) (i : Fin mi) :
    gradient
        (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.natAdd me i))
        (WithLp.toLp 2 (pointEquiv xStar)) =
      WithLp.toLp 2 (P.Aineq i) := by
  have hConstraint :
      P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.natAdd me i) =
        fun x : Point ↦ inner ℝ (WithLp.toLp 2 (P.Aineq i)) x - P.bineq i := by
    -- Rewrite the transported inequality constraint into the affine row residual.
    ext x
    calc
      P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.natAdd me i) x
          = P.standardConstraint (Fin.natAdd me i)
              (((EuclideanSpace.equiv (Fin n) ℝ).symm) (pointEquiv x)) := by
              rfl
      _ = P.standardConstraint (Fin.natAdd me i) x := by
            exact congrArg (P.standardConstraint (Fin.natAdd me i)) (toLp_pointEquiv x)
      _ = (P.Aineq.mulVec x) i - P.bineq i := P.standardConstraint_natAdd_eq i x
      _ = inner ℝ (WithLp.toLp 2 (P.Aineq i)) x - P.bineq i := by
            congr 1
            calc
              (P.Aineq.mulVec x) i = P.Aineq i ⬝ᵥ x := by
                rfl
              _ = x ⬝ᵥ P.Aineq i := by
                rw [dotProduct_comm]
              _ = inner ℝ (WithLp.toLp 2 (P.Aineq i)) x := by
                symm
                simpa using (EuclideanSpace.inner_eq_star_dotProduct
                  (WithLp.toLp 2 (P.Aineq i)) x)
  -- Differentiate the affine row residual against arbitrary directions.
  apply ext_inner_left ℝ
  intro z
  calc
    inner ℝ z
        (gradient
          (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.natAdd me i))
          (WithLp.toLp 2 (pointEquiv xStar)))
        = fderiv ℝ
            (P.toConstrainedOptimizationProblem.euclideanConstraint (Fin.natAdd me i))
            (WithLp.toLp 2 (pointEquiv xStar)) z := by
              simp [inner_gradient_right]
    _ = inner ℝ z (WithLp.toLp 2 (P.Aineq i)) := by
          rw [hConstraint]
          rw [fderiv_sub_const]
          change
            (fderiv ℝ (InnerProductSpace.toDual ℝ Point (WithLp.toLp 2 (P.Aineq i)))
              (WithLp.toLp 2 (pointEquiv xStar))) z =
              inner ℝ z (WithLp.toLp 2 (P.Aineq i))
          rw [(InnerProductSpace.toDual ℝ Point (WithLp.toLp 2 (P.Aineq i))).fderiv]
          rw [InnerProductSpace.toDual_apply_apply, real_inner_comm]

/-- Helper for Chapter09 Lemma 9.4.1: the multiplier-weighted Chapter 8 constraint-gradient sum
is exactly the source matrix expression
`Aeq.transpose.mulVec mult.1 + Aineq.transpose.mulVec mult.2`. -/
theorem activeSetConstraintGradientSum_eq
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier) :
    ∑ i : Fin (me + mi),
        (Fin.append mult.1 mult.2) i •
          gradient (P.toConstrainedOptimizationProblem.euclideanConstraint i)
            (WithLp.toLp 2 (pointEquiv xStar)) =
      P.Aeq.transpose.mulVec mult.1 + P.Aineq.transpose.mulVec mult.2 := by
  have hSplit :
      ∑ i : Fin (me + mi),
          (Fin.append mult.1 mult.2) i •
            gradient (P.toConstrainedOptimizationProblem.euclideanConstraint i)
              (WithLp.toLp 2 (pointEquiv xStar))
        =
          ∑ s : Fin me ⊕ Fin mi,
            match s with
            | Sum.inl j => mult.1 j • WithLp.toLp 2 (P.Aeq j)
            | Sum.inr j => mult.2 j • WithLp.toLp 2 (P.Aineq j) := by
        rw [← Equiv.sum_comp finSumFinEquiv]
        refine Finset.sum_congr rfl ?_
        intro s hs
        cases s with
        | inl j =>
            simpa [toLp_pointEquiv xStar] using
              congrArg (fun v : Point ↦ mult.1 j • v) (P.activeSetEqConstraintGradient_eq xStar j)
        | inr j =>
            simpa [toLp_pointEquiv xStar] using
              congrArg (fun v : Point ↦ mult.2 j • v) (P.activeSetIneqConstraintGradient_eq xStar j)
  rw [hSplit]
  rw [show
    (∑ s : Fin me ⊕ Fin mi,
        match s with
        | Sum.inl j => mult.1 j • WithLp.toLp 2 (P.Aeq j)
        | Sum.inr j => mult.2 j • WithLp.toLp 2 (P.Aineq j)) =
      (∑ j : Fin me, mult.1 j • WithLp.toLp 2 (P.Aeq j)) +
        ∑ j : Fin mi, mult.2 j • WithLp.toLp 2 (P.Aineq j) by
      simp]
  -- Compare both sides coordinatewise using the matrix multiplication formula.
  ext k
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Helper for Chapter09 Lemma 9.4.1: the source stationarity equation yields the Chapter 8
Euclidean Lagrangian stationarity field at `xStar`. -/
theorem activeSetStationarityZeroGradient
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier)
    (hStationarity :
      P.g + Matrix.toEuclideanLin P.G xStar =
        P.Aeq.transpose.mulVec mult.1 + P.Aineq.transpose.mulVec mult.2) :
    ∇ (P.toConstrainedOptimizationProblem.euclideanLagrangian (Fin.append mult.1 mult.2))
      (WithLp.toLp 2 (pointEquiv xStar)) = 0 := by
  -- Route correction: normalize the Chapter 8 Lagrangian gradient once, then rewrite both the
  -- objective and constraint-gradient blocks to the source matrix stationarity equation.
  rw [P.toConstrainedOptimizationProblem.gradient_euclideanLagrangian_eq_objective_sub_sum
      (pointEquiv xStar) (Fin.append mult.1 mult.2)
      (P.toConstrainedOptimizationProblem_differentiableAt_objective xStar)
      (P.toConstrainedOptimizationProblem_hasConstraintGradientsAt xStar)]
  rw [P.activeSetObjectiveGradient_eq xStar]
  have hConstraintSum := P.activeSetConstraintGradientSum_eq xStar mult
  -- Compare the remaining vector identity coordinatewise to avoid coercion noise from
  -- `EuclideanSpace`.
  ext k
  have hConstraintCoord := congrArg (fun v : Fin n → ℝ ↦ v k) hConstraintSum
  have hStationarityCoord := congrArg (fun v : Fin n → ℝ ↦ v k) hStationarity
  simpa using sub_eq_zero.2 (hStationarityCoord.trans hConstraintCoord.symm)

/-- Helper for Chapter09 Lemma 9.4.1: every inequality index of the Chapter 8 bridge carries a
nonnegative multiplier when the active multipliers are nonnegative and inactive multipliers
vanish. -/
theorem activeSetMultiplierDualFeasible
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier)
    (hActiveKKT : P.SatisfiesActiveSetKKT xStar mult)
    (hActiveDualNonneg : ∀ i, i ∈ P.activeSet xStar → 0 ≤ mult.2 i) :
    ∀ {i : Fin (me + mi)}, i ∈ P.toConstrainedOptimizationProblem.ineqIndices →
      0 ≤ (Fin.append mult.1 mult.2) i := by
  rcases (P.satisfiesActiveSetKKT_iff xStar mult).1 hActiveKKT with ⟨_, _, hInactiveZero⟩
  intro i hi
  -- Split the combined index into equality and inequality blocks.
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hiEq : i = Fin.castAdd mi j := by
        simpa using congrArg finSumFinEquiv hsplit
      have hbad : me ≤ j.1 := by
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          ConstrainedOptimizationProblem.ineqIndices,
          StandardConstrainedOptimizationProblem.ineqIndices, hiEq] using hi
      exact False.elim ((Nat.not_le_of_gt j.is_lt) hbad)
  | inr j =>
      have hiEq : i = Fin.natAdd me j := by
        simpa using congrArg finSumFinEquiv hsplit
      by_cases hj : j ∈ P.activeSet xStar
      · -- Active inequality multipliers are nonnegative by hypothesis.
        simpa [hiEq] using hActiveDualNonneg j hj
      · -- Inactive inequality multipliers vanish in the active-set KKT system.
        have hz : mult.2 j = 0 := hInactiveZero j hj
        simp [hiEq, hz]

/-- Helper for Chapter09 Lemma 9.4.1: the combined Chapter 8 multiplier vector satisfies
complementary slackness on every inequality index of the bridge problem. -/
theorem activeSetMultiplierComplementarySlackness
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier)
    (hActiveKKT : P.SatisfiesActiveSetKKT xStar mult) :
    ∀ {i : Fin (me + mi)}, i ∈ P.toConstrainedOptimizationProblem.ineqIndices →
      (Fin.append mult.1 mult.2) i *
        P.toConstrainedOptimizationProblem.constraint i (pointEquiv xStar) = 0 := by
  rcases (P.satisfiesActiveSetKKT_iff xStar mult).1 hActiveKKT with ⟨_, _, hInactiveZero⟩
  intro i hi
  -- Split the combined index into equality and inequality blocks.
  cases hsplit : finSumFinEquiv.symm i with
  | inl j =>
      have hiEq : i = Fin.castAdd mi j := by
        simpa using congrArg finSumFinEquiv hsplit
      have hbad : me ≤ j.1 := by
        simpa [QuadraticProgram.toStandardConstrainedOptimizationProblem,
          ConstrainedOptimizationProblem.ineqIndices,
          StandardConstrainedOptimizationProblem.ineqIndices, hiEq] using hi
      exact False.elim ((Nat.not_le_of_gt j.is_lt) hbad)
  | inr j =>
      have hiEq : i = Fin.natAdd me j := by
        simpa using congrArg finSumFinEquiv hsplit
      by_cases hj : j ∈ P.activeSet xStar
      · -- Active inequalities have zero residual by the definition of `activeSet`.
        have hActiveEq : (P.Aineq.mulVec xStar) j = P.bineq j :=
          (P.mem_activeSet_iff xStar j).1 hj
        subst hiEq
        have hConstraintZero :
            P.toConstrainedOptimizationProblem.constraint
              (Fin.natAdd me j) (pointEquiv xStar) = 0 := by
          calc
            P.toConstrainedOptimizationProblem.constraint (Fin.natAdd me j) (pointEquiv xStar)
                = P.standardConstraint (Fin.natAdd me j)
                    (((EuclideanSpace.equiv (Fin n) ℝ).symm) (pointEquiv xStar)) := by
                        rfl
            _ = P.standardConstraint (Fin.natAdd me j) xStar := by
                  exact congrArg (P.standardConstraint (Fin.natAdd me j))
                    (toLp_pointEquiv xStar)
            _ = (P.Aineq.mulVec xStar) j - P.bineq j := P.standardConstraint_natAdd_eq j xStar
            _ = 0 := by
                  rw [hActiveEq, sub_self]
        rw [hConstraintZero]
        simp
      · -- Inactive inequalities have zero multiplier in the active-set KKT system.
        have hz : mult.2 j = 0 := hInactiveZero j hj
        subst hiEq
        simp [hz]

/-- Chapter09 Lemma 9.4.1 (2): if `xStar` is feasible for `P`, if `mult` satisfies the active-set
equality-constrained KKT system at `xStar`, and if the active inequality multipliers are
nonnegative, then `(mult.1, mult.2)` is a Chapter 8 KKT multiplier pair for the original
quadratic program. -/
theorem isKKTPoint_of_feasible_of_satisfiesActiveSetKKT
    (P : QuadraticProgram n me mi) (xStar : Point) (mult : Multiplier)
    (hFeasible : xStar ∈ P.feasibleSet)
    (hActiveKKT : P.SatisfiesActiveSetKKT xStar mult)
    (hActiveDualNonneg : ∀ i, i ∈ P.activeSet xStar → 0 ≤ mult.2 i) :
    P.toConstrainedOptimizationProblem.IsKKTPoint
      (pointEquiv xStar)
      (Fin.append mult.1 mult.2) := by
  rcases (P.satisfiesActiveSetKKT_iff xStar mult).1 hActiveKKT with
    ⟨hStationarity, _, _⟩
  refine
    { feasible := (P.mem_toConstrainedOptimizationProblem_iff xStar).2 hFeasible
      dualFeasible := ?_
      stationarity := ?_
      complementarySlackness := ?_ }
  · -- The inequality-side multiplier conditions are exactly the active/inactive split.
    intro i hi
    exact P.activeSetMultiplierDualFeasible xStar mult hActiveKKT hActiveDualNonneg hi
  · -- The Chapter 8 stationarity field is the normalized form of the source matrix equation.
    exact P.activeSetStationarityZeroGradient xStar mult hStationarity
  · -- Complementary slackness follows from zero residual on active inequalities and zero
    -- multiplier on inactive inequalities.
    intro i hi
    exact P.activeSetMultiplierComplementarySlackness xStar mult hActiveKKT hi

end QuadraticProgram

end Chapter09Lemma941
