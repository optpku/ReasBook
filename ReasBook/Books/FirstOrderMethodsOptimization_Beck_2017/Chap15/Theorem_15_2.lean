/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import FirstOrderMethodsOptimization_Beck_2017.Chap02.FunctionToEReal
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_3
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Algorithm_15_4
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_2
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Definition_15_4
import FirstOrderMethodsOptimization_Beck_2017.Chap15.Theorem_15_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w uE

open InnerProductSpace (toDual)
open scoped BigOperators
open scoped Gradient
section

variable {X : Type u} {Z : Type v} {Y : Type w}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y]

section

variable {h₁ : X → EReal} {h₂ : Z → EReal}
variable {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
variable {ρ : PosReal}
variable {G : X →ₗ[ℝ] X} {Q : Z →ₗ[ℝ] Z}
variable {x0 : X} {z0 : Z} {y0 : Y}
variable {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}

/- Domain sampling for Theorem 15.2:
- `source-facing`: the textbook ergodic averages `x^(n)` and `z^(n)`, together with the displayed
  averaged primal-gap and feasibility estimate under Assumption 15.2;
- `core/canonical`: `Finset.centerMass` for constant-weight finite averages and
  `IsADPMMProblem` for the Chapter 15 assumption bundle;
- `bridge/view`: the proximal penalties in Assumption 15.2 are linear operators `G` and `Q`, so
  this file states the trajectory and displayed bounds directly in that linear-map language rather
  than routing through a separate quadratic-form owner. The dual maximization hypothesis reuses
  the canonical Chapter 15 primal-space owner `admm_dual_objective_primal`.

This file therefore keeps the public theorem surface source-faithful over
`hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c`, while keeping only the thin local helper owners
needed for the ergodic averages and the canonical trajectory/optimality bridges. -/
-- Semantic search note: the source layer is modeled by adding
-- `[FiniteDimensional ℝ X]`, `[FiniteDimensional ℝ Z]`, and `[FiniteDimensional ℝ Y]`
-- on top of the real inner-product-space structure while keeping the equivalent explicit
-- finite-sum average for a lightweight source-facing statement surface.
/-- The ergodic average
`(1 / (n + 1)) ∑_{k=0}^n u^(k+1)` of the first `n + 1` shifted iterates of `u`. -/
def ergodicAverage {E : Type uE} [AddCommGroup E] [Module ℝ E] (u : ℕ → E) (n : ℕ) : E :=
  (1 / ((n : ℝ) + 1)) • Finset.sum (Finset.range (n + 1)) (fun k ↦ u (k + 1))

/-- The quadratic form associated with a linear operator `P`, namely
`u ↦ ⟪u, P u⟫`. -/
def quadraticPenaltyOfLinearMap
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) : QuadraticForm ℝ E :=
  LinearMap.BilinMap.toQuadraticMap ((innerₗ E).compl₂ P)

/-- Evaluating `quadraticPenaltyOfLinearMap P` recovers the source expression `⟪u, P u⟫`. -/
@[simp] theorem quadraticPenaltyOfLinearMap_apply
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (u : E) :
    quadraticPenaltyOfLinearMap P u = inner ℝ u (P u) :=
  rfl

/-- Helper for Theorem 15.2: scaling the argument of a quadratic penalty scales its value by the
square of the scalar. -/
@[simp] private theorem quadraticPenaltyOfLinearMap_smul
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (t : ℝ) (u : E) :
    quadraticPenaltyOfLinearMap P (t • u) = t ^ (2 : ℕ) * quadraticPenaltyOfLinearMap P u := by
  -- Expand the quadratic penalty to the underlying inner product and collect the two scalar
  -- factors coming from bilinearity.
  simp [quadraticPenaltyOfLinearMap_apply, real_inner_smul_left, real_inner_smul_right]
  ring

/-- A source-facing AD-PMM trajectory with linear proximal penalties `G` and `Q`, realized as
Algorithm 15.4 with the quadratic penalties `u ↦ ⟪u, G u⟫` and `u ↦ ⟪u, Q u⟫`. -/
def IsADPMMLinearTrajectory
    (ρ : PosReal)
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (G : X →ₗ[ℝ] X) (Q : Z →ₗ[ℝ] Z)
    (x0 : X) (z0 : Z) (y0 : Y)
    (x : ℕ → X) (z : ℕ → Z) (y : ℕ → Y) : Prop :=
  IsADPMMTrajectory ρ h₁ h₂ A B c
    (quadraticPenaltyOfLinearMap G) (quadraticPenaltyOfLinearMap Q)
    x0 z0 y0 x z y

namespace IsADPMMLinearTrajectory

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Forgetting the source-facing linear-penalty presentation recovers the canonical
Algorithm 15.4 trajectory owner. -/
theorem toIsADPMMTrajectory
    {ρ : PosReal}
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {G : X →ₗ[ℝ] X} {Q : Z →ₗ[ℝ] Z}
    {x0 : X} {z0 : Z} {y0 : Y}
    {x : ℕ → X} {z : ℕ → Z} {y : ℕ → Y}
    (h : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y) :
    IsADPMMTrajectory ρ h₁ h₂ A B c
      (quadraticPenaltyOfLinearMap G) (quadraticPenaltyOfLinearMap Q)
      x0 z0 y0 x z y :=
  h

end IsADPMMLinearTrajectory

/-- The source-facing primal optimality predicate for the AD-PMM problem data of Theorem 15.2. -/
def IsADPMMPrimalOptimal
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (xStar : X) (zStar : Z) : Prop :=
  (xStar, zStar) ∈ constrained_problem_solutions (H[h₁, h₂]) (admm_feasible_set A B c)

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Expanding `IsADPMMPrimalOptimal` recovers feasibility together with the canonical minimizer
predicate on `admm_feasible_set A B c`. -/
@[simp] theorem isADPMMPrimalOptimal_iff
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (xStar : X) (zStar : Z) :
    IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar ↔
      (xStar, zStar) ∈ constrained_problem_solutions (H[h₁, h₂]) (admm_feasible_set A B c) :=
  Iff.rfl

namespace IsADPMMPrimalOptimal

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- A primal-optimal pair is feasible for the AD-PMM affine constraint. -/
theorem feasible
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {xStar : X} {zStar : Z}
    (h : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar) :
    (xStar, zStar) ∈ admm_feasible_set A B c :=
  (mem_constrained_problem_solutions_iff.mp h).1

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- A primal-optimal pair minimizes `H[h₁, h₂]` on `admm_feasible_set A B c`. -/
theorem isMinOn
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {xStar : X} {zStar : Z}
    (h : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar) :
    IsMinOn (H[h₁, h₂]) (admm_feasible_set A B c) (xStar, zStar) :=
  (mem_constrained_problem_solutions_iff.mp h).2

end IsADPMMPrimalOptimal

/-- The source-facing dual optimality predicate for the AD-PMM dual problem of Theorem 15.2. -/
def IsADPMMDualOptimal
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (yStar : Y) : Prop :=
  IsMaxOn (admm_dual_objective_primal h₁ h₂ A B c) Set.univ yStar

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Expanding `IsADPMMDualOptimal` recovers the canonical `IsMaxOn` owner on the primal-space
dual objective. -/
@[simp] theorem isADPMMDualOptimal_iff
    (h₁ : X → EReal) (h₂ : Z → EReal)
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (yStar : Y) :
    IsADPMMDualOptimal h₁ h₂ A B c yStar ↔
      IsMaxOn (admm_dual_objective_primal h₁ h₂ A B c) Set.univ yStar :=
  Iff.rfl

namespace IsADPMMDualOptimal

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- A dual-optimal point is a maximizer of `admm_dual_objective_primal h₁ h₂ A B c`. -/
theorem isMaxOn
    {h₁ : X → EReal} {h₂ : Z → EReal}
    {A : X →ₗ[ℝ] Y} {B : Z →ₗ[ℝ] Y} {c : Y}
    {yStar : Y}
    (h : IsADPMMDualOptimal h₁ h₂ A B c yStar) :
    IsMaxOn (admm_dual_objective_primal h₁ h₂ A B c) Set.univ yStar :=
  h

end IsADPMMDualOptimal

/-- Helper for Theorem 15.2: the real inner-product four-point identity
`2 ⟪a - b, c - d⟫ = ‖a - d‖² - ‖a - c‖² + ‖b - c‖² - ‖b - d‖²`. -/
private theorem realInner_sub_sub_eq_norm_sub_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b c d : E) :
    2 * inner ℝ (a - b) (c - d) =
      ‖a - d‖ ^ (2 : ℕ) - ‖a - c‖ ^ (2 : ℕ) +
        ‖b - c‖ ^ (2 : ℕ) - ‖b - d‖ ^ (2 : ℕ) := by
  -- Expand the left-hand side into the four scalar pairings appearing in the norm identity.
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  -- Expand the right-hand side with `norm_sub_sq_real`; the remaining statement is scalar algebra.
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real]
  ring

/-- Helper for Theorem 15.2: positive quadratic penalties satisfy the standard three-point
identity used to telescope the `G`- and `Q`-terms in the Lyapunov estimate. -/
private theorem positiveLinearPenalty_threePoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (hP : P.IsPositive) (u v a : E) :
    quadraticPenaltyOfLinearMap P (u - a) - quadraticPenaltyOfLinearMap P (v - a) =
      quadraticPenaltyOfLinearMap P (u - v) +
        2 * inner ℝ (u - v) (P (v - a)) := by
  -- Rewrite every quadratic term as the source inner-product expression.
  simp only [quadraticPenaltyOfLinearMap_apply, map_sub, inner_sub_left, inner_sub_right]
  -- Positivity gives symmetry, so all mixed terms can be oriented as `inner _ (P _)`.
  have huv : inner ℝ u (P v) = inner ℝ v (P u) := by
    calc
      inner ℝ u (P v) = inner ℝ (P v) u := by rw [real_inner_comm]
      _ = inner ℝ v (P u) := hP.isSymmetric v u
  have hua : inner ℝ a (P u) = inner ℝ u (P a) := by
    calc
      inner ℝ a (P u) = inner ℝ (P u) a := by rw [real_inner_comm]
      _ = inner ℝ u (P a) := hP.isSymmetric u a
  have hva : inner ℝ a (P v) = inner ℝ v (P a) := by
    calc
      inner ℝ a (P v) = inner ℝ (P v) a := by rw [real_inner_comm]
      _ = inner ℝ v (P a) := hP.isSymmetric v a
  rw [huv, hua, hva]
  ring

/-- Helper for Theorem 15.2: the shifted multiplier term satisfies the same three-point inequality
as in the source proof, with the defect measured by the shift `b`. -/
private theorem multiplierShift_threePoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ρ : PosReal) (yBar yTilde yk yNext b : E)
    (hshift : yTilde = yNext + (ρ : ℝ) • b) :
    (1 / (ρ : ℝ)) * inner ℝ (yBar - yTilde) (yk - yNext) ≥
      (‖yBar - yNext‖ ^ (2 : ℕ) - ‖yBar - yk‖ ^ (2 : ℕ)) / (2 * (ρ : ℝ)) -
        ((ρ : ℝ) / 2) * ‖b‖ ^ (2 : ℕ) := by
  have hρ : (ρ : ℝ) ≠ 0 := by
    exact ne_of_gt ρ.2
  -- The generic four-point identity isolates the two norm differences and the shifted remainder.
  have hfour :=
    realInner_sub_sub_eq_norm_sub_sq yBar yTilde yk yNext
  have hfour' :
      (1 / (ρ : ℝ)) * inner ℝ (yBar - yTilde) (yk - yNext) =
        (‖yBar - yNext‖ ^ (2 : ℕ) - ‖yBar - yk‖ ^ (2 : ℕ)) / (2 * (ρ : ℝ)) +
          ‖yTilde - yk‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) -
          ‖yTilde - yNext‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) := by
    field_simp [hρ] at hfour ⊢
    linarith
  rw [hfour']
  have hy_nonneg : 0 ≤ ‖yTilde - yk‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) := by
    have hden : 0 ≤ 2 * (ρ : ℝ) := by
      exact mul_nonneg (by norm_num) (le_of_lt ρ.2)
    refine div_nonneg ?_ ?_
    · positivity
    · exact hden
  have hshift_norm :
      ‖yTilde - yNext‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) = ((ρ : ℝ) / 2) * ‖b‖ ^ (2 : ℕ) := by
    rw [hshift]
    calc
      ‖(yNext + (ρ : ℝ) • b) - yNext‖ ^ (2 : ℕ) / (2 * (ρ : ℝ))
          = ‖(ρ : ℝ) • b‖ ^ (2 : ℕ) / (2 * (ρ : ℝ)) := by simp
      _ = (((ρ : ℝ) * ‖b‖) ^ (2 : ℕ)) / (2 * (ρ : ℝ)) := by
            simp [norm_smul, Real.norm_of_nonneg ρ.2.le]
      _ = ((ρ : ℝ) / 2) * ‖b‖ ^ (2 : ℕ) := by
            field_simp [hρ]
  -- Drop the nonnegative term and rewrite the shift norm into the source remainder.
  rw [hshift_norm]
  linarith

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: under Assumption 15.2 the ADMM objective never takes the value
`⊥`, because both block objectives are proper. -/
private theorem admmObjective_ne_bot_of_problem
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c) (xz : X × Z) :
    H[h₁, h₂] xz ≠ ⊥ := by
  rcases xz with ⟨x', z'⟩
  -- Expand the ADMM objective into the block sum and use properness of `h₁` and `h₂`.
  simp [hAssump.toIsProperExtendedRealFunction.ne_bot x', hAssump.h₂_proper.ne_bot z']

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: finiteness of the ADMM objective is exactly blockwise finiteness of
`h₁` and `h₂`. -/
private theorem mem_effectiveDomain_admmObjective_iff
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c) (x' : X) (z' : Z) :
    (x', z') ∈ effective_domain (H[h₁, h₂]) ↔
      x' ∈ effective_domain h₁ ∧ z' ∈ effective_domain h₂ := by
  -- Expand `H[h₁, h₂]` and use properness to rule out `⊥` in both blocks.
  simp [effective_domain, lt_top_iff_ne_top, EReal.add_ne_top_iff_ne_top₂,
    hAssump.toIsProperExtendedRealFunction.ne_bot x', hAssump.h₂_proper.ne_bot z']

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: Assumption 15.2 makes the ADMM objective convex on `X × Z`. -/
private theorem admmObjective_convex_of_problem
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c) :
    is_convex_function (H[h₁, h₂]) := by
  -- Pull the block convexity assumptions back along the coordinate projections.
  have hh₁_fst : is_convex_function (fun xz : X × Z ↦ h₁ xz.1) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := h₁) hAssump.h₁_convex (LinearMap.fst ℝ X Z) (0 : X)
  have hh₂_snd : is_convex_function (fun xz : X × Z ↦ h₂ xz.2) := by
    simpa using
      is_convex_function_precompose_linearMap_add
        (f := h₂) hAssump.h₂_convex (LinearMap.snd ℝ X Z) (0 : Z)
  -- The ADMM objective is the pointwise sum of the two projected block objectives.
  simpa [composite_model_objective_eq_add] using
    is_convex_function_pointwise_add
      hh₁_fst hh₂_snd
      (fun xz ↦ hAssump.toIsProperExtendedRealFunction.ne_bot xz.1)
      (fun xz ↦ hAssump.h₂_proper.ne_bot xz.2)

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: every primal-optimal pair has finite ADMM objective value. -/
private theorem primalOptimal_memEffectiveDomain
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar) :
    (xStar, zStar) ∈ effective_domain (H[h₁, h₂]) := by
  rcases hAssump.ri_qualification with ⟨xHat, hxHat, zHat, hzHat, hEq⟩
  have hHatFeas : (xHat, zHat) ∈ admm_feasible_set A B c := by
    simpa [mem_admm_feasible_set] using hEq
  have hHatDom : (xHat, zHat) ∈ effective_domain (H[h₁, h₂]) := by
    -- The qualification witness is finite in both blocks, hence finite for the product objective.
    refine (mem_effectiveDomain_admmObjective_iff
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump xHat zHat).2 ?_
    exact ⟨intrinsicInterior_subset hxHat, intrinsicInterior_subset hzHat⟩
  -- Compare the optimal point against the finite feasible qualification witness.
  refine mem_effective_domain.mpr ?_
  exact lt_of_le_of_lt (hPrimalOpt.isMinOn hHatFeas) (mem_effective_domain.mp hHatDom)

/-- Helper for Theorem 15.2: a global minimizer of an `EReal` objective lies in the effective
domain once the objective is finite at one comparison point. -/
private theorem minimizer_memEffectiveDomain_of_finiteTestPoint
    {E : Type*} {f : E → EReal} {xMin xTest : E}
    (hxMin : IsMinOn f Set.univ xMin)
    (hfinite : f xTest < ⊤) :
    xMin ∈ effective_domain f := by
  -- Compare the minimizing value against the finite comparison point.
  exact mem_effective_domain.mpr <| lt_of_le_of_lt (hxMin (by simp)) hfinite

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: every sampled iterate pair has finite ADMM objective value. -/
private theorem sampledIterate_memEffectiveDomain
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    (k : ℕ) :
    (x (k + 1), z (k + 1)) ∈ effective_domain (H[h₁, h₂]) := by
  have hStarDom :
      (xStar, zStar) ∈ effective_domain (H[h₁, h₂]) :=
    primalOptimal_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump hPrimalOpt
  have hxStarDom : xStar ∈ effective_domain h₁ :=
    (mem_effectiveDomain_admmObjective_iff
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump xStar zStar).1 hStarDom |>.1
  have hzStarDom : zStar ∈ effective_domain h₂ :=
    (mem_effectiveDomain_admmObjective_iff
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump xStar zStar).1 hStarDom |>.2
  have hTrajectory' := hTrajectory.toIsADPMMTrajectory
  have hxStepMin :
      IsMinOn
        (ad_pmm_x_update_objective ρ h₁ A B c (z k) (y k)
          (quadraticPenaltyOfLinearMap G) (x k))
        Set.univ
        (x (k + 1)) := by
    -- Read the `x`-update directly as the minimizing clause from Algorithm 15.4.
    exact (mem_ad_pmm_x_update_argmin_iff).1 (hTrajectory'.x_step k)
  have hxTestFinite :
      ad_pmm_x_update_objective ρ h₁ A B c (z k) (y k)
        (quadraticPenaltyOfLinearMap G) (x k) xStar < ⊤ := by
    -- The primal optimum is a finite test point for the `x`-subproblem objective.
    rw [ad_pmm_x_update_objective_apply, add_assoc]
    exact EReal.add_lt_top
      (mem_effective_domain.mp hxStarDom).ne
      (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne
  have hxNextObjDom :
      x (k + 1) ∈ effective_domain
        (ad_pmm_x_update_objective ρ h₁ A B c (z k) (y k)
          (quadraticPenaltyOfLinearMap G) (x k)) :=
    minimizer_memEffectiveDomain_of_finiteTestPoint hxStepMin hxTestFinite
  have hxNextDom : x (k + 1) ∈ effective_domain h₁ := by
    -- Peel the finite quadratic penalties back off the minimizing `x`-subproblem value.
    refine mem_effective_domain.mpr ?_
    by_contra hxTop
    have hxTopEq : h₁ (x (k + 1)) = ⊤ := le_antisymm le_top (not_lt.mp hxTop)
    have hrest_ne_bot :
        ((((ρ : ℝ) / 2) * ‖A (x (k + 1)) + B (z k) - c + (1 / (ρ : ℝ)) • y k‖ ^ (2 : ℕ) : ℝ) :
            EReal) +
          ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (x (k + 1) - x k) : ℝ) : EReal)) ≠ ⊥ := by
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
    have hxObjTop :
        ad_pmm_x_update_objective ρ h₁ A B c (z k) (y k)
          (quadraticPenaltyOfLinearMap G) (x k) (x (k + 1)) = ⊤ := by
      rw [ad_pmm_x_update_objective_apply, hxTopEq, add_assoc]
      simpa using EReal.top_add_of_ne_bot hrest_ne_bot
    exact (mem_effective_domain.mp hxNextObjDom).ne hxObjTop
  have hzStepMin :
      IsMinOn
        (ad_pmm_z_update_objective ρ h₂ A B c (x (k + 1)) (y k)
          (quadraticPenaltyOfLinearMap Q) (z k))
        Set.univ
        (z (k + 1)) := by
    -- Read the `z`-update directly as the minimizing clause from Algorithm 15.4.
    exact (mem_ad_pmm_z_update_argmin_iff).1 (hTrajectory'.z_step k)
  have hzTestFinite :
      ad_pmm_z_update_objective ρ h₂ A B c (x (k + 1)) (y k)
        (quadraticPenaltyOfLinearMap Q) (z k) zStar < ⊤ := by
    -- The primal optimum is likewise a finite test point for the `z`-subproblem objective.
    rw [ad_pmm_z_update_objective_apply, add_assoc]
    exact EReal.add_lt_top
      (mem_effective_domain.mp hzStarDom).ne
      (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne
  have hzNextObjDom :
      z (k + 1) ∈ effective_domain
        (ad_pmm_z_update_objective ρ h₂ A B c (x (k + 1)) (y k)
          (quadraticPenaltyOfLinearMap Q) (z k)) :=
    minimizer_memEffectiveDomain_of_finiteTestPoint hzStepMin hzTestFinite
  have hzNextDom : z (k + 1) ∈ effective_domain h₂ := by
    -- Peel the finite quadratic penalties back off the minimizing `z`-subproblem value.
    refine mem_effective_domain.mpr ?_
    by_contra hzTop
    have hzTopEq : h₂ (z (k + 1)) = ⊤ := le_antisymm le_top (not_lt.mp hzTop)
    have hrest_ne_bot :
        ((((ρ : ℝ) / 2) * ‖A (x (k + 1)) + B (z (k + 1)) - c + (1 / (ρ : ℝ)) • y k‖ ^ (2 : ℕ) :
            ℝ) : EReal) +
          ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (z (k + 1) - z k) : ℝ) : EReal)) ≠ ⊥ := by
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
    have hzObjTop :
        ad_pmm_z_update_objective ρ h₂ A B c (x (k + 1)) (y k)
          (quadraticPenaltyOfLinearMap Q) (z k) (z (k + 1)) = ⊤ := by
      rw [ad_pmm_z_update_objective_apply, hzTopEq, add_assoc]
      simpa using EReal.top_add_of_ne_bot hrest_ne_bot
    exact (mem_effective_domain.mp hzNextObjDom).ne hzObjTop
  -- Repackage the blockwise finiteness facts as finiteness of the ADMM objective.
  exact (mem_effectiveDomain_admmObjective_iff
    (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
    hAssump (x (k + 1)) (z (k + 1))).2 ⟨hxNextDom, hzNextDom⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: on the effective domain, the ADMM objective `H[h₁, h₂]` reduces to
the sum of the two finite block values. -/
private theorem admmObjective_toReal
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {x' : X} {z' : Z}
    (hDom : (x', z') ∈ effective_domain (H[h₁, h₂])) :
    (H[h₁, h₂] (x', z')).toReal = (h₁ x').toReal + (h₂ z').toReal := by
  have hxTop : h₁ x' ≠ ⊤ :=
    (mem_effective_domain.mp <|
      (mem_effectiveDomain_admmObjective_iff
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump x' z').1 hDom |>.1).ne
  have hzTop : h₂ z' ≠ ⊤ :=
    (mem_effective_domain.mp <|
      (mem_effectiveDomain_admmObjective_iff
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump x' z').1 hDom |>.2).ne
  -- Expand `H[h₁, h₂]` and convert the finite extended-real sum to the displayed real sum.
  rw [admm_objective_apply,
    EReal.toReal_add hxTop
      (hAssump.toIsProperExtendedRealFunction.ne_bot x')
      hzTop
      (hAssump.h₂_proper.ne_bot z')]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: on finite test points, the AD-PMM `x`-subproblem objective converts
to the displayed real-valued proximal model. -/
private theorem adPmmXUpdateObjective_toReal
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {zk : Z} {yk : Y} {xk : X} {x' : X}
    (hx : x' ∈ effective_domain h₁) :
    (ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk x').toReal =
      (h₁ x').toReal +
        ((ρ : ℝ) / 2) * ‖A x' + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (x' - xk)) := by
  have hxTop : h₁ x' ≠ ⊤ := (mem_effective_domain.mp hx).ne
  have hpenalty_ne_top :
      ((((ρ : ℝ) / 2) * ‖A x' + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (x' - xk) : ℝ) : EReal)) ≠ ⊤ := by
    exact (EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)).2
      ⟨EReal.coe_ne_top _, EReal.coe_ne_top _⟩
  have hpenalty_ne_bot :
      ((((ρ : ℝ) / 2) * ‖A x' + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (x' - xk) : ℝ) : EReal)) ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
  -- Expand the `EReal` objective once, then convert the finite penalty sum to the displayed
  -- real-valued proximal model.
  rw [ad_pmm_x_update_objective_apply, add_assoc,
    EReal.toReal_add hxTop (hAssump.toIsProperExtendedRealFunction.ne_bot x') hpenalty_ne_top
      hpenalty_ne_bot,
    EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _)]
  -- The two remaining extended-real penalty terms are coercions of real scalars.
  rw [EReal.toReal_coe, EReal.toReal_coe]
  ring

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: on finite test points, the AD-PMM `z`-subproblem objective converts
to the displayed real-valued proximal model. -/
private theorem adPmmZUpdateObjective_toReal
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {xNext : X} {yk : Y} {zk : Z} {z' : Z}
    (hz : z' ∈ effective_domain h₂) :
    (ad_pmm_z_update_objective ρ h₂ A B c xNext yk (quadraticPenaltyOfLinearMap Q) zk z').toReal =
      (h₂ z').toReal +
        ((ρ : ℝ) / 2) * ‖A xNext + B z' - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (z' - zk)) := by
  have hzTop : h₂ z' ≠ ⊤ := (mem_effective_domain.mp hz).ne
  have hpenalty_ne_top :
      ((((ρ : ℝ) / 2) * ‖A xNext + B z' - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (z' - zk) : ℝ) : EReal)) ≠ ⊤ := by
    exact (EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _) (EReal.coe_ne_bot _)).2
      ⟨EReal.coe_ne_top _, EReal.coe_ne_top _⟩
  have hpenalty_ne_bot :
      ((((ρ : ℝ) / 2) * ‖A xNext + B z' - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (z' - zk) : ℝ) : EReal)) ≠ ⊥ := by
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
  -- Expand the `EReal` objective once, then convert the finite penalty sum to the displayed
  -- real-valued proximal model.
  rw [ad_pmm_z_update_objective_apply, add_assoc,
    EReal.toReal_add hzTop (hAssump.h₂_proper.ne_bot z') hpenalty_ne_top hpenalty_ne_bot,
    EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) (EReal.coe_ne_top _)
      (EReal.coe_ne_bot _)]
  -- The two remaining extended-real penalty terms are coercions of real scalars.
  rw [EReal.toReal_coe, EReal.toReal_coe]
  ring

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: the intermediate multiplier `y^k + ρ (A x^(k+1) + B z^k - c)`
rewrites to the next multiplier plus the `B`-increment of the `z`-iterate. -/
private theorem yTilde_eq_yNext_add_rho_BStep
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    (k : ℕ) :
    y k + (ρ : ℝ) • (A (x (k + 1)) + B (z k) - c) =
      y (k + 1) + (ρ : ℝ) • B (z k - z (k + 1)) := by
  -- Rewrite the multiplier update once and collect the `B`-increment into one linear-map term.
  rw [hTrajectory.toIsADPMMTrajectory.y_step k, admm_multiplier_update_eq]
  simp [sub_eq_add_neg, smul_add, add_assoc, add_left_comm, add_comm]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: an `x`-subproblem minimizer yields the real-valued comparison of the
proximal `x`-objective against any finite test point. -/
private theorem adPmmXUpdateObjective_toReal_compare_of_isMinOn
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {zk : Z} {yk : Y} {xk : X} {xNext : X} {xTest : X}
    (hxStepMin :
      IsMinOn
        (ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk)
        Set.univ xNext)
    (hxTest : xTest ∈ effective_domain h₁) :
    (h₁ xNext).toReal +
        ((ρ : ℝ) / 2) * ‖A xNext + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (xNext - xk)) ≤
      (h₁ xTest).toReal +
        ((ρ : ℝ) / 2) * ‖A xTest + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (xTest - xk)) := by
  let objective :=
    ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk
  have hxStepMin' := hxStepMin
  rw [isMinOn_univ_iff] at hxStepMin
  have hCompare : objective xNext ≤ objective xTest := hxStepMin xTest
  have hxTestFinite : objective xTest < ⊤ := by
    -- The finite test point makes the whole `EReal` proximal objective finite.
    simpa [objective, add_assoc] using
      (show
        ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk xTest < ⊤ by
          rw [ad_pmm_x_update_objective_apply, add_assoc]
          exact EReal.add_lt_top
            (mem_effective_domain.mp hxTest).ne
            (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne)
  have hxNextObjDom :
      xNext ∈ effective_domain objective :=
    minimizer_memEffectiveDomain_of_finiteTestPoint hxStepMin' hxTestFinite
  have hxNextDom : xNext ∈ effective_domain h₁ := by
    -- Finiteness of the minimizing objective value forces finiteness of the `h₁` term.
    refine mem_effective_domain.mpr ?_
    by_contra hxTop
    have hxTopEq : h₁ xNext = ⊤ := le_antisymm le_top (not_lt.mp hxTop)
    have hrest_ne_bot :
        ((((ρ : ℝ) / 2) * ‖A xNext + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (xNext - xk) : ℝ) : EReal)) ≠ ⊥ := by
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
    have hxObjTop :
        objective xNext = ⊤ := by
      rw [show objective xNext =
        ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk xNext by
          rfl,
        ad_pmm_x_update_objective_apply, hxTopEq, add_assoc]
      simpa using EReal.top_add_of_ne_bot hrest_ne_bot
    exact (mem_effective_domain.mp hxNextObjDom).ne hxObjTop
  have hxNextObjNeBot : objective xNext ≠ ⊥ := by
    -- Properness of `h₁` and the finite quadratic penalties rule out `-∞`.
    simpa [objective, add_assoc] using
      (show
        ad_pmm_x_update_objective ρ h₁ A B c zk yk (quadraticPenaltyOfLinearMap G) xk xNext ≠ ⊥ by
          rw [ad_pmm_x_update_objective_apply, add_assoc]
          exact EReal.add_ne_bot_iff.mpr
            ⟨hAssump.toIsProperExtendedRealFunction.ne_bot _,
              EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩⟩)
  have hCompareReal :
      (objective xNext).toReal ≤ (objective xTest).toReal :=
    EReal.toReal_le_toReal hCompare hxNextObjNeBot (ne_of_lt hxTestFinite)
  have hxNextToReal :
      (objective xNext).toReal =
        (h₁ xNext).toReal +
          ((ρ : ℝ) / 2) * ‖A xNext + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
          ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (xNext - xk)) := by
    simpa [objective] using
      (adPmmXUpdateObjective_toReal
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump hxNextDom)
  have hxTestToReal :
      (objective xTest).toReal =
        (h₁ xTest).toReal +
          ((ρ : ℝ) / 2) * ‖A xTest + B zk - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
          ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (xTest - xk)) := by
    simpa [objective] using
      (adPmmXUpdateObjective_toReal
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump hxTest)
  -- Rewrite both sides to the displayed real-valued proximal-model comparison.
  rw [hxNextToReal, hxTestToReal] at hCompareReal
  exact hCompareReal

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: a `z`-subproblem minimizer yields the real-valued comparison of the
proximal `z`-objective against any finite test point. -/
private theorem adPmmZUpdateObjective_toReal_compare_of_isMinOn
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {xNext : X} {yk : Y} {zk : Z} {zNext : Z} {zTest : Z}
    (hzStepMin :
      IsMinOn
        (ad_pmm_z_update_objective ρ h₂ A B c xNext yk (quadraticPenaltyOfLinearMap Q) zk)
        Set.univ zNext)
    (hzTest : zTest ∈ effective_domain h₂) :
    (h₂ zNext).toReal +
        ((ρ : ℝ) / 2) * ‖A xNext + B zNext - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (zNext - zk)) ≤
      (h₂ zTest).toReal +
        ((ρ : ℝ) / 2) * ‖A xNext + B zTest - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
        ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (zTest - zk)) := by
  let objective :=
    ad_pmm_z_update_objective ρ h₂ A B c xNext yk (quadraticPenaltyOfLinearMap Q) zk
  have hzStepMin' := hzStepMin
  rw [isMinOn_univ_iff] at hzStepMin
  have hCompare : objective zNext ≤ objective zTest := hzStepMin zTest
  have hzTestFinite : objective zTest < ⊤ := by
      -- The finite test point makes the whole `EReal` proximal objective finite.
      simpa [objective, add_assoc] using
      (show
        ad_pmm_z_update_objective ρ h₂ A B c xNext yk
          (quadraticPenaltyOfLinearMap Q) zk zTest < ⊤ by
          rw [ad_pmm_z_update_objective_apply, add_assoc]
          exact EReal.add_lt_top
            (mem_effective_domain.mp hzTest).ne
            (EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)).ne)
  have hzNextObjDom :
      zNext ∈ effective_domain objective :=
    minimizer_memEffectiveDomain_of_finiteTestPoint hzStepMin' hzTestFinite
  have hzNextDom : zNext ∈ effective_domain h₂ := by
    -- Finiteness of the minimizing objective value forces finiteness of the `h₂` term.
    refine mem_effective_domain.mpr ?_
    by_contra hzTop
    have hzTopEq : h₂ zNext = ⊤ := le_antisymm le_top (not_lt.mp hzTop)
    have hrest_ne_bot :
        ((((ρ : ℝ) / 2) * ‖A xNext + B zNext - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ((((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (zNext - zk) : ℝ) : EReal)) ≠ ⊥ := by
      exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩
    have hzObjTop :
        objective zNext = ⊤ := by
      rw [show objective zNext =
        ad_pmm_z_update_objective ρ h₂ A B c xNext yk (quadraticPenaltyOfLinearMap Q) zk zNext by
          rfl,
        ad_pmm_z_update_objective_apply, hzTopEq, add_assoc]
      simpa using EReal.top_add_of_ne_bot hrest_ne_bot
    exact (mem_effective_domain.mp hzNextObjDom).ne hzObjTop
  have hzNextObjNeBot : objective zNext ≠ ⊥ := by
    -- Properness of `h₂` and the finite quadratic penalties rule out `-∞`.
    simpa [objective, add_assoc] using
      (show
        ad_pmm_z_update_objective ρ h₂ A B c xNext yk
          (quadraticPenaltyOfLinearMap Q) zk zNext ≠ ⊥ by
          rw [ad_pmm_z_update_objective_apply, add_assoc]
          exact EReal.add_ne_bot_iff.mpr
            ⟨hAssump.h₂_proper.ne_bot _,
              EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ne_bot _⟩⟩)
  have hCompareReal :
      (objective zNext).toReal ≤ (objective zTest).toReal :=
    EReal.toReal_le_toReal hCompare hzNextObjNeBot (ne_of_lt hzTestFinite)
  have hzNextToReal :
      (objective zNext).toReal =
        (h₂ zNext).toReal +
          ((ρ : ℝ) / 2) * ‖A xNext + B zNext - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
          ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (zNext - zk)) := by
    simpa [objective] using
      (adPmmZUpdateObjective_toReal
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump hzNextDom)
  have hzTestToReal :
      (objective zTest).toReal =
        (h₂ zTest).toReal +
          ((ρ : ℝ) / 2) * ‖A xNext + B zTest - c + (1 / (ρ : ℝ)) • yk‖ ^ (2 : ℕ) +
          ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (zTest - zk)) := by
    simpa [objective] using
      (adPmmZUpdateObjective_toReal
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump hzTest)
  -- Rewrite both sides to the displayed real-valued proximal-model comparison.
  rw [hzNextToReal, hzTestToReal] at hCompareReal
  exact hCompareReal

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: primal feasibility rewrites the two affine pairings against a common
multiplier as the negative residual pairing at the next iterate. -/
private theorem feasibleAffinePairing_eq_negResidualPairing
    {xStar : X} {xNext : X} {zStar : Z} {zNext : Z} {yTilde : Y}
    (hFeasible : A xStar + B zStar = c) :
    inner ℝ (A xStar - A xNext) yTilde + inner ℝ (B zStar - B zNext) yTilde =
      -inner ℝ (A xNext + B zNext - c) yTilde := by
  have hSum :
      (A xStar - A xNext) + (B zStar - B zNext) =
        -(A xNext + B zNext - c) := by
    calc
      (A xStar - A xNext) + (B zStar - B zNext)
          = (A xStar + B zStar) - (A xNext + B zNext) := by
              abel
      _ = c - (A xNext + B zNext) := by rw [hFeasible]
      _ = -(A xNext + B zNext - c) := by
            abel
  -- Combine the two affine terms before inserting feasibility.
  calc
    inner ℝ (A xStar - A xNext) yTilde + inner ℝ (B zStar - B zNext) yTilde =
      inner ℝ ((A xStar - A xNext) + (B zStar - B zNext)) yTilde := by
        rw [← inner_add_left]
    _ = inner ℝ (-(A xNext + B zNext - c)) yTilde := by rw [hSum]
    _ = -inner ℝ (A xNext + B zNext - c) yTilde := by rw [inner_neg_left]

/-- Helper for Theorem 15.2: scaling a shifted affine term by `ρ` removes the explicit
`ρ⁻¹` factor from the multiplier component. -/
private theorem rhoSmul_add_invSmul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : PosReal) (a b : E) :
    (ρ : ℝ) • (a + (1 / (ρ : ℝ)) • b) = b + (ρ : ℝ) • a := by
  have hρ : (ρ : ℝ) ≠ 0 := ne_of_gt ρ.2
  have hOne : (ρ : ℝ) * (1 / (ρ : ℝ)) = 1 := by
    field_simp [hρ]
  -- Expand the scalar action once and cancel the inverse factor from the multiplier term.
  rw [smul_add, smul_smul, hOne, one_smul, add_comm]

/-- Helper for Theorem 15.2: the `Q`-term in the one-block smooth model has gradient
`P (u - u0)` after the factor `1 / 2` cancels the symmetric two-point derivative. -/
private theorem oneBlockQuadraticPenaltyHasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : E →ₗ[ℝ] E) (u0 u : E) (hP : P.IsPositive) :
    HasGradientAt
      (fun v : E ↦ (1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (v - u0))
      (P (u - u0)) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hShift : HasFDerivAt (fun v : E ↦ v - u0) (1 : E →L[ℝ] E) u := by
    -- The anchor shift contributes the identity derivative.
    simpa using (ContinuousLinearMap.id ℝ E).hasFDerivAt.sub_const u0
  have hInner :=
    hShift.inner ℝ ((LinearMap.toContinuousLinearMap P).hasFDerivAt.comp u hShift)
  -- Rewrite the quadratic penalty to its inner-product form before simplifying the derivative.
  change HasFDerivAt
    (fun v : E ↦ (1 / 2 : ℝ) * inner ℝ (v - u0) (P (v - u0)))
    ((toDual ℝ E) (P (u - u0))) u
  convert hInner.const_smul (1 / 2 : ℝ) using 1
  ext w
  simp only [map_sub, ContinuousLinearMap.coe_sub', Pi.sub_apply,
    InnerProductSpace.toDual_apply_apply, one_div, LinearMap.coe_toContinuousLinearMap',
    Function.comp_apply, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp',
    Pi.smul_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.one_apply,
    fderivInnerCLM_apply, smul_eq_mul]
  have hsym : P.IsSymmetric := hP.isSymmetric
  have hu : inner ℝ u (P w) = inner ℝ w (P u) := by
    calc
      inner ℝ u (P w) = inner ℝ (P w) u := by rw [real_inner_comm]
      _ = inner ℝ w (P u) := hsym w u
  have hu0 : inner ℝ u0 (P w) = inner ℝ w (P u0) := by
    calc
      inner ℝ u0 (P w) = inner ℝ (P w) u0 := by rw [real_inner_comm]
      _ = inner ℝ w (P u0) := hsym w u0
  have hpair : inner ℝ (u - u0) (P w) = inner ℝ w (P u - P u0) := by
    rw [inner_sub_left, hu, hu0, inner_sub_right]
  have hPu : inner ℝ (P u) w = inner ℝ w (P u) := by rw [real_inner_comm]
  have hPu0 : inner ℝ (P u0) w = inner ℝ w (P u0) := by rw [real_inner_comm]
  have hleft : inner ℝ (P u) w - inner ℝ (P u0) w = inner ℝ w (P u - P u0) := by
    calc
      inner ℝ (P u) w - inner ℝ (P u0) w = inner ℝ w (P u) - inner ℝ w (P u0) := by
        rw [hPu, hPu0]
      _ = inner ℝ w (P u - P u0) := by rw [inner_sub_right]
  rw [hleft, hpair]
  ring_nf

/-- Helper for Theorem 15.2: the smooth one-block proximal model has gradient equal to the sum of
the affine least-squares gradient and the anchored quadratic-penalty gradient. -/
private theorem oneBlockSmoothHasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : PosReal) (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (u0 : E) (d : F)
    (hP : P.IsPositive) (u : E) :
    HasGradientAt
      (fun v : E ↦
        ((ρ : ℝ) / 2) * ‖L v + d‖ ^ (2 : ℕ) +
          ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (v - u0)))
      (LinearMap.adjoint L ((ρ : ℝ) • (L u + d)) + P (u - u0)) u := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hAffine : HasFDerivAt (fun v : E ↦ L v + d) (LinearMap.toContinuousLinearMap L) u := by
    -- The affine least-squares term differentiates through the linear map `L`.
    simpa using (LinearMap.toContinuousLinearMap L).hasFDerivAt.add_const d
  have hNorm :
      HasFDerivAt
        (fun v : E ↦ ((ρ : ℝ) / 2) * ‖L v + d‖ ^ (2 : ℕ))
        ((toDual ℝ E) (LinearMap.adjoint L ((ρ : ℝ) • (L u + d)))) u := by
    -- Normalize the norm-square derivative to the adjoint-based source formula.
    convert (hAffine.norm_sq).const_smul ((ρ : ℝ) / 2) using 1
    ext w
    simp [ContinuousLinearMap.innerSL_apply_comp, LinearMap.adjoint_eq_toCLM_adjoint, two_smul]
    ring_nf
  have hPenalty :
      HasFDerivAt
        (fun v : E ↦ (1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (v - u0))
        ((toDual ℝ E) (P (u - u0))) u :=
    (oneBlockQuadraticPenaltyHasGradientAt P u0 u hP).hasFDerivAt
  -- Add the two explicit Fréchet derivatives and repackage them as the displayed gradient.
  simpa using hNorm.add hPenalty

/-- Helper for Theorem 15.2: coercing the smooth one-block real model to `EReal` yields an
everywhere-finite objective. -/
private theorem oneBlockSmoothToEReal_finiteDomain_univ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (ρ : PosReal) (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (u0 : E) (d : F) :
    finite_domain
        (Function.toEReal (fun v : E ↦
          ((ρ : ℝ) / 2) * ‖L v + d‖ ^ (2 : ℕ) +
            ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (v - u0)))) = Set.univ := by
  let smooth : E → ℝ := fun v ↦
    ((ρ : ℝ) / 2) * ‖L v + d‖ ^ (2 : ℕ) +
      ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (v - u0))
  -- Route correction: expose the smooth-term finite-domain normalization once instead of asking
  -- the stationary-point theorem to discover it through a large `simpa`.
  apply Set.ext
  intro v
  constructor
  · intro hv
    simp
  · intro _
    change v ∈ finite_domain (Function.toEReal smooth)
    refine ⟨?_, ?_⟩
    · change (((smooth v : ℝ) : EReal)) < ⊤
      exact EReal.coe_lt_top (smooth v)
    · change (((smooth v : ℝ) : EReal)) ≠ ⊥
      exact EReal.coe_ne_bot _

/-- Helper for Theorem 15.2: a negative Riesz-represented subgradient gives the displayed real
first-order comparison inequality. -/
private theorem negToDualSubgradientComparison
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {h : E → EReal} (hProper : IsProperExtendedRealFunction h)
    {u v g : E}
    (hsub : (-toDual ℝ E g : Module.Dual ℝ E) ∈ subdifferential h u)
    (hu : u ∈ effective_domain h) (hv : v ∈ effective_domain h) :
    (h v).toReal - (h u).toReal + inner ℝ (v - u) g ≥ 0 := by
  -- Read the owner subgradient inequality in `ℝ` and then normalize the negative Riesz
  -- functional evaluation into the displayed inner-product term.
  have hEval :
      (-toDual ℝ E g : Module.Dual ℝ E) (v - u) ≤ (h v).toReal - (h u).toReal :=
    subgradient_eval_le_toReal_sub h u v (fun z _ ↦ hProper.ne_bot z) hu hv hsub
  have hEval' :
      -inner ℝ (v - u) g ≤ (h v).toReal - (h u).toReal := by
    simpa [LinearMap.neg_apply, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      real_inner_comm] using hEval
  linarith

/-- Helper for Theorem 15.2: the one-block smooth gradient pairing splits into the displayed
least-squares and proximal contributions. -/
private theorem oneBlockGradientPairing_eq_displayed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : PosReal) (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (u0 : E) (d : F)
    (uNext uTest : E) :
    inner ℝ (uTest - uNext)
        (LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d)) + P (uNext - u0)) =
      inner ℝ (L uTest - L uNext) ((ρ : ℝ) • (L uNext + d)) +
        inner ℝ (uTest - uNext) (P (uNext - u0)) := by
  -- Move the adjoint across the inner product once, then rewrite the linear image of the
  -- difference as the displayed block residual.
  rw [inner_add_right]
  have hAdj :
      inner ℝ (uTest - uNext) (LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d))) =
        inner ℝ (L (uTest - uNext)) ((ρ : ℝ) • (L uNext + d)) := by
    simpa [real_inner_comm] using
      (LinearMap.adjoint_inner_left L (uTest - uNext) ((ρ : ℝ) • (L uNext + d)))
  rw [hAdj]
  simp [map_sub]

/-- Helper for Theorem 15.2: a global minimizer of the one-block proximal model satisfies the
first-order comparison inequality against every finite test point of the nonsmooth term. -/
-- Internal helper for the ergodic AD-PMM proof; this is not the label-associated public theorem.
private theorem oneBlockProximalFirstOrderComparisonAtTestPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (ρ : PosReal) {h : E → EReal}
    (hProper : IsProperExtendedRealFunction h) (hConvex : is_convex_function h)
    (L : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] E) (u0 : E) (d : F) (hP : P.IsPositive)
    {uNext uTest : E}
    (hMin :
      IsMinOn
        (fun u ↦
          h u +
            (((((ρ : ℝ) / 2) * ‖L u + d‖ ^ (2 : ℕ)) +
                ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (u - u0)) : ℝ) : EReal))
        Set.univ uNext)
    (huTest : uTest ∈ effective_domain h) :
    (h uTest).toReal - (h uNext).toReal +
      inner ℝ (L uTest - L uNext) ((ρ : ℝ) • (L uNext + d)) +
      inner ℝ (uTest - uNext) (P (uNext - u0)) ≥ 0 := by
  let smooth : E → ℝ := fun u ↦
    ((ρ : ℝ) / 2) * ‖L u + d‖ ^ (2 : ℕ) +
      ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap P (u - u0))
  let smoothEReal : E → EReal := Function.toEReal smooth
  let objective : E → EReal := fun u ↦ h u + smoothEReal u
  have hMin' : IsMinOn objective Set.univ uNext := by
    -- Freeze the smooth term in one spelling before passing to the stationary-point theorem.
    simpa [objective, smoothEReal, smooth, Function.toEReal] using hMin
  have hsmoothTestNeTop : smoothEReal uTest ≠ ⊤ := by
    -- The smooth real-valued term is always finite after coercion to `EReal`.
    change (((smooth uTest : ℝ) : EReal)) ≠ ⊤
    exact EReal.coe_ne_top _
  have huTestFinite : objective uTest < ⊤ := by
    -- The finite comparison point for `h` keeps the whole one-block objective finite.
    exact EReal.add_lt_top (mem_effective_domain.mp huTest).ne hsmoothTestNeTop
  have huNextObjDom : uNext ∈ effective_domain objective :=
    minimizer_memEffectiveDomain_of_finiteTestPoint hMin' huTestFinite
  have huNext : uNext ∈ effective_domain h := by
    -- Finiteness of the minimizing objective value forces finiteness of the nonsmooth term.
    refine mem_effective_domain.mpr ?_
    by_contra huNextTop
    have huNextTopEq : h uNext = ⊤ := le_antisymm le_top (not_lt.mp huNextTop)
    have hsmoothNeBot : smoothEReal uNext ≠ ⊥ := by
      change (((smooth uNext : ℝ) : EReal)) ≠ ⊥
      exact EReal.coe_ne_bot _
    have hObjectiveTop : objective uNext = ⊤ := by
      change h uNext + smoothEReal uNext = ⊤
      rw [huNextTopEq]
      simpa using EReal.top_add_of_ne_bot hsmoothNeBot
    exact (mem_effective_domain.mp huNextObjDom).ne hObjectiveTop
  have hsmoothFinite :
      finite_domain smoothEReal = Set.univ :=
    oneBlockSmoothToEReal_finiteDomain_univ ρ L P u0 d
  have hdom : effective_domain h ⊆ interior (finite_domain smoothEReal) := by
    -- The smooth real-valued term is finite everywhere, so the qualification is automatic.
    intro u hu
    rw [hsmoothFinite]
    simp
  have hdiff : is_differentiable_at smoothEReal uNext := by
    -- Combine the everywhere-finite domain with the explicit smooth gradient formula.
    refine ⟨?_, ?_⟩
    · rw [hsmoothFinite]
      simp
    · simpa [smoothEReal, smooth, Function.toEReal] using
        (oneBlockSmoothHasGradientAt ρ L P u0 d hP uNext).differentiableAt
  have hMinSmoothFirst : IsMinOn (fun x ↦ smoothEReal x + h x) Set.univ uNext := by
    -- The stationary-point theorem expects the smooth term first in the composite objective.
    simpa [objective, add_comm] using hMin'
  have hLocal : IsLocalMin (fun x ↦ smoothEReal x + h x) uNext :=
    hMinSmoothFirst.isLocalMin (by simp)
  have hStationary :
      is_stationary_point smoothEReal h uNext :=
    is_stationary_point_of_isLocalMin
      (hfproper := Function.toEReal_isProper smooth)
      (hgproper := hProper)
      (hgconvex := hConvex)
      (hdom := hdom)
      (hxStar := huNext)
      (hdiff := hdiff)
      (hlocal := hLocal)
  have hGrad :
      ∇ (fun y ↦ (smoothEReal y).toReal) uNext =
        LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d)) + P (uNext - u0) := by
    -- Identify the abstract gradient from stationarity with the explicit one-block formula.
    simpa [smoothEReal, smooth, Function.toEReal] using
      (oneBlockSmoothHasGradientAt ρ L P u0 d hP uNext).gradient
  have hSub :
      (-toDual ℝ E
          (LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d)) + P (uNext - u0)) :
        Module.Dual ℝ E) ∈ subdifferential h uNext := by
    -- Route correction: read stationarity as subgradient membership before converting it to the
    -- displayed real inequality.
    rw [is_stationary_point_iff] at hStationary
    simpa [hGrad] using hStationary.2
  have hComparison :
      (h uTest).toReal - (h uNext).toReal +
          inner ℝ (uTest - uNext)
            (LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d)) + P (uNext - u0)) ≥
        0 :=
    negToDualSubgradientComparison hProper hSub huNext huTest
  -- Rewrite the single gradient pairing into the displayed `L uTest - L uNext` and proximal
  -- block terms.
  calc
    (h uTest).toReal - (h uNext).toReal +
        inner ℝ (L uTest - L uNext) ((ρ : ℝ) • (L uNext + d)) +
        inner ℝ (uTest - uNext) (P (uNext - u0)) =
      (h uTest).toReal - (h uNext).toReal +
        inner ℝ (uTest - uNext)
          (LinearMap.adjoint L ((ρ : ℝ) • (L uNext + d)) + P (uNext - u0)) := by
            simpa [add_assoc] using
              congrArg
                (fun t ↦ (h uTest).toReal - (h uNext).toReal + t)
                (oneBlockGradientPairing_eq_displayed ρ L P u0 d uNext uTest).symm
    _ ≥ 0 := hComparison

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: the natural `z`-step pairing with `B z^(k+1)` splits into the
displayed `B z^k` pairing plus the explicit `B`-increment remainder. -/
private theorem zUpdateNaturalPairing_eq_displayedSplit
    {xNext : X} {yk : Y} {zk zNext zTest : Z} :
    inner ℝ (B zTest - B zNext) (yk + (ρ : ℝ) • (A xNext + B zNext - c)) =
      inner ℝ (B zTest - B zNext) (yk + (ρ : ℝ) • (A xNext + B zk - c)) +
        (ρ : ℝ) * inner ℝ (B (zTest - zNext)) (B (zNext - zk)) := by
  -- Rewrite the natural pairing once and isolate the `B`-increment as a separate correction term.
  calc
    inner ℝ (B zTest - B zNext) (yk + (ρ : ℝ) • (A xNext + B zNext - c)) =
      inner ℝ (B zTest - B zNext)
        (yk + (ρ : ℝ) • (A xNext + B zk - c) + (ρ : ℝ) • B (zNext - zk)) := by
          congr 1
          simp [smul_add, sub_eq_add_neg]
          abel_nf
    _ =
      inner ℝ (B zTest - B zNext) (yk + (ρ : ℝ) • (A xNext + B zk - c)) +
        inner ℝ (B zTest - B zNext) ((ρ : ℝ) • B (zNext - zk)) := by
          rw [inner_add_right]
    _ =
      inner ℝ (B zTest - B zNext) (yk + (ρ : ℝ) • (A xNext + B zk - c)) +
        (ρ : ℝ) * inner ℝ (B (zTest - zNext)) (B (zNext - zk)) := by
          simp [map_sub, real_inner_smul_right]

omit [FiniteDimensional ℝ Z] in
/-- Helper for Theorem 15.2: the AD-PMM `x`-update minimizes the displayed real-valued proximal
model against any finite comparison point. -/
private theorem xUpdateLinearComparisonAtTestPoint
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    (k : ℕ) {xTest : X}
    (hxTest : xTest ∈ effective_domain h₁) :
    (h₁ xTest).toReal - (h₁ (x (k + 1))).toReal +
      inner ℝ (A xTest - A (x (k + 1)))
        (y k + (ρ : ℝ) • (A (x (k + 1)) + B (z k) - c)) +
      inner ℝ (xTest - x (k + 1)) (G (x (k + 1) - x k)) ≥ 0 := by
  let xNext := x (k + 1)
  have hTrajectory' := hTrajectory.toIsADPMMTrajectory
  have hxStepMin :
      IsMinOn
        (ad_pmm_x_update_objective ρ h₁ A B c (z k) (y k)
          (quadraticPenaltyOfLinearMap G) (x k))
        Set.univ
        xNext := by
    -- Read the `x`-update directly from the minimizing clause in Algorithm 15.4.
    exact (mem_ad_pmm_x_update_argmin_iff).1 (hTrajectory'.x_step k)
  have hxStepMinModel :
      IsMinOn
        (fun u ↦
          h₁ u +
            (((((ρ : ℝ) / 2) * ‖A u + (B (z k) - c + (1 / (ρ : ℝ)) • y k)‖ ^ (2 : ℕ)) +
                ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap G (u - x k)) : ℝ) : EReal))
        Set.univ xNext := by
    rw [isMinOn_univ_iff] at hxStepMin ⊢
    intro u
    simpa [ad_pmm_x_update_objective_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hxStepMin u
  have hCompare :=
    oneBlockProximalFirstOrderComparisonAtTestPoint
      ρ hAssump.toIsProperExtendedRealFunction hAssump.h₁_convex
      A G (x k) (B (z k) - c + (1 / (ρ : ℝ)) • y k) hAssump.G_positive
      hxStepMinModel hxTest
  have hCompare' :
      (h₁ xTest).toReal - (h₁ xNext).toReal +
        inner ℝ (A xTest - A xNext)
          ((ρ : ℝ) • (A xNext + (B (z k) - c + (1 / (ρ : ℝ)) • y k))) +
        inner ℝ (xTest - xNext) (G (xNext - x k)) ≥ 0 := by
    simpa [xNext] using hCompare
  have hScale :
      (ρ : ℝ) • (A xNext + (B (z k) - c + (1 / (ρ : ℝ)) • y k)) =
        y k + (ρ : ℝ) • (A xNext + B (z k) - c) := by
    calc
      (ρ : ℝ) • (A xNext + (B (z k) - c + (1 / (ρ : ℝ)) • y k)) =
          (ρ : ℝ) • ((A xNext + B (z k) - c) + (1 / (ρ : ℝ)) • y k) := by
            abel
      _ = y k + (ρ : ℝ) • (A xNext + B (z k) - c) :=
          rhoSmul_add_invSmul_eq ρ (A xNext + B (z k) - c) (y k)
  -- Route correction: specialize the generic first-order one-block comparison to the `x`-update
  -- and normalize the scaled residual once at the end.
  calc
    (h₁ xTest).toReal - (h₁ xNext).toReal +
        inner ℝ (A xTest - A xNext) (y k + (ρ : ℝ) • (A xNext + B (z k) - c)) +
        inner ℝ (xTest - xNext) (G (xNext - x k)) =
      (h₁ xTest).toReal - (h₁ xNext).toReal +
        inner ℝ (A xTest - A xNext)
          ((ρ : ℝ) • (A xNext + (B (z k) - c + (1 / (ρ : ℝ)) • y k))) +
        inner ℝ (xTest - xNext) (G (xNext - x k)) := by rw [hScale]
    _ ≥ 0 := hCompare'

omit [FiniteDimensional ℝ X] in
/-- Helper for Theorem 15.2: the AD-PMM `z`-update minimizes the displayed real-valued proximal
model against any finite comparison point. -/
private theorem zUpdateLinearComparisonAtTestPoint
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    (k : ℕ) {zTest : Z}
    (hzTest : zTest ∈ effective_domain h₂) :
    (h₂ zTest).toReal - (h₂ (z (k + 1))).toReal +
      inner ℝ (B zTest - B (z (k + 1)))
        (y k + (ρ : ℝ) • (A (x (k + 1)) + B (z k) - c)) +
      (ρ : ℝ) * inner ℝ (B (zTest - z (k + 1))) (B (z (k + 1) - z k)) +
      inner ℝ (zTest - z (k + 1)) (Q (z (k + 1) - z k)) ≥ 0 := by
  let xNext := x (k + 1)
  let zNext := z (k + 1)
  have hTrajectory' := hTrajectory.toIsADPMMTrajectory
  have hzStepMin :
      IsMinOn
        (ad_pmm_z_update_objective ρ h₂ A B c xNext (y k)
          (quadraticPenaltyOfLinearMap Q) (z k))
        Set.univ
        zNext := by
    -- Read the `z`-update as the minimizing clause from Algorithm 15.4.
    exact (mem_ad_pmm_z_update_argmin_iff).1 (hTrajectory'.z_step k)
  have hzStepMinModel :
      IsMinOn
        (fun u ↦
          h₂ u +
            (((((ρ : ℝ) / 2) * ‖B u + (A xNext - c + (1 / (ρ : ℝ)) • y k)‖ ^ (2 : ℕ)) +
                ((1 / 2 : ℝ) * quadraticPenaltyOfLinearMap Q (u - z k)) : ℝ) : EReal))
        Set.univ zNext := by
    rw [isMinOn_univ_iff] at hzStepMin ⊢
    intro u
    simpa only [ad_pmm_z_update_objective_apply, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]
      using hzStepMin u
  have hCompare :=
    oneBlockProximalFirstOrderComparisonAtTestPoint
      ρ hAssump.h₂_proper hAssump.h₂_convex
      B Q (z k) (A xNext - c + (1 / (ρ : ℝ)) • y k) hAssump.Q_positive
      hzStepMinModel hzTest
  have hCompare' :
      (h₂ zTest).toReal - (h₂ zNext).toReal +
        inner ℝ (B zTest - B zNext)
          ((ρ : ℝ) • (B zNext + (A xNext - c + (1 / (ρ : ℝ)) • y k))) +
        inner ℝ (zTest - zNext) (Q (zNext - z k)) ≥ 0 := by
    simpa only [xNext, zNext] using hCompare
  have hScale :
      (ρ : ℝ) • (B zNext + (A xNext - c + (1 / (ρ : ℝ)) • y k)) =
        y k + (ρ : ℝ) • (A xNext + B zNext - c) := by
    calc
      (ρ : ℝ) • (B zNext + (A xNext - c + (1 / (ρ : ℝ)) • y k)) =
          (ρ : ℝ) • ((B zNext + (A xNext - c)) + (1 / (ρ : ℝ)) • y k) := by
            abel
      _ = y k + (ρ : ℝ) • (B zNext + (A xNext - c)) :=
          rhoSmul_add_invSmul_eq ρ (B zNext + (A xNext - c)) (y k)
      _ = y k + (ρ : ℝ) • (A xNext + B zNext - c) := by
          congr 1
          abel
  have hSplit :
      inner ℝ (B zTest - B zNext)
          ((ρ : ℝ) • (B zNext + (A xNext - c + (1 / (ρ : ℝ)) • y k))) =
        inner ℝ (B zTest - B zNext) (y k + (ρ : ℝ) • (A xNext + B (z k) - c)) +
          (ρ : ℝ) * inner ℝ (B (zTest - zNext)) (B (zNext - z k)) := by
    rw [hScale]
    exact zUpdateNaturalPairing_eq_displayedSplit (ρ := ρ) (A := A) (B := B) (c := c)
  -- Route correction: specialize the generic one-block first-order comparison and then rewrite the
  -- natural `B z^(k+1)` pairing to the displayed `B z^k` split form once.
  calc
    (h₂ zTest).toReal - (h₂ zNext).toReal +
        inner ℝ (B zTest - B zNext) (y k + (ρ : ℝ) • (A xNext + B (z k) - c)) +
        (ρ : ℝ) * inner ℝ (B (zTest - zNext)) (B (zNext - z k)) +
        inner ℝ (zTest - zNext) (Q (zNext - z k)) =
      (h₂ zTest).toReal - (h₂ zNext).toReal +
        inner ℝ (B zTest - B zNext)
          ((ρ : ℝ) • (B zNext + (A xNext - c + (1 / (ρ : ℝ)) • y k))) +
        inner ℝ (zTest - zNext) (Q (zNext - z k)) := by
          rw [hSplit]
          abel
    _ ≥ 0 := hCompare'

/-- Helper for Theorem 15.2: one AD-PMM step decreases the standard energy by at least the
current primal gap plus an arbitrary multiplier pairing with the feasibility residual. -/
private theorem oneStepGapResidual_le_energyDrop
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    (k : ℕ) (yBar : Y) :
    ((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
        (H[h₁, h₂] (xStar, zStar)).toReal) +
      inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c) ≤
        ((quadraticPenaltyOfLinearMap G (xStar - x k) +
              ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) +
                quadraticPenaltyOfLinearMap Q (zStar - z k)) +
              (1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ)) -
            (quadraticPenaltyOfLinearMap G (xStar - x (k + 1)) +
              ((ρ : ℝ) * ‖B (zStar - z (k + 1))‖ ^ (2 : ℕ) +
                quadraticPenaltyOfLinearMap Q (zStar - z (k + 1))) +
              (1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2 := by
  let xNext := x (k + 1)
  let zNext := z (k + 1)
  let yTilde : Y := y k + (ρ : ℝ) • (A xNext + B (z k) - c)
  let residual : Y := A xNext + B zNext - c
  have hTrajectory' := hTrajectory.toIsADPMMTrajectory
  have hρ : (ρ : ℝ) ≠ 0 := by
    exact ne_of_gt ρ.2
  have hStarDom :
      (xStar, zStar) ∈ effective_domain (H[h₁, h₂]) :=
    primalOptimal_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump hPrimalOpt
  have hNextDom :
      (xNext, zNext) ∈ effective_domain (H[h₁, h₂]) :=
    sampledIterate_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt k
  have hxStarDom : xStar ∈ effective_domain h₁ :=
    (mem_effectiveDomain_admmObjective_iff
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump xStar zStar).1 hStarDom |>.1
  have hzStarDom : zStar ∈ effective_domain h₂ :=
    (mem_effectiveDomain_admmObjective_iff
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump xStar zStar).1 hStarDom |>.2
  have hObjectiveStar :
      (H[h₁, h₂] (xStar, zStar)).toReal = (h₁ xStar).toReal + (h₂ zStar).toReal :=
    admmObjective_toReal
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump hStarDom
  have hObjectiveNext :
      (H[h₁, h₂] (xNext, zNext)).toReal = (h₁ xNext).toReal + (h₂ zNext).toReal :=
    admmObjective_toReal
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump hNextDom
  have hFeasible : A xStar + B zStar = c := by
    simpa [mem_admm_feasible_set] using hPrimalOpt.feasible
  have hxComp :
      (h₁ xStar).toReal - (h₁ xNext).toReal +
        inner ℝ (A xStar - A xNext) yTilde +
        inner ℝ (xStar - xNext) (G (xNext - x k)) ≥ 0 :=
    xUpdateLinearComparisonAtTestPoint
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory k hxStarDom
  have hzComp :
      (h₂ zStar).toReal - (h₂ zNext).toReal +
        inner ℝ (B zStar - B zNext) yTilde +
        (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) +
        inner ℝ (zStar - zNext) (Q (zNext - z k)) ≥ 0 :=
    zUpdateLinearComparisonAtTestPoint
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory k hzStarDom
  have hAffine :
      inner ℝ (A xStar - A xNext) yTilde + inner ℝ (B zStar - B zNext) yTilde =
        -inner ℝ residual yTilde :=
    feasibleAffinePairing_eq_negResidualPairing
      (A := A) (B := B) (c := c) (xStar := xStar) (xNext := xNext)
      (zStar := zStar) (zNext := zNext) (yTilde := yTilde) hFeasible
  have hBlockGap :
      ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ residual yTilde ≤
        inner ℝ (xStar - xNext) (G (xNext - x k)) +
          (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) +
          inner ℝ (zStar - zNext) (Q (zNext - z k)) := by
    -- Assemble the two blockwise comparison inequalities.
    -- Then rewrite the affine part by feasibility.
    have hCombined :
        0 ≤
          ((H[h₁, h₂] (xStar, zStar)).toReal - (H[h₁, h₂] (xNext, zNext)).toReal) +
            (inner ℝ (A xStar - A xNext) yTilde +
              inner ℝ (B zStar - B zNext) yTilde) +
            (inner ℝ (xStar - xNext) (G (xNext - x k)) +
              ((ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) +
                inner ℝ (zStar - zNext) (Q (zNext - z k)))) := by
      linarith [hxComp, hzComp, hObjectiveStar, hObjectiveNext]
    rw [hAffine] at hCombined
    linarith
  have hyTilde :
      yTilde = y (k + 1) + (ρ : ℝ) • B (z k - zNext) := by
    simpa [xNext, zNext, yTilde] using
      yTilde_eq_yNext_add_rho_BStep
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
        (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
        hTrajectory k
  have hMultiplierCore :=
    multiplierShift_threePoint ρ yBar yTilde (y k) (y (k + 1)) (B (z k - zNext)) hyTilde
  have hMultiplierLink :
      (1 / (ρ : ℝ)) * inner ℝ (yBar - yTilde) (y k - y (k + 1)) =
        -inner ℝ residual (yBar - yTilde) := by
    have hyStepEq : y (k + 1) = y k + (ρ : ℝ) • residual := by
      simpa [xNext, zNext, residual, smul_add, add_left_comm, add_comm] using
        (show y (k + 1) = admm_multiplier_update ρ A B c (y k) xNext zNext from
          by simpa [xNext, zNext] using hTrajectory'.y_step k)
    have hyStep :
        y k - y (k + 1) = -(ρ : ℝ) • residual := by
      rw [hyStepEq]
      simp [sub_eq_add_neg]
    calc
      (1 / (ρ : ℝ)) * inner ℝ (yBar - yTilde) (y k - y (k + 1)) =
        (1 / (ρ : ℝ)) * ((-(ρ : ℝ)) * inner ℝ (yBar - yTilde) residual) := by
          rw [hyStep, real_inner_smul_right]
      _ = -(inner ℝ (yBar - yTilde) residual) := by
          field_simp [hρ]
      _ = -inner ℝ residual (yBar - yTilde) := by rw [real_inner_comm]
  have hMultiplierUpper :
      inner ℝ residual (yBar - yTilde) ≤
        (((1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ)) -
            ((1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2 +
          ((ρ : ℝ) / 2) * ‖B (z k - zNext)‖ ^ (2 : ℕ) := by
    have hMultiplierCore' :
        -inner ℝ residual (yBar - yTilde) ≥
          (‖yBar - y (k + 1)‖ ^ (2 : ℕ) - ‖yBar - y k‖ ^ (2 : ℕ)) / (2 * (ρ : ℝ)) -
            ((ρ : ℝ) / 2) * ‖B (z k - zNext)‖ ^ (2 : ℕ) := by
      rw [← hMultiplierLink]
      exact hMultiplierCore
    have hMultiplierCore'' :
        -inner ℝ residual (yBar - yTilde) ≥
          -((((1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ) -
                ((1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2) +
              ((ρ : ℝ) / 2) * ‖B (z k - zNext)‖ ^ (2 : ℕ)) := by
      convert hMultiplierCore' using 1
      field_simp [hρ]
      ring
    linarith
  have hGterm :
      inner ℝ (xStar - xNext) (G (xNext - x k)) ≤
        (quadraticPenaltyOfLinearMap G (xStar - x k) -
          quadraticPenaltyOfLinearMap G (xStar - xNext)) / 2 := by
    have hThreePoint :=
      positiveLinearPenalty_threePoint G hAssump.G_positive xStar xNext (x k)
    have hStepNonneg : 0 ≤ quadraticPenaltyOfLinearMap G (xNext - x k) := by
      simpa [quadraticPenaltyOfLinearMap_apply] using
        hAssump.G_positive.inner_nonneg_right (xNext - x k)
    -- Use the exact three-point identity and drop the nonnegative step term.
    linarith
  have hBterm :
      (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) ≤
        ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) -
            (ρ : ℝ) * ‖B (zStar - zNext)‖ ^ (2 : ℕ)) / 2 -
          ((ρ : ℝ) / 2) * ‖B (zNext - z k)‖ ^ (2 : ℕ) := by
    have hThreePoint :=
      positiveLinearPenalty_threePoint
        (P := (LinearMap.id : Y →ₗ[ℝ] Y))
        LinearMap.isPositive_id
        (B zStar) (B zNext) (B (z k))
    have hThreePoint' :
        ‖B (zStar - z k)‖ ^ (2 : ℕ) - ‖B (zNext - z k)‖ ^ (2 : ℕ) =
          ‖B (zStar - zNext)‖ ^ (2 : ℕ) +
            2 * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) := by
      simpa [quadraticPenaltyOfLinearMap_apply, map_sub] using hThreePoint
    have hBIdentity :
        ‖B (zStar - z k)‖ ^ (2 : ℕ) - ‖B (zStar - zNext)‖ ^ (2 : ℕ) =
          ‖B (zNext - z k)‖ ^ (2 : ℕ) +
            2 * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) := by
      linarith
    have hBtermEq :
        ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) -
            (ρ : ℝ) * ‖B (zStar - zNext)‖ ^ (2 : ℕ)) / 2 -
          ((ρ : ℝ) / 2) * ‖B (zNext - z k)‖ ^ (2 : ℕ) =
        (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) := by
      -- Scale the three-point identity once.
      -- Then rearrange it into the downstream half-factor form.
      have hScaled := congrArg (fun t : ℝ ↦ ((ρ : ℝ) / 2) * t) hBIdentity
      linarith
    exact le_of_eq hBtermEq.symm
  have hQterm :
      inner ℝ (zStar - zNext) (Q (zNext - z k)) ≤
        (quadraticPenaltyOfLinearMap Q (zStar - z k) -
          quadraticPenaltyOfLinearMap Q (zStar - zNext)) / 2 := by
    have hThreePoint :=
      positiveLinearPenalty_threePoint Q hAssump.Q_positive zStar zNext (z k)
    have hStepNonneg : 0 ≤ quadraticPenaltyOfLinearMap Q (zNext - z k) := by
      simpa [quadraticPenaltyOfLinearMap_apply] using
        hAssump.Q_positive.inner_nonneg_right (zNext - z k)
    -- Use the exact three-point identity and drop the nonnegative step term.
    linarith
  have hTargetRewrite :
      ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar residual =
        ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ residual yTilde +
          inner ℝ residual (yBar - yTilde) := by
    calc
      ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar residual =
        ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ residual yBar := by
            rw [real_inner_comm]
      _ =
        ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          (inner ℝ residual yTilde + inner ℝ residual (yBar - yTilde)) := by
            congr 1
            rw [← inner_add_right]
            abel_nf
      _ =
        ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ residual yTilde +
          inner ℝ residual (yBar - yTilde) := by
            ring
  -- Route correction: rewrite the affine term first, then bound the multiplier, `G`, `B`, and
  -- `Q` contributions separately before the final scalar assembly.
  have hFinal :
      ((H[h₁, h₂] (xNext, zNext)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar residual ≤
        ((quadraticPenaltyOfLinearMap G (xStar - x k) +
              ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) +
                quadraticPenaltyOfLinearMap Q (zStar - z k)) +
              (1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ)) -
            (quadraticPenaltyOfLinearMap G (xStar - xNext) +
                ((ρ : ℝ) * ‖B (zStar - zNext)‖ ^ (2 : ℕ) +
                  quadraticPenaltyOfLinearMap Q (zStar - zNext)) +
                (1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2 := by
    have hTailUpper :
        inner ℝ residual (yBar - yTilde) +
            inner ℝ (xStar - xNext) (G (xNext - x k)) +
            (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) +
            inner ℝ (zStar - zNext) (Q (zNext - z k)) ≤
          ((quadraticPenaltyOfLinearMap G (xStar - x k) +
                ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) +
                  quadraticPenaltyOfLinearMap Q (zStar - z k)) +
                (1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ)) -
              (quadraticPenaltyOfLinearMap G (xStar - xNext) +
                ((ρ : ℝ) * ‖B (zStar - zNext)‖ ^ (2 : ℕ) +
                  quadraticPenaltyOfLinearMap Q (zStar - zNext)) +
                (1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2 := by
      have hBNormSq :
          ‖B (z k) - B zNext‖ ^ (2 : ℕ) = ‖B zNext - B (z k)‖ ^ (2 : ℕ) := by
        -- Rewrite the multiplier defect with the same `B zNext - B (z k)` spelling used downstream.
        rw [show B (z k) - B zNext = -(B zNext - B (z k)) by abel]
        rw [norm_neg]
      have hMultiplierUpper' :
          inner ℝ residual (yBar - yTilde) ≤
            (((1 / (ρ : ℝ)) * ‖yBar - y k‖ ^ (2 : ℕ) -
                  ((1 / (ρ : ℝ)) * ‖yBar - y (k + 1)‖ ^ (2 : ℕ))) / 2) +
              ((ρ : ℝ) / 2) * ‖B zNext - B (z k)‖ ^ (2 : ℕ) := by
        simpa [hBNormSq] using hMultiplierUpper
      have hBterm' :
          (ρ : ℝ) * inner ℝ (B (zStar - zNext)) (B (zNext - z k)) ≤
            ((ρ : ℝ) * ‖B (zStar - z k)‖ ^ (2 : ℕ) -
                (ρ : ℝ) * ‖B (zStar - zNext)‖ ^ (2 : ℕ)) / 2 -
              ((ρ : ℝ) / 2) * ‖B zNext - B (z k)‖ ^ (2 : ℕ) := by
        simpa [map_sub] using hBterm
      -- Combine the four one-step bounds after putting the `B`-step term in a common normal form.
      linarith [hMultiplierUpper', hGterm, hBterm', hQterm]
    rw [hTargetRewrite]
    linarith [hBlockGap, hTailUpper]
  simpa [xNext, zNext, residual] using hFinal

/-- Helper for Theorem 15.2: summing the one-step energy drop bounds yields the cumulative
gap-plus-residual estimate used before Jensen averaging. -/
private theorem cumulativeGapResidualSum_le_initialEnergy
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    (n : ℕ) (yBar : Y) :
    Finset.sum (Finset.range (n + 1)) (fun k ↦
      (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
          (H[h₁, h₂] (xStar, zStar)).toReal) +
        inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c))) ≤
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖yBar - y0‖ ^ (2 : ℕ)) / 2 := by
  let energy : ℕ → ℝ := fun j ↦
    quadraticPenaltyOfLinearMap G (xStar - x j) +
      ((ρ : ℝ) * ‖B (zStar - z j)‖ ^ (2 : ℕ) +
        quadraticPenaltyOfLinearMap Q (zStar - z j)) +
      (1 / (ρ : ℝ)) * ‖yBar - y j‖ ^ (2 : ℕ)
  have hOneStep :
      ∀ k,
        (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
              (H[h₁, h₂] (xStar, zStar)).toReal) +
            inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c)) ≤
          (energy k - energy (k + 1)) / 2 := by
    intro k
    -- Repackage the one-step bound in terms of a single scalar energy sequence.
    simpa [energy] using
      oneStepGapResidual_le_energyDrop
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
        (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
        hAssump hTrajectory hPrimalOpt k yBar
  have hSumStep :
      Finset.sum (Finset.range (n + 1)) (fun k ↦
        (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
            (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c))) ≤
        Finset.sum (Finset.range (n + 1)) (fun k ↦ (energy k - energy (k + 1)) / 2) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    exact hOneStep k
  have hTelescopes :
      ∀ m,
        Finset.sum (Finset.range (m + 1)) (fun k ↦ (energy k - energy (k + 1)) / 2) =
          (energy 0 - energy (m + 1)) / 2 := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hTerminalNonneg : 0 ≤ energy (n + 1) := by
    have hGnonneg :
        0 ≤ quadraticPenaltyOfLinearMap G (xStar - x (n + 1)) := by
      simpa [quadraticPenaltyOfLinearMap_apply] using
        hAssump.G_positive.inner_nonneg_right (xStar - x (n + 1))
    have hBnonneg :
        0 ≤ (ρ : ℝ) * ‖B (zStar - z (n + 1))‖ ^ (2 : ℕ) := by
      exact mul_nonneg ρ.2.le (by positivity)
    have hQnonneg :
        0 ≤ quadraticPenaltyOfLinearMap Q (zStar - z (n + 1)) := by
      simpa [quadraticPenaltyOfLinearMap_apply] using
        hAssump.Q_positive.inner_nonneg_right (zStar - z (n + 1))
    have hYnonneg :
        0 ≤ (1 / (ρ : ℝ)) * ‖yBar - y (n + 1)‖ ^ (2 : ℕ) := by
      exact mul_nonneg (one_div_nonneg.mpr ρ.2.le) (by positivity)
    dsimp [energy]
    exact add_nonneg (add_nonneg hGnonneg (add_nonneg hBnonneg hQnonneg)) hYnonneg
  have hDropTerminal : (energy 0 - energy (n + 1)) / 2 ≤ energy 0 / 2 := by
    linarith
  have hTrajectory' := hTrajectory.toIsADPMMTrajectory
  have hx0 : x 0 = x0 := hTrajectory'.x_zero
  have hz0 : z 0 = z0 := hTrajectory'.z_zero
  have hy0 : y 0 = y0 := hTrajectory'.y_zero
  calc
    Finset.sum (Finset.range (n + 1)) (fun k ↦
        (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
            (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c))) ≤
        Finset.sum (Finset.range (n + 1)) (fun k ↦ (energy k - energy (k + 1)) / 2) := hSumStep
    _ = (energy 0 - energy (n + 1)) / 2 := hTelescopes n
    _ ≤ energy 0 / 2 := hDropTerminal
    _ = (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖yBar - y0‖ ^ (2 : ℕ)) / 2 := by
        simp [energy, hx0, hz0, hy0]

/-- Helper for Theorem 15.2: the ergodic average is the constant-weight center of mass of the
shifted iterates. -/
private theorem ergodicAverage_eq_centerMass
    {E : Type uE} [AddCommGroup E] [Module ℝ E]
    (u : ℕ → E) (n : ℕ) :
    ergodicAverage u n =
      (Finset.range (n + 1)).centerMass (fun _ ↦ (1 : ℝ)) (fun k ↦ u (k + 1)) := by
  -- Expand both averages to the same normalized finite sum.
  simp [ergodicAverage, Finset.centerMass]

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: the ergodic average pair lies in the effective domain of the ADMM
objective because that domain is convex and every sampled iterate pair is finite. -/
private theorem ergodicAverage_memEffectiveDomain
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    (n : ℕ) :
    (ergodicAverage x n, ergodicAverage z n) ∈ effective_domain (H[h₁, h₂]) := by
  have hDomConvex :
      Convex ℝ (effective_domain (H[h₁, h₂])) :=
    effective_domain_convex_of_is_convex_function
      (admmObjective_convex_of_problem
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump)
  have hWeightsNonneg : ∀ k ∈ Finset.range (n + 1), 0 ≤ (1 : ℝ) := by
    intro k hk
    norm_num
  have hWeightSumPos : 0 < ∑ k ∈ Finset.range (n + 1), (1 : ℝ) := by
    simpa using (show 0 < (n : ℝ) + 1 by positivity)
  have hMembers :
      ∀ k ∈ Finset.range (n + 1),
        (fun j ↦ (x (j + 1), z (j + 1))) k ∈ effective_domain (H[h₁, h₂]) := by
    intro k hk
    exact sampledIterate_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt k
  -- Rewrite the ergodic pair to the exact `centerMass` owner consumed by the convexity API.
  have hCenter :
      (ergodicAverage x n, ergodicAverage z n) =
        (Finset.range (n + 1)).centerMass (fun _ ↦ (1 : ℝ))
          (fun k ↦ (x (k + 1), z (k + 1))) := by
    ext
    · simp [ergodicAverage_eq_centerMass, Finset.centerMass, Prod.smul_fst, Prod.fst_sum]
    · simp [ergodicAverage_eq_centerMass, Finset.centerMass, Prod.smul_snd, Prod.snd_sum]
  exact hCenter ▸ hDomConvex.centerMass_mem hWeightsNonneg hWeightSumPos hMembers

omit [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: the normalized residual direction has norm at most `γ` and attains
the support value `γ ‖r‖`. -/
private theorem residualDirection_norm_le_and_inner_eq
    {γ : PosReal} (r : Y) :
    ∃ yDir : Y, ‖yDir‖ ≤ (γ : ℝ) ∧ inner ℝ yDir r = (γ : ℝ) * ‖r‖ := by
  classical
  by_cases hr : r = 0
  · -- At zero residual the zero multiplier gives both the norm and support identities.
    refine ⟨0, ?_, ?_⟩
    · simpa using (show 0 ≤ (γ : ℝ) from γ.2.le)
    · simp [hr]
  · have hnorm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr
    -- Off the origin the explicit normalized residual has norm `γ`.
    refine ⟨((γ : ℝ) / ‖r‖) • r, ?_, ?_⟩
    · have hyDir_norm :
        ‖(((γ : ℝ) / ‖r‖) • r : Y)‖ = (γ : ℝ) := by
          calc
            ‖(((γ : ℝ) / ‖r‖) • r : Y)‖ = |(γ : ℝ) / ‖r‖| * ‖r‖ := norm_smul _ _
            _ = (((γ : ℝ) / ‖r‖) * ‖r‖) := by
                  rw [abs_of_pos (div_pos γ.2 hnorm_pos)]
            _ = (γ : ℝ) := by
                  field_simp [hnorm_pos.ne']
      exact hyDir_norm.le
    · calc
        inner ℝ (((γ : ℝ) / ‖r‖) • r) r = ((γ : ℝ) / ‖r‖) * inner ℝ r r := by
              rw [real_inner_smul_left]
        _ = ((γ : ℝ) / ‖r‖) * (‖r‖ * ‖r‖) := by
              rw [real_inner_self_eq_norm_mul_norm]
        _ = (γ : ℝ) * ‖r‖ := by
              field_simp [hnorm_pos.ne']

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ Y] in
/-- Helper for Theorem 15.2: summing the residual pairings over the sampled iterates is the same
as pairing `yBar` with the averaged residual and multiplying by the sample count. -/
private theorem sumResidualPairing_eq_avgResidualPairing
    (A : X →ₗ[ℝ] Y) (B : Z →ₗ[ℝ] Y) (c : Y)
    (x : ℕ → X) (z : ℕ → Z)
    (n : ℕ) (yBar : Y) :
    Finset.sum (Finset.range (n + 1))
        (fun k ↦ inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c)) =
      ((n : ℝ) + 1) * inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c) := by
  have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by
    positivity
  have hsum :
      Finset.sum (Finset.range (n + 1))
          (fun k ↦ (A (x (k + 1)) + B (z (k + 1)) - c)) =
        ((n : ℝ) + 1) • (A (ergodicAverage x n) + B (ergodicAverage z n) - c) := by
    -- Expand the ergodic averages and gather the linear-map and constant terms into one sum.
    calc
      Finset.sum (Finset.range (n + 1))
          (fun k ↦ (A (x (k + 1)) + B (z (k + 1)) - c)) =
        Finset.sum (Finset.range (n + 1)) (fun k ↦ A (x (k + 1))) +
          Finset.sum (Finset.range (n + 1)) (fun k ↦ B (z (k + 1))) -
          Finset.sum (Finset.range (n + 1)) (fun _ ↦ c) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ =
        Finset.sum (Finset.range (n + 1)) (fun k ↦ A (x (k + 1))) +
          Finset.sum (Finset.range (n + 1)) (fun k ↦ B (z (k + 1))) -
          ((n : ℝ) + 1) • c := by
            rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ]
            simp [Nat.cast_add, Nat.cast_one]
      _ =
        ((n : ℝ) + 1) • A (ergodicAverage x n) +
          ((n : ℝ) + 1) • B (ergodicAverage z n) -
          ((n : ℝ) + 1) • c := by
            rw [ergodicAverage, ergodicAverage]
            simp [map_sum, Finset.smul_sum, smul_smul, hn1_ne]
      _ = ((n : ℝ) + 1) • (A (ergodicAverage x n) + B (ergodicAverage z n) - c) := by
            simp [smul_add, sub_eq_add_neg, add_assoc]
  -- Move the finite sum inside the inner product, then rewrite the summed residual as the scaled
  -- ergodic residual.
  calc
    Finset.sum (Finset.range (n + 1))
        (fun k ↦ inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c)) =
      inner ℝ yBar
        (Finset.sum (Finset.range (n + 1))
          (fun k ↦ (A (x (k + 1)) + B (z (k + 1)) - c))) := by
            rw [inner_sum]
    _ = inner ℝ yBar (((n : ℝ) + 1) • (A (ergodicAverage x n) + B (ergodicAverage z n) - c)) := by
          rw [hsum]
    _ = ((n : ℝ) + 1) * inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c) := by
          rw [real_inner_smul_right]

/-- Helper for Theorem 15.2: the missing averaged Lyapunov inequality with an arbitrary
multiplier `yBar`, together with effective-domain membership of the ergodic average pair. -/
private theorem ergodicGapWithArbitraryMultiplier
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    (n : ℕ) (yBar : Y) :
    (ergodicAverage x n, ergodicAverage z n) ∈ effective_domain (H[h₁, h₂]) ∧
      ((H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
          (H[h₁, h₂] (xStar, zStar)).toReal) +
        inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c) ≤
          (quadraticPenaltyOfLinearMap G (xStar - x0) +
              ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
                quadraticPenaltyOfLinearMap Q (zStar - z0)) +
              (1 / (ρ : ℝ)) * ‖yBar - y0‖ ^ (2 : ℕ)) /
            (2 * ((n : ℝ) + 1)) := by
  -- Route correction: keep the cumulative Lyapunov estimate, the residual-average transport, and
  -- the Jensen step separate instead of mixing them in one wide rewrite chain.
  let avgPair : X × Z := (ergodicAverage x n, ergodicAverage z n)
  let numerator : ℝ :=
    quadraticPenaltyOfLinearMap G (xStar - x0) +
      ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
        quadraticPenaltyOfLinearMap Q (zStar - z0)) +
      (1 / (ρ : ℝ)) * ‖yBar - y0‖ ^ (2 : ℕ)
  have hn1_pos : 0 < (n : ℝ) + 1 := by
    positivity
  have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by
    exact hn1_pos.ne'
  have hAvgDom :
      avgPair ∈ effective_domain (H[h₁, h₂]) :=
    ergodicAverage_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt n
  have hCum :
      Finset.sum (Finset.range (n + 1)) (fun k ↦
        (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
            (H[h₁, h₂] (xStar, zStar)).toReal) +
          inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c))) ≤
        numerator / 2 := by
    simpa [numerator] using
      cumulativeGapResidualSum_le_initialEnergy
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
        (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
        hAssump hTrajectory hPrimalOpt n yBar
  have hConvToReal :
      ConvexOn ℝ (effective_domain (H[h₁, h₂])) (fun xz : X × Z ↦ (H[h₁, h₂] xz).toReal) :=
    convexOn_toReal_of_is_convex_function
      (admmObjective_convex_of_problem
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump)
      (fun xz _ ↦
        admmObjective_ne_bot_of_problem
          (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
          hAssump xz)
  have hMembers :
      ∀ k ∈ Finset.range (n + 1),
        (fun j ↦ (x (j + 1), z (j + 1))) k ∈ effective_domain (H[h₁, h₂]) := by
    intro k hk
    exact sampledIterate_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt k
  have hCenter :
      avgPair =
        (Finset.range (n + 1)).centerMass (fun _ ↦ (1 : ℝ))
          (fun k ↦ (x (k + 1), z (k + 1))) := by
    -- Rewrite the ergodic pair to the exact center-of-mass owner consumed by Jensen.
    ext
    · simp [avgPair, ergodicAverage_eq_centerMass, Finset.centerMass, Prod.smul_fst, Prod.fst_sum]
    · simp [avgPair, ergodicAverage_eq_centerMass, Finset.centerMass, Prod.smul_snd, Prod.snd_sum]
  have hJensenCenter :
      (H[h₁, h₂] avgPair).toReal ≤
        (Finset.range (n + 1)).centerMass (fun _ ↦ (1 : ℝ))
          (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) := by
    -- Jensen bounds the objective at the ergodic center of mass by the averaged sampled values.
    rw [hCenter]
    simpa [Function.comp] using
      hConvToReal.map_centerMass_le
        (t := Finset.range (n + 1)) (w := fun _ ↦ (1 : ℝ))
        (p := fun k ↦ (x (k + 1), z (k + 1)))
        (fun k hk ↦ by norm_num) (by simpa using hn1_pos) hMembers
  have hJensen :
      (H[h₁, h₂] avgPair).toReal ≤
        (1 / ((n : ℝ) + 1)) *
          Finset.sum (Finset.range (n + 1))
            (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) := by
    -- Expanding `centerMass` converts Jensen into the normalized finite sum used by the source.
    calc
      (H[h₁, h₂] avgPair).toReal ≤
          (Finset.range (n + 1)).centerMass (fun _ ↦ (1 : ℝ))
            (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) :=
        hJensenCenter
      _ =
          (1 / ((n : ℝ) + 1)) *
            Finset.sum (Finset.range (n + 1))
              (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) := by
                simp [Finset.centerMass]
  have hObjectiveScaled :
      ((n : ℝ) + 1) * (H[h₁, h₂] avgPair).toReal ≤
        Finset.sum (Finset.range (n + 1))
          (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) := by
    -- Clear the positive averaging denominator before combining with the cumulative estimate.
    calc
      ((n : ℝ) + 1) * (H[h₁, h₂] avgPair).toReal ≤
          ((n : ℝ) + 1) *
            ((1 / ((n : ℝ) + 1)) *
              Finset.sum (Finset.range (n + 1))
                (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal)) := by
                  exact mul_le_mul_of_nonneg_left hJensen hn1_pos.le
      _ =
          Finset.sum (Finset.range (n + 1))
            (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) := by
              field_simp [hn1_ne]
  have hGapScaled :
      ((n : ℝ) + 1) *
          ((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) ≤
        Finset.sum (Finset.range (n + 1)) (fun k ↦
          ((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
            (H[h₁, h₂] (xStar, zStar)).toReal)) := by
    have hConst :
        Finset.sum (Finset.range (n + 1))
            (fun _ ↦ (H[h₁, h₂] (xStar, zStar)).toReal) =
          ((n : ℝ) + 1) * (H[h₁, h₂] (xStar, zStar)).toReal := by
      simp
    calc
      ((n : ℝ) + 1) *
          ((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) =
        ((n : ℝ) + 1) * (H[h₁, h₂] avgPair).toReal -
          Finset.sum (Finset.range (n + 1))
            (fun _ ↦ (H[h₁, h₂] (xStar, zStar)).toReal) := by
              rw [mul_sub, hConst]
      _ ≤
        Finset.sum (Finset.range (n + 1))
            (fun k ↦ (H[h₁, h₂] (x (k + 1), z (k + 1))).toReal) -
          Finset.sum (Finset.range (n + 1))
            (fun _ ↦ (H[h₁, h₂] (xStar, zStar)).toReal) := by
              exact sub_le_sub_right hObjectiveScaled _
      _ =
        Finset.sum (Finset.range (n + 1)) (fun k ↦
          ((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
            (H[h₁, h₂] (xStar, zStar)).toReal)) := by
              rw [← Finset.sum_sub_distrib]
  have hResidualScaled :
      ((n : ℝ) + 1) * inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c) =
        Finset.sum (Finset.range (n + 1))
          (fun k ↦ inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c)) := by
    -- The linear residual term commutes exactly with constant-weight averaging.
    symm
    exact sumResidualPairing_eq_avgResidualPairing A B c x z n yBar
  have hAssembled :
      ((n : ℝ) + 1) *
          (((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
            inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c)) ≤
        numerator / 2 := by
    -- Add the scaled Jensen gap bound to the exact residual-average transport and invoke the
    -- cumulative Lyapunov estimate.
    calc
      ((n : ℝ) + 1) *
          (((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
            inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c)) =
        ((n : ℝ) + 1) *
            ((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          (((n : ℝ) + 1) * inner ℝ yBar
            (A (ergodicAverage x n) + B (ergodicAverage z n) - c)) := by
              ring
      _ ≤
        Finset.sum (Finset.range (n + 1)) (fun k ↦
            ((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
              (H[h₁, h₂] (xStar, zStar)).toReal)) +
          Finset.sum (Finset.range (n + 1))
            (fun k ↦ inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c)) := by
              exact add_le_add hGapScaled (le_of_eq hResidualScaled)
      _ =
        Finset.sum (Finset.range (n + 1)) (fun k ↦
          (((H[h₁, h₂] (x (k + 1), z (k + 1))).toReal -
              (H[h₁, h₂] (xStar, zStar)).toReal) +
            inner ℝ yBar (A (x (k + 1)) + B (z (k + 1)) - c))) := by
              rw [← Finset.sum_add_distrib]
      _ ≤ numerator / 2 := hCum
  have hDiv :
      (((n : ℝ) + 1) *
          (((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
            inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c))) /
        ((n : ℝ) + 1) ≤
      (numerator / 2) / ((n : ℝ) + 1) :=
    div_le_div_of_nonneg_right hAssembled hn1_pos.le
  have hFinal :
      ((H[h₁, h₂] avgPair).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
        inner ℝ yBar (A (ergodicAverage x n) + B (ergodicAverage z n) - c) ≤
          numerator / (2 * ((n : ℝ) + 1)) := by
    -- Divide the assembled estimate by the positive sample count only at the end.
    simpa [hn1_ne, avgPair, numerator, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hDiv
  exact ⟨hAvgDom, by simpa [avgPair, numerator] using hFinal⟩

/-- Helper for Theorem 15.2: dual optimality and strong duality give the averaged primal gap lower
bound `-⟪y*, A xAvg + B zAvg - c⟫ ≤ H(xAvg, zAvg) - H(x*, z*)` whenever the averaged pair has
finite ADMM objective value. -/
private theorem gapGeNegInnerResidualOfDualOptimal
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    {yStar : Y}
    (hDualOpt : IsADPMMDualOptimal h₁ h₂ A B c yStar)
    {xAvg : X} {zAvg : Z}
    (hAvgDom : (xAvg, zAvg) ∈ effective_domain (H[h₁, h₂])) :
    - inner ℝ yStar (A xAvg + B zAvg - c) ≤
      (H[h₁, h₂] (xAvg, zAvg)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal := by
  have hStarDom :
      (xStar, zStar) ∈ effective_domain (H[h₁, h₂]) :=
    primalOptimal_memEffectiveDomain
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump hPrimalOpt
  have hStarObj_ne_top : H[h₁, h₂] (xStar, zStar) ≠ ⊤ :=
    (mem_effective_domain.mp hStarDom).ne
  have hStarObj_ne_bot : H[h₁, h₂] (xStar, zStar) ≠ ⊥ :=
    admmObjective_ne_bot_of_problem
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump (xStar, zStar)
  have hAvgObj_ne_top : H[h₁, h₂] (xAvg, zAvg) ≠ ⊤ :=
    (mem_effective_domain.mp hAvgDom).ne
  have hAvgObj_ne_bot : H[h₁, h₂] (xAvg, zAvg) ≠ ⊥ :=
    admmObjective_ne_bot_of_problem
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
      hAssump (xAvg, zAvg)
  have hDualMax :
      IsMaxOn (admm_dual_objective_primal h₁ h₂ A B c) Set.univ yStar :=
    hDualOpt.isMaxOn
  have hDualValue :
      admm_dual_problem_value h₁ h₂ A B c =
        admm_dual_objective_primal h₁ h₂ A B c yStar := by
    -- The primal-space maximizer attains the same supremum because `toDualMap` is surjective.
    apply le_antisymm
    · rw [admm_dual_problem_value_eq_sSup]
      refine sSup_le ?_
      intro q hq
      rcases hq with ⟨η, rfl⟩
      let ηc : StrongDual ℝ Y :=
        { toLinearMap := η
          cont := LinearMap.continuous_of_finiteDimensional η }
      rcases (InnerProductSpace.toDual ℝ Y).surjective ηc with ⟨y', hy'⟩
      have hy'lin : (InnerProductSpace.toDualMap ℝ Y y' : Module.Dual ℝ Y) = η := by
        exact congrArg ContinuousLinearMap.toLinearMap hy'
      simpa [admm_dual_objective_primal, hy'lin] using (isMaxOn_univ_iff.mp hDualMax) y'
    · rw [admm_dual_problem_value_eq_sSup]
      exact le_sSup ⟨InnerProductSpace.toDualMap ℝ Y yStar, rfl⟩
  have hPrimalValueEq :
      H_opt[h₁, h₂; A, B, c] = H[h₁, h₂] (xStar, zStar) := by
    have hxzStar_data : (xStar, zStar) ∈ admm_feasible_set A B c ∧
        IsMinOn (H[h₁, h₂]) (admm_feasible_set A B c) (xStar, zStar) :=
      ⟨hPrimalOpt.feasible, hPrimalOpt.isMinOn⟩
    have hxzStar_min :
        IsMinOn (constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c))
          Set.univ (xStar, zStar) := by
      rw [isMinOn_univ_iff]
      intro u
      by_cases hu : u ∈ admm_feasible_set A B c
      · simpa [constrained_problem_objective, hu, hxzStar_data.1] using hxzStar_data.2 hu
      · rw [constrained_problem_objective_of_not_mem (H[h₁, h₂]) hu]
        exact le_top
    have hglb_raw := hxzStar_min.isGLB (by simp : (xStar, zStar) ∈ (Set.univ : Set (X × Z)))
    rw [admm_problem_value_eq_sInf]
    have hcs_raw := hglb_raw.csInf_eq ⟨_, ⟨(xStar, zStar), ⟨by simp, rfl⟩⟩⟩
    calc
      sInf (Set.range (constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c)))
          = constrained_problem_objective (H[h₁, h₂]) (admm_feasible_set A B c) (xStar, zStar) := by
              simpa [Set.range] using hcs_raw
      _ = H[h₁, h₂] (xStar, zStar) := by
            simp [constrained_problem_objective, hxzStar_data.1]
  have hStrongDuality :
      H[h₁, h₂] (xStar, zStar) = admm_dual_objective_primal h₁ h₂ A B c yStar := by
    -- Strong duality identifies the primal optimum with the attained dual value at `y*`.
    calc
      H[h₁, h₂] (xStar, zStar) = H_opt[h₁, h₂; A, B, c] := hPrimalValueEq.symm
      _ = admm_dual_problem_value h₁ h₂ A B c := by
            exact admm_problem_value_eq_admm_dual_problem_value
              (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
              hAssump
      _ = admm_dual_objective_primal h₁ h₂ A B c yStar := hDualValue
  have hDualLeLagrangian :
      admm_dual_objective_primal h₁ h₂ A B c yStar ≤
        admm_lagrangian h₁ h₂ A B c xAvg zAvg (InnerProductSpace.toDualMap ℝ Y yStar) := by
    -- The dual objective is the infimum of the Lagrangian, so any primal point dominates it.
    rw [admm_dual_objective_primal, admm_dual_objective_eq_sInf_lagrangian
      h₁ h₂ A B c hAssump.toIsProperExtendedRealFunction hAssump.h₂_proper]
    exact sInf_le ⟨(xAvg, zAvg), rfl⟩
  have hEReal :
      H[h₁, h₂] (xStar, zStar) ≤
        H[h₁, h₂] (xAvg, zAvg) +
          ((inner ℝ yStar (A xAvg + B zAvg - c) : ℝ) : EReal) := by
    -- Compare the attained dual value with the Lagrangian evaluated at the averaged primal point.
    calc
      H[h₁, h₂] (xStar, zStar) = admm_dual_objective_primal h₁ h₂ A B c yStar := hStrongDuality
      _ ≤ admm_lagrangian h₁ h₂ A B c xAvg zAvg (InnerProductSpace.toDualMap ℝ Y yStar) :=
            hDualLeLagrangian
      _ = H[h₁, h₂] (xAvg, zAvg) +
            ((inner ℝ yStar (A xAvg + B zAvg - c) : ℝ) : EReal) := by
            simp [admm_lagrangian, InnerProductSpace.toDualMap_apply_apply]
  have hRight_ne_top :
      H[h₁, h₂] (xAvg, zAvg) +
          ((inner ℝ yStar (A xAvg + B zAvg - c) : ℝ) : EReal) ≠ ⊤ := by
    exact
      (EReal.add_ne_top_iff_ne_top₂ hAvgObj_ne_bot (EReal.coe_ne_bot _)).2
        ⟨hAvgObj_ne_top, EReal.coe_ne_top _⟩
  have hReal :
      (H[h₁, h₂] (xStar, zStar)).toReal ≤
        (H[h₁, h₂] (xAvg, zAvg)).toReal + inner ℝ yStar (A xAvg + B zAvg - c) := by
    -- Move the finite `EReal` inequality down to `ℝ`.
    have hRealRaw :
        (H[h₁, h₂] (xStar, zStar)).toReal ≤
          (H[h₁, h₂] (xAvg, zAvg) +
            ((inner ℝ yStar (A xAvg + B zAvg - c) : ℝ) : EReal)).toReal :=
      EReal.toReal_le_toReal hEReal hStarObj_ne_bot hRight_ne_top
    rw [EReal.toReal_add hAvgObj_ne_top hAvgObj_ne_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      at hRealRaw
    simpa using hRealRaw
  linarith
-- Proof sketch: this is the objective-gap half of the ergodic AD-PMM estimate stated in the
-- source, with the displayed numerator written explicitly and the `C`-norm expanded as
-- `ρ ‖B (z^* - z^0)‖² + ⟪z^* - z^0, Q (z^* - z^0)⟫`.
-- Label-associated main declaration for Theorem 15.2.
/-- Theorem 15.2 (1): the ergodic average objective value satisfies
`H(x^(n), z^(n)) - H_opt ≤
 (‖x^* - x^0‖_G^2 + (ρ * ‖B (z^* - z^0)‖^2 + ⟪z^* - z^0, Q (z^* - z^0)⟫)
   + (1 / ρ) (γ + ‖y^0‖)^2) / (2 (n + 1))`,
which is the source bound with `‖z^* - z^0‖_C^2` expanded along `C = ρ Bᵀ B + Q`. -/
theorem ad_pmm_ergodic_objective_gap_le
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    {yStar : Y}
    (hDualOpt : IsADPMMDualOptimal h₁ h₂ A B c yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ) :
    (H[h₁, h₂] (ergodicAverage x n, ergodicAverage z n)).toReal -
        (H[h₁, h₂] (xStar, zStar)).toReal ≤
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := by
  have _ := hDualOpt
  have _ := hγ
  -- Specialize the averaged multiplier inequality at `yBar = 0`.
  obtain ⟨_hAvgDom, hGap0⟩ :=
    ergodicGapWithArbitraryMultiplier
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt n (0 : Y)
  have hsq0 : ‖y0‖ ^ (2 : ℕ) ≤ ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    have hle : ‖y0‖ ≤ (γ : ℝ) + ‖y0‖ := by
      simpa [add_comm] using (le_add_of_nonneg_right γ.2.le : ‖y0‖ ≤ ‖y0‖ + (γ : ℝ))
    have hmul :=
      mul_le_mul hle hle (norm_nonneg y0) (add_nonneg γ.2.le (norm_nonneg y0))
    simpa [pow_two] using hmul
  have hsq :
      ‖(0 : Y) - y0‖ ^ (2 : ℕ) ≤ ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    simpa using hsq0
  have hρinv_nonneg : 0 ≤ 1 / (ρ : ℝ) := by
    exact one_div_nonneg.mpr ρ.2.le
  have hmul :
      (1 / (ρ : ℝ)) * ‖(0 : Y) - y0‖ ^ (2 : ℕ) ≤
        (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hsq hρinv_nonneg
  have hnum :
      quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖(0 : Y) - y0‖ ^ (2 : ℕ) ≤
        quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      add_le_add_left hmul
        (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)))
  have hden_nonneg : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
  have hbound :
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖(0 : Y) - y0‖ ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) ≤
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) := by
    exact div_le_div_of_nonneg_right hnum hden_nonneg
  -- The `yBar = 0` residual term vanishes.
  simpa using le_trans hGap0 hbound

-- Proof sketch: this is the feasibility-residual half of the source ergodic AD-PMM estimate,
-- again with the displayed numerator written explicitly and `‖z^* - z^0‖_C^2` expanded.
/-- Companion to Theorem 15.2: the ergodic average feasibility residual satisfies
`‖A x^(n) + B z^(n) - c‖ ≤
 (‖x^* - x^0‖_G^2 + (ρ * ‖B (z^* - z^0)‖^2 + ⟪z^* - z^0, Q (z^* - z^0)⟫)
   + (1 / ρ) (γ + ‖y^0‖)^2) / (γ (n + 1))`,
which is the source bound with `‖z^* - z^0‖_C^2` expanded along `C = ρ Bᵀ B + Q`. -/
theorem ad_pmm_ergodic_feasibility_residual_le
    (hAssump : IsADPMMProblem ρ h₁ h₂ A B G Q c)
    (hTrajectory : IsADPMMLinearTrajectory ρ h₁ h₂ A B c G Q x0 z0 y0 x z y)
    {xStar : X} {zStar : Z}
    (hPrimalOpt : IsADPMMPrimalOptimal h₁ h₂ A B c xStar zStar)
    {yStar : Y}
    (hDualOpt : IsADPMMDualOptimal h₁ h₂ A B c yStar)
    {γ : PosReal} (hγ : 2 * ‖yStar‖ ≤ (γ : ℝ))
    (n : ℕ) :
    ‖A (ergodicAverage x n) + B (ergodicAverage z n) - c‖ ≤
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)) /
        ((γ : ℝ) * ((n : ℝ) + 1)) := by
  set xAvg : X := ergodicAverage x n
  set zAvg : Z := ergodicAverage z n
  set residual : Y := A xAvg + B zAvg - c
  set numerator : ℝ :=
    quadraticPenaltyOfLinearMap G (xStar - x0) +
      ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
        quadraticPenaltyOfLinearMap Q (zStar - z0)) +
      (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ)
  -- Choose the residual-supporting multiplier from the normalized direction helper.
  obtain ⟨yDir, hyDirNorm, hyDirInner⟩ :=
    residualDirection_norm_le_and_inner_eq (γ := γ) residual
  obtain ⟨hAvgDom, hGapDirRaw⟩ :=
    ergodicGapWithArbitraryMultiplier
      (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q)
      (c := c) (x0 := x0) (z0 := z0) (y0 := y0) (x := x) (z := z) (y := y)
      hAssump hTrajectory hPrimalOpt n yDir
  have hyDirSq :
      ‖yDir - y0‖ ^ (2 : ℕ) ≤ ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    -- Bound the normalized residual direction against the radius `γ + ‖y⁰‖`.
    have hyDirDist : ‖yDir - y0‖ ≤ (γ : ℝ) + ‖y0‖ := by
      calc
        ‖yDir - y0‖ ≤ ‖yDir‖ + ‖y0‖ := norm_sub_le _ _
        _ ≤ (γ : ℝ) + ‖y0‖ := add_le_add hyDirNorm le_rfl
    have hmul :=
      mul_le_mul hyDirDist hyDirDist
        (norm_nonneg (yDir - y0))
        (add_nonneg γ.2.le (norm_nonneg y0))
    simpa [pow_two] using hmul
  have hρinv_nonneg : 0 ≤ 1 / (ρ : ℝ) := by
    exact one_div_nonneg.mpr ρ.2.le
  have hmul :
      (1 / (ρ : ℝ)) * ‖yDir - y0‖ ^ (2 : ℕ) ≤
        (1 / (ρ : ℝ)) * ((γ : ℝ) + ‖y0‖) ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hyDirSq hρinv_nonneg
  have hnum :
      quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖yDir - y0‖ ^ (2 : ℕ) ≤
        numerator := by
    -- Replace the direction-dependent multiplier term by the theorem numerator.
    simpa [numerator, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hmul
        (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)))
  have hden_nonneg : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
  have hbound :
      (quadraticPenaltyOfLinearMap G (xStar - x0) +
          ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
            quadraticPenaltyOfLinearMap Q (zStar - z0)) +
          (1 / (ρ : ℝ)) * ‖yDir - y0‖ ^ (2 : ℕ)) /
        (2 * ((n : ℝ) + 1)) ≤
      numerator / (2 * ((n : ℝ) + 1)) := by
    exact div_le_div_of_nonneg_right hnum hden_nonneg
  have hGapDir :
      ((H[h₁, h₂] (xAvg, zAvg)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
          (γ : ℝ) * ‖residual‖ ≤
        numerator / (2 * ((n : ℝ) + 1)) := by
    -- Specializing the arbitrary-multiplier gap estimate at `yDir` turns the residual pairing
    -- into `γ ‖r‖`.
    have hGapDir' :
        ((H[h₁, h₂] (xAvg, zAvg)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal) +
            (γ : ℝ) * ‖residual‖ ≤
          (quadraticPenaltyOfLinearMap G (xStar - x0) +
              ((ρ : ℝ) * ‖B (zStar - z0)‖ ^ (2 : ℕ) +
                quadraticPenaltyOfLinearMap Q (zStar - z0)) +
              (1 / (ρ : ℝ)) * ‖yDir - y0‖ ^ (2 : ℕ)) /
            (2 * ((n : ℝ) + 1)) := by
      simpa [xAvg, zAvg, residual, hyDirInner] using hGapDirRaw
    exact le_trans hGapDir' hbound
  have hGapLower :
      - inner ℝ yStar residual ≤
        (H[h₁, h₂] (xAvg, zAvg)).toReal - (H[h₁, h₂] (xStar, zStar)).toReal := by
    -- Strong duality converts the dual-optimal multiplier into a lower bound on the averaged gap.
    simpa [xAvg, zAvg, residual] using
      gapGeNegInnerResidualOfDualOptimal
        (ρ := ρ) (h₁ := h₁) (h₂ := h₂) (A := A) (B := B) (G := G) (Q := Q) (c := c)
        hAssump hPrimalOpt hDualOpt hAvgDom
  have hInnerUpper :
      inner ℝ yStar residual ≤ ‖yStar‖ * ‖residual‖ := by
    exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
  have hMain :
      (γ : ℝ) * ‖residual‖ - inner ℝ yStar residual ≤
        numerator / (2 * ((n : ℝ) + 1)) := by
    -- Combine the upper gap estimate with the dual lower bound.
    linarith
  have hCoeff :
      (((γ : ℝ) - ‖yStar‖) * ‖residual‖) ≤
        numerator / (2 * ((n : ℝ) + 1)) := by
    -- Replace the dual pairing by the Cauchy-Schwarz norm bound.
    have hcombo :
        (γ : ℝ) * ‖residual‖ - ‖yStar‖ * ‖residual‖ ≤
          (γ : ℝ) * ‖residual‖ - inner ℝ yStar residual :=
      sub_le_sub_left hInnerUpper ((γ : ℝ) * ‖residual‖)
    have hleft :
        (((γ : ℝ) - ‖yStar‖) * ‖residual‖) =
          (γ : ℝ) * ‖residual‖ - ‖yStar‖ * ‖residual‖ := by
      ring
    rw [hleft]
    exact le_trans hcombo hMain
  have hγhalf : ‖yStar‖ ≤ (γ : ℝ) / 2 := by
    linarith
  have hCoeffHalf :
      ((γ : ℝ) / 2) * ‖residual‖ ≤ numerator / (2 * ((n : ℝ) + 1)) := by
    -- The hypothesis `γ ≥ 2 ‖y*‖` leaves at least half of the support term available.
    have hhalf_le : (γ : ℝ) / 2 ≤ (γ : ℝ) - ‖yStar‖ := by
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right hhalf_le (norm_nonneg residual)) hCoeff
  have hγhalf_pos : 0 < (γ : ℝ) / 2 := by
    exact div_pos γ.2 (by norm_num)
  have hResidualBound :
      ‖residual‖ ≤ (numerator / (2 * ((n : ℝ) + 1))) / ((γ : ℝ) / 2) := by
    exact (le_div_iff₀ hγhalf_pos).2 (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hCoeffHalf)
  have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt γ.2
  have hn1_ne : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hRewrite :
      (numerator / (2 * ((n : ℝ) + 1))) / ((γ : ℝ) / 2) =
        numerator / ((γ : ℝ) * ((n : ℝ) + 1)) := by
    field_simp [hγ_ne, hn1_ne]
  rw [hRewrite] at hResidualBound
  simpa [xAvg, zAvg, residual, numerator] using hResidualBound

end

end
