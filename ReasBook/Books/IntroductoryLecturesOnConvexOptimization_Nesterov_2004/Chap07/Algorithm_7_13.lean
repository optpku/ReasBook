/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Algorithm 7.13 lies in the chapter's primal prox-linear maximization domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Chap06/Theorem_6_11`, the chapter owner of affine-plus-
  regularizer objectives on a feasible subtype;
- `IsProximalLinearMaximizationOracle` in `Chap07/Definition_7_47`, the chapter owner of
  prox-linear maximization over a feasible set;
- mathlib `IsMaxOn`, the canonical maximizer owner used throughout nearby Chapter 7 files;
- `InnerProductSpace.toDualMap`, the canonical bridge from a primal vector to the corresponding
  linear functional on a real inner-product space.

Best owner abstraction:
- source-facing: the textbook stage objective from Algorithm 7.13;
- core/canonical: the stage payoff given by a linear functional minus a scaled prox term;
- bridge/view: the additive history-dependent offset recovering the displayed textbook formula.

Primitive data:
- the prescribed subgradient sequence, prox function, positive parameters `M` and `v` encoded by
  `NNRealˣ`, and
  initial point `x₀`;
- the iterate sequence `x₀, x₁, x₂, ...`;
- stagewise maximization of the canonical prox-linear payoff.

Derived API:
- the averaged stage linear functional;
- the stage prox weight;
- the history-dependent scalar offset in the textbook formula;
- maximization of the displayed source objective, obtained from the payoff by adding a constant.

The previous version stored iterate feasibility as primitive data and encoded the successor
optimality condition through `IsGreatest` on the image of the objective over `P₀`. In this domain,
the canonical owner is `IsMaxOn`, but mathlib's `IsMaxOn` does not itself record feasibility.
This refinement therefore keeps the textbook objective as a source-facing bridge, stores the
trajectory itself in the feasible subtype `P₀`, and packages the successor optimality statements
with their feasibility data rather than splitting those facts across separate fields. It also
keeps the positive algorithm parameters on the project-standard positive-real owner `NNRealˣ`
instead of carrying separate positivity proof fields.
-/

/-- The stage-`k` prox weight multiplying the prox term in Algorithm 7.13. -/
def primalUpdatePenaltyWeight (M v : NNRealˣ) (k : ℕ) : ℝ :=
  (M : ℝ) * (Real.sqrt (v : ℝ) + Real.sqrt ((k + 1 : ℕ) : ℝ)) /
    (Real.sqrt (v : ℝ) * ((k + 1 : ℕ) : ℝ))

/-- The averaged linear functional
`y ↦ (1 / (k + 1)) ∑_{i=0}^k ⟪subgradient i, y⟫`
governing the stage-`k` primal update. -/
def primalUpdateLinearFunctional (subgradient : ℕ → E) (k : ℕ) : StrongDual ℝ E :=
  InnerProductSpace.toDualMap ℝ E
    ((1 / ((k + 1 : ℕ) : ℝ)) •
      ∑ i ∈ Finset.range (k + 1), subgradient i)

/-- The canonical stage-`k` prox-linear payoff
`y ↦ ⟪c_k, y⟫ - ω_k prox(y)` whose maximizers agree with the textbook objective. -/
def primalUpdatePayoff
    (subgradient : ℕ → E) (prox : E → ℝ) (M v : NNRealˣ) (k : ℕ) (y : E) : ℝ :=
  primalUpdateLinearFunctional subgradient k y -
    primalUpdatePenaltyWeight M v k * prox y

/-- The history-dependent additive offset in the textbook objective. Since it does not depend on
the optimization variable `y`, it does not affect the maximizing set. -/
def primalUpdateOffset
    (subgradient : ℕ → E) (prox : E → ℝ) (M v : NNRealˣ) (x0 : E)
    (trajectory : ℕ → E) (k : ℕ) : ℝ :=
  primalUpdatePenaltyWeight M v k * prox x0 -
    (1 / ((k + 1 : ℕ) : ℝ)) *
      ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (trajectory i)

/-- The stage-`k` objective maximized by the primal update scheme from the prescribed subgradients
`subgradient i = ∇f(x_i)` and prox-function `prox`. -/
def primalUpdateObjective
    (subgradient : ℕ → E) (prox : E → ℝ) (M v : NNRealˣ) (x0 : E)
    (trajectory : ℕ → E) (k : ℕ) (y : E) : ℝ :=
  primalUpdatePayoff subgradient prox M v k y +
    primalUpdateOffset subgradient prox M v x0 trajectory k

/-- The primal-update objective is exactly the average linearized gain minus the scaled prox
displacement term from the textbook formula. -/
theorem primalUpdateObjective_def
    (subgradient : ℕ → E) (prox : E → ℝ) (M v : NNRealˣ) (x0 : E)
    (trajectory : ℕ → E) (k : ℕ) (y : E) :
    primalUpdateObjective subgradient prox M v x0 trajectory k y =
      (1 / ((k + 1 : ℕ) : ℝ)) *
          (∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (y - trajectory i)) -
        primalUpdatePenaltyWeight M v k * (prox y - prox x0) := by
  calc
    primalUpdateObjective subgradient prox M v x0 trajectory k y
        = (1 / ((k + 1 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) y -
          primalUpdatePenaltyWeight M v k * prox y +
            (primalUpdatePenaltyWeight M v k * prox x0 -
              (1 / ((k + 1 : ℕ) : ℝ)) *
                ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (trajectory i)) := by
          simp [primalUpdateObjective, primalUpdatePayoff, primalUpdateOffset,
            primalUpdateLinearFunctional]
    _ = ((1 / ((k + 1 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) y -
          (1 / ((k + 1 : ℕ) : ℝ)) *
            ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (trajectory i)) -
          (primalUpdatePenaltyWeight M v k * prox y -
            primalUpdatePenaltyWeight M v k * prox x0) := by
          ring
    _ = (1 / ((k + 1 : ℕ) : ℝ)) *
          ((∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) y) -
            ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (trajectory i)) -
          primalUpdatePenaltyWeight M v k * (prox y - prox x0) := by
          rw [← mul_sub, ← mul_sub]
    _ = (1 / ((k + 1 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.range (k + 1),
            (inner ℝ (subgradient i) y - inner ℝ (subgradient i) (trajectory i)) -
          primalUpdatePenaltyWeight M v k * (prox y - prox x0) := by
          rw [← Finset.sum_sub_distrib]
    _ = (1 / ((k + 1 : ℕ) : ℝ)) *
          ∑ i ∈ Finset.range (k + 1), inner ℝ (subgradient i) (y - trajectory i) -
          primalUpdatePenaltyWeight M v k * (prox y - prox x0) := by
          congr 2
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (inner_sub_right (subgradient i) y (trajectory i)).symm

/-- Algorithm 7.13: a primal update scheme on `P₀` with prescribed subgradients
`subgradient i = ∇f(x_i)`, prox-function `prox`, positive parameters `M` and `v`, and initial
point `x₀ = x0` is a sequence `x_k` in `P₀` with `x₀ = x0` such that, for every `k ≥ 0`,
`x_{k+1}` maximizes the canonical prox-linear stage payoff, equivalently the textbook objective. -/
structure PrimalUpdateScheme
    (P0 : Set E) (subgradient : ℕ → E) (prox : E → ℝ)
    (M v : NNRealˣ) (x0 : E) where
  /-- The feasible iterate sequence generated by the primal-update rule. -/
  x : ℕ → P0
  /-- The zeroth iterate is the prescribed initial point `x₀`. -/
  x_zero : (x 0 : E) = x0
  /-- Each successor iterate maximizes the canonical stage-`k` prox-linear payoff over `P₀`. -/
  step_isMax :
    ∀ k : ℕ, IsMaxOn (primalUpdatePayoff subgradient prox M v k) P0 (x (k + 1) : E)

namespace PrimalUpdateScheme

/-- A primal update scheme can be used as its underlying iterate sequence `x_k`. -/
instance
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E} :
    CoeFun (PrimalUpdateScheme P0 subgradient prox M v x0) (fun _ ↦ ℕ → E) where
  coe scheme k := scheme.x k

/-- The prescribed initial point belongs to the feasible set `P₀`. -/
theorem x0_mem
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) :
    x0 ∈ P0 := by
  simpa [scheme.x_zero] using (scheme.x 0).property

/-- Every iterate of a primal update scheme belongs to the feasible set `P₀`. -/
theorem x_mem
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) (k : ℕ) :
    (scheme.x k : E) ∈ P0 := by
  exact (scheme.x k).property

/-- Every successor iterate belongs to the feasible set `P₀`. -/
theorem iterates_succ_mem
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) (k : ℕ) :
    (scheme.x (k + 1) : E) ∈ P0 :=
  scheme.x_mem (k + 1)

/-- Each successor iterate is a feasible maximizer of the canonical stage-`k` payoff. -/
theorem step_mem_isMaxOn
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) (k : ℕ) :
    scheme (k + 1) ∈ P0 ∧
      IsMaxOn (primalUpdatePayoff subgradient prox M v k) P0 (scheme (k + 1)) :=
  ⟨scheme.x_mem (k + 1), scheme.step_isMax k⟩

/-- Each successor iterate also maximizes the source-facing textbook objective, since that
objective differs from the canonical payoff only by an additive constant. -/
theorem step_mem_isMaxOn_objective
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) (k : ℕ) :
    scheme (k + 1) ∈ P0 ∧
      IsMaxOn
        (primalUpdateObjective subgradient prox M v x0 scheme k)
        P0
        (scheme (k + 1)) := by
  have hconst :
      IsMaxOn
        (fun _ : E ↦ primalUpdateOffset subgradient prox M v x0 scheme k)
        P0
        (scheme (k + 1)) :=
    isMaxOn_const
  refine ⟨scheme.x_mem (k + 1), ?_⟩
  simpa [primalUpdateObjective, add_comm, add_left_comm, add_assoc] using
    (scheme.step_isMax k).add hconst

/-- Each successor iterate maximizes the source-facing textbook objective over `P₀`. -/
theorem step_isMaxOn_objective
    {P0 : Set E} {subgradient : ℕ → E} {prox : E → ℝ}
    {M v : NNRealˣ} {x0 : E}
    (scheme : PrimalUpdateScheme P0 subgradient prox M v x0) (k : ℕ) :
    IsMaxOn
      (primalUpdateObjective subgradient prox M v x0 scheme k)
      P0
      (scheme (k + 1)) :=
  (scheme.step_mem_isMaxOn_objective k).2

end PrimalUpdateScheme

end
