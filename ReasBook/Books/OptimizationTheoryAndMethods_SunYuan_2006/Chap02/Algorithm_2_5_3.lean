/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]

-- Domain sampling:
-- * source-facing: the Step-3 acceptance alternative and the iterate/update data of
--   Algorithm 2.5.3;
-- * core/canonical: the chapter owners `HasGradientVectorAt`, `lineSearchObjective`,
--   `GoldsteinCondition`, `WolfePowellParameters`, and the mathlib gradient owner `∇`;
-- * bridge/view: `inexactLineSearchAcceptance_iff`, which expands the canonical Step-3 owner
--   back to the textbook inequalities on `f (xk + αk • dk)`.

/-- An accepted inexact line-search step from `xk` along `dk` with steplength `αk`.

The Goldstein branch is recorded through the chapter owner `GoldsteinCondition` for the search
profile `lineSearchObjective f xk dk` and the initial slope datum `inner ℝ gk dk`. The
Wolfe-Powell branch reuses the canonical parameter owner `WolfePowellParameters` together with
the sufficient-decrease and curvature inequalities involving the current gradient `gk` and the
next gradient `gNext`. -/
def InexactLineSearchAcceptance
    (f : Point → ℝ)
    (xk gk gNext dk : Point)
  (αk : ℝ) : Prop :=
  (∃ ρ : ℝ,
      GoldsteinCondition
        (lineSearchObjective f xk dk)
        (inner ℝ gk dk)
        ρ αk) ∨
    (∃ ρ σ : ℝ,
      WolfePowellParameters ρ σ ∧
        0 < αk ∧
        lineSearchObjective f xk dk αk ≤
          lineSearchObjective f xk dk 0 + ρ * αk * inner ℝ gk dk ∧
        σ * inner ℝ gk dk ≤ inner ℝ gNext dk)

/-- Expanding `InexactLineSearchAcceptance` gives exactly the explicit Goldstein-rule
or Wolfe-Powell-rule Step 3 alternative from Chapter02 Algorithm 2.5.3. -/
theorem inexactLineSearchAcceptance_iff
    {f : Point → ℝ}
    {xk gk gNext dk : Point}
    {αk : ℝ} :
    InexactLineSearchAcceptance f xk gk gNext dk αk ↔
      (∃ ρ : ℝ,
        0 < ρ ∧
        ρ < 1 / 2 ∧
        0 < αk ∧
        f (xk + αk • dk) ≤ f xk + ρ * αk * inner ℝ gk dk ∧
        f xk + (1 - ρ) * αk * inner ℝ gk dk ≤ f (xk + αk • dk)) ∨
      (∃ ρ σ : ℝ,
        0 < ρ ∧
        ρ < σ ∧
        σ < 1 ∧
        0 < αk ∧
        f (xk + αk • dk) ≤ f xk + ρ * αk * inner ℝ gk dk ∧
        σ * inner ℝ gk dk ≤ inner ℝ gNext dk) := by
  constructor
  · intro h_accept
    rcases h_accept with h_goldstein | h_wolfe
    · rcases h_goldstein with ⟨ρ, hρ⟩
      rcases goldsteinCondition_iff.mp hρ with ⟨h_parameters, hα, h_upper, h_lower⟩
      rcases goldsteinParameters_iff.mp h_parameters with ⟨hρ_pos, hρ_lt⟩
      left
      refine ⟨ρ, hρ_pos, hρ_lt, hα, ?_, ?_⟩
      · simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_upper
      · simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_lower
    · rcases h_wolfe with ⟨ρ, σ, h_parameters, hα, h_decrease, h_curvature⟩
      rcases wolfePowellParameters_iff.mp h_parameters with ⟨hρ_pos, hρ_lt_sigma, hσ_lt⟩
      right
      refine ⟨ρ, σ, hρ_pos, hρ_lt_sigma, hσ_lt, hα, ?_, h_curvature⟩
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_decrease
  · rintro (⟨ρ, hρ_pos, hρ_lt, hα, h_upper, h_lower⟩ |
      ⟨ρ, σ, hρ_pos, hρ_lt_sigma, hσ_lt, hα, h_decrease, h_curvature⟩)
    · left
      refine ⟨ρ, goldsteinCondition_iff.mpr ?_⟩
      refine ⟨goldsteinParameters_iff.mpr ⟨hρ_pos, hρ_lt⟩, hα, ?_, ?_⟩
      · simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_upper
      · simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_lower
    · right
      refine ⟨ρ, σ, wolfePowellParameters_iff.mpr ⟨hρ_pos, hρ_lt_sigma, hσ_lt⟩,
        hα, ?_, h_curvature⟩
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_decrease

end

section

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
variable {f : Point → ℝ}

/-- Chapter02 Algorithm 2.5.3 reuses the Chapter 1 gradient-vector owner
`HasGradientVectorAt`; on a complete inner-product space this is exactly mathlib's
`HasGradientAt`. -/
theorem hasGradientVectorAt_iff_hasGradientAt
    [CompleteSpace Point]
    {g x : Point} :
    HasGradientVectorAt f g x ↔ HasGradientAt f g x := by
  simpa using
    (hasGradientAt_iff_hasGradientVectorAt :
      HasGradientAt f g x ↔ HasGradientVectorAt f g x).symm

/-- Chapter02 Algorithm 2.5.3: a general inexact-line-search method for unconstrained
optimization on a real inner-product space `Point` starts from `x0`, uses a tolerance
`0 ≤ ε`, and records a chosen gradient field `g` for `f` along the iterates. At each
iterate `x k`, it stops when `‖g (x k)‖ ≤ ε`. If `ε < ‖g (x k)‖`, the method chooses
a descent direction `d k`, selects a positive steplength `α k` by either the Goldstein
rule or the Wolfe-Powell rule, and updates by `x (k + 1) = x k + α k • d k`. -/
structure InexactLineSearchMethod (f : Point → ℝ) (g : Point → Point) where
  ε : ℝ
  x0 : Point
  x : ℕ → Point
  d : ℕ → Point
  α : ℕ → ℝ
  epsilon_nonneg : 0 ≤ ε
  x_zero : x 0 = x0
  gradientAt : ∀ k : ℕ, HasGradientVectorAt f (g (x k)) (x k)
  descentDirection :
    ∀ k : ℕ, ε < ‖g (x k)‖ → inner ℝ (g (x k)) (d k) < 0
  lineSearch :
    ∀ k : ℕ, ε < ‖g (x k)‖ →
      InexactLineSearchAcceptance f (x k) (g (x k)) (g (x (k + 1))) (d k) (α k)
  update :
    ∀ k : ℕ, ε < ‖g (x k)‖ → x (k + 1) = x k + α k • d k

/-- An inexact line-search method can be used as its sequence of iterates. -/
instance {g : Point → Point} : CoeFun (InexactLineSearchMethod f g) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace InexactLineSearchMethod

/-- Evaluating an inexact line-search method as a function returns its iterate sequence. -/
theorem coe_apply {g : Point → Point} (A : InexactLineSearchMethod f g) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The stopping condition of Chapter02 Algorithm 2.5.3 at the iterate `x k`. -/
def terminatedAt {g : Point → Point} (A : InexactLineSearchMethod f g) (k : ℕ) : Prop :=
  ‖g (A k)‖ ≤ A.ε

/-- Unfolding `terminatedAt` gives the gradient-norm stopping test at the current iterate
`x k`. -/
theorem terminatedAt_iff {g : Point → Point} (A : InexactLineSearchMethod f g) (k : ℕ) :
    A.terminatedAt k ↔ ‖g (A k)‖ ≤ A.ε :=
  Iff.rfl

/-- When Chapter02 Algorithm 2.5.3 continues at step `k`, it has a descent direction,
an accepted inexact line-search step, and the standard iterate update. -/
theorem step {g : Point → Point} (A : InexactLineSearchMethod f g) (k : ℕ)
    (h_continue : A.ε < ‖g (A k)‖) :
    inner ℝ (g (A k)) (A.d k) < 0 ∧
      InexactLineSearchAcceptance
        f (A k) (g (A k)) (g (A (k + 1))) (A.d k) (A.α k) ∧
      A (k + 1) = A k + A.α k • A.d k :=
  ⟨A.descentDirection k h_continue, A.lineSearch k h_continue, A.update k h_continue⟩

/-- Unfolding the accepted Step 3 condition in `step` recovers the explicit Goldstein-rule
or Wolfe-Powell-rule alternative. -/
theorem stepSpec {g : Point → Point} (A : InexactLineSearchMethod f g) (k : ℕ)
    (h_continue : A.ε < ‖g (A k)‖) :
    inner ℝ (g (A k)) (A.d k) < 0 ∧
      ((∃ ρ : ℝ,
          0 < ρ ∧
          ρ < 1 / 2 ∧
          0 < A.α k ∧
          f (A k + A.α k • A.d k) ≤ f (A k) + ρ * A.α k * inner ℝ (g (A k)) (A.d k) ∧
          f (A k) + (1 - ρ) * A.α k * inner ℝ (g (A k)) (A.d k) ≤
            f (A k + A.α k • A.d k)) ∨
        (∃ ρ σ : ℝ,
          0 < ρ ∧
          ρ < σ ∧
          σ < 1 ∧
          0 < A.α k ∧
          f (A k + A.α k • A.d k) ≤ f (A k) + ρ * A.α k * inner ℝ (g (A k)) (A.d k) ∧
          σ * inner ℝ (g (A k)) (A.d k) ≤ inner ℝ (g (A (k + 1))) (A.d k))) ∧
      A (k + 1) = A k + A.α k • A.d k := by
  rcases A.step k h_continue with ⟨h_desc, h_accept, h_update⟩
  exact ⟨h_desc, (inexactLineSearchAcceptance_iff.mp h_accept), h_update⟩

end InexactLineSearchMethod

end
