/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_5_9

noncomputable section

open Filter
open scoped Topology

section NegativeCurvatureDirectionMethod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- This item reuses the Chapter 3 quadratic search-path owner and adds the
-- stagewise conditions `(3.5.50)`-`(3.5.52)` attached to that path.

/-- The derivative of the second-order search path paired with `gradient f` at the point
`negativeCurvatureSearchPath x s d a`. -/
def negativeCurvaturePathSlope (f : E → ℝ) (x s d : E) (a : ℝ) : ℝ :=
  inner ℝ (d + (2 * a) • s) (gradient f (negativeCurvatureSearchPath x s d a))

/-- The initial quadratic coefficient `2 g_kᵀ s_k + d_kᵀ G_k d_k` appearing in the
second-order Taylor model for the negative curvature search path. -/
def negativeCurvatureInitialCurvature (f : E → ℝ) (x s d : E) : ℝ :=
  2 * inner ℝ s (gradient f x) + hessianQuadraticAt f x d

/-- A source-faithful statement-stage encoding of the step conditions
`(3.5.50)`-`(3.5.52)` for the negative curvature direction method. -/
structure IsNegativeCurvatureDirectionSequenceOn
    (f : E → ℝ) (D : Set E) (x₀ : E) (x s d : ℕ → E) (α : ℕ → ℝ)
    (ρ σ : ℝ) : Prop where
  start_eq : x 0 = x₀
  mem_domain : ∀ k, x k ∈ D
  rho_mem_Ioo : ρ ∈ Set.Ioo (0 : ℝ) (1 / 2)
  sigma_mem_Ioo : σ ∈ Set.Ioo (0 : ℝ) 1
  step_size_pos : ∀ k, 0 < α k
  step_eq : ∀ k, x (k + 1) = negativeCurvatureSearchPath (x k) (s k) (d k) (α k)
  descent_pair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)
  sufficient_decrease :
    ∀ k,
      f (x (k + 1)) ≤
        f (x k) +
          (ρ / 2) * (α k) ^ (2 : ℕ) *
            negativeCurvatureInitialCurvature f (x k) (s k) (d k)
  curvature_condition :
    ∀ k,
      σ * (inner ℝ (d k) (gradient f (x k)) +
          α k * negativeCurvatureInitialCurvature f (x k) (s k) (d k)) ≤
        negativeCurvaturePathSlope f (x k) (s k) (d k) (α k)

/-- Chapter03 Theorem 3.5.10 (1): if the negative curvature direction iterates stay in a
compact level set and satisfy the step conditions `(3.5.50)`-`(3.5.52)`, then
`g_kᵀ s_k ⟶ 0`. -/
theorem negativeCurvatureDirection_firstOrderPairing_tendsto_zero
    {D : Set E} {f : E → ℝ} {x₀ : E} {x s d : ℕ → E} {α : ℕ → ℝ}
    {ρ σ : ℝ}
    (hD : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelCompact : IsCompact {y : E | y ∈ D ∧ f y ≤ f x₀})
    (hSeq : IsNegativeCurvatureDirectionSequenceOn f D x₀ x s d α ρ σ) :
    Tendsto (fun k ↦ inner ℝ (s k) (gradient f (x k))) atTop (𝓝 0) := sorry

/-- Chapter03 Theorem 3.5.10 (2): under the same hypotheses,
`d_kᵀ G_k d_k ⟶ 0`, written canonically as
`hessianQuadraticAt f (x_k) d_k ⟶ 0`. -/
theorem negativeCurvatureDirection_hessianQuadratic_tendsto_zero
    {D : Set E} {f : E → ℝ} {x₀ : E} {x s d : ℕ → E} {α : ℕ → ℝ}
    {ρ σ : ℝ}
    (hD : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelCompact : IsCompact {y : E | y ∈ D ∧ f y ≤ f x₀})
    (hSeq : IsNegativeCurvatureDirectionSequenceOn f D x₀ x s d α ρ σ) :
    Tendsto (fun k ↦ hessianQuadraticAt f (x k) (d k)) atTop (𝓝 0) := sorry

end NegativeCurvatureDirectionMethod
