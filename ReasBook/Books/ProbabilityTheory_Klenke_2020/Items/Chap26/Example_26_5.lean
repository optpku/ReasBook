/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

noncomputable section

namespace ProbabilityTheory

local notation "PathSpace" => BrownianPathSpace
local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

/- Domain-style sampling for Example 26.5:
* primary domain: one-dimensional pathwise Ornstein--Uhlenbeck formulas driven by continuous paths;
* sampled owner declarations in this domain: `pathwiseItoIntegralAlong` and
  `dyadicPartitionSequence`;
* owner abstraction: the source-facing stochastic convolution is written through the canonical
  dyadic pathwise Itô integral from Chapter 25;
* primitive data: the scalar drift coefficient `b`, diffusion coefficient `σ`, initial value `ξ`,
  and the driving path `w`;
* derived API: the deterministic kernel, the stochastic convolution term, and the displayed
  variation-of-constants path formula. -/

/-- Helper for Example 26.5: the deterministic Ornstein--Uhlenbeck kernel
`s ↦ exp (b (t - s))` at the fixed horizon `t`. -/
def ornsteinUhlenbeckKernel (b : ℝ) (t : NNReal) : NNReal → ℝ :=
  fun s ↦ Real.exp (b * ((t : ℝ) - s))

-- Proof comment: this is just the defining evaluation of the deterministic exponential kernel.
/-- Helper for Example 26.5: evaluating the Ornstein--Uhlenbeck kernel gives
`exp (b (t - s))`. -/
theorem ornsteinUhlenbeckKernel_apply (b : ℝ) (t s : NNReal) :
    ornsteinUhlenbeckKernel b t s = Real.exp (b * ((t : ℝ) - s)) :=
  rfl

/-- Helper for Example 26.5: the source-facing stochastic convolution term
`σ ∫₀ᵗ exp (b (t - s)) dw(s)` written with the canonical dyadic pathwise Itô integral. -/
def ornsteinUhlenbeckStochasticConvolution (σ b : ℝ) (w : PathSpace) : NNReal → ℝ :=
  fun t ↦
    σ * pathwiseItoIntegralAlong (ornsteinUhlenbeckKernel b t) w dyadicPartitionSequence t

-- Proof comment: unfold the stochastic convolution to expose the scalar kernel inside the canonical
-- dyadic pathwise Itô integral.
/-- Helper for Example 26.5: evaluating the stochastic convolution at time `t` gives the displayed
scalar pathwise integral term. -/
theorem ornsteinUhlenbeckStochasticConvolution_apply
    (σ b : ℝ) (w : PathSpace) (t : NNReal) :
    ornsteinUhlenbeckStochasticConvolution σ b w t =
      σ * pathwiseItoIntegralAlong (ornsteinUhlenbeckKernel b t) w dyadicPartitionSequence t :=
  rfl

/-- Helper for Example 26.5: the source-facing Ornstein--Uhlenbeck path formula started from `ξ`
and driven by the continuous path `w`. -/
def ornsteinUhlenbeckSolutionPath (ξ σ b : ℝ) (w : PathSpace) : NNReal → ℝ :=
  fun t ↦ Real.exp (b * (t : ℝ)) * ξ + ornsteinUhlenbeckStochasticConvolution σ b w t

-- Proof comment: expand the two named ingredients to recover the displayed variation-of-constants
-- expression.
/-- Example 26.5: evaluating the Ornstein--Uhlenbeck source-facing path formula gives
`e^{b t} ξ + σ ∫₀ᵗ e^{b (t - s)} dw(s)`, with the stochastic integral formalized by the canonical
dyadic pathwise Itô integral from Chapter 25. -/
theorem ornsteinUhlenbeckProcess_isStrongSolution
    (ξ σ b : ℝ) (w : PathSpace) (t : NNReal) :
    ornsteinUhlenbeckSolutionPath ξ σ b w t =
      Real.exp (b * (t : ℝ)) * ξ +
        σ * pathwiseItoIntegralAlong (ornsteinUhlenbeckKernel b t) w dyadicPartitionSequence t := by
  rw [ornsteinUhlenbeckSolutionPath, ornsteinUhlenbeckStochasticConvolution_apply]

end ProbabilityTheory
