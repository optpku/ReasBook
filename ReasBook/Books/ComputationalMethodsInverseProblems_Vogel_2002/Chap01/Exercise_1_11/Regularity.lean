/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Operator
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

public section

open scoped ContDiff Topology

noncomputable section

namespace Fredholm1D

/-- An `L²` class has a `C^∞` representative on `s` when some representative `g` belongs to the
class and is infinitely differentiable, `ContDiffOn ℝ ∞`, on `s`. -/
@[expose] def HasContDiffRepresentativeOn (μ : MeasureTheory.Measure ℝ) (s : Set ℝ)
    (f : MeasureTheory.Lp ℝ 2 μ) : Prop :=
  ∃ g : ℝ → ℝ, ∃ h_mem : MeasureTheory.MemLp g 2 μ,
    h_mem.toLp g = f ∧ ContDiffOn ℝ ∞ g s

/-- Membership in `HasContDiffRepresentativeOn` is exactly the existence of a
smooth representative realizing the given `L²` class. -/
theorem hasContDiffRepresentativeOn_iff (μ : MeasureTheory.Measure ℝ) (s : Set ℝ)
    (f : MeasureTheory.Lp ℝ 2 μ) :
    HasContDiffRepresentativeOn μ s f ↔
      ∃ g : ℝ → ℝ, ∃ h_mem : MeasureTheory.MemLp g 2 μ,
        h_mem.toLp g = f ∧ ContDiffOn ℝ ∞ g s := Iff.rfl

/-- The Gaussian kernel is infinitely differentiable. -/
theorem gaussianKernel_contDiff (C γ : ℝ) : ContDiff ℝ ∞ (gaussianKernel C γ) := by
  show ContDiff ℝ ∞ (fun x : ℝ => C * Real.exp (-(x ^ 2) / (2 * γ ^ 2)))
  refine (contDiff_const.mul (Real.contDiff_exp.comp ?_)).of_le (le_top)
  fun_prop

set_option maxHeartbeats 1000000 in
/-- The Gaussian blur of an `L²(0, 1)` datum is infinitely differentiable. -/
theorem gaussianBlurFunction_contDiff (C γ : ℝ)
    (z : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    ContDiff ℝ ∞ (gaussianBlurFunction C γ z) := by
  haveI := isProbabilityMeasure_unitIntervalMeasure
  have hK : ContDiff ℝ ∞ (gaussianKernel C γ) := gaussianKernel_contDiff C γ
  rw [contDiff_iff_contDiffAt]
  intro x₀
  -- Cut the Gaussian kernel off smoothly on a window that contains `x - t` for `x` near `x₀`
  -- and `t ∈ (0, 1)`; the blur then agrees with a compactly supported convolution.
  let R : ℝ := |x₀| + 2
  let ψ₀ : ContDiffBump (0 : ℝ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let ψ : ℝ → ℝ := ⇑ψ₀
  let g : ℝ → ℝ := fun s => gaussianKernel C γ s * ψ s
  have hψc : ContDiff ℝ ∞ ψ := ψ₀.contDiff (n := (⊤ : ℕ∞))
  have hg : ContDiff ℝ ∞ g := hK.mul hψc
  have hgsupp : HasCompactSupport g := ψ₀.hasCompactSupport.mul_left
  have hf : MeasureTheory.LocallyIntegrable (z : ℝ → ℝ) unitIntervalMeasure :=
    (MeasureTheory.MemLp.integrable (q := 2) (by norm_num)
      (MeasureTheory.Lp.memLp z)).locallyIntegrable
  have hconv : ContDiff ℝ ∞ (MeasureTheory.convolution (z : ℝ → ℝ) g
      (ContinuousLinearMap.mul ℝ ℝ) unitIntervalMeasure) :=
    HasCompactSupport.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := unitIntervalMeasure) hgsupp hf hg
  have hae : ∀ᵐ t ∂unitIntervalMeasure, t ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [unitIntervalMeasure]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have heq : gaussianBlurFunction C γ z
      =ᶠ[𝓝 x₀] MeasureTheory.convolution (z : ℝ → ℝ) g
        (ContinuousLinearMap.mul ℝ ℝ) unitIntervalMeasure := by
    filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    rw [gaussianBlurFunction_apply, MeasureTheory.convolution_def]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [hae] with t ht
    -- On the window the bump equals `1`, so the cutoff is invisible.
    have ht1 : |t| < 1 := by
      rw [abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hx1 : |x - x₀| < 1 := by
      rw [← Real.dist_eq]
      exact hx
    have hψ1 : ψ (x - t) = 1 := by
      show ψ₀ (x - t) = 1
      apply ContDiffBump.one_of_mem_closedBall
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      have h2 : |x₀ - t| ≤ |x₀| + |t| := by
        have hsplit : x₀ - t = x₀ + -t := by ring
        rw [hsplit]
        calc |x₀ + -t| ≤ |x₀| + |-t| := abs_add_le _ _
          _ = |x₀| + |t| := by rw [abs_neg]
      have hsplit : x - t = (x - x₀) + (x₀ - t) := by ring
      rw [hsplit]
      have h1 : |(x - x₀) + (x₀ - t)| ≤ |x - x₀| + |x₀ - t| := abs_add_le _ _
      have h3 : (0 : ℝ) ≤ |x₀| := abs_nonneg x₀
      change |(x - x₀) + (x₀ - t)| ≤ |x₀| + 2
      linarith
    show gaussianKernel C γ (x - t) * (z : ℝ → ℝ) t
        = (z : ℝ → ℝ) t * (gaussianKernel C γ (x - t) * ψ (x - t))
    rw [hψ1, mul_one]
    ring
  exact hconv.contDiffAt.congr_of_eventuallyEq heq

/-- The Gaussian `L²(0, 1)` blur has a globally smooth representative. -/
theorem gaussianBlurL2_hasSmoothRepresentative (C γ : ℝ)
    (z : MeasureTheory.Lp ℝ 2 unitIntervalMeasure) :
    HasContDiffRepresentativeOn unitIntervalMeasure Set.univ (gaussianBlurL2 C γ z) := by
  refine ⟨gaussianBlurFunction C γ z, gaussianBlurFunction_memLp C γ z, ?_, ?_⟩
  · exact (gaussianBlurL2_apply C γ z).symm
  · exact (gaussianBlurFunction_contDiff C γ z).contDiffOn

end Fredholm1D
