/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Theorem_16_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Exercise 16.1.3: the Laplace kernel `y ↦ exp (-t y)` decreases in the spatial
variable on `NNReal`. -/
private lemma laplaceKernel_antitone (t : NNReal) :
    Antitone (fun y : NNReal ↦ Real.exp (-((t : ℝ) * (y : ℝ)))) := by
  intro y z hyz
  -- Proof comment: the exponent is affine with nonpositive slope `-t`.
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hyz' : (y : ℝ) ≤ (z : ℝ) := by exact_mod_cast hyz
  nlinarith

/-- Helper for Exercise 16.1.3: the Laplace kernel is integrable against every probability law on
`[0, ∞)`. -/
private lemma integrableLaplaceKernel (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    Integrable (fun y : NNReal ↦ Real.exp (-((t : ℝ) * (y : ℝ)))) (μ : Measure NNReal) := by
  -- Proof comment: the exponential kernel is bounded by the constant function `1`.
  refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
  filter_upwards with y
  have hnonneg : 0 ≤ Real.exp (-((t : ℝ) * (y : ℝ))) := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  refine Real.exp_le_one_iff.mpr ?_
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hy : 0 ≤ (y : ℝ) := by exact_mod_cast y.2
  nlinarith

/-- Helper for Exercise 16.1.3: the ordinary Laplace transform of a probability law on `NNReal`
is strictly positive. -/
private lemma laplaceIntegral_pos (μ : ProbabilityMeasure NNReal) (t : NNReal) :
    0 < ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) := by
  -- Proof comment: positivity of the exponential kernel and nontriviality of a probability
  -- measure force the integral to be positive.
  simpa using
    (MeasureTheory.integral_exp_pos
      (μ := (μ : Measure NNReal))
      (f := fun y : NNReal ↦ -((t : ℝ) * (y : ℝ)))
      (integrableLaplaceKernel μ t))

/-- Helper for Exercise 16.1.3: exponentiating the Lévy--Khinchin identity recovers the raw
Laplace integral. -/
private lemma laplaceIntegral_eq_exp_neg_levyKhinchinExponent
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) (t : NNReal) :
    (∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal)) =
      Real.exp (-(((α : ℝ) * (t : ℝ)) +
        ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν)) := by
  rcases hrep with ⟨_, _, hlog⟩
  -- Proof comment: unfold the log-Laplace transform once and cancel `exp` with `log`.
  calc
    ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) =
        Real.exp (-μ.logLaplaceTransform t) := by
          rw [logLaplaceTransform, neg_neg]
          exact (Real.exp_log (laplaceIntegral_pos μ t)).symm
    _ = Real.exp (-(((α : ℝ) * (t : ℝ)) +
        ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν)) := by
          rw [hlog t]

/-- Helper for Exercise 16.1.3: the divided Bernstein kernel at time `n + 1` is dominated by
`2 * min (1, y)`. -/
private lemma bernsteinKernel_div_nat_norm_le_twoMin (n : ℕ) (y : NNReal) :
    ‖(1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ)‖ ≤
      2 * min (1 : ℝ) (y : ℝ) := by
  let d : ℝ := ((n + 1 : ℕ) : ℝ)
  have hd_pos : 0 < d := by
    dsimp [d]
    positivity
  have hd_ge_one : (1 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hExpLeOne : Real.exp (-(d * (y : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have hy : 0 ≤ (y : ℝ) := by exact_mod_cast y.2
    nlinarith
  have hNumNonneg : 0 ≤ 1 - Real.exp (-(d * (y : ℝ))) := by
    linarith
  have hNonneg : 0 ≤ (1 - Real.exp (-(d * (y : ℝ)))) / d := by
    exact div_nonneg hNumNonneg hd_pos.le
  rw [Real.norm_of_nonneg hNonneg]
  by_cases hy : (y : ℝ) ≤ 1
  · rw [min_eq_right hy]
    have hLeY : (1 - Real.exp (-(d * (y : ℝ)))) / d ≤ (y : ℝ) := by
      have hAux : 1 - Real.exp (-(d * (y : ℝ))) ≤ d * (y : ℝ) := by
        have hOneSub : 1 - d * (y : ℝ) ≤ Real.exp (-(d * (y : ℝ))) := by
          simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-(d * (y : ℝ)))
        linarith
      exact (div_le_iff₀ hd_pos).2 <| by simpa [mul_comm, mul_left_comm, mul_assoc] using hAux
    linarith
  · have hy' : 1 ≤ (y : ℝ) := by linarith
    rw [min_eq_left hy']
    have hNumLeOne : 1 - Real.exp (-(d * (y : ℝ))) ≤ 1 := by
      have hExpPos : 0 < Real.exp (-(d * (y : ℝ))) := Real.exp_pos _
      linarith
    have hLeOne : (1 - Real.exp (-(d * (y : ℝ)))) / d ≤ 1 := by
      exact (div_le_iff₀ hd_pos).2 <| by
        simpa using le_trans hNumLeOne hd_ge_one
    linarith

/-- Helper for Exercise 16.1.3: for fixed `y`, the divided Bernstein kernel at time `n + 1`
tends to `0`. -/
private lemma tendsto_bernsteinKernel_div_nat_atTop (y : NNReal) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) := by
  have hUpper :
      ∀ n : ℕ,
        ‖(1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ)‖ ≤
          1 / ((n + 1 : ℕ) : ℝ) := by
    intro n
    have hden_pos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hExpLeOne : Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hy : 0 ≤ (y : ℝ) := by exact_mod_cast y.2
      nlinarith
    have hNumNonneg :
        0 ≤ 1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ))) := by
      linarith
    have hNumLeOne :
        1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ))) ≤ 1 := by
      have hExpPos : 0 < Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ))) := by
        exact Real.exp_pos _
      linarith
    have hNonneg :
        0 ≤
          (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) /
            ((n + 1 : ℕ) : ℝ) := div_nonneg hNumNonneg hden_pos.le
    rw [Real.norm_of_nonneg hNonneg]
    have hmul : (1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = 1 := by
      field_simp [hden_pos.ne']
    have hTarget :
        1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ))) ≤
          (1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) := by
      rw [hmul]
      exact hNumLeOne
    exact (div_le_iff₀ hden_pos).2 hTarget
  have hOneDiv :
      Filter.Tendsto
        (fun n : ℕ ↦ (1 / ((n + 1 : ℕ) : ℝ))) Filter.atTop (nhds (0 : ℝ)) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) Filter.atTop (nhds (0 : ℝ)))
  exact squeeze_zero_norm hUpper hOneDiv

/-- Helper for Exercise 16.1.3: the jump term divided by `n + 1` tends to `0`. -/
private lemma bernsteinJumpTerm_div_nat_tendsto_zero
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (∫ y : NNReal,
          (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ) ∂ν))
      Filter.atTop (nhds 0) := by
  rcases hrep with ⟨_, hInt, _⟩
  have hMeas :
      ∀ n,
        AEStronglyMeasurable
          (fun y : NNReal ↦
            (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ))
          ν := by
    intro n
    fun_prop
  have hBound :
      ∀ n,
        ∀ᵐ y : NNReal ∂ν,
          ‖(1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ)‖ ≤
            2 * min (1 : ℝ) (y : ℝ) := by
    intro n
    exact Filter.Eventually.of_forall fun y : NNReal ↦
      bernsteinKernel_div_nat_norm_le_twoMin n y
  have hLim :
      ∀ᵐ y : NNReal ∂ν,
        Filter.Tendsto
          (fun n ↦
            (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ))
          Filter.atTop (nhds 0) := by
    exact Filter.Eventually.of_forall fun y : NNReal ↦
      tendsto_bernsteinKernel_div_nat_atTop y
  -- Proof comment: dominated convergence turns the pointwise `1 / (n + 1)` decay into an
  -- asymptotic statement for the integrated jump term.
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := ν) (bound := fun y : NNReal ↦ 2 * min (1 : ℝ) (y : ℝ))
      hMeas (hInt.const_mul 2) hBound hLim

/-- Helper for Exercise 16.1.3: the Bernstein kernel `y ↦ 1 - exp (-(t y))` is controlled by the
truncated first-moment kernel up to the scalar factor `t + 1`. -/
private lemma jumpKernel_abs_le_scaledMin (t y : NNReal) :
    |1 - Real.exp (-((t : ℝ) * (y : ℝ)))| ≤
      ((t : ℝ) + 1) * min (1 : ℝ) (y : ℝ) := by
  -- Proof comment: on `[0, 1]`, the bound `1 - exp (-u) ≤ u` is enough, while on `[1, ∞)` the
  -- kernel is bounded by `1`.
  have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (y : ℝ))) := by
    refine sub_nonneg.mpr ?_
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith [show 0 ≤ (t : ℝ) by positivity, show 0 ≤ (y : ℝ) by exact_mod_cast y.2]
  rw [abs_of_nonneg hnonneg]
  by_cases hy : (y : ℝ) ≤ 1
  · rw [min_eq_right hy]
    have hlin : 1 - Real.exp (-((t : ℝ) * (y : ℝ))) ≤ (t : ℝ) * (y : ℝ) := by
      have hExp := Real.add_one_le_exp (-((t : ℝ) * (y : ℝ)))
      linarith
    calc
      1 - Real.exp (-((t : ℝ) * (y : ℝ))) ≤ (t : ℝ) * (y : ℝ) := hlin
      _ ≤ ((t : ℝ) + 1) * (y : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ ?_
        · linarith
        · exact_mod_cast y.2
  · have hy' : 1 ≤ (y : ℝ) := by linarith
    rw [min_eq_left hy']
    calc
      1 - Real.exp (-((t : ℝ) * (y : ℝ))) ≤ 1 := by
        linarith [show 0 ≤ Real.exp (-((t : ℝ) * (y : ℝ))) from (Real.exp_pos _).le]
      _ ≤ (t : ℝ) + 1 := by
        linarith [show 0 ≤ (t : ℝ) by positivity]
      _ = ((t : ℝ) + 1) * 1 := by ring

/-- Helper for Exercise 16.1.3: the Bernstein jump kernel is integrable under the
Lévy--Khinchin truncated first-moment hypothesis. -/
private lemma integrableJumpKernel
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) (t : NNReal) :
    Integrable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ν := by
  rcases hrep with ⟨_, hInt, _⟩
  -- Proof comment: the local jump kernel is dominated by the integrable truncation majorant.
  refine (hInt.const_mul ((t : ℝ) + 1)).mono' (by fun_prop) ?_
  filter_upwards with y
  simpa [Real.norm_eq_abs] using jumpKernel_abs_le_scaledMin t y

/-- Helper for Exercise 16.1.3: the mass of `Set.Iio x` contributes at least the constant kernel
value `exp (-t x)` times that mass to the Laplace integral. -/
private lemma laplaceIntegral_lowerBound_on_Iio
    {μ : ProbabilityMeasure NNReal} {x t : NNReal} :
    ((μ : Measure NNReal) (Set.Iio x)).toReal * Real.exp (-((t : ℝ) * (x : ℝ))) ≤
      ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) := by
  let c : ℝ := Real.exp (-((t : ℝ) * (x : ℝ)))
  have hIntKernel := integrableLaplaceKernel μ t
  have hIntIndicator :
      Integrable (Set.indicator (Set.Iio x) (fun _ : NNReal ↦ c)) (μ : Measure NNReal) := by
    exact (integrable_const c).indicator measurableSet_Iio
  have hIndicatorLe :
      ∀ᵐ y ∂(μ : Measure NNReal),
        Set.indicator (Set.Iio x) (fun _ : NNReal ↦ c) y ≤
          Real.exp (-((t : ℝ) * (y : ℝ))) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    by_cases hy : y < x
    · have hExp :
          -((t : ℝ) * (x : ℝ)) ≤ -((t : ℝ) * (y : ℝ)) := by
        have hy' : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hy.le
        nlinarith [show 0 ≤ (t : ℝ) by positivity]
      have hle : c ≤ Real.exp (-((t : ℝ) * (y : ℝ))) := by
        exact Real.exp_le_exp.mpr hExp
      simpa [Set.indicator, hy, c] using hle
    · have hnonneg : 0 ≤ Real.exp (-((t : ℝ) * (y : ℝ))) := (Real.exp_pos _).le
      simpa [Set.indicator, hy, c] using hnonneg
  -- Proof comment: compare the constant kernel on `Set.Iio x` with the full Laplace kernel
  -- pointwise, then integrate the inequality.
  calc
    ((μ : Measure NNReal) (Set.Iio x)).toReal * c =
        ∫ y, Set.indicator (Set.Iio x) (fun _ : NNReal ↦ c) y ∂(μ : Measure NNReal) := by
          change (μ : Measure NNReal).real (Set.Iio x) • c =
              ∫ y, Set.indicator (Set.Iio x) (fun _ : NNReal ↦ c) y ∂(μ : Measure NNReal)
          exact (MeasureTheory.integral_indicator_const
            (μ := (μ : Measure NNReal)) c measurableSet_Iio).symm
    _ ≤ ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) := by
          exact MeasureTheory.integral_mono_ae hIntIndicator hIntKernel hIndicatorLe

/-- Helper for Exercise 16.1.3: if `μ (Set.Iio x) = 0`, then the Laplace kernel is bounded above
by its value at `x` almost everywhere. -/
private lemma laplaceIntegral_upperBound_of_Iio_eq_zero
    {μ : ProbabilityMeasure NNReal} {x t : NNReal}
    (hzero : (μ : Measure NNReal) (Set.Iio x) = 0) :
    ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) ≤
      Real.exp (-((t : ℝ) * (x : ℝ))) := by
  let c : ℝ := Real.exp (-((t : ℝ) * (x : ℝ)))
  have hIntKernel := integrableLaplaceKernel μ t
  have hIntConst : Integrable (fun _ : NNReal ↦ c) (μ : Measure NNReal) := integrable_const c
  have hAEIci : ∀ᵐ y : NNReal ∂(μ : Measure NNReal), x ≤ y := by
    have hmem : (Set.Ici x : Set NNReal) ∈ ae (μ : Measure NNReal) := by
      simpa using
        (compl_mem_ae_iff.mpr hzero : (Set.Iio x : Set NNReal)ᶜ ∈ ae (μ : Measure NNReal))
    exact hmem
  have hPointwise :
      ∀ᵐ y : NNReal ∂(μ : Measure NNReal),
        Real.exp (-((t : ℝ) * (y : ℝ))) ≤ c := by
    refine hAEIci.mono ?_
    intro y hy
    simpa [c] using (laplaceKernel_antitone t hy)
  -- Proof comment: `μ (Set.Iio x) = 0` forces `x ≤ y` almost surely, so antitonicity of the
  -- kernel controls the whole integral by the constant value at `x`.
  calc
    ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) ≤
        ∫ _y : NNReal, c ∂(μ : Measure NNReal) := by
          exact MeasureTheory.integral_mono_ae hIntKernel hIntConst hPointwise
    _ = c := by
        simp [c]

/-- Helper for Exercise 16.1.3: the Bernstein jump integral is always nonnegative. -/
private lemma bernsteinJumpIntegral_nonneg {ν : Measure NNReal} (t : NNReal) :
    0 ≤ ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν := by
  refine MeasureTheory.integral_nonneg ?_
  intro y
  have hExpLeOne : Real.exp (-((t : ℝ) * (y : ℝ))) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    nlinarith [show 0 ≤ (t : ℝ) by positivity, show 0 ≤ (y : ℝ) by exact_mod_cast y.2]
  exact sub_nonneg.mpr hExpLeOne

/-- Helper for Exercise 16.1.3: the mass of an initial interval is controlled by the drift-gap
exponential bound evaluated at integer times. -/
private lemma measure_Iio_toReal_le_exp_neg_nat_mul_sub
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) (x : NNReal) :
    ∀ n : ℕ,
      ((μ : Measure NNReal) (Set.Iio x)).toReal ≤
        Real.exp (-(((n + 1 : ℕ) : ℝ) * ((α : ℝ) - (x : ℝ)))) := by
  intro n
  let t : NNReal := (n + 1 : ℕ)
  have hlower := laplaceIntegral_lowerBound_on_Iio (μ := μ) (x := x) (t := t)
  have hupper :
      ∫ y : NNReal, Real.exp (-((t : ℝ) * (y : ℝ))) ∂(μ : Measure NNReal) ≤
        Real.exp (-((α : ℝ) * (t : ℝ))) := by
    rw [laplaceIntegral_eq_exp_neg_levyKhinchinExponent hrep t]
    apply Real.exp_le_exp.mpr
    have hnonneg := bernsteinJumpIntegral_nonneg (ν := ν) t
    nlinarith
  have hcompare :
      ((μ : Measure NNReal) (Set.Iio x)).toReal * Real.exp (-((t : ℝ) * (x : ℝ))) ≤
        Real.exp (-((α : ℝ) * (t : ℝ))) := le_trans hlower hupper
  have hsplit :
      Real.exp (-((α : ℝ) * (t : ℝ))) =
        Real.exp (-((t : ℝ) * (x : ℝ))) *
          Real.exp (-((t : ℝ) * ((α : ℝ) - (x : ℝ)))) := by
    have hdecomp :
        -((α : ℝ) * (t : ℝ)) =
          -((t : ℝ) * (x : ℝ)) + -((t : ℝ) * ((α : ℝ) - (x : ℝ))) := by
      ring
    rw [hdecomp, Real.exp_add]
  have hkernel_pos : 0 < Real.exp (-((t : ℝ) * (x : ℝ))) := Real.exp_pos _
  have hcompare' :
      Real.exp (-((t : ℝ) * (x : ℝ))) * ((μ : Measure NNReal) (Set.Iio x)).toReal ≤
        Real.exp (-((t : ℝ) * (x : ℝ))) *
          Real.exp (-((t : ℝ) * ((α : ℝ) - (x : ℝ)))) := by
    simpa [hsplit, mul_comm, mul_left_comm, mul_assoc] using hcompare
  exact le_of_mul_le_mul_left hcompare' hkernel_pos

/-- Helper for Exercise 16.1.3: the exponential drift-gap factor tends to `0` along the positive
integers. -/
private lemma tendsto_exp_neg_nat_mul_sub_atTop {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (-(((n + 1 : ℕ) : ℝ) * a)))
      Filter.atTop (nhds 0) := by
  have hNatTendsto :
      Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    exact (tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) _ _).comp
      (Filter.tendsto_add_atTop_nat 1)
  refine Real.tendsto_exp_neg_atTop_nhds_zero.comp ?_
  simpa [mul_comm] using hNatTendsto.const_mul_atTop ha

/-- Helper for Exercise 16.1.3: if `μ (Set.Iio x) = 0`, then the drift-gap is dominated by the
divided Bernstein jump term along the integer sequence `t = n + 1`. -/
private lemma sub_le_bernsteinJumpTerm_div_nat
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) {x : NNReal}
    (hzero : (μ : Measure NNReal) (Set.Iio x) = 0) :
    ∀ n : ℕ,
      (x : ℝ) - (α : ℝ) ≤
        ∫ y : NNReal,
          (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) /
            ((n + 1 : ℕ) : ℝ) ∂ν := by
  intro n
  let t : NNReal := (n + 1 : ℕ)
  have hupper := laplaceIntegral_upperBound_of_Iio_eq_zero (μ := μ) (x := x) (t := t) hzero
  rw [laplaceIntegral_eq_exp_neg_levyKhinchinExponent hrep t] at hupper
  have hexp :
      -(((α : ℝ) * (t : ℝ)) +
          ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν) ≤
        -((t : ℝ) * (x : ℝ)) := Real.exp_le_exp.mp hupper
  have ht_pos : 0 < (t : ℝ) := by positivity
  have hscaled :
      (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν) / (t : ℝ) =
        ∫ y : NNReal,
          (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) / (t : ℝ) ∂ν := by
    simpa using
      (MeasureTheory.integral_div (μ := ν) (r := (t : ℝ))
        (f := fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (y : ℝ))))).symm
  have hmain :
      (x : ℝ) - (α : ℝ) ≤
        (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν) / (t : ℝ) := by
    have hmul :
        ((x : ℝ) - (α : ℝ)) * (t : ℝ) ≤
          ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (y : ℝ)))) ∂ν := by
      nlinarith
    exact (le_div_iff₀ ht_pos).2 <| by
      simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using hmul
  simpa [t] using (hmain.trans_eq hscaled)

/-- Helper for Exercise 16.1.3: every interval strictly to the left of the drift has zero mass. -/
private lemma measure_Iio_eq_zero_of_lt_drift
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : x < α) :
    (μ : Measure NNReal) (Set.Iio x) = 0 := by
  -- Proof comment: a positive left interval would force the Laplace transform to decay no faster
  -- than `exp (-t x)`, contradicting the drift lower bound `α > x`.
  -- Route correction: isolate the interval-vs-Laplace lower bound first, then send the
  -- exponential decay estimate to `0` instead of mixing it with the jump-term asymptotic.
  by_contra hzero
  have hmass_pos : 0 < (μ : Measure NNReal) (Set.Iio x) := by
    exact bot_lt_iff_ne_bot.mpr hzero
  have hmass_real_pos : 0 < ((μ : Measure NNReal) (Set.Iio x)).toReal := by
    exact ENNReal.toReal_pos hmass_pos.ne' (measure_lt_top (μ := (μ : Measure NNReal)) _).ne
  have hx' : (x : ℝ) < (α : ℝ) := by exact_mod_cast hx
  have hgap_pos : 0 < (α : ℝ) - (x : ℝ) := sub_pos.mpr hx'
  have hExpTendsto :
      Filter.Tendsto
        (fun n : ℕ ↦ Real.exp (-(((n + 1 : ℕ) : ℝ) * ((α : ℝ) - (x : ℝ)))))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_exp_neg_nat_mul_sub_atTop hgap_pos
  obtain ⟨n, hn⟩ := (hExpTendsto.eventually (Iio_mem_nhds hmass_real_pos)).exists
  have hcontr := lt_of_le_of_lt (measure_Iio_toReal_le_exp_neg_nat_mul_sub hrep x n) hn
  exact lt_irrefl _ hcontr

/-- Helper for Exercise 16.1.3: every interval strictly to the right of the drift has positive
mass. -/
private lemma measure_Iio_pos_of_drift_lt
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    {x : NNReal} (hx : α < x) :
    0 < (μ : Measure NNReal) (Set.Iio x) := by
  -- Proof comment: if `μ (Set.Iio x) = 0`, then `x ≤ y` almost everywhere, so the Laplace
  -- transform decays at least like `exp (-t x)`, contradicting the sublinear jump-term asymptotic.
  -- Route correction: after the AE support comparison, divide the exponent inequality by `t`
  -- and contradict the jump-term `o(t)` behavior from the existing asymptotic lemma.
  by_contra hnotpos
  have hzero : (μ : Measure NNReal) (Set.Iio x) = 0 := by
    exact le_antisymm (le_of_not_gt hnotpos) bot_le
  have hx' : (α : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hgap_pos : 0 < (x : ℝ) - (α : ℝ) := sub_pos.mpr hx'
  have hsmall :
      ∀ᶠ n : ℕ in Filter.atTop,
        ∫ y : NNReal,
            (1 - Real.exp (-(((n + 1 : ℕ) : ℝ) * (y : ℝ)))) / ((n + 1 : ℕ) : ℝ) ∂ν <
          ((x : ℝ) - (α : ℝ)) / 2 := by
    simpa using
      (bernsteinJumpTerm_div_nat_tendsto_zero hrep).eventually
        (Iio_mem_nhds (by linarith [hgap_pos]))
  obtain ⟨n, hnsmall, hnbound⟩ :=
    (hsmall.and (Filter.Eventually.of_forall (sub_le_bernsteinJumpTerm_div_nat hrep hzero))).exists
  linarith

-- Proof sketch: use the subordinator Lévy--Khinchin representation from Theorem 16.14 to split
-- the law into the deterministic drift part `α` and a jump contribution supported in `[0, ∞)`.
-- Show first that every interval `[0, x)` with `x < α` has zero mass, and then prove that any
-- `x > α` receives positive mass by isolating the event that the jump part is sufficiently small.
/-- Exercise 16.1.3 in owner-abstraction form: the drift parameter is the essential infimum of
the identity map under the law `μ`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_essInf
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = essInf id (μ : Measure NNReal) := by
  let S : Set NNReal := {x : NNReal | (μ : Measure NNReal) (Set.Iio x) = 0}
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  have hS_sSup : sSup S = α := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hS_nonempty ?_ ?_
    · intro y hy
      by_cases hle : y ≤ α
      · exact hle
      · exfalso
        have hpos : 0 < (μ : Measure NNReal) (Set.Iio y) :=
          measure_Iio_pos_of_drift_lt hrep (lt_of_not_ge hle)
        exact hpos.ne' hy
    · intro w hw
      obtain ⟨a, hwa, haα⟩ := exists_between hw
      refine ⟨a, ?_, hwa⟩
      simpa [S] using measure_Iio_eq_zero_of_lt_drift hrep haα
  -- Proof comment: `essInf_eq_sSup` reduces the claim to the support-edge description of the
  -- null initial intervals.
  rw [essInf_eq_sSup]
  simpa [S] using hS_sSup.symm

/-- Exercise 16.1.3: under a Lévy--Khinchin representation on `[0, ∞)`, the drift parameter `α`
is the supremum of the null initial intervals `[0, x)` of the law `μ`. On `NNReal`, `[0, x)` is
represented by `Set.Iio x`. -/
theorem HasSubordinatorLevyKhinchinRepresentation.drift_eq_sSup_null_initial_interval
    {μ : ProbabilityMeasure NNReal} {α : NNReal} {ν : Measure NNReal}
    (hrep : HasSubordinatorLevyKhinchinRepresentation μ α ν) :
    α = sSup {x : NNReal | (μ : Measure NNReal) (Set.Iio x) = 0} := by
  simpa [essInf_eq_sSup] using hrep.drift_eq_essInf

end MeasureTheory.ProbabilityMeasure
