/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BoundedContinuousFunction CompactlySupported Topology

noncomputable section

/- This exercise splits naturally across the chapter's two convergence layers.
- `source-facing`: vague convergence is stated with `radonMeasureVaguelyConvergesTo`.
- `core/canonical`: weak convergence is stated as `Tendsto ... (𝓝 μ)` on `FiniteMeasure ℝ`.
- `bridge/view`: the weak statement uses the owner embedding
  `ProbabilityMeasure.toFiniteMeasure`, while the canonical Dirac owner theorem is
  `tendsto_diracProba_iff_tendsto`.
The only primitive data here is the Dirac sequence `n ↦ δₙ`, so no extra local wrapper API is
introduced. -/

/-- Helper for the current exercise: a compactly supported continuous
function on `ℝ` vanishes on the positive integer tail. -/
lemma eventually_eq_zero_natCast_of_compactSupport (f : C_c(ℝ, ℝ)) :
    ∀ᶠ n : ℕ in atTop, f (n : ℝ) = 0 := by
  -- Proof comment: compact support is contained in some ball around `0`, so large natural numbers
  -- lie outside the topological support.
  obtain ⟨R, _, hsub⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt (0 : ℝ) 0
  refine Filter.eventually_atTop.2 ⟨Nat.ceil R, ?_⟩
  intro n hn
  have hRn : R ≤ (n : ℝ) := by
    exact (Nat.le_ceil R).trans (by exact_mod_cast hn)
  have hn_support : (n : ℝ) ∉ tsupport f := by
    intro hn_support
    have hn_ball : (n : ℝ) ∈ Metric.ball (0 : ℝ) R := hsub hn_support
    have hn_Ioo : (n : ℝ) ∈ Set.Ioo (-R) R := by
      simpa [Real.ball_eq_Ioo] using hn_ball
    exact not_lt_of_ge hRn hn_Ioo.2
  simpa using image_eq_zero_of_notMem_tsupport hn_support

/-- Helper for the current exercise: the Dirac integrals of a compactly
supported test function tend to zero because the function vanishes on
a tail of the integers. -/
lemma dirac_nat_testIntegrals_tendsto_zero (f : C_c(ℝ, ℝ)) :
    Tendsto (fun n : ℕ ↦ ∫ x, f x ∂Measure.dirac (n : ℝ)) atTop (𝓝 0) := by
  -- Proof comment: once the evaluation points leave the compact support, every Dirac integral is
  -- literally zero, so the sequence is eventually constant.
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_eq_zero_natCast_of_compactSupport f] with n hn
  simp [hn]

/-- Helper for the current exercise: the oscillating sequence `(-1)^n` has no limit in `ℝ`. -/
lemma not_tendsto_negOnePow_nat (l : ℝ) :
    ¬ Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ n) atTop (𝓝 l) := by
  intro h
  -- Proof comment: along the even subsequence the values are constantly `1`.
  have hEvenMap : Tendsto (fun n : ℕ ↦ 2 * n) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro m
    refine Filter.eventually_atTop.2 ⟨m, ?_⟩
    intro n hn
    exact hn.trans (Nat.le_mul_of_pos_left n Nat.zero_lt_two)
  have hEven : Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ (2 * n)) atTop (𝓝 l) := h.comp hEvenMap
  have hEvenEq : ∀ n : ℕ, (-1 : ℝ) ^ (2 * n) = 1 := by
    intro n
    rw [pow_mul]
    norm_num
  have hOne : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 l) := by
    simpa [hEvenEq] using hEven
  -- Proof comment: along the odd subsequence the values are constantly `-1`.
  have hOddMap : Tendsto (fun n : ℕ ↦ 1 + 2 * n) atTop atTop := by
    convert (tendsto_add_atTop_nat 1).comp hEvenMap using 1
    funext n
    simp [Function.comp, Nat.add_comm]
  have hOdd : Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ (1 + 2 * n)) atTop (𝓝 l) := h.comp hOddMap
  have hOddEq : ∀ n : ℕ, (-1 : ℝ) ^ (1 + 2 * n) = -1 := by
    intro n
    rw [pow_add, hEvenEq]
    norm_num
  have hNegOne : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 l) := by
    simpa [hOddEq] using hOdd
  have hl_eq_one : l = 1 := tendsto_nhds_unique hOne tendsto_const_nhds
  have hl_eq_negOne : l = -1 := tendsto_nhds_unique hNegOne tendsto_const_nhds
  linarith

/-- Helper for the current exercise: evaluating `x ↦ cos (π x)` against the Dirac mass at `n` gives
`(-1)^n`. -/
lemma integral_diracProba_nat_cosPi_eq_negOnePow (n : ℕ) :
    ∫ y, Real.cos (Real.pi * y) ∂((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) =
      (-1 : ℝ) ^ n := by
  -- Proof comment: Dirac integration reduces the integral to evaluation at `n`, and
  -- `cos (nπ)` is the standard alternating sequence.
  rw [show (((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (n : ℝ)
    by rfl]
  rw [integral_dirac]
  simpa [mul_comm] using (Real.cos_nat_mul_pi n)

/-- First claim for the current exercise: the Dirac masses `δ_n` on `ℝ` converge vaguely to the zero
measure, in
the canonical sense of `radonMeasureVaguelyConvergesTo`. -/
-- Proof sketch: test against an arbitrary compactly supported continuous function `f`. Its support
-- is contained in some compact set, hence for all sufficiently large `n` one has `f n = 0`. Since
-- `∫ x, f x ∂Measure.dirac (n : ℝ) = f n`, the integrals are eventually zero and therefore tend to
-- the integral against the zero measure.
theorem dirac_nat_vaguely_converges_to_zero :
    radonMeasureVaguelyConvergesTo (fun n ↦ Measure.dirac (n : ℝ)) 0 := by
  -- Proof comment: vague convergence is exactly convergence of compactly supported test integrals
  -- together with the Radon side conditions.
  rw [radonMeasureVaguelyConvergesTo_iff]
  refine ⟨IsRadonMeasure.of_owner 0, ?_, ?_⟩
  · intro n
    exact IsRadonMeasure.of_owner (Measure.dirac (n : ℝ))
  · intro f
    -- Proof comment: the helper already turns the Dirac test integrals into an eventually zero
    -- scalar sequence.
    simpa using dirac_nat_testIntegrals_tendsto_zero f

/-- Second claim for the current exercise: the Dirac masses `δ_n` on `ℝ`, viewed in the owner space
`FiniteMeasure ℝ`, do not converge weakly in its canonical weak topology. -/
-- Proof sketch: test weak convergence against the bounded continuous oscillating function
-- `x ↦ cos (π x)`. The current theorem header is real-indexed, so after obtaining convergence of
-- the real-indexed Dirac integrals we pass to the natural-number subsequence `n ↦ (n : ℝ)`. Along
-- that subsequence the test integrals equal `(-1)^n`, which cannot converge.
theorem dirac_nat_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto (fun n ↦ (diracProba (n : ℝ)).toFiniteMeasure) atTop (𝓝 μ) := by
  -- Route correction: use the oscillating cosine test directly instead of trying to recover a
  -- probability-measure limit from the finite-measure limit.
  rintro ⟨μ, hμ⟩
  let cosPi : ℝ →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℝ ↦ Real.cos (Real.pi * x))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
      1
      (fun x ↦ by
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one (Real.pi * x))
  have hIntegral :
      Tendsto
        (fun x : ℝ ↦
          ∫ y, cosPi y ∂((diracProba x : ProbabilityMeasure ℝ) : Measure ℝ))
        atTop (𝓝 (∫ x, cosPi x ∂(μ : Measure ℝ))) := by
    -- Proof comment: weak convergence forces convergence against every bounded continuous test
    -- function.
    exact (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) cosPi
  have hNatIntegral :
      Tendsto
        (fun n : ℕ ↦
          ∫ y, cosPi y ∂((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))
        atTop (𝓝 (∫ x, cosPi x ∂(μ : Measure ℝ))) := by
    -- Proof comment: convergence along the ambient real index set restricts to the natural-number
    -- subsequence `n ↦ (n : ℝ)`.
    exact hIntegral.comp tendsto_natCast_atTop_atTop
  have hDiracEval :
      (fun n : ℕ ↦
        ∫ y, cosPi y ∂((diracProba (n : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        fun n : ℕ ↦ (-1 : ℝ) ^ n := by
    funext n
    -- Proof comment: the standalone cosine-evaluation helper avoids a brittle theorem-local
    -- normalization step.
    simpa [cosPi] using integral_diracProba_nat_cosPi_eq_negOnePow n
  have hOscillation :
      Tendsto (fun n : ℕ ↦ (-1 : ℝ) ^ n) atTop (𝓝 (∫ x, cosPi x ∂(μ : Measure ℝ))) := by
    -- Proof comment: Dirac integration evaluates `cos (π x)` at `x = n`, which yields `(-1)^n`.
    simpa [hDiracEval] using hNatIntegral
  exact not_tendsto_negOnePow_nat _ hOscillation

/-- Exercise 13.2.5: the Dirac masses `δ_n` on `ℝ` converge vaguely to `0`, but they do not
converge weakly in the canonical finite-measure topology. -/
theorem «dirac_nat_vaguely_converges_to_zero / dirac_nat_not_weakly_convergent» :
    radonMeasureVaguelyConvergesTo (fun n ↦ Measure.dirac (n : ℝ)) 0 ∧
      ¬ ∃ μ : FiniteMeasure ℝ,
        Tendsto (fun n ↦ (diracProba (n : ℝ)).toFiniteMeasure) atTop (𝓝 μ) := by
  -- Proof comment: the exercise consists exactly of the vague convergence claim and the failure of
  -- weak convergence proved above.
  constructor
  · exact dirac_nat_vaguely_converges_to_zero
  · exact dirac_nat_not_weakly_convergent
