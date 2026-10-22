/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_12

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped CompactlySupported Topology

noncomputable section

/-- The `n`-th truncated Lebesgue measure on `ℝ`, obtained by restricting `volume` to `[-n, n]`. -/
def truncatedLebesgueMeasure (n : ℕ) : Measure ℝ :=
  volume.restrict (Set.Icc (-(n : ℝ)) n)

private theorem isFiniteMeasure_truncatedLebesgueMeasure (n : ℕ) :
    IsFiniteMeasure (truncatedLebesgueMeasure n) := by
  simpa [truncatedLebesgueMeasure] using
    (show IsFiniteMeasure (volume.restrict (Set.Icc (-(n : ℝ)) n)) from inferInstance)

/-- The weak-topology owner view of `truncatedLebesgueMeasure`. -/
def truncatedLebesgueFiniteMeasure (n : ℕ) : FiniteMeasure ℝ :=
  ⟨truncatedLebesgueMeasure n, isFiniteMeasure_truncatedLebesgueMeasure n⟩

/-- Helper for Exercise 13.2.4: a compactly supported continuous function on `ℝ` has topological
support contained in a symmetric compact interval. -/
lemma tsupport_subset_Icc_of_compactlySupported (f : C_c(ℝ, ℝ)) :
    ∃ R > 0, tsupport f ⊆ Set.Icc (-R) R := by
  -- Compact support makes `tsupport f` bounded, so it lies in a ball around the origin.
  obtain ⟨R, hR, hsub⟩ := f.hasCompactSupport.isCompact.isBounded.subset_ball_lt (0 : ℝ) 0
  refine ⟨R, hR, ?_⟩
  intro x hx
  have hxBall : x ∈ Metric.ball (0 : ℝ) R := hsub hx
  have hxIoo : x ∈ Set.Ioo (-R) R := by
    simpa [Real.ball_eq_Ioo] using hxBall
  exact ⟨le_of_lt hxIoo.1, le_of_lt hxIoo.2⟩

/-- Helper for Exercise 13.2.4: once `tsupport f` lies in `[-n,n]`, restricting Lebesgue measure
to `[-n,n]` does not change the integral of `f`. -/
lemma integral_truncatedLebesgue_eq_integral_of_tsupport_subset
    (f : C_c(ℝ, ℝ)) (n : ℕ) (hsub : tsupport f ⊆ Set.Icc (-(n : ℝ)) n) :
    ∫ x, f x ∂truncatedLebesgueMeasure n = ∫ x, f x ∂volume := by
  -- Rewrite the restricted integral as an indicator integral over `volume`.
  rw [truncatedLebesgueMeasure, ← integral_indicator measurableSet_Icc]
  -- Outside `[-n,n]`, the function vanishes because points outside the interval lie outside
  -- the topological support.
  congr 1
  funext x
  by_cases hx : x ∈ Set.Icc (-(n : ℝ)) n
  · simp [hx]
  · have hxSupport : x ∉ tsupport f := fun hxT ↦ hx (hsub hxT)
    simp [hx, image_eq_zero_of_notMem_tsupport hxSupport]

/-- Helper for Exercise 13.2.4: the truncated Lebesgue integrals of a compactly supported test
function are eventually equal to its Lebesgue integral. -/
lemma eventually_eq_integral_volume_for_compactlySupported (f : C_c(ℝ, ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∫ x, f x ∂truncatedLebesgueMeasure n = ∫ x, f x ∂volume := by
  -- Enclose the topological support in a fixed symmetric interval.
  obtain ⟨R, _, hRsub⟩ := tsupport_subset_Icc_of_compactlySupported f
  refine ⟨Nat.ceil R, ?_⟩
  intro n hn
  apply integral_truncatedLebesgue_eq_integral_of_tsupport_subset
  intro x hx
  rcases hRsub hx with ⟨hxLeft, hxRight⟩
  have hRceil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
  have hceiln : ((Nat.ceil R : ℕ) : ℝ) ≤ n := by
    exact_mod_cast hn
  have hRn : R ≤ (n : ℝ) := hRceil.trans hceiln
  constructor
  · linarith
  · exact hxRight.trans hRn

/-- Helper for Exercise 13.2.4: the truncated Lebesgue finite measure has total mass `2n`. -/
lemma mass_truncatedLebesgueFiniteMeasure (n : ℕ) :
    ((truncatedLebesgueFiniteMeasure n).mass : ℝ) = (2 : ℝ) * n := by
  have hIcc : (-(n : ℝ)) ≤ n := by
    nlinarith
  have hMassBase :
      ((truncatedLebesgueFiniteMeasure n).mass : ENNReal) =
        ((truncatedLebesgueFiniteMeasure n : Measure ℝ)) Set.univ :=
    FiniteMeasure.ennreal_mass (μ := truncatedLebesgueFiniteMeasure n)
  have hMass :
      ((truncatedLebesgueFiniteMeasure n).mass : ENNReal) =
        truncatedLebesgueMeasure n Set.univ := by
    simpa [truncatedLebesgueFiniteMeasure] using hMassBase
  have hMassReal :
      ((truncatedLebesgueFiniteMeasure n).mass : ℝ) =
        (truncatedLebesgueMeasure n).real Set.univ := by
    simpa [measureReal_def] using congrArg ENNReal.toReal hMass
  have hRestrict :
      (truncatedLebesgueMeasure n).real Set.univ = volume.real (Set.Icc (-(n : ℝ)) n) := by
    simpa [truncatedLebesgueMeasure] using
      (measureReal_restrict_apply_univ (μ := volume) (s := Set.Icc (-(n : ℝ)) n))
  -- Rewrite the total mass through the underlying restricted measure on `[-n,n]`.
  calc
    ((truncatedLebesgueFiniteMeasure n).mass : ℝ) = (truncatedLebesgueMeasure n).real Set.univ :=
      hMassReal
    _ = volume.real (Set.Icc (-(n : ℝ)) n) := hRestrict
    _ = (2 : ℝ) * n := by
          rw [Real.volume_real_Icc_of_le hIcc]
          nlinarith

-- Proof sketch: if `f` is compactly supported, then its support is contained in some compact
-- interval `[-R, R]`. For all sufficiently large `n`, the restriction of Lebesgue measure to
-- `[-n, n]` agrees with Lebesgue measure on the support of `f`, so the test-function integrals are
-- eventually constant and equal to the integral against `volume`.
/-- Exercise 13.2.4 (1): the restrictions of Lebesgue measure to the symmetric intervals `[-n, n]`
converge vaguely to Lebesgue measure on `ℝ`. -/
theorem truncatedLebesgueMeasures_vaguely_converge :
    radonMeasureVaguelyConvergesTo truncatedLebesgueMeasure volume := by
  -- Unfold vague convergence into Radon side conditions plus convergence of test integrals.
  rw [radonMeasureVaguelyConvergesTo_iff]
  refine ⟨IsRadonMeasure.of_owner volume, ?_, ?_⟩
  · intro n
    let _ : IsFiniteMeasure (truncatedLebesgueMeasure n) :=
      isFiniteMeasure_truncatedLebesgueMeasure n
    exact IsRadonMeasure.of_owner (truncatedLebesgueMeasure n)
  · intro f
    obtain ⟨N, hN⟩ := eventually_eq_integral_volume_for_compactlySupported f
    -- From some index on, the test integrals are literally constant.
    exact tendsto_atTop_of_eventually_const hN

-- Proof sketch: weak convergence of finite measures would force convergence of the integrals of the
-- bounded continuous test function `1`, hence convergence of the total masses. But
-- the finite measure `truncatedLebesgueFiniteMeasure n` has mass `2n`,
-- so the masses diverge and no weak limit in `FiniteMeasure ℝ` can exist.
/-- Exercise 13.2.4 (2): the finite measures obtained by restricting Lebesgue measure to `[-n, n]`
do not converge weakly in the finite-measure topology. -/
theorem truncatedLebesgueMeasures_not_weakly_convergent :
    ¬ ∃ μ : FiniteMeasure ℝ,
      Tendsto truncatedLebesgueFiniteMeasure atTop (𝓝 μ) := by
  rintro ⟨μ, hμ⟩
  let oneFun : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.const ℝ (1 : ℝ)
  have hone : oneFun = BoundedContinuousFunction.const ℝ (1 : ℝ) := rfl
  have hIntegral :
      Tendsto (fun n ↦ ∫ x, oneFun x ∂(truncatedLebesgueFiniteMeasure n : Measure ℝ)) atTop
        (𝓝 (∫ x, oneFun x ∂(μ : Measure ℝ))) := by
    exact (MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) oneFun
  let c : ℝ := ∫ x, oneFun x ∂(μ : Measure ℝ)
  have hc_lt : c < c + 1 := by
    linarith
  have hupper :
      ∀ᶠ n : ℕ in atTop, (2 : ℝ) * n < c + 1 := by
    -- Convergence to `c` forces the sequence eventually into the neighborhood `(-∞, c + 1)`.
    filter_upwards [hIntegral.eventually (Iio_mem_nhds hc_lt)] with n hn
    have hn' := hn
    rw [hone] at hn'
    simpa [c, mass_truncatedLebesgueFiniteMeasure] using hn'
  have hlower :
      ∀ᶠ n : ℕ in atTop, c + 1 ≤ (2 : ℝ) * n := by
    -- The deterministic sequence `2n` eventually dominates any fixed real number.
    refine Filter.eventually_atTop.2 ?_
    refine ⟨Nat.ceil ((c + 1) / 2), ?_⟩
    intro n hn
    have hceil : (c + 1) / 2 ≤ (Nat.ceil ((c + 1) / 2) : ℝ) := Nat.le_ceil ((c + 1) / 2)
    have hceille : ((Nat.ceil ((c + 1) / 2) : ℕ) : ℝ) ≤ n := by
      exact_mod_cast hn
    have hhalf : (c + 1) / 2 ≤ (n : ℝ) := hceil.trans hceille
    nlinarith
  rcases (hupper.and hlower).exists with ⟨n, hnUpper, hnLower⟩
  linarith
