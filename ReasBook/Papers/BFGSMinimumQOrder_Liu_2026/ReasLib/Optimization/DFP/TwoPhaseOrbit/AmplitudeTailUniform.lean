module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeDrift
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.PowerTail

public section

open Filter
open scoped Topology

namespace DFP.TwoPhaseOrbit

/-- The tail sum of the forward differences of a convergent real sequence equals its
remaining displacement. -/
private theorem tailTsum_forwardDiff_eq_sub {a : ℕ → ℝ} {aLim : ℝ}
    (hDiff : Summable fun j ↦ a (j + 1) - a j)
    (ha : Tendsto a atTop (𝓝 aLim)) (j : ℕ) :
    ∑' k : ℕ, (a (j + k + 1) - a (j + k)) = aLim - a j := by
  have hPartial :
      Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (a (i + 1) - a i)) atTop
        (𝓝 (aLim - a 0)) := by
    simpa only [Finset.sum_range_sub] using ha.sub tendsto_const_nhds
  have hFull : HasSum (fun i ↦ a (i + 1) - a i) (aLim - a 0) :=
    (hDiff.hasSum_iff_tendsto_nat).mpr hPartial
  have hTail := (hasSum_nat_add_iff' j).mpr hFull
  have hTailValue :
      (aLim - a 0) - ∑ i ∈ Finset.range j, (a (i + 1) - a i) = aLim - a j := by
    rw [Finset.sum_range_sub]
    ring
  rw [hTailValue] at hTail
  have hReindex (k : ℕ) :
      a (j + k + 1) - a (j + k) = a (k + j + 1) - a (k + j) := by
    rw [Nat.add_comm k j]
  exact (hTail.congr_fun hReindex).tsum_eq

/-- Uniform ratio and tail estimates give a quantitative first-order expansion at the
limit of a positive sequence. -/
private theorem positiveSequence_tail_error_le
    {a u s v : ℕ → ℝ} {aLim c M A C B η : ℝ}
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hB : 0 ≤ B) (hη : 0 ≤ η) (haLim : 0 ≤ aLim) (haLim_le : aLim ≤ M)
    (ha_pos : ∀ n, 0 < a n) (ha_le : ∀ n, a n ≤ M)
    (ha_tendsto : Tendsto a atTop (𝓝 aLim))
    (hu_nonneg : ∀ n, 0 ≤ u n) (hs_nonneg : ∀ n, 0 ≤ s n)
    (hs_le : ∀ n, s n ≤ η)
    (hTail : ∀ j, Summable (fun k ↦ u (j + k)) ∧
      (∑' k : ℕ, u (j + k)) ≤ C * s j)
    (hRatio : ∀ n, |a (n + 1) / a n - (1 - c * u n)| ≤ A * u n)
    (hTailApprox : ∀ j,
      |(∑' k : ℕ, u (j + k)) - v j| ≤ B * s j) (j : ℕ) :
    |a j - aLim - c * aLim * v j| ≤
      (M * A * C + c * M * (c + A) * C ^ 2 * η + c * M * B) * s j := by
  have hu : Summable u := by
    simpa only [zero_add] using (hTail 0).1
  have hDiffCoefficient : 0 ≤ M * (c + A) :=
    mul_nonneg hM (add_nonneg hc hA)
  have hDiffBound (n : ℕ) :
      |a (n + 1) - a n| ≤ M * (c + A) * u n := by
    have hIdentity :
        a (n + 1) - a n =
          a n * (a (n + 1) / a n - (1 - c * u n)) - c * a n * u n := by
      field_simp [ne_of_gt (ha_pos n)]
      ring
    have hFirst :
        a n * |a (n + 1) / a n - (1 - c * u n)| ≤ a n * (A * u n) :=
      mul_le_mul_of_nonneg_left (hRatio n) (ha_pos n).le
    rw [hIdentity]
    calc
      |a n * (a (n + 1) / a n - (1 - c * u n)) - c * a n * u n| ≤
          |a n * (a (n + 1) / a n - (1 - c * u n))| +
            |c * a n * u n| := abs_sub _ _
      _ = a n * |a (n + 1) / a n - (1 - c * u n)| + c * a n * u n := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos (ha_pos n), abs_of_nonneg hc,
          abs_of_nonneg (hu_nonneg n)]
      _ ≤ a n * (A * u n) + c * a n * u n :=
        add_le_add hFirst le_rfl
      _ = a n * ((c + A) * u n) := by ring
      _ ≤ M * ((c + A) * u n) :=
        mul_le_mul_of_nonneg_right (ha_le n)
          (mul_nonneg (add_nonneg hc hA) (hu_nonneg n))
      _ = M * (c + A) * u n := by ring
  have hAbsDiff : Summable (fun n ↦ |a (n + 1) - a n|) := by
    exact (hu.mul_left (M * (c + A))).of_nonneg_of_le
      (fun n ↦ abs_nonneg _) hDiffBound
  have hDiff : Summable (fun n ↦ a (n + 1) - a n) := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hAbsDiff
  have hDistanceBound (n : ℕ) :
      |aLim - a n| ≤ M * (c + A) * C * η := by
    have hAbsDiffShift : Summable (fun k ↦ |a (n + k + 1) - a (n + k)|) := by
      have hShift := (summable_nat_add_iff n).mpr hAbsDiff
      refine hShift.congr ?_
      intro k
      rw [Nat.add_comm k n]
    have hNormDiffShift :
        Summable (fun k ↦ ‖a (n + k + 1) - a (n + k)‖) := by
      simpa only [Real.norm_eq_abs] using hAbsDiffShift
    have hTailNorm :
        |∑' k : ℕ, (a (n + k + 1) - a (n + k))| ≤
          ∑' k : ℕ, |a (n + k + 1) - a (n + k)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hNormDiffShift
    rw [← tailTsum_forwardDiff_eq_sub hDiff ha_tendsto n]
    calc
      |∑' k : ℕ, (a (n + k + 1) - a (n + k))| ≤
          ∑' k : ℕ, |a (n + k + 1) - a (n + k)| := hTailNorm
      _ ≤ ∑' k : ℕ, M * (c + A) * u (n + k) :=
        hAbsDiffShift.tsum_le_tsum (fun k ↦ hDiffBound (n + k))
          ((hTail n).1.mul_left (M * (c + A)))
      _ = M * (c + A) * (∑' k : ℕ, u (n + k)) := by
        rw [(hTail n).1.tsum_mul_left]
      _ ≤ M * (c + A) * (C * s n) :=
        mul_le_mul_of_nonneg_left (hTail n).2 hDiffCoefficient
      _ ≤ M * (c + A) * (C * η) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hs_le n) hC) hDiffCoefficient
      _ = M * (c + A) * C * η := by ring
  let q : ℕ → ℝ := fun n ↦ a (n + 1) - a n + c * aLim * u n
  let qCoefficient : ℝ := M * A + c * M * (c + A) * C * η
  have hQCoefficient : 0 ≤ qCoefficient := by
    dsimp only [qCoefficient]
    positivity
  have hQBound (n : ℕ) : |q n| ≤ qCoefficient * u n := by
    have hIdentity :
        q n = a n * (a (n + 1) / a n - (1 - c * u n)) +
          c * (aLim - a n) * u n := by
      dsimp only [q]
      field_simp [ne_of_gt (ha_pos n)]
      ring
    have hFirst :
        |a n * (a (n + 1) / a n - (1 - c * u n))| ≤ M * A * u n := by
      rw [abs_mul, abs_of_pos (ha_pos n)]
      calc
        a n * |a (n + 1) / a n - (1 - c * u n)| ≤ a n * (A * u n) :=
          mul_le_mul_of_nonneg_left (hRatio n) (ha_pos n).le
        _ ≤ M * (A * u n) :=
          mul_le_mul_of_nonneg_right (ha_le n) (mul_nonneg hA (hu_nonneg n))
        _ = M * A * u n := by ring
    have hSecond : |c * (aLim - a n) * u n| ≤
        c * (M * (c + A) * C * η) * u n := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg (hu_nonneg n)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hDistanceBound n) hc) (hu_nonneg n)
    rw [hIdentity]
    calc
      |a n * (a (n + 1) / a n - (1 - c * u n)) +
          c * (aLim - a n) * u n| ≤
          |a n * (a (n + 1) / a n - (1 - c * u n))| +
            |c * (aLim - a n) * u n| := abs_add_le _ _
      _ ≤ M * A * u n + c * (M * (c + A) * C * η) * u n :=
        add_le_add hFirst hSecond
      _ = qCoefficient * u n := by
        dsimp only [qCoefficient]
        ring
  have hAbsQ : Summable (fun n ↦ |q n|) := by
    exact (hu.mul_left qCoefficient).of_nonneg_of_le
      (fun n ↦ abs_nonneg _) hQBound
  have hQ : Summable q := by
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using hAbsQ
  have hDiffShift : Summable (fun k ↦ a (j + k + 1) - a (j + k)) := by
    have hShift := (summable_nat_add_iff j).mpr hDiff
    refine hShift.congr ?_
    intro k
    rw [Nat.add_comm k j]
  have hAbsQShift : Summable (fun k ↦ |q (j + k)|) := by
    have hShift := (summable_nat_add_iff j).mpr hAbsQ
    refine hShift.congr ?_
    intro k
    rw [Nat.add_comm k j]
  have hNormQShift : Summable (fun k ↦ ‖q (j + k)‖) := by
    simpa only [Real.norm_eq_abs] using hAbsQShift
  have hQTailBound :
      |∑' k : ℕ, q (j + k)| ≤ qCoefficient * (C * s j) := by
    have hNormTail : |∑' k : ℕ, q (j + k)| ≤ ∑' k : ℕ, |q (j + k)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hNormQShift
    calc
      |∑' k : ℕ, q (j + k)| ≤ ∑' k : ℕ, |q (j + k)| := hNormTail
      _ ≤ ∑' k : ℕ, qCoefficient * u (j + k) :=
        hAbsQShift.tsum_le_tsum (fun k ↦ hQBound (j + k))
          ((hTail j).1.mul_left qCoefficient)
      _ = qCoefficient * (∑' k : ℕ, u (j + k)) := by
        rw [(hTail j).1.tsum_mul_left]
      _ ≤ qCoefficient * (C * s j) :=
        mul_le_mul_of_nonneg_left (hTail j).2 hQCoefficient
  have hCorrectionBound :
      |c * aLim * ((∑' k : ℕ, u (j + k)) - v j)| ≤ c * M * (B * s j) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg haLim]
    calc
      c * aLim * |(∑' k : ℕ, u (j + k)) - v j| ≤
          c * aLim * (B * s j) :=
        mul_le_mul_of_nonneg_left (hTailApprox j) (mul_nonneg hc haLim)
      _ ≤ c * M * (B * s j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left haLim_le hc) (mul_nonneg hB (hs_nonneg j))
  have hQTsum :
      (∑' k : ℕ, q (j + k)) =
        (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
          c * aLim * (∑' k : ℕ, u (j + k)) := by
    have hTerm (k : ℕ) :
        q (j + k) = (a (j + k + 1) - a (j + k)) +
          (c * aLim) * u (j + k) := by
      dsimp only [q]
    calc
      (∑' k : ℕ, q (j + k)) =
          ∑' k : ℕ, ((a (j + k + 1) - a (j + k)) +
            (c * aLim) * u (j + k)) := tsum_congr hTerm
      _ = (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
          ∑' k : ℕ, (c * aLim) * u (j + k) :=
        Summable.tsum_add hDiffShift ((hTail j).1.mul_left (c * aLim))
      _ = (∑' k : ℕ, (a (j + k + 1) - a (j + k))) +
          c * aLim * (∑' k : ℕ, u (j + k)) := by
        rw [(hTail j).1.tsum_mul_left]
  have hTargetIdentity :
      a j - aLim - c * aLim * v j =
        -(∑' k : ℕ, q (j + k)) +
          c * aLim * ((∑' k : ℕ, u (j + k)) - v j) := by
    rw [hQTsum, tailTsum_forwardDiff_eq_sub hDiff ha_tendsto j]
    ring
  rw [hTargetIdentity]
  calc
    |-(∑' k : ℕ, q (j + k)) +
        c * aLim * ((∑' k : ℕ, u (j + k)) - v j)| ≤
        |∑' k : ℕ, q (j + k)| +
          |c * aLim * ((∑' k : ℕ, u (j + k)) - v j)| := by
      simpa only [abs_neg] using abs_add_le
        (-(∑' k : ℕ, q (j + k)))
        (c * aLim * ((∑' k : ℕ, u (j + k)) - v j))
    _ ≤ qCoefficient * (C * s j) + c * M * (B * s j) :=
      add_le_add hQTailBound hCorrectionBound
    _ = (M * A * C + c * M * (c + A) * C ^ 2 * η + c * M * B) * s j := by
      dsimp only [qCoefficient]
      ring

/-- A common right-hand modulus controls the first-order amplitude-tail error on every
sufficiently small invariant slow-curve orbit. -/
theorem slowCurveAmplitudeTailUniform (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε ↦ ε ^ 5)) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ ωG : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ωG η) ∧
          MonotoneOn ωG (Set.Ioc 0 εbar) ∧ Tendsto ωG (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          ∀ Glim > 0,
            Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
              ∀ j : ℕ,
                |(orbit.state j).amplitude - Glim -
                    (13 / 3 : ℝ) * Glim * (orbit.state j).ε| ≤
                  ωG η * (orbit.state j).ε := by
  obtain ⟨ηDrift, hηDrift, hDriftMod, hDrift⟩ :=
    slowCurveAmplitudeDriftModulus p h h_invariant h_pJet h_hJet
  obtain ⟨ηAmp, hηAmp, Gmin, hGmin, Gmax, hGminMax, hAmp⟩ :=
    slowCurveAmplitudeUniformBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηTail, hηTail, C₄, hC₄, C₆, hC₆, hTail⟩ :=
    DFP.TwoLeg.slowCurvePowerTailBounds p h h_invariant h_pJet h_hJet
  obtain ⟨ηFourth, hηFourth, ω₄, hω₄Spec, hFourth⟩ :=
    DFP.TwoLeg.slowCurveFourthPowerTailAsymptotic
      p h h_invariant h_pJet h_hJet
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    DFP.TwoLeg.slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  let ωA : ℝ → ℝ := Asymptotics.uniformRemainderModulus
    (fun _ : Unit ↦ fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) Set.univ 4
  have hDriftSpec :=
    (Asymptotics.IsUniformRemainderModulusOn.spec _ _ _ _ _).mp hDriftMod
  let εbar := min ηDrift (min ηAmp (min ηTail (min ηFourth ηGraph)))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηDrift.1
      (lt_min hηAmp.1 (lt_min hηTail (lt_min hηFourth hηGraph.1)))
  have hbarDrift : εbar ≤ ηDrift := by
    dsimp only [εbar]
    exact min_le_left _ _
  have hbarAmp : εbar ≤ ηAmp := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hbarTail : εbar ≤ ηTail := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hbarFourth : εbar ≤ ηFourth := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbarGraph : εbar ≤ ηGraph := by
    dsimp only [εbar]
    exact (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεbarLt : εbar < 1 / 4 := hbarDrift.trans_lt hηDrift.2
  have hGmaxNonneg : 0 ≤ Gmax := hGmin.le.trans hGminMax
  let ωG : ℝ → ℝ := fun η ↦
    Gmax * ωA η * C₄ +
      (13 / 2) * Gmax * ((13 / 2) + ωA η) * C₄ ^ 2 * η +
        (13 / 2) * Gmax * ω₄ η
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ωG, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro η hη
    have hηDrift : η ∈ Set.Ioc 0 ηDrift := ⟨hη.1, hη.2.trans hbarDrift⟩
    have hηFourth : η ∈ Set.Ioc 0 ηFourth := ⟨hη.1, hη.2.trans hbarFourth⟩
    have hωA : 0 ≤ ωA η := hDriftSpec.1 η hηDrift
    have hω₄ : 0 ≤ ω₄ η := hω₄Spec.1 η hηFourth
    have hThirteenHalf : 0 ≤ (13 / 2 : ℝ) := by norm_num
    have hFirstNonneg : 0 ≤ Gmax * ωA η * C₄ :=
      mul_nonneg (mul_nonneg hGmaxNonneg hωA) hC₄.le
    have hSecondNonneg :
        0 ≤ (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA η) * C₄ ^ 2 * η :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg (mul_nonneg hThirteenHalf hGmaxNonneg)
            (add_nonneg hThirteenHalf hωA)) (sq_nonneg C₄)) hη.1.le
    have hThirdNonneg : 0 ≤ (13 / 2 : ℝ) * Gmax * ω₄ η :=
      mul_nonneg (mul_nonneg hThirteenHalf hGmaxNonneg) hω₄
    dsimp only [ωG]
    exact add_nonneg (add_nonneg hFirstNonneg hSecondNonneg) hThirdNonneg
  · intro x hx y hy hxy
    have hxDrift : x ∈ Set.Ioc 0 ηDrift := ⟨hx.1, hx.2.trans hbarDrift⟩
    have hyDrift : y ∈ Set.Ioc 0 ηDrift := ⟨hy.1, hy.2.trans hbarDrift⟩
    have hxFourth : x ∈ Set.Ioc 0 ηFourth := ⟨hx.1, hx.2.trans hbarFourth⟩
    have hyFourth : y ∈ Set.Ioc 0 ηFourth := ⟨hy.1, hy.2.trans hbarFourth⟩
    have hAxy : ωA x ≤ ωA y := hDriftSpec.2.1 hxDrift hyDrift hxy
    have hFourxy : ω₄ x ≤ ω₄ y := hω₄Spec.2.1 hxFourth hyFourth hxy
    have hAx : 0 ≤ ωA x := hDriftSpec.1 x hxDrift
    have hAy : 0 ≤ ωA y := hDriftSpec.1 y hyDrift
    have hThirteenHalf : 0 ≤ (13 / 2 : ℝ) := by norm_num
    have hFirst : Gmax * ωA x * C₄ ≤ Gmax * ωA y * C₄ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hAxy hGmaxNonneg) hC₄.le
    have hBase : ((13 / 2 : ℝ) + ωA x) * x ≤
        ((13 / 2 : ℝ) + ωA y) * y := by
      calc
        ((13 / 2 : ℝ) + ωA x) * x ≤ ((13 / 2 : ℝ) + ωA y) * x :=
          mul_le_mul_of_nonneg_right (add_le_add_right hAxy _) hx.1.le
        _ ≤ ((13 / 2 : ℝ) + ωA y) * y :=
          mul_le_mul_of_nonneg_left hxy (add_nonneg hThirteenHalf hAy)
    have hScale : 0 ≤ (13 / 2 : ℝ) * Gmax * C₄ ^ 2 := by
      positivity
    have hSecond :
        (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA x) * C₄ ^ 2 * x ≤
          (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA y) * C₄ ^ 2 * y := by
      calc
        (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA x) * C₄ ^ 2 * x =
            ((13 / 2 : ℝ) * Gmax * C₄ ^ 2) * (((13 / 2) + ωA x) * x) := by
          ring
        _ ≤ ((13 / 2 : ℝ) * Gmax * C₄ ^ 2) * (((13 / 2) + ωA y) * y) :=
          mul_le_mul_of_nonneg_left hBase hScale
        _ = (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA y) * C₄ ^ 2 * y := by
          ring
    have hThird : (13 / 2 : ℝ) * Gmax * ω₄ x ≤
        (13 / 2 : ℝ) * Gmax * ω₄ y :=
      mul_le_mul_of_nonneg_left hFourxy
        (mul_nonneg hThirteenHalf hGmaxNonneg)
    dsimp only [ωG]
    exact add_le_add (add_le_add hFirst hSecond) hThird
  · have hATendsto : Tendsto ωA (𝓝[>] 0) (𝓝 0) := hDriftSpec.2.2.1
    have hFourTendsto : Tendsto ω₄ (𝓝[>] 0) (𝓝 0) := hω₄Spec.2.2
    have hIdTendsto : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hFirstTendsto : Tendsto (fun η ↦ Gmax * ωA η * C₄)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using
        (hATendsto.const_mul Gmax).mul_const C₄
    have hCenterTendsto : Tendsto (fun η ↦ (13 / 2 : ℝ) + ωA η)
        (𝓝[>] 0) (𝓝 (13 / 2)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hATendsto
    have hSecondTendsto : Tendsto
        (fun η ↦ (13 / 2 : ℝ) * Gmax * ((13 / 2) + ωA η) * C₄ ^ 2 * η)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using
        (((hCenterTendsto.const_mul ((13 / 2 : ℝ) * Gmax)).mul_const
          (C₄ ^ 2)).mul hIdTendsto)
    have hThirdTendsto : Tendsto (fun η ↦ (13 / 2 : ℝ) * Gmax * ω₄ η)
        (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero] using hFourTendsto.const_mul ((13 / 2 : ℝ) * Gmax)
    dsimp only [ωG]
    simpa only [zero_add] using (hFirstTendsto.add hSecondTendsto).add hThirdTendsto
  · intro η hη ε₀ hε₀
    dsimp only
    intro Glim hGlimPos hGlimTendsto j
    let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
    have hηDriftMem : η ∈ Set.Ioc 0 ηDrift :=
      ⟨hη.1, hη.2.trans hbarDrift⟩
    have hηFourthMem : η ∈ Set.Ioc 0 ηFourth :=
      ⟨hη.1, hη.2.trans hbarFourth⟩
    have hε₀Amp : ε₀ ∈ Set.Ioc 0 ηAmp :=
      ⟨hε₀.1, hε₀.2.trans (hη.2.trans hbarAmp)⟩
    have hε₀Tail : ε₀ ∈ Set.Ioc 0 ηTail :=
      ⟨hε₀.1, hε₀.2.trans (hη.2.trans hbarTail)⟩
    have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
      ⟨hε₀.1, hε₀.2.trans (hη.2.trans hbarGraph)⟩
    obtain ⟨GlimBounded, hGlimBounded, hGlimBoundedTendsto, hAmpBounds⟩ :=
      hAmp ε₀ hε₀Amp
    have hGlimEq : GlimBounded = Glim :=
      tendsto_nhds_unique hGlimBoundedTendsto hGlimTendsto
    have hGlimLe : Glim ≤ Gmax := by
      rw [← hGlimEq]
      exact hGlimBounded.2
    let a : ℕ → ℝ := fun n ↦ (orbit.state n).amplitude
    let εseq : ℕ → ℝ := fun n ↦
      (DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀)).1
    let u : ℕ → ℝ := fun n ↦ εseq n ^ 4
    let v : ℕ → ℝ := fun n ↦ (2 / 3 : ℝ) * εseq n
    have hεeq (n : ℕ) : (orbit.state n).ε = εseq n := by
      have hcoord := DFP.TwoPhaseOrbit.ofSlowCurve_coordinates p h ε₀ n
      have hcoord' : (orbit.state n).coordinates =
          DFP.TwoLeg.stateMap^[n] (ε₀, p ε₀, h ε₀) := by
        simpa only [orbit] using hcoord
      dsimp only [εseq]
      simpa only [State.coordinates_def] using congrArg Prod.fst hcoord'
    have haPos (n : ℕ) : 0 < a n := by
      have hLower : Gmin ≤ (orbit.state n).amplitude := by
        simpa only [orbit] using (hAmpBounds n).1
      dsimp only [a]
      exact hGmin.trans_le hLower
    have haLe (n : ℕ) : a n ≤ Gmax := by
      dsimp only [a]
      simpa only [orbit] using (hAmpBounds n).2
    have haTendsto : Tendsto a atTop (𝓝 Glim) := by
      simpa only [a, orbit] using hGlimTendsto
    have huNonneg (n : ℕ) : 0 ≤ u n := by
      dsimp only [u]
      exact pow_nonneg (le_of_lt (hGraph ε₀ hε₀Graph n).2.1) 4
    have hεseqNonneg (n : ℕ) : 0 ≤ εseq n :=
      (hGraph ε₀ hε₀Graph n).2.1.le
    have hεseqLe (n : ℕ) : εseq n ≤ η :=
      (hGraph ε₀ hε₀Graph n).2.2.trans hε₀.2
    have hTailData (n : ℕ) : Summable (fun k ↦ u (n + k)) ∧
        (∑' k : ℕ, u (n + k)) ≤ C₄ * εseq n := by
      dsimp only [u, εseq]
      exact (hTail ε₀ hε₀Tail n).1
    have hRatio (n : ℕ) :
        |a (n + 1) / a n - (1 - (13 / 2 : ℝ) * u n)| ≤ ωA η * u n := by
      have hRaw := hDrift η hηDriftMem ε₀ hε₀ n
      simpa only [a, u, orbit, εseq, hεeq n] using hRaw
    have hTailApprox (n : ℕ) :
        |(∑' k : ℕ, u (n + k)) - v n| ≤ ω₄ η * εseq n := by
      have hRaw := hFourth η hηFourthMem ε₀ hε₀ n
      simpa only [u, v, εseq] using hRaw
    have hωA : 0 ≤ ωA η := hDriftSpec.1 η hηDriftMem
    have hω₄ : 0 ≤ ω₄ η := hω₄Spec.1 η hηFourthMem
    have hThirteenHalf : 0 ≤ (13 / 2 : ℝ) := by norm_num
    have hEstimate := positiveSequence_tail_error_le hThirteenHalf hGmaxNonneg hωA
      hC₄.le hω₄ hη.1.le hGlimPos.le hGlimLe haPos haLe haTendsto huNonneg
      hεseqNonneg hεseqLe hTailData hRatio hTailApprox j
    have hLeading : (13 / 2 : ℝ) * Glim * v j =
        (13 / 3 : ℝ) * Glim * εseq j := by
      dsimp only [v]
      ring
    rw [hLeading] at hEstimate
    simpa only [a, orbit, εseq, ωG, hεeq j] using hEstimate

end DFP.TwoPhaseOrbit
