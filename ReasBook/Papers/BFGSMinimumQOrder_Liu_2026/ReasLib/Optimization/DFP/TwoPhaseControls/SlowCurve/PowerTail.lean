module

public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence.ResidualTail
public import ReasLib.Analysis.PSeries
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Asymptotics BigOperators Topology

namespace DFP.TwoLeg

/-- Every sufficiently small positive orbit on an invariant slow graph has
uniformly bounded fourth- and sixth-power tails. -/
theorem slowCurvePowerTailBounds (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∃ C₄ > 0, ∃ C₆ > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let ε n := (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      ∀ j : ℕ,
        (Summable (fun k : ℕ ↦ ε (j + k) ^ 4) ∧
            (∑' k : ℕ, ε (j + k) ^ 4) ≤ C₄ * ε j) ∧
          (Summable (fun k : ℕ ↦ ε (j + k) ^ 6) ∧
            (∑' k : ℕ, ε (j + k) ^ 6) ≤ C₆ * ε j ^ 3) := by
  obtain ⟨ηRec, hηRec, Cε, hCε, hRec⟩ :=
    slowGraphSignedRecurrenceBound p h h_pJet h_hJet
  obtain ⟨ηNext, hηNext, hNext⟩ :=
    slowCurveNextPosLt p h h_pJet h_hJet
  obtain ⟨r, hr, hInvariant⟩ := Metric.eventually_nhds_iff.mp h_invariant
  let δ : ℝ := 1 / 2
  let ηSmall : ℝ := min (ηRec / 2) (1 / (8 * (1 + Cε)))
  have hδlt : δ < (3 / 2 : ℝ) := by
    dsimp only [δ]
    norm_num
  have hηSmallPos : 0 < ηSmall := by
    dsimp only [ηSmall]
    apply lt_min
    · positivity
    · have : 0 < (8 * (1 + Cε) : ℝ) := by positivity
      positivity
  have hdenPos : 0 < (8 * (1 + Cε) : ℝ) := by
    positivity
  have hfiveFourNonneg : 0 ≤ (5 / 4 : ℝ) := by
    norm_num
  have hηSmallLeOne : ηSmall ≤ 1 := by
    have hden : 1 ≤ 8 * (1 + Cε) := by nlinarith [hCε]
    have hbound : 1 / (8 * (1 + Cε)) ≤ 1 := by
      apply (div_le_iff₀ hdenPos).2
      simpa only [one_mul] using hden
    exact (min_le_right _ _).trans hbound
  have hηSmallRec : ηSmall < ηRec := by
    have hhalf : ηRec / 2 < ηRec := by linarith
    exact (min_le_left _ _).trans_lt hhalf
  have hδbound : |(-5 / 4 : ℝ)| * ηSmall + Cε * ηSmall ^ 2 ≤ δ := by
    have hηden : ηSmall ≤ 1 / (8 * (1 + Cε)) := min_le_right _ _
    have hfirst : (5 / 4 : ℝ) * ηSmall ≤
        (5 / 4 : ℝ) / (8 * (1 + Cε)) := by
      calc
        (5 / 4 : ℝ) * ηSmall ≤
            (5 / 4 : ℝ) * (1 / (8 * (1 + Cε))) :=
          mul_le_mul_of_nonneg_left hηden hfiveFourNonneg
        _ = (5 / 4 : ℝ) / (8 * (1 + Cε)) := by ring
    have hsq : ηSmall ^ 2 ≤ ηSmall := by
      nlinarith [hηSmallPos, hηSmallLeOne]
    have hsecond : Cε * ηSmall ^ 2 ≤
        Cε / (8 * (1 + Cε)) := by
      calc
        Cε * ηSmall ^ 2 ≤ Cε * ηSmall :=
          mul_le_mul_of_nonneg_left hsq hCε.le
        _ ≤ Cε * (1 / (8 * (1 + Cε))) :=
          mul_le_mul_of_nonneg_left hηden hCε.le
        _ = Cε / (8 * (1 + Cε)) := by ring
    have hsum : (5 / 4 : ℝ) * ηSmall + Cε * ηSmall ^ 2 ≤
        (5 / 4 : ℝ) / (8 * (1 + Cε)) + Cε / (8 * (1 + Cε)) :=
      add_le_add hfirst hsecond
    calc
      |(-5 / 4 : ℝ)| * ηSmall + Cε * ηSmall ^ 2 =
          (5 / 4 : ℝ) * ηSmall + Cε * ηSmall ^ 2 := by norm_num
      _ ≤ (5 / 4 : ℝ) / (8 * (1 + Cε)) + Cε / (8 * (1 + Cε)) := hsum
      _ ≤ δ := by
        dsimp only [δ]
        rw [← add_div]
        apply (div_le_iff₀ hdenPos).2
        nlinarith [hCε]
  let εbar : ℝ := min ηSmall (min ηNext (r / 2))
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηSmallPos (lt_min hηNext (half_pos hr))
  let Ctail : ℝ := ((3 / 2 : ℝ) - δ)⁻¹
  have hCtailPos : 0 < Ctail := by
    dsimp only [Ctail]
    positivity
  refine ⟨εbar, hεbarPos, Ctail, hCtailPos, Ctail, hCtailPos, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro j
  have hbarSmall : εbar ≤ ηSmall := min_le_left _ _
  have hbarNext : εbar ≤ ηNext :=
    (min_le_right ηSmall (min ηNext (r / 2))).trans (min_le_left _ _)
  have hbarRhalf : εbar ≤ r / 2 :=
    (min_le_right ηSmall (min ηNext (r / 2))).trans (min_le_right _ _)
  have hε₀Small : ε₀ ≤ ηSmall := hε₀.2.trans hbarSmall
  have hε₀Next : ε₀ ≤ ηNext := hε₀.2.trans hbarNext
  have hε₀Rhalf : ε₀ ≤ r / 2 := hε₀.2.trans hbarRhalf
  let εseq : ℕ → ℝ := fun n ↦ (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
  have hgraph : ∀ n : ℕ,
      stateMap^[n] (ε₀, p ε₀, h ε₀) =
          (εseq n, p (εseq n), h (εseq n)) ∧
        εseq n ∈ Set.Ioc 0 ε₀ := by
    intro n
    induction n with
    | zero =>
        constructor
        · rfl
        · exact ⟨hε₀.1, le_rfl⟩
    | succ n ih =>
        let εn := εseq n
        have hεn : εn ∈ Set.Ioc 0 ηNext := by
          refine ⟨ih.2.1, ?_⟩
          exact ih.2.2.trans hε₀Next
        have hnextRaw := hNext εn hεn
        have hεnext : 0 < (stateMap (εn, p εn, h εn)).1 ∧
            (stateMap (εn, p εn, h εn)).1 < εn := by
          have hfirst : (stateMap (εn, p εn, h εn)).1 =
              signedEpsilon εn (p εn) (h εn) := by
            simp only [stateMap, signedEpsilon]
          rw [hfirst]
          exact hnextRaw
        have hεnR : εn < r := by
          have hhalf : r / 2 < r := half_lt_self hr
          exact ih.2.2.trans_lt (hε₀Rhalf.trans_lt hhalf)
        have hdist : dist εn 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos ih.2.1]
          exact hεnR
        have hInv := hInvariant hdist
        have hInv' : stateMap (εn, p εn, h εn) =
            ((stateMap (εn, p εn, h εn)).1,
              p (stateMap (εn, p εn, h εn)).1,
              h (stateMap (εn, p εn, h εn)).1) := by
          simpa only [Function.comp_apply] using hInv
        have hiterate : εseq (n + 1) =
            (stateMap (εn, p εn, h εn)).1 := by
          dsimp only [εseq, εn]
          rw [Function.iterate_succ_apply']
          rw [ih.1]
        constructor
        · have hstate : stateMap^[n + 1] (ε₀, p ε₀, h ε₀) =
              stateMap (εn, p εn, h εn) := by
            rw [Function.iterate_succ_apply', ih.1]
          rw [hstate, hInv', hiterate]
        · rw [hiterate]
          exact ⟨hεnext.1, hεnext.2.le.trans ih.2.2⟩
  have hpositive : ∀ (_ : Unit) n, 0 < εseq n := by
    intro _ n
    exact (hgraph n).2.1
  have hscale : ∀ (_ : Unit) n, εseq n ≤ ηSmall := by
    intro _ n
    exact (hgraph n).2.2.trans hε₀Small
  have hresidual : ∀ (_ : Unit) n,
      |εseq (n + 1) - εseq n + (3 / 2 : ℝ) * εseq n ^ (3 + 1) +
          (-5 / 4 : ℝ) * εseq n ^ (3 + 2)| ≤ Cε * εseq n ^ (3 + 3) := by
    intro _ n
    have hεn := hgraph n
    have hεnSmall : εseq n ∈ Set.Ioc 0 ηSmall := by
      exact ⟨hεn.2.1, hεn.2.2.trans hε₀Small⟩
    have hbound := hRec ηSmall ⟨hηSmallPos, hηSmallRec.le⟩ (εseq n) hεnSmall
    have hstep : εseq (n + 1) =
        signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) := by
      have hiterate : εseq (n + 1) =
          (stateMap (εseq n, p (εseq n), h (εseq n))).1 := by
        dsimp only [εseq]
        rw [Function.iterate_succ_apply']
        rw [hεn.1]
      rw [hiterate]
      simp only [stateMap, signedEpsilon]
    rw [hstep]
    have hidentity :
        signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) - εseq n +
              (3 / 2 : ℝ) * εseq n ^ (3 + 1) +
              (-5 / 4 : ℝ) * εseq n ^ (3 + 2) =
          signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) - εseq n +
              (3 / 2 : ℝ) * εseq n ^ 4 - (5 / 4 : ℝ) * εseq n ^ 5 := by
      ring
    rw [hidentity]
    simpa only [Nat.reduceAdd] using hbound
  have hpq4 : 3 + 1 ≤ 4 := by
    norm_num
  have hpq6 : 3 + 1 ≤ 6 := by
    norm_num
  have htail4 :=
    ParabolicRecurrence.summable_tail_pow_and_tsum_le_of_residual
      (a := (3 / 2 : ℝ)) (b := (-5 / 4 : ℝ)) (C := Cε)
      (η := ηSmall) (δ := δ) (p := 3) (q := 4)
      hδlt hpq4 hCε.le hδbound hpositive hscale hresidual () j
  have htail6 :=
    ParabolicRecurrence.summable_tail_pow_and_tsum_le_of_residual
      (a := (3 / 2 : ℝ)) (b := (-5 / 4 : ℝ)) (C := Cε)
      (η := ηSmall) (δ := δ) (p := 3) (q := 6)
      hδlt hpq6 hCε.le hδbound hpositive hscale hresidual () j
  have htail4' : ∑' k : ℕ, εseq (j + k) ^ 4 ≤ Ctail * εseq j := by
    simpa only [Nat.reduceSub, pow_one, Ctail] using htail4.2
  have htail6' : ∑' k : ℕ, εseq (j + k) ^ 6 ≤ Ctail * εseq j ^ 3 := by
    simpa only [Nat.reduceSub, Ctail] using htail6.2
  have htail4Final :
      (∑' k : ℕ, (stateMap^[j + k] (ε₀, p ε₀, h ε₀)).1 ^ 4) ≤
        Ctail * (stateMap^[j] (ε₀, p ε₀, h ε₀)).1 := by
    simpa only [εseq] using htail4'
  have htail6Final :
      (∑' k : ℕ, (stateMap^[j + k] (ε₀, p ε₀, h ε₀)).1 ^ 6) ≤
        Ctail * (stateMap^[j] (ε₀, p ε₀, h ε₀)).1 ^ 3 := by
    simpa only [εseq] using htail6'
  exact ⟨⟨htail4.1, htail4Final⟩, ⟨htail6.1, htail6Final⟩⟩

/-- Uniformly over sufficiently small positive orbits on an invariant slow graph,
the fourth-power tail has leading term `(2 / 3) * ε j`, with relative error
controlled by a nonnegative monotone right-hand modulus tending to zero. -/
theorem slowCurveFourthPowerTailAsymptotic (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∃ ω₄ : ℝ → ℝ,
      ((∀ η ∈ Set.Ioc 0 εbar, 0 ≤ ω₄ η) ∧
          MonotoneOn ω₄ (Set.Ioc 0 εbar) ∧ Tendsto ω₄ (𝓝[>] 0) (𝓝 0)) ∧
        ∀ η ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 η,
          let ε n := (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
          ∀ j : ℕ,
            |(∑' k : ℕ, ε (j + k) ^ 4) - (2 / 3) * ε j| ≤ ω₄ η * ε j := by
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηRec, hηRec, Cε, hCε, hRec⟩ :=
    slowGraphSignedRecurrenceBound p h h_pJet h_hJet
  obtain ⟨ηScale, hηScale, hScale⟩ :=
    slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  let ηSmall : ℝ := min (ηRec / 2) (1 / (8 * (1 + Cε)))
  let δfun : ℝ → ℝ := fun η ↦ (5 / 4) * η + Cε * η ^ 2
  have hdenPos : 0 < (8 * (1 + Cε) : ℝ) := by
    positivity
  have hηSmallPos : 0 < ηSmall := by
    dsimp only [ηSmall]
    apply lt_min
    · positivity
    · positivity
  have hηSmallLeOne : ηSmall ≤ 1 := by
    have hden : 1 ≤ 8 * (1 + Cε) := by
      nlinarith [hCε]
    have hbound : 1 / (8 * (1 + Cε)) ≤ 1 := by
      apply (div_le_iff₀ hdenPos).2
      simpa only [one_mul] using hden
    exact (min_le_right _ _).trans hbound
  have hηSmallRec : ηSmall < ηRec := by
    have hhalf : ηRec / 2 < ηRec := by
      linarith
    exact (min_le_left _ _).trans_lt hhalf
  have hfiveFourNonneg : 0 ≤ (5 / 4 : ℝ) := by
    norm_num
  have hδSmall : δfun ηSmall ≤ (1 / 2 : ℝ) := by
    have hηden : ηSmall ≤ 1 / (8 * (1 + Cε)) := min_le_right _ _
    have hfirst : (5 / 4 : ℝ) * ηSmall ≤
        (5 / 4 : ℝ) / (8 * (1 + Cε)) := by
      calc
        (5 / 4 : ℝ) * ηSmall ≤
            (5 / 4 : ℝ) * (1 / (8 * (1 + Cε))) :=
          mul_le_mul_of_nonneg_left hηden hfiveFourNonneg
        _ = (5 / 4 : ℝ) / (8 * (1 + Cε)) := by
          ring
    have hsq : ηSmall ^ 2 ≤ ηSmall := by
      nlinarith [hηSmallPos, hηSmallLeOne]
    have hsecond : Cε * ηSmall ^ 2 ≤ Cε / (8 * (1 + Cε)) := by
      calc
        Cε * ηSmall ^ 2 ≤ Cε * ηSmall :=
          mul_le_mul_of_nonneg_left hsq hCε.le
        _ ≤ Cε * (1 / (8 * (1 + Cε))) :=
          mul_le_mul_of_nonneg_left hηden hCε.le
        _ = Cε / (8 * (1 + Cε)) := by
          ring
    have hsum : (5 / 4 : ℝ) * ηSmall + Cε * ηSmall ^ 2 ≤
        (5 / 4 : ℝ) / (8 * (1 + Cε)) + Cε / (8 * (1 + Cε)) :=
      add_le_add hfirst hsecond
    dsimp only [δfun]
    calc
      (5 / 4 : ℝ) * ηSmall + Cε * ηSmall ^ 2 ≤
          (5 / 4 : ℝ) / (8 * (1 + Cε)) + Cε / (8 * (1 + Cε)) := hsum
      _ ≤ 1 / 2 := by
        rw [← add_div]
        apply (div_le_iff₀ hdenPos).2
        nlinarith [hCε]
  have hδfunMonotone : ∀ ⦃x y : ℝ⦄, 0 ≤ x → x ≤ y → δfun x ≤ δfun y := by
    intro x y hx hxy
    have hsquare : x ^ 2 ≤ y ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self hx hxy
    have hscaled : Cε * x ^ 2 ≤ Cε * y ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare hCε.le
    dsimp only [δfun]
    nlinarith
  let εbar : ℝ := min ηGraph (min ηScale ηSmall)
  have hεbarPos : 0 < εbar := by
    dsimp only [εbar]
    exact lt_min hηGraph.1 (lt_min hηScale hηSmallPos)
  have hbarGraph : εbar ≤ ηGraph := min_le_left _ _
  have hbarScale : εbar ≤ ηScale :=
    (min_le_right ηGraph (min ηScale ηSmall)).trans (min_le_left _ _)
  have hbarSmall : εbar ≤ ηSmall :=
    (min_le_right ηGraph (min ηScale ηSmall)).trans (min_le_right _ _)
  let ω₄ : ℝ → ℝ := fun η ↦
    δfun η / ((3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun η))
  have haPos : 0 < (3 / 2 : ℝ) := by
    norm_num
  have hhalfLtA : (1 / 2 : ℝ) < 3 / 2 := by
    norm_num
  refine ⟨εbar, hεbarPos, ω₄, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro η hη
    have hηSmallBound : η ≤ ηSmall := hη.2.trans hbarSmall
    have hδNonneg : 0 ≤ δfun η := by
      dsimp only [δfun]
      exact add_nonneg (mul_nonneg hfiveFourNonneg hη.1.le)
        (mul_nonneg hCε.le (sq_nonneg η))
    have hδHalf : δfun η ≤ 1 / 2 :=
      (hδfunMonotone hη.1.le hηSmallBound).trans hδSmall
    have hδLtA : δfun η < 3 / 2 := hδHalf.trans_lt hhalfLtA
    have hdenNonneg : 0 ≤ (3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun η) :=
      (mul_pos haPos (sub_pos.mpr hδLtA)).le
    dsimp only [ω₄]
    exact div_nonneg hδNonneg hdenNonneg
  · intro x hx y hy hxy
    have hdxdy : δfun x ≤ δfun y := hδfunMonotone hx.1.le hxy
    have hxSmall : x ≤ ηSmall := hx.2.trans hbarSmall
    have hySmall : y ≤ ηSmall := hy.2.trans hbarSmall
    have hdxHalf : δfun x ≤ 1 / 2 :=
      (hδfunMonotone hx.1.le hxSmall).trans hδSmall
    have hdyHalf : δfun y ≤ 1 / 2 :=
      (hδfunMonotone hy.1.le hySmall).trans hδSmall
    have hdxLtA : δfun x < 3 / 2 := hdxHalf.trans_lt hhalfLtA
    have hdyLtA : δfun y < 3 / 2 := hdyHalf.trans_lt hhalfLtA
    have hdenX : 0 < (3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun x) :=
      mul_pos haPos (sub_pos.mpr hdxLtA)
    have hdenY : 0 < (3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun y) :=
      mul_pos haPos (sub_pos.mpr hdyLtA)
    have halgebra :
        δfun x * ((3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun y)) ≤
          δfun y * ((3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun x)) := by
      nlinarith
    dsimp only [ω₄]
    exact (div_le_div_iff₀ hdenX hdenY).2 halgebra
  · have hδContinuous : ContinuousAt δfun 0 := by
      dsimp only [δfun]
      fun_prop
    have hdenContinuous : ContinuousAt
        (fun η : ℝ ↦ (3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun η)) 0 := by
      fun_prop
    have hdenZero :
        (3 / 2 : ℝ) * ((3 / 2 : ℝ) - δfun 0) ≠ 0 := by
      norm_num [δfun]
    have hωContinuous : ContinuousAt ω₄ 0 := by
      dsimp only [ω₄]
      exact hδContinuous.div hdenContinuous hdenZero
    have hωZero : ω₄ 0 = 0 := by
      norm_num [ω₄, δfun]
    have hωTendsto : Tendsto ω₄ (𝓝[>] 0) (𝓝 (ω₄ 0)) :=
      hωContinuous.continuousWithinAt
    simpa only [hωZero] using hωTendsto
  · intro η hη ε₀ hε₀
    dsimp only
    intro j
    have hηGraphBound : η ≤ ηGraph := hη.2.trans hbarGraph
    have hηScaleBound : η ≤ ηScale := hη.2.trans hbarScale
    have hηSmallBound : η ≤ ηSmall := hη.2.trans hbarSmall
    have hηRecBound : η ≤ ηRec := hηSmallBound.trans hηSmallRec.le
    have hε₀Graph : ε₀ ∈ Set.Ioc 0 ηGraph :=
      ⟨hε₀.1, hε₀.2.trans hηGraphBound⟩
    have hε₀Scale : ε₀ ∈ Set.Ioc 0 ηScale :=
      ⟨hε₀.1, hε₀.2.trans hηScaleBound⟩
    let εseq : ℕ → ℝ := fun n ↦ (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
    have hOrbit := hGraph ε₀ hε₀Graph
    have hpositive : ∀ (_ : Unit) n, 0 < εseq n := by
      intro _ n
      simpa only [εseq] using (hOrbit n).2.1
    have hscale : ∀ (_ : Unit) n, εseq n ≤ η := by
      intro _ n
      exact (hOrbit n).2.2.trans hε₀.2
    have hresidual : ∀ (_ : Unit) n,
        |εseq (n + 1) - εseq n + (3 / 2 : ℝ) * εseq n ^ (3 + 1) +
            (-5 / 4 : ℝ) * εseq n ^ (3 + 2)| ≤ Cε * εseq n ^ (3 + 3) := by
      intro _ n
      have hpoint := hRec η ⟨hη.1, hηRecBound⟩ (εseq n)
        ⟨hpositive () n, hscale () n⟩
      have hgraph := (hOrbit n).1
      have hstep : εseq (n + 1) =
          signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) := by
        have hiter := Function.iterate_succ_apply' stateMap n (ε₀, p ε₀, h ε₀)
        dsimp only [εseq]
        rw [hiter, hgraph]
        simp only [stateMap, signedEpsilon]
      rw [hstep]
      have hidentity :
          signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) - εseq n +
                (3 / 2 : ℝ) * εseq n ^ (3 + 1) +
                (-5 / 4 : ℝ) * εseq n ^ (3 + 2) =
            signedEpsilon (εseq n) (p (εseq n)) (h (εseq n)) - εseq n +
                (3 / 2 : ℝ) * εseq n ^ 4 - (5 / 4 : ℝ) * εseq n ^ 5 := by
        ring
      rw [hidentity]
      simpa only [Nat.reduceAdd] using hpoint
    have hNineHalfPos : (0 : ℝ) < 9 / 2 := by
      norm_num
    have hbase : Tendsto (fun n : ℕ ↦ (9 / 2 : ℝ) * (n : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hNineHalfPos
    have hOneThirdPos : (0 : ℝ) < 1 / 3 := by
      norm_num
    have hpow : Tendsto
        (fun n : ℕ ↦ ((9 / 2 : ℝ) * (n : ℝ)) ^ (-(1 : ℝ) / 3))
        atTop (𝓝 0) := by
      have hpowBase := (tendsto_rpow_neg_atTop hOneThirdPos).comp hbase
      convert hpowBase using 1
      funext n
      dsimp only [Function.comp_apply]
      congr 1
      ring
    have hscalePoint := hScale ε₀ hε₀Scale
    have hzeroPoint : Tendsto εseq atTop (𝓝 0) := by
      exact hscalePoint.symm.tendsto_nhds hpow
    have hzero : ∀ _ : Unit, Tendsto εseq atTop (𝓝 0) := by
      intro _
      exact hzeroPoint
    let δη : ℝ := δfun η
    have hδηNonneg : 0 ≤ δη := by
      dsimp only [δη, δfun]
      exact add_nonneg (mul_nonneg hfiveFourNonneg hη.1.le)
        (mul_nonneg hCε.le (sq_nonneg η))
    have hδηHalf : δη ≤ 1 / 2 := by
      dsimp only [δη]
      exact (hδfunMonotone hη.1.le hηSmallBound).trans hδSmall
    have hδηLtA : δη < 3 / 2 := hδηHalf.trans_lt hhalfLtA
    have hδbound : |(-5 / 4 : ℝ)| * η + Cε * η ^ 2 ≤ δη := by
      dsimp only [δη, δfun]
      norm_num
    have herror := ParabolicRecurrence.recurrence_tail_pow_error_of_residual
      (p := 3) (a := (3 / 2 : ℝ)) (b := (-5 / 4 : ℝ)) (C := Cε)
      (η := η) (δ := δη) haPos hδηNonneg hδηLtA hCε.le hδbound
      hpositive hscale hzero hresidual () j
    have hcenter : εseq j / (3 / 2 : ℝ) = (2 / 3 : ℝ) * εseq j := by
      ring
    rw [hcenter] at herror
    simpa only [Nat.reduceAdd, δη, ω₄, εseq] using herror

/-- Along every sufficiently small positive orbit on an invariant slow graph, the
shifted fourth-power tail is asymptotic to `(2 / 3) * ε j`. -/
theorem slowCurveFourthPowerTailIsEquivalent (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let ε n := (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ 4) ~[atTop]
        (fun j : ℕ ↦ (2 / 3 : ℝ) * ε j) := by
  obtain ⟨εbar, hεbar, hscale⟩ :=
    slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let εseq : ℕ → ℝ := fun j ↦ (stateMap^[j] (ε₀, p ε₀, h ε₀)).1
  let C : ℝ := (9 / 2 : ℝ) ^ (-(1 : ℝ) / 3)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hp : 0 < (3 : ℝ) := by
    norm_num
  have hpq : (3 : ℝ) < 4 := by
    norm_num
  have hbaseNonneg : 0 ≤ (9 / 2 : ℝ) := by
    norm_num
  have hright : (fun j : ℕ ↦
      ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) =
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    funext j
    dsimp only [C]
    rw [Real.mul_rpow hbaseNonneg (Nat.cast_nonneg j)]
  have hscalePoint := hscale ε₀ hε₀
  have hscale' : εseq ~[atTop]
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    apply hscalePoint.congr_right
    exact Filter.Eventually.of_forall (fun j ↦ congrFun hright j)
  have htail := Asymptotics.IsEquivalent.tail_rpow_isEquivalent_self
    (q := (4 : ℝ)) hscale' hC hp hpq
  have hCcube : C ^ (3 : ℝ) = (2 / 9 : ℝ) := by
    dsimp only [C]
    rw [← Real.rpow_mul hbaseNonneg]
    have hexponent : (-(1 : ℝ) / 3) * 3 = -1 := by
      ring
    rw [hexponent, Real.rpow_neg_one]
    norm_num
  have hrightCoefficient : ∀ j : ℕ,
      C ^ (3 : ℝ) * (3 / ((4 : ℝ) - 3)) * εseq j ^ ((4 : ℝ) - 3) =
        (2 / 3 : ℝ) * εseq j := by
    intro j
    rw [hCcube]
    norm_num [Real.rpow_one]
  have htail' := htail.congr_right
    (Filter.Eventually.of_forall hrightCoefficient)
  have hleftPower : ∀ j : ℕ,
      (∑' k : ℕ, εseq (j + k) ^ (4 : ℝ)) =
        ∑' k : ℕ, εseq (j + k) ^ 4 := by
    intro j
    apply tsum_congr
    intro k
    exact Real.rpow_natCast (εseq (j + k)) 4
  have htailNatural := htail'.congr_left
    (Filter.Eventually.of_forall hleftPower)
  simpa only [εseq] using htailNatural

/-- Along every sufficiently small positive orbit on an invariant slow graph, the
shifted sixth-power tail is `O(ε j ^ 3)` at `atTop`. -/
theorem slowCurveSixthPowerTailIsBigO (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let ε n := (stateMap^[n] (ε₀, p ε₀, h ε₀)).1
      (fun j : ℕ ↦ ∑' k : ℕ, ε (j + k) ^ 6) =O[atTop]
        (fun j : ℕ ↦ ε j ^ 3) := by
  obtain ⟨εbar, hεbar, hscale⟩ :=
    slowCurveScaleAsymptotic p h h_invariant h_pJet h_hJet
  refine ⟨εbar, hεbar, ?_⟩
  intro ε₀ hε₀
  dsimp only
  let εseq : ℕ → ℝ := fun j ↦ (stateMap^[j] (ε₀, p ε₀, h ε₀)).1
  let C : ℝ := (9 / 2 : ℝ) ^ (-(1 : ℝ) / 3)
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hp : 0 < (3 : ℝ) := by
    norm_num
  have hpq : (3 : ℝ) < 6 := by
    norm_num
  have hbaseNonneg : 0 ≤ (9 / 2 : ℝ) := by
    norm_num
  have hright : (fun j : ℕ ↦
      ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) =
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    funext j
    dsimp only [C]
    rw [Real.mul_rpow hbaseNonneg (Nat.cast_nonneg j)]
  have hscalePoint := hscale ε₀ hε₀
  have hscale' : εseq ~[atTop]
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    apply hscalePoint.congr_right
    exact Filter.Eventually.of_forall (fun j ↦ congrFun hright j)
  have htail := Asymptotics.IsEquivalent.tail_rpow_isBigO_self
    (q := (6 : ℝ)) hscale' hC hp hpq
  have hleftPower : ∀ j : ℕ,
      (∑' k : ℕ, εseq (j + k) ^ (6 : ℝ)) =
        ∑' k : ℕ, εseq (j + k) ^ 6 := by
    intro j
    apply tsum_congr
    intro k
    exact Real.rpow_natCast (εseq (j + k)) 6
  have hrightPower : ∀ j : ℕ,
      εseq j ^ ((6 : ℝ) - 3) = εseq j ^ 3 := by
    intro j
    norm_num [Real.rpow_natCast]
  have htailNatural := (htail.congr_left hleftPower).congr_right hrightPower
  simpa only [εseq] using htailNatural

end DFP.TwoLeg
