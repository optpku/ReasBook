module

public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence
public import ReasLib.Analysis.Asymptotics.ParabolicRecurrence.ResidualTail
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.OrbitBounds
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.InvariantGraph
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoLeg

/-- Along every sufficiently small positive orbit on an invariant slow graph with the
prescribed fifth-order jets, the scale is asymptotic to `((9 / 2) * j) ^ (-1 / 3)`. -/
theorem slowCurveScaleAsymptotic (p h : ℝ → ℝ)
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
      (fun j : ℕ ↦ (stateMap^[j] (ε₀, p ε₀, h ε₀)).1) ~[atTop]
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) := by
  obtain ⟨ηGraph, hηGraph, hGraph⟩ :=
    slowCurveForwardOrbitOnGraph p h h_invariant h_pJet h_hJet
  obtain ⟨ηRec, hηRec, Cε, hCε, hRec⟩ :=
    slowGraphSignedRecurrenceBound p h h_pJet h_hJet
  have hqTendsto : Tendsto
      (fun t : ℝ ↦ |(-5 / 4 : ℝ)| * t + Cε * t ^ 2) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt
        (fun t : ℝ ↦ |(-5 / 4 : ℝ)| * t + Cε * t ^ 2) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hqEvent : ∀ᶠ t : ℝ in 𝓝 0,
      |(-5 / 4 : ℝ)| * t + Cε * t ^ 2 < (1 / 2 : ℝ) :=
    by
      have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
      exact hqTendsto.eventually (Iio_mem_nhds hhalf)
  obtain ⟨δ, hδ, hδrule⟩ := Metric.eventually_nhds_iff.mp hqEvent
  let ηbar := min (min ηGraph (ηRec / 2)) (δ / 2)
  have hηbar_pos : 0 < ηbar := by
    dsimp [ηbar]
    exact lt_min (lt_min hηGraph.1 (half_pos hηRec)) (half_pos hδ)
  have hηbar_graph : ηbar ≤ ηGraph := by
    dsimp [ηbar]
    exact (min_le_left (min ηGraph (ηRec / 2)) (δ / 2)).trans
      (min_le_left ηGraph (ηRec / 2))
  have hηbar_rec : ηbar ∈ Set.Ioc 0 ηRec := by
    constructor
    · exact hηbar_pos
    · have hhalf : ηRec / 2 < ηRec := half_lt_self hηRec
      have hmin : min ηGraph (ηRec / 2) < ηRec :=
        (min_le_right ηGraph (ηRec / 2)).trans_lt hhalf
      exact (min_le_left (min ηGraph (ηRec / 2)) (δ / 2)).trans hmin.le
  have hηbar_delta : ηbar < δ := by
    have hhalf : δ / 2 < δ := half_lt_self hδ
    exact (min_le_right _ _).trans_lt hhalf
  have hqbar : |(-5 / 4 : ℝ)| * ηbar + Cε * ηbar ^ 2 ≤ (1 / 2 : ℝ) := by
    apply le_of_lt
    apply hδrule
    rw [Real.dist_eq, sub_zero, abs_of_pos hηbar_pos]
    exact hηbar_delta
  refine ⟨ηbar, hηbar_pos, ?_⟩
  intro ε₀ hε₀
  let εseq : ℕ → ℝ := fun j ↦ (stateMap^[j] (ε₀, p ε₀, h ε₀)).1
  have hε₀_graph : ε₀ ∈ Set.Ioc 0 ηGraph := by
    exact ⟨hε₀.1, hε₀.2.trans hηbar_graph⟩
  have hOrbit := hGraph ε₀ hε₀_graph
  have hpositive (j : ℕ) : 0 < εseq j := by
    simpa only [εseq] using (hOrbit j).2.1
  have hscale (j : ℕ) : εseq j ≤ ηbar := by
    exact (hOrbit j).2.2.trans hε₀.2
  have hstep (j : ℕ) :
      εseq (j + 1) =
        signedEpsilon (εseq j) (p (εseq j)) (h (εseq j)) := by
    have hiter := Function.iterate_succ_apply' stateMap j (ε₀, p ε₀, h ε₀)
    have hgraph := (hOrbit j).1
    dsimp only [εseq]
    rw [hiter, hgraph]
    simp only [stateMap, signedEpsilon]
  have hresidual (j : ℕ) :
      |εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
          (5 / 4 : ℝ) * εseq j ^ 5| ≤ Cε * εseq j ^ 6 := by
    have hpoint := hRec ηbar hηbar_rec (εseq j)
      ⟨hpositive j, hscale j⟩
    have heq :
        εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
            (5 / 4 : ℝ) * εseq j ^ 5 =
          signedEpsilon (εseq j) (p (εseq j)) (h (εseq j)) - εseq j +
            (3 / 2 : ℝ) * εseq j ^ 4 - (5 / 4 : ℝ) * εseq j ^ 5 := by
      rw [hstep j]
    rw [heq]
    exact hpoint
  have hdecrement (j : ℕ) :
      εseq j ^ 4 ≤ εseq j - εseq (j + 1) := by
    have hδbound : |(-5 / 4 : ℝ)| * ηbar + Cε * ηbar ^ 2 ≤
        (1 / 2 : ℝ) := hqbar
    have hresidual' :
        |εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ (3 + 1) +
            (-5 / 4 : ℝ) * εseq j ^ (3 + 2)| ≤ Cε * εseq j ^ (3 + 3) := by
      simp only [Nat.reduceAdd]
      have heqResidual :
          εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 +
              (-5 / 4 : ℝ) * εseq j ^ 5 =
            εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
              (5 / 4 : ℝ) * εseq j ^ 5 := by
        ring
      rw [heqResidual]
      exact hresidual j
    have hbound :=
      ParabolicRecurrence.decrementBounds_of_residual
        (p := 3) (x := εseq j) (y := εseq (j + 1))
        (a := (3 / 2 : ℝ)) (b := (-5 / 4 : ℝ)) (C := Cε)
        (η := ηbar) (δ := (1 / 2 : ℝ))
        (hpositive j) (hscale j) hCε.le hδbound hresidual'
    have hcoeff : (3 / 2 : ℝ) - 1 / 2 = 1 := by norm_num
    rw [hcoeff] at hbound
    simpa only [Nat.reduceAdd, one_mul] using hbound.1
  have hone : 0 < (1 : ℝ) := by norm_num
  have hpq : 3 + 1 ≤ 4 := by norm_num
  have hpacketPositive : ∀ (_ : Unit) n, 0 < εseq n := by
    intro _ n
    exact hpositive n
  have hpacketDecrement :
      ∀ (_ : Unit) n, (1 : ℝ) * εseq n ^ (3 + 1) ≤
        εseq n - εseq (n + 1) := by
    intro _ n
    simpa only [Nat.reduceAdd, one_mul] using hdecrement n
  have hpacket :=
    ParabolicRecurrence.summable_tail_pow_and_tsum_le_of_decrement
      (ε := fun _ : Unit ↦ εseq) (p := 3) (q := 4) (c := (1 : ℝ))
      hone hpq hpacketPositive hpacketDecrement () 0
  have hsum : Summable (fun j : ℕ ↦ εseq j ^ 4) := by
    simpa only [Nat.zero_add] using hpacket.1
  have hpowZero : Tendsto (fun j : ℕ ↦ εseq j ^ 4) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  have hεzero : Tendsto εseq atTop (𝓝 0) := by
    have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
    have hn4 : 4 ≠ 0 := by norm_num
    have hroot := hpowZero.rpow_const_nhds_zero
      hquarter
    have hrootEq : ∀ j : ℕ, (εseq j ^ 4) ^ (1 / 4 : ℝ) = εseq j := by
      intro j
      have hidentity := Real.pow_rpow_inv_natCast (hpositive j).le hn4
      convert hidentity using 1
      norm_num
    apply hroot.congr'
    exact Filter.Eventually.of_forall hrootEq
  have hrecAtTop :
      (fun j : ℕ ↦ εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4) =O[atTop]
        (fun j : ℕ ↦ εseq j ^ 5) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨Cε * ηbar + 5 / 4, Filter.Eventually.of_forall ?_⟩
    intro j
    have hnonneg : 0 ≤ εseq j := (hpositive j).le
    have hcoefNonneg : 0 ≤ (5 / 4 : ℝ) := by norm_num
    have hpow : εseq j ^ 6 ≤ ηbar * εseq j ^ 5 := by
      calc
        εseq j ^ 6 = εseq j ^ 5 * εseq j := by ring
        _ ≤ εseq j ^ 5 * ηbar :=
          mul_le_mul_of_nonneg_left (hscale j) (pow_nonneg hnonneg 5)
        _ = ηbar * εseq j ^ 5 := by ring
    have heq :
        εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 =
          (εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
            (5 / 4 : ℝ) * εseq j ^ 5) + (5 / 4 : ℝ) * εseq j ^ 5 := by
      ring
    rw [heq]
    calc
      ‖(εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
          (5 / 4 : ℝ) * εseq j ^ 5) + (5 / 4 : ℝ) * εseq j ^ 5‖ ≤
          ‖εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
              (5 / 4 : ℝ) * εseq j ^ 5‖ + ‖(5 / 4 : ℝ) * εseq j ^ 5‖ :=
        norm_add_le _ _
      _ = |εseq (j + 1) - εseq j + (3 / 2 : ℝ) * εseq j ^ 4 -
            (5 / 4 : ℝ) * εseq j ^ 5| + (5 / 4 : ℝ) * εseq j ^ 5 := by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        rw [abs_of_nonneg hcoefNonneg]
        rw [abs_of_nonneg (pow_nonneg hnonneg 5)]
      _ ≤ Cε * εseq j ^ 6 + (5 / 4 : ℝ) * εseq j ^ 5 := by
        exact add_le_add (hresidual j) (le_refl _)
      _ ≤ (Cε * ηbar + 5 / 4) * εseq j ^ 5 := by
        have hmul := mul_le_mul_of_nonneg_left hpow hCε.le
        nlinarith
      _ = (Cε * ηbar + 5 / 4) * ‖εseq j ^ 5‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hnonneg 5)]
  have ha : 0 < (3 / 2 : ℝ) := by norm_num
  have hp : 0 < (3 : ℕ) := by norm_num
  have hasym :=
    Asymptotics.IsEquivalent.ofParabolicRecurrence
      (ε := εseq) (a := (3 / 2 : ℝ)) (p := 3)
      ha hp hpositive hεzero hrecAtTop
  refine hasym.congr_right (Filter.Eventually.of_forall (fun j ↦ ?_))
  dsimp only
  congr 1
  · ring

namespace SlowCurve

/-- The scale coordinate of every sufficiently small forward state-map orbit
carried by an invariant slow curve tends to zero. -/
theorem scaleTendstoZero (curve : DFP.TwoLeg.SlowCurve) :
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 εbar,
      Tendsto
        (fun j : ℕ ↦ (DFP.TwoLeg.stateMap^[j]
          (ε₀, curve.shape ε₀, curve.high ε₀)).1)
        atTop (𝓝 0) := by
  obtain ⟨ηScale, hηScale, hScale⟩ :=
    DFP.TwoLeg.slowCurveScaleAsymptotic
      curve.shape curve.high curve.isInvariant
        curve.shapeRemainder curve.highRemainder
  let εbar := min ηScale (1 / 8)
  have hεbarPos : 0 < εbar := lt_min hηScale (by norm_num)
  have hεbarLt : εbar < (1 / 4 : ℝ) :=
    (min_le_right _ _).trans_lt (by norm_num)
  refine ⟨εbar, ⟨hεbarPos, hεbarLt⟩, ?_⟩
  intro ε₀ hε₀
  have hεScale : ε₀ ∈ Set.Ioc 0 ηScale :=
    ⟨hε₀.1, hε₀.2.trans (min_le_left _ _)⟩
  have hBase : Tendsto (fun j : ℕ ↦ (9 / 2 : ℝ) * (j : ℝ))
      atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num)
  have hModel : Tendsto
      (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3))
      atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hBase using 1
    funext j
    simp only [Function.comp_apply]
    congr 1
    ring
  exact (hScale ε₀ hεScale).symm.tendsto_nhds hModel

end SlowCurve

end DFP.TwoLeg
