module

public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- Fixed fifth-order slow-graph jets make the signed two-leg scale update
positive and strictly smaller than the current scale near zero. -/
theorem slowCurveNextPosLt (p h : ℝ → ℝ)
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀,
      0 < signedEpsilon ε (p ε) (h ε) ∧
        signedEpsilon ε (p ε) (h ε) < ε := by
  let remainder : ℝ → ℝ := fun ε ↦
    signedEpsilon ε (p ε) (h ε) -
      (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)
  have hremainder : remainder =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 6) := by
    simpa only [remainder] using slowGraphSignedRecurrence p h h_pJet h_hJet
  have hfour_lt_six : 4 < 6 := by
    norm_num
  have hpowers : (fun ε : ℝ ↦ ε ^ 6) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    Asymptotics.isLittleO_pow_pow hfour_lt_six
  have hlittle : remainder =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 4) :=
    hremainder.trans_isLittleO hpowers
  have honeEighth : 0 < (1 / 8 : ℝ) := by
    norm_num
  have hsmall := hlittle.bound honeEighth
  obtain ⟨δ, hδ, hδrule⟩ := Metric.eventually_nhds_iff.mp hsmall
  let ε₀ := min (δ / 2) (1 / 2)
  have hhalf : 0 < (1 / 2 : ℝ) := by
    norm_num
  have hε₀ : 0 < ε₀ := by
    exact lt_min (half_pos hδ) hhalf
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε
  have hεhalf : ε ≤ 1 / 2 := hε.2.trans (min_le_right _ _)
  have hεδhalf : ε ≤ δ / 2 := hε.2.trans (min_le_left _ _)
  have hεδ : ε < δ := hεδhalf.trans_lt (half_lt_self hδ)
  have hdist : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε.1]
    exact hεδ
  have hpoint := hδrule hdist
  have hfourth_nonneg : 0 ≤ ε ^ 4 := pow_nonneg hε.1.le 4
  have hbound : |remainder ε| ≤ (1 / 8) * ε ^ 4 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfourth_nonneg] using hpoint
  have hbounds := abs_le.mp hbound
  have hcube : ε ^ 3 ≤ (1 / 2 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hε.1.le hεhalf 3
  have hfourth_le : ε ^ 4 ≤ ε / 8 := by
    calc
      ε ^ 4 = ε * ε ^ 3 := by ring
      _ ≤ ε * (1 / 2 : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hcube hε.1.le
      _ = ε / 8 := by ring
  have hfifth_le : ε ^ 5 ≤ (1 / 2) * ε ^ 4 := by
    calc
      ε ^ 5 = ε ^ 4 * ε := by ring
      _ ≤ ε ^ 4 * (1 / 2) := mul_le_mul_of_nonneg_left hεhalf hfourth_nonneg
      _ = (1 / 2) * ε ^ 4 := by ring
  have hfourth_pos : 0 < ε ^ 4 := pow_pos hε.1 4
  have hfifth_nonneg : 0 ≤ ε ^ 5 := pow_nonneg hε.1.le 5
  have hnext : signedEpsilon ε (p ε) (h ε) =
      ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5 + remainder ε := by
    dsimp only [remainder]
    ring
  rw [hnext]
  constructor
  · nlinarith
  · nlinarith

/-- Every forward iterate of a sufficiently small positive point on an
invariant slow graph has positive scale and positive graph coordinates. -/
theorem slowCurveForwardOrbitPos (p h : ℝ → ℝ)
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
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∀ n : ℕ,
      let xₙ := stateMap^[n] (ε, p ε, h ε)
      0 < xₙ.1 ∧ 0 < xₙ.2.1 ∧ 0 < xₙ.2.2 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpow5 : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (𝓝 0) (𝓝 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using h_pJet
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using h_hJet
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpow5).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpow5).add hh₀Tendsto
  have htwoPos : 0 < (2 : ℝ) := by
    norm_num
  have honePos : 0 < (1 : ℝ) := by
    norm_num
  have hpEventually : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < p ε :=
    hpTendsto.eventually (Ioi_mem_nhds htwoPos)
  have hhEventually : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < h ε :=
    hhTendsto.eventually (Ioi_mem_nhds honePos)
  have hlocal : ∀ᶠ ε in 𝓝 (0 : ℝ),
      stateMap (ε, p ε, h ε) =
          (let ε' := (stateMap (ε, p ε, h ε)).1
           (ε', p ε', h ε')) ∧
        0 < p ε ∧ 0 < h ε :=
    h_invariant.and (hpEventually.and hhEventually)
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hlocal
  obtain ⟨η, hη, hnext⟩ := slowCurveNextPosLt p h h_pJet h_hJet
  let ε₀ := min η (r / 2)
  have hε₀ : 0 < ε₀ := by
    exact lt_min hη (half_pos hr)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε n
  dsimp only
  let x : ℕ → ℝ × ℝ × ℝ := fun j ↦ stateMap^[j] (ε, p ε, h ε)
  have hεη : ε ≤ η := hε.2.trans (min_le_left _ _)
  have hεrhalf : ε ≤ r / 2 := hε.2.trans (min_le_right _ _)
  have horbit : ∀ j : ℕ,
      x j = ((x j).1, p (x j).1, h (x j).1) ∧
        (x j).1 ∈ Set.Ioc 0 ε := by
    intro j
    induction j with
    | zero =>
        have hself : ε ∈ Set.Ioc 0 ε := ⟨hε.1, le_rfl⟩
        constructor
        · rfl
        · simpa only [x, Function.iterate_zero_apply] using hself
    | succ j ih =>
        let εj := (x j).1
        let εnext := (stateMap (εj, p εj, h εj)).1
        have hεj : εj ∈ Set.Ioc 0 ε := by
          simpa only [εj] using ih.2
        have hεjη : εj ∈ Set.Ioc 0 η :=
          ⟨hεj.1, hεj.2.trans hεη⟩
        have hnextRaw := hnext εj hεjη
        have hεnext : 0 < εnext ∧ εnext < εj := by
          simpa only [εnext, stateMap] using hnextRaw
        have hεjr : εj < r := by
          exact hεj.2.trans_lt (hεrhalf.trans_lt (half_lt_self hr))
        have hdist : dist εj 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hεj.1]
          exact hεjr
        have hlocalAt := hrule hdist
        have hgraphStep :
            stateMap (εj, p εj, h εj) =
              (εnext, p εnext, h εnext) := by
          simpa only [εnext] using hlocalAt.1
        have hxSucc : x (j + 1) = stateMap (x j) := by
          dsimp only [x]
          exact Function.iterate_succ_apply' stateMap j (ε, p ε, h ε)
        have hxSuccGraph : x (j + 1) =
            (εnext, p εnext, h εnext) := by
          calc
            x (j + 1) = stateMap (x j) := hxSucc
            _ = stateMap (εj, p εj, h εj) := by rw [ih.1]
            _ = (εnext, p εnext, h εnext) := hgraphStep
        constructor
        · rw [hxSuccGraph]
        · rw [hxSuccGraph]
          exact ⟨hεnext.1, hεnext.2.le.trans hεj.2⟩
  have hxn := horbit n
  have hεnr : (x n).1 < r :=
    hxn.2.2.trans_lt (hεrhalf.trans_lt (half_lt_self hr))
  have hdist : dist (x n).1 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hxn.2.1]
    exact hεnr
  have hlocalAt := hrule hdist
  have hxDef : stateMap^[n] (ε, p ε, h ε) = x n := rfl
  rw [hxDef, hxn.1]
  exact ⟨hxn.2.1, hlocalAt.2.1, hlocalAt.2.2⟩

end DFP.TwoLeg
