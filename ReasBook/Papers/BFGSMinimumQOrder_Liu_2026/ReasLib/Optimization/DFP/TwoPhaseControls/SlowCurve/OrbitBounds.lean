module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Positivity
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- Every forward iterate of a sufficiently small positive point on an invariant
slow graph remains on that graph, with positive scale no larger than its initial scale. -/
theorem slowCurveForwardOrbitOnGraph (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (stateMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    ∃ η₀ ∈ Set.Ioo 0 (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 η₀, ∀ j : ℕ,
      let xj := stateMap^[j] (ε₀, p ε₀, h ε₀)
      xj = (xj.1, p xj.1, h xj.1) ∧ xj.1 ∈ Set.Ioc 0 ε₀ := by
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    let p₀ : ℝ → ℝ := fun ε ↦
      2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
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
    have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [p₀] using h_pJet
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpow5).add hp₀Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
    have hpow5 : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
      have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num
    have h₀Tendsto : Tendsto h₀ (𝓝 0) (𝓝 1) := by
      have hcontinuous : ContinuousAt h₀ 0 := by
        dsimp only [h₀]
        fun_prop
      convert hcontinuous.tendsto using 1
      norm_num [h₀]
    have hDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [h₀] using h_hJet
    simpa only [sub_add_cancel, zero_add] using
      (hDiff.trans_tendsto hpow5).add h₀Tendsto
  have hpEventually : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < p ε := by
    have htwoPos : 0 < (2 : ℝ) := by norm_num
    exact hpTendsto.eventually (Ioi_mem_nhds htwoPos)
  have hhEventually : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < h ε := by
    have honePos : 0 < (1 : ℝ) := by norm_num
    exact hhTendsto.eventually (Ioi_mem_nhds honePos)
  have hlocal : ∀ᶠ ε in 𝓝 (0 : ℝ),
      stateMap (ε, p ε, h ε) =
          (let ε' := (stateMap (ε, p ε, h ε)).1
           (ε', p ε', h ε')) ∧
        0 < p ε ∧ 0 < h ε :=
    h_invariant.and (hpEventually.and hhEventually)
  obtain ⟨r, hr, hrule⟩ := Metric.eventually_nhds_iff.mp hlocal
  obtain ⟨η, hη, hnext⟩ := slowCurveNextPosLt p h h_pJet h_hJet
  let η₀ := min η (min (r / 2) (1 / 8))
  have honeEighth : 0 < (1 / 8 : ℝ) := by norm_num
  have hη₀pos : 0 < η₀ := by
    exact lt_min hη (lt_min (half_pos hr) honeEighth)
  have hη₀leighth : η₀ ≤ (1 / 8 : ℝ) := by
    exact (min_le_right η (min (r / 2) (1 / 8))).trans (min_le_right _ _)
  have hη₀lt : η₀ < (1 / 4 : ℝ) := by
    have honeEighthLt : (1 / 8 : ℝ) < 1 / 4 := by norm_num
    exact hη₀leighth.trans_lt honeEighthLt
  refine ⟨η₀, ⟨hη₀pos, hη₀lt⟩, ?_⟩
  intro ε₀ hε₀ j
  dsimp only
  let x : ℕ → ℝ × ℝ × ℝ := fun k ↦ stateMap^[k] (ε₀, p ε₀, h ε₀)
  have hεη : ε₀ ≤ η := hε₀.2.trans ((min_le_left η (min (r / 2) (1 / 8))))
  have hεrhalf : ε₀ ≤ r / 2 := by
    exact hε₀.2.trans ((min_le_right η (min (r / 2) (1 / 8))).trans (min_le_left _ _))
  have horbit : ∀ k : ℕ,
      x k = ((x k).1, p (x k).1, h (x k).1) ∧
        (x k).1 ∈ Set.Ioc 0 ε₀ := by
    intro k
    induction k with
    | zero =>
        have hself : ε₀ ∈ Set.Ioc 0 ε₀ := ⟨hε₀.1, le_rfl⟩
        constructor
        · rfl
        · simpa only [x, Function.iterate_zero_apply] using hself
    | succ k ih =>
        let εk := (x k).1
        let εnext := (stateMap (εk, p εk, h εk)).1
        have hεk : εk ∈ Set.Ioc 0 ε₀ := by
          simpa only [εk] using ih.2
        have hεkη : εk ∈ Set.Ioc 0 η :=
          ⟨hεk.1, hεk.2.trans hεη⟩
        have hnextRaw := hnext εk hεkη
        have hεnext : 0 < εnext ∧ εnext < εk := by
          simpa only [εnext, stateMap] using hnextRaw
        have hεkr : εk < r := by
          exact hεk.2.trans_lt (hεrhalf.trans_lt (half_lt_self hr))
        have hdist : dist εk 0 < r := by
          rw [Real.dist_eq, sub_zero, abs_of_pos hεk.1]
          exact hεkr
        have hlocalAt := hrule hdist
        have hgraphStep :
            stateMap (εk, p εk, h εk) =
              (εnext, p εnext, h εnext) := by
          simpa only [εnext] using hlocalAt.1
        have hxSucc : x (k + 1) = stateMap (x k) := by
          dsimp only [x]
          exact Function.iterate_succ_apply' stateMap k (ε₀, p ε₀, h ε₀)
        have hxSuccGraph : x (k + 1) =
            (εnext, p εnext, h εnext) := by
          calc
            x (k + 1) = stateMap (x k) := hxSucc
            _ = stateMap (εk, p εk, h εk) := by rw [ih.1]
            _ = (εnext, p εnext, h εnext) := hgraphStep
        constructor
        · rw [hxSuccGraph]
        · rw [hxSuccGraph]
          exact ⟨hεnext.1, hεnext.2.le.trans hεk.2⟩
  have hxn := horbit j
  exact hxn

end DFP.TwoLeg
