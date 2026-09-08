module

public import ReasLib.Analysis.PSeries
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics

public section

open Filter
open scoped Asymptotics Topology

namespace DFP.TwoLeg

/-- Along every sufficiently small positive orbit on an invariant slow graph with the
prescribed fifth-order jets, the fourth powers of the scale form a summable series. -/
theorem slowCurveScaleFourthPowerSummable (p h : ℝ → ℝ)
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
      Summable (fun j : ℕ ↦ ε j ^ 4) := by
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
  have hconstNonneg : 0 ≤ (9 / 2 : ℝ) := by
    norm_num
  have hright : (fun j : ℕ ↦
      ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) =
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    funext j
    dsimp only [C]
    rw [Real.mul_rpow hconstNonneg (Nat.cast_nonneg j)]
  have hscalePoint := hscale ε₀ hε₀
  have hscale' : εseq ~[atTop]
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    apply hscalePoint.congr_right
    exact Filter.Eventually.of_forall (fun j ↦ congrFun hright j)
  have hsummable := Asymptotics.IsEquivalent.summable_rpow_iff
    hscale' hC hp (q := (4 : ℝ))
  have hthree_four : (3 : ℝ) < 4 := by
    norm_num
  have hresultReal : Summable (fun j : ℕ ↦ εseq j ^ (4 : ℝ)) :=
    hsummable.mpr hthree_four
  have hpowFour : (fun j : ℕ ↦ εseq j ^ 4) =
      (fun j : ℕ ↦ εseq j ^ (4 : ℝ)) := by
    funext j
    exact (Real.rpow_natCast (εseq j) 4).symm
  have hresult : Summable (fun j : ℕ ↦ εseq j ^ 4) := by
    rw [hpowFour]
    exact hresultReal
  simpa only [εseq] using hresult

/-- Along every sufficiently small positive orbit on an invariant slow graph with the
prescribed fifth-order jets, the square powers of the scale do not form a summable series. -/
theorem slowCurveScaleSquareNotSummable (p h : ℝ → ℝ)
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
      ¬ Summable (fun j : ℕ ↦ ε j ^ 2) := by
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
  have hconstNonneg : 0 ≤ (9 / 2 : ℝ) := by
    norm_num
  have hright : (fun j : ℕ ↦
      ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)) =
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    funext j
    dsimp only [C]
    rw [Real.mul_rpow hconstNonneg (Nat.cast_nonneg j)]
  have hscalePoint := hscale ε₀ hε₀
  have hscale' : εseq ~[atTop]
      (fun j : ℕ ↦ C * (j : ℝ) ^ (-(1 : ℝ) / 3)) := by
    apply hscalePoint.congr_right
    exact Filter.Eventually.of_forall (fun j ↦ congrFun hright j)
  have hsummable := Asymptotics.IsEquivalent.summable_rpow_iff
    hscale' hC hp (q := (2 : ℝ))
  have hnot : ¬ (3 : ℝ) < 2 := by
    norm_num
  have hresult : ¬ Summable (fun j : ℕ ↦ εseq j ^ 2) := by
    intro hsum
    have hpowTwo : (fun j : ℕ ↦ εseq j ^ 2) =
        (fun j : ℕ ↦ εseq j ^ (2 : ℝ)) := by
      funext j
      exact (Real.rpow_natCast (εseq j) 2).symm
    have hsumReal : Summable (fun j : ℕ ↦ εseq j ^ (2 : ℝ)) := by
      rw [← hpowTwo]
      exact hsum
    exact hnot (hsummable.mp hsumReal)
  simpa only [εseq] using hresult

end DFP.TwoLeg
