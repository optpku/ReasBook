module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness

/-!
# Clean first-center remainders on the slow graph

This module derives exact canceled first-center coordinates directly from the
one-step formulas.  The public cancellation bridge then transfers their
asymptotics to the original observable without importing the legacy center-jet
module.
-/

public section

noncomputable section

open Filter
open scoped EuclideanSpace Matrix Topology Nat ContDiff

namespace DFP.TwoLeg.CenterCancellation

/-- The two coordinates of the canceled first-center displacement share the
same exact rational coefficient, with explicit powers `ε³` and `ε⁵`. -/
theorem canceledHalfCenterDisplacement_coordinates (ε p h : ℝ) :
    canceledHalfCenterDisplacement (ε, p, h) 0 =
        (2 * (p + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 3 ∧
      canceledHalfCenterDisplacement (ε, p, h) 1 =
        (2 * (p + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 5 := by
  constructor <;>
    simp [canceledHalfCenterDisplacement, firstDisplacement,
      DFP.FirstLeg.outputGradient] <;>
    ring

end DFP.TwoLeg.CenterCancellation

namespace DFP.TwoLeg.CenterJet

private theorem slowGraphParameters_tendsto (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    Tendsto p (nhds 0) (nhds 2) ∧ Tendsto h (nhds 0) (nhds 1) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (nhds 0) (nhds 0) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hp₀Tendsto : Tendsto p₀ (nhds 0) (nhds 2) := by
    have hcontinuous : ContinuousAt p₀ 0 := by
      dsimp only [p₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [p₀]
  have hh₀Tendsto : Tendsto h₀ (nhds 0) (nhds 1) := by
    have hcontinuous : ContinuousAt h₀ 0 := by
      dsimp only [h₀]
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num [h₀]
  have hpDiff : (fun ε ↦ p ε - p₀ ε) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  constructor
  · simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  · simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto

private theorem halfCenterCoefficient_tendsto (p : ℝ → ℝ)
    (hp : Tendsto p (nhds 0) (nhds 2)) :
    Tendsto
      (fun ε : ℝ ↦ 2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4)))
      (nhds 0) (nhds 2) := by
  have hB : Tendsto (fun ε : ℝ ↦ 1 + 2 * ε ^ 3 + ε ^ 4)
      (nhds 0) (nhds 1) := by
    have hcontinuous : ContinuousAt
        (fun ε : ℝ ↦ 1 + 2 * ε ^ 3 + ε ^ 4) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hnum : Tendsto (fun ε : ℝ ↦ 2 * (p ε + 1))
      (nhds 0) (nhds (2 * (2 + 1))) :=
    tendsto_const_nhds.mul (hp.add tendsto_const_nhds)
  have hden : Tendsto (fun ε : ℝ ↦ 3 * (1 + 2 * ε ^ 3 + ε ^ 4))
      (nhds 0) (nhds (3 * 1)) := tendsto_const_nhds.mul hB
  have hquotient := hnum.div hden (by norm_num : (3 : ℝ) * 1 ≠ 0)
  norm_num at hquotient
  have hpointwiseDivision :
      (fun ε : ℝ ↦ 2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) =
        (fun ε : ℝ ↦ 2 * (p ε + 1)) /
          (fun ε : ℝ ↦ 3 * (1 + 2 * ε ^ 3 + ε ^ 4)) := by
    funext ε
    rfl
  rw [hpointwiseDivision]
  exact hquotient

private theorem halfCenterRemainder_of_formula
    (i : Fin 2) (n : ℕ) (p h : ℝ → ℝ)
    (hp : Tendsto p (nhds 0) (nhds 2))
    (hh : Tendsto h (nhds 0) (nhds 1))
    (hformula : ∀ ε : ℝ,
      CenterCancellation.canceledHalfCenterDisplacement (ε, p ε, h ε) i =
        (2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ n) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement i - 2 * ε ^ n) =o[nhds 0]
        (fun ε : ℝ ↦ ε ^ n) := by
  let c : ℝ → ℝ := fun ε ↦
    2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))
  have hcTendsto : Tendsto c (nhds 0) (nhds 2) := by
    simpa only [c] using halfCenterCoefficient_tendsto p hp
  have htwoTendsto : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (nhds 0) (nhds 2) :=
    tendsto_const_nhds
  have hcSub : (fun ε ↦ c ε - 2) =o[nhds 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hcTendsto.sub htwoTendsto
  have hmodel : (fun ε ↦ (c ε - 2) * ε ^ n) =o[nhds 0]
      (fun ε : ℝ ↦ ε ^ n) := by
    simpa only [one_mul] using hcSub.mul_isBigO
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ n) (nhds 0))
  have hpath : Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (nhds 0)
      (nhds ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [nhds_prod_eq, id_eq] using tendsto_id.prodMk (hp.prodMk hh)
  have hbridge :=
    (CenterCancellation.halfCenterDisplacement_eventuallyEq_canceled i).comp_tendsto hpath
  apply hmodel.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hbridge] with ε hε
  change (observableMap (ε, p ε, h ε)).halfCenterDisplacement i =
    CenterCancellation.canceledHalfCenterDisplacement (ε, p ε, h ε) i at hε
  rw [hε, hformula ε]
  dsimp only [c]
  ring

/-- A fifth-order perturbation of the polynomial slow graph has low first-center
coordinate `2 ε³` up to `o(ε³)`. -/
theorem slowHalfLowRemainderViaCancellation (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement 0 - 2 * ε ^ 3) =o[nhds 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  apply halfCenterRemainder_of_formula 0 3 p h hpTendsto hhTendsto
  intro ε
  exact (CenterCancellation.canceledHalfCenterDisplacement_coordinates
    ε (p ε) (h ε)).1

/-- A fifth-order perturbation of the polynomial slow graph has high first-center
coordinate `2 ε⁵` up to `o(ε⁵)`. -/
theorem slowHalfHighRemainderViaCancellation (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement 1 - 2 * ε ^ 5) =o[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  apply halfCenterRemainder_of_formula 1 5 p h hpTendsto hhTendsto
  intro ε
  exact (CenterCancellation.canceledHalfCenterDisplacement_coordinates
    ε (p ε) (h ε)).2

private theorem slowGraphJetPath_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k slowGraphJetPath 0 := by
  have hpoly : ContDiffAt ℝ k
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
    fun_prop
  apply hpoly.congr_of_eventuallyEq
  filter_upwards [] with ε
  exact slowGraphJetPath_apply ε

private theorem slowGraphJetPath_zero :
    slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  rw [slowGraphJetPath_apply]
  norm_num

/-- The low first-center coordinate along the polynomial slow graph has finite
Taylor jet `2 ε³` through order three. -/
theorem slowGraphHalfLowJetViaCancellation :
    FiniteTaylorJet.ofFunction ℝ 3
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 0) 0 =
      FiniteTaylorJet.ofFunction ℝ 3 (fun ε : ℝ ↦ 2 * ε ^ 3) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (nhds 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowHalfLowRemainderViaCancellation p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.halfCenterDisplacement_contDiffAt 3 0
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 3
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 0) 0 :=
    houter.comp 0 (slowGraphJetPath_contDiffAt 3)
  have hpolynomial : ContDiffAt ℝ 3 (fun ε : ℝ ↦ 2 * ε ^ 3) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isLittleO hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply] using hremainder

/-- The high first-center coordinate along the polynomial slow graph has finite
Taylor jet `2 ε⁵` through order five. -/
theorem slowGraphHalfHighJetViaCancellation :
    FiniteTaylorJet.ofFunction ℝ 5
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 1) 0 =
      FiniteTaylorJet.ofFunction ℝ 5 (fun ε : ℝ ↦ 2 * ε ^ 5) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[nhds 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (nhds 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[nhds 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[nhds 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowHalfHighRemainderViaCancellation p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.halfCenterDisplacement_contDiffAt 5 1
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 5
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 1) 0 :=
    houter.comp 0 (slowGraphJetPath_contDiffAt 5)
  have hpolynomial : ContDiffAt ℝ 5 (fun ε : ℝ ↦ 2 * ε ^ 5) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isLittleO hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply] using hremainder

end DFP.TwoLeg.CenterJet
