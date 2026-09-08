module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.PeanoComparison
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterSmoothness
public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet.Closure
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg

public section

noncomputable section

open Filter
open scoped Matrix Topology Nat ContDiff

namespace DFP.TwoLeg.CenterJet

/-- Away from the removable line-search singularity, both first-leg center
coordinates share the coefficient `2 * (p + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))`. -/
private theorem halfCenterDisplacement_coordinates (ε p h : ℝ)
    (hp : p ≠ 0) (hh : h ≠ 0)
    (hB : 1 + 2 * ε ^ 3 + ε ^ 4 ≠ 0) :
    (observableMap (ε, p, h)).halfCenterDisplacement =
      WithLp.toLp 2
        ![(2 * (p + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 3,
          (2 * (p + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 5] := by
  have hobs := congrArg Prod.fst (observableMap_centerDisplacements ε p h)
  have hB' : 1 + ε ^ 3 * 2 + ε ^ 4 ≠ 0 := by
    simpa only [mul_comm] using hB
  have hD : ε ^ 3 * (ε + 1) + (ε ^ 3 + 1) ≠ 0 := by
    intro hzero
    apply hB
    calc
      1 + 2 * ε ^ 3 + ε ^ 4 = ε ^ 3 * (ε + 1) + (ε ^ 3 + 1) := by ring
      _ = 0 := hzero
  simp only [] at hobs
  rw [hobs]
  ext i
  fin_cases i <;>
    simp [TwoPhaseControls.first_tau, TwoPhaseControls.first_matrix,
      DFP.FirstLeg.outputGradient.eq_1, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  all_goals
    by_cases hε : ε = 0
    · simp [hε]
    · field_simp [hp, hh, hB, hB', hε]
      field_simp [hD]
      ring

/-- The slow-graph remainder assumptions force the two graph parameters to
converge to their base values `2` and `1`. -/
private theorem slowGraphParameters_tendsto (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    Tendsto p (𝓝 0) (𝓝 2) ∧ Tendsto h (𝓝 0) (𝓝 1) := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpowFive : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
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
    simpa only [p₀] using hp
  have hhDiff : (fun ε ↦ h ε - h₀ ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀] using hh
  constructor
  · simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFive).add hp₀Tendsto
  · simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFive).add hh₀Tendsto

/-- Along a path converging to the base parameters, the exact first-leg center
formula holds throughout a neighborhood of zero. -/
private theorem halfCenterDisplacement_coordinates_eventuallyEq (p h : ℝ → ℝ)
    (hp : Tendsto p (𝓝 0) (𝓝 2)) (hh : Tendsto h (𝓝 0) (𝓝 1)) :
    (fun ε : ℝ ↦ (observableMap (ε, p ε, h ε)).halfCenterDisplacement) =ᶠ[𝓝 0]
      (fun ε : ℝ ↦ WithLp.toLp 2
        ![(2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 3,
          (2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) * ε ^ 5]) := by
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  have hBContinuous : ContinuousAt B 0 := by
    dsimp only [B]
    fun_prop
  have htwoNe : (2 : ℝ) ≠ 0 := by
    norm_num
  have honeNe : (1 : ℝ) ≠ 0 := by
    norm_num
  have hBZeroNe : B 0 ≠ 0 := by
    norm_num [B]
  have hpNe : ∀ᶠ ε in 𝓝 (0 : ℝ), p ε ≠ 0 := hp.eventually_ne htwoNe
  have hhNe : ∀ᶠ ε in 𝓝 (0 : ℝ), h ε ≠ 0 := hh.eventually_ne honeNe
  have hBNe : ∀ᶠ ε in 𝓝 (0 : ℝ), B ε ≠ 0 :=
    hBContinuous.eventually_ne hBZeroNe
  filter_upwards [hpNe, hhNe, hBNe] with ε hpε hhε hBε
  apply halfCenterDisplacement_coordinates ε (p ε) (h ε) hpε hhε
  simpa only [B] using hBε

/-- The common rational coefficient in the first-leg center coordinates converges
to `2` when the shape parameter converges to `2`. -/
private theorem halfCenterCoefficient_tendsto (p : ℝ → ℝ)
    (hp : Tendsto p (𝓝 0) (𝓝 2)) :
    Tendsto
      (fun ε : ℝ ↦ 2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4)))
      (𝓝 0) (𝓝 2) := by
  have hB : Tendsto (fun ε : ℝ ↦ 1 + 2 * ε ^ 3 + ε ^ 4) (𝓝 0) (𝓝 1) := by
    have hcontinuous : ContinuousAt (fun ε : ℝ ↦ 1 + 2 * ε ^ 3 + ε ^ 4) 0 := by
      fun_prop
    convert hcontinuous.tendsto using 1
    norm_num
  have hnum : Tendsto (fun ε : ℝ ↦ 2 * (p ε + 1)) (𝓝 0) (𝓝 (2 * (2 + 1))) :=
    tendsto_const_nhds.mul (hp.add tendsto_const_nhds)
  have hden : Tendsto (fun ε : ℝ ↦ 3 * (1 + 2 * ε ^ 3 + ε ^ 4))
      (𝓝 0) (𝓝 (3 * 1)) := tendsto_const_nhds.mul hB
  have hdenNe : (3 : ℝ) * 1 ≠ 0 := by
    norm_num
  have hquotient := hnum.div hden hdenNe
  norm_num at hquotient
  have hpointwiseDivision :
      (fun ε : ℝ ↦ 2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))) =
        (fun ε : ℝ ↦ 2 * (p ε + 1)) /
          (fun ε : ℝ ↦ 3 * (1 + 2 * ε ^ 3 + ε ^ 4)) := by
    funext ε
    rfl
  rw [hpointwiseDivision]
  exact hquotient

/-- The polynomial slow-graph path is smooth to every finite order at zero. -/
private theorem slowGraphJetPath_contDiffAt (k : ℕ∞ω) :
    ContDiffAt ℝ k slowGraphJetPath 0 := by
  have hpolynomial : ContDiffAt ℝ k
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) 0 := by
    fun_prop
  have hpathEq : slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4, 1 + 8 * ε ^ 3)) := by
    funext ε
    exact slowGraphJetPath_apply ε
  simpa only [hpathEq] using hpolynomial

/-- The polynomial slow-graph path starts at the base two-leg state `(0, 2, 1)`. -/
private theorem slowGraphJetPath_zero :
    slowGraphJetPath 0 = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  rw [slowGraphJetPath_apply]
  norm_num

/-- Along a path agreeing with the slow graph through order five, the low
coordinate of the normalized full-cycle center displacement equals
`-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7` up to `O(ε ^ 8)`. -/
theorem slowFullLowRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 -
        (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  exact slowFullLowRemainderViaStability p h hp hh

/-- Along a path agreeing with the slow graph through order five, the high
coordinate of the normalized full-cycle center displacement equals
`-(508 / 5) * ε ^ 8` up to `O(ε ^ 9)`. -/
theorem slowFullHighRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 -
        (-(508 / 5) * ε ^ 8)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 9) := by
  exact slowFullHighRemainderViaStability p h hp hh

/-- Along a path agreeing with the slow graph through order five, the low
coordinate of the normalized first-leg center displacement equals
`2 * ε ^ 3` up to `o(ε ^ 3)`. -/
theorem slowHalfLowRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement 0 - 2 * ε ^ 3) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  have hcoordinates :=
    halfCenterDisplacement_coordinates_eventuallyEq p h hpTendsto hhTendsto
  let c : ℝ → ℝ := fun ε ↦
    2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))
  have hcTendsto : Tendsto c (𝓝 0) (𝓝 2) := by
    simpa only [c] using halfCenterCoefficient_tendsto p hpTendsto
  have htwoTendsto : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝 0) (𝓝 2) :=
    tendsto_const_nhds
  have hcSub : (fun ε ↦ c ε - 2) =o[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hcTendsto.sub htwoTendsto
  have hproduct := hcSub.mul_isBigO
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0))
  have hmodel : (fun ε ↦ (c ε - 2) * ε ^ 3) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    simpa only [one_mul] using hproduct
  have hremainderEq :
      (fun ε ↦ (c ε - 2) * ε ^ 3) =ᶠ[𝓝 0]
        (fun ε ↦
          (observableMap (ε, p ε, h ε)).halfCenterDisplacement 0 - 2 * ε ^ 3) := by
    filter_upwards [hcoordinates] with ε hε
    have hcoordinate := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hε
    simp only [Matrix.cons_val_zero] at hcoordinate
    rw [hcoordinate]
    dsimp only [c]
    ring
  exact hmodel.congr' hremainderEq Filter.EventuallyEq.rfl

/-- Along a path agreeing with the slow graph through order five, the high
coordinate of the normalized first-leg center displacement equals
`2 * ε ^ 5` up to `o(ε ^ 5)`. -/
theorem slowHalfHighRemainder (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement 1 - 2 * ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  have hcoordinates :=
    halfCenterDisplacement_coordinates_eventuallyEq p h hpTendsto hhTendsto
  let c : ℝ → ℝ := fun ε ↦
    2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))
  have hcTendsto : Tendsto c (𝓝 0) (𝓝 2) := by
    simpa only [c] using halfCenterCoefficient_tendsto p hpTendsto
  have htwoTendsto : Tendsto (fun _ : ℝ ↦ (2 : ℝ)) (𝓝 0) (𝓝 2) :=
    tendsto_const_nhds
  have hcSub : (fun ε ↦ c ε - 2) =o[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    apply (Asymptotics.isLittleO_one_iff ℝ).mpr
    simpa only [sub_self] using hcTendsto.sub htwoTendsto
  have hproduct := hcSub.mul_isBigO
    (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0))
  have hmodel : (fun ε ↦ (c ε - 2) * ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [one_mul] using hproduct
  have hremainderEq :
      (fun ε ↦ (c ε - 2) * ε ^ 5) =ᶠ[𝓝 0]
        (fun ε ↦
          (observableMap (ε, p ε, h ε)).halfCenterDisplacement 1 - 2 * ε ^ 5) := by
    filter_upwards [hcoordinates] with ε hε
    have hcoordinate := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 1) hε
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcoordinate
    rw [hcoordinate]
    dsimp only [c]
    ring
  exact hmodel.congr' hremainderEq Filter.EventuallyEq.rfl

/-- Along any path agreeing with the slow graph through order five, the
normalized first-leg center displacement is `O(ε ^ 3)`. -/
theorem slowHalfBound (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (observableMap (ε, p ε, h ε)).halfCenterDisplacement) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
  obtain ⟨hpTendsto, hhTendsto⟩ := slowGraphParameters_tendsto p h hp hh
  have hcoordinates :=
    halfCenterDisplacement_coordinates_eventuallyEq p h hpTendsto hhTendsto
  let c : ℝ → ℝ := fun ε ↦
    2 * (p ε + 1) / (3 * (1 + 2 * ε ^ 3 + ε ^ 4))
  have hcTendsto : Tendsto c (𝓝 0) (𝓝 2) := by
    simpa only [c] using halfCenterCoefficient_tendsto p hpTendsto
  have hcOrder : c =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hcTendsto.isBigO_one ℝ
  have hthreeOrder : (fun ε : ℝ ↦ ε ^ 3) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)
  have hthreeFive : 3 < 5 := by
    norm_num
  have hfiveOrder : (fun ε : ℝ ↦ ε ^ 5) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) :=
    (Asymptotics.isLittleO_pow_pow hthreeFive).isBigO
  have hvectorPi : (fun ε : ℝ ↦ ![ε ^ 3, ε ^ 5]) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    rw [Asymptotics.isBigO_pi]
    intro i
    fin_cases i
    · simpa using hthreeOrder
    · simpa using hfiveOrder
  let e : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 ↦ ℝ)).symm
  have hmap := e.isBigO_comp (fun ε : ℝ ↦ ![ε ^ 3, ε ^ 5]) (𝓝 0)
  have hvectorLp : (fun ε : ℝ ↦ WithLp.toLp 2 ![ε ^ 3, ε ^ 5]) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    have htrans := hmap.trans hvectorPi
    simpa only [e, PiLp.coe_symm_continuousLinearEquiv] using htrans
  have hscaled := hcOrder.smul hvectorLp
  have hscaledOrder :
      (fun ε : ℝ ↦ c ε • WithLp.toLp 2 ![ε ^ 3, ε ^ 5]) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
    simpa only [one_smul] using hscaled
  have hscaledEq :
      (fun ε : ℝ ↦ c ε • WithLp.toLp 2 ![ε ^ 3, ε ^ 5]) =ᶠ[𝓝 0]
        (fun ε ↦ (observableMap (ε, p ε, h ε)).halfCenterDisplacement) := by
    filter_upwards [hcoordinates] with ε hε
    rw [hε]
    ext i
    fin_cases i <;>
      simp [c, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact hscaledOrder.congr' hscaledEq Filter.EventuallyEq.rfl

/-- The low coordinate of the normalized full-cycle center displacement along
the polynomial slow graph has the order-seven jet
`-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7`. -/
theorem slowFullLow :
      FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 0) 0 =
      FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowFullLowRemainder p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.fullCenterDisplacement_contDiffAt 7 0
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 7
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 0) 0 := by
    exact houter.comp 0 (slowGraphJetPath_contDiffAt 7)
  have hpolynomial : ContDiffAt ℝ 7
      (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply, Nat.reduceAdd] using hremainder

/-- The high coordinate of the normalized full-cycle center displacement along
the polynomial slow graph has the order-eight jet `-(508 / 5) * ε ^ 8`. -/
theorem slowFullHigh :
      FiniteTaylorJet.ofFunction ℝ 8
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 1) 0 =
      FiniteTaylorJet.ofFunction ℝ 8
        (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowFullHighRemainder p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.fullCenterDisplacement_contDiffAt 8 1
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 8
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).fullCenterDisplacement 1) 0 := by
    exact houter.comp 0 (slowGraphJetPath_contDiffAt 8)
  have hpolynomial : ContDiffAt ℝ 8 (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply, Nat.reduceAdd] using hremainder

/-- The low coordinate of the normalized first-leg center displacement along
the polynomial slow graph has the order-three jet `2 * ε ^ 3`. -/
theorem slowHalfLow :
      FiniteTaylorJet.ofFunction ℝ 3
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 0) 0 =
      FiniteTaylorJet.ofFunction ℝ 3 (fun ε : ℝ ↦ 2 * ε ^ 3) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowHalfLowRemainder p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.halfCenterDisplacement_contDiffAt 3 0
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 3
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 0) 0 := by
    exact houter.comp 0 (slowGraphJetPath_contDiffAt 3)
  have hpolynomial : ContDiffAt ℝ 3 (fun ε : ℝ ↦ 2 * ε ^ 3) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isLittleO hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply] using hremainder

/-- The high coordinate of the normalized first-leg center displacement along
the polynomial slow graph has the order-five jet `2 * ε ^ 5`. -/
theorem slowHalfHigh :
      FiniteTaylorJet.ofFunction ℝ 5
        (fun ε : ℝ ↦
          (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 1) 0 =
      FiniteTaylorJet.ofFunction ℝ 5 (fun ε : ℝ ↦ 2 * ε ^ 5) 0 := by
  let p₀ : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h₀ : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) :=
    Asymptotics.isBigO_zero (fun ε : ℝ ↦ ε ^ 5) (𝓝 0)
  have hpZero : (fun ε ↦
      p₀ ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p₀, sub_self] using hzero
  have hhZero : (fun ε ↦ h₀ ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h₀, sub_self] using hzero
  have hremainder := slowHalfHighRemainder p₀ h₀ hpZero hhZero
  have houter := CenterCancellation.halfCenterDisplacement_contDiffAt 5 1
  rw [← slowGraphJetPath_zero] at houter
  have hactual : ContDiffAt ℝ 5
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).halfCenterDisplacement 1) 0 := by
    exact houter.comp 0 (slowGraphJetPath_contDiffAt 5)
  have hpolynomial : ContDiffAt ℝ 5 (fun ε : ℝ ↦ 2 * ε ^ 5) 0 := by
    fun_prop
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isLittleO hactual hpolynomial
  simpa only [zero_add, p₀, h₀, slowGraphJetPath_apply] using hremainder

end DFP.TwoLeg.CenterJet
