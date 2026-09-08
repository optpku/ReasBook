module

public import ReasLib.Analysis.Asymptotics.ArctanTaylor
public import ReasLib.Geometry.Euclidean.Plane.OrientedAngleToReal
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
import all ReasLib.Geometry.Euclidean.Plane.OrientedAngleToReal
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables

/-! # Slow-graph remainder for the first endpoint angle -/

public section
open Filter
open scoped EuclideanSpace Topology
namespace DFP.TwoLeg.EndpointAngleJet

/-- Near the canceled base state, the first endpoint angle is the difference
of the outgoing and incoming gradient-slope arctangents. -/
theorem firstEndpointAngleIncrement_toReal_eq_arctan_sub_eventually :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      (observableMap x).firstEndpointAngleIncrement.toReal =
        Real.arctan
            (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1 /
              DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0) -
          Real.arctan (x.2.1 * x.1 ^ 2) := by
  have hqContinuous := (DFP.FirstLeg.outputGradientEntry_analyticAt 0).continuousAt
  have hqBase : DFP.FirstLeg.outputGradient 0 2 1 0 = 1 := by
    norm_num [DFP.FirstLeg.outputGradient]
  have hqPositive : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0 := by
    apply hqContinuous.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.FirstLeg.outputGradient 0 2 1 0)
    rw [hqBase]
    exact Ioi_mem_nhds zero_lt_one
  filter_upwards [hqPositive] with x hq
  have hprojection := congrArg Prod.fst
    (observableMap_endpointAngleIncrements x.1 x.2.1 x.2.2)
  dsimp only at hprojection
  rw [hprojection]
  have hvector :
      WithLp.toLp 2 (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2) =
        (!₂[DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0,
          DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i <;> rfl
  rw [hvector]
  simpa using EuclideanPlane.oangle_toReal_eq_arctan_sub_of_pos
    1 (x.2.1 * x.1 ^ 2)
    (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 0)
    (DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 1) zero_lt_one hq

/-- Along the polynomial slow graph, the first endpoint-angle lift equals
`-2 ε² - (122/5) ε⁵ + (88/15) ε⁶` up to order seven. -/
theorem slowFirstRemainder :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p : ℝ → ℝ := fun ε ↦
    2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let q : ℝ → ℝ := fun ε ↦
    1 - 2 * (p ε + 1) * ε ^ 3 * (1 + ε) / (3 * B ε)
  let v : ℝ → ℝ := fun ε ↦
    p ε - 2 * (p ε + 1) * (1 + ε ^ 3) / (3 * B ε)
  let s0 : ℝ → ℝ := fun ε ↦ p ε * ε ^ 2
  let s1 : ℝ → ℝ := fun ε ↦ ε ^ 2 * v ε / q ε
  let t1 : ℝ → ℝ := fun ε ↦
    (76 / 5) * ε ^ 5 + (7 / 5) * ε ^ 6
  have hBContinuous : ContinuousAt B 0 := by
    dsimp only [B]
    fun_prop
  have hqContinuous : ContinuousAt q 0 := by
    dsimp [q, p, B]
    fun_prop (disch := norm_num)
  have hpContinuous : ContinuousAt p 0 := by
    dsimp only [p]
    fun_prop
  have hBZero : B 0 = 1 := by norm_num [B]
  have hqZero : q 0 = 1 := by norm_num [q, p, B]
  have hBNe : ∀ᶠ ε in 𝓝 (0 : ℝ), B ε ≠ 0 :=
    hBContinuous.eventually_ne (by norm_num [hBZero])
  have hqNe : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε ≠ 0 :=
    hqContinuous.eventually_ne (by norm_num [hqZero])
  have hslowPath : Tendsto slowGraphJetPath (𝓝 0)
      (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    rw [show slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) by
      funext ε
      exact slowGraphJetPath_apply ε]
    have hc : ContinuousAt
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    convert hc.tendsto using 1 <;> norm_num
  have hangleRaw := hslowPath.eventually
    firstEndpointAngleIncrement_toReal_eq_arctan_sub_eventually
  have hangle : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal =
        Real.arctan (s1 ε) - Real.arctan (s0 ε) := by
    filter_upwards [hangleRaw] with ε hε
    simpa [slowGraphJetPath_apply, s0, s1, q, v, p, B,
      DFP.FirstLeg.outputGradient] using hε
  let den : ℝ → ℝ := fun ε ↦
    6 * ε ^ 7 - 132 * ε ^ 6 - 5 * ε ^ 3 + 5 * ε ^ 2 - 5 * ε + 5
  let r : ℝ → ℝ := fun ε ↦
    -2 * (21 * ε ^ 5 - 234 * ε ^ 4 - 5016 * ε ^ 3 + 5 * ε - 660) /
      (5 * den ε)
  have hdenContinuous : ContinuousAt den 0 := by
    dsimp only [den]
    fun_prop
  have hdenZero : den 0 = 5 := by norm_num [den]
  have hdenNe : ∀ᶠ ε in 𝓝 (0 : ℝ), den ε ≠ 0 :=
    hdenContinuous.eventually_ne (by norm_num [hdenZero])
  have hrContinuous : ContinuousAt r 0 := by
    dsimp only [r]
    fun_prop (disch := norm_num [den])
  have hslopeFactor : ∀ᶠ ε in 𝓝 (0 : ℝ),
      s1 ε - t1 ε = r ε * ε ^ 8 := by
    filter_upwards [hBNe, hqNe, hdenNe] with ε hBε hqε hdenε
    dsimp only [s1]
    rw [sub_eq_iff_eq_add]
    apply (div_eq_iff hqε).2
    dsimp [t1, r, v, q, p, B, den] at hBε hdenε ⊢
    field_simp [hBε, hdenε]
    have hBεNorm : 1 + ε ^ 3 * 2 + ε ^ 4 ≠ 0 := by
      convert hBε using 1 <;> ring
    have hdenεNorm :
        5 - ε * 5 + ε ^ 2 * 5 - ε ^ 3 * 5 - ε ^ 6 * 132 + ε ^ 7 * 6 ≠ 0 := by
      convert hdenε using 1 <;> ring
    field_simp [hBεNorm, hdenεNorm]
    have hdenεHorner :
        ε * (ε * (ε * (ε ^ 3 * (ε * 6 - 132) - 5) + 5) - 5) + 5 ≠ 0 := by
      convert hdenε using 1 <;> ring
    field_simp [hdenεHorner]
    ring
  have hslopeO8 : (fun ε : ℝ ↦ s1 ε - t1 ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
    have hrO : r =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
      hrContinuous.isBigO
    have hproduct := hrO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 8) (𝓝 0))
    have hscaled : (fun ε : ℝ ↦ r ε * ε ^ 8) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) := by
      simpa only [one_mul] using hproduct
    exact hscaled.congr'
      (hslopeFactor.mono fun _ h ↦ h.symm)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hslopeO7 : (fun ε : ℝ ↦ s1 ε - t1 ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hslopeO8.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  let ct1 : ℝ → ℝ := fun ε ↦ 76 / 5 + (7 / 5) * ε
  have hct1Continuous : ContinuousAt ct1 0 := by
    dsimp only [ct1]
    fun_prop
  have ht1O : t1 =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hcO : ct1 =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
      hct1Continuous.isBigO
    have hraw := hcO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 0))
    have hscaled : (fun ε : ℝ ↦ ct1 ε * ε ^ 5) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [one_mul] using hraw
    apply hscaled.congr'
    · filter_upwards [] with ε
      dsimp [t1, ct1]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hpO : p =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hpContinuous.isBigO
  have hs0O : s0 =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    have h := hpO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 0))
    simpa only [s0, one_mul] using h
  have hslopeO5 : (fun ε : ℝ ↦ s1 ε - t1 ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    hslopeO8.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 8)) |>.isBigO
  have hs1O : s1 =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have h := hslopeO5.add ht1O
    exact h.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hpowTwoTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 2) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by fun_prop
    convert hc.tendsto using 1 <;> norm_num
  have hpowFiveTendsto : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    convert hc.tendsto using 1 <;> norm_num
  have hs0Tendsto : Tendsto s0 (𝓝 0) (𝓝 0) :=
    hs0O.trans_tendsto hpowTwoTendsto
  have hs1Tendsto : Tendsto s1 (𝓝 0) (𝓝 0) :=
    hs1O.trans_tendsto hpowFiveTendsto
  have hatan0O8 :
      (fun ε : ℝ ↦ Real.arctan (s0 ε) -
        (s0 ε - s0 ε ^ 3 / 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 8) := by
    simpa only [Nat.reduceMul] using
      (Real.arctan_comp_sub_cubic_isBigO hs0Tendsto hs0O)
  have hatan0 :
      (fun ε : ℝ ↦ Real.arctan (s0 ε) -
        (s0 ε - s0 ε ^ 3 / 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 7) :=
    hatan0O8.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  have hatan1O20 :
      (fun ε : ℝ ↦ Real.arctan (s1 ε) -
        (s1 ε - s1 ε ^ 3 / 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 20) := by
    simpa only [Nat.reduceMul] using
      (Real.arctan_comp_sub_cubic_isBigO hs1Tendsto hs1O)
  have hatan1 :
      (fun ε : ℝ ↦ Real.arctan (s1 ε) -
        (s1 ε - s1 ε ^ 3 / 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 7) :=
    hatan1O20.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 20)) |>.isBigO
  have hs1CubeRaw : (fun ε : ℝ ↦ s1 ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 15) := by
    simpa only [← pow_mul, Nat.reduceMul] using hs1O.pow 3
  have hs1Cube : (fun ε : ℝ ↦ s1 ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hs1CubeRaw.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 15)) |>.isBigO
  let r0 : ℝ → ℝ := fun ε ↦
    -27 * (ε - 22) *
      (27 * ε ^ 8 - 1188 * ε ^ 7 + 13068 * ε ^ 6 -
        90 * ε ^ 4 + 1980 * ε ^ 3 + 100) / 125
  have hr0Continuous : ContinuousAt r0 0 := by
    dsimp only [r0]
    fun_prop
  have hcubeFactor : ∀ ε : ℝ,
      s0 ε ^ 3 - 8 * ε ^ 6 = r0 ε * ε ^ 9 := by
    intro ε
    dsimp [s0, p, r0]
    ring
  have hs0CubeDiff9 : (fun ε : ℝ ↦ s0 ε ^ 3 - 8 * ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 9) := by
    have hrO : r0 =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
      hr0Continuous.isBigO
    have hproduct := hrO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 9) (𝓝 0))
    have hscaled : (fun ε : ℝ ↦ r0 ε * ε ^ 9) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 9) := by
      simpa only [one_mul] using hproduct
    exact hscaled.congr'
      (Filter.Eventually.of_forall fun ε ↦ (hcubeFactor ε).symm)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hs0CubeDiff : (fun ε : ℝ ↦ s0 ε ^ 3 - 8 * ε ^ 6) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hs0CubeDiff9.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 9)) |>.isBigO
  have hs1CubeScaled : (fun ε : ℝ ↦ -(1 / 3) * s1 ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := hs1Cube.const_mul_left (-(1 / 3))
  have hs0CubeScaled :
      (fun ε : ℝ ↦ (1 / 3) * (s0 ε ^ 3 - 8 * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := hs0CubeDiff.const_mul_left (1 / 3)
  have hpolynomial := hslopeO7.add (hs1CubeScaled.add hs0CubeScaled)
  have hpolynomial' :
      (fun ε : ℝ ↦
        (s1 ε - s1 ε ^ 3 / 3) - (s0 ε - s0 ε ^ 3 / 3) -
          (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := by
    apply hpolynomial.congr'
    · filter_upwards [] with ε
      dsimp [t1, s0, p]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have htotal := hatan1.add (hpolynomial'.add hatan0.neg_left)
  apply htotal.congr'
  · filter_upwards [hangle] with ε hε
    rw [hε]
    dsimp [s1, s0]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- The slow first-endpoint angle germ agrees with its degree-six polynomial
through order six. -/
theorem slowFirst_eqModPow_seven :
    DFP.TwoLeg.EqModPow 7
      (fun ε : ℝ ↦
        (observableMap (slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal)
      (fun ε : ℝ ↦
        -2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6) :=
  DFP.TwoLeg.EqModPow.of_isBigO slowFirstRemainder

end DFP.TwoLeg.EndpointAngleJet
