module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowFirstRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondSlopes.Closure
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables

public section

open Filter
open scoped EuclideanSpace Topology

namespace DFP.TwoLeg.EndpointAngleJet

/-- The cubic Taylor polynomial of `Real.arctan` has a fourth-order bound at zero. -/
private theorem arctan_sub_cubic_isBigO :
    (fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 4) := by
  let den : ℝ → ℝ := fun x ↦ 1 + x ^ 2
  let d : ℝ → ℝ := fun x ↦ (den x)⁻¹
  have hden : ContDiff ℝ 4 den := by
    fun_prop
  have hd : ContDiff ℝ 4 d := by
    apply hden.inv
    intro x
    dsimp [den]
    positivity
  have hproduct : den * d = fun _ ↦ 1 := by
    funext x
    dsimp [den, d]
    field_simp
  have hdZero : iteratedDeriv 0 d 0 = 1 := by
    norm_num [d, den]
  have hdOne : iteratedDeriv 1 d 0 = 0 := by
    simp [d, den, iteratedDeriv_succ]
  have hdenZero : iteratedDeriv 0 den 0 = 1 := by
    norm_num [den]
  have hdenOne : iteratedDeriv 1 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenTwo : iteratedDeriv 2 den 0 = 2 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenThree : iteratedDeriv 3 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdTwo : iteratedDeriv 2 d 0 = -2 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 2 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo,
      hdZero, hdOne, iteratedDeriv_const] at h
    linarith
  have hdThree : iteratedDeriv 3 d 0 = 0 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 3 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo, hdenThree,
      hdZero, hdOne, hdTwo, iteratedDeriv_const] at h
    linarith
  have hderivArctan : deriv Real.arctan = d := by
    simpa only [d, den, one_div] using Real.deriv_arctan
  have h₀ : iteratedDeriv 0 Real.arctan 0 = 0 := by
    simp
  have h₁ : iteratedDeriv 1 Real.arctan 0 = 1 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₂ : iteratedDeriv 2 Real.arctan 0 = 0 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₃ : iteratedDeriv 3 Real.arctan 0 = -2 := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdTwo
  have h₄ : iteratedDeriv 4 Real.arctan 0 = 0 := by
    rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdThree
  have hTaylor := taylor_isLittleO_univ (x₀ := 0) (n := 4) Real.contDiff_arctan
  have hPolynomial (x : ℝ) :
      taylorWithinEval Real.arctan 4 Set.univ 0 x = x - x ^ 3 / 3 := by
    rw [taylor_within_apply]
    norm_num [iteratedDerivWithin_univ, Finset.sum_range_succ,
      h₀, h₁, h₂, h₃, h₄]
    ring
  exact hTaylor.isBigO.congr'
    (Filter.Eventually.of_forall fun x ↦ by simp only [hPolynomial])
    (Filter.Eventually.of_forall fun x ↦ by simp)

/-- The canonical oriented angle between two vectors in the positive first-coordinate
chart is the difference of their arctangent slope coordinates. -/
private theorem endpointAngle_toReal_eq_arctan_sub (a b c : ℝ) (hb : 0 < b) :
    (EuclideanPlane.orientation.oangle
      (!₂[(1 : ℝ), a] : EuclideanSpace ℝ (Fin 2))
      (!₂[b, c] : EuclideanSpace ℝ (Fin 2))).toReal =
        Real.arctan (c / b) - Real.arctan a := by
  let e : EuclideanSpace ℝ (Fin 2) := !₂[(1 : ℝ), 0]
  have he : e ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change (1 : ℝ) = 0 at hzero
    norm_num at hzero
  have hrightAngle :
      EuclideanPlane.orientation.rotation (Real.pi / 2 : ℝ) e =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    rw [EuclideanPlane.orientation.rotation_pi_div_two]
    change EuclideanPlane.perp e = _
    rw [EuclideanPlane.perp_apply]
    simp [e]
  have hslope (r : ℝ) :
      e + r • EuclideanPlane.orientation.rotation (Real.pi / 2 : ℝ) e =
        (!₂[(1 : ℝ), r] : EuclideanSpace ℝ (Fin 2)) := by
    rw [hrightAngle]
    ext i
    fin_cases i
    · simp [e]
    · simp [e]
  have hfirst : EuclideanPlane.orientation.oangle e
      (!₂[(1 : ℝ), a] : EuclideanSpace ℝ (Fin 2)) = Real.arctan a := by
    rw [← hslope a]
    exact EuclideanPlane.orientation.oangle_add_right_smul_rotation_pi_div_two he a
  have hscaled :
      b • (!₂[(1 : ℝ), c / b] : EuclideanSpace ℝ (Fin 2)) =
        (!₂[b, c] : EuclideanSpace ℝ (Fin 2)) := by
    ext i
    fin_cases i
    · simp
    · simp
      field_simp [hb.ne']
  have hsecond : EuclideanPlane.orientation.oangle e
      (!₂[b, c] : EuclideanSpace ℝ (Fin 2)) = Real.arctan (c / b) := by
    rw [← hscaled,
      EuclideanPlane.orientation.oangle_smul_right_of_pos e _ hb]
    rw [← hslope (c / b)]
    exact EuclideanPlane.orientation.oangle_add_right_smul_rotation_pi_div_two he (c / b)
  have hleftNe : (!₂[(1 : ℝ), a] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change (1 : ℝ) = 0 at hzero
    norm_num at hzero
  have hrightNe : (!₂[b, c] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
    intro h
    have hzero := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    change b = 0 at hzero
    exact hb.ne' hzero
  have hangle : EuclideanPlane.orientation.oangle
      (!₂[(1 : ℝ), a] : EuclideanSpace ℝ (Fin 2))
      (!₂[b, c] : EuclideanSpace ℝ (Fin 2)) =
        (Real.arctan (c / b) - Real.arctan a : ℝ) := by
    rw [← EuclideanPlane.orientation.oangle_sub_left he hleftNe hrightNe,
      hfirst, hsecond, Real.Angle.coe_sub]
  rw [hangle]
  apply Real.Angle.toReal_coe_eq_self_iff.mpr
  have hcRange := Real.arctan_mem_Ioo (c / b)
  have haRange := Real.arctan_mem_Ioo a
  constructor
  · linarith [hcRange.1, hcRange.2, haRange.1, haRange.2]
  · linarith [hcRange.1, hcRange.2, haRange.1, haRange.2]

/-- Along the slow-graph path, the canonical real lift of the first endpoint-gradient
angle increment is
`-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6 + O(ε ^ 7)`. -/
theorem slowFirst :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  let p : ℝ → ℝ := fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let B : ℝ → ℝ := fun ε ↦ 1 + 2 * ε ^ 3 + ε ^ 4
  let q : ℝ → ℝ := fun ε ↦
    1 - 2 * (p ε + 1) * ε ^ 3 * (1 + ε) / (3 * B ε)
  let v : ℝ → ℝ := fun ε ↦
    p ε - 2 * (p ε + 1) * (1 + ε ^ 3) / (3 * B ε)
  have hqContinuous : ContinuousAt q 0 := by
    dsimp [q, p, B]
    fun_prop (disch := norm_num)
  have hqZero : q 0 = 1 := by
    norm_num [q, p, B]
  have hqZeroNe : q 0 ≠ 0 := by
    rw [hqZero]
    norm_num
  have hqPositive : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < q ε := by
    apply hqContinuous.eventually
    rw [hqZero]
    exact Ioi_mem_nhds zero_lt_one
  have hangle : ∀ᶠ ε in 𝓝 (0 : ℝ),
      (observableMap (slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal =
        Real.arctan (ε ^ 2 * v ε / q ε) - Real.arctan (p ε * ε ^ 2) := by
    filter_upwards [hqPositive] with ε hqε
    have hpath : slowGraphJetPath ε = (ε, p ε, 1 + 8 * ε ^ 3) := by
      simpa only [p] using slowGraphJetPath_apply ε
    have hprojection := congrArg Prod.fst
      (observableMap_endpointAngleIncrements ε (p ε) (1 + 8 * ε ^ 3))
    dsimp only at hprojection
    rw [hpath, hprojection]
    simpa [DFP.FirstLeg.outputGradient, p, B, q, v] using
        endpointAngle_toReal_eq_arctan_sub (p ε * ε ^ 2) (q ε) (ε ^ 2 * v ε) hqε
  let tv : ℝ → ℝ := fun ε ↦ (76 / 5) * ε ^ 3 + (7 / 5) * ε ^ 4
  let rv : ℝ → ℝ := fun ε ↦
    (-16 * ε * (ε - 7) * (ε + 1)) / (5 * B ε)
  let rq : ℝ → ℝ := fun ε ↦
    (2 * (ε + 1) * (3 * ε ^ 4 - 66 * ε ^ 3 - 5)) / (5 * B ε)
  have hBContinuous : ContinuousAt B 0 := by
    dsimp [B]
    fun_prop
  have hBZero : B 0 = 1 := by
    norm_num [B]
  have hBNe : ∀ᶠ ε in 𝓝 (0 : ℝ), B ε ≠ 0 := hBContinuous.eventually_ne (by norm_num [hBZero])
  have hrvContinuous : ContinuousAt rv 0 := by
    dsimp [rv, B]
    fun_prop (disch := norm_num)
  have hrqContinuous : ContinuousAt rq 0 := by
    dsimp [rq, B]
    fun_prop (disch := norm_num)
  have hvFactor : ∀ᶠ ε in 𝓝 (0 : ℝ), v ε - tv ε = rv ε * ε ^ 5 := by
    filter_upwards [hBNe] with ε hBε
    dsimp [v, tv, rv, p, B] at hBε ⊢
    field_simp [hBε]
    ring
  have hqFactor : ∀ᶠ ε in 𝓝 (0 : ℝ), q ε - 1 = rq ε * ε ^ 3 := by
    filter_upwards [hBNe] with ε hBε
    dsimp [q, rq, p, B] at hBε ⊢
    field_simp [hBε]
    ring
  have hvO : (fun ε : ℝ ↦ v ε - tv ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hrO : rv =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) := hrvContinuous.isBigO
    have hproduct := hrO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 (0 : ℝ)))
    have hscaled : (fun ε : ℝ ↦ rv ε * ε ^ 5) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [one_mul] using hproduct
    exact hscaled.congr'
      (hvFactor.mono fun _ h ↦ h.symm) (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hqO : (fun ε : ℝ ↦ q ε - 1) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hrO : rq =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) := hrqContinuous.isBigO
    have hproduct := hrO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 (0 : ℝ)))
    have hscaled : (fun ε : ℝ ↦ rq ε * ε ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
      simpa only [one_mul] using hproduct
    exact hscaled.congr'
      (hqFactor.mono fun _ h ↦ h.symm) (Filter.Eventually.of_forall fun _ ↦ rfl)
  let s₀ : ℝ → ℝ := fun ε ↦ p ε * ε ^ 2
  let s₁ : ℝ → ℝ := fun ε ↦ ε ^ 2 * v ε / q ε
  let t₁ : ℝ → ℝ := fun ε ↦ ε ^ 2 * tv ε
  have hqInvContinuous : ContinuousAt (fun ε ↦ (q ε)⁻¹) 0 :=
    hqContinuous.inv₀ hqZeroNe
  have hqInvO : (fun ε ↦ (q ε)⁻¹) =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hqInvContinuous.isBigO
  have hvDivO : (fun ε : ℝ ↦ (v ε - tv ε) / q ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    have h := hvO.mul hqInvO
    simpa only [div_eq_mul_inv, mul_one] using h
  have hqInvSubO : (fun ε : ℝ ↦ (q ε)⁻¹ - 1) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) := by
    have hraw := hqO.neg_left.mul hqInvO
    have hscaled : (fun ε : ℝ ↦ -(q ε - 1) * (q ε)⁻¹) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
      simpa only [mul_one] using hraw
    refine hscaled.congr' ?_ (Filter.Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [hqContinuous.eventually_ne hqZeroNe] with ε hqε
    field_simp [hqε]
    ring
  let ctv : ℝ → ℝ := fun ε ↦ 76 / 5 + (7 / 5) * ε
  have hctvContinuous : ContinuousAt ctv 0 := by
    dsimp [ctv]
    fun_prop
  have htvO : tv =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 3) := by
    have hcO : ctv =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) := hctvContinuous.isBigO
    have hraw := hcO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 (0 : ℝ)))
    have hscaled : (fun ε : ℝ ↦ ctv ε * ε ^ 3) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 3) := by
      simpa only [one_mul] using hraw
    apply hscaled.congr'
    · apply Filter.Eventually.of_forall
      intro ε
      dsimp [tv, ctv]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hfirstSlopeError :
      (fun ε : ℝ ↦ ε ^ 2 * ((v ε - tv ε) / q ε)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := by
    have h := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 (0 : ℝ))).mul hvDivO
    simpa only [← pow_add, Nat.reduceAdd] using h
  have hsecondSlopeErrorRaw :
      (fun ε : ℝ ↦ ε ^ 2 * (tv ε * ((q ε)⁻¹ - 1))) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) := by
    have hproduct := htvO.mul hqInvSubO
    have h := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 (0 : ℝ))).mul hproduct
    simpa only [← pow_add, Nat.reduceAdd] using h
  have hsecondSlopeError :
      (fun ε : ℝ ↦ ε ^ 2 * (tv ε * ((q ε)⁻¹ - 1))) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hsecondSlopeErrorRaw.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  have hslopeO : (fun ε : ℝ ↦ s₁ ε - t₁ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
    have hsum := hfirstSlopeError.add hsecondSlopeError
    apply hsum.congr'
    · filter_upwards [hqContinuous.eventually_ne hqZeroNe] with ε hqε
      dsimp [s₁, t₁]
      field_simp [hqε]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ by ring
  have ht₁O : t₁ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have h := (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 (0 : ℝ))).mul htvO
    simpa only [t₁, ← pow_add, Nat.reduceAdd] using h
  have hslopeOrderFive : (fun ε : ℝ ↦ s₁ ε - t₁ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) :=
    hslopeO.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 5 < 7)) |>.isBigO
  have hs₁O : s₁ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have h := hslopeOrderFive.add ht₁O
    exact h.congr'
      (Filter.Eventually.of_forall fun ε ↦ by ring)
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hs₁CubeRaw : (fun ε : ℝ ↦ s₁ ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 15) := by
    simpa only [← pow_mul, Nat.reduceMul] using hs₁O.pow 3
  have hs₁Cube : (fun ε : ℝ ↦ s₁ ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) :=
    hs₁CubeRaw.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 15)) |>.isBigO
  have hpContinuous : ContinuousAt p 0 := by
    dsimp [p]
    fun_prop
  have hpO : p =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) := hpContinuous.isBigO
  have hs₀O : s₀ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    have h := hpO.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 (0 : ℝ)))
    simpa only [s₀, one_mul] using h
  let a₀ : ℝ → ℝ := fun ε ↦ 2 * ε ^ 2
  let d₀ : ℝ → ℝ := fun ε ↦ s₀ ε - a₀ ε
  let cd₀ : ℝ → ℝ := fun ε ↦ 198 / 5 - (9 / 5) * ε
  have hcd₀Continuous : ContinuousAt cd₀ 0 := by
    dsimp [cd₀]
    fun_prop
  have hcd₀O : cd₀ =O[𝓝 (0 : ℝ)] (fun _ : ℝ ↦ (1 : ℝ)) :=
    hcd₀Continuous.isBigO
  have hd₀O : d₀ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hraw := hcd₀O.mul
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 5) (𝓝 (0 : ℝ)))
    have hscaled : (fun ε : ℝ ↦ cd₀ ε * ε ^ 5) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) := by
      simpa only [one_mul] using hraw
    apply hscaled.congr'
    · apply Filter.Eventually.of_forall
      intro ε
      dsimp [d₀, s₀, a₀, cd₀, p]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have ha₀O : a₀ =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
    simpa only [a₀] using
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 2) (𝓝 (0 : ℝ))).const_mul_left 2
  have hs₀SqO : (fun ε : ℝ ↦ s₀ ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using hs₀O.pow 2
  have hs₀a₀O : (fun ε : ℝ ↦ s₀ ε * a₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_add, Nat.reduceAdd] using hs₀O.mul ha₀O
  have ha₀SqO : (fun ε : ℝ ↦ a₀ ε ^ 2) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [← pow_mul, Nat.reduceMul] using ha₀O.pow 2
  have hcubeFactorO :
      (fun ε : ℝ ↦ s₀ ε ^ 2 + s₀ ε * a₀ ε + a₀ ε ^ 2) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 4) := by
    simpa only [add_assoc] using hs₀SqO.add (hs₀a₀O.add ha₀SqO)
  have hs₀CubeDiffRaw :
      (fun ε : ℝ ↦ s₀ ε ^ 3 - 8 * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 9) := by
    have hproduct := hd₀O.mul hcubeFactorO
    have hscaled :
        (fun ε : ℝ ↦ d₀ ε *
          (s₀ ε ^ 2 + s₀ ε * a₀ ε + a₀ ε ^ 2)) =O[𝓝 0]
            (fun ε : ℝ ↦ ε ^ 9) := by
      simpa only [← pow_add, Nat.reduceAdd] using hproduct
    apply hscaled.congr'
    · apply Filter.Eventually.of_forall
      intro ε
      dsimp [d₀, a₀]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hs₀CubeDiff :
      (fun ε : ℝ ↦ s₀ ε ^ 3 - 8 * ε ^ 6) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hs₀CubeDiffRaw.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 9)) |>.isBigO
  have hs₀Continuous : ContinuousAt s₀ 0 := by
    dsimp [s₀, p]
    fun_prop
  have hs₀Zero : s₀ 0 = 0 := by
    norm_num [s₀]
  have hs₀Tendsto : Tendsto s₀ (𝓝 0) (𝓝 0) := by
    change Tendsto s₀ (𝓝 0) (𝓝 (s₀ 0)) at hs₀Continuous
    rwa [hs₀Zero] at hs₀Continuous
  have hvContinuous : ContinuousAt v 0 := by
    dsimp [v, p, B]
    fun_prop (disch := norm_num)
  have hs₁Continuous : ContinuousAt s₁ 0 := by
    have hpow : ContinuousAt (fun ε : ℝ ↦ ε ^ 2) 0 := by
      fun_prop
    change ContinuousAt (((fun ε : ℝ ↦ ε ^ 2) * v) / q) 0
    exact (hpow.mul hvContinuous).div hqContinuous hqZeroNe
  have hs₁Zero : s₁ 0 = 0 := by
    norm_num [s₁]
  have hs₁Tendsto : Tendsto s₁ (𝓝 0) (𝓝 0) := by
    change Tendsto s₁ (𝓝 0) (𝓝 (s₁ 0)) at hs₁Continuous
    rwa [hs₁Zero] at hs₁Continuous
  have hatan₀Raw := arctan_sub_cubic_isBigO.comp_tendsto hs₀Tendsto
  have hatan₀OrderEight :
      (fun ε : ℝ ↦ Real.arctan (s₀ ε) - (s₀ ε - s₀ ε ^ 3 / 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) := by
    have h := hatan₀Raw.trans (hs₀O.pow 4)
    change ((fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) ∘ s₀) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8)
    simpa only [← pow_mul, Nat.reduceMul] using h
  have hatan₀ :
      (fun ε : ℝ ↦ Real.arctan (s₀ ε) - (s₀ ε - s₀ ε ^ 3 / 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hatan₀OrderEight.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 8)) |>.isBigO
  have hatan₁Raw := arctan_sub_cubic_isBigO.comp_tendsto hs₁Tendsto
  have hatan₁OrderTwenty :
      (fun ε : ℝ ↦ Real.arctan (s₁ ε) - (s₁ ε - s₁ ε ^ 3 / 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 20) := by
    have h := hatan₁Raw.trans (hs₁O.pow 4)
    change ((fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) ∘ s₁) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 20)
    simpa only [← pow_mul, Nat.reduceMul] using h
  have hatan₁ :
      (fun ε : ℝ ↦ Real.arctan (s₁ ε) - (s₁ ε - s₁ ε ^ 3 / 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) :=
    hatan₁OrderTwenty.trans_isLittleO
      (Asymptotics.isLittleO_pow_pow (by norm_num : 7 < 20)) |>.isBigO
  have hs₁CubeScaled : (fun ε : ℝ ↦ -(1 / 3) * s₁ ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := hs₁Cube.const_mul_left (-(1 / 3))
  have hs₀CubeScaled : (fun ε : ℝ ↦ (1 / 3) * (s₀ ε ^ 3 - 8 * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := hs₀CubeDiff.const_mul_left (1 / 3)
  have hpolynomial := hslopeO.add (hs₁CubeScaled.add hs₀CubeScaled)
  have hpolynomial' :
      (fun ε : ℝ ↦
        (s₁ ε - s₁ ε ^ 3 / 3) - (s₀ ε - s₀ ε ^ 3 / 3) -
          (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 7) := by
    apply hpolynomial.congr'
    · apply Filter.Eventually.of_forall
      intro ε
      dsimp [t₁, tv, s₀, p]
      ring
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have htotal := hatan₁.add (hpolynomial'.add hatan₀.neg_left)
  apply htotal.congr'
  · filter_upwards [hangle] with ε hε
    rw [hε]
    dsimp [s₁, s₀]
    ring
  · exact Filter.Eventually.of_forall fun _ ↦ rfl

/-- Along the slow-graph path, the canonical real lift of the second endpoint-gradient
angle increment is
`-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6 + O(ε ^ 7)`. -/
theorem slowSecond :
    (fun ε : ℝ ↦
      (observableMap (slowGraphJetPath ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  exact slowSecondRemainder

end DFP.TwoLeg.EndpointAngleJet
