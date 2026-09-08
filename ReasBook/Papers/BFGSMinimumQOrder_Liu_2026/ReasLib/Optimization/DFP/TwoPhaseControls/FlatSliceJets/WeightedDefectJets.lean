module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.AnalyticJetGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.PureScaleJets
public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.GermCongruence
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg

private def weightedPath (P₃ H₃ P₄ H₄ : ℝ) (ε : ℝ) : ℝ × ℝ × ℝ :=
  (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
    1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)

private def radiusPath (P₃ H₃ P₄ H₄ : ℝ) (ε : ℝ) : ℝ :=
  radiusFactor ε
    (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
    (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)

private def signedPath (P₃ H₃ P₄ H₄ : ℝ) (ε : ℝ) : ℝ :=
  ε * Real.sqrt (radiusPath P₃ H₃ P₄ H₄ ε)

private theorem weightedPath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (weightedPath P₃ H₃ P₄ H₄) 0 := by
  unfold weightedPath
  fun_prop

private theorem radiusPath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (radiusPath P₃ H₃ P₄ H₄) 0 := by
  have houter : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ => radiusFactor x.1 x.2.1 x.2.2)
      (weightedPath P₃ H₃ P₄ H₄ 0) := by
    simpa [weightedPath] using analyticAt_radiusFactor
  have h := houter.comp
    (f := weightedPath P₃ H₃ P₄ H₄)
    (weightedPath_analyticAt P₃ H₃ P₄ H₄)
  change AnalyticAt ℝ
    (fun ε : ℝ => radiusFactor ε
      (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
      (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0
  simpa only [Function.comp_def, weightedPath] using h

private theorem radiusPath_zero (P₃ H₃ P₄ H₄ : ℝ) :
    radiusPath P₃ H₃ P₄ H₄ 0 = 1 := by
  simp [radiusPath, radiusFactor_base]

private theorem signedPath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (signedPath P₃ H₃ P₄ H₄) 0 := by
  have hr := radiusPath_analyticAt P₃ H₃ P₄ H₄
  have hr0 : radiusPath P₃ H₃ P₄ H₄ 0 ≠ 0 := by
    rw [radiusPath_zero]
    norm_num
  exact analyticAt_id.mul (hr.sqrt hr0)

private theorem signedPath_zero (P₃ H₃ P₄ H₄ : ℝ) :
    signedPath P₃ H₃ P₄ H₄ 0 = 0 := by
  simp [signedPath]

private theorem eqModPow_mono {n m : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow m f g) (hnm : n ≤ m) : EqModPow n f g := by
  obtain rfl | hlt := hnm.eq_or_lt
  · exact h
  · unfold EqModPow at h ⊢
    exact h.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO

private theorem eqModPow_mul_id {n : ℕ} {f g : ℝ → ℝ}
    (h : EqModPow n f g) :
    EqModPow (n + 1) (fun ε => ε * f ε) (fun ε => ε * g ε) := by
  unfold EqModPow at h ⊢
  have hprod := (Asymptotics.isBigO_refl (fun ε : ℝ => ε) (𝓝 0)).mul h
  refine hprod.congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε => by ring)
  · exact Filter.Eventually.of_forall (fun ε => by
      change ε * ε ^ n = ε ^ (n + 1)
      rw [pow_succ]; ring)

/-- The full weighted radius expansion as an order-five function germ. -/
private theorem weightedNormalizedRadiusGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5 (radiusPath P₃ H₃ P₄ H₄)
      (fun ε : ℝ =>
        1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
          ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) := by
  have hjet :=
    weightedNormalizedRadiusJet_via_scaleStationarity P₃ H₃ P₄ H₄
  have hjet' :
      FiniteTaylorJet.ofFunction ℝ 4 (radiusPath P₃ H₃ P₄ H₄) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ =>
            1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
              ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0 := by
    change
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => radiusFactor ε
            (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)
            (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ =>
            1 + ((6 * H₃ + 5 * P₃ - 300) / 18) * ε ^ 3 +
              ((6 * H₄ + 5 * P₄ + 54) / 18) * ε ^ 4) 0
    exact hjet
  simpa using EqModPow.of_analytic_jet_eq
    (radiusPath_analyticAt P₃ H₃ P₄ H₄) (by fun_prop) hjet'

/-- The updated signed scale differs from the input scale only by `O(ε^4)`. -/
private theorem weightedSignedScale_identityGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 4 (signedPath P₃ H₃ P₄ H₄) (fun ε : ℝ => ε) := by
  let A : ℝ := (6 * H₃ + 5 * P₃ - 300) / 18
  let B : ℝ := (6 * H₄ + 5 * P₄ + 54) / 18
  have hr5 := weightedNormalizedRadiusGerm P₃ H₃ P₄ H₄
  have hr3poly :
      EqModPow 3
        (fun ε : ℝ => 1 + A * ε ^ 3 + B * ε ^ 4)
        (fun _ : ℝ => 1) := by
    apply EqModPow.of_factor (q := fun ε : ℝ => A + B * ε)
    · fun_prop
    · intro ε
      ring
  have hr3 :
      EqModPow 3 (radiusPath P₃ H₃ P₄ H₄) (fun _ : ℝ => 1) := by
    have hr5' :
        EqModPow 5 (radiusPath P₃ H₃ P₄ H₄)
          (fun ε : ℝ => 1 + A * ε ^ 3 + B * ε ^ 4) := by
      simpa only [A, B] using hr5
    exact (eqModPow_mono hr5' (by norm_num)).trans hr3poly
  have hsquare :
      EqModPow 3 (radiusPath P₃ H₃ P₄ H₄)
        (fun ε : ℝ => ((1 : ℝ) : ℝ) ^ 2) := by
    simpa using hr3
  have hsqrt :
      EqModPow 3 (fun ε => Real.sqrt (radiusPath P₃ H₃ P₄ H₄ ε))
        (fun _ : ℝ => 1) := by
    apply EqModPow.sqrt_of_sq hsquare
    · exact (radiusPath_analyticAt P₃ H₃ P₄ H₄).continuousAt
    · fun_prop
    · rw [radiusPath_zero]
      norm_num
    · norm_num
  change EqModPow 4
    (fun ε => ε * Real.sqrt (radiusPath P₃ H₃ P₄ H₄ ε))
    (fun ε : ℝ => ε)
  simpa only [Nat.reduceAdd, mul_one] using eqModPow_mul_id hsqrt

/-- Cubing the updated signed scale agrees with cubing the input modulo `O(ε^5)`. -/
private theorem weightedSignedScale_cubeGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5 (fun ε => signedPath P₃ H₃ P₄ H₄ ε ^ 3)
      (fun ε : ℝ => ε ^ 3) := by
  let y := signedPath P₃ H₃ P₄ H₄
  let q : ℝ → ℝ := fun ε => y ε ^ 2 + y ε * ε + ε ^ 2
  have hy := weightedSignedScale_identityGerm P₃ H₃ P₄ H₄
  have hyAnalytic : AnalyticAt ℝ y 0 := signedPath_analyticAt P₃ H₃ P₄ H₄
  have hqAnalytic : AnalyticAt ℝ q 0 := by
    exact ((hyAnalytic.pow 2).add (hyAnalytic.mul analyticAt_id)).add
      (analyticAt_id.pow 2)
  have hqO : q =O[𝓝 0] (fun ε : ℝ => ε) := by
    have h := hqAnalytic.differentiableAt.isBigO_sub
    simpa [q, y, signedPath_zero] using h
  unfold EqModPow at hy ⊢
  have hprod := hy.mul hqO
  refine hprod.congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε => by dsimp only [q, y]; ring)
  · exact Filter.Eventually.of_forall (fun ε => by ring)

/-- The fourth power of the updated signed scale agrees with the input fourth power
modulo `O(ε^5)`. -/
private theorem weightedSignedScale_fourthGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5 (fun ε => signedPath P₃ H₃ P₄ H₄ ε ^ 4)
      (fun ε : ℝ => ε ^ 4) := by
  let y := signedPath P₃ H₃ P₄ H₄
  let q : ℝ → ℝ := fun ε =>
    y ε ^ 3 + y ε ^ 2 * ε + y ε * ε ^ 2 + ε ^ 3
  have hy := weightedSignedScale_identityGerm P₃ H₃ P₄ H₄
  have hyAnalytic : AnalyticAt ℝ y 0 := signedPath_analyticAt P₃ H₃ P₄ H₄
  have hqAnalytic : AnalyticAt ℝ q 0 := by
    exact (((hyAnalytic.pow 3).add ((hyAnalytic.pow 2).mul analyticAt_id)).add
      (hyAnalytic.mul (analyticAt_id.pow 2))).add (analyticAt_id.pow 3)
  have hqO : q =O[𝓝 0] (fun ε : ℝ => ε) := by
    have h := hqAnalytic.differentiableAt.isBigO_sub
    simpa [q, y, signedPath_zero] using h
  unfold EqModPow at hy ⊢
  have hprod := hy.mul hqO
  refine hprod.congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε => by dsimp only [q, y]; ring)
  · exact Filter.Eventually.of_forall (fun ε => by ring)

private def statePath (P₃ H₃ P₄ H₄ : ℝ) : ℝ → ℝ × ℝ × ℝ :=
  stateMap ∘ weightedPath P₃ H₃ P₄ H₄

private def shapePath (P₃ H₃ P₄ H₄ : ℝ) (ε : ℝ) : ℝ :=
  (statePath P₃ H₃ P₄ H₄ ε).2.1

private def highPath (P₃ H₃ P₄ H₄ : ℝ) (ε : ℝ) : ℝ :=
  (statePath P₃ H₃ P₄ H₄ ε).2.2

private theorem statePath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (statePath P₃ H₃ P₄ H₄) 0 := by
  have houter : AnalyticAt ℝ stateMap (weightedPath P₃ H₃ P₄ H₄ 0) := by
    simpa [weightedPath] using stateMapAnalytic
  exact houter.comp (weightedPath_analyticAt P₃ H₃ P₄ H₄)

private theorem shapePath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (shapePath P₃ H₃ P₄ H₄) 0 := by
  exact analyticAt_fst.comp (analyticAt_snd.comp
    (statePath_analyticAt P₃ H₃ P₄ H₄))

private theorem highPath_analyticAt (P₃ H₃ P₄ H₄ : ℝ) :
    AnalyticAt ℝ (highPath P₃ H₃ P₄ H₄) 0 := by
  exact analyticAt_snd.comp (analyticAt_snd.comp
    (statePath_analyticAt P₃ H₃ P₄ H₄))

private theorem eqModPow_congr_right {n : ℕ} {f g k : ℝ → ℝ}
    (h : EqModPow n f g) (hg : ∀ ε, k ε = g ε) : EqModPow n f k := by
  unfold EqModPow at h ⊢
  refine h.congr' (Filter.Eventually.of_forall fun ε => ?_)
    (Filter.Eventually.of_forall fun _ => rfl)
  change f ε - g ε = f ε - k ε
  rw [hg ε]

private theorem weightedShapeGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5 (shapePath P₃ H₃ P₄ H₄)
      (fun ε : ℝ =>
        2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
          ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) := by
  have hjet := weightedTransversePJet_via_scaleStationarity P₃ H₃ P₄ H₄
  have hjet' :
      FiniteTaylorJet.ofFunction ℝ 4 (shapePath P₃ H₃ P₄ H₄) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ =>
            2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
              ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 := by
    change
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ =>
            (stateMap
              (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.1) 0 = _
    exact hjet
  simpa using EqModPow.of_analytic_jet_eq
    (shapePath_analyticAt P₃ H₃ P₄ H₄) (by fun_prop) hjet'

private theorem weightedHighGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5 (highPath P₃ H₃ P₄ H₄)
      (fun ε : ℝ => 1 + 8 * ε ^ 3) := by
  have hjet := weightedTransverseHJet_via_scaleStationarity P₃ H₃ P₄ H₄
  have hjet' :
      FiniteTaylorJet.ofFunction ℝ 4 (highPath P₃ H₃ P₄ H₄) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ => 1 + 8 * ε ^ 3) 0 := by
    change
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ =>
            (stateMap
              (ε, 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4,
                1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)).2.2) 0 = _
    exact hjet
  simpa using EqModPow.of_analytic_jet_eq
    (highPath_analyticAt P₃ H₃ P₄ H₄) (by fun_prop) hjet'

private theorem nextShapeGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5
      (fun ε =>
        2 + P₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
          P₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4)
      (fun ε : ℝ => 2 + P₃ * ε ^ 3 + P₄ * ε ^ 4) := by
  have h3 := weightedSignedScale_cubeGerm P₃ H₃ P₄ H₄
  have h4 := weightedSignedScale_fourthGerm P₃ H₃ P₄ H₄
  have hy := signedPath_analyticAt P₃ H₃ P₄ H₄
  have hP3 := EqModPow.mul (EqModPow.refl 5 (fun _ : ℝ => P₃)) h3
    continuousAt_const (hy.pow 3).continuousAt
  have hP4 := EqModPow.mul (EqModPow.refl 5 (fun _ : ℝ => P₄)) h4
    continuousAt_const (hy.pow 4).continuousAt
  exact (EqModPow.refl 5 (fun _ : ℝ => 2)).add hP3 |>.add hP4

private theorem nextHighGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5
      (fun ε =>
        1 + H₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
          H₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4)
      (fun ε : ℝ => 1 + H₃ * ε ^ 3 + H₄ * ε ^ 4) := by
  have h3 := weightedSignedScale_cubeGerm P₃ H₃ P₄ H₄
  have h4 := weightedSignedScale_fourthGerm P₃ H₃ P₄ H₄
  have hy := signedPath_analyticAt P₃ H₃ P₄ H₄
  have hH3 := EqModPow.mul (EqModPow.refl 5 (fun _ : ℝ => H₃)) h3
    continuousAt_const (hy.pow 3).continuousAt
  have hH4 := EqModPow.mul (EqModPow.refl 5 (fun _ : ℝ => H₄)) h4
    continuousAt_const (hy.pow 4).continuousAt
  exact (EqModPow.refl 5 (fun _ : ℝ => 1)).add hH3 |>.add hH4

private theorem shapeDefectGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5
      (fun ε =>
        shapePath P₃ H₃ P₄ H₄ ε -
          (2 + P₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            P₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4))
      (fun ε : ℝ =>
        ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
          ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) := by
  have h := (weightedShapeGerm P₃ H₃ P₄ H₄).sub
    (nextShapeGerm P₃ H₃ P₄ H₄)
  apply eqModPow_congr_right h
  intro ε
  ring

private theorem highDefectGerm (P₃ H₃ P₄ H₄ : ℝ) :
    EqModPow 5
      (fun ε =>
        highPath P₃ H₃ P₄ H₄ ε -
          (1 + H₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            H₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4))
      (fun ε : ℝ => (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) := by
  have h := (weightedHighGerm P₃ H₃ P₄ H₄).sub
    (nextHighGerm P₃ H₃ P₄ H₄)
  apply eqModPow_congr_right h
  intro ε
  ring

/-- The shape graph-invariance defect jet, with its scalar and mixed expansions
discharged by scale stationarity. -/
theorem weightedTransversePDefectJet_via_scaleStationarity
    (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          let x := graphJetPath P₃ H₃ P₄ H₄ ε
          let y := stateMap x
          let nextGraph := graphJetPath P₃ H₃ P₄ H₄ y.1
          y.2.1 - nextGraph.2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0 := by
  change FiniteTaylorJet.ofFunction ℝ 4
      (fun ε : ℝ =>
        shapePath P₃ H₃ P₄ H₄ ε -
          (2 + P₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            P₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4)) 0 = _
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
  · have hy := signedPath_analyticAt P₃ H₃ P₄ H₄
    have hnext : AnalyticAt ℝ
        (fun ε : ℝ =>
          2 + P₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            P₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4) 0 := by
      exact (analyticAt_const.add (analyticAt_const.mul (hy.pow 3))).add
        (analyticAt_const.mul (hy.pow 4))
    exact ((shapePath_analyticAt P₃ H₃ P₄ H₄).sub hnext).contDiffAt
  · fun_prop
  · simpa [EqModPow] using shapeDefectGerm P₃ H₃ P₄ H₄

/-- The high-coordinate graph-invariance defect jet, with its scalar and mixed
expansions discharged by scale stationarity. -/
theorem weightedTransverseHDefectJet_via_scaleStationarity
    (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ =>
          let x := graphJetPath P₃ H₃ P₄ H₄ ε
          let y := stateMap x
          let nextGraph := graphJetPath P₃ H₃ P₄ H₄ y.1
          y.2.2 - nextGraph.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ => (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) 0 := by
  change FiniteTaylorJet.ofFunction ℝ 4
      (fun ε : ℝ =>
        highPath P₃ H₃ P₄ H₄ ε -
          (1 + H₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            H₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4)) 0 = _
  apply FiniteTaylorJet.ofFunction_eq_of_sub_isBigO_succ
  · have hy := signedPath_analyticAt P₃ H₃ P₄ H₄
    have hnext : AnalyticAt ℝ
        (fun ε : ℝ =>
          1 + H₃ * signedPath P₃ H₃ P₄ H₄ ε ^ 3 +
            H₄ * signedPath P₃ H₃ P₄ H₄ ε ^ 4) 0 := by
      exact (analyticAt_const.add (analyticAt_const.mul (hy.pow 3))).add
        (analyticAt_const.mul (hy.pow 4))
    exact ((highPath_analyticAt P₃ H₃ P₄ H₄).sub hnext).contDiffAt
  · fun_prop
  · simpa [EqModPow] using highDefectGerm P₃ H₃ P₄ H₄

end DFP.TwoLeg
