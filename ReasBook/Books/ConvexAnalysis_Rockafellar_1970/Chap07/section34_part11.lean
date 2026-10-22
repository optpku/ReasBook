/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part10

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart11 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

/-- Helper for Text 34.1.1: the mixed lower closure takes the value `0` at the origin. -/
lemma helperForText_34_1_1_mixedLowerClosure_origin_eq_zero :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) 0 0 = ((0 : ℝ) : EReal) := by
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · -- Each local infimum is bounded above by an open-interval witness, and that witness already
    -- has inner first closure equal to `0`.
    refine iSup_le ?_
    intro ε
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval 0
        (by simp [InClosedUnitInterval]) ε with ⟨w, hwOpen⟩
    calc
      (⨅ w' : {w' : Fin 1 → ℝ // ‖w' - 0‖ < ε.1}, partialClosure₁ openUnitSquarePowerSaddle 0 w'.1)
          ≤ partialClosure₁ openUnitSquarePowerSaddle 0 w.1 := iInf_le _ w
      _ = ((0 : ℝ) : EReal) :=
        helperForText_34_1_1_partialClosure1_zero_eq_zero_of_openSecond hwOpen
  · -- Conversely, one fixed positive radius already has all local first-closure values at least
    -- `0`, so the outer supremum is also at least `0`.
    let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, by positivity⟩
    refine le_trans ?_
      (le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - 0‖ < ε'.1}, partialClosure₁ openUnitSquarePowerSaddle 0 w.1)
        ε)
    refine le_iInf ?_
    intro w
    by_cases hwOpen : InOpenUnitInterval w.1
    · rw [helperForText_34_1_1_partialClosure1_zero_eq_zero_of_openSecond hwOpen]
    · rw [helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval hwOpen]
      exact le_top

/-- Helper for Text 34.1.1: if `v` already lies outside `[0, 1]`, then the mixed lower closure
`cl₂(cl₁ K)` stays constantly `⊤`. -/
lemma helperForText_34_1_1_mixedLowerClosure_eq_top_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ⊤ := by
  rcases helperForText_34_1_1_exists_radius_outside_closedUnitInterval v hv with ⟨ε, hε⟩
  -- A small second-variable neighborhood misses `(0,1)`, so the inner first closure is
  -- constantly `⊤` there.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm le_top
  have hLocal :
      (⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
          partialClosure₁ openUnitSquarePowerSaddle u w.1) = ⊤ := by
    apply le_antisymm le_top
    refine le_iInf ?_
    intro w
    rw [helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval (hε w)]
  calc
    (⊤ : EReal)
        ≤ ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
            partialClosure₁ openUnitSquarePowerSaddle u w.1 := by
          rw [hLocal]
    _ ≤
      ⨆ ε' : {ε' : ℝ // 0 < ε'},
        ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1},
          partialClosure₁ openUnitSquarePowerSaddle u w.1 :=
        le_iSup
          (fun ε' : {ε' : ℝ // 0 < ε'} =>
            ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1},
              partialClosure₁ openUnitSquarePowerSaddle u w.1)
          ε

/-- Helper for Text 34.1.1: if `u` lies outside `[0, 1]` while `v` stays in `[0, 1]`, then the
mixed lower closure `cl₂(cl₁ K)` is already `⊥`. -/
lemma helperForText_34_1_1_mixedLowerClosure_eq_bot_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hu : ¬ InClosedUnitInterval u) (hv : InClosedUnitInterval v) :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ⊥ := by
  -- Every `v`-ball inside `[0,1]` contains an open second-variable witness where the inner
  -- first closure has already dropped to `⊥`.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval v hv ε with
      ⟨w, hwOpen⟩
    calc
      (⨅ z : {z : Fin 1 → ℝ // ‖z - v‖ < ε.1}, partialClosure₁ openUnitSquarePowerSaddle u z.1)
          ≤ partialClosure₁ openUnitSquarePowerSaddle u w.1 := iInf_le _ w
      _ = ⊥ := helperForText_34_1_1_partialClosure1_eq_bot_of_not_inClosedUnitInterval hu hwOpen
  · exact bot_le

/-- Helper for Text 34.1.1: if the first coordinate is `0` and both variables lie in `[0,1]`,
then the mixed lower closure `cl₂(cl₁ K)` takes the boundary value `0`. -/
lemma helperForText_34_1_1_mixedLowerClosure_zeroFirst_eq_zero_of_closedSecond
    {u v : Fin 1 → ℝ} (hu0 : u 0 = 0) (_hu : InClosedUnitInterval u)
    (hv : InClosedUnitInterval v) :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ((0 : ℝ) : EReal) := by
  have huZero : u = 0 := by
    ext i
    fin_cases i
    simpa using hu0
  -- Rewrite to the literal origin in the first variable and repeat the same inf/sup argument as
  -- at `(0,0)`, now centered at an arbitrary closed second-variable point.
  rw [huZero]
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval v hv ε with
      ⟨w, hwOpen⟩
    calc
      (⨅ z : {z : Fin 1 → ℝ // ‖z - v‖ < ε.1}, partialClosure₁ openUnitSquarePowerSaddle 0 z.1)
          ≤ partialClosure₁ openUnitSquarePowerSaddle 0 w.1 := iInf_le _ w
      _ = ((0 : ℝ) : EReal) :=
        helperForText_34_1_1_partialClosure1_zero_eq_zero_of_openSecond hwOpen
  · let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, by positivity⟩
    refine le_trans ?_
      (le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, partialClosure₁ openUnitSquarePowerSaddle 0 w.1)
        ε)
    refine le_iInf ?_
    intro w
    by_cases hwOpen : InOpenUnitInterval w.1
    · rw [helperForText_34_1_1_partialClosure1_zero_eq_zero_of_openSecond hwOpen]
    · rw [helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval hwOpen]
      exact le_top

/-- Helper for Text 34.1.1: on the closed square away from the zero base, the mixed lower
closure `cl₂(cl₁ K)` already recovers the original power kernel `u^v`. -/
lemma helperForText_34_1_1_mixedLowerClosure_eq_powerKernel_of_closedSquare_nonzeroFirst
    {u v : Fin 1 → ℝ} (hu : InClosedUnitInterval u) (hv : InClosedUnitInterval v)
    (hu0 : u 0 ≠ 0) :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v =
      oneDimensionalPowerKernel u v := by
  have hCont : ContinuousAt (fun x : ℝ => (u 0) ^ x) (v 0) :=
    Real.continuousAt_const_rpow hu0
  have hNonnegClosure :
      ((0 : ℝ) : EReal) ≤ partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v := by
    -- A single neighborhood already has all inner first-closure values in `[0,+∞]`: open
    -- second-variable points give real powers, and the rest contribute `⊤`.
    unfold partialClosure₂ convexClosureInSecond
    let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, by positivity⟩
    refine le_trans ?_
      (le_iSup
        (fun ε' : {ε' : ℝ // 0 < ε'} =>
          ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1}, partialClosure₁ openUnitSquarePowerSaddle u w.1)
        ε)
    refine le_iInf ?_
    intro w
    by_cases hwOpen : InOpenUnitInterval w.1
    · have hValue :
          partialClosure₁ openUnitSquarePowerSaddle u w.1 = oneDimensionalPowerKernel u w.1 := by
        rw [helperForText_34_1_1_partialClosure1_formula]
        simp [hwOpen, hu]
      have hrpow : 0 ≤ (u 0) ^ (w.1 0) := Real.rpow_nonneg hu.1 _
      rw [hValue]
      simpa [oneDimensionalPowerKernel] using hrpow
    · rw [helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval hwOpen]
      exact le_top
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm
  · -- Approximate `v` by open-interval points and rewrite the inner first closure by the
    -- already-proved `cl₁` formula on the closed strip.
    refine (EReal.le_of_forall_lt_iff_le (x := oneDimensionalPowerKernel u v)
      (y := ⨆ ε : {ε : ℝ // 0 < ε},
        ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
          partialClosure₁ openUnitSquarePowerSaddle u w.1)).1 ?_
    intro zr hz
    have hzReal : (u 0) ^ (v 0) < zr := by
      simpa [oneDimensionalPowerKernel] using hz
    refine iSup_le ?_
    intro ε
    have hGap : 0 < zr - (u 0) ^ (v 0) := by
      linarith
    rcases (Metric.continuousAt_iff.mp hCont) (zr - (u 0) ^ (v 0)) hGap with ⟨δ, hδPos, hδ⟩
    let η : {r : ℝ // 0 < r} := by
      refine ⟨min δ (ε.1 / 2), ?_⟩
      apply lt_min
      · exact hδPos
      · linarith [ε.2]
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval v hv η with
      ⟨w, hwOpen⟩
    have hwInEps : ‖w.1 - v‖ < ε.1 := by
      have hwHalf : ‖w.1 - v‖ < ε.1 / 2 := lt_of_lt_of_le w.2 (min_le_right _ _)
      linarith [ε.2]
    have hwNorm : ‖w.1 - v‖ < δ := lt_of_lt_of_le w.2 (min_le_left _ _)
    rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
    have hwCoord : dist (w.1 0) (v 0) < δ := by
      simpa [Real.dist_eq] using hwNorm
    have hPowDist : dist ((u 0) ^ (w.1 0)) ((u 0) ^ (v 0)) < zr - (u 0) ^ (v 0) := hδ hwCoord
    have hAbs : |(u 0) ^ (w.1 0) - (u 0) ^ (v 0)| < zr - (u 0) ^ (v 0) := by
      simpa [Real.dist_eq] using hPowDist
    have hPowLt : (u 0) ^ (w.1 0) < zr := by
      have hUpper : (u 0) ^ (w.1 0) - (u 0) ^ (v 0) < zr - (u 0) ^ (v 0) :=
        (abs_lt.mp hAbs).2
      linarith
    have hValue :
        partialClosure₁ openUnitSquarePowerSaddle u w.1 = oneDimensionalPowerKernel u w.1 := by
      rw [helperForText_34_1_1_partialClosure1_formula]
      simp [hwOpen, hu]
    exact le_trans (iInf_le _ ⟨w.1, hwInEps⟩) <| by
      rw [hValue]
      simpa [oneDimensionalPowerKernel] using hPowLt.le
  · -- Any lower barrier below `u^v` survives on a sufficiently small neighborhood; open points
    -- stay above the barrier by continuity, and non-open points contribute only `⊤`.
    refine (forall_lt_iff_le).1 ?_
    intro z hz
    cases z using EReal.rec with
    | bot =>
        have hNonneg :
            ((0 : ℝ) : EReal) ≤
              ⨆ ε : {ε : ℝ // 0 < ε},
                ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
                  partialClosure₁ openUnitSquarePowerSaddle u w.1 := by
          simpa [partialClosure₂, convexClosureInSecond] using hNonnegClosure
        exact lt_of_lt_of_le (by norm_num) hNonneg
    | coe zr =>
        have hzReal : zr < (u 0) ^ (v 0) := by
          simpa [oneDimensionalPowerKernel] using hz
        by_cases hzNonneg : 0 ≤ zr
        · let β : ℝ := (zr + (u 0) ^ (v 0)) / 2
          have hzBeta : zr < β := by
            dsimp [β]
            linarith
          have hGap : 0 < (u 0) ^ (v 0) - β := by
            dsimp [β]
            linarith
          rcases (Metric.continuousAt_iff.mp hCont) ((u 0) ^ (v 0) - β) hGap with
            ⟨δ, hδPos, hδ⟩
          let ε : {ε : ℝ // 0 < ε} := ⟨δ, hδPos⟩
          have hLocal :
              (β : EReal) ≤
                ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
                  partialClosure₁ openUnitSquarePowerSaddle u w.1 := by
            refine le_iInf ?_
            intro w
            by_cases hwOpen : InOpenUnitInterval w.1
            · have hwNorm : ‖w.1 - v‖ < δ := w.2
              rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
              have hwCoord : dist (w.1 0) (v 0) < δ := by
                simpa [Real.dist_eq] using hwNorm
              have hPowDist :
                  dist ((u 0) ^ (w.1 0)) ((u 0) ^ (v 0)) < (u 0) ^ (v 0) - β :=
                hδ hwCoord
              have hAbs : |(u 0) ^ (w.1 0) - (u 0) ^ (v 0)| < (u 0) ^ (v 0) - β := by
                simpa [Real.dist_eq] using hPowDist
              have hPowGt : β < (u 0) ^ (w.1 0) := by
                have hLower :
                    -((u 0) ^ (v 0) - β) < (u 0) ^ (w.1 0) - (u 0) ^ (v 0) :=
                  (abs_lt.mp hAbs).1
                linarith
              have hValue :
                  partialClosure₁ openUnitSquarePowerSaddle u w.1 =
                    oneDimensionalPowerKernel u w.1 := by
                rw [helperForText_34_1_1_partialClosure1_formula]
                simp [hwOpen, hu]
              exact le_of_lt <| by
                rw [hValue]
                simpa [oneDimensionalPowerKernel] using hPowGt
            · rw [helperForText_34_1_1_partialClosure1_eq_top_of_not_inOpenUnitInterval hwOpen]
              exact le_top
          have hClosureLower :
              (β : EReal) ≤
                ⨆ ε : {ε : ℝ // 0 < ε},
                  ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε.1},
                    partialClosure₁ openUnitSquarePowerSaddle u w.1 :=
            le_trans hLocal
              (le_iSup
                (fun ε' : {ε' : ℝ // 0 < ε'} =>
                  ⨅ w : {w : Fin 1 → ℝ // ‖w - v‖ < ε'.1},
                    partialClosure₁ openUnitSquarePowerSaddle u w.1)
                ε)
          exact lt_of_lt_of_le (by exact_mod_cast hzBeta) hClosureLower
        · have hNeg : (zr : EReal) < ((0 : ℝ) : EReal) := by
            exact_mod_cast lt_of_not_ge hzNonneg
          exact lt_of_lt_of_le hNeg hNonnegClosure
    | top =>
        exfalso
        exact not_lt_of_ge le_top hz

/-- Helper for Text 34.1.1: when the second coordinate already lies outside `[0,1]`, the imported
lower formula takes its final `⊤` branch. -/
lemma helperForText_34_1_1_importedLowerFormula_eq_top_of_not_inClosedUnitInterval_second
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    openUnitSquarePowerLowerClosureFormula u v = ⊤ := by
  have hNotOrigin : ¬ (u 0 = 0 ∧ v 0 = 0) := by
    intro hOrigin
    apply hv
    constructor <;> linarith [hOrigin.2]
  simp [openUnitSquarePowerLowerClosureFormula, hNotOrigin, hv]

/-- Helper for Text 34.1.1: evaluating the mixed lower closure and the imported lower formula at
the off-off point `(2, 2)` now yields the same value `⊤`. -/
lemma helperForText_34_1_1_mixedLowerClosure_counterexample_values :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle)
        (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) = ⊤ ∧
      openUnitSquarePowerLowerClosureFormula
        (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) = ⊤ := by
  constructor
  · refine helperForText_34_1_1_mixedLowerClosure_eq_top_of_not_inClosedUnitInterval ?_
    simp [InClosedUnitInterval]
  · refine
      helperForText_34_1_1_importedLowerFormula_eq_top_of_not_inClosedUnitInterval_second ?_
    simp [InClosedUnitInterval]

/-- Helper for Text 34.1.1: this is the corrected pointwise formula for `cl₂(cl₁ K)` that the
part-3 branch computations actually prove, before comparing with the imported part-2 formula. -/
noncomputable def helperForText_34_1_1_correctedMixedLowerClosureFormula : SaddleFunction 1 1 :=
  fun u v =>
    if u 0 = 0 ∧ v 0 = 0 then
      ((0 : ℝ) : EReal)
    else if InClosedUnitInterval v then
      if InClosedUnitInterval u then oneDimensionalPowerKernel u v else ⊥
    else
      ⊤

/-- Helper for Text 34.1.1: the corrected local lower-closure formula returns `⊤` whenever the
second coordinate already lies outside `[0,1]`. -/
lemma helperForText_34_1_1_correctedMixedLowerClosureFormula_eq_top_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    helperForText_34_1_1_correctedMixedLowerClosureFormula u v = ⊤ := by
  -- A second-variable off-domain point cannot be the distinguished origin, so the corrected
  -- piecewise formula falls through to its final `⊤` branch.
  have hNotOrigin : ¬ (u 0 = 0 ∧ v 0 = 0) := by
    intro hOrigin
    apply hv
    constructor <;> linarith [hOrigin.2]
  simp [helperForText_34_1_1_correctedMixedLowerClosureFormula, hNotOrigin, hv]

/-- Helper for Text 34.1.1: the actual mixed lower closure agrees with the corrected local
formula obtained by splitting first on `v ∈ [0,1]` and only then on `u ∈ [0,1]`. -/
lemma helperForText_34_1_1_mixedLowerClosure_eq_correctedFormula :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) =
      helperForText_34_1_1_correctedMixedLowerClosureFormula := by
  funext u
  funext v
  by_cases hOrigin : u 0 = 0 ∧ v 0 = 0
  · rcases hOrigin with ⟨hu0, hv0⟩
    have hOrigin' : u 0 = 0 ∧ v 0 = 0 := ⟨hu0, hv0⟩
    have hu : InClosedUnitInterval u := by
      constructor <;> linarith
    have hv : InClosedUnitInterval v := by
      constructor <;> linarith
    -- At the distinguished origin, the mixed lower closure already has the special value `0`.
    have hValue :
        partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ((0 : ℝ) : EReal) :=
      helperForText_34_1_1_mixedLowerClosure_zeroFirst_eq_zero_of_closedSecond hu0 hu hv
    simpa [helperForText_34_1_1_correctedMixedLowerClosureFormula, hOrigin'] using hValue
  · by_cases hv : InClosedUnitInterval v
    · by_cases hu : InClosedUnitInterval u
      · by_cases hu0 : u 0 = 0
        · have hValue :
              partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v =
                ((0 : ℝ) : EReal) :=
            helperForText_34_1_1_mixedLowerClosure_zeroFirst_eq_zero_of_closedSecond hu0 hu hv
          have hv0_ne : v 0 ≠ 0 := by
            intro hv0
            exact hOrigin ⟨hu0, hv0⟩
          have hKernelZero : oneDimensionalPowerKernel u v = ((0 : ℝ) : EReal) := by
            -- Away from the origin, the base `u = 0` forces the finite power branch to be `0`.
            simp [oneDimensionalPowerKernel, hu0, hv0_ne]
          calc
            partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v
                = ((0 : ℝ) : EReal) := hValue
            _ = oneDimensionalPowerKernel u v := hKernelZero.symm
            _ = helperForText_34_1_1_correctedMixedLowerClosureFormula u v := by
                  simp [helperForText_34_1_1_correctedMixedLowerClosureFormula, hOrigin, hv, hu]
        · -- On the closed square away from the zero base, the mixed lower closure is just `u^v`.
          have hValue :
              partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v =
                oneDimensionalPowerKernel u v :=
            helperForText_34_1_1_mixedLowerClosure_eq_powerKernel_of_closedSquare_nonzeroFirst
              hu hv hu0
          simpa [helperForText_34_1_1_correctedMixedLowerClosureFormula, hOrigin, hv, hu] using
            hValue
      · -- If `v ∈ [0,1]` but `u ∉ [0,1]`, the mixed lower closure already drops to `⊥`.
        have hValue :
            partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ⊥ :=
          helperForText_34_1_1_mixedLowerClosure_eq_bot_of_not_inClosedUnitInterval hu hv
        simpa [helperForText_34_1_1_correctedMixedLowerClosureFormula, hOrigin, hv, hu] using
          hValue
    · -- Outside `[0,1]` in the second variable, the mixed lower closure is constantly `⊤`.
      have hValue :
          partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) u v = ⊤ :=
        helperForText_34_1_1_mixedLowerClosure_eq_top_of_not_inClosedUnitInterval hv
      simpa [helperForText_34_1_1_correctedMixedLowerClosureFormula, hOrigin, hv] using hValue

/-- Helper for Text 34.1.1: the corrected local lower-closure formula agrees with the imported
part-2 formula on the off-off branch. -/
lemma helperForText_34_1_1_correctedMixedLowerClosureFormula_offOff_branch_agrees
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    helperForText_34_1_1_correctedMixedLowerClosureFormula u v =
      openUnitSquarePowerLowerClosureFormula u v := by
  rw [helperForText_34_1_1_correctedMixedLowerClosureFormula_eq_top_of_not_inClosedUnitInterval hv]
  rw [helperForText_34_1_1_importedLowerFormula_eq_top_of_not_inClosedUnitInterval_second hv]

/-- Helper for Text 34.1.1: the corrected local formula and the imported part-2 formula now
agree at the explicit off-off witness `(2, 2)`. -/
lemma helperForText_34_1_1_correctedImportedAgreement_counterexample_values :
    helperForText_34_1_1_correctedMixedLowerClosureFormula
        (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) = ⊤ ∧
      openUnitSquarePowerLowerClosureFormula
        (fun _ : Fin 1 => (2 : ℝ)) (fun _ : Fin 1 => (2 : ℝ)) = ⊤ := by
  constructor
  · refine
      helperForText_34_1_1_correctedMixedLowerClosureFormula_eq_top_of_not_inClosedUnitInterval ?_
    simp [InClosedUnitInterval]
  · refine
      helperForText_34_1_1_importedLowerFormula_eq_top_of_not_inClosedUnitInterval_second ?_
    simp [InClosedUnitInterval]

/-- Helper for Text 34.1.1: the corrected local lower-closure formula now agrees definitionally
with the imported part-2 formula. -/
lemma helperForText_34_1_1_correctedMixedLowerClosureFormula_eq_importedLowerClosureFormula :
    helperForText_34_1_1_correctedMixedLowerClosureFormula =
      openUnitSquarePowerLowerClosureFormula := by
  funext u
  funext v
  simp [helperForText_34_1_1_correctedMixedLowerClosureFormula,
    openUnitSquarePowerLowerClosureFormula]

/-- Helper for Text 34.1.1: once the imported lower formula is repaired to match the corrected
local branch computation, the displayed mixed lower-closure formula follows immediately. -/
lemma helperForText_34_1_1_mixedLowerClosure_formula_of_correctedImportedAgreement
    (hAgreement :
      helperForText_34_1_1_correctedMixedLowerClosureFormula =
        openUnitSquarePowerLowerClosureFormula) :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) =
      openUnitSquarePowerLowerClosureFormula := by
  -- First rewrite the actual mixed lower closure to the corrected local formula proved above.
  calc
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle)
        = helperForText_34_1_1_correctedMixedLowerClosureFormula :=
      helperForText_34_1_1_mixedLowerClosure_eq_correctedFormula
    -- The remaining step is exactly the upstream agreement that part 2 still lacks.
    _ = openUnitSquarePowerLowerClosureFormula := hAgreement

/-- Helper for Text 34.1.1: the displayed mixed lower-closure formula is equivalent to the
upstream agreement between the corrected local formula and the imported part-2 definition. -/
lemma helperForText_34_1_1_mixedLowerClosure_formula_iff_correctedImportedAgreement :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) =
        openUnitSquarePowerLowerClosureFormula ↔
      helperForText_34_1_1_correctedMixedLowerClosureFormula =
        openUnitSquarePowerLowerClosureFormula := by
  constructor
  · intro hLower
    -- Rewrite the actual mixed lower closure to the corrected local formula first.
    calc
      helperForText_34_1_1_correctedMixedLowerClosureFormula
          = partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) := by
            symm
            exact helperForText_34_1_1_mixedLowerClosure_eq_correctedFormula
      _ = openUnitSquarePowerLowerClosureFormula := hLower
  · intro hAgreement
    -- Conversely, the corrected imported agreement already implies the displayed lower formula.
    exact
      helperForText_34_1_1_mixedLowerClosure_formula_of_correctedImportedAgreement hAgreement

/-- Helper for Text 34.1.1: the mixed lower closure `cl₂(cl₁ K)` is the displayed lower
closure formula with value `0` at the origin and `-∞` on the left off-domain branch. -/
lemma helperForText_34_1_1_mixedLowerClosure_formula :
    partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) =
      openUnitSquarePowerLowerClosureFormula := by
  exact
    helperForText_34_1_1_mixedLowerClosure_formula_of_correctedImportedAgreement
      helperForText_34_1_1_correctedMixedLowerClosureFormula_eq_importedLowerClosureFormula

/-- Helper for Text 34.1.1: if `v` already lies outside `[0, 1]`, then the mixed upper closure
`cl₁(cl₂ K)` stays constantly `⊤`. -/
lemma helperForText_34_1_1_mixedUpperClosure_eq_top_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hv : ¬ InClosedUnitInterval v) :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v = ⊤ := by
  -- The inner second closure is already constantly `⊤`, so every first-variable local supremum
  -- is `⊤` as well.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm le_top
  refine le_iInf ?_
  intro ε
  have hCenter : ‖u - u‖ < ε.1 := by
    simpa using ε.2
  let wu : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} := ⟨u, hCenter⟩
  have hValue : partialClosure₂ openUnitSquarePowerSaddle wu.1 v = ⊤ :=
    helperForText_34_1_1_partialClosure2_eq_top_of_not_inClosedUnitInterval hv
  calc
    (⊤ : EReal) = partialClosure₂ openUnitSquarePowerSaddle wu.1 v := by simp [hValue]
    _ ≤
      ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
        partialClosure₂ openUnitSquarePowerSaddle w.1 v :=
        le_iSup
          (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} =>
            partialClosure₂ openUnitSquarePowerSaddle w.1 v)
          wu

/-- Helper for Text 34.1.1: if `u` lies outside `[0, 1]` while `v` stays in `[0, 1]`, then
the mixed upper closure `cl₁(cl₂ K)` is already `⊥`. -/
lemma helperForText_34_1_1_mixedUpperClosure_eq_bot_of_not_inClosedUnitInterval
    {u v : Fin 1 → ℝ} (hu : ¬ InClosedUnitInterval u) (hv : InClosedUnitInterval v) :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v = ⊥ := by
  rcases helperForText_34_1_1_exists_radius_outside_closedUnitInterval u hu with ⟨ε, hε⟩
  -- On a small first-variable neighborhood, every point is still outside `(0,1)`, so the
  -- already-computed second closure stays equal to `⊥`.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · have hLocal :
        (⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
            partialClosure₂ openUnitSquarePowerSaddle w.1 v) = ⊥ := by
      apply le_antisymm
      · refine iSup_le ?_
        intro w
        have hwNoOpen : ¬ InOpenUnitInterval w.1 := hε w
        have hValue : partialClosure₂ openUnitSquarePowerSaddle w.1 v = ⊥ :=
          helperForText_34_1_1_partialClosure2_eq_bot_of_not_inOpenUnitInterval hwNoOpen hv
        rw [hValue]
      · exact bot_le
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε'.1},
            partialClosure₂ openUnitSquarePowerSaddle w.1 v)
          ≤
        ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
          partialClosure₂ openUnitSquarePowerSaddle w.1 v := iInf_le _ ε
      _ = ⊥ := hLocal
  · exact bot_le

/-- Helper for Text 34.1.1: on the closed square, the mixed upper closure `cl₁(cl₂ K)`
already recovers the original power kernel `u^v`. -/
lemma helperForText_34_1_1_mixedUpperClosure_eq_powerKernel_of_closedSquare
    {u v : Fin 1 → ℝ} (hu : InClosedUnitInterval u) (hv : InClosedUnitInterval v) :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v =
      oneDimensionalPowerKernel u v := by
  have hCont : ContinuousAt (fun x : ℝ => x ^ (v 0)) (u 0) :=
    Real.continuousAt_rpow_const (u 0) (v 0) (Or.inr hv.1)
  have hNonnegClosure :
      ((0 : ℝ) : EReal) ≤ partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v := by
    -- Every first-variable neighborhood meets `(0,1)`, and at such points the inner closure is
    -- already the nonnegative real value `u^v`.
    unfold partialClosure₁ concaveClosureInFirst
    refine le_iInf ?_
    intro ε
    rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval u hu ε with
      ⟨w, hwOpen⟩
    have hValue : ((0 : ℝ) : EReal) ≤ partialClosure₂ openUnitSquarePowerSaddle w.1 v := by
      have hEq :
          partialClosure₂ openUnitSquarePowerSaddle w.1 v = oneDimensionalPowerKernel w.1 v :=
        helperForText_34_1_1_partialClosure2_eq_powerKernel_of_openFirst_closedSecond hwOpen hv
      have hrpow : 0 ≤ (w.1 0) ^ (v 0) := Real.rpow_nonneg hwOpen.1.le _
      rw [hEq]
      simpa [oneDimensionalPowerKernel] using hrpow
    exact le_trans hValue
      (le_iSup
        (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} =>
          partialClosure₂ openUnitSquarePowerSaddle w.1 v)
        w)
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm
  · -- Continuity of `x ↦ x^v` on `[0,1]` controls every local first-variable supremum from
    -- above once the inner second closure is rewritten on open witnesses.
    refine (EReal.le_of_forall_lt_iff_le (x := oneDimensionalPowerKernel u v)
      (y := ⨅ ε : {ε : ℝ // 0 < ε},
        ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
          partialClosure₂ openUnitSquarePowerSaddle w.1 v)).1 ?_
    intro z hz
    have hzReal : (u 0) ^ (v 0) < z := by
      simpa [oneDimensionalPowerKernel] using hz
    have hGap : 0 < z - (u 0) ^ (v 0) := by
      linarith
    rcases (Metric.continuousAt_iff.mp hCont) (z - (u 0) ^ (v 0)) hGap with ⟨δ, hδPos, hδ⟩
    let ε : {ε : ℝ // 0 < ε} := ⟨δ, hδPos⟩
    calc
      (⨅ ε' : {ε' : ℝ // 0 < ε'},
          ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε'.1},
            partialClosure₂ openUnitSquarePowerSaddle w.1 v)
          ≤ ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
              partialClosure₂ openUnitSquarePowerSaddle w.1 v :=
            iInf_le _ ε
      _ ≤ ((z : ℝ) : EReal) := by
        refine iSup_le ?_
        intro w
        by_cases hwOpen : InOpenUnitInterval w.1
        · have hwNorm : ‖w.1 - u‖ < δ := w.2
          rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
          have hwCoord : dist (w.1 0) (u 0) < δ := by
            simpa [Real.dist_eq] using hwNorm
          have hPowDist : dist ((w.1 0) ^ (v 0)) ((u 0) ^ (v 0)) < z - (u 0) ^ (v 0) :=
            hδ hwCoord
          have hAbs : |(w.1 0) ^ (v 0) - (u 0) ^ (v 0)| < z - (u 0) ^ (v 0) := by
            simpa [Real.dist_eq] using hPowDist
          have hPowLt : (w.1 0) ^ (v 0) < z := by
            have hUpper : (w.1 0) ^ (v 0) - (u 0) ^ (v 0) < z - (u 0) ^ (v 0) :=
              (abs_lt.mp hAbs).2
            linarith
          have hValue :
              partialClosure₂ openUnitSquarePowerSaddle w.1 v = oneDimensionalPowerKernel w.1 v :=
            helperForText_34_1_1_partialClosure2_eq_powerKernel_of_openFirst_closedSecond hwOpen hv
          rw [hValue]
          simpa [oneDimensionalPowerKernel] using hPowLt.le
        · have hValue : partialClosure₂ openUnitSquarePowerSaddle w.1 v = ⊥ :=
            helperForText_34_1_1_partialClosure2_eq_bot_of_not_inOpenUnitInterval hwOpen hv
          rw [hValue]
          exact bot_le
  · -- Conversely, every lower barrier below `u^v` survives on a smaller neighborhood, and that
    -- neighborhood still contains an open-interval witness where the inner closure equals `u^v`.
    refine (forall_lt_iff_le).1 ?_
    intro z hz
    cases z using EReal.rec with
    | bot =>
        have hNonnegClosure' :
            ((0 : ℝ) : EReal) ≤
              ⨅ ε : {ε : ℝ // 0 < ε},
                ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
                  partialClosure₂ openUnitSquarePowerSaddle w.1 v := by
          simpa [partialClosure₁, concaveClosureInFirst] using hNonnegClosure
        exact lt_of_lt_of_le (by norm_num) hNonnegClosure'
    | coe zr =>
        have hzReal : zr < (u 0) ^ (v 0) := by
          simpa [oneDimensionalPowerKernel] using hz
        by_cases hzNonneg : 0 ≤ zr
        · let β : ℝ := (zr + (u 0) ^ (v 0)) / 2
          have hzBeta : zr < β := by
            dsimp [β]
            linarith
          have hGap : 0 < (u 0) ^ (v 0) - β := by
            dsimp [β]
            linarith
          rcases (Metric.continuousAt_iff.mp hCont) ((u 0) ^ (v 0) - β) hGap with
            ⟨δ, hδPos, hδ⟩
          have hClosureLower :
              (β : EReal) ≤
                ⨅ ε : {ε : ℝ // 0 < ε},
                  ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
                    partialClosure₂ openUnitSquarePowerSaddle w.1 v := by
            refine le_iInf ?_
            intro ε
            let η : {r : ℝ // 0 < r} := by
              refine ⟨min δ (ε.1 / 2), ?_⟩
              apply lt_min
              · exact hδPos
              · linarith [ε.2]
            rcases helperForText_34_1_1_ball_hits_openUnitInterval_of_closedUnitInterval u hu η with
              ⟨w, hwOpen⟩
            have hwInEps : ‖w.1 - u‖ < ε.1 := by
              have hwHalf : ‖w.1 - u‖ < ε.1 / 2 := lt_of_lt_of_le w.2 (min_le_right _ _)
              linarith [ε.2]
            have hwNorm : ‖w.1 - u‖ < δ := lt_of_lt_of_le w.2 (min_le_left _ _)
            rw [helperForText_34_1_1_norm_fin1_eq_abs] at hwNorm
            have hwCoord : dist (w.1 0) (u 0) < δ := by
              simpa [Real.dist_eq] using hwNorm
            have hPowDist : dist ((w.1 0) ^ (v 0)) ((u 0) ^ (v 0)) < (u 0) ^ (v 0) - β :=
              hδ hwCoord
            have hAbs : |(w.1 0) ^ (v 0) - (u 0) ^ (v 0)| < (u 0) ^ (v 0) - β := by
              simpa [Real.dist_eq] using hPowDist
            have hPowGt : β < (w.1 0) ^ (v 0) := by
              have hLower :
                  -((u 0) ^ (v 0) - β) < (w.1 0) ^ (v 0) - (u 0) ^ (v 0) :=
                (abs_lt.mp hAbs).1
              linarith
            have hValue :
                partialClosure₂ openUnitSquarePowerSaddle w.1 v =
                  oneDimensionalPowerKernel w.1 v :=
              helperForText_34_1_1_partialClosure2_eq_powerKernel_of_openFirst_closedSecond hwOpen hv
            calc
              (β : EReal) ≤ partialClosure₂ openUnitSquarePowerSaddle w.1 v := by
                rw [hValue]
                exact le_of_lt <| by
                  simpa [oneDimensionalPowerKernel] using hPowGt
              _ ≤
                ⨆ w' : {w' : Fin 1 → ℝ // ‖w' - u‖ < ε.1},
                  partialClosure₂ openUnitSquarePowerSaddle w'.1 v :=
                  le_iSup
                    (fun w' : {w' : Fin 1 → ℝ // ‖w' - u‖ < ε.1} =>
                      partialClosure₂ openUnitSquarePowerSaddle w'.1 v)
                    ⟨w.1, hwInEps⟩
          exact lt_of_lt_of_le (by exact_mod_cast hzBeta) hClosureLower
        · have hNeg : (zr : EReal) < ((0 : ℝ) : EReal) := by
            exact_mod_cast lt_of_not_ge hzNonneg
          have hNonnegClosure' :
              ((0 : ℝ) : EReal) ≤
                ⨅ ε : {ε : ℝ // 0 < ε},
                  ⨆ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
                    partialClosure₂ openUnitSquarePowerSaddle w.1 v := by
            simpa [partialClosure₁, concaveClosureInFirst] using hNonnegClosure
          exact lt_of_lt_of_le hNeg hNonnegClosure'
    | top =>
        exfalso
        exact not_lt_of_ge le_top hz

/-- Helper for Text 34.1.1: the mixed upper closure `cl₁(cl₂ K)` is the displayed upper
closure formula with value `1` at the origin. -/
lemma helperForText_34_1_1_mixedUpperClosure_formula :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) =
      openUnitSquarePowerUpperClosureFormula := by
  funext u
  funext v
  by_cases hv : InClosedUnitInterval v
  · by_cases hu : InClosedUnitInterval u
    · -- On the closed square, the mixed upper closure is already the original power kernel; the
      -- displayed special origin branch just makes the value `1 = 0^0` explicit.
      have hValue :
          partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v =
            oneDimensionalPowerKernel u v :=
        helperForText_34_1_1_mixedUpperClosure_eq_powerKernel_of_closedSquare hu hv
      by_cases hOrigin : u 0 = 0 ∧ v 0 = 0
      · have hOriginValue : oneDimensionalPowerKernel u v = ((1 : ℝ) : EReal) := by
          rcases hOrigin with ⟨hu0, hv0⟩
          simp [oneDimensionalPowerKernel, hu0, hv0]
        calc
          partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v
              = oneDimensionalPowerKernel u v := hValue
          _ = ((1 : ℝ) : EReal) := hOriginValue
          _ = openUnitSquarePowerUpperClosureFormula u v := by
                simp [openUnitSquarePowerUpperClosureFormula, hOrigin]
      · simpa [openUnitSquarePowerUpperClosureFormula, hOrigin, hv, hu] using hValue
    · -- Outside `[0,1]` in the first variable, the mixed upper closure is already `⊥`.
      have hValue : partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v = ⊥ :=
        helperForText_34_1_1_mixedUpperClosure_eq_bot_of_not_inClosedUnitInterval hu hv
      have hNotOrigin : ¬ (u 0 = 0 ∧ v 0 = 0) := by
        intro hOrigin
        apply hu
        constructor <;> linarith [hOrigin.1]
      simp [openUnitSquarePowerUpperClosureFormula, hNotOrigin, hv, hu, hValue]
  · -- Outside `[0,1]` in the second variable, the mixed upper closure is constantly `⊤`.
    have hValue : partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) u v = ⊤ :=
      helperForText_34_1_1_mixedUpperClosure_eq_top_of_not_inClosedUnitInterval hv
    have hNotOrigin : ¬ (u 0 = 0 ∧ v 0 = 0) := by
      intro hOrigin
      apply hv
      constructor <;> linarith [hOrigin.2]
    simp [openUnitSquarePowerUpperClosureFormula, hNotOrigin, hv, hValue]

/-- Helper for Text 34.1.1: specializing the mixed upper-closure formula at the origin gives
the value `1`. -/
lemma helperForText_34_1_1_mixedUpperClosure_origin_eq_one :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) 0 0 = ((1 : ℝ) : EReal) := by
  -- Evaluate the already-proved mixed upper-closure formula at the origin.
  have hPointwise :
      partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) 0 0 =
        openUnitSquarePowerUpperClosureFormula 0 0 :=
    congrArg (fun F => F 0 0) helperForText_34_1_1_mixedUpperClosure_formula
  -- The explicit piecewise formula selects the distinguished origin branch there.
  simpa [openUnitSquarePowerUpperClosureFormula] using hPointwise

/-- Helper for Text 34.1.1: the two iterated mixed closures really differ at the origin, with
upper value `1` and lower value `0`. -/
lemma helperForText_34_1_1_mixedClosures_differ_at_origin :
    partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) 0 0 ≠
      partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) 0 0 := by
  -- Rewrite both mixed closures to their explicit origin values.
  rw [helperForText_34_1_1_mixedUpperClosure_origin_eq_one]
  rw [helperForText_34_1_1_mixedLowerClosure_origin_eq_zero]
  -- The resulting extended-real constants are visibly different.
  norm_num

/-- Helper for Text 34.1.1: on the open unit square, the upper simple extension reduces to the
finite power kernel `u^v`. -/
lemma helperForText_34_1_1_openSquare_value_of_open_membership
    {u v : Fin 1 → ℝ} (hu : InOpenUnitInterval u) (hv : InOpenUnitInterval v) :
    openUnitSquarePowerSaddle u v = oneDimensionalPowerKernel u v := by
  -- Inside `(0,1) × (0,1)`, both branch conditions are true, so only the finite kernel remains.
  simp [openUnitSquarePowerSaddle, hu, hv]

/-- Helper for Text 34.1.1: for every fixed `v ∈ (0,1)`, the section `u ↦ u^v` is concave on
the open unit interval. -/
lemma helperForText_34_1_1_powerKernel_concave_in_first_on_openUnitInterval
    {v : Fin 1 → ℝ} (hv : InOpenUnitInterval v) :
    IsERealConcaveOn {u : Fin 1 → ℝ | InOpenUnitInterval u}
      (fun u => oneDimensionalPowerKernel u v) := by
  intro x y hx hy a b ha hb hab hxy
  -- Pass to the unique coordinate, where `t ↦ t^(v 0)` is concave on `[0, ∞)` because
  -- `v 0 ∈ [0,1]`.
  have hv0 : 0 ≤ v 0 := le_of_lt hv.1
  have hv1 : v 0 ≤ 1 := le_of_lt hv.2
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ (v 0)) :=
    Real.concaveOn_rpow hv0 hv1
  have hxIci : x 0 ∈ Set.Ici (0 : ℝ) := hx.1.le
  have hyIci : y 0 ∈ Set.Ici (0 : ℝ) := hy.1.le
  have hineqReal :
      a * (x 0) ^ (v 0) + b * (y 0) ^ (v 0) ≤ (a * x 0 + b * y 0) ^ (v 0) := by
    simpa [smul_eq_mul] using hconc.2 hxIci hyIci ha hb hab
  -- Lift the scalar Jensen inequality from `ℝ` to `EReal`.
  have hineqE :
      (((a * (x 0) ^ (v 0) + b * (y 0) ^ (v 0) : ℝ)) : EReal) ≤
        (((a * x 0 + b * y 0) ^ (v 0) : ℝ) : EReal) :=
    (EReal.coe_le_coe_iff).2 hineqReal
  simpa [oneDimensionalPowerKernel, smul_eq_mul, Pi.smul_apply, EReal.coe_add, EReal.coe_mul,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hineqE

/-- Helper for Text 34.1.1: with `u ∈ (0,1)` fixed, the power kernel rewrites as an exponential
of an affine function in the second variable. -/
lemma helperForText_34_1_1_powerKernel_eq_exp_log_on_openFirst
    {u v : Fin 1 → ℝ} (hu : InOpenUnitInterval u) :
    oneDimensionalPowerKernel u v =
      ((Real.exp ((Real.log (u 0)) * (v 0)) : ℝ) : EReal) := by
  -- Positive bases admit the standard identity `u^v = exp(log u * v)`.
  simp [oneDimensionalPowerKernel, Real.rpow_def_of_pos hu.1]

/-- Helper for Text 34.1.1: for every fixed `u ∈ (0,1)`, the section `v ↦ u^v` is convex on
the open unit interval. -/
lemma helperForText_34_1_1_powerKernel_convex_in_second_on_openUnitInterval
    {u : Fin 1 → ℝ} (hu : InOpenUnitInterval u) :
    IsERealConvexOn {v : Fin 1 → ℝ | InOpenUnitInterval v}
      (fun v => oneDimensionalPowerKernel u v) := by
  intro x y hx hy a b ha hb hab hxy
  -- For fixed positive base `u 0`, the scalar function `t ↦ (u 0)^t` is convex on `ℝ`.
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => (u 0) ^ t) :=
    convexOn_rpow_left hu.1
  have hineqReal :
      (u 0) ^ (a * x 0 + b * y 0) ≤
        a * (u 0) ^ (x 0) + b * (u 0) ^ (y 0) := by
    simpa [smul_eq_mul] using
      hconv.2 (by simp) (by simp) ha hb hab
  -- Lift the scalar convexity inequality from `ℝ` to `EReal`.
  have hineqE :
      ((((u 0) ^ (a * x 0 + b * y 0) : ℝ)) : EReal) ≤
        (((a * (u 0) ^ (x 0) + b * (u 0) ^ (y 0) : ℝ)) : EReal) :=
    (EReal.coe_le_coe_iff).2 hineqReal
  simpa [oneDimensionalPowerKernel, smul_eq_mul, Pi.smul_apply, EReal.coe_add, EReal.coe_mul,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hineqE

/-- Helper for Text 34.1.1: on the open unit square, the saddle kernel `K(u,v)=u^v` is
concave in the first variable and convex in the second. -/
lemma helperForText_34_1_1_openUnitSquarePowerSaddle_isConcaveConvexOn :
    IsConcaveConvexOn
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        openUnitSquarePowerSaddle := by
  constructor
  · intro v hv x y hx hy a b ha hb hab hxy
    -- On the open square, the saddle kernel agrees with the finite power kernel `u^v`.
    -- Jensen for `t ↦ t^(v 0)` then yields concavity in the first variable.
    simpa [helperForText_34_1_1_openSquare_value_of_open_membership hxy hv,
      helperForText_34_1_1_openSquare_value_of_open_membership hx hv,
      helperForText_34_1_1_openSquare_value_of_open_membership hy hv] using
      (helperForText_34_1_1_powerKernel_concave_in_first_on_openUnitInterval hv
        hx hy ha hb hab hxy)
  · intro u hu x y hx hy a b ha hb hab hxy
    -- With the first coordinate fixed in `(0,1)`, the same open-square rewrite reduces the
    -- second-variable section to the convex scalar map `v ↦ u^v`.
    simpa [helperForText_34_1_1_openSquare_value_of_open_membership hu hxy,
      helperForText_34_1_1_openSquare_value_of_open_membership hu hx,
      helperForText_34_1_1_openSquare_value_of_open_membership hu hy] using
      (helperForText_34_1_1_powerKernel_convex_in_second_on_openUnitInterval hu
        hx hy ha hb hab hxy)

-- Proof sketch: identify the open-square branch with the finite kernel `u^v`, prove sectionwise
-- concavity in `u` and convexity in `v`, and then combine those with the explicit mixed-closure
-- formulas for both iterated orders.
-- Route correction: the earlier global route was impossible because the upper simple extension is
-- not concave-convex on all of `Set.univ × Set.univ`; the theorem only asks for the on-domain
-- saddle property on `(0,1) × (0,1)`.
/-- Text 34.1.1: for the saddle-function `K(u, v) = u^v` on the open unit square, `K` is
concave-convex on `(0,1) × (0,1)`; the two iterated mixed closures are given by the displayed
piecewise formulas; and they differ at the origin. -/
theorem section34_example_u_pow_v :
    IsConcaveConvexOn
        {u : Fin 1 → ℝ | InOpenUnitInterval u}
        {v : Fin 1 → ℝ | InOpenUnitInterval v}
        openUnitSquarePowerSaddle ∧
      partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) =
        openUnitSquarePowerUpperClosureFormula ∧
      partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) =
        openUnitSquarePowerLowerClosureFormula ∧
      partialClosure₁ (partialClosure₂ openUnitSquarePowerSaddle) 0 0 ≠
        partialClosure₂ (partialClosure₁ openUnitSquarePowerSaddle) 0 0 := by
  refine ⟨?_, helperForText_34_1_1_mixedUpperClosure_formula,
    helperForText_34_1_1_mixedLowerClosure_formula, ?_⟩
  · -- The dedicated helper packages the open-square saddle-property proof.
    exact helperForText_34_1_1_openUnitSquarePowerSaddle_isConcaveConvexOn
  · exact helperForText_34_1_1_mixedClosures_differ_at_origin

end SaddleAmbient

end Section34
end Chap07
