/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap CircleDegree unitInterval
open FundamentalGroup

/-- Helper for Problem 1.8.2: a lift of `f ∘ Real.fourierChar` records the degree of `f` through
the displacement of its endpoint over one turn. -/
lemma circleDegree_eq_fourierChar_lift_displacement
    (f : C(Circle, Circle)) {c : ℝ} (hc : Real.fourierChar c = f 1)
    (F : C(ℝ, ℝ)) (hF0 : F 0 = c)
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩) :
    F 1 - c = (deg(f) : ℝ) := by
  let a : Path (f 1) 1 :=
    (((Path.segment (0 : ℝ) c).map Real.continuous_fourierChar).cast
      (by simp) hc.symm).symm
  let mappedLoop : Path (f 1) (f 1) := (standardLoop 1).map f.continuous
  let loop : Path (1 : Circle) 1 := (a.symm.trans mappedLoop).trans a
  have hF1 : Real.fourierChar (F 1) = f 1 := by
    have hraw : Real.fourierChar (F 1) = f (Real.fourierChar (1 : ℝ)) := congrFun hF (1 : ℝ)
    have hchar1 : Real.fourierChar (1 : ℝ) = (1 : Circle) := by
      rw [Real.fourierChar_apply']
      simpa [mul_comm, mul_left_comm, mul_assoc] using Circle.exp_two_pi
    simpa [hchar1] using hraw
  have hclass :
      circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦loop⟧) = deg(f) := by
    -- Rewrite the degree-specification loop using the chosen basepoint-change path `a`.
    have hdeg := congrArg circleFundamentalGroupLiftIndex (circleDegree_spec f a)
    rw [show γ[a] (FundamentalGroup.map f (1 : Circle) (standardLoopClass 1)) =
        FundamentalGroup.fromPath ⟦loop⟧ by
          rw [show FundamentalGroup.map f (1 : Circle) (standardLoopClass 1) =
              FundamentalGroup.fromPath ⟦mappedLoop⟧ by
                rfl]
          rw [fundamentalGroupMulEquivOfPath_apply_fromPath]] at hdeg
    rw [circleFundamentalGroupLiftIndex_standardLoop] at hdeg
    exact hdeg
  have hfirstLift :
      real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero a.symm) =
        (Path.segment (0 : ℝ) c).toContinuousMap := by
    -- The chosen return path is literally the Fourier character of the segment from `0` to `c`.
    change real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero a.symm) =
          (Path.segment (0 : ℝ) c).toContinuousMap
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (circle_path_start_eq_fourierChar_zero a.symm)).2 ?_).symm
    refine ⟨?_, by simp⟩
    ext s
    simp [a]
  have hmidLift :
      real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap c
        (by simpa [mappedLoop] using hc.symm) =
        F.comp ⟨fun s : I ↦ (s : ℝ), continuous_subtype_val⟩ := by
    -- Restrict the global lift `F` to the unit interval to lift the mapped standard loop.
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff'
      (by simpa [mappedLoop] using hc.symm)).2 ?_).symm
    refine ⟨?_, by simp [hF0]⟩
    ext s
    simpa [Function.comp_apply, mappedLoop, standardLoop_eq_fourierChar_mul] using
      congrFun hF (s : ℝ)
  have hlastStart : a.toContinuousMap 0 = Real.fourierChar (F 1) := by
    -- At the end of the middle segment, the lift lands over the basepoint `f 1`.
    simpa [a] using hF1.symm
  have hlastLift :
      real_fourierChar_isCoveringMap.liftPath a.toContinuousMap (F 1) hlastStart =
        (Path.segment (F 1) (F 1 - c)).toContinuousMap := by
    -- The final return path subtracts the original lift value `c`.
    refine ((real_fourierChar_isCoveringMap.eq_liftPath_iff' hlastStart).2 ?_).symm
    refine ⟨?_, by simp⟩
    ext s
    exact congrArg Subtype.val <| by
      have hperiod : Real.fourierChar (F 1 - c) = (1 : Circle) := by
        have hmul : (2 * Real.pi) * (F 1 - c) = (2 * Real.pi) * F 1 - (2 * Real.pi) * c := by
          ring
        rw [Real.fourierChar_apply', hmul, Circle.exp_sub]
        simpa [Real.fourierChar_apply'] using (div_eq_one.2 (hF1.trans hc.symm))
      have hsegment :
          Real.fourierChar ((Path.segment (0 : ℝ) c) (σ s)) =
            Real.fourierChar ((1 - (s : ℝ)) * c) := by
        change Real.fourierChar ((Path.segment (0 : ℝ) c) (σ s)) = _
        rw [Path.segment_apply]
        simp [AffineMap.lineMap_apply_module]
      calc
        Real.fourierChar ((Path.segment (F 1) (F 1 - c)) s) =
            Real.fourierChar (((1 - (s : ℝ)) * c) + (F 1 - c)) := by
              rw [Path.segment_apply]
              have hline :
                  (AffineMap.lineMap (F 1) (F 1 - c)) (s : ℝ) = -(s : ℝ) * c + F 1 := by
                rw [AffineMap.lineMap_apply_module, smul_eq_mul, smul_eq_mul]
                ring
              rw [hline]
              congr 1
              ring
        _ = Real.fourierChar ((1 - (s : ℝ)) * c) * Real.fourierChar (F 1 - c) := by
              simpa using Real.fourierChar.map_add_eq_mul' ((1 - (s : ℝ)) * c) (F 1 - c)
        _ = Real.fourierChar ((1 - (s : ℝ)) * c) := by
                simp [hperiod]
        _ = a s := by
                simpa [a] using hsegment.symm
  have hprefix :
      real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1 = F 1 := by
    -- Concatenate the first segment lift with the restricted lift of the mapped loop.
    have hfirstEnd :
        (real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero a.symm)) 1 = c := by
      simpa using DFunLike.congr_fun hfirstLift 1
    have hmidEnd :
        (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap c
          (by simpa [mappedLoop] using hc.symm)) 1 = F 1 := by
      simpa using DFunLike.congr_fun hmidLift 1
    have hmidEnd' :
        (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap
          ((real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero a.symm)) 1)
          (by
            simpa [mappedLoop] using
              (congr_fun
                (real_fourierChar_isCoveringMap.liftPath_lifts a.symm.toContinuousMap 0
                  (circle_path_start_eq_fourierChar_zero a.symm)) 1).symm)) 1 = F 1 := by
      simpa [hfirstEnd] using hmidEnd
    have htrans := DFunLike.congr_fun
      (real_fourierChar_isCoveringMap.liftPath_trans
        (by rw [fourierChar_zero_eq_one]) a.symm mappedLoop) 1
    have htrans' :
        (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1 =
          (real_fourierChar_isCoveringMap.liftPath mappedLoop.toContinuousMap
            ((real_fourierChar_isCoveringMap.liftPath a.symm.toContinuousMap 0
              (circle_path_start_eq_fourierChar_zero a.symm)) 1)
            (by
              simpa [mappedLoop] using
                (congr_fun
                  (real_fourierChar_isCoveringMap.liftPath_lifts a.symm.toContinuousMap 0
                    (circle_path_start_eq_fourierChar_zero a.symm)) 1).symm)) 1 := by
      simpa using htrans
    exact htrans'.trans hmidEnd'
  have hlastLift' :
      real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
        (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1)
        (by simpa [hprefix] using hlastStart) =
          (Path.segment (F 1) (F 1 - c)).toContinuousMap := by
    simpa [hprefix] using hlastLift
  have hloopLift :
      real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero loop) 1 = F 1 - c := by
    -- A second application of lift concatenation computes the endpoint of the transported loop.
    have hlastEnd :
        (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
          (real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop)) 1)
          (by simpa [hprefix] using hlastStart)) 1 = F 1 - c := by
      simpa using DFunLike.congr_fun hlastLift' 1
    have hlastEnd' :
        (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
          ((real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1)
          (by
            simpa using
              (congr_fun
                (real_fourierChar_isCoveringMap.liftPath_lifts
                  (a.symm.trans mappedLoop).toContinuousMap 0
                  (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1).symm)) 1 =
          F 1 - c := by
      simpa using hlastEnd
    have htrans := DFunLike.congr_fun
      (real_fourierChar_isCoveringMap.liftPath_trans
        (by rw [fourierChar_zero_eq_one])
        (a.symm.trans mappedLoop) a) 1
    have htrans' :
        (real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero loop)) 1 =
          (real_fourierChar_isCoveringMap.liftPath a.toContinuousMap
            ((real_fourierChar_isCoveringMap.liftPath (a.symm.trans mappedLoop).toContinuousMap 0
              (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1)
            (by
              simpa using
                (congr_fun
                  (real_fourierChar_isCoveringMap.liftPath_lifts
                    (a.symm.trans mappedLoop).toContinuousMap 0
                    (circle_path_start_eq_fourierChar_zero (a.symm.trans mappedLoop))) 1).symm)) 1 := by
      simpa [loop] using htrans
    exact htrans'.trans hlastEnd'
  have hloopIndex :
      ((deg(f) : ℤ) : ℝ) =
        real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero loop) 1 := by
    -- The loop class from `circleDegree_spec` has lift index exactly `deg(f)`.
    calc
      ((deg(f) : ℤ) : ℝ) =
          ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦loop⟧) : ℤ) : ℝ) := by
            exact congrArg (fun n : ℤ ↦ (n : ℝ)) hclass.symm
      _ = real_fourierChar_isCoveringMap.liftPath loop.toContinuousMap 0
            (circle_path_start_eq_fourierChar_zero loop) 1 := by
              simpa using circleFundamentalGroupLiftIndex_spec loop
  exact hloopLift.symm.trans hloopIndex.symm

/-- Helper for Problem 1.8.2: subtracting the parameter from a lift of `f ∘ Real.fourierChar`
produces the quotient map `z ↦ f z / z`. -/
lemma fourierChar_lift_difference_eq_quotient
    (f : C(Circle, Circle)) (F : C(ℝ, ℝ))
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩)
    (t : ℝ) :
    Real.fourierChar (F t - t) = f (Real.fourierChar t) / Real.fourierChar t := by
  -- Rewrite the Fourier character of the difference as a quotient in the circle group.
  calc
    Real.fourierChar (F t - t) = Real.fourierChar (F t) / Real.fourierChar t := by
      have hmul : (2 * Real.pi) * (F t - t) = (2 * Real.pi) * F t - (2 * Real.pi) * t := by
        ring
      rw [Real.fourierChar_apply', hmul, Circle.exp_sub, Real.fourierChar_apply',
        Real.fourierChar_apply']
    _ = f (Real.fourierChar t) / Real.fourierChar t := by
      simpa [Function.comp_apply] using congrFun hF t

/-- Helper for Problem 1.8.2: if `f` has no fixed points, then the lift difference `F t - t`
never hits an integer. -/
lemma fourierChar_lift_difference_ne_int_of_no_fixed_points
    (f : C(Circle, Circle)) (hno : ∀ z : Circle, f z ≠ z)
    (F : C(ℝ, ℝ))
    (hF : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩)
    (t : ℝ) (n : ℤ) :
    F t - t ≠ n := by
  -- An integer value would make the quotient map equal `1`, forcing a fixed point.
  intro hnt
  have hquot :
      f (Real.fourierChar t) / Real.fourierChar t = (1 : Circle) := by
    rw [← fourierChar_lift_difference_eq_quotient f F hF t, hnt]
    exact fourierChar_int_eq_one n
  have hfix : f (Real.fourierChar t) = Real.fourierChar t := div_eq_one.1 hquot
  exact hno (Real.fourierChar t) hfix

/-- Helper for Problem 1.8.2: a continuous real function that avoids all integers cannot change by
a nonzero integer over the interval `[0, 1]`. -/
lemma integer_avoiding_continuous_step_eq_zero
    {d : ℝ → ℝ} (hd : Continuous d)
    (havoid : ∀ t : ℝ, ∀ n : ℤ, d t ≠ n) {k : ℤ}
    (hk : d 1 - d 0 = (k : ℝ)) :
    k = 0 := by
  -- Any nonzero integer jump would force the image of `[0, 1]` to cross an integer by IVT.
  by_contra hk0
  rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
  · let n : ℤ := Int.floor (d 0)
    have hd10 : d 1 ≤ d 0 := by
      have hk_real : (k : ℝ) < 0 := by exact_mod_cast hkneg
      linarith [hk, hk_real]
    have hn_mem : ((n : ℤ) : ℝ) ∈ Set.uIcc (d 0) (d 1) := by
      rw [Set.uIcc_of_ge hd10]
      refine ⟨?_, ?_⟩
      · have hk_int : k ≤ -1 := by omega
        have hk_le : (k : ℝ) ≤ -1 := by exact_mod_cast hk_int
        have hlt : d 0 - 1 < (n : ℝ) := by
          simpa [n] using (Int.sub_one_lt_floor (d 0))
        linarith [hk, hk_le, hlt]
      · simpa [n] using (Int.floor_le (d 0))
    obtain ⟨t, _, htd⟩ := (intermediate_value_uIcc hd.continuousOn) hn_mem
    exact (havoid t n) (by simpa [n] using htd)
  · let n : ℤ := Int.floor (d 0) + 1
    have hd01 : d 0 ≤ d 1 := by
      have hk_real : (0 : ℝ) < k := by exact_mod_cast hkpos
      linarith [hk, hk_real]
    have hn_mem : ((n : ℤ) : ℝ) ∈ Set.uIcc (d 0) (d 1) := by
      rw [Set.uIcc_of_le hd01]
      refine ⟨?_, ?_⟩
      · have hlt : d 0 < (n : ℝ) := by
          simpa [n] using (lt_floor_add_one (d 0))
        exact hlt.le
      · have hk_int : (1 : ℤ) ≤ k := by omega
        have hk_ge : (1 : ℝ) ≤ k := by exact_mod_cast hk_int
        have hfloor : ((Int.floor (d 0) : ℤ) : ℝ) ≤ d 0 := Int.floor_le (d 0)
        calc
          (n : ℝ) = ((Int.floor (d 0) : ℤ) : ℝ) + 1 := by simp [n]
          _ ≤ d 0 + 1 := by linarith
          _ ≤ d 0 + k := by linarith
          _ = d 1 := by linarith [hk]
    obtain ⟨t, _, htd⟩ := (intermediate_value_uIcc hd.continuousOn) hn_mem
    exact (havoid t n) (by simpa [n] using htd)

/-- Problem 1.8.2: any continuous self-map of `S¹` whose degree is not `1` has a fixed point. -/
-- Proof sketch: argue contrapositively. If `f` has no fixed point, then the quotient map
-- `z ↦ f z / z` is a well-defined continuous self-map of `S¹`. Its degree is `deg(f) - 1`, and
-- the absence of fixed points lets one show this quotient is null-homotopic, hence has degree
-- `0`. Therefore `deg(f) = 1`, contradicting the hypothesis.
theorem circle_exists_fixed_point_of_degree_ne_one
    (f : C(Circle, Circle)) (hf : deg(f) ≠ 1) :
    ∃ z : Circle, Function.IsFixedPt f z := by
  classical
  by_contra hnofix
  push Not at hnofix
  have hno : ∀ z : Circle, f z ≠ z := by
    intro z
    simpa [Function.IsFixedPt] using hnofix z
  let c : ℝ := Complex.arg (f 1) / (2 * Real.pi)
  have hc : Real.fourierChar c = f 1 := by
    -- Choose a concrete lift of the basepoint `f 1` using the argument.
    dsimp [c]
    rw [Real.fourierChar_apply']
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      positivity
    field_simp [h2pi]
    simpa using Circle.exp_arg (f 1)
  let g : C(ℝ, Circle) := f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  obtain ⟨F, hF, -⟩ := real_fourierChar_isCoveringMap.existsUnique_continuousMap_lifts g 0 c
    (by simpa [g, Function.comp_apply] using hc)
  have hF0 : F 0 = c := hF.1
  have hFcomp : Real.fourierChar ∘ F = f.comp ⟨Real.fourierChar, Real.continuous_fourierChar⟩ := by
    simpa [g] using hF.2
  have hdeg :
      F 1 - c = (deg(f) : ℝ) :=
    circleDegree_eq_fourierChar_lift_displacement f hc F hF0 hFcomp
  let d : ℝ → ℝ := fun t ↦ F t - t
  have hd : Continuous d := F.continuous.sub continuous_id
  have havoid : ∀ t : ℝ, ∀ n : ℤ, d t ≠ n := by
    intro t n
    exact fourierChar_lift_difference_ne_int_of_no_fixed_points f hno F hFcomp t n
  have hstep : d 1 - d 0 = ((deg(f) - 1 : ℤ) : ℝ) := by
    -- The displacement changes by `deg(f) - 1` over a unit turn.
    dsimp [d]
    calc
      (F 1 - 1) - (F 0 - 0) = (F 1 - F 0) - 1 := by ring
      _ = ((deg(f) : ℤ) : ℝ) - 1 := by simpa [hF0] using congrArg (fun x : ℝ ↦ x - c) hdeg
      _ = ((deg(f) - 1 : ℤ) : ℝ) := by norm_num
  have hzero : deg(f) - 1 = 0 :=
    integer_avoiding_continuous_step_eq_zero hd havoid hstep
  exact hf (sub_eq_zero.mp hzero)
