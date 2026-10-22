/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part13

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Helper for Example 26.2.1: the open-quadrant `+∞` extension of the real core is proper convex,
and its effective-domain interior is exactly the open positive quadrant. -/
lemma helperForExample_26_2_1_openQuadrantExtension_package :
    ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
        helperForExample_26_2_1_openQuadrantExtension ∧
      interior (effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
        helperForExample_26_2_1_openQuadrantExtension) = openPositiveQuadrantR2 := by
  let φ : (Fin 2 → ℝ) → ℝ := fun x => x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1)
  have hCopen : IsOpen openPositiveQuadrantR2 :=
    helperForExample_26_2_1_openQuadrant_isOpen
  have hCconv : Convex ℝ openPositiveQuadrantR2 :=
    helperForExample_26_2_1_openQuadrant_isConvex
  have hCne : openPositiveQuadrantR2.Nonempty := by
    refine ⟨![1, 1], ?_⟩
    simp [openPositiveQuadrantR2]
  have hEqOn :
      Set.EqOn (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) φ
        openPositiveQuadrantR2 := by
    intro x hx
    -- On the open quadrant the piecewise function agrees with the real core.
    simpa [φ] using congrArg EReal.toReal
      (helperForExample_26_2_1_value_on_openQuadrant hx)
  have hφconv : ConvexOn ℝ openPositiveQuadrantR2 φ := by
    -- Strict convexity on the open quadrant gives the convexity input needed for the extension.
    exact (helperForExample_26_2_1_strictConvexOn_openQuadrant.convexOn).congr hEqOn
  -- Apply Corollary 25.5.1 to the real core and rewrite the resulting extension.
  simpa [helperForExample_26_2_1_openQuadrantExtension, φ] using
    (helperForCorollary_25_5_1_properConvexExtension
      (hCopen := hCopen) (_hCconv := hCconv) hCne hφconv)

/-- Helper for Example 26.2.1: the open-quadrant extension is finite exactly on the open positive
quadrant. -/
lemma helperForExample_26_2_1_openQuadrantExtension_effectiveDomain_eq :
    effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
      helperForExample_26_2_1_openQuadrantExtension = openPositiveQuadrantR2 := by
  ext x
  constructor
  · intro hx
    rw [effectiveDomain_eq] at hx
    rcases hx with ⟨_, hfinite⟩
    by_cases hxOpen : x ∈ openPositiveQuadrantR2
    · exact hxOpen
    · -- Off the open quadrant the indicator term forces the extension to be `+∞`.
      have hIndicator :
          indicatorFunction openPositiveQuadrantR2 x = (⊤ : EReal) := by
        simp [indicatorFunction, hxOpen]
      have hxTop :
          helperForExample_26_2_1_openQuadrantExtension x = (⊤ : EReal) := by
        rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
        have htop :=
          (EReal.add_top_of_ne_bot
            (x := (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ)) : EReal))
            (EReal.coe_ne_bot _))
        convert htop using 1 <;> simp [sub_eq_add_neg, EReal.coe_mul]
      exact False.elim ((not_lt_of_ge le_rfl) (hxTop ▸ hfinite))
  · intro hx
    rcases hx with ⟨hx0, hx1⟩
    have hxOpen : x ∈ openPositiveQuadrantR2 := ⟨hx0, hx1⟩
    rw [effectiveDomain_eq]
    constructor
    · simp
    · -- On the open quadrant the extension is exactly its finite real-valued core, hence finite.
      have hIndicator :
          indicatorFunction openPositiveQuadrantR2 x = (0 : EReal) := by
        simp [indicatorFunction, hxOpen]
      have hxVal :
          helperForExample_26_2_1_openQuadrantExtension x =
            (((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ)) : EReal) := by
        rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
        simp
      rw [hxVal]
      change ((((x 1 ^ 2 / (2 * x 0) - 2 * Real.sqrt (x 1) : ℝ)) : EReal) < ⊤)
      exact EReal.coe_lt_top _

/-- Helper for Example 26.2.1: every open-quadrant point is a theorem-side relative-interior
basepoint for the closure-limit formula. -/
lemma helperForExample_26_2_1_openQuadrantExtension_basepoint_mem_relativeInterior
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x ∈
      euclideanRelativeInterior 2
        (((fun z : EuclideanSpace ℝ (Fin 2) => (z : Fin 2 → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
            helperForExample_26_2_1_openQuadrantExtension)) := by
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    ((fun z : EuclideanSpace ℝ (Fin 2) => (z : Fin 2 → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
        helperForExample_26_2_1_openQuadrantExtension)
  have hCopen : IsOpen C := by
    -- After identifying the effective domain, the theorem-side set is an open preimage.
    simpa [C, helperForExample_26_2_1_openQuadrantExtension_effectiveDomain_eq] using
      helperForExample_26_2_1_openQuadrant_isOpen.preimage (by fun_prop)
  have hxC : (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x ∈ C := by
    -- The transported point lies in the preimage because its coordinate representative is `x`.
    change
      (((EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x :
          EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ) ∈
        effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
          helperForExample_26_2_1_openQuadrantExtension
    simpa [helperForExample_26_2_1_openQuadrantExtension_effectiveDomain_eq] using hx
  have hCne : C.Nonempty := ⟨(EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x, hxC⟩
  have hspanC : affineSpan ℝ C = ⊤ := hCopen.affineSpan_eq_top hCne
  have hriC : euclideanRelativeInterior 2 C = interior C := by
    -- Open nonempty subsets of `ℝ²` are full-dimensional, so their relative interior is ordinary
    -- interior.
    apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := 2) (C := C)
    simp [hspanC]
  have hxInt : (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x ∈ interior C := by
    exact mem_interior_iff_mem_nhds.2 (hCopen.mem_nhds hxC)
  simpa [C, hriC] using hxInt

/-- Helper for Example 26.2.1: the Euclidean-space segment expressions produced by the closure
theorem simplify to the expected coordinate formulas for the three basepoints used below. -/
lemma helperForExample_26_2_1_segmentCoordinateRewrite_euclideanClosureBasepoints
    (x : Fin 2 → ℝ) (t : ℝ) :
    ((((1 - t) • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm (![1, 1] : Fin 2 → ℝ) +
        t • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x :
          EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ) =
        ![1 - t + t * x 0, 1 - t + t * x 1]) ∧
      ((((1 - t) • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm (x + ![1, 1]) +
          t • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x :
            EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ) =
          ![x 0 + (1 - t), x 1 + (1 - t)]) ∧
      ((((1 - t) • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm (x + ![1, 0]) +
          t • (EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x :
            EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ) =
          ![x 0 + (1 - t), x 1]) := by
  constructor
  · -- The fixed basepoint `![1, 1]` contributes `1 - t` to each coordinate.
    ext i
    fin_cases i
    · change (1 - t) * 1 + t * x 0 = 1 - t + t * x 0
      ring
    · change (1 - t) * 1 + t * x 1 = 1 - t + t * x 1
      ring
  constructor
  · -- Translating the basepoint by `x` makes the segment add `1 - t` coordinatewise.
    ext i
    fin_cases i
    · change (1 - t) * (x 0 + 1) + t * x 0 = x 0 + (1 - t)
      ring
    · change (1 - t) * (x 1 + 1) + t * x 1 = x 1 + (1 - t)
      ring
  · -- Translating by `![1, 0]` perturbs only the first coordinate.
    ext i
    fin_cases i
    · change (1 - t) * (x 0 + 1) + t * x 0 = x 0 + (1 - t)
      ring
    · have htail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, htail]
      ring

/-- Helper for Example 26.2.1: along the segment approaching a nonnegative `ξ₁`-axis point from
the open quadrant, the closure limit of the core branch is `0`. -/
lemma helperForExample_26_2_1_axisClosureLimit {a : ℝ} (ha : 0 ≤ a) :
    Filter.Tendsto
      (fun t : ℝ =>
        (((((1 - t) ^ 2 / (2 * (a + (1 - t))) - 2 * Real.sqrt (1 - t) : ℝ))) : EReal))
      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (nhds (0 : EReal)) := by
  by_cases ha0 : a = 0
  · let g : ℝ → ℝ := fun t => (1 - t) / 2 - 2 * Real.sqrt (1 - t)
    have hEventuallyEq :
        Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
          (fun t : ℝ =>
            (((((1 - t) ^ 2 / (2 * (a + (1 - t))) - 2 * Real.sqrt (1 - t) : ℝ))) : EReal))
          (fun t : ℝ => ((g t : ℝ) : EReal)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hden : 2 * (1 - t) ≠ 0 := by
        have ht' : 0 < 1 - t := sub_pos.mpr ht
        have : 0 < 2 * (1 - t) := by positivity
        exact ne_of_gt this
      apply congrArg (fun r : ℝ => (r : EReal))
      calc
        (1 - t) ^ 2 / (2 * (a + (1 - t))) - 2 * Real.sqrt (1 - t) =
            (1 - t) ^ 2 / (2 * (1 - t)) - 2 * Real.sqrt (1 - t) := by
              simp [ha0]
        _ = (1 - t) / 2 - 2 * Real.sqrt (1 - t) := by
              field_simp [hden]
        _ = g t := by
              rfl
    have hOneSub : ContinuousWithinAt (fun t : ℝ => 1 - t) (Set.Iio 1) 1 :=
      continuousWithinAt_const.sub continuousWithinAt_id
    have hSqrt :
        ContinuousWithinAt (fun t : ℝ => Real.sqrt (1 - t)) (Set.Iio 1) 1 :=
      Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hOneSub
    have hHalf :
        ContinuousWithinAt (fun t : ℝ => (1 - t) / 2) (Set.Iio 1) 1 := by
      exact hOneSub.div_const 2
    have hCont : ContinuousWithinAt g (Set.Iio 1) 1 := by
      -- After the algebraic rewrite at `a = 0`, the axis limit is a sum of continuous terms.
      exact hHalf.sub (continuousWithinAt_const.mul hSqrt)
    have hReal :
        Filter.Tendsto g (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (nhds 0) := by
      simpa [g] using hCont.tendsto
    have hcoe : Continuous fun r : ℝ => ((r : ℝ) : EReal) := by
      simpa using (EReal.continuous_coe_iff (f := fun r : ℝ => r)).2 continuous_id
    exact (hcoe.continuousAt.tendsto.comp hReal).congr' hEventuallyEq.symm
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
    let g : ℝ → ℝ := fun t =>
      (1 - t) ^ 2 / (2 * (a + (1 - t))) - 2 * Real.sqrt (1 - t)
    have hOneSub : ContinuousWithinAt (fun t : ℝ => 1 - t) (Set.Iio 1) 1 :=
      continuousWithinAt_const.sub continuousWithinAt_id
    have hNum : ContinuousWithinAt (fun t : ℝ => (1 - t) ^ 2) (Set.Iio 1) 1 :=
      hOneSub.pow 2
    have hDen :
        ContinuousWithinAt (fun t : ℝ => 2 * (a + (1 - t))) (Set.Iio 1) 1 := by
      exact continuousWithinAt_const.mul (continuousWithinAt_const.add hOneSub)
    have hQuot :
        ContinuousWithinAt (fun t : ℝ => (1 - t) ^ 2 / (2 * (a + (1 - t))))
          (Set.Iio 1) 1 := by
      refine hNum.div hDen ?_
      positivity
    have hSqrt :
        ContinuousWithinAt (fun t : ℝ => Real.sqrt (1 - t)) (Set.Iio 1) 1 :=
      Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hOneSub
    have hCont : ContinuousWithinAt g (Set.Iio 1) 1 := by
      -- For `a > 0`, every denominator stays nonzero at the limit point, so continuity is direct.
      exact hQuot.sub (continuousWithinAt_const.mul hSqrt)
    have hReal :
        Filter.Tendsto g (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (nhds 0) := by
      simpa [g] using hCont.tendsto
    have hcoe : Continuous fun r : ℝ => ((r : ℝ) : EReal) := by
      simpa using (EReal.continuous_coe_iff (f := fun r : ℝ => r)).2 continuous_id
    simpa [g] using (hcoe.continuousAt.tendsto.comp hReal)

/-- Helper for Example 26.2.1: the translated interior basepoints used in the closure argument
produce the expected coordinatewise segment formulas. -/
lemma helperForExample_26_2_1_segmentCoordinateRewrite_translatedInteriorBasepoints
    (x : Fin 2 → ℝ) (t : ℝ) :
    (((1 - t) • (x + ![1, 1]) + t • x : Fin 2 → ℝ) = ![x 0 + (1 - t), x 1 + (1 - t)]) ∧
      (((1 - t) • (x + ![1, 0]) + t • x : Fin 2 → ℝ) = ![x 0 + (1 - t), x 1]) := by
  constructor
  · -- The `x + (1, 1)` segment adds `1 - t` to both coordinates.
    ext i
    fin_cases i
    · change (1 - t) * (x 0 + 1) + t * x 0 = x 0 + (1 - t)
      ring
    · change (1 - t) * (x 1 + 1) + t * x 1 = x 1 + (1 - t)
      ring
  · -- The `x + (1, 0)` segment only perturbs the first coordinate.
    ext i
    fin_cases i
    · change (1 - t) * (x 0 + 1) + t * x 0 = x 0 + (1 - t)
      ring
    · have htail : Matrix.vecHead (Matrix.vecTail x) = x 1 := rfl
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, htail]
      ring

/-- Helper for Example 26.2.1: on the positive `ξ₂`-axis, the quadratic-over-linear core tends to
`+∞` along the translated interior segment. -/
lemma helperForExample_26_2_1_verticalAxis_coreBlowup {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun t : ℝ => (((b ^ 2 / (2 * (1 - t)) - 2 * Real.sqrt b : ℝ)) : EReal))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (⊤ : EReal)) := by
  rw [EReal.tendsto_nhds_top_iff_real]
  intro x
  let K : ℝ := max 1 (x + 2 * Real.sqrt b + 1)
  let A : ℝ := b ^ 2 / (2 * K)
  have hKpos : 0 < K := by
    -- Choose a positive comparison threshold dominating the affine shift by `-2 √b`.
    dsimp [K]
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hKgt : x + 2 * Real.sqrt b < K := by
    dsimp [K]
    have hlt : x + 2 * Real.sqrt b < x + 2 * Real.sqrt b + 1 := by
      linarith
    exact lt_of_lt_of_le hlt (le_max_right _ _)
  have hApos : 0 < A := by
    -- The translated denominator window has positive radius because `b > 0`.
    dsimp [A]
    positivity
  have hEvent : Set.Ioo (1 - A) 1 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    -- Restrict to a left-neighborhood where `1 - t` is smaller than the chosen radius.
    exact Ioo_mem_nhdsLT (sub_lt_self _ hApos)
  filter_upwards [hEvent] with t ht
  have htlt : t < 1 := ht.2
  have htlower : 1 - A < t := ht.1
  have honeSubPos : 0 < 1 - t := sub_pos.mpr htlt
  have honeSubLt : 1 - t < b ^ 2 / (2 * K) := by
    dsimp [A] at *
    linarith
  have hfrac : K < b ^ 2 / (2 * (1 - t)) := by
    -- Shrinking `1 - t` forces the reciprocal quadratic-over-linear term above `K`.
    have hdenpos : 0 < 2 * (1 - t) := by
      positivity
    rw [lt_div_iff₀ hdenpos]
    have hmul := mul_lt_mul_of_pos_left honeSubLt hKpos
    have hmul' : K * (1 - t) < b ^ 2 / 2 := by
      have hEq : K * (b ^ 2 / (2 * K)) = b ^ 2 / 2 := by
        field_simp [hKpos.ne']
      simpa [hEq] using hmul
    nlinarith
  -- Reinsert the constant `-2 √b`; the reciprocal term still dominates every real threshold.
  have hreal : x < b ^ 2 / (2 * (1 - t)) - 2 * Real.sqrt b := by
    linarith
  exact_mod_cast hreal

/-- Helper for Example 26.2.1: the convex closure of the open-quadrant extension takes the value
`0` on the nonnegative `ξ₁`-axis. -/
lemma helperForExample_26_2_1_openQuadrantExtension_closure_eq_zero_on_axis
    {x : Fin 2 → ℝ} (hx : x ∈ nonnegativeXi1AxisR2) :
    convexFunctionClosure helperForExample_26_2_1_openQuadrantExtension x = (0 : EReal) := by
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
  let e := EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)
  let x0E : EuclideanSpace ℝ (Fin 2) := e.symm (x + ![1, 1])
  let yE : EuclideanSpace ℝ (Fin 2) := e.symm x
  have hx0Open : x + ![1, 1] ∈ openPositiveQuadrantR2 := by
    rcases hx with ⟨hx0, hx1⟩
    constructor
    · simpa using add_pos_of_nonneg_of_pos hx0 (show (0 : ℝ) < 1 by norm_num)
    · simp [hx1]
  have hx0ri :
      x0E ∈
        euclideanRelativeInterior 2
          (((fun z : EuclideanSpace ℝ (Fin 2) => (z : Fin 2 → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              helperForExample_26_2_1_openQuadrantExtension)) :=
    by simpa [x0E, e] using
      helperForExample_26_2_1_openQuadrantExtension_basepoint_mem_relativeInterior hx0Open
  have hlim :=
    ((convexFunctionClosure_eq_limit_along_segment
      (f := helperForExample_26_2_1_openQuadrantExtension) (x := x0E) hx0ri).1
      hproperExt yE)
  have haxisLim :
      Filter.Tendsto
        (fun t : ℝ =>
          (((((1 - t) ^ 2 / (2 * (x 0 + (1 - t))) - 2 * Real.sqrt (1 - t) : ℝ))) : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (nhds (0 : EReal)) :=
    helperForExample_26_2_1_axisClosureLimit hx.1
  have hEventuallyEq :
      Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
        (fun t : ℝ =>
          helperForExample_26_2_1_openQuadrantExtension
            ((((1 - t) • x0E + t • yE : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ)))
        (fun t : ℝ =>
          (((((1 - t) ^ 2 / (2 * (x 0 + (1 - t))) - 2 * Real.sqrt (1 - t) : ℝ))) : EReal)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rcases
        helperForExample_26_2_1_segmentCoordinateRewrite_euclideanClosureBasepoints x t with
      ⟨_hFixed, hAxis, _hVertical⟩
    have hpos : 0 < x 0 + (1 - t) ∧ 0 < 1 - t := by
      constructor
      · have : 0 < 1 - t := sub_pos.mpr ht
        linarith [hx.1]
      · exact sub_pos.mpr ht
    have hAxisMem : ![x 0 + (1 - t), 1 - t] ∈ openPositiveQuadrantR2 := by
      simpa [openPositiveQuadrantR2, hx.2] using hpos
    have hIndicator :
        indicatorFunction openPositiveQuadrantR2 ![x 0 + (1 - t), 1 - t] = (0 : EReal) := by
      simp [indicatorFunction, hAxisMem]
    -- Along the axis segment the indicator vanishes and only the real core remains.
    rw [hAxis]
    simp [helperForExample_26_2_1_openQuadrantExtension, hIndicator, hx.2]
  -- The rewritten segment has the explicit one-variable limit `0`, so the closure value is `0`.
  exact tendsto_nhds_unique (hlim.congr' hEventuallyEq) haxisLim

/-- Helper for Example 26.2.1: if a point has a negative coordinate, then the segment from an
interior point eventually leaves the open quadrant, so the closure value is `+∞`. -/
lemma helperForExample_26_2_1_openQuadrantExtension_closure_eq_top_outsideQuadrantClosure
    {x : Fin 2 → ℝ} (hx : x 0 < 0 ∨ x 1 < 0) :
    convexFunctionClosure helperForExample_26_2_1_openQuadrantExtension x = (⊤ : EReal) := by
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
  let e := EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)
  let x0E : EuclideanSpace ℝ (Fin 2) := e.symm (![1, 1] : Fin 2 → ℝ)
  let yE : EuclideanSpace ℝ (Fin 2) := e.symm x
  have hx0ri :
      x0E ∈
        euclideanRelativeInterior 2
          (((fun z : EuclideanSpace ℝ (Fin 2) => (z : Fin 2 → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              helperForExample_26_2_1_openQuadrantExtension)) := by
    simpa [x0E, e] using
      helperForExample_26_2_1_openQuadrantExtension_basepoint_mem_relativeInterior
        (by simp [openPositiveQuadrantR2])
  have hlim :=
    ((convexFunctionClosure_eq_limit_along_segment
      (f := helperForExample_26_2_1_openQuadrantExtension) (x := x0E) hx0ri).1
      hproperExt yE)
  have hEventNeg :
      ∀ i : Fin 2, x i < 0 →
        ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)), 1 - t + t * x i < 0 := by
    intro i hi
    have hcont : ContinuousWithinAt (fun t : ℝ => 1 - t + t * x i) (Set.Iio (1 : ℝ)) 1 := by
      exact (continuousWithinAt_const.sub continuousWithinAt_id).add
        (continuousWithinAt_id.mul continuousWithinAt_const)
    have htend :
        Filter.Tendsto (fun t : ℝ => 1 - t + t * x i)
          (nhdsWithin 1 (Set.Iio (1 : ℝ))) (nhds (x i)) := by
      simpa using hcont.tendsto
    have hopen : {s : ℝ | s < 0} ∈ nhds (x i) := by
      exact (isOpen_lt continuous_id continuous_const).mem_nhds hi
    exact Filter.mem_of_superset (htend hopen) (by intro t ht; simpa using ht)
  have hEventuallyEq :
      Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
        (fun t : ℝ =>
          helperForExample_26_2_1_openQuadrantExtension
            ((((1 - t) • x0E + t • yE : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ)))
        (fun _ : ℝ => (⊤ : EReal)) := by
    rcases hx with hx0 | hx1
    · filter_upwards [hEventNeg 0 hx0] with t ht
      rcases
          helperForExample_26_2_1_segmentCoordinateRewrite_euclideanClosureBasepoints x t with
        ⟨hFixed, _hAxis, _hVertical⟩
      let v : Fin 2 → ℝ := ![1 - t + t * x 0, 1 - t + t * x 1]
      have hnotMem : v ∉ openPositiveQuadrantR2 := by
        intro hv
        exact (not_lt_of_ge hv.1.le) ht
      have hIndicator :
          indicatorFunction openPositiveQuadrantR2 v =
            (⊤ : EReal) := by
        simp [indicatorFunction, hnotMem]
      -- A negative first coordinate keeps the segment outside the open quadrant.
      rw [hFixed]
      rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
      have htop :=
        (EReal.add_top_of_ne_bot
          (x := ((((1 - t + t * x 1) ^ 2 / (2 * (1 - t + t * x 0)) -
            2 * Real.sqrt (1 - t + t * x 1) : ℝ)) : EReal))
          (EReal.coe_ne_bot _))
      convert htop using 1 <;> simp [sub_eq_add_neg, EReal.coe_mul]
    · filter_upwards [hEventNeg 1 hx1] with t ht
      rcases
          helperForExample_26_2_1_segmentCoordinateRewrite_euclideanClosureBasepoints x t with
        ⟨hFixed, _hAxis, _hVertical⟩
      let v : Fin 2 → ℝ := ![1 - t + t * x 0, 1 - t + t * x 1]
      have hnotMem : v ∉ openPositiveQuadrantR2 := by
        intro hv
        exact (not_lt_of_ge hv.2.le) ht
      have hIndicator :
          indicatorFunction openPositiveQuadrantR2 v =
            (⊤ : EReal) := by
        simp [indicatorFunction, hnotMem]
      -- A negative second coordinate yields the same eventual `+∞` behavior.
      rw [hFixed]
      rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
      have htop :=
        (EReal.add_top_of_ne_bot
          (x := ((((1 - t + t * x 1) ^ 2 / (2 * (1 - t + t * x 0)) -
            2 * Real.sqrt (1 - t + t * x 1) : ℝ)) : EReal))
          (EReal.coe_ne_bot _))
      convert htop using 1 <;> simp [sub_eq_add_neg, EReal.coe_mul]
  have htopLim :
      Filter.Tendsto (fun _ : ℝ => (⊤ : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))) (nhds (⊤ : EReal)) := by
    simpa using tendsto_const_nhds
  -- The closure-limit theorem and the eventual-`⊤` rewrite identify the boundary value as `+∞`.
  exact tendsto_nhds_unique (hlim.congr' hEventuallyEq) htopLim

/-- Helper for Example 26.2.1: approaching a point of the positive `ξ₂`-axis from the interior
forces the core term `ξ₂^2 / (2 ξ₁)` to blow up, so the closure value is `+∞`. -/
lemma helperForExample_26_2_1_openQuadrantExtension_closure_eq_top_on_verticalAxis
    {x : Fin 2 → ℝ} (hx : x 0 = 0 ∧ 0 < x 1) :
    convexFunctionClosure helperForExample_26_2_1_openQuadrantExtension x = (⊤ : EReal) := by
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
  let e := EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)
  let x0E : EuclideanSpace ℝ (Fin 2) := e.symm (x + ![1, 0])
  let yE : EuclideanSpace ℝ (Fin 2) := e.symm x
  have hx0Open : x + ![1, 0] ∈ openPositiveQuadrantR2 := by
    constructor <;> simp [hx.1, hx.2]
  have hx0ri :
      x0E ∈
        euclideanRelativeInterior 2
          (((fun z : EuclideanSpace ℝ (Fin 2) => (z : Fin 2 → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin 2 → ℝ))
              helperForExample_26_2_1_openQuadrantExtension)) :=
    by simpa [x0E, e] using
      helperForExample_26_2_1_openQuadrantExtension_basepoint_mem_relativeInterior hx0Open
  have hlim :=
    ((convexFunctionClosure_eq_limit_along_segment
      (f := helperForExample_26_2_1_openQuadrantExtension) (x := x0E) hx0ri).1
      hproperExt yE)
  have hverticalLim :
      Filter.Tendsto
        (fun t : ℝ => ((((x 1 ^ 2 / (2 * (1 - t)) - 2 * Real.sqrt (x 1) : ℝ))) : EReal))
        (nhdsWithin 1 (Set.Iio 1)) (nhds (⊤ : EReal)) :=
    helperForExample_26_2_1_verticalAxis_coreBlowup hx.2
  have hEventuallyEq :
      Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
        (fun t : ℝ =>
          helperForExample_26_2_1_openQuadrantExtension
            ((((1 - t) • x0E + t • yE : EuclideanSpace ℝ (Fin 2)) : Fin 2 → ℝ)))
        (fun t : ℝ =>
          ((((x 1 ^ 2 / (2 * (1 - t)) - 2 * Real.sqrt (x 1) : ℝ))) : EReal)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rcases
        helperForExample_26_2_1_segmentCoordinateRewrite_euclideanClosureBasepoints x t with
      ⟨_hFixed, _hAxis, hVertical⟩
    have hpos : 0 < 1 - t ∧ 0 < x 1 := ⟨sub_pos.mpr ht, hx.2⟩
    have hVerticalMem : ![1 - t, x 1] ∈ openPositiveQuadrantR2 := by
      simpa [openPositiveQuadrantR2] using hpos
    have hIndicator : indicatorFunction openPositiveQuadrantR2 ![1 - t, x 1] = (0 : EReal) := by
      simp [indicatorFunction, hVerticalMem]
    -- On the vertical-axis segment the second coordinate stays fixed and positive.
    rw [hVertical]
    simp [hx.1]
    rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
    simp
  -- The reciprocal quadratic-over-linear term diverges to `+∞` along this segment.
  exact tendsto_nhds_unique (hlim.congr' hEventuallyEq) hverticalLim

/-- Helper for Example 26.2.1: the textbook piecewise function is exactly the closed convex
closure of the open-quadrant `+∞` extension of its real core. -/
lemma helperForExample_26_2_1_openQuadrantExtension_closure_eq_target :
    convexFunctionClosure helperForExample_26_2_1_openQuadrantExtension =
      quadraticOverLinearMinusSqrtFunction := by
  funext x
  by_cases hxOpen : x ∈ openPositiveQuadrantR2
  · rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
    have hxri :=
      helperForExample_26_2_1_openQuadrantExtension_basepoint_mem_relativeInterior hxOpen
    have hagree :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := helperForExample_26_2_1_openQuadrantExtension) hproperExt).2
        ((EuclideanSpace.equiv (ι := Fin 2) (𝕜 := ℝ)).symm x) hxri
    have hExtVal :
        helperForExample_26_2_1_openQuadrantExtension x =
          quadraticOverLinearMinusSqrtFunction x := by
      rcases hxOpen with ⟨hx0, hx1⟩
      have hxMem : x ∈ openPositiveQuadrantR2 := ⟨hx0, hx1⟩
      have hIndicator : indicatorFunction openPositiveQuadrantR2 x = (0 : EReal) := by
        simp [indicatorFunction, hxMem]
      -- On interior points both functions are the same finite real branch.
      rw [helperForExample_26_2_1_openQuadrantExtension, hIndicator]
      simp [quadraticOverLinearMinusSqrtFunction, hxMem, hx0, hx1, le_of_lt hx1]
    simpa using hagree.trans hExtVal
  · by_cases hneg : x 0 < 0 ∨ x 1 < 0
    · rw [helperForExample_26_2_1_openQuadrantExtension_closure_eq_top_outsideQuadrantClosure hneg]
      have hxNeZero : x ≠ 0 := by
        intro hxZero
        rcases hneg with hx0 | hx1
        · have : (0 : ℝ) < 0 := by simpa [hxZero] using hx0
          linarith
        · have : (0 : ℝ) < 0 := by simpa [hxZero] using hx1
          linarith
      have hnotBranch : ¬ (0 < x 0 ∧ 0 ≤ x 1) := by
        intro hbranch
        rcases hneg with hx0 | hx1
        · linarith
        · linarith
      -- A negative coordinate places the textbook function in the exterior `+∞` branch.
      simp [quadraticOverLinearMinusSqrtFunction, hnotBranch, hxNeZero]
    · by_cases hvert : x 0 = 0 ∧ 0 < x 1
      · rw [helperForExample_26_2_1_openQuadrantExtension_closure_eq_top_on_verticalAxis hvert]
        have hxNeZero : x ≠ 0 := by
          intro hxZero
          have : x 1 = 0 := by simpa [hxZero]
          linarith
        have hnotBranch : ¬ (0 < x 0 ∧ 0 ≤ x 1) := by
          intro hbranch
          linarith [hbranch.1]
        -- The positive vertical axis also lands in the `+∞` branch of the textbook function.
        simp [quadraticOverLinearMinusSqrtFunction, hnotBranch, hxNeZero]
      · have hx0nonneg : 0 ≤ x 0 := by
          by_contra hx0neg
          exact hneg (Or.inl (lt_of_not_ge hx0neg))
        have hx1nonneg : 0 ≤ x 1 := by
          by_contra hx1neg
          exact hneg (Or.inr (lt_of_not_ge hx1neg))
        have hx1zero : x 1 = 0 := by
          by_contra hx1zero
          have hx1pos : 0 < x 1 := lt_of_le_of_ne hx1nonneg (by simpa [eq_comm] using hx1zero)
          by_cases hx0zero : x 0 = 0
          · exact hvert ⟨hx0zero, hx1pos⟩
          · have hx0pos : 0 < x 0 := lt_of_le_of_ne hx0nonneg (Ne.symm hx0zero)
            exact hxOpen ⟨hx0pos, hx1pos⟩
        have hxAxis : x ∈ nonnegativeXi1AxisR2 := ⟨hx0nonneg, hx1zero⟩
        -- The remaining case is exactly the nonnegative `ξ₁`-axis, where both functions vanish.
        rw [helperForExample_26_2_1_openQuadrantExtension_closure_eq_zero_on_axis hxAxis,
          helperForExample_26_2_1_value_on_nonnegativeXi1Axis hxAxis]

/-- Helper for Example 26.2.1: the real core is differentiable at every point of the open
positive quadrant. -/
lemma helperForExample_26_2_1_coreDifferentiableAt_openQuadrant
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 1 ^ 2 / (2 * y 0) - 2 * Real.sqrt (y 1)) x := by
  rcases hx with ⟨hx0, hx1⟩
  have hnum : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 1 ^ 2) x := by
    -- The numerator is a polynomial in the second coordinate.
    fun_prop
  have hden : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => 2 * y 0) x := by
    -- The denominator is a nonvanishing scalar multiple of the first coordinate.
    exact ((differentiable_apply 0).differentiableAt).const_mul 2
  have hinv : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => (2 * y 0)⁻¹) x := by
    refine hden.inv ?_
    positivity
  have hquot : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => y 1 ^ 2 / (2 * y 0)) x := by
    -- Rewrite division as multiplication by the reciprocal of the positive denominator.
    simpa [div_eq_mul_inv] using hnum.mul hinv
  have hsqrt : DifferentiableAt ℝ (fun y : Fin 2 → ℝ => Real.sqrt (y 1)) x := by
    -- Positivity of `x 1` lets us apply the chain rule through `sqrt`.
    refine DifferentiableAt.sqrt (f := fun y : Fin 2 → ℝ => y 1) ?_ ?_
    · fun_prop
    · linarith
  -- Subtracting the `2 √ξ₂` term preserves differentiability on the open quadrant.
  simpa [sub_eq_add_neg] using hquot.sub
    (show DifferentiableAt ℝ (fun y : Fin 2 → ℝ => 2 * Real.sqrt (y 1)) x by
      simpa using hsqrt.const_mul 2)

/-- Helper for Example 26.2.1: on the open positive quadrant, differentiability of the
open-quadrant extension transfers through the convex closure, so the subdifferential is a
singleton there. -/
lemma helperForExample_26_2_1_openQuadrant_subdifferential_singleton
    {x : Fin 2 → ℝ} (hx : x ∈ openPositiveQuadrantR2) :
    ∃ g : Fin 2 → ℝ,
      subdifferentialAt quadraticOverLinearMinusSqrtFunction x =
        {dotProductEquiv ℝ (Fin 2) g} := by
  let φ : (Fin 2 → ℝ) → ℝ := fun y => y 1 ^ 2 / (2 * y 0) - 2 * Real.sqrt (y 1)
  have hdiffCore : DifferentiableAt ℝ φ x := by
    -- Inside the open quadrant the real core is differentiable, so the `+∞` extension is too.
    simpa [φ] using helperForExample_26_2_1_coreDifferentiableAt_openQuadrant hx
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := helperForExample_26_2_1_openQuadrant_isOpen)
        (f := φ) (x := x) hx hdiffCore with
    ⟨hExtDiff, _hGradEq⟩
  rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _⟩
  have hExtConv : ConvexFunction helperForExample_26_2_1_openQuadrantExtension := by
    simpa [ConvexFunction] using hproperExt.1
  have hpreimageExt :
      ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
          subdifferentialAt helperForExample_26_2_1_openQuadrantExtension x) =
        ({erealGradientAt hExtDiff} : Set (Fin 2 → ℝ)) := by
    -- Differentiability collapses the Euclideanized subdifferential fiber to a singleton.
    exact
      helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient hExtConv hExtDiff
  have hsubNonemptyExt :
      Set.Nonempty (subdifferentialAt helperForExample_26_2_1_openQuadrantExtension x) := by
    refine ⟨dotProductEquiv ℝ (Fin 2) (erealGradientAt hExtDiff), ?_⟩
    have hmem :
        erealGradientAt hExtDiff ∈
          ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
            subdifferentialAt helperForExample_26_2_1_openQuadrantExtension x) := by
      simpa [hpreimageExt]
    simpa using hmem
  have hsubEqClosure :
      subdifferentialAt (convexFunctionClosure helperForExample_26_2_1_openQuadrantExtension) x =
        subdifferentialAt helperForExample_26_2_1_openQuadrantExtension x := by
    -- At a subdifferentiable point the closure and the original function have the same fiber.
    exact
      (convexFunctionClosure_eq_at_subdifferentiable_point_and_subdifferential_eq
        helperForExample_26_2_1_openQuadrantExtension hproperExt x hsubNonemptyExt).2
  have hsubEqTarget :
      subdifferentialAt quadraticOverLinearMinusSqrtFunction x =
        subdifferentialAt helperForExample_26_2_1_openQuadrantExtension x := by
    simpa [helperForExample_26_2_1_openQuadrantExtension_closure_eq_target] using hsubEqClosure
  have hpreimageTarget :
      ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
          subdifferentialAt quadraticOverLinearMinusSqrtFunction x) =
        ({erealGradientAt hExtDiff} : Set (Fin 2 → ℝ)) := by
    rw [hsubEqTarget]
    exact hpreimageExt
  refine ⟨erealGradientAt hExtDiff, ?_⟩
  ext ξ
  constructor
  · intro hξ
    have hpre :
        (dotProductEquiv ℝ (Fin 2)).symm ξ ∈
          ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
            subdifferentialAt quadraticOverLinearMinusSqrtFunction x) := by
      simpa using hξ
    have hs : (dotProductEquiv ℝ (Fin 2)).symm ξ = erealGradientAt hExtDiff := by
      simpa [hpreimageTarget] using hpre
    -- Applying the Euclidean equivalence back to the unique fiber element gives the desired
    -- singleton in dual coordinates.
    rw [Set.mem_singleton_iff]
    have := congrArg (dotProductEquiv ℝ (Fin 2)) hs
    simpa using this
  · intro hξ
    rw [Set.mem_singleton_iff] at hξ
    rw [hξ]
    have hpre :
        erealGradientAt hExtDiff ∈
          ((dotProductEquiv ℝ (Fin 2)) ⁻¹'
            subdifferentialAt quadraticOverLinearMinusSqrtFunction x) := by
      simpa [hpreimageTarget]
    simpa using hpre

/-- Helper for Example 26.2.1: the interior singleton fibers together with the already-proved
axis/exterior emptiness identify the whole effective domain of `∂ f` and show that `∂ f` is
globally single-valued. -/
lemma helperForExample_26_2_1_subdifferentialDomain_eq_openQuadrant_and_singleValued :
    subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction =
        openPositiveQuadrantR2 ∧
      IsSingleValuedMultivaluedMap (subdifferentialAt quadraticOverLinearMinusSqrtFunction) := by
  constructor
  · ext x
    constructor
    · intro hxSub
      exact helperForExample_26_2_1_subdifferentialEffectiveDomain_subset_openQuadrant hxSub
    · intro hxOpen
      rcases helperForExample_26_2_1_openQuadrant_subdifferential_singleton hxOpen with ⟨g, hg⟩
      change subdifferentialAt quadraticOverLinearMinusSqrtFunction x ≠ ∅
      rw [hg]
      simp
  · intro x u hu v hv
    by_cases hxOpen : x ∈ openPositiveQuadrantR2
    · rcases helperForExample_26_2_1_openQuadrant_subdifferential_singleton hxOpen with ⟨g, hg⟩
      rw [hg] at hu hv
      exact hu.trans hv.symm
    · have hxSub :
          x ∈ subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction := by
        change subdifferentialAt quadraticOverLinearMinusSqrtFunction x ≠ ∅
        intro hEmpty
        simpa [hEmpty] using hu
      exact False.elim (hxOpen
        (helperForExample_26_2_1_subdifferentialEffectiveDomain_subset_openQuadrant hxSub))

-- Proof sketch: compute the effective domain and subdifferential domain of the explicit
-- piecewise formula, note that the Hessian is positive definite on the open quadrant, observe that
-- the restriction to the non-negative `ξ₁`-axis is identically zero, and then invoke the Chapter
-- 26 definitions to package the example as essentially strictly convex and essentially smooth.
/-- Example 26.2.1: the function
`f(ξ₁, ξ₂) = ξ₂^2 / (2 ξ₁) - 2 √ξ₂` for `ξ₁ > 0`, `ξ₂ ≥ 0`, with `f(0, 0) = 0` and `f = +∞`
otherwise, has `dom ∂ f` equal to the open positive quadrant, is strictly convex there, is
constant on the non-negative `ξ₁`-axis and therefore not strictly convex on all of `dom f`, yet
is essentially strictly convex and essentially smooth. -/
theorem quadraticOverLinearMinusSqrtFunction_has_positiveQuadrantSubdifferentialDomain_and_essential_properties :
    subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction = openPositiveQuadrantR2 ∧
      StrictConvexOn ℝ openPositiveQuadrantR2
        (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) ∧
      Set.EqOn (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal)
        (fun _ : Fin 2 → ℝ => (0 : ℝ)) nonnegativeXi1AxisR2 ∧
      ¬ StrictConvexOn ℝ
        (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction)
        (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) ∧
      IsEssentiallyStrictlyConvex quadraticOverLinearMinusSqrtFunction ∧
      IsEssentiallySmooth quadraticOverLinearMinusSqrtFunction := by
  rcases helperForExample_26_2_1_effectiveDomain_and_axisValues with ⟨hdom, haxis⟩
  have hnotStrict :
      ¬ StrictConvexOn ℝ
        (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction)
        (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) :=
    helperForExample_26_2_1_not_strictConvexOn_effectiveDomain
  -- The explicit domain/axis computations already settle the easy geometric part of the example.
  have hsolved :
      Set.EqOn (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal)
          (fun _ : Fin 2 → ℝ => (0 : ℝ)) nonnegativeXi1AxisR2 ∧
        ¬ StrictConvexOn ℝ
          (effectiveDomain (Set.univ : Set (Fin 2 → ℝ)) quadraticOverLinearMinusSqrtFunction)
          (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) := by
    exact ⟨haxis, hnotStrict⟩
  have hsubdom_subset :
      subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction ⊆
        openPositiveQuadrantR2 :=
    helperForExample_26_2_1_subdifferentialEffectiveDomain_subset_openQuadrant
  have hstrict :
      StrictConvexOn ℝ openPositiveQuadrantR2
        (fun x => (quadraticOverLinearMinusSqrtFunction x).toReal) :=
    helperForExample_26_2_1_strictConvexOn_openQuadrant
  -- Route correction: the remaining work is not the axis geometry but the convex-analytic core:
  -- the reverse inclusion `openPositiveQuadrantR2 ⊆ dom ∂ f` and the Chapter 26 packaging
  -- remain; strict convexity on the open quadrant is now isolated in `hstrict`, while the
  -- exterior and axis exclusions are already encoded in `hsubdom_subset`.
  have hremaining :
      subdifferentialEffectiveDomain quadraticOverLinearMinusSqrtFunction =
          openPositiveQuadrantR2 ∧
        IsEssentiallyStrictlyConvex quadraticOverLinearMinusSqrtFunction ∧
        IsEssentiallySmooth quadraticOverLinearMinusSqrtFunction := by
    rcases helperForExample_26_2_1_openQuadrantExtension_package with ⟨hproperExt, _hintExt⟩
    have hclosurePkg :=
      convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := helperForExample_26_2_1_openQuadrantExtension) hproperExt
    have hproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin 2 → ℝ))
          quadraticOverLinearMinusSqrtFunction := by
      -- The textbook function is the closed convex closure of the open-quadrant extension.
      simpa [helperForExample_26_2_1_openQuadrantExtension_closure_eq_target] using hclosurePkg.1.2
    have hproperEReal :
        ProperConvexERealFunction (F := (Fin 2 → ℝ))
          quadraticOverLinearMinusSqrtFunction :=
      helperForLemma_26_2_properConvexERealFunction hproper
    have hclosed :
        LowerSemicontinuous quadraticOverLinearMinusSqrtFunction := by
      -- Lower semicontinuity comes from the closure package as well.
      simpa [helperForExample_26_2_1_openQuadrantExtension_closure_eq_target] using
        hclosurePkg.1.1.2
    rcases
        helperForExample_26_2_1_subdifferentialDomain_eq_openQuadrant_and_singleValued with
      ⟨hsubdom, hsingleValued⟩
    have hessStrict :
        IsEssentiallyStrictlyConvex quadraticOverLinearMinusSqrtFunction := by
      refine ⟨hproper, ?_⟩
      intro C hCsub hCconv
      have hCsubset : C ⊆ openPositiveQuadrantR2 := by
        intro x hxC
        simpa [hsubdom] using hCsub hxC
      -- Definition 26.2.1 reduces strict convexity on `C` to the already-proved interior case.
      exact hstrict.subset hCsubset hCconv
    have hessSmooth :
        IsEssentiallySmooth quadraticOverLinearMinusSqrtFunction :=
      ((subdifferential_singleValued_iff_essentiallySmooth
          (f := quadraticOverLinearMinusSqrtFunction) hproperEReal hclosed).1).1
        hsingleValued
    exact ⟨hsubdom, hessStrict, hessSmooth⟩
  rcases hsolved with ⟨haxis', hnotStrict'⟩
  rcases hremaining with ⟨hsubdom, hessStrict, hessSmooth⟩
  exact ⟨hsubdom, hstrict, haxis', hnotStrict', hessStrict, hessSmooth⟩


end Section26
end Chap05
