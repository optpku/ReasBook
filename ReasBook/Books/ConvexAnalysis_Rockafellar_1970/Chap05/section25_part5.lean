/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section15_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part4

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Theorem 25.3: on a small interval `(x, b) ⊆ I`, the right-derivative selector at
`x` is the greatest lower bound of its strict-right tail. -/
lemma helperForTheorem_25_3_rightDerivWithin_isGLB_on_Ioo
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x b : ℝ} (hx : x ∈ I) (hxb : x < b) (hIoo : Set.Ioo x b ⊆ I) :
    IsGLB ((fun t => derivWithin f (Set.Ioi t) t) '' Set.Ioo x b)
      (derivWithin f (Set.Ioi x) x) := by
  let g : ℝ → ℝ := fun t => derivWithin f (Set.Ioi t) t
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  have hmonoI : MonotoneOn g I := by
    simpa [g, hIopen.interior_eq] using hf.monotoneOn_rightDeriv
  have hsInfEq :
      derivWithin f (Set.Ioi x) x = sInf (slope f x '' Set.Ioo x b) := by
    -- Restrict the global `sInf` formula for the right derivative to a small interval inside `I`.
    calc
      derivWithin f (Set.Ioi x) x =
          sInf (slope f x '' {y | y ∈ I ∧ x < y}) := by
            exact hf.rightDeriv_eq_sInf_slope_of_mem_interior hxInt
      _ = sInf (slope f x '' Set.Ioo x b) := by
        symm
        apply (hf.monotoneOn_slope_gt hx).csInf_eq_of_subset_of_forall_exists_le
          (bddBelow_slope_lt_of_mem_interior hf hxInt)
        · intro y hy
          exact ⟨hIoo hy, hy.1⟩
        · rintro y ⟨hyI, hxy⟩
          obtain ⟨z, hxz, hzy⟩ := exists_between (lt_min hxb hxy)
          exact ⟨z, ⟨hxz, hzy.trans_le (min_le_left _ _)⟩, hzy.le.trans (min_le_right _ _)⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    -- Monotonicity of the right derivative makes every strict-right value dominate the value at `x`.
    exact hmonoI hx (hIoo hw) hw.1.le
  · intro u hu
    have hslopeLower :
        u ≤ sInf (slope f x '' Set.Ioo x b) := by
      refine le_csInf ?_ ?_
      · rw [Set.image_nonempty]
        exact Set.nonempty_Ioo.2 hxb
      · rintro _ ⟨y, hy, rfl⟩
        have hyI : y ∈ I := hIoo hy
        have hcontf : ContinuousOn f I := hf.continuousOn hIopen
        have hcontSlope : ContinuousAt (fun z : ℝ => slope f z y) x := by
          -- With the right endpoint fixed, secant slopes vary continuously as the left endpoint
          -- approaches `x`.
          have hcontNum :
              ContinuousAt (fun z : ℝ => f y - f z) x :=
            continuousAt_const.sub (hcontf.continuousAt (hIopen.mem_nhds hx))
          have hcontDen :
              ContinuousAt (fun z : ℝ => y - z) x :=
            continuousAt_const.sub continuousAt_id
          have hne : y - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hy.1)
          simpa [slope_def_field] using hcontNum.div hcontDen hne
        have hnebot : (𝓝[Set.Ioo x y] x).NeBot := by
          exact
            (mem_closure_iff_nhdsWithin_neBot).1 (by
              rw [closure_Ioo hy.1.ne]
              simp [hy.1.le])
        letI := hnebot
        have hmem :
            ∀ᶠ z in 𝓝[Set.Ioo x y] x, slope f z y ∈ Set.Ici u := by
          -- Every intermediate point contributes a right derivative below the secant slope to `y`.
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hzIoo : z ∈ Set.Ioo x b := ⟨hz.1, hz.2.trans hy.2⟩
          have huz : u ≤ derivWithin f (Set.Ioi z) z := hu ⟨z, hzIoo, rfl⟩
          have hzI : z ∈ I := hIoo hzIoo
          have hzInt : z ∈ interior I := by
            simpa [hIopen.interior_eq] using hzI
          have hsec :
              derivWithin f (Set.Ioi z) z ≤ slope f z y :=
            hf.rightDeriv_le_slope_of_mem_interior hzInt hyI hz.2
          exact le_trans huz hsec
        have htarget : slope f x y ∈ Set.Ici u :=
          isClosed_Ici.mem_of_tendsto hcontSlope.continuousWithinAt.tendsto hmem
        exact htarget
    simpa [hsInfEq] using hslopeLower

/-- Helper for Theorem 25.3: on a small interval `(a, x) ⊆ I`, the left-derivative selector at
`x` is the least upper bound of its strict-left tail. -/
lemma helperForTheorem_25_3_leftDerivWithin_isLUB_on_Ioo
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {a x : ℝ} (hx : x ∈ I) (hax : a < x) (hIoo : Set.Ioo a x ⊆ I) :
    IsLUB ((fun t => derivWithin f (Set.Iio t) t) '' Set.Ioo a x)
      (derivWithin f (Set.Iio x) x) := by
  let l : ℝ → ℝ := fun t => derivWithin f (Set.Iio t) t
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  have hmonoI : MonotoneOn l I := by
    simpa [l, hIopen.interior_eq] using hf.monotoneOn_leftDeriv
  have hsSupEq :
      derivWithin f (Set.Iio x) x = sSup (slope f x '' Set.Ioo a x) := by
    -- Restrict the global `sSup` formula for the left derivative to a small interval inside `I`.
    calc
      derivWithin f (Set.Iio x) x =
          sSup (slope f x '' {y | y ∈ I ∧ y < x}) := by
            exact hf.leftDeriv_eq_sSup_slope_of_mem_interior hxInt
      _ = sSup (slope f x '' Set.Ioo a x) := by
        symm
        apply (hf.monotoneOn_slope_lt hx).csSup_eq_of_subset_of_forall_exists_le
          (bddAbove_slope_gt_of_mem_interior hf hxInt)
        · intro y hy
          exact ⟨hIoo hy, hy.2⟩
        · rintro y ⟨hyI, hyx⟩
          obtain ⟨z, hyz, hzx⟩ := exists_between (max_lt hax hyx)
          exact ⟨z, ⟨(le_max_left _ _).trans_lt hyz, hzx⟩, (le_max_right _ _).trans hyz.le⟩
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    -- Monotonicity of the left derivative makes every strict-left value lie below the value at `x`.
    exact hmonoI (hIoo hw) hx hw.2.le
  · intro u hu
    have hslopeUpper :
        sSup (slope f x '' Set.Ioo a x) ≤ u := by
      refine csSup_le ?_ ?_
      · rw [Set.image_nonempty]
        exact Set.nonempty_Ioo.2 hax
      · rintro _ ⟨y, hy, rfl⟩
        have hyI : y ∈ I := hIoo hy
        have hcontf : ContinuousOn f I := hf.continuousOn hIopen
        have hcontSlope : ContinuousAt (fun z : ℝ => slope f y z) x := by
          -- With the left endpoint fixed, secant slopes vary continuously as the right endpoint
          -- approaches `x`.
          have hcontNum :
              ContinuousAt (fun z : ℝ => f z - f y) x :=
            (hcontf.continuousAt (hIopen.mem_nhds hx)).sub continuousAt_const
          have hcontDen :
              ContinuousAt (fun z : ℝ => z - y) x :=
            continuousAt_id.sub continuousAt_const
          have hne : x - y ≠ 0 := sub_ne_zero.mpr hy.2.ne'
          simpa [slope_def_field] using hcontNum.div hcontDen hne
        have hnebot : (𝓝[Set.Ioo y x] x).NeBot := by
          exact
            (mem_closure_iff_nhdsWithin_neBot).1 (by
              rw [closure_Ioo hy.2.ne]
              simp [hy.2.le])
        letI := hnebot
        have hmem :
            ∀ᶠ z in 𝓝[Set.Ioo y x] x, slope f y z ∈ Set.Iic u := by
          -- Every intermediate point contributes a left derivative above the secant slope from `y`.
          filter_upwards [self_mem_nhdsWithin] with z hz
          have hzIoo : z ∈ Set.Ioo a x := ⟨hy.1.trans hz.1, hz.2⟩
          have huz : derivWithin f (Set.Iio z) z ≤ u := hu ⟨z, hzIoo, rfl⟩
          have hzI : z ∈ I := hIoo hzIoo
          have hzInt : z ∈ interior I := by
            simpa [hIopen.interior_eq] using hzI
          have hsec :
              slope f y z ≤ derivWithin f (Set.Iio z) z :=
            hf.slope_le_leftDeriv_of_mem_interior hyI hzInt hz.1
          exact le_trans hsec huz
        have htarget : slope f y x ∈ Set.Iic u :=
          isClosed_Iic.mem_of_tendsto hcontSlope.continuousWithinAt.tendsto hmem
        simpa [slope_comm] using htarget
    simpa [hsSupEq] using hslopeUpper

/-- Helper for Theorem 25.3: the right-derivative selector is right-continuous at every point of
the open interval `I`. -/
lemma helperForTheorem_25_3_rightDerivWithin_rightContinuousOn_openInterval
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x : ℝ} (hx : x ∈ I) :
    Filter.Tendsto (fun t => derivWithin f (Set.Ioi t) t) (𝓝[>] x)
      (𝓝 (derivWithin f (Set.Ioi x) x)) := by
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  rcases (mem_nhds_iff_exists_Ioo_subset.mp <| mem_interior_iff_mem_nhds.mp hxInt) with
    ⟨a, b, hxab, habI⟩
  have hxbI : Set.Ioo x b ⊆ I := by
    intro t ht
    exact habI ⟨hxab.1.trans ht.1, ht.2⟩
  have hmonoLocal :
      MonotoneOn (fun t => derivWithin f (Set.Ioi t) t) (Set.Ioo x b) := by
    intro u hu v hv huv
    exact
      (by
        have hmonoI : MonotoneOn (fun t => derivWithin f (Set.Ioi t) t) I := by
          simpa [hIopen.interior_eq] using hf.monotoneOn_rightDeriv
        exact hmonoI (hxbI hu) (hxbI hv) huv)
  have htail :
      IsGLB ((fun t => derivWithin f (Set.Ioi t) t) '' Set.Ioo x b)
        (derivWithin f (Set.Ioi x) x) :=
    helperForTheorem_25_3_rightDerivWithin_isGLB_on_Ioo hIopen hf hx hxab.2 hxbI
  have hlimit :
      Filter.Tendsto (fun t => derivWithin f (Set.Ioi t) t) (𝓝[>] x)
        (𝓝 (sInf ((fun t => derivWithin f (Set.Ioi t) t) '' Set.Ioo x b))) := by
    exact
      MonotoneOn.tendsto_nhdsWithin_Ioo_right
        (Set.nonempty_Ioo.2 hxab.2) hmonoLocal
        (by exact ⟨derivWithin f (Set.Ioi x) x, htail.1⟩)
  have hsInf :
      sInf ((fun t => derivWithin f (Set.Ioi t) t) '' Set.Ioo x b) =
        derivWithin f (Set.Ioi x) x := by
    exact htail.csInf_eq (by
      rw [Set.image_nonempty]
      exact Set.nonempty_Ioo.2 hxab.2)
  -- The local strict-right tail already has `g x` as its infimum, so the monotone right-limit
  -- theorem gives the desired self-limit.
  simpa [nhdsWithin_Ioo_eq_nhdsGT hxab.2, hsInf] using hlimit

/-- Helper for Theorem 25.3: the left-derivative selector is left-continuous at every point of
the open interval `I`. -/
lemma helperForTheorem_25_3_leftDerivWithin_leftContinuousOn_openInterval
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x : ℝ} (hx : x ∈ I) :
    Filter.Tendsto (fun t => derivWithin f (Set.Iio t) t) (𝓝[<] x)
      (𝓝 (derivWithin f (Set.Iio x) x)) := by
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  rcases (mem_nhds_iff_exists_Ioo_subset.mp <| mem_interior_iff_mem_nhds.mp hxInt) with
    ⟨a, b, hxab, habI⟩
  have haxI : Set.Ioo a x ⊆ I := by
    intro t ht
    exact habI ⟨ht.1, ht.2.trans hxab.2⟩
  have hmonoLocal :
      MonotoneOn (fun t => derivWithin f (Set.Iio t) t) (Set.Ioo a x) := by
    intro u hu v hv huv
    exact
      (by
        have hmonoI : MonotoneOn (fun t => derivWithin f (Set.Iio t) t) I := by
          simpa [hIopen.interior_eq] using hf.monotoneOn_leftDeriv
        exact hmonoI (haxI hu) (haxI hv) huv)
  have htail :
      IsLUB ((fun t => derivWithin f (Set.Iio t) t) '' Set.Ioo a x)
        (derivWithin f (Set.Iio x) x) :=
    helperForTheorem_25_3_leftDerivWithin_isLUB_on_Ioo hIopen hf hx hxab.1 haxI
  have hlimit :
      Filter.Tendsto (fun t => derivWithin f (Set.Iio t) t) (𝓝[<] x)
        (𝓝 (sSup ((fun t => derivWithin f (Set.Iio t) t) '' Set.Ioo a x))) := by
    exact
      MonotoneOn.tendsto_nhdsWithin_Ioo_left
        (Set.nonempty_Ioo.2 hxab.1) hmonoLocal
        (by exact ⟨derivWithin f (Set.Iio x) x, htail.1⟩)
  have hsSup :
      sSup ((fun t => derivWithin f (Set.Iio t) t) '' Set.Ioo a x) =
        derivWithin f (Set.Iio x) x := by
    exact htail.csSup_eq (by
      rw [Set.image_nonempty]
      exact Set.nonempty_Ioo.2 hxab.1)
  -- The local strict-left tail already has `l x` as its supremum, so the monotone left-limit
  -- theorem gives the desired self-limit.
  simpa [nhdsWithin_Ioo_eq_nhdsLT hxab.1, hsSup] using hlimit

/-- Helper for Theorem 25.3: on the differentiability set `D`, the derivative is continuous within
`D` at each point because its left and right restrictions agree with the corresponding one-sided
derivative selectors. -/
lemma helperForTheorem_25_3_deriv_continuousWithinAt_on_D
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) :
    let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt f (deriv f x) x}
    ∀ {x : ℝ}, x ∈ D → ContinuousWithinAt (deriv f) D x := by
  intro D x hxD
  have hEqOn :
      Set.EqOn (deriv f) (fun t => derivWithin f (Set.Ioi t) t) D ∧
        Set.EqOn (deriv f) (fun t => derivWithin f (Set.Iio t) t) D := by
    simpa [D] using helperForTheorem_25_3_deriv_eq_oneSidedDerivWithin_on_D (I := I) (f := f)
  have hrightSelector :
      Filter.Tendsto (fun t => derivWithin f (Set.Ioi t) t) (𝓝[D ∩ Set.Ioi x] x)
        (𝓝 (derivWithin f (Set.Ioi x) x)) := by
    -- Restrict the right self-limit of the selector to the finer filter carried by `D`.
    exact
      tendsto_nhdsWithin_mono_left (by
        intro t ht
        exact ht.2)
        (helperForTheorem_25_3_rightDerivWithin_rightContinuousOn_openInterval hIopen hf hxD.1)
  have hleftSelector :
      Filter.Tendsto (fun t => derivWithin f (Set.Iio t) t) (𝓝[D ∩ Set.Iio x] x)
        (𝓝 (derivWithin f (Set.Iio x) x)) := by
    -- Restrict the left self-limit of the selector to the finer filter carried by `D`.
    exact
      tendsto_nhdsWithin_mono_left (by
        intro t ht
        exact ht.2)
        (helperForTheorem_25_3_leftDerivWithin_leftContinuousOn_openInterval hIopen hf hxD.1)
  have hrightEventually :
      (fun t => deriv f t) =ᶠ[𝓝[D ∩ Set.Ioi x] x] fun t => derivWithin f (Set.Ioi t) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hEqOn.1 ht.1
  have hleftEventually :
      (fun t => deriv f t) =ᶠ[𝓝[D ∩ Set.Iio x] x] fun t => derivWithin f (Set.Iio t) t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hEqOn.2 ht.1
  have hright :
      Filter.Tendsto (deriv f) (𝓝[D ∩ Set.Ioi x] x) (𝓝 (deriv f x)) := by
    -- Rewrite the right-hand restriction of `deriv` to the right selector and evaluate at `x`.
    simpa [hEqOn.1 hxD] using hrightSelector.congr' hrightEventually.symm
  have hleft :
      Filter.Tendsto (deriv f) (𝓝[D ∩ Set.Iio x] x) (𝓝 (deriv f x)) := by
    -- Rewrite the left-hand restriction of `deriv` to the left selector and evaluate at `x`.
    simpa [hEqOn.2 hxD] using hleftSelector.congr' hleftEventually.symm
  -- Combining the left and right restrictions yields continuity within `D`.
  exact (continuousWithinAt_iff_continuous_left'_right').2 ⟨hleft, hright⟩

/-- Helper for Theorem 25.3: if the exceptional set `I \ D` is countable, then `D` is dense in
the open interval `I`. -/
lemma helperForTheorem_25_3_subset_closure_of_countable_diff
    {I D : Set ℝ} (hIopen : IsOpen I) (hcount : Set.Countable (I \ D)) :
    I ⊆ closure D := by
  have hdenseCompl : Dense ((I \ D)ᶜ) := hcount.dense_compl ℝ
  intro x hxI
  rw [mem_closure_iff]
  intro U hU hxU
  have hUIne : (U ∩ I).Nonempty := ⟨x, hxU, hxI⟩
  -- A dense complement point in `U ∩ I` cannot lie in `I \ D`, so it belongs to `D`.
  rcases hdenseCompl.inter_open_nonempty (U ∩ I) (hU.inter hIopen) hUIne with
    ⟨y, hy⟩
  have hyI : y ∈ I := hy.1.2
  have hyNotMem : y ∉ I \ D := hy.2
  refine ⟨y, hy.1.1, ?_⟩
  by_contra hyD
  exact hyNotMem ⟨hyI, hyD⟩

/-- Theorem 25.3: if `f` is a finite convex function on an open interval `I ⊆ ℝ`, and
`D = {x ∈ I | f' x exists}`, then `I \ D` is countable, `D` is dense in `I`, and the derivative
function `f'`, represented in Lean by `deriv f`, is continuous and nondecreasing on `D`. -/
theorem convexOn_openInterval_countable_nondifferentiabilitySet_dense_and_deriv_continuousOn_monotoneOn
    {I : Set ℝ} (hIopen : IsOpen I) (hIconv : Convex ℝ I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) :
    let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt f (deriv f x) x}
    Set.Countable (I \ D) ∧
      I ⊆ closure D ∧
      ContinuousOn (deriv f) D ∧
      MonotoneOn (deriv f) D := by
  let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt f (deriv f x) x}
  let g : ℝ → ℝ := fun x => derivWithin f (Set.Ioi x) x
  have hmonoI : MonotoneOn g I := by
    simpa [g, hIopen.interior_eq] using hf.monotoneOn_rightDeriv
  have hcountDisc :
      Set.Countable {x ∈ I | ¬ ContinuousWithinAt g I x} :=
    hmonoI.countable_not_continuousWithinAt
  have hsubset :
      I \ D ⊆ {x ∈ I | ¬ ContinuousWithinAt g I x} := by
    -- Nondifferentiability forces a jump in the right-derivative selector.
    simpa [D, g] using
      helperForTheorem_25_3_nondiff_subset_rightDeriv_discontinuitySet
        hIopen hf
  have hcount : Set.Countable (I \ D) :=
    hcountDisc.mono hsubset
  have hclosure : I ⊆ closure D := by
    -- Density of `D` follows from the countability of its exceptional complement inside `I`.
    exact helperForTheorem_25_3_subset_closure_of_countable_diff hIopen hcount
  have hEqOn :
      Set.EqOn (deriv f) (fun x => derivWithin f (Set.Ioi x) x) D ∧
        Set.EqOn (deriv f) (fun x => derivWithin f (Set.Iio x) x) D := by
    simpa [D] using helperForTheorem_25_3_deriv_eq_oneSidedDerivWithin_on_D (I := I) (f := f)
  have hmonoDeriv : MonotoneOn (deriv f) D := by
    intro x hx y hy hxy
    -- On `D`, the ordinary derivative is the right derivative selector, which is monotone on `I`.
    rw [hEqOn.1 hx, hEqOn.1 hy]
    exact hmonoI hx.1 hy.1 hxy
  have hcontDeriv : ContinuousOn (deriv f) D := by
    intro x hx
    -- On `D`, relative continuity comes from the left/right self-limits of the one-sided selectors.
    simpa [D] using
      (helperForTheorem_25_3_deriv_continuousWithinAt_on_D
        (I := I) hIopen hf (x := x) hx)
  refine ⟨hcount, hclosure, ?_, hmonoDeriv⟩
  exact hcontDeriv

-- Proof sketch: for `x ∈ interior (dom f)`, membership in the effective domain makes `f x`
-- finite. Apply the bilateral directional-derivative criterion from Section 23 at such `x` to
-- identify existence of the ordinary two-sided directional derivative along `y` with the equality
-- `f'(x; y) = -f'(x; -y)`, then rewrite this pointwise equivalence as a characterization of `D`.
/-- Helper for Theorem 25.4: an interior point of the effective domain is a finite-value point of
`f`. -/
lemma helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    interior_subset hx
  refine ⟨?_, ?_⟩
  · -- Effective-domain membership rules out the value `⊤`.
    exact
      mem_effectiveDomain_imp_ne_top
        (S := (Set.univ : Set (Fin n → Real))) (f := f) hxDom
  · -- Properness rules out the value `⊥` everywhere on `Set.univ`.
    exact hproper.2.2 x (by simp)

/-- Helper for Theorem 25.4: equality of the opposite one-sided directional derivatives upgrades
to existence of the ordinary bilateral directional derivative. -/
lemma helperForTheorem_25_4_bilateral_of_eq_neg_upperDirectionalDerivative
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {x y : Fin n → Real} (hx : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hEq : upperDirectionalDerivativeAt f x y = -upperDirectionalDerivativeAt f x (-y)) :
    HasBilateralDirectionalDerivativeAt f x y := by
  have hright :
      Filter.Tendsto (directionalDifferenceQuotientAt f x y)
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x y)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 y |>.2.1
  have hrightNeg :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (-y))
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x (-y))) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 (-y) |>.2.1
  have hEqNeg :
      upperDirectionalDerivativeAt f x (-y) = -upperDirectionalDerivativeAt f x y := by
    have hneg :
        -(upperDirectionalDerivativeAt f x y) =
          upperDirectionalDerivativeAt f x (-y) := by
      simpa using congrArg Neg.neg hEq
    exact hneg.symm
  -- The bilateral criterion from Section 23 packages the two right-hand ray limits.
  refine ((bilateralDirectionalDerivative_iff_exists_neg_direction
      (f := f) (x := x) (y := y) hx).2).2 ?_
  refine ⟨upperDirectionalDerivativeAt f x y, hright, ?_⟩
  -- Rewrite the right-ray limit along `-y` using the assumed symmetry relation.
  simpa [hEqNeg] using hrightNeg

/-- Helper for Theorem 25.4: a bilateral directional derivative forces the opposite one-sided
directional derivatives to be negatives of each other. -/
lemma helperForTheorem_25_4_eq_neg_upperDirectionalDerivative_of_bilateral
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f)
    {x y : Fin n → Real} (hx : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hbilat : HasBilateralDirectionalDerivativeAt f x y) :
    upperDirectionalDerivativeAt f x y = -upperDirectionalDerivativeAt f x (-y) := by
  have hright :
      Filter.Tendsto (directionalDifferenceQuotientAt f x y)
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x y)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 y |>.2.1
  have hrightNeg :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (-y))
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x (-y))) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 (-y) |>.2.1
  rcases
      ((bilateralDirectionalDerivative_iff_exists_neg_direction
        (f := f) (x := x) (y := y) hx).2).1 hbilat with
    ⟨L, hrightY, hrightNegY⟩
  have hLy : upperDirectionalDerivativeAt f x y = L :=
    -- The bilateral witness agrees with the canonical right-hand limit along `y`.
    tendsto_nhds_unique hright hrightY
  have hnegLy : upperDirectionalDerivativeAt f x (-y) = -L :=
    -- The right-hand limit along `-y` identifies the opposite directional derivative.
    tendsto_nhds_unique hrightNeg hrightNegY
  -- Substitute the identified witness into the claimed symmetry relation.
  calc
    upperDirectionalDerivativeAt f x y = L := hLy
    _ = -upperDirectionalDerivativeAt f x (-y) := by
      rw [hnegLy]
      simp

/-- Helper for Theorem 25.4: at an interior point of the effective domain, the symmetry of the
opposite upper directional derivatives is equivalent to existence of the ordinary bilateral
directional derivative. -/
lemma helperForTheorem_25_4_pointwiseCriterion
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x y : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    upperDirectionalDerivativeAt f x y = -upperDirectionalDerivativeAt f x (-y) ↔
      HasBilateralDirectionalDerivativeAt f x y := by
  have hf : ConvexFunction f := by
    -- Proper convexity on the whole space gives the convexity input needed for the Section 23
    -- directional-derivative criterion.
    simpa [ConvexFunction] using hproper.1
  have hxFinite :
      f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
      (f := f) hproper hx
  constructor
  · intro hEq
    -- Symmetry of the opposite one-sided directional derivatives yields the bilateral derivative.
    exact
      helperForTheorem_25_4_bilateral_of_eq_neg_upperDirectionalDerivative
        (f := f) hf hxFinite hEq
  · intro hbilat
    -- Conversely, the bilateral derivative identifies the two one-sided limits as negatives.
    exact
      helperForTheorem_25_4_eq_neg_upperDirectionalDerivative_of_bilateral
        (f := f) hf hxFinite hbilat

/-- Theorem 25.4: let `f` be a proper convex function on `ℝ^n`, fix a nonzero direction `y`, and
let
`D = {x ∈ int (dom f) | lim_{λ → 0} (f (x + λ y) - f x) / λ exists}`.
Equivalently, by the bilateral directional-derivative criterion from Section 23, `D` is the set
of interior points where `f'(x; y) = -f'(x; -y)`. -/
theorem properConvex_fixedDirection_mem_bilateralDirectionalDerivativeSet_iff
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (y : Fin n → Real) (hy : y ≠ 0) :
    let D : Set (Fin n → Real) :=
      {x |
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
          upperDirectionalDerivativeAt f x y = -upperDirectionalDerivativeAt f x (-y)}
    ∀ x : Fin n → Real,
      x ∈ D ↔
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
          HasBilateralDirectionalDerivativeAt f x y := by
  have _ : y ≠ 0 := hy
  intro D x
  constructor
  · rintro ⟨hxInt, hEq⟩
    refine ⟨hxInt, ?_⟩
    -- Apply the pointwise directional-derivative criterion at the chosen interior point.
    exact
      (helperForTheorem_25_4_pointwiseCriterion
        (f := f) hproper (x := x) (y := y) hxInt).1 hEq
  · rintro ⟨hxInt, hbilat⟩
    refine ⟨hxInt, ?_⟩
    -- Reuse the same pointwise criterion in the reverse direction.
    exact
      (helperForTheorem_25_4_pointwiseCriterion
        (f := f) hproper (x := x) (y := y) hxInt).2 hbilat

-- Proof sketch: apply Theorem 25.4 in each nonzero direction and Fubini-type differentiation
-- arguments to show that along almost every line through an interior point the directional
-- derivative exists, giving a null exceptional set. Then combine the one-dimensional continuity of
-- monotone derivatives with Theorem 25.2 to identify differentiability points, and use uniqueness
-- of the convex subgradient to prove the chosen gradient varies continuously on the
-- differentiability locus.
/-- Helper for Theorem 25.5: the differentiability set is exactly the intersection of the
coordinate-partial sets from the textbook proof. -/
lemma helperForTheorem_25_5_differentiabilitySet_eq_iInter_coordinatePartialSets
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt f x}
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    D = ⋂ j, Dj j := by
  intro U D Dj
  ext x
  constructor
  · intro hxD
    have hpartials :
        ∀ j : Fin n,
          HasCoordinatePartialDerivativeAt f x j ((((erealGradientAt hxD.2) j : Real) : EReal)) :=
      (ERealDifferentiableAt.coordinatePartials_and_directionalDerivative_formula hxD.2).1
    -- Differentiability gives every coordinate partial derivative with the corresponding
    -- gradient coordinate as its value.
    refine Set.mem_iInter.2 ?_
    intro j
    exact ⟨hxD.1, (erealGradientAt hxD.2) j, hpartials j⟩
  · by_cases hn : n = 0
    · subst hn
      intro _hxInter
      have hDomAll :
          effectiveDomain (Set.univ : Set (Fin 0 → Real)) f = Set.univ := by
        ext y
        constructor
        · intro _hy
          simp
        · intro _hy
          obtain ⟨y0, r0, hy0⟩ :=
            properConvexFunctionOn_exists_finite_point (n := 0) (f := f) hproper
          have hyEq : y = y0 := Subsingleton.elim _ _
          have hfy : f y = (r0 : EReal) := by
            simpa [hyEq] using hy0
          by_contra hyNotDom
          have hyTop :
              f y = (⊤ : EReal) :=
            not_mem_effectiveDomain_univ_imp_eq_top (f := f) hyNotDom
          rw [hfy] at hyTop
          simp at hyTop
      have hUall :
          U = Set.univ := by
        -- Once the effective domain is all of the zero-dimensional space, its interior is also
        -- all of space.
        simp [U, hDomAll]
      have hf : ConvexFunction f := by
        simpa [ConvexFunction] using hproper.1
      have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
        obtain ⟨x0, r0, hx0⟩ :=
          properConvexFunctionOn_exists_finite_point (n := 0) (f := f) hproper
        have hxEq : x = x0 := Subsingleton.elim _ _
        have hfx : f x = (r0 : EReal) := by
          simpa [hxEq] using hx0
        constructor
        · rw [hfx]
          simp
        · exact hproper.2.2 x (by simp)
      have hpartials :
          ∀ j : Fin 0, ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal) := by
        intro j
        exact Fin.elim0 j
      have hcore :=
        convexFunction_differentiableAt_iff_directionalDerivativeHasGradient_and_coordinatePartials_imply_linearity
          (f := f) hf x hxFinite
      have hlin :
          ∃ g : Fin 0 → Real,
            ∀ y : Fin 0 → Real,
              upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal) :=
        hcore.2 hpartials
      have hdiff : ERealDifferentiableAt f x := hcore.1.2 hlin
      -- The zero-dimensional case is vacuous for coordinates, so differentiability follows from
      -- the vacuous coordinate-partial hypothesis once `x` is known to lie in `U = univ`.
      exact ⟨by simpa [hUall], hdiff⟩
    · intro hxInter
      let j0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
      have hxj0 : x ∈ Dj j0 := Set.mem_iInter.1 hxInter j0
      have hxU : x ∈ U := hxj0.1
      have hf : ConvexFunction f := by
        simpa [ConvexFunction] using hproper.1
      have hxFinite :
          f x ≠ ⊤ ∧ f x ≠ ⊥ :=
        helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
          (f := f) hproper hxU
      have hpartials :
          ∀ j : Fin n, ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal) := by
        intro j
        exact (Set.mem_iInter.1 hxInter j).2
      have hcore :=
        convexFunction_differentiableAt_iff_directionalDerivativeHasGradient_and_coordinatePartials_imply_linearity
          (f := f) hf x hxFinite
      have hlin :
          ∃ g : Fin n → Real,
            ∀ y : Fin n → Real,
              upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal) :=
        hcore.2 hpartials
      have hdiff : ERealDifferentiableAt f x := hcore.1.2 hlin
      -- Theorem 25.2 upgrades existence of all finite coordinate partials to differentiability.
      exact ⟨hxU, hdiff⟩

/-- Helper for Theorem 25.5: the dense/null part reduces to the one-dimensional slice analysis
from the textbook route. -/
lemma helperForTheorem_25_5_mem_coordinatePartialSet_of_lineDifferentiableClosure
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {V : Set (Fin n → Real)} (hVopen : IsOpen V)
    (hVsub : V ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    {x : Fin n → Real} (hxV : x ∈ V) (j : Fin n)
    (hline :
      LineDifferentiableAt ℝ (fun z : Fin n → Real => (convexFunctionClosure f z).toReal) x
        (Pi.single j (1 : Real))) :
    x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) ∧
      ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal) := by
  let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  let g : (Fin n → Real) → Real := fun z => (convexFunctionClosure f z).toReal
  let e : Fin n → Real := Pi.single j (1 : Real)
  let L : Real := lineDeriv ℝ g x e
  have hxU : x ∈ U := hVsub hxV
  have hxFinite :
      f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
      (f := f) hproper hxU
  have hclx : convexFunctionClosure f x = f x :=
    helperForCorollary_25_1_1_1_closure_eq_at_interior_point
      (f := f) hproper hxU
  have hlineDeriv : HasLineDerivAt ℝ g L x e := hline.hasLineDerivAt
  have hEventuallyV :
      ∀ᶠ t : Real in 𝓝 (0 : Real), x + t • e ∈ V := by
    -- The open neighborhood `V` controls a full two-sided ray around `x`.
    have hcont : ContinuousAt (fun t : Real => x + t • e) (0 : Real) := by
      fun_prop
    exact hcont.tendsto.eventually (hVopen.mem_nhds (by simpa [e] using hxV))
  refine ⟨hxU, L, ?_⟩
  constructor
  · have hrightReal :
        Filter.Tendsto (fun t : Real => t⁻¹ * (g (x + t • e) - g x))
          (𝓝[>] (0 : Real)) (𝓝 L) := by
      -- The right scalar slope is exactly the line derivative of the real-valued closure.
      simpa [g, e, L, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hlineDeriv.tendsto_slope_zero_right
    have hrightCoe :
        Filter.Tendsto
          (fun t : Real => (((t⁻¹ * (g (x + t • e) - g x) : Real) : Real) : EReal))
          (𝓝[>] (0 : Real)) (𝓝 ((L : Real) : EReal)) :=
      (EReal.tendsto_coe).2 hrightReal
    have hquotEq :
        ∀ᶠ t : Real in 𝓝[>] (0 : Real),
          directionalDifferenceQuotientAt f x e t =
            (((t⁻¹ * (g (x + t • e) - g x) : Real) : Real) : EReal) := by
      filter_upwards [self_mem_nhdsWithin, hEventuallyV.filter_mono nhdsWithin_le_nhds] with
        t ht htV
      have htne : t ≠ 0 := ne_of_gt ht
      have hxt : x + t • e ∈ U := hVsub htV
      have hxtFinite :
          f (x + t • e) ≠ ⊤ ∧ f (x + t • e) ≠ ⊥ :=
        helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
          (f := f) hproper hxt
      have hclxt :
          convexFunctionClosure f (x + t • e) = f (x + t • e) :=
        helperForCorollary_25_1_1_1_closure_eq_at_interior_point
          (f := f) hproper hxt
      -- Inside `V`, the closure agrees with `f`, so the `EReal` quotient is just the coerced
      -- real slope of the closure.
      rw [directionalDifferenceQuotientAt]
      simp [g, hclx, hclxt, EReal.coe_mul, EReal.coe_sub, EReal.coe_inv,
        EReal.coe_toReal hxFinite.1 hxFinite.2,
        EReal.coe_toReal hxtFinite.1 hxtFinite.2, div_eq_mul_inv, mul_comm]
    exact Filter.Tendsto.congr' (by
      filter_upwards [hquotEq] with t htEq
      exact htEq.symm) hrightCoe
  · have hleftReal :
        Filter.Tendsto (fun t : Real => t⁻¹ * (g (x + t • e) - g x))
          (𝓝[<] (0 : Real)) (𝓝 L) := by
      -- The same scalar slope converges from the left because the line derivative is two-sided.
      simpa [g, e, L, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
        hlineDeriv.tendsto_slope_zero_left
    have hleftCoe :
        Filter.Tendsto
          (fun t : Real => (((t⁻¹ * (g (x + t • e) - g x) : Real) : Real) : EReal))
          (𝓝[<] (0 : Real)) (𝓝 ((L : Real) : EReal)) :=
      (EReal.tendsto_coe).2 hleftReal
    have hquotEq :
        ∀ᶠ t : Real in 𝓝[<] (0 : Real),
          directionalDifferenceQuotientAt f x e t =
            (((t⁻¹ * (g (x + t • e) - g x) : Real) : Real) : EReal) := by
      filter_upwards [self_mem_nhdsWithin, hEventuallyV.filter_mono nhdsWithin_le_nhds] with
        t ht htV
      have htne : t ≠ 0 := ne_of_lt ht
      have hxt : x + t • e ∈ U := hVsub htV
      have hxtFinite :
          f (x + t • e) ≠ ⊤ ∧ f (x + t • e) ≠ ⊥ :=
        helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
          (f := f) hproper hxt
      have hclxt :
          convexFunctionClosure f (x + t • e) = f (x + t • e) :=
        helperForCorollary_25_1_1_1_closure_eq_at_interior_point
          (f := f) hproper hxt
      -- The left ray stays inside the same neighborhood, so the same quotient rewrite applies.
      rw [directionalDifferenceQuotientAt]
      simp [g, hclx, hclxt, EReal.coe_mul, EReal.coe_sub, EReal.coe_inv,
        EReal.coe_toReal hxFinite.1 hxFinite.2,
        EReal.coe_toReal hxtFinite.1 hxtFinite.2, div_eq_mul_inv, mul_comm]
    exact Filter.Tendsto.congr' (by
      filter_upwards [hquotEq] with t htEq
      exact htEq.symm) hleftCoe

/-- Helper for Theorem 25.5: on a small ball contained in `int (dom f)`, the failure of the
`j`th coordinate partial derivative is a null set because the real-valued closure is locally
Lipschitz and hence almost everywhere line-differentiable in the `e_j` direction. -/
lemma helperForTheorem_25_5_coordinatePartialSet_null_on_ball
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (j : Fin n) {c : Fin n → Real} {r : Real} (hr : 0 < r)
    (hclosedSub :
      Metric.closedBall c (2 * r) ⊆
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    MeasureTheory.volume (Metric.ball c r \ Dj j) = 0 := by
  classical
  intro U Dj
  let g : (Fin n → Real) → Real := fun z => (convexFunctionClosure f z).toReal
  let e : Fin n → Real := Pi.single j (1 : Real)
  let S : Set (Fin n → Real) := Metric.closedBall c (2 * r)
  have hclosurePack :
      ClosedConvexFunction (convexFunctionClosure f) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := f) hproper).1
  have hSnonempty : S.Nonempty := by
    refine ⟨c, ?_⟩
    simp [S, hr.le]
  have hUsubClosureDom :
      U ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)) := by
    intro x hxU
    have hxFinite :
        f x ≠ ⊤ ∧ f x ≠ ⊥ :=
      helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
        (f := f) hproper hxU
    have hclx :
        convexFunctionClosure f x = f x :=
      helperForCorollary_25_1_1_1_closure_eq_at_interior_point
        (f := f) hproper hxU
    have hUsubDom :
        U ⊆ effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) := by
      intro y hy
      have hyFinite :
          f y ≠ ⊤ ∧ f y ≠ ⊥ :=
        helperForTheorem_25_4_finiteAt_of_mem_interior_effectiveDomain
          (f := f) hproper hy
      have hcly :
          convexFunctionClosure f y = f y :=
        helperForCorollary_25_1_1_1_closure_eq_at_interior_point
          (f := f) hproper hy
      simpa [effectiveDomain_eq, lt_top_iff_ne_top, hcly] using hyFinite.1
    exact mem_interior_iff_mem_nhds.2 <|
      Filter.mem_of_superset (isOpen_interior.mem_nhds hxU) hUsubDom
  have hSLipPack :=
    closedProperConvex_subdifferentialImageOn_nonempty_closed_bounded_and_lipschitzOn
      (f := convexFunctionClosure f) hclosurePack.1 hclosurePack.2 hSnonempty
      Metric.isClosed_closedBall (isCompact_closedBall c (2 * r)).isBounded
      (fun x hx => hUsubClosureDom (hclosedSub hx))
  let α : Real :=
    sSup ((fun xStar : Fin n → Real => euclideanNorm xStar) ''
      subdifferentialImageOn (convexFunctionClosure f) S)
  have hSLipEuclid :
      ∀ x ∈ S, ∀ y ∈ S, |g y - g x| ≤ α * euclideanNorm (y - x) := by
    -- The Chapter 24 Lipschitz bound is stated in the book's Euclidean norm.
    simpa [g, S, α] using hSLipPack.2.2.2.2
  have hBallSubS : Metric.ball c r ⊆ S := by
    intro x hx
    have hxle : dist x c ≤ 2 * r := by
      linarith [show dist x c < r from hx]
    simpa [S] using hxle
  have hBallLip :
      LipschitzOnWith
        ⟨max α 0 * Real.sqrt (n : Real),
          mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)⟩ g (Metric.ball c r) := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hxS : x ∈ S := hBallSubS hx
    have hyS : y ∈ S := hBallSubS hy
    have hEuclidToSup :
        euclideanNorm (y - x) ≤ Real.sqrt (n : Real) * ‖y - x‖ := by
      simpa [euclideanNorm] using
        (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm (n := n) (y - x)).2
    have hEuclidNonneg : 0 ≤ euclideanNorm (y - x) := by
      simp [euclideanNorm]
    have hxy :
        dist (g x) (g y) ≤ (max α 0 * Real.sqrt (n : Real)) * dist x y := by
      calc
        dist (g x) (g y) = |g y - g x| := by rw [Real.dist_eq, abs_sub_comm]
        _ ≤ α * euclideanNorm (y - x) := hSLipEuclid x hxS y hyS
        _ ≤ max α 0 * euclideanNorm (y - x) := by
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hEuclidNonneg
        _ ≤ max α 0 * (Real.sqrt (n : Real) * ‖y - x‖) := by
          exact mul_le_mul_of_nonneg_left hEuclidToSup (by positivity)
        _ = (max α 0 * Real.sqrt (n : Real)) * ‖y - x‖ := by ring
        _ = (max α 0 * Real.sqrt (n : Real)) * dist x y := by rw [dist_eq_norm, norm_sub_rev]
    simpa using hxy
  obtain ⟨gExt, hgExtLip, hgExtEq⟩ := hBallLip.extend_real
  have hgoodAE :
      ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Real)),
        LineDifferentiableAt ℝ gExt x e :=
    hgExtLip.ae_lineDifferentiableAt e
  have hbadMeas :
      MeasurableSet {x : Fin n → Real | ¬ LineDifferentiableAt ℝ gExt x e} :=
    (measurableSet_lineDifferentiableAt hgExtLip.continuous).compl
  have hbadNull :
      MeasureTheory.volume {x : Fin n → Real | ¬ LineDifferentiableAt ℝ gExt x e} = 0 := by
    rw [MeasureTheory.ae_iff] at hgoodAE
    simpa [hbadMeas] using hgoodAE
  have hsubsetBad :
      Metric.ball c r \ Dj j ⊆ {x : Fin n → Real | ¬ LineDifferentiableAt ℝ gExt x e} := by
    intro x hx
    by_contra hxGood
    have hxEqNhds :
        (fun z : Fin n → Real => (convexFunctionClosure f z).toReal) =ᶠ[𝓝 x] gExt := by
      -- Inside the open ball, the global Lipschitz extension agrees with the original closure.
      filter_upwards [Metric.isOpen_ball.mem_nhds hx.1] with z hz
      exact hgExtEq hz
    have hxGoodClosure :
        LineDifferentiableAt ℝ g x e :=
      (LineDifferentiableAt.congr_of_eventuallyEq (f := gExt) (f₁ := g) (x := x) (v := e)
        (by simpa using hxGood) hxEqNhds)
    have hxDj :
        x ∈ Dj j := by
      -- Route correction: use local Lipschitz + ambient line differentiability instead of the
      -- earlier slice/Fubini decomposition to produce the coordinate partial.
      exact
        helperForTheorem_25_5_mem_coordinatePartialSet_of_lineDifferentiableClosure
          (f := f) hproper Metric.isOpen_ball (fun z hz => hclosedSub (hBallSubS hz)) hx.1 j
          (by simpa [g, e] using hxGoodClosure)
    exact hx.2 hxDj
  exact MeasureTheory.measure_mono_null hsubsetBad hbadNull

/-- Helper for Theorem 25.5: each coordinate-partial exceptional set in `U` has measure zero by
covering `U` with countably many small balls whose doubled closed balls stay inside `U`, and then
applying the local nullity lemma on each ball. -/
lemma helperForTheorem_25_5_coordinatePartialSet_nullComplement
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (j : Fin n) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let Dj : Fin n → Set (Fin n → Real) :=
      fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
    MeasureTheory.volume (U \ Dj j) = 0 := by
  classical
  intro U Dj
  let centers : Nat → Fin n → Real := TopologicalSpace.denseSeq (Fin n → Real)
  let A : Nat × Nat → Set (Fin n → Real) := fun p =>
    let c := centers p.1
    let r : Real := 1 / (p.2 + 1 : Real)
    if Metric.closedBall c (2 * r) ⊆ U then Metric.ball c r else ∅
  have hcover : U ⊆ ⋃ p : Nat × Nat, A p := by
    intro x hxU
    rcases helperForTheorem_25_1_exists_closedBall_subset_of_isOpen
        (n := n) (C := U) isOpen_interior hxU with ⟨R, hRpos, hRsub⟩
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < R / 4 by linarith)
    have hr0 : 0 < (1 / (m + 1 : Real)) := by positivity
    obtain ⟨k, hk⟩ :=
      (TopologicalSpace.denseRange_denseSeq (α := Fin n → Real)).exists_dist_lt
        (x := x) (ε := 1 / (m + 1 : Real)) hr0
    let c : Fin n → Real := centers k
    let r : Real := 1 / (m + 1 : Real)
    have hrpos : 0 < r := by positivity
    have hxBall : x ∈ Metric.ball c r := by
      simpa [Metric.mem_ball, centers, c, r, dist_comm] using hk
    have hclosedSub :
        Metric.closedBall c (2 * r) ⊆ U := by
      intro z hz
      have hzx : dist z x < R := by
        have hzc : dist z c ≤ 2 * r := by simpa [c, r] using hz
        have hcx : dist c x < r := by
          simpa [centers, c, r, dist_comm] using hk
        have : dist z x ≤ dist z c + dist c x := dist_triangle _ _ _
        linarith
      exact hRsub (by simpa using le_of_lt hzx)
    refine Set.mem_iUnion.2 ⟨(k, m), ?_⟩
    -- The chosen dense center gives a covering ball whose doubled closed ball still stays in `U`.
    change x ∈ (if Metric.closedBall c (2 * r) ⊆ U then Metric.ball c r else ∅)
    simp [hclosedSub, hxBall]
  have hsubset :
      U \ Dj j ⊆ ⋃ p : Nat × Nat, A p \ Dj j := by
    intro x hx
    rcases Set.mem_iUnion.1 (hcover hx.1) with ⟨p, hp⟩
    exact Set.mem_iUnion.2 ⟨p, ⟨hp, hx.2⟩⟩
  have hnullA :
      ∀ p : Nat × Nat, MeasureTheory.volume (A p \ Dj j) = 0 := by
    intro p
    let c : Fin n → Real := centers p.1
    let r : Real := 1 / (p.2 + 1 : Real)
    by_cases hA : Metric.closedBall c (2 * r) ⊆ U
    · have hr : 0 < r := by positivity
      -- On active covering balls, the local Lipschitz/line-differentiability lemma gives nullity.
      change MeasureTheory.volume
          ((if Metric.closedBall c (2 * r) ⊆ U then Metric.ball c r else ∅) \ Dj j) = 0
      simp [hA]
      simpa [U, Dj] using
        helperForTheorem_25_5_coordinatePartialSet_null_on_ball
          (f := f) hproper j hr hA
    · change MeasureTheory.volume
          ((if Metric.closedBall c (2 * r) ⊆ U then Metric.ball c r else ∅) \ Dj j) = 0
      simp [hA]
  have hnullUnion :
      MeasureTheory.volume (⋃ p : Nat × Nat, A p \ Dj j) = 0 :=
    MeasureTheory.measure_iUnion_null hnullA
  exact MeasureTheory.measure_mono_null hsubset hnullUnion

/-- Helper for Theorem 25.5: the dense/null part reduces to the one-dimensional slice analysis
from the textbook route. -/
lemma helperForTheorem_25_5_dense_of_null_complement_in_open
    {n : Nat} {U A : Set (Fin n → Real)} (hUopen : IsOpen U) (hAU : A ⊆ U)
    (hnull : MeasureTheory.volume (U \ A) = 0) :
    U ⊆ closure A := by
  intro x hxU
  have hAlmostEverywhere :
      ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Real)), y ∉ U \ A := by
    rw [MeasureTheory.ae_iff]
    simpa using hnull
  have hDense :
      Dense ((U \ A)ᶜ) :=
    MeasureTheory.Measure.dense_of_ae (μ := MeasureTheory.volume) hAlmostEverywhere
  -- Intersect the ambient dense full-measure set with any open neighborhood inside `U`.
  rw [mem_closure_iff]
  intro s hs hxS
  rcases hDense.inter_open_nonempty (s ∩ U) (hs.inter hUopen) ⟨x, hxS, hxU⟩ with
    ⟨y, hy⟩
  have hyS : y ∈ s := hy.1.1
  have hyU : y ∈ U := hy.1.2
  have hyNotBad : y ∉ U \ A := hy.2
  have hyA : y ∈ A := by
    by_contra hyA'
    exact hyNotBad ⟨hyU, hyA'⟩
  have _hyU_from_A : y ∈ U := hAU hyA
  exact ⟨y, hyS, hyA⟩

/-- Helper for Theorem 25.5: the dense/null part reduces to the one-dimensional slice analysis
from the textbook route. -/
lemma helperForTheorem_25_5_differentiabilitySet_dense_and_null
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f) :
    let U : Set (Fin n → Real) := interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)
    let D : Set (Fin n → Real) := {x | x ∈ U ∧ ERealDifferentiableAt f x}
    U ⊆ closure D ∧
      MeasureTheory.volume (U \ D) = 0 := by
  intro U D
  let Dj : Fin n → Set (Fin n → Real) :=
    fun j => {x | x ∈ U ∧ ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)}
  have hD_eq :
      D = ⋂ j : Fin n, Dj j := by
    simpa [U, D, Dj] using
      helperForTheorem_25_5_differentiabilitySet_eq_iInter_coordinatePartialSets
        (f := f) hproper
  have hUopen : IsOpen U := by
    simpa [U] using
      isOpen_interior
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  have hDsubU : D ⊆ U := by
    intro x hxD
    exact hxD.1
  have hnull :
      MeasureTheory.volume (U \ D) = 0 := by
    have hnullDj :
        ∀ j : Fin n, MeasureTheory.volume (U \ Dj j) = 0 := by
      intro j
      -- Each coordinate exceptional set is locally null by the Lipschitz-line-differentiability
      -- argument on countably many covering balls inside `U`.
      simpa [U, Dj] using
        helperForTheorem_25_5_coordinatePartialSet_nullComplement
          (f := f) hproper j
    have hUD_eq : U \ D = ⋃ j : Fin n, U \ Dj j := by
      ext x
      rw [hD_eq]
      simp [Set.mem_diff, not_forall, exists_prop]
    -- The differentiability exceptional set is the finite union of the coordinate exceptional sets.
    rw [hUD_eq]
    exact MeasureTheory.measure_iUnion_null hnullDj
  have hDense :
      U ⊆ closure D :=
    helperForTheorem_25_5_dense_of_null_complement_in_open
      hUopen hDsubU hnull
  exact ⟨hDense, hnull⟩

end Section25
end Chap05
