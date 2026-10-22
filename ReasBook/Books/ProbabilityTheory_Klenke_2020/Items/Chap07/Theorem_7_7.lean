/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Order.UpperLower
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped Topology

variable {I : Set ℝ} {φ : ℝ → ℝ} {a b t x y : ℝ}

/-- Helper: a convex subset of `ℝ` has only finitely many points outside its
interior. -/
lemma finiteBoundary_of_convex_real (hI : Convex ℝ I) : (I \ interior I).Finite := by
  let lowerEndpoint : Set ℝ := {x | x ∈ I ∧ ∀ z ∈ I, x ≤ z}
  let upperEndpoint : Set ℝ := {x | x ∈ I ∧ ∀ z ∈ I, z ≤ x}
  have hlower : lowerEndpoint.Subsingleton := by
    intro u hu v hv
    exact le_antisymm (hu.2 v hv.1) (hv.2 u hu.1)
  have hupper : upperEndpoint.Subsingleton := by
    intro u hu v hv
    exact le_antisymm (hv.2 u hu.1) (hu.2 v hv.1)
  refine (hlower.finite.union hupper.finite).subset ?_
  intro z hz
  by_contra hz'
  have hzLower : z ∉ lowerEndpoint := by
    simpa [lowerEndpoint] using fun h ↦ hz' (Or.inl h)
  have hzUpper : z ∉ upperEndpoint := by
    simpa [upperEndpoint] using fun h ↦ hz' (Or.inr h)
  have hzI : z ∈ I := hz.1
  have hzNotInterior : z ∉ interior I := hz.2
  -- A non-interior point of an interval cannot have both a point to its left and a point to its
  -- right inside the interval, otherwise the whole open interval between them would lie in `I`.
  obtain ⟨u, huI, huz : u < z⟩ : ∃ u ∈ I, u < z := by
    by_contra hu
    apply hzLower
    refine ⟨hzI, fun w hw ↦ ?_⟩
    by_contra hzw
    exact hu ⟨w, hw, lt_of_not_ge hzw⟩
  obtain ⟨v, hvI, hzv : z < v⟩ : ∃ v ∈ I, z < v := by
    by_contra hv
    apply hzUpper
    refine ⟨hzI, fun w hw ↦ ?_⟩
    by_contra hwz
    exact hv ⟨w, hw, lt_of_not_ge hwz⟩
  have huvI : Icc u v ⊆ I := hI.ordConnected.out huI hvI
  have hneigh : Ioo u v ∈ 𝓝 z := Ioo_mem_nhds huz hzv
  have hI_nhds : I ∈ 𝓝 z := by
    refine Filter.mem_of_superset hneigh ?_
    intro w hw
    exact huvI (Ioo_subset_Icc_self hw)
  exact hzNotInterior (mem_interior_iff_mem_nhds.2 hI_nhds)

/-- Canonical continuity theorem for a convex real-valued function on the interior of its domain. -/
recall ConvexOn.continuousOn_interior {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {C : Set E} {f : E → ℝ} [FiniteDimensional ℝ E] (hf : ConvexOn ℝ C f) :
  ContinuousOn f (interior C)

/-- A convex real-valued function on an interval is Borel measurable for the subspace Borel
structure on that interval. -/
-- Proof sketch: Use continuity on `interior I`, then extend measurability across the at-most
-- two boundary points of an interval to obtain measurability on the whole subtype `I`.
theorem convexOn_subtype_measurable
    (hφ : ConvexOn ℝ I φ) :
    Measurable (Set.restrict I φ) := by
  classical
  let bad : Set I := {z | (z : ℝ) ∉ interior I}
  let ψ : ℝ → ℝ := Set.piecewise (interior I) φ 0
  have hbad : bad.Finite := by
    have himage : Subtype.val '' bad = I \ interior I := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.2, hz⟩
      · intro hx
        refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
        simpa [bad] using hx.2
    refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Subtype.val_injective)
    · simpa [himage] using (finiteBoundary_of_convex_real hφ.1)
  have hψ : Measurable ψ := by
    -- The interior part is continuous by convexity, and the complement is constant.
    simpa [ψ] using
      (hφ.continuousOn_interior).measurable_piecewise continuousOn_const measurableSet_interior
  refine measurable_of_measurable_on_compl_finite bad hbad ?_
  have hψsub : Measurable fun z : ↥(badᶜ) ↦ ψ z := by
    exact hψ.comp (measurable_subtype_coe.comp measurable_subtype_coe)
  convert hψsub using 1
  ext z
  have hzInterior : ((z : I) : ℝ) ∈ interior I := by
    have hzNotBad : (z : I) ∉ bad := z.2
    simpa [bad] using hzNotBad
  simp [ψ, hzInterior]

section InteriorPoint

/-- For an interior point `x`, the difference-quotient function
`y ↦ (φ y - φ x) / (y - x)` is monotone increasing on `I \ {x}`. -/
-- Semantic search verified the canonical mathlib owner family via `ConvexOn.slope_mono`,
-- `ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior`,
-- `ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior`,
-- `ConvexOn.monotoneOn_leftDeriv`, and `ConvexOn.monotoneOn_rightDeriv`.
theorem convexOn_monotoneOn_differenceQuotient
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    MonotoneOn (slope φ x) (I \ {x}) := by
  -- The canonical slope monotonicity theorem already gives the required difference-quotient
  -- monotonicity once `x` is viewed as a point of `I`.
  simpa using hφ.slope_mono (interior_subset hx)

/-- The left derivative at an interior point equals the supremum of the left secant slopes
ending at `x` from the left. -/
recall ConvexOn.leftDeriv_eq_sSup_slope_of_mem_interior {I : Set ℝ} {φ : ℝ → ℝ} {x : ℝ}
  (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
  derivWithin φ (Iio x) x = sSup (slope φ x '' {y | y ∈ I ∧ y < x})

/-- The right derivative at an interior point equals the infimum of the right secant slopes
starting at `x` from the right. -/
recall ConvexOn.rightDeriv_eq_sInf_slope_of_mem_interior {I : Set ℝ} {φ : ℝ → ℝ} {x : ℝ}
  (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
  derivWithin φ (Ioi x) x = sInf (slope φ x '' {y | y ∈ I ∧ x < y})

/-- At an interior point, the left derivative is bounded above by the right derivative. -/
recall ConvexOn.leftDeriv_le_rightDeriv_of_mem_interior {I : Set ℝ} {φ : ℝ → ℝ} {x : ℝ}
  (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
  derivWithin φ (Iio x) x ≤ derivWithin φ (Ioi x) x

/-- A real number `t` is a supporting slope of a
convex function at an interior point `x` exactly when it lies between the left and right
derivatives at `x`. -/
-- Proof sketch: For `y > x`, compare `t` with secant slopes using the right derivative; for
-- `y < x`, compare with secant slopes using the left derivative, then combine the two directions.
theorem convexOn_supportingSlope_iff (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    (∀ y ∈ I, φ x + t * (y - x) ≤ φ y) ↔
      t ∈ Icc (derivWithin φ (Iio x) x) (derivWithin φ (Ioi x) x) := by
  constructor
  · intro ht
    constructor
    · -- For secants ending to the left of `x`, the supporting-line inequality bounds the slope
      -- from above, so the left derivative, as a supremum of such slopes, is at most `t`.
      rw [hφ.leftDeriv_eq_sSup_slope_of_mem_interior hx]
      refine csSup_le ?_ ?_
      · rw [image_nonempty]
        rcases mem_interior_iff_mem_nhds.mp hx with hx'
        rw [mem_nhds_iff_exists_Ioo_subset] at hx'
        obtain ⟨u, v, huv, huvI⟩ := hx'
        obtain ⟨z, huz, hzx⟩ := exists_between huv.1
        exact ⟨z, huvI ⟨huz, hzx.trans huv.2⟩, hzx⟩
      · rintro _ ⟨z, ⟨hzI, hzx : z < x⟩, rfl⟩
        have htz := ht z hzI
        rw [slope_def_field]
        exact (div_le_iff_of_neg (sub_neg.mpr hzx)).2 (by linarith)
    · -- For secants starting to the right of `x`, the same inequality bounds the slope from
      -- below, so `t` is at most the right derivative, the infimum of those slopes.
      rw [hφ.rightDeriv_eq_sInf_slope_of_mem_interior hx]
      refine le_csInf ?_ ?_
      · rw [image_nonempty]
        rcases mem_interior_iff_mem_nhds.mp hx with hx'
        rw [mem_nhds_iff_exists_Ioo_subset] at hx'
        obtain ⟨u, v, huv, huvI⟩ := hx'
        obtain ⟨z, hxz, hzv⟩ := exists_between huv.2
        exact ⟨z, huvI ⟨huv.1.trans hxz, hzv⟩, hxz⟩
      · rintro _ ⟨z, ⟨hzI, hxz : x < z⟩, rfl⟩
        have htz := ht z hzI
        rw [slope_def_field]
        exact (le_div_iff₀ (sub_pos.mpr hxz)).2 (by linarith)
  · rintro ⟨htLeft, htRight⟩ y hyI
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · -- On the left of `x`, the secant slope is bounded by the left derivative, hence by `t`.
      have hslope : slope φ x y ≤ t := by
        calc
          slope φ x y = slope φ y x := by rw [slope_comm]
          _ ≤ derivWithin φ (Iio x) x := by
            exact hφ.slope_le_leftDeriv_of_mem_interior hyI hx hyx
          _ ≤ t := htLeft
      rw [slope_def_field] at hslope
      have hyx' : y - x < 0 := sub_neg.mpr hyx
      exact by
        have : t * (y - x) ≤ φ y - φ x := (div_le_iff_of_neg hyx').1 hslope
        linarith
    · -- At `y = x` the supporting-line inequality is tautological.
      simp
    · -- On the right of `x`, `t` is bounded by the right derivative, hence by the secant slope.
      have hslope : t ≤ slope φ x y := by
        calc
          t ≤ derivWithin φ (Ioi x) x := htRight
          _ ≤ slope φ x y := by
            exact hφ.rightDeriv_le_slope_of_mem_interior hx hyI hxy
      rw [slope_def_field] at hslope
      have hxy' : 0 < y - x := sub_pos.mpr hxy
      exact by
        have : t * (y - x) ≤ φ y - φ x := (le_div_iff₀ hxy').1 hslope
        linarith

/-- The left-derivative map of a convex function is monotone on the interior of the interval. -/
recall ConvexOn.monotoneOn_leftDeriv {I : Set ℝ} {φ : ℝ → ℝ}
  (hφ : ConvexOn ℝ I φ) :
  MonotoneOn (fun z ↦ derivWithin φ (Iio z) z) (interior I)

/-- The right-derivative map of a convex function is monotone on the interior of the interval. -/
recall ConvexOn.monotoneOn_rightDeriv {I : Set ℝ} {φ : ℝ → ℝ}
  (hφ : ConvexOn ℝ I φ) :
  MonotoneOn (fun z ↦ derivWithin φ (Ioi z) z) (interior I)

/-- Helper: the right derivative at a smaller interior point is bounded by the
left derivative at a larger interior point. -/
lemma rightDeriv_le_leftDeriv_of_lt
    (hφ : ConvexOn ℝ I φ) {u v : ℝ} (hu : u ∈ interior I) (hv : v ∈ interior I)
    (huv : u < v) :
    derivWithin φ (Ioi u) u ≤ derivWithin φ (Iio v) v := by
  -- Compare both one-sided derivatives to the secant slope joining `u` and `v`.
  calc
    derivWithin φ (Ioi u) u ≤ slope φ u v := by
      exact hφ.rightDeriv_le_slope_of_mem_interior hu (interior_subset hv) huv
    _ ≤ derivWithin φ (Iio v) v := by
      exact hφ.slope_le_leftDeriv_of_mem_interior (interior_subset hu) hv huv

/-- Helper: any strict lower bound on `D⁻φ(x)` is eventually a lower bound on the
nearby left derivatives from the left. -/
lemma eventually_lt_leftDeriv_of_lt
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) {r : ℝ}
    (hr : r < derivWithin φ (Iio x) x) :
    ∀ᶠ z in 𝓝[<] x, r < derivWithin φ (Iio z) z := by
  have hnonempty : (slope φ x '' {y | y ∈ I ∧ y < x}).Nonempty := by
    rcases mem_interior_iff_mem_nhds.mp hx with hx'
    rw [mem_nhds_iff_exists_Ioo_subset] at hx'
    obtain ⟨u, v, huv, huvI⟩ := hx'
    obtain ⟨z, huz, hzx⟩ := exists_between huv.1
    exact ⟨slope φ x z, ⟨z, ⟨huvI ⟨huz, hzx.trans huv.2⟩, hzx⟩, rfl⟩⟩
  rw [hφ.leftDeriv_eq_sSup_slope_of_mem_interior hx] at hr
  obtain ⟨m, hm, hry⟩ := exists_lt_of_lt_csSup hnonempty hr
  rcases hm with ⟨y, ⟨hyI, hyx⟩, rfl⟩
  have hcontφ : ContinuousAt φ x := by
    exact hφ.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx)
  have hcontSlope : ContinuousAt (fun z : ℝ ↦ slope φ y z) x := by
    -- The fixed-left-endpoint secant slope is continuous away from `y`.
    rw [show (fun z : ℝ ↦ slope φ y z) = fun z ↦ (φ z - φ y) / (z - y) by
      ext z
      rw [slope_def_field]]
    refine (hcontφ.sub continuousAt_const).div ?_ ?_
    · exact continuousAt_id.sub continuousAt_const
    · exact sub_ne_zero.mpr hyx.ne'
  have hSlopeEvent : ∀ᶠ z in 𝓝[<] x, r < slope φ y z := by
    have : ∀ᶠ z in 𝓝 x, r < slope φ y z := by
      have hry' : r < slope φ y x := by simpa [slope_comm] using hry
      exact hcontSlope.eventually (Ioi_mem_nhds hry')
    exact this.filter_mono nhdsWithin_le_nhds
  have hInteriorEvent : ∀ᶠ z in 𝓝[<] x, z ∈ interior I := by
    exact (nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x) (isOpen_interior.mem_nhds hx)
  have hRightOfY : ∀ᶠ z in 𝓝[<] x, y < z := by
    exact (nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x) (Ioi_mem_nhds hyx)
  -- Near `x`, the fixed secant slope sits below the nearby left derivatives.
  filter_upwards [hSlopeEvent, hInteriorEvent, hRightOfY] with z hzSlope hzInterior hyz
  exact hzSlope.trans_le (hφ.slope_le_leftDeriv_of_mem_interior hyI hzInterior hyz)

/-- Helper: any strict upper bound on `D⁺φ(x)` is eventually an upper bound on the
nearby right derivatives from the right. -/
lemma eventually_rightDeriv_lt_of_gt
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) {r : ℝ}
    (hr : derivWithin φ (Ioi x) x < r) :
    ∀ᶠ z in 𝓝[>] x, derivWithin φ (Ioi z) z < r := by
  have hnonempty : (slope φ x '' {y | y ∈ I ∧ x < y}).Nonempty := by
    rcases mem_interior_iff_mem_nhds.mp hx with hx'
    rw [mem_nhds_iff_exists_Ioo_subset] at hx'
    obtain ⟨u, v, huv, huvI⟩ := hx'
    obtain ⟨z, hxz, hzv⟩ := exists_between huv.2
    exact ⟨slope φ x z, ⟨z, ⟨huvI ⟨huv.1.trans hxz, hzv⟩, hxz⟩, rfl⟩⟩
  rw [hφ.rightDeriv_eq_sInf_slope_of_mem_interior hx] at hr
  obtain ⟨m, hm, hyr⟩ := exists_lt_of_csInf_lt hnonempty hr
  rcases hm with ⟨y, ⟨hyI, hxy⟩, rfl⟩
  have hcontφ : ContinuousAt φ x := by
    exact hφ.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds hx)
  have hcontSlope : ContinuousAt (fun z : ℝ ↦ slope φ z y) x := by
    -- The fixed-right-endpoint secant slope is continuous away from `y`.
    rw [show (fun z : ℝ ↦ slope φ z y) = fun z ↦ (φ y - φ z) / (y - z) by
      ext z
      rw [slope_def_field]]
    refine (continuousAt_const.sub hcontφ).div ?_ ?_
    · exact continuousAt_const.sub continuousAt_id
    · exact sub_ne_zero.mpr hxy.ne'
  have hSlopeEvent : ∀ᶠ z in 𝓝[>] x, slope φ z y < r := by
    have : ∀ᶠ z in 𝓝 x, slope φ z y < r := by
      exact hcontSlope.eventually (Iio_mem_nhds hyr)
    exact this.filter_mono nhdsWithin_le_nhds
  have hInteriorEvent : ∀ᶠ z in 𝓝[>] x, z ∈ interior I := by
    change interior I ∈ 𝓝[>] x
    exact (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (isOpen_interior.mem_nhds hx)
  have hLeftOfY : ∀ᶠ z in 𝓝[>] x, z < y := by
    exact (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (Iio_mem_nhds hxy)
  -- Near `x`, the nearby right derivatives sit below the fixed secant slope.
  filter_upwards [hSlopeEvent, hInteriorEvent, hLeftOfY] with z hzSlope hzInterior hzy
  exact (hφ.rightDeriv_le_slope_of_mem_interior hzInterior hyI hzy).trans_lt hzSlope

/-- The left-derivative map of a convex function is left continuous on the interior of the
interval. -/
-- Proof sketch: Apply one-sided continuity of monotone functions to the monotone left-derivative
-- map on `interior I`.
theorem convexOn_leftDeriv_continuousWithinAt_Iic
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (Iic x) x := by
  rw [← continuousWithinAt_Iio_iff_Iic]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro r hr
    -- Strict lower bounds propagate from the left via the secant-slope characterization.
    exact eventually_lt_leftDeriv_of_lt hφ hx hr
  · intro r hr
    -- Strict upper bounds come from monotonicity of the left-derivative map.
    have hInteriorEvent : ∀ᶠ z in 𝓝[<] x, z ∈ interior I := by
      exact (nhdsWithin_le_nhds : 𝓝[<] x ≤ 𝓝 x) (isOpen_interior.mem_nhds hx)
    filter_upwards [self_mem_nhdsWithin, hInteriorEvent] with z hzx hzInterior
    exact (hφ.monotoneOn_leftDeriv hzInterior hx hzx.le).trans_lt hr

/-- The right-derivative map of a convex function is right continuous on the interior of the
interval. -/
-- Proof sketch: Apply one-sided continuity of monotone functions to the monotone right-derivative
-- map on `interior I`.
theorem convexOn_rightDeriv_continuousWithinAt_Ici
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Ioi z) z) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro r hr
    -- Strict lower bounds come from monotonicity of the right-derivative map.
    have hInteriorEvent : ∀ᶠ z in 𝓝[>] x, z ∈ interior I := by
      exact (nhdsWithin_le_nhds : 𝓝[>] x ≤ 𝓝 x) (isOpen_interior.mem_nhds hx)
    filter_upwards [self_mem_nhdsWithin, hInteriorEvent] with z hxz hzInterior
    exact hr.trans_le (hφ.monotoneOn_rightDeriv hx hzInterior hxz.le)
  · intro r hr
    -- Strict upper bounds propagate from the right via the secant-slope characterization.
    exact eventually_rightDeriv_lt_of_gt hφ hx hr

/-- At any interior point where the left-derivative map
is continuous, the left and right derivatives of a convex function coincide. -/
-- Proof sketch: Since `D⁻φ` is always left continuous, ordinary continuity at `x` adds the
-- right-continuity needed to squeeze `D⁺φ x` to the same value using monotonicity and
-- `D⁻φ ≤ D⁺φ`.
theorem convexOn_leftDeriv_eq_rightDeriv_of_leftDeriv_continuousWithinAt_Iic
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I)
    (hcont : ContinuousAt (fun z ↦ derivWithin φ (Iio z) z) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := by
  refine le_antisymm (hφ.leftDeriv_le_rightDeriv_of_mem_interior hx) ?_
  by_contra hlt
  let r := (derivWithin φ (Iio x) x + derivWithin φ (Ioi x) x) / 2
  have hrLeft : derivWithin φ (Iio x) x < r := by
    dsimp [r]
    linarith
  have hrRight : r < derivWithin φ (Ioi x) x := by
    dsimp [r]
    linarith
  have hcontRight : ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (Ioi x) x := by
    exact (continuousWithinAt_Ioi_iff_Ici).2 hcont.continuousWithinAt
  have hEventuallyLt : ∀ᶠ z in 𝓝[>] x, derivWithin φ (Iio z) z < r := by
    exact hcontRight.eventually (Iio_mem_nhds hrLeft)
  have hInteriorEvent : ∀ᶠ z in 𝓝[>] x, z ∈ interior I := by
    rcases mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hx) with
      ⟨u, v, huv, huvI⟩
    filter_upwards [Ioo_mem_nhdsGT huv.2] with z hz
    exact huvI ⟨huv.1.trans hz.1, hz.2⟩
  have hRightEvent : ∀ᶠ z in 𝓝[>] x, x < z := by
    simpa using (show Set.Ioi x ∈ 𝓝[>] x from self_mem_nhdsWithin)
  have hEventually :
      ∀ᶠ z in 𝓝[>] x, x < z ∧ derivWithin φ (Iio z) z < r ∧ z ∈ interior I :=
    hRightEvent.and (hEventuallyLt.and hInteriorEvent)
  have hFalse : ∀ᶠ z in 𝓝[>] x, False := by
    filter_upwards [hEventually] with z hz
    exact (not_le_of_gt hrRight)
      ((rightDeriv_le_leftDeriv_of_lt hφ hx hz.2.2 hz.1).trans hz.2.1.le)
  have : ¬ (𝓝[>] x).NeBot := by
    rw [Filter.eventually_false_iff_eq_bot.mp hFalse]
    simp
  exact this inferInstance

/-- At any interior point where the right-derivative
map is continuous, the left and right derivatives of a convex function coincide. -/
-- Proof sketch: Since `D⁺φ` is always right continuous, ordinary continuity at `x` adds the
-- left-continuity needed to squeeze `D⁻φ x` to the same value using monotonicity and
-- `D⁻φ ≤ D⁺φ`.
theorem convexOn_leftDeriv_eq_rightDeriv_of_rightDeriv_continuousWithinAt_Ici
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I)
    (hcont : ContinuousAt (fun z ↦ derivWithin φ (Ioi z) z) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := by
  refine le_antisymm (hφ.leftDeriv_le_rightDeriv_of_mem_interior hx) ?_
  by_contra hlt
  let r := (derivWithin φ (Iio x) x + derivWithin φ (Ioi x) x) / 2
  have hrLeft : derivWithin φ (Iio x) x < r := by
    dsimp [r]
    linarith
  have hrRight : r < derivWithin φ (Ioi x) x := by
    dsimp [r]
    linarith
  have hcontLeft : ContinuousWithinAt (fun z ↦ derivWithin φ (Ioi z) z) (Iio x) x := by
    exact (continuousWithinAt_Iio_iff_Iic).2 hcont.continuousWithinAt
  have hEventuallyGt : ∀ᶠ z in 𝓝[<] x, r < derivWithin φ (Ioi z) z := by
    exact hcontLeft.eventually (Ioi_mem_nhds hrRight)
  have hInteriorEvent : ∀ᶠ z in 𝓝[<] x, z ∈ interior I := by
    rcases mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hx) with
      ⟨u, v, huv, huvI⟩
    filter_upwards [Ioo_mem_nhdsLT huv.1] with z hz
    exact huvI ⟨hz.1, hz.2.trans huv.2⟩
  have hLeftEvent : ∀ᶠ z in 𝓝[<] x, z < x := by
    simpa using (show Set.Iio x ∈ 𝓝[<] x from self_mem_nhdsWithin)
  have hEventually :
      ∀ᶠ z in 𝓝[<] x, z < x ∧ r < derivWithin φ (Ioi z) z ∧ z ∈ interior I :=
    hLeftEvent.and (hEventuallyGt.and hInteriorEvent)
  have hFalse : ∀ᶠ z in 𝓝[<] x, False := by
    filter_upwards [hEventually] with z hz
    exact (not_le_of_gt hz.2.1)
      ((rightDeriv_le_leftDeriv_of_lt hφ hz.2.2 hx hz.1).trans hrLeft.le)
  have : ¬ (𝓝[<] x).NeBot := by
    rw [Filter.eventually_false_iff_eq_bot.mp hFalse]
    simp
  exact this inferInstance

/-- Helper: when the one-sided derivatives agree at an interior point, they give
the ordinary derivative. -/
lemma hasDerivAt_of_leftDeriv_eq_rightDeriv
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I)
    (hEq : derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x) :
    HasDerivAt φ (derivWithin φ (Ioi x) x) x := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · -- The left secant slopes converge to `D⁻φ(x)`, which equals `D⁺φ(x)` by hypothesis.
    have hleft : Filter.Tendsto (slope φ x) (𝓝[<] x) (𝓝 (derivWithin φ (Iio x) x)) := by
      rw [← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio]
      exact hφ.hasDerivWithinAt_leftDeriv_of_mem_interior hx
    simpa [hEq] using hleft
  · -- The right secant slopes converge to `D⁺φ(x)` directly.
    rw [← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
    exact hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx

/-- A convex function is differentiable at an interior
point exactly when its left and right derivatives at that point agree. -/
-- Proof sketch: If `φ` is differentiable, both one-sided derivatives equal the ordinary
-- derivative; conversely, equality of the one-sided derivatives upgrades the two one-sided limits
-- of the secant slopes to a single derivative.
theorem convexOn_differentiableAt_iff_leftDeriv_eq_rightDeriv
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    DifferentiableAt ℝ φ x ↔
      derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := by
  constructor
  · intro hxdiff
    have hf' := hxdiff.hasDerivAt
    have hleft : Filter.Tendsto (slope φ x) (𝓝[<] x) (𝓝 (derivWithin φ (Iio x) x)) := by
      rw [← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio]
      exact hφ.hasDerivWithinAt_leftDeriv_of_mem_interior hx
    have hright : Filter.Tendsto (slope φ x) (𝓝[>] x) (𝓝 (derivWithin φ (Ioi x) x)) := by
      rw [← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
      exact hφ.hasDerivWithinAt_rightDeriv_of_mem_interior hx
    have hleft' : Filter.Tendsto (slope φ x) (𝓝[<] x) (𝓝 (deriv φ x)) := by
      exact hf'.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hright' : Filter.Tendsto (slope φ x) (𝓝[>] x) (𝓝 (deriv φ x)) := by
      exact hf'.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hEqLeft : derivWithin φ (Iio x) x = deriv φ x := tendsto_nhds_unique hleft hleft'
    have hEqRight : derivWithin φ (Ioi x) x = deriv φ x := tendsto_nhds_unique hright hright'
    exact hEqLeft.trans hEqRight.symm
  · intro hEq
    exact (hasDerivAt_of_leftDeriv_eq_rightDeriv hφ hx hEq).differentiableAt

/-- At an interior differentiability point of a convex
function, the ordinary derivative agrees with the right derivative. -/
theorem convexOn_deriv_eq_rightDeriv_of_differentiableAt
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) (hxdiff : DifferentiableAt ℝ φ x) :
    deriv φ x = derivWithin φ (Ioi x) x := by
  -- Once the one-sided derivatives agree, the ordinary derivative is exactly that common value.
  have hEq :=
    (convexOn_differentiableAt_iff_leftDeriv_eq_rightDeriv hφ hx).mp hxdiff
  exact (hasDerivAt_of_leftDeriv_eq_rightDeriv hφ hx hEq).deriv

end InteriorPoint

/-- Helper: the unordered closed interval between two interior points of a convex
real set stays inside the interior. -/
lemma uIcc_subset_interior_of_mem_interior
    (hI : Convex ℝ I) (ha : a ∈ interior I) (hb : b ∈ interior I) :
    Set.uIcc a b ⊆ interior I := by
  -- The interior of a convex real set is again convex, hence order-connected.
  exact (hI.interior.ordConnected).uIcc_subset ha hb

/-- A convex function on an interval is differentiable almost everywhere on that interval. -/
-- Proof sketch: The one-sided derivative maps are monotone on `interior I`, so their
-- discontinuity sets are countable; outside this null set the left and right derivatives coincide,
-- hence `φ` is differentiable there.
theorem convexOn_ae_differentiableAt
    (hφ : ConvexOn ℝ I φ) :
    ∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ φ x := by
  let bad :
      Set ℝ := {x ∈ interior I |
        ¬ ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (interior I) x}
  have hbadCount : bad.Countable :=
    (hφ.monotoneOn_leftDeriv).countable_not_continuousWithinAt
  have hbadAE : ∀ᵐ x ∂volume, x ∉ bad := by
    rw [ae_iff]
    simpa [bad] using (hbadCount.measure_zero volume)
  have hInteriorAE : ∀ᵐ x ∂(volume.restrict I), x ∈ interior I := by
    rw [ae_iff]
    change (volume.restrict I) (interior I)ᶜ = 0
    rw [Measure.restrict_apply measurableSet_interior.compl]
    simpa [Set.diff_eq, inter_assoc, inter_left_comm, inter_comm] using
      ((finiteBoundary_of_convex_real hφ.1).countable.measure_zero volume)
  have hbadAERestrict : ∀ᵐ x ∂(volume.restrict I), x ∉ bad :=
    ae_restrict_of_ae hbadAE
  filter_upwards [hInteriorAE, hbadAERestrict] with x hxInterior hxBad
  have hcontWithin :
      ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (interior I) x := by
    by_contra hnot
    exact hxBad ⟨hxInterior, hnot⟩
  have hcontAt :
      ContinuousAt (fun z ↦ derivWithin φ (Iio z) z) x := by
    exact (continuousWithinAt_iff_continuousAt (isOpen_interior.mem_nhds hxInterior)).1 hcontWithin
  have hEq :
      derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x :=
    convexOn_leftDeriv_eq_rightDeriv_of_leftDeriv_continuousWithinAt_Iic hφ hxInterior hcontAt
  exact (convexOn_differentiableAt_iff_leftDeriv_eq_rightDeriv hφ hxInterior).2 hEq

/-- On interior points of the interval, the increment
of a convex function is the interval integral of its right derivative. -/
-- Proof sketch: The right derivative is monotone, hence measurable and locally integrable; then
-- use almost-everywhere differentiability together with the one-dimensional fundamental theorem of
-- calculus for monotone derivatives.
theorem convexOn_sub_eq_intervalIntegral_rightDeriv
    (hφ : ConvexOn ℝ I φ) (ha : a ∈ interior I) (hb : b ∈ interior I) :
    φ b - φ a = ∫ x in a..b, derivWithin φ (Ioi x) x := by
  have huIcc : Set.uIcc a b ⊆ interior I :=
    uIcc_subset_interior_of_mem_interior hφ.1 ha hb
  have hcont : ContinuousOn φ (Set.uIcc a b) := by
    -- Every point of the integration interval lies in the interior, where `φ` is continuous.
    intro z hz
    exact hφ.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds (huIcc hz))
      |>.continuousWithinAt
  have hderiv :
      ∀ z ∈ Ioo (min a b) (max a b), HasDerivWithinAt φ (derivWithin φ (Ioi z) z) (Ioi z) z := by
    intro z hz
    exact hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (huIcc (uIoo_subset_uIcc_self hz))
  have hmono : MonotoneOn (fun z ↦ derivWithin φ (Ioi z) z) (Set.uIcc a b) := by
    intro u hu v hv huv
    exact hφ.monotoneOn_rightDeriv (huIcc hu) (huIcc hv) huv
  have hint : IntervalIntegrable (fun z ↦ derivWithin φ (Ioi z) z) volume a b :=
    hmono.intervalIntegrable
  -- The right-derivative FTC applies on the compact interval between the two interior points.
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint).symm

/-- Item (1) for Theorem 7.7: a convex real-valued function on an interval is
continuous on the interior,
and hence Borel measurable for the subspace Borel structure on that interval. -/
theorem convexOn_continuousOn_interior_and_subtype_measurable
    (hφ : ConvexOn ℝ I φ) :
    ContinuousOn φ (interior I) ∧ Measurable (Set.restrict I φ) := by
  constructor
  -- The continuity component is exactly the canonical convexity theorem on the interior.
  · exact hφ.continuousOn_interior
  -- Measurability on the subtype was proved above from continuity plus the finite boundary.
  · exact convexOn_subtype_measurable hφ

/-- Item (2a) for Theorem 7.7: for an interior point `x`, the
difference-quotient function is monotone increasing on `I \ {x}`. -/
theorem convexOn_differenceQuotient_mono
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    MonotoneOn (slope φ x) (I \ {x}) := by
  -- This is the already-proved monotonicity of the difference quotient at an interior point.
  exact convexOn_monotoneOn_differenceQuotient hφ hx

/-- Item (2b) for Theorem 7.7: for an interior point `x`, the left
derivative is the supremum of the left secant slopes ending at `x`. -/
theorem convexOn_leftDeriv_eq_sSup_slope
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    derivWithin φ (Iio x) x = sSup (slope φ x '' {y | y ∈ I ∧ y < x}) := by
  -- The left derivative formula was recalled above from the convex-analysis API.
  exact hφ.leftDeriv_eq_sSup_slope_of_mem_interior hx

/-- Item (2c) for Theorem 7.7: for an interior point `x`, the right
derivative is the infimum of the right secant slopes starting at `x`. -/
theorem convexOn_rightDeriv_eq_sInf_slope
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    derivWithin φ (Ioi x) x = sInf (slope φ x '' {y | y ∈ I ∧ x < y}) := by
  -- The right derivative formula is the matching recalled one-sided derivative identity.
  exact hφ.rightDeriv_eq_sInf_slope_of_mem_interior hx

/-- Item (3) for Theorem 7.7: at an interior point `x`, the left
derivative is bounded above by the right derivative, and a real number `t` is a
supporting slope exactly when it lies between them. -/
theorem convexOn_leftDeriv_le_rightDeriv_and_supportingSlope_iff
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    derivWithin φ (Iio x) x ≤ derivWithin φ (Ioi x) x ∧
      ((∀ y ∈ I, φ x + t * (y - x) ≤ φ y) ↔
        t ∈ Icc (derivWithin φ (Iio x) x) (derivWithin φ (Ioi x) x)) := by
  constructor
  -- The derivative order is the standard convex one-sided derivative inequality.
  · exact hφ.leftDeriv_le_rightDeriv_of_mem_interior hx
  -- The supporting-slope characterization was proved above from the secant-slope formulas.
  · exact convexOn_supportingSlope_iff hφ hx

/-- Item (4a) for Theorem 7.7: the left-derivative map `x ↦ D⁻φ(x)` is monotone increasing on
`interior I`. -/
theorem convexOn_leftDeriv_monotoneOn_interior
    (hφ : ConvexOn ℝ I φ) :
    MonotoneOn (fun z ↦ derivWithin φ (Iio z) z) (interior I) := by
  -- This wrapper forwards to the monotonicity theorem already recalled above.
  exact hφ.monotoneOn_leftDeriv

/-- Item (4b) for Theorem 7.7: the right-derivative map `x ↦ D⁺φ(x)` is monotone increasing on
`interior I`. -/
theorem convexOn_rightDeriv_monotoneOn_interior
    (hφ : ConvexOn ℝ I φ) :
    MonotoneOn (fun z ↦ derivWithin φ (Ioi z) z) (interior I) := by
  -- This is the corresponding monotonicity theorem for right derivatives.
  exact hφ.monotoneOn_rightDeriv

/-- Item (4c) for Theorem 7.7: the left-derivative map `x ↦ D⁻φ(x)` is left continuous at interior
points. -/
theorem convexOn_leftDeriv_leftContinuousWithinAt
    (hφ : ConvexOn ℝ I φ) {x : ℝ} (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Iio z) z) (Iic x) x := by
  -- The left continuity statement was established earlier from one-sided continuity
  -- of monotone maps.
  exact convexOn_leftDeriv_continuousWithinAt_Iic hφ hx

/-- Item (4d) for Theorem 7.7: the right-derivative map `x ↦ D⁺φ(x)`
is right continuous at interior points. -/
theorem convexOn_rightDeriv_rightContinuousWithinAt
    (hφ : ConvexOn ℝ I φ) {x : ℝ} (hx : x ∈ interior I) :
    ContinuousWithinAt (fun z ↦ derivWithin φ (Ioi z) z) (Ici x) x := by
  -- The right continuity statement is the matching theorem proved above.
  exact convexOn_rightDeriv_continuousWithinAt_Ici hφ hx

/-- Item (4e) for Theorem 7.7: if the left-derivative map is
continuous at an interior point `x`, then `D⁻φ(x) = D⁺φ(x)`. -/
theorem convexOn_leftDeriv_eq_rightDeriv_of_leftDeriv_continuousAt
    (hφ : ConvexOn ℝ I φ) {x : ℝ} (hx : x ∈ interior I)
    (hcont : ContinuousAt (fun z ↦ derivWithin φ (Iio z) z) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := by
  -- The equality follows from the previously proved continuity criterion for the
  -- left derivative map.
  exact convexOn_leftDeriv_eq_rightDeriv_of_leftDeriv_continuousWithinAt_Iic hφ hx hcont

/-- Item (4f) for Theorem 7.7: if the right-derivative map is
continuous at an interior point `x`, then `D⁻φ(x) = D⁺φ(x)`. -/
theorem convexOn_leftDeriv_eq_rightDeriv_of_rightDeriv_continuousAt
    (hφ : ConvexOn ℝ I φ) {x : ℝ} (hx : x ∈ interior I)
    (hcont : ContinuousAt (fun z ↦ derivWithin φ (Ioi z) z) x) :
    derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x := by
  -- The symmetric continuity criterion identifies the two one-sided derivatives.
  exact convexOn_leftDeriv_eq_rightDeriv_of_rightDeriv_continuousWithinAt_Ici hφ hx hcont

/-- Item (5) for Theorem 7.7: a convex function is differentiable at
an interior point exactly when its left and right derivatives agree there; in
that case the ordinary derivative equals the right derivative. -/
theorem convexOn_differentiableAt_iff_oneSidedDeriv_eq_and_deriv_eq_rightDeriv
    (hφ : ConvexOn ℝ I φ) (hx : x ∈ interior I) :
    (DifferentiableAt ℝ φ x ↔ derivWithin φ (Iio x) x = derivWithin φ (Ioi x) x) ∧
      (DifferentiableAt ℝ φ x → deriv φ x = derivWithin φ (Ioi x) x) := by
  constructor
  -- The first component is the one-sided derivative criterion for differentiability.
  · exact convexOn_differentiableAt_iff_leftDeriv_eq_rightDeriv hφ hx
  -- Once differentiable, the ordinary derivative is the common one-sided derivative.
  · intro hxdiff
    exact convexOn_deriv_eq_rightDeriv_of_differentiableAt hφ hx hxdiff

/-- Theorem 7.7: item (6). A convex function on an interval is
differentiable almost everywhere, and for interior points `a, b` the increment
`φ b - φ a` is the interval integral of the right derivative. -/
theorem convexOn_ae_differentiableAt_and_sub_eq_intervalIntegral_rightDeriv
    (hφ : ConvexOn ℝ I φ) :
    (∀ᵐ x ∂(volume.restrict I), DifferentiableAt ℝ φ x) ∧
      ∀ ⦃a b : ℝ⦄, a ∈ interior I → b ∈ interior I →
        φ b - φ a = ∫ x in a..b, derivWithin φ (Ioi x) x := by
  constructor
  -- Almost-everywhere differentiability was already proved using countable discontinuities.
  · exact convexOn_ae_differentiableAt hφ
  -- The increment formula is the previously established interval-integral identity.
  · intro a b ha hb
    exact convexOn_sub_eq_intervalIntegral_rightDeriv hφ ha hb
