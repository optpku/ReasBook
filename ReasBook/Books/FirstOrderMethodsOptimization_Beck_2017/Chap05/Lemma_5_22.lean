/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_13
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Interval
open scoped Gradient

section

/- Lemma 5.22 is `source-facing`: it asks for a scalar-valued selection of one-dimensional
subgradients along an interval. The owner abstractions already exist upstream as Chapter 2's
`is_convex_function` and Chapter 3's `subdifferential`; on `ℝ`, the canonical reusable public
surface is the vector-side bridge `euclideanSubdifferential`, so the slope `g : ℝ` should appear
directly as a point of that set rather than through a parallel strong-dual wrapper. -/

/-- A real slope `g` belongs to the one-dimensional Euclidean subdifferential of `f` at `t`
exactly when the supporting-line inequality with slope `g` holds at every point. -/
theorem real_slope_mem_euclideanSubdifferential_iff
    {f : ℝ → EReal} {t g : ℝ} :
    g ∈ euclideanSubdifferential f t ↔
      t ∈ effective_domain f ∧ ∀ y : ℝ, f y ≥ f t + ((g * (y - t) : ℝ) : EReal) := by
  -- Rewrite Euclidean subgradient membership into the owner affine-support inequality.
  rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential, mem_subdifferential]
  have happly : ∀ y : ℝ, (InnerProductSpace.toDualMap ℝ ℝ g : Module.Dual ℝ ℝ) (y - t) = g * (y - t) := by
    intro y
    simpa [InnerProductSpace.toDualMap_apply_apply] using (RCLike.inner_apply' g (y - t))
  simp [is_subgradient_at, ge_iff_le, happly]

/-- A real-valued function `h` is a subgradient selection on `[a, b]` when it is interval
integrable on `[a, b]` and every interior value `h t` belongs to the one-dimensional Euclidean
subdifferential of `f` at `t`. -/
def IsSubgradientSelectionOnInterval (f : ℝ → EReal) (a b : ℝ) (h : ℝ → ℝ) : Prop :=
  IntervalIntegrable h MeasureTheory.volume a b ∧
    ∀ t ∈ Set.Ioo a b, h t ∈ euclideanSubdifferential f t

namespace IsSubgradientSelectionOnInterval

/-- A subgradient selection on `[a, b]` is interval integrable on that interval. -/
theorem intervalIntegrable
    {f : ℝ → EReal} {a b : ℝ} {h : ℝ → ℝ}
    (hh : IsSubgradientSelectionOnInterval f a b h) :
    IntervalIntegrable h MeasureTheory.volume a b :=
  hh.1

/-- A subgradient selection on `[a, b]` takes values in the one-dimensional Euclidean
subdifferential at every interior point. -/
theorem mem_euclideanSubdifferential
    {f : ℝ → EReal} {a b : ℝ} {h : ℝ → ℝ}
    (hh : IsSubgradientSelectionOnInterval f a b h) {t : ℝ} (ht : t ∈ Set.Ioo a b) :
    h t ∈ euclideanSubdifferential f t :=
  hh.2 t ht

end IsSubgradientSelectionOnInterval

/-- Helper for Lemma 5.22: an interior point of `[a, b]` belongs to the interior of
`effective_domain f` as soon as `Set.Icc a b ⊆ effective_domain f`. -/
lemma mem_interior_effectiveDomain_of_mem_Ioo
    {f : ℝ → EReal} {a b t : ℝ} (hdom : Set.Icc a b ⊆ effective_domain f)
    (ht : t ∈ Set.Ioo a b) :
    t ∈ interior (effective_domain f) := by
  -- The open interval `Set.Ioo a b` is the interior of `Set.Icc a b`, so interior monotonicity
  -- transfers the interval inclusion into an interior-domain inclusion.
  refine interior_mono hdom ?_
  simpa [interior_Icc] using ht

/-- Helper for Lemma 5.22: every interior point of `[a, b]` admits a Euclidean subgradient of `f`.
-/
lemma euclideanSubdifferential_nonempty_of_mem_Ioo
    (f : ℝ → EReal) (h_convex : is_convex_function f) {a b t : ℝ}
    (hdom : Set.Icc a b ⊆ effective_domain f) (ht : t ∈ Set.Ioo a b) :
    Set.Nonempty (euclideanSubdifferential f t) := by
  have ht_int : t ∈ interior (effective_domain f) :=
    mem_interior_effectiveDomain_of_mem_Ioo hdom ht
  rcases strongDualSubdifferential_nonempty_at_interior_point (f := f) h_convex ht_int with
    ⟨φ, hφ⟩
  rcases (InnerProductSpace.toDual ℝ ℝ).surjective φ with ⟨z, rfl⟩
  refine ⟨z, ?_⟩
  -- Convert the strong-dual witness back through the Riesz map.
  rw [mem_euclideanSubdifferential_iff]
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hφ

/-- Helper for Lemma 5.22: if `g x = (f x).toReal` is absolutely continuous on `[a, b]`, then
the derivative-based selection together with arbitrary interior fallback subgradients gives the
required interval-integrable subgradient field and endpoint integral identity. -/
theorem exists_subgradient_selection_of_absolutelyContinuousToReal
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_convex : is_convex_function f)
    {a b : ℝ} (hab : a < b) (hdom : Set.Icc a b ⊆ effective_domain f)
    (hac : AbsolutelyContinuousOnInterval (fun x ↦ (f x).toReal) a b) :
    ∃ h : ℝ → ℝ,
      IsSubgradientSelectionOnInterval f a b h ∧
        (f b).toReal - (f a).toReal = ∫ t in a..b, h t := by
  classical
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  let h : ℝ → ℝ := fun t ↦
    if htdiff : DifferentiableAt ℝ g t then
      deriv g t
    else if ht : t ∈ Set.Ioo a b then
      Classical.choose (euclideanSubdifferential_nonempty_of_mem_Ioo f h_convex hdom ht)
    else
      0
  have hh_subgrad : ∀ t ∈ Set.Ioo a b, h t ∈ euclideanSubdifferential f t := by
    intro t ht
    by_cases htdiff : DifferentiableAt ℝ g t
    · -- At differentiability points, the convex extended-real function has the gradient singleton
      -- as its strong-dual subdifferential, hence the Euclidean representative is a subgradient.
      have ht_finite : t ∈ interior (finite_domain f) := by
        have ht_int : t ∈ interior (effective_domain f) :=
          mem_interior_effectiveDomain_of_mem_Ioo hdom ht
        simpa [finite_domain_eq_effective_domain hne_bot] using ht_int
      have hdiff_ext : is_differentiable_at f t := ⟨ht_finite, htdiff⟩
      have hsingle :
          strongDualSubdifferential f t = {InnerProductSpace.toDual ℝ ℝ (∇ g t)} := by
        simpa [g] using
          subdifferential_eq_singleton_gradient_of_differentiableAt f t h_convex hdiff_ext
      have hmem :
          deriv g t ∈ euclideanSubdifferential f t := by
        have hstrong : InnerProductSpace.toDual ℝ ℝ (∇ g t) ∈ strongDualSubdifferential f t := by
          simp [hsingle]
        rw [mem_euclideanSubdifferential_iff]
        simpa [g, gradient_eq_deriv', InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hstrong
      simpa only [h, htdiff] using hmem
    · -- At the exceptional interior points, use the arbitrary Euclidean subgradient witness.
      simpa only [h, htdiff, ht] using
        Classical.choose_spec (euclideanSubdifferential_nonempty_of_mem_Ioo f h_convex hdom ht)
  have hh_eq_deriv :
      h =ᵐ[MeasureTheory.volume.restrict (Ι a b)] deriv g := by
    exact (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).2 <| by
      filter_upwards [hac.ae_differentiableAt] with t htdiff ht
      have ht_ioc : t ∈ Set.Ioc a b := by
        simpa [Set.uIoc_of_le hab.le] using ht
      have hdiff : DifferentiableAt ℝ g t := by
        apply htdiff
        simpa [Set.uIcc_of_le hab.le] using (show t ∈ Set.Icc a b from ⟨ht_ioc.1.le, ht_ioc.2⟩)
      simp [h, g, hdiff]
  have hh_int : IntervalIntegrable h MeasureTheory.volume a b :=
    hac.intervalIntegrable_deriv.congr_ae hh_eq_deriv.symm
  refine ⟨h, ⟨hh_int, hh_subgrad⟩, ?_⟩
  -- Replace `h` by `deriv g` almost everywhere and finish with the absolute-continuity FTC.
  calc
    (f b).toReal - (f a).toReal = g b - g a := rfl
    _ = ∫ t in a..b, deriv g t := by
      symm
      simpa [g] using hac.integral_deriv_eq_sub
    _ = ∫ t in a..b, h t := by
      symm
      exact intervalIntegral.integral_congr_ae_restrict hh_eq_deriv

/-- Helper for Lemma 5.22: the right derivative of `x ↦ (f x).toReal` at an interior point of
`[a, b]` is a Euclidean subgradient of `f` at that point. -/
lemma rightDeriv_mem_euclideanSubdifferentialOnIoo
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_convex : is_convex_function f)
    {a b t : ℝ} (hdom : Set.Icc a b ⊆ effective_domain f) (ht : t ∈ Set.Ioo a b) :
    derivWithin (fun x ↦ (f x).toReal) (Set.Ioi t) t ∈ euclideanSubdifferential f t := by
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  have hconv : ConvexOn ℝ (effective_domain f) g :=
    convexOn_toReal_of_is_convex_function h_convex (fun x _ ↦ hne_bot x)
  have ht_int : t ∈ interior (effective_domain f) :=
    mem_interior_effectiveDomain_of_mem_Ioo hdom ht
  have ht_dom : t ∈ effective_domain f := interior_subset ht_int
  rw [real_slope_mem_euclideanSubdifferential_iff]
  constructor
  · exact ht_dom
  · intro y
    by_cases hy_dom : y ∈ effective_domain f
    · rcases lt_trichotomy y t with hyt | rfl | hty
      · -- For points to the left of `t`, compare the secant slope with the left and right
        -- derivatives of the convex real restriction.
        have hslope :
            slope g y t ≤ derivWithin g (Set.Iio t) t :=
          hconv.slope_le_leftDeriv_of_mem_interior hy_dom ht_int hyt
        have hleft_right :
            derivWithin g (Set.Iio t) t ≤ derivWithin g (Set.Ioi t) t :=
          hconv.leftDeriv_le_rightDeriv_of_mem_interior ht_int
        have hreal :
            g y ≥ g t + derivWithin g (Set.Ioi t) t * (y - t) := by
          have hle :
              slope g y t ≤ derivWithin g (Set.Ioi t) t :=
            hslope.trans hleft_right
          have hslope_eq : g y - g t = slope g y t * (y - t) := by
            have hs :
                (t - y) * slope g y t = g t - g y := by
              simpa [smul_eq_mul] using (sub_smul_slope g y t)
            calc
              g y - g t = -(g t - g y) := by ring
              _ = -((t - y) * slope g y t) := by rw [hs]
              _ = slope g y t * (y - t) := by ring
          have hyt_sign : y - t < 0 := sub_neg.mpr hyt
          nlinarith [hle, hslope_eq]
        have hy_val : f y = (((f y).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (mem_effective_domain.mp hy_dom).ne (hne_bot y)).symm
        have ht_val : f t = (((f t).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (mem_effective_domain.mp ht_dom).ne (hne_bot t)).symm
        rw [hy_val, ht_val, ← EReal.coe_add]
        exact_mod_cast hreal
      · -- At the basepoint, the supporting-line inequality is an equality.
        have hy_val : f y = (((f y).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (mem_effective_domain.mp hy_dom).ne (hne_bot y)).symm
        rw [hy_val, show y - y = 0 by ring, mul_zero, EReal.coe_zero, add_zero]
      · -- For points to the right of `t`, bound the secant slope below by the right derivative.
        have hslope :
            derivWithin g (Set.Ioi t) t ≤ slope g t y :=
          hconv.rightDeriv_le_slope_of_mem_interior ht_int hy_dom hty
        have hreal :
            g y ≥ g t + derivWithin g (Set.Ioi t) t * (y - t) := by
          have hslope_eq : g y - g t = slope g t y * (y - t) := by
            have hs :
                (y - t) * slope g t y = g y - g t := by
              simpa [smul_eq_mul] using (sub_smul_slope g t y)
            calc
              g y - g t = (y - t) * slope g t y := hs.symm
              _ = slope g t y * (y - t) := by ring
          have hty_sign : 0 < y - t := sub_pos.mpr hty
          nlinarith [hslope, hslope_eq]
        have hy_val : f y = (((f y).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (mem_effective_domain.mp hy_dom).ne (hne_bot y)).symm
        have ht_val : f t = (((f t).toReal : ℝ) : EReal) :=
          (EReal.coe_toReal (mem_effective_domain.mp ht_dom).ne (hne_bot t)).symm
        rw [hy_val, ht_val, ← EReal.coe_add]
        exact_mod_cast hreal
    · -- Outside the effective domain, `f y = ⊤`, so the support inequality is trivial.
      have hytop : f y = ⊤ := by
        by_contra hnot_top
        apply hy_dom
        exact mem_effective_domain.mpr (lt_of_le_of_ne le_top hnot_top)
      simp [hytop]

/-- Helper for Lemma 5.22: once the right derivative of `x ↦ (f x).toReal` is interval integrable
on `[a, b]`, the direct one-sided FTC route produces the required subgradient selection and
endpoint integral identity. -/
theorem exists_subgradient_selection_of_rightDerivIntervalIntegrable
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a < b)
    (hdom : Set.Icc a b ⊆ effective_domain f)
    (hint :
      IntervalIntegrable (fun x ↦ derivWithin (fun y ↦ (f y).toReal) (Set.Ioi x) x)
        MeasureTheory.volume a b) :
    ∃ h : ℝ → ℝ,
      IsSubgradientSelectionOnInterval f a b h ∧
        (f b).toReal - (f a).toReal = ∫ t in a..b, h t := by
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  have hcont : ContinuousOn g (Set.Icc a b) := by
    -- The Chapter 2 bridge supplies continuity of the finite-valued restriction on the effective
    -- domain, and the interval hypothesis restricts that continuity to `[a, b]`.
    exact
      (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
        h_closed h_convex (fun x _ ↦ hne_bot x)).mono hdom
  have hderiv :
      ∀ x ∈ Set.Ioo a b, HasDerivWithinAt g (derivWithin g (Set.Ioi x) x) (Set.Ioi x) x := by
    intro x hx
    -- Convexity gives the right derivative as the derivative within `Set.Ioi x` at every
    -- interior point of the effective domain.
    have hx_int : x ∈ interior (effective_domain f) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom hx
    have hconv : ConvexOn ℝ (effective_domain f) g :=
      convexOn_toReal_of_is_convex_function h_convex (fun z _ ↦ hne_bot z)
    exact hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hx_int
  refine ⟨fun x ↦ derivWithin g (Set.Ioi x) x, ⟨hint, ?_⟩, ?_⟩
  · -- The right derivative is a Euclidean subgradient at each interior point.
    intro t ht
    simpa [g] using
      rightDeriv_mem_euclideanSubdifferentialOnIoo f hne_bot h_convex hdom ht
  · -- Apply the one-sided FTC to the interval-integrable right derivative.
    calc
      (f b).toReal - (f a).toReal = g b - g a := rfl
      _ = ∫ t in a..b, derivWithin g (Set.Ioi t) t := by
        symm
        exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab.le hcont hderiv hint

/-- Helper for Lemma 5.22: the right derivative of `x ↦ (f x).toReal` is interval integrable on
the left half `[a, (a + b) / 2]` of the interval. -/
lemma rightDeriv_intervalIntegrableOnLeftHalf
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a < b)
    (hdom : Set.Icc a b ⊆ effective_domain f) :
    IntervalIntegrable
      (fun x ↦ derivWithin (fun y ↦ (f y).toReal) (Set.Ioi x) x)
      MeasureTheory.volume a ((a + b) / 2) := by
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  let h : ℝ → ℝ := fun x ↦ derivWithin g (Set.Ioi x) x
  let m : ℝ := (a + b) / 2
  let K : ℝ := h m
  have hcont : ContinuousOn g (Set.Icc a b) := by
    -- Continuity of the finite-valued restriction is the ambient regularity input for the FTC.
    exact
      (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
        h_closed h_convex (fun x _ ↦ hne_bot x)).mono hdom
  have hconv : ConvexOn ℝ (effective_domain f) g :=
    convexOn_toReal_of_is_convex_function h_convex (fun x _ ↦ hne_bot x)
  have ham : a < m := by
    -- The midpoint lies strictly inside `[a, b]`.
    dsimp [m]
    linarith
  have hmb : m < b := by
    -- The midpoint lies strictly inside `[a, b]`.
    dsimp [m]
    linarith
  have hm_int : m ∈ interior (effective_domain f) :=
    mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨ham, hmb⟩
  have hcont_left : ContinuousOn g (Set.Icc a m) := by
    -- Restrict the ambient continuity of `g` to the left half interval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨hx.1, hx.2.trans hmb.le⟩
  have hcont_shift : ContinuousOn (fun x : ℝ ↦ K * x - g x) (Set.Icc a m) := by
    -- The shifted function has nonnegative right derivative on the left half.
    exact (continuous_const.mul continuous_id).continuousOn.sub hcont_left
  have hderiv_shift :
      ∀ x ∈ Set.Ioo a m,
        HasDerivWithinAt (fun y : ℝ ↦ K * y - g y) (K - h x) (Set.Ioi x) x := by
    intro x hx
    have hx_int : x ∈ interior (effective_domain f) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨hx.1, hx.2.trans hmb⟩
    have hg : HasDerivWithinAt g (h x) (Set.Ioi x) x := by
      -- On interior points, convexity identifies the one-sided derivative with the right derivative.
      simpa [h] using hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hx_int
    -- Differentiate the affine shift `x ↦ K * x` and subtract the derivative of `g`.
    simpa [h] using (hasDerivAt_const_mul K).hasDerivWithinAt.sub hg
  have hshift_nonneg : ∀ x ∈ Set.Ioo a m, 0 ≤ K - h x := by
    intro x hx
    have hx_int : x ∈ interior (effective_domain f) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨hx.1, hx.2.trans hmb⟩
    have hle : h x ≤ h m :=
      hconv.monotoneOn_rightDeriv hx_int hm_int hx.2.le
    -- Monotonicity of the right derivative turns the shift derivative into a nonnegative function.
    simpa [K] using sub_nonneg.mpr hle
  have hK_sub_h :
      MeasureTheory.IntegrableOn (fun x ↦ K - h x) (Set.Ioc a m) MeasureTheory.volume := by
    -- Apply the one-sided FTC integrability criterion to the shifted left-half function.
    exact intervalIntegral.integrableOn_deriv_right_of_nonneg
      hcont_shift hderiv_shift hshift_nonneg
  have hh_ioc :
      MeasureTheory.IntegrableOn h (Set.Ioc a m) MeasureTheory.volume := by
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ ↦ K) (Set.Ioc a m) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
    have hshifted :
        MeasureTheory.IntegrableOn
          (fun x : ℝ ↦ K - (K - h x)) (Set.Ioc a m) MeasureTheory.volume :=
      hconst.sub hK_sub_h
    have hrecover : (fun x : ℝ ↦ K - (K - h x)) = h := by
      funext x
      ring
    -- Recover the right derivative itself by undoing the affine shift.
    simpa [hrecover] using hshifted
  -- Convert the left-half `IntegrableOn` statement into the requested interval-integrability form.
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ham.le).2 hh_ioc

/-- Helper for Lemma 5.22: the right derivative of `x ↦ (f x).toReal` is interval integrable on
the right half `[(a + b) / 2, b]` of the interval. -/
lemma rightDeriv_intervalIntegrableOnRightHalf
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a < b)
    (hdom : Set.Icc a b ⊆ effective_domain f) :
    IntervalIntegrable
      (fun x ↦ derivWithin (fun y ↦ (f y).toReal) (Set.Ioi x) x)
      MeasureTheory.volume ((a + b) / 2) b := by
  let g : ℝ → ℝ := fun x ↦ (f x).toReal
  let h : ℝ → ℝ := fun x ↦ derivWithin g (Set.Ioi x) x
  let m : ℝ := (a + b) / 2
  let K : ℝ := h m
  have hcont : ContinuousOn g (Set.Icc a b) := by
    -- Continuity of the finite-valued restriction is the ambient regularity input for the FTC.
    exact
      (continuousOn_toReal_effective_domain_of_lowerSemicontinuous_convex_univariate
        h_closed h_convex (fun x _ ↦ hne_bot x)).mono hdom
  have hconv : ConvexOn ℝ (effective_domain f) g :=
    convexOn_toReal_of_is_convex_function h_convex (fun x _ ↦ hne_bot x)
  have ham : a < m := by
    -- The midpoint lies strictly inside `[a, b]`.
    dsimp [m]
    linarith
  have hmb : m < b := by
    -- The midpoint lies strictly inside `[a, b]`.
    dsimp [m]
    linarith
  have hm_int : m ∈ interior (effective_domain f) :=
    mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨ham, hmb⟩
  have hcont_right : ContinuousOn g (Set.Icc m b) := by
    -- Restrict the ambient continuity of `g` to the right half interval.
    refine hcont.mono ?_
    intro x hx
    exact ⟨ham.le.trans hx.1, hx.2⟩
  have hcont_shift : ContinuousOn (fun x : ℝ ↦ g x - K * x) (Set.Icc m b) := by
    -- The shifted function has nonnegative right derivative on the right half.
    exact hcont_right.sub (continuous_const.mul continuous_id).continuousOn
  have hderiv_shift :
      ∀ x ∈ Set.Ioo m b,
        HasDerivWithinAt (fun y : ℝ ↦ g y - K * y) (h x - K) (Set.Ioi x) x := by
    intro x hx
    have hx_int : x ∈ interior (effective_domain f) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨ham.trans hx.1, hx.2⟩
    have hg : HasDerivWithinAt g (h x) (Set.Ioi x) x := by
      -- On interior points, convexity identifies the one-sided derivative with the right derivative.
      simpa [h] using hconv.hasDerivWithinAt_rightDeriv_of_mem_interior hx_int
    -- Differentiate the affine shift `x ↦ K * x` and subtract it from the derivative of `g`.
    simpa [h] using hg.sub (hasDerivAt_const_mul K).hasDerivWithinAt
  have hshift_nonneg : ∀ x ∈ Set.Ioo m b, 0 ≤ h x - K := by
    intro x hx
    have hx_int : x ∈ interior (effective_domain f) :=
      mem_interior_effectiveDomain_of_mem_Ioo hdom ⟨ham.trans hx.1, hx.2⟩
    have hle : h m ≤ h x :=
      hconv.monotoneOn_rightDeriv hm_int hx_int hx.1.le
    -- Monotonicity of the right derivative turns the shift derivative into a nonnegative function.
    simpa [K] using sub_nonneg.mpr hle
  have hh_sub_K :
      MeasureTheory.IntegrableOn (fun x ↦ h x - K) (Set.Ioc m b) MeasureTheory.volume := by
    -- Apply the one-sided FTC integrability criterion to the shifted right-half function.
    exact intervalIntegral.integrableOn_deriv_right_of_nonneg
      hcont_shift hderiv_shift hshift_nonneg
  have hh_ioc :
      MeasureTheory.IntegrableOn h (Set.Ioc m b) MeasureTheory.volume := by
    have hconst :
        MeasureTheory.IntegrableOn (fun _ : ℝ ↦ K) (Set.Ioc m b) MeasureTheory.volume :=
      MeasureTheory.integrableOn_const measure_Ioc_lt_top.ne
    have hshifted :
        MeasureTheory.IntegrableOn
          (fun x : ℝ ↦ (h x - K) + K) (Set.Ioc m b) MeasureTheory.volume :=
      hh_sub_K.add hconst
    have hrecover : (fun x : ℝ ↦ (h x - K) + K) = h := by
      funext x
      ring
    -- Recover the right derivative itself by undoing the affine shift.
    simpa [hrecover] using hshifted
  -- Convert the right-half `IntegrableOn` statement into the requested interval-integrability form.
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hmb.le).2 hh_ioc

/-- Helper for Lemma 5.22: the right derivative of `x ↦ (f x).toReal` is interval integrable on
the whole interval `[a, b]`. -/
lemma rightDeriv_intervalIntegrableOnIccOfLowerSemicontinuousConvex
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a < b)
    (hdom : Set.Icc a b ⊆ effective_domain f) :
    IntervalIntegrable
      (fun x ↦ derivWithin (fun y ↦ (f y).toReal) (Set.Ioi x) x)
      MeasureTheory.volume a b := by
  let m : ℝ := (a + b) / 2
  have hleft :=
    rightDeriv_intervalIntegrableOnLeftHalf f hne_bot h_closed h_convex hab hdom
  have hright :=
    rightDeriv_intervalIntegrableOnRightHalf f hne_bot h_closed h_convex hab hdom
  -- Join the two half-interval integrability statements at the midpoint.
  simpa [m] using IntervalIntegrable.trans (b := m) hleft hright

-- Proof sketch: the interval hypothesis places every interior point `t ∈ (a, b)` in the relative
-- interior of `dom(f)`, so the Chapter 3 existence theorem gives a nonempty one-dimensional
-- subdifferential there. Choosing the monotone right-derivative selection `h(t) ∈ ∂ f(t)` and
-- applying the one-sided fundamental theorem of calculus on `[a, b]` yields the integral formula.
/-- Lemma 5.22: if a closed convex function `f : ℝ → (-∞, ∞]` never takes the value `-∞` and is
finite on `[a, b]` with `a < b`, then there exists a real-valued function `h` such that `h` is a
subgradient selection on `[a, b]` and its interval integral equals the endpoint difference
`(f b).toReal - (f a).toReal`. -/
theorem exists_subgradient_selection_eq_intervalIntegral
    (f : ℝ → EReal) (hne_bot : ∀ x, f x ≠ ⊥) (h_closed : LowerSemicontinuous f)
    (h_convex : is_convex_function f) {a b : ℝ} (hab : a < b)
    (hdom : Set.Icc a b ⊆ effective_domain f) :
    ∃ h : ℝ → ℝ,
      IsSubgradientSelectionOnInterval f a b h ∧
        (f b).toReal - (f a).toReal = ∫ t in a..b, h t := by
  -- Route correction: replace the unavailable absolute-continuity bridge by the direct
  -- right-derivative FTC route. The only remaining analytic blocker is interval integrability of
  -- the right derivative on `[a, b]`.
  have hint :
      IntervalIntegrable (fun x ↦ derivWithin (fun y ↦ (f y).toReal) (Set.Ioi x) x)
        MeasureTheory.volume a b := by
    -- Split at the midpoint and use the shifted-function integrability bridge on each half.
    exact
      rightDeriv_intervalIntegrableOnIccOfLowerSemicontinuousConvex
        f hne_bot h_closed h_convex hab hdom
  exact
    exists_subgradient_selection_of_rightDerivIntervalIntegrable
      f hne_bot h_closed h_convex hab hdom hint

end
