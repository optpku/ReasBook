/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_34

-- Declarations for this item will be appended below by the statement pipeline.

namespace ERealFunction

attribute [local instance] Classical.propDecidable

private noncomputable def finiteOnOpenInterval (f : ℝ → ℝ) (α β : EReal) :
    ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if x ∈ erealOpenInterval α β then
      ⟨((f x : ℝ) : EReal), EReal.bot_lt_coe _⟩
    else
      ⟨(⊤ : EReal), Set.mem_Ioi.mpr bot_lt_top⟩

/-- Helper for Example 9.36: the effective domain of the finite-open-interval model is exactly
the underlying open interval. -/
private theorem finiteOnOpenInterval_effectiveDomain (f : ℝ → ℝ) (α β : EReal) :
    effectiveDomain (finiteOnOpenInterval f α β) = erealOpenInterval α β := by
  -- The interior branch is finite, while every exterior point is sent to `+∞`.
  ext x
  by_cases hx : x ∈ erealOpenInterval α β
  · simp [mem_effectiveDomain_iff, finiteOnOpenInterval, hx]
  · simp [mem_effectiveDomain_iff, finiteOnOpenInterval, hx]

/-- Helper for Example 9.36: a genuine one-sided `EReal` limit above `⊥` forces the corresponding
one-sided `liminf` to stay above `⊥`. -/
private theorem boundary_liminf_gt_bot_of_tendsto
    {g : ℝ → Set.Ioi (⊥ : EReal)} {x : ℝ} {s : Set ℝ} {a : EReal}
    (hs : Filter.NeBot (nhdsWithin x s))
    (h : Filter.Tendsto (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x s) (nhds a)) (ha : ⊥ < a) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x s) := by
  -- A convergent filter has `liminf` equal to its limit value.
  let _ : Filter.NeBot (nhdsWithin x s) := hs
  rw [h.liminf_eq]
  exact ha

/-- Helper for Example 9.36: strict convexity of the finite real seed on the open interval gives
strict convexity of its `]-∞,+∞]`-valued open-interval model. -/
private theorem strictlyConvex_finiteOnOpenInterval_of_strictConvexOn
    {f : ℝ → ℝ} {α β : EReal} (hf : StrictConvexOn ℝ (erealOpenInterval α β) f) :
    StrictlyConvex (finiteOnOpenInterval f α β) := by
  intro x hx y hy hxy a ha0 ha1
  -- Translate the effective-domain assumptions back to the open interval.
  have hx' : x ∈ erealOpenInterval α β := by
    simpa [finiteOnOpenInterval_effectiveDomain] using hx
  have hy' : y ∈ erealOpenInterval α β := by
    simpa [finiteOnOpenInterval_effectiveDomain] using hy
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hab : a + (1 - a) = 1 := by ring
  have hxy' : a • x + (1 - a) • y ∈ erealOpenInterval α β := by
    exact hf.1 hx' hy' ha0.le hb0.le hab
  -- Then the Jensen inequality is exactly the real strict-convexity inequality cast to `EReal`.
  have hineq :
      f (a * x + (1 - a) * y) < a * f x + (1 - a) * f y :=
    hf.2 hx' hy' hxy ha0 hb0 hab
  have hineqE :
      (((f (a * x + (1 - a) * y) : ℝ) : EReal)) <
        (((a * f x + (1 - a) * f y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  calc
    (finiteOnOpenInterval f α β (a • x + (1 - a) • y) : EReal)
        = (((f (a * x + (1 - a) * y) : ℝ) : EReal)) := by
            rw [finiteOnOpenInterval, if_pos hxy']
            rfl
    _ < (((a * f x + (1 - a) * f y : ℝ) : EReal)) := hineqE
    _ = (a : EReal) * (finiteOnOpenInterval f α β x : EReal) +
          (1 - a : EReal) * (finiteOnOpenInterval f α β y : EReal) := by
            simp [finiteOnOpenInterval, hx', hy', EReal.coe_mul, EReal.coe_add]

/-- Helper for Example 9.36: a finite everywhere-defined strictly convex real function stays
strictly convex after coercion to `EReal`. -/
private theorem strictlyConvex_toEReal_of_strictConvexOn_univ
    {f : ℝ → ℝ} (hf : StrictConvexOn ℝ Set.univ f) :
    StrictlyConvex f.toEReal := by
  intro x hx y hy hxy a ha0 ha1
  have hb0 : 0 < 1 - a := sub_pos.mpr ha1
  have hab : a + (1 - a) = 1 := by ring
  -- On `univ`, the real strict-convexity inequality is already the desired one.
  have hineq :
      f (a * x + (1 - a) * y) < a * f x + (1 - a) * f y :=
    hf.2 (by simp) (by simp) hxy ha0 hb0 hab
  have hineqE :
      (((f (a * x + (1 - a) * y) : ℝ) : EReal)) <
        (((a * f x + (1 - a) * f y : ℝ) : EReal)) := by
    exact_mod_cast hineq
  calc
    (f.toEReal (a • x + (1 - a) • y) : EReal)
        = (((f (a * x + (1 - a) * y) : ℝ) : EReal)) := by
            simp [Function.toEReal_apply, smul_eq_mul]
    _ < (((a * f x + (1 - a) * f y : ℝ) : EReal)) := hineqE
    _ = (a : EReal) * (f.toEReal x : EReal) + (1 - a : EReal) * (f.toEReal y : EReal) := by
          simp [Function.toEReal_apply, EReal.coe_mul, EReal.coe_add]

/-- Helper for Example 9.36: continuity and strict convexity package an everywhere-finite real
function into `Γ₀(ℝ)`. -/
private theorem toEReal_mem_gammaZero_of_continuous
    {f : ℝ → ℝ} (hcont : Continuous f) (hstrict : StrictlyConvex f.toEReal) :
    f.toEReal ∈ Γ₀(ℝ) := by
  rw [mem_gammaZero_iff]
  constructor
  · -- Continuous real formulas remain lower semicontinuous after coercion to `EReal`.
    simpa [Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous
  · refine ⟨?_, subset_rfl, ?_⟩
    -- The coercion `toEReal` is finite at every point.
    rw [Function.effectiveDomain_toEReal]
    exact Set.univ_nonempty
    intro x hx y hy a ha0 ha1
    by_cases hxy : x = y
    · -- For equal endpoints, Jensen's inequality is an equality after collapsing the barycenter.
      subst y
      have hcombo : a • x + (1 - a) • x = x := by
        calc
          a • x + (1 - a) • x = (a + (1 - a)) • x := by rw [add_smul]
          _ = x := by simp
      have ha_nonneg : 0 ≤ (a : EReal) := by
        exact_mod_cast ha0.le
      have hb_nonneg : 0 ≤ ((1 - a : ℝ) : EReal) := by
        exact_mod_cast (sub_nonneg.mpr ha1.le)
      have hsum : (a : EReal) + (1 - a : EReal) = 1 := by
        exact_mod_cast (show a + (1 - a : ℝ) = 1 by ring)
      have hweight :
          (a : EReal) * (f.toEReal x : EReal) + (1 - a : EReal) * (f.toEReal x : EReal) =
            (f.toEReal x : EReal) := by
        calc
          (a : EReal) * (f.toEReal x : EReal) + (1 - a : EReal) * (f.toEReal x : EReal)
              = ((a : EReal) + (1 - a : EReal)) * (f.toEReal x : EReal) := by
                  symm
                  exact EReal.right_distrib_of_nonneg ha_nonneg hb_nonneg
          _ = (f.toEReal x : EReal) := by rw [hsum, one_mul]
      calc
        (f.toEReal (a • x + (1 - a) • x) : EReal) = (f.toEReal x : EReal) := by
          simpa [Function.toEReal_apply] using congrArg (fun t : ℝ ↦ (((f t : ℝ) : EReal))) hcombo
        _ ≤ (a : EReal) * (f.toEReal x : EReal) + (1 - a : EReal) * (f.toEReal x : EReal) := by
          rw [hweight]
    · -- Distinct endpoints use the available strict Jensen inequality.
      exact le_of_lt (hstrict (by simpa using hx) (by simpa using hy) hxy ha0 ha1)

/-- Helper for Example 9.36: the `EReal` interval `]0,+∞[` is the real half-line `(0,+∞)`. -/
private theorem erealOpenInterval_zero_top :
    erealOpenInterval (0 : EReal) ⊤ = Set.Ioi (0 : ℝ) := by
  ext x
  simp [mem_erealOpenInterval_iff]

/-- Helper for Example 9.36: the `EReal` interval `]0,1[` is the real interval `(0,1)`. -/
private theorem erealOpenInterval_zero_one :
    erealOpenInterval (0 : EReal) (1 : EReal) = Set.Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rw [mem_erealOpenInterval_iff] at hx
    exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
  · intro hx
    rw [mem_erealOpenInterval_iff]
    exact ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩

/-- Helper for Example 9.36: for `p > 1`, the real seed `x ↦ |x| ^ p` is strictly convex on
all of `ℝ`. -/
private theorem abs_power_strictConvexOn_univ (p : ℝ) (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  -- Reuse the norm-power argument from Chapter 8 specialized to `ℝ`.
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  by_cases hnorm : |x| = |y|
  · have hy_le : |y| ≤ |x| := by
      simpa [hnorm] using (le_rfl : |y| ≤ |y|)
    have hlt_norm : |a • x + b • y| < |x| := by
      refine norm_combo_lt_of_ne le_rfl ?_ hxy ha hb hab
      simpa [Real.norm_eq_abs] using hy_le
    calc
      |a • x + b • y| ^ p < |x| ^ p :=
        Real.rpow_lt_rpow (abs_nonneg _) hlt_norm (lt_trans zero_lt_one hp)
      _ = a • (|x| ^ p) + b • (|y| ^ p) := by
        rw [hnorm, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]
  · have hle_norm : |a • x + b • y| ≤ a * |x| + b * |y| := by
      calc
        |a • x + b • y| = ‖a * x + b * y‖ := by simp [Real.norm_eq_abs, smul_eq_mul]
        _ ≤ ‖a * x‖ + ‖b * y‖ := norm_add_le _ _
        _ = a * |x| + b * |y| := by
          simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg ha.le, abs_of_nonneg hb.le]
    have hlt_rpow : (a * |x| + b * |y|) ^ p < a * |x| ^ p + b * |y| ^ p := by
      exact (strictConvexOn_rpow hp).2 (by simp) (by simp) (by simpa using hnorm) ha hb
        (by simpa [smul_eq_mul] using hab)
    exact lt_of_le_of_lt (Real.rpow_le_rpow (abs_nonneg _) hle_norm (by positivity))
      (by simpa [smul_eq_mul] using hlt_rpow)

private noncomputable def inversePowerOpenInterval (p : ℝ) : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval (fun x ↦ 1 / x ^ p) 0 ⊤

/-- Helper for Example 9.36: positive inverse powers diverge to `+∞` as `x → 0+`. -/
private theorem inverse_power_tendsto_top_nhdsWithin_zero (p : ℝ) (hp : 0 < p) :
    Filter.Tendsto (fun x : ℝ ↦ ((1 / x ^ p : ℝ) : EReal))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ⊤) := by
  -- Rewrite the inverse power as `x ^ (-p)` on the positive half-line and use the standard
  -- asymptotic for negative exponents.
  have hEq :
      (fun x : ℝ ↦ (1 / x ^ p : ℝ)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun x ↦ x ^ (-p)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro x hx
    calc
      1 / x ^ p = (x ^ p)⁻¹ := by simp [one_div]
      _ = x⁻¹ ^ p := by simpa [one_div] using (Real.inv_rpow hx.le p).symm
      _ = x ^ (-p) := by rw [Real.rpow_neg_eq_inv_rpow]
  have hreal : Filter.Tendsto (fun x : ℝ ↦ x ^ (-p))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    simpa using (tendsto_rpow_neg_nhdsGT_zero (y := -p) (by linarith))
  rw [EReal.tendsto_nhds_top_iff_real]
  intro M
  exact (hreal.congr' hEq.symm).eventually_gt_atTop M |>.mono fun x hx ↦ by exact_mod_cast hx

private theorem inversePowerOpenInterval_zero_liminf_gt_bot (p : ℝ) (x : ℝ)
    (hx : (0 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (inversePowerOpenInterval p y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : 0 = x := by
    exact_mod_cast hx
  subst x
  -- Every right-sided value is a positive real number, so the liminf stays above `⊥`.
  have hnonneg :
      ∀ᶠ y in nhdsWithin (0 : ℝ) (Set.Ioi 0), (0 : EReal) ≤ (inversePowerOpenInterval p y : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    rw [inversePowerOpenInterval, finiteOnOpenInterval, if_pos hy']
    have hpos : 0 < (1 / y ^ p : ℝ) := one_div_pos.mpr (Real.rpow_pos_of_pos hy p)
    have hE : (0 : EReal) ≤ (((1 / y ^ p : ℝ) : EReal)) := by
      exact_mod_cast hpos.le
    simpa using hE
  have hliminf :
      (0 : EReal) ≤ Filter.liminf (fun y : ℝ ↦ (inversePowerOpenInterval p y : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact Filter.le_liminf_of_le
      (f := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (u := fun y : ℝ ↦ (inversePowerOpenInterval p y : EReal))
      (a := (0 : EReal))
      (by isBoundedDefault) hnonneg
  exact lt_of_lt_of_le (show ⊥ < (0 : EReal) by exact EReal.bot_lt_coe 0) hliminf

private theorem liminf_gt_bot_of_eq_top_right
    (g : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) (hx : (⊤ : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (g y : EReal)) (nhdsWithin x (Set.Iio x)) := by
  exact False.elim (EReal.top_ne_coe x hx)

/-- The `]-∞,+∞]`-valued one-sided-limit extension of `x ↦ 1 / x^p` from `(0,+∞)`. -/
noncomputable def inversePowerIoiExtension (p : ℝ) : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension (inversePowerOpenInterval p) 0 ⊤
    (fun {x} hx ↦ inversePowerOpenInterval_zero_liminf_gt_bot p x hx)
    (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (inversePowerOpenInterval p) x hx)

/-- On `(0,+∞)`, `inversePowerIoiExtension p` is given by `x ↦ 1 / x^p`. -/
@[simp] theorem inversePowerIoiExtension_apply_of_pos (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (inversePowerIoiExtension p x : EReal) = ((1 / x ^ p : ℝ) : EReal) := by
  -- Interior points evaluate through the open-interval branch of the extension.
  have hx' : x ∈ erealOpenInterval (0 : EReal) ⊤ := by
    simpa [erealOpenInterval_zero_top] using hx
  rw [inversePowerIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, inversePowerOpenInterval, finiteOnOpenInterval, hx']

/-- For a positive exponent `p`, `inversePowerIoiExtension p` takes the value `+∞` at `0`. -/
@[simp] theorem inversePowerIoiExtension_apply_zero (p : ℝ) (hp : 0 < p) :
    (inversePowerIoiExtension p 0 : EReal) = ⊤ := by
  -- The extension value at `0` is the right-sided `liminf`, which here is `+∞`.
  have hEq :
      (fun y : ℝ ↦ (inversePowerOpenInterval p y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((1 / y ^ p : ℝ) : EReal)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    simp [inversePowerOpenInterval, finiteOnOpenInterval, hy']
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((1 / y ^ p : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊤ : EReal)) :=
    inverse_power_tendsto_top_nhdsWithin_zero p hp
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (inversePowerOpenInterval p y : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) = (⊤ : EReal) :=
    (hEReal.congr' hEq.symm).liminf_eq
  rw [inversePowerIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hliminf]

/-- On `(-∞,0)`, `inversePowerIoiExtension p` takes the value `+∞`. -/
@[simp] theorem inversePowerIoiExtension_apply_of_neg (p : ℝ) {x : ℝ} (hx : x < 0) :
    (inversePowerIoiExtension p x : EReal) = ⊤ := by
  -- Negative points lie outside the interval and are not boundary points.
  have hxmem : x ∉ erealOpenInterval (0 : EReal) ⊤ := by
    intro hxmem
    rw [erealOpenInterval_zero_top] at hxmem
    exact not_lt_of_gt hx hxmem
  have hxzero : ¬ (0 : EReal) = (x : EReal) := by
    exact fun h ↦ (show ¬ (x : EReal) = (0 : EReal) from by exact_mod_cast (ne_of_lt hx)) h.symm
  have hxtop : ¬ (⊤ : EReal) = (x : EReal) := EReal.top_ne_coe x
  rw [inversePowerIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxzero, hxtop]

/-- For a positive exponent `p`, the effective domain of `inversePowerIoiExtension p` is the open
half-line `(0,+∞)`. -/
theorem effectiveDomain_inversePowerIoiExtension (p : ℝ) (hp : 0 < p) :
    effectiveDomain (inversePowerIoiExtension p) = Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hpos : 0 < x
    · exact hpos
    have hxle : x ≤ 0 := le_of_not_gt hpos
    rcases hxle.eq_or_lt with rfl | hneg
    · simpa [mem_effectiveDomain_iff, inversePowerIoiExtension_apply_zero, hp] using hx
    · have htop := inversePowerIoiExtension_apply_of_neg p hneg
      simpa [mem_effectiveDomain_iff, htop] using hx
  · intro hx
    rw [mem_effectiveDomain_iff, inversePowerIoiExtension_apply_of_pos p hx]
    exact EReal.coe_lt_top _

private noncomputable def negPowerOpenInterval (p : ℝ) : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval (fun x ↦ -(x ^ p)) 0 ⊤

private theorem negPowerOpenInterval_zero_liminf_gt_bot (p : ℝ) (hp : 0 < p) (x : ℝ)
    (hx : (0 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (negPowerOpenInterval p y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : 0 = x := by exact_mod_cast hx
  subst x
  -- On the positive side the open-interval model is just the real function `-x^p`.
  have hEq :
      (fun y : ℝ ↦ (negPowerOpenInterval p y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-(y ^ p) : ℝ) : EReal)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    simp [negPowerOpenInterval, finiteOnOpenInterval, hy']
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -(y ^ p)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    -- The exponent `p > 0` makes `x ↦ x^p` continuous at `0`, so the negated power also tends to
    -- `0` from the right.
    have hpow :
        Filter.Tendsto (fun y : ℝ ↦ y ^ p) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
      simpa [Real.zero_rpow hp.ne'] using
        ((Real.continuousAt_rpow_const (x := 0) (q := p) (Or.inr hp.le)).continuousWithinAt.tendsto)
    simpa using (continuous_neg.continuousAt.tendsto.comp hpow)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-(y ^ p) : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  exact boundary_liminf_gt_bot_of_tendsto (by infer_instance) (hEReal.congr' hEq.symm)
    (show ⊥ < (0 : EReal) by exact EReal.bot_lt_coe 0)

/-- For a positive exponent `p`, the `]-∞,+∞]`-valued one-sided-limit extension of
`x ↦ -x^p` from `(0,+∞)`. -/
noncomputable def negPowerIciExtension (p : ℝ) (hp : 0 < p) : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension (negPowerOpenInterval p) 0 ⊤
    (fun {x} hx ↦ negPowerOpenInterval_zero_liminf_gt_bot p hp x hx)
    (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (negPowerOpenInterval p) x hx)

/-- On `(0,+∞)`, `negPowerIciExtension p hp` is given by `x ↦ -x^p`. -/
@[simp] theorem negPowerIciExtension_apply_of_pos (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : 0 < x) :
    (negPowerIciExtension p hp x : EReal) = ((-(x ^ p) : ℝ) : EReal) := by
  -- Interior points evaluate through the open-interval branch of the extension.
  have hx' : x ∈ erealOpenInterval (0 : EReal) ⊤ := by
    simpa [erealOpenInterval_zero_top] using hx
  rw [negPowerIciExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, negPowerOpenInterval, finiteOnOpenInterval, hx']

/-- At `0`, `negPowerIciExtension p hp` takes the value `0`. -/
@[simp] theorem negPowerIciExtension_apply_zero (p : ℝ) (hp : 0 < p) :
    (negPowerIciExtension p hp 0 : EReal) = 0 := by
  -- The extension value at `0` is the right-sided `liminf`, which here is the actual limit `0`.
  have hEq :
      (fun y : ℝ ↦ (negPowerOpenInterval p y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-(y ^ p) : ℝ) : EReal)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    simp [negPowerOpenInterval, finiteOnOpenInterval, hy']
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -(y ^ p)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hpow :
        Filter.Tendsto (fun y : ℝ ↦ y ^ p) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
      simpa [Real.zero_rpow hp.ne'] using
        ((Real.continuousAt_rpow_const (x := 0) (q := p) (Or.inr hp.le)).continuousWithinAt.tendsto)
    simpa using (continuous_neg.continuousAt.tendsto.comp hpow)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-(y ^ p) : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (negPowerOpenInterval p y : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) = (0 : EReal) :=
    (hEReal.congr' hEq.symm).liminf_eq
  rw [negPowerIciExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hliminf]

/-- On `(-∞,0)`, `negPowerIciExtension p hp` takes the value `+∞`. -/
@[simp] theorem negPowerIciExtension_apply_of_neg (p : ℝ) (hp : 0 < p) {x : ℝ} (hx : x < 0) :
    (negPowerIciExtension p hp x : EReal) = ⊤ := by
  -- Negative points lie outside the interval and are not boundary points.
  have hxmem : x ∉ erealOpenInterval (0 : EReal) ⊤ := by
    intro hxmem
    rw [erealOpenInterval_zero_top] at hxmem
    exact not_lt_of_gt hx hxmem
  have hxzero : ¬ (0 : EReal) = (x : EReal) := by
    exact fun h ↦ (show ¬ (x : EReal) = (0 : EReal) from by exact_mod_cast (ne_of_lt hx)) h.symm
  have hxtop : ¬ (⊤ : EReal) = (x : EReal) := EReal.top_ne_coe x
  rw [negPowerIciExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxzero, hxtop]

/-- The effective domain of `negPowerIciExtension p hp` is the closed half-line `[0,+∞)`. -/
theorem effectiveDomain_negPowerIciExtension (p : ℝ) (hp : 0 < p) :
    effectiveDomain (negPowerIciExtension p hp) = Set.Ici (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hpos : 0 < x
    · exact hpos.le
    have hxle : x ≤ 0 := le_of_not_gt hpos
    rcases hxle.eq_or_lt with rfl | hneg
    · simp
    · have htop := negPowerIciExtension_apply_of_neg p hp hneg
      simpa [mem_effectiveDomain_iff, htop] using hx
  · intro hx
    rw [mem_effectiveDomain_iff]
    have hx' : 0 ≤ x := hx
    rcases hx'.eq_or_lt with rfl | hpos
    · simpa [negPowerIciExtension_apply_zero, hp]
    · rw [negPowerIciExtension_apply_of_pos p hp hpos]
      exact EReal.coe_lt_top _

private noncomputable def inverseSqrtOneSubSqOpenInterval : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval (fun x ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) (-1) 1

/-- Helper for Example 9.36: the `EReal` interval `]-1,1[` is the real interval `(-1,1)`. -/
private theorem erealOpenInterval_neg_one_one :
    erealOpenInterval (-1 : EReal) (1 : EReal) = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    rw [mem_erealOpenInterval_iff] at hx
    have hxL' : (((-1 : ℝ) : EReal) < (x : EReal)) := by
      simpa using hx.1
    have hxR' : ((x : EReal) < ((1 : ℝ) : EReal)) := by
      simpa using hx.2
    exact ⟨by exact_mod_cast hxL', by exact_mod_cast hxR'⟩
  · intro hx
    rw [mem_erealOpenInterval_iff]
    have hxL' : (((-1 : ℝ) : EReal) < (x : EReal)) := by
      exact_mod_cast hx.1
    have hxR' : ((x : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast hx.2
    simpa using ⟨hxL', hxR'⟩

/-- Helper for Example 9.36: strict Jensen inequality for the square function. -/
private theorem weighted_square_lt {x y a b : ℝ} (hxy : x ≠ y) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) :
    (a * x + b * y) ^ (2 : ℕ) < a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) := by
  -- Expand the weighted-square gap as a positive multiple of `(x - y)^2`.
  have hb' : b = 1 - a := by
    linarith
  subst b
  have hsq : 0 < (x - y) ^ (2 : ℕ) := by
    rw [sq_pos_iff]
    exact sub_ne_zero.mpr hxy
  have hprod : 0 < a * (1 - a) * (x - y) ^ (2 : ℕ) := by
    positivity
  have hEq :
      a * x ^ (2 : ℕ) + (1 - a) * y ^ (2 : ℕ) -
        (a * x + (1 - a) * y) ^ (2 : ℕ) =
      a * (1 - a) * (x - y) ^ (2 : ℕ) := by
    ring
  nlinarith [hEq, hprod]

/-- Helper for Example 9.36: on positive reals, the inverse square root is the `(-1/2)`-power. -/
private theorem inverse_sqrt_eq_rpow_neg_half {t : ℝ} (ht : 0 < t) :
    1 / Real.sqrt t = t ^ (-(1 : ℝ) / 2) := by
  -- Normalize the inverse square root to the standard `rpow` API.
  calc
    1 / Real.sqrt t = (Real.sqrt t)⁻¹ := by simp [one_div]
    _ = (t ^ ((1 : ℝ) / 2))⁻¹ := by rw [Real.sqrt_eq_rpow]
    _ = t⁻¹ ^ ((1 : ℝ) / 2) := by rw [← Real.inv_rpow ht.le]
    _ = t ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_neg_eq_inv_rpow]
      norm_num

/-- Helper for Example 9.36: the factor `1 - x²` tends to `0+` as `x → -1+`. -/
private theorem one_sub_sq_tendsto_nhdsGT_zero_at_neg_one_right :
    Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  -- Split the target filter into convergence to `0` and eventual positivity.
  have h0' :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (nhds ((fun x : ℝ ↦ 1 - x ^ (2 : ℕ)) (-1))) := by
    have hcont : Continuous (fun x : ℝ ↦ 1 - x ^ (2 : ℕ)) := by
      continuity
    exact hcont.continuousAt.continuousWithinAt.tendsto
  have h0 :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : ℝ)) := by
    simpa using h0'
  have hlt :
      Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
    exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
      (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hpos :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (Filter.principal (Set.Ioi (0 : ℝ))) := by
    rw [Filter.tendsto_principal]
    filter_upwards [hlt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := hx
    change 0 < 1 - x ^ (2 : ℕ)
    nlinarith [hxIoo.1, hxIoo.2]
  change
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
      ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
  exact Filter.tendsto_inf.2 ⟨h0, hpos⟩

/-- Helper for Example 9.36: the factor `1 - x²` tends to `0+` as `x → 1-`. -/
private theorem one_sub_sq_tendsto_nhdsGT_zero_at_one_left :
    Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
  -- The left-endpoint proof is symmetric to the right-endpoint one at `-1`.
  have h0' :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds ((fun x : ℝ ↦ 1 - x ^ (2 : ℕ)) 1)) := by
    have hcont : Continuous (fun x : ℝ ↦ 1 - x ^ (2 : ℕ)) := by
      continuity
    exact hcont.continuousAt.continuousWithinAt.tendsto
  have h0 :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
    simpa using h0'
  have hgt :
      Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
    exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
  have hpos :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Filter.principal (Set.Ioi (0 : ℝ))) := by
    rw [Filter.tendsto_principal]
    filter_upwards [hgt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
    change 0 < 1 - x ^ (2 : ℕ)
    nlinarith [hxIoo.1, hxIoo.2]
  change
    Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      ((nhds (0 : ℝ)) ⊓ Filter.principal (Set.Ioi (0 : ℝ)))
  exact Filter.tendsto_inf.2 ⟨h0, hpos⟩

/-- Helper for Example 9.36: the positive seed `t ↦ t^(-1/2)` is strictly convex on `(0,+∞)`. -/
private theorem inverse_rpow_neg_half_strictConvexOn_Ioi :
    StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun t : ℝ ↦ t ^ (-(1 : ℝ) / 2)) := by
  -- The second derivative is positive on the positive half-line.
  apply strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ))
  · intro t ht
    exact (Real.continuousAt_rpow_const (x := t) (q := (-(1 : ℝ) / 2))
      (Or.inl ht.ne')).continuousWithinAt
  · intro t ht
    rw [Real.iter_deriv_rpow_const (-(1 : ℝ) / 2) t 2]
    have hcoeff :
        0 < Polynomial.eval (-(1 : ℝ) / 2) (descPochhammer ℝ 2) := by
      norm_num [descPochhammer]
    have htpos : 0 < t ^ (-(1 : ℝ) / 2 - (2 : ℝ)) := Real.rpow_pos_of_pos ht _
    exact mul_pos hcoeff htpos

/-- Helper for Example 9.36: the open-interval inverse-square-root model tends to `+∞` at `-1`. -/
private theorem inverseSqrtOneSubSqOpenInterval_tendsto_top_at_neg_one :
    Filter.Tendsto (fun x : ℝ ↦ (inverseSqrtOneSubSqOpenInterval x : EReal))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds ⊤) := by
  -- Near `-1`, the open-interval model agrees with the real formula.
  have hEq :
      Filter.EventuallyEq (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (fun x : ℝ ↦ (inverseSqrtOneSubSqOpenInterval x : EReal))
        (fun x : ℝ ↦ ((1 / Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal)) := by
    have hlt :
        Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
      exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
        (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
    filter_upwards [hlt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := hx
    have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_neg_one_one] using hxIoo
    simp [inverseSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]
  have hReal :
      Filter.Tendsto (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) Filter.atTop := by
    have hrpow :
        Filter.Tendsto (fun x : ℝ ↦ x ^ (-(1 : ℝ) / 2))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      simpa using
        tendsto_rpow_neg_nhdsGT_zero (y := (-(1 : ℝ) / 2)) (by norm_num)
    exact hrpow.comp one_sub_sq_tendsto_nhdsGT_zero_at_neg_one_right
  have hFormula :
      Filter.Tendsto (fun x : ℝ ↦ ((1 / Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds ⊤) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    have hEqReal :
        Filter.EventuallyEq (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
          (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ)))
          (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2)) := by
      have hlt :
          Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
        exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
          (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
      filter_upwards [hlt] with x hx
      have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := hx
      have hpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hxIoo.1, hxIoo.2]
      exact inverse_sqrt_eq_rpow_neg_half hpos
    exact
      (hReal.congr' hEqReal.symm).eventually_gt_atTop M |>.mono fun x hx ↦ by
        exact_mod_cast hx
  exact hFormula.congr' hEq.symm

/-- Helper for Example 9.36: the open-interval inverse-square-root model tends to `+∞` at `1`. -/
private theorem inverseSqrtOneSubSqOpenInterval_tendsto_top_at_one :
    Filter.Tendsto (fun x : ℝ ↦ (inverseSqrtOneSubSqOpenInterval x : EReal))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds ⊤) := by
  -- Near `1`, the open-interval model again agrees with the real formula.
  have hEq :
      Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (fun x : ℝ ↦ (inverseSqrtOneSubSqOpenInterval x : EReal))
        (fun x : ℝ ↦ ((1 / Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal)) := by
    have hgt :
        Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
      exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
        (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
    filter_upwards [hgt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
    have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_neg_one_one] using hxIoo
    simp [inverseSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]
  have hReal :
      Filter.Tendsto (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) Filter.atTop := by
    have hrpow :
        Filter.Tendsto (fun x : ℝ ↦ x ^ (-(1 : ℝ) / 2))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      simpa using
        tendsto_rpow_neg_nhdsGT_zero (y := (-(1 : ℝ) / 2)) (by norm_num)
    exact hrpow.comp one_sub_sq_tendsto_nhdsGT_zero_at_one_left
  have hFormula :
      Filter.Tendsto (fun x : ℝ ↦ ((1 / Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds ⊤) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    have hEqReal :
        Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio 1))
          (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ)))
          (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2)) := by
      have hgt :
          Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
        exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
          (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
      filter_upwards [hgt] with x hx
      have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
      have hpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hxIoo.1, hxIoo.2]
      exact inverse_sqrt_eq_rpow_neg_half hpos
    exact
      (hReal.congr' hEqReal.symm).eventually_gt_atTop M |>.mono fun x hx ↦ by
        exact_mod_cast hx
  exact hFormula.congr' hEq.symm

private theorem inverseSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot (x : ℝ)
    (hx : (-1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (inverseSqrtOneSubSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : x = -1 := by
    have hxE : (((-1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (-1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The explicit `+∞` boundary limit forces the right-sided liminf above `⊥`.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Ioi_neBot le_rfl)
    inverseSqrtOneSubSqOpenInterval_tendsto_top_at_neg_one bot_lt_top

private theorem inverseSqrtOneSubSqOpenInterval_one_liminf_gt_bot (x : ℝ)
    (hx : (1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (inverseSqrtOneSubSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Iio x)) := by
  have hx' : x = 1 := by
    have hxE : (((1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The symmetric `+∞` boundary limit gives the left-sided liminf bound.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Iio_neBot le_rfl)
    inverseSqrtOneSubSqOpenInterval_tendsto_top_at_one bot_lt_top

/-- The `]-∞,+∞]`-valued extension of `x ↦ 1 / √(1 - x^2)` from `(-1,1)` by `+∞` outside that
interval. -/
noncomputable def inverseSqrtOneSubSqFunction : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension inverseSqrtOneSubSqOpenInterval (-1) 1
    (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
    (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

/-- On `(-1,1)`, `inverseSqrtOneSubSqFunction` is given by `x ↦ 1 / √(1 - x^2)`. -/
@[simp] theorem inverseSqrtOneSubSqFunction_apply_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (inverseSqrtOneSubSqFunction x : EReal) =
      ((1 / Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Interior points stay on the open-interval branch of the extension.
  have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [erealOpenInterval_neg_one_one] using hx
  rw [inverseSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, inverseSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]

/-- At `-1`, `inverseSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem inverseSqrtOneSubSqFunction_apply_neg_one :
    (inverseSqrtOneSubSqFunction (-1) : EReal) = ⊤ := by
  -- The boundary branch is exactly the right-sided liminf, which equals `+∞`.
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (inverseSqrtOneSubSqOpenInterval y : EReal))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) = ⊤ := by
    exact inverseSqrtOneSubSqOpenInterval_tendsto_top_at_neg_one.liminf_eq
  have hmem : (-1 : ℝ) ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simp [erealOpenInterval_neg_one_one]
  rw [inverseSqrtOneSubSqFunction, oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal]
  simp [hmem, hliminf]

/-- At `1`, `inverseSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem inverseSqrtOneSubSqFunction_apply_one :
    (inverseSqrtOneSubSqFunction 1 : EReal) = ⊤ := by
  -- The left-sided liminf at `1` is the same `+∞` boundary value.
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (inverseSqrtOneSubSqOpenInterval y : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) = ⊤ := by
    exact inverseSqrtOneSubSqOpenInterval_tendsto_top_at_one.liminf_eq
  have hmem : (1 : ℝ) ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    rw [erealOpenInterval_neg_one_one]
    norm_num
  have hleft : ¬ ((-1 : EReal) = ((1 : ℝ) : EReal)) := by
    intro h
    have h' : (((-1 : ℝ) : EReal) = ((1 : ℝ) : EReal)) := by
      simpa using h
    have : (-1 : ℝ) = 1 := by
      exact_mod_cast h'
    norm_num at this
  have hone : (1 : EReal) = ((1 : ℝ) : EReal) := by
    norm_num
  rw [inverseSqrtOneSubSqFunction, oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal]
  rw [if_neg hmem, if_neg hleft, if_pos hone]
  exact hliminf

/-- On `(-∞,-1)`, `inverseSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem inverseSqrtOneSubSqFunction_apply_of_lt_neg_one {x : ℝ} (hx : x < -1) :
    (inverseSqrtOneSubSqFunction x : EReal) = ⊤ := by
  -- Points strictly left of the interval activate the exterior `+∞` branch.
  have hxmem : x ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_neg_one_one] at hxmem
    exact not_lt_of_gt hx hxmem.1
  have hxnegOne : ¬ (-1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((-1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (-1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  rw [inverseSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxnegOne, hxone]

/-- On `(1,+∞)`, `inverseSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem inverseSqrtOneSubSqFunction_apply_of_one_lt {x : ℝ} (hx : 1 < x) :
    (inverseSqrtOneSubSqFunction x : EReal) = ⊤ := by
  -- Points strictly right of the interval also lie on the exterior branch.
  have hxmem : x ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_neg_one_one] at hxmem
    exact not_lt_of_gt hx hxmem.2
  have hxnegOne : ¬ (-1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((-1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (-1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  rw [inverseSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxnegOne, hxone]

/-- The effective domain of `inverseSqrtOneSubSqFunction` is the open interval `(-1,1)`. -/
theorem effectiveDomain_inverseSqrtOneSubSqFunction :
    effectiveDomain inverseSqrtOneSubSqFunction = Set.Ioo (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    by_cases hxL : x < -1
    · have htop := inverseSqrtOneSubSqFunction_apply_of_lt_neg_one hxL
      simpa [mem_effectiveDomain_iff, htop] using hx
    have hxGe : -1 ≤ x := le_of_not_gt hxL
    by_cases hxR : 1 < x
    · have htop := inverseSqrtOneSubSqFunction_apply_of_one_lt hxR
      simpa [mem_effectiveDomain_iff, htop] using hx
    have hxLe : x ≤ 1 := le_of_not_gt hxR
    rcases eq_or_lt_of_le hxGe with rfl | hxGt
    · have htop := inverseSqrtOneSubSqFunction_apply_neg_one
      simpa [mem_effectiveDomain_iff, htop] using hx
    rcases eq_or_lt_of_le hxLe with rfl | hxLt
    · have htop := inverseSqrtOneSubSqFunction_apply_one
      simpa [mem_effectiveDomain_iff, htop] using hx
    exact ⟨hxGt, hxLt⟩
  · intro hx
    rw [mem_effectiveDomain_iff]
    rw [inverseSqrtOneSubSqFunction_apply_of_mem_Ioo hx]
    exact EReal.coe_lt_top _

private noncomputable def negSqrtOneSubSqOpenInterval : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval (fun x ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) (-1) 1

/-- Helper for Example 9.36: the open-interval negative-square-root model tends to `0` at `-1`. -/
private theorem negSqrtOneSubSqOpenInterval_tendsto_zero_at_neg_one :
    Filter.Tendsto (fun x : ℝ ↦ (negSqrtOneSubSqOpenInterval x : EReal))
      (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : EReal)) := by
  -- Near `-1`, the model agrees with the real square-root formula.
  have hEq :
      Filter.EventuallyEq (nhdsWithin (-1 : ℝ) (Set.Ioi (-1)))
        (fun x : ℝ ↦ (negSqrtOneSubSqOpenInterval x : EReal))
        (fun x : ℝ ↦ ((-Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal)) := by
    have hlt :
        Set.Ioi (-1 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ nhdsWithin (-1 : ℝ) (Set.Ioi (-1)) := by
      exact inter_mem_nhdsWithin (Set.Ioi (-1 : ℝ))
        (Iio_mem_nhds (by norm_num : (-1 : ℝ) < 1))
    filter_upwards [hlt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := hx
    have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_neg_one_one] using hxIoo
    simp [negSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]
  have hZero :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : ℝ)) := by
    exact one_sub_sq_tendsto_nhdsGT_zero_at_neg_one_right.mono_right inf_le_left
  have hFormula :
      Filter.Tendsto (fun x : ℝ ↦ ((-Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : EReal)) := by
    have hSqrt :
        Filter.Tendsto (fun x : ℝ ↦ Real.sqrt (1 - x ^ (2 : ℕ)))
          (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : ℝ)) := by
      simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hZero)
    have hNeg :
        Filter.Tendsto (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ)))
          (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) (nhds (0 : ℝ)) := by
      simpa using hSqrt.neg
    simpa using (continuous_coe_real_ereal.continuousAt.tendsto.comp hNeg)
  exact hFormula.congr' hEq.symm

/-- Helper for Example 9.36: the open-interval negative-square-root model tends to `0` at `1`. -/
private theorem negSqrtOneSubSqOpenInterval_tendsto_zero_at_one :
    Filter.Tendsto (fun x : ℝ ↦ (negSqrtOneSubSqOpenInterval x : EReal))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : EReal)) := by
  -- The left-endpoint argument is symmetric.
  have hEq :
      Filter.EventuallyEq (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (fun x : ℝ ↦ (negSqrtOneSubSqOpenInterval x : EReal))
        (fun x : ℝ ↦ ((-Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal)) := by
    have hgt :
        Set.Iio (1 : ℝ) ∩ Set.Ioi (-1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) := by
      exact inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
        (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 1))
    filter_upwards [hgt] with x hx
    have hxIoo : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨hx.2, hx.1⟩
    have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_neg_one_one] using hxIoo
    simp [negSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]
  have hZero :
      Filter.Tendsto (fun x : ℝ ↦ 1 - x ^ (2 : ℕ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
    exact one_sub_sq_tendsto_nhdsGT_zero_at_one_left.mono_right inf_le_left
  have hFormula :
      Filter.Tendsto (fun x : ℝ ↦ ((-Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : EReal)) := by
    have hSqrt :
        Filter.Tendsto (fun x : ℝ ↦ Real.sqrt (1 - x ^ (2 : ℕ)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
      simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hZero)
    have hNeg :
        Filter.Tendsto (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ)))
          (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
      simpa using hSqrt.neg
    simpa using (continuous_coe_real_ereal.continuousAt.tendsto.comp hNeg)
  exact hFormula.congr' hEq.symm

private theorem negSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot (x : ℝ)
    (hx : (-1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (negSqrtOneSubSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : x = -1 := by
    have hxE : (((-1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (-1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The right-sided limit is the finite value `0`, hence still above `⊥`.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Ioi_neBot le_rfl)
    negSqrtOneSubSqOpenInterval_tendsto_zero_at_neg_one (EReal.bot_lt_coe 0)

private theorem negSqrtOneSubSqOpenInterval_one_liminf_gt_bot (x : ℝ)
    (hx : (1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (negSqrtOneSubSqOpenInterval y : EReal))
      (nhdsWithin x (Set.Iio x)) := by
  have hx' : x = 1 := by
    have hxE : (((1 : ℝ) : EReal) = (x : EReal)) := by
      simpa using hx
    have hxR : (1 : ℝ) = x := by
      exact_mod_cast hxE
    linarith
  subst x
  -- The left-sided limit is the same finite endpoint value `0`.
  exact boundary_liminf_gt_bot_of_tendsto (nhdsWithin_Iio_neBot le_rfl)
    negSqrtOneSubSqOpenInterval_tendsto_zero_at_one (EReal.bot_lt_coe 0)

/-- The `]-∞,+∞]`-valued extension of `x ↦ -√(1 - x^2)` from `[-1,1]` by `+∞` outside that
interval. -/
noncomputable def negSqrtOneSubSqFunction : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension negSqrtOneSubSqOpenInterval (-1) 1
    (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
    (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

/-- On `(-1,1)`, `negSqrtOneSubSqFunction` is given by `x ↦ -√(1 - x^2)`. -/
@[simp] theorem negSqrtOneSubSqFunction_apply_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (negSqrtOneSubSqFunction x : EReal) =
      ((-Real.sqrt (1 - x ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- Interior points use the open-interval branch.
  have hxE : x ∈ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [erealOpenInterval_neg_one_one] using hx
  rw [negSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, negSqrtOneSubSqOpenInterval, finiteOnOpenInterval, hxE]

/-- At `-1`, `negSqrtOneSubSqFunction` takes the value `0`. -/
@[simp] theorem negSqrtOneSubSqFunction_apply_neg_one :
    (negSqrtOneSubSqFunction (-1) : EReal) = 0 := by
  -- The right-sided liminf equals the finite endpoint value `0`.
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (negSqrtOneSubSqOpenInterval y : EReal))
        (nhdsWithin (-1 : ℝ) (Set.Ioi (-1))) = (0 : EReal) := by
    exact negSqrtOneSubSqOpenInterval_tendsto_zero_at_neg_one.liminf_eq
  have hmem : (-1 : ℝ) ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simp [erealOpenInterval_neg_one_one]
  rw [negSqrtOneSubSqFunction, oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal]
  simp [hmem, hliminf]

/-- At `1`, `negSqrtOneSubSqFunction` takes the value `0`. -/
@[simp] theorem negSqrtOneSubSqFunction_apply_one :
    (negSqrtOneSubSqFunction 1 : EReal) = 0 := by
  -- The left-sided liminf gives the symmetric endpoint value.
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (negSqrtOneSubSqOpenInterval y : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) = (0 : EReal) := by
    exact negSqrtOneSubSqOpenInterval_tendsto_zero_at_one.liminf_eq
  have hmem : (1 : ℝ) ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    rw [erealOpenInterval_neg_one_one]
    norm_num
  have hleft : ¬ ((-1 : EReal) = ((1 : ℝ) : EReal)) := by
    intro h
    have h' : (((-1 : ℝ) : EReal) = ((1 : ℝ) : EReal)) := by
      simpa using h
    have : (-1 : ℝ) = 1 := by
      exact_mod_cast h'
    norm_num at this
  have hone : (1 : EReal) = ((1 : ℝ) : EReal) := by
    norm_num
  rw [negSqrtOneSubSqFunction, oneSidedLimitExtension_coe, oneSidedLimitExtensionEReal]
  rw [if_neg hmem, if_neg hleft, if_pos hone]
  exact hliminf

/-- On `(-∞,-1)`, `negSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem negSqrtOneSubSqFunction_apply_of_lt_neg_one {x : ℝ} (hx : x < -1) :
    (negSqrtOneSubSqFunction x : EReal) = ⊤ := by
  -- Exterior points remain on the constant `+∞` branch.
  have hxmem : x ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_neg_one_one] at hxmem
    exact not_lt_of_gt hx hxmem.1
  have hxnegOne : ¬ (-1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((-1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (-1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  rw [negSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxnegOne, hxone]

/-- On `(1,+∞)`, `negSqrtOneSubSqFunction` takes the value `+∞`. -/
@[simp] theorem negSqrtOneSubSqFunction_apply_of_one_lt {x : ℝ} (hx : 1 < x) :
    (negSqrtOneSubSqFunction x : EReal) = ⊤ := by
  -- The same exterior branch applies to points to the right of `1`.
  have hxmem : x ∉ erealOpenInterval (-1 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_neg_one_one] at hxmem
    exact not_lt_of_gt hx hxmem.2
  have hxnegOne : ¬ (-1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((-1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (-1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    exact fun h ↦ by
      have h' : (((1 : ℝ) : EReal) = (x : EReal)) := by
        simpa using h
      have : (1 : ℝ) = x := by
        exact_mod_cast h'
      linarith
  rw [negSqrtOneSubSqFunction, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxnegOne, hxone]

/-- The effective domain of `negSqrtOneSubSqFunction` is the closed interval `[-1,1]`. -/
theorem effectiveDomain_negSqrtOneSubSqFunction :
    effectiveDomain negSqrtOneSubSqFunction = Set.Icc (-1 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    by_cases hxL : x < -1
    · have htop := negSqrtOneSubSqFunction_apply_of_lt_neg_one hxL
      simpa [mem_effectiveDomain_iff, htop] using hx
    have hxGe : -1 ≤ x := le_of_not_gt hxL
    by_cases hxR : 1 < x
    · have htop := negSqrtOneSubSqFunction_apply_of_one_lt hxR
      simpa [mem_effectiveDomain_iff, htop] using hx
    have hxLe : x ≤ 1 := le_of_not_gt hxR
    exact ⟨hxGe, hxLe⟩
  · intro hx
    rw [mem_effectiveDomain_iff]
    rcases eq_or_lt_of_le hx.1 with rfl | hxGt
    · simpa [negSqrtOneSubSqFunction_apply_neg_one]
    rcases eq_or_lt_of_le hx.2 with rfl | hxLt
    · simpa [negSqrtOneSubSqFunction_apply_one]
    rw [negSqrtOneSubSqFunction_apply_of_mem_Ioo ⟨hxGt, hxLt⟩]
    exact EReal.coe_lt_top _

private noncomputable def binaryEntropyOpenInterval : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval
    (fun x ↦ x * Real.log x + (1 - x) * Real.log (1 - x))
    0 1

/-- Helper for Example 9.36: the logarithmic entropy seed is exactly `-Real.binEntropy`. -/
private theorem binary_entropy_seed_eq_neg_binEntropy (x : ℝ) :
    x * Real.log x + (1 - x) * Real.log (1 - x) = -Real.binEntropy x := by
  -- Normalize the raw formula to the canonical entropy API from mathlib.
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_eq_neg]
  ring

private theorem binaryEntropyOpenInterval_zero_liminf_gt_bot (x : ℝ)
    (hx : (0 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : 0 = x := by
    exact_mod_cast hx
  subst x
  -- Near `0` inside `(0,1)`, the open-interval model is `-Real.binEntropy`, which tends to `0`.
  have hEq :
      (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal)) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := hy
    have hyE : y ∈ erealOpenInterval (0 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_zero_one] using hy'
    simpa [binaryEntropyOpenInterval, finiteOnOpenInterval, hyE,
      binary_entropy_seed_eq_neg_binEntropy]
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.binEntropy y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    simpa using
      (((Real.binEntropy_continuous.neg).continuousAt : ContinuousAt (fun y : ℝ ↦ -Real.binEntropy y)
        0).continuousWithinAt.tendsto)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  exact boundary_liminf_gt_bot_of_tendsto (by infer_instance) (hEReal.congr' hEq.symm)
    (show ⊥ < (0 : EReal) by exact EReal.bot_lt_coe 0)

private theorem binaryEntropyOpenInterval_one_liminf_gt_bot (x : ℝ)
    (hx : (1 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal))
      (nhdsWithin x (Set.Iio x)) := by
  have hx' : 1 = x := by
    exact_mod_cast hx
  subst x
  -- Near `1` inside `(0,1)`, the same entropy normalization reduces the limit to continuity at `1`.
  have hEq :
      (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal)) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)]
        (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal)) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy.2, hy.1⟩
    have hyE : y ∈ erealOpenInterval (0 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_zero_one] using hy'
    simpa [binaryEntropyOpenInterval, finiteOnOpenInterval, hyE,
      binary_entropy_seed_eq_neg_binEntropy]
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.binEntropy y)
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
    simpa using
      (((Real.binEntropy_continuous.neg).continuousAt : ContinuousAt (fun y : ℝ ↦ -Real.binEntropy y)
        1).continuousWithinAt.tendsto)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  exact boundary_liminf_gt_bot_of_tendsto (by infer_instance) (hEReal.congr' hEq.symm)
    (show ⊥ < (0 : EReal) by exact EReal.bot_lt_coe 0)

/-- The `]-∞,+∞]`-valued binary entropy integrand:
it equals `x log x + (1 - x) log(1 - x)` on `(0,1)`, equals `0` at `0` and `1`, and equals `+∞`
outside `[0,1]`. -/
noncomputable def binaryEntropy : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension binaryEntropyOpenInterval 0 1
    (fun {x} hx ↦ binaryEntropyOpenInterval_zero_liminf_gt_bot x hx)
    (fun {x} hx ↦ binaryEntropyOpenInterval_one_liminf_gt_bot x hx)

/-- On `(0,1)`, `binaryEntropy` is given by `x log x + (1 - x) log(1 - x)`. -/
@[simp] theorem binaryEntropy_apply_of_mem_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (binaryEntropy x : EReal) =
      ((x * Real.log x + (1 - x) * Real.log (1 - x) : ℝ) : EReal) := by
  -- Interior points evaluate through the open-interval branch of the extension.
  have hx' : x ∈ erealOpenInterval (0 : EReal) (1 : EReal) := by
    simpa [erealOpenInterval_zero_one] using hx
  rw [binaryEntropy, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, binaryEntropyOpenInterval, finiteOnOpenInterval, hx']

/-- At `0`, `binaryEntropy` takes the value `0`. -/
@[simp] theorem binaryEntropy_apply_zero :
    (binaryEntropy 0 : EReal) = 0 := by
  -- The extension value at `0` is the right-sided `liminf`, which here is the actual limit `0`.
  have hEq :
      (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal)) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ))
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := hy
    have hyE : y ∈ erealOpenInterval (0 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_zero_one] using hy'
    simpa [binaryEntropyOpenInterval, finiteOnOpenInterval, hyE,
      binary_entropy_seed_eq_neg_binEntropy]
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.binEntropy y)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by
    simpa using
      (((Real.binEntropy_continuous.neg).continuousAt : ContinuousAt (fun y : ℝ ↦ -Real.binEntropy y)
        0).continuousWithinAt.tendsto)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) = (0 : EReal) :=
    (hEReal.congr' hEq.symm).liminf_eq
  rw [binaryEntropy, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hliminf]

/-- At `1`, `binaryEntropy` takes the value `0`. -/
@[simp] theorem binaryEntropy_apply_one :
    (binaryEntropy 1 : EReal) = 0 := by
  -- The extension value at `1` is the left-sided `liminf`, which again equals `0`.
  have hEq :
      (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal)) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio 1)]
        (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal)) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Iio (1 : ℝ))
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with y hy
    have hy' : y ∈ Set.Ioo (0 : ℝ) 1 := ⟨hy.2, hy.1⟩
    have hyE : y ∈ erealOpenInterval (0 : EReal) (1 : EReal) := by
      simpa [erealOpenInterval_zero_one] using hy'
    simpa [binaryEntropyOpenInterval, finiteOnOpenInterval, hyE,
      binary_entropy_seed_eq_neg_binEntropy]
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.binEntropy y)
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : ℝ)) := by
    simpa using
      (((Real.binEntropy_continuous.neg).continuousAt : ContinuousAt (fun y : ℝ ↦ -Real.binEntropy y)
        1).continuousWithinAt.tendsto)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.binEntropy y : ℝ) : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (0 : EReal)) := by
    simpa using
      (((continuous_coe_real_ereal.continuousAt : ContinuousAt ((↑) : ℝ → EReal) 0).tendsto).comp
        hreal)
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (binaryEntropyOpenInterval y : EReal))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) = (0 : EReal) :=
    (hEReal.congr' hEq.symm).liminf_eq
  rw [binaryEntropy, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hliminf]

/-- On `(-∞,0)`, `binaryEntropy` takes the value `+∞`. -/
@[simp] theorem binaryEntropy_apply_of_lt_zero {x : ℝ} (hx : x < 0) :
    (binaryEntropy x : EReal) = ⊤ := by
  -- Points strictly left of `0` lie outside the interval and are not boundary points.
  have hxmem : x ∉ erealOpenInterval (0 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_zero_one] at hxmem
    exact not_lt_of_gt hx hxmem.1
  have hxzero : ¬ (0 : EReal) = (x : EReal) := by
    exact fun h ↦ (show ¬ (x : EReal) = (0 : EReal) from by exact_mod_cast (ne_of_lt hx)) h.symm
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    intro h
    have hx' : (1 : ℝ) = x := by
      exact_mod_cast h
    linarith
  rw [binaryEntropy, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxzero, hxone]

/-- On `(1,+∞)`, `binaryEntropy` takes the value `+∞`. -/
@[simp] theorem binaryEntropy_apply_of_one_lt {x : ℝ} (hx : 1 < x) :
    (binaryEntropy x : EReal) = ⊤ := by
  -- Points strictly right of `1` lie outside the interval and are not boundary points.
  have hxmem : x ∉ erealOpenInterval (0 : EReal) (1 : EReal) := by
    intro hxmem
    rw [erealOpenInterval_zero_one] at hxmem
    exact not_lt_of_gt hx hxmem.2
  have hxzero : ¬ (0 : EReal) = (x : EReal) := by
    intro h
    have hx' : (0 : ℝ) = x := by
      exact_mod_cast h
    linarith
  have hxone : ¬ (1 : EReal) = (x : EReal) := by
    exact fun h ↦ (show ¬ (x : EReal) = (1 : EReal) from by exact_mod_cast (ne_of_gt hx)) h.symm
  rw [binaryEntropy, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxzero, hxone]

/-- The effective domain of `binaryEntropy` is the closed interval `[0,1]`. -/
theorem effectiveDomain_binaryEntropy :
    effectiveDomain binaryEntropy = Set.Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    by_cases hx0 : x < 0
    · have htop := binaryEntropy_apply_of_lt_zero hx0
      simpa [mem_effectiveDomain_iff, htop] using hx
    by_cases hx1 : 1 < x
    · have htop := binaryEntropy_apply_of_one_lt hx1
      simpa [mem_effectiveDomain_iff, htop] using hx
    exact ⟨le_of_not_gt hx0, le_of_not_gt hx1⟩
  · intro hx
    rw [mem_effectiveDomain_iff]
    rcases hx with ⟨hx0, hx1⟩
    rcases eq_or_lt_of_le hx0 with rfl | hx0'
    · simpa [binaryEntropy_apply_zero]
    rcases eq_or_lt_of_le hx1 with rfl | hx1'
    · simpa [binaryEntropy_apply_one]
    · rw [binaryEntropy_apply_of_mem_Ioo ⟨hx0', hx1'⟩]
      exact EReal.coe_lt_top _

private noncomputable def negLogOpenInterval : ℝ → Set.Ioi (⊥ : EReal) :=
  finiteOnOpenInterval (fun x ↦ -Real.log x) 0 ⊤

private theorem negLogOpenInterval_zero_liminf_gt_bot (x : ℝ)
    (hx : (0 : EReal) = (x : EReal)) :
    ⊥ < Filter.liminf (fun y : ℝ ↦ (negLogOpenInterval y : EReal))
      (nhdsWithin x (Set.Ioi x)) := by
  have hx' : 0 = x := by exact_mod_cast hx
  subst x
  -- On the positive side the open-interval model is exactly the real function `-log`.
  have hEq :
      (fun y : ℝ ↦ (negLogOpenInterval y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-Real.log y : ℝ) : EReal)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    simp [negLogOpenInterval, finiteOnOpenInterval, hy']
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.log y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    simpa [neg_mul] using Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (by norm_num : (-1 : ℝ) < 0)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.log y : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    exact (hreal.eventually_gt_atTop M).mono fun y hy ↦ by exact_mod_cast hy
  exact boundary_liminf_gt_bot_of_tendsto (by infer_instance) (hEReal.congr' hEq.symm) bot_lt_top

/-- The `]-∞,+∞]`-valued extension of `x ↦ - log x` from `(0,+∞)` by `+∞` on `(-∞,0]`. -/
noncomputable def negLogIoiExtension : ℝ → Set.Ioi (⊥ : EReal) :=
  oneSidedLimitExtension negLogOpenInterval 0 ⊤
    (fun {x} hx ↦ negLogOpenInterval_zero_liminf_gt_bot x hx)
    (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right negLogOpenInterval x hx)

/-- On `(0,+∞)`, `negLogIoiExtension` is given by `x ↦ - log x`. -/
@[simp] theorem negLogIoiExtension_apply_of_pos {x : ℝ} (hx : 0 < x) :
    (negLogIoiExtension x : EReal) = ((-Real.log x : ℝ) : EReal) := by
  -- Interior points evaluate through the positive branch of the extension.
  have hx' : x ∈ erealOpenInterval (0 : EReal) ⊤ := by
    simpa [erealOpenInterval_zero_top] using hx
  rw [negLogIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, negLogOpenInterval, finiteOnOpenInterval, hx']

/-- At `0`, `negLogIoiExtension` takes the value `+∞`. -/
@[simp] theorem negLogIoiExtension_apply_zero :
    (negLogIoiExtension 0 : EReal) = ⊤ := by
  -- The extension value at `0` is the right-sided `liminf`, which here is `+∞`.
  have hEq :
      (fun y : ℝ ↦ (negLogOpenInterval y : EReal)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun y : ℝ ↦ ((-Real.log y : ℝ) : EReal)) := by
    apply eventuallyEq_nhdsWithin_of_eqOn
    intro y hy
    have hy' : y ∈ erealOpenInterval (0 : EReal) ⊤ := by
      simpa [erealOpenInterval_zero_top] using hy
    simp [negLogOpenInterval, finiteOnOpenInterval, hy']
  have hreal :
      Filter.Tendsto (fun y : ℝ ↦ -Real.log y) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    simpa [neg_mul] using Real.tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg (by norm_num : (-1 : ℝ) < 0)
  have hEReal :
      Filter.Tendsto (fun y : ℝ ↦ ((-Real.log y : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro M
    exact (hreal.eventually_gt_atTop M).mono fun y hy ↦ by exact_mod_cast hy
  have hliminf :
      Filter.liminf (fun y : ℝ ↦ (negLogOpenInterval y : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) = (⊤ : EReal) :=
    (hEReal.congr' hEq.symm).liminf_eq
  rw [negLogIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hliminf]

/-- On `(-∞,0)`, `negLogIoiExtension` takes the value `+∞`. -/
@[simp] theorem negLogIoiExtension_apply_of_neg {x : ℝ} (hx : x < 0) :
    (negLogIoiExtension x : EReal) = ⊤ := by
  -- Negative points lie outside the interval and are not boundary points.
  have hxmem : x ∉ erealOpenInterval (0 : EReal) ⊤ := by
    intro hxmem
    rw [erealOpenInterval_zero_top] at hxmem
    exact not_lt_of_gt hx hxmem
  have hxzero : ¬ (0 : EReal) = (x : EReal) := by
    exact fun h ↦ (show ¬ (x : EReal) = (0 : EReal) from by exact_mod_cast (ne_of_lt hx)) h.symm
  have hxtop : ¬ (⊤ : EReal) = (x : EReal) := EReal.top_ne_coe x
  rw [negLogIoiExtension, oneSidedLimitExtension_coe]
  simp [oneSidedLimitExtensionEReal, hxmem, hxzero, hxtop]

/-- The effective domain of `negLogIoiExtension` is the open half-line `(0,+∞)`. -/
theorem effectiveDomain_negLogIoiExtension :
    effectiveDomain negLogIoiExtension = Set.Ioi (0 : ℝ) := by
  ext x
  constructor
  · intro hx
    by_cases hpos : 0 < x
    · exact hpos
    have hxle : x ≤ 0 := le_of_not_gt hpos
    rcases hxle.eq_or_lt with rfl | hneg
    · simpa [mem_effectiveDomain_iff, negLogIoiExtension_apply_zero] using hx
    · have htop := negLogIoiExtension_apply_of_neg hneg
      simpa [mem_effectiveDomain_iff, htop] using hx
  · intro hx
    rw [mem_effectiveDomain_iff, negLogIoiExtension_apply_of_pos hx]
    exact EReal.coe_lt_top _

-- Proof sketch: apply the one-dimensional derivative criterion from Proposition 8.14 to
-- `Real.exp`, whose derivative is itself and hence strictly increasing, then combine the resulting
-- strict convexity with lower semicontinuity to package the function into `Γ₀(ℝ)`.
/-- The everywhere-finite exponential function is strictly convex. -/
theorem exp_strictlyConvex :
    StrictlyConvex Real.exp.toEReal := by
  -- The real exponential is already strictly convex on all of `ℝ`.
  exact strictlyConvex_toEReal_of_strictConvexOn_univ strictConvexOn_exp

-- Proof sketch: combine `exp_strictlyConvex` with the continuity of `Real.exp`, viewed through
-- the canonical bridge `Real.exp.toEReal`.
/-- Example 9.36 (i): the everywhere-finite exponential function belongs to `Γ₀(ℝ)`. -/
theorem exp_mem_gammaZero :
    Real.exp.toEReal ∈ Γ₀(ℝ) := by
  -- Package the continuous real formula together with the strict-convexity bridge.
  exact toEReal_mem_gammaZero_of_continuous Real.continuous_exp exp_strictlyConvex

-- Proof sketch: on `ℝ`, the real-valued function `x ↦ |x|^p` is strictly convex for `p > 1` by
-- the power-function criterion from Proposition 8.14 and the convexity facts recorded earlier in
-- Chapter 8; coercing to `EReal` keeps the function finite everywhere, so it belongs to
-- `Γ₀(ℝ)`.
/-- For `p > 1`, the everywhere-finite power function `x ↦ |x|^p` is strictly convex. -/
theorem absPower_strictlyConvex (p : ℝ) (hp : 1 < p) :
    StrictlyConvex (fun x ↦ |x| ^ p).toEReal := by
  -- Transfer the real strict-convexity seed to the everywhere-finite `EReal` model.
  exact strictlyConvex_toEReal_of_strictConvexOn_univ (abs_power_strictConvexOn_univ p hp)

-- Proof sketch: combine `absPower_strictlyConvex p hp` with lower semicontinuity of the real
-- formula `x ↦ |x|^p`, viewed as `(fun x ↦ |x| ^ p).toEReal`.
/-- Example 9.36 (ii): for `p > 1`, the everywhere-finite power function `x ↦ |x|^p` belongs to
`Γ₀(ℝ)`. -/
theorem absPower_mem_gammaZero (p : ℝ) (hp : 1 < p) :
    (fun x ↦ |x| ^ p).toEReal ∈ Γ₀(ℝ) := by
  -- Package the continuous real formula together with the strict-convexity bridge.
  have hcont : Continuous (fun x : ℝ ↦ |x| ^ p) := by
    have hp0 : 0 ≤ p := le_of_lt (lt_trans zero_lt_one hp)
    simpa using (continuous_abs.rpow_const fun _ => Or.inr hp0)
  exact toEReal_mem_gammaZero_of_continuous hcont (absPower_strictlyConvex p hp)

-- Proof sketch: first show that `x ↦ 1 / x^p` is strictly convex on `(0,+∞)` when `p ≥ 1` by the
-- derivative test from Proposition 8.14. Then identify the corresponding positive-exponent
-- one-sided-limit extension from Proposition 9.34 with left endpoint `0` and right endpoint
-- `+∞`, which yields both strict convexity and membership in `Γ₀(ℝ)`.
/-- For `p ≥ 1`, the function equal to `1 / x^p` on `(0,+∞)` and to `+∞` on `(-∞,0]` is strictly
convex. -/
theorem inversePowerIoiExtension_strictlyConvex (p : ℝ) (hp : 1 ≤ p) :
    StrictlyConvex (inversePowerIoiExtension p) := by
  -- Route correction: prove strict convexity on `(0,+∞)` first, then transfer it through the
  -- one-sided-limit extension from Proposition 9.34.
  have hseedIoi : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x ^ p) := by
    have hpow : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x ^ (-p)) := by
      -- A positive second derivative gives the strict-convexity seed on the positive half-line.
      apply strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ))
      · intro x hx
        exact (Real.continuousAt_rpow_const (x := x) (q := -p) (Or.inl hx.ne')).continuousWithinAt
      · intro x hx
        rw [Real.iter_deriv_rpow_const (-p) x 2]
        have hcoeff : 0 < Polynomial.eval (-p) (descPochhammer ℝ 2) := by
          norm_num [descPochhammer]
          nlinarith
        have hpowx : 0 < x ^ (-p - (2 : ℝ)) := Real.rpow_pos_of_pos hx _
        exact mul_pos hcoeff hpowx
    exact hpow.congr fun x hx ↦ by
      calc
        x ^ (-p) = x⁻¹ ^ p := by rw [Real.rpow_neg_eq_inv_rpow]
        _ = (x ^ p)⁻¹ := by simpa [one_div] using (Real.inv_rpow hx.le p)
        _ = 1 / x ^ p := by simp [one_div]
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ 1 / x ^ p) := by
    simpa [erealOpenInterval_zero_top] using hseedIoi
  have hdom :
      effectiveDomain (inversePowerOpenInterval p) = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [inversePowerOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ 1 / x ^ p) (0 : EReal) ⊤
  have hstrict : StrictlyConvex (inversePowerOpenInterval p) :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [inversePowerIoiExtension] using
    oneSidedLimitExtension_strictlyConvex (g := inversePowerOpenInterval p) (α := (0 : EReal))
      (β := ⊤) (by simp) hdom hstrict
      (fun {x} hx ↦ inversePowerOpenInterval_zero_liminf_gt_bot p x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (inversePowerOpenInterval p) x hx)

-- Proof sketch: apply Proposition 9.34 to the strictly convex open-interval model from
-- `inversePowerIoiExtension_strictlyConvex p hp`.
/-- Example 9.36 (iii): for `p ≥ 1`, the function equal to `1 / x^p` on `(0,+∞)` and to `+∞` on
`(-∞,0]` belongs to `Γ₀(ℝ)`. -/
theorem inversePowerIoiExtension_mem_gammaZero (p : ℝ) (hp : 1 ≤ p) :
    inversePowerIoiExtension p ∈ Γ₀(ℝ) := by
  have hseedIoi : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x ^ p) := by
    have hpow : StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ x ^ (-p)) := by
      -- The positive half-line seed is the same second-derivative computation used above.
      apply strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ))
      · intro x hx
        exact (Real.continuousAt_rpow_const (x := x) (q := -p) (Or.inl hx.ne')).continuousWithinAt
      · intro x hx
        rw [Real.iter_deriv_rpow_const (-p) x 2]
        have hcoeff : 0 < Polynomial.eval (-p) (descPochhammer ℝ 2) := by
          norm_num [descPochhammer]
          nlinarith
        have hpowx : 0 < x ^ (-p - (2 : ℝ)) := Real.rpow_pos_of_pos hx _
        exact mul_pos hcoeff hpowx
    exact hpow.congr fun x hx ↦ by
      calc
        x ^ (-p) = x⁻¹ ^ p := by rw [Real.rpow_neg_eq_inv_rpow]
        _ = (x ^ p)⁻¹ := by simpa [one_div] using (Real.inv_rpow hx.le p)
        _ = 1 / x ^ p := by simp [one_div]
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ 1 / x ^ p) := by
    simpa [erealOpenInterval_zero_top] using hseedIoi
  have hdom :
      effectiveDomain (inversePowerOpenInterval p) = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [inversePowerOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ 1 / x ^ p) (0 : EReal) ⊤
  have hstrict : StrictlyConvex (inversePowerOpenInterval p) :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [inversePowerIoiExtension] using
    oneSidedLimitExtension_mem_gammaZero (g := inversePowerOpenInterval p) (α := (0 : EReal))
      (β := ⊤) (by simp) hdom hstrict
      (fun {x} hx ↦ inversePowerOpenInterval_zero_liminf_gt_bot p x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (inversePowerOpenInterval p) x hx)

-- Proof sketch: the real-valued function `x ↦ -x^p` is strictly convex on `(0,+∞)` for
-- `0 < p < 1` by Proposition 8.14. Extending it by `+∞` on the negative half-line is again a
-- one-sided-limit extension, so Proposition 9.34 yields the `Γ₀(ℝ)` and strict-convexity claims.
/-- For `0 < p < 1`, the function equal to `-x^p` on `[0,+∞)` and to `+∞` on `(-∞,0)` is
strictly convex. -/
theorem negPowerIciExtension_strictlyConvex (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictlyConvex (negPowerIciExtension p hp0) := by
  -- Route correction: use the strict convexity of the real seed on `(0,+∞)` and then transfer it
  -- through Proposition 9.34's one-sided-limit extension.
  have hseed : StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ -(x ^ p)) := by
    simpa [erealOpenInterval_zero_top] using
      show StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(x ^ p)) from
        (Real.strictConcaveOn_rpow hp0 hp1).neg.subset Set.Ioi_subset_Ici_self (convex_Ioi (0 : ℝ))
  have hdom :
      effectiveDomain (negPowerOpenInterval p) = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [negPowerOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ -(x ^ p)) (0 : EReal) ⊤
  have hstrict : StrictlyConvex (negPowerOpenInterval p) :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [negPowerIciExtension] using
    oneSidedLimitExtension_strictlyConvex (g := negPowerOpenInterval p) (α := (0 : EReal))
      (β := ⊤) (by simp) hdom hstrict
      (fun {x} hx ↦ negPowerOpenInterval_zero_liminf_gt_bot p hp0 x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (negPowerOpenInterval p) x hx)

-- Proof sketch: apply Proposition 9.34 to the open-interval model underlying
-- `negPowerIciExtension p hp0`.
/-- Example 9.36 (iv): for `0 < p < 1`, the function equal to `-x^p` on `[0,+∞)` and to `+∞` on
`(-∞,0)` belongs to `Γ₀(ℝ)`. -/
theorem negPowerIciExtension_mem_gammaZero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    negPowerIciExtension p hp0 ∈ Γ₀(ℝ) := by
  have hseed : StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ -(x ^ p)) := by
    simpa [erealOpenInterval_zero_top] using
      show StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -(x ^ p)) from
        (Real.strictConcaveOn_rpow hp0 hp1).neg.subset Set.Ioi_subset_Ici_self (convex_Ioi (0 : ℝ))
  have hdom :
      effectiveDomain (negPowerOpenInterval p) = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [negPowerOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ -(x ^ p)) (0 : EReal) ⊤
  have hstrict : StrictlyConvex (negPowerOpenInterval p) :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [negPowerIciExtension] using
    oneSidedLimitExtension_mem_gammaZero (g := negPowerOpenInterval p) (α := (0 : EReal))
      (β := ⊤) (by simp) hdom hstrict
      (fun {x} hx ↦ negPowerOpenInterval_zero_liminf_gt_bot p hp0 x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right (negPowerOpenInterval p) x hx)

-- Proof sketch: on `(-1,1)`, the real-valued function `x ↦ 1 / √(1 - x^2)` is strictly convex by
-- the derivative criterion from Proposition 8.14. The boundary values blow up to `+∞` at `±1`,
-- so Proposition 9.34 applies on the interval `(-1,1)` and gives the extension result.
/-- The function equal to `1 / √(1 - x^2)` on `(-1,1)` and to `+∞` outside `[-1,1]` is strictly
convex. -/
theorem inverseSqrtOneSubSqFunction_strictlyConvex :
    StrictlyConvex inverseSqrtOneSubSqFunction := by
  -- Route correction: prove the real seed on `(-1,1)` directly, then transfer it through
  -- Proposition 9.34's one-sided-limit extension.
  have hseedIoo :
      StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) := by
    have hseedRpow :
        StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
          (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2)) := by
      refine ⟨convex_Ioo (-1 : ℝ) 1, ?_⟩
      intro x hx y hy hxy a b ha hb hab
      -- Strict convexity of `x ↦ x²` makes the inner factor strictly larger at the midpoint.
      have hmix : a * x + b * y ∈ Set.Ioo (-1 : ℝ) 1 :=
        (convex_Ioo (-1 : ℝ) 1) hx hy ha.le hb.le hab
      have hxpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hx.1, hx.2]
      have hypos : 0 < 1 - y ^ (2 : ℕ) := by
        nlinarith [hy.1, hy.2]
      have hmpos : 0 < 1 - (a * x + b * y) ^ (2 : ℕ) := by
        nlinarith [hmix.1, hmix.2]
      have hsquare :
          (a * x + b * y) ^ (2 : ℕ) < a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) :=
        weighted_square_lt hxy ha hb hab
      have hinner :
          a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) <
            1 - (a * x + b * y) ^ (2 : ℕ) := by
        nlinarith
      have hauvpos :
          0 < a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) := by
        positivity
      have hanti := Real.strictAntiOn_rpow_Ioi_of_exponent_neg
        (show (-(1 : ℝ) / 2) < 0 by norm_num)
      have hmono :
          (1 - (a * x + b * y) ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) <
            (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) ^ (-(1 : ℝ) / 2) :=
        hanti hauvpos hmpos hinner
      have hconv :
          (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) ^ (-(1 : ℝ) / 2) ≤
            a * (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) +
              b * (1 - y ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) :=
        inverse_rpow_neg_half_strictConvexOn_Ioi.convexOn.2 hxpos hypos ha.le hb.le hab
      exact lt_of_lt_of_le hmono hconv
    exact hseedRpow.congr fun x hx ↦ by
      have hpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hx.1, hx.2]
      symm
      exact inverse_sqrt_eq_rpow_neg_half hpos
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (-1 : EReal) (1 : EReal))
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) := by
    simpa [erealOpenInterval_neg_one_one] using hseedIoo
  have hdom :
      effectiveDomain inverseSqrtOneSubSqOpenInterval =
        erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [inverseSqrtOneSubSqOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) (-1 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex inverseSqrtOneSubSqOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  have hαβ : (-1 : EReal) < (1 : EReal) := by
    have hαβ' : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast (show (-1 : ℝ) < 1 by norm_num)
    simpa using hαβ'
  simpa [inverseSqrtOneSubSqFunction] using
    oneSidedLimitExtension_strictlyConvex (g := inverseSqrtOneSubSqOpenInterval)
      (α := (-1 : EReal)) (β := (1 : EReal)) hαβ hdom hstrict
      (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
      (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: apply Proposition 9.34 on the interval `(-1,1)`.
/-- Example 9.36 (v): the function equal to `1 / √(1 - x^2)` on `(-1,1)` and to `+∞` outside
`[-1,1]` belongs to `Γ₀(ℝ)`. -/
theorem inverseSqrtOneSubSqFunction_mem_gammaZero :
    inverseSqrtOneSubSqFunction ∈ Γ₀(ℝ) := by
  have hseedIoo :
      StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) := by
    have hseedRpow :
        StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
          (fun x : ℝ ↦ (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2)) := by
      refine ⟨convex_Ioo (-1 : ℝ) 1, ?_⟩
      intro x hx y hy hxy a b ha hb hab
      -- The same strict-inner-gap argument yields the seed strict convexity.
      have hmix : a * x + b * y ∈ Set.Ioo (-1 : ℝ) 1 :=
        (convex_Ioo (-1 : ℝ) 1) hx hy ha.le hb.le hab
      have hxpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hx.1, hx.2]
      have hypos : 0 < 1 - y ^ (2 : ℕ) := by
        nlinarith [hy.1, hy.2]
      have hmpos : 0 < 1 - (a * x + b * y) ^ (2 : ℕ) := by
        nlinarith [hmix.1, hmix.2]
      have hsquare :
          (a * x + b * y) ^ (2 : ℕ) < a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) :=
        weighted_square_lt hxy ha hb hab
      have hinner :
          a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) <
            1 - (a * x + b * y) ^ (2 : ℕ) := by
        nlinarith
      have hauvpos :
          0 < a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) := by
        positivity
      have hanti := Real.strictAntiOn_rpow_Ioi_of_exponent_neg
        (show (-(1 : ℝ) / 2) < 0 by norm_num)
      have hmono :
          (1 - (a * x + b * y) ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) <
            (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) ^ (-(1 : ℝ) / 2) :=
        hanti hauvpos hmpos hinner
      have hconv :
          (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) ^ (-(1 : ℝ) / 2) ≤
            a * (1 - x ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) +
              b * (1 - y ^ (2 : ℕ)) ^ (-(1 : ℝ) / 2) :=
        inverse_rpow_neg_half_strictConvexOn_Ioi.convexOn.2 hxpos hypos ha.le hb.le hab
      exact lt_of_lt_of_le hmono hconv
    exact hseedRpow.congr fun x hx ↦ by
      have hpos : 0 < 1 - x ^ (2 : ℕ) := by
        nlinarith [hx.1, hx.2]
      symm
      exact inverse_sqrt_eq_rpow_neg_half hpos
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (-1 : EReal) (1 : EReal))
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) := by
    simpa [erealOpenInterval_neg_one_one] using hseedIoo
  have hdom :
      effectiveDomain inverseSqrtOneSubSqOpenInterval =
        erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [inverseSqrtOneSubSqOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x : ℝ ↦ 1 / Real.sqrt (1 - x ^ (2 : ℕ))) (-1 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex inverseSqrtOneSubSqOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  have hαβ : (-1 : EReal) < (1 : EReal) := by
    have hαβ' : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast (show (-1 : ℝ) < 1 by norm_num)
    simpa using hαβ'
  simpa [inverseSqrtOneSubSqFunction] using
    oneSidedLimitExtension_mem_gammaZero (g := inverseSqrtOneSubSqOpenInterval)
      (α := (-1 : EReal)) (β := (1 : EReal)) hαβ hdom hstrict
      (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
      (fun {x} hx ↦ inverseSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: apply Proposition 8.14 to the real-valued function `x ↦ -√(1 - x^2)` on
-- `(-1,1)`, then use the one-sided-limit extension mechanism of Proposition 9.34 together with
-- the finite boundary values at `±1` to obtain the closed-interval extension.
/-- The function equal to `-√(1 - x^2)` on `[-1,1]` and to `+∞` outside that interval is strictly
convex. -/
theorem negSqrtOneSubSqFunction_strictlyConvex :
    StrictlyConvex negSqrtOneSubSqFunction := by
  -- Route correction: combine strict convexity of the square with concavity of `sqrt` on `[0,+∞)`.
  have hseedIoo :
      StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) := by
    refine ⟨convex_Ioo (-1 : ℝ) 1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    -- The midpoint stays in `(-1,1)`, so every square-root argument remains positive.
    have hmix : a * x + b * y ∈ Set.Ioo (-1 : ℝ) 1 :=
      (convex_Ioo (-1 : ℝ) 1) hx hy ha.le hb.le hab
    have hxpos : 0 < 1 - x ^ (2 : ℕ) := by
      nlinarith [hx.1, hx.2]
    have hypos : 0 < 1 - y ^ (2 : ℕ) := by
      nlinarith [hy.1, hy.2]
    have hmpos : 0 < 1 - (a * x + b * y) ^ (2 : ℕ) := by
      nlinarith [hmix.1, hmix.2]
    have hsquare :
        (a * x + b * y) ^ (2 : ℕ) < a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) :=
      weighted_square_lt hxy ha hb hab
    have hinner :
        a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) <
          1 - (a * x + b * y) ^ (2 : ℕ) := by
      nlinarith
    have hauvpos :
        0 < a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) := by
      positivity
    have hsqrt_mono :
        Real.sqrt (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) <
          Real.sqrt (1 - (a * x + b * y) ^ (2 : ℕ)) := by
      exact Real.strictMonoOn_sqrt hauvpos.le hmpos.le hinner
    have hconc :
        a * Real.sqrt (1 - x ^ (2 : ℕ)) + b * Real.sqrt (1 - y ^ (2 : ℕ)) ≤
          Real.sqrt (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) := by
      simpa [smul_eq_mul] using
        (Real.strictConcaveOn_sqrt.concaveOn.2 hxpos.le hypos.le ha.le hb.le hab)
    have hlt :
        a * Real.sqrt (1 - x ^ (2 : ℕ)) + b * Real.sqrt (1 - y ^ (2 : ℕ)) <
          Real.sqrt (1 - (a * x + b * y) ^ (2 : ℕ)) :=
      lt_of_le_of_lt hconc hsqrt_mono
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using neg_lt_neg hlt
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (-1 : EReal) (1 : EReal))
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) := by
    simpa [erealOpenInterval_neg_one_one] using hseedIoo
  have hdom :
      effectiveDomain negSqrtOneSubSqOpenInterval =
        erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [negSqrtOneSubSqOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) (-1 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex negSqrtOneSubSqOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  have hαβ : (-1 : EReal) < (1 : EReal) := by
    have hαβ' : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast (show (-1 : ℝ) < 1 by norm_num)
    simpa using hαβ'
  simpa [negSqrtOneSubSqFunction] using
    oneSidedLimitExtension_strictlyConvex (g := negSqrtOneSubSqOpenInterval)
      (α := (-1 : EReal)) (β := (1 : EReal)) hαβ hdom hstrict
      (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
      (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: apply Proposition 9.34 to the corresponding one-sided-limit extension.
/-- Example 9.36 (vi): the function equal to `-√(1 - x^2)` on `[-1,1]` and to `+∞` outside that
interval belongs to `Γ₀(ℝ)`. -/
theorem negSqrtOneSubSqFunction_mem_gammaZero :
    negSqrtOneSubSqFunction ∈ Γ₀(ℝ) := by
  have hseedIoo :
      StrictConvexOn ℝ (Set.Ioo (-1 : ℝ) 1)
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) := by
    refine ⟨convex_Ioo (-1 : ℝ) 1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    -- The same midpoint estimate packages the seed for the `Γ₀` argument.
    have hmix : a * x + b * y ∈ Set.Ioo (-1 : ℝ) 1 :=
      (convex_Ioo (-1 : ℝ) 1) hx hy ha.le hb.le hab
    have hxpos : 0 < 1 - x ^ (2 : ℕ) := by
      nlinarith [hx.1, hx.2]
    have hypos : 0 < 1 - y ^ (2 : ℕ) := by
      nlinarith [hy.1, hy.2]
    have hmpos : 0 < 1 - (a * x + b * y) ^ (2 : ℕ) := by
      nlinarith [hmix.1, hmix.2]
    have hsquare :
        (a * x + b * y) ^ (2 : ℕ) < a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) :=
      weighted_square_lt hxy ha hb hab
    have hinner :
        a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) <
          1 - (a * x + b * y) ^ (2 : ℕ) := by
      nlinarith
    have hauvpos :
        0 < a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ)) := by
      positivity
    have hsqrt_mono :
        Real.sqrt (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) <
          Real.sqrt (1 - (a * x + b * y) ^ (2 : ℕ)) := by
      exact Real.strictMonoOn_sqrt hauvpos.le hmpos.le hinner
    have hconc :
        a * Real.sqrt (1 - x ^ (2 : ℕ)) + b * Real.sqrt (1 - y ^ (2 : ℕ)) ≤
          Real.sqrt (a * (1 - x ^ (2 : ℕ)) + b * (1 - y ^ (2 : ℕ))) := by
      simpa [smul_eq_mul] using
        (Real.strictConcaveOn_sqrt.concaveOn.2 hxpos.le hypos.le ha.le hb.le hab)
    have hlt :
        a * Real.sqrt (1 - x ^ (2 : ℕ)) + b * Real.sqrt (1 - y ^ (2 : ℕ)) <
          Real.sqrt (1 - (a * x + b * y) ^ (2 : ℕ)) :=
      lt_of_le_of_lt hconc hsqrt_mono
    simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using neg_lt_neg hlt
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (-1 : EReal) (1 : EReal))
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) := by
    simpa [erealOpenInterval_neg_one_one] using hseedIoo
  have hdom :
      effectiveDomain negSqrtOneSubSqOpenInterval =
        erealOpenInterval (-1 : EReal) (1 : EReal) := by
    simpa [negSqrtOneSubSqOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x : ℝ ↦ -Real.sqrt (1 - x ^ (2 : ℕ))) (-1 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex negSqrtOneSubSqOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  have hαβ : (-1 : EReal) < (1 : EReal) := by
    have hαβ' : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
      exact_mod_cast (show (-1 : ℝ) < 1 by norm_num)
    simpa using hαβ'
  simpa [negSqrtOneSubSqFunction] using
    oneSidedLimitExtension_mem_gammaZero (g := negSqrtOneSubSqOpenInterval)
      (α := (-1 : EReal)) (β := (1 : EReal)) hαβ hdom hstrict
      (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_neg_one_liminf_gt_bot x hx)
      (fun {x} hx ↦ negSqrtOneSubSqOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: the real-valued function `x ↦ x log x + (1 - x) log(1 - x)` is strictly convex
-- on `(0,1)` by Proposition 8.14. Its endpoint limits at `0` and `1` are both `0`, so
-- Proposition 9.34 gives the lower-semicontinuous extension to `[0,1]` and hence membership in
-- `Γ₀(ℝ)` together with strict convexity.
/-- The binary entropy integrand is strictly convex. -/
theorem binaryEntropy_strictlyConvex :
    StrictlyConvex binaryEntropy := by
  -- Route correction: rewrite the seed to `-Real.binEntropy` and then transfer strict convexity
  -- through Proposition 9.34's one-sided-limit extension.
  have hseedBase : StrictConvexOn ℝ (Set.Ioo (0 : ℝ) 1) (fun x : ℝ ↦ -Real.binEntropy x) :=
    (Real.strictConcave_binEntropy.neg).subset Set.Ioo_subset_Icc_self (convex_Ioo (0 : ℝ) 1)
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (0 : EReal) (1 : EReal))
        (fun x : ℝ ↦ x * Real.log x + (1 - x) * Real.log (1 - x)) := by
    simpa [erealOpenInterval_zero_one] using
      hseedBase.congr fun x hx ↦ (binary_entropy_seed_eq_neg_binEntropy x).symm
  have hdom :
      effectiveDomain binaryEntropyOpenInterval = erealOpenInterval (0 : EReal) (1 : EReal) := by
    simpa [binaryEntropyOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x ↦ x * Real.log x + (1 - x) * Real.log (1 - x)) (0 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex binaryEntropyOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [binaryEntropy] using
    oneSidedLimitExtension_strictlyConvex (g := binaryEntropyOpenInterval) (α := (0 : EReal))
      (β := (1 : EReal)) (by simp) hdom hstrict
      (fun {x} hx ↦ binaryEntropyOpenInterval_zero_liminf_gt_bot x hx)
      (fun {x} hx ↦ binaryEntropyOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: apply Proposition 9.34 to the open-interval model of `binaryEntropy`.
/-- Example 9.36 (vii): the binary entropy integrand, equal to `x \log x + (1 - x)\log(1 - x)` on
`(0,1)`, equal to `0` at `0` and `1`, and equal to `+∞` outside `[0,1]`, belongs to `Γ₀(ℝ)`. -/
theorem binaryEntropy_mem_gammaZero :
    binaryEntropy ∈ Γ₀(ℝ) := by
  have hseedBase : StrictConvexOn ℝ (Set.Ioo (0 : ℝ) 1) (fun x : ℝ ↦ -Real.binEntropy x) :=
    (Real.strictConcave_binEntropy.neg).subset Set.Ioo_subset_Icc_self (convex_Ioo (0 : ℝ) 1)
  have hseed :
      StrictConvexOn ℝ (erealOpenInterval (0 : EReal) (1 : EReal))
        (fun x : ℝ ↦ x * Real.log x + (1 - x) * Real.log (1 - x)) := by
    simpa [erealOpenInterval_zero_one] using
      hseedBase.congr fun x hx ↦ (binary_entropy_seed_eq_neg_binEntropy x).symm
  have hdom :
      effectiveDomain binaryEntropyOpenInterval = erealOpenInterval (0 : EReal) (1 : EReal) := by
    simpa [binaryEntropyOpenInterval] using
      finiteOnOpenInterval_effectiveDomain
        (fun x ↦ x * Real.log x + (1 - x) * Real.log (1 - x)) (0 : EReal) (1 : EReal)
  have hstrict : StrictlyConvex binaryEntropyOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [binaryEntropy] using
    oneSidedLimitExtension_mem_gammaZero (g := binaryEntropyOpenInterval) (α := (0 : EReal))
      (β := (1 : EReal)) (by simp) hdom hstrict
      (fun {x} hx ↦ binaryEntropyOpenInterval_zero_liminf_gt_bot x hx)
      (fun {x} hx ↦ binaryEntropyOpenInterval_one_liminf_gt_bot x hx)

-- Proof sketch: on `(0,+∞)`, the real-valued function `x ↦ - log x` is strictly convex by the
-- derivative test in Proposition 8.14. Extending by `+∞` on `(-∞,0]` fits the half-line case of
-- Proposition 9.34, which yields the `Γ₀(ℝ)` and strict-convexity conclusions.
/-- The function equal to `- \log x` on `(0,+∞)` and to `+∞` on `(-∞,0]` is strictly convex. -/
theorem negLogIoiExtension_strictlyConvex :
    StrictlyConvex negLogIoiExtension := by
  -- Route correction: transfer strict convexity of the seed `-log` on `(0,+∞)` through the
  -- one-sided-limit extension rather than proving Jensen directly on the extended function.
  have hseed : StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ -Real.log x) := by
    simpa [erealOpenInterval_zero_top] using
      show StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) from
        strictConcaveOn_log_Ioi.neg
  have hdom :
      effectiveDomain negLogOpenInterval = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [negLogOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ -Real.log x) (0 : EReal) ⊤
  have hstrict : StrictlyConvex negLogOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [negLogIoiExtension] using
    oneSidedLimitExtension_strictlyConvex (g := negLogOpenInterval) (α := (0 : EReal)) (β := ⊤)
      (by simp) hdom hstrict
      (fun {x} hx ↦ negLogOpenInterval_zero_liminf_gt_bot x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right negLogOpenInterval x hx)

-- Proof sketch: apply Proposition 9.34 in the half-line case.
/-- Example 9.36 (viii): the function equal to `- \log x` on `(0,+∞)` and to `+∞` on `(-∞,0]`
belongs to `Γ₀(ℝ)`. -/
theorem negLogIoiExtension_mem_gammaZero :
    negLogIoiExtension ∈ Γ₀(ℝ) := by
  have hseed : StrictConvexOn ℝ (erealOpenInterval (0 : EReal) ⊤) (fun x : ℝ ↦ -Real.log x) := by
    simpa [erealOpenInterval_zero_top] using
      show StrictConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ -Real.log x) from
        strictConcaveOn_log_Ioi.neg
  have hdom :
      effectiveDomain negLogOpenInterval = erealOpenInterval (0 : EReal) ⊤ := by
    simpa [negLogOpenInterval] using
      finiteOnOpenInterval_effectiveDomain (fun x : ℝ ↦ -Real.log x) (0 : EReal) ⊤
  have hstrict : StrictlyConvex negLogOpenInterval :=
    strictlyConvex_finiteOnOpenInterval_of_strictConvexOn hseed
  simpa [negLogIoiExtension] using
    oneSidedLimitExtension_mem_gammaZero (g := negLogOpenInterval) (α := (0 : EReal))
      (β := ⊤) (by simp) hdom hstrict
      (fun {x} hx ↦ negLogOpenInterval_zero_liminf_gt_bot x hx)
      (fun {x} hx ↦ liminf_gt_bot_of_eq_top_right negLogOpenInterval x hx)

end ERealFunction
