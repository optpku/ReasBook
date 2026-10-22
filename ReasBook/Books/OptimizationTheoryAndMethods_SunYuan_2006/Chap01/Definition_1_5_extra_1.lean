/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Basic

noncomputable section

open Filter

universe u

variable {E : Type u} [NormedAddCommGroup E]

-- Semantic recall: mathlib does not provide a canonical owner for textbook `Q`-convergence
-- rates, and this file is the chapter owner reused by `Theorem_1_5_2` and
-- `Definition_1_5_extra_2`.

/-- The `Q`-error ratio of order `α` for `x` relative to `xStar`.
As a raw function this uses Lean's totalized real division when the denominator vanishes; the
quotient-limit predicates below add eventual nonvanishing hypotheses where needed. -/
def qErrorRatio (x : ℕ → E) (xStar : E) (α : ℝ) : ℕ → ℝ :=
  fun k ↦ ‖x (k + 1) - xStar‖ / Real.rpow ‖x k - xStar‖ α

/-- The defining formula for `qErrorRatio`. -/
@[simp] theorem qErrorRatio_apply (x : ℕ → E) (xStar : E) (α : ℝ) (k : ℕ) :
    qErrorRatio x xStar α k = ‖x (k + 1) - xStar‖ / Real.rpow ‖x k - xStar‖ α := rfl

/-- Auxiliary denominator-safe `Q`-ratio convergence data for `x` relative to `xStar`. This is a
bridge/view layer for arguments that need the quotient interpreted on a tail where the
denominator does not vanish. -/
class HasQRatioConvergenceTo (x : ℕ → E) (xStar : E) (α β : ℝ) : Prop where
  /-- The sequence converges to `xStar`. -/
  tendsto : Tendsto x atTop (nhds xStar)
  /-- The quotient denominator is well-defined on a tail. -/
  eventually_ne : ∀ᶠ k in atTop, x k ≠ xStar
  /-- The `Q`-error ratio converges to `β`. -/
  ratio_tendsto : Tendsto (qErrorRatio x xStar α) atTop (nhds β)

/-- The predicate `HasQRatioConvergenceTo` is proof-irrelevant. -/
instance hasQRatioConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} {α β : ℝ} :
    Subsingleton (HasQRatioConvergenceTo x xStar α β) := inferInstance

/-- The defining characterization of `HasQRatioConvergenceTo`. -/
theorem hasQRatioConvergenceTo_iff (x : ℕ → E) (xStar : E) (α β : ℝ) :
    HasQRatioConvergenceTo x xStar α β ↔
      Tendsto x atTop (nhds xStar) ∧
        (∀ᶠ k in atTop, x k ≠ xStar) ∧
        Tendsto (qErrorRatio x xStar α) atTop (nhds β) := by
  constructor
  · intro h
    exact ⟨h.tendsto, h.eventually_ne, h.ratio_tendsto⟩
  · rintro ⟨tendsto, eventually_ne, ratio_tendsto⟩
    exact ⟨tendsto, eventually_ne, ratio_tendsto⟩

/-- Chapter01 Definition 1.5-extra-1: a sequence `x` has `α`-order `Q`-convergence to `xStar`
with positive quotient limit `β` when `1 ≤ α`, `x` converges to `xStar`, and the ratio
`‖x (k + 1) - xStar‖ / ‖x k - xStar‖^α` tends to `β`. The eventual nonvanishing forced by the
positive limit is exposed separately as derived bridge API. -/
class HasQOrderConvergenceTo (x : ℕ → E) (xStar : E) (α β : ℝ) : Prop where
  /-- The order parameter satisfies the lower bound required in the textbook definition. -/
  one_le : 1 ≤ α
  /-- The quotient limit is a positive constant, as required in the textbook definition. -/
  beta_pos : 0 < β
  /-- The sequence converges to `xStar`. -/
  tendsto : Tendsto x atTop (nhds xStar)
  /-- The `Q`-error ratio converges to `β`. -/
  ratio_tendsto : Tendsto (qErrorRatio x xStar α) atTop (nhds β)

/-- The predicate `HasQOrderConvergenceTo` is proof-irrelevant. -/
instance hasQOrderConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} {α β : ℝ} :
    Subsingleton (HasQOrderConvergenceTo x xStar α β) := inferInstance

/-- The defining characterization of `HasQOrderConvergenceTo`. -/
theorem hasQOrderConvergenceTo_iff (x : ℕ → E) (xStar : E) (α β : ℝ) :
    HasQOrderConvergenceTo x xStar α β ↔
      1 ≤ α ∧ 0 < β ∧ Tendsto x atTop (nhds xStar) ∧
        Tendsto (qErrorRatio x xStar α) atTop (nhds β) := by
  constructor
  · intro h
    exact ⟨h.one_le, h.beta_pos, h.tendsto, h.ratio_tendsto⟩
  · rintro ⟨one_le, beta_pos, tendsto, ratio_tendsto⟩
    exact
      { one_le := one_le
        beta_pos := beta_pos
        tendsto := tendsto
        ratio_tendsto := ratio_tendsto }

/-- Positive-limit `Q`-order convergence forces the denominator to be nonzero on a tail. -/
theorem HasQOrderConvergenceTo.eventually_ne
    {x : ℕ → E} {xStar : E} {α β : ℝ} (h : HasQOrderConvergenceTo x xStar α β) :
    ∀ᶠ k in atTop, x k ≠ xStar := by
  -- Use the positive quotient limit to force the ratio away from `0` on a tail.
  have hHalf : β / 2 < β := by linarith [h.beta_pos]
  have hαne : α ≠ 0 := by
    have hαpos : 0 < α := lt_of_lt_of_le zero_lt_one h.one_le
    exact ne_of_gt hαpos
  filter_upwards [h.ratio_tendsto.eventually (Ioi_mem_nhds hHalf)] with k hk
  intro hxk
  -- If `x k = xStar`, then the denominator vanishes and the totalized ratio is `0`.
  have hratio_zero : qErrorRatio x xStar α k = 0 := by
    rw [qErrorRatio_apply, hxk, sub_self, norm_zero]
    rw [show Real.rpow (0 : ℝ) α = 0 by simpa using Real.zero_rpow hαne, div_zero]
  have : ¬ β / 2 < qErrorRatio x xStar α k := by
    rw [hratio_zero]
    linarith [h.beta_pos]
  exact this hk

/-- Positive-limit `Q`-order convergence canonically refines to the auxiliary denominator-safe
bridge API. -/
theorem HasQOrderConvergenceTo.toHasQRatioConvergenceTo
    {x : ℕ → E} {xStar : E} {α β : ℝ} (h : HasQOrderConvergenceTo x xStar α β) :
    HasQRatioConvergenceTo x xStar α β :=
  { tendsto := h.tendsto
    eventually_ne := h.eventually_ne
    ratio_tendsto := h.ratio_tendsto }

/-- Positive-limit `Q`-order convergence yields the textbook eventual estimate
`‖x (k + 1) - xStar‖ ≤ C * ‖x k - xStar‖^α` on a tail. This is the source-facing bridge from the
canonical Chapter 1 owner `HasQOrderConvergenceTo` to eventual error-inequality formulations. -/
theorem HasQOrderConvergenceTo.hasEventualRpowErrorEstimateTo
    {x : ℕ → E} {xStar : E} {α β : ℝ}
    (h : HasQOrderConvergenceTo x xStar α β) :
    ∃ C ∈ Set.Ioi (0 : ℝ),
      ∀ᶠ k in atTop, ‖x (k + 1) - xStar‖ ≤ C * Real.rpow ‖x k - xStar‖ α := by
  refine ⟨β + 1, show 0 < β + 1 by linarith [h.beta_pos], ?_⟩
  -- Bound the quotient by a fixed constant and then clear the positive denominator.
  have hUpper : β < β + 1 := by linarith
  filter_upwards
      [h.ratio_tendsto.eventually (Iio_mem_nhds hUpper), h.eventually_ne] with k hkRatio hkNe
  have hnorm_pos : 0 < ‖x k - xStar‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hkNe)
  have hdenom_pos : 0 < Real.rpow ‖x k - xStar‖ α := Real.rpow_pos_of_pos hnorm_pos α
  have hkRatio_le : qErrorRatio x xStar α k ≤ β + 1 := hkRatio.le
  rw [qErrorRatio_apply] at hkRatio_le
  exact (div_le_iff₀ hdenom_pos).1 hkRatio_le

/-- Helper for Chapter01 Definition 1.5-extra-1: an eventual `α`-order error estimate bounds the
first-order `Q`-error ratio by `C * ‖x k - xStar‖^(α - 1)`. -/
lemma qErrorRatio_one_le_of_rpowErrorEstimate
    {x : ℕ → E} {xStar : E} {α C : ℝ} {k : ℕ}
    (hxk : x k ≠ xStar)
    (hestimate : ‖x (k + 1) - xStar‖ ≤ C * Real.rpow ‖x k - xStar‖ α) :
    qErrorRatio x xStar 1 k ≤ C * Real.rpow ‖x k - xStar‖ (α - 1) := by
  -- Rewrite the order-`α` estimate so that dividing by the first-order denominator is exact.
  have hnorm_pos : 0 < ‖x k - xStar‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxk)
  have hone : Real.rpow ‖x k - xStar‖ 1 = ‖x k - xStar‖ := by
    simp
  have hrpow_split :
      Real.rpow ‖x k - xStar‖ α =
        Real.rpow ‖x k - xStar‖ (α - 1) * ‖x k - xStar‖ := by
    have hrpow_add :
        Real.rpow ‖x k - xStar‖ ((α - 1) + 1) =
          Real.rpow ‖x k - xStar‖ (α - 1) * Real.rpow ‖x k - xStar‖ 1 := by
      simpa using (Real.rpow_add hnorm_pos (α - 1) 1)
    calc
      Real.rpow ‖x k - xStar‖ α = Real.rpow ‖x k - xStar‖ ((α - 1) + 1) := by
        congr 2
        linarith
      _ = Real.rpow ‖x k - xStar‖ (α - 1) * Real.rpow ‖x k - xStar‖ 1 := hrpow_add
      _ = Real.rpow ‖x k - xStar‖ (α - 1) * ‖x k - xStar‖ := by rw [hone]
  rw [qErrorRatio_apply, hone]
  have hmul :
      ‖x (k + 1) - xStar‖ ≤
        (C * Real.rpow ‖x k - xStar‖ (α - 1)) * ‖x k - xStar‖ := by
    calc
      ‖x (k + 1) - xStar‖ ≤ C * Real.rpow ‖x k - xStar‖ α := hestimate
      _ = C * (Real.rpow ‖x k - xStar‖ (α - 1) * ‖x k - xStar‖) := by rw [hrpow_split]
      _ = (C * Real.rpow ‖x k - xStar‖ (α - 1)) * ‖x k - xStar‖ := by
            simp [mul_assoc]
  -- Divide by the positive norm to obtain the desired first-order quotient bound.
  exact (div_le_iff₀ hnorm_pos).2 hmul

/-- A sequence converges `Q`-linearly to `xStar` when it has first-order `Q`-convergence with
quotient limit `β` satisfying `β < 1`; positivity is part of `HasQOrderConvergenceTo`. -/
def HasQLinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  ∃ β : ℝ, β < 1 ∧ HasQOrderConvergenceTo x xStar 1 β

/-- The defining characterization of `HasQLinearConvergenceTo`. -/
theorem hasQLinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    HasQLinearConvergenceTo x xStar ↔
      ∃ β : ℝ, β < 1 ∧ HasQOrderConvergenceTo x xStar 1 β := Iff.rfl

/-- A sequence converges `Q`-superlinearly to `xStar` when it converges to `xStar` and its
first-order `Q`-error ratio tends to `0`. Denominator nonvanishing, when genuinely needed for a
derived comparison, is supplied separately as an auxiliary hypothesis. -/
class HasQSuperlinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  /-- The sequence converges to `xStar`. -/
  tendsto : Tendsto x atTop (nhds xStar)
  /-- The first-order `Q`-error ratio converges to `0`. -/
  ratio_tendsto : Tendsto (qErrorRatio x xStar 1) atTop (nhds 0)

/-- The predicate `HasQSuperlinearConvergenceTo` is proof-irrelevant. -/
instance hasQSuperlinearConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} :
    Subsingleton (HasQSuperlinearConvergenceTo x xStar) := inferInstance

/-- The defining characterization of `HasQSuperlinearConvergenceTo`. -/
theorem hasQSuperlinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    HasQSuperlinearConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧
        Tendsto (qErrorRatio x xStar 1) atTop (nhds 0) := by
  constructor
  · intro h
    exact ⟨h.tendsto, h.ratio_tendsto⟩
  · rintro ⟨tendsto, ratio_tendsto⟩
    exact ⟨tendsto, ratio_tendsto⟩

/-- A `Q`-superlinear sequence together with an explicit denominator-safe tail refines to the
auxiliary denominator-safe ratio-convergence bridge. -/
theorem HasQSuperlinearConvergenceTo.toHasQRatioConvergenceTo
    {x : ℕ → E} {xStar : E} (h : HasQSuperlinearConvergenceTo x xStar)
    (eventually_ne : ∀ᶠ k in atTop, x k ≠ xStar) :
    HasQRatioConvergenceTo x xStar 1 0 :=
  { tendsto := h.tendsto
    eventually_ne := eventually_ne
    ratio_tendsto := h.ratio_tendsto }

/-- Higher-order `Q`-convergence with order `α > 1` implies `Q`-superlinear convergence. -/
theorem HasQOrderConvergenceTo.hasQSuperlinearConvergenceTo
    {x : ℕ → E} {xStar : E} {α β : ℝ}
    (h : HasQOrderConvergenceTo x xStar α β) (hα : 1 < α) :
    HasQSuperlinearConvergenceTo x xStar := by
  rcases h.hasEventualRpowErrorEstimateTo with ⟨C, hCpos, hEstimate⟩
  refine
    { tendsto := h.tendsto
      ratio_tendsto := ?_ }
  -- The base error norm tends to `0`, so its `(α - 1)`-power also tends to `0`.
  have hαsub_pos : 0 < α - 1 := by linarith
  have hnorm_tendsto : Tendsto (fun k ↦ ‖x k - xStar‖) atTop (nhds 0) := by
    have hsub_tendsto :
        Tendsto (fun k ↦ x k - xStar) atTop (nhds (xStar - xStar)) := by
      exact h.tendsto.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ xStar) atTop (nhds xStar))
    simpa using hsub_tendsto.norm
  have hpow_tendsto :
      Tendsto (fun k ↦ Real.rpow ‖x k - xStar‖ (α - 1)) atTop (nhds 0) := by
    exact Filter.Tendsto.rpow_const_nhds_zero hnorm_tendsto hαsub_pos
  have hmajor_tendsto :
      Tendsto (fun k ↦ C * Real.rpow ‖x k - xStar‖ (α - 1)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow_tendsto)
  -- Squeeze the first-order ratio between `0` and the vanishing majorant.
  have hratio_nonneg : ∀ᶠ k in atTop, 0 ≤ qErrorRatio x xStar 1 k := by
    exact Eventually.of_forall fun k ↦ by
      rw [qErrorRatio_apply]
      exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hratio_le :
      ∀ᶠ k in atTop, qErrorRatio x xStar 1 k ≤ C * Real.rpow ‖x k - xStar‖ (α - 1) := by
    filter_upwards [hEstimate, h.eventually_ne] with k hkEstimate hkNe
    exact
      qErrorRatio_one_le_of_rpowErrorEstimate
        (x := x) (xStar := xStar) (α := α) (C := C) (k := k) hkNe hkEstimate
  exact squeeze_zero' hratio_nonneg hratio_le hmajor_tendsto

/-- A sequence converges `Q`-quadratically to `xStar` when it has second-order `Q`-convergence
with a positive quotient limit. -/
def HasQQuadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  ∃ β : ℝ, HasQOrderConvergenceTo x xStar 2 β

/-- The defining characterization of `HasQQuadraticConvergenceTo`. -/
theorem hasQQuadraticConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    HasQQuadraticConvergenceTo x xStar ↔
      ∃ β : ℝ, HasQOrderConvergenceTo x xStar 2 β := Iff.rfl

/-- `Q`-quadratic convergence implies `Q`-superlinear convergence. -/
theorem hasQSuperlinearConvergenceTo_of_hasQQuadraticConvergenceTo
    {x : ℕ → E} {xStar : E}
    (h : HasQQuadraticConvergenceTo x xStar) :
    HasQSuperlinearConvergenceTo x xStar := by
  rcases h with ⟨β, hβ⟩
  exact hβ.hasQSuperlinearConvergenceTo one_lt_two
