/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped NNReal Topology

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

section LocalLIL

variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/-- Helper for Corollary 22.3: the recentered future process
`(t, ω) ↦ B (s + t) ω - B s ω` is again a Brownian motion. -/
lemma incrementProcess_isBrownianMotion
    (hB : IsBrownianMotion μ B) (s : NNReal) :
    IsBrownianMotion μ (fun t ω ↦ B (s + t) ω - B s ω) := by
  -- Proof comment: the increment process is a literal time-shifted recentering of `B`, so the
  -- Brownian fields transport directly along the translated time mesh.
  refine
    { zero := ?_
      indepIncrements := ?_
      stationaryIncrements := ?_
      gaussian_marginal := ?_
      continuous_paths := ?_ }
  · funext ω
    simp
  · intro n t ht
    have hTranslated :
        ∀ i j, i ≤ j → (fun i ↦ s + t i) i ≤ (fun i ↦ s + t i) j := by
      intro i j hij
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left (ht hij) s
    simpa [add_assoc] using hB.indepIncrements n (fun i ↦ s + t i) hTranslated
  · intro u t r
    simpa [add_assoc, add_left_comm, add_comm] using hB.stationaryIncrements (s + u) t r
  · intro t ht
    have hId :
        IdentDistrib
          (fun ω ↦ B (s + t) ω - B s ω)
          (fun ω ↦ B t ω - B 0 ω)
          μ μ := by
      simpa [add_assoc, add_comm, add_left_comm] using
        hB.stationaryIncrements.identDistrib_increment (r := 0) (s := t) (t := s)
    have hLaw0 : HasLaw (fun ω ↦ B t ω - B 0 ω) (gaussianReal 0 t) μ := by
      simpa [hB.zero] using hB.gaussian_marginal ht
    exact hId.symm.hasLaw hLaw0
  · filter_upwards [hB.continuous_paths] with ω hω
    have hshift : Continuous (fun t : NNReal ↦ B (s + t) ω) :=
      hω.comp (continuous_const.add continuous_id)
    simpa [HasAlmostSurelyContinuousPaths, processPath] using hshift.sub continuous_const

/-- Helper for Corollary 22.3: the time inversion of the recentered future process is again a
Brownian motion. -/
lemma timeInversionIncrementProcess_isBrownianMotion
    (hB : IsBrownianMotion μ B) (s : NNReal) :
    IsBrownianMotion μ
      (ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω)) := by
  -- Proof comment: first recenter to the future increment process, then apply the Brownian
  -- time-inversion theorem from Theorem 21.14.
  exact IsBrownianMotion.timeInversion (incrementProcess_isBrownianMotion hB s)

/-- Helper for Corollary 22.3: the time inversion of the shifted increment process evaluates to
the textbook formula `u * (B (s + u⁻¹) - B s)` away from `u = 0`. -/
lemma timeInversionIncrementProcess_apply
    (s u : NNReal) (ω : Ω) :
    ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω =
      if u = 0 then 0 else (u : ℝ) * (B (s + u⁻¹) ω - B s ω) := by
  -- Proof comment: this is just the defining computation rule for time inversion specialized to
  -- the shifted increment process.
  simp [ProbabilityTheory.timeInversion_apply]

/-- Helper for Corollary 22.3: after time inversion, the normalized global LIL expression at `u`
is exactly the local increment normalization evaluated at `u⁻¹`. -/
lemma normalizedTimeInversionIncrement_eq_localNormAtInv
    (s u : NNReal) (ω : Ω) (hu : u ≠ 0) :
    (ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω) /
        Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))) =
      (B (s + u⁻¹) ω - B s ω) /
        Real.sqrt
          (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹))) := by
  have hu_pos : 0 < (u : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr hu
  have hu_nonneg : 0 ≤ (u : ℝ) := le_of_lt hu_pos
  have hsqrt :
      Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))) =
        (u : ℝ) *
          Real.sqrt
            (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹))) := by
    -- Proof comment: factor the global normalization through the positive scale `u` and the
    -- local normalization at the inverted time `u⁻¹`.
    calc
      Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ)))
          = Real.sqrt (u : ℝ) * Real.sqrt (2 * Real.log (Real.log (u : ℝ))) := by
              rw [show 2 * (u : ℝ) * Real.log (Real.log (u : ℝ)) =
                    (u : ℝ) * (2 * Real.log (Real.log (u : ℝ))) by ring]
              rw [Real.sqrt_mul hu_nonneg]
      _ = ((u : ℝ) * Real.sqrt ((u : ℝ)⁻¹)) * Real.sqrt (2 * Real.log (Real.log (u : ℝ))) := by
            rw [show Real.sqrt (u : ℝ) = (u : ℝ) * Real.sqrt ((u : ℝ)⁻¹) by
              rw [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]]
      _ = (u : ℝ) *
            (Real.sqrt ((u : ℝ)⁻¹) * Real.sqrt (2 * Real.log (Real.log (u : ℝ)))) := by
            ring
      _ = (u : ℝ) *
            Real.sqrt (((u : ℝ)⁻¹) * (2 * Real.log (Real.log (u : ℝ)))) := by
            rw [← Real.sqrt_mul (inv_nonneg.2 hu_nonneg)]
      _ = (u : ℝ) *
            Real.sqrt
              (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹))) := by
            simp [NNReal.coe_inv, mul_assoc, mul_comm]
  -- Proof comment: rewrite the time-inverted numerator, then cancel the common nonzero factor
  -- `u` against the denominator scaling from `hsqrt`.
  rw [timeInversionIncrementProcess_apply (B := B) s u ω, if_neg hu, hsqrt]
  field_simp [hu]

/-- Helper for Corollary 22.3: the normalized time-inverted global expression agrees eventually
with the local normalized increment expression evaluated at the inverted time. -/
lemma normalizedTimeInversionIncrement_eventuallyEq_localNormAtInv
    (s : NNReal) (ω : Ω) :
    (fun u : NNReal ↦
      ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
        Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ)))) =ᶠ[atTop]
      (fun u : NNReal ↦
        (B (s + u⁻¹) ω - B s ω) /
          Real.sqrt
            (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹)))) := by
  -- Proof comment: along `atTop`, all parameters are eventually positive, so the pointwise
  -- normalization rewrite from `normalizedTimeInversionIncrement_eq_localNormAtInv` applies.
  filter_upwards [eventually_gt_atTop (0 : NNReal)] with u hu
  simpa using
    normalizedTimeInversionIncrement_eq_localNormAtInv (B := B) s u ω (ne_of_gt hu)

/-- Helper for Corollary 22.3: composing a function with inversion transports its `limsup` from
`atTop` to the right-neighborhood filter `𝓝[>] 0`. -/
lemma limsup_inv_atTop_eq_limsup_nhdsGTZero
    {α : Type*} [ConditionallyCompleteLinearOrder α] (f : NNReal → α) :
    limsup (fun u : NNReal ↦ f (u⁻¹)) atTop = limsup f (𝓝[>] (0 : NNReal)) := by
  -- Proof comment: `limsup` along a composition is definitional via `Filter.map`, and inversion
  -- sends `atTop` exactly to `𝓝[>] 0`.
  change limsup f (Filter.map Inv.inv atTop) = limsup f (𝓝[>] (0 : NNReal))
  simpa using congrArg (limsup f)
    (inv_atTop₀ : ((atTop : Filter NNReal)⁻¹) = 𝓝[>] (0 : NNReal))

/- Corollary 22.3 is `source-facing`: it records the local law of the iterated logarithm for the
increment process at a fixed time. Its core/canonical owner remains `IsBrownianMotion`; the
primitive data are a Brownian motion `B` and a time `s`, while the local limsup formula is derived
from the owner-level time-inversion theorem and the global law of the iterated logarithm. -/

-- Proof sketch: for fixed `s`, the increment process `t ↦ B (s + t) - B s` is again a Brownian
-- motion by stationary independent increments and almost-sure continuity. Apply Theorem 22.1 to
-- the time inversion from Theorem 21.14 of that increment process, equivalently to
-- `t ↦ t * (B (s + t⁻¹) - B s)`, and rewrite the resulting asymptotic statement back as the
-- one-sided `t ↓ 0` limsup of the normalized increment process.
/-- Helper for Corollary 22.3: specialize the missing global Brownian LIL input to the
time-inverted increment process. -/
lemma ae_limsup_timeInversionIncrement_div_sqrt_two_mul_t_log_log_eq_one_of_owner
    (hOwner :
      ∀ {μ : Measure Ω} {W : NNReal → Ω → ℝ},
        IsBrownianMotion μ W →
          ∀ᵐ ω ∂μ,
            limsup
              (fun u : NNReal ↦
                W u ω / Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
              atTop = 1)
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (s : NNReal) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun u : NNReal ↦
          ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
            Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
        atTop = 1 := by
  have hWInv : IsBrownianMotion μ
      (ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω)) := by
    -- Proof comment: reuse the already established Brownian structure of the time-inverted
    -- increment process.
    simpa using timeInversionIncrementProcess_isBrownianMotion (B := B) hB s
  -- Proof comment: once the owner theorem is available abstractly, the current helper is exactly
  -- its specialization to `hWInv`.
  simpa using hOwner hWInv

/-- Helper for Corollary 22.3: specialize the missing global Brownian LIL input to the
time-inverted increment process. -/
lemma ae_limsup_timeInversionIncrement_div_sqrt_two_mul_t_log_log_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (s : NNReal) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun u : NNReal ↦
          ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
            Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
        atTop = 1 := by
  have hWInv : IsBrownianMotion μ
      (ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω)) := by
    -- Proof comment: the recentered increment process is Brownian, hence so is its time
    -- inversion.
    simpa using timeInversionIncrementProcess_isBrownianMotion (B := B) hB s
  -- Route correction: the only missing step is the canonical owner-theorem specialization from
  -- Theorem 22.1 to the time-inverted increment process.
  simpa using hWInv.ae_limsup_div_sqrt_two_mul_t_log_log_eq_one

/-- Helper for Corollary 22.3: once the time-inverted increment process satisfies the global LIL
at `atTop`, the desired local `t ↓ 0` increment statement follows by the established inversion and
filter transport lemmas. -/
lemma limsup_localIncrement_eq_limsup_timeInversionIncrement
    {B : NNReal → Ω → ℝ} (s : NNReal) (ω : Ω) :
    limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal))
      =
        limsup
          (fun u : NNReal ↦
            ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
              Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
          atTop := by
  let W : NNReal → Ω → ℝ := fun t ω ↦ B (s + t) ω - B s ω
  have hRewrite :
      (fun u : NNReal ↦
        ProbabilityTheory.timeInversion W u ω /
          Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ)))) =ᶠ[atTop]
        (fun u : NNReal ↦
          (B (s + u⁻¹) ω - B s ω) /
            Real.sqrt
              (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹)))) := by
    -- Proof comment: this is the deterministic sample-path rewrite established from the explicit
    -- time-inversion formula.
    simpa [W] using
      normalizedTimeInversionIncrement_eventuallyEq_localNormAtInv (B := B) s ω
  -- Proof comment: first move the local limsup to `atTop` along inversion, then rewrite the
  -- global integrand by the eventual equality from the explicit normalization formula.
  calc
    limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal))
      =
        limsup
          (fun u : NNReal ↦
            (B (s + u⁻¹) ω - B s ω) /
              Real.sqrt
                (2 * ((u⁻¹ : NNReal) : ℝ) * Real.log (Real.log (((u⁻¹ : NNReal) : ℝ)⁻¹))))
          atTop := by
            -- Proof comment: inversion sends `atTop` to the punctured neighborhood filter at `0`.
            symm
            simpa using
              limsup_inv_atTop_eq_limsup_nhdsGTZero
                (f := fun t : NNReal ↦
                  (B (s + t) ω - B s ω) /
                    Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
    _ =
        limsup
          (fun u : NNReal ↦
            ProbabilityTheory.timeInversion W u ω /
              Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
          atTop := by
            -- Proof comment: the explicit time-inversion normalization agrees eventually with the
            -- local increment normalization evaluated at `u⁻¹`.
            simpa [W] using limsup_congr hRewrite.symm

/-- Helper for Corollary 22.3: once the time-inverted increment process satisfies the global LIL
at `atTop`, the desired local `t ↓ 0` increment statement follows by the established inversion and
filter transport lemmas. -/
lemma ae_limsup_increment_div_sqrt_two_mul_t_log_log_inv_eq_one_of_timeInversion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (s : NNReal)
    (hGlobal :
      ∀ᵐ ω ∂μ,
        limsup
          (fun u : NNReal ↦
            ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
              Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
          atTop = 1) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal)) = 1 := by
  filter_upwards [hGlobal] with ω hω
  -- Proof comment: the deterministic limsup transport has already been isolated, so this
  -- almost-sure statement is now a single rewrite followed by the upstream global input.
  calc
    limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal))
      =
        limsup
          (fun u : NNReal ↦
            ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
              Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
          atTop := by
            exact
              limsup_localIncrement_eq_limsup_timeInversionIncrement (B := B) s ω
    _ = 1 := hω

/-- Corollary 22.3: for every `s ≥ 0`, Brownian increments at time `s` satisfy the local law of
the iterated logarithm
`limsup_{t ↓ 0} (B (s + t) - B s) / sqrt(2 t log log (1 / t)) = 1` almost surely. -/
theorem ae_limsup_increment_div_sqrt_two_mul_t_log_log_inv_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) (s : NNReal) :
    ∀ᵐ ω ∂μ,
      limsup
        (fun t : NNReal ↦
          (B (s + t) ω - B s ω) /
            Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal)) = 1 := by
  have hGlobal :
      ∀ᵐ ω ∂μ,
        limsup
          (fun u : NNReal ↦
            ProbabilityTheory.timeInversion (fun t ω ↦ B (s + t) ω - B s ω) u ω /
              Real.sqrt (2 * (u : ℝ) * Real.log (Real.log (u : ℝ))))
          atTop = 1 := by
    -- Proof comment: isolate the upstream dependency application in a dedicated helper so the
    -- main corollary proof only performs the established local transport steps.
    simpa using
      ae_limsup_timeInversionIncrement_div_sqrt_two_mul_t_log_log_eq_one (B := B) hB s
  -- Proof comment: the remaining work is exactly the already verified inversion/filter transport.
  exact
    ae_limsup_increment_div_sqrt_two_mul_t_log_log_inv_eq_one_of_timeInversion
      (B := B) s hGlobal

end LocalLIL

end IsBrownianMotion

end ProbabilityTheory
