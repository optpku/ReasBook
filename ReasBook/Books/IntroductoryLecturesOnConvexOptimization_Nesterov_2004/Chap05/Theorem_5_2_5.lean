/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_2_3

open scoped BigOperators SelfConcordantQuadraticRegion
open scoped StronglyConvexHalfGapIndex StronglyConvexMultiStageAccelerationNotation
open scoped StronglyConvexScaledGap

noncomputable section

universe u

/- Theorem 5.2.5 lies in the Chapter 5 multistage acceleration domain for strongly convex
self-concordant objectives.

Sampled declarations in this domain:
* `stronglyConvexHalfGapIndex` from `Definition_5_2_10`, the chapter owner for the source
  positive threshold index `k_p`;
* `stronglyConvexMultiStageAccelerationStageLength`,
  `stronglyConvexMultiStageAccelerationTotalLowerLevelIterations`,
  `stronglyConvexMultiStageAccelerationOrbit`, and
  `IsStronglyConvexMultiStageAccelerationStoppingStage` from `Definition_5_2_11`, the chapter
  owners for the stage schedule, cumulative lower-level work, multistage orbit `(5.2.28)`, and
  first stopping stage;
* `one_le_stronglyConvexHalfGapIndex` and
  `one_le_stronglyConvexMultiStageAccelerationStageLength`, the derived owner API ensuring that
  the source schedule uses positive stage lengths;
* `Nat.ceil` / `Nat.le_ceil`, the canonical mathlib owner for the ceiling schedule appearing in
  the source formula for `t_k`;
* `Real.logb`, the canonical base-`2` logarithm owner used in the stopping-stage estimate.

Source/core/bridge triage:
* source-facing: Theorem 5.2.5 itself, stated for the textbook multistage strategy with stopping
  region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* core/canonical: the chapter owner orbit
  `stronglyConvexMultiStageAccelerationOrbit innerIterate kp p x0` together with the canonical
  least-stage predicate `IsStronglyConvexMultiStageAccelerationStoppingStage ... T`;
* bridge/view: the arithmetic passage from the stagewise rate bound and the ceiling schedule to
  the logarithmic bound on the stopping stage and the geometric-series bound on the total work.

Primitive data:
* the canonical positive half-gap index `k_p`;
* the source stopping region `f(x) - f* ≤ 1 / (8 M_f^2)`;
* the recursive outer orbit `y_k`;
* the source first-stopping-stage witness `T`;
* the stagewise rate estimate inherited from the lower-level method.

Derived API:
* the total number of lower-level iterations performed before the stopping stage;
* the stage bound `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`;
* the resulting total-work bound.

This refinement restores the source theorem surface. The previous version replaced the textbook
strategy by an abstract geometric-decay lemma over an auxiliary gap observable and by an extra
terminal-region bridge hypothesis. Here the main declarations speak directly about the source
ceiling schedule and the source stopping threshold. -/

section

variable {E : Type u} {f : E → ℝ}
variable {innerIterate : ℕ → E → E} {c p fStar : ℝ} {Mf : NNReal} {x0 : E}

private theorem stoppingStageSetup
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hTpos : 0 < T) (hp : 0 < p) :
    x0 ∉ 𝒬[f | fStar, Mf] ∧
      0 < Mf ∧
      0 < f x0 - fStar ∧
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty := by
  have hx0 : x0 ∉ 𝒬[f | fStar, Mf] := by
    simpa using
      stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage hT hTpos
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hgap : 0 < f x0 - fStar :=
    gap_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hkp :
      (stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)).Nonempty :=
    stronglyConvexHalfGapAdmissibleIndices_nonempty hp hgap
  exact ⟨hx0, hMf, hgap, hkp⟩

/-- Helper for Theorem 5.2.5: on a nonnegative gap, the exponent `3 / 2` is the product
`gap * √gap`. -/
private theorem gapThreeHalves_eq_mul_sqrt
    {gap : ℝ} (hgap : 0 ≤ gap) :
    Real.rpow gap (3 / 2 : ℝ) = gap * Real.sqrt gap := by
  -- Rewrite the `3 / 2` power as `1 + 1 / 2`, then identify the square-root factor.
  calc
    Real.rpow gap (3 / 2 : ℝ) = Real.rpow gap ((1 : ℝ) + 1 / 2) := by norm_num
    _ = Real.rpow gap (1 : ℝ) * Real.rpow gap (1 / 2 : ℝ) := by
      simpa using
        Real.rpow_add_of_nonneg hgap
          (show 0 ≤ (1 : ℝ) by positivity)
          (show 0 ≤ (1 / 2 : ℝ) by positivity)
    _ = gap * Real.sqrt gap := by
      simp [Real.sqrt_eq_rpow]

/-- Helper for Theorem 5.2.5: squaring the Chapter 5 scaled gap recovers `M_f^2 * gap`. -/
private theorem scaledGapSquare_eq_mul_gap
    {Mf gap : ℝ} (hgap : 0 ≤ gap) :
    (Δ Mf gap) ^ (2 : ℕ) = Mf ^ (2 : ℕ) * gap := by
  -- Expanding `Δ Mf gap = Mf * √gap` reduces the square to `Mf^2 * gap`.
  rw [stronglyConvexScaledGap]
  calc
    (Mf * Real.sqrt gap) ^ (2 : ℕ) = Mf ^ (2 : ℕ) * (Real.sqrt gap) ^ (2 : ℕ) := by ring
    _ = Mf ^ (2 : ℕ) * gap := by
      rw [Real.sq_sqrt hgap]

/-- Helper for Theorem 5.2.5: raising the scheduled real denominator
`kp / 2^(k / (2p))` to the power `p` produces the normalized scalar `kp^p / 2^(k/2)`. -/
private theorem scheduledDenominatorRpow
    {kp k : ℕ} (hp : 0 < p) :
    Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) ) p =
      Real.rpow (kp : ℝ) p / Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
  have hden_nonneg : 0 ≤ Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)) := by
    exact le_of_lt (Real.rpow_pos_of_pos zero_lt_two _)
  -- First distribute the outer `p`-power across the quotient.
  calc
    Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) ) p =
        Real.rpow (kp : ℝ) p /
          Real.rpow (Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) p := by
      simpa using Real.div_rpow (show 0 ≤ (kp : ℝ) by exact_mod_cast Nat.zero_le kp) hden_nonneg p
    _ = Real.rpow (kp : ℝ) p / Real.rpow (2 : ℝ) (((k : ℝ) / (2 * p)) * p) := by
      congr 1
      simpa using
        (Real.rpow_mul (show 0 ≤ (2 : ℝ) by norm_num) ((k : ℝ) / (2 * p)) p).symm
    _ = Real.rpow (kp : ℝ) p / Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
      congr 1
      field_simp [hp.ne']

/-- Helper for Theorem 5.2.5: the square root of the geometric gap bound
`gap₀ / 2^k` is `√gap₀ / 2^(k/2)`. -/
private theorem sqrt_gap_div_pow_two
    {gap0 : ℝ} {k : ℕ} (hgap0 : 0 ≤ gap0) :
    Real.sqrt (gap0 / (2 : ℝ) ^ k) =
      Real.sqrt gap0 / Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
  -- Pull the square root through the quotient, then rewrite the denominator by `Real.rpow`.
  rw [Real.sqrt_div hgap0 ((2 : ℝ) ^ k)]
  have htwo : Real.sqrt ((2 : ℝ) ^ k) = Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      Real.rpow ((2 : ℝ) ^ k) (1 / 2 : ℝ) =
          Real.rpow (2 : ℝ) ((k : ℝ) * (1 / 2 : ℝ)) := by
        simpa using
          (Real.rpow_natCast_mul (show 0 ≤ (2 : ℝ) by norm_num) k (1 / 2 : ℝ)).symm
      _ = Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
        congr 1
        ring
  rw [htwo]

/-- Helper for Theorem 5.2.5: the schedule denominator `kp / 2^(k / (2p))` is a geometric term
with ratio `(2^(1 / (2p)))⁻¹`. -/
private theorem stageLengthGeometricRewrite
    {kp k : ℕ} (hp : 0 < p) :
    (kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)) =
      (kp : ℝ) * ((Real.rpow (2 : ℝ) (1 / (2 * p)))⁻¹) ^ k := by
  have hexponent : (k : ℝ) / (2 * p) = (1 / (2 * p)) * k := by
    field_simp [hp.ne']
  -- Rewrite the varying denominator as a fixed ratio to the `k`-th power.
  calc
    (kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)) =
        (kp : ℝ) * (Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (kp : ℝ) * (Real.rpow (2 : ℝ) ((1 / (2 * p)) * k))⁻¹ := by
      rw [hexponent]
    _ = (kp : ℝ) * ((Real.rpow (2 : ℝ) (1 / (2 * p))) ^ k)⁻¹ := by
      congr 1
      simpa [mul_comm] using
        (Real.rpow_mul_natCast (show 0 ≤ (2 : ℝ) by norm_num) (1 / (2 * p)) k)
    _ = (kp : ℝ) * ((Real.rpow (2 : ℝ) (1 / (2 * p)))⁻¹) ^ k := by
      rw [inv_pow]

/-- Helper for Theorem 5.2.5: if `T` is the first stage whose output lies in the terminal
region, then the predecessor stage is still outside that region whenever `2 ≤ T`. -/
private theorem pred_not_mem_selfConcordantQuadraticRegion_of_stoppingStage
    {T : ℕ}
    (hTtwo : 2 ≤ T)
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T) :
    y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1) ∉ 𝒬[f | fStar, Mf] := by
  -- The least-stage witness forbids terminal-region membership at any earlier stage.
  intro hpred_mem
  have hpred_lt : T - 1 < T := Nat.sub_lt (lt_of_lt_of_le (by norm_num) hTtwo) (by norm_num)
  exact (not_lt_of_ge (hT.2 hpred_mem)) hpred_lt

/-- Helper for Theorem 5.2.5: outside the Chapter 5 terminal region, the function gap is
strictly larger than the source threshold `1 / (8 M_f^2)`. -/
private theorem gap_lower_bound_of_not_mem_selfConcordantQuadraticRegion
    {x : E}
    (hx : x ∉ 𝒬[f | fStar, Mf]) :
    1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) < f x - fStar := by
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx
  -- Rewriting nonmembership through the divided threshold exposes the strict gap lower bound.
  rw [mem_selfConcordantQuadraticRegion_iff_div hMf] at hx
  exact lt_of_not_ge hx

/-- Helper for Theorem 5.2.5: in the positive-`c` branch, the scheduled stage length and the
least-index property of `k_p` force one stage to cut the current gap by at least one half once
the inductive gap bound `gap_k ≤ gap₀ / 2^k` is available. -/
private theorem nextStageGap_le_half_of_stageGapBound
    {T k : ℕ}
    (hc : 0 < c) (hp : 0 < p) (_hMf : 0 < Mf)
    (hstage_rate :
      ∀ j : ℕ, j < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (j + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] j : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] j) - fStar)
              (3 / 2 : ℝ))
    (hk : k < T)
    (hkp_mem :
      k[c, Mf; p](f x0 - fStar) ∈
        stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar))
    (hgapk_pos :
      0 < f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
    (hgap_bound :
      f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar ≤
        (f x0 - fStar) / (2 : ℝ) ^ k) :
    f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
      (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar) / 2 := by
  let kp := k[c, Mf; p](f x0 - fStar)
  let gap0 := f x0 - fStar
  let gapk := f (y[innerIterate | kp; p; x0] k) - fStar
  let coeff : ℝ := Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)
  have hkp_pos : 1 ≤ kp := hkp_mem.1
  have hgapk_nonneg : 0 ≤ gapk := hgapk_pos.le
  have hpowk_pos : 0 < (2 : ℝ) ^ k := by positivity
  have hgap0_pos : 0 < gap0 := by
    -- The current positive gap sits below `gap₀ / 2^k`, so the initial gap is positive too.
    have hmul :
        gapk * (2 : ℝ) ^ k ≤ gap0 := by
      have hscaled := mul_le_mul_of_nonneg_right hgap_bound hpowk_pos.le
      simpa [gap0, gapk, div_eq_mul_inv, hpowk_pos.ne', mul_assoc, mul_left_comm, mul_comm] using
        hscaled
    exact lt_of_lt_of_le (mul_pos hgapk_pos hpowk_pos) hmul
  have hkp_pow_pos : 0 < Real.rpow (kp : ℝ) p := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast hkp_pos) p
  have htwo_half_pos : 0 < Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
    exact Real.rpow_pos_of_pos zero_lt_two _
  have hschedule_pos :
      0 <
        ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) := by
    exact
      div_pos (by exact_mod_cast hkp_pos)
        (Real.rpow_pos_of_pos zero_lt_two _)
  have hcoeff_nonneg : 0 ≤ coeff := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt (Real.rpow_pos_of_pos zero_lt_two _)) hc.le)
      (show 0 ≤ (Mf : ℝ) by exact_mod_cast Mf.2)
  have hsched_le :
      ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) ≤ t[kp; p] k :=
    Nat.le_ceil _
  have hsched_nonneg :
      0 ≤ ((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p))) := by
    exact hschedule_pos.le
  have hsched_pow_le :
      Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))) p ≤
        Real.rpow (t[kp; p] k : ℝ) p := by
    exact Real.rpow_le_rpow hsched_nonneg hsched_le hp.le
  have hsched_pow_pos :
      0 < Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))) p := by
    exact Real.rpow_pos_of_pos hschedule_pos p
  have hstage_pow_pos :
      0 < Real.rpow (t[kp; p] k : ℝ) p := by
    exact
      Real.rpow_pos_of_pos
        (by
          exact_mod_cast
            one_le_stronglyConvexMultiStageAccelerationStageLength hkp_pos p k)
        p
  have hhalf_coeff :
      (coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0 ≤ 1 / 2 := by
    have hmem_scalar :
        (coeff * Real.rpow gap0 (3 / 2 : ℝ)) / Real.rpow (kp : ℝ) p ≤ gap0 / 2 := by
      simpa [kp, gap0, coeff, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hkp_mem.2
    rw [gapThreeHalves_eq_mul_sqrt hgap0_pos.le] at hmem_scalar
    have hrewritten :
        ((coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0) * gap0 ≤ gap0 / 2 := by
      simpa [div_eq_mul_inv, hkp_pow_pos.ne', mul_assoc, mul_left_comm, mul_comm] using hmem_scalar
    have hrewritten' :
        ((coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0) * gap0 ≤ (1 / 2) * gap0 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hrewritten
    exact le_of_mul_le_mul_right hrewritten' hgap0_pos
  have hsqrt_bound :
      Real.sqrt gapk ≤ Real.sqrt gap0 / Real.rpow (2 : ℝ) ((k : ℝ) / 2) := by
    have hsqrt_raw : Real.sqrt gapk ≤ Real.sqrt (gap0 / (2 : ℝ) ^ k) := by
      gcongr
    simpa [gap0, gapk, sqrt_gap_div_pow_two hgap0_pos.le] using hsqrt_raw
  have hsqrt_factor :
      (coeff / Real.rpow (t[kp; p] k : ℝ) p) * Real.sqrt gapk ≤
        (coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0 := by
    have hpow_inv :
        (Real.rpow (t[kp; p] k : ℝ) p)⁻¹ ≤
          (Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))) p)⁻¹ := by
      exact (inv_le_inv₀ hstage_pow_pos hsched_pow_pos).mpr hsched_pow_le
    have hcoeff_stage_nonneg :
        0 ≤ coeff / Real.rpow (t[kp; p] k : ℝ) p := by
      exact div_nonneg hcoeff_nonneg (le_of_lt hstage_pow_pos)
    -- Route correction: normalize the scheduled denominator and the square-root factor once,
    -- then cancel the geometric `2^(k/2)` term before using the admissible-index inequality.
    calc
      (coeff / Real.rpow (t[kp; p] k : ℝ) p) * Real.sqrt gapk
          ≤ (coeff / Real.rpow (t[kp; p] k : ℝ) p) *
              (Real.sqrt gap0 / Real.rpow (2 : ℝ) ((k : ℝ) / 2)) := by
        exact mul_le_mul_of_nonneg_left hsqrt_bound hcoeff_stage_nonneg
      _ = (coeff * (Real.rpow (t[kp; p] k : ℝ) p)⁻¹) *
            (Real.sqrt gap0 / Real.rpow (2 : ℝ) ((k : ℝ) / 2)) := by
        rw [div_eq_mul_inv]
      _ ≤ (coeff *
            (Real.rpow (((kp : ℝ) / Real.rpow (2 : ℝ) ((k : ℝ) / (2 * p)))) p)⁻¹) *
            (Real.sqrt gap0 / Real.rpow (2 : ℝ) ((k : ℝ) / 2)) := by
        gcongr
      _ = (coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0 := by
        rw [scheduledDenominatorRpow (kp := kp) (k := k) hp]
        field_simp [hkp_pow_pos.ne', htwo_half_pos.ne']
  -- Turn the stagewise estimate into the target half-contraction after separating one `gap_k`
  -- factor from `gap_k^(3/2)`.
  calc
    f (y[innerIterate | kp; p; x0] (k + 1)) - fStar ≤
        (coeff / Real.rpow (t[kp; p] k : ℝ) p) * Real.rpow gapk (3 / 2 : ℝ) := by
      simpa [kp, gapk, coeff] using hstage_rate k hk
    _ = ((coeff / Real.rpow (t[kp; p] k : ℝ) p) * Real.sqrt gapk) * gapk := by
      rw [gapThreeHalves_eq_mul_sqrt hgapk_nonneg]
      ring
    _ ≤ (((coeff / Real.rpow (kp : ℝ) p) * Real.sqrt gap0) * gapk) := by
      gcongr
    _ ≤ (1 / 2) * gapk := by
      gcongr
    _ = gapk / 2 := by ring

/-- Helper for Theorem 5.2.5: in the positive-`c` branch, every pre-stopping stage gap decays at
least geometrically as `gap₀ / 2^k`. -/
private theorem stageGap_le_initialGap_div_pow_two
    {T : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hMf : 0 < Mf)
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ))
    (hkp_mem :
      k[c, Mf; p](f x0 - fStar) ∈
        stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar)) :
    ∀ k : ℕ, k < T →
      f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar ≤
        (f x0 - fStar) / (2 : ℝ) ^ k := by
  intro k hk
  induction k with
  | zero =>
      -- The initial stage gap is exactly the initial suboptimality.
      simp
  | succ k ih =>
      have hk_lt : k < T := Nat.lt_of_succ_lt hk
      have hgapk_bound :
          f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar ≤
            (f x0 - fStar) / (2 : ℝ) ^ k :=
        ih hk_lt
      have hnot_mem :
          y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k ∉ 𝒬[f | fStar, Mf] :=
        stronglyConvexMultiStageAcceleration_not_mem_of_lt_stoppingStage hT hk_lt
      have hgapk_pos :
          0 < f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar :=
        gap_pos_of_not_mem_selfConcordantQuadraticRegion hnot_mem
      have hhalf :
          f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
            (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar) / 2 :=
        nextStageGap_le_half_of_stageGapBound
          hc hp hMf hstage_rate hk_lt hkp_mem hgapk_pos hgapk_bound
      -- One more half-step updates the geometric denominator from `2^k` to `2^(k+1)`.
      calc
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
            (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar) / 2 := hhalf
        _ ≤ ((f x0 - fStar) / (2 : ℝ) ^ k) / 2 := by
          gcongr
        _ = (f x0 - fStar) / (2 : ℝ) ^ (k + 1) := by
          rw [pow_succ]
          field_simp [show ((2 : ℝ) ^ k) ≠ 0 by positivity]

/-- Helper for Theorem 5.2.5: a finite geometric sum with ratio `r ∈ [0,1)` is bounded by the
full geometric tail `(1 - r)⁻¹`. -/
private theorem finiteGeometricRangeSum_le_inv_sub
    {r : ℝ} {T : ℕ}
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1) :
    Finset.sum (Finset.range T) (fun j ↦ r ^ j) ≤ (1 - r)⁻¹ := by
  have hr_ne_one : r ≠ 1 := ne_of_lt hr_lt_one
  have hden_pos : 0 < 1 - r := sub_pos.mpr hr_lt_one
  have hpow_le_one : r ^ T ≤ 1 := by
    exact pow_le_one₀ hr_nonneg hr_lt_one.le
  have hnum_le_one : 1 - r ^ T ≤ 1 := by
    exact sub_le_self _ (pow_nonneg hr_nonneg _)
  -- Rewrite the finite sum once into the stable `(1 - r^T) / (1 - r)` normal form.
  calc
    Finset.sum (Finset.range T) (fun j ↦ r ^ j) = (r ^ T - 1) / (r - 1) := by
      simpa using geom_sum_eq hr_ne_one T
    _ = (1 - r ^ T) / (1 - r) := by
      rw [show r ^ T - 1 = -(1 - r ^ T) by ring, show r - 1 = -(1 - r) by ring, neg_div_neg_eq]
    _ ≤ 1 / (1 - r) := by
      exact div_le_div_of_nonneg_right hnum_le_one hden_pos.le
    _ = (1 - r)⁻¹ := by rw [one_div]

/-- Helper for Theorem 5.2.5: casting the chapter owner for total lower-level work gives the
corresponding real-valued finite sum of stage lengths. -/
private theorem stronglyConvexMultiStageAccelerationTotalLowerLevelIterations_cast_sum
    {kp T : ℕ} :
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations kp p T : ℝ) =
      Finset.sum (Finset.range T) (fun j ↦ (t[kp; p] j : ℝ)) := by
  -- Expand the owner once, then cast the finite sum termwise.
  simp [stronglyConvexMultiStageAccelerationTotalLowerLevelIterations]

/-- Helper for Theorem 5.2.5: the total lower-level work of the scheduled multistage method is
bounded by the number of stages plus the corresponding geometric tail. -/
private theorem totalLowerLevelIterations_le_stageCount_add_scheduleTail
    {kp T : ℕ}
    (hp : 0 < p) (hkp : 1 ≤ kp) :
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations kp p T : ℝ) ≤
      T +
        (Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
        (kp : ℝ) := by
  let ratio : ℝ := (Real.rpow (2 : ℝ) (1 / (2 * p)))⁻¹
  have hexp_pos : 0 < (1 / (2 * p) : ℝ) := by
    have hp' : 0 < 2 * p := by positivity
    positivity
  have hratio_nonneg : 0 ≤ ratio := by
    dsimp [ratio]
    exact inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos zero_lt_two _))
  have hratio_lt_one : ratio < 1 := by
    dsimp [ratio]
    have hbase_gt_one : 1 < Real.rpow (2 : ℝ) (1 / (2 * p)) :=
      Real.one_lt_rpow (by norm_num) hexp_pos
    exact inv_lt_one_of_one_lt₀ hbase_gt_one
  have hratio_ne_zero : ratio ≠ 0 := by
    dsimp [ratio]
    exact inv_ne_zero (ne_of_gt (Real.rpow_pos_of_pos zero_lt_two _))
  have hratio_den_ne : Real.rpow (2 : ℝ) (1 / (2 * p)) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (Real.one_lt_rpow (by norm_num) hexp_pos))
  have hterm_bound :
      ∀ j : ℕ, (t[kp; p] j : ℝ) ≤ 1 + (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p)) := by
    intro j
    -- Bound each ceiling stage length by one plus its defining real argument.
    simpa [add_comm] using (Nat.ceil_lt_add_one
      (show 0 ≤ (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p)) by
        exact div_nonneg (by exact_mod_cast Nat.zero_le kp)
          (le_of_lt (Real.rpow_pos_of_pos zero_lt_two _)))).le
  have hsum_bound :
      Finset.sum (Finset.range T) (fun j ↦ (t[kp; p] j : ℝ)) ≤
        Finset.sum (Finset.range T)
          (fun j ↦ 1 + (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p))) := by
    exact Finset.sum_le_sum fun j _ ↦ hterm_bound j
  have hschedule_rewrite :
      Finset.sum (Finset.range T)
        (fun j ↦ (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p))) =
        (kp : ℝ) * Finset.sum (Finset.range T) (fun j ↦ ratio ^ j) := by
    -- Route correction: rewrite every schedule term through one fixed geometric ratio before
    -- summing, instead of reopening `Real.rpow` normalization inside the sum estimate.
    have hterm_rewrite :
        ∀ j : ℕ,
          (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p)) =
            (kp : ℝ) * ratio ^ j := by
      intro j
      simpa [ratio] using stageLengthGeometricRewrite (kp := kp) (k := j) hp
    refine (Finset.sum_congr rfl fun j _ ↦ hterm_rewrite j).trans ?_
    rw [Finset.mul_sum]
  have hgeom_bound :
      Finset.sum (Finset.range T) (fun j ↦ ratio ^ j) ≤ (1 - ratio)⁻¹ :=
    finiteGeometricRangeSum_le_inv_sub hratio_nonneg hratio_lt_one
  have hratio_closed :
      (1 - ratio)⁻¹ =
        Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1) := by
    let a : ℝ := Real.rpow (2 : ℝ) (1 / (2 * p))
    have ha_pos : 0 < a := by
      dsimp [a]
      exact Real.rpow_pos_of_pos zero_lt_two _
    calc
      (1 - ratio)⁻¹ = (1 - a⁻¹)⁻¹ := by rfl
      _ = a / (a - 1) := by
        field_simp [a, ha_pos.ne']
      _ =
          Real.rpow (2 : ℝ) (1 / (2 * p)) /
            (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1) := by
        rfl
  -- Separate the constant stage-count contribution from the geometric tail and bound the latter.
  calc
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations kp p T : ℝ) =
        Finset.sum (Finset.range T) (fun j ↦ (t[kp; p] j : ℝ)) := by
      rw [stronglyConvexMultiStageAccelerationTotalLowerLevelIterations_cast_sum]
    _ ≤
        Finset.sum (Finset.range T)
          (fun j ↦ 1 + (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p))) := hsum_bound
    _ = T +
        Finset.sum (Finset.range T)
          (fun j ↦ (kp : ℝ) / Real.rpow (2 : ℝ) ((j : ℝ) / (2 * p))) := by
      simp [Finset.sum_add_distrib]
    _ = T + (kp : ℝ) * Finset.sum (Finset.range T) (fun j ↦ ratio ^ j) := by
      rw [hschedule_rewrite]
    _ ≤ T + (kp : ℝ) * (1 - ratio)⁻¹ := by
      have hkp_nonneg : 0 ≤ (kp : ℝ) := by positivity
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (mul_le_mul_of_nonneg_left hgeom_bound hkp_nonneg) T
    _ = T +
        (Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
        (kp : ℝ) := by
      rw [hratio_closed]
      ring

/-- Helper for Theorem 5.2.5: in the positive-`c` branch, the predecessor-stage gap threshold
forces the scalar inequality `(2^(T-1)) < 8 * Δ_f(x₀)^2`. -/
private theorem predStagePow_lt_eight_mul_scaledGapSquare
    {T : ℕ}
    (hc : 0 < c) (hp : 0 < p) (hTtwo : 2 ≤ T)
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (2 : ℝ) ^ (T - 1) < 8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
  have hTone : 1 ≤ T := le_trans (by norm_num) hTtwo
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  obtain ⟨_, hMf, hgap0, hkp_nonempty⟩ := stoppingStageSetup hT hTpos hp
  have hkp_mem :
      k[c, Mf; p](f x0 - fStar) ∈
        stronglyConvexHalfGapAdmissibleIndices c Mf p (f x0 - fStar) :=
    (isLeast_stronglyConvexHalfGapIndex c Mf p (f x0 - fStar) hkp_nonempty).1
  have hpred_lt : T - 1 < T := Nat.sub_lt (lt_of_lt_of_le (by norm_num) hTtwo) (by norm_num)
  have hpred_gap_bound :
      f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar ≤
        (f x0 - fStar) / (2 : ℝ) ^ (T - 1) :=
    stageGap_le_initialGap_div_pow_two hc hp hMf hT hstage_rate hkp_mem (T - 1) hpred_lt
  have hpred_not_mem :
      y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1) ∉ 𝒬[f | fStar, Mf] :=
    pred_not_mem_selfConcordantQuadraticRegion_of_stoppingStage hTtwo hT
  have hlower :
      1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) <
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar :=
    gap_lower_bound_of_not_mem_selfConcordantQuadraticRegion hpred_not_mem
  have hcoeff_pos : 0 < (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  let coeff : ℝ := (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ)
  have hlower_scaled :
      1 <
        coeff *
          (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar) := by
    have hlower' :
        1 / coeff <
          f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar := by
      simpa [coeff] using hlower
    have hmul :
        1 <
          (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar) * coeff :=
      (div_lt_iff₀ hcoeff_pos).mp hlower'
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  have hupper_scaled :
      coeff *
          (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (T - 1)) - fStar) ≤
        coeff * ((f x0 - fStar) / (2 : ℝ) ^ (T - 1)) := by
    exact mul_le_mul_of_nonneg_left hpred_gap_bound hcoeff_pos.le
  have hpow_lt_scaled :
      (2 : ℝ) ^ (T - 1) < coeff * (f x0 - fStar) := by
    have hbound :
        1 < coeff * ((f x0 - fStar) / (2 : ℝ) ^ (T - 1)) :=
      lt_of_lt_of_le hlower_scaled hupper_scaled
    have hpow_pos : 0 < (2 : ℝ) ^ (T - 1) := by positivity
    have hbound' : 1 < (coeff * (f x0 - fStar)) / (2 : ℝ) ^ (T - 1) := by
      simpa [coeff, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
    have hraw :
        (2 : ℝ) ^ (T - 1) < coeff * (f x0 - fStar) := by
      simpa [coeff] using (lt_div_iff₀ hpow_pos).1 hbound'
    exact hraw
  -- Package the predecessor-stage threshold into the textbook scaled-gap normal form.
  calc
    (2 : ℝ) ^ (T - 1) < (8 : ℝ) * ((Mf : ℝ) ^ (2 : ℕ) * (f x0 - fStar)) := by
      simpa [coeff, mul_assoc, mul_left_comm, mul_comm] using hpow_lt_scaled
    _ = 8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
      rw [scaledGapSquare_eq_mul_gap hgap0.le]

-- Proof sketch: prove by induction that
-- `f (y[innerIterate | kp; p; x0] k) - f* ≤ (1 / 2)^k * (f x₀ - f*)` for all
-- `k ≤ T - 1`, using the source
-- stagewise estimate together with the ceiling lower bound
-- `((1 / 2 : ℝ) ^ (k / (2 * p))) * kp ≤ t[kp; p] k` and the defining property of `kp`. Since
-- the
-- initial point lies outside the source quadratic-convergence region, one first derives the
-- nondegenerate regime `0 < Mf` and `0 < f x₀ - f*`, hence the admissible-index set defining
-- `k_p` is automatically nonempty. Since the preterminal stage output lies outside the source
-- quadratic-convergence region, one has
-- `1 / (8 M_f^2) < f (y[innerIterate | kp; p; x0] (T - 1)) - f*`, which rearranges to
-- `T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`.
/-- Theorem 5.2.5 (1): let `k_p = k[c, M_f; p](f(x₀) - f*)`, and consider
the multistage strategy `(5.2.28)` whose `k`-th stage (`k ≥ 1`) runs the lower-level method for
`t_k = ⌈k_p / 2^((k - 1) / (2p))⌉` steps and stops once
`f(y_k) - f* ≤ 1 / (8 M_f^2)`. If each stage output satisfies the source rate estimate
`f(y_{k+1}) - f* ≤ (2^(5/2) c M_f / t_{k+1}^p) * (f(y_k) - f*)^(3/2)`, then the total
number of stages satisfies `T ≤ 4 + log₂ ((Δ M_f (f(x₀) - f*))^2)`, equivalently
`T ≤ 4 + log₂ (M_f^2 (f(x₀) - f*))`, provided that `p > 0` and the initial point starts outside
the terminal region `𝒬[f | f*, M_f]`. -/
theorem selfConcordantStronglyConvexStrategy_totalStages_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hx0 : x0 ∉ 𝒬[f | fStar, Mf])
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
              Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (T : ℝ) ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
  have hTone : 1 ≤ T :=
    one_le_of_isStronglyConvexMultiStageAccelerationStoppingStage_of_initial_not_mem hT hx0
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hTone
  have hMf : 0 < Mf := Mf_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hgap0 : 0 < f x0 - fStar := gap_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hscaled_sq_pos : 0 < ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
    rw [scaledGapSquare_eq_mul_gap hgap0.le]
    positivity
  have hlog8 :
      Real.logb 2 (8 : ℝ) = 3 := by
    -- Evaluate the base-`2` logarithm of `8 = 2^3` once and reuse it in both branches.
    calc
      Real.logb 2 (8 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
      _ = (3 : ℝ) * Real.logb 2 (2 : ℝ) := by
        simpa using Real.logb_pow (2 : ℝ) (2 : ℝ) 3
      _ = 3 := by
        rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
        ring
  have hlog_target :
      Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) =
        3 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
    rw [Real.logb_mul (by norm_num) hscaled_sq_pos.ne', hlog8]
  have hx0_scaled_gt :
      1 < 8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
    have hx0_notle :
        ¬ (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x0 - fStar) ≤ 1 := by
      rwa [mem_selfConcordantQuadraticRegion_iff] at hx0
    have hx0_gt' : 1 < (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x0 - fStar) :=
      lt_of_not_ge hx0_notle
    calc
      1 < (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x0 - fStar) := hx0_gt'
      _ = 8 * ((Mf : ℝ) ^ (2 : ℕ) * (f x0 - fStar)) := by ring
      _ = 8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
        rw [scaledGapSquare_eq_mul_gap hgap0.le]
  by_cases hc_nonpos : c ≤ 0
  · have hstage_zero :
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (0 + 1)) - fStar ≤ 0 := by
      have hstage0 := hstage_rate 0 hTpos
      have hpow_nonneg :
          0 ≤ Real.rpow (f x0 - fStar) (3 / 2 : ℝ) := Real.rpow_nonneg hgap0.le _
      have hstage_len_pos :
          0 < Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] 0 : ℝ) p := by
        exact Real.rpow_pos_of_pos
          (by
            exact_mod_cast
              one_le_stronglyConvexMultiStageAccelerationStageLength
                (one_le_stronglyConvexHalfGapIndex c Mf p (f x0 - fStar)
                  (stronglyConvexHalfGapAdmissibleIndices_nonempty hp hgap0))
                p 0)
          p
      have hcoeff_nonpos :
          Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) ≤ 0 := by
        have hfirst :
            Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c ≤ 0 := by
          exact mul_nonpos_of_nonneg_of_nonpos
            (le_of_lt (Real.rpow_pos_of_pos zero_lt_two _)) hc_nonpos
        simpa [mul_assoc] using
          mul_nonpos_of_nonpos_of_nonneg hfirst (show 0 ≤ (Mf : ℝ) by exact_mod_cast Mf.2)
      have hquot_nonpos :
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] 0 : ℝ) p) ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hstage_len_pos.le
      have hrhs_nonpos :
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] 0 : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] 0) - fStar)
              (3 / 2 : ℝ) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hquot_nonpos hpow_nonneg
      simpa using le_trans hstage0 hrhs_nonpos
    have hstage_one_mem :
        y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] 1 ∈ 𝒬[f | fStar, Mf] := by
      rw [mem_selfConcordantQuadraticRegion_iff]
      have hcoeff_nonneg : 0 ≤ (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by positivity
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos hcoeff_nonneg hstage_zero) (by norm_num)
    have hT_le_one : T ≤ 1 := hT.2 hstage_one_mem
    have hrhs_gt_one : 1 < 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
      have hlog_pos :
          0 < Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) :=
        Real.logb_pos (b := 2) (hb := by norm_num) hx0_scaled_gt
      calc
        (1 : ℝ) < 1 + Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) := by
          linarith
        _ = 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
          rw [hlog_target]
          ring
    calc
      (T : ℝ) ≤ 1 := by exact_mod_cast hT_le_one
      _ ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := le_of_lt hrhs_gt_one
  · have hc : 0 < c := lt_of_not_ge hc_nonpos
    by_cases hTsmall : T ≤ 1
    · have hrhs_gt_one : 1 < 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
        have hlog_pos :
            0 < Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) :=
          Real.logb_pos (b := 2) (hb := by norm_num) hx0_scaled_gt
        calc
          (1 : ℝ) < 1 + Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) := by
            linarith
          _ = 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
            rw [hlog_target]
            ring
      calc
        (T : ℝ) ≤ 1 := by exact_mod_cast hTsmall
        _ ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := le_of_lt hrhs_gt_one
    · have hTtwo : 2 ≤ T := Nat.succ_le_of_lt (lt_of_not_ge hTsmall)
      have hpred_lt :
          (2 : ℝ) ^ (T - 1) < 8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) :=
        predStagePow_lt_eight_mul_scaledGapSquare hc hp hTtwo hT hstage_rate
      have hlog_left :
          Real.logb 2 ((2 : ℝ) ^ (T - 1)) = ((T - 1 : ℕ) : ℝ) := by
        calc
          Real.logb 2 ((2 : ℝ) ^ (T - 1)) =
              ((T - 1 : ℕ) : ℝ) * Real.logb 2 (2 : ℝ) := by
            simpa using Real.logb_pow (2 : ℝ) (2 : ℝ) (T - 1)
          _ = ((T - 1 : ℕ) : ℝ) := by
            rw [Real.logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]
            ring
      have hpred_log_lt :
          ((T - 1 : ℕ) : ℝ) <
            3 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
        have hraw :
            Real.logb 2 ((2 : ℝ) ^ (T - 1)) <
              Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) :=
          Real.logb_lt_logb (b := 2) (hb := by norm_num) (by positivity) hpred_lt
        calc
          ((T - 1 : ℕ) : ℝ) = Real.logb 2 ((2 : ℝ) ^ (T - 1)) := by
            rw [hlog_left]
          _ < Real.logb 2 (8 * ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) := hraw
          _ = 3 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := hlog_target
      -- Route correction: keep the predecessor index on the nat side until the final cast, then
      -- recover `T = (T - 1) + 1` after the `logb` inequality is already normalized.
      calc
        (T : ℝ) = (((T - 1 : ℕ) + 1 : ℕ) : ℝ) := by
          rw [Nat.sub_add_cancel hTone]
        _ = ((T - 1 : ℕ) : ℝ) + 1 := by
          rw [Nat.cast_add, Nat.cast_one]
        _ ≤
            (3 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ))) + 1 := by
          linarith
        _ = 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) := by
          ring

-- Proof sketch: write
-- `N = ∑_{k=0}^{T-1} t k`, use `Nat.ceil x ≤ x + 1` to bound each stage length by
-- `1 + kp / 2^{k / (2p)}`, sum the geometric series, and insert the stopping-stage estimate from
-- `selfConcordantStronglyConvexStrategy_totalStages_le`.
/-- Theorem 5.2.5 (2): the total number `N` of lower-level iterations in the multistage
strategy `(5.2.28)` by
`4 + log₂ ((Δ M_f (f(x₀) - f*))^2) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, equivalently
`4 + log₂ (M_f^2 (f(x₀) - f*)) + (2^(1 / (2p)) / (2^(1 / (2p)) - 1)) * k_p`, assuming
`p > 0` and `x₀ ∉ 𝒬[f | f*, M_f]`. -/
theorem selfConcordantStronglyConvexStrategy_totalLowerLevelIterations_le
    {T : ℕ}
    (hT :
      IsStronglyConvexMultiStageAccelerationStoppingStage
        innerIterate 𝒬[f | fStar, Mf] (k[c, Mf; p](f x0 - fStar)) p x0 T)
    (hx0 : x0 ∉ 𝒬[f | fStar, Mf])
    (hp : 0 < p)
    (hstage_rate :
      ∀ k : ℕ, k < T →
        f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] (k + 1)) - fStar ≤
          ((Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ)) /
              Real.rpow (t[k[c, Mf; p](f x0 - fStar); p] k : ℝ) p) *
            Real.rpow (f (y[innerIterate | k[c, Mf; p](f x0 - fStar); p; x0] k) - fStar)
              (3 / 2 : ℝ)) :
    (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
        k[c, Mf; p](f x0 - fStar) p T : ℝ) ≤
      4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) +
        (Real.rpow (2 : ℝ) (1 / (2 * p)) /
          (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
        (k[c, Mf; p](f x0 - fStar) : ℝ) := by
  have hgap0 : 0 < f x0 - fStar := gap_pos_of_not_mem_selfConcordantQuadraticRegion hx0
  have hkp : 1 ≤ k[c, Mf; p](f x0 - fStar) :=
    one_le_stronglyConvexHalfGapIndex c Mf p (f x0 - fStar)
      (stronglyConvexHalfGapAdmissibleIndices_nonempty hp hgap0)
  have hstage_bound :
      (T : ℝ) ≤ 4 + Real.logb 2 ((Δ (Mf : ℝ) (f x0 - fStar)) ^ (2 : ℕ)) :=
    selfConcordantStronglyConvexStrategy_totalStages_le hT hx0 hp hstage_rate
  have hschedule_bound :
      (stronglyConvexMultiStageAccelerationTotalLowerLevelIterations
          k[c, Mf; p](f x0 - fStar) p T : ℝ) ≤
        T +
          (Real.rpow (2 : ℝ) (1 / (2 * p)) /
            (Real.rpow (2 : ℝ) (1 / (2 * p)) - 1)) *
          (k[c, Mf; p](f x0 - fStar) : ℝ) :=
    totalLowerLevelIterations_le_stageCount_add_scheduleTail hp hkp
  -- Combine the schedule tail with the already-established stopping-stage count bound.
  linarith

end
