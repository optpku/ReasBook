/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/- Theorem 7.13 lies in Chapter 7's barrier-regularized affine-maximization domain.

Mandatory domain-style sampling before refinement:
- `maximalValueOn` in `Chap07/Definition_7_56.lean`, the chapter owner for optimal values of real
  objectives on feasible sets;
- the direct specialization of `maximalValueOn` in `Chap07/Definition_7_55.lean` to the
  barrier-regularized affine payoff on `hatP ∩ interior Q`;
- `x0 ∈ argmin[hatP ∩ interior Q] F` in `Chap07/Definition_7_52.lean`, the chapter owner for the
  constrained analytic center appearing in the theorem hypotheses;
- `IsMaxOn`, the canonical owner for the attained maximizers of the unsmoothed and smoothed
  problems;
- `affineMax_le_affineBarrierRegularizedPayoff_max_add_logTerm` and
  `affineMax_sub_base_le_sq_sqrt_add_sqrt_of_affineBarrierRegularizedPayoff_max` in
  `Chap07/Lemma_7_11.lean`, the upstream witness-level comparisons whose attained-value forms are
  auxiliary to the owner-level scalar bridge;
- the nearby `.toReal` owner style in `Chap07/Proposition_7_23.lean`.

Best owner abstraction:
- source-facing: Theorem 7.13's comparison between the actual Chapter 7 optimal value
  `maximalValueOn (hatP ∩ Q) ℓ` and the barrier-regularized value
  `maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)` under the
  constrained analytic-center, maximizer, and barrier-segment hypotheses;
- core/canonical: `maximalValueOn`, `argmin[hatP ∩ interior Q] F`, and `IsMaxOn`;
- bridge/view: the scalar logarithmic and square-gap inequalities on the real owner surfaces
  `ℓ⋆.toReal` and `ℓ⋆(β).toReal`.

Primitive data:
- the feasible sets `hatP` and `Q`;
- the barrier term `F`, base point `x₀`, and affine functional `ℓ`;
- the smoothing coefficient `β` and barrier parameter `v`;
- the attained maximizers `xStar` and `xBeta`.

Derived API:
- the actual optimal value `ℓ⋆` and the direct smoothed specialization `ℓ⋆β` of
  `maximalValueOn`;
- the `.toReal` bridge back to the textbook real inequalities;
- the auxiliary scalar gap-bound companion theorem below;
- the closed-form logarithmic comparison bound below.

Source/core/bridge triage:
- source-facing: the numbered theorem `optimal_value_le_smoothed_value_log_barrier_bound`;
- core/canonical: `maximalValueOn`, `argmin[hatP ∩ interior Q] F`, and `IsMaxOn`;
- bridge/view: the scalar logarithmic and square-gap comparison hypotheses on the attained values
  `ℓ xStar` and `Φβ xBeta`, together with the owner equalities supplied by
  `maximalValueOn_eq_of_isMaxOn`.

The previous version promoted the bridge/view layer to the main labeled theorem by assuming the
already-derived scalar gap inequalities as hypotheses on `ℓ⋆.toReal` and `ℓ⋆(β).toReal`, which
does not faithfully encode finiteness in `EReal`. This refinement restores the numbered theorem to
the source-facing layer, with the actual Chapter 7 constrained-center, maximizer, and
barrier-segment hypotheses, and demotes the scalar-gap formulation to a companion theorem stated
on attained real values and lifted back to the owner values by `maximalValueOn_eq_of_isMaxOn`.
-/

variable {hatP Q : Set E} {F : E → ℝ} {x0 xStar xBeta : E}
variable {ℓ : AffineMap ℝ E ℝ} {β v : ℝ}

/- Fixed ambient-context notation for the Chapter 7 optimal value owner `ℓ⋆`. -/
set_option quotPrecheck false in
local notation:max "ℓ⋆" =>
  maximalValueOn (hatP ∩ Q) ℓ

local notation "P₀" => hatP ∩ interior Q
local notation "Φβ" => affineBarrierRegularizedPayoff x0 β ℓ F
set_option quotPrecheck false in
local notation:max "ℓ⋆β" =>
  maximalValueOn P₀ Φβ

/-- Helper for Theorem 7.13: when a maximizer attains `maximalValueOn`, the owner projects back to
the attained real value via `.toReal`. -/
private theorem toReal_maximalValueOn_eq_of_isMaxOn
    {P : Set E} {f : E → ℝ} {x : E} (hx : x ∈ P) (hmax : IsMaxOn f P x) :
    (maximalValueOn P f).toReal = f x := by
  -- First identify the owner with the attained finite `EReal`, then remove the coercion.
  rw [maximalValueOn_eq_of_isMaxOn hx hmax, EReal.toReal_coe]

/-- Helper for Theorem 7.13: a square-gap bound implies the closed-form logarithmic bound that
appears in the theorem statement. -/
private theorem log_gap_term_le_of_square_gap_bound
    {a b c : ℝ} (ha_nonneg : 0 ≤ a) (hc : 0 < c)
    (ha : a ≤ (Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) :
    max (Real.log (a / c)) 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (b / c) := Real.sqrt_nonneg _
  have hone_le : 1 ≤ 1 + Real.sqrt (b / c) := by
    linarith
  have hs_pos : 0 < 1 + Real.sqrt (b / c) := by
    positivity
  have hrhs_nonneg : 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.sqrt (b / c)) :=
      Real.log_nonneg hone_le
    nlinarith
  have hsqrtc_pos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtc_ne : Real.sqrt c ≠ 0 := hsqrtc_pos.ne'
  have hdiv :
      a / c ≤ (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
    -- Normalize the square bound by the positive quantity `c`.
    calc
      a / c ≤ ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / c := by
        exact div_le_div_of_nonneg_right ha hc.le
      _ = ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / (Real.sqrt c) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt hc.le]
      _ = ((Real.sqrt b + Real.sqrt c) / Real.sqrt c) ^ (2 : ℕ) := by
        field_simp [pow_two, hsqrtc_ne]
      _ = (Real.sqrt b / Real.sqrt c + 1) ^ (2 : ℕ) := by
        congr 1
        field_simp [hsqrtc_ne]
      _ = (Real.sqrt (b / c) + 1) ^ (2 : ℕ) := by
        rw [Real.sqrt_div' b hc.le]
      _ = (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
        ring
  by_cases hpos : 0 < a / c
  · -- In the positive case, compare logarithms after the normalization above.
    refine (max_le_iff.mpr ?_)
    constructor
    · calc
        Real.log (a / c) ≤ Real.log ((1 + Real.sqrt (b / c)) ^ (2 : ℕ)) :=
          Real.log_le_log hpos hdiv
        _ = Real.log ((1 + Real.sqrt (b / c)) * (1 + Real.sqrt (b / c))) := by
          rw [pow_two]
        _ = Real.log (1 + Real.sqrt (b / c)) + Real.log (1 + Real.sqrt (b / c)) := by
          rw [Real.log_mul hs_pos.ne' hs_pos.ne']
        _ = 2 * Real.log (1 + Real.sqrt (b / c)) := by
          ring
    · exact hrhs_nonneg
  · have hnonpos : a / c ≤ 0 := le_of_not_gt hpos
    have hquot_nonneg : 0 ≤ a / c := by
      exact div_nonneg ha_nonneg hc.le
    have hquot_zero : a / c = 0 := le_antisymm hnonpos hquot_nonneg
    have hlog_zero : Real.log (a / c) = 0 := by
      simp [hquot_zero]
    simpa [hlog_zero] using hrhs_nonneg

-- Proof sketch: use `maximalValueOn_eq_of_isMaxOn` to identify the owner values `ℓ⋆` and `ℓ⋆(β)`
-- with the attained real values `ℓ xStar` and `Φβ xBeta`. Combining the logarithmic comparison on
-- those attained values with the square-gap bound yields the displayed owner-level estimate.
/-- If `xStar` and `xBeta` attain the unsmoothed and smoothed maxima and their attained values
satisfy the logarithmic and square-gap comparisons produced by the Chapter 7 source hypotheses,
then the actual owner value `ℓ⋆` is bounded above by the smoothed owner value `ℓ⋆(β)` plus the
explicit logarithmic error term. This is the bridge/view form of Theorem 7.13, kept as an
auxiliary companion. -/
theorem optimal_value_le_smoothed_value_log_barrier_bound_of_gap_bounds
    (hβv : 0 < β * v)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxStar_max : IsMaxOn ℓ (hatP ∩ Q) xStar)
    (hx0_mem : x0 ∈ hatP ∩ Q)
    (hxBeta_mem : xBeta ∈ P₀)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hlogGap :
      ℓ xStar ≤
        Φβ xBeta +
          β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0))
    (hsquareGap :
      ℓ xStar - ℓ x0 ≤
        (Real.sqrt (Φβ xBeta - ℓ x0) + Real.sqrt (β * v)) ^ (2 : ℕ)) :
    ℓ⋆ ≤
      ℓ⋆β +
        β * v *
          (1 + 2 * Real.log
            (1 + Real.sqrt (((ℓ⋆β).toReal - ℓ x0) / (β * v)))) := by
  have h_value_star : ℓ⋆ = (ℓ xStar : EReal) :=
    maximalValueOn_eq_of_isMaxOn hxStar_mem hxStar_max
  have h_value_beta : ℓ⋆β = (Φβ xBeta : EReal) :=
    maximalValueOn_eq_of_isMaxOn hxBeta_mem hxBeta_max
  have hgap_nonneg : 0 ≤ ℓ xStar - ℓ x0 := by
    have hbase_le : ℓ x0 ≤ ℓ xStar := isMaxOn_iff.mp hxStar_max x0 hx0_mem
    linarith
  have hlogTerm :
      max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0 ≤
        2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v))) :=
    log_gap_term_le_of_square_gap_bound hgap_nonneg hβv hsquareGap
  have herror :
      β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) ≤
        β * v * (1 + 2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v)))) := by
    -- Upgrade the logarithmic term inside the positive prefactor `β * v`.
    have hinside :
        1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0 ≤
          1 + 2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v))) := by
      linarith
    exact mul_le_mul_of_nonneg_left hinside hβv.le
  have hreal :
      ℓ xStar ≤
        Φβ xBeta +
          β * v * (1 + 2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v)))) := by
    -- Replace the source logarithmic gap term by the closed form given by `hlogTerm`.
    calc
      ℓ xStar ≤
          Φβ xBeta +
            β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) :=
        hlogGap
      _ ≤
          Φβ xBeta +
            β * v * (1 + 2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v)))) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right herror (Φβ xBeta)
  -- Rewrite the owner values to the attained reals and transport the real inequality to `EReal`.
  rw [h_value_star, h_value_beta, EReal.toReal_coe]
  have hreal_ereal :
      ((ℓ xStar : ℝ) : EReal) ≤
        ((Φβ xBeta +
            β * v * (1 + 2 * Real.log (1 + Real.sqrt ((Φβ xBeta - ℓ x0) / (β * v)))) : ℝ) :
          EReal) := by
    exact_mod_cast hreal
  simpa [EReal.coe_add, EReal.coe_mul, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using hreal_ereal

/-- Helper for Theorem 7.13: comparing the smoothed maximizer with an interior segment point from
`x₀` to `xStar` yields the mixed feasible-set inequality used in the source proof. -/
private theorem regularized_gap_bound_along_segment
    (hβ : 0 < β)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P₀)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α))
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    α * (ℓ xStar - ℓ x0) + β * v * Real.log (1 - α) ≤ Φβ xBeta - ℓ x0 := by
  let xα : E := AffineMap.lineMap x0 xStar α
  -- Move the segment point into the strict feasible region using the source hypotheses.
  have hxα_mem : xα ∈ P₀ := by
    simpa [xα, AffineMap.lineMap_apply_module', add_comm] using
      hsegment_mem hxStar_mem hα
  have hFα : F xα ≤ F x0 - v * Real.log (1 - α) := by
    simpa [xα, AffineMap.lineMap_apply_module', add_comm] using
      hF_segment hxStar_mem hα
  have hmaxα : Φβ xα ≤ Φβ xBeta := isMaxOn_iff.mp hxBeta_max xα hxα_mem
  -- Rewrite the affine part along the line segment from `x₀` to `xStar`.
  have hℓα :
      ℓ xα - ℓ x0 = α * (ℓ xStar - ℓ x0) := by
    calc
      ℓ xα - ℓ x0
          = ((AffineMap.lineMap (ℓ x0) (ℓ xStar)) α : ℝ) - ℓ x0 := by
              dsimp [xα]
              rw [AffineMap.apply_lineMap]
      _ = ((1 - α) * ℓ x0 + α * ℓ xStar) - ℓ x0 := by
            simpa using congrArg (fun t : ℝ ↦ t - ℓ x0)
              (AffineMap.lineMap_apply_module (ℓ x0) (ℓ xStar) α)
      _ = α * (ℓ xStar - ℓ x0) := by
            ring
  -- The barrier estimate turns the penalty term into the logarithmic gain.
  have hbarrier :
      β * v * Real.log (1 - α) ≤ -β * (F xα - F x0) := by
    have hFα' : F xα - F x0 ≤ -v * Real.log (1 - α) := by
      linarith
    have hβmul :
        β * (F xα - F x0) ≤ β * (-v * Real.log (1 - α)) :=
      mul_le_mul_of_nonneg_left hFα' hβ.le
    nlinarith
  have hcore :
      α * (ℓ xStar - ℓ x0) + β * v * Real.log (1 - α) ≤ Φβ xα - ℓ x0 := by
    rw [affineBarrierRegularizedPayoff_def]
    nlinarith [hℓα, hbarrier]
  linarith

/-- Helper for Theorem 7.13: the mixed-segment inequality yields the attained logarithmic gap
estimate needed by the owner-level bridge theorem. -/
private theorem attained_log_gap_of_segment_barrier
    (hβ : 0 < β) (hv : 0 < v)
    (hx0_P0 : x0 ∈ P₀)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P₀)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar ≤
      Φβ xBeta +
        β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) := by
  let Δ : ℝ := ℓ xStar - ℓ x0
  let A : ℝ := Φβ xBeta - ℓ x0
  let c : ℝ := β * v
  have hc : 0 < c := mul_pos hβ hv
  -- Evaluating the smoothed maximizer at `x₀` shows that the regularized gap `A` is nonnegative.
  have hA_nonneg : 0 ≤ A := by
    have hx0_le : Φβ x0 ≤ Φβ xBeta := isMaxOn_iff.mp hxBeta_max x0 hx0_P0
    have hPhi0 : Φβ x0 = ℓ x0 := by
      rw [affineBarrierRegularizedPayoff_def]
      ring
    dsimp [A]
    linarith
  by_cases hsmall : Δ ≤ c
  · have hgap :
        Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
      have hmax_nonneg : 0 ≤ max (Real.log (Δ / c)) 0 := le_max_right _ _
      have htail_nonneg : 0 ≤ c * max (Real.log (Δ / c)) 0 :=
        mul_nonneg hc.le hmax_nonneg
      linarith
    dsimp [Δ, A, c] at hgap
    linarith
  · have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    let α : ℝ := 1 - c / Δ
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · have hdiv_lt_one : c / Δ < 1 := (div_lt_one hΔ_pos).2 hlarge
        dsimp [α]
        linarith
      · have hdiv_pos : 0 < c / Δ := div_pos hc hΔ_pos
        dsimp [α]
        linarith
    have hαineq :
        α * Δ + c * Real.log (1 - α) ≤ A := by
      simpa [Δ, A, c] using
        regularized_gap_bound_along_segment hβ hxStar_mem hxBeta_max
          hsegment_mem hF_segment hα_mem
    have h_one_sub : 1 - α = c / Δ := by
      dsimp [α]
      ring
    -- Choosing `α = 1 - c / Δ` converts the segment inequality into the standard log form.
    have hrewrite :
        α * Δ + c * Real.log (1 - α) = Δ - c - c * Real.log (Δ / c) := by
      calc
        α * Δ + c * Real.log (1 - α)
            = (1 - c / Δ) * Δ + c * Real.log (c / Δ) := by
                rw [h_one_sub]
        _ = Δ - c + c * Real.log (c / Δ) := by
              field_simp [hΔ_pos.ne']
        _ = Δ - c - c * Real.log (Δ / c) := by
              rw [Real.log_div hc.ne' hΔ_pos.ne', Real.log_div hΔ_pos.ne' hc.ne']
              ring
    have hlog_nonneg : 0 ≤ Real.log (Δ / c) := by
      have hdiv_gt_one : 1 < Δ / c := (one_lt_div hc).2 hlarge
      exact Real.log_nonneg hdiv_gt_one.le
    have hgap :
        Δ ≤ A + c * (1 + Real.log (Δ / c)) := by
      rw [hrewrite] at hαineq
      linarith
    have hgap' :
        Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
      simpa [max_eq_left hlog_nonneg] using hgap
    dsimp [Δ, A, c] at hgap'
    linarith

/-- Helper for Theorem 7.13: the mixed-segment inequality also yields the attained square-gap
estimate needed by the owner-level bridge theorem. -/
private theorem attained_square_gap_of_segment_barrier
    (hβ : 0 < β) (hv : 0 < v)
    (hx0_P0 : x0 ∈ P₀)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P₀)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar - ℓ x0 ≤
      (Real.sqrt (Φβ xBeta - ℓ x0) + Real.sqrt (β * v)) ^ (2 : ℕ) := by
  let Δ : ℝ := ℓ xStar - ℓ x0
  let A : ℝ := Φβ xBeta - ℓ x0
  let c : ℝ := β * v
  have hc : 0 < c := mul_pos hβ hv
  have hA_nonneg : 0 ≤ A := by
    -- Reuse the base-point comparison to show the smoothed attained gap is nonnegative.
    have hx0_le : Φβ x0 ≤ Φβ xBeta := isMaxOn_iff.mp hxBeta_max x0 hx0_P0
    have hPhi0 : Φβ x0 = ℓ x0 := by
      rw [affineBarrierRegularizedPayoff_def]
      ring
    dsimp [A]
    linarith
  by_cases hsmall : Δ ≤ c
  · have hgap :
        Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsqrtA_nonneg : 0 ≤ Real.sqrt A := Real.sqrt_nonneg A
      have hsqrtc_nonneg : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
      nlinarith [hsmall, hA_nonneg, hsqrtA_nonneg, hsqrtc_nonneg,
        Real.sq_sqrt hA_nonneg, Real.sq_sqrt hc.le]
    dsimp [Δ, A, c] at hgap
    simpa using hgap
  · have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    have hsqrtΔ_ne : Real.sqrt Δ ≠ 0 := (Real.sqrt_pos.2 hΔ_pos).ne'
    have hsqrtc_ne : Real.sqrt c ≠ 0 := (Real.sqrt_pos.2 hc).ne'
    let α : ℝ := 1 - Real.sqrt c / Real.sqrt Δ
    have hsqrt_ratio_lt_one : Real.sqrt c / Real.sqrt Δ < 1 := by
      have hsqrt_lt : Real.sqrt c < Real.sqrt Δ := Real.sqrt_lt_sqrt hc.le hlarge
      exact (div_lt_one (Real.sqrt_pos.2 hΔ_pos)).2 hsqrt_lt
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        linarith
      · have hsqrt_ratio_pos : 0 < Real.sqrt c / Real.sqrt Δ := by
          positivity
        dsimp [α]
        linarith
    have hαineq :
        α * Δ + c * Real.log (1 - α) ≤ A := by
      simpa [Δ, A, c] using
        regularized_gap_bound_along_segment hβ hxStar_mem hxBeta_max
          hsegment_mem hF_segment hα_mem
    have h_one_sub : 1 - α = Real.sqrt c / Real.sqrt Δ := by
      dsimp [α]
      ring
    have h_one_sub_pos : 0 < 1 - α := by
      rw [h_one_sub]
      positivity
    -- Bound `-log (1 - α)` by `α / (1 - α)` before inserting the square-root choice of `α`.
    have hlog_bound : -Real.log (1 - α) ≤ α / (1 - α) := by
      have haux : Real.log ((1 - α)⁻¹) ≤ (1 - α)⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr h_one_sub_pos)
      have haux' : -Real.log (1 - α) ≤ (1 - α)⁻¹ - 1 := by
        simpa [Real.log_inv] using haux
      have hfrac : (1 - α)⁻¹ - 1 = α / (1 - α) := by
        field_simp [h_one_sub_pos.ne']
        ring
      simpa [hfrac] using haux'
    have hlog_term : -c * Real.log (1 - α) ≤ c * α / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hc.le
      have hmul' : c * (-Real.log (1 - α)) ≤ c * (α / (1 - α)) := hmul
      convert hmul' using 1
      · ring
      · ring
    have hmain :
        α * Δ - c * α / (1 - α) ≤ A := by
      nlinarith [hαineq, hlog_term]
    have hexpr :
        α * Δ - c * α / (1 - α) = (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) := by
      let s : ℝ := Real.sqrt Δ
      let t : ℝ := Real.sqrt c
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.sqrt_pos.2 hΔ_pos
      have ht_pos : 0 < t := by
        dsimp [t]
        exact Real.sqrt_pos.2 hc
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have hα_def : α = 1 - t / s := by
        dsimp [α, s, t]
      have hΔ_sq : Δ = s ^ (2 : ℕ) := by
        dsimp [s]
        simpa [pow_two] using (Real.sq_sqrt hΔ_pos.le).symm
      have hc_sq : c = t ^ (2 : ℕ) := by
        dsimp [t]
        simpa [pow_two] using (Real.sq_sqrt hc.le).symm
      have hexpr_st :
          α * Δ - c * α / (1 - α) = (s - t) ^ (2 : ℕ) := by
        rw [hα_def, hΔ_sq, hc_sq]
        have hdenom : 1 - (1 - t / s) = t / s := by
          ring
        rw [hdenom]
        field_simp [hs_ne, ht_ne]
      simpa [s, t] using hexpr_st
    have hsq : (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) ≤ A := by
      rw [← hexpr]
      exact hmain
    have hleft_nonneg : 0 ≤ Real.sqrt Δ - Real.sqrt c := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt hlarge.le)
    have hleft_le : Real.sqrt Δ - Real.sqrt c ≤ Real.sqrt A := by
      exact (Real.le_sqrt hleft_nonneg hA_nonneg).2 (by simpa [pow_two] using hsq)
    have hsqrtΔ_le : Real.sqrt Δ ≤ Real.sqrt A + Real.sqrt c := by
      linarith
    have hgap :
        Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt c := by
        positivity
      have hsq' : (Real.sqrt Δ) ^ (2 : ℕ) ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
        nlinarith [hsqrtΔ_le, hsum_nonneg, Real.sqrt_nonneg Δ]
      simpa [pow_two, Real.sq_sqrt hΔ_pos.le] using hsq'
    dsimp [Δ, A, c] at hgap
    simpa using hgap

-- Proof sketch: the constrained analytic-center hypothesis for `x₀`, the attained maximizers
-- `xStar` and `xBeta`, and the barrier segment estimate first yield the attained-value
-- inequalities from Lemma 7.11. Applying the companion bridge theorem above lifts those
-- inequalities to the owner values `ℓ⋆` and `ℓ⋆(β)` and gives the displayed bound.
/-- Theorem 7.13: if `x₀` is a constrained analytic center of the strict feasible region
`hatP ∩ interior Q`, if `xStar` maximizes `ℓ` on `hatP ∩ Q`, if `xBeta` maximizes the
barrier-regularized payoff on `hatP ∩ interior Q`, and if every open segment from `x₀` to a
feasible point of `hatP ∩ Q` stays in the strict feasible region and satisfies the displayed
barrier estimate, then the actual optimal value `ℓ⋆` is bounded above by the smoothed value
`ℓ⋆(β)` plus the explicit logarithmic error term. -/
theorem optimal_value_le_smoothed_value_log_barrier_bound
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P₀] F)
    (hxStar_mem : xStar ∈ hatP ∩ Q)
    (hxStar_max : IsMaxOn ℓ (hatP ∩ Q) xStar)
    (hxBeta_mem : xBeta ∈ P₀)
    (hxBeta_max : IsMaxOn Φβ P₀ xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P₀)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ hatP ∩ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ⋆ ≤
      ℓ⋆β +
        β * v *
          (1 + 2 * Real.log
            (1 + Real.sqrt (((ℓ⋆β).toReal - ℓ x0) / (β * v)))) :=
    by
  -- Route correction: work directly with interior segment points from `x₀` to `xStar`,
  -- rather than trying to force the single-set API of `Lemma_7_11`.
  have hx0_P0 : x0 ∈ P₀ := (mem_constrainedArgmin_iff.mp hx0).1
  have hx0_mem : x0 ∈ hatP ∩ Q := by
    exact ⟨hx0_P0.1, interior_subset hx0_P0.2⟩
  -- First obtain the attained-value inequalities on `ℓ xStar` and `Φβ xBeta`.
  have hlogGap :
      ℓ xStar ≤
        Φβ xBeta +
          β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) :=
    attained_log_gap_of_segment_barrier hβ hv hx0_P0 hxStar_mem hxBeta_max
      hsegment_mem hF_segment
  have hsquareGap :
      ℓ xStar - ℓ x0 ≤
        (Real.sqrt (Φβ xBeta - ℓ x0) + Real.sqrt (β * v)) ^ (2 : ℕ) :=
    attained_square_gap_of_segment_barrier hβ hv hx0_P0 hxStar_mem hxBeta_max
      hsegment_mem hF_segment
  -- Then lift those real inequalities to the owner values `ℓ⋆` and `ℓ⋆(β)`.
  exact optimal_value_le_smoothed_value_log_barrier_bound_of_gap_bounds
    (hβv := mul_pos hβ hv)
    hxStar_mem hxStar_max hx0_mem hxBeta_mem hxBeta_max hlogGap hsquareGap

end
