/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/- Lemma 7.11 lies in Chapter 7's barrier-regularized affine-maximization domain.

Mandatory domain-style sampling before refinement:
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner for
  constrained minimizers and the canonical feasibility-plus-`IsMinOn` bridge;
- `IsMaxOn` in mathlib's `Order/Filter/Extr`, the canonical maximality predicate on a set;
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for supremum values of real
  objectives on a feasible set;
- `Uβ` / `Argmaxβ` in `Chap07/Definition_7_53`, the nearby barrier-regularized maximization API
  that likewise separates a source-facing payoff from its maximizer layer.

Best owner abstraction:
- source-facing: the affine payoff `x ↦ ℓ x - β (F x - F x₀)` and Lemma 7.11's attained-maximizer
  comparison estimates;
- core/canonical: the constrained-minimizer owner `argmin[P] F` for the base point `x₀`, together
  with mathlib's `IsMaxOn` for the two maximizers;
- bridge/view: `maximalValueOn` from `Definition_7_56`, used downstream by `Definition_7_55` to
  pass from attained maximizers to the value notation `ℓ⋆(β)`.

Primitive data:
- the feasible set `P`;
- the barrier term `F`;
- the base point `x₀`;
- the affine functional `ℓ`;
- the regularization parameter `β`.

Derived API:
- the barrier-regularized payoff owner `affineBarrierRegularizedPayoff`;
- the attained-maximizer comparison lemmas below.

Source/core/bridge triage:
- source-facing: the payoff owner and the three comparison lemmas from Lemma 7.11;
- core/canonical: `argmin[P] F` and `IsMaxOn`;
- bridge/view: the `maximalValueOn` specialization in `Definition_7_55`.

The refinement keeps the source-facing payoff owner local to this file. The statement-level repair
is to reuse the existing constrained-argmin owner for `x₀` and to encode the two maximizers with
their missing feasibility data instead of bare `IsMaxOn` hypotheses, whose mathlib meaning alone
does not express attainment on `P`.
-/

/-- The barrier-regularized affine payoff
`ℓ(x) - β (F(x) - F(x₀))` attached to an affine functional `ℓ`, a barrier term `F`, and a base
point `x₀`. -/
def affineBarrierRegularizedPayoff
    (x0 : E) (β : ℝ) (ℓ : AffineMap ℝ E ℝ) (F : E → ℝ) (x : E) : ℝ :=
  ℓ x - β * (F x - F x0)

-- Proof sketch: unfold `affineBarrierRegularizedPayoff`.
/-- Expanding `affineBarrierRegularizedPayoff x₀ β ℓ F x` gives the affine value `ℓ(x)` minus the
barrier penalty `β (F(x) - F(x₀))`. -/
theorem affineBarrierRegularizedPayoff_def
    (x0 : E) (β : ℝ) (ℓ : AffineMap ℝ E ℝ) (F : E → ℝ) (x : E) :
    affineBarrierRegularizedPayoff x0 β ℓ F x =
      ℓ x - β * (F x - F x0) :=
  rfl

section Lemma711

variable {P : Set E} {F : E → ℝ} {ℓ : AffineMap ℝ E ℝ}
variable {x0 xStar xBeta : E} {β v : ℝ}

local notation "Φβ" => affineBarrierRegularizedPayoff x0 β ℓ F

-- Proof sketch: since `x₀` minimizes `F` on `P`, every feasible value satisfies
-- `F(x) - F(x₀) ≥ 0`. Hence the regularized payoff is bounded above pointwise on `P` by the
-- affine functional `ℓ`, and comparing the maximizers `xBeta` and `xStar` gives the result.
/-- Lemma 7.11 (1): if `xBeta` belongs to `P` and maximizes the barrier-regularized affine payoff
there, `xStar` belongs to `P` and maximizes `ℓ` there, and `x₀` minimizes `F` on `P`, then
`ℓ⋆(β) ≤ ℓ⋆`. -/
theorem affineBarrierRegularizedPayoff_max_le_affine_max
    (hβ : 0 < β)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta) :
    Φβ xBeta ≤ ℓ xStar := by
  let _ := hxStar_mem
  let _ := hxBeta_max
  rcases mem_constrainedArgmin_iff.mp hx0 with ⟨_, hx0_min⟩
  -- The minimizer property at `x₀` makes the barrier penalty nonnegative at every feasible point.
  have hpayoff_le : Φβ xBeta ≤ ℓ xBeta := by
    rw [affineBarrierRegularizedPayoff_def]
    have hmin := (isMinOn_iff.mp hx0_min) xBeta hxBeta_mem
    nlinarith
  -- Compare the affine value at `xBeta` with the attained affine maximum at `xStar`.
  have hmax := (isMaxOn_iff.mp hxStar_max) xBeta hxBeta_mem
  exact hpayoff_le.trans hmax

/-- Helper for Lemma 7.11: along the segment from `x₀` to `xStar`, the affine increment of `ℓ`
matches the scalar increment `α (ℓ(xStar) - ℓ(x₀))`. -/
lemma affine_value_sub_base_on_segment
    (α : ℝ) :
    ℓ (x0 + α • (xStar - x0)) - ℓ x0 = α * (ℓ xStar - ℓ x0) := by
  -- Rewrite the geometric segment as the canonical affine line map.
  have hline : x0 + α • (xStar - x0) = AffineMap.lineMap x0 xStar α := by
    simp [AffineMap.lineMap_apply_module', add_comm]
  -- Transport the segment through `ℓ` and simplify the resulting scalar line map.
  rw [hline, AffineMap.apply_lineMap, AffineMap.lineMap_apply_module]
  ring

/-- Helper for Lemma 7.11: the attained regularized maximum is at least the base affine value
`ℓ(x₀)`. -/
lemma base_value_le_affineBarrierRegularizedPayoff_max
    (hx0 : x0 ∈ argmin[P] F)
    (hxBeta_max : IsMaxOn Φβ P xBeta) :
    ℓ x0 ≤ Φβ xBeta := by
  rcases mem_constrainedArgmin_iff.mp hx0 with ⟨hx0_mem, _⟩
  -- Evaluate maximality at the feasible base point `x₀`.
  have hmax := (isMaxOn_iff.mp hxBeta_max) x0 hx0_mem
  -- The regularized payoff equals `ℓ x₀` because the barrier gap vanishes at the base point.
  simpa [affineBarrierRegularizedPayoff_def] using hmax

/-- Helper for Lemma 7.11: every admissible segment point from `x₀` to `xStar` yields the common
regularized-gap inequality used in both quantitative estimates. -/
lemma regularized_gap_bound_along_segment
    (hβ : 0 < β)
    (hxStar_mem : xStar ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α))
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    α * (ℓ xStar - ℓ x0) + β * v * Real.log (1 - α) ≤ Φβ xBeta - ℓ x0 := by
  -- Compare the regularized maximizer with the feasible segment point toward `xStar`.
  have hsegment_point_mem : x0 + α • (xStar - x0) ∈ P :=
    hsegment_mem hxStar_mem hα
  have hmax := (isMaxOn_iff.mp hxBeta_max) (x0 + α • (xStar - x0)) hsegment_point_mem
  -- The barrier estimate turns the penalty term into a logarithmic lower bound.
  have hsegment_payoff :
      ℓ (x0 + α • (xStar - x0)) + β * v * Real.log (1 - α) ≤
        Φβ (x0 + α • (xStar - x0)) := by
    rw [affineBarrierRegularizedPayoff_def]
    have hbarrier := hF_segment hxStar_mem hα
    nlinarith
  -- Rewrite the affine term on the segment and subtract the base value `ℓ x₀`.
  have hchain :
      ℓ (x0 + α • (xStar - x0)) + β * v * Real.log (1 - α) ≤ Φβ xBeta :=
    hsegment_payoff.trans hmax
  have haffine :=
    affine_value_sub_base_on_segment (ℓ := ℓ) (x0 := x0) (xStar := xStar) α
  linarith

-- Proof sketch: evaluate the regularized payoff at the segment points
-- `x₀ + α • (xStar - x₀)`, use the affine identity for `ℓ`, and apply the barrier estimate
-- `F(x₀ + α • (xStar - x₀)) ≤ F(x₀) - v log(1 - α)`. Optimizing the resulting one-variable lower
-- bound in `α` yields the logarithmic error term.
/-- Lemma 7.11 (2): under the same attained-maximizer setup, if every segment from `x₀` to a point
of `P` stays in `P` and satisfies the displayed barrier estimate, then
`ℓ⋆ ≤ ℓ⋆(β) + β v (1 + [log ((ℓ⋆ - ℓ₀) / (β v))]_+)`. -/
theorem affineMax_le_affineBarrierRegularizedPayoff_max_add_logTerm
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar ≤
      Φβ xBeta +
        β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) := by
  let _ := hxStar_max
  let _ := hxBeta_mem
  let Δ : ℝ := ℓ xStar - ℓ x0
  let A : ℝ := Φβ xBeta - ℓ x0
  let c : ℝ := β * v
  have hc : 0 < c := by
    simpa [c] using mul_pos hβ hv
  have hA : 0 ≤ A := by
    -- Compare the regularized maximizer with the feasible base point `x₀`.
    have hbase :=
      base_value_le_affineBarrierRegularizedPayoff_max
        (x0 := x0) (β := β) (ℓ := ℓ) (F := F) (P := P) (xBeta := xBeta) hx0 hxBeta_max
    simpa [A] using sub_nonneg.mpr hbase
  by_cases hΔ_le_c : Δ ≤ c
  · -- In the small-gap regime, the logarithmic correction is nonnegative and dominates `Δ`.
    have hmax_nonneg : 0 ≤ max (Real.log (Δ / c)) 0 :=
      le_max_right _ _
    have hc_le_term : c ≤ c * (1 + max (Real.log (Δ / c)) 0) := by
      nlinarith [hc.le, hmax_nonneg]
    have hbound : Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
      linarith
    have hbound' :
        ℓ xStar - ℓ x0 ≤
          Φβ xBeta - ℓ x0 + β * v * (1 + max (Real.log ((ℓ xStar - ℓ x0) / (β * v))) 0) := by
      simpa [Δ, A, c] using hbound
    linarith
  · -- In the large-gap regime, optimize the segment estimate at `α = 1 - c / Δ`.
    have hΔ_gt_c : c < Δ :=
      lt_of_not_ge hΔ_le_c
    have hΔ_pos : 0 < Δ :=
      lt_trans hc hΔ_gt_c
    have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
    have hc_ne : c ≠ 0 := ne_of_gt hc
    let α : ℝ := 1 - c / Δ
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        have hdiv_lt_one : c / Δ < 1 := by
          rw [div_lt_iff₀ hΔ_pos]
          simpa using hΔ_gt_c
        linarith
      · dsimp [α]
        have hdiv_pos : 0 < c / Δ := div_pos hc hΔ_pos
        linarith
    have hsegment :=
      regularized_gap_bound_along_segment
        (x0 := x0) (β := β) (ℓ := ℓ) (F := F) (P := P)
        (xStar := xStar) (xBeta := xBeta) (v := v)
        hβ hxStar_mem hxBeta_max hsegment_mem hF_segment hα_mem
    have halpha_mul : α * Δ = Δ - c := by
      dsimp [α]
      field_simp [hΔ_ne]
    have hone_sub_alpha : 1 - α = c / Δ := by
      dsimp [α]
      ring
    have hsegment' : Δ - c + c * Real.log (c / Δ) ≤ A := by
      rw [halpha_mul, hone_sub_alpha] at hsegment
      simpa [Δ, A, c] using hsegment
    have hlog :
        Real.log (c / Δ) = -Real.log (Δ / c) := by
      have hratio : c / Δ = (Δ / c)⁻¹ := by
        field_simp [hΔ_ne, hc_ne]
      rw [hratio, Real.log_inv]
    have hratio_ge_one : 1 ≤ Δ / c := by
      have hratio_gt_one : 1 < Δ / c := by
        rw [lt_div_iff₀ hc]
        simpa using hΔ_gt_c
      exact hratio_gt_one.le
    have hlog_nonneg : 0 ≤ Real.log (Δ / c) :=
      Real.log_nonneg hratio_ge_one
    have hbound : Δ ≤ A + c * (1 + Real.log (Δ / c)) := by
      have hsegment'' : Δ - c - c * Real.log (Δ / c) ≤ A := by
        calc
          Δ - c - c * Real.log (Δ / c)
              = Δ - c + c * Real.log (c / Δ) := by
                  rw [hlog]
                  ring
          _ ≤ A := hsegment'
      linarith
    have hmax_eq : max (Real.log (Δ / c)) 0 = Real.log (Δ / c) :=
      max_eq_left hlog_nonneg
    have hbound' :
        ℓ xStar - ℓ x0 ≤
          Φβ xBeta - ℓ x0 + β * v * (1 + Real.log ((ℓ xStar - ℓ x0) / (β * v))) := by
      simpa [Δ, A, c] using hbound
    rw [hmax_eq]
    linarith

/-- Helper for Lemma 7.11: on the interval `0 ≤ α < 1`, the singular logarithmic term is bounded
by the rational term `α / (1 - α)`. -/
lemma neg_log_one_sub_le_div_of_mem_Ico
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    -Real.log (1 - α) ≤ α / (1 - α) := by
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hlog_aux :
      -Real.log (1 - α) ≤ (1 - α)⁻¹ - 1 := by
    simpa [Real.log_inv] using
      (Real.log_le_sub_one_of_pos (x := (1 - α)⁻¹) (inv_pos.mpr hone_sub_pos))
  have hrewrite : (1 - α)⁻¹ - 1 = α / (1 - α) := by
    field_simp [hone_sub_pos.ne']
    ring
  rwa [hrewrite] at hlog_aux

-- Proof sketch: start from the same segment lower bound for the regularized payoff, rewrite it
-- as `Δ ≤ A / α - (β v / α) log(1 - α)`, use `log (1 + t) ≤ t`, and minimize the resulting
-- expression `A / α + B / (1 - α)` over `α ∈ (0, 1)` to obtain the square bound.
/-- Lemma 7.11 (3): under the same attained-maximizer and barrier-segment hypotheses, the affine
gap from `x₀` to the maximizer `xStar` is bounded by
`(sqrt (ℓ⋆(β) - ℓ₀) + sqrt (β v))²`. -/
theorem affineMax_sub_base_le_sq_sqrt_add_sqrt_of_affineBarrierRegularizedPayoff_max
    (hβ : 0 < β) (hv : 0 < v)
    (hx0 : x0 ∈ argmin[P] F)
    (hxStar_mem : xStar ∈ P)
    (hxStar_max : IsMaxOn ℓ P xStar)
    (hxBeta_mem : xBeta ∈ P)
    (hxBeta_max : IsMaxOn Φβ P xBeta)
    (hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        x0 + α • (x - x0) ∈ P)
    (hF_segment :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃α : ℝ⦄, α ∈ Set.Ico (0 : ℝ) 1 →
        F (x0 + α • (x - x0)) ≤ F x0 - v * Real.log (1 - α)) :
    ℓ xStar - ℓ x0 ≤
      (Real.sqrt (Φβ xBeta - ℓ x0) +
        Real.sqrt (β * v)) ^ (2 : ℕ) := by
  let _ := hxStar_max
  let _ := hxBeta_mem
  let Δ : ℝ := ℓ xStar - ℓ x0
  let A : ℝ := Φβ xBeta - ℓ x0
  let c : ℝ := β * v
  have hc : 0 < c := by
    simpa [c] using mul_pos hβ hv
  have hA : 0 ≤ A := by
    -- Compare the regularized maximizer with the feasible base point `x₀`.
    have hbase :=
      base_value_le_affineBarrierRegularizedPayoff_max
        (x0 := x0) (β := β) (ℓ := ℓ) (F := F) (P := P) (xBeta := xBeta) hx0 hxBeta_max
    simpa [A] using sub_nonneg.mpr hbase
  by_cases hΔ_le_c : Δ ≤ c
  · -- If the affine gap is already at most `c = β v`, the square bound is immediate.
    have hc_bound : c ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      nlinarith [hA, hc.le, Real.sq_sqrt hA, Real.sq_sqrt hc.le,
        Real.sqrt_nonneg A, Real.sqrt_nonneg c]
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      linarith
    simpa [Δ, A, c] using hbound
  · -- Otherwise, use the segment point with `1 - α = sqrt c / sqrt Δ`.
    have hΔ_gt_c : c < Δ :=
      lt_of_not_ge hΔ_le_c
    have hΔ_pos : 0 < Δ :=
      lt_trans hc hΔ_gt_c
    let α : ℝ := 1 - Real.sqrt c / Real.sqrt Δ
    have hsqrt_ratio_lt_one : Real.sqrt c / Real.sqrt Δ < 1 := by
      have hsqrt_lt : Real.sqrt c < Real.sqrt Δ := Real.sqrt_lt_sqrt hc.le hΔ_gt_c
      exact (div_lt_one (Real.sqrt_pos.2 hΔ_pos)).2 hsqrt_lt
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        linarith
      · dsimp [α]
        have hratio_pos : 0 < Real.sqrt c / Real.sqrt Δ := by
          positivity
        linarith
    have hsegment :=
      regularized_gap_bound_along_segment
        (x0 := x0) (β := β) (ℓ := ℓ) (F := F) (P := P)
        (xStar := xStar) (xBeta := xBeta) (v := v)
        hβ hxStar_mem hxBeta_max hsegment_mem hF_segment hα_mem
    have hone_sub_alpha : 1 - α = Real.sqrt c / Real.sqrt Δ := by
      dsimp [α]
      ring
    have hone_sub_pos : 0 < 1 - α := by
      rw [hone_sub_alpha]
      positivity
    have hlog_bound : -Real.log (1 - α) ≤ α / (1 - α) :=
      neg_log_one_sub_le_div_of_mem_Ico hα_mem
    have hlog_term : -c * Real.log (1 - α) ≤ c * α / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hc.le
      have hmul' : c * (-Real.log (1 - α)) ≤ c * (α / (1 - α)) := hmul
      convert hmul' using 1
      · ring
      · ring
    have hmain : α * Δ - c * α / (1 - α) ≤ A := by
      nlinarith [hsegment, hlog_term]
    -- Rewrite the square-root choice of `α` into the exact quadratic expression.
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
    have hsquare : (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) ≤ A := by
      rw [← hexpr]
      exact hmain
    have hsqrt_sub_nonneg : 0 ≤ Real.sqrt Δ - Real.sqrt c := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt hΔ_gt_c.le)
    have hsqrt_le : Real.sqrt Δ - Real.sqrt c ≤ Real.sqrt A := by
      exact (Real.le_sqrt hsqrt_sub_nonneg hA).2 (by simpa [pow_two] using hsquare)
    have hsqrt_sum : Real.sqrt Δ ≤ Real.sqrt A + Real.sqrt c := by
      linarith
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt c := by
        positivity
      have hsq' : (Real.sqrt Δ) ^ (2 : ℕ) ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
        nlinarith [hsqrt_sum, hsum_nonneg, Real.sqrt_nonneg Δ]
      simpa [pow_two, Real.sq_sqrt hΔ_pos.le] using hsq'
    simpa [Δ, A, c] using hbound

end Lemma711

end
