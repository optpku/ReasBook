/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_10
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_34
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_11
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_31
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped BigOperators ProbabilityTheory ProjectedSubgradientErgodicNotation
open MeasureTheory
open InnerProductSpace (toDualMap)

noncomputable section

section

variable {Ω : Type v}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  stochastic_projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  stochastic_projected_subgradient_method_iterate C h_problem.feasible_nonempty
    h_problem.feasible_closed h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

/- Theorem 8.37 is `source-facing`: it states the stochastic strongly-convex `O(1 / k)` rate for
the actual stochastic projected-subgradient iterates and for their weighted averages. The owner
abstractions already present in the chapter are the pathwise iterate sequence
`stochastic_projected_subgradient_method`, the running-best objective value
`best_achieved_function_value`, the stochastic oracle package
`StochasticProjectedSubgradientOracle`, the standing constrained problem class
`IsConstrainedConvexProblem`, and the canonical strong-convexity predicate
`StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)`, together with the chapter owner
`projected_subgradient_strongly_convex_average_weight` for the canonical ergodic weights
`α_n^k`. The only new data object needed by the source is the averaged random iterate `x^(k)`, so
it is exposed directly as a concrete weighted sum of the sampled iterates rather than via a
surrogate wrapper. -/

/-- The weighted average random iterate `x^(k)` used in the strongly convex stochastic
projected-subgradient rate. It uses the canonical weight convention from Theorem 8.31, so
`x^(0) = x^0` and for `k > 0` the coefficients are `α_n^k = 2 n / (k (k + 1))`. -/
def stochastic_projected_subgradient_strongly_convex_average_iterate
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (g : ℕ → C → Ω → E) (t : ℕ → ℝ) (x0 : C) (k : ℕ) : Ω → E :=
  let xSeq :=
    stochastic_projected_subgradient_method_iterate C h_problem.feasible_nonempty
      h_problem.feasible_closed h_problem.feasible_convex g t x0
  fun ω ↦ Finset.sum (Finset.range (k + 1)) fun n ↦ α[k](n) • xSeq n ω

local notation "x^(" k ")" =>
  stochastic_projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k

/-- Evaluating the stochastic strongly convex averaged iterate at `k` gives the weighted sum
`∑_{n=0}^k α_n^k x^n(ω)` with the canonical Chapter 8 ergodic weights `α_n^k`. -/
theorem stochastic_projected_subgradient_strongly_convex_average_iterate_eq_sum
    (k : ℕ) :
    x^(k) =
      fun ω ↦ Finset.sum (Finset.range (k + 1)) fun n ↦ α[k](n) • x̄[n] ω := by
  rfl

-- Proof sketch: unfold
-- `stochastic_projected_subgradient_strongly_convex_average_iterate` at `k = 0`; the range has
-- only the index `0`, and the degenerate branch in the weight formula makes the unique
-- coefficient equal to `1`.
/-- The stochastic strongly convex weighted average at `k = 0` is the initial random iterate
`x^0`. -/
theorem stochastic_projected_subgradient_strongly_convex_average_iterate_zero (ω : Ω) :
    x^(0) ω = x̄[0] ω := by
  -- Unfold the degenerate weighted average; only the index `0` survives with coefficient `1`.
  rw [stochastic_projected_subgradient_strongly_convex_average_iterate_eq_sum]
  simp

section

omit [CompleteSpace E]

/-- Helper for Theorem 8.37: a Euclidean subgradient of the real-valued restriction
`x ↦ (f x).toReal` at a finite point yields a genuine subgradient of the original extended-real
objective. -/
lemma toDualMap_mem_subdifferential_of_mem_euclideanSubdifferentialAt_toReal
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {x v : E} (hx : x ∈ effective_domain f)
    (hv : v ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) x) :
    (toDualMap ℝ E v : Module.Dual ℝ E) ∈ subdifferential f x := by
  -- Rewrite the Euclidean membership into the real-valued subgradient inequality.
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hv
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hx, ?_⟩
  intro y hy
  -- Finite values on the feasible domain let the real inequality lift back to `EReal`.
  have hx_top : f x ≠ ⊤ := ne_of_lt hx
  have hy_top : f y ≠ ⊤ := ne_of_lt hy
  have hx_bot : f x ≠ ⊥ := h_problem.ne_bot x
  have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
  have hvy : (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := hv y
  have hvyE :
      (((f x).toReal + inner ℝ v (y - x) : ℝ) : EReal) ≤
        (((f y).toReal : ℝ) : EReal) := by
    exact EReal.coe_le_coe (by simpa [ge_iff_le] using hvy)
  simpa [InnerProductSpace.toDualMap_apply_apply, EReal.coe_toReal hx_top hx_bot,
    EReal.coe_toReal hy_top hy_bot, EReal.coe_add, ge_iff_le] using hvyE

/-- Helper for Theorem 8.37: every Euclidean subgradient at a feasible point supports the
strongly convex objective at an optimal point with the quadratic correction term. -/
lemma strongly_convex_support_at_optimal_point
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ) {x xStar v : E} (hxC : x ∈ C) (hxStar : xStar ∈ XStar)
    (hv : v ∈ euclideanSubdifferentialAt (fun y ↦ (f y).toReal) x) :
    ((f x).toReal - fOpt) + (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ inner ℝ v (x - xStar) := by
  -- Route correction: avoid the broken Chapter 5 first-order-support file by shifting `f` by the
  -- affine functional `y ↦ -⟪v, y⟫`. The Euclidean subgradient inequality then says `x`
  -- minimizes the shifted objective on all of `E`, so Theorem 5.25 applies directly.
  let fShift : E → EReal := fun y ↦ f y + (((-inner ℝ v y : ℝ) : EReal))
  have hx_dom : x ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxC)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hv_support : ∀ y : E, (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := by
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff] at hv
    exact hv
  -- The affine shift preserves the effective domain because the added term is always finite.
  have hdomShift : effective_domain fShift = effective_domain f := by
    ext y
    constructor
    · intro hy
      change f y < ⊤
      refine lt_top_iff_ne_top.mpr ?_
      exact
        (EReal.add_ne_top_iff_of_ne_bot_of_ne_top (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).1
          (ne_of_lt hy)
    · intro hy
      simpa [fShift] using EReal.add_lt_top (ne_of_lt hy) (EReal.coe_ne_top _)
  have hne_bot_shift : ∀ y, fShift y ≠ ⊥ := by
    intro y
    simpa [fShift, EReal.add_ne_bot_iff] using
      (show f y ≠ ⊥ ∧ (((-inner ℝ v y : ℝ) : EReal) ≠ ⊥) from
        ⟨h_problem.ne_bot y, EReal.coe_ne_bot _⟩)
  -- On the finite domain, the shifted real-valued objective is `y ↦ (f y).toReal - ⟪v, y⟫`.
  have htoRealShift :
      ∀ {y : E}, y ∈ effective_domain fShift →
        (fShift y).toReal = (f y).toReal - inner ℝ v y := by
    intro y hy
    have hy_dom : y ∈ effective_domain f := by
      simpa [hdomShift] using hy
    have hy_top : f y ≠ ⊤ := ne_of_lt hy_dom
    have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
    rw [show fShift y = f y + (((-inner ℝ v y : ℝ) : EReal)) by rfl,
      EReal.toReal_add hy_top hy_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
    simp [sub_eq_add_neg]
  -- The strong-convexity modulus is unchanged because affine terms cancel in the Jensen defect.
  have hstrongShift :
      StrongConvexOn (effective_domain fShift) σ (fun y ↦ (fShift y).toReal) := by
    refine ⟨?_, ?_⟩
    · simpa [hdomShift] using h_strong.1
    · intro y hy z hz a b ha hb hab
      have hy_dom : y ∈ effective_domain f := by
        simpa [hdomShift] using hy
      have hz_dom : z ∈ effective_domain f := by
        simpa [hdomShift] using hz
      have hyz_dom : a • y + b • z ∈ effective_domain f := h_strong.1 hy_dom hz_dom ha hb hab
      have hyz_shift : a • y + b • z ∈ effective_domain fShift := by
        simpa [hdomShift] using hyz_dom
      have hbase := h_strong.2 hy_dom hz_dom ha hb hab
      have hinner :
          inner ℝ v (a • y + b • z) = a * inner ℝ v y + b * inner ℝ v z := by
        rw [inner_add_right, inner_smul_right, inner_smul_right]
      calc
        (fShift (a • y + b • z)).toReal =
            (f (a • y + b • z)).toReal - inner ℝ v (a • y + b • z) := by
              exact htoRealShift hyz_shift
        _ ≤ a * (f y).toReal + b * (f z).toReal -
            a * b * ((σ / 2) * ‖y - z‖ ^ (2 : ℕ)) - inner ℝ v (a • y + b • z) := by
              exact sub_le_sub_right hbase _
        _ = a * ((fShift y).toReal) + b * ((fShift z).toReal) -
            a * b * ((σ / 2) * ‖y - z‖ ^ (2 : ℕ)) := by
              rw [htoRealShift hy, htoRealShift hz, hinner]
              ring
  -- The Euclidean subgradient inequality exactly says that `x` minimizes the shifted objective.
  have hminShift : IsMinOn fShift Set.univ x := by
    rw [isMinOn_univ_iff]
    intro y
    by_cases hy_dom : y ∈ effective_domain f
    · have hx_top : f x ≠ ⊤ := ne_of_lt hx_dom
      have hx_bot : f x ≠ ⊥ := h_problem.ne_bot x
      have hy_top : f y ≠ ⊤ := ne_of_lt hy_dom
      have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
      have hsub : (f y).toReal ≥ (f x).toReal + inner ℝ v (y - x) := hv_support y
      have hinner_sub : inner ℝ v (y - x) = inner ℝ v y - inner ℝ v x := by
        rw [inner_sub_right]
      have hreal :
          (f x).toReal - inner ℝ v x ≤ (f y).toReal - inner ℝ v y := by
        nlinarith [hsub, hinner_sub]
      have hcoe :
          ((((f x).toReal - inner ℝ v x : ℝ) : EReal) ≤
            (((f y).toReal - inner ℝ v y : ℝ) : EReal)) := EReal.coe_le_coe hreal
      simpa [fShift, EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
        EReal.coe_add, sub_eq_add_neg] using hcoe
    · have hy_top : f y = ⊤ := le_antisymm le_top (not_lt.mp hy_dom)
      simp [fShift, hy_top]
  have hxShift_dom : x ∈ effective_domain fShift := by
    simpa [hdomShift] using hx_dom
  have hxStarShift_dom : xStar ∈ effective_domain fShift := by
    simpa [hdomShift] using hxStar_dom
  let φ : E → ℝ := fun y ↦ (fShift y).toReal
  have hminReal : ∀ {y : E}, y ∈ effective_domain fShift → φ x ≤ φ y := by
    intro y hy
    have hle : fShift x ≤ fShift y := (isMinOn_iff.mp hminShift) y (by simp)
    exact EReal.toReal_le_toReal hle (hne_bot_shift x) (ne_of_lt hy)
  let c : ℝ := (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)
  have happrox :
      ∀ n : ℕ, φ xStar - φ x ≥ (n : ℝ) / (n + 1 : ℝ) * c := by
    intro n
    let a : ℝ := (n : ℝ) / (n + 1 : ℝ)
    let b : ℝ := 1 / (n + 1 : ℝ)
    have ha : 0 ≤ a := by
      positivity
    have hb : 0 ≤ b := by
      positivity
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    have hm_dom : a • x + b • xStar ∈ effective_domain fShift :=
      hstrongShift.1 hxShift_dom hxStarShift_dom ha hb hab
    have hmin_mid : φ x ≤ φ (a • x + b • xStar) :=
      hminReal hm_dom
    have hstrong_mid :
        φ (a • x + b • xStar) ≤
          a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) :=
      hstrongShift.2 hxShift_dom hxStarShift_dom ha hb hab
    have hcombine :
        φ x ≤ a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) :=
      le_trans hmin_mid hstrong_mid
    have hb_pos : 0 < b := by
      positivity
    have hscaled :
        0 ≤ b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) := by
      have hcombine' :
          0 ≤
            a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) - φ x := by
        linarith
      have hrewrite :
          a * φ x + b * φ xStar - a * b * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) - φ x =
            b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) := by
        have ha' : a = 1 - b := by
          linarith
        rw [ha']
        ring
      simpa [hrewrite] using hcombine'
    have hgoal_nonneg :
        0 ≤ φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) := by
      by_contra hneg
      have hneg' : φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ)) < 0 :=
        lt_of_not_ge hneg
      have : b * (φ xStar - φ x - a * ((σ / 2) * ‖x - xStar‖ ^ (2 : ℕ))) < 0 := by
        exact mul_neg_of_pos_of_neg hb_pos hneg'
      linarith
    simpa [a, c] using hgoal_nonneg
  -- A contradiction argument upgrades the `n / (n + 1)` approximations to the full coefficient.
  have hquadReal :
      φ xStar ≥ φ x + c := by
    by_cases hxxStar : x = xStar
    · subst hxxStar
      simp [c]
    · have hc : 0 < c := by
        have hnorm_pos : 0 < ‖x - xStar‖ ^ (2 : ℕ) := by
          positivity [norm_pos_iff.mpr (sub_ne_zero.mpr hxxStar)]
        positivity
      by_contra hlt
      have hgap_pos : 0 < (c - (φ xStar - φ x)) / c := by
        have : 0 < c - (φ xStar - φ x) := by
          linarith
        exact div_pos this hc
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap_pos
      have hfrac :
          (φ xStar - φ x) / c < (n : ℝ) / (n + 1 : ℝ) := by
        have hleft :
            1 - (1 / (n + 1 : ℝ)) > 1 - ((c - (φ xStar - φ x)) / c) := by
          linarith
        have hleft' : (n : ℝ) / (n + 1 : ℝ) = 1 - 1 / (n + 1 : ℝ) := by
          field_simp
          ring
        have hright' : 1 - ((c - (φ xStar - φ x)) / c) = (φ xStar - φ x) / c := by
          have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
          field_simp [hc_ne]
          ring
        linarith
      have hlt' : φ xStar - φ x < (n : ℝ) / (n + 1 : ℝ) * c := by
        have hmul := mul_lt_mul_of_pos_right hfrac hc
        have hc_ne : (c : ℝ) ≠ 0 := ne_of_gt hc
        field_simp [hc_ne] at hmul
        have hn1pos : 0 < (n + 1 : ℝ) := by
          positivity
        have hmul' : (φ xStar - φ x) * (n + 1 : ℝ) < (n : ℝ) * c := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
        have hdiv : φ xStar - φ x < ((n : ℝ) * c) / (n + 1 : ℝ) := by
          have hmul'' :
              (φ xStar - φ x) * (n + 1 : ℝ) <
                (((n : ℝ) * c) / (n + 1 : ℝ)) * (n + 1 : ℝ) := by
            simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul'
          have hdiv' :
              ((φ xStar - φ x) * (n + 1 : ℝ)) / (n + 1 : ℝ) <
                ((n : ℝ) * c) / (n + 1 : ℝ) := by
            exact (div_lt_iff₀ hn1pos).2 hmul''
          simpa [hn1pos.ne', div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv'
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
      have hge' := happrox n
      linarith
  -- Rewrite the shifted inequality back to the original objective and isolate the desired term.
  have hquadReal' :
      fOpt - inner ℝ v xStar ≥
        (f x).toReal - inner ℝ v x + (σ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [φ, c, htoRealShift hxStarShift_dom, htoRealShift hxShift_dom,
      optimal_point_toReal_eq_fOpt h_problem hxStar] using hquadReal
  have hinner_diff : inner ℝ v (x - xStar) = inner ℝ v x - inner ℝ v xStar := by
    rw [inner_sub_right]
  nlinarith [hquadReal', hinner_diff]

end

section Measure

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace E] [BorelSpace E]

/-- The sigma-algebra generated by the stochastic iterate `x[n]`. -/
abbrev stochastic_iterate_sigma_algebra (n : ℕ) : MeasurableSpace Ω :=
  MeasurableSpace.comap x̄[n] inferInstance

section

omit [IsProbabilityMeasure μ] [BorelSpace E]

/-- Helper for Theorem 8.37: the oracle unbiasedness clause lifts the deterministic strong
support inequality to the conditional expectation subgradient almost surely. -/
lemma ae_condexp_inner_ge_gap_add_strong_term
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ᵐ ω ∂μ,
      ((f (x̄[n] ω)).toReal - fOpt) + (σ / 2) * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) ≤
        inner ℝ
          (μ[fun ω ↦ g n (x[n] ω) ω |
            stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
          (x̄[n] ω - xStar) := by
  -- Specialize the deterministic support inequality to the random iterate and conditional mean.
  filter_upwards [h_oracle.unbiased n] with ω hω
  exact strongly_convex_support_at_optimal_point
    h_problem h_strong hσ ((x[n] ω).property) hxStar hω

end

section

omit [IsProbabilityMeasure μ] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Theorem 8.37: once the right factor is measurable with respect to the conditioning
sigma-algebra, the conditional expectation of the inner product pulls through that factor. -/
lemma condexp_inner_of_aestronglyMeasurable_right
    {m : MeasurableSpace Ω} {u v : Ω → E}
    (hv : AEStronglyMeasurable[m] v μ)
    (huv : Integrable (fun ω ↦ inner ℝ (u ω) (v ω)) μ)
    (hu : Integrable u μ) :
    μ[(fun ω ↦ inner ℝ (u ω) (v ω)) | m] =ᵐ[μ]
      fun ω ↦ inner ℝ (μ[u | m] ω) (v ω) := by
  -- This is exactly the Mathlib pull-out theorem specialized to the real inner product.
  simpa [innerSL_apply_apply] using
    (MeasureTheory.condExp_bilin_of_aestronglyMeasurable_right
      (innerSL ℝ) hv huv hu)

end

section

omit [IsProbabilityMeasure μ] [BorelSpace E]

/-- Helper for Theorem 8.37: each stochastic iterate is almost surely strongly measurable. -/
lemma stochastic_iterate_aestronglyMeasurable
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ) :
    AEStronglyMeasurable (x̄[n]) μ := by
  induction n with
  | zero =>
      -- The initial iterate is the constant feasible starting point.
      simpa using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω ↦ (x0 : E)) μ)
  | succ n ih =>
      let P : E → E := fun y ↦
        (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex y : E)
      have hg :
          AEStronglyMeasurable (fun ω ↦ g n (x[n] ω) ω) μ :=
        (h_oracle.integrable_subgradient n).aestronglyMeasurable
      have hupdate :
          AEStronglyMeasurable
            (fun ω ↦ x̄[n] ω - t n • g n (x[n] ω) ω) μ :=
        ih.sub (hg.const_smul (t n))
      have hproj :
          AEStronglyMeasurable
            (fun ω ↦ P (x̄[n] ω - t n • g n (x[n] ω) ω)) μ :=
        (metricProjection_nonexpansive C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex).continuous.comp_aestronglyMeasurable hupdate
      -- Rewrite the recursive update into the measurable projection map applied above.
      refine hproj.congr ?_
      filter_upwards with ω
      simpa [P] using
        (stochastic_projected_subgradient_method_iterate_succ
          C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex g t x0 n ω)

end

section

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Theorem 8.37: one stochastic projection step has a coarse quadratic growth bound,
used only to bootstrap square-integrability of the iterates. -/
lemma projected_sqdist_step_growth_bound
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ ω,
      ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        2 * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) +
          2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
  intro ω
  let P : E → E := fun y ↦
    (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex y : E)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hfix : P xStar = xStar := by
    simpa [P] using
      projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex hxStar_data.1
  have hstep :
      x̄[n + 1] ω = P (x̄[n] ω - t n • g n (x[n] ω) ω) := by
    simpa [P] using
      (stochastic_projected_subgradient_method_iterate_succ
        C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex g t x0 n ω)
  have hnonexp :
      ‖x̄[n + 1] ω - xStar‖ ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ := by
    -- Firm nonexpansiveness against the fixed feasible point `xStar` yields the norm contraction.
    have hfirm :
        inner ℝ (x̄[n + 1] ω - xStar)
            ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar) ≥
          ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) := by
      simpa [P, hstep, hfix, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        metricProjection_firmly_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex
          (x̄[n] ω - t n • g n (x[n] ω) ω) xStar
    have habs :
        inner ℝ (x̄[n + 1] ω - xStar)
            ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar) ≤
          ‖x̄[n + 1] ω - xStar‖ *
            ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    nlinarith [hfirm, habs, norm_nonneg (x̄[n + 1] ω - xStar),
      norm_nonneg ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar)]
  have htriangle :
      ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ≤
        ‖x̄[n] ω - xStar‖ + ‖t n • g n (x[n] ω) ω‖ := by
    -- Rewrite the update vector as the iterate offset minus the stochastic step.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_sub_le (x̄[n] ω - xStar) (t n • g n (x[n] ω) ω)
  have hnonexp_sq :
      ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hnonexp, norm_nonneg (x̄[n + 1] ω - xStar),
      norm_nonneg ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar)]
  have htriangle_sq :
      ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) ≤
        (‖x̄[n] ω - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) := by
    nlinarith [htriangle, norm_nonneg ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar),
      add_nonneg (norm_nonneg (x̄[n] ω - xStar))
        (norm_nonneg (t n • g n (x[n] ω) ω))]
  have hsq_sum :
      (‖x̄[n] ω - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) ≤
        2 * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) +
          2 * ‖t n • g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖x̄[n] ω - xStar‖ - ‖t n • g n (x[n] ω) ω‖)]
  calc
    ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := hnonexp_sq
    _ ≤ (‖x̄[n] ω - xStar‖ + ‖t n • g n (x[n] ω) ω‖) ^ (2 : ℕ) := htriangle_sq
    _ ≤ 2 * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) +
          2 * ‖t n • g n (x[n] ω) ω‖ ^ (2 : ℕ) := hsq_sum
    _ =
        2 * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) +
          2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
        have habs_sq :
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
              (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
          calc
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
                |t n| ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by ring
            _ = (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
                rw [sq_abs]
        rw [norm_smul, Real.norm_eq_abs, habs_sq]
        ring

end

section

omit [BorelSpace E]

/-- Helper for Theorem 8.37: the squared distance to the optimal point is integrable at every
iterate, obtained from the coarse quadratic growth recursion. -/
lemma stochastic_iterate_sqdist_integrable
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    Integrable (fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)) μ := by
  induction n with
  | zero =>
      -- The initial squared distance is a constant random variable.
      simpa using integrable_const (‖(x0 : E) - xStar‖ ^ (2 : ℕ) : ℝ)
  | succ n ih =>
      have hbound_int :
          Integrable
            (fun ω ↦
              2 * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) +
                2 * (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) μ := by
        -- The rough growth bound is controlled by the previous square distance plus the oracle
        -- second-moment bound.
        exact (ih.const_mul 2).add ((h_oracle.integrable_sqnorm_subgradient n).const_mul
          (2 * (t n) ^ (2 : ℕ)))
      have hmeas :
          AEStronglyMeasurable (fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)) μ := by
        -- Measurability comes from the iterate measurability established above and the continuity
        -- of the squared norm.
        exact
          ((continuous_norm.comp_aestronglyMeasurable
              ((stochastic_iterate_aestronglyMeasurable
                h_problem g t x0 h_oracle (n + 1)).sub
                  aestronglyMeasurable_const)).pow 2)
      refine Integrable.mono' hbound_int hmeas ?_
      filter_upwards with ω
      have hgrowth :=
        projected_sqdist_step_growth_bound
          h_problem g t x0 hxStar n ω
      have hnonneg : 0 ≤ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) := by positivity
      simpa [abs_of_nonneg hnonneg] using hgrowth

end

section

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Theorem 8.37: the pathwise projection step satisfies the exact squared-distance
expansion from equation `(8.55)` before conditioning. -/
lemma projected_sqdist_step_pointwise
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    ∀ ω,
      ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
  intro ω
  let P : E → E := fun y ↦
    (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
      h_problem.feasible_convex y : E)
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hfix : P xStar = xStar := by
    simpa [P] using
      projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex hxStar_data.1
  have hstep :
      x̄[n + 1] ω = P (x̄[n] ω - t n • g n (x[n] ω) ω) := by
    simpa [P] using
      (stochastic_projected_subgradient_method_iterate_succ
        C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex g t x0 n ω)
  have hnonexp :
      ‖x̄[n + 1] ω - xStar‖ ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ := by
    -- Firm nonexpansiveness against `xStar` again gives the exact one-step norm contraction.
    have hfirm :
        inner ℝ (x̄[n + 1] ω - xStar)
            ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar) ≥
          ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) := by
      simpa [P, hstep, hfix, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        metricProjection_firmly_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex
          (x̄[n] ω - t n • g n (x[n] ω) ω) xStar
    have habs :
        inner ℝ (x̄[n + 1] ω - xStar)
            ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar) ≤
          ‖x̄[n + 1] ω - xStar‖ *
            ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ := by
      exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
    nlinarith [hfirm, habs, norm_nonneg (x̄[n + 1] ω - xStar),
      norm_nonneg ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar)]
  have hnonexp_sq :
      ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := by
    nlinarith [hnonexp, norm_nonneg (x̄[n + 1] ω - xStar),
      norm_nonneg ((x̄[n] ω - t n • g n (x[n] ω) ω) - xStar)]
  -- Expand the exact squared norm of the iterate offset after one stochastic step.
  calc
    ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ) ≤
        ‖(x̄[n] ω - t n • g n (x[n] ω) ω) - xStar‖ ^ (2 : ℕ) := hnonexp_sq
    _ = ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
        have hrewrite :
            (x̄[n] ω - t n • g n (x[n] ω) ω) - xStar =
              (x̄[n] ω - xStar) - t n • g n (x[n] ω) ω := by
          abel
        have habs_sq :
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
              (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
          calc
            (|t n| * ‖g n (x[n] ω) ω‖) ^ (2 : ℕ) =
                |t n| ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by ring
            _ = (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ) := by
                rw [sq_abs]
        rw [hrewrite, norm_sub_sq_real]
        rw [real_inner_smul_right, real_inner_comm, norm_smul, Real.norm_eq_abs, habs_sq]
        ring

end

/-- Helper for Theorem 8.37: composing the iterate with a continuous scalar observable stays
measurable with respect to the sigma-algebra generated by that iterate, so conditional expectation
fixes it as soon as the generated sigma-algebra is known to sit inside the ambient one. -/
private lemma condexp_iterate_scalar_comp_eq_self
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {φ : E → ℝ} (hφ : Continuous φ) (n : ℕ)
    (hm : stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›)
    (h_int : Integrable (fun ω ↦ φ (x̄[n] ω)) μ) :
    μ[(fun ω ↦ φ (x̄[n] ω)) |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
      fun ω ↦ φ (x̄[n] ω) := by
  have hx_ae : AEMeasurable (x̄[n]) μ := by
    exact
      (stochastic_iterate_aestronglyMeasurable
        h_problem g t x0 h_oracle n).aemeasurable
  have hcomp_meas :
      AEStronglyMeasurable[stochastic_iterate_sigma_algebra h_problem g t x0 n]
        (fun ω ↦ φ (x̄[n] ω)) μ := by
    -- Re-express the scalar observable as a composition through the iterate-generated sigma
    -- algebra, so the conditional expectation can be identified with the observable itself.
    simpa [Function.comp] using
      (hφ.aestronglyMeasurable.comp_ae_measurable' hx_ae)
  exact MeasureTheory.condExp_of_aestronglyMeasurable' hm hcomp_meas h_int

section

omit [IsProbabilityMeasure μ]

/-- Helper for Theorem 8.37: the iterate offset `x[n] - xStar` is almost surely strongly
measurable with respect to the sigma-algebra generated by `x[n]`. -/
private lemma iterate_offset_aestronglyMeasurable_comap
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm : stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›)
    {xStar : E} :
    AEStronglyMeasurable[stochastic_iterate_sigma_algebra h_problem g t x0 n]
      (fun ω ↦ x̄[n] ω - xStar) μ := by
  let offset : Ω → E := fun ω ↦ x̄[n] ω - xStar
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate is a.e. strongly measurable in the ambient space, and translating by `xStar`
    -- preserves that ambient measurability.
    exact
      (stochastic_iterate_aestronglyMeasurable
        h_problem g t x0 h_oracle n).sub
        aestronglyMeasurable_const
  have hmeas_offset :
      Measurable[stochastic_iterate_sigma_algebra h_problem g t x0 n] offset := by
    -- Over the pullback sigma-algebra, the iterate map is measurable by definition.
    have hx_meas :
        Measurable[stochastic_iterate_sigma_algebra h_problem g t x0 n]
          x̄[n] := by
      simpa [stochastic_iterate_sigma_algebra] using
        (measurable_iff_comap_le.mpr (show
          stochastic_iterate_sigma_algebra h_problem g t x0 n ≤
            stochastic_iterate_sigma_algebra h_problem g t x0 n from le_rfl))
    exact (continuous_id.sub continuous_const).measurable.comp hx_meas
  rcases (aestronglyMeasurable_iff_aemeasurable_separable.1 hoffset_ae).2 with
    ⟨s, hs_sep, hs_ae⟩
  obtain ⟨s₀, hs₀_subset, hs₀_count, hs_subset_closure⟩ :=
    hs_sep.exists_countable_dense_subset
  have hs_closure_ae : ∀ᵐ ω ∂μ, offset ω ∈ closure s₀ := by
    filter_upwards [hs_ae] with ω hω
    exact hs_subset_closure hω
  have hs_meas :
      MeasurableSet[stochastic_iterate_sigma_algebra h_problem g t x0 n]
        {ω | offset ω ∈ closure s₀} := by
    exact hmeas_offset isClosed_closure.measurableSet
  have hs_trim : ∀ᵐ ω ∂μ.trim hm, offset ω ∈ closure s₀ := by
    have hs_meas_compl :
        MeasurableSet[stochastic_iterate_sigma_algebra h_problem g t x0 n]
          {ω | offset ω ∉ closure s₀} := hs_meas.compl
    rw [ae_iff]
    rw [trim_measurableSet_eq hm hs_meas_compl]
    simpa [ae_iff] using hs_closure_ae
  have htrim :
      AEStronglyMeasurable[stochastic_iterate_sigma_algebra h_problem g t x0 n]
        offset (μ.trim hm) := by
    -- On the trimmed measure, measurability in the pullback sigma-algebra plus the ambient
    -- a.e. separable range gives the desired relative strong measurability.
    exact
      (aestronglyMeasurable_iff_aemeasurable_separable).2
        ⟨hmeas_offset.aemeasurable,
          ⟨closure s₀, hs₀_count.isSeparable.closure, hs_trim⟩⟩
  exact htrim.of_trim hm

end

/-- Helper for Theorem 8.37: conditioning on the sigma-algebra generated by `x[n]` pulls the
iterate offset out of the inner product. -/
private lemma condexp_inner_iterate_offset_comap_pullout
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm : stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    μ[(fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)) |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
      fun ω ↦
        inner ℝ
          (μ[fun ω ↦ g n (x[n] ω) ω |
            stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
          (x̄[n] ω - xStar) := by
  let gFun : Ω → E := fun ω ↦ g n (x[n] ω) ω
  let offset : Ω → E := fun ω ↦ x̄[n] ω - xStar
  have hg_ae : AEStronglyMeasurable gFun μ := by
    -- The oracle integrability hypothesis already supplies almost-everywhere measurability of the
    -- sampled stochastic subgradient.
    exact (h_oracle.integrable_subgradient n).aestronglyMeasurable
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate itself is a.e. strongly measurable, and translating by `xStar` preserves that.
    exact
      (stochastic_iterate_aestronglyMeasurable
        h_problem g t x0 h_oracle n).sub
        aestronglyMeasurable_const
  have hg_memLp : MemLp gFun 2 μ := by
    -- The oracle's squared-norm integrability is exactly the `L²` membership criterion.
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hg_ae).2
      (h_oracle.integrable_sqnorm_subgradient n)
  have hoffset_memLp : MemLp offset 2 μ := by
    -- The offset has integrable squared norm by the iterate square-distance bootstrap.
    simpa [offset] using
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hoffset_ae).2
        (stochastic_iterate_sqdist_integrable
          h_problem g t x0 h_oracle hxStar n)
  have hinner_lp :
      Integrable
        (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) μ := by
    -- The pointwise inner product of two `L²` functions is integrable.
    exact MeasureTheory.L2.integrable_inner (hg_memLp.toLp gFun) (hoffset_memLp.toLp offset)
  have hinner_eq :
      (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) =ᵐ[μ]
        fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) := by
    filter_upwards [MemLp.coeFn_toLp hg_memLp, MemLp.coeFn_toLp hoffset_memLp] with ω hg hoffset
    simp [gFun, offset, hg, hoffset]
  have hinner_int :
      Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)) μ := by
    exact (integrable_congr hinner_eq).1 hinner_lp
  -- Pull the measurable iterate offset through the conditional expectation in one step.
  exact condexp_inner_of_aestronglyMeasurable_right
    (iterate_offset_aestronglyMeasurable_comap
      h_problem g t x0 h_oracle n hm)
    hinner_int
    (h_oracle.integrable_subgradient n)

section

omit [BorelSpace E]

/-- Helper for Theorem 8.37: the inner-product term in the projected-square expansion is
integrable, because both the stochastic subgradient and the iterate offset belong to `L²`. -/
lemma integrable_inner_iterate_offset
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)) μ := by
  let gFun : Ω → E := fun ω ↦ g n (x[n] ω) ω
  let offset : Ω → E := fun ω ↦ x̄[n] ω - xStar
  have hg_ae : AEStronglyMeasurable gFun μ := by
    -- The oracle integrability hypothesis already supplies almost-everywhere measurability of the
    -- sampled stochastic subgradient.
    exact (h_oracle.integrable_subgradient n).aestronglyMeasurable
  have hoffset_ae : AEStronglyMeasurable offset μ := by
    -- The iterate itself is a.e. strongly measurable, and translating by `xStar` preserves that.
    exact
      (stochastic_iterate_aestronglyMeasurable
        h_problem g t x0 h_oracle n).sub
        aestronglyMeasurable_const
  have hg_memLp : MemLp gFun 2 μ := by
    -- The oracle's squared-norm integrability is exactly the `L²` membership criterion.
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hg_ae).2
      (h_oracle.integrable_sqnorm_subgradient n)
  have hoffset_memLp : MemLp offset 2 μ := by
    -- The offset has integrable squared norm by the iterate square-distance bootstrap.
    simpa [offset] using
      (MeasureTheory.memLp_two_iff_integrable_sq_norm hoffset_ae).2
        (stochastic_iterate_sqdist_integrable
          h_problem g t x0 h_oracle hxStar n)
  have hinner_lp :
      Integrable
        (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) μ := by
    -- The pointwise inner product of two `L²` functions is integrable.
    exact MeasureTheory.L2.integrable_inner (hg_memLp.toLp gFun) (hoffset_memLp.toLp offset)
  have hinner_eq :
      (fun ω ↦ inner ℝ ((hg_memLp.toLp gFun) ω) ((hoffset_memLp.toLp offset) ω)) =ᵐ[μ]
        fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) := by
    filter_upwards [MemLp.coeFn_toLp hg_memLp, MemLp.coeFn_toLp hoffset_memLp] with ω hg hoffset
    simp [gFun, offset, hg, hoffset]
  exact (integrable_congr hinner_eq).1 hinner_lp

end

/-- Helper for Theorem 8.37: under the measurable iterate-generated sigma-algebra branch,
right-hand side of the projected-square expansion normalizes exactly into the target form with the
inner-product factor pulled through the conditional expectation. -/
private lemma condexp_projected_sqdist_step_rhs_eq
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    (hm : stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    μ[(fun ω ↦
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
      fun ω ↦
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
              (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
  let sqdist : Ω → ℝ := fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)
  let innerTerm : Ω → ℝ := fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)
  let sqnorm : Ω → ℝ := fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)
  have hsqdist_int : Integrable sqdist μ := by
    simpa [sqdist] using
      stochastic_iterate_sqdist_integrable
        h_problem g t x0 h_oracle hxStar n
  have hinner_int : Integrable innerTerm μ := by
    simpa [innerTerm] using
      integrable_inner_iterate_offset
        h_problem g t x0 h_oracle n hxStar
  have hsqnorm_int : Integrable sqnorm μ := by
    simpa [sqnorm] using h_oracle.integrable_sqnorm_subgradient n
  have hsqdist_ce :
      μ[sqdist | stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
        sqdist := by
    -- The squared-distance term depends only on the current iterate, so conditioning fixes it.
    exact condexp_iterate_scalar_comp_eq_self
      h_problem g t x0 h_oracle
      ((continuous_norm.comp (continuous_id.sub continuous_const)).pow 2)
      n hm hsqdist_int
  have hinner_ce :
      μ[innerTerm | stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
        fun ω ↦
          inner ℝ
            (μ[fun ω ↦ g n (x[n] ω) ω |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
            (x̄[n] ω - xStar) := by
    -- Pull the iterate offset through the conditional expectation in the inner-product term.
    simpa [innerTerm] using
      condexp_inner_iterate_offset_comap_pullout
        h_problem g t x0 h_oracle n hm hxStar
  have hscaled_inner_ce :
      μ[(fun ω ↦ (2 * t n) * innerTerm ω) |
          stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
        fun ω ↦
          (2 * t n) *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
              (x̄[n] ω - xStar) := by
    -- The deterministic scalar `2 * t n` commutes with conditional expectation.
    refine (MeasureTheory.condExp_smul (2 * t n) innerTerm
      (stochastic_iterate_sigma_algebra h_problem g t x0 n)).trans ?_
    filter_upwards [hinner_ce] with ω hω
    simp [hω]
  have hscaled_sqnorm_ce :
      μ[(fun ω ↦ (t n) ^ (2 : ℕ) * sqnorm ω) |
          stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
        fun ω ↦
          (t n) ^ (2 : ℕ) *
            μ[sqnorm | stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
    -- The squared-norm term is also just a deterministic scalar multiple.
    refine (MeasureTheory.condExp_smul ((t n) ^ (2 : ℕ)) sqnorm
      (stochastic_iterate_sigma_algebra h_problem g t x0 n)).trans ?_
    filter_upwards with ω
    simp
  have hsub_ce :
      μ[(fun ω ↦ sqdist ω - (2 * t n) * innerTerm ω) |
          stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
        fun ω ↦
          sqdist ω -
            (2 * t n) *
              inner ℝ
                (μ[fun ω ↦ g n (x[n] ω) ω |
                  stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
                (x̄[n] ω - xStar) := by
    -- First normalize the difference `sqdist - 2 t_n innerTerm`.
    exact (MeasureTheory.condExp_sub hsqdist_int (hinner_int.const_mul (2 * t n))
      (stochastic_iterate_sigma_algebra h_problem g t x0 n)).trans
        (hsqdist_ce.sub hscaled_inner_ce)
  -- Combine the normalized difference with the conditioned squared-norm term.
  calc
    μ[(fun ω ↦
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n * inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] =ᵐ[μ]
      μ[(fun ω ↦ sqdist ω - (2 * t n) * innerTerm ω + (t n) ^ (2 : ℕ) * sqnorm ω) |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] := by
          exact MeasureTheory.condExp_congr_ae <| Filter.Eventually.of_forall fun ω ↦ by
            simp [sqdist, innerTerm, sqnorm]
    _ =ᵐ[μ]
      (fun ω ↦
          sqdist ω -
            (2 * t n) *
              inner ℝ
                (μ[fun ω ↦ g n (x[n] ω) ω |
                  stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
                (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[sqnorm | stochastic_iterate_sigma_algebra h_problem g t x0 n] ω) := by
          exact (MeasureTheory.condExp_add
            (hsqdist_int.sub (hinner_int.const_mul (2 * t n)))
            (hsqnorm_int.const_mul ((t n) ^ (2 : ℕ)))
            _).trans
            (hsub_ce.add hscaled_sqnorm_ce)
    _ =ᵐ[μ]
      fun ω ↦
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
              (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
          exact Filter.Eventually.of_forall fun ω ↦ by simp [sqdist, sqnorm]

/-- Helper for Theorem 8.37: the conditional projected-square estimate at the sigma-algebra
generated by the measurable iterate `x[n]`. This is the source-faithful `(8.55) + (8.u196)`
bridge before any integration or telescoping. -/
lemma conditional_projected_sqdist_le_of_strongly_convex_support
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ)
    (hm : stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›) :
    ∀ᵐ ω ∂μ,
      μ[(fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)) |
          stochastic_iterate_sigma_algebra h_problem g t x0 n] ω ≤
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            (((f (x̄[n] ω)).toReal - fOpt) +
              (σ / 2) * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
  let sqdistNext : Ω → ℝ := fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)
  let rawRhs : Ω → ℝ := fun ω ↦
    ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
      2 * t n * inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar) +
      (t n) ^ (2 : ℕ) * ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)
  have hsqdistNext_int : Integrable sqdistNext μ := by
    simpa [sqdistNext] using
      stochastic_iterate_sqdist_integrable
        h_problem g t x0 h_oracle hxStar (n + 1)
  have hinner_int :
      Integrable (fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)) μ := by
    exact integrable_inner_iterate_offset
      h_problem g t x0 h_oracle n hxStar
  have hrawRhs_int : Integrable rawRhs μ := by
    -- Every term in the raw pathwise square expansion is integrable.
    simpa [rawRhs] using
      (stochastic_iterate_sqdist_integrable
        h_problem g t x0 h_oracle hxStar n).sub
        (hinner_int.const_mul (2 * t n)) |>.add
        ((h_oracle.integrable_sqnorm_subgradient n).const_mul ((t n) ^ (2 : ℕ)))
  have hmono :
      μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n] ≤ᵐ[μ]
        μ[rawRhs | stochastic_iterate_sigma_algebra h_problem g t x0 n] := by
    -- Condition the pointwise projection inequality from `projected_sqdist_step_pointwise`.
    refine MeasureTheory.condExp_mono hsqdistNext_int hrawRhs_int ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [sqdistNext, rawRhs] using
        projected_sqdist_step_pointwise
          h_problem g t x0 hxStar n ω
  have ht_nonneg : 0 ≤ t n := by
    rw [h_stepsize n]
    positivity
  have hrhs_eq :=
    condexp_projected_sqdist_step_rhs_eq
      h_problem g t x0 h_oracle n hm hxStar
  have hsupport :=
    ae_condexp_inner_ge_gap_add_strong_term
      h_problem g t x0 h_strong hσ h_oracle hxStar n
  -- With measurability available, the conditional expansion reduces to a single monotonicity step.
  filter_upwards [hmono, hrhs_eq, hsupport] with ω hωmono hωrhs hωsupport
  have hstep :
      μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n] ω ≤
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
              (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
    exact hωrhs ▸ hωmono
  have hreplace :
      ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            inner ℝ
              (μ[fun ω ↦ g n (x[n] ω) ω |
                stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
              (x̄[n] ω - xStar) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω ≤
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) -
          2 * t n *
            (((f (x̄[n] ω)).toReal - fOpt) +
              (σ / 2) * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)) +
          (t n) ^ (2 : ℕ) *
            μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
              stochastic_iterate_sigma_algebra h_problem g t x0 n] ω := by
    nlinarith
  exact le_trans hstep hreplace

/-
The next few helper lemmas only use the data explicitly appearing in their statements, so
the surrounding section's extra typeclass parameters are omitted locally to keep lint clean.
-/
omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- Helper for Theorem 8.37: every feasible point has real-valued objective gap at least `0`. -/
private lemma feasibleObjectiveGap_nonneg
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {y : E} (hy : y ∈ C) :
    0 ≤ (f y).toReal - fOpt := by
  -- Feasibility places the current objective value in the image set controlled by the GLB data.
  have hy_image : f y ∈ f '' C := by
    exact ⟨y, hy, rfl⟩
  have hlower : (fOpt : EReal) ≤ f y :=
    h_problem.optimal_value_isGLB.1 hy_image
  have hy_dom : y ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hy)
  have hy_top : f y ≠ ⊤ := ne_of_lt hy_dom
  have hy_bot : f y ≠ ⊥ := h_problem.ne_bot y
  have hreal : (fOpt : EReal) ≤ (((f y).toReal : ℝ) : EReal) := by
    simpa [EReal.coe_toReal hy_top hy_bot] using hlower
  have hreal' : fOpt ≤ (f y).toReal := EReal.coe_le_coe_iff.mp hreal
  linarith

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 8.37: the real-valued objective gap at the `n`th stochastic iterate is
almost everywhere measurable. -/
private lemma aemeasurableIterateObjectiveGap
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ) :
    AEMeasurable (fun ω ↦ (f (x̄[n] ω)).toReal - fOpt) μ := by
  -- Compose the measurable objective with the a.e. measurable iterate and subtract the constant.
  have hf_meas : Measurable (fun x : E ↦ (f x).toReal) := by
    have hmeas_ereal : Measurable f := by
      simpa using h_problem.closed.measurable
    simpa using Measurable.ereal_toReal hmeas_ereal
  exact
    (hf_meas.comp_aemeasurable
      (stochastic_iterate_aestronglyMeasurable
        h_problem g t x0 h_oracle n).aemeasurable).sub
      aemeasurable_const

/-- Helper for Theorem 8.37: the conditional-expectation inner-product term is integrable. -/
private lemma integrableCondexpInnerIterateOffset
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (n : ℕ)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    Integrable
      (fun ω ↦
        inner ℝ
          (μ[fun ω ↦ g n (x[n] ω) ω |
            stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
          (x̄[n] ω - xStar)) μ := by
  by_cases hm :
      stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›
  · -- On the measurable branch, this is the conditional expectation of the integrable raw inner
    -- product term.
    let rawInner : Ω → ℝ := fun ω ↦ inner ℝ (g n (x[n] ω) ω) (x̄[n] ω - xStar)
    have hcond_int :
        Integrable
          (μ[rawInner | stochastic_iterate_sigma_algebra h_problem g t x0 n]) μ := by
      exact MeasureTheory.integrable_condExp
    refine hcond_int.congr ?_
    simpa [rawInner] using
      condexp_inner_iterate_offset_comap_pullout
        h_problem g t x0 h_oracle n hm hxStar
  · -- On the bad branch, the conditional expectation is definitionally zero.
    simp [MeasureTheory.condExp_of_not_le hm]

/-- Helper for Theorem 8.37: the stochastic iterate objective gap is integrable because the strong
gap is dominated by the integrable conditional inner-product term. -/
private lemma integrableIterateObjectiveGap
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    Integrable (fun ω ↦ (f (x̄[n] ω)).toReal - fOpt) μ := by
  let gapFun : Ω → ℝ := fun ω ↦ (f (x̄[n] ω)).toReal - fOpt
  let innerCond : Ω → ℝ := fun ω ↦
    inner ℝ
      (μ[fun ω ↦ g n (x[n] ω) ω |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] ω)
      (x̄[n] ω - xStar)
  have hinnerCond_int : Integrable innerCond μ := by
    simpa [innerCond] using
      integrableCondexpInnerIterateOffset
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_oracle n hxStar
  have hdom : ∀ᵐ ω ∂μ, ‖gapFun ω‖ ≤ innerCond ω := by
    -- The iterate gap is nonnegative and bounded above by the strong gap term from the support
    -- inequality.
    filter_upwards
      [ae_condexp_inner_ge_gap_add_strong_term
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_oracle hxStar n] with ω hω
    have hgap_nonneg : 0 ≤ gapFun ω := by
      simpa [gapFun] using
        feasibleObjectiveGap_nonneg h_problem ((x[n] ω).property)
    have hsq_nonneg : 0 ≤ (σ / 2) * ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) := by
      positivity
    have habs : ‖gapFun ω‖ = gapFun ω := by
      simpa using Real.norm_of_nonneg hgap_nonneg
    rw [habs]
    nlinarith
  exact Integrable.mono'
    hinnerCond_int
    (aemeasurableIterateObjectiveGap
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).aestronglyMeasurable
    hdom

omit [IsProbabilityMeasure μ] [BorelSpace E] in
/-- Helper for Theorem 8.37: on the nonmeasurable sigma-algebra branch, the pulled-back
conditional subgradient vanishes, so both the current objective gap and the current squared
distance to the optimal point vanish almost surely. -/
private lemma iterateGapAndSqdistAeEqZero_of_notMeasurableSigma
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) {n : ℕ}
    (hm :
      ¬ stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›) :
    ∀ᵐ ω ∂μ,
      (f (x̄[n] ω)).toReal - fOpt = 0 ∧
        ‖x̄[n] ω - xStar‖ ^ (2 : ℕ) = 0 := by
  have hsupport :=
    ae_condexp_inner_ge_gap_add_strong_term
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_oracle hxStar n
  have hcond_zero :
      μ[fun ω ↦ g n (x[n] ω) ω |
        stochastic_iterate_sigma_algebra h_problem g t x0 n] = 0 := by
    exact MeasureTheory.condExp_of_not_le hm
  -- The bad branch collapses the conditional mean to zero, so the strong gap term must vanish.
  filter_upwards [hsupport] with ω hω
  let gap : ℝ := (f (x̄[n] ω)).toReal - fOpt
  let sqdist : ℝ := ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)
  have hgap_nonneg : 0 ≤ gap := by
    simpa [gap] using feasibleObjectiveGap_nonneg h_problem ((x[n] ω).property)
  have hsq_nonneg : 0 ≤ sqdist := by
    positivity
  have hsum_nonpos : gap + (σ / 2) * sqdist ≤ 0 := by
    simpa [gap, sqdist, hcond_zero] using hω
  have hscaled_eq_zero : (σ / 2) * sqdist = 0 := by
    have hscaled_nonneg : 0 ≤ (σ / 2) * sqdist := by
      positivity
    nlinarith
  have hgap_eq_zero : gap = 0 := by
    nlinarith
  have hsqdist_eq_zero : sqdist = 0 := by
    have hsigma_half_pos : 0 < σ / 2 := by
      positivity
    nlinarith
  exact ⟨by simpa [gap] using hgap_eq_zero, by simpa [sqdist] using hsqdist_eq_zero⟩

omit [BorelSpace E] in
/-- Helper for Theorem 8.37: the nonmeasurable sigma-algebra branch already forces the current
expected objective gap and the current expected squared distance to vanish. -/
private lemma expectedGapAndSqdistEqZero_of_notMeasurableSigma
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) {n : ℕ}
    (hm :
      ¬ stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω›) :
    (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt = 0) ∧
      (μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] = 0) := by
  let gapFun : Ω → ℝ := fun ω ↦ (f (x̄[n] ω)).toReal - fOpt
  let sqdist : Ω → ℝ := fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)
  have hzero :=
    iterateGapAndSqdistAeEqZero_of_notMeasurableSigma
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_oracle hxStar hm
  have hgap_zero_eq : gapFun =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- The bad branch forces the current objective gap to vanish almost surely.
    filter_upwards [hzero] with ω hω
    simpa [gapFun] using hω.1
  have hsqdist_zero_eq : sqdist =ᵐ[μ] fun _ : Ω ↦ 0 := by
    -- The same branch also collapses the current squared distance to zero almost surely.
    filter_upwards [hzero] with ω hω
    simpa [sqdist] using hω.2
  have hgap_int : Integrable gapFun μ := by
    -- An almost surely zero gap has zero integral.
    exact (integrable_zero Ω ℝ μ).congr hgap_zero_eq.symm
  have hobj_int : Integrable (fun ω ↦ (f (x̄[n] ω)).toReal) μ := by
    -- Add back the constant `fOpt` to recover integrability of the objective itself.
    simpa [gapFun, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hgap_int.add (integrable_const fOpt)
  have hgap_integral :
      MeasureTheory.integral μ gapFun = μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt := by
    -- Normalize the expected gap into an ordinary integral.
    simp [gapFun, integral_sub hobj_int (integrable_const fOpt), integral_const]
  have hsqdist_int : Integrable sqdist μ := by
    -- The iterate square-distance bootstrap already gives integrability at time `n`.
    simpa [sqdist] using
      stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n
  constructor
  · -- Integrate the almost surely zero gap.
    calc
      μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt = MeasureTheory.integral μ gapFun := by
            symm
            exact hgap_integral
      _ = MeasureTheory.integral μ (fun _ : Ω ↦ (0 : ℝ)) := by
            exact integral_congr_ae hgap_zero_eq
      _ = 0 := by simp
  · -- Integrate the almost surely zero squared distance.
    calc
      μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] = MeasureTheory.integral μ sqdist := by
        simp [sqdist]
      _ = MeasureTheory.integral μ (fun _ : Ω ↦ (0 : ℝ)) := by
            exact integral_congr_ae hsqdist_zero_eq
      _ = 0 := by simp

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
/-- Helper for Theorem 8.37: the running best-value gap satisfies the one-step minimum
recurrence after subtracting `fOpt`. -/
private lemma bestAchievedGap_succ (k : ℕ) :
    (fun ω ↦
      best_achieved_function_value
        (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) (k + 1) - fOpt) =
      fun ω ↦
        min
          (best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt)
          ((f (x̄[k + 1] ω)).toReal - fOpt) := by
  -- Rewrite the prefix minimum by inserting the new iterate value and translate by `fOpt`.
  funext ω
  simp [best_achieved_function_value, Finset.range_add_one, min_sub_sub_right, min_comm]

omit [IsProbabilityMeasure μ] in
/-- Helper for Theorem 8.37: the running best-value gap is almost everywhere measurable. -/
private lemma aemeasurableBestAchievedGap
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (k : ℕ) :
    AEMeasurable
      (fun ω ↦
        best_achieved_function_value
          (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt) μ := by
  induction k with
  | zero =>
      -- At `k = 0`, the running best value is just the initial iterate value.
      simpa [best_achieved_function_value] using
        aemeasurableIterateObjectiveGap
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle 0
  | succ k hk =>
      -- The successor step is the minimum of the previous best gap and the new iterate gap.
      rw [bestAchievedGap_succ (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        (f := f) (fOpt := fOpt) k]
      exact hk.min <|
        aemeasurableIterateObjectiveGap
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle (k + 1)

/-- Helper for Theorem 8.37: the running best-value gap is integrable because it is nonnegative
and pointwise dominated by the initial iterate gap. -/
private lemma integrableBestAchievedGap
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Integrable
      (fun ω ↦
        best_achieved_function_value
          (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt) μ := by
  have hgap0_int :
      Integrable (fun ω ↦ (f (x̄[0] ω)).toReal - fOpt) μ := by
    exact
      integrableIterateObjectiveGap
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_oracle hxStar 0
  have hdom :
      ∀ᵐ ω ∂μ,
        ‖best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt‖ ≤
          (f (x̄[0] ω)).toReal - fOpt := by
    -- The running minimum is nonnegative above `fOpt` and never exceeds the initial iterate
    -- value.
    filter_upwards with ω
    have hbest_nonneg :
        0 ≤
          best_achieved_function_value
              (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt := by
      have hlower :
          fOpt ≤
            best_achieved_function_value
              (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k := by
        unfold best_achieved_function_value
        apply Finset.le_min'
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
        have hgap_nonneg := feasibleObjectiveGap_nonneg h_problem ((x[n] ω).property)
        linarith
      exact sub_nonneg.mpr hlower
    have hbest_le :
        best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k ≤
          (f (x̄[0] ω)).toReal := by
      exact
        best_achieved_function_value_le_objective_value
          (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k 0 (by simp)
    have habs :
        ‖best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt‖ =
          best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k - fOpt := by
      simpa using Real.norm_of_nonneg hbest_nonneg
    rw [habs]
    linarith [hbest_le]
  exact Integrable.mono'
    hgap0_int
    (aemeasurableBestAchievedGap
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle k).aestronglyMeasurable
    hdom

/-- Theorem 8.37: integrating the conditional one-step inequality first yields the stable
expectation-level remainder estimate before the stepsize coefficients are normalized. -/
lemma expectedGapStepWithStrongRemainder_le
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    2 * t n * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) +
        σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
        μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] ≤
      μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
        (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
  let sqdist : Ω → ℝ := fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)
  let sqdistNext : Ω → ℝ := fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)
  let gapFun : Ω → ℝ := fun ω ↦ (f (x̄[n] ω)).toReal - fOpt
  let upperRhs : Ω → ℝ := fun ω ↦
    (1 - σ * t n) * sqdist ω +
      (-2 * t n) * gapFun ω +
      (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ)
  have hm :
      stochastic_iterate_sigma_algebra h_problem g t x0 n ≤ ‹MeasurableSpace Ω› := by
    -- The iterate measurability hypothesis is exactly the needed sigma-algebra inclusion.
    simpa [stochastic_iterate_sigma_algebra] using
      (measurable_iff_comap_le.mp (h_iterate_meas n))
  have ht_nonneg : 0 ≤ t n := by
    -- The prescribed strongly-convex stepsize is nonnegative.
    rw [h_stepsize n]
    positivity
  have hsqdist_int : Integrable sqdist μ := by
    -- The current squared distance is integrable by the iterate bootstrap.
    simpa [sqdist] using
      stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar n
  have hsqdistNext_int : Integrable sqdistNext μ := by
    -- The next squared distance is integrable for the same reason.
    simpa [sqdistNext] using
      stochastic_iterate_sqdist_integrable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle hxStar (n + 1)
  have hgap_int : Integrable gapFun μ := by
    -- The current objective gap is integrable from the strong-support domination lemma.
    simpa [gapFun] using
      integrableIterateObjectiveGap
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_oracle hxStar n
  have hupperRhs_int : Integrable upperRhs μ := by
    -- The simplified upper bound is a finite linear combination of integrable terms.
    have htmp :
        Integrable
          (fun ω ↦
            (1 - σ * t n) * sqdist ω +
              ((-2 * t n) * gapFun ω +
                (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ))) μ := by
      exact
        (hsqdist_int.const_mul (1 - σ * t n)).add
          ((hgap_int.const_mul (-2 * t n)).add
            (integrable_const ((t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) : ℝ)))
    simpa [upperRhs, add_assoc] using htmp
  have hcond_bound :
      ∀ᵐ ω ∂μ,
        (μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n]) ω ≤ upperRhs ω := by
    have hstep :=
      conditional_projected_sqdist_le_of_strongly_convex_support
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_stepsize h_oracle hxStar n hm
    -- The conditional square-norm bound closes the remaining stochastic term.
    filter_upwards [hstep, h_oracle.sqnorm_condexp_le n] with ω hωstep hωsqnorm
    have hωsqnorm' :
        (μ[(fun ω ↦ ‖g n (x[n] ω) ω‖ ^ (2 : ℕ)) |
          stochastic_iterate_sigma_algebra h_problem g t x0 n]) ω ≤
          h_oracle.L_tilde_f ^ (2 : ℕ) := by
      simpa using hωsqnorm
    have ht_sq_nonneg : 0 ≤ (t n) ^ (2 : ℕ) := by
      positivity
    dsimp [upperRhs, gapFun, sqdist] at *
    nlinarith
  have hcond_int :
      Integrable
        (μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n]) μ := by
    -- Conditional expectation preserves integrability of the next-step distance.
    exact MeasureTheory.integrable_condExp
  have hintegral_le :
      MeasureTheory.integral μ
          (fun ω ↦
            (μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n]) ω) ≤
        MeasureTheory.integral μ upperRhs := by
    -- Integrate the almost-everywhere conditional inequality.
    exact MeasureTheory.integral_mono_ae hcond_int hupperRhs_int hcond_bound
  have hobj_int : Integrable (fun ω ↦ (f (x̄[n] ω)).toReal) μ := by
    -- Add back the constant `fOpt` to recover the raw objective integrability.
    simpa [gapFun, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hgap_int.add (integrable_const fOpt)
  have hgap_integral :
      MeasureTheory.integral μ gapFun = μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt := by
    -- Rewrite the expected objective gap as the integral of the pointwise gap.
    simp [gapFun, integral_sub hobj_int (integrable_const fOpt), integral_const]
  have hupper_integral :
      MeasureTheory.integral μ upperRhs =
        μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          2 * t n * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) -
          σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
          (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
    have hsum_int :
        Integrable
          (fun ω ↦ (1 - σ * t n) * sqdist ω + (-2 * t n) * gapFun ω) μ := by
      exact (hsqdist_int.const_mul (1 - σ * t n)).add (hgap_int.const_mul (-2 * t n))
    have hscaled_sqdist :
        MeasureTheory.integral μ (fun ω ↦ (1 - σ * t n) * sqdist ω) =
          (1 - σ * t n) * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] := by
      rw [integral_const_mul]
    have hscaled_gap :
        MeasureTheory.integral μ (fun ω ↦ (-2 * t n) * gapFun ω) =
          (-2 * t n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) := by
      rw [integral_const_mul]
      rw [hgap_integral]
    -- Evaluate the integral of the simplified upper bound termwise.
    calc
      MeasureTheory.integral μ upperRhs
          = MeasureTheory.integral μ
              (fun ω ↦
                (1 - σ * t n) * sqdist ω +
                  (-2 * t n) * gapFun ω +
                  ((t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ))) := by
                simp [upperRhs]
      _ =
          MeasureTheory.integral μ
              (fun ω ↦ (1 - σ * t n) * sqdist ω + (-2 * t n) * gapFun ω) +
            MeasureTheory.integral μ
              (fun _ : Ω ↦ (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ)) := by
              rw [integral_add hsum_int (integrable_const _)]
      _ =
          (MeasureTheory.integral μ (fun ω ↦ (1 - σ * t n) * sqdist ω) +
            MeasureTheory.integral μ (fun ω ↦ (-2 * t n) * gapFun ω)) +
            MeasureTheory.integral μ
              (fun _ : Ω ↦ (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ)) := by
              rw [integral_add (hsqdist_int.const_mul (1 - σ * t n))
                (hgap_int.const_mul (-2 * t n))]
      _ =
          (1 - σ * t n) * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
            (-2 * t n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) +
            (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
              rw [hscaled_sqdist, hscaled_gap, integral_const]
              simp
      _ =
          μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
            2 * t n * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) -
            σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
            (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
              ring
  have hmain :
      μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] ≤
        μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          2 * t n * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) -
          σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
          (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
    -- Integrate the conditional one-step inequality and collapse the conditional expectation.
    calc
      μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] =
          MeasureTheory.integral μ
            (fun ω ↦
              (μ[sqdistNext | stochastic_iterate_sigma_algebra h_problem g t x0 n]) ω) := by
        simpa [sqdistNext] using
          (MeasureTheory.integral_condExp
            (μ := μ) (m := stochastic_iterate_sigma_algebra h_problem g t x0 n) (hm := hm)
            (f := sqdistNext)).symm
      _ ≤ MeasureTheory.integral μ upperRhs := hintegral_le
      _ =
          μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
            2 * t n * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) -
            σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] +
            (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := hupper_integral
  nlinarith

-- Local API note: Chap. 8 expectation statements use the project notation `μ[fun ω ↦ ...]`.
lemma expected_one_step_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (n : ℕ) :
    μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt ≤
      (σ * (n - 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
        (σ * (n + 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
        h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
  have ht_pos : 0 < t n := by
    rw [h_stepsize]
    positivity
  have hbase :=
    expectedGapStepWithStrongRemainder_le
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar n
  have hInv :
      1 / (2 * t n) = σ * (n + 1 : ℝ) / 4 := by
    rw [h_stepsize]
    field_simp [hσ.ne']
    ring
  have hCoeff :
      (1 / (2 * t n)) - σ / 2 = σ * (n - 1 : ℝ) / 4 := by
    rw [hInv]
    ring
  have hLast :
      (t n / 2) * h_oracle.L_tilde_f ^ (2 : ℕ) =
        h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
    rw [h_stepsize]
    field_simp [hσ.ne']
  have hrewrite :
      (2 * t n) *
          (((1 / (2 * t n)) - σ / 2) *
              μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
            (1 / (2 * t n)) * μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
            (t n / 2) * h_oracle.L_tilde_f ^ (2 : ℕ)) =
        μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          σ * t n * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
          (t n) ^ (2 : ℕ) * h_oracle.L_tilde_f ^ (2 : ℕ) := by
    field_simp [ht_pos.ne']
  have hmul :
      (2 * t n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) ≤
        (2 * t n) *
          (((1 / (2 * t n)) - σ / 2) *
              μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
            (1 / (2 * t n)) * μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
            (t n / 2) * h_oracle.L_tilde_f ^ (2 : ℕ)) := by
    rw [hrewrite]
    nlinarith [hbase]
  have h2t_pos : 0 < 2 * t n := by
    positivity
  -- Route correction: all expectation normalization is isolated in the previous helper, so only
  -- the schedule coefficients are rewritten here.
  calc
    μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt ≤
        (((1 / (2 * t n)) - σ / 2) *
            μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          (1 / (2 * t n)) * μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
          (t n / 2) * h_oracle.L_tilde_f ^ (2 : ℕ)) := by
            nlinarith
    _ =
        (σ * (n - 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[n] ω - xStar‖ ^ (2 : ℕ)] -
          (σ * (n + 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[n + 1] ω - xStar‖ ^ (2 : ℕ)] +
          h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)) := by
            rw [hCoeff, hInv, hLast]

/-- Helper for Theorem 8.37: the weighted squared-distance contributions telescope to the single
terminal remainder `-(σ k (k + 1) / 4) d_{k+1}`. -/
private lemma stronglyConvexWeightedDistanceTelescope
    (d : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
            (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1)) =
      -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) := by
  -- The boundary terms cancel inductively, leaving only the final tail.
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      simp [Nat.cast_add, Nat.cast_one, add_assoc]
      ring

/-- Helper for Theorem 8.37: the real-valued prefix sum of the integers `0, …, k` is
`k (k + 1) / 2`. -/
private theorem sumRangeNatCast (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ)) =
      (k : ℝ) * (k + 1) / 2 := by
  -- Evaluate the arithmetic progression directly in `ℝ` to avoid cast noise later.
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ, hk]
      have hpoly :
          (k : ℝ) * (k + 1) / 2 + (k + 1 : ℝ) =
            ((k + 1 : ℝ) * ((k + 1 : ℝ) + 1) / 2) := by
        ring
      simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc] using hpoly

/-- Helper for Theorem 8.37: the harmonic-type prefix sum `∑_{n=0}^k n / (n + 1)` is bounded by
`k`. -/
private theorem sumNatDivSucc_le (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) ≤ k := by
  -- Each new summand `(k + 1) / (k + 2)` is at most `1`, so the prefix sum grows by at most one.
  induction k with
  | zero =>
      norm_num
  | succ k hk =>
      rw [Finset.sum_range_succ]
      have hfrac :
          ((k + 1 : ℝ) / ((k + 1 : ℝ) + 1)) ≤ 1 := by
        have hden : 0 < ((k + 1 : ℝ) + 1) := by positivity
        exact (div_le_iff₀ hden).2 (by nlinarith)
      have hmain :
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) +
              ((k + 1 : ℝ) / ((k + 1 : ℝ) + 1)) ≤
            (k + 1 : ℝ) := by
        nlinarith [hk, hfrac]
      simpa [Nat.cast_add, Nat.cast_one] using hmain

/-- Helper for Theorem 8.37: the weighted telescope keeps the negative squared-distance tail before
it is discarded in the final bound. -/
lemma weighted_expected_gap_sum_with_tail_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
      -(σ * k * (k + 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[k + 1] ω - xStar‖ ^ (2 : ℕ)] +
        h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
  let d : ℕ → ℝ := fun m ↦ μ[fun ω ↦ ‖x̄[m] ω - xStar‖ ^ (2 : ℕ)]
  have hsum_le :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
              (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1) +
              (n : ℝ) * (h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) := by
    -- Multiply the one-step gap estimate by `n` before summing over the prefix.
    refine Finset.sum_le_sum ?_
    intro n hn
    have hstep :=
      expected_one_step_gap_le_of_strongly_convex_stepsize
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar n
    have hmul :
        (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt) ≤
          (n : ℝ) *
            ((σ * (n - 1 : ℝ) / 4) * d n -
              (σ * (n + 1 : ℝ) / 4) * d (n + 1) +
              h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    nlinarith
  have htele :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
              (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1)) =
        -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) :=
    stronglyConvexWeightedDistanceTelescope (σ := σ) d k
  have hrem_eq :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ (n : ℝ) * (h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) =
        (h_oracle.L_tilde_f ^ (2 : ℕ) / σ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) := by
    -- Pull the constant factor `L_tilde_f^2 / σ` out of the finite sum.
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    field_simp [hσ.ne']
  have hconst_nonneg : 0 ≤ h_oracle.L_tilde_f ^ (2 : ℕ) / σ := by
    positivity
  have hrem_le :
      (h_oracle.L_tilde_f ^ (2 : ℕ) / σ) *
          Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) ≤
        h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
    -- The harmonic-type remainder is bounded by `k`.
    have hscaled :=
      mul_le_mul_of_nonneg_left (sumNatDivSucc_le k) hconst_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
  calc
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦
          (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
            (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1) +
            (n : ℝ) * (h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) :=
      hsum_le
    _ =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦
            (σ * (n : ℝ) * ((n : ℝ) - 1) / 4) * d n -
              (σ * (n : ℝ) * ((n : ℝ) + 1) / 4) * d (n + 1)) +
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (n : ℝ) * (h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (n + 1 : ℝ)))) := by
          rw [Finset.sum_add_distrib]
    _ =
        -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) +
          (h_oracle.L_tilde_f ^ (2 : ℕ) / σ) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (n : ℝ) / (n + 1 : ℝ)) := by
          rw [htele, hrem_eq]
    _ ≤
        -(σ * (k : ℝ) * (k + 1 : ℝ) / 4) * d (k + 1) +
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
          gcongr
    _ =
        -(σ * k * (k + 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[k + 1] ω - xStar‖ ^ (2 : ℕ)] +
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
          simp [d]

/-- Helper for Theorem 8.37: the `n`-weighted telescope obtained by summing the integrated
one-step inequalities. -/
lemma weighted_expected_gap_sum_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
      h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
  have htail :=
    weighted_expected_gap_sum_with_tail_le_of_strongly_convex_stepsize
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar k
  have htail_nonpos :
      -(σ * k * (k + 1 : ℝ) / 4) * μ[fun ω ↦ ‖x̄[k + 1] ω - xStar‖ ^ (2 : ℕ)] ≤ 0 := by
    -- The terminal squared-distance term is nonnegative, so the prefactor contributes a
    -- nonpositive tail.
    have hsq_nonneg :
        0 ≤ μ[fun ω ↦ ‖x̄[k + 1] ω - xStar‖ ^ (2 : ℕ)] := by
      exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun ω ↦ by positivity
    have hcoeff_nonneg : 0 ≤ σ * k * (k + 1 : ℝ) / 4 := by
      positivity
    have hprod_nonneg :
        0 ≤ (σ * k * (k + 1 : ℝ) / 4) *
          μ[fun ω ↦ ‖x̄[k + 1] ω - xStar‖ ^ (2 : ℕ)] := by
      exact mul_nonneg hcoeff_nonneg hsq_nonneg
    simpa [neg_mul] using neg_nonpos.mpr hprod_nonneg
  linarith

/-- Helper for Theorem 8.37: normalizing the weighted telescope gives the exact simplex-weighted
objective-gap estimate used in the ergodic part of the proof. -/
lemma normalized_strongly_convex_weighted_gap_le
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {xStar : E} (hxStar : xStar ∈ XStar) {k : ℕ} (hk : 0 < k) :
    Finset.sum (Finset.range (k + 1))
        (fun n ↦
          ((2 : ℝ) * n / (k * (k + 1) : ℝ)) *
            (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  have hweighted :=
    weighted_expected_gap_sum_le_of_strongly_convex_stepsize
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar k
  have hkR_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk
  have hrewrite :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦
            ((2 : ℝ) * n / (k * (k + 1) : ℝ)) *
              (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) =
        ((2 : ℝ) / (k * (k + 1) : ℝ)) *
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
    -- Rewrite the normalized coefficients as a common scalar factor.
    calc
      Finset.sum (Finset.range (k + 1))
          (fun n ↦
            ((2 : ℝ) * n / (k * (k + 1) : ℝ)) *
              (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦
            ((2 : ℝ) / (k * (k + 1) : ℝ)) *
              ((n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt))) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            field_simp [hkR_pos.ne']
      _ =
          ((2 : ℝ) / (k * (k + 1) : ℝ)) *
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
            rw [← Finset.mul_sum]
  have hscaled :=
    mul_le_mul_of_nonneg_left hweighted
      (by positivity : 0 ≤ (2 : ℝ) / (k * (k + 1) : ℝ))
  rw [hrewrite]
  have hratio :
      ((2 : ℝ) / (k * (k + 1) : ℝ)) * (h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ) =
        2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
    field_simp [hσ.ne', hkR_pos.ne']
  simpa [hratio] using hscaled

omit [MeasurableSpace Ω] [MeasurableSpace E] [BorelSpace E] in
/-- Helper for Theorem 8.37: for `k > 0`, the weighted average iterate is a convex combination of
feasible iterates, hence it remains in `C` pathwise. -/
lemma strongly_convex_average_iterate_mem_feasible
    {k : ℕ} (hk : 0 < k) :
    ∀ ω,
      x^(k) ω ∈ C :=
  by
    intro ω
    rcases projected_subgradient_strongly_convex_average_weights_form_simplex
      (k := k) hk with ⟨hnonneg, hsum⟩
    -- Rewrite the average iterate as the convex combination from the textbook formula.
    rw [stochastic_projected_subgradient_strongly_convex_average_iterate_eq_sum]
    exact
      Convex.sum_mem (s := C) (t := Finset.range (k + 1))
        (w := fun n ↦ α[k](n)) (z := fun n ↦ x̄[n] ω) h_problem.feasible_convex
        hnonneg hsum (fun n hn ↦ (x[n] ω).property)

/-- Helper for Theorem 8.37: for `k > 0`, Jensen's inequality converts the value gap at the
stochastic weighted average iterate into the simplex-weighted sum of the expected iterate gaps. -/
lemma averageIterateGap_le_weightedExpectedGaps
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    {k : ℕ} (hk : 0 < k) :
    μ[fun ω ↦ (f (x^(k) ω)).toReal] - fOpt ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦ α[k](n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let avgGap : Ω → ℝ := fun ω ↦ (f (x^(k) ω)).toReal - fOpt
  let weightedGap : Ω → ℝ := fun ω ↦
    Finset.sum (Finset.range (k + 1))
      (fun n ↦ α[k](n) * ((f (x̄[n] ω)).toReal - fOpt))
  rcases projected_subgradient_strongly_convex_average_weights_form_simplex
    (k := k) hk with ⟨hnonneg, hsum⟩
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun z : E ↦ (f z).toReal) :=
    convexOn_toReal_of_is_convex_function h_problem.convex (fun z _ ↦ h_problem.ne_bot z)
  have hiterate_mem :
      ∀ n ∈ Finset.range (k + 1), ∀ ω, x̄[n] ω ∈ effective_domain f := by
    intro n hn ω
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[n] ω).property)
  have hpointwise :
      ∀ ω, avgGap ω ≤ weightedGap ω := by
    intro ω
    have hJensen :
        (f (x^(k) ω)).toReal ≤
          Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f (x̄[n] ω)).toReal) := by
      -- Rewrite the stochastic average iterate to the finite convex combination used by Jensen.
      rw [stochastic_projected_subgradient_strongly_convex_average_iterate_eq_sum]
      simpa [smul_eq_mul] using hconv.map_sum_le hnonneg hsum (fun n hn ↦ hiterate_mem n hn ω)
    have hsum_const :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) = fOpt := by
      -- The simplex weights sum to one, so the constant term is preserved exactly.
      calc
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) =
            (Finset.sum (Finset.range (k + 1)) fun n ↦ α[k](n)) * fOpt := by
              exact (Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ α[k](n)) fOpt).symm
        _ = fOpt := by
              rw [hsum]
              ring
    have hgap_rewrite :
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f (x̄[n] ω)).toReal) - fOpt =
          weightedGap ω := by
      -- Pull the constant `fOpt` through the finite convex combination.
      calc
        Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f (x̄[n] ω)).toReal) - fOpt =
            Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f (x̄[n] ω)).toReal) -
              Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * fOpt) := by
                rw [hsum_const]
        _ =
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ α[k](n) * ((f (x̄[n] ω)).toReal - fOpt)) := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl ?_
                intro n hn
                ring
        _ = weightedGap ω := by
              rfl
    -- Jensen gives the value inequality, and the simplex identity rewrites it into the gap form.
    calc
      avgGap ω ≤
          Finset.sum (Finset.range (k + 1)) (fun n ↦ α[k](n) * (f (x̄[n] ω)).toReal) - fOpt := by
            dsimp [avgGap]
            linarith
      _ = weightedGap ω := hgap_rewrite
  have hweighted_int : Integrable weightedGap μ := by
    -- The weighted iterate-gap process is integrable termwise along the finite prefix.
    simpa [weightedGap] using
      (integrable_finset_sum (s := Finset.range (k + 1)) fun n hn ↦
        (integrableIterateObjectiveGap
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_strong hσ h_oracle hxStar n).const_mul (α[k](n)))
  have hf_meas : Measurable (fun x : E ↦ (f x).toReal) := by
    -- The closed constrained problem hypothesis gives measurability of the extended-real objective.
    have hmeas_ereal : Measurable f := by
      simpa using h_problem.closed.measurable
    simpa using Measurable.ereal_toReal hmeas_ereal
  have havg_iter_aesm : AEStronglyMeasurable (x^(k)) μ := by
    -- Finite linear combinations of the stochastic iterates remain a.e. strongly measurable.
    rw [stochastic_projected_subgradient_strongly_convex_average_iterate_eq_sum]
    exact (Finset.range (k + 1)).aestronglyMeasurable_fun_sum fun n _ ↦
      (stochastic_iterate_aestronglyMeasurable
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_oracle n).const_smul (α[k](n))
  have havg_gap_aemeas : AEMeasurable avgGap μ := by
    -- Compose the measurable objective with the averaged iterate and subtract the constant gap.
    exact (hf_meas.comp_aemeasurable havg_iter_aesm.aemeasurable).sub aemeasurable_const
  have havg_gap_int : Integrable avgGap μ := by
    have hdom : ∀ᵐ ω ∂μ, ‖avgGap ω‖ ≤ weightedGap ω := by
      filter_upwards with ω
      have havg_nonneg : 0 ≤ avgGap ω := by
        simpa [avgGap] using
          feasibleObjectiveGap_nonneg h_problem
            (strongly_convex_average_iterate_mem_feasible
              (h_problem := h_problem) (g := g) (t := t) (x0 := x0) hk ω)
      rw [Real.norm_of_nonneg havg_nonneg]
      exact hpointwise ω
    exact Integrable.mono' hweighted_int havg_gap_aemeas.aestronglyMeasurable hdom
  have havg_gap_value :
      μ[fun ω ↦ (f (x^(k) ω)).toReal] - fOpt = MeasureTheory.integral μ avgGap := by
    have havg_val_int : Integrable (fun ω ↦ (f (x^(k) ω)).toReal) μ := by
      -- Add the constant `fOpt` back to the already integrable averaged gap.
      simpa [avgGap, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        havg_gap_int.add (integrable_const fOpt)
    -- Rewrite the averaged value gap as the integral of the pointwise averaged gap.
    simpa [avgGap] using
      (MeasureTheory.integral_sub havg_val_int (integrable_const fOpt)).symm
  have hweighted_gap_value :
      MeasureTheory.integral μ weightedGap =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ α[k](n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
    -- Exchange the finite sum and the expectation, then rewrite each term as an expected gap.
    rw [MeasureTheory.integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro n hn
      rw [integral_const_mul]
      have hgap_value :
          μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt =
            MeasureTheory.integral μ (fun ω ↦ (f (x̄[n] ω)).toReal - fOpt) := by
        have hgap_int :=
          integrableIterateObjectiveGap
            (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
            h_strong hσ h_oracle hxStar n
        have hval_int : Integrable (fun ω ↦ (f (x̄[n] ω)).toReal) μ := by
          -- Restore the constant to convert the integrable gap into the integrable objective value.
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            hgap_int.add (integrable_const fOpt)
        -- Normalize each iterate expectation into the integral of its gap function.
        simpa using
          (MeasureTheory.integral_sub hval_int (integrable_const fOpt)).symm
      rw [hgap_value]
    · intro n hn
      exact
        (integrableIterateObjectiveGap
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_strong hσ h_oracle hxStar n).const_mul (α[k](n))
  have hintegral_le :
      MeasureTheory.integral μ avgGap ≤ MeasureTheory.integral μ weightedGap := by
    -- Integrate the pointwise Jensen gap inequality once both sides are known to be integrable.
    refine integral_mono_ae havg_gap_int hweighted_int ?_
    exact Filter.Eventually.of_forall hpointwise
  -- Route correction: keep the Jensen transport as a separate expectation lemma, rather than
  -- mixing it with the one-step stochastic normalization.
  calc
    μ[fun ω ↦ (f (x^(k) ω)).toReal] - fOpt = MeasureTheory.integral μ avgGap :=
      havg_gap_value
    _ ≤ MeasureTheory.integral μ weightedGap := hintegral_le
    _ =
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ α[k](n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) :=
      hweighted_gap_value

-- Proof sketch: combine the conditional one-step estimate from Lemma 8.11 with the unbiased
-- oracle hypothesis from Assumption 8.34 and the strong-convexity lower support inequality from
-- Theorem 5.24. Substituting the stepsizes `t_n = 2 / (σ (n + 1))`, taking expectations, and
-- summing the weighted inequalities from `n = 0` to `k` telescopes the squared-distance terms and
-- yields the stated `O(1 / k)` bound for the expected running minimum.
/--
Part (1) of Theorem 8.37: under Assumptions 8.7 and 8.34, if `f` is `σ`-strongly convex with
`σ > 0`, the stochastic projected subgradient method uses the stepsizes
`t_k = 2 / (σ (k + 1))`, and the sampled directions satisfy the oracle assumptions along the
generated iterates, with each iterate `x^n` measurable as a random variable, then the expected
best objective value attained among the first `k + 1`
stochastic iterates satisfies
`E(f_best^k) - fOpt ≤ 2 L_tilde_f^2 / (σ (k + 1))`. -/
theorem stochastic_projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (k : ℕ) :
    μ[fun ω ↦
        best_achieved_function_value (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k] -
      fOpt ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hbest0 :
        (fun ω ↦
          best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) 0) =
          fun ω ↦ (f (x̄[0] ω)).toReal := by
      -- The prefix of length one contains only the initial iterate.
      funext ω
      unfold best_achieved_function_value
      simp
    have hgap0 :=
      expected_one_step_gap_le_of_strongly_convex_stepsize
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar 0
    have hsq0_nonneg :
        0 ≤ μ[fun ω ↦ ‖x̄[0] ω - xStar‖ ^ (2 : ℕ)] := by
      exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun ω ↦ by positivity
    have hsq1_nonneg :
        0 ≤ μ[fun ω ↦ ‖x̄[1] ω - xStar‖ ^ (2 : ℕ)] := by
      exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun ω ↦ by positivity
    have hbase0 :
        μ[fun ω ↦ (f (x̄[0] ω)).toReal] - fOpt ≤
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
      have hfirst :
          μ[fun ω ↦ (f (x̄[0] ω)).toReal] - fOpt ≤
            h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        nlinarith [hgap0, hsq0_nonneg, hsq1_nonneg]
      have hconst_nonneg :
          0 ≤ h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        positivity
      have hsecond :
          h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) ≤
            2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
        calc
          h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) ≤
              h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) +
                h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
                  linarith
          _ = 2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
                ring
      exact hfirst.trans hsecond
    -- At `k = 0`, the schedule-specific one-step estimate already bounds the initial gap.
    rw [hbest0]
    simpa using hbase0
  · let bestVal : Ω → ℝ := fun ω ↦
      best_achieved_function_value
        (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k
    let bestGap : Ω → ℝ := fun ω ↦ bestVal ω - fOpt
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hbestGap_int :
        Integrable bestGap μ := by
      simpa [bestGap, bestVal] using
        integrableBestAchievedGap
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_strong hσ h_oracle hxStar k
    have hbestVal_int : Integrable bestVal μ := by
      -- Add the constant `fOpt` back to the already integrable best-gap process.
      have := hbestGap_int.add (integrable_const fOpt)
      simpa [bestGap, bestVal, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hweighted :=
      weighted_expected_gap_sum_le_of_strongly_convex_stepsize
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar k
    have hbest_sum :
        (Finset.sum (Finset.range (k + 1)) fun n ↦ (n : ℝ)) *
            (μ[bestVal] - fOpt) ≤
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
      calc
        (Finset.sum (Finset.range (k + 1)) fun n ↦ (n : ℝ)) * (μ[bestVal] - fOpt) =
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ (n : ℝ) * (μ[bestVal] - fOpt)) := by
                exact Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ (n : ℝ))
                  (μ[bestVal] - fOpt)
        _ ≤ Finset.sum (Finset.range (k + 1))
              (fun n ↦ (n : ℝ) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) := by
                refine Finset.sum_le_sum ?_
                intro n hn
                have hobjGap_int :
                    Integrable (fun ω ↦ (f (x̄[n] ω)).toReal - fOpt) μ := by
                  exact
                    integrableIterateObjectiveGap
                      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
                      h_strong hσ h_oracle hxStar n
                have hobj_int : Integrable (fun ω ↦ (f (x̄[n] ω)).toReal) μ := by
                  have := hobjGap_int.add (integrable_const fOpt)
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
                have hbest_le :
                    μ[bestVal] ≤ μ[fun ω ↦ (f (x̄[n] ω)).toReal] := by
                  refine integral_mono_ae hbestVal_int hobj_int ?_
                  exact Filter.Eventually.of_forall fun ω ↦
                    best_achieved_function_value_le_objective_value
                      (fun x : E ↦ (f x).toReal) (fun j ↦ x̄[j] ω) k n hn
                exact mul_le_mul_of_nonneg_left
                  (sub_le_sub_right hbest_le fOpt)
                  (by positivity)
    have hmain :
        ((k : ℝ) * (k + 1 : ℝ) / 2) * (μ[bestVal] - fOpt) ≤
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
      rw [sumRangeNatCast] at hbest_sum
      exact hbest_sum.trans hweighted
    have hkR_pos : 0 < (k : ℝ) := by
      exact_mod_cast hk_pos
    have hcoeff_pos : 0 < (k : ℝ) * (k + 1 : ℝ) / 2 := by
      positivity
    have hmain' :
        (μ[bestVal] - fOpt) * ((k : ℝ) * (k + 1 : ℝ) / 2) ≤
          h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ := by
      simpa [mul_comm] using hmain
    have hratio :
        (h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ) /
            ((k : ℝ) * (k + 1 : ℝ) / 2) =
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      field_simp [hσ.ne', hkR_pos.ne']
    -- Divide by the positive weight sum `k (k + 1) / 2` to isolate the expected best gap.
    calc
      μ[fun ω ↦
          best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) k] - fOpt =
          μ[bestVal] - fOpt := by
            rfl
      _ ≤
          (h_oracle.L_tilde_f ^ (2 : ℕ) * k / σ) /
            ((k : ℝ) * (k + 1 : ℝ) / 2) :=
        (le_div_iff₀ hcoeff_pos).2 hmain'
      _ = 2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := hratio

-- Proof sketch: start from the weighted estimate proved for the expected iterate values in the
-- proof of part (1), divide by `k (k + 1) / 2`, and rewrite the normalized coefficients as the
-- canonical strong-convexity weights. Jensen's inequality for the convex restriction of `f` then
-- transfers the estimate to the averaged random iterate `x^(k)`.
/-- Part (2) of Theorem 8.37: with the same assumptions as in part (1), the weighted average random
iterate
`x^(k) = ∑_{n=0}^k α_n^k x^n`, where `α_n^k = 2 n / (k (k + 1))` for `k > 0` and `x^(0) = x^0`,
satisfies the same expected objective-gap bound
`E(f(x^(k))) - fOpt ≤ 2 L_tilde_f^2 / (σ (k + 1))`. -/
theorem stochastic_projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ)
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (h_iterate_meas : ∀ n, Measurable (x̄[n]))
    (h_oracle :
      StochasticProjectedSubgradientOracle μ (fun x ↦ (f x).toReal)
        x̄ (fun n ω ↦ g n (x[n] ω) ω))
    (k : ℕ) :
    μ[fun ω ↦ (f (x^(k) ω)).toReal] -
      fOpt ≤
      2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  by_cases hk0 : k = 0
  · subst hk0
    have hbest0 :
        μ[fun ω ↦
            best_achieved_function_value
              (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) 0] - fOpt ≤
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (0 + 1 : ℝ)) := by
      -- Part (a) already controls the single-point prefix at `k = 0`.
      simpa using
        stochastic_projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
          (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
          h_strong hσ h_stepsize h_iterate_meas h_oracle 0
    have hbest0_eq :
        (fun ω ↦
          best_achieved_function_value
            (fun x : E ↦ (f x).toReal) (fun n ↦ x̄[n] ω) 0) =
          fun ω ↦ (f (x̄[0] ω)).toReal := by
      -- The running minimum over a singleton prefix is the initial iterate value.
      funext ω
      unfold best_achieved_function_value
      simp
    rw [hbest0_eq] at hbest0
    -- The degenerate weighted average coincides with the initial iterate.
    simpa [stochastic_projected_subgradient_strongly_convex_average_iterate_zero] using hbest0
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have havg :=
      averageIterateGap_le_weightedExpectedGaps
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_oracle hk_pos
    have hweighted :=
      normalized_strongly_convex_weighted_gap_le
        (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
        h_strong hσ h_stepsize h_iterate_meas h_oracle hxStar hk_pos
    have hweighted_alpha :
        Finset.sum (Finset.range (k + 1))
            (fun n ↦ α[k](n) * (μ[fun ω ↦ (f (x̄[n] ω)).toReal] - fOpt)) ≤
          2 * h_oracle.L_tilde_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) := by
      -- Rewrite the canonical coefficients `α_n^k` to the normalized closed form.
      simpa [projected_subgradient_strongly_convex_average_weight_eq_of_pos hk_pos] using hweighted
    -- Route correction: part (b) now closes by composing the Jensen adapter with the normalized
    -- weighted-gap estimate, instead of interleaving Jensen with the one-step stochastic proof.
    exact havg.trans hweighted_alpha

end Measure

end
