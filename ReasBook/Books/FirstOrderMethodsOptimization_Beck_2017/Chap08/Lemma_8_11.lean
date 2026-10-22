/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)

-- Proof sketch: use nonexpansiveness of the metric projection to compare `‖x[k + 1] - xStar‖`
-- with `‖x[k] - t_k g_k - xStar‖`, expand the square, and rewrite the cross term with the
-- subgradient inequality coming from the hypothesis
-- `toDualMap ℝ E (g k (x[k])) ∈ ∂ₛ f(x̄[k])`. Then use
-- `hxStar : xStar ∈ XStar` together with `h_problem.optimal_set_eq` and
-- `h_problem.optimal_value_isGLB` to identify `xStar` as an optimal feasible point with value
-- `fOpt`.
/-- Helper for Lemma 8.11: every point of the optimal set attains the recorded optimal value in
the extended-real objective. -/
private lemma optimal_point_value_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    f xStar = (fOpt : EReal) := by
  -- Unpack the source-facing optimal-set description into feasibility and minimality.
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  -- The minimizer-induced GLB must agree with the problem's stored optimal value.
  exact IsGLB.unique
    (by simpa [Set.mem_image] using (hxStar_data.2.isGLB hxStar_data.1))
    h_problem.optimal_value_isGLB

/-- Helper for Lemma 8.11: every point of the optimal set has real value equal to the recorded
optimal value `fOpt`. -/
lemma optimal_point_toReal_eq_fOpt
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    (f xStar).toReal = fOpt := by
  -- First identify the extended-real value, then drop back to reals.
  rw [optimal_point_value_eq_fOpt h_problem hxStar]
  exact EReal.toReal_coe fOpt

variable [CompleteSpace E]
variable {g : ℕ → C → E} {t : ℕ → ℝ} {x0 : C}

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

/-- Helper for Lemma 8.11: the subgradient inequality at the current iterate controls the optimal
gap by the pairing with the displacement toward an optimal point. -/
lemma subgradient_gap_le_inner_at_iterate
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k]))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    (f x̄[k]).toReal - fOpt ≤ inner ℝ (g k (x[k])) (x̄[k] - xStar) := by
  -- Convert optimality of `xStar` into the feasibility data needed by the subgradient inequality.
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxStar_dom : xStar ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain hxStar_data.1)
  have hxk_dom : x̄[k] ∈ effective_domain f := by
    exact interior_subset (h_problem.feasible_subset_interior_effective_domain (x[k]).2)
  have hxk_top : f x̄[k] ≠ ⊤ := ne_of_lt hxk_dom
  have hxk_bot : f x̄[k] ≠ ⊥ := h_problem.ne_bot _
  -- Rewrite subgradient membership into the textbook supporting-hyperplane inequality.
  have hsub : (toDualMap ℝ E (g k (x[k])) : Module.Dual ℝ E) ∈ ∂ f(x̄[k]) := by
    simpa [mem_strongDualSubdifferential] using h_subgrad k
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hsub
  have hgapE :
      f x̄[k] + ((inner ℝ (g k (x[k])) (xStar - x̄[k]) : ℝ) : EReal) ≤
        (fOpt : EReal) := by
    have hineq := hsub.2 xStar hxStar_dom
    -- Replace the optimal-point value by the recorded optimum before converting to reals.
    simpa [ge_iff_le, InnerProductSpace.toDualMap_apply_apply,
      optimal_point_value_eq_fOpt h_problem hxStar] using
      hineq
  have hgapReal :
      (f x̄[k]).toReal + inner ℝ (g k (x[k])) (xStar - x̄[k]) ≤ fOpt := by
    -- All terms are finite on the feasible set, so the EReal inequality descends to reals.
    have hcoe :
        (((f x̄[k]).toReal + inner ℝ (g k (x[k])) (xStar - x̄[k]) : ℝ) : EReal) ≤
          (fOpt : EReal) := by
      simpa [EReal.coe_toReal hxk_top hxk_bot, EReal.coe_add] using hgapE
    exact EReal.coe_le_coe_iff.mp hcoe
  have hinner_neg :
      inner ℝ (g k (x[k])) (xStar - x̄[k]) =
        -inner ℝ (g k (x[k])) (x̄[k] - xStar) := by
    -- Reorient the displacement so the pairing matches the source statement.
    rw [show xStar - x̄[k] = -(x̄[k] - xStar) by abel, inner_neg_right]
  have hgapReal' :
      (f x̄[k]).toReal + (-inner ℝ (g k (x[k])) (x̄[k] - xStar)) ≤ fOpt := by
    simpa [hinner_neg] using hgapReal
  -- Rearranging the real inequality isolates the optimality gap on the left-hand side.
  have hle :
      (f x̄[k]).toReal ≤ fOpt + inner ℝ (g k (x[k])) (x̄[k] - xStar) := by
    linarith
  exact (sub_le_iff_le_add).2 (by simpa [add_comm] using hle)

/-- Lemma 8.11: under Assumption 8.7, every projected-subgradient step with nonnegative stepsize
satisfies the fundamental inequality
`‖x^{k+1} - xStar‖^2 ≤ ‖x^k - xStar‖^2
  - 2 t_k ((f x^k).toReal - fOpt) + t_k^2 ‖g_k‖^2`
for each optimal point `xStar ∈ XStar`, where the chosen direction at iteration `k` is a
subgradient of `f` at `x^k`. -/
theorem projected_subgradient_method_fundamental_inequality
    (h_subgrad :
      ∀ k,
        toDualMap ℝ E (g k (x[k])) ∈ ∂ₛf(x̄[k]))
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) (ht_nonneg : 0 ≤ t k) :
    ‖x̄[k + 1] - xStar‖ ^ 2 ≤
      ‖x̄[k] - xStar‖ ^ 2 -
        2 * t k * ((f x̄[k]).toReal - fOpt) +
          (t k) ^ 2 * ‖g k (x[k])‖ ^ 2 := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  have hxkp1 :
      x̄[k + 1] =
        metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
          h_problem.feasible_convex (x̄[k] - t k • g k (x[k])) := by
    simpa using
      projected_subgradient_method_iterate_succ C h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex g t x0 k
  have hxStar_proj :
      (metricProjection C h_problem.feasible_nonempty h_problem.feasible_closed
        h_problem.feasible_convex xStar : E) = xStar := by
    simpa [projectionPoint] using
      projectionPoint_eq_self_of_mem C h_problem.feasible_nonempty
        h_problem.feasible_closed h_problem.feasible_convex hxStar_data.1
  have hdist :
      ‖x̄[k + 1] - xStar‖ ≤ ‖(x̄[k] - t k • g k (x[k])) - xStar‖ := by
    simpa [hxkp1, hxStar_proj, dist_eq_norm] using
      LipschitzWith.dist_le_mul
        (metricProjection_nonexpansive C h_problem.feasible_nonempty
          h_problem.feasible_closed h_problem.feasible_convex)
        (x̄[k] - t k • g k (x[k])) xStar
  have hsq :
      ‖x̄[k + 1] - xStar‖ ^ (2 : ℕ) ≤ ‖(x̄[k] - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) := by
    rw [sq_le_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hdist
  have hgap_le_inner :
      (f x̄[k]).toReal - fOpt ≤ inner ℝ (x̄[k] - xStar) (g k (x[k])) := by
    simpa [real_inner_comm] using
      subgradient_gap_le_inner_at_iterate h_problem h_subgrad hxStar k
  have hexpand :
      ‖(x̄[k] - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) =
        ‖x̄[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * inner ℝ (x̄[k] - xStar) (g k (x[k])) +
            (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) := by
    have hrewrite :
        (x̄[k] - t k • g k (x[k])) - xStar = (x̄[k] - xStar) - t k • g k (x[k]) := by
      abel
    rw [hrewrite, norm_sub_sq_real]
    rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    ring
  have hstep_gap :
      ‖(x̄[k] - t k • g k (x[k])) - xStar‖ ^ (2 : ℕ) ≤
        ‖x̄[k] - xStar‖ ^ (2 : ℕ) -
          2 * t k * ((f x̄[k]).toReal - fOpt) +
            (t k) ^ (2 : ℕ) * ‖g k (x[k])‖ ^ (2 : ℕ) := by
    rw [hexpand]
    nlinarith
  exact hsq.trans hstep_gap

end
