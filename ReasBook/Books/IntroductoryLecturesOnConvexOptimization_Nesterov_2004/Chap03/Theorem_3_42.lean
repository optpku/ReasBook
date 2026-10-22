/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped WithTopConvexAnalysis

/- Theorem 3.42 lies in the chapter's whole-space subgradient-method / sampled-prefix-value domain.

Mandatory domain-style sampling before refinement:
- `bestFunctionValueUpTo` and `bestFunctionValueUpTo_le` in `Theorem_3_2_10`, the chapter owner
  surface for best sampled objective values;
- the notation `∂[Q] f(x)` and `mem_subdifferentialWithin_iff` in `Theorem_3_44`, the chapter
  owner surface for real-valued relative subgradients;
- `bestFunctionValueUpTo_sub_le_of_constant_stepsizes` in `Theorem_3_41`, a nearby owner-shaped
  sampled-value theorem for the same chapter method family.

Best owner abstraction:
- source-facing: the finite-horizon subgradient-method guarantee;
- core/canonical: `bestFunctionValueUpTo (fun i ↦ f (x i)) N` for the sampled-value conclusion and
  `∂[Set.univ] f(x k)` for chosen whole-space subgradients;
- bridge/view: the existential iterate statement derived from the sampled-value owner inequality.

Primitive data:
- a real inner-product space `E`;
- a real-valued objective `f`, a global minimizer `xStar`, iterates `x`, chosen subgradients `g`,
  stepsizes `η`, and constants `ε`, `M`.

Derived API:
- the whole-space affine lower support inequality read directly from
  `mem_subdifferentialWithin_iff`;
- the owner-level sampled-value bound
  `bestFunctionValueUpTo (fun i ↦ f (x i)) N ≤ f xStar + ε`;
- the existence of an iterate with value at most `f xStar + ε` as a thin corollary.

Source/core/bridge triage:
- source-facing: the finite-horizon guarantee for the unconstrained method;
- core/canonical: `bestFunctionValueUpTo` together with `∂[Set.univ] f(x)`;
- bridge/view: the existential iterate extraction from the best sampled-value owner.

The previous version still exposed the theorem only through a raw existential and kept a public
one-off lemma specializing `mem_subdifferentialWithin_iff` to `Set.univ`. This refinement keeps
the theorem's mathematical content but centers the public API on the chapter's sampled-value owner
and uses the whole-space specialization only internally.
-/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable {f : E → ℝ} {xStar : E} {x g : ℕ → E} {η : ℕ → ℝ} {ε M : ℝ}

/-- Helper for Theorem 3.42: a whole-space subgradient at `y` gives the affine lower-support
comparison against `xStar`. -/
lemma subgradient_gap_le_inner_sub_of_mem_subdifferential_univ
    {y g0 : E} (hg : g0 ∈ ∂[Set.univ] f(y)) :
    f y - f xStar ≤ inner ℝ g0 (y - xStar) := by
  -- Rewrite the owner subgradient predicate into the affine support inequality on `Set.univ`.
  rw [mem_subdifferentialWithin_iff] at hg
  rcases hg with ⟨-, hsubgrad⟩
  have hsupport := hsubgrad (by simp : xStar ∈ Set.univ)
  -- Reorient the support term so that it matches the distance-drop calculation.
  have hinner : inner ℝ g0 (xStar - y) = -inner ℝ g0 (y - xStar) := by
    rw [inner_sub_right, inner_sub_right]
    ring
  rw [hinner] at hsupport
  linarith

/-- Helper for Theorem 3.42: a whole-space subgradient at a point with positive objective gap
cannot vanish. -/
lemma subgradient_ne_zero_of_positive_gap
    {y g0 : E} (hg : g0 ∈ ∂[Set.univ] f(y)) (hgap : 0 < f y - f xStar) :
    g0 ≠ 0 := by
  -- If the chosen subgradient were zero, the support inequality would force a nonpositive gap.
  intro hg0
  have hle :=
    subgradient_gap_le_inner_sub_of_mem_subdifferential_univ
      (f := f) (xStar := xStar) hg
  rw [hg0, inner_zero_left] at hle
  linarith

omit [InnerProductSpace ℝ E] in
/-- Helper for Theorem 3.42: a norm-square bound places the point back inside the reference closed
ball. -/
lemma mem_closedBall_of_norm_sq_le_norm_sq
    {x0 xStar y : E}
    (hbound : ‖y - xStar‖ ^ (2 : ℕ) ≤ ‖x0 - xStar‖ ^ (2 : ℕ)) :
    y ∈ Metric.closedBall xStar ‖x0 - xStar‖ := by
  -- Convert the squared-norm comparison into the metric closed-ball inequality.
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hsq : |‖y - xStar‖| ≤ |‖x0 - xStar‖| := sq_le_sq.mp hbound
  simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hsq

/-- Theorem 3.42: for the subgradient iteration with normalized stepsizes
`αₖ = ηₖ / ‖g(xₖ)‖²`, where `ηₖ = ε` whenever `f(xₖ) - f(x*) ≥ ε`, if every chosen search
direction `gₖ` is a whole-space subgradient of `f` at `xₖ` and every such subgradient on the
reference closed ball has norm at most `M`, then the chapter owner
`bestFunctionValueUpTo (fun i ↦ f (x i)) N` among `x₀, …, x_N` is at most `f(x*) + ε` once
`N ≥ (M² / ε²) ‖x₀ - x*‖²`. -/
-- Proof sketch: argue by contradiction and assume `f (x k) - f xStar ≥ ε` for every `k ≤ N`.
-- On such indices the stepsize equals `ε / ‖g k‖²`. Combine the recursion for `x`, the
-- affine lower-support inequality from `mem_subdifferentialWithin_iff` at `xStar`, and the bound
-- `‖g k‖ ≤ M` on the reference closed ball to
-- obtain `‖x (k + 1) - xStar‖² ≤ ‖x k - xStar‖² - ε² / M²`. Summing this descent estimate from
-- `0` to `N` contradicts the assumed lower bound on `N`, so the best sampled value up to time
-- `N` must already be at most `f xStar + ε`.
theorem subgradient_method_bestFunctionValueUpTo_le_minimizer_add_of_stepsize_bound
    (hxStar : IsMinOn f Set.univ xStar)
    (hε : 0 < ε)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Set.univ] f((x k)))
    (hsubgrad_norm :
      ∀ ⦃y v : E⦄, y ∈ Metric.closedBall xStar ‖x 0 - xStar‖ →
        v ∈ ∂[Set.univ] f(y) → ‖v‖ ≤ M)
    (hη : ∀ k : ℕ, ε ≤ f (x k) - f xStar → η k = ε)
    (hstep : ∀ k : ℕ, x (k + 1) = x k - (η k / ‖g k‖ ^ (2 : ℕ)) • g k)
    {N : ℕ}
    (hN :
      (M ^ (2 : ℕ) / ε ^ (2 : ℕ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤ (N : ℝ)) :
    bestFunctionValueUpTo (fun i ↦ f (x i)) N ≤ f xStar + ε := by
  by_cases hgood : ∃ j : Fin (N + 1), f (x j) ≤ f xStar + ε
  · -- If one sampled iterate is already good, the owner best-value bound is immediate.
    rcases hgood with ⟨j, hj⟩
    exact (bestFunctionValueUpTo_le j).trans hj
  · -- Otherwise every sampled iterate is bad, so we run the textbook distance-drop contradiction.
    have hbad : ∀ j : Fin (N + 1), ε ≤ f (x j) - f xStar := by
      intro j
      have hj_not : ¬ f (x j) ≤ f xStar + ε := by
        intro hj
        exact hgood ⟨j, hj⟩
      have hj_lt : f xStar + ε < f (x j) := lt_of_not_ge hj_not
      linarith
    have hxStar_le_x0 : f xStar ≤ f (x 0) := hxStar (by simp : x 0 ∈ Set.univ)
    have hzero_bad : ε ≤ f (x 0) - f xStar := hbad ⟨0, Nat.succ_pos _⟩
    have hg0_ne : g 0 ≠ 0 := by
      have hgap0 : 0 < f (x 0) - f xStar := by
        linarith [hε, hzero_bad, hxStar_le_x0]
      exact
        subgradient_ne_zero_of_positive_gap
          (f := f) (xStar := xStar) (hsubgrad 0) hgap0
    have hM_pos : 0 < M := by
      have hx0_ball : x 0 ∈ Metric.closedBall xStar ‖x 0 - xStar‖ :=
        by
          simp [Metric.mem_closedBall, dist_eq_norm]
      have hnorm_le : ‖g 0‖ ≤ M := hsubgrad_norm hx0_ball (hsubgrad 0)
      have hnorm_pos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0_ne
      linarith
    have hsqdist_step :
        ∀ {k : ℕ}, k ≤ N →
          x k ∈ Metric.closedBall xStar ‖x 0 - xStar‖ →
          ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / M ^ (2 : ℕ) := by
      intro k hk hxk_ball
      have hg_mem := hsubgrad k
      have hgap : ε ≤ f (x k) - f xStar := hbad ⟨k, Nat.lt_succ_iff.mpr hk⟩
      have hinner_le :
          f (x k) - f xStar ≤ inner ℝ (g k) (x k - xStar) :=
        subgradient_gap_le_inner_sub_of_mem_subdifferential_univ
          (f := f) (xStar := xStar) hg_mem
      have hgap_pos : 0 < f (x k) - f xStar := lt_of_lt_of_le hε hgap
      have hg_ne :
          g k ≠ 0 :=
        subgradient_ne_zero_of_positive_gap
          (f := f) (xStar := xStar) hg_mem hgap_pos
      have hnorm_sq_ne : ‖g k‖ ^ (2 : ℕ) ≠ 0 := by
        exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hg_ne)
      have hη_eq : η k = ε := hη k hgap
      rw [hstep k, hη_eq]
      -- Expand the squared distance after one normalized subgradient step.
      have hexpand :
          ‖(x k - (ε / ‖g k‖ ^ (2 : ℕ)) • g k) - xStar‖ ^ (2 : ℕ) =
            ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (ε / ‖g k‖ ^ (2 : ℕ)) * inner ℝ (x k - xStar) (g k) +
              (ε / ‖g k‖ ^ (2 : ℕ)) ^ 2 * ‖g k‖ ^ (2 : ℕ) := by
        have hfirst :
            (x k - (ε / ‖g k‖ ^ (2 : ℕ)) • g k) - xStar =
              (x k - xStar) - (ε / ‖g k‖ ^ (2 : ℕ)) • g k := by
          abel
        rw [hfirst, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
        by_cases hεnorm : 0 ≤ ε / ‖g k‖ ^ (2 : ℕ)
        · rw [abs_of_nonneg hεnorm]
          ring
        · rw [abs_of_neg (lt_of_not_ge hεnorm)]
          ring
      rw [hexpand]
      have hcross :
          f (x k) - f xStar ≤ inner ℝ (x k - xStar) (g k) := by
        simpa [real_inner_comm] using hinner_le
      have hnorm_le : ‖g k‖ ≤ M := hsubgrad_norm hxk_ball hg_mem
      have hnorm_pos : 0 < ‖g k‖ := norm_pos_iff.mpr hg_ne
      have hfrac_le :
          ε ^ (2 : ℕ) / M ^ (2 : ℕ) ≤ ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) := by
        have hnorm_sq_le : ‖g k‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (M - ‖g k‖)]
        have hrecip : 1 / M ^ (2 : ℕ) ≤ 1 / ‖g k‖ ^ (2 : ℕ) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact hnorm_sq_le
        have hmul :=
          mul_le_mul_of_nonneg_left hrecip (by positivity : 0 ≤ ε ^ (2 : ℕ))
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hmain :
          ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (ε / ‖g k‖ ^ (2 : ℕ)) * inner ℝ (x k - xStar) (g k) +
              (ε / ‖g k‖ ^ (2 : ℕ)) ^ 2 * ‖g k‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) := by
        have hcoef_nonneg : 0 ≤ ε / ‖g k‖ ^ (2 : ℕ) := by positivity
        have hterm :
            (ε / ‖g k‖ ^ (2 : ℕ)) ^ 2 * ‖g k‖ ^ (2 : ℕ) =
              ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) := by
          field_simp [hnorm_sq_ne]
        rw [hterm]
        have hgap_mul :
            ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) ≤
              (ε / ‖g k‖ ^ (2 : ℕ)) * (f (x k) - f xStar) := by
          have hmul := mul_le_mul_of_nonneg_left hgap hcoef_nonneg
          simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
        have hstep1 :
            ‖x k - xStar‖ ^ (2 : ℕ) -
                2 * (ε / ‖g k‖ ^ (2 : ℕ)) * inner ℝ (x k - xStar) (g k) +
                ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) ≤
              ‖x k - xStar‖ ^ (2 : ℕ) -
                2 * (ε / ‖g k‖ ^ (2 : ℕ)) * (f (x k) - f xStar) +
                ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) := by
          have hmul :
              2 * (ε / ‖g k‖ ^ (2 : ℕ)) * (f (x k) - f xStar) ≤
                2 * (ε / ‖g k‖ ^ (2 : ℕ)) * inner ℝ (x k - xStar) (g k) := by
            exact mul_le_mul_of_nonneg_left hcross (by positivity)
          linarith
        have hstep2 :
            ‖x k - xStar‖ ^ (2 : ℕ) -
                2 * (ε / ‖g k‖ ^ (2 : ℕ)) * (f (x k) - f xStar) +
                ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) ≤
              ‖x k - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) := by
          linarith
        exact hstep1.trans hstep2
      have hfinish :
          ‖x k - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / ‖g k‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) - ε ^ (2 : ℕ) / M ^ (2 : ℕ) := by
        linarith
      exact hmain.trans hfinish
    have hsqdist_prefix :
        ∀ m : ℕ, m ≤ N + 1 →
          ‖x m - xStar‖ ^ (2 : ℕ) ≤
            ‖x 0 - xStar‖ ^ (2 : ℕ) - (m : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) := by
      intro m hm
      induction m with
      | zero =>
          simp
      | succ m ihm =>
          have hm_le : m ≤ N + 1 := Nat.le_of_succ_le hm
          have hmN : m ≤ N := by omega
          have hprefix := ihm hm_le
          have hcoef_nonneg : 0 ≤ (m : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) := by
            positivity
          have hsq_le :
              ‖x m - xStar‖ ^ (2 : ℕ) ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
            linarith
          have hxball :
              x m ∈ Metric.closedBall xStar ‖x 0 - xStar‖ :=
            mem_closedBall_of_norm_sq_le_norm_sq
              (x0 := x 0) (xStar := xStar) (y := x m) hsq_le
          have hdrop := hsqdist_step hmN hxball
          have hsucc :
              ‖x (m + 1) - xStar‖ ^ (2 : ℕ) ≤
                ‖x 0 - xStar‖ ^ (2 : ℕ) -
                  ((m + 1 : ℕ) : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) := by
            have hstep' :
                ‖x (m + 1) - xStar‖ ^ (2 : ℕ) ≤
                  ‖x 0 - xStar‖ ^ (2 : ℕ) -
                    (m : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) -
                    ε ^ (2 : ℕ) / M ^ (2 : ℕ) := by
              linarith
            have hrewrite :
                ‖x 0 - xStar‖ ^ (2 : ℕ) -
                    (m : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) -
                    ε ^ (2 : ℕ) / M ^ (2 : ℕ) =
                  ‖x 0 - xStar‖ ^ (2 : ℕ) -
                    ((m + 1 : ℕ) : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) := by
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
            simpa [hrewrite] using hstep'
          exact hsucc
    have hend :
        ‖x (N + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖x 0 - xStar‖ ^ (2 : ℕ) -
            ((N + 1 : ℕ) : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) :=
      hsqdist_prefix (N + 1) (le_rfl)
    have hdrop_total :
        ((N + 1 : ℕ) : ℝ) * (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) ≤
          ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      have hnorm_nonneg : 0 ≤ ‖x (N + 1) - xStar‖ ^ (2 : ℕ) := by positivity
      linarith
    have hratio_pos : 0 < ε ^ (2 : ℕ) / M ^ (2 : ℕ) := by positivity
    have hNplus1_le :
        (N + 1 : ℝ) ≤
          ‖x 0 - xStar‖ ^ (2 : ℕ) / (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) := by
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
        (le_div_iff₀ hratio_pos).2 hdrop_total
    have hrewrite :
        ‖x 0 - xStar‖ ^ (2 : ℕ) / (ε ^ (2 : ℕ) / M ^ (2 : ℕ)) =
          (M ^ (2 : ℕ) / ε ^ (2 : ℕ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      field_simp [hε.ne', hM_pos.ne']
    have hNplus1_le' :
        (N + 1 : ℝ) ≤ (M ^ (2 : ℕ) / ε ^ (2 : ℕ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      rw [← hrewrite]
      exact hNplus1_le
    linarith

/-- The owner inequality in Theorem 3.42 yields an actual sampled iterate whose value is at most
`ε` above the minimizer value. -/
theorem subgradient_method_exists_value_le_minimizer_add_of_stepsize_bound
    (hxStar : IsMinOn f Set.univ xStar)
    (hε : 0 < ε)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Set.univ] f((x k)))
    (hsubgrad_norm :
      ∀ ⦃y v : E⦄, y ∈ Metric.closedBall xStar ‖x 0 - xStar‖ →
        v ∈ ∂[Set.univ] f(y) → ‖v‖ ≤ M)
    (hη : ∀ k : ℕ, ε ≤ f (x k) - f xStar → η k = ε)
    (hstep : ∀ k : ℕ, x (k + 1) = x k - (η k / ‖g k‖ ^ (2 : ℕ)) • g k)
    {N : ℕ}
    (hN :
      (M ^ (2 : ℕ) / ε ^ (2 : ℕ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤ (N : ℝ)) :
    ∃ k ≤ N, f (x k) ≤ f xStar + ε := by
  have hbest :
      bestFunctionValueUpTo (fun i ↦ f (x i)) N ≤ f xStar + ε :=
    subgradient_method_bestFunctionValueUpTo_le_minimizer_add_of_stepsize_bound hxStar hε
      hsubgrad hsubgrad_norm hη hstep hN
  obtain ⟨j, hj⟩ := bestFunctionValueUpTo_exists_eq (fun i ↦ f (x i)) N
  exact ⟨j, Nat.lt_succ_iff.mp j.2, hj.le.trans hbest⟩

end

end
