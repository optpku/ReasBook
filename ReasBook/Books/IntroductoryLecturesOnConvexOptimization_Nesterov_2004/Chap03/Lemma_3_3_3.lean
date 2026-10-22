/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_68
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1

noncomputable section

universe u

open scoped LevelMethodNotation

/- Lemma 3.3.3 lies in the level-method history / real-inner-product projection domain.

Sampled owner declarations:
* `LevelMethodHistory.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity` in
  `Lemma_3_3_1`
* `constrainedSublevelSet` in `Definition_3_3`, recalled in `Definition_3_68`
* `IsProjectionPointOn.iff_isMinOn` in `Definition_2_33`
* `IsProjectionPointOn.pythagorean_ineq` in `Lemma_2_14`
* `Bornology.IsBounded`, `Metric.diam`, and `Metric.dist_le_diam_of_mem` in mathlib's metric
  boundedness API
* the notation `δ[history](k)`, `ℓ[history](α, k)`, and `𝓛[Q, model, history](α, k)` in
  `Lemma_3_3_1` and `Definition_3_68`

Best owner abstractions:
* the scalar level-method data are organized by `LevelMethodHistory`
* the projection step is organized by `IsProjectionPointOn`

Primitive data:
* the iterate sequence `x`
* the terminal comparison point `xStar`
* the bounded feasible set `Q`
* the model family `model`
* the boundedness witness for `Q` and the diameter bound `Metric.diam Q ≤ D`

Derived API:
* the terminal level-set membership is obtained from the owner interval-monotonicity comparison
  together with `𝓛[Q, model, history](α, i)`
* the one-step squared-distance drop is obtained from `IsProjectionPointOn.pythagorean_ineq`
* the initial-distance estimate `‖x k - xStar‖ ≤ D` is derived from `Metric.dist_le_diam_of_mem`
  and `Metric.diam Q ≤ D`

Source/core/bridge triage:
* source-facing: the step-count estimate and the final block-length bound for bounded feasible
  sets
* core/canonical: `LevelMethodHistory`, `constrainedSublevelSet`, and `IsProjectionPointOn`
* bridge/view: converting a projection hypothesis to `IsMinOn` if needed via
  `IsProjectionPointOn.iff_isMinOn`

Accordingly, this file keeps only the genuinely new counting estimate and the source-facing
bounded-feasible-set block bound. The helper level-set and projection facts are reused directly
from their owners rather than repeated here as parallel public declarations.
-/

section Count

variable {E : Type u} [SeminormedAddCommGroup E]

/-- A uniform positive lower bound on the step lengths together with a telescoping squared-distance
estimate bounds the number of indices in the step range. -/
-- Proof sketch: square the step lower bound to get a uniform lower bound on every
-- `‖x (i + 1) - x i‖ ^ 2`. Sum the distance-drop inequalities for `i = k, …, p`; the middle
-- squared-distance terms telescope, leaving
-- `((p + 1 - k : ℕ) : ℝ) * c^2 ≤ ‖x k - xStar‖^2 ≤ D^2`. The truncated subtraction already makes
-- the bound vacuous when `p < k`, so no separate order hypothesis is needed. Divide by the
-- positive number `c^2`.
theorem count_le_sqdist_ratio_of_uniform_step_lower_bound
    {x : ℕ → E} {xStar : E} {c D : ℝ} {k p : ℕ}
    (hc_pos : 0 < c)
    (hstep_drop :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - xStar‖ ^ (2 : ℕ) + ‖x (i + 1) - x i‖ ^ (2 : ℕ) ≤
          ‖x i - xStar‖ ^ (2 : ℕ))
    (hstep_lower :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → c ≤ ‖x (i + 1) - x i‖)
    (hstart_dist : ‖x k - xStar‖ ≤ D) :
    ((p + 1 - k : ℕ) : ℝ) ≤ D ^ (2 : ℕ) / c ^ (2 : ℕ) := by
  by_cases hkp : k ≤ p
  · have hc_sq_pos : 0 < c ^ (2 : ℕ) := by
      nlinarith [hc_pos]
    have htelescoping :
        ∀ n : ℕ, k + n ≤ p + 1 →
          (n : ℝ) * c ^ (2 : ℕ) + ‖x (k + n) - xStar‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) := by
      intro n
      induction n with
      | zero =>
          intro _
          simp
      | succ n ihn =>
          intro hkn_succ
          have hkn : k + n ≤ p + 1 := by
            omega
          have hik : k ≤ k + n := Nat.le_add_right _ _
          have hip : k + n ≤ p := by
            omega
          have hdrop := hstep_drop hik hip
          have hstep_sq : c ^ (2 : ℕ) ≤ ‖x (k + n + 1) - x (k + n)‖ ^ (2 : ℕ) := by
            nlinarith [hstep_lower hik hip]
          have hi := ihn hkn
          have hdrop' :
              ‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) + c ^ (2 : ℕ) ≤
                ‖x (k + n) - xStar‖ ^ (2 : ℕ) := by
            nlinarith
          have hnext :
              ((n + 1 : ℕ) : ℝ) * c ^ (2 : ℕ) + ‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) ≤
                ‖x k - xStar‖ ^ (2 : ℕ) := by
            have hnext' :
                (n : ℝ) * c ^ (2 : ℕ) +
                    (‖x (k + n + 1) - xStar‖ ^ (2 : ℕ) + c ^ (2 : ℕ)) ≤
                  ‖x k - xStar‖ ^ (2 : ℕ) := by
              nlinarith
            simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc, add_left_comm, add_comm,
              mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hnext'
          simpa [Nat.add_assoc] using hnext
    have hcount_sq :
        (((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ)) ≤ ‖x k - xStar‖ ^ (2 : ℕ) := by
      have hmain := htelescoping (p + 1 - k) (by omega)
      have hnonneg : 0 ≤ ‖x (k + (p + 1 - k)) - xStar‖ ^ (2 : ℕ) := by positivity
      have hbound :
          ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) ≤
            ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) +
              ‖x (k + (p + 1 - k)) - xStar‖ ^ (2 : ℕ) := by
        linarith
      exact hbound.trans hmain
    have hstart_sq : ‖x k - xStar‖ ^ (2 : ℕ) ≤ D ^ (2 : ℕ) := by
      have hD_nonneg : 0 ≤ D := le_trans (norm_nonneg _) hstart_dist
      exact sq_le_sq.mpr (by
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hD_nonneg] using hstart_dist)
    have hcount : ((p + 1 - k : ℕ) : ℝ) * c ^ (2 : ℕ) ≤ D ^ (2 : ℕ) :=
      hcount_sq.trans hstart_sq
    exact (le_div_iff₀ hc_sq_pos).2 hcount
  · have hpk : p + 1 ≤ k := by omega
    have : p + 1 - k = 0 := Nat.sub_eq_zero_of_le hpk
    have hnonneg : 0 ≤ D ^ (2 : ℕ) / c ^ (2 : ℕ) := by
      positivity
    simpa [this] using hnonneg

end Count

section Projection

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lemma 3.3.3: let `Q` be the bounded feasible set from problem `(3.3.1)` with
`diam Q ≤ D`. If the gap satisfies `δ_p ≥ (1 - α) δ_k`, and if the iterates are generated by
projections onto the level sets
`𝓛_i(α) = {x ∈ Q | \hat f_i(X; x) ≤ (1 - α)\hat f_i^* + α f_i^*}` with the step-size lower bound
coming from Lemma `3.3.2`, then
`p + 1 - k ≤ M_f^2 D^2 / ((1 - α)^2 δ_p^2)`. -/
-- Proof sketch: combine
-- `history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity`
-- with the assumptions `model p xStar = fhat(history, p)` and
-- `model i xStar ≤ model p xStar` for `k ≤ i ≤ p` to place `xStar` in every intermediate level
-- set `𝓛[Q, model, history](α, i)`.
-- Then apply
-- `IsProjectionPointOn.pythagorean_ineq` to each projection step to get
-- `‖x (i + 1) - xStar‖^2 + ‖x (i + 1) - x i‖^2 ≤ ‖x i - xStar‖^2`. The step-size hypothesis gives
-- `‖x (i + 1) - x i‖ ≥ ((1 - α) δ[history](i)) / M_f`, and the antitonicity
-- `δ[history](p) ≤ δ[history](i)` on the block upgrades this to the uniform bound
-- `((1 - α) δ[history](p)) / M_f`. Finally use
-- `Metric.dist_le_diam_of_mem` with `x k ∈ Q`, `xStar ∈ Q`, and `Metric.diam Q ≤ D` to bound
-- `‖x k - xStar‖ ≤ D` and invoke
-- `count_le_sqdist_ratio_of_uniform_step_lower_bound`.
theorem iteration_count_bound_of_bounded_feasible_set
    (history : LevelMethodHistory) (Q : Set E) (model : ℕ → E → ℝ)
    (x : ℕ → E) {α Mf D : ℝ} {k p : ℕ} {xStar : E}
    (hα : α < 1)
    (hoptimal_mono :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → fstar(history, p) ≤ fstar(history, i))
    (hgap_antitone :
      ∀ ⦃i j : ℕ⦄, k ≤ i → i ≤ j → j ≤ p → δ[history](j) ≤ δ[history](i))
    (hgap_large : δ[history](p) ≥ (1 - α) * δ[history](k))
    (hgap_pos : 0 < δ[history](p))
    (hMf_pos : 0 < Mf)
    (hQ_bounded : Bornology.IsBounded Q)
    (hdiam : Metric.diam Q ≤ D)
    (hxk_mem : x k ∈ Q)
    (hxStar_mem : xStar ∈ Q)
    (hxStar_terminal : model p xStar = fhat(history, p))
    (hmodel_le_terminal :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → model i xStar ≤ model p xStar)
    (hconvex :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        Convex ℝ (𝓛[Q, model, history](α, i)))
    (hprojection :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        IsProjectionPointOn (𝓛[Q, model, history](α, i)) (x i) (x (i + 1)))
    (hstep_lower :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - x i‖ ≥
          ((1 - α) * δ[history](i)) / Mf) :
    ((p + 1 - k : ℕ) : ℝ) ≤
      (Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) /
        ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) := by
  have hOneSubAlpha_pos : 0 < 1 - α := sub_pos.mpr hα
  have hOneSubAlpha_nonneg : 0 ≤ 1 - α := le_of_lt hOneSubAlpha_pos
  have hxStar_mem_level :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p → xStar ∈ 𝓛[Q, model, history](α, i) := by
    intro i hki hip
    refine mem_constrainedSublevelSet_iff.2 ⟨hxStar_mem, ?_⟩
    have hlevel :=
      history.levelValue_ge_approximateOptimalValue_of_intervalMonotonicity
        (le_of_lt hα)
        hoptimal_mono
        (fun {_} hki' hip' ↦ hgap_antitone (Nat.le_refl k) hki' hip')
        hgap_large
        hki
        hip
    have hmodel : model i xStar ≤ fhat(history, p) := by
      rw [← hxStar_terminal]
      exact hmodel_le_terminal hki hip
    exact_mod_cast le_trans hmodel hlevel
  have hstep_drop_sq :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ‖x (i + 1) - xStar‖ ^ (2 : ℕ) + ‖x (i + 1) - x i‖ ^ (2 : ℕ) ≤
          ‖x i - xStar‖ ^ (2 : ℕ) := by
    intro i hki hip
    simpa [norm_sub_rev, add_comm] using
      IsProjectionPointOn.pythagorean_ineq
        (hconvex hki hip) (hprojection hki hip) (hxStar_mem_level hki hip)
  have hstep_uniform :
      ∀ ⦃i : ℕ⦄, k ≤ i → i ≤ p →
        ((1 - α) * δ[history](p)) / Mf ≤ ‖x (i + 1) - x i‖ := by
    intro i hki hip
    have hterminal_le : δ[history](p) ≤ δ[history](i) :=
      hgap_antitone hki hip (Nat.le_refl p)
    have hscaled :
        ((1 - α) * δ[history](p)) / Mf ≤ ((1 - α) * δ[history](i)) / Mf := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hterminal_le hOneSubAlpha_nonneg)
        (le_of_lt hMf_pos)
    exact hscaled.trans (hstep_lower hki hip)
  have hstart_dist : ‖x k - xStar‖ ≤ D := by
    have hdist : dist (x k) xStar ≤ Metric.diam Q :=
      Metric.dist_le_diam_of_mem hQ_bounded hxk_mem hxStar_mem
    simpa [dist_eq_norm] using hdist.trans hdiam
  have hc_pos : 0 < ((1 - α) * δ[history](p)) / Mf := by
    positivity
  have hcount :=
    count_le_sqdist_ratio_of_uniform_step_lower_bound
      hc_pos hstep_drop_sq hstep_uniform hstart_dist
  have hMf_ne : Mf ≠ 0 := ne_of_gt hMf_pos
  have hgap_ne : δ[history](p) ≠ 0 := ne_of_gt hgap_pos
  have hOneSubAlpha_ne : 1 - α ≠ 0 := ne_of_gt hOneSubAlpha_pos
  calc
    ((p + 1 - k : ℕ) : ℝ)
        ≤ D ^ (2 : ℕ) / ((((1 - α) * δ[history](p)) / Mf) ^ (2 : ℕ)) := hcount
    _ = (Mf ^ (2 : ℕ) * D ^ (2 : ℕ)) /
          ((1 - α) ^ (2 : ℕ) * δ[history](p) ^ (2 : ℕ)) := by
          field_simp [hMf_ne, hgap_ne, hOneSubAlpha_ne]

end Projection
