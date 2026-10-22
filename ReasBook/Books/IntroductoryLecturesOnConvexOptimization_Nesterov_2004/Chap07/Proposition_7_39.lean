/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_40

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u}

/- Proposition 7.39 lies in Chapter 7's relative-scale / scalar iteration-bound domain.

Mandatory domain-style sampling before refinement:
- `relativeScaleIterationBound` in `Proposition_7_40`, the Chapter 7 owner of the logarithmic
  threshold `R_n(δ)`;
- `relativeScaleIterationBound_def` in `Proposition_7_40`, the canonical bridge from the owner to
  the textbook logarithmic formula;
- `relativeScaleIterationBound_lt_uniformBound` in `Proposition_7_40`, the sibling scalar theorem
  in the same domain using the same positivity structure;
- `IsRelativeAccuracy` in `Definition_7_1`, the chapter owner for two-sided relative accuracy.

Best owner abstraction:
- source-facing: Proposition 7.39's upper bound `f(x_k^*) ≤ (1 + δ) f^*` under the mixed scalar
  estimate and the iteration threshold;
- core/canonical: the scalar threshold owner `relativeScaleIterationBound`;
- bridge/view: `relativeScaleIterationBound_def`.

Primitive data:
- the objective `f`, the best point `xkStar`, the positive dimension `n : ℕ+`, and the scalars
  `δ`, `L`, `R`, `fStar`, `k`;
- the source estimate `hEstimate`.

Derived API:
- the owner-level lower bound `relativeScaleIterationBound n δ L R fStar ≤ k`;
- the induced exponential lower bound on
  `Real.exp (δ * (k + 1) / n) - 1`.

The target theorem is source-facing rather than a new owner: it proves only the upper relative
bound and does not carry the lower bound `fStar ≤ f xkStar` needed for the chapter owner
`IsRelativeAccuracy`. The refinement therefore keeps the source theorem surface, reuses the owner
`relativeScaleIterationBound` directly, and avoids reintroducing the raw logarithmic formula as a
parallel local declaration.
-/

-- Proof sketch: use the lower bound on `k` to show that the exponential remainder term in the
-- mixed bound is at most `δ * (1 - δ / 2) * fStar²`, so together with the term
-- `δ * (1 / 2) * fStar²` the right-hand side of `hEstimate` is bounded by
-- `δ * (1 - δ) * fStar²`. After dividing by the positive factor `(1 - δ) * fStar`, this yields
-- `f xkStar - fStar ≤ δ * fStar`, hence `f xkStar ≤ (1 + δ) * fStar`.
/-- Proposition 7.39: if `δ ∈ (0, 1 / 2)`, the quasi-Newton best point `x_k^*` satisfies the
estimate
`(1 - δ) (f(x_k^*) - f^*) f^* ≤ δ \hat f(x^*) + L² R² / (2 n (e^{δ (k + 1) / n} - 1))`
with `\hat f(x^*) = (1 / 2) (f^*)²`, and the iteration index `k` is at least
`R_n(δ) = (n / δ) log (1 + L² R² / (n δ (1 - 2δ) (f^*)²))`, then
`f(x_k^*) ≤ (1 + δ) f^*`. -/
theorem quasiNewton_bestPoint_relative_accuracy_of_iterationBound
    (f : X → ℝ) (xkStar : X) (n : ℕ+) (δ L R fStar : ℝ) (k : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hfStar : 0 < fStar)
    (hEstimate :
      (1 - δ) * (f xkStar - fStar) * fStar ≤
        δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
          (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
            (2 * (n : ℝ) * (Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1)))
    (hk : relativeScaleIterationBound n δ L R fStar ≤ (k : ℝ)) :
    f xkStar ≤ (1 + δ) * fStar := by
  let x : ℝ :=
    ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
      (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)
  let e : ℝ := Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) - 1
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have h_one_sub_δ : 0 < 1 - δ := by
    linarith [hδ.2]
  have h_one_sub_two_δ : 0 < 1 - 2 * δ := by
    linarith [hδ.2]
  have hfStar_sq_pos : 0 < fStar ^ (2 : ℕ) := by
    positivity
  have hscale_pos : 0 < δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) := by
    exact mul_pos (mul_pos hδ.1 h_one_sub_two_δ) hfStar_sq_pos
  have hk_log : Real.log (1 + x) ≤ δ * (k : ℝ) / (n : ℝ) := by
    have hratio_pos : 0 < (n : ℝ) / δ := by
      exact div_pos hn hδ.1
    rw [relativeScaleIterationBound_def] at hk
    have hk_mul : Real.log (1 + x) * ((n : ℝ) / δ) ≤ (k : ℝ) := by
      simpa [x, mul_comm, mul_left_comm, mul_assoc] using hk
    have hk_div : Real.log (1 + x) ≤ (k : ℝ) / ((n : ℝ) / δ) := by
      exact (le_div_iff₀ hratio_pos).2 hk_mul
    have hδ_ne : δ ≠ 0 := hδ.1.ne'
    have hn_ne : (n : ℝ) ≠ 0 := hn.ne'
    have hdiv_eq : (k : ℝ) / ((n : ℝ) / δ) = δ * (k : ℝ) / (n : ℝ) := by
      field_simp [hδ_ne, hn_ne]
    simpa [hdiv_eq] using hk_div
  have hk_step : δ * (k : ℝ) / (n : ℝ) ≤ δ * (((k + 1 : ℕ) : ℝ)) / (n : ℝ) := by
    have hk_cast : (k : ℝ) ≤ (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.le_succ k
    have hδn_nonneg : 0 ≤ δ / (n : ℝ) := by
      exact (div_pos hδ.1 hn).le
    have hmul := mul_le_mul_of_nonneg_left hk_cast hδn_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hlog_arg_pos : 0 < 1 + x := by
    linarith
  have hx_le_e : x ≤ e := by
    have h_exp_bound : 1 + x ≤ Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      refine (Real.log_le_iff_le_exp hlog_arg_pos).1 ?_
      exact hk_log.trans hk_step
    linarith [h_exp_bound]
  have he_pos : 0 < e := by
    have harg_pos : 0 < δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ) := by
      have hk1_pos : 0 < (((k + 1 : ℕ) : ℝ)) := by
        positivity
      exact div_pos (mul_pos hδ.1 hk1_pos) hn
    have hexp_gt_one : 1 < Real.exp (δ * ((k + 1 : ℕ) : ℝ) / (n : ℝ)) := by
      exact (Real.one_lt_exp_iff).2 harg_pos
    linarith
  have hscaled_le :
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
          (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) ≤
        (n : ℝ) * e := by
    have hx_mul :
        (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
            (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) ≤
          e * (n : ℝ) := by
      exact (div_le_iff₀ hn).1 (by
        simpa [x, e, mul_comm, mul_left_comm, mul_assoc] using hx_le_e)
    simpa [mul_comm] using hx_mul
  have hnum_le :
      L ^ (2 : ℕ) * R ^ (2 : ℕ) ≤
        (n : ℝ) * e * (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ)) := by
    exact (div_le_iff₀ hscale_pos).1 hscaled_le
  have hremainder :
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) ≤
        δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) / 2 := by
    have hden_pos : 0 < 2 * (n : ℝ) * e := by
      exact mul_pos (by positivity) he_pos
    refine (div_le_iff₀ hden_pos).2 ?_
    nlinarith [hnum_le]
  have hmain :
      (1 - δ) * (f xkStar - fStar) * fStar ≤
        δ * (1 - δ) * fStar ^ (2 : ℕ) := by
    have hEstimate' :
        (1 - δ) * (f xkStar - fStar) * fStar ≤
          δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
            (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) := by
      simpa [e] using hEstimate
    have hsum :
        δ * ((1 / 2 : ℝ) * fStar ^ (2 : ℕ)) +
            (L ^ (2 : ℕ) * R ^ (2 : ℕ)) / (2 * (n : ℝ) * e) ≤
          δ * (1 - δ) * fStar ^ (2 : ℕ) := by
      nlinarith [hremainder]
    exact hEstimate'.trans hsum
  have hfactor_pos : 0 < (1 - δ) * fStar := by
    exact mul_pos h_one_sub_δ hfStar
  have hgap_div :
      f xkStar - fStar ≤
        (δ * (1 - δ) * fStar ^ (2 : ℕ)) / ((1 - δ) * fStar) := by
    refine (le_div_iff₀ hfactor_pos).2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  have hgap : f xkStar - fStar ≤ δ * fStar := by
    have h_one_sub_δ_ne : 1 - δ ≠ 0 := h_one_sub_δ.ne'
    have hfStar_ne : fStar ≠ 0 := hfStar.ne'
    have hdiv_eq :
        (δ * (1 - δ) * fStar ^ (2 : ℕ)) / ((1 - δ) * fStar) = δ * fStar := by
      field_simp [h_one_sub_δ_ne, hfStar_ne]
    simpa [hdiv_eq] using hgap_div
  nlinarith [hgap]

end
