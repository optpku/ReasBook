/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {α : Type u} {f : α → ℝ} {x0 : α} {gStar : ℕ → ℝ} {L ω fStar : ℝ}

/- Primary domain: square-root complexity bounds for real optimization-error quantities.

Source/core/bridge triage for Proposition 1.6.10:
* source-facing: the textbook stopping criterion for `g_N^*`
* core/canonical: `sqrt_rate_complexity_bound` from `Definition_1_2_5.lean`
* bridge/view: the concrete constant `Real.sqrt ((L * (f x0 - fStar)) / ω)` together with the
  shifted sequence view `k ↦ gStar (k - 1)`

Relevant owner-style declarations sampled before refining:
* `sqrt_rate_complexity_bound` in `Definition_1_2_5.lean`
* `HasConvergenceRateOfOrder` in `Definition_1_6_9.lean`
* `HasGeometricRateOfConvergence.complexity_bound` in `Definition_1_2_6.lean`
* `minGradientNormAlongIterates_le_sqrt` in `Theorem_1_6_8.lean`

Primitive data:
* the sequence `gStar`
* the concrete square-root constant `Real.sqrt ((L * (f x0 - fStar)) / ω)`
* the pointwise estimate at index `N`

Derived API:
* the source-facing `ε`-complexity conclusion, obtained by applying the owner theorem at the
  shifted index `N + 1` -/

/-- Proposition 1.6.10: if the textbook rate estimate
`g_N^* ≤ [ω⁻¹ L (f(x₀) - f^*)]^{1/2} / (N + 1)^{1/2}` holds and
`N + 1 ≥ L (f(x₀) - f^*) / (ω ε^2)`, then `g_N^* ≤ ε`. -/
-- Proof sketch: apply the assumed rate bound at the chosen index `N`, then use the lower bound on
-- `N + 1`; if `ω = 0` then the rate estimate already gives `g_N^* ≤ 0`, while in the `ω ≠ 0`
-- branch the threshold rewrites to the owner theorem's canonical `(c / ε)^2` form.
theorem le_of_complexity_bound_from_rate_estimate
    (hRate :
      ∀ N : ℕ,
        gStar N ≤
          Real.sqrt ((L * (f x0 - fStar)) / ω) / Real.sqrt ((N : ℝ) + 1))
    {N : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    (hN : (L * (f x0 - fStar)) / (ω * ε ^ (2 : ℕ)) ≤ (N : ℝ) + 1) :
    gStar N ≤ ε := by
  let c : ℝ := Real.sqrt ((L * (f x0 - fStar)) / ω)
  let a : ℝ := (L * (f x0 - fStar)) / ω
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hbound : ∀ ⦃k : ℕ⦄, 0 < k → gStar (k - 1) ≤ c / Real.sqrt (k : ℝ) := by
    intro k hk
    have hk' : (((k - 1 : ℕ) : ℝ) + 1) = k := by
      exact_mod_cast Nat.succ_pred_eq_of_pos hk
    simpa [c, hk'] using hRate (k - 1)
  have hcomplexity : (c / ε) ^ (2 : ℕ) ≤ ((N + 1 : ℕ) : ℝ) := by
    by_cases hω : ω = 0
    · have hc : c = 0 := by
        simp [c, hω]
      calc
        (c / ε) ^ (2 : ℕ) = 0 := by simp [hc]
        _ ≤ ((N + 1 : ℕ) : ℝ) := by positivity
    · have hN' : a / ε ^ (2 : ℕ) ≤ (N : ℝ) + 1 := by
        change ((L * (f x0 - fStar)) / ω) / ε ^ (2 : ℕ) ≤ (N : ℝ) + 1
        calc
          ((L * (f x0 - fStar)) / ω) / ε ^ (2 : ℕ) =
              (L * (f x0 - fStar)) / (ω * ε ^ (2 : ℕ)) := by
            field_simp [hω, hε_ne]
          _ ≤ (N : ℝ) + 1 := hN
      by_cases hrad : 0 ≤ a
      · have hsq : c ^ (2 : ℕ) = a := by
          simpa [a, c, pow_two] using Real.sq_sqrt hrad
        calc
          (c / ε) ^ (2 : ℕ) = c ^ (2 : ℕ) / ε ^ (2 : ℕ) := by
            field_simp [hε_ne]
          _ = a / ε ^ (2 : ℕ) := by rw [hsq]
          _ ≤ (N : ℝ) + 1 := hN'
          _ = ((N + 1 : ℕ) : ℝ) := by norm_num
      · have hc : c = 0 := by
          simpa [a, c] using Real.sqrt_eq_zero_of_nonpos (le_of_lt <| lt_of_not_ge hrad)
        calc
          (c / ε) ^ (2 : ℕ) = 0 := by simp [hc]
          _ ≤ ((N + 1 : ℕ) : ℝ) := by positivity
  simpa using sqrt_rate_complexity_bound hbound hε (Nat.succ_pos N) hcomplexity

end
