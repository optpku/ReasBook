/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}
  {f : X → ℝ} {φ : U → ℝ}
  {fμ₂ : ℝ → X → ℝ}
  {barx : ℕ → X} {baru : ℕ → U}
  {L2phi D2 : ℝ}

/- This item lies in the chapter's excessive-gap / smoothing-rate domain.

Sampled owner-style declarations:
- `scheme_6_2_37_primal_dual_gap_le_rate` in `Chap06/Theorem_6_2_4`, the canonical Chapter 6
  theorem with the same gap-rate conclusion;
- `primal_dual_gap_bound_of_smoothed_lower_approximation` in `Chap06/Lemma_6_12`, the chapter
  bridge from a lower smoothing estimate and a smoothed residual gap bound to a raw primal-dual
  gap estimate;
- `satisfiesExcessiveGapCondition` in `Chap06/Theorem_6_4`, the source-facing excessive-gap owner
  behind the stagewise inequality used to derive this rate.

Best owner abstraction:
- source-facing: the explicit rate estimate for the raw primal-dual gap along scheme `(6.2.37)`;
- core/canonical: the Chapter 6 primal-dual gap rate theorem;
- bridge/view: none is needed in the statement itself, since the item is already the direct
  source-facing rate claim.

Primitive data:
- the lower smoothing estimate `f x - μ₂ D₂ ≤ f_{μ₂}(x)`;
- the stagewise inequality
  `f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)` with
  `μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`.

Derived API:
- the explicit rate
  `f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))`.

The upstream Chapter 6 file currently packages the same statement through a dependency chain that
is failing earlier in the build, so this item file keeps the statement directly as a theorem
skeleton instead of using a `recall`.
-/

-- Proof sketch: specialize the lower smoothing estimate at
-- `μ₂ = 4 L₂(φ) / ((k + 1) (k + 2))` and `x = \bar x_k`, combine it with the stagewise scheme
-- inequality `f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)`, and rearrange.
/-- Theorem 6.8: if scheme `(6.2.37)` yields
`f_{μ₂,k}(\bar x_k) ≤ φ(\bar u_k)` with
`μ₂,k = 4 L₂(φ) / ((k + 1) (k + 2))`, and if the smoothing family satisfies
`f(x) - μ₂ D₂ ≤ f_{μ₂}(x)` for every `μ₂` and `x`, then
`f(\bar x_k) - φ(\bar u_k) ≤ 4 L₂(φ) D₂ / ((k + 1) (k + 2))` for every integer `k ≥ 0`. -/
theorem primal_dual_gap_le_scheme_6_2_37_rate
    (happrox : ∀ μ₂ x, f x - μ₂ * D2 ≤ fμ₂ μ₂ x)
    (hscheme :
      ∀ k : ℕ,
        fμ₂ ((4 * L2phi) / (((k : ℝ) + 1) * ((k : ℝ) + 2))) (barx k) ≤ φ (baru k))
    (k : ℕ) :
    f (barx k) - φ (baru k) ≤
      (4 * L2phi * D2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  -- Introduce the scheme parameter so both hypotheses share the same expression.
  set μk : ℝ := (4 * L2phi) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) with hμk
  -- Specialize the smoothing lower bound and the stagewise scheme inequality at index `k`.
  have h_lower : f (barx k) - μk * D2 ≤ fμ₂ μk (barx k) := by
    simpa [μk] using happrox μk (barx k)
  have h_upper : fμ₂ μk (barx k) ≤ φ (baru k) := by
    simpa [μk] using hscheme k
  -- Eliminate the smoothed quantity to recover the raw primal-dual gap bound.
  have h_gap : f (barx k) - φ (baru k) ≤ μk * D2 := by
    linarith
  -- Normalize the parameter budget into the closed form announced in the theorem.
  have h_rate :
      μk * D2 = (4 * L2phi * D2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    rw [hμk]
    ring_nf
  -- Rewrite the scheme parameter into the announced explicit rate.
  calc
    f (barx k) - φ (baru k) ≤ μk * D2 := h_gap
    _ = (4 * L2phi * D2) / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := h_rate

end
