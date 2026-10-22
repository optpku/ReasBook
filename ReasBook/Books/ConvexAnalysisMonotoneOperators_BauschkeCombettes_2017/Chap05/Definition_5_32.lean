/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H]
variable {C : Set H} {x : ℕ → H}

/-- Definition 5.32: a sequence `x : ℕ → H` is quasi-Fejér monotone with respect to `C` if for
every `c ∈ C` there is a summable nonnegative error sequence controlling the one-step growth of
the squared distances `‖x n - c‖ ^ 2`. -/
def QuasiFejerMonotone (C : Set H) (x : ℕ → H) : Prop :=
  ∀ c ∈ C, ∃ ε : ℕ → NNReal, Summable ε ∧
    ∀ n : ℕ, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n

-- Proof sketch: unfold `QuasiFejerMonotone` and specialize the defining quantifiers at the chosen
-- point `c ∈ C`.
/-- A quasi-Fejér-monotone sequence admits a summable nonnegative error sequence at each point of
`C` that controls the one-step squared-distance inequality. -/
theorem QuasiFejerMonotone.exists_summable_sqdist_error (h : QuasiFejerMonotone C x)
    (c : H) (hc : c ∈ C) :
    ∃ ε : ℕ → NNReal, Summable ε ∧
      ∀ n : ℕ, ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 + ε n := by
  -- Specialize the defining witnesses at the chosen comparison point.
  exact h c hc

/-- Helper for Definition 5.32: Fejér monotonicity implies the one-step squared-distance estimate
at each comparison point. -/
lemma FejerMonotone.sqdist_step (h : FejerMonotone C x) {c : H} (hc : c ∈ C) (n : ℕ) :
    ‖x (n + 1) - c‖ ^ 2 ≤ ‖x n - c‖ ^ 2 := by
  -- Rewrite the Fejér inequality into a norm inequality in the ambient additive group.
  have hdist : ‖x (n + 1) - c‖ ≤ ‖x n - c‖ := by
    simpa [dist_eq_norm] using h.step c hc n
  -- Square both sides; norms are nonnegative, so the ordered-ring squaring lemma applies.
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist

-- Proof sketch: for each `c ∈ C`, use the zero error sequence `ε n = 0`; it is summable, and the
-- Fejér inequality strengthens the corresponding squared-distance estimate.
/-- Every Fejér-monotone sequence is quasi-Fejér monotone with respect to the same set. -/
theorem FejerMonotone.quasiFejerMonotone (h : FejerMonotone C x) :
    QuasiFejerMonotone C x := by
  intro c hc
  -- Choose the zero error sequence; its summability is immediate.
  refine ⟨fun _ ↦ 0, summable_zero, ?_⟩
  intro n
  -- The squared-distance bridge closes the quasi-Fejér estimate with zero error.
  simpa using h.sqdist_step hc n

end
