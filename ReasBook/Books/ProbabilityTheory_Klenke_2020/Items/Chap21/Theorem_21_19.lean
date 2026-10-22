/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Theorem_21_19Core

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Theorem 21.19: reflection principle for Brownian motion. For every `a > 0` and `T > 0`,
the strict running maximum on `[0, T]` has probability `2 * P[B T > a]`. -/
theorem reflectionPrincipleForBrownianMotion
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    μ {ω | ∃ s ∈ Set.Icc (0 : NNReal) T, a < B s ω} =
      2 * μ {ω | a < B T ω} := by
  -- Proof comment: reuse the established Chapter 21 owner theorem; this file restores the
  -- label-bearing textbook entry expected by the orchestrator.
  exact runningMaximum_eq_two_mul_brownianTerminalTail (hB := hB) ha hT

end ProbabilityTheory
