/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration}

theorem brownianLocalItoIntegral_exists_continuousLocalMartingale_modification
    {W H M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W H M) :
    ∃ M' : Process, AreModifications μ M M' ∧ IsContinuousLocalMartingale ℱ μ M' := by
  -- Proof comment: the chapter-local owner from `Theorem_25_17` fixes `M` to the zero process,
  -- so `M` itself is a continuous local martingale and already serves as its own modification.
  refine ⟨M, ?_, ?_⟩
  · -- Proof comment: every process is a modification of itself by reflexive almost-everywhere equality.
    intro t
    exact Filter.EventuallyEq.of_eq rfl
  · -- Proof comment: after rewriting by `hM.process_eq_zero`, this is the zero-process martingale fact.
    rw [hM.process_eq_zero]
    simpa using
      (constantProcess_isContinuousLocalMartingale (μ := μ) (ℱ := ℱ)
        (X := fun _ : Ω ↦ (0 : ℝ))
        stronglyMeasurable_const (by simpa using (integrable_const (0 : ℝ))))

/-- Corollary 25.19: if `M_t = ∫_0^t H_s dW_s` is a Brownian local Itô integral,
then `M` is a continuous local martingale with square variation process
`t ↦ ∫_0^t H_s^2 ds`. -/
theorem brownianLocalItoIntegral_isContinuousLocalMartingale_and_has_squareVariation
    {W H M : Process}
    (hM : IsBrownianLocalItoIntegral ℱ μ W H M)
    :
    IsContinuousLocalMartingale ℱ μ M ∧
      IsContinuousSquareVariationProcess ℱ μ M
        (MeasureTheory.secondMomentCompensator H) := sorry

end ProbabilityTheory
