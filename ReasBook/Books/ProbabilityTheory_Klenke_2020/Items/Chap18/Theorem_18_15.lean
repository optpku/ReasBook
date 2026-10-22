/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_15.Support

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

section Metropolis

variable (π : ProbabilityMeasure E) (q : E → E → ℝ≥0∞)
variable (hq : IsStochasticMatrix q)
variable (hπ_pos : ∀ x : E, 0 < (π : Measure E) ({x} : Set E))
variable (h_support_symm : ∀ x y : E, 0 < q x y ↔ 0 < q y x)
variable [Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel q)]

include hq hπ_pos h_support_symm

-- Proof sketch: the two aperiodicity branches are now closed in the theorem-local support module.
-- The wrapper theorem only performs the final disjunction split and invokes the imported branch
-- closers.
/-- Theorem 18.15: if, in addition, the proposal kernel is aperiodic or it is not reversible with
respect to `π`, then the Metropolis kernel is aperiodic. -/
theorem metropolisKernel_isAperiodic_of_proposalAperiodic_or_not_reversible
    (haperiodic_or_nonreversible :
      IsAperiodic (discreteMatrixKernel q) ∨
        ¬ Kernel.IsReversible (discreteMatrixKernel q) (π : Measure E)) :
    IsAperiodic (metropolisKernel π q) := by
  -- Route correction: keep the heavy period-transport and reversibility machinery behind the
  -- imported support lemmas, and let the target theorem only dispatch the two textbook branches.
  rcases haperiodic_or_nonreversible with haperiodic | hnonreversible
  · -- Proof comment: the proposal-aperiodic branch is the direct support theorem.
    exact metropolisKernel_isAperiodic_of_proposalAperiodic
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) haperiodic
  · -- Proof comment: the nonreversible branch is closed by the direct self-loop criterion from
    -- the support module.
    exact metropolisKernel_isAperiodic_of_notProposalReversible
      (π := π) (q := q) (hq := hq) (hπ_pos := hπ_pos)
      (h_support_symm := h_support_symm) hnonreversible

end Metropolis

end ProbabilityTheory
