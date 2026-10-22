/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: the conclusion is the textbook inequality `f^*(-v) + g(Lv) ≤ 0`.
- `core/canonical`: the owner declarations are `fenchelDualObjective`, `primalOptimalValue`, and
  Proposition 15.13.
- `bridge/view`: the hypothesis `g^* = g ∘ L` rewrites the owner dual objective to the
  source-facing expression.
-/

-- Proof sketch: apply Proposition 15.13 to obtain `v` with
-- `primalOptimalValue f g = -(fenchelDualObjective f g v)`. The hypothesis `f + g ≥ 0` gives
-- `0 ≤ primalOptimalValue f g`, and the identity `g^* = g ∘ L` rewrites the dual objective term
-- as `f^*(-v) + g(Lv)`.

/-- Corollary 15.15: if `f, g ∈ Γ₀(H)`, if `0 ∈ sri (dom f - dom g)`, if `f + g ≥ 0`, and if
`g^* = g ∘ L` for a bounded linear operator `L`, then there exists `v ∈ H` such that
`f^*(-v) + g(Lv) ≤ 0`. -/
theorem exists_dual_vector_le_zero_of_pointwiseAdd_nonneg_and_conjugate_eq_comp
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hsri : (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g))
    (L : H →L[ℝ] H)
    (hfg_nonneg : ∀ x : H, (0 : EReal) ≤ primalObjective f g x)
    (hg_conj : g.asEReal∗ = g.asEReal ∘ L) :
    ∃ v : H, f.asEReal∗ (-v) + (g (L v) : EReal) ≤ 0 := by
  have hprimal_nonneg : (0 : EReal) ≤ primalOptimalValue f g := by
    rw [primalOptimalValue_eq_iInf_primalObjective]
    exact le_iInf hfg_nonneg
  obtain ⟨v, _, hv⟩ :=
    exists_mem_argmin_fenchelDualObjective_eq_neg_primalOptimalValue_of_zero_mem_sri_sub_effectiveDomain
      f g hf hg hsri
  refine ⟨v, ?_⟩
  have hdual_nonpos : fenchelDualObjective f g v ≤ 0 := by
    have : (0 : EReal) ≤ -fenchelDualObjective f g v := by
      simpa [hv] using hprimal_nonneg
    simpa using this
  simpa [fenchelDualObjective, hg_conj] using hdual_nonpos

end FenchelDuality

end ERealFunction
