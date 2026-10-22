/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use the graph criterion in Definition 20.20. If `(x, u)` is monotonically related
-- to every point of `gra ∂ f`, then Moreau's proximal construction at `x + u` produces
-- `p = Prox_f (x + u)` with `x + u - p ∈ (∂ f) p`; testing the monotonicity relation against
-- `(p, x + u - p)` forces `x = p` and hence `u ∈ (∂ f) x`.
/-- Theorem 20.25: (Moreau) if `f ∈ Γ₀(H)`, then the subdifferential `∂ f` is maximally
monotone. -/
theorem subdifferential_isMaximallyMonotone_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Maximal SetValuedOperator.IsMonotone (∂ f) := by
  rw [SetValuedOperator.maximal_iff_mem_iff]
  intro x u
  constructor
  · intro hu y v hv
    exact (SetValuedOperator.isMonotone_iff (∂ f)).1
      (subdifferential_isMonotone f hf.2.nonempty) hu hv
  · intro hxu
    let p := Prox[f, hf] (x + u)
    have hp : x + u - p ∈ (∂ f) p := by
      simpa [p] using
        (eq_proximityOperator_iff_sub_mem_subdifferential hf (x + u) p).mp rfl
    have hpp : 0 ≤ ⟪x - p, u - (x + u - p)⟫_ℝ := hxu hp
    have hneg : 0 ≤ -‖x - p‖ ^ 2 := by
      calc
        0 ≤ ⟪x - p, u - (x + u - p)⟫_ℝ := hpp
        _ = ⟪x - p, -(x - p)⟫_ℝ := by
          congr 1
          abel_nf
        _ = -‖x - p‖ ^ 2 := by
          rw [inner_neg_right, real_inner_self_eq_norm_sq]
    have hnorm : ‖x - p‖ = 0 := by
      nlinarith [sq_nonneg ‖x - p‖, hneg]
    have hxp : x = p := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
    simpa [hxp] using hp

end SubdifferentialCalculus

end ERealFunction
