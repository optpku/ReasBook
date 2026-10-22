/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Order/FiniteFamily.lean
-/

module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin

public section

universe u v

namespace Finite

/-- A finite family of positive elements in a linear order has a common positive
lower bound below any prescribed positive bound. -/
theorem exists_pos_le {ι : Type u} [Finite ι] {α : Type v} [LinearOrder α] [Zero α]
    (bound : α) (threshold : ι → α) (hbound : 0 < bound)
    (hthreshold : ∀ i, 0 < threshold i) :
    ∃ x, 0 < x ∧ x ≤ bound ∧ ∀ i, x ≤ threshold i := by
  classical
  by_cases hι : Nonempty ι
  · letI : Fintype ι := Fintype.ofFinite ι
    have hUniv : (Finset.univ : Finset ι).Nonempty := by
      obtain ⟨i⟩ := hι
      exact ⟨i, Finset.mem_univ i⟩
    let lower : α := Finset.univ.inf' hUniv threshold
    have hlowerPos : 0 < lower := by
      dsimp only [lower]
      rw [Finset.lt_inf'_iff]
      intro i _
      exact hthreshold i
    refine ⟨min bound lower, lt_min hbound hlowerPos, min_le_left _ _, ?_⟩
    intro i
    exact (min_le_right bound lower).trans
      (Finset.inf'_le threshold (Finset.mem_univ i))
  · exact ⟨bound, hbound, le_rfl, fun i ↦ (hι ⟨i⟩).elim⟩

end Finite
