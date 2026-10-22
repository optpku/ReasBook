/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets

public section

namespace KKT

universe u v

variable {H : Type u} {ι : Type v}

/-- The strict complementarity condition for `c`, `f`, and `μ` requires every
active constraint to have a strictly positive multiplier. -/
def StrictComplementarity (c : ι → H → ℝ) (f : H) (μ : ι → ℝ) : Prop :=
  ∀ i, i ∈ ActiveSet.active c f → 0 < μ i

/-- `StrictComplementarity c f μ` is equivalent to requiring `0 < μ i`
whenever the corresponding constraint is active at `f`. -/
theorem strictComplementarity_iff (c : ι → H → ℝ) (f : H) (μ : ι → ℝ) :
    StrictComplementarity c f μ ↔ ∀ i, c i f = 0 → 0 < μ i := by
  constructor
  · intro hsc i hi
    -- Convert the textbook equality `c i f = 0` into active-set membership.
    exact hsc i ((ActiveSet.mem_active c f i).2 hi)
  · intro hpos i hi
    -- Rewrite active-set membership back to the defining equality of an active constraint.
    exact hpos i ((ActiveSet.mem_active c f i).1 hi)

/-- Under strict complementarity, every active constraint has a strictly
positive multiplier. -/
theorem pos_of_mem_active {c : ι → H → ℝ} {f : H} {μ : ι → ℝ}
    (hsc : StrictComplementarity c f μ) {i : ι}
    (hi : i ∈ ActiveSet.active c f) :
    0 < μ i := by
  -- This is the defining projection of strict complementarity at the active index `i`.
  exact hsc i hi

end KKT
