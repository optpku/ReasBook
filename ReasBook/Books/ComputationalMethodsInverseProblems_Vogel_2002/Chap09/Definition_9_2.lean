/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Operations

public section

/-
Definition 9.2. For a feasible point `f`, the active indices are formalized by
`ActiveSet.active c f = {i | c i f = 0}` and the inactive indices by
`ActiveSet.inactive c f = {i | 0 < c i f}`. The source complement statement is
recorded by `ActiveSet.inactive_eq_compl_active` under the explicit
pointwise-feasibility hypothesis `∀ i, 0 ≤ c i f`.
-/
namespace ActiveSet

universe u v

variable {H : Type u} {ι : Type v}

/-- The active set of `c` at `f` consists of the indices where the constraint
value vanishes. -/
def active (c : ι → H → ℝ) (f : H) : Set ι :=
  {i | c i f = 0}

/-- Membership in `active c f` is equivalent to vanishing of the corresponding
constraint value at `f`. -/
theorem mem_active (c : ι → H → ℝ) (f : H) (i : ι) :
    i ∈ active c f ↔ c i f = 0 := by
  -- Unfolding the set-builder reduces active-set membership to the defining equality.
  rfl

/-- The inactive set of `c` at `f` consists of the indices where the constraint
value is strictly positive. -/
def inactive (c : ι → H → ℝ) (f : H) : Set ι :=
  {i | 0 < c i f}

/-- Membership in `inactive c f` is equivalent to strict positivity of the
corresponding constraint value at `f`. -/
theorem mem_inactive (c : ι → H → ℝ) (f : H) (i : ι) :
    i ∈ inactive c f ↔ 0 < c i f := by
  -- Unfolding the set-builder reduces inactive-set membership to the defining inequality.
  rfl

/-- Definition 9.2: under pointwise feasibility, the inactive indices are
exactly the complement of the active indices. -/
theorem inactive_eq_compl_active (c : ι → H → ℝ) (f : H)
    (hfeas : ∀ i, 0 ≤ c i f) :
    inactive c f = (active c f)ᶜ := by
  ext i
  constructor
  · intro hi
    -- A strictly positive constraint value cannot vanish, so the index is outside the active set.
    rw [mem_inactive] at hi
    rw [Set.mem_compl_iff, mem_active]
    exact ne_of_gt hi
  · intro hi
    -- Feasibility upgrades nonvanishing to strict positivity, so the index is inactive.
    rw [Set.mem_compl_iff, mem_active] at hi
    rw [mem_inactive]
    exact lt_of_le_of_ne (hfeas i) (by simpa [eq_comm] using hi)

end ActiveSet

#check ActiveSet.active

/-
Companion source-facing checks for the inactive-index owner and the feasible-point
complement relation from Definition 9.2.
-/
#check ActiveSet.inactive
#check ActiveSet.inactive_eq_compl_active
