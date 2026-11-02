import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith

open scoped BigOperators

-- Domain-style sampling for this refine pass:
-- * primary domain: one-row Gomory fractional cuts as halfspaces in `Fin n → ℝ`
-- * source-facing owner kept here: `gomory_fractional_cut`
-- * bridge/view owner inspected: the canonical projection surface `Prod.fst '' S`
-- * derived API kept here: the slack-variable projection theorem for equation (5.25)
-- * duplicate slack-set wrapper removed in favor of the canonical projection owner

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this environment, so this file follows the local Chapter 5 cut-as-halfspace
-- pattern used in `ch5_sec5_1_1_lemma_5_4` and `ch5_sec5_2_definition_5_2_extra_1`.

section Definition524Extra1

variable {n : ℕ}

/-- Definition 5.2.4-extra-1. For a tableau row
`x_h + ∑_{j ∈ N} ā_j x_j = b̄` with `f_j = ā_j - ⌊ā_j⌋` and
`f₀ = b̄ - ⌊b̄⌋`, the associated Gomory fractional cut is the halfspace
`∑_{j ∈ N} f_j x_j ≥ f₀`. -/
def gomory_fractional_cut
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ |
    (Int.fract tableauRhs : ℝ) ≤
      Finset.sum N fun j ↦ (Int.fract (tableauCoeff j) : ℝ) * x j}

/-- Membership in `gomory_fractional_cut N tableauCoeff tableauRhs` is exactly the inequality
`f₀ ≤ ∑_{j ∈ N} f_j x_j` built from the fractional parts of the tableau row coefficients and
right-hand side. -/
@[simp]
theorem mem_gomory_fractional_cut_iff
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ)
    (x : Fin n → ℝ) :
    x ∈ gomory_fractional_cut N tableauCoeff tableauRhs ↔
      (Int.fract tableauRhs : ℝ) ≤
        Finset.sum N fun j ↦ (Int.fract (tableauCoeff j) : ℝ) * x j :=
  Iff.rfl

/-- The slack-variable form of equation `(5.25)` is an extended formulation whose projection to
the original variables is exactly the Gomory fractional cut. -/
theorem gomory_fractional_cut_eq_slack_projection
    (N : Finset (Fin n))
    (tableauCoeff : Fin n → ℚ)
    (tableauRhs : ℚ) :
    Prod.fst '' {xs : (Fin n → ℝ) × ℝ |
      (Finset.sum N fun j ↦ -((Int.fract (tableauCoeff j) : ℝ) * xs.1 j)) + xs.2 =
          -(Int.fract tableauRhs : ℝ) ∧
        0 ≤ xs.2} =
      gomory_fractional_cut N tableauCoeff tableauRhs := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨⟨x', s⟩, hs, rfl⟩
    rcases hs with ⟨hs_eq, hs_nonneg⟩
    set cutValue : ℝ :=
      Finset.sum N fun j ↦ (Int.fract (tableauCoeff j) : ℝ) * x' j
    have hs_eq' : -cutValue + s = -(Int.fract tableauRhs : ℝ) := by
      simpa [cutValue] using hs_eq
    rw [mem_gomory_fractional_cut_iff]
    linarith
  · intro x hx
    rw [mem_gomory_fractional_cut_iff] at hx
    set cutValue : ℝ :=
      Finset.sum N fun j ↦ (Int.fract (tableauCoeff j) : ℝ) * x j
    refine ⟨(x, cutValue - (Int.fract tableauRhs : ℝ)), ?_, rfl⟩
    constructor
    · have hneg :
          Finset.sum N (fun j ↦ -((Int.fract (tableauCoeff j) : ℝ) * x j)) = -cutValue := by
        simp [cutValue]
      linarith
    · simpa [cutValue] using hx

end Definition524Extra1
