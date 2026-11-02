import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Module

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Theorem 3.44 (Helly), stated on the canonical finite-dimensional ambient space. For convex
sets `C₁, …, C_h` in a finite-dimensional vector space `E` over an ordered field `𝕜`, if
`h ≥ finrank 𝕜 E + 1` and the intersection of all `h` sets is empty, then some
`finrank 𝕜 E + 1` of them already have empty intersection. Specializing to `E = 𝕜^d`, and in
particular to `𝕜 = ℝ`, recovers the textbook statement. -/
theorem helly_theorem_empty_subfamily {h : ℕ}
    (F : Fin h → Set E)
    (h_card : finrank 𝕜 E + 1 ≤ h)
    (h_convex : ∀ i, Convex 𝕜 (F i))
    (h_empty : (⋂ i, F i) = ∅) :
    ∃ s : Finset (Fin h), s.card = finrank 𝕜 E + 1 ∧ (⋂ i ∈ s, F i) = ∅ := by
  classical
  by_contra h_subfamily
  have h_inter : ∀ s : Finset (Fin h), s.card = finrank 𝕜 E + 1 → (⋂ i ∈ s, F i).Nonempty := by
    intro s hs
    by_contra hs_empty
    exact h_subfamily ⟨s, hs, Set.not_nonempty_iff_eq_empty.mp hs_empty⟩
  have h_card' : finrank 𝕜 E + 1 ≤ (Finset.univ : Finset (Fin h)).card := by
    simpa using h_card
  have h_nonempty : (⋂ i, F i).Nonempty := by
    simpa using
      (Convex.helly_theorem h_card'
        (fun i _ ↦ h_convex i)
        (fun s _ hs ↦ h_inter s hs))
  exact h_nonempty.ne_empty h_empty
