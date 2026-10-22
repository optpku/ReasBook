/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u

variable {Ω : Type u}

/-- Definition 1.27: Part (i) of the textbook definition. A set function on `𝒜` is monotone if it
is order-preserving under inclusion of sets in `𝒜`. -/
structure IsMonotoneSetFunction (𝒜 : Set (Set Ω))
    (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal) : Prop where
  /-- The value of a monotone set function does not decrease when the set increases. -/
  mono : ∀ ⦃s t : Subtype (fun u : Set Ω ↦ u ∈ 𝒜)⦄, s.1 ⊆ t.1 → μ s ≤ μ t

/-- A monotone set function on `𝒜` canonically lifts to an `OrderHom` on the subtype of sets
belonging to `𝒜`. -/
instance (𝒜 : Set (Set Ω)) :
    CanLift (Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal)
      (Subtype (fun s : Set Ω ↦ s ∈ 𝒜) →o ENNReal)
      (↑)
      (IsMonotoneSetFunction 𝒜) where
  prf μ hμ := ⟨⟨μ, hμ.mono⟩, rfl⟩

/-- A set function on `𝒜` is additive if it sends every finite disjoint union of sets in `𝒜` whose
union is again in `𝒜` to the corresponding finite sum. This is part (ii) of the textbook
definition. -/
structure IsAdditiveSetFunction (𝒜 : Set (Set Ω))
    (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal) : Prop where
  /-- The value of an additive set function on a finite disjoint union is the finite sum of the
  values on the pieces. -/
  eq_sum : ∀ ⦃n : ℕ⦄ (s : Fin n → Subtype (fun u : Set Ω ↦ u ∈ 𝒜)),
    Pairwise (fun i j ↦ Disjoint (s i).1 (s j).1) →
      ∀ (h_union : (⋃ i, (s i).1) ∈ 𝒜),
        μ ⟨⋃ i, (s i).1, h_union⟩ = ∑ i, μ (s i)

/-- A set function on `𝒜` is `σ`-additive if it sends every countable disjoint union of sets in
`𝒜` whose union is again in `𝒜` to the corresponding series. This is part (iii) of the textbook
definition. -/
structure IsSigmaAdditiveSetFunction (𝒜 : Set (Set Ω))
    (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal) : Prop where
  /-- The value of a `σ`-additive set function on a countable disjoint union is the sum of the
  values on the pieces. -/
  eq_tsum : ∀ (s : ℕ → Subtype (fun u : Set Ω ↦ u ∈ 𝒜)),
    Pairwise (fun i j ↦ Disjoint (s i).1 (s j).1) →
      ∀ (h_union : (⋃ i, (s i).1) ∈ 𝒜),
        μ ⟨⋃ i, (s i).1, h_union⟩ = ∑' i, μ (s i)

/-- A set function on `𝒜` is subadditive if the value of any set in `𝒜` is bounded above by the sum
of the values of finitely many covering sets from `𝒜`. This is part (iv) of the textbook
definition. -/
structure IsSubadditiveSetFunction (𝒜 : Set (Set Ω))
    (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal) : Prop where
  /-- The value of a subadditive set function on a set is bounded by the finite sum of the values
  on any finite cover by sets in `𝒜`. -/
  le_sum : ∀ ⦃n : ℕ⦄ (s : Subtype (fun u : Set Ω ↦ u ∈ 𝒜))
      (cover : Fin n → Subtype (fun u : Set Ω ↦ u ∈ 𝒜)),
    s.1 ⊆ ⋃ i, (cover i).1 → μ s ≤ ∑ i, μ (cover i)

/-- A set function on `𝒜` is `σ`-subadditive if the value of any set in `𝒜` is bounded above by the
sum of the values of any countable cover by sets from `𝒜`. This is part (v) of the textbook
definition. -/
structure IsSigmaSubadditiveSetFunction (𝒜 : Set (Set Ω))
    (μ : Subtype (fun s : Set Ω ↦ s ∈ 𝒜) → ENNReal) : Prop where
  /-- The value of a `σ`-subadditive set function on a set is bounded by the sum of the values on
  any countable cover by sets in `𝒜`. -/
  le_tsum : ∀ (s : Subtype (fun u : Set Ω ↦ u ∈ 𝒜))
      (cover : ℕ → Subtype (fun u : Set Ω ↦ u ∈ 𝒜)),
    s.1 ⊆ ⋃ i, (cover i).1 → μ s ≤ ∑' i, μ (cover i)
