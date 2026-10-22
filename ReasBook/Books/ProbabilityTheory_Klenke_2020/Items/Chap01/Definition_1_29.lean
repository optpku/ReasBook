/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} {C : Set (Set Ω)}

namespace MeasureTheory.AddContent

/-- A content on a semiring is finite if it takes a finite value on every member of the semiring. -/
class IsFinite (μ : AddContent ℝ≥0∞ C) : Prop where
  /-- A finite content takes a finite value on every set of the underlying semiring. -/
  lt_top : ∀ ⦃s : Set Ω⦄, s ∈ C → μ s < ⊤

/-- A content on a semiring is finite exactly when it takes a finite value on every semiring
set. -/
theorem isFinite_iff (μ : AddContent ℝ≥0∞ C) :
    IsFinite μ ↔ ∀ s ∈ C, μ s < ⊤ := by
  constructor
  · intro hμ s hs
    exact hμ.lt_top hs
  · intro hμ
    exact ⟨fun s hs ↦ hμ s hs⟩

/-- A content on a semiring is `σ`-finite if the ambient space is covered by a sequence of
semiring sets of finite content. -/
class IsSigmaFinite (μ : AddContent ℝ≥0∞ C) : Prop where
  /-- A σ-finite content admits a countable semiring cover of the ambient space by finite-content
  sets. -/
  exists_covering_sequence :
    ∃ s : ℕ → Set Ω, (∀ n, s n ∈ C) ∧ (⋃ n, s n) = Set.univ ∧ ∀ n, μ (s n) < ⊤

/-- A content on a semiring is `σ`-finite exactly when the space is covered by countably many
semiring sets of finite content. -/
theorem isSigmaFinite_iff (μ : AddContent ℝ≥0∞ C) :
    IsSigmaFinite μ ↔
      ∃ s : ℕ → Set Ω, (∀ n, s n ∈ C) ∧ (⋃ n, s n) = Set.univ ∧ ∀ n, μ (s n) < ⊤ := by
  constructor
  · intro hμ
    exact hμ.exists_covering_sequence
  · rintro ⟨s, hsC, hsUnion, hsFinite⟩
    exact ⟨⟨s, hsC, hsUnion, hsFinite⟩⟩

/-- Definition 1.29: for a content on a semiring, finiteness means pointwise finiteness on the
semiring, while `σ`-finiteness means the ambient space admits a countable cover by semiring sets
of finite content. -/
theorem definition_1_29 (μ : AddContent ℝ≥0∞ C) :
    (IsFinite μ ↔ ∀ s ∈ C, μ s < ⊤) ∧
      (IsSigmaFinite μ ↔
        ∃ s : ℕ → Set Ω, (∀ n, s n ∈ C) ∧ (⋃ n, s n) = Set.univ ∧ ∀ n, μ (s n) < ⊤) :=
  ⟨isFinite_iff μ, isSigmaFinite_iff μ⟩

end MeasureTheory.AddContent
