/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u v w

section

variable {A : Type u} {B : Type v} {X : Type w}
variable [Preorder A] [Preorder B] [TopologicalSpace X]
variable {x : A → X} {k : B → A} {x₀ : X}

/-- Fact 1.9 in textbook subnet form: a monotone cofinal reindexing preserves the limit of a
convergent net. -/
theorem subnet_tendsto_same_limit_of_monotone_cofinal
    (hx : Tendsto x atTop (nhds x₀)) (hk_mono : Monotone k)
    (hk_cofinal : ∀ a₀ : A, ∃ b₀ : B, ∀ b : B, b₀ ≤ b → a₀ ≤ k b) :
    Tendsto (x ∘ k) atTop (nhds x₀) := by
  simpa [Function.comp] using hx.comp <|
    hk_mono.tendsto_atTop_atTop fun a₀ ↦ by
      rcases hk_cofinal a₀ with ⟨b₀, hb₀⟩
      exact ⟨b₀, hb₀ b₀ le_rfl⟩

end
