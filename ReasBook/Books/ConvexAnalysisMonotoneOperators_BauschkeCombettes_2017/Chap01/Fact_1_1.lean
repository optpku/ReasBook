/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Fact 1.1 (Zorn's lemma): if every chain in a preorder has an upper bound, then there exists
a maximal element. -/
theorem fact_1_1 {α : Type u} [Preorder α]
    (h : ∀ c : Set α, IsChain (fun a b : α ↦ a ≤ b) c → BddAbove c) :
    ∃ m : α, IsMax m :=
  zorn_le h
