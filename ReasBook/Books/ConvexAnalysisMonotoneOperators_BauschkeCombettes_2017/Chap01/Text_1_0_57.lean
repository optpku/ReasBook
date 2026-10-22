/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

/-- Text 1.0.57: for a topological space `X` and a subset `C ⊆ X`, the extended-real indicator
`ν_C`, equal to `0` on `C` and `+∞` on `Cᶜ`, is lower semicontinuous if and only if `C` is
closed. -/
theorem lowerSemicontinuous_indicator_compl_top_iff_isClosed
    {X : Type u} [TopologicalSpace X] (C : Set X) :
    LowerSemicontinuous (indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ↔ IsClosed C := by
  constructor
  · intro hν
    have hopen :
        IsOpen ((indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ⁻¹' Ioi (0 : EReal)) :=
      hν.isOpen_preimage (0 : EReal)
    have hpreimage :
        ((indicator Cᶜ fun _ : X ↦ (⊤ : EReal)) ⁻¹' Ioi (0 : EReal)) = Cᶜ := by
      ext x
      by_cases hx : x ∈ C
      · simp [hx]
      · simp [hx, EReal.zero_lt_top]
    simpa [hpreimage] using hopen.isClosed_compl
  · intro hC
    simpa using hC.isOpen_compl.lowerSemicontinuous_indicator (show (0 : EReal) ≤ ⊤ by simp)
