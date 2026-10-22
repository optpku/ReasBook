/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-- Lemma 1.20: if `X` and `Y` are Hausdorff spaces, `T : X → Y` is continuous, and `C ⊆ X` is
compact, then `T(C)` is compact. This is the textbook Hausdorff-space specialization of the
canonical theorem `IsCompact.image`. -/
theorem lemma_1_20
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {C : Set X} {T : X → Y} (hC : IsCompact C) (hT : Continuous T) :
    IsCompact (T '' C) :=
  hC.image hT
