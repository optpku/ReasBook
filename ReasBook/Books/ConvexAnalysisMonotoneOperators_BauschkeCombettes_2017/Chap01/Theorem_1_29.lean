/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

/-- Theorem 1.29: a lower semicontinuous extended-real-valued function on a Hausdorff space
attains a minimum on a compact set as soon as that compact set meets the domain of the function.
-/
-- Proof sketch: apply the canonical compact-attainment theorem
-- `LowerSemicontinuousOn.exists_isMinOn` to the restriction of `f` to `C`; the hypothesis
-- `(C ∩ {x | f x < ⊤}).Nonempty` supplies a point of `C`, so the compact set is nonempty.
theorem lowerSemicontinuous_exists_isMinOn_of_isCompact {X : Type u}
    [TopologicalSpace X] [T2Space X] {f : X → EReal} {C : Set X}
    (hf : LowerSemicontinuous f) (hC : IsCompact C)
    (hdom : (C ∩ { x | f x < ⊤ }).Nonempty) :
    ∃ x ∈ C, IsMinOn f C x := by
  obtain ⟨x, hxC, _⟩ := hdom
  exact (hf.lowerSemicontinuousOn C).exists_isMinOn ⟨x, hxC⟩ hC

/-- Theorem 1.29, infimum form: a minimizing point on the compact set realizes the infimum of the
image. -/
-- Proof sketch: obtain a minimizer from
-- `lowerSemicontinuous_exists_isMinOn_of_isCompact`, then identify its value with `sInf (f '' C)`
-- using the GLB characterization of `IsMinOn`.
theorem lowerSemicontinuous_exists_eq_sInf_image_of_isCompact {X : Type u}
    [TopologicalSpace X] [T2Space X] {f : X → EReal} {C : Set X}
    (hf : LowerSemicontinuous f) (hC : IsCompact C)
    (hdom : (C ∩ { x | f x < ⊤ }).Nonempty) :
    ∃ x ∈ C, f x = sInf (f '' C) := by
  obtain ⟨x, hxC, hmin⟩ := lowerSemicontinuous_exists_isMinOn_of_isCompact hf hC hdom
  exact ⟨x, hxC, eq_sInf_image_of_isMinOn hxC hmin⟩

end ERealFunction
