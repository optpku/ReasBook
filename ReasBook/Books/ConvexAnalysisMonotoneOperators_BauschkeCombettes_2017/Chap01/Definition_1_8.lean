/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace ERealFunction

variable {X : Type u}

/-- Definition 1.8: a sequence in the domain of an extended-real-valued function is minimizing
when its function values converge to the infimum of the image of the function. -/
def IsMinimizingSequence (f : X → EReal) (x : ℕ → X) : Prop :=
  (∀ n : ℕ, x n ∈ dom f) ∧ Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f)))

/-- A minimizing sequence takes values in the domain of the function termwise. -/
theorem IsMinimizingSequence.mem_dom {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) (n : ℕ) :
    x n ∈ dom f :=
  hx.1 n

/-- Helper for Definition 1.8: a minimizing sequence has function values strictly below `+∞`
termwise. -/
theorem IsMinimizingSequence.lt_top {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) (n : ℕ) :
    f (x n) < ⊤ := by
  simpa [mem_dom_iff] using hx.mem_dom n

/-- A minimizing sequence has function values converging to the infimum of the image of `f`. -/
theorem IsMinimizingSequence.tendsto {f : X → EReal} {x : ℕ → X}
    (hx : IsMinimizingSequence f x) :
    Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f))) :=
  hx.2

/-- A sequence is minimizing exactly when all of its function values are strictly below `+∞` and
those values converge to the infimum of the image of `f`. -/
theorem isMinimizingSequence_iff_lt_top (f : X → EReal) (x : ℕ → X) :
    IsMinimizingSequence f x ↔
      (∀ n : ℕ, f (x n) < ⊤) ∧ Tendsto (f ∘ x) atTop (nhds (sInf (Set.range f))) := by
  simp [IsMinimizingSequence, mem_dom_iff]

end ERealFunction
