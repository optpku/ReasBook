/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [PseudoMetricSpace X]
variable {C : Set X} {x : ℕ → X}

/-- Definition 5.1: a sequence `x : ℕ → X` is Fejer monotone with respect to `C` if for every
`c ∈ C` the distances `dist (x n) c` do not increase from one step to the next. In a seminormed
additive group this is the textbook inequality `‖x n - c‖`. -/
def FejerMonotone (C : Set X) (x : ℕ → X) : Prop :=
  ∀ c ∈ C, ∀ n : ℕ, dist (x (n + 1)) c ≤ dist (x n) c

-- Proof sketch: unfold `FejerMonotone` and specialize the defining inequality at the chosen
-- point `c ∈ C` and index `n`.
/-- A Fejer-monotone sequence satisfies the defining one-step distance inequality at each point of
`C`. -/
theorem FejerMonotone.step (h : FejerMonotone C x) (c : X) (hc : c ∈ C) (n : ℕ) :
    dist (x (n + 1)) c ≤ dist (x n) c :=
  h c hc n

end
