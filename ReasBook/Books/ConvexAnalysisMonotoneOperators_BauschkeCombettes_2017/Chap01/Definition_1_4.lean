/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {X : Type u}

/-- The domain of an extended-real-valued function is the set of points where the value is
strictly less than `+∞`. -/
def dom (f : X → EReal) : Set X := f ⁻¹' Set.Iio ⊤

/-- A point belongs to the domain exactly when the function value is finite above. -/
@[simp]
theorem mem_dom_iff (f : X → EReal) (x : X) :
    x ∈ dom f ↔ f x < ⊤ :=
  Iff.rfl

/-- A point belongs to the domain exactly when the function value is not `+∞`. -/
@[simp]
theorem mem_dom_iff_ne_top (f : X → EReal) (x : X) :
    x ∈ dom f ↔ f x ≠ ⊤ := by
  rw [mem_dom_iff, lt_top_iff_ne_top]

/-- A point lies outside the domain exactly when the function value is `+∞`. -/
@[simp]
theorem not_mem_dom_iff (f : X → EReal) (x : X) :
    x ∉ dom f ↔ f x = ⊤ := by
  rw [mem_dom_iff_ne_top]
  simp

/-- The graph of an extended-real-valued function is the set of pairs `(x, ξ)` with real ordinate
`ξ` equal to the function value at `x`. -/
def graph (f : X → EReal) : Set (X × ℝ) := { p | f p.1 = (p.2 : EReal) }

/-- A real pair belongs to the graph exactly when its second coordinate equals the function
value. -/
@[simp]
theorem mem_graph_iff (f : X → EReal) (x : X) (ξ : ℝ) :
    (x, ξ) ∈ graph f ↔ f x = (ξ : EReal) :=
  Iff.rfl

/-- The epigraph of an extended-real-valued function is the set of pairs `(x, ξ)` with real
ordinate `ξ` lying above the function value at `x`. -/
def epigraph (f : X → EReal) : Set (X × ℝ) := { p | f p.1 ≤ (p.2 : EReal) }

/-- A real pair belongs to the epigraph exactly when its second coordinate majorizes the function
value. -/
@[simp]
theorem mem_epigraph_iff (f : X → EReal) (x : X) (ξ : ℝ) :
    (x, ξ) ∈ epigraph f ↔ f x ≤ (ξ : EReal) :=
  Iff.rfl

/-- The lower level set at height `ξ` is the set of points where the function value is at most
`ξ`. -/
def lowerLevelSet (f : X → EReal) (ξ : ℝ) : Set X := f ⁻¹' Set.Iic (ξ : EReal)

/-- A point belongs to the lower level set at height `ξ` exactly when the function value is at most
`ξ`. -/
@[simp]
theorem mem_lowerLevelSet_iff (f : X → EReal) (ξ : ℝ) (x : X) :
    x ∈ lowerLevelSet f ξ ↔ f x ≤ (ξ : EReal) :=
  Iff.rfl

/-- The strict lower level set at height `ξ` is the set of points where the function value is
strictly less than `ξ`. -/
def strictLowerLevelSet (f : X → EReal) (ξ : ℝ) : Set X := f ⁻¹' Set.Iio (ξ : EReal)

/-- A point belongs to the strict lower level set at height `ξ` exactly when the function value is
strictly less than `ξ`. -/
@[simp]
theorem mem_strictLowerLevelSet_iff (f : X → EReal) (ξ : ℝ) (x : X) :
    x ∈ strictLowerLevelSet f ξ ↔ f x < (ξ : EReal) :=
  Iff.rfl

/-- Definition 1.4: an extended-real-valued function is proper when it never attains `-∞` and its
domain is nonempty. -/
def IsProper (f : X → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (dom f).Nonempty

/-- A function is proper exactly when it never takes the value `-∞` and its domain is nonempty. -/
@[simp]
theorem isProper_iff (f : X → EReal) :
    IsProper f ↔ (∀ x, f x ≠ ⊥) ∧ (dom f).Nonempty :=
  Iff.rfl

/-- A function is proper exactly when `-∞` is not in its range and its domain is nonempty. -/
theorem isProper_iff_bot_notMem_range (f : X → EReal) :
    IsProper f ↔ ⊥ ∉ Set.range f ∧ (dom f).Nonempty := by
  simp [IsProper]

end ERealFunction
