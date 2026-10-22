/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

open scoped BigOperators

-- Proof sketch: identify the fiber of the sum map over `x` with the countable disjoint union of
-- the singleton sets `{(x - y, y)}` indexed by `y : ℤ`, then apply countable additivity of `μ`.
/-- Example 1.99: For the sum map `X : ℤ × ℤ → ℤ`, `(a, b) ↦ a + b`, the pushforward of a measure
`μ` along `X` assigns to the singleton `{x}` the sum of the masses of the points `(x - y, y)`. -/
theorem map_add_int_singleton_eq_tsum (μ : Measure (ℤ × ℤ)) (x : ℤ) :
    μ.map (fun p : ℤ × ℤ ↦ p.1 + p.2) ({x} : Set ℤ) =
      ∑' y : ℤ, μ ({(x - y, y)} : Set (ℤ × ℤ)) := by
  have hx : MeasurableSet ({x} : Set ℤ) := measurableSet_singleton x
  have hpre : (fun p : ℤ × ℤ ↦ p.1 + p.2) ⁻¹' ({x} : Set ℤ) =
      ⋃ y : ℤ, ({(x - y, y)} : Set (ℤ × ℤ)) := by
    ext p
    constructor
    · rintro (hp : p.1 + p.2 = x)
      rcases p with ⟨a, b⟩
      refine Set.mem_iUnion.2 ⟨b, ?_⟩
      ext
      · exact eq_sub_iff_add_eq.mpr (by simpa using hp)
      · rfl
    · intro hp
      rcases Set.mem_iUnion.1 hp with ⟨y, hy⟩
      rcases hy with rfl
      simp
  rw [Measure.map_apply (by fun_prop) hx, hpre]
  refine measure_iUnion ?_ ?_
  · intro i j hij
    simp [hij]
  · intro y
    exact measurableSet_singleton (x - y, y)
