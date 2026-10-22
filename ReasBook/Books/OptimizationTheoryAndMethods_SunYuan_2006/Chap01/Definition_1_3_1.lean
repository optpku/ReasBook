/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item: `Convex`, `convex_iff_add_mem`, and
-- `Convex.lineMap_mem`.

section Definition131

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter01 Definition 1.3.1: for `S : Set Point`, the statement that `S` is convex is
formalized by `Convex ℝ S`.
-/
#check (Convex ℝ : Set Point → Prop)

/-- Weighted-combination characterization of convexity on `ℝ^n`. -/
theorem convex_iff_weightedAdd_mem {S : Set Point} :
    Convex ℝ S ↔
      ∀ ⦃x₁ x₂ : Point⦄, x₁ ∈ S → x₂ ∈ S →
        ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 → α • x₁ + (1 - α) • x₂ ∈ S := by
  constructor
  · intro hS x₁ x₂ hx₁ hx₂ α hα
    simpa [AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      hS.lineMap_mem hx₂ hx₁ hα
  · intro hS
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    have hb_one : b ≤ (1 : ℝ) := by
      calc
        b ≤ b + a := by exact le_add_of_nonneg_right ha
        _ = a + b := by ac_rfl
        _ = 1 := hab
    have hba : 1 - b = a := by
      rw [sub_eq_iff_eq_add]
      simpa using hab.symm
    simpa [hba, add_comm] using hS hy hx ⟨hb, hb_one⟩

end Definition131
