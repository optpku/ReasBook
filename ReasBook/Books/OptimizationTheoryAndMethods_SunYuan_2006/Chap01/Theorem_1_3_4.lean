/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Pointwise

-- Semantic recall hits verified for this item: `Convex.inter`, `Convex.add`, and `Convex.sub`.

section Theorem134

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter01 Theorem 1.3.4: if `S₁, S₂ ⊆ ℝ^n` are convex, then their intersection, pointwise sum,
and pointwise difference are convex. This item is a canonical recall of mathlib's exact owner
lemmas `Convex.inter`, `Convex.add`, and `Convex.sub`, specialized here to
`Point = EuclideanSpace ℝ (Fin n)`.
-/

#check fun {S₁ S₂ : Set Point} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂) ↦ hS₁.inter hS₂
#check fun {S₁ S₂ : Set Point} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂) ↦ hS₁.add hS₂
#check fun {S₁ S₂ : Set Point} (hS₁ : Convex ℝ S₁) (hS₂ : Convex ℝ S₂) ↦ hS₁.sub hS₂

end Theorem134
