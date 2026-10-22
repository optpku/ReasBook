/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall hits verified for this item: `Convex.interior` and `Convex.closure`.

section Theorem135

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter01 Theorem 1.3.5: if `S ⊆ ℝ^n` is convex, then both `interior S` and `closure S`
are convex.

Primary domain: convex subsets of topological vector spaces.
Core/canonical owner: `Convex ℝ S`.
Primitive data: the convexity proof `hS`.
Derived API: `hS.interior` and `hS.closure`.

This item is therefore a direct canonical recall of mathlib's owner lemmas
`Convex.interior` and `Convex.closure`, specialized here to `Point = ℝ^n`.
-/

#check fun {S : Set Point} (hS : Convex ℝ S) ↦ hS.interior
#check fun {S : Set Point} (hS : Convex ℝ S) ↦ hS.closure

end Theorem135
