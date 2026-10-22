/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.PiL2

section Chapter08Theorem8217

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * primary domain: convex-analysis extremum theory on a feasible set;
-- * inspected canonical owners:
--   `IsMinOn.of_isLocalMinOn_of_convexOn`,
--   `ConvexOn.convex_le`,
--   `StrictConvexOn.eq_of_isMinOn`;
-- * source/core/bridge triage:
--   the local-to-global item is a recall of the core owner
--   `IsMinOn.of_isLocalMinOn_of_convexOn`,
--   while the convexity of the feasible minimizer set is the source-facing bridge/view theorem
--   derived from `ConvexOn`.

/- Chapter08 Theorem 8.2.17 (1): each local minimizer of a convex programming problem is a
global minimizer on the feasible set.

This item is an exact `Point = ℝ^n` specialization of the canonical mathlib owner
`IsMinOn.of_isLocalMinOn_of_convexOn`, so it stays at the recall layer instead of re-owning a
parallel theorem name. -/
#check
  (fun {S : Set Point} {f : Point → ℝ} {xStar : Point} (hxStar : xStar ∈ S)
      (h_localMin : IsLocalMinOn f S xStar) (hf_convex : ConvexOn ℝ S f) ↦
    IsMinOn.of_isLocalMinOn_of_convexOn hxStar h_localMin hf_convex)

/-- Chapter08 Theorem 8.2.17 (2): for a convex programming problem, the set of feasible global
minimizers is convex. -/
theorem convex_setOf_globalMinimizers_of_convexProgramming
    (S : Set Point) (f : Point → ℝ)
    (hf_convex : ConvexOn ℝ S f) :
    Convex ℝ
      {x : Point |
        x ∈ S ∧ IsMinOn f S x} := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨hxS, hxMin⟩
  rcases hy with ⟨hyS, hyMin⟩
  refine ⟨hf_convex.1 hxS hyS ha hb hab, ?_⟩
  intro z hz
  calc
    f (a • x + b • y) ≤ a • f x + b • f y := hf_convex.2 hxS hyS ha hb hab
    _ ≤ a • f z + b • f z := by
      gcongr
      · exact hxMin hz
      · exact hyMin hz
    _ = f z := by rw [← add_smul, hab, one_smul]

end Chapter08Theorem8217
