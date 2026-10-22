/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.LocalExtr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_6

noncomputable section

section Chapter14Theorem1417

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualSpace" => StrongDual ℝ X

open scoped ClarkeDifferential Subgradient

-- Domain sampling:
-- * primary domain: convex nonsmooth analysis on real normed spaces
-- * inspected chapter owners in the minimal closure:
--   `clarkeDifferential`,
--   `subdifferential`,
--   `mem_subdifferential_iff`,
--   `clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt`
-- * inspected mathlib minimizer owners:
--   `IsMinOn`,
--   `isMinOn_univ_iff`,
--   `IsMinOn.isLocalMin`
-- * source/core/bridge triage:
--   - source-facing: `isLocalMin_of_zero_mem_clarkeDifferential_of_convexOn`
--   - core/canonical: `subdifferential` together with `IsMinOn`
--   - bridge/view: Lemma 14.1.6 identifies `∂ᶜ f` with `∂ f` under convexity and local
--     Lipschitz regularity
-- * primitive data vs derived API:
--   - primitive data: convexity, local Lipschitz regularity, and the vanishing generalized
--     gradient `0 ∈ (∂ᶜ f) xStar`
--   - derived API: first a global minimizer on `Set.univ`, then the source-facing local
--     minimizer conclusion

/-- Chapter14 Theorem 14.1.7: if `f : X → ℝ` is convex on `Set.univ` and Lipschitz near
`xStar`, and if the zero functional belongs to the Clarke generalized differential
`clarkeDifferential f xStar`, then `xStar` is a local minimizer of `f`. -/
theorem isLocalMin_of_zero_mem_clarkeDifferential_of_convexOn
    (f : X → ℝ)
    (xStar : X)
    (h_convex : ConvexOn ℝ Set.univ f)
    (h_local : LocallyLipschitzAt f xStar)
    (h_zero : (0 : DualSpace) ∈ (∂ᶜ f) xStar) :
    IsLocalMin f xStar := by
  have h_min : IsMinOn f Set.univ xStar := by
    simpa [isMinOn_univ_iff] using
      (mem_subdifferential_iff f xStar 0).1 <| by
        rwa [← clarkeDifferential_eq_subdifferential_of_convexOn_of_locallyLipschitzAt
          f xStar h_convex h_local]
  exact h_min.isLocalMin (by simp)

#print axioms clarkeDifferential

end Chapter14Theorem1417
