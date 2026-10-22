/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.Order.LocalExtr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_4

noncomputable section

open scoped ClarkeDirectionalDerivative ClarkeDifferential

section Chapter14Theorem1415

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

local notation "DualSpace" => StrongDual ℝ X

-- Domain sampling:
-- * primary domain: Clarke-stationary necessary conditions for local extrema on real normed spaces
-- * inspected Chapter 14 owners in the minimal closure:
--   `clarkeDifferential`,
--   `IsClarkeStationaryPoint`,
--   `isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential`,
--   `IsLocalExtr.isClarkeStationaryPoint`
-- * inspected mathlib local-extremum owner:
--   `IsLocalExtr`,
--   `IsLocalExtr.elim`,
--   `IsLocalMax.neg`
-- * source/core/bridge triage:
--   - source-facing: `zero_mem_clarkeDifferential_of_isLocalExtr`
--   - core/canonical: `clarkeDifferential` and `IsClarkeStationaryPoint`
--   - bridge/view: local-extremum hypotheses transported to Clarke stationarity
-- * primitive data vs derived API:
--   - primitive data: the canonical local-extremum owner `IsLocalExtr f xStar` and local
--     Lipschitz regularity there
--   - derived API: the zero-functional membership conclusion in `(∂ᶜ f) xStar`

/-- Chapter14 Theorem 14.1.5: if `f` attains a local extremum at `xStar` and `f` is
Lipschitz near `xStar`, then the zero functional belongs to the Clarke differential
`(∂ᶜ f) xStar = ∂ᶜ f(xStar)`. The theorem is stated over the chapter's canonical real normed-space
owners; the textbook `ℝ^n` case is recovered by specializing `X`. -/
theorem zero_mem_clarkeDifferential_of_isLocalExtr
    (f : X → ℝ)
    (xStar : X)
    (h_local : LocallyLipschitzAt f xStar)
    (h_ext : IsLocalExtr f xStar) :
    (0 : DualSpace) ∈ (∂ᶜ f) xStar :=
  isClarkeStationaryPoint_iff_zero_mem_clarkeDifferential.mp
    (h_ext.isClarkeStationaryPoint h_local)

#print axioms clarkeDirectionalDeriv
#print axioms clarkeDifferential

end Chapter14Theorem1415
