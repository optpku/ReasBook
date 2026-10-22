/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))
variable (hconv : ConvexOn f (effectiveDomain f))

-- Proof sketch: `effectiveDomain f` is nonempty and convex because `f` is convex on its
-- effective domain. Fact 6.14 then gives nonemptiness of the relative interior of this convex set
-- in finite dimension.
/-- Corollary 16.18 (1): clause (i). The relative interior of the effective domain of an
`]-∞,+∞]`-valued function that is convex on its effective domain is nonempty on a
finite-dimensional real Hilbert space. -/
theorem relativeInterior_effectiveDomain_nonempty_of_convexOn
    :
    (ri (effectiveDomain f)).Nonempty := sorry

-- Proof sketch: Corollary 8.41 yields local Lipschitz control, hence continuity of the finite
-- representative of `f`, at every point of `ri (effectiveDomain f)`. Proposition 16.17 then gives
-- a nonempty subdifferential at each such point.
/-- Corollary 16.18 (2): clause (i). Every point in the relative interior of the effective domain
of a function convex on its effective domain is a subdifferentiability point. -/
theorem relativeInterior_effectiveDomain_subset_subdifferentiabilityDomain_of_convexOn
    :
    ri (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := sorry

-- Proof sketch: by clause (i), choose `x ∈ ri (effectiveDomain f)` together with a subgradient
-- `u ∈ ∂ f x`. The defining subgradient inequality then exhibits the affine map
-- `y ↦ ⟪y, u⟫ + ((f x : EReal).toReal - ⟪x, u⟫)` as a continuous affine minorant of `f`.
/-- Corollary 16.18 (3): clause (ii). An `]-∞,+∞]`-valued function convex on its effective domain
on a finite-dimensional real Hilbert space admits a continuous affine minorant. -/
theorem exists_continuousAffineMinorantWithSlope_of_convexOn
    :
    ∃ u : H, HasContinuousAffineMinorantWithSlope f.asEReal u := sorry

end SubdifferentialContinuity

end ERealFunction
