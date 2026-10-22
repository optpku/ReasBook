/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section BoundednessAndSubdifferentialRegularity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: combine the Chapter 8 local boundedness and local Lipschitz criteria for convex
-- real-valued functions on bounded balls with Proposition 16.17 for subdifferentials and
-- Proposition 14.15 for Fenchel conjugates. The finite-dimensional conclusion then follows from
-- the bounded-set Lipschitz theorem on closed bounded subsets together with the first equivalence.
/-- Proposition 16.20: for a continuous convex real-valued function on a real Hilbert space, the
following are equivalent: boundedness on every bounded subset, Lipschitz continuity on every
bounded subset, global subdifferentiability with bounded subdifferential image on bounded sets, and
supercoercivity of the Fenchel conjugate. -/
theorem continuous_convex_tfae_boundedOnEveryBoundedSet_lipschitzOnEveryBoundedSet_subdifferential_boundedImage_supercoercive_conjugate
    (f : H → ℝ) (hcont : Continuous f) (hconv : _root_.ConvexOn ℝ Set.univ f) :
    List.TFAE
      [∀ B : Set H, Bornology.IsBounded B → Bornology.IsBounded (f '' B),
        ∀ B : Set H, Bornology.IsBounded B → ∃ β : NNReal, LipschitzOnWith β f B,
        (∀ x : H, SubdifferentiableAt f.toEReal x) ∧
          ∀ B : Set H, Bornology.IsBounded B →
            Bornology.IsBounded (SetValuedOperator.image (∂ f.toEReal) B),
        Supercoercive f.toEReal.asEReal∗] := sorry

end BoundednessAndSubdifferentialRegularity

section FiniteDimensionalBoundedness

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

-- Proof sketch: Corollary 8.40 first promotes convexity on `Set.univ` to continuity, so the
-- finite-dimensional conclusion does not need continuity as primitive data. Corollary 8.41 then
-- gives a Lipschitz constant for `f` on the closure of any bounded set, and a Lipschitz map sends
-- bounded sets to bounded sets.
/-- In finite dimension, a convex real-valued function is bounded on every bounded subset of the
ambient real normed space. -/
theorem boundedOnEveryBoundedSet_of_convex_finiteDimensional
    (f : H → ℝ) (hconv : _root_.ConvexOn ℝ Set.univ f) (B : Set H)
    (hB : Bornology.IsBounded B) :
    Bornology.IsBounded (f '' B) := sorry

end FiniteDimensionalBoundedness

end ERealFunction
