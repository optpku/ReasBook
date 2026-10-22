/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u v

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {I : Type v} [Finite I]
variable {H : I → Type u}
variable [∀ i, NormedAddCommGroup (H i)]

variable [∀ i, InnerProductSpace ℝ (H i)]

-- Proof sketch: Proposition 16.7 sends every `u ∈ ∂ f(x)` to a family of slice subgradients.
-- Since `hconv.nonempty` and `SubdifferentiableAt f x` imply `x ∈ effectiveDomain f`, Proposition
-- 17.31 (1) makes each slice subdifferential the singleton `{grad i}` and identifies `x i` with
-- an effective-domain point of the `i`-th slice. Thus every subgradient of `f` at `x` must agree
-- coordinatewise with `grad`, hence equal `grad` itself in `lp H 2`; `SubdifferentiableAt f x`
-- supplies the nonemptiness needed to conclude equality with that singleton.
/-- At a subdifferentiability point `x`, if every coordinate slice through `x` has Gâteaux
gradient `grad i`, then the subdifferential of `f` at `x` is the singleton consisting of the
assembled coordinatewise gradient. -/
theorem subdifferential_eq_singleton_of_coordinatewise_hasGateauxDerivativeAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxsub : SubdifferentiableAt f x) (grad : lp H 2)
    (hgrad : ∀ i,
      HasGateauxDerivativeAt
        (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
        (toDualMap ℝ (H i) (grad i)) (x i)) :
    (∂ f) x = ({grad} : Set (lp H 2)) := sorry

variable [∀ i, CompleteSpace (H i)]

-- Proof sketch: the previous theorem identifies `∂ f(x)` with the singleton `{grad}`.
-- Proposition 17.31 (2) then upgrades this singleton subdifferential, together with continuity on
-- the effective domain, to Gâteaux differentiability of `f` at `x` with gradient `grad`. Here
-- continuity is used only for the upgrade from singleton subdifferential to derivative, while
-- Proposition 16.17 (2) supplies the subdifferentiability input required by the preceding
-- singleton-subdifferential theorem.
/-- Proposition 17.34: for a convex function on a finite Hilbert sum, if `x` is a continuity point
on the effective domain and every coordinate slice through `x` is Gâteaux differentiable at `x i`,
then `f` is Gâteaux differentiable at `x` with gradient equal to the assembled family of the slice
gradients. -/
theorem hasGateauxDerivativeAt_of_coordinatewise_hasGateauxDerivativeAt
    {f : lp H 2 → Set.Ioi (⊥ : EReal)} (hconv : ConvexOn f (effectiveDomain f))
    {x : lp H 2} (hxcont : ContinuousAtOnEffectiveDomain f x) (grad : lp H 2)
    (hgrad : ∀ i,
      HasGateauxDerivativeAt
        (fun y ↦ (f (coordinateSlice x i y) : EReal).toReal)
        (toDualMap ℝ (H i) (grad i)) (x i)) :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ (lp H 2) grad) x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
