/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The first-order lower-support inequality on the effective domain associated to a Gâteaux
derivative field `DT`. -/
def GateauxSupportInequalityOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ) : Prop :=
  ∀ x ∈ effectiveDomain f, ∀ y ∈ effectiveDomain f,
    DT y (x - y) + (f y : EReal).toReal ≤ (f x : EReal).toReal

/-- The derivative field `DT` is monotone on `U` when every pair of points of `U` has
nonnegative monotonicity pairing. -/
def GateauxDerivativeMonotoneOn
    (DT : H → H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, 0 ≤ (DT x - DT y) (x - y)

/-- The second derivative field `A₂` is nonnegative on `U` when each of its quadratic forms is
nonnegative on every direction at every point of `U`. -/
def GateauxSecondDerivativeNonnegativeOn
    (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ z : H, 0 ≤ A₂ x z z

-- Proof sketch: use the standard segment reduction to a one-variable function on an open interval.
-- The effective-domain nonemptiness hypothesis matches the project owner `ConvexOn`, which stores
-- properness as part of convexity on a set. Proposition 17.6 gives clause (ii) from convexity,
-- adding the two support inequalities yields clause (iii), and monotonicity of the derivative
-- along every segment gives convexity via Proposition 8.14. If a second derivative field is given
-- on the effective domain, then nonnegativity of its quadratic form is equivalent to monotonicity
-- of the first derivative field along line segments, so clause (iv) joins the same TFAE list. The
-- second-derivative field is recorded through the canonical owner `HasGateauxDerivativeOn` applied
-- to `DT`.
/-- Proposition 17.7: on a nonempty open convex effective domain, convexity of `f` is equivalent
to the first-order lower-support inequality and to monotonicity of a Gâteaux derivative field for
the finite representative `x ↦ (f x : EReal).toReal`; moreover, for any second Gâteaux derivative
field on the effective domain, these conditions are also equivalent to nonnegativity of its
quadratic form. -/
theorem convex_tfae_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hdom : (effectiveDomain f).Nonempty) (hopen : IsOpen (effectiveDomain f))
    (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f)) :
    List.TFAE
        [ConvexOn f (effectiveDomain f),
          GateauxSupportInequalityOn f DT,
          GateauxDerivativeMonotoneOn DT (effectiveDomain f)] ∧
      (∀ A₂ : H → H →L[ℝ] H →L[ℝ] ℝ,
        HasGateauxDerivativeOn DT A₂ (effectiveDomain f) →
          List.TFAE
            [ConvexOn f (effectiveDomain f),
              GateauxSupportInequalityOn f DT,
              GateauxDerivativeMonotoneOn DT (effectiveDomain f),
              GateauxSecondDerivativeNonnegativeOn A₂ (effectiveDomain f)]) := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
