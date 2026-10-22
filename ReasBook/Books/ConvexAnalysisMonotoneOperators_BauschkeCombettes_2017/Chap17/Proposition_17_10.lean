/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfStrictlyConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The strict first-order lower-support inequality on the effective domain associated to a
Gâteaux derivative field `DT`. -/
def StrictGateauxSupportInequalityOn
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ) : Prop :=
  ∀ x ∈ effectiveDomain f, ∀ y ∈ effectiveDomain f, x ≠ y →
    DT y (x - y) + (f y : EReal).toReal < (f x : EReal).toReal

/-- The strict lower-support inequality implies the non-strict support inequality from
Proposition 17.7. -/
theorem StrictGateauxSupportInequalityOn.toGateauxSupportInequalityOn
    {f : H → Set.Ioi (⊥ : EReal)} {DT : H → H →L[ℝ] ℝ}
    (hstrict : StrictGateauxSupportInequalityOn f DT) :
    GateauxSupportInequalityOn f DT := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp
  · exact (hstrict x hx y hy hxy).le

/-- The derivative field `DT` is strictly monotone on `U` when every distinct pair of points of
`U` has strictly positive monotonicity pairing. -/
def StrictGateauxDerivativeMonotoneOn
    (DT : H → H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ≠ y → 0 < (DT x - DT y) (x - y)

/-- Strict monotonicity implies the non-strict monotonicity predicate from Proposition 17.7. -/
theorem StrictGateauxDerivativeMonotoneOn.toGateauxDerivativeMonotoneOn
    {DT : H → H →L[ℝ] ℝ} {U : Set H}
    (hstrict : StrictGateauxDerivativeMonotoneOn DT U) :
    GateauxDerivativeMonotoneOn DT U := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst hxy
    simp
  · exact (hstrict x hx y hy hxy).le

/-- The second derivative field `A₂` is positive on `U` when each of its quadratic forms is
strictly positive on every nonzero direction at every point of `U`. -/
def GateauxSecondDerivativePositiveOn
    (A₂ : H → H →L[ℝ] H →L[ℝ] ℝ) (U : Set H) : Prop :=
  ∀ x ∈ U, ∀ z : H, z ≠ 0 → 0 < A₂ x z z

/-- Strict positivity of the quadratic forms implies the non-strict nonnegativity predicate from
Proposition 17.7. -/
theorem GateauxSecondDerivativePositiveOn.toGateauxSecondDerivativeNonnegativeOn
    {A₂ : H → H →L[ℝ] H →L[ℝ] ℝ} {U : Set H}
    (hpositive : GateauxSecondDerivativePositiveOn A₂ U) :
    GateauxSecondDerivativeNonnegativeOn A₂ U := by
  intro x hx z
  by_cases hz : z = 0
  · subst hz
    simp
  · exact (hpositive x hx z hz).le

-- Proof sketch: unfold `GateauxSecondDerivativePositiveOn`; this is exactly the pointwise
-- strict positivity of the quadratic forms defined by `A₂` on nonzero directions.
/-- Unfolding `GateauxSecondDerivativePositiveOn` gives the strict positivity of the quadratic form
associated to the second derivative field on nonzero directions. -/
theorem gateauxSecondDerivativePositiveOn_iff
    {A₂ : H → H →L[ℝ] H →L[ℝ] ℝ} {U : Set H} :
    GateauxSecondDerivativePositiveOn A₂ U ↔
      ∀ x ∈ U, ∀ z : H, z ≠ 0 → 0 < A₂ x z z :=
  Iff.rfl

-- Proof sketch: identify clause (ii) with the strict first-order support inequality attached to
-- the Gâteaux derivative field `DT`, and identify clause (iii) with strict monotonicity of `DT`.
-- The equivalence between strict convexity and these first-order conditions is then obtained by
-- the standard segment argument on the open convex effective domain. For the final implication,
-- integrate the positive second-directional quadratic form along line segments to obtain strict
-- monotonicity of `DT`, which feeds back into the preceding equivalence.
/-- Proposition 17.10: on an open convex effective domain, strict convexity of `f` is equivalent
to the strict first-order lower-support inequality and to strict monotonicity of a Gâteaux
derivative field for the finite representative `x ↦ (f x : EReal).toReal`; moreover, for any
second Gâteaux derivative field on the effective domain, strict positivity of its quadratic form
implies strict monotonicity and hence these equivalent conditions. -/
theorem strictlyConvex_tfae_of_open_convex_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (DT : H → H →L[ℝ] ℝ)
    (hopen : IsOpen (effectiveDomain f)) (hconv : Convex ℝ (effectiveDomain f))
    (hDT : HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal) DT (effectiveDomain f)) :
    List.TFAE
      [StrictlyConvex f,
          StrictGateauxSupportInequalityOn f DT,
          StrictGateauxDerivativeMonotoneOn DT (effectiveDomain f)] ∧
      (∀ A₂ : H → H →L[ℝ] H →L[ℝ] ℝ,
        HasGateauxDerivativeOn DT A₂ (effectiveDomain f) →
          GateauxSecondDerivativePositiveOn A₂ (effectiveDomain f) →
            StrictGateauxDerivativeMonotoneOn DT (effectiveDomain f)) := sorry

end DifferentiabilityOfStrictlyConvexFunctions

end ERealFunction
