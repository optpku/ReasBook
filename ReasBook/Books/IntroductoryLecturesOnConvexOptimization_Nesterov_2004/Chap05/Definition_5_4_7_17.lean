/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators StandardSimplex
open EuclideanSpace (positiveOrthant)

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Xₙ" => positiveOrthant n

/- Definition 5.4.7.17 lies in the Chapter 5 simplex-monomial / positive-orthant domain.

Sampled owner declarations:
* `stdSimplex`, the canonical owner of the exponent simplex `Δₙ`;
* `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` from
  `Chap01/Definition_1_10_2`, the chapter owner and membership bridge for the strict positive
  orthant `ℝⁿ₊₊`;
* `relativeDirection` together with the notation `δ[x](h)` from `Definition_5_4_7_14`, the
  nearby owner-level pattern for source-facing orthant objects in this subsection.

Best owner abstraction:
* source-facing: the simplex monomial `ξ_a`, written in Lean as `ξ_[a]`;
* core/canonical: `stdSimplex ℝ (Fin n)` for the exponent vector and `positiveOrthant n` for the
  domain;
* bridge/view: the ambient monomial `ambientMonomialXi a : Eₙ → ℝ`, whose restriction to
  `positiveOrthant n` is the source-facing owner `ξ_[a]`.

Primitive data:
* the simplex exponent `a : Δ[n]`.

Derived API:
* the ambient monomial on `ℝⁿ`;
* the source-facing monomial owner `ξ_[a]` on the canonical positive orthant;
* the evaluation lemmas relating the ambient and restricted views.

The previous file used a raw subtype presentation of the strict orthant. This refinement keeps the
same mathematical object but reuses the chapter owner `positiveOrthant n` for the domain, adds the
textbook notation `ξ_[a]`, and exposes the ambient `ℝⁿ` bridge needed by the nearby derivative
API. -/

/-- The ambient monomial `x ↦ x^a = ∏ i, (x^(i))^(a^(i))` on `ℝⁿ`. Its restriction to the
strict positive orthant is the source-facing owner `ξ_[a]`. -/
def ambientMonomialXi (a : Δ[n]) : Eₙ → ℝ :=
  fun x ↦ ∏ i : Fin n, Real.rpow (x i) (a i)

/-- Definition 5.4.7.17: for a simplex vector `a ∈ Δₙ`, `monomialXi a` is the monomial
`ξ_a(x) = x^a = ∏_{i=1}^n (x^(i))^(a^(i))` on the strict positive orthant `\mathbb{R}^n_{++}`. -/
def monomialXi (a : Δ[n]) : Xₙ → ℝ :=
  fun x ↦ ambientMonomialXi a x

namespace MonomialXi

/- Source-facing Lean notation for the textbook simplex monomial `ξ_a`. -/
scoped notation:max "ξ_[" a:arg "]" => monomialXi a

end MonomialXi

open scoped MonomialXi

/-- Evaluating the ambient monomial at `x : ℝⁿ` gives the coordinate product formula
`∏ i, (x^(i))^(a^(i))`. -/
@[simp] theorem ambientMonomialXi_apply
    (a : Δ[n])
    (x : Eₙ) :
    ambientMonomialXi a x = ∏ i : Fin n, Real.rpow (x i) (a i) :=
  rfl

-- Proof sketch: unfold `monomialXi`; its value is definitionally the finite product of the
-- coordinatewise real powers prescribed by the exponent vector `a`.
/-- Evaluating `ξ_[a]` at a positive vector `x` gives the textbook formula
`∏_{i=1}^n (x^(i))^(a^(i))`. -/
@[simp] theorem monomialXi_apply
    (a : Δ[n])
    (x : Xₙ) :
    ξ_[a] x = ∏ i : Fin n, Real.rpow ((x : Eₙ) i) (a i) :=
  rfl

/-- Restricting the ambient monomial to the strict positive orthant recovers the source-facing
owner `ξ_[a]`. -/
@[simp] theorem ambientMonomialXi_eq_monomialXi
    (a : Δ[n])
    (x : Xₙ) :
    ambientMonomialXi a x = ξ_[a] x :=
  rfl

end
