/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 4.1.15 lies in the diagonal cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticDualDomain` in `Definition_4_1_14`, the chapter owner of `dom ψ`;
* `cubicRegularizedQuadraticScalarDualDomain_eq` in `Definition_4_1_14`, the canonical bridge
  from `dom ψ` to bounded-below shifted quadratics;
* `quadraticObjective` in `Chap01/Definition_1_9_1`, the owner of the shifted quadratic
  `q_λ`;
* `sInf (Set.range Hdiag)`, the canonical order-theoretic owner of the minimum value of the
  finite diagonal family;
* `Finset.filter` on `Finset.univ`, the canonical finite-index realization of the active set `I*`.

Best owner abstraction:
* source-facing: the diagonal invariants `H_min`, `I*`, and `G²`;
* core/canonical: `cubicRegularizedQuadraticDualDomain` together with
  `cubicRegularizedQuadraticScalarDualDomain_eq`;
* bridge/view: specialize the generic dual-domain owner to `H = Matrix.diagonal Hdiag`.

Primitive data:
* the diagonal data `Hdiag`;
* the active gradient coordinates of `g` on the minimal-index set.

Derived API:
* `cubicRegularizedDiagonalMinimum Hdiag`;
* `cubicRegularizedMinimalDiagonalIndices Hdiag`;
* `cubicRegularizedMinimalDiagonalGradientSquare g Hdiag`;
* the diagonal specialization of the existing owner `cubicRegularizedQuadraticDualDomain`.

This file therefore keeps the source-facing diagonal invariants, but deletes the duplicate local
`dom ψ` owner and reuses the chapter owner `cubicRegularizedQuadraticDualDomain` for the diagonal
case. -/

/-- The minimal diagonal entry `H_min` of a diagonal matrix with entries `Hdiag`, realized as the
infimum of the finite diagonal value set. -/
def cubicRegularizedDiagonalMinimum (Hdiag : Fin n → ℝ) : ℝ :=
  sInf (Set.range Hdiag)

/-- The finite index set `I* = { i | H_i = H_min }` of minimal diagonal entries. -/
def cubicRegularizedMinimalDiagonalIndices (Hdiag : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ Hdiag i = cubicRegularizedDiagonalMinimum Hdiag)

/-- The squared gradient mass `G² = ∑_{i ∈ I*} (g^(i))²` on the minimal diagonal indices. -/
def cubicRegularizedMinimalDiagonalGradientSquare (g : E) (Hdiag : Fin n → ℝ) : ℝ :=
  Finset.sum (cubicRegularizedMinimalDiagonalIndices Hdiag) (fun i ↦ (g i) ^ (2 : ℕ))

namespace CubicRegularizedDiagonalInvariants

scoped notation:max "H_min[" Hdiag "]" =>
  cubicRegularizedDiagonalMinimum Hdiag

scoped notation:max "I*[" Hdiag "]" =>
  cubicRegularizedMinimalDiagonalIndices Hdiag

scoped notation:max "G²[" g ";" Hdiag "]" =>
  cubicRegularizedMinimalDiagonalGradientSquare g Hdiag

end CubicRegularizedDiagonalInvariants

open scoped CubicRegularizedDiagonalInvariants

/- Definition 4.1.15's domain `dom ψ` is the existing owner
`cubicRegularizedQuadraticDualDomain`; in the diagonal case, the bounded-below characterization of
`q_λ` is the existing bridge theorem `cubicRegularizedQuadraticScalarDualDomain_eq`. -/
recall cubicRegularizedQuadraticDualDomain

/- The bounded-below characterization of the diagonal `dom ψ` is the existing theorem
`cubicRegularizedQuadraticScalarDualDomain_eq`, specialized to `H = Matrix.diagonal Hdiag`. -/
recall cubicRegularizedQuadraticScalarDualDomain_eq

-- Proof sketch: unfold `cubicRegularizedMinimalDiagonalIndices`; membership in the filtered
-- finite set is exactly the defining equality `H_i = H_min`.
/-- An index lies in `I*[Hdiag]` exactly when its diagonal entry equals `H_min[Hdiag]`. -/
theorem mem_cubicRegularizedMinimalDiagonalIndices_iff
    (Hdiag : Fin n → ℝ) (i : Fin n) :
    i ∈ I*[Hdiag] ↔ Hdiag i = H_min[Hdiag] := by
  simp [cubicRegularizedMinimalDiagonalIndices]
