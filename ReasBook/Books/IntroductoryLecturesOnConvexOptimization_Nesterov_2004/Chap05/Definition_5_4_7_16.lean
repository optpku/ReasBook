/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

namespace StandardSimplex

/- Source-facing Lean notation for the textbook standard simplex `Δ_n` in `ℝⁿ`. -/
scoped[StandardSimplex] notation:max "Δ[" n:arg "]" => stdSimplex ℝ (Fin n)

end StandardSimplex

open scoped StandardSimplex

section

variable (n : ℕ)

/- Definition 5.4.7.16 lies in the finite-dimensional simplex / coordinate-vector domain.

Sampled owner declarations:
* mathlib `stdSimplex`, the canonical owner of the standard simplex;
* mathlib `stdSimplex_eq_inter`, the companion decomposition of the same owner into
  nonnegativity and normalization constraints;
* mathlib `Pi.one_apply`, the canonical coordinate formula for the constant-one function;
* `Definition_6_11`, a later project recall of the same simplex owner, reusing the same shared
  notation surface.

Best owner abstraction:
* source-facing: the textbook simplex `Δ_n`, exposed in Lean by the reusable notation `Δ[n]`, and
  the all-ones vector `\bar e_n` in `ℝⁿ`;
* core/canonical: `stdSimplex ℝ (Fin n)` and `(1 : Fin n → ℝ)`;
* bridge/view: the set-builder expansion of `stdSimplex` and the coordinate formula
  `(1 : Fin n → ℝ) i = 1`.

Primitive data:
* the dimension `n`.

Derived API:
* the defining set-builder equation for `Δ[n]`;
* the coordinatewise evaluation fact for the constant-one vector, already owned by
  `Pi.one_apply`.

This item is therefore recall-first. The file keeps no parallel local wrapper such as `barE`:
the all-ones vector is canonically the function `1`, and the simplex is canonically `stdSimplex`,
with the reusable source-facing notation `Δ[n]`.
-/

/- The exported notation `Δ[n]` is the canonical real `Fin n` specialization of the simplex
owner. -/
example : Set (Fin n → ℝ) := Δ[n]

/- Definition 5.4.7.16 recalls the canonical standard simplex owner. -/
recall stdSimplex
    (𝕜 : Type*) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι] :
    Set (ι → 𝕜)

/- Definition 5.4.7.16: in `ℝⁿ`, the standard simplex `Δ_n`, written in Lean as `Δ[n]`, is
definitionally the set of vectors with nonnegative coordinates and coordinate sum equal to `1`. -/
#check
  (show Δ[n] = {x : Fin n → ℝ | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, x i = 1} from rfl)

variable (i : Fin n)

/- The textbook vector `\bar e_n = (1, \dots, 1)^{\mathsf T}` is the canonical constant-one
function in `ℝⁿ`. -/
#check (1 : Fin n → ℝ)

/- Every coordinate of the same vector is `1`, by the canonical owner theorem `Pi.one_apply`. -/
#check (show (1 : Fin n → ℝ) i = 1 from Pi.one_apply i)

end
