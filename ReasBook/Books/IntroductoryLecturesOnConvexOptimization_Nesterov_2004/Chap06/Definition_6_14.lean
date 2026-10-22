/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

/- Definition 6.14 lies in the finite simplex / entropic prox-geometry domain.

Sampled owner declarations:
* project `EuclideanSpace.l1Seminorm`, the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`;
* project `EuclideanSpace.l1Seminorm_apply`, the coordinate formula for that owner;
* project `entropyFunction`, the canonical entropy owner on `Fin n → ℝ`;
* project `entropyFunction_apply`, the coordinate expansion of that owner.

Best owner abstraction:
* source-facing: the normalized entropy prox-function on the simplex `Δ[n]`;
* core/canonical: `EuclideanSpace.l1Seminorm` for the ambient geometry and `entropyFunction` for
  the entropy term;
* bridge/view: restricting `x ↦ log n + entropyFunction n x` to the simplex subtype `Δ[n]`.

Primitive data:
* the positive dimension `n : ℕ+`.

Derived API:
* the pointwise formula for the normalized entropy prox-function on `Δ[n]`;
* the textbook use of `EuclideanSpace.l1Seminorm (n : ℕ)` and
  `EuclideanSpace.l1Seminorm (m : ℕ)` as the ambient norms on `ℝⁿ` and `ℝᵐ`.

Source/core/bridge triage:
* source-facing: `normalizedEntropyProxFunction`;
* core/canonical: `EuclideanSpace.l1Seminorm` and `entropyFunction`;
* bridge/view: this file, which keeps the simplex-subtype prox function but deletes the duplicate
  bundled prox-structure wrapper.
-/

/-- The normalized entropy prox-function from Definition 6.14 is
`x ↦ log n + ∑ᵢ xᵢ log xᵢ` on the standard simplex `Δ_n`; the same owner specializes to the
textbook pair `(d₁, d₂)` by using the dimensions `n` and `m`. -/
def normalizedEntropyProxFunction (n : ℕ+) : Δ[n] → ℝ :=
  fun x ↦ Real.log (n : ℝ) + entropyFunction (n : ℕ) x

/-- The ambient norm from Definition 6.14 is the canonical coordinate `ℓ₁` seminorm on `ℝⁿ`,
written in textbook form as the sum of the coordinate absolute values. -/
-- Proof sketch: specialize `EuclideanSpace.l1Seminorm_apply` to real coordinates and rewrite
-- `‖x i‖` as `|x i|`.
theorem l1Seminorm_eq_sum_abs (n : ℕ+) (x : EuclideanSpace ℝ (Fin (n : ℕ))) :
    EuclideanSpace.l1Seminorm (n : ℕ) x = ∑ i : Fin (n : ℕ), |x i| := by
  -- Move from the owner seminorm formula to the textbook absolute-value surface.
  simpa [Real.norm_eq_abs] using EuclideanSpace.l1Seminorm_apply (n := (n : ℕ)) x

/-- Definition 6.14: evaluating `normalizedEntropyProxFunction n` gives the textbook formula
`log n + ∑ᵢ xᵢ log xᵢ` on `Δ_n`. -/
-- Proof sketch: unfold `normalizedEntropyProxFunction` and then expand `entropyFunction`
-- coordinatewise using `entropyFunction_apply`.
theorem normalizedEntropyProxFunction_apply (n : ℕ+) (x : Δ[n]) :
    normalizedEntropyProxFunction n x =
      Real.log (n : ℝ) + ∑ i : Fin (n : ℕ), x i * Real.log (x i) := by
  -- Expand the simplex bridge definition and then rewrite the entropy owner coordinatewise.
  rw [normalizedEntropyProxFunction, entropyFunction_apply]
