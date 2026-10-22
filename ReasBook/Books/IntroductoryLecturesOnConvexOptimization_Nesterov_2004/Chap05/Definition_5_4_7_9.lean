/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.7.9 lies in the Chapter 5 entropy-epigraph / cone-composition domain.

Sampled owner declarations:
* `powerConeQ1`, `powerConeBarrier`, and `powerConeBarrierParameter` from
  `Definition_5_4_7_1`, the earlier Chapter 5 owners for the orthant `ℝ_+²`, its logarithmic
  barrier, and the parameter `ν = 2`;
* mathlib `ConvexCone.positive`, the canonical owner for the scalar cone `ℝ_+`;
* `sublevelLogBarrier` from `Theorem_5_1_4`, the chapter owner for barriers of affine half-space
  domains of the form `β - f x > 0`;
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the downstream owner that consumes the
  data assembled here in `Definition_5_4_7_8`.

Best owner abstraction:
* reuse the existing orthant/barrier owners `powerConeQ1`, `powerConeBarrier`, and
  `powerConeBarrierParameter`, together with `ConvexCone.positive ℝ ℝ`;
* keep only the entropy-specific map `ξ` and the affine half-space `Q₂` as new source-facing
  data in this file;
* reuse the canonical half-space barrier specialization
  `sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0`.

Primitive data:
* the relative-entropy map `entropyEpigraphRelativeEntropy`;
* the half-space `entropyEpigraphQ2`.

Derived API:
* the textbook quotient formula for `entropyEpigraphRelativeEntropy`;
* the positive-orthant bridge rewriting that formula as a logarithmic difference;
* the membership lemma for `entropyEpigraphQ2`;
* the canonical half-space barrier specialization and its pointwise evaluation.

Source/core/bridge triage:
* source-facing: `entropyEpigraphRelativeEntropy` and `entropyEpigraphQ2`;
* core/canonical: `powerConeQ1`, `powerConeBarrier`, `powerConeBarrierParameter`,
  `ConvexCone.positive ℝ ℝ`, and `sublevelLogBarrier`;
* bridge/view: the coordinate evaluation lemmas below.

This refinement removes the duplicate local orthant, orthant-barrier, scalar-cone, and
half-space-barrier-parameter wrappers. Definition 5.4.7.9 now reuses the existing Chapter 5
owners for those pieces, keeps only the entropy-specific data as new declarations, and takes the
textbook quotient formula as the primitive owner rather than storing the positive-orthant
`log x₁ - log x₂` expansion as data. -/

/- Definition 5.4.7.9 reuses the earlier orthant owner `powerConeQ1 = ℝ_+²`. -/
recall powerConeQ1
recall mem_powerConeQ1_iff

/- Definition 5.4.7.9 reuses the earlier orthant logarithmic barrier and its parameter `ν = 2`. -/
recall powerConeBarrier
recall powerConeBarrier_apply
recall powerConeBarrierParameter
recall powerConeBarrierParameter_eq

/- Definition 5.4.7.9 reuses the canonical positive cone `ConvexCone.positive ℝ ℝ` as the scalar
cone `K = ℝ_+`. -/
set_option linter.hashCommand false in
#check (ConvexCone.positive ℝ ℝ : ConvexCone ℝ ℝ)

set_option linter.hashCommand false in
#check ConvexCone.mem_positive

/-- Definition 5.4.7.9: in the entropy-epigraph composition model, the scalar map
`ξ(x) = -x^(1) [log x^(1) - log x^(2)]` is the relative-entropy term on `ℝ²`. -/
def entropyEpigraphRelativeEntropy : (ℝ × ℝ) → ℝ :=
  fun x ↦ -x.1 * Real.log (x.1 / x.2)

namespace EntropyEpigraph

/- Source-facing Lean notation for the textbook entropy-epigraph map `ξ`. -/
scoped notation:max "ξ" => entropyEpigraphRelativeEntropy

end EntropyEpigraph

open scoped EntropyEpigraph

/-- Evaluating `ξ` at `(x₁, x₂)` gives the textbook formula
`-x^(1) log (x^(1) / x^(2))`. -/
theorem entropyEpigraphRelativeEntropy_apply (x₁ x₂ : ℝ) :
    ξ (x₁, x₂) = -x₁ * Real.log (x₁ / x₂) :=
  rfl

-- Proof sketch: on the strict positive orthant, rewrite the logarithm of the quotient with
-- `Real.log_div`.
/- On the strict positive orthant, `ξ` can be written as
`-x^(1) [log x^(1) - log x^(2)]`. -/
theorem entropyEpigraphRelativeEntropy_eq_neg_mul_log_sub
    {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    ξ (x₁, x₂) = -x₁ * (Real.log x₁ - Real.log x₂) := by
  rw [entropyEpigraphRelativeEntropy_apply, Real.log_div hx₁.ne' hx₂.ne']

/-- The half-space `Q₂ = {(y, z) ∈ ℝ × ℝ : y + z ≥ 0}` used in the entropy-epigraph
composition model. -/
def entropyEpigraphQ2 : Set (ℝ × ℝ) :=
  {yz | 0 ≤ yz.1 + yz.2}

namespace EntropyEpigraph

/- Source-facing Lean notation for the textbook entropy-epigraph half-space `Q₂`. -/
scoped notation:max "Q₂" => entropyEpigraphQ2

end EntropyEpigraph

/-- A pair `(y, z)` belongs to `Q₂` exactly when `y + z ≥ 0`. -/
theorem mem_entropyEpigraphQ2_iff (y z : ℝ) :
    (y, z) ∈ Q₂ ↔ 0 ≤ y + z := by
  simp [entropyEpigraphQ2]

/- Definition 5.4.7.9 reuses the canonical logarithmic barrier specialization for
`Q₂ = {(y, z) : y + z ≥ 0}`. -/
set_option linter.hashCommand false in
#check (sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 : (ℝ × ℝ) → ℝ)

/-- Evaluating the recalled half-space barrier specialization at `(y, z)` gives the textbook
formula `Φ(y, z) = -log (y + z)`. -/
theorem entropyEpigraphQ2_sublevelLogBarrier_apply (y z : ℝ) :
    sublevelLogBarrier (fun yz : ℝ × ℝ ↦ -yz.1 - yz.2) 0 (y, z) = -Real.log (y + z) := by
  rw [sublevelLogBarrier_apply]
  ring_nf

end
