/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_57

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ConditionalGradientContraction
open scoped BigOperators WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 6.62 lies in the Chapter 6 accuracy-certificate / estimating-sequence domain.

Sampled owner-style declarations:
- `ConditionalGradientContraction.estimatingFunctionalSequence` in `Theorem_6_14`, the chapter
  owner for affine-linearization estimating families;
- `A[a](t)` in `Definition_6_53`, the chapter owner for accumulated weights;
- `localModelAccuracyCertificate` in `Definition_6_61`, the neighboring source-facing companion
  for the unshifted certificate `ℓ_t`;
- `dualizedLinearEstimatingFunction` in
  `Text_6_4_4_Accuracy_Certificates_Recover_Dual_Information`, the downstream dualized view of
  the same source-facing estimating function.

Best owner abstraction:
- `ConditionalGradientContraction.estimatingFunctionalSequence`, together with the canonical
  accumulated-weight owner `A[a](t)`.

Primitive data:
- the feasible set `Q`;
- the weights `a`;
- the smooth term `f` with a chosen first-order field `gradF`;
- the regularizer `ψ`;
- the iterate sequence `xSeq`.

Derived API:
- the source-facing estimating function `linearEstimatingFunction`;
- the source-facing shifted weights `linearEstimatingWeights`;
- the source-facing denominator `linearEstimatingWeightSum`;
- the source-facing certificate `linearEstimatingAccuracyCertificate`;
- the explicit finite-sum expansion `linearEstimatingFunction_def`.

Source/core/bridge triage:
- source-facing: `linearEstimatingFunction` and `linearEstimatingAccuracyCertificate`;
- bridge/view: `linearEstimatingWeights` and `linearEstimatingWeightSum`;
- core/canonical: `estimatingFunctionalSequence` and `A[a](t)`;
- source-facing denominator formula: `linearEstimatingWeightSum_def`.

The previous version stored the explicit finite sum and an ad hoc denominator map `A` as
primitive public data. This file instead keeps the textbook objects while deriving them from the
existing Chapter 6 owners. -/

namespace LinearEstimatingCertificate

section

variable (Q : Set E) (ψ : Q → ℝ)

private abbrev regularizerExtension : E → ℝ :=
  Function.extend Subtype.val ψ 0

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
@[simp] private theorem regularizerExtension_apply (x : Q) :
    regularizerExtension Q ψ x = ψ x := by
  simp [regularizerExtension]

end

section

variable (a : ℕ → ℝ)

def linearEstimatingWeights : ℕ → ℝ
  | 0 => 0
  | t + 1 => a (t + 1)

/-- The normalization factor in Definition 6.62, written through the chapter owner `A_t` for the
shifted weight sequence `0, a₁, a₂, ...`. -/
def linearEstimatingWeightSum (t : ℕ) : ℝ :=
  A[(linearEstimatingWeights a)](t)

/-- Expanding `linearEstimatingWeightSum a t` gives the source-facing denominator
`\sum_{k < t} a_{k+1}`. -/
theorem linearEstimatingWeightSum_def (t : ℕ) :
    linearEstimatingWeightSum a t = ∑ k ∈ Finset.range t, a (k + 1) := by
  induction t with
  | zero =>
      simp [linearEstimatingWeightSum, accumulatedWeights, linearEstimatingWeights]
  | succ t ih =>
      calc
        linearEstimatingWeightSum a (t + 1) =
            linearEstimatingWeightSum a t + a (t + 1) := by
              simp [linearEstimatingWeightSum, accumulatedWeights, linearEstimatingWeights,
                Finset.sum_range_succ, add_assoc]
        _ = ∑ k ∈ Finset.range t, a (k + 1) + a (t + 1) := by
              rw [ih]
        _ = ∑ k ∈ Finset.range (t + 1), a (k + 1) := by
              rw [Finset.sum_range_succ]

end

section

variable (Q : Set E) (a : ℕ → ℝ) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q)

/-- The linear estimating function `φ_t` from Definition 6.62, expressed as the Chapter 6
estimating-function owner with zero initial weight and the textbook affine increments indexed by
`a_{k+1}`. -/
def linearEstimatingFunction (t : ℕ) : Q → ℝ :=
  fun x ↦
    estimatingFunctionalSequence
      (linearEstimatingWeights a)
      (fun _ ↦ 0)
      f
      (fun y ↦ InnerProductSpace.toDualMap ℝ E (gradF y))
      (regularizerExtension Q ψ)
      (fun k ↦ (xSeq k : E))
      t x

-- Proof sketch: unfold the owner specialization and use the zero initial weight to remove the
-- initial model term.
/-- Expanding `linearEstimatingFunction Q a f gradF ψ xSeq t` gives the finite sum of the affine
models of `f` at `x₀, …, x_{t-1}`, weighted by `a₁, …, a_t`, together with the regularizer
term `ψ(x)`. -/
theorem linearEstimatingFunction_def (t : ℕ) (x : Q) :
    linearEstimatingFunction Q a f gradF ψ xSeq t x =
      Finset.sum (Finset.range t) fun k ↦
        a (k + 1) *
          (f (xSeq k) + inner ℝ (gradF (xSeq k)) ((x : E) - (xSeq k : E)) + ψ x) := by
  induction t with
  | zero =>
      simp [linearEstimatingFunction, estimatingFunctionalSequence, linearEstimatingWeights]
  | succ t ih =>
      change
        estimatingFunctionalSequence
            (linearEstimatingWeights a)
            (fun _ ↦ 0)
            f
            (fun y ↦ InnerProductSpace.toDualMap ℝ E (gradF y))
            (regularizerExtension Q ψ)
            (fun k ↦ (xSeq k : E))
            t x +
          linearEstimatingWeights a (t + 1) *
            (f (xSeq t) +
              (InnerProductSpace.toDualMap ℝ E (gradF (xSeq t))) ((x : E) - (xSeq t : E)) +
              regularizerExtension Q ψ x) =
        ∑ k ∈ Finset.range (t + 1),
          a (k + 1) *
            (f (xSeq k) + inner ℝ (gradF (xSeq k)) ((x : E) - (xSeq k : E)) + ψ x)
      rw [show
        estimatingFunctionalSequence
            (linearEstimatingWeights a)
            (fun _ ↦ 0)
            f
            (fun y ↦ InnerProductSpace.toDualMap ℝ E (gradF y))
            (regularizerExtension Q ψ)
            (fun k ↦ (xSeq k : E))
            t x =
          linearEstimatingFunction Q a f gradF ψ xSeq t x by
        rfl]
      rw [ih, Finset.sum_range_succ]
      simp [linearEstimatingWeights, add_assoc]

/-- Definition 6.62: the accuracy certificate `\hat ℓ_t` is the accumulated-weight-normalized
infimum of the estimating function `φ_t` over `Q`, with source-facing denominator
`\sum_{k < t} a_{k+1}` encoded by `linearEstimatingWeightSum a t = A[linearEstimatingWeights a](t)`.
When the infimum is attained, this recovers the textbook minimum formula
`\hat ℓ_t = (1 / A_t) \min_{x ∈ Q} φ_t(x)`. -/
def linearEstimatingAccuracyCertificate (t : ℕ) : ℝ :=
  sInf (Set.range (linearEstimatingFunction Q a f gradF ψ xSeq t)) /
    linearEstimatingWeightSum a t

-- Proof sketch: unfold `linearEstimatingAccuracyCertificate`.
/-- Expanding `linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t` gives the infimum of the
range of the estimating function `φ_t`, divided by the source-facing denominator
`\sum_{k < t} a_{k+1}`. -/
theorem linearEstimatingAccuracyCertificate_def (t : ℕ) :
    linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t =
      sInf (Set.range (linearEstimatingFunction Q a f gradF ψ xSeq t)) /
        ∑ k ∈ Finset.range t, a (k + 1) := by
  rw [linearEstimatingAccuracyCertificate, linearEstimatingWeightSum_def]

end

end LinearEstimatingCertificate

open LinearEstimatingCertificate

end
