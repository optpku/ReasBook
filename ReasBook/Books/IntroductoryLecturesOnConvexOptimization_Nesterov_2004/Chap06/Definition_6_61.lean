/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_57

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ConditionalGradientContraction
open scoped BigOperators Gradient WeightSequenceNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Definition 6.61 lies in the Chapter 6 accuracy-certificate / estimating-sequence domain.

Sampled owner-style declarations:
- `ConditionalGradientContraction.estimatingFunctionalSequence` in `Theorem_6_14`, the chapter
  owner for recursive affine-linearization accumulators;
- `SecondOrderLocalModel.estimatingFunction` in `Theorem_6_16`, the method-level specialization
  of that owner;
- `initialLinearizationGap_eq_linearizedCompositeGap` in `Definition_6_54`, the chapter bridge
  from subtype regularizers to ambient owners via `Function.extend Subtype.val Ψ 0`;
- `linearEstimatingFunction` in `Definition_6_62`, the neighboring finite-sum companion for the
  same affine-increment pattern.

Best owner abstraction:
- core/canonical: `ConditionalGradientContraction.estimatingFunctionalSequence`.

Primitive data:
- the feasible set `Q`;
- the smooth term `f` and regularizer `ψ`;
- the iterate sequence `xSeq`;
- the weight sequence `a`.

Derived API:
- the thin bridge `accuracyCertificateLocalModel`;
- the explicit finite-sum expansion `accuracyCertificateLocalModel_apply`;
- the source-facing certificate `localModelAccuracyCertificate`.

Source/core/bridge triage:
- source-facing: `localModelAccuracyCertificate`;
- core/canonical: `estimatingFunctionalSequence`;
- bridge/view: `accuracyCertificateLocalModel`, obtained by specializing the owner with the
  initial affine model at `x₀`, the shifted iterate sequence `x_{t+1}`, and the canonical
  extension `Function.extend Subtype.val ψ 0`.

This file therefore keeps `ℓ_t` as the source-facing object and reuses the chapter owner directly,
instead of rebuilding a second recursive estimating-function owner on the feasible subtype.
-/

section AccuracyCertificate

variable (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)

private abbrev regularizerExtension : E → ℝ :=
  Function.extend Subtype.val ψ 0

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
@[simp] private theorem regularizerExtension_apply (x : Q) :
    regularizerExtension Q ψ x = ψ x := by
  simp [regularizerExtension]

private def initialAccuracyCertificateModel : E → ℝ :=
  fun x ↦
    f (xSeq 0) +
      inner ℝ (∇ f (xSeq 0)) (x - (xSeq 0 : E)) +
      regularizerExtension Q ψ x

/-- The weighted affine local model whose minimum value defines the accuracy certificate `ℓ_t`,
expressed as the Chapter 6 estimating-function owner specialized to the initial affine model at
`x₀` and the shifted iterate sequence `x_{t+1}`. -/
def accuracyCertificateLocalModel (t : ℕ) : Q → ℝ :=
  fun x ↦
    estimatingFunctionalSequence
      a
      (initialAccuracyCertificateModel Q f ψ xSeq)
      f
      (fun y ↦ InnerProductSpace.toDualMap ℝ E (∇ f y))
      (regularizerExtension Q ψ)
      (fun k ↦ (xSeq (k + 1) : E))
      t x

-- Proof sketch: unfold the owner specialization and use `Finset.sum_range_succ`.
/-- Evaluating `accuracyCertificateLocalModel Q f ψ xSeq a t` at a feasible point `x : Q` gives
the weighted sum of the affine linearizations of `f` at `x_k` plus the regularizer value `ψ(x)`.
-/
theorem accuracyCertificateLocalModel_apply (t : ℕ) (x : Q) :
    accuracyCertificateLocalModel Q f ψ xSeq a t x =
      Finset.sum (Finset.range (t + 1)) fun k ↦
        a k * (f (xSeq k) + inner ℝ (∇ f (xSeq k)) ((x : E) - (xSeq k : E)) + ψ x) := by
  unfold accuracyCertificateLocalModel
  induction t with
  | zero =>
      simp [estimatingFunctionalSequence, initialAccuracyCertificateModel]
  | succ t ih =>
      simp [estimatingFunctionalSequence, ih, Finset.sum_range_succ, add_assoc]

/-- Definition 6.61: the accuracy certificate `ℓ_t` is the accumulated-weight-normalized infimum
of the weighted affine local model over the feasible set `Q`. When the infimum is attained, this
recovers the textbook minimum in equation `(6.u655)`. -/
def localModelAccuracyCertificate (t : ℕ) : ℝ :=
  sInf (Set.range (accuracyCertificateLocalModel Q f ψ xSeq a t)) /
    A[a](t)

-- Proof sketch: unfold `localModelAccuracyCertificate`.
/-- Expanding `localModelAccuracyCertificate Q f ψ xSeq a t` gives the infimum of the weighted
local-model objective over `Q`, divided by the accumulated weight `A_t`. -/
theorem localModelAccuracyCertificate_def (t : ℕ) :
    localModelAccuracyCertificate Q f ψ xSeq a t =
      sInf (Set.range (accuracyCertificateLocalModel Q f ψ xSeq a t)) /
        A[a](t) :=
  rfl

end AccuracyCertificate

end
