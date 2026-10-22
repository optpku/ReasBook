/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_61
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_62
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open LinearEstimatingCertificate
open scoped BigOperators Gradient WeightSequenceNotation

universe u v

variable {E : Type u} {E₂ : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-
Text 6.4.4 lies in the Chapter 6 accuracy-certificate / dual-maximizer bridge domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax` in `Theorem_6_1`, the Chapter 6
  owners of the zero-smoothed max-representation `f x = max_{u ∈ Q_d} (⟪A x, u⟫ - g(u))`;
- `smoothedPrimalObjectiveArgmax.value_eq` in `Theorem_6_1`, the owner bridge from argmax
  membership to the selected dual value;
- `accuracyCertificateLocalModel` / `localModelAccuracyCertificate` in `Definition_6_61`;
- `linearEstimatingFunction` / `linearEstimatingAccuracyCertificate` in `Definition_6_62`.

Best owner abstraction:
- source-facing: Text 6.4.4's statement that the Chapter 6 certificates recover explicit dual
  values attached to a canonical maximizer selection;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `accuracyCertificateLocalModel`, and `linearEstimatingFunction`;
- bridge/view: the recovered dual gradient `A^* u(x)` and the resulting explicit finite-sum
  formulas.

Primitive data:
- the feasible set `Q`, regularizer `ψ`, iterate sequence `xSeq`, and weights `a`;
- the dual data `A`, `Qd`, `g`, and the selected maximizer field `u`;
- the owner-level max-representation hypotheses
  `f x = smoothedPrimalObjective A Qd 0 g 0 0 x` and
  `u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x`;
- the recovered first-order identities
  `InnerProductSpace.toDualMap ℝ E (gradF x) = A.flip (u x)` and
  `InnerProductSpace.toDualMap ℝ E (∇ f x) = A.flip (u x)`.

Derived API:
- the pointwise value bridge `f x = (A x) (u x) - g (u x)`;
- the certificate equalities written directly on the Chapter 6 owner surface.

The previous version duplicated the source-facing conclusion through free-form rewrite hypotheses
and public wrapper functions for explicit sums. This refinement keeps the explicit sums only as
theorem conclusions, and anchors the public API in the canonical Chapter 6 max-representation and
argmax owners, with the recovered dual information expressed through the owner-level identity
`InnerProductSpace.toDualMap ℝ E (...) = A.flip (u x)`.
-/

section DualRecovery

variable (f : E → ℝ) (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂)
  (g : E₂ → ℝ) (u : E → E₂)

variable
  (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
  (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)

/-- If `f` is presented through the Chapter 6 zero-smoothed max-representation owner and `u x`
lies in the canonical argmax set, then `u x` realizes the selected dual value of `f` at `x`. -/
theorem objective_eq_selectedDualValue
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (x : E) :
    f x = A x (u x) - g (u x) := by
  rw [hobj x, smoothedPrimalObjectiveArgmax.value_eq (hu x)]
  simp [smoothedPrimalObjectiveMaximand]

/-- If the gradient of `f` at `x₀` is the recovered dual gradient `A^* u(x₀)`, then the affine
linearization of `f` at `x₀` equals the selected dual value evaluated at the comparison point
`y`. -/
theorem affineLinearization_eq_selectedDualValue
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (x₀ y gradx : E)
    (hgradx : InnerProductSpace.toDualMap ℝ E gradx = A.flip (u x₀)) :
    f x₀ + inner ℝ gradx (y - x₀) = A y (u x₀) - g (u x₀) := by
  have hvalue := objective_eq_selectedDualValue f A Qd g u hobj hu x₀
  have hpair :
      inner ℝ gradx (y - x₀) = A (y - x₀) (u x₀) := by
    calc
      inner ℝ gradx (y - x₀)
          = (InnerProductSpace.toDualMap ℝ E gradx) (y - x₀) := by
              rw [InnerProductSpace.toDualMap_apply_apply]
      _ = A (y - x₀) (u x₀) := by
            rw [hgradx, ContinuousLinearMap.flip_apply]
  have hlin : A (y - x₀) (u x₀) = A y (u x₀) - A x₀ (u x₀) := by
    simp
  calc
    f x₀ + inner ℝ gradx (y - x₀)
        = (A x₀ (u x₀) - g (u x₀)) + A (y - x₀) (u x₀) := by
          rw [hvalue, hpair]
    _ = (A x₀ (u x₀) - g (u x₀)) + (A y (u x₀) - A x₀ (u x₀)) := by
          rw [hlin]
    _ = A y (u x₀) - g (u x₀) := by
          ring

end DualRecovery

/-- Under the canonical zero-smoothed max-representation assumptions, the Chapter 6 estimating
function built from the recovered dual gradient `A^* u(x)` is exactly the explicit finite sum of
selected dual values. -/
theorem linearEstimatingFunction_eq_selectedDualValueSum
    (Q : Set E) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂) (g : E₂ → ℝ) (u : E → E₂) (t : ℕ)
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (hgradF : ∀ x : E, InnerProductSpace.toDualMap ℝ E (gradF x) = A.flip (u x)) :
    linearEstimatingFunction Q a f gradF ψ xSeq t =
      fun x : Q ↦
        Finset.sum (Finset.range t) fun k ↦
          a (k + 1) * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x) := by
  funext x
  rw [linearEstimatingFunction_def]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hlinear :=
    affineLinearization_eq_selectedDualValue
      f A Qd g u hobj hu (xSeq k) x (gradF (xSeq k)) (hgradF (xSeq k))
  simpa using congrArg (fun r : ℝ ↦ a (k + 1) * (r + ψ x)) hlinear

/-- The Chapter 6 certificate `\hat ℓ_t` equals the normalized infimum of the explicit selected
dual-value sum attached to the canonical maximizer field `u`. -/
theorem linearEstimatingAccuracyCertificate_eq_selectedDualValue
    (Q : Set E) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂) (g : E₂ → ℝ) (u : E → E₂) (t : ℕ)
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (hgradF : ∀ x : E, InnerProductSpace.toDualMap ℝ E (gradF x) = A.flip (u x)) :
    linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t =
      sInf
          (Set.range fun x : Q ↦
            Finset.sum (Finset.range t) fun k ↦
              a (k + 1) * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x)) /
        linearEstimatingWeightSum a t := by
  unfold linearEstimatingAccuracyCertificate
  rw [linearEstimatingFunction_eq_selectedDualValueSum
    Q f gradF ψ xSeq a A Qd g u t hobj hu hgradF]

section Complete

variable [CompleteSpace E]

/-- Under the canonical zero-smoothed max-representation assumptions, the Chapter 6 local model
`accuracyCertificateLocalModel` is exactly the explicit finite sum of selected dual values. -/
theorem accuracyCertificateLocalModel_eq_selectedDualValueSum
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂) (g : E₂ → ℝ) (u : E → E₂) (t : ℕ)
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (hgrad : ∀ x : E, InnerProductSpace.toDualMap ℝ E (∇ f x) = A.flip (u x)) :
    accuracyCertificateLocalModel Q f ψ xSeq a t =
      fun x : Q ↦
        Finset.sum (Finset.range (t + 1)) fun k ↦
          a k * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x) := by
  funext x
  rw [accuracyCertificateLocalModel_apply]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hlinear :=
    affineLinearization_eq_selectedDualValue
      f A Qd g u hobj hu (xSeq k) x (∇ f (xSeq k)) (hgrad (xSeq k))
  simpa using congrArg (fun r : ℝ ↦ a k * (r + ψ x)) hlinear

/-- The Chapter 6 certificate `ℓ_t` equals the normalized infimum of the explicit selected
dual-value local model attached to the canonical maximizer field `u`. -/
theorem localModelAccuracyCertificate_eq_selectedDualValue
    (Q : Set E) (f : E → ℝ) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂) (g : E₂ → ℝ) (u : E → E₂) (t : ℕ)
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (hgrad : ∀ x : E, InnerProductSpace.toDualMap ℝ E (∇ f x) = A.flip (u x)) :
    localModelAccuracyCertificate Q f ψ xSeq a t =
      sInf
          (Set.range fun x : Q ↦
            Finset.sum (Finset.range (t + 1)) fun k ↦
              a k * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x)) /
        A[a](t) := by
  unfold localModelAccuracyCertificate
  rw [accuracyCertificateLocalModel_eq_selectedDualValueSum
    Q f ψ xSeq a A Qd g u t hobj hu hgrad]

/-- Text 6.4.4-Accuracy Certificates Recover Dual Information: if `f` is represented by the
Chapter 6 zero-smoothed dual owner, `u(x)` is the canonical selected maximizer, and the gradient
of `f` is the recovered dual gradient `A^* u(x)`, then both Chapter 6 accuracy certificates are
exactly the normalized infima of explicit finite sums of the selected dual values
`⟪A x, u(x_k)⟫ - g(u(x_k))`.
-/
theorem accuracy_certificates_recover_dual_information
    (Q : Set E) (f : E → ℝ) (gradF : E → E) (ψ : Q → ℝ) (xSeq : ℕ → Q) (a : ℕ → ℝ)
    (A : E →L[ℝ] StrongDual ℝ E₂) (Qd : Set E₂) (g : E₂ → ℝ) (u : E → E₂) (t : ℕ)
    (hobj : ∀ x : E, f x = smoothedPrimalObjective A Qd 0 g 0 0 x)
    (hu : ∀ x : E, u x ∈ smoothedPrimalObjectiveArgmax A Qd g 0 0 x)
    (hgrad : ∀ x : E, InnerProductSpace.toDualMap ℝ E (∇ f x) = A.flip (u x))
    (hgradF : ∀ x : E, InnerProductSpace.toDualMap ℝ E (gradF x) = A.flip (u x)) :
    localModelAccuracyCertificate Q f ψ xSeq a t =
      sInf
          (Set.range fun x : Q ↦
            Finset.sum (Finset.range (t + 1)) fun k ↦
              a k * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x)) /
        A[a](t) ∧
      linearEstimatingAccuracyCertificate Q a f gradF ψ xSeq t =
        sInf
            (Set.range fun x : Q ↦
              Finset.sum (Finset.range t) fun k ↦
                a (k + 1) * (A (x : E) (u (xSeq k)) - g (u (xSeq k)) + ψ x)) /
          linearEstimatingWeightSum a t := by
  exact ⟨
    localModelAccuracyCertificate_eq_selectedDualValue
      Q f ψ xSeq a A Qd g u t hobj hu hgrad,
    linearEstimatingAccuracyCertificate_eq_selectedDualValue
      Q f gradF ψ xSeq a A Qd g u t hobj hu hgradF
  ⟩

end Complete

end
