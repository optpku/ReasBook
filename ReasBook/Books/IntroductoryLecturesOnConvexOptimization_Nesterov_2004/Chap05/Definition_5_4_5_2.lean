/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.5.2 lies in the minimum-volume enclosing-ellipsoid / logarithmic-barrier
domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` in `Chap05/Definition_5_4_4_5`, the chapter owner for the `-\log \det`
  contribution on `𝕊^n₊₊`;
* `logDetBarrier_apply` in the same file, the canonical expansion bridge back to the textbook
  determinant formula;
* the ambient symmetric-space bridge in `Chap05/Theorem_5_4_5_1`, which transports this owner
  barrier to the path-following setting without introducing a second public MVEE barrier owner;
* `logarithmicBarrier` in `Chap05/Definition_5_4_5_7`, the nearby inscribed-ellipsoid analogue
  with the same `τ`-shifted logarithmic-barrier pattern.

Best owner abstraction:
* source-facing: the MVEE barrier and strict domain on `(H, v, τ)`;
* core/canonical: `logDetBarrier n` for the determinant barrier on `𝕊^n₊₊`;
* bridge/view: the textbook expansion `logDetBarrier n H = -log det H`.

Primitive data:
* the finite point family `a`;
* the strict-cone variable `H : 𝕊^n₊₊`, center `v`, and scalar `τ`.

Derived API:
* the strict barrier domain `minimumVolumeEnclosingEllipsoidBarrierDomain a`;
* its owner carrier `MinimumVolumeEnclosingEllipsoidBarrierPoint a`;
* the determinant contribution `logDetBarrier n H`;
* the ambient bridge formula `minimumVolumeEnclosingEllipsoidBarrierAmbient a`.

This file therefore keeps the source-facing MVEE barrier on its strict domain, and reuses the
chapter owner `logDetBarrier` instead of repeating a parallel local `-log det` API. The raw
formula on `𝕊^n₊₊ × Eₙ × ℝ` is retained only as a bridge view.
-/

noncomputable section

open Matrix
open scoped BigOperators RealSymmetricMatrixSpace

variable {ι : Type*} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev pointSlack (H : SymmMat) (v x : Eₙ) : ℝ :=
  1 - ‖(H : Mat).toEuclideanLin x - v‖ ^ (2 : ℕ)

/-- The strict domain on which the minimum-volume enclosing ellipsoid logarithmic barrier is
defined. -/
def minimumVolumeEnclosingEllipsoidBarrierDomain
    (a : ι → Eₙ) : Set (𝕊^n₊₊ × Eₙ × ℝ) :=
  {Hvτ | 0 < Hvτ.2.2 - logDetBarrier n Hvτ.1 ∧
    ∀ i, 0 < pointSlack Hvτ.1 Hvτ.2.1 (a i)}

/-- The ambient pullback domain of the MVEE logarithmic barrier on `𝕊ⁿ × Eₙ × ℝ`. It is a
bridge/view that records strict positivity of the shape variable together with the same strict
slack inequalities used by the source-facing strict-domain owner
`minimumVolumeEnclosingEllipsoidBarrierDomain a`. -/
def minimumVolumeEnclosingEllipsoidBarrierAmbientDomain
    (a : ι → Eₙ) : Set (SymmMat × Eₙ × ℝ) :=
  {Hvτ | Hvτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
    0 < Hvτ.2.2 - logDetBarrierAmbient n Hvτ.1 ∧
      ∀ i, 0 < pointSlack Hvτ.1 Hvτ.2.1 (a i)}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n H = τ + log det H` is positive and every ellipsoid slack
`1 - ‖H a_i - v‖²` is positive. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a ↔
      0 < τ - logDetBarrier n H ∧
        ∀ i,
          0 < 1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierDomain, pointSlack]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det H` formula. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff_formula
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a ↔
      0 < τ + Real.log (((H : SymmMat) : Mat).det) ∧
        ∀ i,
          0 < 1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  simp [mem_minimumVolumeEnclosingEllipsoidBarrierDomain_iff]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict cone,
the shifted logarithmic argument `τ + log det H` is positive, and every ellipsoid slack
`1 - ‖H a_i - v‖²` is positive. -/
theorem mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff
    (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a ↔
      H ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n H ∧
          ∀ i,
            0 < 1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ) := by
  rfl

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_minimumVolumeEnclosingEllipsoidBarrierAmbientDomain_iff_strict
    (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    ((H : SymmMat), v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierAmbientDomain a ↔
      (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbientDomain,
    minimumVolumeEnclosingEllipsoidBarrierDomain, logDetBarrier, logDetBarrierAmbient]

/-- The subtype of points in the strict MVEE barrier domain. This is the natural owner carrier
for the MVEE logarithmic barrier. -/
abbrev MinimumVolumeEnclosingEllipsoidBarrierPoint
    (a : ι → Eₙ) :=
  {Hvτ : 𝕊^n₊₊ × Eₙ × ℝ // Hvτ ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a}

/-- The ambient formula underlying the MVEE logarithmic barrier. It is only a bridge view; the
owner barrier is `minimumVolumeEnclosingEllipsoidBarrier a` on
`MinimumVolumeEnclosingEllipsoidBarrierPoint a`. -/
def minimumVolumeEnclosingEllipsoidBarrierAmbient
    [Fintype ι] (a : ι → Eₙ) : SymmMat × Eₙ × ℝ → ℝ :=
  fun Hvτ ↦
    logDetBarrierAmbient n Hvτ.1
      - Real.log (Hvτ.2.2 - logDetBarrierAmbient n Hvτ.1)
      - ∑ i,
          Real.log (pointSlack Hvτ.1 Hvτ.2.1 (a i))

/-- Definition 5.4.5.2: the logarithmic barrier for the minimum-volume enclosing ellipsoid
problem, kept on its strict domain. -/
def minimumVolumeEnclosingEllipsoidBarrier
    [Fintype ι] (a : ι → Eₙ) : MinimumVolumeEnclosingEllipsoidBarrierPoint a → ℝ :=
  fun Hvτ ↦ minimumVolumeEnclosingEllipsoidBarrierAmbient a
    ((Hvτ.1.1 : SymmMat), Hvτ.1.2.1, Hvτ.1.2.2)

/-- Evaluating the ambient MVEE barrier recovers the canonical owner formula equivalent to the
textbook expression
`-\log \det H - \log (\tau + \log \det H) - \sum_i \log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrierAmbient_apply
    [Fintype ι] (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    minimumVolumeEnclosingEllipsoidBarrierAmbient a (H, v, τ) =
      logDetBarrierAmbient n H
        - Real.log (τ - logDetBarrierAmbient n H)
        - ∑ i,
            Real.log (1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbient, pointSlack]

/-- Expanding `logDetBarrier n` rewrites the ambient MVEE barrier back to the textbook
formula `-log det H - log (τ + log det H) - \sum_i log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrierAmbient_apply_formula
    [Fintype ι] (a : ι → Eₙ) (H : SymmMat) (v : Eₙ) (τ : ℝ) :
    minimumVolumeEnclosingEllipsoidBarrierAmbient a (H, v, τ) =
      -Real.log (H : Mat).det
        - Real.log (τ + Real.log (H : Mat).det)
        - ∑ i,
            Real.log (1 - ‖(H : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrierAmbient_apply]

/-- Evaluating the MVEE barrier on a strict-domain point recovers its ambient bridge formula. -/
@[simp] theorem minimumVolumeEnclosingEllipsoidBarrier_apply
    [Fintype ι] (a : ι → Eₙ) (Hvτ : MinimumVolumeEnclosingEllipsoidBarrierPoint a) :
    minimumVolumeEnclosingEllipsoidBarrier a Hvτ =
      minimumVolumeEnclosingEllipsoidBarrierAmbient a
        ((Hvτ.1.1 : SymmMat), Hvτ.1.2.1, Hvτ.1.2.2) :=
  rfl

/-- At a strict-domain triple `(H, v, τ)`, the MVEE logarithmic barrier is the textbook
formula. -/
theorem minimumVolumeEnclosingEllipsoidBarrier_apply_triple
    [Fintype ι] (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ)
    (h : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a) :
    minimumVolumeEnclosingEllipsoidBarrier a ⟨(H, v, τ), h⟩ =
      logDetBarrier n H
        - Real.log (τ - logDetBarrier n H)
        - ∑ i,
            Real.log (1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  simp [minimumVolumeEnclosingEllipsoidBarrier, minimumVolumeEnclosingEllipsoidBarrierAmbient,
    pointSlack, logDetBarrier, logDetBarrierAmbient]

/-- At a strict-domain triple `(H, v, τ)`, the MVEE logarithmic barrier is the textbook formula
`-log det H - log (τ + log det H) - \sum_i log (1 - \|H a_i - v\|^2)`. -/
theorem minimumVolumeEnclosingEllipsoidBarrier_apply_triple_formula
    [Fintype ι] (a : ι → Eₙ) (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ)
    (h : (H, v, τ) ∈ minimumVolumeEnclosingEllipsoidBarrierDomain a) :
    minimumVolumeEnclosingEllipsoidBarrier a ⟨(H, v, τ), h⟩ =
      -Real.log (((H : SymmMat) : Mat).det)
        - Real.log (τ + Real.log (((H : SymmMat) : Mat).det))
        - ∑ i,
            Real.log (1 - ‖((H : SymmMat) : Mat).toEuclideanLin (a i) - v‖ ^ (2 : ℕ)) := by
  rw [minimumVolumeEnclosingEllipsoidBarrier_apply_triple]
  simp

end
