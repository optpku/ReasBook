/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_4_3_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace MaximumVolumeInscribedEllipsoid

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped BigOperators RealSymmetricMatrixSpace SecondOrderCone

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "SymmMat" => 𝕊^n

private abbrev secondOrderSlack
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (i : Fin m) : E × ℝ :=
  ((G : Mat).toEuclideanLin (a i), b i - inner ℝ (a i) v)

/- Definition 5.4.5.7 lies in the maximum-volume-inscribed-ellipsoid / logarithmic-barrier
domain.

Sampled owner-style declarations in this domain:
* `logDetBarrier` and `logDetBarrier_apply` in `Chap05/Definition_5_4_4_5`, the chapter owner of
  the determinant contribution on `𝕊^n₊₊`;
* `secondOrderCone` and `mem_interior_secondOrderCone_iff` in `Chap05/Lemma_5_4_3_3`, the
  chapter owner/view for the strict second-order-cone inequalities `‖x‖ < t`;
* `circumscribedEllipsoidBarrierDomain` and `circumscribedEllipsoidBarrier` in
  `Chap05/Definition_5_4_5_5`, the adjacent ellipsoid-barrier owner pattern on a strict-domain
  subtype;
* `analyticBarrierDomain`, `AnalyticBarrierPoint`, and `analyticBarrier` in
  `Chap03/Definition_3_62`, the chapter precedent for keeping a barrier on its strict-domain
  carrier and any raw formula only as a bridge.

Source/core/bridge triage:
* source-facing: the strict inscribed-ellipsoid barrier domain and barrier;
* core/canonical: `logDetBarrier n` on `𝕊^n₊₊` together with `interior K₂[E]` for each
  second-order-cone slack;
* bridge/view: the raw triple formula `logarithmicBarrierAmbient` and the slack pairs
  `secondOrderSlack a b G v i`.

Primitive data:
* the half-space data `a`, `b`.

Derived API:
* the strict domain `logarithmicBarrierDomain a b`;
* the strict-domain carrier `LogarithmicBarrierPoint a b`;
* the ambient bridge domain `logarithmicBarrierAmbientDomain a b`;
* the ambient bridge formula `logarithmicBarrierAmbient a b`;
* the source-facing barrier `logarithmicBarrier a b`.

This file therefore keeps the textbook inscribed-ellipsoid barrier on its strict-domain carrier,
reuses the chapter owner `logDetBarrier` for the determinant term, reuses the chapter
second-order-cone owner for each strict slack `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`, and exports only the raw
ambient pullback domain/formula as a bridge for downstream path-following statements.
-/

/-- The strict domain on which the maximum-volume inscribed ellipsoid logarithmic barrier is
defined. -/
def logarithmicBarrierDomain
    (a : Fin m → E) (b : Fin m → ℝ) : Set (𝕊^n₊₊ × E × ℝ) :=
  {Gvτ |
    0 < Gvτ.2.2 - logDetBarrier n Gvτ.1 ∧
      ∀ i : Fin m,
        secondOrderSlack a b Gvτ.1 Gvτ.2.1 i ∈ interior K₂[E]}

/-- The ambient pullback domain of the maximum-volume inscribed ellipsoid logarithmic barrier on
`𝕊ⁿ × E × ℝ`. It is a bridge/view that records strict positivity of the shape variable together
with the same strict second-order-cone inequalities used by the source-facing strict-domain owner
`logarithmicBarrierDomain a b`. -/
def logarithmicBarrierAmbientDomain
    (a : Fin m → E) (b : Fin m → ℝ) : Set (SymmMat × E × ℝ) :=
  {Gvτ |
    Gvτ.1 ∈ (𝕊^n₊₊ : Set SymmMat) ∧
      0 < Gvτ.2.2 - logDetBarrierAmbient n Gvτ.1 ∧
        ∀ i : Fin m,
          secondOrderSlack a b Gvτ.1 Gvτ.2.1 i ∈ interior K₂[E]}

/-- Membership in the barrier domain means that the shifted logarithmic argument
`τ - logDetBarrier n G = τ + log det G` is positive and every second-order-cone slack lies in the
strict branch `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`. -/
theorem mem_logarithmicBarrierDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierDomain a b ↔
      0 < τ - logDetBarrier n G ∧
        ∀ i : Fin m, ‖(toMatrix G).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [logarithmicBarrierDomain, secondOrderSlack, mem_interior_secondOrderCone_iff, toMatrix_def]

/-- Membership in the ambient bridge domain means that the shape variable lies in the strict cone,
the shifted logarithmic argument `τ + log det G` is positive, and every second-order-cone slack
lies in the strict branch `‖G aᵢ‖ < bᵢ - ⟪aᵢ, v⟫`. -/
theorem mem_logarithmicBarrierAmbientDomain_iff
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierAmbientDomain a b ↔
      G ∈ (𝕊^n₊₊ : Set SymmMat) ∧
        0 < τ - logDetBarrierAmbient n G ∧
          ∀ i : Fin m, ‖(G : Mat).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [logarithmicBarrierAmbientDomain, secondOrderSlack, mem_interior_secondOrderCone_iff]

/-- Restricting the ambient bridge domain to a strict-cone shape recovers the source-facing
strict-domain owner. -/
@[simp] theorem mem_logarithmicBarrierAmbientDomain_iff_strict
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    ((G : SymmMat), v, τ) ∈ logarithmicBarrierAmbientDomain a b ↔
      (G, v, τ) ∈ logarithmicBarrierDomain a b := by
  simp [logarithmicBarrierAmbientDomain, logarithmicBarrierDomain, secondOrderSlack,
    mem_interior_secondOrderCone_iff, logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites barrier-domain membership back to the textbook
`τ + log det G` formula. -/
theorem mem_logarithmicBarrierDomain_iff_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    (G, v, τ) ∈ logarithmicBarrierDomain a b ↔
      0 < τ + Real.log (toMatrix G).det ∧
        ∀ i : Fin m, ‖(toMatrix G).toEuclideanLin (a i)‖ < b i - inner ℝ (a i) v := by
  simp [mem_logarithmicBarrierDomain_iff, toMatrix_def]

/-- The subtype of points in the strict inscribed-ellipsoid barrier domain. This is the natural
owner carrier for the logarithmic barrier. -/
abbrev LogarithmicBarrierPoint
    (a : Fin m → E) (b : Fin m → ℝ) :=
  {Gvτ : 𝕊^n₊₊ × E × ℝ // Gvτ ∈ logarithmicBarrierDomain a b}

/-- The ambient formula underlying the maximum-volume inscribed ellipsoid logarithmic barrier. It
is only a bridge view; the owner barrier is `logarithmicBarrier a b` on
`LogarithmicBarrierPoint a b`. -/
def logarithmicBarrierAmbient
    (a : Fin m → E) (b : Fin m → ℝ) : SymmMat × E × ℝ → ℝ :=
  fun Gvτ ↦
    logDetBarrierAmbient n Gvτ.1
      - Real.log (Gvτ.2.2 - logDetBarrierAmbient n Gvτ.1)
      + ∑ i : Fin m, secondOrderConeBarrier (secondOrderSlack a b Gvτ.1 Gvτ.2.1 i)

/-- Definition 5.4.5.7: the logarithmic barrier for the maximum-volume inscribed ellipsoid
reformulation is
`F(G, v, τ) = -log det G - log (τ + log det G)
  - ∑ᵢ log ((bᵢ - ⟪aᵢ, v⟫)^2 - ‖G aᵢ‖^2)`. -/
def logarithmicBarrier
    (a : Fin m → E) (b : Fin m → ℝ) :
    LogarithmicBarrierPoint a b → ℝ :=
  fun Gvτ ↦ logarithmicBarrierAmbient a b ((Gvτ.1.1 : SymmMat), Gvτ.1.2.1, Gvτ.1.2.2)

/-- Evaluating the ambient maximum-volume inscribed ellipsoid barrier recovers the owner formula
built from the chapter determinant barrier `logDetBarrier n` and the canonical
second-order-cone barrier owner on each slack pair. -/
theorem logarithmicBarrierAmbient_apply
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b (G, v, τ) =
      logDetBarrierAmbient n G
        - Real.log (τ - logDetBarrierAmbient n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((G : Mat).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simp [logarithmicBarrierAmbient, secondOrderSlack]

/-- On a strict-cone slice, the ambient inscribed-ellipsoid barrier agrees with the owner formula
built from `logDetBarrier n`. -/
theorem logarithmicBarrierAmbient_apply_strict
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b ((G : SymmMat), v, τ) =
      logDetBarrier n G
        - Real.log (τ - logDetBarrier n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((toMatrix G).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simp [logarithmicBarrierAmbient_apply, toMatrix_def, logDetBarrier, logDetBarrierAmbient]

/-- Expanding `logDetBarrier n` rewrites the ambient barrier back to the textbook
`-log det G - log (τ + log det G)` formula. -/
theorem logarithmicBarrierAmbient_apply_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : SymmMat) (v : E) (τ : ℝ) :
    logarithmicBarrierAmbient a b (G, v, τ) =
      -Real.log (G : Mat).det
        - Real.log (τ + Real.log (G : Mat).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
  rw [logarithmicBarrierAmbient_apply]
  calc
    logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
        + ∑ i : Fin m, secondOrderConeBarrier (secondOrderSlack a b G v i)
      = logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
          + ∑ i : Fin m,
              (-Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ))) := by
            refine congrArg
              (fun s ↦ logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G) + s) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [secondOrderConeBarrier_apply, secondOrderSlack]
    _ = logDetBarrierAmbient n G - Real.log (τ - logDetBarrierAmbient n G)
          - ∑ i : Fin m,
              Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
            rw [Finset.sum_neg_distrib]
            simp [sub_eq_add_neg]
    _ = -Real.log (G : Mat).det
          - Real.log (τ + Real.log (G : Mat).det)
          - ∑ i : Fin m,
              Real.log
                ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                  ‖(G : Mat).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
            simp [logDetBarrierAmbient]

/-- Evaluating the inscribed-ellipsoid barrier on a strict-domain point recovers its ambient
bridge formula. -/
@[simp] theorem logarithmicBarrier_apply
    (a : Fin m → E) (b : Fin m → ℝ) (Gvτ : LogarithmicBarrierPoint a b) :
    logarithmicBarrier a b Gvτ =
      logarithmicBarrierAmbient a b ((Gvτ.1.1 : SymmMat), Gvτ.1.2.1, Gvτ.1.2.2) :=
  rfl

/-- At a strict-domain triple `(G, v, τ)`, the logarithmic barrier is the owner formula built
from `logDetBarrier n` and the canonical second-order-cone barrier owner. -/
theorem logarithmicBarrier_apply_triple
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ)
    (h : (G, v, τ) ∈ logarithmicBarrierDomain a b) :
    logarithmicBarrier a b ⟨(G, v, τ), h⟩ =
      logDetBarrier n G
        - Real.log (τ - logDetBarrier n G)
        + ∑ i : Fin m,
            secondOrderConeBarrier
              ((toMatrix G).toEuclideanLin (a i), b i - inner ℝ (a i) v) := by
  simpa using logarithmicBarrierAmbient_apply_strict a b G v τ

/-- At a strict-domain triple `(G, v, τ)`, the inscribed-ellipsoid logarithmic barrier is the
textbook formula
`-log det G - log (τ + log det G) - \sum_i log ((bᵢ - ⟪aᵢ, v⟫)^2 - ‖G aᵢ‖²)`. -/
theorem logarithmicBarrier_apply_triple_formula
    (a : Fin m → E) (b : Fin m → ℝ) (G : 𝕊^n₊₊) (v : E) (τ : ℝ)
    (h : (G, v, τ) ∈ logarithmicBarrierDomain a b) :
    logarithmicBarrier a b ⟨(G, v, τ), h⟩ =
      -Real.log (toMatrix G).det
        - Real.log (τ + Real.log (toMatrix G).det)
        - ∑ i : Fin m,
            Real.log
              ((b i - inner ℝ (a i) v) ^ (2 : ℕ) -
                ‖(toMatrix G).toEuclideanLin (a i)‖ ^ (2 : ℕ)) := by
  simpa [toMatrix_def] using logarithmicBarrierAmbient_apply_formula a b (G : SymmMat) v τ

end

end MaximumVolumeInscribedEllipsoid
