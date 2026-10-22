/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.4.7.10 lies in the Chapter 5 entropy-epigraph / exponential-cone domain.

Sampled owner declarations:
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the upstream source-facing owner for the
  conic entropy epigraph;
* `mem_entropyEpigraphCone_iff` from `Definition_5_4_7_8`, the explicit coordinate membership
  theorem for that owner;
* `entropyEpigraphConeBarrier` from `Theorem_5_4_7_6`, the upstream logarithmic barrier owner on
  the entropy-epigraph cone;
* `entropyEpigraphConeBarrier_apply` from `Theorem_5_4_7_6`, the pointwise bridge for that
  barrier.

Best owner abstraction:
* keep Definition 5.4.7.10 source-facing as the exponential cone and its barrier;
* reuse `entropyEpigraphCone` and `entropyEpigraphConeBarrier` as the core owners;
* express the present file through the coordinate change `((x, y), τ) ↦ ((τ, y), -x)`.

Primitive data:
* no new cone/barrier data beyond the source-facing coordinate change.

Derived API:
* `exponentialCone` and `exponentialConeBarrier`;
* the textbook membership criterion `mem_exponentialCone_iff`;
* the textbook evaluation formula `exponentialConeBarrier_apply`.

Source/core/bridge triage:
* source-facing: `exponentialCone` and `exponentialConeBarrier`;
* core/canonical: `entropyEpigraphCone` and `entropyEpigraphConeBarrier`;
* bridge/view: the coordinate change `((x, y), τ) ↦ ((τ, y), -x)`.

This refinement removes the duplicate raw cone and barrier bodies. The exponential cone is kept as
the source-facing object from the text, but its implementation now reuses the chapter owner
`entropyEpigraphCone`, and the barrier is the corresponding pullback of
`entropyEpigraphConeBarrier`. -/

/-- Definition 5.4.7.10 (1): the exponential cone is the source-facing coordinate view of the
entropy-epigraph cone under `((x, y), τ) ↦ ((τ, y), -x)`. -/
def exponentialCone : Set ((ℝ × ℝ) × ℝ) :=
  {p | ((p.2, p.1.2), -p.1.1) ∈ entropyEpigraphCone}

/-- A triple `((x, y), τ)` belongs to `exponentialCone` exactly when
`y ≥ τ * exp (x / τ)` and `τ > 0`. -/
theorem mem_exponentialCone_iff (x y τ : ℝ) :
    ((x, y), τ) ∈ exponentialCone ↔
      y ≥ τ * Real.exp (x / τ) ∧ 0 < τ := by
  change ((τ, y), -x) ∈ entropyEpigraphCone ↔
      y ≥ τ * Real.exp (x / τ) ∧ 0 < τ
  rw [mem_entropyEpigraphCone_iff]
  constructor
  · rintro ⟨hτ, hy, hx⟩
    refine ⟨?_, hτ⟩
    have hlog : x / τ ≤ Real.log (y / τ) := by
      have hx' : x ≤ τ * Real.log (y / τ) := by
        have hlog_div : Real.log (y / τ) = Real.log y - Real.log τ :=
          Real.log_div hy.ne' hτ.ne'
        rw [hlog_div]
        linarith
      exact (div_le_iff₀ hτ).2 <| by simpa [mul_comm] using hx'
    have hexp : Real.exp (x / τ) ≤ y / τ :=
      (Real.le_log_iff_exp_le (div_pos hy hτ)).1 hlog
    calc
      τ * Real.exp (x / τ) ≤ τ * (y / τ) := by
        exact mul_le_mul_of_nonneg_left hexp hτ.le
      _ = y := by field_simp [hτ.ne']
  · rintro ⟨hy, hτ⟩
    have hy_pos : 0 < y := by
      exact lt_of_lt_of_le (mul_pos hτ (Real.exp_pos (x / τ))) hy
    refine ⟨hτ, hy_pos, ?_⟩
    have hdiv : Real.exp (x / τ) ≤ y / τ := by
      exact (le_div_iff₀ hτ).2 <| by simpa [mul_comm] using hy
    have hlog : x / τ ≤ Real.log (y / τ) :=
      (Real.le_log_iff_exp_le (div_pos hy_pos hτ)).2 hdiv
    have hx' : x ≤ τ * Real.log (y / τ) :=
      by simpa [mul_comm] using (div_le_iff₀ hτ).1 hlog
    rw [Real.log_div hy_pos.ne' hτ.ne'] at hx'
    linarith

/-- Definition 5.4.7.10 (2): the exponential-cone barrier is the pullback of the entropy-epigraph
cone barrier under the same coordinate change. -/
def exponentialConeBarrier : ((ℝ × ℝ) × ℝ) → ℝ :=
  fun p ↦ entropyEpigraphConeBarrier ((p.2, p.1.2), -p.1.1)

/-- Evaluating `exponentialConeBarrier` at `((x, y), τ)` gives the textbook formula
`-log (τ log (y / τ) - x) - log y - log τ`. -/
theorem exponentialConeBarrier_apply (x y τ : ℝ) :
    exponentialConeBarrier ((x, y), τ) =
      -Real.log (τ * Real.log (y / τ) - x) - Real.log y - Real.log τ := by
  rw [exponentialConeBarrier, entropyEpigraphConeBarrier_apply]
  by_cases hτ : τ = 0
  · simp [hτ]
  · by_cases hy : y = 0
    · simp [hy]
    · rw [Real.log_div hτ hy, Real.log_div hy hτ]
      ring_nf

end
