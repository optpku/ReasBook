/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: finite-window best-gradient quantities along first-order iterate sequences on a
real Hilbert space.

Owner-style declarations sampled before refining this file:
* `Finset.inf'`, the mathlib owner for minima over nonempty finite sets;
* `Finset.inf'_le`, the canonical pointwise upper-bound API for that owner;
* `Finset.exists_mem_eq_inf'`, the canonical attainment API for that owner;
* `minGradientNormAlongIterates_le_sqrt` in `Chap01/Theorem_1_6_8`, the direct downstream chapter
  consumer of the source-facing quantity defined here.

Source/core/bridge triage:
* source-facing: the textbook quantity `g_{k,T}`;
* core/canonical: the nonempty finite interval `Finset.Icc k T` together with `Finset.inf'`;
* bridge/view: the interval-membership and attainment consequences specialized to gradient norms.

Primitive data:
* the objective `f`;
* the iterate sequence `x`;
* the window endpoints `k ≤ T`.

Derived API:
* the pointwise bound `minGradientNormAlongIterates.le`;
* the attainment statement `minGradientNormAlongIterates.exists_eq`.

No earlier project owner packages this finite-window minimum pattern, so the correct owner
abstraction here is the direct `Finset.inf'` specialization rather than a new wrapper structure.
This file therefore keeps the source-facing owner `minGradientNormAlongIterates` and exposes only
the two canonical derived consequences directly from that owner. -/

/-- Definition 2.23: for iterates `xᵢ` of a differentiable function `f : E → ℝ` on a real Hilbert
space and indices `k ≤ T`, `g[f; x; k, T | h]` is the minimum of `‖∇ f (xᵢ)‖` over all `i` with
`k ≤ i ≤ T`. -/
def minGradientNormAlongIterates (f : E → ℝ) (x : ℕ → E)
    (k T : ℕ) (h : k ≤ T) : ℝ :=
  (Finset.Icc k T).inf' (Finset.nonempty_Icc.2 h) (fun i ↦ ‖∇ f (x i)‖)

/-
Source-facing notation for Definition 2.23: `g[f; x; k, T | h]` is the textbook quantity
`g_{k,T}` attached to the objective `f`, iterate sequence `x`, and window proof `h : k ≤ T`.
-/
namespace MinGradientNormAlongIterates

scoped notation:max "g[" f ";" x ";" k "," T "|" h "]" =>
  minGradientNormAlongIterates f x k T h

end MinGradientNormAlongIterates

open scoped MinGradientNormAlongIterates

/-- Unfolding `g[f; x; k, T | h]` gives the canonical finite-interval infimum formula from
Definition 2.23. -/
@[simp] theorem minGradientNormAlongIterates_def (f : E → ℝ) (x : ℕ → E) (k T : ℕ)
    (h : k ≤ T) :
    g[f; x; k, T | h] =
      (Finset.Icc k T).inf' (Finset.nonempty_Icc.2 h) (fun i ↦ ‖∇ f (x i)‖) := rfl

namespace minGradientNormAlongIterates

/-- The window minimum `g[f; x; k, T | h]` is bounded above by each sampled gradient norm in the
same window. -/
theorem le (f : E → ℝ) (x : ℕ → E)
    {k T i : ℕ} (h : k ≤ T) (hki : k ≤ i) (hiT : i ≤ T) :
    g[f; x; k, T | h] ≤ ‖∇ f (x i)‖ := by
  rw [minGradientNormAlongIterates_def]
  exact Finset.inf'_le (fun j ↦ ‖∇ f (x j)‖) (Finset.mem_Icc.mpr ⟨hki, hiT⟩)

/-- Some index in the window `k ≤ i ≤ T` attains the minimum gradient norm
`g[f; x; k, T | h]`. -/
theorem exists_eq (f : E → ℝ) (x : ℕ → E)
    {k T : ℕ} (h : k ≤ T) :
    ∃ i, k ≤ i ∧ i ≤ T ∧
      g[f; x; k, T | h] = ‖∇ f (x i)‖ := by
  rcases (Finset.Icc k T).exists_mem_eq_inf' (Finset.nonempty_Icc.2 h)
      (fun i ↦ ‖∇ f (x i)‖) with ⟨i, hi, hmin⟩
  rcases Finset.mem_Icc.mp hi with ⟨hki, hiT⟩
  exact ⟨i, hki, hiT, hmin⟩

end minGradientNormAlongIterates
