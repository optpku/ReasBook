/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Text_4_2_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u}

/- Definition 5.2.9 lies in the Chapter 5 strongly-convex self-concordant quadratic-regime
domain.

Sampled owner-style declarations:
* `cubicNewtonQuadraticDecreaseRegion` in `Chap04/Text_4_2_11`, the Chapter 4 core owner for the
  corresponding quadratic-decrease region written in multiplication form;
* `mem_cubicNewtonQuadraticDecreaseRegion` in `Chap04/Text_4_2_11`, the atomic expansion of that
  Chapter 4 owner;
* `intermediateNewtonQuadraticConvergenceRegion` in `Chap05/Proposition_5_2_1`, the nearby
  Chapter 5 pattern where a source-facing quadratic region remains a public owner and notation is
  used on theorem surfaces.

Source/core/bridge triage:
* source-facing: `Q_f = {x | f x - f* ≤ 1 / (8 M_f^2)}`;
* core/canonical: the Chapter 4 region `cubicNewtonQuadraticDecreaseRegion` when a separate
  identification of thresholds is available;
* bridge/view: the membership theorem below and the comparison theorem to the Chapter 4 owner.

Primitive data:
* the objective `f`;
* the optimal value `fStar`;
* the self-concordance scaling constant `M_f`.

Derived API:
* the source-facing region `Q_f` itself;
* the textbook membership formula;
* a thin bridge to the Chapter 4 multiplication-form owner when the thresholds are identified.

This refinement restores Definition 5.2.9 as a Chapter 5 source-facing owner instead of collapsing
it into the earlier Chapter 4 owner. The Chapter 4 region remains the canonical comparison target,
but it is now downstream of the Chapter 5 surface rather than replacing it. The public owner is
written in the zero-safe multiplication form `8 M_f² (f x - f*) ≤ 1`, so the quadratic case
`M_f = 0` correctly yields the whole space; the divided threshold remains available as a positive-
parameter bridge theorem. -/

/-- Definition 5.2.9: the Chapter 5 quadratic-convergence region, written in the zero-safe
multiplication form `8 M_f² (f(x) - f*) ≤ 1`. When `M_f = 0`, this is all of `E`, matching the
degenerate quadratic regime. -/
def selfConcordantQuadraticRegion
    (f : E → ℝ) (fStar : ℝ) (Mf : NNReal) : Set E :=
  {x | (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1}

/-- Source-facing notation for the Chapter 5 quadratic-convergence region `Q_f`. -/
scoped[SelfConcordantQuadraticRegion] notation:max "𝒬[" f " | " fStar ", " Mf "]" =>
  selfConcordantQuadraticRegion f fStar Mf

open scoped SelfConcordantQuadraticRegion

-- Proof sketch: unfold `selfConcordantQuadraticRegion`.
/-- Membership in `𝒬[f | f*, M_f]` is exactly the zero-safe inequality
`8 M_f² (f(x) - f*) ≤ 1`. -/
theorem mem_selfConcordantQuadraticRegion_iff
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E} :
    x ∈ 𝒬[f | fStar, Mf] ↔
      (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1 :=
  Iff.rfl

/-- In the nondegenerate regime `M_f > 0`, the zero-safe multiplication-form owner
`𝒬[f | f*, M_f]` is equivalent to the textbook divided threshold
`f(x) - f* ≤ 1 / (8 M_f^2)`. -/
theorem mem_selfConcordantQuadraticRegion_iff_div
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} (hMf : 0 < Mf) {x : E} :
    x ∈ 𝒬[f | fStar, Mf] ↔
      f x - fStar ≤ 1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) := by
  have hMf' : 0 < (Mf : ℝ) := by
    exact_mod_cast hMf
  have hcoeff : 0 < (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  change (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 1 ↔
    f x - fStar ≤ 1 / (8 * (Mf : ℝ) ^ (2 : ℕ))
  constructor
  · intro hx
    exact (le_div_iff₀ hcoeff).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hx
  · intro hx
    have hx' : (f x - fStar) * ((8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ)) ≤ 1 :=
      (le_div_iff₀ hcoeff).1 hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using hx'

/-- If `x` lies outside the Chapter 5 quadratic-convergence region `𝒬[f | f*, M_f]`, then the
scaling constant `M_f` is necessarily positive. In the degenerate quadratic case `M_f = 0`, the
zero-safe owner `𝒬[f | f*, M_f]` is all of `E`. -/
theorem Mf_pos_of_not_mem_selfConcordantQuadraticRegion
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E}
    (hx : x ∉ 𝒬[f | fStar, Mf]) :
    0 < Mf := by
  by_contra hMf
  have hMf_zero : Mf = 0 := le_antisymm (le_of_not_gt hMf) Mf.2
  have hx_mem : x ∈ 𝒬[f | fStar, Mf] := by
    rw [mem_selfConcordantQuadraticRegion_iff]
    norm_num [hMf_zero]
  exact hx hx_mem

/-- If `x` lies outside the Chapter 5 quadratic-convergence region `𝒬[f | f*, M_f]`, then its
suboptimality gap `f(x) - f*` is positive. Nonpositive gaps automatically satisfy the zero-safe
membership inequality. -/
theorem gap_pos_of_not_mem_selfConcordantQuadraticRegion
    {f : E → ℝ} {fStar : ℝ} {Mf : NNReal} {x : E}
    (hx : x ∉ 𝒬[f | fStar, Mf]) :
    0 < f x - fStar := by
  by_contra hgap
  have hcoeff : 0 ≤ (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) := by
    positivity
  have hx_mem : x ∈ 𝒬[f | fStar, Mf] := by
    rw [mem_selfConcordantQuadraticRegion_iff]
    have hmul : (8 : ℝ) * (Mf : ℝ) ^ (2 : ℕ) * (f x - fStar) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hcoeff (le_of_not_gt hgap)
    linarith
  exact hx hx_mem

-- Proof sketch: rewrite membership in `𝒬[f | fStar, M_f]` through the positive-`M_f` divided
-- threshold bridge, rewrite the Chapter 4 region by its multiplication-form owner, and convert
-- between the two divided thresholds using the positive factor `2 * L₃^2`.
/-- If `f* = f(x^*)` and the Chapter 5 threshold `1 / (8 M_f^2)` matches the divided Chapter 4
threshold `σ^3 / (2 L₃^2)` with `L₃ > 0`, then the Chapter 5 region `Q_f` agrees pointwise with
the Chapter 4 quadratic-decrease region
`cubicNewtonQuadraticDecreaseRegion f xStar σ L3`. -/
theorem mem_selfConcordantQuadraticRegion_iff_mem_cubicNewtonQuadraticDecreaseRegion
    {f : E → ℝ} {fStar σ : ℝ} {Mf L3 : NNReal} {xStar x : E}
    (hfStar : f xStar = fStar)
    (hMf : 0 < Mf)
    (hthreshold :
      1 / (8 * (Mf : ℝ) ^ (2 : ℕ)) = σ ^ (3 : ℕ) / (2 * (L3 : ℝ) ^ (2 : ℕ)))
    (hL3 : 0 < (L3 : ℝ)) :
    x ∈ 𝒬[f | fStar, Mf] ↔
      x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 := by
  rw [mem_selfConcordantQuadraticRegion_iff_div hMf, mem_cubicNewtonQuadraticDecreaseRegion,
    ← hfStar, hthreshold]
  have hcoeff : 0 < 2 * (L3 : ℝ) ^ (2 : ℕ) := by
    positivity
  constructor
  · intro hx
    have hx' : (f x - f xStar) * (2 * (L3 : ℝ) ^ (2 : ℕ)) ≤ σ ^ (3 : ℕ) :=
      (le_div_iff₀ hcoeff).1 hx
    simpa [mul_assoc, mul_left_comm, mul_comm] using hx'
  · intro hx
    exact (le_div_iff₀ hcoeff).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hx
