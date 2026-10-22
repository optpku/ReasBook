/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.3 lies in the chapter's real convex-analysis / epigraph domain.

Primary domain:
- convexity of the absolute value function on `ℝ`;
- the epigraph of `x ↦ |x|` as a closed subset of `ℝ × ℝ`;
- the half-space presentation of that epigraph.

Sampled owner-style declarations:
- mathlib `convexOn_univ_norm`, the canonical convexity owner for norms on real normed spaces;
- mathlib `IsClosed.epigraph`, the canonical closed-epigraph owner for continuous real-valued
  functions on closed domains;
- mathlib `abs_le`, the canonical order-theoretic characterization of `|x| ≤ t`.

Best owner abstraction:
- core/canonical: `ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|)` and the standard epigraph subset
  `{p : ℝ × ℝ | |p.1| ≤ p.2}`;
- bridge/view: the half-space presentation
  `{p : ℝ × ℝ | p.2 ≥ p.1} ∩ {p : ℝ × ℝ | p.2 ≥ -p.1}`.

Primitive data:
- the function `x ↦ |x|`.

Derived API:
- the closedness of its epigraph;
- the half-space description of the same epigraph.

Source/core/bridge triage:
- source-facing: the three statements of Proposition 3.3;
- core/canonical: mathlib `ConvexOn`, continuity, and epigraph closedness;
- bridge/view: the half-space equality translating the epigraph inequality into two affine
  inequalities.

The file therefore keeps the three textbook statements as the public surface, but avoids any local
wrapper definition for the epigraph because the standard mathlib epigraph set is already the right
owner expression in this domain.
-/

/-- Proposition 3.3 (1): the absolute value function on `ℝ` is convex on all of `ℝ`. -/
-- Proof sketch: identify `|x|` with the norm on `ℝ` and use the standard convexity of the norm.
theorem abs_convexOn_univ :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
  simpa [Real.norm_eq_abs] using
    (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))

/-- Proposition 3.3 (2): the epigraph of the absolute value function on `ℝ` is closed in
`ℝ × ℝ`. -/
-- Proof sketch: `x ↦ |x|` is continuous on the closed domain `Set.univ`; apply the canonical
-- `IsClosed.epigraph` theorem.
theorem abs_epigraph_isClosed :
    IsClosed {p : ℝ × ℝ | |p.1| ≤ p.2} := by
  simpa using IsClosed.epigraph isClosed_univ continuous_abs.continuousOn

/-- Proposition 3.3 (3): the epigraph of the absolute value function on `ℝ` is exactly the
intersection of the half-spaces `t ≥ x` and `t ≥ -x`. -/
-- Proof sketch: rewrite `|x|` as `max x (-x)`. Then `|x| ≤ t` is equivalent to the pair of
-- inequalities `x ≤ t` and `-x ≤ t`.
theorem abs_epigraph_eq_inter_halfspaces :
    {p : ℝ × ℝ | |p.1| ≤ p.2} = {p : ℝ × ℝ | p.2 ≥ p.1} ∩ {p : ℝ × ℝ | p.2 ≥ -p.1} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₂, by simpa using neg_le_neg h₁⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by simpa using neg_le_neg h₂, h₁⟩
