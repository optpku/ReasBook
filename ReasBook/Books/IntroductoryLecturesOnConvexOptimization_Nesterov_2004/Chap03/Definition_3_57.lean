/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_7

-- Declarations for this item will be appended below by the statement pipeline.

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

open Matrix
open scoped EllipsoidNotation

/-
Definition 3.57 lies in the chapter's Euclidean ellipsoid / cutting-plane domain.

Sampled owner-style declarations:
- `centerCutEllipsoid` in `Lemma_3_2_7`, the earlier Chapter 3 source-facing owner of the
  half-ellipsoid cut `E₊`;
- `mem_centerCutEllipsoid_iff` in `Lemma_3_2_7`, the canonical companion membership theorem;
- `affineEllipsoid` and `mem_affineEllipsoid_iff` in `Lemma_3_2_7`, the owner/view for the
  ambient ellipsoid `E(H, x̄)`;
- `Matrix.toEuclideanLin` in mathlib, the owner of the matrix action on `EuclideanSpace ℝ (Fin n)`.

Best owner abstraction:
- source-facing/core owner: `centerCutEllipsoid`;
- bridge/view: the textbook sign-reversed inequality `0 ≤ inner ℝ g (xBar - x)`.

Primitive data:
- `H : Mat`;
- `xBar : E`;
- `g : E`.

Derived API:
- the half-ellipsoid `centerCutEllipsoid H xBar g`;
- its canonical membership theorem `mem_centerCutEllipsoid_iff`;
- the textbook reformulation below, obtained by expanding ellipsoid membership and rewriting
  `inner ℝ g (x - xBar) ≤ 0` as `0 ≤ inner ℝ g (xBar - x)`.

Source/core/bridge triage:
- source-facing: the half-ellipsoid `E₊`;
- core/canonical: the existing chapter owner from `Lemma_3_2_7`;
- bridge/view: the expanded textbook membership formula.

This file should therefore reuse the owner directly and keep only the thin bridge needed to match
the textbook phrasing, rather than maintaining a parallel local definition `halfEllipsoid`.
-/

recall centerCutEllipsoid
    (H : Mat) (xBar g : E) :
    Set E

recall mem_centerCutEllipsoid_iff
    {H : Mat} {xBar g x : E} :
    x ∈ E₊(H, xBar, g) ↔
      x ∈ E(H, xBar) ∧ inner ℝ g (x - xBar) ≤ 0

/-- Membership in `E₊` is exactly the defining quadratic inequality for `E(H, x̄)` together with
the textbook halfspace inequality `⟪g, xBar - x⟫ ≥ 0`. -/
theorem mem_centerCutEllipsoid_textbook_iff
    {H : Mat} {xBar g x : E} :
    x ∈ E₊(H, xBar, g) ↔
      inner ℝ (toEuclideanLin H⁻¹ (x - xBar)) (x - xBar) ≤ 1 ∧
        0 ≤ inner ℝ g (xBar - x) := by
  rw [mem_centerCutEllipsoid_iff, mem_affineEllipsoid_iff]
  constructor
  · rintro ⟨hxEll, hxCut⟩
    refine ⟨hxEll, ?_⟩
    simpa [inner_sub_right, sub_nonneg] using hxCut
  · rintro ⟨hxEll, hxCut⟩
    refine ⟨hxEll, ?_⟩
    simpa [inner_sub_right, sub_nonneg] using hxCut
