/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Proposition 2.25 is a source-facing compact-parameter value-function statement.

Relevant owner declarations sampled before refining:
* `IsCompact.continuous_sInf`, the owner continuity theorem for compact-section infima
* `IsCompact.exists_sInf_image_eq`, the compact-attainment theorem giving the textbook minimum on
  nonempty fibers
* `IsCompact.exists_sInf_image_eq_and_le`, the sharper compact-attainment theorem with the
  minimizing inequality

Owner abstraction:
* `IsCompact.continuous_sInf`

Primitive data:
* an ambient topological space `X`
* the compact set `Q : Set X`
* the continuous family `φ : ℝ × Q → ℝ`

Derived API:
* continuity of the profile `t ↦ inf_{x ∈ Q} φ(t, x)`

Source/core/bridge triage:
* source-facing: Proposition 2.25's continuity statement for the compact-section minimum profile
* core/canonical: `IsCompact.continuous_sInf`
* bridge/view: the compact subtype presentation of `Q` and the range
  `Set.range fun x : Q ↦ φ (t, x)`

The file therefore keeps only the source-facing continuity theorem and reuses the owner result
directly, with no parallel local compact-infimum wrapper.
-/

/-- Proposition 2.25: if `Q` is compact and `φ : ℝ × Q → ℝ` is continuous, then the infimum
profile `t ↦ inf_{x ∈ Q} φ(t, x)` is continuous. Applied to a compact subset `Q ⊆ ℝ^n`, this is
the textbook minimum-value function `f^*(t) = min_{x ∈ Q} φ(t, x)`. -/
-- Proof sketch: view the compact set `Q` as a compact subtype and apply the owner theorem
-- `IsCompact.continuous_sInf` on `Set.univ : Set Q`.
theorem continuous_sInf_range_of_isCompact
    {X : Type u} [TopologicalSpace X] {Q : Set X} (hQ : IsCompact Q)
    {φ : ℝ × Q → ℝ} (hφ : Continuous φ) :
    Continuous (fun t ↦ sInf (Set.range fun x ↦ φ (t, x))) := by
  -- Equip the compact subtype `Q` with its canonical compact-space structure.
  let _ : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  -- The owner theorem applies to the compact parameter set `Set.univ : Set Q`.
  simpa [Set.image_univ] using isCompact_univ.continuous_sInf hφ
