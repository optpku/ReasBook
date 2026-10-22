/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.20: A topology on a set `Ω` is the canonical mathlib notion
`TopologicalSpace Ω`; its open sets are the sets `s` with `IsOpen s`, and a set is closed exactly
when its complement is open. -/
recall TopologicalSpace

universe u

variable {Ω : Type u} [PseudoMetricSpace Ω] {s : Set Ω}

/- In a metric space, and more generally in a pseudometric space, the canonical local openness
criterion is `Metric.isOpen_iff`: a set is open iff every point of the set lies in some positive
radius open ball contained in the set. -/
recall Metric.isOpen_iff

/-- Textbook reformulation of `Metric.isOpen_iff`: open sets are exactly unions of open balls with
positive radius. -/
theorem isOpen_iff_exists_union_of_metric_balls :
    IsOpen s ↔ ∃ F : Set (Ω × ℝ), (∀ p ∈ F, 0 < p.2) ∧ s = ⋃ p ∈ F, Metric.ball p.1 p.2 := by
  constructor
  · intro hs
    let F : Set (Ω × ℝ) := {p | p.1 ∈ s ∧ 0 < p.2 ∧ Metric.ball p.1 p.2 ⊆ s}
    refine ⟨F, ?_, ?_⟩
    · intro p hp
      exact hp.2.1
    · ext x
      constructor
      · intro hx
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs x hx
        have hpF : (x, r) ∈ F := ⟨hx, hr, hball⟩
        exact Set.mem_biUnion hpF (Metric.mem_ball_self hr)
      · intro hx
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨p, hx⟩
        rw [Set.mem_iUnion] at hx
        rcases hx with ⟨hpF, hxp⟩
        exact hpF.2.2 hxp
  · rintro ⟨F, hFpos, rfl⟩
    exact isOpen_biUnion fun p hp ↦ Metric.isOpen_ball
