/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.64: in a metric space, the open ball of center `x` and positive radius `ρ` is the
canonical set `Metric.ball x ρ`; the closed ball and the open-ball description of the induced
metric topology are recalled by the companion canonical API below. -/
recall Metric.ball {α : Type u} [PseudoMetricSpace α] (x : α) (ε : ℝ) : Set α

/- Closed balls in a metric space are formalized by the canonical set `Metric.closedBall x ρ`. -/
recall Metric.closedBall {α : Type u} [PseudoMetricSpace α] (x : α) (ε : ℝ) : Set α

/- Membership in an open ball is characterized by the textbook inequality `dist x y < ρ`. -/
recall Metric.mem_ball' {α : Type u} [PseudoMetricSpace α] {x y : α} {ε : ℝ} :
    y ∈ Metric.ball x ε ↔ dist x y < ε

/- Membership in a closed ball is characterized by the textbook inequality `dist x y ≤ ρ`. -/
recall Metric.mem_closedBall' {α : Type u} [PseudoMetricSpace α] {x y : α} {ε : ℝ} :
    y ∈ Metric.closedBall x ε ↔ dist x y ≤ ε

/- The metric topology on a metric space is characterized by the open-ball basis
`Metric.isOpen_iff`. -/
recall Metric.isOpen_iff {α : Type u} [PseudoMetricSpace α] {s : Set α} :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s
