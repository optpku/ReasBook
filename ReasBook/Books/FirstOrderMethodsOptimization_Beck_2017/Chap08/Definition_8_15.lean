/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {α : Type u} [PseudoMetricSpace α]

/- Definition 8.15 is `source-facing`: the textbook introduces a property of a sequence relative
to a fixed set, namely that the distance to each point of the set does not increase from one
iterate to the next. The natural owner abstraction is therefore a predicate on `x : ℕ → α` and
`S : Set α`, with a companion bridge to the canonical order-theoretic notion `Antitone` applied to
the distance profile `k ↦ dist (x k) y`. -/

/-- Definition 8.15: a sequence `x` is Fejér monotone with respect to `S` if, for every
`y ∈ S`, the distance from `x (k + 1)` to `y` is at most the distance from `x k` to `y` for all
`k ≥ 0`. -/
def IsFejerMonotoneWithRespectTo (x : ℕ → α) (S : Set α) : Prop :=
  ∀ y ∈ S, ∀ k : ℕ, dist (x (k + 1)) y ≤ dist (x k) y

-- Proof sketch: apply `antitone_nat_of_succ_le` pointwise in `y` to pass from the successor-step
-- inequalities to an antitone distance profile, and recover the displayed successor inequality
-- from antitonicity by evaluating at `k ≤ k + 1`.
/-- The Fejér monotonicity condition is equivalent to saying that, for each `y ∈ S`, the distance
profile `k ↦ dist (x k) y` is antitone. -/
theorem isFejerMonotoneWithRespectTo_iff_antitone_dist
    (x : ℕ → α) (S : Set α) :
    IsFejerMonotoneWithRespectTo x S ↔
      ∀ y ∈ S, Antitone (fun k ↦ dist (x k) y) := by
  constructor
  · intro hFejer y hyS
    -- For a fixed point `y ∈ S`, the textbook's one-step inequality makes the distance profile
    -- nonincreasing along successors, so mathlib upgrades it to an antitone sequence on `ℕ`.
    refine antitone_nat_of_succ_le ?_
    intro k
    exact hFejer y hyS k
  · intro hAntitone y hyS k
    -- Evaluating antitonicity at the successor relation recovers the displayed Fejér inequality.
    exact hAntitone y hyS (Nat.le_succ k)

end
