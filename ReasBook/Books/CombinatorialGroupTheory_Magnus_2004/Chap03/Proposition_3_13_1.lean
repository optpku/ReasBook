/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory via transitive actions on integer-valued metric spaces.

Layer triage:
- `source-facing`: an integer-valued distance bridge `d` on `V`, its source balls `S_l(v)`, and
  Behr's bounded descending-path condition `(II)`.
- `core/canonical`: `PseudoMetricSpace V`, `IsIsometricSMul G V`, `MulAction.IsPretransitive`,
  `MulAction.stabilizer`, `Relation.ReflTransGen`, and `Group.IsFinitelyPresented`.
- `bridge/view`: `integerClosedBall`, the notation `S[d](v, l)`,
  `HasBoundedDescendingPathsInBall`, and `integerClosedBall_eq_closedBall` connect the source
  integer distance data and Behr's condition `(II)` to the canonical metric closed-ball and
  relation-closure owners.

Primitive vs. derived:
- primitive public data: the integer-valued distance `d`, the step bound `k`, and the ambient
  group action on `V`;
- derived API: the source balls `S[d](v, l)`, the ballwise descending-path predicate
  `HasBoundedDescendingPathsInBall d k v l`, and condition `(II)`, all expressed through the
  canonical relation-closure owner `Relation.ReflTransGen`.

Domain sampling:
1. `PseudoMetricSpace` and `Metric.closedBall` are mathlib's owners for the ambient metric layer.
2. `IsIsometricSMul` is mathlib's owner predicate for distance-preserving scalar actions.
3. `MulAction.IsPretransitive` together with `MulAction.stabilizer` are mathlib's owners for the
   transitivity and vertex-stabilizer layers of the action.
4. `Relation.ReflTransGen` is mathlib's owner abstraction for a finite iterated chain of
   one-step moves, so it is the right core for the bounded descending-path condition and its
   ballwise owner predicate.
-/

section

open MulAction

variable {V : Type u}

/-- The closed radius-`l` ball of the integer-valued distance `d` around `v`. -/
def integerClosedBall (d : V → V → ℕ) (v : V) (l : ℕ) : Set V :=
  {w | d v w ≤ l}

namespace BehrDistance

scoped notation "S[" d "](" v "," l ")" => integerClosedBall d v l

end BehrDistance

open scoped BehrDistance

-- Proof sketch: unfold `integerClosedBall`; its membership predicate is exactly the defining
-- inequality `d v w ≤ l`.
/-- Membership in `integerClosedBall d v l` is exactly the inequality `d v w ≤ l`. -/
@[simp] theorem mem_integerClosedBall (d : V → V → ℕ) (v w : V) (l : ℕ) :
    w ∈ S[d](v, l) ↔ d v w ≤ l :=
  Iff.rfl

/-- When `d` agrees with the ambient metric, the source ball `S[d](v, l)` is the metric closed
ball of radius `l`. -/
theorem integerClosedBall_eq_closedBall [PseudoMetricSpace V]
    (d : V → V → ℕ) (hdist : ∀ v w : V, dist v w = d v w) (v : V) (l : ℕ) :
    S[d](v, l) = Metric.closedBall v l := by
  ext w
  rw [Metric.mem_closedBall', mem_integerClosedBall, hdist, Nat.cast_le]

/-- A bounded descending path from `p` to `q` inside the radius-`l` ball around `v`. -/
def HasBoundedDescendingPathInBall (d : V → V → ℕ) (k : ℕ) (v : V) (l : ℕ) (p q : V) : Prop :=
  Relation.ReflTransGen
    (fun a b ↦ a ∈ S[d](v, l) ∧ b ∈ S[d](v, l) ∧ d a q > d b q ∧ d a b ≤ k)
    p q

/-- Behr's bounded descending-path condition inside the radius-`l` ball around `v`. -/
def HasBoundedDescendingPathsInBall (d : V → V → ℕ) (k : ℕ) (v : V) (l : ℕ) : Prop :=
  ∀ ⦃p q : V⦄, p ∈ S[d](v, l) → q ∈ S[d](v, l) → HasBoundedDescendingPathInBall d k v l p q

/-- Behr's condition `(II)` for the integer-valued distance `d`. -/
def SatisfiesBehrConditionII (d : V → V → ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ ∀ v : V, ∀ l : ℕ, 1 ≤ l → HasBoundedDescendingPathsInBall d k v l

section

variable {G : Type v} [Group G] [MulAction G V] [PseudoMetricSpace V] [IsIsometricSMul G V]

-- Proof sketch: choose a base vertex `v0` and the finite generating set obtained from the finite
-- ball of radius `k` around `v0`; then follow Behr's rewriting argument using the bounded
-- descending-path hypothesis to control relators and deduce a finite presentation of `G` from a
-- finite presentation of the stabilizer `stabilizer G v0`.
/-- Proposition 3-13-1: if `d` is an integer-valued distance whose balls `S_l(v)` are finite for
`l ≥ 1`, if `d` agrees with the ambient metric on `V`, and if the bounded descending-path
condition `(II)` holds, then any transitive isometric action of `G` on `V` has finitely presented
acting group whenever one vertex stabilizer is finitely presented. -/
theorem isFinitelyPresented_of_finitelyPresented_stabilizer_of_behr_distance_action
    (d : V → V → ℕ)
    (hdist : ∀ v w : V, dist v w = d v w)
    (hfinite : ∀ v : V, ∀ l : ℕ, 1 ≤ l → (S[d](v, l)).Finite)
    (hdesc : SatisfiesBehrConditionII d)
    (v0 : V)
    (htrans : MulAction.IsPretransitive G V)
    (hstab : Group.IsFinitelyPresented (stabilizer G v0)) :
    Group.IsFinitelyPresented G := sorry

end
end
