import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tooling was unavailable in this environment: `tool_search` exposed no deferred
-- Lean search tools such as `lean_leansearch`, so this file uses mathlib's `Quiver.Path`,
-- additive path weights, and local explicit predicates for circuits and bounded shortest paths.

open Quiver
open Quiver.Path

universe u v

namespace Quiver.Path

/-- A closed quiver path is a circuit when it is nonempty and does not repeat a vertex away from
its basepoint. -/
def IsCircuit
    {V : Type u} [Quiver V] {v : V}
    (P : Path v v) : Prop :=
  P.length ≠ 0 ∧ List.Nodup P.vertices.tail

/-- A path is shortest among all paths with at most `k` arcs when it satisfies the arc bound and
no competing path with at most `k` arcs has smaller additive length. -/
def IsShortestPathOfCardinalityAtMost
    {V : Type u} [Quiver V]
    {R : Type v} [Preorder R] [AddMonoid R]
    {s t : V}
    (P : Path s t)
    (ℓ : ∀ {u v : V}, (u ⟶ v) → R)
    (k : ℕ) : Prop :=
  P.length ≤ k ∧
    ∀ Q : Path s t,
      Q.length ≤ k → addWeight ℓ P ≤ addWeight ℓ Q

end Quiver.Path

namespace Quiver

/-- A weighted quiver has no negative-length circuit if every circuit has nonnegative additive
length. -/
def HasNoNegativeLengthCircuit
    {V : Type u} [Quiver V]
    {R : Type v} [Preorder R] [AddMonoid R]
    (ℓ : ∀ {u v : V}, (u ⟶ v) → R) : Prop :=
  ∀ ⦃v : V⦄ (P : Path v v),
    P.IsCircuit → 0 ≤ addWeight ℓ P

end Quiver

namespace Digraph

variable {V : Type u}

/-- The canonical edge type of a digraph, viewed as quiver arrows. -/
abbrev Edge (D : Digraph V) (u v : V) :=
  PLift (D.Adj u v)

/-- The canonical quiver underlying a digraph. -/
abbrev toQuiver (D : Digraph V) : Quiver V where
  Hom u v := D.Edge u v

/-- The directed-path type of a digraph, via its canonical quiver view. -/
abbrev Path (D : Digraph V) (u v : V) :=
  @Quiver.Path V D.toQuiver u v

/-- A closed directed path in a digraph is a circuit when it is one in the canonical quiver view. -/
abbrev Path.IsCircuit {D : Digraph V} {u : V} (P : D.Path u u) : Prop :=
  @Quiver.Path.IsCircuit V D.toQuiver u P

/-- The additive length of a directed digraph path, computed in the canonical quiver view. -/
abbrev Path.addWeight
    {R : Type v} [AddMonoid R]
    {D : Digraph V} {u v : V}
    (P : D.Path u v)
    (ℓ : ∀ {x y : V}, D.Edge x y → R) : R :=
  @Quiver.Path.addWeight V D.toQuiver R _ ℓ _ _ P

/-- A weighted digraph has no negative-length circuit when its canonical quiver view does. -/
def HasNoNegativeLengthCircuit
    {R : Type v} [Preorder R] [AddMonoid R]
    (D : Digraph V)
    (ℓ : ∀ {u v : V}, D.Edge u v → R) : Prop :=
  ∀ ⦃v : V⦄ (P : D.Path v v),
    P.IsCircuit → 0 ≤ P.addWeight ℓ

end Digraph

/-- Helper for Remark 4.13: if a path obtained by appending one final arc has cardinality at most
`k`, then its prefix has cardinality at most `k - 1`. -/
lemma prefix_length_le_pred_of_cons_bound
    {V : Type u} [Quiver V]
    {k : ℕ}
    {s u v : V}
    (P' : Path s u)
    (uv : u ⟶ v)
    (h_cons : (P'.cons uv).length ≤ k) :
    P'.length ≤ k - 1 := by
  -- Rewriting the appended path length exposes the single nat-arithmetic step.
  have hsucc : P'.length.succ ≤ k := by
    simpa using h_cons
  exact Nat.le_pred_of_lt (Nat.lt_of_succ_le hsucc)

/-- Helper for Remark 4.13: appending one fixed final arc preserves the cardinality bound when the
prefix already has cardinality at most `k - 1`. -/
lemma cons_length_le_of_pred_bound
    {V : Type u} [Quiver V]
    {k : ℕ}
    {s u v : V}
    (Q : Path s u)
    (uv : u ⟶ v)
    (hk : 0 < k)
    (hQ : Q.length ≤ k - 1) :
    (Q.cons uv).length ≤ k := by
  -- Positivity of `k` turns the predecessor bound into the expected successor bound.
  have hsucc : Q.length.succ ≤ k := by
    exact Nat.succ_le_of_lt <| lt_of_le_of_lt hQ <| Nat.sub_lt hk (by simp)
  simpa using hsucc

/-- Helper for Remark 4.13: if two paths ending with the same final arc are ordered by additive
weight, then their prefixes are ordered by additive weight as well. -/
lemma prefix_weight_le_of_appended_weight_le
    {V : Type u} [Quiver V]
    {R : Type v} [AddCommMonoid R] [Preorder R] [IsOrderedCancelAddMonoid R]
    (ℓ : ∀ {x y : V}, (x ⟶ y) → R)
    {s u v : V}
    (P' Q : Path s u)
    (uv : u ⟶ v)
    (h_cons : addWeight ℓ (P'.cons uv) ≤ addWeight ℓ (Q.cons uv)) :
    addWeight ℓ P' ≤ addWeight ℓ Q := by
  -- Expanding both additive weights leaves the same final-edge contribution on each side.
  rw [addWeight_cons, addWeight_cons] at h_cons
  exact IsOrderedCancelAddMonoid.le_of_add_le_add_right (ℓ uv) _ _ h_cons

/-- Remark 4.13. If `k ∈ {1, ..., n - 1}`, `P = P'.cons uv` is an `s,v`-path of cardinality at
most `k` with minimum length among all `s,v`-paths of cardinality at most `k`, then the prefix
`P'` is an `s,u`-path of minimum length among all `s,u`-paths of cardinality at most `k - 1`.

In this quiver-path formalization, the source's ambient upper bound on `k` and no-negative-circuit
hypothesis are redundant for the prefix-optimality conclusion, and the lower bound `1 ≤ k` follows
from the path shape `P'.cons uv` together with the boundedness hypothesis. -/
theorem prefix_of_bounded_shortest_path_is_bounded_shortest_path
    {V : Type u} [Quiver V]
    {R : Type v} [AddCommMonoid R] [Preorder R] [IsOrderedCancelAddMonoid R]
    (ℓ : ∀ {x y : V}, (x ⟶ y) → R)
    {k : ℕ}
    {s u v : V}
    (P' : Path s u)
    (uv : u ⟶ v)
    (hP : (P'.cons uv).IsShortestPathOfCardinalityAtMost ℓ k) :
    P'.IsShortestPathOfCardinalityAtMost ℓ (k - 1) := by
  rcases hP with ⟨hP_length, hP_shortest⟩
  have hk : 0 < k := by
    have hlen : 0 < (P'.cons uv).length := by
      simp
    exact lt_of_lt_of_le hlen hP_length
  refine ⟨?_, ?_⟩
  · -- The bound on `P'.cons uv` immediately yields the shorter bound for the prefix.
    exact prefix_length_le_pred_of_cons_bound P' uv hP_length
  · intro Q hQ_length
    -- Append the same final arc to compare two `s,v` competitors with the original optimality.
    have hQ_cons_length : (Q.cons uv).length ≤ k := by
      exact cons_length_le_of_pred_bound Q uv hk hQ_length
    have h_cons_weight :
        addWeight ℓ (P'.cons uv) ≤ addWeight ℓ (Q.cons uv) := by
      exact hP_shortest (Q.cons uv) hQ_cons_length
    -- Cancelling the common final-edge contribution recovers the desired prefix comparison.
    exact prefix_weight_le_of_appended_weight_le ℓ P' Q uv h_cons_weight
