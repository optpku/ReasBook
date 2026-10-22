/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_13_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

/-!
Primary domain: combinatorial group theory via locally finite locally convex graphs and
vertex-transitive graph automorphism actions.

Layer triage:
- `source-facing`: a locally finite locally convex graph `Γ`, a group `G` acting transitively on
  its vertices by graph automorphisms, and the finite presentability of one vertex stabilizer.
- `core/canonical`: `SimpleGraph`, `SimpleGraph.Iso`, `SimpleGraph.LocallyFinite`,
  `SimpleGraph.dist`, `PseudoMetricSpace`, `IsIsometricSMul`, `MulAction.stabilizer`,
  `MulAction.IsPretransitive`, and `Group.IsFinitelyPresented`.
- `bridge/view`: `SimpleGraph.IsLocallyConvex` below records the source geodesic-ball convexity
  condition, while the induced vertex action from `ρ : G →* (Γ ≃g Γ)` is expressed canonically by
  `MulAction.compHom V ρ` together with the owner subgroup `MulAction.stabilizer`.

Domain sampling:
1. `SimpleGraph` is mathlib's canonical owner for an undirected incidence graph.
2. `SimpleGraph.Iso` is mathlib's owner abstraction for graph automorphisms.
3. `SimpleGraph.LocallyFinite` and `SimpleGraph.dist` are the canonical owners for finite valence
   and graph metric structure.
4. `PseudoMetricSpace` and `IsIsometricSMul` are the canonical owners for the metric and
   isometric-action layers used by Proposition `3-13-1`.
5. `MulAction.compHom`, `MulAction.stabilizer`, and `Group.IsFinitelyPresented` are the canonical
   owners for the induced vertex action, its stabilizer, and the conclusion.

Primitive vs. derived:
- primitive public data: the graph `Γ`, the graph-isomorphism action `ρ`, and the local convexity
  hypothesis on graph balls;
- derived API: connectedness forced by local convexity, the canonical induced action
  `MulAction.compHom V ρ` on vertices, the stabilizer of a chosen vertex for that action, finite
  closed graph balls in the connected case, bounded descending paths in balls, and the graph-metric
  form of Behr's descending-path condition.
-/

section

open MulAction
open scoped BehrDistance

variable {G : Type u} {V : Type v} [Group G]

namespace SimpleGraph

/-- A graph is locally convex when every closed graph-metric ball is geodesically convex: any two
vertices of the ball are joined by a shortest walk that stays inside the same ball. -/
def IsLocallyConvex (Γ : SimpleGraph V) : Prop :=
  ∀ v : V,
    ∀ l : ℕ,
      ∀ ⦃p q : V⦄,
        p ∈ S[Γ.dist](v, l) →
          q ∈ S[Γ.dist](v, l) →
            ∃ r : Γ.Walk p q,
              r.length = Γ.dist p q ∧
                ∀ w ∈ r.support, w ∈ S[Γ.dist](v, l)

variable (Γ : SimpleGraph V)

/-- Local convexity already forces connectedness on a nonempty graph: for any `p q`, the
radius-`Γ.dist p q` ball around `p` contains both endpoints, hence contains a shortest walk from
`p` to `q`. -/
theorem IsLocallyConvex.connected [Nonempty V] (hconvex : Γ.IsLocallyConvex) : Γ.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨v, fun w ↦ ?_⟩
  have hv : v ∈ S[Γ.dist](v, Γ.dist v w) := by
    simp [mem_integerClosedBall]
  have hw : w ∈ S[Γ.dist](v, Γ.dist v w) := by
    simp [mem_integerClosedBall]
  obtain ⟨r, -, -⟩ :
      ∃ r : Γ.Walk v w,
        r.length = Γ.dist v w ∧
          ∀ x ∈ r.support, x ∈ S[Γ.dist](v, Γ.dist v w) :=
    hconvex v (Γ.dist v w) hv hw
  exact r.reachable

-- Proof sketch: in a connected graph every vertex of the closed ball is reachable from the
-- center, so `SimpleGraph.dist` no longer sees the off-component junk value `0`. Induct on the
-- radius: the ball of radius `0` is `{v}`, and a vertex at radius at most `l + 1` is either
-- already in the radius-`l` ball or adjacent to a vertex there. Local finiteness makes the
-- resulting neighbor union finite.
/-- Every closed ball in a connected locally finite graph is finite. -/
theorem graphClosedBall_finite_of_locallyFinite_of_connected [Γ.LocallyFinite]
    (hconn : Γ.Connected) (v : V) (l : ℕ) :
    (S[Γ.dist](v, l)).Finite := sorry

-- Proof sketch: choose the geodesic inside the ball from the local-convexity hypothesis. Along a
-- shortest path, each successive step moves to an adjacent vertex and reduces the remaining graph
-- distance to the endpoint by exactly `1`, so this path witnesses condition `(II)` of Proposition
-- `3-13-1` with `k = 1`.
/-- Local convexity gives Behr's bounded descending-path condition with step bound `1`. -/
theorem hasBoundedDescendingPathInBall_of_isLocallyConvex
    (hconvex : Γ.IsLocallyConvex) (v : V) (l : ℕ) {p q : V}
    (hp : p ∈ S[Γ.dist](v, l))
    (hq : q ∈ S[Γ.dist](v, l)) :
    HasBoundedDescendingPathInBall Γ.dist 1 v l p q := sorry

namespace Iso

variable {Γ : SimpleGraph V} {G : Type u} [Group G]

/-- A source-facing transitivity hypothesis for `ρ` yields the canonical `IsPretransitive`
instance on the induced action `MulAction.compHom V ρ`. -/
theorem isPretransitive_compHom (ρ : G →* (Γ ≃g Γ))
    (htrans : ∀ p q : V, ∃ g : G, (ρ g) p = q) :
    letI := MulAction.compHom V ρ
    MulAction.IsPretransitive G V := by
  letI := MulAction.compHom V ρ
  exact ⟨fun p q ↦ by
    obtain ⟨g, hg⟩ := htrans p q
    exact ⟨g, hg⟩⟩

-- Proof sketch: a graph isomorphism sends walks to walks of the same length in both directions,
-- hence preserves reachability and the infimum of walk lengths that defines the graph metric.
/-- A graph automorphism preserves the graph metric. -/
theorem dist_eq (σ : Γ ≃g Γ) (p q : V) :
    Γ.dist (σ p) (σ q) = Γ.dist p q := sorry

end Iso

end SimpleGraph

-- Proof sketch: apply Proposition `3-13-1` to the graph metric `Γ.dist`. Local finiteness gives
-- finite closed balls in the connected case, local convexity gives condition `(II)` with `k = 1`,
-- graph automorphisms preserve graph distance, and the transitivity hypothesis is stated for the
-- action induced by `ρ`. The stabilizer hypothesis is exactly the finite presentability of one
-- vertex stabilizer for that induced action.
/-- Proposition 3-13-2: if a locally finite locally convex graph `Γ` admits a vertex-transitive
action of `G` by graph automorphisms, then finite presentability of one vertex stabilizer implies
finite presentability of `G`. The action is given through the canonical owner
`G →* (Γ ≃g Γ)` of graph automorphisms. -/
theorem isFinitelyPresented_of_finitelyPresented_stabilizer_of_locallyFinite_locallyConvex_graph
    (Γ : SimpleGraph V)
    [Γ.LocallyFinite]
    (hconvex : Γ.IsLocallyConvex)
    (ρ : G →* (Γ ≃g Γ))
    (v0 : V)
    (htrans : ∀ p q : V, ∃ g : G, (ρ g) p = q)
    (hstab : letI : MulAction G V := MulAction.compHom V ρ
      Group.IsFinitelyPresented (stabilizer G v0)) :
    Group.IsFinitelyPresented G := by
  letI : Nonempty V := ⟨v0⟩
  letI : MulAction G V := MulAction.compHom V ρ
  letI : PseudoMetricSpace V := {
    dist := fun x y ↦ Γ.dist x y
    dist_self := by intro x; simp [SimpleGraph.dist_self]
    dist_comm := by intro x y; simp [SimpleGraph.dist_comm]
    dist_triangle := by
      intro x y z
      have h : Γ.dist x z ≤ Γ.dist x y + Γ.dist y z := hconvex.connected.dist_triangle
      exact_mod_cast h
  }
  letI : IsIsometricSMul G V :=
    IsIsometricSMul.mk fun g ↦ by
      refine Isometry.of_dist_eq fun p q ↦ ?_
      change (Γ.dist ((ρ g) p) ((ρ g) q) : ℝ) = (Γ.dist p q : ℝ)
      exact congrArg (fun n : ℕ ↦ (n : ℝ)) ((ρ g).dist_eq p q)
  exact
    isFinitelyPresented_of_finitelyPresented_stabilizer_of_behr_distance_action
      Γ.dist
      (fun _ _ ↦ rfl)
      (fun v l _ ↦ Γ.graphClosedBall_finite_of_locallyFinite_of_connected hconvex.connected v l)
      (by
        refine ⟨1, le_rfl, ?_⟩
        intro v l _ p q hp hq
        exact Γ.hasBoundedDescendingPathInBall_of_isLocallyConvex hconvex v l hp hq)
      v0
      (SimpleGraph.Iso.isPretransitive_compHom ρ htrans)
      (by simpa using hstab)

end
end
