/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

universe u v

open List Quiver

-- Layer triage:
-- `source-facing`: cyclic permutations of a loop, cyclic paths, reduced paths, and cyclically
-- reduced loops in a `1`-complex.
-- `core/canonical`: `Quiver.Path` is the owner abstraction for finite composable edge sequences,
-- `Quiver.Total` is the owner abstraction for arrows remembered together with their endpoints,
-- and `Cycle.Chain` is the canonical owner predicate for cyclic adjacency on the rotation
-- quotient of total arrows.
-- `bridge/view`: a loop presents a cyclic path by forgetting its basepoint and retaining only its
-- cyclically ordered edge sequence, while path decomposition via `Quiver.Path.comp` expresses the
-- source-facing cyclic-permutation relation on representatives.
-- Domain sampling:
-- 1. `Quiver.Path` is the canonical owner for finite composable paths.
-- 2. `Quiver.Total` is mathlib's canonical type of arrows together with their source and target.
-- 3. `Cycle α` is mathlib's canonical rotation quotient of lists, with `Cycle.Chain` the owner
--    predicate for cyclic adjacency conditions.
-- 4. `Quiver.Path.comp`, together with `List.IsRotated`, is the bridge from a based loop to its
--    intrinsic cyclic edge sequence.

namespace Quiver.Total

variable {V : Type u} [Quiver.{v} V]

/-- Two total arrows are composable when the target of the first equals the source of the
second. -/
def Composable (e f : Total V) : Prop :=
  e.right = f.left

/-- Reversing a total arrow swaps its endpoints and reverses the arrow. -/
def reverse [Quiver.HasReverse V] (e : Total V) : Total V :=
  match e with
  | ⟨a, b, f⟩ => ⟨b, a, Quiver.reverse f⟩

/-- A pair of consecutive total arrows is reduced when the second is not the inverse of the first.
This is the primitive local relation underlying reduced and cyclically reduced paths. -/
def IsReducedPair [Quiver.HasInvolutiveReverse V] (e f : Total V) : Prop :=
  f ≠ reverse e

@[simp] theorem left_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).left = e.right := by
  cases e
  rfl

@[simp] theorem right_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).right = e.left := by
  cases e
  rfl

@[simp] theorem hom_reverse [Quiver.HasReverse V] (e : Total V) :
    (reverse e).hom = Quiver.reverse e.hom := by
  cases e
  rfl

@[simp] theorem composable_reverse_reverse [Quiver.HasReverse V] (e f : Total V) :
    Composable (reverse e) (reverse f) ↔ Composable f e := by
  cases e
  cases f
  exact eq_comm

end Quiver.Total

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V]

/-- A loop is a path whose initial and terminal vertices coincide. -/
abbrev Loop (V : Type u) [Quiver.{v} V] :=
  Σ a : V, Path a a

/-- The ordered list of edges traversed by a path. -/
def edgeList {a b : V} (p : Path a b) : List (Total V) :=
  match p with
  | .nil => []
  | .cons q e => edgeList q ++ [⟨_, _, e⟩]

/-- Edge lists turn path concatenation into list concatenation. -/
@[simp] private theorem edgeList_comp {a b c : V} (p : Path a b) (q : Path b c) :
    edgeList (p.comp q) = edgeList p ++ edgeList q := by
  induction q with
  | nil =>
      rw [Path.comp_nil]
      simp [edgeList]
  | cons q e ih =>
      simpa [edgeList, List.append_assoc] using
        congrArg (fun L ↦ L ++ [⟨_, _, e⟩]) ih

/-- Every edge in the head position of an edge list starts at the initial vertex of the path. -/
private theorem left_eq_of_mem_head?_edgeList {a b : V} (p : Path a b) :
    ∀ e ∈ (edgeList p).head?, e.left = a := by
  induction p with
  | nil =>
      intro e h
      simp [edgeList] at h
  | cons p e ih =>
      intro f hf
      cases p with
      | nil =>
          have hf' : ⟨a, _, e⟩ = f := by
            simpa [Option.mem_def, edgeList] using hf
          cases hf'
          rfl
      | cons p' e' =>
          have hf' : f ∈ (edgeList (Path.cons p' e')).head? := by
            simpa [edgeList] using hf
          exact ih _ hf'

/-- Every edge in the last position of an edge list ends at the terminal vertex of the path. -/
private theorem right_eq_of_mem_getLast?_edgeList {a b : V} (p : Path a b) :
    ∀ e ∈ (edgeList p).getLast?, e.right = b := by
  induction p with
  | nil =>
      intro e h
      simp [edgeList] at h
  | cons p e ih =>
      intro f hf
      have hf' : ⟨_, _, e⟩ = f := by
        simpa [Option.mem_def, edgeList] using hf
      cases hf'
      rfl

/-- The ordered edge list of a path is composable in the usual linear sense. -/
private theorem edgeList_isChain {a b : V} (p : Path a b) :
    (edgeList p).IsChain Total.Composable := by
  induction p with
  | nil =>
      simp [edgeList]
  | cons p e ih =>
      refine ih.append ?_ ?_
      · simp
      · intro f hf g hg
        have hg' : ⟨_, _, e⟩ = g := by
          simpa [Option.mem_def] using hg
        cases hg'
        simpa [Total.Composable] using right_eq_of_mem_getLast?_edgeList p f hf

/-- The edge list of a loop is a cyclically composable list of total arrows. -/
private theorem edgeList_chain {a : V} (p : Path a a) :
    (edgeList p : Cycle (Total V)).Chain Total.Composable := by
  by_cases hp : edgeList p = []
  · simp [hp]
  · rcases List.exists_cons_of_ne_nil hp with ⟨e, l, hl⟩
    rw [hl, Cycle.chain_coe_cons]
    have hchain : (e :: l).IsChain Total.Composable := hl ▸ edgeList_isChain p
    refine hchain.append ?_ ?_
    · simp
    · intro f hf g hg
      have hg' : e = g := by
        simpa [Option.mem_def] using hg
      cases hg'
      have hf' : f ∈ (edgeList p).getLast? := by simpa [hl] using hf
      have hr : f.right = a := right_eq_of_mem_getLast?_edgeList p f hf'
      have hl' : e.left = a := by
        have he : e ∈ (edgeList p).head? := by
          exact hl ▸ by simp [Option.mem_def]
        exact left_eq_of_mem_head?_edgeList p e he
      simp [Total.Composable, hr, hl']

/-- Two loops differ by a cyclic permutation when one is obtained from the other by cutting it
into two composable pieces and reassembling them in the opposite order. -/
def IsCyclicPermutation (p q : Loop V) : Prop :=
  ∃ p₁ : Path p.1 q.1, ∃ p₂ : Path q.1 p.1,
    p.2 = p₁.comp p₂ ∧ q.2 = p₂.comp p₁

/-- The owner type of cyclic paths is the subtype of cyclic total-edge data satisfying the
canonical cyclic composability condition. -/
abbrev CyclicPath (V : Type u) [Quiver.{v} V] :=
  { c : Cycle (Total V) // c.Chain Total.Composable }

/-- Definition 3-2-3 (1): the cyclic path determined by a loop is its cyclically ordered edge
sequence, with the basepoint forgotten. -/
abbrev cyclicPath (p : Loop V) : CyclicPath V :=
  ⟨edgeList p.2, edgeList_chain p.2⟩

/-- A cyclic permutation of a loop preserves the underlying cyclic path. -/
theorem cyclicPath_eq_of_isCyclicPermutation {p q : Loop V} (h : IsCyclicPermutation p q) :
    cyclicPath p = cyclicPath q := by
  rcases h with ⟨p₁, p₂, hp, hq⟩
  apply Subtype.ext
  apply Cycle.coe_eq_coe.2
  rw [hp, hq, edgeList_comp, edgeList_comp]
  exact List.isRotated_append

section

variable [Quiver.HasInvolutiveReverse V]

/-- Definition 3-2-3 (2): a path is reduced when no consecutive pair of edges is of the form
`e, e⁻¹`. -/
def IsReduced {a b : V} (p : Path a b) : Prop :=
  (edgeList p).IsChain Total.IsReducedPair

/-- A cyclic path is cyclically reduced when no adjacent pair of cyclically consecutive edges is
of the form `e, e⁻¹`. -/
def IsCyclicallyReducedCycle (c : CyclicPath V) : Prop :=
  c.1.Chain Total.IsReducedPair

/-- Definition 3-2-3 (3): a loop is cyclically reduced when its underlying cyclic path is. -/
def IsCyclicallyReduced (p : Loop V) : Prop :=
  IsCyclicallyReducedCycle (cyclicPath p)

/-- For a based loop, the cyclic condition recovers the textbook reduced-plus-endpoint form. -/
theorem isCyclicallyReduced_iff (p : Loop V) :
    IsCyclicallyReduced p ↔
      IsReduced p.2 ∧
        ∀ e ∈ (edgeList p.2).head?, ∀ f ∈ (edgeList p.2).getLast?, Total.IsReducedPair e f := by
  sorry

end

/-- Definition 3-2-3 (4): a path is simple when its visited vertices do not repeat away from the
possible initial-terminal overlap; equivalently, the initial-vertex list and terminal-vertex list
of its traversed edges are both nodup. -/
def IsSimple {a b : V} (p : Path a b) : Prop :=
  Nodup p.vertices.dropLast ∧ Nodup p.vertices.tail

end Quiver.Path
