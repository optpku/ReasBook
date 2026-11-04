/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_2.ch4_sec4_3_2_remark_4_13

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search note: `lean_leansearch` was unavailable in this session, so this file uses
-- local inspection of mathlib's `Quiver.Path`, `Quiver.Path.addWeightOfEPs`,
-- `SimpleGraph.Path`, `SimpleGraph.Walk`, and `Digraph` APIs.

open Quiver
open Quiver.Path

universe u

variable {V : Type u}

local notation "DPath[" D "]" => @Digraph.Path _ D
local notation "addWeightOfEPs[" D "]" =>
  @Quiver.Path.addWeightOfEPs _ (@Digraph.toQuiver _ D) ℝ inferInstance

private def digraphEdgePath {D : Digraph V} {u v : V} (h : D.Adj u v) : DPath[D] u v :=
  @Quiver.Path.cons V D.toQuiver u u v (@Quiver.Path.nil V D.toQuiver u) ⟨h⟩

/-- The bidirected digraph obtained from an undirected graph by replacing each edge with both
possible arc orientations. -/
def bidirectedDigraph (G : SimpleGraph V) : Digraph V where
  Adj := G.Adj

@[simp]
lemma bidirectedDigraph_toSimpleGraphStrict (G : SimpleGraph V) :
    (bidirectedDigraph G).toSimpleGraphStrict = G := by
  ext u v
  constructor
  · rintro ⟨hneq, huv, _⟩
    exact huv
  · intro huv
    exact ⟨G.ne_of_adj huv, huv, huv.symm⟩

/-- The directed arc lengths induced by an undirected edge-length function. -/
def bidirectedArcLength (ℓ : Sym2 V → ℝ) : V → V → ℝ :=
  fun u v ↦ ℓ (s(u, v))

/-- The length of an undirected path is the sum of the lengths of the edges it uses. -/
def undirectedPathLength (ℓ : Sym2 V → ℝ) {G : SimpleGraph V} {u v : V} (p : G.Path u v) : ℝ :=
  (((p : G.Walk u v).edges).map ℓ).sum

/-- The set of lengths of undirected `s,t`-paths in `G`. -/
def undirectedPathLengths (G : SimpleGraph V) (ℓ : Sym2 V → ℝ) (s t : V) : Set ℝ :=
  {L | ∃ p : G.Path s t, undirectedPathLength ℓ p = L}

/-- The set of lengths of directed `s,t`-walks in the bidirected digraph associated with `G`. -/
def bidirectedWalkLengths (G : SimpleGraph V) (ℓ : Sym2 V → ℝ) (s t : V) : Set ℝ :=
  {L | ∃ p : DPath[bidirectedDigraph G] s t,
      addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p = L}

/-- Helper for Exercise 4.19: a nonnegative sum does not increase when one passes to a
subpermutation of the list. -/
lemma List.sum_le_sum_of_subperm_of_nonneg {α : Type*} (f : α → ℝ) {l₁ l₂ : List α}
    (hsubperm : List.Subperm l₁ l₂) (hnonneg : ∀ a ∈ l₂, 0 ≤ f a) :
    (l₁.map f).sum ≤ (l₂.map f).sum := by
  -- Turn the subpermutation into a sublist after permuting the larger list.
  obtain ⟨l, hperm, hsublist⟩ := List.subperm_iff.mp hsubperm
  have hsublist_map : List.Sublist (l₁.map f) (l.map f) := hsublist.map f
  have hnonneg_map : ∀ x ∈ l.map f, 0 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact hnonneg a (hperm.subset ha)
  calc
    (l₁.map f).sum ≤ (l.map f).sum := hsublist_map.sum_le_sum hnonneg_map
    _ = (l₂.map f).sum := by simpa using hperm.map f |>.sum_eq

/-- Helper for Exercise 4.19: every undirected path has nonnegative length when all edge lengths
in the graph are nonnegative. -/
lemma undirectedPathLength_nonneg {G : SimpleGraph V} (ℓ : Sym2 V → ℝ)
    (hℓ : ∀ e ∈ G.edgeSet, 0 ≤ ℓ e) {u v : V} (p : G.Path u v) :
    0 ≤ undirectedPathLength ℓ p := by
  -- Each edge in the path belongs to `G.edgeSet`, so every summand is nonnegative.
  rw [undirectedPathLength]
  exact List.sum_nonneg fun x hx ↦ by
    rcases List.mem_map.mp hx with ⟨e, he, rfl⟩
    exact hℓ e ((p : G.Walk u v).edges_subset_edgeSet he)

namespace SimpleGraph.Walk

/-- Helper for Exercise 4.19: orient each edge of an undirected walk in the direction in which
the walk traverses it. -/
def toBidirectedPath {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    DPath[bidirectedDigraph G] u v :=
  show (fun u v (_ : G.Walk u v) ↦ DPath[bidirectedDigraph G] u v) _ _ p from
    p.concatRec
      (@Quiver.Path.nil V (bidirectedDigraph G).toQuiver)
      (fun _ h q ↦ @Quiver.Path.cons V (bidirectedDigraph G).toQuiver _ _ _ q ⟨h⟩)

/-- Helper for Exercise 4.19: orienting an undirected walk in the bidirected digraph preserves
its total edge-length sum. -/
lemma addWeightOfEPs_toBidirectedPath_eq {G : SimpleGraph V} (ℓ : Sym2 V → ℝ) {u v : V}
    (p : G.Walk u v) :
    addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p.toBidirectedPath =
      (p.edges.map ℓ).sum := by
  -- The directed and undirected objectives agree edge by edge after orienting the walk.
  letI := (bidirectedDigraph G).toQuiver
  refine
    show (fun u v (p : G.Walk u v) ↦
      addWeightOfEPs (bidirectedArcLength ℓ) (toBidirectedPath p) = (p.edges.map ℓ).sum) _ _ p from
      p.concatRec ?_ ?_
  · intro u
    rw [toBidirectedPath, SimpleGraph.Walk.concatRec_nil, Quiver.Path.addWeightOfEPs_nil]
    rfl
  · intro u v w p h ih
    rw [toBidirectedPath, SimpleGraph.Walk.concatRec_concat, Quiver.Path.addWeightOfEPs_cons]
    simpa [SimpleGraph.Walk.edges_concat, bidirectedArcLength, ih]

/-- Helper for Exercise 4.19: the edge-length sum of `toPath` is bounded by the edge-length sum
of the original walk when all edge lengths are nonnegative. -/
lemma edge_sum_toPath_le_of_nonneg {G : SimpleGraph V} [DecidableEq V]
    (ℓ : Sym2 V → ℝ) (hℓ : ∀ e ∈ G.edgeSet, 0 ≤ ℓ e) {u v : V} (p : G.Walk u v) :
    (((p.toPath : G.Walk u v).edges).map ℓ).sum ≤ (p.edges.map ℓ).sum := by
  -- `toPath` keeps a nodup subpermutation of the original edge list, so the nonnegative sum
  -- can only decrease.
  have hsubperm : List.Subperm ((p.toPath : G.Walk u v).edges) p.edges := by
    exact List.Nodup.subperm (p.toPath.2.1.edges_nodup) p.edges_toPath_subset
  refine List.sum_le_sum_of_subperm_of_nonneg ℓ hsubperm ?_
  intro e he
  exact hℓ e (p.edges_subset_edgeSet he)

end SimpleGraph.Walk

namespace Quiver.Path

/-- Helper for Exercise 4.19: forget the arc orientations in a walk of the bidirected digraph. -/
def toSimpleGraphWalk {G : SimpleGraph V} {u v : V}
    (p : DPath[bidirectedDigraph G] u v) : G.Walk u v :=
  @Quiver.Path.rec V (bidirectedDigraph G).toQuiver u
    (fun v _ ↦ G.Walk u v)
    SimpleGraph.Walk.nil
    (fun _ h q ↦ q.concat h.down)
    v p

/-- Helper for Exercise 4.19: converting a bidirected walk to an undirected walk preserves
its total length. -/
lemma addWeightOfEPs_toSimpleGraphWalk_eq {G : SimpleGraph V} (ℓ : Sym2 V → ℝ) {u v : V}
    (p : DPath[bidirectedDigraph G] u v) :
    addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p =
      ((toSimpleGraphWalk p).edges.map ℓ).sum := by
  -- Follow the walk recursion and rewrite both objective functions edge by edge.
  letI := (bidirectedDigraph G).toQuiver
  induction p with
  | nil =>
      rw [Quiver.Path.addWeightOfEPs_nil]
      simp [toSimpleGraphWalk]
  | cons p h ih =>
      rw [Quiver.Path.addWeightOfEPs_cons]
      rw [ih]
      simp [toSimpleGraphWalk, SimpleGraph.Walk.edges_concat, bidirectedArcLength]

/-- Helper for Exercise 4.19: a bidirected walk shortens to an undirected path of no larger
length when all edges have nonnegative length. -/
lemma toPath_length_le_addWeightOfEPs_of_nonneg {G : SimpleGraph V} [DecidableEq V]
    (ℓ : Sym2 V → ℝ) (hℓ : ∀ e ∈ G.edgeSet, 0 ≤ ℓ e) {u v : V}
    (p : DPath[bidirectedDigraph G] u v) :
    undirectedPathLength ℓ p.toSimpleGraphWalk.toPath ≤
      addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p := by
  -- Route correction: compare the directed walk with the undirected walk obtained by forgetting
  -- orientation, then shorten that walk using `toPath`.
  rw [addWeightOfEPs_toSimpleGraphWalk_eq]
  simpa [undirectedPathLength] using
    SimpleGraph.Walk.edge_sum_toPath_le_of_nonneg ℓ hℓ (toSimpleGraphWalk p)

/-- Helper for Exercise 4.19: every bidirected walk has nonnegative total length when all
undirected edge lengths are nonnegative. -/
lemma addWeightOfEPs_nonneg_of_nonneg {G : SimpleGraph V}
    (ℓ : Sym2 V → ℝ) (hℓ : ∀ e ∈ G.edgeSet, 0 ≤ ℓ e) {u v : V}
    (p : DPath[bidirectedDigraph G] u v) :
    0 ≤ addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p := by
  -- First shorten the walk to a path, then use nonnegativity of path lengths.
  classical
  have hpath :
      0 ≤ undirectedPathLength ℓ p.toSimpleGraphWalk.toPath :=
    undirectedPathLength_nonneg ℓ hℓ p.toSimpleGraphWalk.toPath
  exact hpath.trans (toPath_length_le_addWeightOfEPs_of_nonneg ℓ hℓ p)

end Quiver.Path

/-- Helper for Exercise 4.19: alternate along a fixed undirected edge in the bidirected digraph,
starting at `u` and ending at `v`. -/
def alternatingEdgePath {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    ℕ → DPath[bidirectedDigraph G] u v
  | 0 => digraphEdgePath huv
  | n + 1 =>
      @Quiver.Path.cons V (bidirectedDigraph G).toQuiver _ _ _
        (@Quiver.Path.cons V (bidirectedDigraph G).toQuiver _ _ _
          (alternatingEdgePath huv n) ⟨huv.symm⟩)
        ⟨huv⟩

/-- Helper for Exercise 4.19: the alternating walk traverses the edge `u-v` exactly `2n+1`
times, so its total length is `(2n+1) * ℓ(u,v)`. -/
lemma alternatingEdgePath_addWeightOfEPs {G : SimpleGraph V} (ℓ : Sym2 V → ℝ) {u v : V}
    (huv : G.Adj u v) (n : ℕ) :
    addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) (alternatingEdgePath huv n) =
      ((2 * n + 1 : ℕ) : ℝ) * ℓ (s(u, v)) := by
  -- Unfold one pair of traversals at a time and use the induction hypothesis.
  letI := (bidirectedDigraph G).toQuiver
  induction n with
  | zero =>
      rw [alternatingEdgePath, digraphEdgePath, Quiver.Path.addWeightOfEPs_cons,
        Quiver.Path.addWeightOfEPs_nil]
      simp [bidirectedArcLength]
  | succ n ih =>
      rw [alternatingEdgePath, Quiver.Path.addWeightOfEPs_cons, Quiver.Path.addWeightOfEPs_cons]
      simp [bidirectedArcLength, ih, Sym2.eq_swap]
      ring_nf

/-- Exercise 4.19 (1): if all undirected edge lengths are nonnegative, then replacing every
undirected edge by the two opposite directed arcs yields a directed shortest-walk instance whose
optimal value agrees with the undirected shortest `s,t`-path problem. -/
theorem exercise_4_19_bidirected_reduction
    (G : SimpleGraph V) (ℓ : Sym2 V → ℝ) (s t : V)
    (hℓ : ∀ e ∈ G.edgeSet, 0 ≤ ℓ e) :
    sInf (undirectedPathLengths G ℓ s t) = sInf (bidirectedWalkLengths G ℓ s t) := by
  classical
  let P := undirectedPathLengths G ℓ s t
  let W := bidirectedWalkLengths G ℓ s t
  by_cases hP : P.Nonempty
  · have hW : W.Nonempty := by
      rcases hP with ⟨L, hL⟩
      rcases hL with ⟨p, rfl⟩
      refine ⟨undirectedPathLength ℓ p, ?_⟩
      refine ⟨(p : G.Walk s t).toBidirectedPath, ?_⟩
      simpa [P, W, undirectedPathLength] using
        SimpleGraph.Walk.addWeightOfEPs_toBidirectedPath_eq ℓ (p : G.Walk s t)
    have hP_bdd : BddBelow P := by
      refine ⟨0, ?_⟩
      intro L hL
      rcases hL with ⟨p, rfl⟩
      exact undirectedPathLength_nonneg ℓ hℓ p
    have hW_bdd : BddBelow W := by
      refine ⟨0, ?_⟩
      intro L hL
      rcases hL with ⟨p, rfl⟩
      exact Quiver.Path.addWeightOfEPs_nonneg_of_nonneg ℓ hℓ p
    have hP_glb : IsGLB P (sInf P) := Real.isGLB_sInf hP hP_bdd
    have hW_glb : IsGLB W (sInf W) := Real.isGLB_sInf hW hW_bdd
    apply le_antisymm
    · -- Every directed walk shortens to an undirected path of no larger length.
      refine hW_glb.2 ?_
      intro L hL
      rcases hL with ⟨p, rfl⟩
      have hmemP : undirectedPathLength ℓ p.toSimpleGraphWalk.toPath ∈ P := by
        refine ⟨p.toSimpleGraphWalk.toPath, rfl⟩
      exact (hP_glb.1 hmemP).trans
        (Quiver.Path.toPath_length_le_addWeightOfEPs_of_nonneg ℓ hℓ p)
    · -- Every undirected path is realized exactly as a directed walk in the bidirected digraph.
      refine hP_glb.2 ?_
      intro L hL
      rcases hL with ⟨p, rfl⟩
      have hmemW :
          addWeightOfEPs[bidirectedDigraph G]
              (bidirectedArcLength ℓ) ((p : G.Walk s t).toBidirectedPath) ∈ W := by
        refine ⟨(p : G.Walk s t).toBidirectedPath, rfl⟩
      calc
        sInf W ≤ addWeightOfEPs[bidirectedDigraph G]
            (bidirectedArcLength ℓ) ((p : G.Walk s t).toBidirectedPath) :=
          hW_glb.1 hmemW
        _ = undirectedPathLength ℓ p := by
          simpa [undirectedPathLength] using
            SimpleGraph.Walk.addWeightOfEPs_toBidirectedPath_eq ℓ (p : G.Walk s t)
  · have hP_empty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hP
    have hW_empty : W = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro L hL
      rcases hL with ⟨p, rfl⟩
      have hmemP : undirectedPathLength ℓ p.toSimpleGraphWalk.toPath ∈ P := by
        refine ⟨p.toSimpleGraphWalk.toPath, rfl⟩
      exact hP ⟨_, hmemP⟩
    simp [P, W, hP_empty, hW_empty, Real.sInf_empty]

/-- Exercise 4.19 (2): if some undirected edge has negative length, then the bidirected
construction creates a negative directed 2-cycle, so the directed shortest-walk problem is
unbounded below between the endpoints of that edge. -/
theorem exercise_4_19_negative_lengths_obstruct_reduction
    (G : SimpleGraph V) (ℓ : Sym2 V → ℝ)
    {u v : V} (huv : G.Adj u v) (hneg : ℓ (s(u, v)) < 0) :
    ∀ M : ℝ, ∃ p : DPath[bidirectedDigraph G] u v,
      addWeightOfEPs[bidirectedDigraph G] (bidirectedArcLength ℓ) p < M := by
  intro M
  -- Choose enough back-and-forth traversals of the negative 2-cycle to push the value below `M`.
  let a := ℓ (s(u, v))
  obtain ⟨n, hn⟩ := exists_nat_gt ((-M) / (-(2 * ℓ (s(u, v)))))
  have hden : 0 < -(2 * ℓ (s(u, v))) := by
    nlinarith
  have hmul : -M < (n : ℝ) * (-(2 * ℓ (s(u, v)))) := by
    exact (div_lt_iff₀ hden).mp hn
  have hmain : ((2 : ℝ) * (n : ℝ)) * a < M := by
    dsimp [a] at hmul ⊢
    nlinarith
  have hrewrite : (((2 * n + 1 : ℕ) : ℝ) * a) = ((2 : ℝ) * (n : ℝ)) * a + a := by
    norm_num
    ring
  have hfinal : (((2 * n + 1 : ℕ) : ℝ) * a) < M := by
    rw [hrewrite]
    nlinarith [hmain, hneg]
  refine ⟨alternatingEdgePath huv n, ?_⟩
  rw [alternatingEdgePath_addWeightOfEPs ℓ huv n]
  simpa [a] using hfinal
