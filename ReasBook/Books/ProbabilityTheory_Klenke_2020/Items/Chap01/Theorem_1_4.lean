/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u v

/-- `t` is a disjoint-union decomposition in `A` of the union of the family `s`. -/
structure IsDisjointUnionDecomposition {ι : Type v} {Ω : Type u}
    (A : Set (Set Ω)) (s t : ι → Set Ω) : Prop where
  mem : ∀ i, t i ∈ A
  pairwiseDisjoint : Pairwise fun i j ↦ Disjoint (t i) (t j)
  iUnion_eq : (⋃ i, t i) = ⋃ i, s i

/-- Helper for Theorem 1.4: rewrite a countable intersection as one set difference against a
countable union of tail differences. -/
lemma iInter_eq_head_diff_iUnion_tail_diff {Ω : Type u} (s : ℕ → Set Ω) :
    (⋂ n, s n) = s 0 \ ⋃ n, (s 0 \ s (n + 1)) := by
  ext x
  constructor
  · intro hx
    -- Unpack the intersection so we can isolate the head set and exclude each tail difference.
    have hx' : ∀ n, x ∈ s n := by
      simpa only [mem_iInter] using hx
    refine ⟨hx' 0, ?_⟩
    intro hxUnion
    rcases mem_iUnion.mp hxUnion with ⟨n, hn⟩
    exact hn.2 (hx' (n + 1))
  · intro hx
    rcases hx with ⟨hx0, hxnot⟩
    -- Recover every tail membership by contradiction from the excluded differences.
    have hx' : ∀ n, x ∈ s n := by
      intro n
      cases n with
      | zero => exact hx0
      | succ k =>
          by_contra hmem
          apply hxnot
          exact mem_iUnion.mpr ⟨k, ⟨hx0, hmem⟩⟩
    simpa only [mem_iInter] using hx'

/-- Helper for Theorem 1.4: the canonical disjointed family stays inside a difference-closed family
whenever the original family does. -/
lemma disjointed_mem_of_isDiffClosed {Ω : Type u} {A : Set (Set Ω)} (hA : IsDiffClosed A)
    {ι : Type v} [Preorder ι] [LocallyFiniteOrderBot ι] {s : ι → Set Ω}
    (hs : ∀ i, s i ∈ A) : ∀ i, disjointed s i ∈ A := by
  intro i
  -- The `disjointed` construction is obtained by repeatedly subtracting earlier sets.
  refine disjointedRec (f := s) ?_ (hs i)
  intro t j ht
  exact hA.diff_mem ht (hs j)

/-- Theorem 1.4 (1): A `\`-closed family of sets is `∩`-closed. -/
-- Proof sketch: rewrite `s ∩ t` as `s \ (s \ t)` and apply closure under set difference twice.
theorem isInterClosed_of_isDiffClosed {Ω : Type u} {A : Set (Set Ω)}
    (hA : IsDiffClosed A) : IsInterClosed A := by
  refine ⟨?_⟩
  intro s t hs ht
  -- First form the inner difference `s \ t`, which remains in `A`.
  have hst : s \ t ∈ A := hA.diff_mem hs ht
  -- Then rewrite the intersection in the textbook form `s \ (s \ t)`.
  have hinter : s ∩ t = s \ (s \ t) := by
    ext x
    simp
  rw [hinter]
  exact hA.diff_mem hs hst

/-- Theorem 1.4 (2): A `\`-closed and `σ`-`∪`-closed family of sets is `σ`-`∩`-closed. -/
-- Proof sketch: rewrite `⋂ n, s n` as `s 0 \ ⋃ n, (s 0 \ s (n + 1))` and use the closure
-- assumptions together with part (1).
theorem isCountablyInterClosed_of_isDiffClosed_of_isCountablyUnionClosed {Ω : Type u}
    {A : Set (Set Ω)} (hA : IsDiffClosed A) (hσA : IsCountablyUnionClosed A) :
    IsCountablyInterClosed A := by
  refine ⟨?_⟩
  intro s hs
  -- Rewrite the countable intersection into the textbook difference-of-a-union form.
  rw [iInter_eq_head_diff_iUnion_tail_diff]
  -- The head set belongs to `A`, and so does the countable union of all tail differences.
  refine hA.diff_mem (hs 0) ?_
  refine hσA.iUnion_mem (fun n ↦ s 0 \ s (n + 1)) ?_
  intro n
  exact hA.diff_mem (hs 0) (hs (n + 1))

/-- Theorem 1.4 (3): A countable union of sets in a `\`-closed family can be rewritten using the
canonical disjointed family, which still lies in the family and has the same union. -/
-- Proof sketch: show by repeated use of set-difference closure that each `disjointed s n` lies in
-- `A`, then apply `disjoint_disjointed` and `iUnion_disjointed`.
theorem disjointed_isDisjointUnionDecomposition_of_isDiffClosed {Ω : Type u}
    {A : Set (Set Ω)} (hA : IsDiffClosed A) {s : ℕ → Set Ω} (hs : ∀ n, s n ∈ A) :
    IsDisjointUnionDecomposition A s (disjointed s) := by
  refine { mem := ?_, pairwiseDisjoint := ?_, iUnion_eq := ?_ }
  · -- Repeated differences keep every disjointed layer inside `A`.
    exact disjointed_mem_of_isDiffClosed hA hs
  · -- The canonical disjointed family is pairwise disjoint.
    simpa [Function.onFun] using disjoint_disjointed s
  · -- The disjointed family has the same union as the original family.
    simpa using iUnion_disjointed (f := s)

/-- Theorem 1.4 (4): A finite union of sets in a `\`-closed family can be rewritten as a finite
disjoint union of sets in the same family using the canonical disjointed construction. -/
-- Proof sketch: apply the same disjointization argument to the finite linearly ordered index type
-- `Fin n`, then use `disjoint_disjointed` and `iUnion_disjointed`.
theorem disjointed_isDisjointUnionDecomposition_fin_of_isDiffClosed {Ω : Type u}
    {A : Set (Set Ω)} (hA : IsDiffClosed A) {n : ℕ} {s : Fin n → Set Ω} (hs : ∀ i, s i ∈ A) :
    IsDisjointUnionDecomposition A s (disjointed s) := by
  refine { mem := ?_, pairwiseDisjoint := ?_, iUnion_eq := ?_ }
  · -- The same repeated-difference argument works for finite ordered index types.
    exact disjointed_mem_of_isDiffClosed hA hs
  · -- The finite disjointed family is pairwise disjoint as well.
    simpa [Function.onFun] using disjoint_disjointed s
  · -- Disjointization preserves the union in the finite case too.
    simpa using iUnion_disjointed (f := s)
