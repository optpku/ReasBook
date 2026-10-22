/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Theorem_2_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open unitInterval

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

/-- ProofStep 2.7.7: for a finite open cover by path-connected open subsets that is closed under
finite intersections and contains the common basepoint `x`, one can choose for each `y : X` a
path from `x` to `y` such that whenever `y ∈ O i`, the chosen path is entirely contained in
`O i`. -/
-- Proof sketch: for each `y`, the family of cover members containing `y` is nonempty by the cover
-- assumption and finite because the cover is finite. Closure under finite intersections therefore
-- produces a member `O j` equal to the intersection of all those cover members. Since `x` belongs
-- to every `O i`, both `x` and `y` lie in `O j`; path connectedness of `O j` gives a path from
-- `x` to `y` inside `O j`, hence inside every cover member containing `y`.
theorem exists_cover_compatible_basepoint_paths
    (O : ι → TopologicalSpace.Opens X)
    [Finite ι]
    (hO : TopologicalSpace.IsOpenCover O)
    (x : X) (hx : ∀ i, x ∈ O i)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    ∃ γ : ∀ y : X, Path x y,
      ∀ (i : ι) (y : X), y ∈ O i → ∀ t : I, γ y t ∈ O i := by
  classical
  letI := Fintype.ofFinite ι
  let coverAt : X → Finset ι := fun y ↦ Finset.univ.filter fun i ↦ y ∈ O i
  have coverAt_nonempty : ∀ y, (coverAt y).Nonempty := fun y ↦ by
    obtain ⟨i, hi⟩ := hO.exists_mem y
    exact ⟨i, by simp [coverAt, hi]⟩
  let center : X → ι := fun y ↦ Classical.choose (hinter (coverAt y) (coverAt_nonempty y))
  have center_eq : ∀ y, (coverAt y).inf' (coverAt_nonempty y) O = O (center y) := fun y ↦
    Classical.choose_spec (hinter (coverAt y) (coverAt_nonempty y))
  have center_mem : ∀ y, y ∈ O (center y) := fun y ↦ by
    have hy : y ∈ (coverAt y).inf' (coverAt_nonempty y) O := by
      rw [Finset.inf'_eq_inf]
      change y ∈ (((coverAt y).inf O : TopologicalSpace.Opens X) : Set X)
      rw [TopologicalSpace.Opens.coe_finset_inf]
      simp [coverAt]
    simpa [center_eq y] using hy
  have center_le : ∀ {i y}, y ∈ O i → O (center y) ≤ O i := by
    intro i y hyi
    have hi : i ∈ coverAt y := by simp [coverAt, hyi]
    have hle : (coverAt y).inf' (coverAt_nonempty y) O ≤ O i := by
      rw [Finset.inf'_eq_inf]
      exact Finset.inf_le hi
    simpa [center_eq y] using hle
  let γ : ∀ y : X, Path x y := fun y ↦
    letI := hpath (center y)
    (PathConnectedSpace.somePath ⟨x, hx (center y)⟩ ⟨y, center_mem y⟩).map continuous_subtype_val
  refine ⟨γ, ?_⟩
  intro i y hyi t
  have hγ : γ y t ∈ O (center y) := by
    simp [γ]
  exact center_le hyi hγ
