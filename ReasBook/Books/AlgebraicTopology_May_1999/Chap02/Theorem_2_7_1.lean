/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

namespace Set.Icc

/-- Compatibility wrapper for the `convexCombo` to `convexComb` API rename. -/
def convexCombo {a b : ℝ} (x y : Icc a b) (t : unitInterval) : Icc a b :=
  convexComb x y t

@[simp] theorem coe_convexCombo {a b : ℝ} (x y : Icc a b) (t : unitInterval) :
    (convexCombo x y t : ℝ) = (1 - t) * x + t * y := rfl

@[simp] theorem convexCombo_zero {a b : ℝ} (x y : Icc a b) :
    convexCombo x y 0 = x := by simp [convexCombo]

@[simp] theorem convexCombo_one {a b : ℝ} (x y : Icc a b) :
    convexCombo x y 1 = y := by simp [convexCombo]

@[simp] theorem convexCombo_eq {a b : ℝ} (x : Icc a b) (t : unitInterval) :
    convexCombo x x t = x := by simp [convexCombo]

theorem le_convexCombo {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    x ≤ convexCombo x y t := by simpa [convexCombo] using le_convexComb h t

theorem convexCombo_le {a b : ℝ} {x y : Icc a b} (h : x ≤ y) (t : unitInterval) :
    convexCombo x y t ≤ y := by simpa [convexCombo] using convexComb_le h t

@[continuity, fun_prop] theorem continuous_convexCombo {a b : ℝ} (x y : Icc a b) :
    Continuous (convexCombo x y) := by
  simpa [convexCombo] using continuous_convexComb x y

@[continuity, fun_prop] theorem continuous_convexCombo_prod {a b : ℝ} :
    Continuous fun x : Icc a b × Icc a b × unitInterval ↦
      convexCombo x.1 x.2.1 x.2.2 := by
  simpa [convexCombo] using (continuous_convexComb_prod (a := a) (b := b))

end Set.Icc

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory CategoryTheory.Limits
open Path.Homotopic.Quotient
open TopologicalSpace.Opens
open unitInterval
open scoped FundamentalGroupoid

noncomputable section

variable {ι : Type v} {X : Type u} [TopologicalSpace X]

namespace TopologicalSpace.IsOpenCover

/-- An indexed open cover is closed under nonempty finite intersections when every nonempty finite
intersection of members of the cover is itself another member of the cover. -/
def ClosedUnderNonemptyFiniteIntersections
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) : Prop :=
  ∀ s : Finset ι, ∀ hs : s.Nonempty, ∃ i, s.inf' hs O = O i

/-- The index category of an indexed open cover, whose morphisms are inclusions between cover
members. -/
abbrev Index (O : ι → TopologicalSpace.Opens (TopCat.of X)) :=
  InducedCategory (TopologicalSpace.Opens (TopCat.of X)) O

end TopologicalSpace.IsOpenCover

/-- The diagram sending each member of an open cover to its fundamental groupoid. -/
abbrev fundamental_groupoid_cover_diagram
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) :
    TopologicalSpace.IsOpenCover.Index O ⥤ Grpd :=
  inducedFunctor O ⋙ toTopCat (TopCat.of X) ⋙ π

/-- Naturality of the canonical inclusion functors from the fundamental groupoids of cover
elements into the fundamental groupoid of the ambient space. -/
-- Proof sketch: unravel a morphism in `TopologicalSpace.IsOpenCover.Index O` as an inclusion
-- `O i ⟶ O j`; the two
-- composites both send a path class in `O i` to the same path class in `X`, so functoriality of
-- `π` identifies them.
theorem fundamental_groupoid_cover_cocone_naturality
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {i j : TopologicalSpace.IsOpenCover.Index O} (f : i ⟶ j) :
    (fundamental_groupoid_cover_diagram O).map f ≫
        πₘ (inclusion' (O j)) =
      πₘ (inclusion' (O i)) := by
  -- First identify the composite inclusion in `TopCat`.
  have hcomp : ((toTopCat (TopCat.of X)).map f.hom) ≫ inclusion' (O j) = inclusion' (O i) := by
    -- Both continuous maps are the subtype inclusion `O i ↪ X`.
    ext x
    rfl
  -- Then functoriality of `π` transports that equality to the induced functors on groupoids.
  change πₘ ((toTopCat (TopCat.of X)).map f.hom) ≫ πₘ (inclusion' (O j)) = πₘ (inclusion' (O i))
  simpa [FundamentalGroupoid.map_comp] using congrArg πₘ hcomp

namespace TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

/-- Helper for Theorem 2.7.1: closure under nonempty finite intersections produces a cover member
realizing the binary overlap of two chosen opens. -/
theorem binary_intersection_member
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (i j : ι) :
    ∃ k, O k = O i ⊓ O j := by
  classical
  -- Apply the finite-intersection hypothesis to the two-element subfamily `{i, j}`.
  obtain ⟨k, hk⟩ := hinter ({i, j} : Finset ι) (by simp)
  -- The resulting finite infimum is exactly the binary intersection.
  refine ⟨k, ?_⟩
  simpa [Finset.inf'_insert, Finset.inf'_singleton] using hk.symm

end TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections

/-- The canonical cocone from the fundamental groupoids of the members of an open cover to the
fundamental groupoid of the ambient space. -/
def fundamental_groupoid_cover_cocone
    (O : ι → TopologicalSpace.Opens (TopCat.of X)) :
    Cocone (fundamental_groupoid_cover_diagram O) where
  pt := πₓ (TopCat.of X)
  ι :=
    { app := fun i ↦ πₘ (inclusion' (O i))
      naturality := fun _ _ f ↦ fundamental_groupoid_cover_cocone_naturality O f }

/-- Helper for Theorem 2.7.1: if a point lies in two chosen members of the cover, then any cocone
over the cover diagram assigns the same object of the target groupoid to that point from either
side of the overlap. -/
theorem cocone_object_eq_of_overlap_point
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {i j : TopologicalSpace.IsOpenCover.Index O} {x : X}
    (hx₁ : x ∈ O i) (hx₂ : x ∈ O j) :
    (S.ι.app i).obj ⟨x, hx₁⟩ = (S.ι.app j).obj ⟨x, hx₂⟩ := by
  classical
  -- Compare both chosen objects through the cover member realizing the binary overlap.
  obtain ⟨k, hk⟩ :=
    TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections.binary_intersection_member
      hinter i j
  have hxk : x ∈ O k := by
    rw [hk]
    exact ⟨hx₁, hx₂⟩
  have fki :=
    InducedCategory.homMk
      (homOfLE (show O k ≤ O i by rw [hk]; exact inf_le_left))
  have fkj :=
    InducedCategory.homMk
      (homOfLE (show O k ≤ O j by rw [hk]; exact inf_le_right))
  -- Naturality identifies the objects coming from the overlap with the objects coming from each
  -- side separately.
  have hwi := Functor.congr_obj (S.w fki) ⟨x, hxk⟩
  have hwj := Functor.congr_obj (S.w fkj) ⟨x, hxk⟩
  change (S.ι.app i).obj (((fundamental_groupoid_cover_diagram O).map fki).obj ⟨x, hxk⟩) =
      (S.ι.app k).obj ⟨x, hxk⟩ at hwi
  change (S.ι.app j).obj (((fundamental_groupoid_cover_diagram O).map fkj).obj ⟨x, hxk⟩) =
      (S.ι.app k).obj ⟨x, hxk⟩ at hwj
  have hmapi :
      ((fundamental_groupoid_cover_diagram O).map fki).obj ⟨x, hxk⟩ = ⟨x, hx₁⟩ := by
    rfl
  have hmapj :
      ((fundamental_groupoid_cover_diagram O).map fkj).obj ⟨x, hxk⟩ = ⟨x, hx₂⟩ := by
    rfl
  have hi : (S.ι.app i).obj ⟨x, hx₁⟩ = (S.ι.app k).obj ⟨x, hxk⟩ := by
    simpa [hmapi] using hwi
  have hj : (S.ι.app j).obj ⟨x, hx₂⟩ = (S.ι.app k).obj ⟨x, hxk⟩ := by
    simpa [hmapj] using hwj
  exact hi.trans hj.symm

/-- Helper for Theorem 2.7.1: choose one cover member containing a given point. -/
noncomputable def chosen_cover_index
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O) (x : X) :
    TopologicalSpace.IsOpenCover.Index O :=
  Classical.choose (hO.exists_mem x)

/-- Helper for Theorem 2.7.1: the chosen cover member produced by `chosen_cover_index` does contain
the original point. -/
theorem mem_chosen_cover_index
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O) (x : X) :
    x ∈ O (chosen_cover_index O hO x) :=
  Classical.choose_spec (hO.exists_mem x)

/-- Helper for Theorem 2.7.1: the object assigned to a point by first choosing one containing cover
member and then applying the corresponding cocone leg. -/
noncomputable abbrev chosen_cover_object
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (x : X) : S.pt :=
  (S.ι.app (chosen_cover_index O hO x)).obj ⟨x, mem_chosen_cover_index O hO x⟩

/-- Helper for Theorem 2.7.1: if a point already lies in a specified cover member, then the chosen
object attached to that point agrees with the object coming from that specified member. -/
theorem chosen_cover_object_eq_of_mem
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {i : TopologicalSpace.IsOpenCover.Index O} {x : X}
    (hx : x ∈ O i) :
    chosen_cover_object O hO S x = (S.ι.app i).obj ⟨x, hx⟩ := by
  -- Compare the chosen containing cover member with the explicitly supplied one on their overlap.
  simpa [chosen_cover_object] using
    cocone_object_eq_of_overlap_point hinter S
      (i := chosen_cover_index O hO x) (j := i)
      (hx₁ := mem_chosen_cover_index O hO x) (hx₂ := hx)

/-- Helper for Theorem 2.7.1: every path admits a finite-cover-compatible monotone partition of the
unit interval, so each subpath lies entirely in a single member of the open cover. -/
theorem path_partition_subordinate_to_open_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∃ t : ℕ → I, t 0 = 0 ∧
      Monotone t ∧
      (∃ n, ∀ m ≥ n, t m = 1) ∧
      ∀ n, ∃ i, Set.range (γ.subpath (t n) (t (n + 1))) ⊆ O i := by
  let c : ι → Set I := fun i ↦ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)
  have hc₁ : ∀ i, IsOpen (c i) := by
    intro i
    exact (O i).isOpen.preimage γ.continuous
  have hc₂ : Set.univ ⊆ ⋃ i, c i := by
    intro s _
    obtain ⟨i, hi⟩ := hO.exists_mem (γ s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  -- Pull the cover back along `γ` and apply the unit-interval subdivision theorem.
  obtain ⟨t, ht0, hmono, hstable, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  refine ⟨t, ht0, hmono, hstable, ?_⟩
  intro n
  obtain ⟨i, hi⟩ := hsub n
  refine ⟨i, ?_⟩
  -- The range description of `subpath` converts interval containment into cover containment.
  rw [Path.range_subpath_of_le γ (t n) (t (n + 1)) (hmono (Nat.le_succ n))]
  intro z hz
  rcases hz with ⟨s, hs, rfl⟩
  exact hi hs

/-- Helper for Theorem 2.7.1: the eventually constant monotone partition supplied by the unit
interval cover lemma can be truncated at its first stable value to obtain finite `Fin`-indexed
subdivision data for the path. -/
theorem path_subdivision_data_of_open_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∃ n : ℕ, ∃ t : Fin (n + 1) → I,
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      Monotone t ∧
      ∃ u : Fin n → ι,
        ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k) := by
  let c : ι → Set I := fun i ↦ (fun s : I ↦ γ s) ⁻¹' (O i : Set X)
  have hc₁ : ∀ i, IsOpen (c i) := by
    -- Pull the cover back along the path.
    intro i
    exact (O i).isOpen.preimage γ.continuous
  have hc₂ : Set.univ ⊆ ⋃ i, c i := by
    -- Every point of the path lies in some cover member because `O` covers `X`.
    intro s _
    obtain ⟨i, hi⟩ := hO.exists_mem (γ s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, hstable, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc₁ hc₂
  obtain ⟨n, hn⟩ := hstable
  have hmono_fin : Monotone (fun k : Fin (n + 1) ↦ t k.1) := by
    -- Restricting a monotone sequence along `Fin` preserves monotonicity.
    intro a b hab
    exact hmono hab
  have hsub_fin : ∀ k : Fin n, ∃ i, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O i := by
    -- Convert interval containment in the pullback cover into range containment for the subpath.
    intro k
    obtain ⟨i, hi⟩ := hsub k.1
    refine ⟨i, ?_⟩
    rw [Path.range_subpath_of_le γ (t k.castSucc) (t k.succ) (hmono (Nat.le_succ k.1))]
    intro z hz
    rcases hz with ⟨s, hs, rfl⟩
    exact hi hs
  choose u hu using hsub_fin
  refine ⟨n, (fun k : Fin (n + 1) ↦ t k.1), ?_, ?_, hmono_fin, u, ?_⟩
  · simpa using ht0
  · simpa using hn n le_rfl
  · -- The finite labels inherit the subordinate-cover property piecewise.
    intro k
    simpa using hu k

/-- Helper for Theorem 2.7.1: a continuous square in `X` admits a finite monotone grid whose
closed cells each land in a single member of the open cover. This is the finite 2-dimensional
subdivision used to compare homotopic paths cell by cell. -/
theorem square_subdivision_data_of_open_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (f : C(I × I, X)) :
    ∃ n : ℕ, ∃ t : Fin (n + 1) → I,
      t 0 = 0 ∧
      t (Fin.last n) = 1 ∧
      Monotone t ∧
      ∃ u : Fin n → Fin n → ι,
        ∀ k l : Fin n,
          Set.Icc (t k.castSucc) (t k.succ) ×ˢ Set.Icc (t l.castSucc) (t l.succ) ⊆
            f ⁻¹' (O (u k l) : Set X) := by
  let c : ι → Set (I × I) := fun i ↦ f ⁻¹' (O i : Set X)
  have hc₁ : ∀ i, IsOpen (c i) := by
    -- Pull the open cover back along the square map.
    intro i
    exact (O i).isOpen.preimage f.continuous
  have hc₂ : Set.univ ⊆ ⋃ i, c i := by
    -- Every point of the square lands in some cover member because `O` covers `X`.
    intro s _
    obtain ⟨i, hi⟩ := hO.exists_mem (f s)
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨t, ht0, hmono, hstable, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self hc₁ hc₂
  obtain ⟨n, hn⟩ := hstable
  have hmono_fin : Monotone (fun k : Fin (n + 1) ↦ t k.1) := by
    -- Restrict the monotone sequence to the finite initial segment ending at the stable value.
    intro a b hab
    exact hmono hab
  have hsub_fin :
      ∀ k l : Fin n,
        ∃ i,
          Set.Icc (t k.castSucc) (t k.succ) ×ˢ Set.Icc (t l.castSucc) (t l.succ) ⊆ c i := by
    -- The square subdivision theorem already provides a cover label for every grid cell.
    intro k l
    simpa using hsub k.1 l.1
  choose u hu using hsub_fin
  refine ⟨n, (fun k : Fin (n + 1) ↦ t k.1), ?_, ?_, hmono_fin, u, ?_⟩
  · simpa using ht0
  · simpa using hn n le_rfl
  · -- Each finite cell of the grid is subordinate to the chosen cover member.
    intro k l
    simpa [c] using hu k l

/-- Helper for Theorem 2.7.1: a horizontal edge of a square cell subordinate to one cover member
still lands in that same cover member. -/
theorem horizontal_edge_subset_of_square_cell_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (f : C(I × I, X))
    {a b c d : I} (hab : a ≤ b) {s : I} (hs : s ∈ Set.Icc c d)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hcell : Set.Icc a b ×ˢ Set.Icc c d ⊆ f ⁻¹' (O i : Set X)) :
    Set.range (fun t : I ↦ f (Set.Icc.convexCombo a b t, s)) ⊆ O i := by
  -- Every horizontal edge point stays in the rectangle because convex combinations stay in the
  -- interval `[a, b]` and the fixed vertical coordinate already lies in `[c, d]`.
  intro z hz
  rcases hz with ⟨t, rfl⟩
  refine hcell ?_
  exact ⟨⟨Set.Icc.le_convexCombo hab t, Set.Icc.convexCombo_le hab t⟩, hs⟩

/-- Helper for Theorem 2.7.1: a vertical edge of a square cell subordinate to one cover member
still lands in that same cover member. -/
theorem vertical_edge_subset_of_square_cell_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (f : C(I × I, X))
    {a b c d : I} {t : I} (ht : t ∈ Set.Icc a b) (hcd : c ≤ d)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hcell : Set.Icc a b ×ˢ Set.Icc c d ⊆ f ⁻¹' (O i : Set X)) :
    Set.range (fun s : I ↦ f (t, Set.Icc.convexCombo c d s)) ⊆ O i := by
  -- The same interval argument applies after swapping the horizontal and vertical roles.
  intro z hz
  rcases hz with ⟨s, rfl⟩
  refine hcell ?_
  exact ⟨ht, ⟨Set.Icc.le_convexCombo hcd s, Set.Icc.convexCombo_le hcd s⟩⟩

/-- Helper for Theorem 2.7.1: if the range of a subpath lands in one open set, then the initial
endpoint of that subpath lies in the same open set. -/
theorem subpath_source_mem_of_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y) (a b : I)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    γ a ∈ O i := by
  -- Evaluate the range inclusion at the left endpoint `0` of the subpath.
  exact hsub ⟨0, by simp⟩

/-- Helper for Theorem 2.7.1: if the range of a subpath lands in one open set, then the terminal
endpoint of that subpath lies in the same open set. -/
theorem subpath_target_mem_of_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y) (a b : I)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    γ b ∈ O i := by
  -- Evaluate the range inclusion at the right endpoint `1` of the subpath.
  exact hsub ⟨1, by simp⟩

/-- Helper for Theorem 2.7.1: the underlying continuous map of a subordinate subpath can be
restricted to a fixed member of the cover. -/
noncomputable def lift_subpath_to_open_map
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    C(I, O i) :=
  ⟨fun s ↦ ⟨γ.subpath a b s, hsub ⟨s, rfl⟩⟩,
    (γ.subpath a b).continuous.subtype_mk (fun s ↦ hsub ⟨s, rfl⟩)⟩

/-- Helper for Theorem 2.7.1: the restricted continuous map starts at the expected endpoint in the
chosen open set. -/
theorem lift_subpath_to_open_map_source
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    lift_subpath_to_open_map O γ a b i hsub 0 =
      ⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ := by
  -- Both subtype points have the same underlying value `γ a`.
  ext
  simp [lift_subpath_to_open_map]

/-- Helper for Theorem 2.7.1: the restricted continuous map ends at the expected endpoint in the
chosen open set. -/
theorem lift_subpath_to_open_map_target
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    lift_subpath_to_open_map O γ a b i hsub 1 =
      ⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ := by
  -- Both subtype points have the same underlying value `γ b`.
  ext
  simp [lift_subpath_to_open_map]

/-- Helper for Theorem 2.7.1: a subpath whose range is contained in one cover member lifts to a
path in the subtype corresponding to that cover member. -/
noncomputable def lift_subpath_to_open
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    Path
      (x := (⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ : O i))
      (y := (⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i)) :=
  Path.mk
    (lift_subpath_to_open_map O γ a b i hsub)
    (lift_subpath_to_open_map_source O γ a b i hsub)
    (lift_subpath_to_open_map_target O γ a b i hsub)

/-- Helper for Theorem 2.7.1: the lifted subpath has the expected underlying values in the ambient
space. -/
@[simp]
theorem lift_subpath_to_open_apply
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    {x y : X} (γ : Path x y) (a b s : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    ((lift_subpath_to_open O γ a b i hsub) s : X) = γ.subpath a b s := by
  rfl

/-- Helper for Theorem 2.7.1: a smaller monotone subpath of a subpath already subordinate to one
cover member stays subordinate to that same cover member. -/
theorem subpath_range_subset_of_subpath_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {a b c d : I} (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    Set.range (γ.subpath c d) ⊆ O i := by
  -- Any point on the smaller subpath comes from a parameter in `[c, d]`, hence also from one in
  -- `[a, b]`, so the larger subpath's range containment applies.
  rw [Path.range_subpath_of_le γ c d hcd]
  intro z hz
  rcases hz with ⟨s, hs, rfl⟩
  have hab : a ≤ b := le_trans hac (le_trans hcd hdb)
  rw [Path.range_subpath_of_le γ a b hab] at hsub
  refine hsub ?_
  exact ⟨s, ⟨le_trans hac hs.1, le_trans hs.2 hdb⟩, rfl⟩

/-- Helper for Theorem 2.7.1: one subpath segment landing in a single cover member induces a
morphism in the cocone target between the chosen objects at its endpoints. -/
noncomputable def local_subpath_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    chosen_cover_object O hO S (γ a) ⟶ chosen_cover_object O hO S (γ b) :=
  eqToHom
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub)) ≫
    (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub⟧) ≫
    eqToHom
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub)).symm

/-- Helper for Theorem 2.7.1: the endpoint-transported local segment morphism is heterogeneously
equal to the raw functor image of the lifted subpath inside the chosen cover member. -/
theorem local_subpath_morphism_heq_functor_map
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    local_subpath_morphism O hO hinter S γ a b i hsub ≍
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub⟧) := by
  -- Remove the endpoint `eqToHom`s by viewing the local morphism as a conjugate of the raw map.
  exact
    (CategoryTheory.conj_eqToHom_iff_heq
      (local_subpath_morphism O hO hinter S γ a b i hsub)
      ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub⟧))
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub))
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub))).1 rfl

/-- Helper for Theorem 2.7.1: `local_subpath_morphism` is heterogeneously unchanged when only the
segment endpoints, the chosen cover label, and the subordinate proof are replaced by equal data. -/
theorem local_subpath_morphism_heq_of_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {a a' b b' : I}
    {i i' : TopologicalSpace.IsOpenCover.Index O}
    (ha : a = a')
    (hb : b = b')
    (hi : i = i')
    {hsub : Set.range (γ.subpath a b) ⊆ O i}
    {hsub' : Set.range (γ.subpath a' b') ⊆ O i'} :
    local_subpath_morphism O hO hinter S γ a b i hsub ≍
      local_subpath_morphism O hO hinter S γ a' b' i' hsub' := by
  -- Reduce to the literally identical endpoint and label data, then discard the subordinate proof
  -- by proof irrelevance.
  subst ha
  subst hb
  subst hi
  have hproof : hsub = hsub' := Subsingleton.elim _ _
  subst hproof
  rfl

/-- Helper for Theorem 2.7.1: pointwise equal cover-subordinate subpaths inside one cover member
induce the same local segment morphism in the cocone target. -/
theorem local_subpath_morphism_heq_of_subpath_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y x' y' : X}
    (γ : Path x y) (a b : I)
    (γ' : Path x' y') (a' b' : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i)
    (hsub' : Set.range (γ'.subpath a' b') ⊆ O i)
    (hseg : ∀ s : I, γ.subpath a b s = γ'.subpath a' b' s) :
    local_subpath_morphism O hO hinter S γ a b i hsub ≍
      local_subpath_morphism O hO hinter S γ' a' b' i hsub' := by
  let p := lift_subpath_to_open O γ a b i hsub
  let q := lift_subpath_to_open O γ' a' b' i hsub'
  have hpq : ∀ s : I, p s = q s := by
    -- The two lifted subtype paths agree pointwise because their ambient subpaths agree.
    intro s
    have hval : ((p s : O i) : X) = ((q s : O i) : X) := by
      change γ.subpath a b s = γ'.subpath a' b' s
      exact hseg s
    exact Subtype.ext hval
  let hs :
      ((⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ : O i)) =
        ((⟨γ' a', subpath_source_mem_of_range_subset γ' a' b' hsub'⟩ : O i)) := by
    -- Evaluate the pointwise equality at the source parameter.
    simpa [p, q] using hpq 0
  let ht :
      ((⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i)) =
        ((⟨γ' b', subpath_target_mem_of_range_subset γ' a' b' hsub'⟩ : O i)) := by
    -- Evaluate the pointwise equality at the target parameter.
    simpa [p, q] using hpq 1
  have hpath_heq :
      FundamentalGroupoid.fromPath ⟦p⟧ ≍
        FundamentalGroupoid.fromPath ⟦q⟧ := by
    -- Inside the fixed open set `O i`, pointwise equal lifted paths define the same path class.
    simpa [p, q] using
      (ContinuousMap.Homotopy.heq_path_of_eq_image
        (X₁ := TopCat.of (O i))
        (X₂ := TopCat.of (O i))
        (Y := TopCat.of (O i))
        (f := ContinuousMap.id _)
        (g := ContinuousMap.id _)
        (p := p)
        (q := q)
        hpq)
  have hpath_eq :
      FundamentalGroupoid.fromPath ⟦p⟧ =
        eqToHom (congrArg FundamentalGroupoid.mk hs) ≫
          FundamentalGroupoid.fromPath ⟦q⟧ ≫
          eqToHom (congrArg FundamentalGroupoid.mk ht).symm := by
    -- Convert the local path-class HEq into the conjugation form expected after applying `S.ι.app i`.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (FundamentalGroupoid.fromPath ⟦p⟧)
        (FundamentalGroupoid.fromPath ⟦q⟧)
        (congrArg FundamentalGroupoid.mk hs)
        (congrArg FundamentalGroupoid.mk ht)).2 hpath_heq
  have hraw :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦q⟧) := by
    -- Map the conjugation formula through the cocone leg on `O i` and remove the resulting
    -- endpoint transports.
    have hmap := congrArg (fun f ↦ (S.ι.app i).map f) hpath_eq
    change
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) =
        (S.ι.app i).map
          (eqToHom (congrArg FundamentalGroupoid.mk hs) ≫
            FundamentalGroupoid.fromPath ⟦q⟧ ≫
            eqToHom (congrArg FundamentalGroupoid.mk ht).symm) at hmap
    rw [Functor.map_comp, Functor.map_comp, CategoryTheory.eqToHom_map,
      CategoryTheory.eqToHom_map] at hmap
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧))
        ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦q⟧))
        (congrArg (S.ι.app i).obj (congrArg FundamentalGroupoid.mk hs))
        (congrArg (S.ι.app i).obj (congrArg FundamentalGroupoid.mk ht))).1 hmap
  have hleft :
      local_subpath_morphism O hO hinter S γ a b i hsub ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) := by
    -- Normalize the first local morphism to its raw functor image.
    simpa [p] using local_subpath_morphism_heq_functor_map hO hinter S γ a b i hsub
  have hright :
      local_subpath_morphism O hO hinter S γ' a' b' i hsub' ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦q⟧) := by
    -- Do the same normalization for the second local morphism.
    simpa [q] using local_subpath_morphism_heq_functor_map hO hinter S γ' a' b' i hsub'
  -- Both local morphisms reduce to the same raw image in the cocone target.
  exact hleft.trans (hraw.trans hright.symm)

/-- Helper for Theorem 2.7.1: a local subpath with equal endpoints contributes the identity
morphism in the cocone target. -/
theorem local_subpath_morphism_eq_id_of_eq_endpoints
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    (a : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a a) ⊆ O i) :
    local_subpath_morphism O hO hinter S γ a a i hsub =
      𝟙 (chosen_cover_object O hO S (γ a)) := by
  let p := lift_subpath_to_open O γ a a i hsub
  have hp : p = Path.refl ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i)) := by
    -- A lifted subpath with identical endpoints is pointwise the constant path in the chosen open
    -- set.
    apply Path.ext
    funext s
    ext
    simpa [p] using
      (lift_subpath_to_open_apply (O := O) (γ := γ) (a := a) (b := a) (s := s) (i := i)
        (hsub := hsub))
  have hraw :
      local_subpath_morphism O hO hinter S γ a a i hsub ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) := by
    -- First remove the endpoint conjugations from the local morphism.
    simpa [p] using local_subpath_morphism_heq_functor_map hO hinter S γ a a i hsub
  have hrefl :
      FundamentalGroupoid.fromPath ⟦p⟧ =
        𝟙 (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i))) := by
    -- The degenerate lifted path represents the identity in the local fundamental groupoid.
    rw [hp, FundamentalGroupoid.id_eq_path_refl]
  have hmap_id :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) =
        𝟙 ((S.ι.app i).obj
          (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i)))) := by
    -- Functoriality sends the local identity path class to the identity morphism in the cocone
    -- target.
    have hmap_eq :
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p⟧) =
          (S.ι.app i).map
            (𝟙 (FundamentalGroupoid.mk
              ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i)))) :=
      congrArg (fun f ↦ (S.ι.app i).map f) hrefl
    exact hmap_eq.trans ((S.ι.app i).map_id _)
  have hobj :
      (S.ι.app i).obj
          (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i))) =
        chosen_cover_object O hO S (γ a) := by
    -- The endpoint object computed inside `O i` is the chosen endpoint object.
    exact
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a a hsub)).symm
  have hid :
      𝟙 ((S.ι.app i).obj
          (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i)))) ≍
        𝟙 (chosen_cover_object O hO S (γ a)) := by
    -- Transport the identity morphism along the endpoint-object equality.
    exact
      (CategoryTheory.eqToHom_heq_id_dom
        ((S.ι.app i).obj
          (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i))))
        (chosen_cover_object O hO S (γ a))
        hobj).symm.trans
      (CategoryTheory.eqToHom_heq_id_cod
        ((S.ι.app i).obj
          (FundamentalGroupoid.mk ((⟨γ a, subpath_source_mem_of_range_subset γ a a hsub⟩ : O i))))
        (chosen_cover_object O hO S (γ a))
        hobj)
  exact eq_of_heq (hraw.trans (hmap_id.heq.trans hid))

/-- Helper for Theorem 2.7.1: a finite cover-subordinate subdivision of a path determines the
composite of its local segment morphisms between the chosen objects at the endpoints. -/
noncomputable def subdivision_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) :
    ∀ {n : ℕ},
      (t : Fin (n + 1) → I) →
      (u : Fin n → TopologicalSpace.IsOpenCover.Index O) →
      (∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) →
      ((chosen_cover_object O hO S (γ (t 0))) ⟶
        (chosen_cover_object O hO S (γ (t (Fin.last n)))))
  | 0, _t, _u, _hu => 𝟙 _
  | n + 1, t, u, hu =>
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n))

/-- Helper for Theorem 2.7.1: a subdivision with a single interval is already the corresponding
local segment morphism. -/
theorem subdivision_morphism_single_interval_heq_local
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    (t : Fin 2 → I)
    (u : Fin 1 → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin 1, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu ≍
      local_subpath_morphism O hO hinter S γ
        (t 0)
        (t (Fin.last 1))
        (u (Fin.last 0))
        (hu (Fin.last 0)) := by
  -- A one-interval subdivision has trivial recursive part, so the unique local factor is all
  -- that remains after unfolding `subdivision_morphism`.
  simpa [subdivision_morphism]

/-- Helper for Theorem 2.7.1: inside a fixed open set, endpoint-fixed homotopic paths induce the
same morphism under any functor out of that fundamental groupoid. -/
theorem functor_map_eq_of_homotopic_paths_in_open
    (U : TopologicalSpace.Opens (TopCat.of X))
    {C : Type v} [Category C]
    (F : πₓ (TopCat.of U) ⥤ C)
    {x y : U} {p q : Path x y}
    (h : Path.Homotopic p q) :
    F.map (FundamentalGroupoid.fromPath ⟦p⟧) =
      F.map (FundamentalGroupoid.fromPath ⟦q⟧) := by
  -- The quotient relation in the local fundamental groupoid already identifies the two paths.
  exact congrArg F.map ((FundamentalGroupoid.fromPath_eq_iff_homotopic p q).2 h)

/-- Helper for Theorem 2.7.1: if one whole subpath lies in a chosen cover member, then splitting it
at an intermediate breakpoint gives a concatenation homotopic, inside that same open set, to the
original lifted subpath. -/
theorem lifted_subpath_trans_homotopic_in_open
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    (a c b : I) (hac : a ≤ c) (hcb : c ≤ b)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    Path.Homotopic
      ((lift_subpath_to_open O γ a c i
          (subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb hsub)).trans
        (lift_subpath_to_open O γ c b i
          (subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl hsub)))
      (lift_subpath_to_open O γ a b i hsub) := by
  let hsub_ac :=
    subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb hsub
  let hsub_cb :=
    subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl hsub
  let p_ac := lift_subpath_to_open O γ a c i hsub_ac
  let p_cb := lift_subpath_to_open O γ c b i hsub_cb
  let p_ab := lift_subpath_to_open O γ a b i hsub
  -- First lift the ambient breakpoint-insertion homotopy into the chosen cover member.
  have h_refl :
      Path.Homotopic
        (p_ac.trans p_cb)
        (p_ab.trans
          (Path.refl ((⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i)))) := by
    let H := Path.Homotopy.subpathTransSubpathRefl γ a c b
    refine ⟨
      { toFun := fun x ↦ ⟨H x, ?_⟩
        continuous_toFun := H.continuous_toFun.subtype_mk (fun x ↦ ?_)
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
    · let s : I := Set.Icc.convexCombo c b x.1
      have hs_lower : c ≤ s := Set.Icc.le_convexCombo hcb x.1
      have hs_upper : s ≤ b := Set.Icc.convexCombo_le hcb x.1
      have hleft :
          Set.range (γ.subpath a s) ⊆ O i :=
        subpath_range_subset_of_subpath_range_subset γ le_rfl
          (le_trans hac hs_lower) hs_upper hsub
      have hright :
          Set.range (γ.subpath s b) ⊆ O i :=
        subpath_range_subset_of_subpath_range_subset γ
          (le_trans hac hs_lower) hs_upper le_rfl hsub
      have htrans :
          Set.range (((γ.subpath a s).trans (γ.subpath s b)) : Path (γ a) (γ b)) ⊆ O i := by
        rw [Path.trans_range]
        intro z hz
        rcases hz with hz | hz
        · exact hleft hz
        · exact hright hz
      exact htrans ⟨x.2, rfl⟩
    · let s : I := Set.Icc.convexCombo c b x.1
      have hs_lower : c ≤ s := Set.Icc.le_convexCombo hcb x.1
      have hs_upper : s ≤ b := Set.Icc.convexCombo_le hcb x.1
      have hleft :
          Set.range (γ.subpath a s) ⊆ O i :=
        subpath_range_subset_of_subpath_range_subset γ le_rfl
          (le_trans hac hs_lower) hs_upper hsub
      have hright :
          Set.range (γ.subpath s b) ⊆ O i :=
        subpath_range_subset_of_subpath_range_subset γ
          (le_trans hac hs_lower) hs_upper le_rfl hsub
      have htrans :
          Set.range (((γ.subpath a s).trans (γ.subpath s b)) : Path (γ a) (γ b)) ⊆ O i := by
        rw [Path.trans_range]
        intro z hz
        rcases hz with hz | hz
        · exact hleft hz
        · exact hright hz
      exact htrans ⟨x.2, rfl⟩
    · intro t
      ext
      change H (0, t) = (((p_ac.trans p_cb) t : O i) : X)
      calc
        H (0, t) = ((γ.subpath a c).trans (γ.subpath c b)) t := by
          simpa using H.map_zero_left t
        _ = (((p_ac.trans p_cb) t : O i) : X) := by
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs <;> rfl
    · intro t
      ext
      change H (1, t) = (((p_ab.trans (Path.refl ((⟨γ b,
        subpath_target_mem_of_range_subset γ a b hsub⟩ : O i))) ) t : O i) : X)
      calc
        H (1, t) = ((γ.subpath a b).trans (Path.refl (γ b))) t := by
          simpa using H.map_one_left t
        _ = (((p_ab.trans (Path.refl ((⟨γ b,
            subpath_target_mem_of_range_subset γ a b hsub⟩ : O i))) ) t : O i) : X) := by
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs <;> rfl
    · intro t s hs
      rcases hs with rfl | rfl
      · ext
        simp [H]
      · ext
        simp [H]
  -- Then remove the redundant terminal constant segment with the standard homotopy.
  exact Path.Homotopic.trans h_refl (Path.Homotopic.trans_refl p_ab)

/-- Helper for Theorem 2.7.1: when two consecutive subdivision pieces lie in the same cover member,
their associated cocone-target morphisms compose to the morphism of the unsplit piece. -/
theorem local_subpath_morphism_trans
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    (a c b : I) (hac : a ≤ c) (hcb : c ≤ b)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    local_subpath_morphism O hO hinter S γ a c i
        (subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb hsub) ≫
      local_subpath_morphism O hO hinter S γ c b i
        (subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl hsub) =
      local_subpath_morphism O hO hinter S γ a b i hsub := by
  let hsub_ac :=
    subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb hsub
  let hsub_cb :=
    subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl hsub
  let p_ac := lift_subpath_to_open O γ a c i hsub_ac
  let p_cb := lift_subpath_to_open O γ c b i hsub_cb
  let p_ab := lift_subpath_to_open O γ a b i hsub
  -- Normalize both local pieces to raw functor images before composing them.
  have hleft :
      local_subpath_morphism O hO hinter S γ a c i hsub_ac ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ac⟧) := by
    simpa [hsub_ac, p_ac] using
      local_subpath_morphism_heq_functor_map hO hinter S γ a c i hsub_ac
  have hright :
      local_subpath_morphism O hO hinter S γ c b i hsub_cb ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_cb⟧) := by
    simpa [hsub_cb, p_cb] using
      local_subpath_morphism_heq_functor_map hO hinter S γ c b i hsub_cb
  have hcomp :
      local_subpath_morphism O hO hinter S γ a c i hsub_ac ≫
          local_subpath_morphism O hO hinter S γ c b i hsub_cb ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ac⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_cb⟧) := by
    -- The heq normalization lets the midpoint transports disappear before any path algebra.
    refine
      CategoryTheory.heq_comp
        (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub))
        (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ c) (subpath_target_mem_of_range_subset γ a c hsub_ac))
        (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub))
        ?_ ?_
    · exact hleft
    · exact hright
  have hpath_eq :
      FundamentalGroupoid.fromPath ⟦p_ac⟧ ≫
          FundamentalGroupoid.fromPath ⟦p_cb⟧ =
        FundamentalGroupoid.fromPath ⟦p_ab⟧ := by
    -- The concatenated lifted segment and the unsplit lifted segment define the same local path
    -- class because they are homotopic rel endpoints inside `O i`.
    rw [FundamentalGroupoid.comp_eq]
    calc
      Path.Homotopic.Quotient.trans
          (FundamentalGroupoid.fromPath ⟦p_ac⟧)
          (FundamentalGroupoid.fromPath ⟦p_cb⟧) =
        FundamentalGroupoid.fromPath ⟦p_ac.trans p_cb⟧ := by
          simpa [FundamentalGroupoid.fromPath] using
            (Path.Homotopic.Quotient.mk_trans p_ac p_cb).symm
      _ = FundamentalGroupoid.fromPath ⟦p_ab⟧ := by
          exact
            (FundamentalGroupoid.fromPath_eq_iff_homotopic (p_ac.trans p_cb) p_ab).2
              (lifted_subpath_trans_homotopic_in_open γ a c b hac hcb i hsub)
  have hmap :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ac⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_cb⟧) =
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ab⟧) := by
    -- Inside one open set, functoriality and the lifted breakpoint-insertion homotopy identify
    -- the concatenated local image with the unsplit local image.
    have hmap' :
        (S.ι.app i).map
            (FundamentalGroupoid.fromPath ⟦p_ac⟧ ≫
              FundamentalGroupoid.fromPath ⟦p_cb⟧) =
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ab⟧) := by
      exact congrArg (fun f ↦ (S.ι.app i).map f) hpath_eq
    calc
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ac⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_cb⟧) =
        (S.ι.app i).map
          (FundamentalGroupoid.fromPath ⟦p_ac⟧ ≫
            FundamentalGroupoid.fromPath ⟦p_cb⟧) := by
          exact ((S.ι.app i).map_comp _ _).symm
      _ = (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ab⟧) := hmap'
  -- Reinsert the endpoint conjugations for the unsplit segment only at the end.
  exact
    (CategoryTheory.conj_eqToHom_iff_heq
      (local_subpath_morphism O hO hinter S γ a c i hsub_ac ≫
        local_subpath_morphism O hO hinter S γ c b i hsub_cb)
      ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦p_ab⟧))
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub))
      (chosen_cover_object_eq_of_mem hO hinter S
        (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub))).2
      (hcomp.trans hmap.heq)

/-- Helper for Theorem 2.7.1: if a chosen overlap member maps into a cover member `O i`, then the
local segment morphism computed in `O i` agrees with the one computed in that overlap member. -/
theorem local_subpath_morphism_eq_of_overlap_member
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (k' : TopologicalSpace.IsOpenCover.Index O)
    (fki : k' ⟶ i)
    (hsub_i : Set.range (γ.subpath a b) ⊆ O i)
    (hsub_k : Set.range (γ.subpath a b) ⊆ O k')
    (hmapi :
      ((fundamental_groupoid_cover_diagram O).map fki).map
          (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b k' hsub_k⟧) =
        FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧) :
    local_subpath_morphism O hO hinter S γ a b i hsub_i =
      local_subpath_morphism O hO hinter S γ a b k' hsub_k := by
  let mk :=
    FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b k' hsub_k⟧
  have hnat :
      (S.ι.app i).map (((fundamental_groupoid_cover_diagram O).map fki).map mk) =
        eqToHom
            (Functor.congr_obj (S.w fki)
              (FundamentalGroupoid.mk
                ⟨γ a, subpath_source_mem_of_range_subset γ a b hsub_k⟩)) ≫
          (S.ι.app k').map mk ≫
            eqToHom
              (Functor.congr_obj (S.w fki)
                (FundamentalGroupoid.mk
                  ⟨γ b, subpath_target_mem_of_range_subset γ a b hsub_k⟩)).symm := by
    -- Evaluate cocone naturality at the concrete lifted path class inside the overlap member.
    simpa [Functor.comp_map, mk] using Functor.congr_hom (S.w fki) mk
  -- Route correction: compare the raw functor images first, using cocone naturality at the
  -- specific lifted path class, and only then reinsert the endpoint transports on both sides.
  have hraw_eq :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧) =
        eqToHom
            (Functor.congr_obj (S.w fki)
              (FundamentalGroupoid.mk
                ⟨γ a, subpath_source_mem_of_range_subset γ a b hsub_k⟩)) ≫
          (S.ι.app k').map mk ≫
        eqToHom
              (Functor.congr_obj (S.w fki)
                (FundamentalGroupoid.mk
                  ⟨γ b, subpath_target_mem_of_range_subset γ a b hsub_k⟩)).symm := by
    -- Replace the mapped overlap path by the chosen representative in `O i`.
    have hmapi' :
        ((fundamental_groupoid_cover_diagram O).map fki).map mk =
          FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧ := by
      simpa [mk] using hmapi
    rw [hmapi'] at hnat
    simpa [mk] using hnat
  have hraw :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧) ≍
        (S.ι.app k').map mk := by
    -- The naturality equality is exactly a conjugation by endpoint object equalities.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧))
        ((S.ι.app k').map mk)
        (Functor.congr_obj (S.w fki)
          (FundamentalGroupoid.mk
            ⟨γ a, subpath_source_mem_of_range_subset γ a b hsub_k⟩))
        (Functor.congr_obj (S.w fki)
          (FundamentalGroupoid.mk
            ⟨γ b, subpath_target_mem_of_range_subset γ a b hsub_k⟩))).1 hraw_eq
  have hi :
      local_subpath_morphism O hO hinter S γ a b i hsub_i ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧) := by
    -- Remove the chosen-endpoint conjugations from the `O i` local morphism.
    simpa using local_subpath_morphism_heq_functor_map hO hinter S γ a b i hsub_i
  have hk :
      local_subpath_morphism O hO hinter S γ a b k' hsub_k ≍
        (S.ι.app k').map mk := by
    -- Do the same normalization for the overlap-member local morphism.
    simpa [mk] using local_subpath_morphism_heq_functor_map hO hinter S γ a b k' hsub_k
  -- With both sides normalized to raw functor images, heterogeneous equality collapses to an
  -- ordinary equality because the endpoint objects of the local morphisms already agree.
  exact eq_of_heq (hi.trans (hraw.trans hk.symm))

/-- Helper for Theorem 2.7.1: if one subpath lies in two cover members, the corresponding local
segment morphism in the cocone target is independent of which overlap label is chosen. -/
theorem local_subpath_morphism_eq_of_overlap
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    (i j : TopologicalSpace.IsOpenCover.Index O)
    (hsub_i : Set.range (γ.subpath a b) ⊆ O i)
    (hsub_j : Set.range (γ.subpath a b) ⊆ O j) :
    local_subpath_morphism O hO hinter S γ a b i hsub_i =
      local_subpath_morphism O hO hinter S γ a b j hsub_j := by
  classical
  obtain ⟨k, hk⟩ :=
    TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections.binary_intersection_member
      hinter i j
  let k' : TopologicalSpace.IsOpenCover.Index O := k
  let hsub_k : Set.range (γ.subpath a b) ⊆ O k' := by
    -- The same subpath lands in the binary overlap because it lands in both members separately.
    rw [hk]
    intro z hz
    exact ⟨hsub_i hz, hsub_j hz⟩
  have hleki : O k' ≤ O i := by
    -- The overlap is contained in each of its two factors.
    intro z hz
    exact (show z ∈ O i ∧ z ∈ O j by simpa [k', hk] using hz).1
  have hlekj : O k' ≤ O j := by
    -- The same overlap containment also gives the second projection.
    intro z hz
    exact (show z ∈ O i ∧ z ∈ O j by simpa [k', hk] using hz).2
  let fki : k' ⟶ i := InducedCategory.homMk (homOfLE hleki)
  let fkj : k' ⟶ j := InducedCategory.homMk (homOfLE hlekj)
  have hmapi :
      ((fundamental_groupoid_cover_diagram O).map fki).map
          (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b k' hsub_k⟧) =
        FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub_i⟧ := by
    -- Mapping the common lifted path along the overlap inclusion just forgets the extra proof.
    rfl
  have hmapj :
      ((fundamental_groupoid_cover_diagram O).map fkj).map
          (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b k' hsub_k⟧) =
        FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b j hsub_j⟧ := by
    -- The same simplification works for the second inclusion from the overlap.
    rfl
  have hi_to_k :=
    local_subpath_morphism_eq_of_overlap_member hO hinter S γ a b i k' fki hsub_i hsub_k hmapi
  have hj_to_k :=
    local_subpath_morphism_eq_of_overlap_member hO hinter S γ a b j k' fkj hsub_j hsub_k hmapj
  exact hi_to_k.trans hj_to_k.symm

/-- Helper for Theorem 2.7.1: once the breakpoint tuple is fixed, the subdivision composite is
independent of which subordinate cover label is chosen on each segment. -/
theorem subdivision_morphism_eq_of_same_points
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u v : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hv : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu =
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := v)
        hv := by
  induction n with
  | zero =>
      -- With no nontrivial segments, both subdivision composites are identities.
      rfl
  | succ n ih =>
      -- Unfold one recursive step so the induction hypothesis handles the prefix and the overlap
      -- lemma compares the terminal local segment.
      rw [subdivision_morphism, subdivision_morphism]
      have hprefix :=
        ih
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (v := fun k ↦ v k.castSucc)
          (hu := fun k : Fin n ↦ hu k.castSucc)
          (hv := fun k : Fin n ↦ hv k.castSucc)
      have hlast :=
        local_subpath_morphism_eq_of_overlap hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (v (Fin.last n))
          (hu (Fin.last n))
          (hv (Fin.last n))
      simpa [hprefix, hlast]

/-- Helper for Theorem 2.7.1: inserting a breakpoint into the subdivision interval indexed by `j`
creates a refined point tuple by placing the new breakpoint immediately after the original left
endpoint of that interval. -/
abbrev insert_subdivision_points
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) :
    Fin (n + 3) → I :=
  j.succ.castSucc.insertNth c t

/-- Helper for Theorem 2.7.1: the refined label tuple duplicates the label of the split interval on
the two pieces created by inserting the breakpoint. -/
abbrev insert_subdivision_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) (j : Fin (n + 1)) :
    Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O :=
  j.succ.insertNth (u j) u

/-- Helper for Theorem 2.7.1: the inserted breakpoint occupies the new point slot immediately after
the left endpoint of the split interval. -/
@[simp] theorem insert_subdivision_points_inserted
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) :
    insert_subdivision_points t j c j.succ.castSucc = c := by
  -- This is the defining property of `Fin.insertNth` at the inserted coordinate.
  simp [insert_subdivision_points]

/-- Helper for Theorem 2.7.1: the right endpoint of the newly created right-hand interval is the
original right endpoint of the split interval. -/
@[simp] theorem insert_subdivision_points_right_endpoint
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) :
    insert_subdivision_points t j c j.succ.succ = t j.succ := by
  -- Evaluate `insertNth` one position above the inserted breakpoint.
  rw [insert_subdivision_points]
  have h : j.succ.castSucc < j.succ.succ := by
    simp
  rw [Fin.insertNth_apply_above h]
  simp

/-- Helper for Theorem 2.7.1: the inserted label entry is the original label of the interval being
split. -/
@[simp] theorem insert_subdivision_labels_inserted
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) (j : Fin (n + 1)) :
    insert_subdivision_labels u j j.succ = u j := by
  -- The duplicated label sits exactly at the new interval index introduced by the insertion.
  simp [insert_subdivision_labels]

/-- Helper for Theorem 2.7.1: for every original interval, the left endpoint of the corresponding
refined interval obtained from `j.succ.succAbove` is still the original left endpoint. -/
theorem insert_subdivision_points_unchanged_castSucc
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) (m : Fin (n + 1)) :
    insert_subdivision_points t j c (j.succ.succAbove m).castSucc = t m.castSucc := by
  -- Move the refined index into the exact `succAbove` form on which `insertNth` computes by
  -- definition, then read off the unchanged original entry.
  rw [insert_subdivision_points]
  rw [← Fin.castSucc_succAbove_castSucc (i := j.succ) (j := m)]
  simpa using (Fin.insertNth_apply_succAbove
    (i := j.succ.castSucc) (x := c) (p := t) (j := m.castSucc))

/-- Helper for Theorem 2.7.1: the left split interval created by breakpoint insertion ends at the
newly inserted breakpoint. -/
@[simp] theorem insert_subdivision_points_split_left_succ
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) :
    insert_subdivision_points t j c (j.succ.succAbove j).succ = c := by
  -- The refined interval indexed by `j.succ.succAbove j` is the left half of the split original
  -- interval, so its right endpoint is exactly the inserted breakpoint.
  rw [Fin.succAbove_succ_self, ← Fin.castSucc_succ]
  simp [insert_subdivision_points]

/-- Helper for Theorem 2.7.1: away from the split interval itself, the right endpoint of the
refined interval corresponding to `m` is the original right endpoint. -/
theorem insert_subdivision_points_unchanged_succ
    {n : ℕ} (t : Fin (n + 2) → I) (j m : Fin (n + 1)) (c : I) (hm : m ≠ j) :
    insert_subdivision_points t j c (j.succ.succAbove m).succ = t m.succ := by
  -- Separate the cases where the unchanged interval lies before or after the split interval, and
  -- in each case evaluate the tuple insertion with the corresponding `below`/`above` rule.
  rcases lt_or_gt_of_ne hm with hmj | hjm
  · have hleft : j.succ.succAbove m = m.castSucc := by
      simpa using (Fin.succAbove_of_castSucc_lt j.succ m (by simpa using hmj.le))
    rw [hleft, ← Fin.castSucc_succ, insert_subdivision_points]
    have hlt : m.succ.castSucc < j.succ.castSucc := by
      simpa using (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_lt_succ_iff.mpr hmj))
    rw [Fin.insertNth_apply_below hlt]
    simpa [Fin.castSucc_succ] using
      congrArg t (Fin.castPred_castSucc (i := m.succ) (h' := Fin.castSucc_ne_last _))
  · have hleft : j.succ.succAbove m = m.succ := by
      simpa using
        (Fin.succAbove_of_le_castSucc j.succ m (by simpa using (Fin.succ_le_castSucc_iff.mpr hjm)))
    rw [hleft, insert_subdivision_points]
    have hgt : j.succ.castSucc < m.succ.succ := by
      simpa using
        (Fin.castSucc_lt_succ_iff.mpr (show j.succ ≤ m.succ by simpa using hjm.le))
    rw [Fin.insertNth_apply_above hgt]
    simpa using congrArg t (Fin.pred_succ (i := m.succ) (h := Fin.succ_ne_zero _))

/-- Helper for Theorem 2.7.1: the duplicated-label refinement agrees with the original labels on
every interval index coming from `j.succ.succAbove`. -/
theorem insert_subdivision_labels_unchanged
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) (j m : Fin (n + 1)) :
    insert_subdivision_labels u j (j.succ.succAbove m) = u m := by
  -- Composing `insertNth` with `succAbove` removes the inserted duplicate label and recovers the
  -- original tuple.
  change ((j.succ.insertNth (u j) u) ∘ j.succ.succAbove) m = u m
  simpa using congrFun
    (Fin.insertNth_comp_succAbove (i := j.succ) (x := u j) (p := u)) m

/-- Helper for Theorem 2.7.1: inserting a breakpoint inside a monotone subdivision preserves
monotonicity of the breakpoint tuple. -/
theorem insert_subdivision_points_monotone
    {n : ℕ}
    {t : Fin (n + 2) → I}
    (ht : Monotone t)
    (j : Fin (n + 1))
    (c : I)
    (hac : t j.castSucc ≤ c)
    (hcb : c ≤ t j.succ) :
    Monotone (insert_subdivision_points t j c) := by
  -- Check the adjacent inequalities in the refined tuple; away from the inserted breakpoint the
  -- tuple is unchanged, while the two new adjacent pairs are controlled by `hac` and `hcb`.
  refine Fin.monotone_iff_le_succ.2 ?_
  intro k
  cases k using Fin.succAboveCases j.succ with
  | x =>
      have hinserted :
          insert_subdivision_points t j c j.castSucc.succ = c := by
        simpa [Fin.succAbove_succ_self] using insert_subdivision_points_split_left_succ t j c
      simpa [hinserted] using hcb
  | p m =>
      by_cases hm : m = j
      · subst m
        have hleft_endpoint :
            insert_subdivision_points t j c j.castSucc.castSucc = t j.castSucc := by
          simpa [Fin.succAbove_succ_self] using
            insert_subdivision_points_unchanged_castSucc t j c j
        have hright_endpoint :
            insert_subdivision_points t j c j.castSucc.succ = c := by
          simpa [Fin.succAbove_succ_self] using
            insert_subdivision_points_split_left_succ t j c
        simpa [Fin.succAbove_succ_self, hleft_endpoint, hright_endpoint] using hac
      · simpa [insert_subdivision_points_unchanged_castSucc,
          insert_subdivision_points_unchanged_succ, hm] using
          (Fin.monotone_iff_le_succ.1 ht m)

/-- Helper for Theorem 2.7.1: inserting a breakpoint does not change the initial endpoint of the
breakpoint tuple. -/
@[simp] theorem insert_subdivision_points_zero
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (j : Fin (n + 1))
    (c : I) :
    insert_subdivision_points t j c 0 = t 0 := by
  -- The inserted breakpoint is always placed strictly after the initial point.
  have hlt : (0 : Fin (n + 3)) < j.castSucc.succ := by
    exact Fin.pos_iff_ne_zero.2 (by simp)
  simpa [insert_subdivision_points] using
    (@Fin.insertNth_apply_below
      (n := n + 2)
      (α := fun _ : Fin (n + 3) ↦ I)
      (i := j.castSucc.succ)
      (j := 0)
      hlt
      c
      t)

/-- Helper for Theorem 2.7.1: inserting a breakpoint does not change the terminal endpoint of the
breakpoint tuple. -/
@[simp] theorem insert_subdivision_points_last_unchanged
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (j : Fin (n + 1))
    (c : I) :
    insert_subdivision_points t j c (Fin.last (n + 2)) = t (Fin.last (n + 1)) := by
  -- The inserted breakpoint sits before the terminal endpoint, so the last point is inherited
  -- unchanged from the original tuple.
  have hlt : j.castSucc.succ < Fin.last (n + 2) := by
    simpa [Fin.castSucc_succ] using (Fin.castSucc_lt_last j.succ)
  simpa [insert_subdivision_points] using
    (@Fin.insertNth_apply_above
      (n := n + 2)
      (α := fun _ : Fin (n + 3) ↦ I)
      (i := j.castSucc.succ)
      (j := Fin.last (n + 2))
      hlt
      c
      t)

/-- Helper for Theorem 2.7.1: away from the inserted coordinate, the refined breakpoint tuple
agrees with the original tuple after transporting old indices through `succAbove`. -/
theorem insert_subdivision_points_succAbove
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin (n + 1)) (c : I) (k : Fin (n + 2)) :
    insert_subdivision_points t j c (j.succ.castSucc.succAbove k) = t k := by
  -- This is the defining computation rule for `insertNth` on the old coordinates.
  rw [insert_subdivision_points]
  simpa using
    (Fin.insertNth_apply_succAbove
      (i := j.succ.castSucc)
      (x := c)
      (p := t)
      (j := k))

/-- Helper for Theorem 2.7.1: inserting a breakpoint inside one subordinate interval preserves the
subordinate-cover property for the whole refined subdivision. -/
theorem insert_subdivision_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin (n + 1))
    (c : I)
    (hac : t j.castSucc ≤ c)
    (hcb : c ≤ t j.succ) :
    ∀ k : Fin (n + 2),
      Set.range
          (γ.subpath
            ((insert_subdivision_points t j c) k.castSucc)
            ((insert_subdivision_points t j c) k.succ)) ⊆
        O ((insert_subdivision_labels u j) k) := by
  intro k
  -- Split the refined interval index into the newly created right split piece and the family of
  -- intervals transported from the original subdivision.
  cases k using Fin.succAboveCases j.succ with
  | x =>
      -- The freshly inserted right split piece is the right half of the original `j`-interval.
      have hright :
          Set.range (γ.subpath c (t j.succ)) ⊆ O (u j) :=
        subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu j)
      rw [insert_subdivision_points_inserted, insert_subdivision_points_right_endpoint,
        insert_subdivision_labels_inserted]
      exact hright
  | p m =>
      by_cases hm : m = j
      · -- The transported interval with `m = j` is the left half of the split original interval.
        subst m
        have hleft :
            Set.range (γ.subpath (t j.castSucc) c) ⊆ O (u j) :=
          subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu j)
        have hleft_endpoint :
            insert_subdivision_points t j c j.castSucc.castSucc = t j.castSucc := by
          simpa [Fin.succAbove_succ_self] using
            insert_subdivision_points_unchanged_castSucc t j c j
        have hright_endpoint :
            insert_subdivision_points t j c j.castSucc.succ = c := by
          simpa [Fin.succAbove_succ_self] using insert_subdivision_points_split_left_succ t j c
        have hlabel : insert_subdivision_labels u j j.castSucc = u j := by
          simpa [Fin.succAbove_succ_self] using insert_subdivision_labels_unchanged u j j
        simpa [Fin.succAbove_succ_self, hleft_endpoint, hright_endpoint, hlabel] using hleft
      · -- Every other transported interval is literally unchanged after the insertion.
        simpa [insert_subdivision_points_unchanged_castSucc,
          insert_subdivision_points_unchanged_succ, insert_subdivision_labels_unchanged, hm] using
          hu m

/-- Helper for Theorem 2.7.1: if the inserted breakpoint is not in the terminal interval, removing
the unchanged final point from the refined tuple gives the refinement of the original prefix tuple.
-/
theorem insert_subdivision_points_castSucc_prefix
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin n) (c : I) :
    (fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc) =
      j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc) := by
  -- Split the refined prefix at the inserted coordinate and compare the remaining entries by
  -- commuting `castSucc` with `succAbove`.
  funext k
  cases k using Fin.succAboveCases j.succ.castSucc with
  | x =>
      simp [insert_subdivision_points]
  | p m =>
      rw [← Fin.castSucc_succAbove_castSucc]
      simp [insert_subdivision_points]

/-- Helper for Theorem 2.7.1: if the split interval is not terminal, removing the unchanged final
label from the refined label tuple gives the corresponding refinement of the original prefix labels.
-/
theorem insert_subdivision_labels_castSucc_prefix
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) (j : Fin n) :
    (fun k : Fin (n + 1) ↦ insert_subdivision_labels u j.castSucc k.castSucc) =
      j.succ.insertNth (u j.castSucc) (fun k : Fin n ↦ u k.castSucc) := by
  -- The label tuple behaves the same way: away from the duplicated entry, dropping the last label
  -- commutes with inserting a duplicate into the prefix.
  funext k
  cases k using Fin.succAboveCases j.succ with
  | x =>
      simp [insert_subdivision_labels]
  | p m =>
      rw [← Fin.castSucc_succAbove_castSucc]
      simp [insert_subdivision_labels]

/-- Helper for Theorem 2.7.1: after inserting a breakpoint into a nonterminal interval of the
prefix tuple `fun k ↦ t k.castSucc`, the last prefix point is still the original penultimate
subdivision point. -/
theorem insert_subdivision_points_castSucc_prefix_last
    {n : ℕ} (t : Fin (n + 2) → I) (j : Fin n) (c : I) :
    (((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) :
        Fin (n + 2) → I) (Fin.last (n + 1))) =
      t (Fin.castSucc (Fin.last n)) := by
  -- Evaluate the inserted prefix tuple at its last point using the generic "above the insertion"
  -- computation rule, then identify the predecessor of the last point.
  have hlt : j.succ.castSucc < Fin.last (n + 1) := by
    simpa using j.succ.castSucc_lt_last
  rw [Fin.insertNth_apply_above hlt]
  have hpred :
      ((Fin.last (n + 1)).pred (by simpa using hlt.ne)).castSucc =
        Fin.castSucc (Fin.last n) := by
    ext
    simp
  simpa [hpred]

/-- Helper for Theorem 2.7.1: the breakpoint-inserted list of subdivision points obtained by
splitting the final interval of `t` at `c`. -/
abbrev split_last_subdivision_points
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) : Fin (n + 3) → I :=
  Fin.snoc (Fin.snoc (Fin.init t) c) (t (Fin.last (n + 1)))

/-- Helper for Theorem 2.7.1: the cover labels for the subdivision obtained by repeating the final
label on the two pieces created by splitting the last interval. -/
abbrev split_last_subdivision_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) :
    Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O :=
  Fin.snoc u (u (Fin.last n))

/-- Helper for Theorem 2.7.1: the refined subdivision keeps the original terminal point as its
new final point. -/
@[simp] theorem split_last_subdivision_points_last
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) :
    split_last_subdivision_points t c (Fin.last (n + 2)) = t (Fin.last (n + 1)) := by
  simp [split_last_subdivision_points]

/-- Helper for Theorem 2.7.1: the refined subdivision keeps the original initial point as its
initial point. -/
@[simp] theorem split_last_subdivision_points_zero
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) :
    split_last_subdivision_points t c 0 = t 0 := by
  simp [split_last_subdivision_points, Fin.init_def]

/-- Helper for Theorem 2.7.1: the inserted breakpoint becomes the penultimate point of the refined
subdivision. -/
@[simp] theorem split_last_subdivision_points_castSucc_last
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) :
    split_last_subdivision_points t c (Fin.castSucc (Fin.last (n + 1))) = c := by
  simp [split_last_subdivision_points]

/-- Helper for Theorem 2.7.1: away from the final split, cast-successor indices recover the
original subdivision points. -/
@[simp] theorem split_last_subdivision_points_castSucc_castSucc
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) (k : Fin (n + 1)) :
    split_last_subdivision_points t c k.castSucc.castSucc = t k.castSucc := by
  rw [split_last_subdivision_points, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.init_def]

/-- Helper for Theorem 2.7.1: the successor of the original final unchanged prefix point is the
inserted breakpoint. -/
@[simp] theorem split_last_subdivision_points_castSucc_succ_last
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) :
    split_last_subdivision_points t c (Fin.last n).castSucc.succ = c := by
  -- Rewrite the successor of the unchanged final prefix point as a cast-successor so that the
  -- outer `Fin.snoc` exposes the inner breakpoint insertion directly.
  rw [split_last_subdivision_points, ← Fin.castSucc_succ (Fin.last n), Fin.snoc_castSucc]
  simp

/-- Helper for Theorem 2.7.1: the successor of an unchanged refined point is the corresponding
successor in the original subdivision. -/
@[simp] theorem split_last_subdivision_points_castSucc_succ
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) (l : Fin n) :
    split_last_subdivision_points t c l.castSucc.castSucc.succ = t l.castSucc.succ := by
  rw [split_last_subdivision_points, ← Fin.castSucc_succ l.castSucc, Fin.snoc_castSucc,
    ← Fin.castSucc_succ l, Fin.snoc_castSucc, Fin.init_def]

/-- Helper for Theorem 2.7.1: the repeated-label tuple agrees with the original labels on all
cast-successor indices. -/
@[simp] theorem split_last_subdivision_labels_castSucc
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) (k : Fin (n + 1)) :
    split_last_subdivision_labels u k.castSucc = u k := by
  simp [split_last_subdivision_labels]

/-- Helper for Theorem 2.7.1: the new terminal label is the original final label. -/
@[simp] theorem split_last_subdivision_labels_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) :
    split_last_subdivision_labels u (Fin.last (n + 1)) = u (Fin.last n) := by
  simp [split_last_subdivision_labels]

/-- Helper for Theorem 2.7.1: inserting a breakpoint in the terminal interval duplicates the last
label tuple entry, so the arbitrary-insertion label data specializes to the existing split-last
label tuple. -/
@[simp] theorem insert_subdivision_labels_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)} {n : ℕ}
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) :
    insert_subdivision_labels u (Fin.last n) = split_last_subdivision_labels u := by
  -- At the last interval the arbitrary insertion model and the dedicated split-last model agree
  -- entrywise, so later induction can use the established split-last API as its base case.
  funext k
  cases k using Fin.lastCases with
  | last =>
      simp [insert_subdivision_labels, split_last_subdivision_labels]
  | cast l =>
      simp [insert_subdivision_labels, split_last_subdivision_labels]

/-- Helper for Theorem 2.7.1: inserting a breakpoint into the terminal interval gives the same
point tuple as the dedicated split-last refinement. -/
@[simp] theorem insert_subdivision_points_last
    {n : ℕ} (t : Fin (n + 2) → I) (c : I) :
    insert_subdivision_points t (Fin.last n) c = split_last_subdivision_points t c := by
  -- Compare the two tuple constructions entrywise on the unchanged prefix, the new breakpoint,
  -- and the final original endpoint.
  funext k
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · simpa [insert_subdivision_points, split_last_subdivision_points, Fin.succ_last] using
      insert_subdivision_points_right_endpoint t (Fin.last n) c
  · refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · simp [insert_subdivision_points, split_last_subdivision_points]
    · simpa [insert_subdivision_points, split_last_subdivision_points] using
        (insert_subdivision_points_unchanged_castSucc t (Fin.last n) c l)

/-- Helper for Theorem 2.7.1: if the last subdivision interval stays inside one chosen open set,
then splitting that interval at an intermediate breakpoint produces a refined subdivision that is
still subordinate to the repeated cover labels. -/
theorem split_last_subdivision_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (c : I)
    (hac : t (Fin.castSucc (Fin.last n)) ≤ c)
    (hcb : c ≤ t (Fin.last (n + 1))) :
    ∀ k : Fin (n + 2),
      Set.range
          (γ.subpath
            ((split_last_subdivision_points t c) k.castSucc)
            ((split_last_subdivision_points t c) k.succ)) ⊆
        O ((split_last_subdivision_labels u) k) := by
  intro k
  -- Split the refined interval index into the unchanged prefix, the new left terminal piece, and
  -- the new right terminal piece created by breaking the original final interval at `c`.
  refine Fin.lastCases ?_ (fun j ↦ ?_) k
  · -- The final refined interval is the right half of the original last segment.
    have hright :
        Set.range (γ.subpath c (t (Fin.last (n + 1)))) ⊆ O (u (Fin.last n)) :=
      subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n))
    rw [Fin.succ_last, split_last_subdivision_points_castSucc_last,
      split_last_subdivision_points_last, split_last_subdivision_labels_last]
    exact hright
  · refine Fin.lastCases ?_ (fun l ↦ ?_) j
    · -- The penultimate refined interval is the left half of the original last segment.
      have hleft :
          Set.range (γ.subpath (t (Fin.castSucc (Fin.last n))) c) ⊆ O (u (Fin.last n)) :=
        subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))
      rw [split_last_subdivision_points_castSucc_castSucc,
        split_last_subdivision_points_castSucc_succ_last, split_last_subdivision_labels_castSucc]
      exact hleft
    · -- Every earlier refined interval agrees with the corresponding original interval.
      rw [split_last_subdivision_points_castSucc_castSucc,
        split_last_subdivision_points_castSucc_succ, split_last_subdivision_labels_castSucc]
      exact hu l.castSucc

/-- Helper for Theorem 2.7.1: for fixed subdivision points and labels, `subdivision_morphism`
does not depend on which proof family witnesses that each segment stays inside the chosen cover
member. -/
theorem subdivision_morphism_subordinate_proof_irrel
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu hu' : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu =
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu' := by
  -- The subordinate family is a `Pi`-type of proofs, so proof irrelevance identifies any two
  -- witnesses before `subdivision_morphism` ever inspects them computationally.
  have hproof : hu = hu' := Subsingleton.elim _ _
  subst hproof
  rfl

/-- Helper for Theorem 2.7.1: `subdivision_morphism` is heterogeneously unchanged when the
subdivision point tuple and label tuple are replaced by equal data. -/
theorem subdivision_morphism_heq_of_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    {t t' : Fin (n + 1) → I}
    {u u' : Fin n → TopologicalSpace.IsOpenCover.Index O}
    (ht : t = t')
    (hu : u = u')
    {hsub : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
    {hsub' : ∀ k : Fin n, Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)} :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hsub ≍
      subdivision_morphism O hO hinter S γ
        (t := t')
        (u := u')
        hsub' := by
  -- After rewriting the point and label tuples, the only remaining difference is the proof family,
  -- which disappears by proof irrelevance.
  cases ht
  cases hu
  have hproof : hsub = hsub' := Subsingleton.elim _ _
  subst hproof
  rfl

/-- Helper for Theorem 2.7.1: `subdivision_morphism` is heterogeneously unchanged when the
subdivision length is transported along an equality and the point and label tuples are casted
accordingly. -/
theorem subdivision_morphism_heq_of_cast_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n n' : ℕ}
    (hn : n = n')
    {t : Fin (n + 1) → I}
    {u : Fin n → TopologicalSpace.IsOpenCover.Index O}
    {t' : Fin (n' + 1) → I}
    {u' : Fin n' → TopologicalSpace.IsOpenCover.Index O}
    (ht : t = fun q ↦ t' (Fin.cast (congrArg Nat.succ hn) q))
    (hu : u = fun q ↦ u' (Fin.cast hn q))
    {hsub : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
    {hsub' : ∀ k : Fin n', Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)} :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hsub ≍
      subdivision_morphism O hO hinter S γ
        (t := t')
        (u := u')
        hsub' := by
  -- Reduce the length transport to the already-proved same-length comparison.
  cases hn
  simp at ht hu
  exact subdivision_morphism_heq_of_eq hO hinter S γ ht hu

/-- Helper for Theorem 2.7.1: after one recursive unfold of a nonterminal breakpoint insertion,
the remaining prefix composite is exactly the smaller insertion problem on the original prefix
subdivision. -/
theorem subdivision_morphism_insert_prefix_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin n)
    (c : I)
    (hac : t j.castSucc.castSucc ≤ c)
    (hcb : c ≤ t j.castSucc.succ)
    (hprefix :
      ∀ k : Fin (n + 1),
        Set.range
            (γ.subpath
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.castSucc))
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.succ))) ⊆
          O ((((j.succ.insertNth (u j.castSucc) (fun l : Fin n ↦ u l.castSucc)) :
            Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) k))) :
    subdivision_morphism O hO hinter S γ
        (t := fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc)
        (u := fun k : Fin (n + 1) ↦ insert_subdivision_labels u j.castSucc k.castSucc)
        (fun k : Fin (n + 1) ↦
          insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb k.castSucc) ≍
      subdivision_morphism O hO hinter S γ
        (t := ((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) :
          Fin (n + 2) → I))
        (u := ((j.succ.insertNth (u j.castSucc) (fun k : Fin n ↦ u k.castSucc)) :
          Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O))
        hprefix := by
  -- Route correction: normalize the recursive prefix by commuting `castSucc` past insertion
  -- before attempting any breakpoint-insertion induction.
  simpa using
    (subdivision_morphism_heq_of_eq
      (hO := hO) (hinter := hinter) (S := S) (γ := γ)
      (t := fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc)
      (u := fun k : Fin (n + 1) ↦ insert_subdivision_labels u j.castSucc k.castSucc)
      (t' := ((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) :
        Fin (n + 2) → I))
      (u' := ((j.succ.insertNth (u j.castSucc) (fun k : Fin n ↦ u k.castSucc)) :
        Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O))
      (ht := insert_subdivision_points_castSucc_prefix t j c)
      (hu := insert_subdivision_labels_castSucc_prefix u j))

/-- Helper for Theorem 2.7.1: if a breakpoint is inserted in a nonterminal interval, then the last
local segment of the refined subdivision is still the original terminal local segment. This is the
transport-stable tail comparison that will later be paired with
`subdivision_morphism_insert_prefix_heq` to build the full nonterminal normal form. -/
theorem subdivision_morphism_insert_nonterminal_terminal_segment_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin n)
    (c : I)
    (hac : t j.castSucc.castSucc ≤ c)
    (hcb : c ≤ t j.castSucc.succ) :
    local_subpath_morphism O hO hinter S γ
          (insert_subdivision_points t j.castSucc c (Fin.castSucc (Fin.last (n + 1))))
          (insert_subdivision_points t j.castSucc c (Fin.last (n + 2)))
          (insert_subdivision_labels u j.castSucc (Fin.last (n + 1)))
          (insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb (Fin.last (n + 1))) ≍
      local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)) := by
  have hlast_index :
      j.castSucc.succ.succAbove (Fin.last n) = Fin.last (n + 1) := by
    simpa using
      (Fin.succAbove_ne_last_last
        (a := j.castSucc.succ)
        (h := Fin.succ_ne_last_iff.mpr j.castSucc_ne_last))
  have hleft_eq :
      insert_subdivision_points t j.castSucc c (Fin.castSucc (Fin.last (n + 1))) =
        t (Fin.castSucc (Fin.last n)) := by
    simpa [hlast_index] using
      (insert_subdivision_points_unchanged_castSucc t j.castSucc c (Fin.last n))
  have hright_eq :
      insert_subdivision_points t j.castSucc c (Fin.last (n + 2)) =
        t (Fin.last (n + 1)) := by
    have hm : (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
      exact fun h => j.castSucc_ne_last h.symm
    simpa [Fin.succ_last, hlast_index] using
      (insert_subdivision_points_unchanged_succ t j.castSucc (Fin.last n) c hm)
  have hlabel_eq :
      insert_subdivision_labels u j.castSucc (Fin.last (n + 1)) =
        u (Fin.last n) := by
    simpa [hlast_index] using
      (insert_subdivision_labels_unchanged u j.castSucc (Fin.last n))
  -- The inserted breakpoint lies strictly before the final interval, so the terminal local
  -- segment of the refined subdivision is literally the original final segment.
  refine local_subpath_morphism_heq_of_eq hO hinter S γ hleft_eq hright_eq hlabel_eq

/-- Helper for Theorem 2.7.1: after unfolding a nonterminal breakpoint insertion once, the
refined subdivision composite is the inserted-prefix composite followed by the unchanged terminal
segment, with the midpoint transport exposed explicitly. -/
theorem subdivision_morphism_insert_nonterminal_normal_form_with_transport
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin n)
    (c : I)
    (hac : t j.castSucc.castSucc ≤ c)
    (hcb : c ≤ t j.castSucc.succ)
    (hprefix :
      ∀ k : Fin (n + 1),
        Set.range
            (γ.subpath
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.castSucc))
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.succ))) ⊆
          O ((((j.succ.insertNth (u j.castSucc) (fun l : Fin n ↦ u l.castSucc)) :
            Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) k))) :
    subdivision_morphism O hO hinter S γ
        (t := insert_subdivision_points t j.castSucc c)
        (u := insert_subdivision_labels u j.castSucc)
        (insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb) ≍
      subdivision_morphism O hO hinter S γ
          (t := ((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) :
            Fin (n + 2) → I))
          (u := ((j.succ.insertNth (u j.castSucc) (fun k : Fin n ↦ u k.castSucc)) :
            Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O))
          hprefix ≫
        eqToHom
          (congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z))
            (insert_subdivision_points_castSucc_prefix_last t j c)) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)) := by
  -- Route correction: make the midpoint transport between the normalized recursive prefix and the
  -- unchanged terminal segment explicit before composing the two existing HEq comparisons.
  rw [subdivision_morphism]
  have hprefix_heq :=
    subdivision_morphism_insert_prefix_heq hO hinter S γ t u hu j c hac hcb hprefix
  have htail_heq :=
    subdivision_morphism_insert_nonterminal_terminal_segment_heq hO hinter S γ t u hu j c hac hcb
  set tprefix : Fin (n + 2) → I :=
    ((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) : Fin (n + 2) → I)
  have hsource_point :
      (fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc) 0 =
        tprefix 0 := by
    -- Evaluate the prefix-normalization equality at the initial point.
    simpa using
      congrArg (fun f : (Fin (n + 2) → I) => f 0)
        (insert_subdivision_points_castSucc_prefix t j c)
  have hsource :
      chosen_cover_object O hO S
          (γ ((fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc) 0)) =
        chosen_cover_object O hO S (γ (tprefix 0)) := by
    -- The refined recursive prefix and the explicit inserted-prefix tuple have the same initial
    -- point because `castSucc` commutes with insertion on the prefix.
    simpa using congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hsource_point
  have hmid_point :
      (fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc)
          (Fin.last (n + 1)) =
        tprefix (Fin.last (n + 1)) := by
    -- Evaluate the same tuple equality at the recursive breakpoint where the tail begins.
    simpa using
      congrArg (fun f : (Fin (n + 2) → I) => f (Fin.last (n + 1)))
        (insert_subdivision_points_castSucc_prefix t j c)
  have hmid :
      chosen_cover_object O hO S
          (γ ((fun k : Fin (n + 2) ↦ insert_subdivision_points t j.castSucc c k.castSucc)
            (Fin.last (n + 1)))) =
        chosen_cover_object O hO S (γ (tprefix (Fin.last (n + 1)))) := by
    -- The same prefix-normalization identifies the recursive midpoint where the unchanged tail
    -- starts.
    simpa using congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hmid_point
  have htarget_point :
      insert_subdivision_points t j.castSucc c (Fin.last (n + 2)) =
        t (Fin.last (n + 1)) := by
    -- Because the split interval is nonterminal, the final subdivision point is untouched.
    have hm : (Fin.last n : Fin (n + 1)) ≠ j.castSucc := by
      exact fun h => j.castSucc_ne_last h.symm
    simpa [Fin.succ_last] using
      (insert_subdivision_points_unchanged_succ t j.castSucc (Fin.last n) c hm)
  have htarget :
      chosen_cover_object O hO S (γ (insert_subdivision_points t j.castSucc c (Fin.last (n + 2)))) =
        chosen_cover_object O hO S (γ (t (Fin.last (n + 1)))) := by
    -- Apply the unchanged-final-point identity at the chosen endpoint object level.
    exact congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) htarget_point
  have htail_transport :
      local_subpath_morphism O hO hinter S γ
          (insert_subdivision_points t j.castSucc c (Fin.castSucc (Fin.last (n + 1))))
          (insert_subdivision_points t j.castSucc c (Fin.last (n + 2)))
          (insert_subdivision_labels u j.castSucc (Fin.last (n + 1)))
          (insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb (Fin.last (n + 1))) ≍
        eqToHom
          (congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z))
            (insert_subdivision_points_castSucc_prefix_last t j c)) ≫
          local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last n)))
            (t (Fin.last (n + 1)))
            (u (Fin.last n))
            (hu (Fin.last n)) := by
    -- The tail comparison already proves the refined terminal piece is the original one; add only
    -- the midpoint transport needed to match the codomain of the normalized prefix.
    exact
      (CategoryTheory.heq_eqToHom_comp_iff
        (local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)))
        (local_subpath_morphism O hO hinter S γ
          (insert_subdivision_points t j.castSucc c (Fin.castSucc (Fin.last (n + 1))))
          (insert_subdivision_points t j.castSucc c (Fin.last (n + 2)))
          (insert_subdivision_labels u j.castSucc (Fin.last (n + 1)))
          (insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb (Fin.last (n + 1))))
        (congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z))
          (insert_subdivision_points_castSucc_prefix_last t j c))).2 htail_heq
  -- Compose the recursive-prefix normalization with the transported tail comparison.
  simpa using
    (CategoryTheory.heq_comp hsource hmid htarget hprefix_heq htail_transport)

/-- Helper for Theorem 2.7.1: once the explicit inserted-prefix subdivision composite has been
identified with the original recursive prefix composite, the midpoint transport exposed by
`subdivision_morphism_insert_nonterminal_normal_form_with_transport` cancels against the unchanged
terminal local morphism. -/
theorem subdivision_morphism_insert_nonterminal_transport_cancel
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin n)
    (c : I)
    (hac : t j.castSucc.castSucc ≤ c)
    (hcb : c ≤ t j.castSucc.succ)
    (hprefix :
      ∀ k : Fin (n + 1),
        Set.range
            (γ.subpath
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.castSucc))
              ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
                Fin (n + 2) → I) k.succ))) ⊆
          O ((((j.succ.insertNth (u j.castSucc) (fun l : Fin n ↦ u l.castSucc)) :
            Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O) k)))
    (hprefix_eq :
      subdivision_morphism O hO hinter S γ
          (t := ((j.succ.castSucc.insertNth c (fun k : Fin (n + 1) ↦ t k.castSucc)) :
            Fin (n + 2) → I))
          (u := ((j.succ.insertNth (u j.castSucc) (fun k : Fin n ↦ u k.castSucc)) :
            Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O))
          hprefix ≍
        subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc)) :
    subdivision_morphism O hO hinter S γ
        (t := insert_subdivision_points t j.castSucc c)
        (u := insert_subdivision_labels u j.castSucc)
        (insert_subdivision_subordinate γ t u hu j.castSucc c hac hcb) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)) := by
  have hnormal :=
    subdivision_morphism_insert_nonterminal_normal_form_with_transport
      hO hinter S γ t u hu j c hac hcb hprefix
  have hmid :
      chosen_cover_object O hO S
          (γ
            ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 1) ↦ t l.castSucc)) :
              Fin (n + 2) → I) (Fin.last (n + 1))))) =
        chosen_cover_object O hO S (γ (t (Fin.castSucc (Fin.last n)))) := by
    -- Evaluate the explicit inserted-prefix tuple at its final breakpoint, then transport that
    -- endpoint object back to the original recursive prefix endpoint.
    simpa using
      congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z))
        (insert_subdivision_points_castSucc_prefix_last t j c)
  have htail_cancel :
      eqToHom hmid ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)) ≍
      local_subpath_morphism O hO hinter S γ
        (t (Fin.castSucc (Fin.last n)))
        (t (Fin.last (n + 1)))
        (u (Fin.last n))
        (hu (Fin.last n)) := by
    -- The exposed midpoint transport is redundant once the unchanged tail is viewed from the
    -- original recursive breakpoint.
    simpa using
      (CategoryTheory.eqToHom_comp_heq
        (local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n)))
        hmid)
  -- Replace the explicit inserted-prefix composite by the recursive prefix supplied by the
  -- induction hypothesis, then remove the now-redundant midpoint transport before the unchanged
  -- terminal segment.
  exact hnormal.trans <|
    CategoryTheory.heq_comp rfl
      hmid
      rfl
      hprefix_eq
      htail_cancel

/-- Helper for Theorem 2.7.1: when a breakpoint is inserted before the terminal interval, the
recursively truncated refined subdivision is itself cover-subordinate. This packages the prefix
data in the literal form needed by the nonterminal insertion normal form and by the smaller
induction problem. -/
theorem inserted_prefix_subdivision_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 3) → I)
    (u : Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 2), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin (n + 1))
    (c : I)
    (hac : t j.castSucc.castSucc ≤ c)
    (hcb : c ≤ t j.castSucc.succ) :
    ∀ k : Fin (n + 2),
      Set.range
          (γ.subpath
            ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 2) ↦ t l.castSucc)) :
              Fin (n + 3) → I) k.castSucc))
            ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 2) ↦ t l.castSucc)) :
              Fin (n + 3) → I) k.succ))) ⊆
        O ((((j.succ.insertNth (u j.castSucc) (fun l : Fin (n + 1) ↦ u l.castSucc)) :
          Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O) k)) := by
  intro k
  -- Rewrite the truncated refined tuple back to the ambient inserted subdivision and reuse the
  -- already proved insertion lemma on the original prefix tuple itself.
  simpa [insert_subdivision_points, insert_subdivision_labels] using
    insert_subdivision_subordinate γ
      (fun l : Fin (n + 2) ↦ t l.castSucc)
      (fun l : Fin (n + 1) ↦ u l.castSucc)
      (fun l : Fin (n + 1) ↦ hu l.castSucc)
      j c hac hcb k

/-- Helper for Theorem 2.7.1: after unfolding the split-last refinement once, the remaining
refined prefix composite is the original prefix composite followed by the new left terminal
segment. -/
theorem subdivision_morphism_split_last_prefix_normal_form
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (c : I)
    (hac : t (Fin.castSucc (Fin.last n)) ≤ c)
    (hcb : c ≤ t (Fin.last (n + 1))) :
    subdivision_morphism O hO hinter S γ
        (t := fun k ↦ split_last_subdivision_points t c k.castSucc)
        (u := fun k ↦ split_last_subdivision_labels u k.castSucc)
        (fun k : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb k.castSucc) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          (subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))) := by
  -- Route correction: isolate the recursive prefix before comparing the final right split piece.
  have hleft :
      Set.range (γ.subpath (t (Fin.castSucc (Fin.last n))) c) ⊆ O (u (Fin.last n)) :=
    subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))
  -- Unfold the refined prefix once so that the recursive prefix and the new left terminal piece
  -- can be normalized separately.
  rw [subdivision_morphism]
  have hprefix_rec :
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ (fun j ↦ split_last_subdivision_points t c j.castSucc) k.castSucc)
          (u := fun k ↦ (fun j ↦ split_last_subdivision_labels u j.castSucc) k.castSucc)
          (fun k : Fin n ↦
            (fun j : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb j.castSucc)
              k.castSucc) ≍
        subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) := by
    -- The recursively refined prefix agrees with the original prefix after simplifying the
    -- doubly cast split-last tuples.
    refine subdivision_morphism_heq_of_eq hO hinter S γ ?_ ?_
    · funext k
      simp [Fin.init_def]
    · funext k
      simp
  have hleft_segment :
      local_subpath_morphism O hO hinter S γ
          ((fun j ↦ split_last_subdivision_points t c j.castSucc) (Fin.castSucc (Fin.last n)))
          ((fun j ↦ split_last_subdivision_points t c j.castSucc) (Fin.last (n + 1)))
          ((fun j ↦ split_last_subdivision_labels u j.castSucc) (Fin.last n))
          ((fun j : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb j.castSucc)
            (Fin.last n)) ≍
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          hleft := by
    -- The terminal segment of the refined prefix is exactly the left half of the original last
    -- interval after simplifying the cast-successor indices.
    refine local_subpath_morphism_heq_of_eq hO hinter S γ ?_ ?_ ?_
    · simp [Fin.init_def]
    · simp
    · simp
  have hfull :
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ (fun j ↦ split_last_subdivision_points t c j.castSucc) k.castSucc)
          (u := fun k ↦ (fun j ↦ split_last_subdivision_labels u j.castSucc) k.castSucc)
          (fun k : Fin n ↦
            (fun j : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb j.castSucc)
              k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          ((fun j ↦ split_last_subdivision_points t c j.castSucc) (Fin.castSucc (Fin.last n)))
          ((fun j ↦ split_last_subdivision_points t c j.castSucc) (Fin.last (n + 1)))
          ((fun j ↦ split_last_subdivision_labels u j.castSucc) (Fin.last n))
          ((fun j : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb j.castSucc)
            (Fin.last n)) ≍
        subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          hleft := by
    refine CategoryTheory.heq_comp ?_ ?_ ?_ hprefix_rec hleft_segment
    · simp [Fin.init_def]
    · simp [Fin.init_def]
    · simp
  simpa using hfull

/-- Helper for Theorem 2.7.1: the final segment of the split-last refinement is exactly the right
half of the original terminal interval, viewed as a local cover morphism. -/
theorem split_last_terminal_local_subpath_morphism
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (c : I)
    (hac : t (Fin.castSucc (Fin.last n)) ≤ c)
    (hcb : c ≤ t (Fin.last (n + 1))) :
    local_subpath_morphism O hO hinter S γ
        (split_last_subdivision_points t c (Fin.last (n + 1)).castSucc)
        (split_last_subdivision_points t c (Fin.last (n + 1 + 1)))
        (split_last_subdivision_labels u (Fin.last (n + 1)))
        (split_last_subdivision_subordinate γ t u hu c hac hcb (Fin.last (n + 1))) ≍
      local_subpath_morphism O hO hinter S γ
        c
        (t (Fin.last (n + 1)))
        (u (Fin.last n))
        (subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n))) := by
  -- Route correction: keep the endpoint-transport comparison for the terminal right piece
  -- separate from the recursive prefix normalization, so the main split-last theorem only composes
  -- two semantic helpers instead of mixing both transport problems.
  -- Normalize the split-last endpoint and label data first, then remove the remaining subordinate
  -- proof mismatch by proof irrelevance through `local_subpath_morphism_heq_of_eq`.
  refine
    local_subpath_morphism_heq_of_eq hO hinter S γ
      (a := split_last_subdivision_points t c (Fin.last (n + 1)).castSucc)
      (a' := c)
      (b := split_last_subdivision_points t c (Fin.last (n + 1 + 1)))
      (b' := t (Fin.last (n + 1)))
      (i := split_last_subdivision_labels u (Fin.last (n + 1)))
      (i' := u (Fin.last n))
      (hsub := split_last_subdivision_subordinate γ t u hu c hac hcb (Fin.last (n + 1)))
      (hsub' := subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n)))
      ?_ ?_ ?_
  · simp
  · simp
  · simp

/-- Helper for Theorem 2.7.1: after splitting the final interval of a subdivision, the refined
subdivision composite is the unchanged prefix composite followed by the two new terminal local
segment morphisms. -/
theorem subdivision_morphism_split_last_normal_form
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (c : I)
    (hac : t (Fin.castSucc (Fin.last n)) ≤ c)
    (hcb : c ≤ t (Fin.last (n + 1))) :
    subdivision_morphism O hO hinter S γ
        (t := split_last_subdivision_points t c)
        (u := split_last_subdivision_labels u)
        (split_last_subdivision_subordinate γ t u hu c hac hcb) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          (subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))) ≫
        local_subpath_morphism O hO hinter S γ
          c
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n))) := by
  have hleft :
      Set.range (γ.subpath (t (Fin.castSucc (Fin.last n))) c) ⊆ O (u (Fin.last n)) :=
    subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))
  have hright :
      Set.range (γ.subpath c (t (Fin.last (n + 1)))) ⊆ O (u (Fin.last n)) :=
    subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n))
  have hprefix :=
    subdivision_morphism_split_last_prefix_normal_form hO hinter S γ t u hu c hac hcb
  have hright_segment :
      local_subpath_morphism O hO hinter S γ
          (split_last_subdivision_points t c (Fin.last (n + 1)).castSucc)
          (split_last_subdivision_points t c (Fin.last (n + 1 + 1)))
          (split_last_subdivision_labels u (Fin.last (n + 1)))
          (split_last_subdivision_subordinate γ t u hu c hac hcb (Fin.last (n + 1))) ≍
        local_subpath_morphism O hO hinter S γ
          c
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          hright :=
    split_last_terminal_local_subpath_morphism hO hinter S γ t u hu c hac hcb
  -- Unfold the outer recursion once, then replace the refined prefix by the semantic prefix
  -- normal form and identify the terminal right segment by simplification.
  rw [subdivision_morphism]
  have hfull :
      subdivision_morphism O hO hinter S γ
          (t := fun k ↦ split_last_subdivision_points t c k.castSucc)
          (u := fun k ↦ split_last_subdivision_labels u k.castSucc)
          (fun k : Fin (n + 1) ↦ split_last_subdivision_subordinate γ t u hu c hac hcb k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (split_last_subdivision_points t c (Fin.last (n + 1)).castSucc)
          (split_last_subdivision_points t c (Fin.last (n + 1 + 1)))
          (split_last_subdivision_labels u (Fin.last (n + 1)))
          (split_last_subdivision_subordinate γ t u hu c hac hcb (Fin.last (n + 1))) ≍
      (subdivision_morphism O hO hinter S γ
          (t := fun k ↦ t k.castSucc)
          (u := fun k ↦ u k.castSucc)
          (fun k : Fin n ↦ hu k.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          hleft) ≫
        local_subpath_morphism O hO hinter S γ
          c
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          hright := by
    refine CategoryTheory.heq_comp ?_ ?_ ?_ hprefix hright_segment
    · simp [split_last_subdivision_points, Fin.init_def]
    · simp [split_last_subdivision_points, Fin.init_def]
    · simp [split_last_subdivision_points, Fin.init_def]
  simpa [Category.assoc] using hfull

/-- Helper for Theorem 2.7.1: splitting the final subdivision interval at an intermediate
breakpoint does not change the resulting cocone-target subdivision composite. -/
theorem subdivision_morphism_split_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (c : I)
    (hac : t (Fin.castSucc (Fin.last n)) ≤ c)
    (hcb : c ≤ t (Fin.last (n + 1))) :
    subdivision_morphism O hO hinter S γ
        (t := split_last_subdivision_points t c)
        (u := split_last_subdivision_labels u)
        (split_last_subdivision_subordinate γ t u hu c hac hcb) ≍
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  have hleft :
      Set.range (γ.subpath (t (Fin.castSucc (Fin.last n))) c) ⊆ O (u (Fin.last n)) :=
    subpath_range_subset_of_subpath_range_subset γ le_rfl hac hcb (hu (Fin.last n))
  have hright :
      Set.range (γ.subpath c (t (Fin.last (n + 1)))) ⊆ O (u (Fin.last n)) :=
    subpath_range_subset_of_subpath_range_subset γ hac hcb le_rfl (hu (Fin.last n))
  -- Rewrite the refinement as the unchanged prefix followed by the two split terminal factors.
  have hnormal :=
    subdivision_morphism_split_last_normal_form hO hinter S γ t u hu c hac hcb
  have hcollapse :
      local_subpath_morphism O hO hinter S γ
          (t (Fin.castSucc (Fin.last n)))
          c
          (u (Fin.last n))
          hleft ≫
        local_subpath_morphism O hO hinter S γ
          c
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          hright =
      local_subpath_morphism O hO hinter S γ
        (t (Fin.castSucc (Fin.last n)))
        (t (Fin.last (n + 1)))
        (u (Fin.last n))
        (hu (Fin.last n)) := by
    -- The last two refined pieces lie in the same open set, so the local van Kampen step merges
    -- them back into the original unsplit terminal piece.
    exact local_subpath_morphism_trans hO hinter S γ _ _ _ hac hcb _ (hu (Fin.last n))
  -- Replace the split terminal factors by the original final segment of the unsplit subdivision.
  simpa [subdivision_morphism, hcollapse] using hnormal

/-- Helper for Theorem 2.7.1: inserting an intermediate breakpoint into any subordinate
subdivision interval does not change the resulting cocone-target subdivision composite. -/
theorem subdivision_morphism_eq_of_insert_breakpoint
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (j : Fin (n + 1))
    (c : I)
    (hac : t j.castSucc ≤ c)
    (hcb : c ≤ t j.succ) :
    subdivision_morphism O hO hinter S γ
        (t := insert_subdivision_points t j c)
        (u := insert_subdivision_labels u j)
        (insert_subdivision_subordinate γ t u hu j c hac hcb) ≍
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  -- Route correction: prove ordinary insertion invariance directly by induction on the number of
  -- intervals, splitting the insertion index into the terminal and nonterminal cases.
  revert t u hu j c hac hcb
  induction n with
  | zero =>
      intro t u hu j c hac hcb
      have hj : j = Fin.last 0 := by
        ext
        simp
      subst hj
      -- The only interval is terminal, so the arbitrary insertion model reduces to split-last.
      have hrewrite :
          subdivision_morphism O hO hinter S γ
              (t := insert_subdivision_points t (Fin.last 0) c)
              (u := insert_subdivision_labels u (Fin.last 0))
              (insert_subdivision_subordinate γ t u hu (Fin.last 0) c hac hcb) ≍
            subdivision_morphism O hO hinter S γ
              (t := split_last_subdivision_points t c)
              (u := split_last_subdivision_labels u)
              (split_last_subdivision_subordinate γ t u hu c hac hcb) := by
        exact
          subdivision_morphism_heq_of_eq hO hinter S γ
            (t := insert_subdivision_points t (Fin.last 0) c)
            (u := insert_subdivision_labels u (Fin.last 0))
            (t' := split_last_subdivision_points t c)
            (u' := split_last_subdivision_labels u)
            (ht := insert_subdivision_points_last t c)
            (hu := insert_subdivision_labels_last u)
      exact hrewrite.trans (subdivision_morphism_split_last hO hinter S γ t u hu c hac hcb)
  | succ n ih =>
      intro t u hu j
      refine Fin.lastCases ?_ ?_ j
      · intro c hac hcb
        -- Terminal insertion is exactly the already proved split-last case.
        have hrewrite :
            subdivision_morphism O hO hinter S γ
                (t := insert_subdivision_points t (Fin.last (n + 1)) c)
                (u := insert_subdivision_labels u (Fin.last (n + 1)))
                (insert_subdivision_subordinate γ t u hu (Fin.last (n + 1)) c hac hcb) ≍
              subdivision_morphism O hO hinter S γ
                (t := split_last_subdivision_points t c)
                (u := split_last_subdivision_labels u)
                (split_last_subdivision_subordinate γ t u hu c hac hcb) := by
          exact
            subdivision_morphism_heq_of_eq hO hinter S γ
              (t := insert_subdivision_points t (Fin.last (n + 1)) c)
              (u := insert_subdivision_labels u (Fin.last (n + 1)))
              (t' := split_last_subdivision_points t c)
              (u' := split_last_subdivision_labels u)
              (ht := insert_subdivision_points_last t c)
              (hu := insert_subdivision_labels_last u)
        exact hrewrite.trans (subdivision_morphism_split_last hO hinter S γ t u hu c hac hcb)
      · intro j c hac hcb
        -- For a nonterminal insertion, compare the recursively truncated refined prefix with the
        -- smaller insertion problem on the original prefix, then cancel the exposed midpoint
        -- transport before the unchanged terminal segment.
        have hprefix :
            ∀ k : Fin (n + 2),
              Set.range
                  (γ.subpath
                    ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 2) ↦ t l.castSucc)) :
                      Fin (n + 3) → I) k.castSucc))
                    ((((j.succ.castSucc.insertNth c (fun l : Fin (n + 2) ↦ t l.castSucc)) :
                      Fin (n + 3) → I) k.succ))) ⊆
                O ((((j.succ.insertNth (u j.castSucc) (fun l : Fin (n + 1) ↦ u l.castSucc)) :
                  Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O) k)) :=
          inserted_prefix_subdivision_subordinate γ t u hu j c hac hcb
        have hprefix_eq :
            subdivision_morphism O hO hinter S γ
                (t := ((j.succ.castSucc.insertNth c (fun k : Fin (n + 2) ↦ t k.castSucc)) :
                  Fin (n + 3) → I))
                (u := ((j.succ.insertNth (u j.castSucc) (fun k : Fin (n + 1) ↦ u k.castSucc)) :
                  Fin (n + 2) → TopologicalSpace.IsOpenCover.Index O))
                hprefix ≍
              subdivision_morphism O hO hinter S γ
                (t := fun k ↦ t k.castSucc)
                (u := fun k ↦ u k.castSucc)
                (fun k : Fin (n + 1) ↦ hu k.castSucc) := by
          simpa [insert_subdivision_points, insert_subdivision_labels] using
            (ih
              (t := fun k : Fin (n + 2) ↦ t k.castSucc)
              (u := fun k : Fin (n + 1) ↦ u k.castSucc)
              (hu := fun k : Fin (n + 1) ↦ hu k.castSucc)
              (j := j)
              (c := c)
              (hac := hac)
              (hcb := hcb))
        simpa [subdivision_morphism] using
          (subdivision_morphism_insert_nonterminal_transport_cancel
            hO hinter S γ t u hu j c hac hcb hprefix hprefix_eq)

/-- Helper for Theorem 2.7.1: a finite refinement schedule between two subdivisions of the same
path, generated by repeatedly inserting a breakpoint inside an existing subdivision interval and
duplicating that interval's cover label on the two resulting pieces. -/
inductive subdivision_refinement
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y) :
    {n m : ℕ} →
      (t : Fin (n + 1) → I) →
      (u : Fin n → TopologicalSpace.IsOpenCover.Index O) →
      (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) →
      (t' : Fin (m + 1) → I) →
      (u' : Fin m → TopologicalSpace.IsOpenCover.Index O) →
      (hu' : ∀ k : Fin m, Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)) →
      Prop
  | refl {n : ℕ}
      (t : Fin (n + 1) → I)
      (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
      (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
      subdivision_refinement γ t u hu t u hu
  | insert {n m : ℕ}
      {t : Fin (n + 1) → I}
      {u : Fin n → TopologicalSpace.IsOpenCover.Index O}
      {hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
      {t' : Fin (m + 2) → I}
      {u' : Fin (m + 1) → TopologicalSpace.IsOpenCover.Index O}
      {hu' : ∀ k : Fin (m + 1), Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)}
      (h : subdivision_refinement γ t u hu t' u' hu')
      (j : Fin (m + 1))
      (c : I)
      (hac : t' j.castSucc ≤ c)
      (hcb : c ≤ t' j.succ) :
      subdivision_refinement γ t u hu
        (insert_subdivision_points t' j c)
        (insert_subdivision_labels u' j)
        (insert_subdivision_subordinate γ t' u' hu' j c hac hcb)

/-- Helper for Theorem 2.7.1: any finite refinement schedule built from repeated breakpoint
insertions leaves the resulting subdivision composite unchanged up to the endpoint transports
already isolated in the one-step insertion theorem. -/
theorem subdivision_morphism_heq_of_refinement
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n m : ℕ}
    {t : Fin (n + 1) → I}
    {u : Fin n → TopologicalSpace.IsOpenCover.Index O}
    {hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
    {t' : Fin (m + 1) → I}
    {u' : Fin m → TopologicalSpace.IsOpenCover.Index O}
    {hu' : ∀ k : Fin m, Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)}
    (href : subdivision_refinement (O := O) γ t u hu t' u' hu') :
    subdivision_morphism O hO hinter S γ
        (t := t')
        (u := u')
        hu' ≍
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  -- Route correction: recurse on the refinement witness itself, so the refined tuple and
  -- subordinate proof stay generalized through each insertion step.
  induction href with
  | refl t u hu =>
      -- The trivial refinement compares a subdivision with itself.
      rfl
  | @insert m t u hu t' u' hu' href j c hac hcb ih =>
      -- First remove the final insertion step by the one-step insertion theorem, then continue
      -- along the shorter refinement schedule.
      exact
        (subdivision_morphism_eq_of_insert_breakpoint
          (hO := hO) (hinter := hinter) (S := S) (γ := γ)
          (t := t') (u := u') (hu := hu') (j := j) (c := c) (hac := hac) (hcb := hcb)).trans ih

/-- Helper for Theorem 2.7.1: every subdivision obtained from a monotone one by a finite
refinement schedule is still monotone. -/
theorem subdivision_refinement_monotone
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n m : ℕ}
    {t : Fin (n + 1) → I}
    {u : Fin n → TopologicalSpace.IsOpenCover.Index O}
    {hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
    {t' : Fin (m + 1) → I}
    {u' : Fin m → TopologicalSpace.IsOpenCover.Index O}
    {hu' : ∀ k : Fin m, Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)}
    (ht : Monotone t)
    (href : subdivision_refinement (O := O) γ t u hu t' u' hu') :
    Monotone t' := by
  -- Follow the refinement witness itself: every insertion step preserves monotonicity by the
  -- previous lemma.
  induction href with
  | refl t u hu =>
      exact ht
  | @insert m t u hu t' u' hu' href j c hac hcb ih =>
      exact insert_subdivision_points_monotone (ih ht) j c hac hcb

/-- Helper for Theorem 2.7.1: every finite refinement schedule preserves the initial and terminal
breakpoints of an endpoint-normalized subdivision. -/
theorem subdivision_refinement_endpoints
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n m : ℕ}
    {t : Fin (n + 1) → I}
    {u : Fin n → TopologicalSpace.IsOpenCover.Index O}
    {hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)}
    {t' : Fin (m + 1) → I}
    {u' : Fin m → TopologicalSpace.IsOpenCover.Index O}
    {hu' : ∀ k : Fin m, Set.range (γ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)}
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (href : subdivision_refinement (O := O) γ t u hu t' u' hu') :
    t' 0 = 0 ∧ t' (Fin.last m) = 1 := by
  -- Refinement inserts points only in the interior of existing intervals, so the two endpoints
  -- remain fixed throughout the schedule.
  induction href with
  | refl t u hu =>
      exact ⟨ht0, ht1⟩
  | @insert m t u hu t' u' hu' href j c hac hcb ih =>
      rcases ih ht0 ht1 with ⟨h0, h1⟩
      exact ⟨by simpa [h0] using insert_subdivision_points_zero t' j c,
        by simpa [h1] using insert_subdivision_points_last_unchanged t' j c⟩

/-- Helper for Theorem 2.7.1: any functor factoring the canonical cover cocone must send a point
of `Π(X)` to the object obtained by evaluating the corresponding cocone leg on a chosen containing
cover member. -/
theorem factorization_obj_eq_chosen_cover_object
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt)
    (hd : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i)
    (x : πₓ (TopCat.of X)) :
    d.obj x = chosen_cover_object O hO S x.as := by
  let i := chosen_cover_index O hO x.as
  -- Evaluate the factorization identity at the chosen cover object containing `x`.
  have hobj := Functor.congr_obj (hd i) ⟨x.as, mem_chosen_cover_index O hO x.as⟩
  simpa [fundamental_groupoid_cover_cocone, chosen_cover_object, i] using hobj

/-- Helper for Theorem 2.7.1: on a path segment whose image lies in one cover member, any
factorization through the canonical cocone agrees with the corresponding local segment morphism. -/
theorem factorization_map_eq_local_subpath_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt)
    (hd : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i)
    {x y : X} (γ : Path x y) (a b : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i) :
    d.map (FundamentalGroupoid.fromPath ⟦γ.subpath a b⟧) ≍
      local_subpath_morphism O hO hinter S γ a b i hsub := by
  let p := FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub⟧
  -- Evaluate the factorization identity on the lifted local path inside `O i`, then convert the
  -- resulting conjugation formula into a heterogeneous equality with the raw functor image.
  have hmap := Functor.congr_hom (hd i) p
  have hraw :
      d.map (FundamentalGroupoid.fromPath ⟦γ.subpath a b⟧) ≍
        (S.ι.app i).map p := by
    exact
    (CategoryTheory.conj_eqToHom_iff_heq
      (d.map (FundamentalGroupoid.fromPath ⟦γ.subpath a b⟧))
      ((S.ι.app i).map p)
      (Functor.congr_obj (hd i)
        (FundamentalGroupoid.mk ⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩))
        (Functor.congr_obj (hd i)
          (FundamentalGroupoid.mk ⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩))).1
      (by
        simpa [p, Functor.comp_map, fundamental_groupoid_cover_cocone, local_subpath_morphism] using
          hmap)
  -- Compare the raw image with the canonical local morphism by removing the endpoint transports on
  -- the cocone side as well.
  exact hraw.trans (local_subpath_morphism_heq_functor_map hO hinter S γ a b i hsub).symm

/-- Helper for Theorem 2.7.1: splitting an ambient path at an intermediate parameter gives the same
morphism in the fundamental groupoid as traversing the two resulting subpaths in succession. -/
theorem fromPath_subpath_split
    {x y : X} (γ : Path x y) (a c b : I) :
    FundamentalGroupoid.fromPath ⟦γ.subpath a c⟧ ≫
        FundamentalGroupoid.fromPath ⟦γ.subpath c b⟧ =
      FundamentalGroupoid.fromPath ⟦γ.subpath a b⟧ := by
  -- Convert composition in `Π(X)` into path concatenation, then use the standard subpath
  -- concatenation homotopy.
  rw [FundamentalGroupoid.comp_eq]
  simpa [FundamentalGroupoid.fromPath, ← Path.Homotopic.Quotient.mk_trans] using
    (FundamentalGroupoid.fromPath_eq_iff_homotopic
      ((γ.subpath a c).trans (γ.subpath c b))
      (γ.subpath a b)).2
      ⟨Path.Homotopy.subpathTransSubpath γ a c b⟩

/-- Helper for Theorem 2.7.1: mapping the full subpath `γ.subpath 0 1` differs from mapping `γ`
only by the endpoint transports forced by `Path.subpath_zero_one`. -/
theorem functor_map_fromPath_subpath_zero_one_heq
    {Y : Type*} [TopologicalSpace Y]
    {C : Type*} [Category C]
    (d : πₓ (TopCat.of Y) ⥤ C)
    {x y : Y} (γ : Path x y) :
    d.map (FundamentalGroupoid.fromPath ⟦γ.subpath 0 1⟧) ≍
      d.map (FundamentalGroupoid.fromPath ⟦γ⟧) := by
  have hcast :
      FundamentalGroupoid.fromPath ⟦γ.subpath 0 1⟧ =
        eqToHom (congrArg FundamentalGroupoid.mk γ.source) ≫
          FundamentalGroupoid.fromPath ⟦γ⟧ ≫
          eqToHom (congrArg FundamentalGroupoid.mk γ.target).symm := by
    -- Rewrite the full subpath as the endpoint-cast of `γ`, then use the standard
    -- `FundamentalGroupoid.fromPath` transport formula.
    rw [Path.subpath_zero_one]
    simpa [FundamentalGroupoid.fromPath] using
      (FundamentalGroupoid.conj_eqToHom (p := γ) γ.source γ.target).symm
  exact
    (CategoryTheory.conj_eqToHom_iff_heq
      (d.map (FundamentalGroupoid.fromPath ⟦γ.subpath 0 1⟧))
      (d.map (FundamentalGroupoid.fromPath ⟦γ⟧))
      (congrArg d.obj (congrArg FundamentalGroupoid.mk γ.source))
      (congrArg d.obj (congrArg FundamentalGroupoid.mk γ.target))).1 <|
      by
        -- Apply `d` to the endpoint-transport identity and normalize the resulting `eqToHom`s.
        rw [hcast]
        change d.map (eqToHom (congrArg FundamentalGroupoid.mk γ.source) ≫
          (FundamentalGroupoid.fromPath ⟦γ⟧ ≫
            eqToHom (congrArg FundamentalGroupoid.mk γ.target).symm)) = _
        rw [d.map_comp, d.map_comp, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map]

/-- Helper for Theorem 2.7.1: once a subordinate subdivision is fixed, any factorization through
the canonical cover cocone sends the corresponding path class to the recursive subdivision
composite in the cocone target. -/
theorem factorization_map_eq_subdivision_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt)
    (hd : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i)
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    d.map (FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.last n))⟧) ≍
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  induction n with
  | zero =>
      -- With a single subdivision point, the path segment is constant, so both sides are the
      -- identity morphism.
      have hself : γ.subpath (t 0) (t (Fin.last 0)) = Path.refl (γ (t 0)) := by
        simpa using Path.subpath_self γ (t 0)
      have hx :
          d.obj (FundamentalGroupoid.mk (γ (t 0))) =
            chosen_cover_object O hO S (γ (t 0)) :=
        factorization_obj_eq_chosen_cover_object O hO S d hd (FundamentalGroupoid.mk (γ (t 0)))
      have hid :
          𝟙 (d.obj (FundamentalGroupoid.mk (γ (t 0)))) ≍
            𝟙 (chosen_cover_object O hO S (γ (t 0))) := by
        exact
          (CategoryTheory.eqToHom_heq_id_dom
            (d.obj (FundamentalGroupoid.mk (γ (t 0))))
            (chosen_cover_object O hO S (γ (t 0))) hx).symm.trans
          (CategoryTheory.eqToHom_heq_id_cod
            (d.obj (FundamentalGroupoid.mk (γ (t 0))))
            (chosen_cover_object O hO S (γ (t 0))) hx)
      have hrefl :
          FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.last 0))⟧ =
            𝟙 (FundamentalGroupoid.mk (γ (t 0))) := by
        rw [hself, FundamentalGroupoid.id_eq_path_refl]
        rfl
      have hmap_id :
          d.map (FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.last 0))⟧) =
            𝟙 (d.obj (FundamentalGroupoid.mk (γ (t 0)))) := by
        rw [hrefl]
        exact d.map_id (FundamentalGroupoid.mk (γ (t 0)))
      exact
        (by
          exact hmap_id.heq : d.map (FundamentalGroupoid.fromPath
            ⟦γ.subpath (t 0) (t (Fin.last 0))⟧) ≍
              𝟙 (d.obj (FundamentalGroupoid.mk (γ (t 0))))).trans <|
          (by simpa [subdivision_morphism] using hid)
  | succ n ih =>
      -- Peel off the final subdivision piece. The induction hypothesis handles the unchanged
      -- prefix, while the single-segment factorization lemma identifies the terminal segment.
      simp only [subdivision_morphism]
      have hsplit := fromPath_subpath_split γ
        (t 0) (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))
      rw [← hsplit]
      have hcomp :
          d.map
              (FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.castSucc (Fin.last n)))⟧ ≫
                FundamentalGroupoid.fromPath
                  ⟦γ.subpath (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))⟧) =
            d.map (FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.castSucc (Fin.last n)))⟧) ≫
              d.map (FundamentalGroupoid.fromPath
                ⟦γ.subpath (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))⟧) := by
        simpa using
          d.map_comp
            (FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.castSucc (Fin.last n)))⟧)
            (FundamentalGroupoid.fromPath
              ⟦γ.subpath (t (Fin.castSucc (Fin.last n))) (t (Fin.last (n + 1)))⟧)
      have hlast :=
        factorization_map_eq_local_subpath_morphism O hO hinter S d hd γ
          (t (Fin.castSucc (Fin.last n)))
          (t (Fin.last (n + 1)))
          (u (Fin.last n))
          (hu (Fin.last n))
      exact hcomp.heq.trans <|
        CategoryTheory.heq_comp
          (factorization_obj_eq_chosen_cover_object O hO S d hd
            (FundamentalGroupoid.mk (γ (t 0))))
          (factorization_obj_eq_chosen_cover_object O hO S d hd
            (FundamentalGroupoid.mk (γ (t (Fin.castSucc (Fin.last n))))))
          (factorization_obj_eq_chosen_cover_object O hO S d hd
            (FundamentalGroupoid.mk (γ (t (Fin.last (n + 1))))))
          (ih
            (t := fun k ↦ t k.castSucc)
            (u := fun k ↦ u k.castSucc)
            (hu := fun k ↦ hu k.castSucc))
          hlast

/-- Helper for Theorem 2.7.1: when a subordinate subdivision starts at `0` and ends at `1`, the
corresponding factorization formula evaluates the original path class itself. -/
theorem factorization_map_eq_subdivision_morphism_zero_one
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt)
    (hd : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i)
    {x y : X}
    (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1) :
    d.map (FundamentalGroupoid.fromPath ⟦γ⟧) ≍
      subdivision_morphism O hO hinter S γ (t := t) (u := u) hu := by
  have hs : γ (t 0) = x := by
    -- The initial breakpoint is forced to be `0`, so the subdivision starts at the source of `γ`.
    simp [ht0]
  have ht : γ (t (Fin.last n)) = y := by
    -- Likewise the terminal breakpoint is `1`, so the subdivision ends at the target of `γ`.
    simp [ht1]
  have hsubpath :
      γ.subpath (t 0) (t (Fin.last n)) = (γ.cast hs ht) := by
    -- After rewriting the subdivision endpoints to `0` and `1`, the subpath is just `γ` with the
    -- endpoint equalities recorded explicitly in its type.
    ext s
    simp [Path.subpath, ht0, ht1]
  have hnormalize :
      d.map (FundamentalGroupoid.fromPath
        ⟦γ.subpath (t 0) (t (Fin.last n))⟧) ≍
        d.map (FundamentalGroupoid.fromPath ⟦γ⟧) := by
    have hcast :
        FundamentalGroupoid.fromPath ⟦γ.subpath (t 0) (t (Fin.last n))⟧ =
          eqToHom (congrArg FundamentalGroupoid.mk hs) ≫
            FundamentalGroupoid.fromPath ⟦γ⟧ ≫
            eqToHom (congrArg FundamentalGroupoid.mk ht).symm := by
      -- Replace the ambient subpath by the corresponding endpoint-cast of `γ`.
      rw [hsubpath]
      simpa [FundamentalGroupoid.fromPath] using
        (FundamentalGroupoid.conj_eqToHom (p := γ) hs ht).symm
    -- Convert the resulting conjugation formula into the heterogeneous equality needed to compare
    -- the representative-level fixed-subdivision formula with the original path class.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (d.map (FundamentalGroupoid.fromPath
          ⟦γ.subpath (t 0) (t (Fin.last n))⟧))
        (d.map (FundamentalGroupoid.fromPath ⟦γ⟧))
        (congrArg d.obj (congrArg FundamentalGroupoid.mk hs))
        (congrArg d.obj (congrArg FundamentalGroupoid.mk ht))).1 <|
        by
          rw [hcast]
          change d.map (eqToHom (congrArg FundamentalGroupoid.mk hs) ≫
            (FundamentalGroupoid.fromPath ⟦γ⟧ ≫
              eqToHom (congrArg FundamentalGroupoid.mk ht).symm)) = _
          rw [d.map_comp, d.map_comp, CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map]
  -- Route correction: normalize the ambient representative first, then invoke the already proved
  -- fixed-subdivision factorization formula.
  exact hnormalize.symm.trans
    (factorization_map_eq_subdivision_morphism O hO hinter S d hd γ t u hu)

/-- Helper for Theorem 2.7.1: a factorization through the canonical cover cocone is unique once
its composites with the cover legs are fixed. -/
theorem factorization_unique_of_cover_legs
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {d d' : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt}
    (hd : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i)
    (hd' : ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d' = S.ι.app i) :
    d = d' := by
  refine Functor.hext ?_ ?_
  · intro x
    -- Both functors are forced onto the same chosen-cover object at `x`.
    exact (factorization_obj_eq_chosen_cover_object O hO S d hd x).trans
      (factorization_obj_eq_chosen_cover_object O hO S d' hd' x).symm
  · intro x y f
    refine Quotient.inductionOn f ?_
    intro γ
    obtain ⟨n, t, ht0, ht1, _hmono, u, hu⟩ := path_subdivision_data_of_open_cover O hO γ
    have hdγ :=
      factorization_map_eq_subdivision_morphism_zero_one O hO hinter S d hd γ t u hu ht0 ht1
    have hd'γ :=
      factorization_map_eq_subdivision_morphism_zero_one O hO hinter S d' hd' γ t u hu ht0 ht1
    have hdγ' :
        d.map (FundamentalGroupoid.fromPath ⟦γ⟧) ≍
          subdivision_morphism O hO hinter S γ (t := t) (u := u) hu := by
      -- The chosen subdivision begins at `0` and ends at `1`, so the ambient subpath is the
      -- original path itself.
      exact hdγ
    have hd'γ' :
        d'.map (FundamentalGroupoid.fromPath ⟦γ⟧) ≍
          subdivision_morphism O hO hinter S γ (t := t) (u := u) hu := by
      -- The same fixed subdivision computes the image under any other factorization as well.
      exact hd'γ
    exact hdγ'.trans hd'γ'.symm

/-- Helper for Theorem 2.7.1: the subdivision data chosen by `Classical.choose` for a path. -/
noncomputable abbrev chosen_subdivision_data
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :=
  path_subdivision_data_of_open_cover O hO γ

/-- Helper for Theorem 2.7.1: the chosen subdivision length attached to a path. -/
noncomputable abbrev chosen_subdivision_length
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) : ℕ :=
  Classical.choose (chosen_subdivision_data O hO γ)

/-- Helper for Theorem 2.7.1: the chosen breakpoint tuple attached to a path. -/
noncomputable abbrev chosen_subdivision_points
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    Fin (chosen_subdivision_length O hO γ + 1) → I :=
  Classical.choose (Classical.choose_spec (chosen_subdivision_data O hO γ))

/-- Helper for Theorem 2.7.1: the chosen breakpoint tuple starts at `0`. -/
theorem chosen_subdivision_points_zero
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    chosen_subdivision_points O hO γ 0 = 0 := by
  -- Unpack the first component of the chosen subdivision data.
  exact (Classical.choose_spec (Classical.choose_spec (chosen_subdivision_data O hO γ))).1

/-- Helper for Theorem 2.7.1: the chosen breakpoint tuple ends at `1`. -/
theorem chosen_subdivision_points_last
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    chosen_subdivision_points O hO γ (Fin.last (chosen_subdivision_length O hO γ)) = 1 := by
  -- The second component of the chosen subdivision data records the terminal breakpoint.
  exact (Classical.choose_spec (Classical.choose_spec (chosen_subdivision_data O hO γ))).2.1

/-- Helper for Theorem 2.7.1: the chosen cover-label tuple for the chosen subdivision of a path. -/
noncomputable abbrev chosen_subdivision_labels
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    Fin (chosen_subdivision_length O hO γ) → TopologicalSpace.IsOpenCover.Index O :=
  Classical.choose ((Classical.choose_spec (Classical.choose_spec (chosen_subdivision_data O hO γ))).2.2.2)

/-- Helper for Theorem 2.7.1: each chosen subdivision segment stays inside its chosen cover
member. -/
theorem chosen_subdivision_subordinate
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    ∀ k : Fin (chosen_subdivision_length O hO γ),
      Set.range
          (γ.subpath
            ((chosen_subdivision_points O hO γ) k.castSucc)
            ((chosen_subdivision_points O hO γ) k.succ)) ⊆
        O ((chosen_subdivision_labels O hO γ) k) := by
  -- The final component of the chosen subdivision package is exactly the subordinate proof family.
  exact
    Classical.choose_spec
      ((Classical.choose_spec (Classical.choose_spec (chosen_subdivision_data O hO γ))).2.2.2)

/-- Helper for Theorem 2.7.1: the chosen subdivision starts at the source of the path. -/
theorem chosen_subdivision_source_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    γ (chosen_subdivision_points O hO γ 0) = x := by
  -- Rewrite the initial chosen breakpoint to `0`.
  simpa [chosen_subdivision_points_zero O hO γ]

/-- Helper for Theorem 2.7.1: the chosen subdivision ends at the target of the path. -/
theorem chosen_subdivision_target_eq
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    γ (chosen_subdivision_points O hO γ (Fin.last (chosen_subdivision_length O hO γ))) = y := by
  -- Rewrite the final chosen breakpoint to `1`.
  simpa [chosen_subdivision_points_last O hO γ]

/-- Helper for Theorem 2.7.1: the chosen subdivision of a path has at least one nontrivial
interval, because its first breakpoint is `0` and its last breakpoint is `1`. -/
theorem chosen_subdivision_length_ne_zero
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    chosen_subdivision_length O hO γ ≠ 0 := by
  -- If the chosen subdivision had length `0`, its first and last breakpoints would coincide,
  -- contradicting the endpoint normalization `0` and `1`.
  intro hzero
  let n := chosen_subdivision_length O hO γ
  let t := chosen_subdivision_points O hO γ
  have h0 : t 0 = 0 := by
    simpa [n, t] using chosen_subdivision_points_zero O hO γ
  have h1 : t (Fin.last n) = 1 := by
    simpa [n, t] using chosen_subdivision_points_last O hO γ
  have hlast0 : (Fin.last n : Fin (n + 1)) = 0 := by
    simpa [n, hzero] using (show (Fin.last 0 : Fin (0 + 1)) = 0 by rfl)
  have h1' : t 0 = 1 := by
    simpa [hlast0] using h1
  simpa [h1'] using h0

/-- Helper for Theorem 2.7.1: the chosen breakpoint tuple attached to a path is monotone. -/
theorem chosen_subdivision_points_monotone
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y) :
    Monotone (chosen_subdivision_points O hO γ) := by
  -- The monotonicity witness is one of the components stored in the chosen subdivision package.
  exact (Classical.choose_spec (Classical.choose_spec (chosen_subdivision_data O hO γ))).2.2.1

/-- Helper for Theorem 2.7.1: any point lying between the first and last points of a monotone
breakpoint tuple lies in one of its subdivision intervals. -/
theorem exists_subdivision_interval_of_monotone
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (hmono : Monotone t)
    (c : I)
    (hc0 : t 0 ≤ c)
    (hc1 : c ≤ t (Fin.last (n + 1)))
    :
    ∃ j : Fin (n + 1), t j.castSucc ≤ c ∧ c ≤ t j.succ := by
  -- Peel intervals from the right. Either `c` already lies in the unchanged prefix, or it lies in
  -- the last interval.
  induction n with
  | zero =>
      refine ⟨0, ?_, ?_⟩
      · exact hc0
      · exact hc1
  | succ n ih =>
      by_cases hc : c ≤ t (Fin.castSucc (Fin.last (n + 1)))
      · obtain ⟨j, hj_left, hj_right⟩ :=
          ih
            (fun k : Fin (n + 2) ↦ t k.castSucc)
            (fun a b hab ↦ hmono hab)
            (by simpa using hc0)
            (by simpa using hc)
        exact ⟨j.castSucc, hj_left, hj_right⟩
      · refine ⟨Fin.last (n + 1), ?_, ?_⟩
        · exact le_of_not_ge hc
        · exact hc1

/-- Helper for Theorem 2.7.1: repeatedly inserting a finite family of points into an
endpoint-normalized monotone subdivision produces a refinement whose breakpoint tuple contains all
of those points. -/
theorem subdivision_refinement_insert_finite_points
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (htmono : Monotone t)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last (n + 1)) = 1) :
    ∀ {m : ℕ} (s : Fin m → I),
      ∃ N : ℕ,
        ∃ w : Fin (N + 2) → I,
          ∃ v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O,
            ∃ hv :
              ∀ k : Fin (N + 1),
                Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k),
              subdivision_refinement γ t u hu w v hv ∧
                ∀ j : Fin m, ∃ k : Fin (N + 2), w k = s j := by
  intro m
  induction m with
  | zero =>
      intro s
      -- With no extra points to insert, the original subdivision already does the job.
      refine ⟨n, t, u, hu, subdivision_refinement.refl t u hu, ?_⟩
      intro j
      exact Fin.elim0 j
  | succ m ih =>
      intro s
      -- First refine so that all tail points `s 1, ..., s m` already occur in the breakpoint
      -- tuple; the leading point `s 0` will then be inserted into the resulting monotone tuple.
      obtain ⟨N, w, v, hv, href, htail⟩ := ih (fun j : Fin m ↦ s j.succ)
      have hwmono : Monotone w := subdivision_refinement_monotone γ htmono href
      have hwend : w 0 = 0 ∧ w (Fin.last (N + 1)) = 1 :=
        subdivision_refinement_endpoints γ ht0 ht1 href
      rcases hwend with ⟨hw0, hw1⟩
      obtain ⟨j, hj_left, hj_right⟩ :=
        exists_subdivision_interval_of_monotone
          w
          hwmono
          (s 0)
          (by simpa [hw0] using (s 0).2.1)
          (by simpa [hw1] using (s 0).2.2)
      let w' : Fin (N + 3) → I := insert_subdivision_points w j (s 0)
      let v' : Fin (N + 2) → TopologicalSpace.IsOpenCover.Index O := insert_subdivision_labels v j
      let hv' :
          ∀ k : Fin (N + 2),
            Set.range (γ.subpath (w' k.castSucc) (w' k.succ)) ⊆ O (v' k) :=
        insert_subdivision_subordinate γ w v hv j (s 0) hj_left hj_right
      refine ⟨N + 1, w', v', hv', subdivision_refinement.insert href j (s 0) hj_left hj_right, ?_⟩
      intro l
      refine Fin.cases ?_ ?_ l
      · -- The freshly inserted breakpoint occupies the new inserted coordinate.
        refine ⟨j.succ.castSucc, ?_⟩
        simpa [w'] using insert_subdivision_points_inserted w j (s 0)
      · intro l
        -- Every previously recorded tail point survives at the corresponding `succAbove` index.
        obtain ⟨k, hk⟩ := htail l
        refine ⟨j.succ.castSucc.succAbove k, ?_⟩
        calc
          w' (j.succ.castSucc.succAbove k) = w k := by
            simpa [w'] using insert_subdivision_points_succAbove w j (s 0) k
          _ = s l.succ := hk

/-- Helper for Theorem 2.7.1: the representative-level morphism obtained by applying the chosen
subdivision construction to a path. -/
noncomputable abbrev chosen_subdivision_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) :
    chosen_cover_object O hO S x ⟶ chosen_cover_object O hO S y :=
  eqToHom
      (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
        (chosen_subdivision_source_eq O hO γ).symm) ≫
    subdivision_morphism O hO hinter S γ
      (t := chosen_subdivision_points O hO γ)
      (u := chosen_subdivision_labels O hO γ)
      (chosen_subdivision_subordinate O hO γ) ≫
    eqToHom
      (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
        (chosen_subdivision_target_eq O hO γ))

/-- Helper for Theorem 2.7.1: the subdivision composite attached to an explicit subdivision,
viewed after transporting its endpoints to the chosen endpoint objects of the whole path. -/
noncomputable abbrev normalized_subdivision_morphism
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hx : γ (t 0) = x)
    (hy : γ (t (Fin.last n)) = y) :
    chosen_cover_object O hO S x ⟶ chosen_cover_object O hO S y :=
  eqToHom (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hx).symm ≫
    subdivision_morphism O hO hinter S γ
      (t := t)
      (u := u)
      hu ≫
    eqToHom (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hy)

/-- Helper for Theorem 2.7.1: if a whole subdivided ambient subpath already lies in one chosen
cover member, then the recursive subdivision composite collapses to the corresponding single local
segment morphism in that member. -/
theorem subdivision_morphism_eq_local_subpath_morphism_of_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hmono : Monotone t)
    (hn : n ≠ 0)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath (t 0) (t (Fin.last n))) ⊆ O i) :
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu =
      local_subpath_morphism O hO hinter S γ
        (t 0)
        (t (Fin.last n))
        i
        hsub := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  induction m with
  | zero =>
      -- With one subdivision interval, the recursive composite is already the terminal local
      -- segment, so only the cover label has to be changed to the ambient label `i`.
      change
        𝟙 (chosen_cover_object O hO S (γ (t 0))) ≫
            local_subpath_morphism O hO hinter S γ
              (t 0)
              (t (Fin.last 1))
              (u (Fin.last 0))
              (hu (Fin.last 0)) =
          local_subpath_morphism O hO hinter S γ
            (t 0)
            (t (Fin.last 1))
            i
            hsub
      simp
      simpa using
        local_subpath_morphism_eq_of_overlap hO hinter S γ
          (t 0)
          (t (Fin.last 1))
          (u (Fin.last 0))
          i
          (hu (Fin.last 0))
          hsub
  | succ m ih =>
      have hzero_le_prefix :
          t 0 ≤ t (Fin.castSucc (Fin.last (m + 1))) := by
        exact hmono (by simp)
      have hprefix_le_last :
          t (Fin.castSucc (Fin.last (m + 1))) ≤ t (Fin.last (m + 2)) := by
        exact hmono (Fin.le_last _)
      have hprefix_sub :
          Set.range
              (γ.subpath (t 0) (t (Fin.castSucc (Fin.last (m + 1))))) ⊆
            O i := by
        -- The prefix still lies in the ambient open because it is a smaller subpath of the full
        -- ambient segment.
        exact
          subpath_range_subset_of_subpath_range_subset γ
            le_rfl
            hzero_le_prefix
            hprefix_le_last
            hsub
      have hlast_sub :
          Set.range
              (γ.subpath
                (t (Fin.castSucc (Fin.last (m + 1))))
                (t (Fin.last (m + 2)))) ⊆
            O i := by
        -- The terminal interval is another smaller subpath of the same ambient segment.
        exact
          subpath_range_subset_of_subpath_range_subset γ
            hzero_le_prefix
            hprefix_le_last
            le_rfl
            hsub
      have hprefix_eq :
          subdivision_morphism O hO hinter S γ
              (t := fun k : Fin (m + 2) ↦ t k.castSucc)
              (u := fun k : Fin (m + 1) ↦ u k.castSucc)
              (fun k : Fin (m + 1) ↦ hu k.castSucc) =
            local_subpath_morphism O hO hinter S γ
              (t 0)
              (t (Fin.castSucc (Fin.last (m + 1))))
              i
              hprefix_sub := by
        -- Apply the induction hypothesis to the unchanged prefix subdivision.
        simpa using
          (ih
            (t := fun k : Fin (m + 2) ↦ t k.castSucc)
            (u := fun k : Fin (m + 1) ↦ u k.castSucc)
            (hu := fun k : Fin (m + 1) ↦ hu k.castSucc)
            (hmono := fun a b hab ↦ hmono hab)
            (hn := by simp)
            (hsub := hprefix_sub))
      have hlast_eq :
          local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t (Fin.last (m + 2)))
              (u (Fin.last (m + 1)))
              (hu (Fin.last (m + 1))) =
            local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t (Fin.last (m + 2)))
              i
              hlast_sub := by
        -- The final interval also lies in `O i`, so the terminal local morphism is independent
        -- of whether it is labelled by `u (Fin.last _)` or by `i`.
        exact
          local_subpath_morphism_eq_of_overlap hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t (Fin.last (m + 2)))
            (u (Fin.last (m + 1)))
            i
            (hu (Fin.last (m + 1)))
            hlast_sub
      have hcollapse :
          local_subpath_morphism O hO hinter S γ
              (t 0)
              (t (Fin.castSucc (Fin.last (m + 1))))
              i
              hprefix_sub ≫
            local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t (Fin.last (m + 2)))
              i
              hlast_sub =
          local_subpath_morphism O hO hinter S γ
            (t 0)
            (t (Fin.last (m + 2)))
            i
            hsub := by
        -- Once both pieces use the same ambient label `i`, they telescope back to the full
        -- unsplit segment.
        exact
          local_subpath_morphism_trans hO hinter S γ
            (t 0)
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t (Fin.last (m + 2)))
            hzero_le_prefix
            hprefix_le_last
            i
            hsub
      -- The recursive subdivision composite is exactly the prefix composite followed by the final
      -- local segment, so the prefix-collapse and label-independence lemmas reduce it to
      -- `hcollapse`.
      rw [subdivision_morphism]
      rw [hprefix_eq, hlast_eq]
      exact hcollapse

/-- Helper for Theorem 2.7.1: if a path already lies in one chosen cover member, the
chosen-subdivision composite agrees with the cocone leg applied to that local path class. -/
theorem chosen_subdivision_morphism_eq_cover_leg_map
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {i : TopologicalSpace.IsOpenCover.Index O}
    {x y : O i} (γ : Path x y) :
    chosen_subdivision_morphism O hO hinter S
        (γ.map (show Continuous ((↑) : O i → X) by continuity)) =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
        (show (y : X) ∈ O i by exact y.property)).symm := by
  let γX : Path (x : X) y := γ.map (show Continuous ((↑) : O i → X) by continuity)
  let n := chosen_subdivision_length O hO γX
  let t := chosen_subdivision_points O hO γX
  let u := chosen_subdivision_labels O hO γX
  have h0 : t 0 = 0 := by
    -- The chosen subdivision starts at the initial endpoint of the ambient image path.
    simpa [n, t, γX] using chosen_subdivision_points_zero O hO γX
  have h1 : t (Fin.last n) = 1 := by
    -- The chosen subdivision ends at the terminal endpoint of the ambient image path.
    simpa [n, t, γX] using chosen_subdivision_points_last O hO γX
  have hlen : n ≠ 0 := by
    -- A chosen subdivision of a path inside one cover member cannot be trivial, because its first
    -- breakpoint is `0` while its last breakpoint is `1`.
    intro hzero
    have hlast0 : (Fin.last n : Fin (n + 1)) = 0 := by
      simpa [n, hzero] using (show (Fin.last 0 : Fin (0 + 1)) = 0 by rfl)
    have h1' : t 0 = 1 := by
      simpa [hlast0] using h1
    simpa [h1'] using h0
  have hsub :
      Set.range (γX.subpath (t 0) (t (Fin.last n))) ⊆ O i := by
    -- Every point of the chosen ambient subpath still comes from the original subtype-valued path
    -- `γ`, so it stays inside `O i`.
    intro z hz
    rcases hz with ⟨s, rfl⟩
    exact ((γ.subpath (t 0) (t (Fin.last n)) s)).property
  have hcollapse :=
    subdivision_morphism_eq_local_subpath_morphism_of_range_subset hO hinter S
      (γ := γX)
      (t := t)
      (u := u)
      (hu := chosen_subdivision_subordinate O hO γX)
      (hmono := chosen_subdivision_points_monotone O hO γX)
      (hn := hlen)
      (i := i)
      (hsub := hsub)
  have hsub01 : Set.range (γX.subpath 0 1) ⊆ O i := by
    -- The full ambient image path also stays inside `O i`.
    intro z hz
    rcases hz with ⟨s, rfl⟩
    exact ((γ.subpath 0 1 s)).property
  have hchosen_raw :
      chosen_subdivision_morphism O hO hinter S γX ≍
        subdivision_morphism O hO hinter S γX
          (t := t)
          (u := u)
          (chosen_subdivision_subordinate O hO γX) := by
    -- Strip off the endpoint transports in `chosen_subdivision_morphism`.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (chosen_subdivision_morphism O hO hinter S γX)
        (subdivision_morphism O hO hinter S γX
          (t := t)
          (u := u)
          (chosen_subdivision_subordinate O hO γX))
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (chosen_subdivision_source_eq O hO γX).symm)
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (chosen_subdivision_target_eq O hO γX).symm)).1 rfl
  have hlocal01 :
      local_subpath_morphism O hO hinter S γX
          (t 0)
          (t (Fin.last n))
          i
          hsub ≍
        local_subpath_morphism O hO hinter S γX
          0
          1
          i
          hsub01 := by
    -- Rewrite the chosen endpoints to `0` and `1` without changing the local morphism.
    simpa [γX, n, t] using
      (local_subpath_morphism_heq_of_eq hO hinter S γX h0 h1 rfl
        (hsub := hsub)
        (hsub' := hsub01))
  have hlift_eq : lift_subpath_to_open O γX 0 1 i hsub01 = γ.subpath 0 1 := by
    -- Lifting the full ambient image path back into `O i` simply recovers the original subtype
    -- path restricted to the whole interval.
    ext s
    rfl
  have hmap_heq :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γX 0 1 i hsub01⟧) ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) := by
    -- Replace the lifted full subpath by `γ.subpath 0 1`, then normalize that full subpath back
    -- to `γ` inside the local fundamental groupoid of `O i`.
    rw [hlift_eq]
    exact functor_map_fromPath_subpath_zero_one_heq (S.ι.app i) γ
  have hchosen_heq :
      chosen_subdivision_morphism O hO hinter S γX ≍
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) := by
    -- Collapse the chosen subdivision to one local segment, normalize that segment to the full
    -- interval `[0,1]`, and then compare its raw map with the cocone-leg image of `γ`.
    refine hchosen_raw.trans ?_
    refine hcollapse.heq.trans ?_
    refine hlocal01.trans ?_
    simpa [γX, hsub01] using
      (local_subpath_morphism_heq_functor_map hO hinter S γX 0 1 i hsub01).trans hmap_heq
  -- Reinsert the endpoint transports corresponding to the chosen source and target objects.
  exact
    (CategoryTheory.conj_eqToHom_iff_heq
      (chosen_subdivision_morphism O hO hinter S γX)
      ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧))
      (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property))
      (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
        (show (y : X) ∈ O i by exact y.property))).2 hchosen_heq

/-- Helper for Theorem 2.7.1: inside one cover member, endpoint-fixed homotopic paths induce the
same chosen-subdivision composite in the ambient cocone target. -/
theorem chosen_subdivision_morphism_eq_of_homotopic_in_cover
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {i : TopologicalSpace.IsOpenCover.Index O}
    {x y : O i} {γ γ' : Path x y}
    (hγ : Path.Homotopic γ γ') :
    chosen_subdivision_morphism O hO hinter S
        (γ.map (show Continuous ((↑) : O i → X) by continuity)) =
      chosen_subdivision_morphism O hO hinter S
        (γ'.map (show Continuous ((↑) : O i → X) by continuity)) := by
  have hcover :
      chosen_subdivision_morphism O hO hinter S
          (γ.map (show Continuous ((↑) : O i → X) by continuity)) =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
          (show (x : X) ∈ O i by exact x.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)).symm := by
    -- Normalize the chosen subdivision of the ambient image path to the cocone leg on `O i`.
    simpa using
      chosen_subdivision_morphism_eq_cover_leg_map
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (i := i)
        (x := x)
        (y := y)
        (γ := γ)
  have hcover' :
      chosen_subdivision_morphism O hO hinter S
          (γ'.map (show Continuous ((↑) : O i → X) by continuity)) =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
          (show (x : X) ∈ O i by exact x.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ'⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)).symm := by
    -- The same endpoint transports appear for any other path in the same local object pair.
    simpa using
      chosen_subdivision_morphism_eq_cover_leg_map
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (i := i)
        (x := x)
        (y := y)
        (γ := γ')
  have hmap :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) =
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ'⟧) := by
    -- Once both paths live in the same open, homotopy invariance is already available locally.
    exact functor_map_eq_of_homotopic_paths_in_open (U := O i) (F := S.ι.app i) hγ
  calc
    chosen_subdivision_morphism O hO hinter S
        (γ.map (show Continuous ((↑) : O i → X) by continuity)) =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
        (show (y : X) ∈ O i by exact y.property)).symm := hcover
    _ =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ'⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
        (show (y : X) ∈ O i by exact y.property)).symm := by
      simpa [Category.assoc] using
        congrArg
          (fun f ↦
            eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
              (show (x : X) ∈ O i by exact x.property)) ≫
              f ≫
            eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
              (show (y : X) ∈ O i by exact y.property)).symm)
          hmap
    _ =
      chosen_subdivision_morphism O hO hinter S
        (γ'.map (show Continuous ((↑) : O i → X) by continuity)) := hcover'.symm

/-- Helper for Theorem 2.7.1: the finite breakpoint-insertion engine can be packaged together with
the monotonicity, endpoint-normalization, and breakpoint-containment data of the resulting refined
tuple. -/
theorem subdivision_refinement_insert_finite_points_endpoint_data
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 2) → I)
    (u : Fin (n + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (n + 1), Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (htmono : Monotone t)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last (n + 1)) = 1)
    {m : ℕ}
    (s : Fin m → I) :
    ∃ N : ℕ,
      ∃ w : Fin (N + 2) → I,
        ∃ v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O,
          ∃ hv :
            ∀ k : Fin (N + 1),
              Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k),
            subdivision_refinement γ t u hu w v hv ∧
              Monotone w ∧
              w 0 = 0 ∧
              w (Fin.last (N + 1)) = 1 ∧
              ∀ j : Fin m, ∃ k : Fin (N + 2), w k = s j := by
  obtain ⟨N, w, v, hv, href, hcontains⟩ :=
    subdivision_refinement_insert_finite_points γ t u hu htmono ht0 ht1 s
  have hwmono : Monotone w := by
    -- Any tuple built by a finite refinement schedule from a monotone tuple is still monotone.
    exact subdivision_refinement_monotone γ htmono href
  have hwend : w 0 = 0 ∧ w (Fin.last (N + 1)) = 1 := by
    -- The insertion schedule never changes the two endpoints of the tuple.
    exact subdivision_refinement_endpoints γ ht0 ht1 href
  rcases hwend with ⟨hw0, hw1⟩
  refine ⟨N, w, v, hv, href, hwmono, hw0, hw1, hcontains⟩

/-- Helper for Theorem 2.7.1: the finite insertion engine also applies to any endpoint-normalized
nontrivial subdivision indexed by `Fin (n + 1)` by first viewing `n` as a successor. -/
theorem subdivision_refinement_insert_finite_points_of_nontrivial
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (htmono : Monotone t)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    {m : ℕ}
    (s : Fin m → I) :
    ∃ N : ℕ,
      ∃ w : Fin (N + 1) → I,
        ∃ v : Fin N → TopologicalSpace.IsOpenCover.Index O,
          ∃ hv :
            ∀ k : Fin N,
              Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k),
            subdivision_refinement γ t u hu w v hv ∧
              Monotone w ∧
              w 0 = 0 ∧
              w (Fin.last N) = 1 ∧
              ∀ j : Fin m, ∃ k : Fin (N + 1), w k = s j := by
  -- Rewrite the nontrivial subdivision length as a successor, then apply the existing insertion
  -- engine without any further index transport in the main argument.
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨n', rfl⟩
  obtain ⟨N, w, v, hv, href, hwmono, hw0, hw1, hcontains⟩ :=
    subdivision_refinement_insert_finite_points_endpoint_data
      (γ := γ)
      (t := t)
      (u := u)
      (hu := hu)
      (htmono := htmono)
      (ht0 := ht0)
      (ht1 := ht1)
      (s := s)
  exact ⟨N + 1, w, v, hv, href, hwmono, hw0, hw1, hcontains⟩

/-- Helper for Theorem 2.7.1: the chosen subdivision of a path and any explicit endpoint-normalized
nondegenerate subordinate subdivision admit a literal common breakpoint refinement schedule,
possibly with different cover-label choices coming from the two refinement routes. -/
theorem chosen_explicit_subdivision_common_refinement
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (hmono : Monotone t)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    ∃ N : ℕ,
      ∃ w : Fin (N + 1) → I,
        ∃ vChosen : Fin N → TopologicalSpace.IsOpenCover.Index O,
          ∃ hvChosen :
            ∀ k : Fin N,
              Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (vChosen k),
            subdivision_refinement γ
                (chosen_subdivision_points O hO γ)
                (chosen_subdivision_labels O hO γ)
                (chosen_subdivision_subordinate O hO γ)
                w
                vChosen
                hvChosen ∧
              Monotone w ∧
              w 0 = 0 ∧
              w (Fin.last N) = 1 ∧
              ∀ j : Fin (n + 1), ∃ k : Fin (N + 1), w k = t j := by
  -- Route correction: keep the literal shared tuple coming from the chosen-side insertion engine,
  -- and record only the geometric data actually needed later on the explicit side.
  let _ := hn
  let _ := ht0
  let _ := ht1
  let _ := hmono
  let _ := u
  let _ := hu
  obtain ⟨N, w, vChosen, hvChosen, hrefChosen, hwmono, hw0, hw1, hcontains⟩ :=
    subdivision_refinement_insert_finite_points_of_nontrivial
      (γ := γ)
      (t := chosen_subdivision_points O hO γ)
      (hn := chosen_subdivision_length_ne_zero O hO γ)
      (u := chosen_subdivision_labels O hO γ)
      (hu := chosen_subdivision_subordinate O hO γ)
      (htmono := chosen_subdivision_points_monotone O hO γ)
      (ht0 := chosen_subdivision_points_zero O hO γ)
      (ht1 := chosen_subdivision_points_last O hO γ)
      (s := t)
  -- The shared tuple is exactly the chosen-side refinement containing all explicit breakpoints.
  exact ⟨N, w, vChosen, hvChosen, hrefChosen, hwmono, hw0, hw1, hcontains⟩

/-- Helper for Theorem 2.7.1: once the breakpoint tuple and endpoint transports are fixed, the
normalized subdivision composite is independent of which subordinate cover label is chosen on each
segment. -/
theorem normalized_subdivision_morphism_eq_of_same_points
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u v : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hv : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (v k))
    (hx : γ (t 0) = x)
    (hy : γ (t (Fin.last n)) = y) :
    normalized_subdivision_morphism O hO hinter S γ t u hu hx hy =
      normalized_subdivision_morphism O hO hinter S γ t v hv hx hy := by
  -- The endpoint transports are identical on both sides, so only the raw subdivision composite
  -- depends on the cover labels.
  rw [normalized_subdivision_morphism, normalized_subdivision_morphism]
  rw [subdivision_morphism_eq_of_same_points hO hinter S γ t u v hu hv]

/-- Helper for Theorem 2.7.1: once every explicit breakpoint occurs among the shared tuple points,
no explicit breakpoint can lie strictly between two consecutive shared breakpoints. -/
theorem shared_tuple_breakpoint_not_strictly_between_consecutive
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (hcontains : ∀ j : Fin (n + 1), ∃ k : Fin (N + 1), w k = t j) :
    ∀ (k : Fin N) (j : Fin (n + 1)), ¬ (w k.castSucc < t j ∧ t j < w k.succ) := by
  intro k j hbetween
  obtain ⟨l, hl⟩ := hcontains j
  have hkltl : k.castSucc < l := by
    -- A breakpoint strictly above `w k.castSucc` cannot occur at or before `k.castSucc`.
    by_contra hnot
    have hle : l ≤ k.castSucc := le_of_not_gt hnot
    have hwle : w l ≤ w k.castSucc := hwmono hle
    exact not_lt_of_ge (by simpa [hl] using hwle) hbetween.1
  have hltk : l < k.succ := by
    -- The same breakpoint also lies strictly below `w k.succ`, so it cannot occur at or after
    -- `k.succ`.
    by_contra hnot
    have hle : k.succ ≤ l := le_of_not_gt hnot
    have hwle : w k.succ ≤ w l := hwmono hle
    exact not_lt_of_ge (by simpa [hl] using hwle) hbetween.2
  have hkltl' : k.1 < l.1 := hkltl
  have hltk' : l.1 ≤ k.1 := by
    have h' : l.1 < k.succ.1 := hltk
    simpa [Fin.succ] using h'
  omega

/-- Helper for Theorem 2.7.1: if every explicit breakpoint occurs in a shared monotone tuple, then
each consecutive shared interval lies in one explicit interval. -/
theorem shared_tuple_interval_owner_of_breakpoint_containment
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (htmono : Monotone t)
    (hwmono : Monotone w)
    (hcontains : ∀ j : Fin (n + 1), ∃ k : Fin (N + 1), w k = t j) :
    ∃ owner : Fin N → Fin n,
      ∀ k : Fin N, t (owner k).castSucc ≤ w k.castSucc ∧ w k.succ ≤ t (owner k).succ := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  classical
  have howner_exists :
      ∀ k : Fin N, ∃ j : Fin (m + 1), t j.castSucc ≤ w k.castSucc ∧ w k.succ ≤ t j.succ := by
    intro k
    by_cases hdeg : w k.castSucc = w k.succ
    · -- If the shared interval is degenerate, any explicit interval containing that point works.
      obtain ⟨j, hj_left, hj_right⟩ :=
        exists_subdivision_interval_of_monotone t htmono (w k.castSucc)
          (by simpa [ht0] using (w k.castSucc).2.1)
          (by simpa [ht1] using (w k.castSucc).2.2)
      exact ⟨j, hj_left, by simpa [hdeg] using hj_right⟩
    · have hstep : w k.castSucc ≤ w k.succ := by
        exact hwmono (le_of_lt (by simpa using Fin.castSucc_lt_succ k))
      have hab : w k.castSucc < w k.succ := lt_of_le_of_ne hstep hdeg
      let half : I := ⟨(1 : ℝ) / 2, by norm_num⟩
      let c : I := Set.Icc.convexCombo (w k.castSucc) (w k.succ) half
      have hleft_mid : w k.castSucc < c := by
        -- The midpoint of a nondegenerate shared interval is strictly above its left endpoint.
        change ((w k.castSucc : ℝ) < (c : ℝ))
        rw [show (c : ℝ) = (Set.Icc.convexCombo (w k.castSucc) (w k.succ) half : I) by rfl]
        rw [Set.Icc.coe_convexCombo]
        simp [half]
        nlinarith [show ((w k.castSucc : I) : ℝ) < w k.succ by exact hab]
      have hright_mid : c < w k.succ := by
        -- The same midpoint is strictly below the right endpoint.
        change ((c : ℝ) < (w k.succ : ℝ))
        rw [show (c : ℝ) = (Set.Icc.convexCombo (w k.castSucc) (w k.succ) half : I) by rfl]
        rw [Set.Icc.coe_convexCombo]
        simp [half]
        nlinarith [show ((w k.castSucc : I) : ℝ) < w k.succ by exact hab]
      obtain ⟨j, hj_left, hj_right⟩ :=
        exists_subdivision_interval_of_monotone t htmono c
          (by simpa [c, ht0] using c.2.1)
          (by simpa [c, ht1] using c.2.2)
      have hleft : t j.castSucc ≤ w k.castSucc := by
        -- If the left explicit endpoint were still above `w k.castSucc`, it would give a forbidden
        -- explicit breakpoint strictly inside the shared interval.
        by_contra hnot
        have hstrict : w k.castSucc < t j.castSucc := lt_of_not_ge hnot
        exact
          (shared_tuple_breakpoint_not_strictly_between_consecutive t w hwmono hcontains
            k j.castSucc) ⟨hstrict, lt_of_le_of_lt hj_left hright_mid⟩
      have hright : w k.succ ≤ t j.succ := by
        -- The same argument rules out the right explicit endpoint lying strictly before
        -- `w k.succ`.
        by_contra hnot
        have hstrict : t j.succ < w k.succ := lt_of_not_ge hnot
        exact
          (shared_tuple_breakpoint_not_strictly_between_consecutive t w hwmono hcontains
            k j.succ) ⟨lt_of_lt_of_le hleft_mid hj_right, hstrict⟩
      exact ⟨j, hleft, hright⟩
  refine ⟨fun k ↦ Classical.choose (howner_exists k), ?_⟩
  intro k
  -- Unpack the explicit interval chosen for this shared segment.
  exact Classical.choose_spec (howner_exists k)

/-- Helper for Theorem 2.7.1: if every explicit breakpoint occurs in a shared endpoint-normalized
monotone tuple, then the shared tuple admits a coherent monotone list of breakpoint cutpoints. -/
theorem shared_tuple_breakpoint_cutpoints
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (hw0 : w 0 = 0)
    (hw1 : w (Fin.last N) = 1)
    (htmono : Monotone t)
    (hwmono : Monotone w)
    (hcontains : ∀ j : Fin (n + 1), ∃ k : Fin (N + 1), w k = t j) :
    ∃ sigma : Fin (n + 1) → Fin (N + 1),
      sigma 0 = 0 ∧
      sigma (Fin.last n) = Fin.last N ∧
      Monotone sigma ∧
      ∀ j : Fin (n + 1), w (sigma j) = t j := by
  classical
  have hcontains_nat :
      ∀ j : Fin (n + 1), ∃ m : ℕ, ∃ k : Fin (N + 1), k.1 = m ∧ w k = t j := by
    intro j
    obtain ⟨k, hk⟩ := hcontains j
    exact ⟨k.1, k, rfl, hk⟩
  let leastOccurrence : Fin (n + 1) → Fin (N + 1) := fun j ↦
    Classical.choose (Nat.find_spec (hcontains_nat j))
  have hleast_eq : ∀ j : Fin (n + 1), w (leastOccurrence j) = t j := by
    intro j
    exact (Classical.choose_spec (Nat.find_spec (hcontains_nat j))).2
  have hleast_min :
      ∀ (j : Fin (n + 1)) (k : Fin (N + 1)),
        w k = t j → leastOccurrence j ≤ k := by
    intro j k hk
    have hfind_val : (leastOccurrence j).1 = Nat.find (hcontains_nat j) := by
      exact (Classical.choose_spec (Nat.find_spec (hcontains_nat j))).1
    by_contra hnot
    have hklt : k.1 < Nat.find (hcontains_nat j) := by
      have hklt' : k.1 < (leastOccurrence j).1 := lt_of_not_ge hnot
      simpa [hfind_val] using hklt'
    exact (Nat.find_min (hcontains_nat j) hklt) ⟨k, rfl, hk⟩
  let sigma : Fin (n + 1) → Fin (N + 1) := fun j ↦
    if hj : j = Fin.last n then Fin.last N else leastOccurrence j
  have hsigma_zero : sigma 0 = 0 := by
    have hzero_ne_last : (0 : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have hval : 0 = n := by
        simpa using congrArg Fin.val h
      exact hn hval.symm
    have hleast_zero :
        leastOccurrence 0 = 0 := by
      apply le_antisymm
      · exact hleast_min 0 0 (by simpa [ht0] using hw0)
      · exact Fin.zero_le _
    simp [sigma, hzero_ne_last, hleast_zero]
  have hsigma_last : sigma (Fin.last n) = Fin.last N := by
    simp [sigma]
  have hsigma_mono : Monotone sigma := by
    refine Fin.monotone_iff_le_succ.2 ?_
    intro k
    have hleft :
        sigma k.castSucc = leastOccurrence k.castSucc := by
      simp [sigma, Fin.castSucc_ne_last]
    by_cases hk : k.succ = Fin.last n
    · -- The terminal breakpoint is sent to the terminal point of the shared tuple.
      simpa [sigma, hk, hleft] using (Fin.le_last (leastOccurrence k.castSucc))
    · have hstep :
          leastOccurrence k.castSucc ≤ leastOccurrence k.succ := by
        by_contra hnot
        have hlt : leastOccurrence k.succ < leastOccurrence k.castSucc := lt_of_not_ge hnot
        have hback : t k.succ ≤ t k.castSucc := by
          -- A smaller occurrence of the later breakpoint would force the later value to be no
          -- larger than the earlier one.
          simpa [hleast_eq] using hwmono (le_of_lt hlt)
        have hforward : t k.castSucc ≤ t k.succ := htmono (Fin.castSucc_le_succ k)
        have hvalue_eq : t k.succ = t k.castSucc := le_antisymm hback hforward
        have hsame_value :
            w (leastOccurrence k.succ) = t k.castSucc := by
          simpa [hvalue_eq] using hleast_eq k.succ
        exact hnot (hleast_min k.castSucc (leastOccurrence k.succ) hsame_value)
      have hright :
          sigma k.succ = leastOccurrence k.succ := by
        simp [sigma, hk]
      simpa [hleft, hright] using hstep
  have hsigma_eq : ∀ j : Fin (n + 1), w (sigma j) = t j := by
    intro j
    by_cases hj : j = Fin.last n
    · subst hj
      simpa [hsigma_last, ht1] using hw1
    · simp [sigma, hj, hleast_eq]
  refine ⟨sigma, hsigma_zero, hsigma_last, hsigma_mono, hsigma_eq⟩

/-- Helper for Theorem 2.7.1: a monotone sequence of cutpoints from `0` to the final shared
breakpoint partitions the shared intervals into unique consecutive blocks. -/
theorem shared_tuple_cutpoint_block_existsUnique
    {n N : ℕ}
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma) :
    ∀ k : Fin N, ∃! j : Fin n, sigma j.castSucc ≤ k.castSucc ∧ k.succ ≤ sigma j.succ := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  intro k
  classical
  let admissible : ℕ → Prop := fun j =>
    ∃ hj : j < m + 1, k.castSucc < sigma ((⟨j, hj⟩ : Fin (m + 1)).succ)
  have hadmissible : ∃ j, admissible j := by
    refine ⟨m, ?_⟩
    refine ⟨Nat.lt_succ_self m, ?_⟩
    have hlast :
        ((⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)).succ : Fin (m + 2)) = Fin.last (m + 1) := by
      ext
      simp
    rw [hlast]
    rw [hsigma1]
    exact Fin.castSucc_lt_last k
  let jNat := Nat.find hadmissible
  have hjNat_spec : admissible jNat := Nat.find_spec hadmissible
  obtain ⟨hjNat_lt, hjNat_right⟩ := hjNat_spec
  let j : Fin (m + 1) := ⟨jNat, hjNat_lt⟩
  have hj_right : k.succ ≤ sigma j.succ := by
    change k.1 + 1 ≤ (sigma j.succ).1
    exact Nat.succ_le_of_lt (by simpa [j] using hjNat_right)
  have hj_left : sigma j.castSucc ≤ k.castSucc := by
    by_contra hleft
    have hklt_left : k.castSucc < sigma j.castSucc := lt_of_not_ge hleft
    by_cases hjzero : jNat = 0
    · have hzero_left : sigma j.castSucc ≤ k.castSucc := by
        simpa [j, hjzero, hsigma0] using (Fin.zero_le k.castSucc)
      exact hleft hzero_left
    · have hjpos : 0 < jNat := Nat.pos_of_ne_zero hjzero
      have hjPred_lt : jNat - 1 < m + 1 := by
        omega
      have hpred_admissible : admissible (jNat - 1) := by
        refine ⟨hjPred_lt, ?_⟩
        have hpred_index :
            ((⟨jNat - 1, hjPred_lt⟩ : Fin (m + 1)).succ : Fin (m + 2)) = j.castSucc := by
          ext
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)
        rw [hpred_index]
        exact hklt_left
      have hmin := Nat.find_min' hadmissible hpred_admissible
      omega
  refine ⟨j, ⟨hj_left, hj_right⟩, ?_⟩
  intro j' hj'
  have hj'_right : k.castSucc < sigma j'.succ := by
    change k.1 < (sigma j'.succ).1
    exact lt_of_lt_of_le (Nat.lt_succ_self k.1) (by simpa using hj'.2)
  have hj'_admissible : admissible j'.1 := by
    refine ⟨j'.is_lt, ?_⟩
    simpa using hj'_right
  have hj_le : jNat ≤ j'.1 := Nat.find_min' hadmissible hj'_admissible
  have hj_fin_le : j ≤ j' := hj_le
  by_contra hne
  have hj_lt : j < j' := lt_of_le_of_ne hj_fin_le (by
    intro h
    exact hne h.symm)
  have hj_right' : k.castSucc < sigma j.succ := by
    change k.1 < (sigma j.succ).1
    exact lt_of_lt_of_le (Nat.lt_succ_self k.1) (by simpa using hj_right)
  have hsucc_le : j.succ ≤ j'.castSucc := by
    change j.1 + 1 ≤ j'.1
    exact Nat.succ_le_of_lt hj_lt
  have hsigma_le : sigma j.succ ≤ sigma j'.castSucc := hsigmamono hsucc_le
  exact not_lt_of_ge (le_trans hsigma_le hj'.1) hj_right'

/-- Helper for Theorem 2.7.1: the canonical explicit interval associated to a shared interval is the
unique cutpoint block determined by the monotone cutpoint sequence `sigma`. -/
noncomputable def shared_tuple_cutpoint_block
    {n N : ℕ}
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma) :
    Fin N → Fin n :=
  fun k ↦
    Classical.choose <|
      ExistsUnique.exists <|
        shared_tuple_cutpoint_block_existsUnique hn sigma hsigma0 hsigma1 hsigmamono k

/-- Helper for Theorem 2.7.1: the canonical cutpoint block of a shared interval is bounded by the
two consecutive cutpoints that define that block. -/
theorem shared_tuple_cutpoint_block_spec
    {n N : ℕ}
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (k : Fin N) :
    sigma (shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k).castSucc ≤
        k.castSucc ∧
      k.succ ≤ sigma (shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k).succ := by
  exact
    Classical.choose_spec <|
      ExistsUnique.exists <|
        shared_tuple_cutpoint_block_existsUnique hn sigma hsigma0 hsigma1 hsigmamono k

/-- Helper for Theorem 2.7.1: if the endpoints of a shared interval lie between two consecutive
cutpoints of `sigma`, then the canonical cutpoint block attached to that shared interval is exactly
that explicit block. -/
theorem shared_tuple_cutpoint_block_eq_of_between
    {n N : ℕ}
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (j : Fin n)
    (k : Fin N)
    (hj_left : sigma j.castSucc ≤ k.castSucc)
    (hj_right : k.succ ≤ sigma j.succ) :
    shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k = j := by
  obtain ⟨j₀, hj₀, hjunique⟩ :=
    shared_tuple_cutpoint_block_existsUnique hn sigma hsigma0 hsigma1 hsigmamono k
  -- Compare the canonical chosen block and the proposed block `j` against the same uniqueness
  -- witness for the cutpoint partition.
  have hchosen :
      shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k = j₀ :=
    hjunique _ (shared_tuple_cutpoint_block_spec hn sigma hsigma0 hsigma1 hsigmamono k)
  have hj :
      j = j₀ :=
    hjunique _ ⟨hj_left, hj_right⟩
  exact hchosen.trans hj.symm

/-- Helper for Theorem 2.7.1: relabelling each shared interval by its canonical cutpoint block
produces the explicit-side labels on the shared tuple. -/
noncomputable abbrev shared_tuple_cutpoint_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {n N : ℕ}
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma) :
    Fin N → TopologicalSpace.IsOpenCover.Index O :=
  fun k ↦ u (shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k)

/-- Helper for Theorem 2.7.1: on a fixed sigma-block, the canonical shared-tuple label is the
explicit label of that block. -/
theorem shared_tuple_cutpoint_labels_eq_of_between
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {n N : ℕ}
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (j : Fin n)
    (k : Fin N)
    (hj_left : sigma j.castSucc ≤ k.castSucc)
    (hj_right : k.succ ≤ sigma j.succ) :
    shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono k = u j := by
  -- The canonical shared label is defined by applying `u` to the canonical cutpoint block.
  simp [shared_tuple_cutpoint_labels,
    shared_tuple_cutpoint_block_eq_of_between hn sigma hsigma0 hsigma1 hsigmamono j k hj_left
      hj_right]

/-- Helper for Theorem 2.7.1: each shared interval stays inside the explicit cover member indexed
by its canonical cutpoint block. -/
theorem shared_tuple_cutpoint_block_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : n ≠ 0)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin (n + 1), w (sigma j) = t j)
    (hwmono : Monotone w)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    ∀ k : Fin N,
      Set.range
          (γ.subpath (w k.castSucc) (w k.succ)) ⊆
        O (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono k) := by
  intro k
  let j := shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k
  have hj :=
    shared_tuple_cutpoint_block_spec hn sigma hsigma0 hsigma1 hsigmamono k
  have hj_left :
      t j.castSucc ≤ w k.castSucc := by
    calc
      t j.castSucc = w (sigma j.castSucc) := by
        symm
        exact hsigmaeq j.castSucc
      _ ≤ w k.castSucc := hwmono hj.1
  have hj_right :
      w k.succ ≤ t j.succ := by
    calc
      w k.succ ≤ w (sigma j.succ) := hwmono hj.2
      _ = t j.succ := hsigmaeq j.succ
  -- The shared interval is a smaller subpath of the explicit interval indexed by its cutpoint
  -- block, so it inherits that explicit interval's cover label.
  exact
    subpath_range_subset_of_subpath_range_subset γ
      hj_left
      (hwmono (le_of_lt (by simpa using Fin.castSucc_lt_succ k)))
      hj_right
      (hu j)

/-- Helper for Theorem 2.7.1: truncating a shared tuple at a chosen shared breakpoint produces the
literal prefix tuple seen by the recursive definition of `subdivision_morphism`. -/
noncomputable abbrev shared_tuple_prefix_points
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (k : Fin (N + 1)) :
    Fin (k.1 + 1) → I :=
  fun q ↦ w ⟨q.1, Nat.lt_of_lt_of_le q.is_lt (Nat.succ_le_of_lt k.is_lt)⟩

/-- Helper for Theorem 2.7.1: truncating the shared-tuple label family at the same breakpoint
keeps exactly the labels on the earlier shared intervals. -/
noncomputable abbrev shared_tuple_prefix_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (k : Fin (N + 1)) :
    Fin k.1 → TopologicalSpace.IsOpenCover.Index O :=
  fun q ↦ v ⟨q.1, Nat.lt_of_lt_of_le q.is_lt (Nat.lt_succ_iff.mp k.is_lt)⟩

/-- Helper for Theorem 2.7.1: retaining only the suffix of a shared tuple starting at `a`
produces the literal terminal tuple from `a` to the global endpoint. -/
noncomputable abbrev shared_tuple_suffix_points
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (a : Fin (N + 1)) :
    Fin (N - a.1 + 1) → I :=
  fun q ↦
    w ⟨a.1 + q.1, by
      have hq : q.1 < N - a.1 + 1 := q.is_lt
      omega⟩

/-- Helper for Theorem 2.7.1: the label family on a shared tuple restricts to the literal suffix
starting at `a`. -/
noncomputable abbrev shared_tuple_suffix_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (a : Fin (N + 1)) :
    Fin (N - a.1) → TopologicalSpace.IsOpenCover.Index O :=
  fun q ↦
    v ⟨a.1 + q.1, by
      have hq : q.1 < N - a.1 := q.is_lt
      omega⟩

/-- Helper for Theorem 2.7.1: the subordinacy witness on a shared tuple restricts to every
literal shared prefix. -/
theorem shared_tuple_prefix_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (k : Fin (N + 1)) :
    ∀ q : Fin k.1,
      Set.range
          (γ.subpath
            (shared_tuple_prefix_points w k q.castSucc)
            (shared_tuple_prefix_points w k q.succ)) ⊆
        O (shared_tuple_prefix_labels v k q) := by
  intro q
  -- Restricting to the literal prefix changes neither the `q`-th shared interval nor its label.
  simpa [shared_tuple_prefix_points, shared_tuple_prefix_labels] using
    hv ⟨q.1, Nat.lt_of_lt_of_le q.is_lt (Nat.lt_succ_iff.mp k.is_lt)⟩

/-- Helper for Theorem 2.7.1: the subordinacy witness on a shared tuple also restricts to every
literal suffix. -/
theorem shared_tuple_suffix_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    ∀ q : Fin (N - a.1),
      Set.range
          (γ.subpath
            (shared_tuple_suffix_points w a q.castSucc)
            (shared_tuple_suffix_points w a q.succ)) ⊆
        O (shared_tuple_suffix_labels v a q) := by
  intro q
  -- Restricting to the literal suffix again keeps the original shared interval and its label.
  intro z hz
  rcases hz with ⟨s, rfl⟩
  exact
    (hv ⟨a.1 + q.1, by
      have hq : q.1 < N - a.1 := q.is_lt
      omega⟩) ⟨s, by
        have hsucc :
            (⟨a.1 + q.1 + 1, by
              have hq : q.1 < N - a.1 := q.is_lt
              omega⟩ : Fin (N + 1)) =
              ⟨a.1 + q.succ.1, by
                have hq : q.succ.1 < N - a.1 + 1 := q.succ.is_lt
                omega⟩ := by
          ext
          simp [Fin.succ, Nat.add_assoc]
        change
          (γ.subpath
            (w ⟨a.1 + q.1, by
              have hq : q.1 < N - a.1 := q.is_lt
              omega⟩)
            (w ⟨a.1 + q.1 + 1, by
              have hq : q.1 < N - a.1 := q.is_lt
              omega⟩)) s =
            (γ.subpath
              (shared_tuple_suffix_points w a q.castSucc)
              (shared_tuple_suffix_points w a q.succ)) s
        rw [hsucc]
        rfl⟩

/-- Helper for Theorem 2.7.1: taking the recursive prefix of the literal shared suffix starting at
`a.castSucc` gives exactly the suffix of the recursive ambient tuple starting at `a`. -/
theorem shared_tuple_suffix_points_recursive_castSucc
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (a : Fin (N + 1)) :
    (fun q : Fin (N - a.1 + 1) ↦
      shared_tuple_suffix_points w a.castSucc ⟨q.1, by
        have ha' : a.castSucc.1 = a.1 := rfl
        omega⟩) =
      shared_tuple_suffix_points (fun r : Fin (N + 1) ↦ w r.castSucc) a := by
  -- Both tuples list the same ambient shared breakpoints from `a` up to the predecessor of the
  -- global terminal point.
  funext q
  simp [shared_tuple_suffix_points]

/-- Helper for Theorem 2.7.1: the same cast-successor normalization holds for the label family on
literal shared suffixes. -/
theorem shared_tuple_suffix_labels_recursive_castSucc
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (a : Fin (N + 1)) :
    (fun q : Fin (N - a.1) ↦
      shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
        have ha' : a.castSucc.1 = a.1 := rfl
        omega⟩) =
      shared_tuple_suffix_labels (fun r : Fin N ↦ v r.castSucc) a := by
  -- Restricting the suffix after deleting the global terminal interval keeps exactly the same
  -- labels on the remaining shared intervals.
  funext q
  simp [shared_tuple_suffix_labels]

/-- Helper for Theorem 2.7.1: the recursive call obtained by unfolding the literal shared suffix
starting at `a.castSucc` is exactly the literal shared suffix of the recursively truncated ambient
tuple starting at `a`. -/
theorem subdivision_morphism_literal_suffix_step
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv :
      ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    subdivision_morphism O hO hinter S γ
        (t := fun q : Fin (N - a.1 + 1) ↦
          shared_tuple_suffix_points w a.castSucc ⟨q.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩)
        (u := fun q : Fin (N - a.1) ↦
          shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩)
        (fun q : Fin (N - a.1) ↦
          shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨q.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩) ≍
      subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points (fun r : Fin (N + 1) ↦ w r.castSucc) a)
        (u := shared_tuple_suffix_labels
          (fun r : Fin N ↦ v r.castSucc)
          a)
        (shared_tuple_suffix_subordinate
          γ
          (fun r : Fin (N + 1) ↦ w r.castSucc)
          (fun r : Fin N ↦ v r.castSucc)
          (fun r : Fin N ↦ hv r.castSucc)
          a) := by
  -- Normalize the recursive point and label tuples on the literal suffix by commuting the ambient
  -- `castSucc` through the suffix construction before comparing subdivision composites.
  exact
    subdivision_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (t := fun q : Fin (N - a.1 + 1) ↦
        shared_tuple_suffix_points w a.castSucc ⟨q.1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩)
      (u := fun q : Fin (N - a.1) ↦
        shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩)
      (t' := shared_tuple_suffix_points (fun r : Fin (N + 1) ↦ w r.castSucc) a)
      (u' := shared_tuple_suffix_labels
        (fun r : Fin N ↦ v r.castSucc)
        a)
      (ht := shared_tuple_suffix_points_recursive_castSucc w a)
      (hu := shared_tuple_suffix_labels_recursive_castSucc v a)

/-- Helper for Theorem 2.7.1: taking the literal shared suffix from the initial breakpoint leaves
the point tuple unchanged. -/
theorem shared_tuple_suffix_points_zero_eq_self
    {N : ℕ}
    (w : Fin (N + 1) → I) :
    shared_tuple_suffix_points w 0 = w := by
  funext q
  simp [shared_tuple_suffix_points]

/-- Helper for Theorem 2.7.1: taking the literal shared suffix from the initial breakpoint leaves
the label family unchanged. -/
theorem shared_tuple_suffix_labels_zero_eq_self
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O) :
    shared_tuple_suffix_labels v 0 = v := by
  funext q
  simp [shared_tuple_suffix_labels]

/-- Helper for Theorem 2.7.1: replacing a shared tuple by its literal suffix starting at the
initial breakpoint does not change the subdivision composite. -/
theorem subdivision_morphism_suffix_zero_heq_self
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w 0)
        (u := shared_tuple_suffix_labels v 0)
        (shared_tuple_suffix_subordinate γ w v hv 0) ≍
      subdivision_morphism O hO hinter S γ
        (t := w)
        (u := v)
        hv := by
  -- Normalizing the zero suffix removes no breakpoints and no labels.
  exact
    subdivision_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (t := shared_tuple_suffix_points w 0)
      (u := shared_tuple_suffix_labels v 0)
      (t' := w)
      (u' := v)
      (ht := shared_tuple_suffix_points_zero_eq_self w)
      (hu := shared_tuple_suffix_labels_zero_eq_self v)

/-- Helper for Theorem 2.7.1: the initial point of the terminal literal suffix is the predecessor
of the global endpoint. -/
theorem shared_tuple_terminal_suffix_zero_eq_prevlast
    {N : ℕ}
    (w : Fin (N + 2) → I) :
    shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)) 0 =
      w (Fin.castSucc (Fin.last N)) := by
  -- Evaluating the terminal suffix at its initial point keeps the predecessor of the global
  -- endpoint.
  change w ⟨N, by omega⟩ = w (Fin.castSucc (Fin.last N))
  congr 1

/-- Helper for Theorem 2.7.1: the final point of the terminal literal suffix is the global
endpoint. -/
theorem shared_tuple_terminal_suffix_last_eq_last
    {N : ℕ}
    (w : Fin (N + 2) → I) :
    shared_tuple_suffix_points
        w
        (Fin.castSucc (Fin.last N))
        ⟨1, by simp⟩ =
      w (Fin.last (N + 1)) := by
  -- The terminal suffix has exactly one interval, so its final point is the ambient final point.
  change w ⟨N + 1, by omega⟩ = w (Fin.last (N + 1))
  congr 1

/-- Helper for Theorem 2.7.1: the unique label on the terminal literal suffix is the ambient final
interval label. -/
theorem shared_tuple_terminal_suffix_label_eq_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O) :
    shared_tuple_suffix_labels
        v
        (Fin.castSucc (Fin.last N))
        ⟨0, by simp⟩ =
      v (Fin.last N) := by
  -- Restricting the label family to the terminal one-interval suffix keeps the last ambient
  -- interval label.
  change v ⟨N, by omega⟩ = v (Fin.last N)
  congr 1

/-- Helper for Theorem 2.7.1: the terminal literal suffix contains exactly one interval. -/
theorem shared_tuple_terminal_suffix_length_eq_one
    {N : ℕ} :
    N + 1 - (Fin.castSucc (Fin.last N)).1 = 1 := by
  -- The terminal suffix starts at the predecessor of the ambient endpoint, so only the last
  -- interval remains.
  simp

/-- Helper for Theorem 2.7.1: after transporting the terminal literal suffix to the explicit
two-point index type `Fin 2`, its point tuple is exactly the ambient predecessor breakpoint
followed by the ambient endpoint. -/
theorem shared_tuple_terminal_suffix_points_cast_eq
    {N : ℕ}
    (w : Fin (N + 2) → I) :
    (fun q : Fin 2 ↦
      shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
        (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q)) =
      fun q : Fin 2 ↦
        if q = 0 then w (Fin.castSucc (Fin.last N)) else w (Fin.last (N + 1)) := by
  -- The transported terminal suffix has only its initial and terminal points.
  funext q
  fin_cases q
  · change
      shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)) 0 =
        w (Fin.castSucc (Fin.last N))
    exact shared_tuple_terminal_suffix_zero_eq_prevlast w
  · change
      shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)) ⟨1, by simp⟩ =
        w (Fin.last (N + 1))
    exact shared_tuple_terminal_suffix_last_eq_last w

/-- Helper for Theorem 2.7.1: after transporting the terminal literal suffix label family to the
explicit one-interval index type `Fin 1`, it is the constant family with value the ambient final
label. -/
theorem shared_tuple_terminal_suffix_labels_cast_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O) :
    (fun q : Fin 1 ↦
      shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
        (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q)) =
      fun _ : Fin 1 ↦ v (Fin.last N) := by
  -- The transported terminal suffix has a single interval label, namely the ambient final one.
  funext q
  fin_cases q
  change
    shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)) ⟨0, by simp⟩ =
      v (Fin.last N)
  exact shared_tuple_terminal_suffix_label_eq_last v

/-- Helper for Theorem 2.7.1: the ambient final subdivision interval is itself subordinate to the
cover label carried by the terminal literal suffix. -/
theorem shared_tuple_terminal_suffix_subordinate_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    Set.range
        (γ.subpath
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))) ⊆
      O (v (Fin.last N)) := by
  -- This is exactly the final ambient subordinacy datum already stored in `hv`.
  exact hv (Fin.last N)

/-- Helper for Theorem 2.7.1: taking the recursive prefix of the literal shared prefix ending at
`k.succ` recovers the shorter literal shared prefix ending at `k`. -/
theorem shared_tuple_prefix_points_castSucc
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (k : Fin N) :
    (fun q ↦ shared_tuple_prefix_points w k.succ q.castSucc) =
      shared_tuple_prefix_points w k.castSucc := by
  -- Both prefix tuples evaluate to the same ambient breakpoint on every index.
  funext q
  simp [shared_tuple_prefix_points]

/-- Helper for Theorem 2.7.1: truncating the recursive ambient prefix tuple at `a` gives exactly
the same literal shared prefix as truncating the original tuple at `a.castSucc`. -/
theorem shared_tuple_prefix_points_recursive_castSucc
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (a : Fin (N + 1)) :
    shared_tuple_prefix_points (fun q ↦ w q.castSucc) a =
      shared_tuple_prefix_points w a.castSucc := by
  -- Both prefix tuples read off the same initial ambient breakpoints of `w`.
  funext q
  simp [shared_tuple_prefix_points]

/-- Helper for Theorem 2.7.1: the recursive prefix of the label family on the literal shared
prefix ending at `k.succ` is exactly the shorter literal shared prefix label family ending at
`k`. -/
theorem shared_tuple_prefix_labels_castSucc
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (k : Fin N) :
    (fun q ↦ shared_tuple_prefix_labels v k.succ q.castSucc) =
      shared_tuple_prefix_labels v k.castSucc := by
  -- The recursive prefix keeps precisely the labels on the earlier shared intervals.
  funext q
  simp [shared_tuple_prefix_labels]

/-- Helper for Theorem 2.7.1: truncating the recursive ambient label family at `a` gives exactly
the same literal shared-prefix labels as truncating the original family at `a.castSucc`. -/
theorem shared_tuple_prefix_labels_recursive_castSucc
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (a : Fin (N + 1)) :
    shared_tuple_prefix_labels (fun q ↦ v q.castSucc) a =
      shared_tuple_prefix_labels v a.castSucc := by
  -- The recursive prefix keeps exactly the labels on the same initial shared intervals.
  funext q
  simp [shared_tuple_prefix_labels]

/-- Helper for Theorem 2.7.1: every literal shared suffix of a monotone shared tuple is still
monotone. -/
theorem shared_tuple_suffix_points_monotone
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (a : Fin (N + 1)) :
    Monotone (shared_tuple_suffix_points w a) := by
  -- Restricting a monotone breakpoint tuple to a terminal block preserves monotonicity.
  intro p q hpq
  simpa [shared_tuple_suffix_points] using hwmono (by
    change a.1 + p.1 ≤ a.1 + q.1
    omega)


/-- Helper for Theorem 2.7.1: after unfolding the literal shared prefix ending at `k.succ`, the
recursive prefix term is heterogeneously equal to the subdivision composite of the shorter literal
shared prefix ending at `k`. -/
theorem subdivision_morphism_shared_prefix_recursive_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (k : Fin N) :
    subdivision_morphism O hO hinter S γ
        (t := fun q ↦ shared_tuple_prefix_points w k.succ q.castSucc)
        (u := fun q ↦ shared_tuple_prefix_labels v k.succ q.castSucc)
        (fun q : Fin k.1 ↦ shared_tuple_prefix_subordinate γ w v hv k.succ q.castSucc) ≍
      subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w k.castSucc)
        (u := shared_tuple_prefix_labels v k.castSucc)
        (shared_tuple_prefix_subordinate γ w v hv k.castSucc) := by
  -- Normalize the recursively truncated point and label tuples back to the shorter literal shared
  -- prefix before comparing the two subdivision composites.
  exact
    subdivision_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (t := fun q ↦ shared_tuple_prefix_points w k.succ q.castSucc)
      (u := fun q ↦ shared_tuple_prefix_labels v k.succ q.castSucc)
      (t' := shared_tuple_prefix_points w k.castSucc)
      (u' := shared_tuple_prefix_labels v k.castSucc)
      (ht := shared_tuple_prefix_points_castSucc w k)
      (hu := shared_tuple_prefix_labels_castSucc v k)

/-- Helper for Theorem 2.7.1: the recursive prefix term obtained by unfolding the literal shared
prefix ending at `k.succ` is definitionally the same subdivision composite as the shorter literal
shared prefix ending at `k`. -/
theorem subdivision_morphism_shared_prefix_recursive_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (k : Fin N) :
    subdivision_morphism O hO hinter S γ
        (t := fun q ↦ shared_tuple_prefix_points w k.succ q.castSucc)
        (u := fun q ↦ shared_tuple_prefix_labels v k.succ q.castSucc)
        (fun q : Fin k.1 ↦ shared_tuple_prefix_subordinate γ w v hv k.succ q.castSucc) =
      subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w k.castSucc)
        (u := shared_tuple_prefix_labels v k.castSucc)
        (shared_tuple_prefix_subordinate γ w v hv k.castSucc) := by
  -- The earlier heterogeneous comparison already identifies the two recursive prefix composites, so
  -- after normalizing their source and target objects they are equal.
  exact
    eq_of_heq <|
      subdivision_morphism_shared_prefix_recursive_heq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (hv := hv)
        (k := k)

/-- Helper for Theorem 2.7.1: unfolding `subdivision_morphism` on the literal shared prefix ending
at `k.succ` yields the earlier literal prefix followed by the terminal shared interval `k`. -/
theorem subdivision_morphism_prefix_decomposition_at_cutpoint
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (k : Fin N) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w k.succ)
        (u := shared_tuple_prefix_labels v k.succ)
        (shared_tuple_prefix_subordinate γ w v hv k.succ) =
      subdivision_morphism O hO hinter S γ
          (t := fun q ↦ shared_tuple_prefix_points w k.succ q.castSucc)
          (u := fun q ↦ shared_tuple_prefix_labels v k.succ q.castSucc)
          (fun q : Fin k.1 ↦ shared_tuple_prefix_subordinate γ w v hv k.succ q.castSucc) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_prefix_points w k.succ (Fin.castSucc (Fin.last k.1)))
          (shared_tuple_prefix_points w k.succ (Fin.last (k.1 + 1)))
          (shared_tuple_prefix_labels v k.succ (Fin.last k.1))
          (shared_tuple_prefix_subordinate γ w v hv k.succ (Fin.last k.1)) := by
  -- The longer literal prefix is definitionally the shorter prefix with the terminal shared
  -- interval `k` appended, so one recursive unfold gives the desired decomposition.
  rfl

/-- Helper for Theorem 2.7.1: the recursively truncated literal shared suffix still ends at the
ambient predecessor of the global terminal breakpoint. -/
theorem shared_tuple_recursive_tail_suffix_last_eq_prevlast
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (a : Fin (N + 1)) :
    shared_tuple_suffix_points
        (fun q : Fin (N + 1) ↦ w q.castSucc)
        a
        (Fin.last (N - a.1)) =
      w (Fin.castSucc (Fin.last N)) := by
  -- Evaluating the recursive tail suffix at its terminal point lands at the ambient predecessor
  -- of the global endpoint.
  change w ⟨a.1 + (Fin.last (N - a.1)).1, by omega⟩ = w (Fin.castSucc (Fin.last N))
  congr 1
  ext
  simp
  omega

/-- Helper for Theorem 2.7.1: the target object of the recursively truncated literal shared suffix
is the chosen object at the ambient predecessor breakpoint. -/
theorem shared_tuple_recursive_tail_suffix_endpoint_obj_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (a : Fin (N + 1)) :
    chosen_cover_object O hO S
        (γ
          (shared_tuple_suffix_points
            (fun q : Fin (N + 1) ↦ w q.castSucc)
            a
            (Fin.last (N - a.1)))) =
      chosen_cover_object O hO S
        (γ (w (Fin.castSucc (Fin.last N)))) := by
  -- Transport the terminal-point normalization through the chosen-object construction.
  simpa using
    congrArg
      (fun z : I ↦ chosen_cover_object O hO S (γ z))
      (shared_tuple_recursive_tail_suffix_last_eq_prevlast (w := w) (a := a))

/-- Helper for Theorem 2.7.1: the interval-count of the ambient suffix starting at `a.castSucc`
agrees with the interval-count of the recursively truncated suffix starting at `a`. -/
theorem shared_tuple_castSucc_suffix_length_eq
    {N : ℕ}
    (a : Fin (N + 1)) :
    N + 1 - a.castSucc.1 = N - a.1 + 1 := by
  have ha' : a.castSucc.1 = a.1 := rfl
  omega

/-- Helper for Theorem 2.7.1: the terminal interval index of the recursively truncated suffix can be
viewed as the terminal interval index of the ambient suffix starting at `a.castSucc`. -/
noncomputable abbrev ambient_suffix_terminal_interval
    {N : ℕ}
    (a : Fin (N + 1)) :
    Fin (N + 1 - a.castSucc.1) :=
  Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm (Fin.last (N - a.1))

/-- Helper for Theorem 2.7.1: the terminal point index of the recursively truncated suffix can be
viewed as the terminal point index of the ambient suffix starting at `a.castSucc`. -/
noncomputable abbrev ambient_suffix_terminal_point
    {N : ℕ}
    (a : Fin (N + 1)) :
    Fin (N + 1 - a.castSucc.1 + 1) :=
  Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
    (Fin.last (N - a.1 + 1))

/-- Helper for Theorem 2.7.1: the successor of the casted terminal recursive interval index is the
same point index as the casted terminal point of the ambient suffix. -/
theorem ambient_suffix_terminal_point_succ_eq
    {N : ℕ}
    (a : Fin (N + 1)) :
    ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
      (Fin.last (N - a.1))).succ) =
      Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
        (Fin.last (N - a.1 + 1)) := by
  -- Both expressions describe the final point of the ambient suffix after one recursive unfold.
  ext
  simp [shared_tuple_castSucc_suffix_length_eq]

/-- Helper for Theorem 2.7.1: the casted terminal interval, terminal point, and terminal label of
the ambient suffix `shared_tuple_suffix_points w a.castSucc` are exactly the ambient predecessor
point, ambient endpoint, and ambient last label. -/
theorem ambient_suffix_terminal_segment_data
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (a : Fin (N + 1)) :
    shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc =
        w (Fin.castSucc (Fin.last N)) ∧
      shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a) =
        w (Fin.last (N + 1)) ∧
      shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a) =
        v (Fin.last N) := by
  have ha' : a.castSucc.1 = a.1 := rfl
  have hinterval :
      (ambient_suffix_terminal_interval a).1 = N - a.1 := by
    simp [ambient_suffix_terminal_interval]
  have hpoint :
      (ambient_suffix_terminal_point a).1 = N - a.1 + 1 := by
    simp [ambient_suffix_terminal_point]
  constructor
  · -- Evaluating the casted terminal interval of the ambient suffix lands at the predecessor of
    -- the global endpoint.
    change w ⟨a.castSucc.1 + (ambient_suffix_terminal_interval a).1, by omega⟩ =
      w (Fin.castSucc (Fin.last N))
    have hindex :
        (⟨a.castSucc.1 + (ambient_suffix_terminal_interval a).1, by omega⟩ : Fin (N + 2)) =
          Fin.castSucc (Fin.last N) := by
      ext
      calc
        a.castSucc.1 + (ambient_suffix_terminal_interval a).1 = a.1 + (N - a.1) := by
          omega
        _ = N := Nat.add_sub_of_le (Nat.le_of_lt_succ a.is_lt)
        _ = (Fin.castSucc (Fin.last N)).1 := rfl
    exact congrArg w hindex
  constructor
  · -- Evaluating the casted terminal point of the ambient suffix lands at the global endpoint.
    change w ⟨a.castSucc.1 + (ambient_suffix_terminal_point a).1, by omega⟩ =
      w (Fin.last (N + 1))
    have hindex :
        (⟨a.castSucc.1 + (ambient_suffix_terminal_point a).1, by omega⟩ : Fin (N + 2)) =
          Fin.last (N + 1) := by
      ext
      calc
        a.castSucc.1 + (ambient_suffix_terminal_point a).1 = a.1 + (N - a.1 + 1) := by
          omega
        _ = (a.1 + (N - a.1)) + 1 := by omega
        _ = N + 1 := by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ a.is_lt)]
        _ = (Fin.last (N + 1)).1 := rfl
    exact congrArg w hindex
  · -- The terminal interval of the ambient suffix inherits exactly the ambient final label.
    change v ⟨a.castSucc.1 + (ambient_suffix_terminal_interval a).1, by omega⟩ = v (Fin.last N)
    have hindex :
        (⟨a.castSucc.1 + (ambient_suffix_terminal_interval a).1, by omega⟩ : Fin (N + 1)) =
          Fin.last N := by
      ext
      calc
        a.castSucc.1 + (ambient_suffix_terminal_interval a).1 = a.1 + (N - a.1) := by
          omega
        _ = N := Nat.add_sub_of_le (Nat.le_of_lt_succ a.is_lt)
        _ = (Fin.last N).1 := rfl
    exact congrArg v hindex

/-- Helper for Theorem 2.7.1: after one unfold of the ambient literal suffix subdivision, the
terminal local factor is the ambient final local segment with the recursive-tail endpoint transport
made explicit. -/
theorem ambient_suffix_terminal_segment_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
        (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (ambient_suffix_terminal_interval a)) ≍
      eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) := by
  obtain ⟨hleft, hright, hlabel⟩ := ambient_suffix_terminal_segment_data w v a
  have hraw :
      local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
          (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (ambient_suffix_terminal_interval a)) ≍
        local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) := by
    -- Normalize the ambient suffix's terminal local factor to the literal ambient final segment.
    exact local_subpath_morphism_heq_of_eq hO hinter S γ hleft hright hlabel
  -- Reinsert exactly the recursive-tail endpoint transport needed by the preceding recursive
  -- suffix composite.
  exact
    (CategoryTheory.heq_eqToHom_comp_iff
      (local_subpath_morphism O hO hinter S γ
        (w (Fin.castSucc (Fin.last N)))
        (w (Fin.last (N + 1)))
        (v (Fin.last N))
        (hv (Fin.last N)))
      (local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
        (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (ambient_suffix_terminal_interval a)))
        (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (a := a))).2 hraw

/-- Helper for Theorem 2.7.1: unfolding the ambient literal suffix starting at `a.castSucc`
exposes the recursive ambient-suffix call followed by its terminal local factor. -/
theorem ambient_suffix_recursive_endpoint_obj_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (a : Fin (N + 1)) :
    chosen_cover_object O hO S
        (γ
          ((fun q : Fin (N - a.1 + 1) ↦
            shared_tuple_suffix_points w a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩) (Fin.last (N - a.1)))) =
      chosen_cover_object O hO S
        (γ
          (shared_tuple_suffix_points w a.castSucc
            (ambient_suffix_terminal_interval a).castSucc)) := by
  have hleft :
      ((fun q : Fin (N - a.1 + 1) ↦
        shared_tuple_suffix_points w a.castSucc ⟨q.1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩) (Fin.last (N - a.1))) =
        w (Fin.castSucc (Fin.last N)) := by
    -- The recursive ambient-suffix call still ends at the predecessor of the global endpoint.
    simpa [shared_tuple_suffix_points] using
      (shared_tuple_recursive_tail_suffix_last_eq_prevlast (w := w) (a := a))
  have hright :
      shared_tuple_suffix_points w a.castSucc
          (ambient_suffix_terminal_interval a).castSucc =
        w (Fin.castSucc (Fin.last N)) :=
    (ambient_suffix_terminal_segment_data (w := w) (v := v) (a := a)).1
  -- Both midpoint objects come from the same ambient predecessor breakpoint.
  exact
    congrArg
      (fun z : I ↦ chosen_cover_object O hO S (γ z))
      (hleft.trans hright.symm)

/-- Helper for Theorem 2.7.1: rewriting the ambient suffix interval count into explicit succ form
turns one unfold of `subdivision_morphism` into the raw recursive-tail decomposition. -/
theorem ambient_suffix_eq_def_succ
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w a.castSucc)
        (u := shared_tuple_suffix_labels v a.castSucc)
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N - a.1 + 1) ↦
            shared_tuple_suffix_points w a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (u := fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc
            ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))).castSucc))
          (shared_tuple_suffix_points w a.castSucc
            (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
              (Fin.last (N - a.1 + 1))))
          (shared_tuple_suffix_labels v a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1)))) := by
  let tCast : Fin (N - a.1 + 1 + 1) → I := fun q ↦
    shared_tuple_suffix_points w a.castSucc ⟨q.1, by
      have ha' : a.castSucc.1 = a.1 := rfl
      omega⟩
  let uCast : Fin (N - a.1 + 1) → TopologicalSpace.IsOpenCover.Index O := fun q ↦
    shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
      have ha' : a.castSucc.1 = a.1 := rfl
      omega⟩
  have hcast :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w a.castSucc)
          (u := shared_tuple_suffix_labels v a.castSucc)
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc) ≍
        subdivision_morphism O hO hinter S γ
          (t := tCast)
          (u := uCast)
          (fun q : Fin (N - a.1 + 1) ↦
            shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩) := by
    -- Transport the ambient suffix call to the exact recursive input length before unfolding it.
    have ht :
        shared_tuple_suffix_points w a.castSucc =
          fun q ↦ tCast (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a)) q) := by
      funext q
      simp [tCast, shared_tuple_castSucc_suffix_length_eq]
    have hu :
        shared_tuple_suffix_labels v a.castSucc =
          fun q ↦ uCast (Fin.cast (shared_tuple_castSucc_suffix_length_eq a) q) := by
      funext q
      simp [uCast, shared_tuple_castSucc_suffix_length_eq]
    exact
      subdivision_morphism_heq_of_cast_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (hn := shared_tuple_castSucc_suffix_length_eq a)
        (ht := ht)
        (hu := hu)
  -- Once the input length is normalized, a single unfold exposes the recursive tail and the
  -- terminal local factor in exactly the desired raw shape.
  have hterminal :
      local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc ⟨N - a.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩)
          (shared_tuple_suffix_points w a.castSucc ⟨N - a.1 + 1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩)
          (shared_tuple_suffix_labels v a.castSucc ⟨N - a.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩)
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨N - a.1, by
            have ha' : a.castSucc.1 = a.1 := rfl
            omega⟩) ≍
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc
            ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))).castSucc))
          (shared_tuple_suffix_points w a.castSucc
            (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
              (Fin.last (N - a.1 + 1))))
          (shared_tuple_suffix_labels v a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1)))) := by
    -- The direct terminal indices of the casted model are exactly the packaged cast expressions.
    exact
      local_subpath_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (a := shared_tuple_suffix_points w a.castSucc ⟨N - a.1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩)
        (a' := shared_tuple_suffix_points w a.castSucc
          ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
            (Fin.last (N - a.1))).castSucc))
        (b := shared_tuple_suffix_points w a.castSucc ⟨N - a.1 + 1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩)
        (b' := shared_tuple_suffix_points w a.castSucc
          (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
            (Fin.last (N - a.1 + 1))))
        (i := shared_tuple_suffix_labels v a.castSucc ⟨N - a.1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩)
        (i' := shared_tuple_suffix_labels v a.castSucc
          (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
            (Fin.last (N - a.1))))
        (by
          apply congrArg (shared_tuple_suffix_points w a.castSucc)
          ext
          simp [ambient_suffix_terminal_interval, shared_tuple_castSucc_suffix_length_eq])
        (by
          apply congrArg (shared_tuple_suffix_points w a.castSucc)
          ext
          simp [ambient_suffix_terminal_point, shared_tuple_castSucc_suffix_length_eq])
        (by
          apply congrArg (shared_tuple_suffix_labels v a.castSucc)
          ext
          simp [ambient_suffix_terminal_interval, shared_tuple_castSucc_suffix_length_eq])
  have hmid :
      chosen_cover_object O hO S
          (γ
            ((fun q : Fin (N - a.1 + 1) ↦
              shared_tuple_suffix_points w a.castSucc ⟨q.1, by
                have ha' : a.castSucc.1 = a.1 := rfl
                omega⟩) (Fin.last (N - a.1)))) =
        chosen_cover_object O hO S
          (γ
            (shared_tuple_suffix_points w a.castSucc
              ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
                (Fin.last (N - a.1))).castSucc))) := by
    -- The recursive tail and the packaged terminal factor meet at the same ambient predecessor
    -- breakpoint.
    exact
      ambient_suffix_recursive_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (a := a)
  have htarget :
      chosen_cover_object O hO S
          (γ
            (shared_tuple_suffix_points w a.castSucc ⟨N - a.1 + 1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)) =
        chosen_cover_object O hO S
          (γ
            (shared_tuple_suffix_points w a.castSucc
              (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
                (Fin.last (N - a.1 + 1))))) := by
    -- The two endpoint presentations are the same terminal point of the ambient suffix.
    have hend :
        shared_tuple_suffix_points w a.castSucc ⟨N - a.1 + 1, by
          have ha' : a.castSucc.1 = a.1 := rfl
          omega⟩ =
          shared_tuple_suffix_points w a.castSucc
            (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
              (Fin.last (N - a.1 + 1))) := by
      apply congrArg (shared_tuple_suffix_points w a.castSucc)
      ext
      simp [ambient_suffix_terminal_point, shared_tuple_castSucc_suffix_length_eq]
    exact congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hend
  exact
    hcast.trans <|
      (CategoryTheory.heq_comp
        rfl
        hmid
        htarget
        HEq.rfl
        hterminal).trans <|
        (by
          rfl)

/-- Helper for Theorem 2.7.1: one recursive unfold of the ambient literal suffix starting at
`a.castSucc` exposes the recursive tail followed by its raw terminal local factor. -/
theorem ambient_suffix_raw_tail_unfold_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w a.castSucc)
        (u := shared_tuple_suffix_labels v a.castSucc)
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N - a.1 + 1) ↦
            shared_tuple_suffix_points w a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (u := fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc
            ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))).castSucc))
          (shared_tuple_suffix_points w a.castSucc
            (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
              (Fin.last (N - a.1 + 1))))
          (shared_tuple_suffix_labels v a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1))))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
              (Fin.last (N - a.1)))) := by
  -- Separate the raw succ-branch reduction from later terminal-index packaging.
  simpa using
    ambient_suffix_eq_def_succ
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)

/-- Helper for Theorem 2.7.1: the raw terminal local factor of the ambient suffix is the same
local morphism as the packaged ambient terminal factor. -/
theorem ambient_suffix_raw_terminal_factor_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc
          ((Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
            (Fin.last (N - a.1))).castSucc))
        (shared_tuple_suffix_points w a.castSucc
          (Fin.cast (congrArg Nat.succ (shared_tuple_castSucc_suffix_length_eq a).symm)
            (Fin.last (N - a.1 + 1))))
        (shared_tuple_suffix_labels v a.castSucc
          (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
            (Fin.last (N - a.1))))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (Fin.cast (shared_tuple_castSucc_suffix_length_eq a).symm
            (Fin.last (N - a.1)))) ≍
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
          (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (ambient_suffix_terminal_interval a)) := by
  -- The raw terminal factor is just the packaged terminal factor with the casts written out.
  simpa [ambient_suffix_terminal_interval, ambient_suffix_terminal_point]

/-- Helper for Theorem 2.7.1: after the ambient suffix has been unfolded, the only remaining
mismatch is the recursive-endpoint transport inserted in front of the packaged ambient terminal
factor. -/
theorem ambient_suffix_terminal_transport_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
        (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (ambient_suffix_terminal_interval a)) ≍
      eqToHom (ambient_suffix_recursive_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
          (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (ambient_suffix_terminal_interval a)) := by
  -- Reinsert the recursive-endpoint transport in front of the already normalized ambient terminal
  -- factor.
  exact
    (CategoryTheory.heq_eqToHom_comp_iff
      (local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
        (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (ambient_suffix_terminal_interval a)))
      (local_subpath_morphism O hO hinter S γ
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
        (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
        (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc
          (ambient_suffix_terminal_interval a)))
      (ambient_suffix_recursive_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (a := a))).2 HEq.rfl

/-- Helper for Theorem 2.7.1: unfolding the ambient literal suffix starting at `a.castSucc`
exposes the recursive ambient-suffix call, the midpoint transport to the ambient terminal segment,
and then the ambient terminal local factor itself. -/
theorem ambient_suffix_subdivision_unfold_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w a.castSucc)
        (u := shared_tuple_suffix_labels v a.castSucc)
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc) ≍
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N - a.1 + 1) ↦
            shared_tuple_suffix_points w a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (u := fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_labels v a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩)
          (fun q : Fin (N - a.1) ↦
            shared_tuple_suffix_subordinate γ w v hv a.castSucc ⟨q.1, by
              have ha' : a.castSucc.1 = a.1 := rfl
              omega⟩) ≫
        eqToHom (ambient_suffix_recursive_endpoint_obj_eq
          (hO := hO)
          (S := S)
          (γ := γ)
          (w := w)
          (v := v)
          (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
          (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (ambient_suffix_terminal_interval a)) := by
  have hraw :=
    ambient_suffix_raw_tail_unfold_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)
  have hraw_terminal :=
    ambient_suffix_raw_terminal_factor_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)
  have hterminal :=
    ambient_suffix_terminal_transport_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)
  -- First expose the exact recursive tail, then package only the terminal factor through the
  -- recursive endpoint transport.
  exact
    hraw.trans <|
      (CategoryTheory.heq_comp rfl rfl rfl HEq.rfl hraw_terminal).trans <|
        CategoryTheory.heq_comp rfl
          (ambient_suffix_recursive_endpoint_obj_eq
            (hO := hO)
            (S := S)
            (γ := γ)
            (w := w)
            (v := v)
            (a := a))
          rfl
          HEq.rfl
          hterminal

/-- Helper for Theorem 2.7.1: the recursive-tail literal shared suffix followed by the ambient last
local segment is exactly the ambient literal shared suffix. -/
theorem subdivision_morphism_suffix_append_last_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points
          (fun q : Fin (N + 1) ↦ w q.castSucc)
          a)
        (u := shared_tuple_suffix_labels
          (fun q : Fin N ↦ v q.castSucc)
          a)
        (shared_tuple_suffix_subordinate
          γ
          (fun q : Fin (N + 1) ↦ w q.castSucc)
          (fun q : Fin N ↦ v q.castSucc)
          (fun q : Fin N ↦ hv q.castSucc)
          a) ≫
        eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
          (hO := hO)
          (S := S)
          (γ := γ)
          (w := w)
          (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) ≍
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w a.castSucc)
        (u := shared_tuple_suffix_labels v a.castSucc)
        (shared_tuple_suffix_subordinate γ w v hv a.castSucc) := by
  have hunfold :=
    ambient_suffix_subdivision_unfold_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)
  have hstep :=
    subdivision_morphism_literal_suffix_step
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)
      (a := a)
  have hterminal_compare :
      eqToHom (ambient_suffix_recursive_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_interval a).castSucc)
          (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))
          (shared_tuple_suffix_labels v a.castSucc (ambient_suffix_terminal_interval a))
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc
            (ambient_suffix_terminal_interval a)) ≍
      eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
        (hO := hO)
        (S := S)
        (γ := γ)
        (w := w)
        (a := a)) ≫
        local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) := by
    -- The packaged terminal factor already compares to the ambient final segment; removing the
    -- ambient recursive-endpoint transport leaves exactly the target terminal factor.
    exact
      (ambient_suffix_terminal_transport_heq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (hv := hv)
        (a := a)).symm.trans <|
        ambient_suffix_terminal_segment_heq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (v := v)
          (hv := hv)
          (a := a)
  have hterminal_target :
      chosen_cover_object O hO S
          (γ (shared_tuple_suffix_points w a.castSucc (ambient_suffix_terminal_point a))) =
        chosen_cover_object O hO S
          (γ (w (Fin.last (N + 1)))) := by
    -- The packaged ambient suffix endpoint is the global terminal breakpoint.
    exact
      congrArg
        (fun z : I ↦ chosen_cover_object O hO S (γ z))
        (ambient_suffix_terminal_segment_data (w := w) (v := v) (a := a)).2.1
  -- Normalize the recursive tail on the left and the ambient suffix on the right to the same
  -- one-step suffix decomposition.
  exact
    (CategoryTheory.heq_comp rfl
      (congrArg
        (fun z : I ↦ chosen_cover_object O hO S (γ z))
        (congrArg
          (fun f : Fin (N - a.1 + 1) → I ↦ f (Fin.last (N - a.1)))
          (shared_tuple_suffix_points_recursive_castSucc w a))).symm
      hterminal_target.symm
      hstep.symm
      hterminal_compare.symm).trans hunfold.symm

/-- Helper for Theorem 2.7.1: if the reassembly theorem already holds for the tuple obtained by
dropping the global terminal breakpoint, then composing that recursive factorization with the
ambient last interval yields the reassembly theorem at the corresponding ambient cutpoint. -/
theorem subdivision_morphism_literal_cutpoint_reassembly_step_of_tail
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (a : Fin (N + 1))
    (htail :
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N + 1) ↦ w q.castSucc)
          (u := fun q : Fin N ↦ v q.castSucc)
          (fun q : Fin N ↦ hv q.castSucc) ≍
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points (fun q : Fin (N + 1) ↦ w q.castSucc) a)
            (u := shared_tuple_prefix_labels
              (fun q : Fin N ↦ v q.castSucc)
              a)
            (shared_tuple_prefix_subordinate
              γ
              (fun q : Fin (N + 1) ↦ w q.castSucc)
              (fun q : Fin N ↦ v q.castSucc)
              (fun q : Fin N ↦ hv q.castSucc)
              a) ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points
              (fun q : Fin (N + 1) ↦ w q.castSucc)
              a)
            (u := shared_tuple_suffix_labels
              (fun q : Fin N ↦ v q.castSucc)
              a)
            (shared_tuple_suffix_subordinate
              γ
              (fun q : Fin (N + 1) ↦ w q.castSucc)
              (fun q : Fin N ↦ v q.castSucc)
              (fun q : Fin N ↦ hv q.castSucc)
              a)) :
    subdivision_morphism O hO hinter S γ
        (t := w)
        (u := v)
        hv ≍
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w a.castSucc)
          (u := shared_tuple_prefix_labels v a.castSucc)
          (shared_tuple_prefix_subordinate γ w v hv a.castSucc) ≫
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w a.castSucc)
          (u := shared_tuple_suffix_labels v a.castSucc)
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc) := by
  let prefixTail :=
    subdivision_morphism O hO hinter S γ
      (t := shared_tuple_prefix_points (fun q : Fin (N + 1) ↦ w q.castSucc) a)
      (u := shared_tuple_prefix_labels (fun q : Fin N ↦ v q.castSucc) a)
      (shared_tuple_prefix_subordinate
        γ
        (fun q : Fin (N + 1) ↦ w q.castSucc)
        (fun q : Fin N ↦ v q.castSucc)
        (fun q : Fin N ↦ hv q.castSucc)
        a)
  let suffixTail :=
    subdivision_morphism O hO hinter S γ
      (t := shared_tuple_suffix_points (fun q : Fin (N + 1) ↦ w q.castSucc) a)
      (u := shared_tuple_suffix_labels (fun q : Fin N ↦ v q.castSucc) a)
      (shared_tuple_suffix_subordinate
        γ
        (fun q : Fin (N + 1) ↦ w q.castSucc)
        (fun q : Fin N ↦ v q.castSucc)
        (fun q : Fin N ↦ hv q.castSucc)
        a)
  let localLast :=
    local_subpath_morphism O hO hinter S γ
      (w (Fin.castSucc (Fin.last N)))
      (w (Fin.last (N + 1)))
      (v (Fin.last N))
      (hv (Fin.last N))
  have hunfold :
      subdivision_morphism O hO hinter S γ
          (t := w)
          (u := v)
          hv ≍
        subdivision_morphism O hO hinter S γ
            (t := fun q : Fin (N + 1) ↦ w q.castSucc)
            (u := fun q : Fin N ↦ v q.castSucc)
            (fun q : Fin N ↦ hv q.castSucc) ≫
          localLast := by
    -- Unfold the ambient subdivision once to expose the recursive tail and the last local factor.
    simpa [localLast, subdivision_morphism]
  have hlocal_transport :
      localLast ≍
        eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
          (hO := hO)
          (S := S)
          (γ := γ)
          (w := w)
          (a := a)) ≫
          localLast := by
    -- The only extra data needed after the recursive tail is the endpoint transport into the
    -- ambient final segment.
    exact
      (CategoryTheory.heq_eqToHom_comp_iff
        localLast
        localLast
        (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
          (hO := hO)
          (S := S)
          (γ := γ)
          (w := w)
          (a := a))).2 HEq.rfl
  have htail_comp :
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N + 1) ↦ w q.castSucc)
          (u := fun q : Fin N ↦ v q.castSucc)
          (fun q : Fin N ↦ hv q.castSucc) ≫
          localLast ≍
        (prefixTail ≫ suffixTail) ≫
          (eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
            (hO := hO)
            (S := S)
            (γ := γ)
            (w := w)
            (a := a)) ≫
            localLast) := by
    -- Right-whisker the recursive factorization by the transported ambient final segment.
    exact
      CategoryTheory.heq_comp
        rfl
        (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
          (hO := hO)
          (S := S)
          (γ := γ)
          (w := w)
          (a := a)).symm
        rfl
        htail
        hlocal_transport
  have hsuffix :
      suffixTail ≫
          eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
            (hO := hO)
            (S := S)
            (γ := γ)
            (w := w)
            (a := a)) ≫
          localLast ≍
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w a.castSucc)
          (u := shared_tuple_suffix_labels v a.castSucc)
          (shared_tuple_suffix_subordinate γ w v hv a.castSucc) := by
    -- The transported recursive tail plus the ambient final segment is exactly the ambient suffix.
    exact
      subdivision_morphism_suffix_append_last_heq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (hv := hv)
        (a := a)
  have hprefix :
      prefixTail ≍
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w a.castSucc)
          (u := shared_tuple_prefix_labels v a.castSucc)
          (shared_tuple_prefix_subordinate γ w v hv a.castSucc) := by
    -- The recursive prefix reads exactly the same literal shared prefix of the ambient tuple.
    exact
      subdivision_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := shared_tuple_prefix_points (fun q : Fin (N + 1) ↦ w q.castSucc) a)
        (u := shared_tuple_prefix_labels (fun q : Fin N ↦ v q.castSucc) a)
        (t' := shared_tuple_prefix_points w a.castSucc)
        (u' := shared_tuple_prefix_labels v a.castSucc)
        (ht := shared_tuple_prefix_points_recursive_castSucc w a)
        (hu := shared_tuple_prefix_labels_recursive_castSucc v a)
  have hsuffix_whisker :
      prefixTail ≫
          (suffixTail ≫
            eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
              (hO := hO)
              (S := S)
              (γ := γ)
              (w := w)
              (a := a)) ≫
            localLast) ≍
        prefixTail ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points w a.castSucc)
            (u := shared_tuple_suffix_labels v a.castSucc)
            (shared_tuple_suffix_subordinate γ w v hv a.castSucc) := by
    have hprefix_suffix_mid :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_prefix_points
                (fun q : Fin (N + 1) ↦ w q.castSucc)
                a
                (Fin.last a.1))) =
          chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points
                (fun q : Fin (N + 1) ↦ w q.castSucc)
                a
                0)) := by
      -- The recursive prefix ends where the recursive suffix begins.
      simp [shared_tuple_prefix_points, shared_tuple_suffix_points]
    have hsuffix_target :
        chosen_cover_object O hO S
            (γ (w (Fin.last (N + 1)))) =
          chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points
                w
                a.castSucc
                (Fin.last (N + 1 - a.castSucc.1)))) := by
      -- The ambient suffix still ends at the global terminal breakpoint.
      have hsuffix_last :
          shared_tuple_suffix_points
              w
              a.castSucc
              (Fin.last (N + 1 - a.castSucc.1)) =
            w (Fin.last (N + 1)) := by
        change
          w ⟨a.castSucc.1 + (Fin.last (N + 1 - a.castSucc.1)).1, by
            have hq : (Fin.last (N + 1 - a.castSucc.1)).1 < N + 1 - a.castSucc.1 + 1 :=
              (Fin.last (N + 1 - a.castSucc.1)).is_lt
            omega⟩ =
            w (Fin.last (N + 1))
        congr 1
        ext
        simp
      exact congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hsuffix_last.symm
    -- Whisker the suffix collapse by the already-fixed recursive prefix.
    exact CategoryTheory.heq_comp rfl hprefix_suffix_mid hsuffix_target HEq.rfl hsuffix
  have hprefix_whisker :
      prefixTail ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points w a.castSucc)
            (u := shared_tuple_suffix_labels v a.castSucc)
            (shared_tuple_suffix_subordinate γ w v hv a.castSucc) ≍
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w a.castSucc)
            (u := shared_tuple_prefix_labels v a.castSucc)
            (shared_tuple_prefix_subordinate γ w v hv a.castSucc) ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points w a.castSucc)
            (u := shared_tuple_suffix_labels v a.castSucc)
            (shared_tuple_suffix_subordinate γ w v hv a.castSucc) := by
    -- Finally rewrite the recursive prefix to the ambient literal prefix.
    exact CategoryTheory.heq_comp rfl rfl rfl hprefix HEq.rfl
  have htail_assoc :
      subdivision_morphism O hO hinter S γ
          (t := fun q : Fin (N + 1) ↦ w q.castSucc)
          (u := fun q : Fin N ↦ v q.castSucc)
          (fun q : Fin N ↦ hv q.castSucc) ≫
          localLast ≍
        prefixTail ≫
          (suffixTail ≫
            eqToHom (shared_tuple_recursive_tail_suffix_endpoint_obj_eq
              (hO := hO)
              (S := S)
              (γ := γ)
              (w := w)
              (a := a)) ≫
            localLast) := by
    -- Reassociate the right-hand side so the suffix collapse can be whiskered cleanly.
    simpa [prefixTail, suffixTail, Category.assoc] using htail_comp
  exact hunfold.trans <| htail_assoc.trans <| hsuffix_whisker.trans hprefix_whisker

/-- Helper for Theorem 2.7.1: the terminal interval exposed by decomposing the literal prefix at
the penultimate breakpoint is exactly the ambient final local segment. -/
theorem terminal_prefix_last_local_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
      local_subpath_morphism O hO hinter S γ
          (shared_tuple_prefix_points w (Fin.last N).succ (Fin.castSucc (Fin.last N)))
          (shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)))
          (shared_tuple_prefix_labels v (Fin.last N).succ (Fin.last N))
          (shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ (Fin.last N)) ≍
      local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) := by
  -- The terminal interval of the literal prefix is exactly the ambient final shared interval.
  exact
    local_subpath_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (ha := by
        change w ⟨N, by omega⟩ = w (Fin.castSucc (Fin.last N))
        congr 1)
      (hb := by
        change w ⟨N + 1, by omega⟩ = w (Fin.last (N + 1))
        congr 1)
      (hi := by
        change v ⟨N, by omega⟩ = v (Fin.last N)
        congr 1)

/-- Helper for Theorem 2.7.1: the recursive factor appearing in the terminal ambient-suffix
specialization is already the identity morphism. -/
theorem terminal_suffix_recursive_factor_eq_id
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := fun q : Fin 1 ↦
          shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)) ⟨q.1, by omega⟩)
        (u := fun q : Fin 0 ↦
          shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)) ⟨q.1, by omega⟩)
        (fun q : Fin 0 ↦
          shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N)) ⟨q.1, by omega⟩) =
      𝟙 _ := by
  -- The terminal suffix has no recursive subintervals left, so the recursive factor is the base
  -- case of `subdivision_morphism`.
  rfl

/-- Helper for Theorem 2.7.1: the raw terminal indices `⟨N, _⟩`, `⟨N + 1, _⟩`, and `⟨N, _⟩`
appearing after one-step simplification of the terminal suffix are the canonical ambient final
segment data. -/
theorem terminal_suffix_raw_index_local_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    local_subpath_morphism O hO hinter S γ
        (w ⟨N, by omega⟩)
        (w ⟨N + 1, by omega⟩)
        (v ⟨N, by omega⟩)
        (hv ⟨N, by omega⟩) ≍
      local_subpath_morphism O hO hinter S γ
        (w (Fin.castSucc (Fin.last N)))
        (w (Fin.last (N + 1)))
        (v (Fin.last N))
        (hv (Fin.last N)) := by
  -- The simplified raw terminal indices are definitionally the predecessor breakpoint, the global
  -- endpoint, and the ambient last label.
  exact
    local_subpath_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (ha := by
        change w ⟨N, by omega⟩ = w (Fin.castSucc (Fin.last N))
        congr 1)
      (hb := by
        change w ⟨N + 1, by omega⟩ = w (Fin.last (N + 1))
        congr 1)
      (hi := by
        change v ⟨N, by omega⟩ = v (Fin.last N)
        congr 1)

/-- Helper for Theorem 2.7.1: the explicit `Fin 2` / `Fin 1` model of the terminal literal suffix
still lies in the ambient final cover member. -/
theorem terminal_literal_suffix_explicit_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    ∀ q : Fin 1,
      Set.range
          (γ.subpath
            ((fun r : Fin 2 ↦
              if r = 0 then w (Fin.castSucc (Fin.last N)) else w (Fin.last (N + 1))) q.castSucc)
            ((fun r : Fin 2 ↦
              if r = 0 then w (Fin.castSucc (Fin.last N)) else w (Fin.last (N + 1))) q.succ)) ⊆
        O ((fun _ : Fin 1 ↦ v (Fin.last N)) q) := by
  intro q
  -- The explicit terminal model has only one interval, which is exactly the ambient final
  -- interval already controlled by `hv`.
  fin_cases q
  simpa [Path.subpath] using shared_tuple_terminal_suffix_subordinate_last γ w v hv

/-- Helper for Theorem 2.7.1: the hidden terminal-suffix interval count coming from
`Fin.castSucc (Fin.last N)` is definitionally the ordinary subtraction `N + 1 - N`. -/
theorem terminal_literal_suffix_hidden_length_eq
    {N : ℕ} :
    N + 1 - (Fin.castSucc (Fin.last N)).1 = N + 1 - N := by
  rfl

/-- Helper for Theorem 2.7.1: after transporting the terminal literal suffix to the canonical
one-interval `Fin 2` / `Fin 1` model, the unique interval is still subordinate to the ambient
final cover member. -/
theorem terminal_literal_suffix_canonical_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    ∀ q : Fin 1,
      Set.range
          (γ.subpath
            ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r)) q.castSucc)
            ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r)) q.succ)) ⊆
        O ((fun q : Fin 1 ↦
          shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
            (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q)) q) := by
  intro q
  -- Transport the hidden terminal suffix data to the canonical one-interval model before reading
  -- off the unique subordinate interval.
  simpa [shared_tuple_terminal_suffix_length_eq_one] using
    shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))
      (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q)

/-- Helper for Theorem 2.7.1: the hidden terminal literal suffix call is heterogeneously equal to
the canonical one-interval `Fin 2` / `Fin 1` model obtained by transporting its index length. -/
theorem terminal_literal_suffix_hidden_to_canonical_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
        (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
        (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) ≍
      subdivision_morphism O hO hinter S γ
        (t := fun r : Fin 2 ↦
          shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
            (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
        (u := fun q : Fin 1 ↦
          shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
            (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
        (terminal_literal_suffix_canonical_subordinate γ w v hv) := by
  -- Transport the hidden suffix length to the explicit one-interval length before comparing the
  -- recursive applications themselves.
  have ht :
      shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)) =
        fun q ↦
          (fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
            (Fin.cast
              (congrArg Nat.succ (shared_tuple_terminal_suffix_length_eq_one : _)) q) := by
    funext q
    simp [shared_tuple_terminal_suffix_length_eq_one]
  have hu :
      shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)) =
        fun q ↦
          (fun r : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
            (Fin.cast (shared_tuple_terminal_suffix_length_eq_one : _) q) := by
    funext q
    simp [shared_tuple_terminal_suffix_length_eq_one]
  exact
    subdivision_morphism_heq_of_cast_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (hn := shared_tuple_terminal_suffix_length_eq_one)
      (ht := ht)
      (hu := hu)

/-- Helper for Theorem 2.7.1: the terminal literal suffix can be transported once and for all to
the explicit one-interval subdivision on `Fin 2` / `Fin 1`. -/
theorem terminal_literal_suffix_cast_bridge
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
        (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
        (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) ≍
    subdivision_morphism O hO hinter S γ
        (t := fun q : Fin 2 ↦
          if q = 0 then w (Fin.castSucc (Fin.last N)) else w (Fin.last (N + 1)))
        (u := fun _ : Fin 1 ↦ v (Fin.last N))
        (terminal_literal_suffix_explicit_subordinate γ w v hv) := by
  -- First move the hidden terminal suffix to the canonical one-interval model.
  have hcanonical :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
          (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
          (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) ≍
        subdivision_morphism O hO hinter S γ
          (t := fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
          (u := fun q : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
          (terminal_literal_suffix_canonical_subordinate γ w v hv) := by
    exact terminal_literal_suffix_hidden_to_canonical_heq hO hinter S γ w v hv
  have hexplicit :
      subdivision_morphism O hO hinter S γ
          (t := fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
          (u := fun q : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
          (terminal_literal_suffix_canonical_subordinate γ w v hv) ≍
        subdivision_morphism O hO hinter S γ
          (t := fun q : Fin 2 ↦
            if q = 0 then w (Fin.castSucc (Fin.last N)) else w (Fin.last (N + 1)))
          (u := fun _ : Fin 1 ↦ v (Fin.last N))
          (terminal_literal_suffix_explicit_subordinate γ w v hv) := by
    -- Then rewrite the canonical point and label tuples to the explicit endpoint-normalized
    -- presentation.
    exact
      subdivision_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (ht := shared_tuple_terminal_suffix_points_cast_eq w)
        (hu := shared_tuple_terminal_suffix_labels_cast_eq v)
  exact hcanonical.trans hexplicit

/-- Helper for Theorem 2.7.1: the terminal literal suffix is a one-interval subdivision whose
single recursive unfold is the ambient final local segment. -/
theorem terminal_literal_suffix_raw_unfold_heq_last_local
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
        (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
        (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) ≍
      local_subpath_morphism O hO hinter S γ
        (w (Fin.castSucc (Fin.last N)))
        (w (Fin.last (N + 1)))
        (v (Fin.last N))
        (hv (Fin.last N)) := by
  -- Route correction: normalize the hidden terminal suffix at the input-data level, not by
  -- unfolding the equation compiler for `subdivision_morphism`.
  have hcanonical :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
          (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
          (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) ≍
        subdivision_morphism O hO hinter S γ
          (t := fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
          (u := fun q : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
          (terminal_literal_suffix_canonical_subordinate γ w v hv) := by
    exact terminal_literal_suffix_hidden_to_canonical_heq hO hinter S γ w v hv
  have hone :
      subdivision_morphism O hO hinter S γ
          (t := fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
          (u := fun q : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
          (terminal_literal_suffix_canonical_subordinate γ w v hv) ≍
        local_subpath_morphism O hO hinter S γ
          ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r)) 0)
          ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
            (Fin.last 1))
          ((fun q : Fin 1 ↦
              shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
            (Fin.last 0))
          (terminal_literal_suffix_canonical_subordinate γ w v hv (Fin.last 0)) := by
    -- The canonical terminal model has exactly one interval.
    exact
      subdivision_morphism_single_interval_heq_local
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := fun r : Fin 2 ↦
          shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
            (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
        (u := fun q : Fin 1 ↦
          shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
            (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
        (hu := terminal_literal_suffix_canonical_subordinate γ w v hv)
  have hlocal :
      local_subpath_morphism O hO hinter S γ
          ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r)) 0)
          ((fun r : Fin 2 ↦
              shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
            (Fin.last 1))
          ((fun q : Fin 1 ↦
              shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
                (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
            (Fin.last 0))
          (terminal_literal_suffix_canonical_subordinate γ w v hv (Fin.last 0)) ≍
        local_subpath_morphism O hO hinter S γ
          (w (Fin.castSucc (Fin.last N)))
          (w (Fin.last (N + 1)))
          (v (Fin.last N))
          (hv (Fin.last N)) := by
    -- Normalize the canonical endpoints and label to the ambient final local segment.
    have hstart :
        ((fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r)) 0) =
          w (Fin.castSucc (Fin.last N)) := by
      simpa using congrArg (fun f : Fin 2 → I ↦ f 0) (shared_tuple_terminal_suffix_points_cast_eq w)
    have hend :
        ((fun r : Fin 2 ↦
            shared_tuple_suffix_points w (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) r))
          (Fin.last 1)) =
          w (Fin.last (N + 1)) := by
      simpa using
        congrArg
          (fun f : Fin 2 → I ↦ f (Fin.last 1))
          (shared_tuple_terminal_suffix_points_cast_eq w)
    have hlabel :
        ((fun q : Fin 1 ↦
            shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N))
              (Fin.cast (by simp [shared_tuple_terminal_suffix_length_eq_one]) q))
          (Fin.last 0)) =
          v (Fin.last N) := by
      simpa using
        congrArg
          (fun f : Fin 1 → TopologicalSpace.IsOpenCover.Index O ↦ f (Fin.last 0))
          (shared_tuple_terminal_suffix_labels_cast_eq v)
    exact
      local_subpath_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        hstart
        hend
        hlabel
  exact hcanonical.trans (hone.trans hlocal)

/-- Helper for Theorem 2.7.1: the final local segment in the terminal prefix decomposition agrees
with the one-interval terminal literal suffix subdivision. -/
theorem terminal_literal_suffix_subdivision_heq_last_local
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 2) → I)
    (v : Fin (N + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin (N + 1), Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
      local_subpath_morphism O hO hinter S γ
          (shared_tuple_prefix_points w (Fin.last N).succ (Fin.castSucc (Fin.last N)))
          (shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)))
          (shared_tuple_prefix_labels v (Fin.last N).succ (Fin.last N))
          (shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ (Fin.last N)) ≍
      subdivision_morphism O hO hinter S γ
        (t := shared_tuple_suffix_points w (Fin.castSucc (Fin.last N)))
        (u := shared_tuple_suffix_labels v (Fin.castSucc (Fin.last N)))
        (shared_tuple_suffix_subordinate γ w v hv (Fin.castSucc (Fin.last N))) := by
  -- Compare both sides to the same ambient final local segment.
  exact
    (terminal_prefix_last_local_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := v)
      (hv := hv)).trans <|
      (terminal_literal_suffix_raw_unfold_heq_last_local
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := w)
        (v := v)
        (hv := hv)).symm

/-- Helper for Theorem 2.7.1: splitting a literal shared subdivision at a nonterminal ambient
cutpoint factors the full subdivision composite as the literal prefix up to that cutpoint followed
by the literal suffix starting there. -/
theorem subdivision_morphism_literal_nonterminal_cutpoint_reassembly_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k))
    (kPoint : Fin (N + 1))
    (hk : kPoint ≠ Fin.last N) :
    subdivision_morphism O hO hinter S γ
        (t := w)
        (u := v)
        hv ≍
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w kPoint)
          (u := shared_tuple_prefix_labels v kPoint)
          (shared_tuple_prefix_subordinate γ w v hv kPoint) ≫
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := shared_tuple_suffix_labels v kPoint)
          (shared_tuple_suffix_subordinate γ w v hv kPoint) := by
  -- Route correction: the old `a.castSucc`-parameterized reassembly exposed transport arithmetic
  -- instead of the actual ambient split point used by downstream consumers.
  cases N with
  | zero =>
      exfalso
      fin_cases kPoint
      exact hk rfl
  | succ N =>
      cases kPoint using Fin.lastCases with
      | last =>
          exfalso
          exact hk rfl
      | cast a =>
          cases a using Fin.lastCases with
          | last =>
            -- The cutpoint is the penultimate ambient breakpoint, so the suffix is the terminal
            -- one-interval block and the prefix is the recursively truncated ambient tuple.
            have hfull :
                subdivision_morphism O hO hinter S γ
                    (t := w)
                    (u := v)
                    hv =
                  subdivision_morphism O hO hinter S γ
                      (t := fun q ↦
                        shared_tuple_prefix_points w (Fin.last N).succ q.castSucc)
                      (u := fun q ↦
                        shared_tuple_prefix_labels v (Fin.last N).succ q.castSucc)
                      (fun q : Fin N ↦
                        shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ q.castSucc) ≫
                    local_subpath_morphism O hO hinter S γ
                      (shared_tuple_prefix_points w (Fin.last N).succ (Fin.castSucc (Fin.last N)))
                      (shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)))
                      (shared_tuple_prefix_labels v (Fin.last N).succ (Fin.last N))
                      (shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ
                        (Fin.last N)) := by
              -- Unfold the full subdivision once at the global terminal interval, then rewrite the
              -- resulting prefix decomposition by expanding the literal prefix data directly.
              simpa [shared_tuple_prefix_points, shared_tuple_prefix_labels]
                using
                  subdivision_morphism_prefix_decomposition_at_cutpoint
                    (hO := hO)
                    (hinter := hinter)
                    (S := S)
                    (γ := γ)
                    (w := w)
                    (v := v)
                    (hv := hv)
                    (k := Fin.last N)
            have hprefix :
                subdivision_morphism O hO hinter S γ
                    (t := fun q ↦
                      shared_tuple_prefix_points w (Fin.last N).succ q.castSucc)
                    (u := fun q ↦
                      shared_tuple_prefix_labels v (Fin.last N).succ q.castSucc)
                    (fun q : Fin N ↦
                      shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ q.castSucc) =
                  subdivision_morphism O hO hinter S γ
                    (t := shared_tuple_prefix_points w (Fin.last N).castSucc)
                    (u := shared_tuple_prefix_labels v (Fin.last N).castSucc)
                    (shared_tuple_prefix_subordinate γ w v hv (Fin.last N).castSucc) := by
              -- The recursive prefix created by the unfold is exactly the literal shared prefix
              -- ending at the penultimate point.
              simpa using
                subdivision_morphism_shared_prefix_recursive_eq
                  (hO := hO)
                  (hinter := hinter)
                  (S := S)
                  (γ := γ)
                  (w := w)
                  (v := v)
                  (hv := hv)
                  (k := Fin.last N)
            have hsuffix :
                local_subpath_morphism O hO hinter S γ
                    (shared_tuple_prefix_points w (Fin.last N).succ (Fin.castSucc (Fin.last N)))
                    (shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)))
                    (shared_tuple_prefix_labels v (Fin.last N).succ (Fin.last N))
                    (shared_tuple_prefix_subordinate γ w v hv (Fin.last N).succ
                      (Fin.last N)) ≍
                  subdivision_morphism O hO hinter S γ
                    (t := shared_tuple_suffix_points w (Fin.last N).castSucc)
                    (u := shared_tuple_suffix_labels v (Fin.last N).castSucc)
                    (shared_tuple_suffix_subordinate γ w v hv (Fin.last N).castSucc) := by
              -- Consume the dedicated terminal-suffix comparison in the exact morphism shape
              -- needed by the penultimate-cutpoint branch.
              exact
                terminal_literal_suffix_subdivision_heq_last_local
                  (hO := hO)
                  (hinter := hinter)
                  (S := S)
                  (γ := γ)
                  (w := w)
                  (v := v)
                  (hv := hv)
            have hsuffix_target :
                chosen_cover_object O hO S
                    (γ (shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)))) =
                  chosen_cover_object O hO S
                    (γ
                      (shared_tuple_suffix_points w (Fin.last N).castSucc
                        (Fin.last (N + 1 - (Fin.last N).castSucc.1)))) := by
              have hprefix_last :
                  shared_tuple_prefix_points w (Fin.last N).succ (Fin.last (N + 1)) =
                    w (Fin.last (N + 1)) := by
                -- The literal prefix ending at the global terminal point still evaluates to the
                -- global terminal breakpoint there.
                change
                  w ⟨(Fin.last (N + 1)).1, by
                    exact
                      Nat.lt_of_lt_of_le
                        (Fin.last (N + 1)).is_lt
                        (Nat.succ_le_of_lt (Fin.last N).succ.is_lt)⟩ =
                    w (Fin.last (N + 1))
                congr 1
              have hsuffix_last :
                  shared_tuple_suffix_points w (Fin.last N).castSucc
                      (Fin.last (N + 1 - (Fin.last N).castSucc.1)) =
                    w (Fin.last (N + 1)) := by
                -- The terminal literal suffix ends at the ambient terminal breakpoint.
                change
                  w ⟨(Fin.last N).castSucc.1 +
                      (Fin.last (N + 1 - (Fin.last N).castSucc.1)).1, by omega⟩ =
                    w (Fin.last (N + 1))
                congr 1
                ext
                simp
              -- Both second factors land at the same chosen global endpoint object.
              exact
                congrArg
                  (fun z : I ↦ chosen_cover_object O hO S (γ z))
                  (hprefix_last.trans hsuffix_last.symm)
            exact
              hfull.heq.trans <|
                CategoryTheory.heq_comp rfl rfl hsuffix_target hprefix.heq hsuffix
          | cast b =>
            -- The strictly earlier cutpoint is handled by the recursive theorem on the truncated
            -- ambient tuple, then lifted back by the dedicated one-step tail reassembly theorem.
            exact
              subdivision_morphism_literal_cutpoint_reassembly_step_of_tail
                (hO := hO)
                (hinter := hinter)
                (S := S)
                (γ := γ)
                (w := w)
                (v := v)
                (hv := hv)
                (a := b.castSucc)
                (htail := subdivision_morphism_literal_nonterminal_cutpoint_reassembly_heq
                  (hO := hO)
                  (hinter := hinter)
                  (S := S)
                  (γ := γ)
                  (w := fun q : Fin (N + 1) ↦ w q.castSucc)
                  (v := fun q : Fin N ↦ v q.castSucc)
                  (hv := fun q : Fin N ↦ hv q.castSucc)
                  (kPoint := b.castSucc)
                  (hk := by
                    intro h
                    apply b.castSucc_ne_last
                    simpa using h))

/-- Helper for Theorem 2.7.1: the literal shared prefix ending at the global terminal point is the
entire shared tuple. -/
theorem shared_tuple_prefix_points_last_eq_self
    {N : ℕ}
    (w : Fin (N + 1) → I) :
    shared_tuple_prefix_points w (Fin.last N) = w := by
  -- Reading the literal prefix up to the terminal point keeps every breakpoint of the tuple.
  funext q
  simp [shared_tuple_prefix_points]

/-- Helper for Theorem 2.7.1: the literal shared-prefix label family ending at the global terminal
point is the full label family. -/
theorem shared_tuple_prefix_labels_last_eq_self
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N : ℕ}
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O) :
    shared_tuple_prefix_labels v (Fin.last N) = v := by
  -- Truncating the labels at the terminal point does not discard any interval labels.
  funext q
  simp [shared_tuple_prefix_labels]

/-- Helper for Theorem 2.7.1: replacing a shared tuple by the literal prefix ending at its terminal
point does not change the resulting subdivision composite. -/
theorem subdivision_morphism_prefix_last_heq_self
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (v : Fin N → TopologicalSpace.IsOpenCover.Index O)
    (hv : ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (v k)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w (Fin.last N))
        (u := shared_tuple_prefix_labels v (Fin.last N))
        (shared_tuple_prefix_subordinate γ w v hv (Fin.last N)) ≍
      subdivision_morphism O hO hinter S γ
        (t := w)
        (u := v)
        hv := by
  -- Normalize the literal terminal prefix back to the original shared tuple and label family.
  exact
    subdivision_morphism_heq_of_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (t := shared_tuple_prefix_points w (Fin.last N))
      (u := shared_tuple_prefix_labels v (Fin.last N))
      (t' := w)
      (u' := v)
      (ht := shared_tuple_prefix_points_last_eq_self w)
      (hu := shared_tuple_prefix_labels_last_eq_self v)

/-- Helper for Theorem 2.7.1: in the strict terminal-block case, the literal shared suffix starting
at the previous explicit cutpoint collapses to the single local morphism of the final explicit
interval. -/
theorem shared_tuple_cutpoint_terminal_suffix_collapse
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (t : Fin ((m + 1).succ + 1) → I)
    (hn : (m + 1).succ ≠ 0)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (m + 1).succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin ((m + 1).succ + 1), w (sigma j) = t j)
    (hk : sigma (Fin.castSucc (Fin.last (m + 1))) ≠ Fin.last N) :
    let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
    ∃ hterminal_sub :
        Set.range
            (γ.subpath
              (w kPoint)
              (w (Fin.last N))) ⊆
          O (u (Fin.last (m + 1))),
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := shared_tuple_suffix_labels
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            kPoint)
          (shared_tuple_suffix_subordinate
            γ
            w
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu))
            kPoint) ≍
        local_subpath_morphism O hO hinter S γ
          (w kPoint)
          (w (Fin.last N))
          (u (Fin.last (m + 1)))
          hterminal_sub := by
  dsimp
  let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
  have hterminal_sub :
      Set.range
          (γ.subpath
            (w kPoint)
            (w (Fin.last N))) ⊆
        O (u (Fin.last (m + 1))) := by
    -- The terminal sigma-block is a smaller subpath of the last explicit interval.
    have hleft :
        t (Fin.castSucc (Fin.last (m + 1))) ≤
          w kPoint := by
      simpa [kPoint, hsigmaeq (Fin.castSucc (Fin.last (m + 1)))] using le_rfl
    have hmid :
        w kPoint ≤ w (Fin.last N) := by
      exact
        hwmono (by
          simpa [kPoint, hsigma1] using
            hsigmamono (Fin.castSucc_le_succ (Fin.last (m + 1))))
    have hright :
        w (Fin.last N) ≤ t (Fin.last (m + 1).succ) := by
      exact le_of_eq <|
        calc
          w (Fin.last N) = w (sigma (Fin.last (m + 1).succ)) := by rw [hsigma1]
          _ = t (Fin.last (m + 1).succ) := hsigmaeq (Fin.last (m + 1).succ)
    exact
      subpath_range_subset_of_subpath_range_subset γ
        hleft
        hmid
        hright
        (hu (Fin.last (m + 1)))
  have htailLabels :
      shared_tuple_suffix_labels
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          kPoint =
        fun _ ↦ u (Fin.last (m + 1)) := by
    -- Every interval in the literal terminal suffix belongs to the last explicit cutpoint block.
    funext q
    let k : Fin N := ⟨kPoint.1 + q.1, by
      have hq : q.1 < N - kPoint.1 := q.is_lt
      omega⟩
    have hk_left :
        sigma (Fin.castSucc (Fin.last (m + 1))) ≤ k.castSucc := by
      -- Every suffix interval starts at or after the cutpoint where the terminal block begins.
      change kPoint.1 ≤ kPoint.1 + q.1
      omega
    have hk_right_last : k.succ ≤ Fin.last N := by
      -- The suffix index bounds force every suffix interval to end before the final shared point.
      change kPoint.1 + q.1 + 1 ≤ N
      have hq : q.1 < N - kPoint.1 := q.is_lt
      omega
    have hk_right :
        k.succ ≤ sigma (Fin.last (m + 1).succ) := by
      -- The last explicit cutpoint is the final shared breakpoint.
      simpa [hsigma1] using hk_right_last
    simpa [shared_tuple_suffix_labels, k, kPoint] using
      shared_tuple_cutpoint_labels_eq_of_between
        (u := u)
        (hn := hn)
        (sigma := sigma)
        (hsigma0 := hsigma0)
        (hsigma1 := hsigma1)
        (hsigmamono := hsigmamono)
        (j := Fin.last (m + 1))
        (k := k)
        hk_left
        hk_right
  have hkPoint_lt : kPoint.1 < N := by
    -- The strict-branch hypothesis says this cutpoint is genuinely before the last shared point.
    have hkPoint_ne : kPoint ≠ Fin.last N := by
      simpa [kPoint] using hk
    have hkPoint_ne_val : kPoint.1 ≠ N := by
      intro h
      apply hkPoint_ne
      ext
      simpa using h
    omega
  have hsuffixNonempty : N - kPoint.1 ≠ 0 := by
    -- A strict terminal suffix contains at least one shared interval.
    omega
  have hsuffixMono :
      Monotone (shared_tuple_suffix_points w kPoint) := by
    intro a b hab
    -- The literal suffix inherits monotonicity from the ambient shared tuple.
    exact hwmono (by
      change kPoint.1 + a.1 ≤ kPoint.1 + b.1
      exact Nat.add_le_add_left hab _)
  have hsuffixStart :
      shared_tuple_suffix_points w kPoint 0 = w kPoint := by
    -- The suffix starts at the chosen cutpoint.
    simp [shared_tuple_suffix_points, kPoint]
  have hsuffixLast :
      shared_tuple_suffix_points w kPoint (Fin.last (N - kPoint.1)) = w (Fin.last N) := by
    -- The suffix ends at the terminal shared breakpoint.
    have hlastIndex :
        (⟨kPoint.1 + (Fin.last (N - kPoint.1)).1, by
          have hq : (Fin.last (N - kPoint.1)).1 < N - kPoint.1 + 1 :=
            (Fin.last (N - kPoint.1)).is_lt
          omega⟩ : Fin (N + 1)) =
          Fin.last N := by
      ext
      simp
      omega
    simpa [shared_tuple_suffix_points] using congrArg w hlastIndex
  have hterminal_sub_suffix :
      Set.range
          (γ.subpath
            (shared_tuple_suffix_points w kPoint 0)
            (shared_tuple_suffix_points w kPoint (Fin.last (N - kPoint.1)))) ⊆
        O (u (Fin.last (m + 1))) := by
    -- The literal suffix endpoints are exactly the ambient terminal sigma-block endpoints.
    rw [hsuffixStart, hsuffixLast]
    exact hterminal_sub
  have hterminal_suffix_sub :
      ∀ q : Fin (N - kPoint.1),
        Set.range
            (γ.subpath
              (shared_tuple_suffix_points w kPoint q.castSucc)
              (shared_tuple_suffix_points w kPoint q.succ)) ⊆
          O (u (Fin.last (m + 1))) := by
    intro q
    have hleft :
        w kPoint ≤ shared_tuple_suffix_points w kPoint q.castSucc := by
      -- Every suffix interval starts to the right of the suffix source.
      exact hsuffixMono (show (0 : Fin (N - kPoint.1 + 1)) ≤ q.castSucc by
        change (0 : ℕ) ≤ q.castSucc.1
        exact Nat.zero_le _)
    have hmid :
        shared_tuple_suffix_points w kPoint q.castSucc ≤
          shared_tuple_suffix_points w kPoint q.succ := by
      -- Consecutive suffix breakpoints remain ordered.
      exact hsuffixMono (Fin.castSucc_le_succ q)
    have hright :
        shared_tuple_suffix_points w kPoint q.succ ≤ w (Fin.last N) := by
      -- Every suffix interval ends before the terminal shared breakpoint.
      rw [← hsuffixLast]
      exact hsuffixMono (Fin.le_last _)
    exact
      subpath_range_subset_of_subpath_range_subset γ
        hleft
        hmid
        hright
        hterminal_sub
  have htailRelabel :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := shared_tuple_suffix_labels
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            kPoint)
          (shared_tuple_suffix_subordinate
            γ
            w
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu))
            kPoint) ≍
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := fun _ ↦ u (Fin.last (m + 1)))
          hterminal_suffix_sub := by
    -- Rewrite the canonical cutpoint labels on the suffix to the constant last explicit label.
    exact
      subdivision_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := shared_tuple_suffix_points w kPoint)
        (u := shared_tuple_suffix_labels
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          kPoint)
        (u' := fun _ ↦ u (Fin.last (m + 1)))
        (ht := rfl)
        (hu := htailLabels)
  have htailCollapseConst :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := fun _ ↦ u (Fin.last (m + 1)))
          hterminal_suffix_sub =
        local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w kPoint 0)
          (shared_tuple_suffix_points w kPoint (Fin.last (N - kPoint.1)))
          (u (Fin.last (m + 1)))
          hterminal_sub_suffix := by
    -- A suffix whose every interval lies in one cover member collapses to one local segment.
    exact
      subdivision_morphism_eq_local_subpath_morphism_of_range_subset
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := shared_tuple_suffix_points w kPoint)
        (u := fun _ ↦ u (Fin.last (m + 1)))
        (hu := hterminal_suffix_sub)
        (hmono := hsuffixMono)
        (hn := hsuffixNonempty)
        (i := u (Fin.last (m + 1)))
        (hsub := hterminal_sub_suffix)
  have htailLocalTransport :
      local_subpath_morphism O hO hinter S γ
          (shared_tuple_suffix_points w kPoint 0)
          (shared_tuple_suffix_points w kPoint (Fin.last (N - kPoint.1)))
          (u (Fin.last (m + 1)))
          hterminal_sub_suffix ≍
        local_subpath_morphism O hO hinter S γ
          (w kPoint)
          (w (Fin.last N))
          (u (Fin.last (m + 1)))
          hterminal_sub := by
    -- Replace the literal suffix endpoints by the ambient terminal sigma-block endpoints.
    exact
      local_subpath_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (a := shared_tuple_suffix_points w kPoint 0)
        (a' := w kPoint)
        (b := shared_tuple_suffix_points w kPoint (Fin.last (N - kPoint.1)))
        (b' := w (Fin.last N))
        (i := u (Fin.last (m + 1)))
        (i' := u (Fin.last (m + 1)))
        hsuffixStart
        hsuffixLast
        rfl
        (hsub := hterminal_sub_suffix)
        (hsub' := hterminal_sub)
  refine ⟨hterminal_sub, ?_⟩
  exact htailRelabel.trans (htailCollapseConst.heq.trans htailLocalTransport)

/-- Helper for Theorem 2.7.1: once the shared tuple is relabelled by cutpoint blocks, every
interval in the literal suffix beginning at the final nonterminal cutpoint carries the last
explicit cover label. -/
theorem shared_tuple_terminal_suffix_labels_eq_last
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N m : ℕ}
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hn : (m + 1).succ ≠ 0)
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma) :
    let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
    shared_tuple_suffix_labels
        (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
        kPoint =
      fun _ ↦ u (Fin.last (m + 1)) := by
  dsimp
  funext q
  let k : Fin N := ⟨(sigma (Fin.castSucc (Fin.last (m + 1)))).1 + q.1, by
    have hq : q.1 < N - (sigma (Fin.castSucc (Fin.last (m + 1)))).1 := q.is_lt
    omega⟩
  have hk_left :
      sigma (Fin.castSucc (Fin.last (m + 1))) ≤ k.castSucc := by
    -- Every suffix interval starts at or after the cutpoint where the terminal block begins.
    change (sigma (Fin.castSucc (Fin.last (m + 1)))).1 ≤
      (sigma (Fin.castSucc (Fin.last (m + 1)))).1 + q.1
    omega
  have hk_right_last : k.succ ≤ Fin.last N := by
    -- The suffix index bounds force every suffix interval to end before the final shared point.
    change (sigma (Fin.castSucc (Fin.last (m + 1)))).1 + q.1 + 1 ≤ N
    have hq : q.1 < N - (sigma (Fin.castSucc (Fin.last (m + 1)))).1 := q.is_lt
    omega
  have hk_right :
      k.succ ≤ sigma (Fin.last (m + 1).succ) := by
    -- The last explicit cutpoint is the final shared breakpoint.
    simpa [hsigma1] using hk_right_last
  -- The canonical cutpoint block of each suffix interval is therefore the last explicit block.
  simpa [shared_tuple_suffix_labels, k] using
    shared_tuple_cutpoint_labels_eq_of_between
      (u := u)
      (hn := hn)
      (sigma := sigma)
      (hsigma0 := hsigma0)
      (hsigma1 := hsigma1)
      (hsigmamono := hsigmamono)
      (j := Fin.last (m + 1))
      (k := k)
      hk_left
      hk_right

/-- Helper for Theorem 2.7.1: if two consecutive explicit cutpoints are sent to the same shared
breakpoint, then the corresponding explicit interval is degenerate. -/
theorem explicit_interval_eq_of_sigma_eq
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigmaeq : ∀ j : Fin (n + 1), w (sigma j) = t j)
    (j : Fin n)
    (hdeg : sigma j.castSucc = sigma j.succ) :
    t j.castSucc = t j.succ := by
  -- Compare both explicit endpoints through the coincident shared breakpoint.
  calc
    t j.castSucc = w (sigma j.castSucc) := by
      symm
      exact hsigmaeq j.castSucc
    _ = w (sigma j.succ) := by rw [hdeg]
    _ = t j.succ := hsigmaeq j.succ

/-- Helper for Theorem 2.7.1: any monotone contiguous slice of a subdivision tuple whose whole
range stays inside one cover member can be repackaged as an explicit subdivision collapsing to the
single local morphism of that slice. -/
theorem exists_monotone_slice_subdivision_eq_local_subpath_morphism
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (a b : Fin (N + 1))
    (hab : a < b)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath (w a) (w b)) ⊆ O i) :
    ∃ M : ℕ,
      ∃ s : Fin (M + 1) → I,
        ∃ hM : M ≠ 0,
          ∃ hs0 : s 0 = w a,
            ∃ hs1 : s (Fin.last M) = w b,
              ∃ hsmono : Monotone s,
                ∃ v : Fin M → TopologicalSpace.IsOpenCover.Index O,
                  ∃ hv :
                    ∀ k : Fin M,
                      Set.range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ O (v k),
                    subdivision_morphism O hO hinter S γ
                        (t := s)
                        (u := v)
                        hv ≍
                      local_subpath_morphism O hO hinter S γ (w a) (w b) i hsub := by
  let M := b.1 - a.1
  let idx : Fin (M + 1) → Fin (N + 1) := fun q ↦
    ⟨a.1 + q.1, by
      have hq : q.1 < M + 1 := q.is_lt
      dsimp [M] at hq ⊢
      omega⟩
  let s : Fin (M + 1) → I := fun q ↦ w (idx q)
  let v : Fin M → TopologicalSpace.IsOpenCover.Index O := fun _ ↦ i
  have hM : M ≠ 0 := by
    -- The slice has positive length because `a < b`.
    dsimp [M]
    omega
  have hidx0 : idx 0 = a := by
    ext
    simp [idx, M]
  have hidx1 : idx (Fin.last M) = b := by
    ext
    dsimp [idx, M]
    omega
  have hs0 : s 0 = w a := by
    -- The slice starts at the left endpoint.
    simpa [s, hidx0]
  have hs1 : s (Fin.last M) = w b := by
    -- The slice ends at the right endpoint.
    simpa [s, hidx1]
  have hsmono : Monotone s := by
    -- The packaged slice inherits monotonicity from the ambient tuple.
    intro p q hpq
    exact hwmono (by
      change (a.1 + p.1 : ℕ) ≤ a.1 + q.1
      exact Nat.add_le_add_left hpq a.1)
  have hv :
      ∀ k : Fin M,
        Set.range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ O (v k) := by
    intro k
    have hleft : w a ≤ s k.castSucc := by
      -- Every slice interval starts to the right of the slice source.
      exact hwmono (by
        change (a.1 : ℕ) ≤ a.1 + k.castSucc.1
        omega)
    have hmid : s k.castSucc ≤ s k.succ := by
      -- Consecutive slice breakpoints remain ordered.
      exact hsmono (Fin.castSucc_le_succ k)
    have hright : s k.succ ≤ w b := by
      -- Every slice interval ends to the left of the slice target.
      exact hwmono (by
        change (a.1 + k.succ.1 : ℕ) ≤ b.1
        dsimp [M]
        omega)
    -- Each packaged slice interval is a smaller subpath of the full slice.
    simpa [v] using
      subpath_range_subset_of_subpath_range_subset γ hleft hmid hright hsub
  have hslice :
      Set.range (γ.subpath (s 0) (s (Fin.last M))) ⊆ O i := by
    -- The packaged slice has the same endpoints as the original ambient slice.
    simpa [hs0, hs1] using hsub
  have hcollapse :
      subdivision_morphism O hO hinter S γ
          (t := s)
          (u := v)
          hv =
        local_subpath_morphism O hO hinter S γ
          (s 0)
          (s (Fin.last M))
          i
          hslice := by
    -- Collapse the repackaged slice to one local segment morphism.
    exact
      subdivision_morphism_eq_local_subpath_morphism_of_range_subset
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := s)
        (u := v)
        (hu := hv)
        (hmono := hsmono)
        (hn := hM)
        (i := i)
        (hsub := hslice)
  have hlocal :
      local_subpath_morphism O hO hinter S γ
          (s 0)
          (s (Fin.last M))
          i
          hslice ≍
        local_subpath_morphism O hO hinter S γ
          (w a)
          (w b)
          i
          hsub := by
    -- Rewrite the packaged slice endpoints back to the original ones.
    exact
      local_subpath_morphism_heq_of_eq hO hinter S γ hs0 hs1 rfl
        (hsub := hslice)
        (hsub' := hsub)
  have hfinal :
      subdivision_morphism O hO hinter S γ
          (t := s)
          (u := v)
          hv ≍
        local_subpath_morphism O hO hinter S γ (w a) (w b) i hsub := by
    -- Compose the slice-collapse equality with the endpoint normalization.
    exact hcollapse.heq.trans hlocal
  exact ⟨M, s, hM, hs0, hs1, hsmono, v, hv, hfinal⟩

/-- Helper for Theorem 2.7.1: a nondegenerate sigma-block of the shared tuple can be repackaged
as a subordinate subdivision whose composite is the explicit local morphism attached to that block.
-/
theorem exists_cutpoint_block_subdivision_eq_local_subpath_morphism
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : n ≠ 0)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigmaeq : ∀ j : Fin (n + 1), w (sigma j) = t j)
    (hwmono : Monotone w)
    (j : Fin n)
    (hstrict : sigma j.castSucc < sigma j.succ) :
    ∃ M : ℕ,
      ∃ s : Fin (M + 1) → I,
        ∃ hM : M ≠ 0,
          ∃ hs0 : s 0 = t j.castSucc,
            ∃ hs1 : s (Fin.last M) = t j.succ,
              ∃ hsmono : Monotone s,
                ∃ v : Fin M → TopologicalSpace.IsOpenCover.Index O,
                  ∃ hv :
                    ∀ k : Fin M,
                      Set.range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ O (v k),
                    subdivision_morphism O hO hinter S γ
                        (t := s)
                        (u := v)
                        hv ≍
                      local_subpath_morphism O hO hinter S γ
                        (t j.castSucc)
                        (t j.succ)
                        (u j)
                        (hu j) := by
  have hblock_sub :
      Set.range (γ.subpath (w (sigma j.castSucc)) (w (sigma j.succ))) ⊆ O (u j) := by
    -- The whole sigma-block runs between the two explicit endpoints of interval `j`, so it stays
    -- in the same chosen cover member as that explicit interval.
    intro z hz
    rcases hz with ⟨s, rfl⟩
    exact
      (hu j) ⟨s, by
        rw [← hsigmaeq j.castSucc, ← hsigmaeq j.succ]⟩
  obtain ⟨M, s, hM, hs0w, hs1w, hsmono, v, hv, hslice⟩ :=
    exists_monotone_slice_subdivision_eq_local_subpath_morphism
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (hwmono := hwmono)
      (a := sigma j.castSucc)
      (b := sigma j.succ)
      (hab := hstrict)
      (i := u j)
      (hsub := hblock_sub)
  have hs0 : s 0 = t j.castSucc := by
    -- Rewrite the packaged slice source through the explicit left cutpoint of block `j`.
    rw [hs0w, hsigmaeq j.castSucc]
  have hs1 : s (Fin.last M) = t j.succ := by
    -- Rewrite the packaged slice target through the explicit right cutpoint of block `j`.
    rw [hs1w, hsigmaeq j.succ]
  have hlocal :
      local_subpath_morphism O hO hinter S γ
          (w (sigma j.castSucc))
          (w (sigma j.succ))
          (u j)
          hblock_sub ≍
        local_subpath_morphism O hO hinter S γ
          (t j.castSucc)
          (t j.succ)
          (u j)
          (hu j) := by
    -- The sigma-block and the explicit block have the same endpoints, so their local morphisms
    -- differ only by the endpoint transports already recorded in `hsigmaeq`.
    exact
      local_subpath_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (a := w (sigma j.castSucc))
        (a' := t j.castSucc)
        (b := w (sigma j.succ))
        (b' := t j.succ)
        (i := u j)
        (i' := u j)
        (hsigmaeq j.castSucc)
        (hsigmaeq j.succ)
        rfl
        (hsub := hblock_sub)
        (hsub' := hu j)
  exact ⟨M, s, hM, hs0, hs1, hsmono, v, hv, hslice.trans hlocal⟩

/-- Helper for Theorem 2.7.1: a literal terminal suffix of a monotone shared tuple can be
packaged as a subordinate subdivision whose composite is the single local morphism from the suffix
source to the global terminal point. -/
theorem terminal_suffix_subdivision_eq_local_subpath_morphism
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (a : Fin (N + 1))
    (ha : a ≠ Fin.last N)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath (w a) (w (Fin.last N))) ⊆ O i) :
    ∃ M : ℕ,
      ∃ s : Fin (M + 1) → I,
        ∃ hM : M ≠ 0,
          ∃ hs0 : s 0 = w a,
            ∃ hs1 : s (Fin.last M) = w (Fin.last N),
              ∃ hsmono : Monotone s,
                ∃ hsuffix :
                  ∀ q : Fin (M + 1),
                    ∃ hq : a.1 + q.1 < N + 1, s q = w ⟨a.1 + q.1, hq⟩,
                  ∃ v : Fin M → TopologicalSpace.IsOpenCover.Index O,
                    ∃ hv :
                      ∀ k : Fin M,
                        Set.range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ O (v k),
                      subdivision_morphism O hO hinter S γ
                          (t := s)
                          (u := v)
                          hv ≍
                        local_subpath_morphism O hO hinter S γ
                          (w a)
                          (w (Fin.last N))
                          i
                          hsub := by
  let M := N - a.1
  let s : Fin (M + 1) → I := fun q ↦
    w ⟨a.1 + q.1, by
      have hq : q.1 < M + 1 := q.is_lt
      dsimp [M] at hq ⊢
      omega⟩
  let v : Fin M → TopologicalSpace.IsOpenCover.Index O := fun _ ↦ i
  have ha_lt : a.1 < N := by
    have hlt : a < Fin.last N := lt_of_le_of_ne (Fin.le_last a) (by simpa using ha)
    simpa using hlt
  have hM : M ≠ 0 := by
    dsimp [M]
    omega
  have hs0 : s 0 = w a := by
    -- The packaged terminal suffix starts at the designated shared breakpoint.
    simp [s, M]
  have hs1 : s (Fin.last M) = w (Fin.last N) := by
    -- The packaged terminal suffix ends at the final shared breakpoint.
    have hval : a.1 + (Fin.last M).1 = N := by
      dsimp [M]
      omega
    have hidx :
        (⟨a.1 + (Fin.last M).1, by
          dsimp [M]
          omega⟩ : Fin (N + 1)) = Fin.last N := by
      ext
      simpa [hval]
    simpa [s] using congrArg w hidx
  have hsmono : Monotone s := by
    -- The literal suffix inherits monotonicity from the ambient shared tuple.
    intro p q hpq
    exact hwmono (by
      change a.1 + p.1 ≤ a.1 + q.1
      omega)
  have hsuffix :
      ∀ q : Fin (M + 1),
        ∃ hq : a.1 + q.1 < N + 1, s q = w ⟨a.1 + q.1, hq⟩ := by
    intro q
    refine ⟨by
      dsimp [M]
      omega, ?_⟩
    rfl
  have hsuffix_sub :
      Set.range (γ.subpath (s 0) (s (Fin.last M))) ⊆ O i := by
    -- Rewriting the packaged suffix endpoints recovers the original terminal suffix range
    -- inclusion.
    simpa [hs0, hs1] using hsub
  have hv :
      ∀ k : Fin M,
        Set.range (γ.subpath (s k.castSucc) (s k.succ)) ⊆ O (v k) := by
    intro k
    have hleft : s 0 ≤ s k.castSucc := by
      exact hsmono (by
        change (0 : ℕ) ≤ k.castSucc.1
        exact Nat.zero_le _)
    have hmid : s k.castSucc ≤ s k.succ := by
      exact hsmono (Fin.castSucc_le_succ k)
    have hright : s k.succ ≤ s (Fin.last M) := by
      exact hsmono (Fin.le_last _)
    -- Each packaged suffix interval is a smaller subpath of the full terminal suffix.
    simpa [v] using
      subpath_range_subset_of_subpath_range_subset γ hleft hmid hright hsuffix_sub
  have hcollapse :
      subdivision_morphism O hO hinter S γ
          (t := s)
          (u := v)
          hv =
        local_subpath_morphism O hO hinter S γ
          (s 0)
          (s (Fin.last M))
          i
          hsuffix_sub := by
    -- A subdivision whose entire range lies in one open set collapses to the corresponding local
    -- morphism.
    exact
      subdivision_morphism_eq_local_subpath_morphism_of_range_subset
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := s)
        (u := v)
        (hu := hv)
        (hmono := hsmono)
        (hn := hM)
        (i := i)
        (hsub := hsuffix_sub)
  have hlocal :
      local_subpath_morphism O hO hinter S γ
          (s 0)
          (s (Fin.last M))
          i
          hsuffix_sub ≍
        local_subpath_morphism O hO hinter S γ
          (w a)
          (w (Fin.last N))
          i
          hsub := by
    -- Normalize the packaged suffix endpoints back to the original terminal suffix endpoints.
    exact
      local_subpath_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (a := s 0)
        (a' := w a)
        (b := s (Fin.last M))
        (b' := w (Fin.last N))
        (i := i)
        (i' := i)
        hs0
        hs1
        rfl
        (hsub := hsuffix_sub)
        (hsub' := hsub)
  exact ⟨M, s, hM, hs0, hs1, hsmono, hsuffix, v, hv, hcollapse.heq.trans hlocal⟩

/-- Helper for Theorem 2.7.1: truncating the shared tuple at the previous explicit cutpoint
repackages the literal shared prefix as the canonical cutpoint-block subdivision of the truncated
explicit prefix. -/
theorem subdivision_morphism_prefix_transport_to_sigma_truncation
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N m : ℕ}
    (t : Fin ((m + 1).succ + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : (m + 1).succ ≠ 0)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin ((m + 1).succ + 1), w (sigma j) = t j) :
    let kPoint := sigma (Fin.castSucc (Fin.last (m + 1)))
    let tPrefix : Fin (m.succ + 1) → I := fun q ↦ t q.castSucc
    let uPrefix : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ u q.castSucc
    let v := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono
    ∃ sigmaTrunc : Fin (m.succ + 1) → Fin (kPoint.1 + 1),
      ∃ hsigma0Trunc : sigmaTrunc 0 = 0,
        ∃ hsigma1Trunc : sigmaTrunc (Fin.last m.succ) = Fin.last kPoint.1,
          ∃ hsigmamonoTrunc : Monotone sigmaTrunc,
            ∃ hsigmaeqTrunc :
                ∀ j : Fin (m.succ + 1),
                  shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j,
              shared_tuple_prefix_labels v kPoint =
                shared_tuple_cutpoint_labels
                  uPrefix
                  (by simp)
                  sigmaTrunc
                  hsigma0Trunc
                  hsigma1Trunc
                  hsigmamonoTrunc := by
  let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
  let tPrefix : Fin (m.succ + 1) → I := fun q ↦ t q.castSucc
  let uPrefix : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ u q.castSucc
  let v : Fin N → TopologicalSpace.IsOpenCover.Index O :=
    shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono
  let sigmaTrunc : Fin (m.succ + 1) → Fin (kPoint.1 + 1) := fun q ↦
    ⟨(sigma q.castSucc).1, by
      have hq_le :
          sigma q.castSucc ≤ kPoint := by
        -- Every truncated explicit breakpoint still lies inside the literal shared prefix.
        exact hsigmamono (by
          change q.1 ≤ (Fin.castSucc (Fin.last (m + 1))).1
          simpa using Nat.le_of_lt_succ q.is_lt)
      change (sigma q.castSucc).1 < kPoint.1 + 1
      exact Nat.lt_succ_of_le (by
        change (sigma q.castSucc).1 ≤ kPoint.1
        simpa [kPoint] using hq_le)⟩
  have hsigma0Trunc : sigmaTrunc 0 = 0 := by
    -- The truncated breakpoint comparison still starts at the initial shared breakpoint.
    ext
    simp [sigmaTrunc, hsigma0]
  have hsigma1Trunc : sigmaTrunc (Fin.last m.succ) = Fin.last kPoint.1 := by
    -- The final truncated explicit breakpoint lands exactly on the truncation point.
    ext
    simp [sigmaTrunc, kPoint]
  have hsigmamonoTrunc : Monotone sigmaTrunc := by
    intro a b hab
    change (sigma a.castSucc).1 ≤ (sigma b.castSucc).1
    have hab' : a.castSucc ≤ b.castSucc := by
      change a.1 ≤ b.1
      exact hab
    simpa using hsigmamono hab'
  have hsigmaeqTrunc :
      ∀ j : Fin (m.succ + 1),
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j := by
    intro j
    -- Reindexing the literal shared prefix does not change the compared breakpoint values.
    simpa [shared_tuple_prefix_points, sigmaTrunc, tPrefix, kPoint] using hsigmaeq j.castSucc
  have hlabels :
      shared_tuple_prefix_labels v kPoint =
        shared_tuple_cutpoint_labels
          uPrefix
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc := by
    funext q
    let qOrig : Fin N := ⟨q.1, by
      exact Nat.lt_of_lt_of_le q.is_lt (Nat.lt_succ_iff.mp kPoint.is_lt)⟩
    let j :=
      shared_tuple_cutpoint_block
        (by simp)
        sigmaTrunc
        hsigma0Trunc
        hsigma1Trunc
        hsigmamonoTrunc
        q
    have hj :
        sigmaTrunc j.castSucc ≤ q.castSucc ∧
          q.succ ≤ sigmaTrunc j.succ := by
      -- The truncated canonical cutpoint block records the same consecutive prefix bounds.
      simpa [j] using
        shared_tuple_cutpoint_block_spec
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc
          q
    have horig :
        shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono qOrig = j.castSucc := by
      -- Those same bounds identify the original cutpoint block as the cast-successor of the
      -- truncated one.
      apply
        shared_tuple_cutpoint_block_eq_of_between
          (hn := hn)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
      · simpa [sigmaTrunc, qOrig, j] using hj.1
      · simpa [sigmaTrunc, qOrig, j] using hj.2
    -- After translating the prefix interval index back to the ambient shared tuple, both
    -- canonical label assignments are literally the same.
    simp [shared_tuple_prefix_labels, shared_tuple_cutpoint_labels, v, uPrefix, qOrig, j, horig]
  exact ⟨sigmaTrunc, hsigma0Trunc, hsigma1Trunc, hsigmamonoTrunc, hsigmaeqTrunc, hlabels⟩

/-- Helper for Theorem 2.7.1: every literal shared prefix of a monotone shared tuple is still
monotone. -/
theorem shared_tuple_prefix_points_monotone
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (k : Fin (N + 1)) :
    Monotone (shared_tuple_prefix_points w k) := by
  -- Restricting a monotone breakpoint tuple to an initial segment preserves monotonicity.
  intro a b hab
  simpa [shared_tuple_prefix_points] using hwmono hab

/-- Helper for Theorem 2.7.1: after transporting the explicit prefix data to `sigmaTrunc`, the
canonical cutpoint-block labels on the literal shared prefix ambient tuple are subordinate. -/
theorem shared_tuple_prefix_transport_cutpoint_block_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (t : Fin ((m + 1).succ + 1) → I)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (m + 1).succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (kPoint : Fin (N + 1))
    (sigmaTrunc : Fin (m.succ + 1) → Fin (kPoint.1 + 1))
    (hsigma0Trunc : sigmaTrunc 0 = 0)
    (hsigma1Trunc : sigmaTrunc (Fin.last m.succ) = Fin.last kPoint.1)
    (hsigmamonoTrunc : Monotone sigmaTrunc)
    (hsigmaeqTrunc :
      ∀ j : Fin (m.succ + 1),
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = (fun q ↦ t q.castSucc) j) :
    ∀ q : Fin kPoint.1,
      Set.range
          (γ.subpath
            (shared_tuple_prefix_points w kPoint q.castSucc)
            (shared_tuple_prefix_points w kPoint q.succ)) ⊆
        O (shared_tuple_cutpoint_labels
          (fun r : Fin m.succ ↦ u r.castSucc)
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc
          q) := by
  -- This is exactly the canonical cutpoint-block subordinacy theorem applied to the literal shared
  -- prefix ambient tuple and the transported explicit prefix breakpoints.
  exact
    shared_tuple_cutpoint_block_subordinate
      (γ := γ)
      (t := fun q : Fin (m.succ + 1) ↦ t q.castSucc)
      (w := shared_tuple_prefix_points w kPoint)
      (hn := by simp)
      (sigma := sigmaTrunc)
      (hsigma0 := hsigma0Trunc)
      (hsigma1 := hsigma1Trunc)
      (hsigmamono := hsigmamonoTrunc)
      (hsigmaeq := hsigmaeqTrunc)
      (hwmono := shared_tuple_prefix_points_monotone w hwmono kPoint)
      (u := fun r : Fin m.succ ↦ u r.castSucc)
      (hu := fun r : Fin m.succ ↦ hu r.castSucc)

/-- Helper for Theorem 2.7.1: the literal shared prefix ambient tuple equipped with its
transported canonical cutpoint labels should collapse to the transported explicit prefix
subdivision. -/
theorem shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core_base
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (kPoint : Fin (N + 1))
    (tPrefix : Fin 2 → I)
    (uPrefix : Fin 1 → TopologicalSpace.IsOpenCover.Index O)
    (huPrefix :
      ∀ q : Fin 1, Set.range (γ.subpath (tPrefix q.castSucc) (tPrefix q.succ)) ⊆ O (uPrefix q))
    (sigmaTrunc : Fin 2 → Fin (kPoint.1 + 1))
    (hsigma0Trunc : sigmaTrunc 0 = 0)
    (hsigma1Trunc : sigmaTrunc (Fin.last 1) = Fin.last kPoint.1)
    (hsigmamonoTrunc : Monotone sigmaTrunc)
    (hsigmaeqTrunc :
      ∀ j : Fin 2,
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j)
    (hcanonical_sub :
      ∀ q : Fin kPoint.1,
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w kPoint q.castSucc)
              (shared_tuple_prefix_points w kPoint q.succ)) ⊆
          O (shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc
            q)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w kPoint)
        (u := shared_tuple_cutpoint_labels
          uPrefix
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc)
        hcanonical_sub ≍
      subdivision_morphism O hO hinter S γ
        (t := tPrefix)
        (u := uPrefix)
        huPrefix := by
  have hstart :
      shared_tuple_prefix_points w kPoint 0 =
        tPrefix (Fin.castSucc (Fin.last 0)) := by
    -- The transported explicit prefix still starts at the initial shared breakpoint.
    simpa [hsigma0Trunc] using hsigmaeqTrunc 0
  have hend_raw :
      shared_tuple_prefix_points w kPoint (sigmaTrunc (Fin.last 1)) =
        tPrefix (Fin.last 0).succ := by
    -- The transported explicit terminal breakpoint is recorded by the last value of
    -- `sigmaTrunc`.
    simpa using hsigmaeqTrunc (Fin.last 1)
  by_cases hkPoint : kPoint.1 = 0
  · have hlast0 : (Fin.last kPoint.1 : Fin (kPoint.1 + 1)) = 0 := by
      simpa [hkPoint] using (show (Fin.last 0 : Fin (0 + 1)) = 0 by rfl)
    have hkPoint_eq : kPoint = 0 := by
      ext
      simpa using hkPoint
    have hend0 :
        shared_tuple_prefix_points w kPoint 0 =
          tPrefix (Fin.last 0).succ := by
      -- In the degenerate prefix case, the transported terminal breakpoint is the initial one.
      calc
        shared_tuple_prefix_points w kPoint 0 =
            shared_tuple_prefix_points w kPoint (Fin.last kPoint.1) := by rw [hlast0]
        _ = tPrefix (Fin.last 0).succ := by
          rw [← hsigma1Trunc]
          exact hend_raw
    have hsigma_same :
        sigmaTrunc (Fin.castSucc (Fin.last 0)) = sigmaTrunc (Fin.last 0).succ := by
      calc
        sigmaTrunc (Fin.castSucc (Fin.last 0)) = 0 := hsigma0Trunc
        _ = Fin.last kPoint.1 := by simpa [hlast0]
        _ = sigmaTrunc (Fin.last 0).succ := hsigma1Trunc.symm
    have hdeg :
        tPrefix (Fin.castSucc (Fin.last 0)) = tPrefix (Fin.last 0).succ := by
      -- If the two transported cutpoints coincide, the unique explicit interval is degenerate.
      exact
        explicit_interval_eq_of_sigma_eq
          tPrefix
          (shared_tuple_prefix_points w kPoint)
          sigmaTrunc
          hsigmaeqTrunc
          (Fin.last 0)
          hsigma_same
    have hmem :
        γ (shared_tuple_prefix_points w kPoint 0) ∈ O (uPrefix (Fin.last 0)) := by
      -- The degenerate explicit interval still lies in its chosen cover member.
      rw [hstart]
      exact
        subpath_source_mem_of_range_subset γ
          (tPrefix (Fin.castSucc (Fin.last 0)))
          (tPrefix (Fin.last 0).succ)
          (huPrefix (Fin.last 0))
    have hsub :
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w kPoint 0)
              (shared_tuple_prefix_points w kPoint 0)) ⊆
          O (uPrefix (Fin.last 0)) := by
      -- Once the shared prefix has no intervals, its unique point is still in the explicit cover
      -- member.
      intro z hz
      rcases hz with ⟨s, rfl⟩
      simpa [Path.subpath_self] using hmem
    have hw :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaTrunc
              hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc)
            hcanonical_sub ≍
          𝟙 (chosen_cover_object O hO S
            (γ (shared_tuple_prefix_points w kPoint 0))) := by
      -- A literal shared prefix with no intervals contributes the identity.
      cases hkPoint_eq
      rfl
    have ht :
        subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            huPrefix =
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last 0)))
            (tPrefix (Fin.last 0).succ)
            (uPrefix (Fin.last 0))
            (huPrefix (Fin.last 0)) := by
      -- A one-interval explicit subdivision is already its unique local segment.
      simp [subdivision_morphism]
    have hlocal :
        local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last 0)))
            (tPrefix (Fin.last 0).succ)
            (uPrefix (Fin.last 0))
            (huPrefix (Fin.last 0)) ≍
          local_subpath_morphism O hO hinter S γ
            (shared_tuple_prefix_points w kPoint 0)
            (shared_tuple_prefix_points w kPoint 0)
            (uPrefix (Fin.last 0))
            hsub := by
      -- Both endpoint pairs collapse to the same degenerate shared-prefix point.
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := tPrefix (Fin.castSucc (Fin.last 0)))
          (a' := shared_tuple_prefix_points w kPoint 0)
          (b := tPrefix (Fin.last 0).succ)
          (b' := shared_tuple_prefix_points w kPoint 0)
          (i := uPrefix (Fin.last 0))
          (i' := uPrefix (Fin.last 0))
          hstart.symm
          (hdeg.symm.trans hstart.symm)
          rfl
          (hsub := huPrefix (Fin.last 0))
          (hsub' := hsub)
    have hlocal_id :
        local_subpath_morphism O hO hinter S γ
            (shared_tuple_prefix_points w kPoint 0)
            (shared_tuple_prefix_points w kPoint 0)
            (uPrefix (Fin.last 0))
            hsub =
          𝟙 (chosen_cover_object O hO S
            (γ (shared_tuple_prefix_points w kPoint 0))) := by
      -- A local segment with identical endpoints is the identity.
      exact
        local_subpath_morphism_eq_id_of_eq_endpoints
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := shared_tuple_prefix_points w kPoint 0)
          (i := uPrefix (Fin.last 0))
          (hsub := hsub)
    exact hw.trans (hlocal_id.heq.symm.trans (hlocal.symm.trans ht.heq.symm))
  · have hsub :
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w kPoint 0)
              (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))) ⊆
          O (uPrefix (Fin.last 0)) := by
      -- The whole literal shared prefix has the same endpoints as the unique explicit interval.
      intro z hz
      rcases hz with ⟨s, rfl⟩
      exact
        (huPrefix (Fin.last 0)) ⟨s, by
          change
            γ.subpath
                (tPrefix (Fin.castSucc (Fin.last 0)))
                (tPrefix (Fin.last 0).succ) s =
              γ.subpath
                (shared_tuple_prefix_points w kPoint 0)
                (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1)) s
          have hend :
              shared_tuple_prefix_points w kPoint (Fin.last kPoint.1) =
                tPrefix (Fin.last 0).succ := by
            rw [← hsigma1Trunc]
            exact hend_raw
          rw [← hstart, ← hend]⟩
    have hwcollapse :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaTrunc
              hsigma0Trunc
              hsigma1Trunc
              hsigmamonoTrunc)
            hcanonical_sub =
          local_subpath_morphism O hO hinter S γ
            (shared_tuple_prefix_points w kPoint 0)
            (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))
            (uPrefix (Fin.last 0))
            hsub := by
      -- When the explicit prefix has one interval, the whole shared prefix stays in that same
      -- cover member and collapses to one local segment.
      exact
        subdivision_morphism_eq_local_subpath_morphism_of_range_subset
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (t := shared_tuple_prefix_points w kPoint)
          (u := shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc)
          (hu := hcanonical_sub)
          (hmono := shared_tuple_prefix_points_monotone w hwmono kPoint)
          (hn := hkPoint)
          (i := uPrefix (Fin.last 0))
          (hsub := hsub)
    have hlocal :
        local_subpath_morphism O hO hinter S γ
            (shared_tuple_prefix_points w kPoint 0)
            (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))
            (uPrefix (Fin.last 0))
            hsub ≍
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last 0)))
            (tPrefix (Fin.last 0).succ)
            (uPrefix (Fin.last 0))
            (huPrefix (Fin.last 0)) := by
      -- The shared prefix and the explicit interval have the same global endpoints.
      have hend :
          shared_tuple_prefix_points w kPoint (Fin.last kPoint.1) =
            tPrefix (Fin.last 0).succ := by
        rw [← hsigma1Trunc]
        exact hend_raw
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := shared_tuple_prefix_points w kPoint 0)
          (a' := tPrefix (Fin.castSucc (Fin.last 0)))
          (b := shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))
          (b' := tPrefix (Fin.last 0).succ)
          (i := uPrefix (Fin.last 0))
          (i' := uPrefix (Fin.last 0))
          hstart
          hend
          rfl
          (hsub := hsub)
          (hsub' := huPrefix (Fin.last 0))
    have ht :
        subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            huPrefix =
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last 0)))
            (tPrefix (Fin.last 0).succ)
            (uPrefix (Fin.last 0))
            (huPrefix (Fin.last 0)) := by
      -- A one-interval explicit subdivision is already its unique local segment.
      simp [subdivision_morphism]
    exact hwcollapse.heq.trans (hlocal.trans ht.heq.symm)

/-- Helper for Theorem 2.7.1: transporting the explicit prefix data on the literal shared prefix
ending at `kPoint` one step further to the previous explicit cutpoint packages the exact recursive
comparison data needed in the successor step. -/
theorem shared_tuple_prefix_transport_to_previous_cutpoint
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (kPoint : Fin (N + 1))
    (tPrefix : Fin ((m + 1).succ + 1) → I)
    (uPrefix : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (sigmaTrunc : Fin ((m + 1).succ + 1) → Fin (kPoint.1 + 1))
    (hsigma0Trunc : sigmaTrunc 0 = 0)
    (hsigma1Trunc : sigmaTrunc (Fin.last (m + 1).succ) = Fin.last kPoint.1)
    (hsigmamonoTrunc : Monotone sigmaTrunc)
    (hsigmaeqTrunc :
      ∀ j : Fin ((m + 1).succ + 1),
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j) :
    let kPrev : Fin (kPoint.1 + 1) := sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))
    let tTrunc : Fin (m.succ + 1) → I := fun q ↦ tPrefix q.castSucc
    let uTrunc : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ uPrefix q.castSucc
    let v :=
      shared_tuple_cutpoint_labels
        uPrefix
        (by simp)
        sigmaTrunc
        hsigma0Trunc
        hsigma1Trunc
        hsigmamonoTrunc
    ∃ sigmaPrev : Fin (m.succ + 1) → Fin (kPrev.1 + 1),
      ∃ hsigma0Prev : sigmaPrev 0 = 0,
        ∃ hsigma1Prev : sigmaPrev (Fin.last m.succ) = Fin.last kPrev.1,
          ∃ hsigmamonoPrev : Monotone sigmaPrev,
            ∃ hsigmaeqPrev :
                ∀ j : Fin (m.succ + 1),
                  shared_tuple_prefix_points
                      (shared_tuple_prefix_points w kPoint)
                      kPrev
                      (sigmaPrev j) =
                    tTrunc j,
              shared_tuple_prefix_labels v kPrev =
                shared_tuple_cutpoint_labels
                  uTrunc
                  (by simp)
                  sigmaPrev
                  hsigma0Prev
                  hsigma1Prev
                  hsigmamonoPrev := by
  -- Reapply the prefix-transport theorem inside the literal shared prefix ending at `kPoint`.
  dsimp
  simpa using
    subdivision_morphism_prefix_transport_to_sigma_truncation
      (t := tPrefix)
      (w := shared_tuple_prefix_points w kPoint)
      (hn := by simp)
      (u := uPrefix)
      (sigma := sigmaTrunc)
      (hsigma0 := hsigma0Trunc)
      (hsigma1 := hsigma1Trunc)
      (hsigmamono := hsigmamonoTrunc)
      (hsigmaeq := hsigmaeqTrunc)

/-- Helper for Theorem 2.7.1: the literal shared prefix ambient tuple equipped with its
transported canonical cutpoint labels should collapse to the transported explicit prefix
subdivision. -/
theorem shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core_succ_step
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (kPoint : Fin (N + 1))
    (tPrefix : Fin ((m + 1).succ + 1) → I)
    (uPrefix : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (huPrefix :
      ∀ q : Fin (m + 1).succ,
        Set.range (γ.subpath (tPrefix q.castSucc) (tPrefix q.succ)) ⊆ O (uPrefix q))
    (sigmaTrunc : Fin ((m + 1).succ + 1) → Fin (kPoint.1 + 1))
    (hsigma0Trunc : sigmaTrunc 0 = 0)
    (hsigma1Trunc : sigmaTrunc (Fin.last (m + 1).succ) = Fin.last kPoint.1)
    (hsigmamonoTrunc : Monotone sigmaTrunc)
    (hsigmaeqTrunc :
      ∀ j : Fin ((m + 1).succ + 1),
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j)
    (hcanonical_sub :
      ∀ q : Fin kPoint.1,
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w kPoint q.castSucc)
              (shared_tuple_prefix_points w kPoint q.succ)) ⊆
          O (shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc
            q))
    (sigmaPrev :
      Fin (m.succ + 1) →
        Fin ((sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))).1 + 1))
    (hsigma0Prev : sigmaPrev 0 = 0)
    (hsigma1Prev :
      sigmaPrev (Fin.last m.succ) =
        Fin.last (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))).1)
    (hsigmamonoPrev : Monotone sigmaPrev)
    (hsigmaeqPrev :
      ∀ j : Fin (m.succ + 1),
        shared_tuple_prefix_points
            (shared_tuple_prefix_points w kPoint)
            (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))
            (sigmaPrev j) =
          (fun q ↦ tPrefix q.castSucc) j)
    (hlabelsPrev :
      shared_tuple_prefix_labels
          (shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc)
          (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))) =
        shared_tuple_cutpoint_labels
          (fun q : Fin m.succ ↦ uPrefix q.castSucc)
          (by simp)
          sigmaPrev
          hsigma0Prev
          hsigma1Prev
          hsigmamonoPrev)
    (hcanonical_sub_prev :
      ∀ q : Fin (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))).1,
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))
                q.castSucc)
              (shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))
                q.succ)) ⊆
          O (shared_tuple_cutpoint_labels
            (fun q : Fin m.succ ↦ uPrefix q.castSucc)
            (by simp)
            sigmaPrev
            hsigma0Prev
            hsigma1Prev
            hsigmamonoPrev
            q))
    (hprevCollapse :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points
            (shared_tuple_prefix_points w kPoint)
            (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
          (u := shared_tuple_cutpoint_labels
            (fun q : Fin m.succ ↦ uPrefix q.castSucc)
            (by simp)
            sigmaPrev
            hsigma0Prev
            hsigma1Prev
            hsigmamonoPrev)
          hcanonical_sub_prev ≍
        subdivision_morphism O hO hinter S γ
          (t := fun q ↦ tPrefix q.castSucc)
          (u := fun q ↦ uPrefix q.castSucc)
          (fun q : Fin m.succ ↦ huPrefix q.castSucc)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w kPoint)
        (u := shared_tuple_cutpoint_labels
          uPrefix
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc)
        hcanonical_sub ≍
      subdivision_morphism O hO hinter S γ
        (t := tPrefix)
        (u := uPrefix)
        huPrefix := by
  -- Route correction: the ambient prefix step should consume the already-proved predecessor
  -- collapse instead of trying to reconstruct it from transport data a second time.
  let kPrev : Fin (kPoint.1 + 1) := sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))
  let tTrunc : Fin (m.succ + 1) → I := fun q ↦ tPrefix q.castSucc
  let uTrunc : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ uPrefix q.castSucc
  by_cases hk : kPrev = Fin.last kPoint.1
  · dsimp [kPrev] at hk
    have hnlen : kPoint.1 = (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))).1 := by
      -- The predecessor cutpoint has the same index as the ambient terminal point.
      simpa using congrArg Fin.val hk.symm
    have hpointsCast :
        shared_tuple_prefix_points w kPoint =
          fun q ↦
            shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))
              (Fin.cast (congrArg Nat.succ hnlen) q) := by
      -- After transporting the terminal-prefix length, both breakpoint tuples are literally the
      -- same.
      funext q
      simpa [shared_tuple_prefix_points, hk, hnlen]
    have hlabelsCast :
        shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc =
          fun q ↦
            shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))
              (Fin.cast hnlen q) := by
      -- The terminal literal prefix labels are just the ambient labels read through the length
      -- transport.
      funext q
      simpa [shared_tuple_prefix_labels, hk, hnlen]
    have hshared :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaTrunc
              hsigma0Trunc
              hsigma1Trunc
              hsigmamonoTrunc)
            hcanonical_sub ≍
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (shared_tuple_prefix_subordinate
              γ
              (shared_tuple_prefix_points w kPoint)
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              hcanonical_sub
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))) := by
      -- The ambient prefix differs from the terminal predecessor model only by the length
      -- transport encoded by `hnlen`.
      exact
        subdivision_morphism_heq_of_cast_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          hnlen
          (ht := hpointsCast)
          (hu := hlabelsCast)
    have hprefixLabelsHeq :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (shared_tuple_prefix_subordinate
              γ
              (shared_tuple_prefix_points w kPoint)
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              hcanonical_sub
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1))))) ≍
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (u := shared_tuple_cutpoint_labels
              uTrunc
              (by simp)
              sigmaPrev
              hsigma0Prev
              hsigma1Prev
              hsigmamonoPrev)
            hcanonical_sub_prev := by
      -- The transported predecessor data differ only by the relabeling recorded in
      -- `hlabelsPrev`.
      exact
        subdivision_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (ht := rfl)
          (hu := hlabelsPrev)
    have hsigma_same :
        sigmaTrunc (Fin.castSucc (Fin.last (m + 1))) =
          sigmaTrunc ((Fin.last (m + 1)).succ) := by
      -- In the degenerate branch, the last explicit interval has identical sigma endpoints.
      calc
        sigmaTrunc (Fin.castSucc (Fin.last (m + 1))) = Fin.last kPoint.1 := hk
        _ = sigmaTrunc ((Fin.last (m + 1)).succ) := hsigma1Trunc.symm
    have hdeg :
        tPrefix (Fin.castSucc (Fin.last (m + 1))) =
          tPrefix ((Fin.last (m + 1)).succ) := by
      -- So the deleted final explicit interval contributes only an identity morphism.
      exact
        explicit_interval_eq_of_sigma_eq
          tPrefix
          (shared_tuple_prefix_points w kPoint)
          sigmaTrunc
          hsigmaeqTrunc
          (Fin.last (m + 1))
          hsigma_same
    have hconst_sub :
        Set.range
            (γ.subpath
              (tPrefix (Fin.castSucc (Fin.last (m + 1))))
              (tPrefix (Fin.castSucc (Fin.last (m + 1))))) ⊆
          O (uPrefix (Fin.last (m + 1))) := by
      -- Rewriting the constant last interval by `hdeg` recovers the original explicit cover
      -- containment.
      intro z hz
      have hz' :
          z ∈ Set.range
            (γ.subpath
              (tPrefix (Fin.castSucc (Fin.last (m + 1))))
              (tPrefix ((Fin.last (m + 1)).succ))) := by
        rcases hz with ⟨s, rfl⟩
        refine ⟨s, ?_⟩
        change γ.subpath _ _ s = γ.subpath _ _ s
        rw [hdeg]
      exact huPrefix (Fin.last (m + 1)) hz'
    have hlast_heq :
        local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (tPrefix ((Fin.last (m + 1)).succ))
            (uPrefix (Fin.last (m + 1)))
            (huPrefix (Fin.last (m + 1))) ≍
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (uPrefix (Fin.last (m + 1)))
            hconst_sub := by
      -- Replace the final target by the equal source so the last explicit factor becomes
      -- constant.
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := tPrefix (Fin.castSucc (Fin.last (m + 1))))
          (a' := tPrefix (Fin.castSucc (Fin.last (m + 1))))
          (b := tPrefix ((Fin.last (m + 1)).succ))
          (b' := tPrefix (Fin.castSucc (Fin.last (m + 1))))
          (i := uPrefix (Fin.last (m + 1)))
          (i' := uPrefix (Fin.last (m + 1)))
          rfl
          hdeg.symm
          rfl
          (hsub := huPrefix (Fin.last (m + 1)))
          (hsub' := hconst_sub)
    have hlast_id :
        local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (uPrefix (Fin.last (m + 1)))
            hconst_sub =
          𝟙 (chosen_cover_object O hO S
            (γ (tPrefix (Fin.castSucc (Fin.last (m + 1)))))) := by
      -- A local segment with identical endpoints is the identity.
      exact
        local_subpath_morphism_eq_id_of_eq_endpoints
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := tPrefix (Fin.castSucc (Fin.last (m + 1))))
          (i := uPrefix (Fin.last (m + 1)))
          (hsub := hconst_sub)
    have hobj_last :
        chosen_cover_object O hO S
            (γ (tPrefix (Fin.castSucc (Fin.last (m + 1))))) =
          chosen_cover_object O hO S
            (γ (tPrefix ((Fin.last (m + 1)).succ))) := by
      -- The chosen endpoint objects agree because the deleted terminal interval is degenerate.
      exact congrArg (chosen_cover_object O hO S) (congrArg γ hdeg)
    have htail_heq :
        local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (tPrefix ((Fin.last (m + 1)).succ))
            (uPrefix (Fin.last (m + 1)))
            (huPrefix (Fin.last (m + 1))) ≍
          𝟙 (chosen_cover_object O hO S
            (γ (tPrefix (Fin.castSucc (Fin.last (m + 1)))))) := by
      -- Keep the deleted last interval as a heterogeneous identity for the final `comp_id`
      -- normalization.
      exact hlast_heq.trans hlast_id.heq
    have hcomp_heq :
        subdivision_morphism O hO hinter S γ
            (t := tTrunc)
            (u := uTrunc)
            (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.castSucc (Fin.last (m + 1))))
            (tPrefix ((Fin.last (m + 1)).succ))
            (uPrefix (Fin.last (m + 1)))
            (huPrefix (Fin.last (m + 1))) ≍
          subdivision_morphism O hO hinter S γ
            (t := tTrunc)
            (u := uTrunc)
            (fun q : Fin m.succ ↦ huPrefix q.castSucc) := by
      have hcomp_to_id :
          subdivision_morphism O hO hinter S γ
              (t := tTrunc)
              (u := uTrunc)
              (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (tPrefix (Fin.castSucc (Fin.last (m + 1))))
              (tPrefix ((Fin.last (m + 1)).succ))
              (uPrefix (Fin.last (m + 1)))
              (huPrefix (Fin.last (m + 1))) ≍
          subdivision_morphism O hO hinter S γ
              (t := tTrunc)
              (u := uTrunc)
              (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
            𝟙 (chosen_cover_object O hO S
              (γ (tPrefix (Fin.castSucc (Fin.last (m + 1)))))) := by
        -- Compose the predecessor collapse with the heterogeneous identity description of the
        -- deleted last interval.
        exact CategoryTheory.heq_comp rfl rfl hobj_last.symm HEq.rfl htail_heq
      -- Removing the final identity factor leaves the predecessor composite unchanged.
      exact hcomp_to_id.trans
        (CategoryTheory.Category.comp_id
          (subdivision_morphism O hO hinter S γ
            (t := tTrunc)
            (u := uTrunc)
            (fun q : Fin m.succ ↦ huPrefix q.castSucc))).heq
    have hfull_explicit :
        subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            huPrefix ≍
          subdivision_morphism O hO hinter S γ
            (t := tTrunc)
            (u := uTrunc)
            (fun q : Fin m.succ ↦ huPrefix q.castSucc) := by
      -- One unfold of the explicit prefix subdivision isolates the final degenerate interval.
      exact
        (rfl :
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              huPrefix =
            subdivision_morphism O hO hinter S γ
                (t := tTrunc)
                (u := uTrunc)
                (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
              local_subpath_morphism O hO hinter S γ
                (tPrefix (Fin.castSucc (Fin.last (m + 1))))
                (tPrefix ((Fin.last (m + 1)).succ))
                (uPrefix (Fin.last (m + 1)))
                (huPrefix (Fin.last (m + 1)))).heq.trans hcomp_heq
    have hprevCollapse' :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              (sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))))
            (u := shared_tuple_cutpoint_labels
              uTrunc
              (by simp)
              sigmaPrev
              hsigma0Prev
              hsigma1Prev
              hsigmamonoPrev)
            hcanonical_sub_prev ≍
          subdivision_morphism O hO hinter S γ
            (t := tTrunc)
            (u := uTrunc)
            (fun q : Fin m.succ ↦ huPrefix q.castSucc) := by
      -- Rewrite the predecessor collapse to the literal terminal-prefix model.
      exact hprevCollapse
    exact hshared.trans (hprefixLabelsHeq.trans (hprevCollapse'.trans hfull_explicit.symm))
  · have hreassembly :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaTrunc
              hsigma0Trunc
              hsigma1Trunc
              hsigmamonoTrunc)
            hcanonical_sub ≍
          subdivision_morphism O hO hinter S γ
              (t := shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev)
              (u := shared_tuple_prefix_labels
                (shared_tuple_cutpoint_labels
                  uPrefix
                  (by simp)
                  sigmaTrunc
                  hsigma0Trunc
                  hsigma1Trunc
                  hsigmamonoTrunc)
                kPrev)
              (shared_tuple_prefix_subordinate
                γ
                (shared_tuple_prefix_points w kPoint)
                (shared_tuple_cutpoint_labels
                  uPrefix
                  (by simp)
                  sigmaTrunc
                  hsigma0Trunc
                  hsigma1Trunc
                  hsigmamonoTrunc)
                hcanonical_sub
                kPrev) ≫
            subdivision_morphism O hO hinter S γ
              (t := shared_tuple_suffix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev)
              (u := shared_tuple_suffix_labels
                (shared_tuple_cutpoint_labels
                  uPrefix
                  (by simp)
                  sigmaTrunc
                  hsigma0Trunc
                  hsigma1Trunc
                  hsigmamonoTrunc)
                kPrev)
              (shared_tuple_suffix_subordinate
                γ
                (shared_tuple_prefix_points w kPoint)
                (shared_tuple_cutpoint_labels
                  uPrefix
                  (by simp)
                  sigmaTrunc
                  hsigma0Trunc
                  hsigma1Trunc
                  hsigmamonoTrunc)
                hcanonical_sub
                kPrev) := by
      -- The ambient prefix factors at the previous explicit cutpoint into predecessor prefix and
      -- terminal shared suffix.
      exact
        subdivision_morphism_literal_nonterminal_cutpoint_reassembly_heq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := shared_tuple_prefix_points w kPoint)
          (v := shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc)
          (hv := hcanonical_sub)
          (kPoint := kPrev)
          hk
    have hprefixLabelsHeq :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              kPrev)
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              kPrev)
            (shared_tuple_prefix_subordinate
              γ
              (shared_tuple_prefix_points w kPoint)
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              hcanonical_sub
              kPrev) ≍
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              kPrev)
            (u := shared_tuple_cutpoint_labels
              uTrunc
              (by simp)
              sigmaPrev
              hsigma0Prev
              hsigma1Prev
              hsigmamonoPrev)
            hcanonical_sub_prev := by
      -- The transported predecessor tuple differs from the literal predecessor prefix only by the
      -- relabeling encoded in `hlabelsPrev`.
      exact
        subdivision_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (ht := rfl)
          (hu := hlabelsPrev)
    obtain ⟨hterminal_sub, htailCollapse⟩ :=
      shared_tuple_cutpoint_terminal_suffix_collapse
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := shared_tuple_prefix_points w kPoint)
        (hwmono := shared_tuple_prefix_points_monotone w hwmono kPoint)
        (t := tPrefix)
        (hn := by simp)
        (u := uPrefix)
        (hu := huPrefix)
        (sigma := sigmaTrunc)
        (hsigma0 := hsigma0Trunc)
        (hsigma1 := hsigma1Trunc)
        (hsigmamono := hsigmamonoTrunc)
        (hsigmaeq := hsigmaeqTrunc)
        hk
    have hkPrev_eq :
        shared_tuple_prefix_points w kPoint kPrev =
          tTrunc (Fin.last m.succ) := by
      -- The previous explicit cutpoint is the endpoint of the truncated explicit prefix.
      simpa [kPrev, tTrunc] using hsigmaeqTrunc (Fin.castSucc (Fin.last (m + 1)))
    have hlast_eq :
        shared_tuple_prefix_points w kPoint (Fin.last kPoint.1) =
          tPrefix (Fin.last (m + 1).succ) := by
      -- The ambient prefix endpoint is the final explicit breakpoint.
      rw [← hsigma1Trunc]
      simpa using hsigmaeqTrunc (Fin.last (m + 1).succ)
    have htailTransport :
        local_subpath_morphism O hO hinter S γ
            (shared_tuple_prefix_points w kPoint kPrev)
            (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))
            (uPrefix (Fin.last (m + 1)))
            hterminal_sub ≍
          local_subpath_morphism O hO hinter S γ
            (tTrunc (Fin.last m.succ))
            (tPrefix (Fin.last (m + 1).succ))
            (uPrefix (Fin.last (m + 1)))
            (huPrefix (Fin.last (m + 1))) := by
      -- Normalize the terminal shared suffix back to the last explicit interval.
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := shared_tuple_prefix_points w kPoint kPrev)
          (a' := tTrunc (Fin.last m.succ))
          (b := shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))
          (b' := tPrefix (Fin.last (m + 1).succ))
          (i := uPrefix (Fin.last (m + 1)))
          (i' := uPrefix (Fin.last (m + 1)))
          hkPrev_eq
          hlast_eq
          rfl
          (hsub := hterminal_sub)
          (hsub' := huPrefix (Fin.last (m + 1)))
    have hsource :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev
                0)) =
          chosen_cover_object O hO S
            (γ (tTrunc 0)) := by
      -- The predecessor prefix still starts at the initial explicit breakpoint.
      simpa [tTrunc, hsigma0Prev] using
        congrArg
          (fun z : I ↦ chosen_cover_object O hO S (γ z))
          (hsigmaeqPrev 0)
    have hmid :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev
                (Fin.last kPrev.1))) =
          chosen_cover_object O hO S
            (γ (tTrunc (Fin.last m.succ))) := by
      -- The predecessor prefix endpoint is the previous explicit cutpoint.
      simpa [tTrunc, hsigma1Prev] using
        congrArg
          (fun z : I ↦ chosen_cover_object O hO S (γ z))
          (hsigmaeqPrev (Fin.last m.succ))
    have htarget :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev
                (Fin.last (kPoint.1 - kPrev.1)))) =
          chosen_cover_object O hO S
            (γ (tPrefix (Fin.last (m + 1).succ))) := by
      have hsuffixLast :
          shared_tuple_suffix_points
              (shared_tuple_prefix_points w kPoint)
              kPrev
              (Fin.last (kPoint.1 - kPrev.1)) =
            shared_tuple_prefix_points w kPoint (Fin.last kPoint.1) := by
        -- The terminal shared suffix of the ambient prefix ends at the ambient prefix endpoint.
        have hlastIndex :
            (⟨kPrev.1 + (Fin.last (kPoint.1 - kPrev.1)).1, by
              have hq : (Fin.last (kPoint.1 - kPrev.1)).1 < kPoint.1 - kPrev.1 + 1 :=
                (Fin.last (kPoint.1 - kPrev.1)).is_lt
              omega⟩ : Fin (kPoint.1 + 1)) =
              Fin.last kPoint.1 := by
          ext
          simp
          omega
        simpa [shared_tuple_suffix_points] using
          congrArg (shared_tuple_prefix_points w kPoint) hlastIndex
      calc
        chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev
                (Fin.last (kPoint.1 - kPrev.1)))) =
          chosen_cover_object O hO S
            (γ (shared_tuple_prefix_points w kPoint (Fin.last kPoint.1))) := by
              rw [hsuffixLast]
        _ =
          chosen_cover_object O hO S
            (γ (tPrefix (Fin.last (m + 1).succ))) := by
              simpa using
                congrArg
                  (fun z : I ↦ chosen_cover_object O hO S (γ z))
                  hlast_eq
    have hprefixTail :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points
              (shared_tuple_prefix_points w kPoint)
              kPrev)
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              kPrev)
            (shared_tuple_prefix_subordinate
              γ
              (shared_tuple_prefix_points w kPoint)
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              hcanonical_sub
              kPrev) ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points
              (shared_tuple_prefix_points w kPoint)
              kPrev)
            (u := shared_tuple_suffix_labels
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              kPrev)
            (shared_tuple_suffix_subordinate
              γ
              (shared_tuple_prefix_points w kPoint)
              (shared_tuple_cutpoint_labels
                uPrefix
                (by simp)
                sigmaTrunc
                hsigma0Trunc
                hsigma1Trunc
                hsigmamonoTrunc)
              hcanonical_sub
              kPrev) ≍
          subdivision_morphism O hO hinter S γ
              (t := tTrunc)
              (u := uTrunc)
              (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (tTrunc (Fin.last m.succ))
              (tPrefix (Fin.last (m + 1).succ))
              (uPrefix (Fin.last (m + 1)))
              (huPrefix (Fin.last (m + 1))) := by
      -- Compose the predecessor collapse with the terminal shared-block collapse.
      exact
        CategoryTheory.heq_comp
          hsource
          hmid
          htarget
          (hprefixLabelsHeq.trans hprevCollapse)
          (htailCollapse.trans htailTransport)
    have hfull_explicit :
        subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            huPrefix =
          subdivision_morphism O hO hinter S γ
              (t := tTrunc)
              (u := uTrunc)
              (fun q : Fin m.succ ↦ huPrefix q.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (tTrunc (Fin.last m.succ))
              (tPrefix (Fin.last (m + 1).succ))
              (uPrefix (Fin.last (m + 1)))
              (huPrefix (Fin.last (m + 1))) := by
      -- One recursive unfold of the explicit prefix subdivision isolates its final interval.
      rfl
    exact hreassembly.trans (hprefixTail.trans hfull_explicit.heq.symm)

/-- Helper for Theorem 2.7.1: the literal shared prefix ambient tuple equipped with its
transported canonical cutpoint labels should collapse to the transported explicit prefix
subdivision. -/
theorem shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (kPoint : Fin (N + 1))
    (tPrefix : Fin (m.succ + 1) → I)
    (uPrefix : Fin m.succ → TopologicalSpace.IsOpenCover.Index O)
    (huPrefix :
      ∀ q : Fin m.succ, Set.range (γ.subpath (tPrefix q.castSucc) (tPrefix q.succ)) ⊆ O (uPrefix q))
    (sigmaTrunc : Fin (m.succ + 1) → Fin (kPoint.1 + 1))
    (hsigma0Trunc : sigmaTrunc 0 = 0)
    (hsigma1Trunc : sigmaTrunc (Fin.last m.succ) = Fin.last kPoint.1)
    (hsigmamonoTrunc : Monotone sigmaTrunc)
    (hsigmaeqTrunc :
      ∀ j : Fin (m.succ + 1),
        shared_tuple_prefix_points w kPoint (sigmaTrunc j) = tPrefix j)
    (hcanonical_sub :
      ∀ q : Fin kPoint.1,
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w kPoint q.castSucc)
              (shared_tuple_prefix_points w kPoint q.succ)) ⊆
          O (shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc
            q)) :
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w kPoint)
        (u := shared_tuple_cutpoint_labels
          uPrefix
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc)
        hcanonical_sub ≍
    subdivision_morphism O hO hinter S γ
        (t := tPrefix)
        (u := uPrefix)
        huPrefix := by
  -- Route correction: the successor step must recurse on the transported predecessor prefix and
  -- then consume that recursive collapse in the ambient-prefix reassembly theorem.
  induction m generalizing N w hwmono kPoint with
  | zero =>
      -- Collapse the transported shared prefix to the unique explicit interval.
      exact
        shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core_base
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (hwmono := hwmono)
          (kPoint := kPoint)
          (tPrefix := tPrefix)
          (uPrefix := uPrefix)
          (huPrefix := huPrefix)
          (sigmaTrunc := sigmaTrunc)
          (hsigma0Trunc := hsigma0Trunc)
          (hsigma1Trunc := hsigma1Trunc)
          (hsigmamonoTrunc := hsigmamonoTrunc)
          (hsigmaeqTrunc := hsigmaeqTrunc)
          (hcanonical_sub := hcanonical_sub)
  | succ m ih =>
      let kPrev : Fin (kPoint.1 + 1) := sigmaTrunc (Fin.castSucc (Fin.last (m + 1)))
      let tTrunc : Fin (m.succ + 1) → I := fun q ↦ tPrefix q.castSucc
      let uTrunc : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ uPrefix q.castSucc
      obtain ⟨sigmaPrev, hsigma0Prev, hsigma1Prev, hsigmamonoPrev, hsigmaeqPrev, hlabelsPrev⟩ :=
        shared_tuple_prefix_transport_to_previous_cutpoint
          (w := w)
          (kPoint := kPoint)
          (tPrefix := tPrefix)
          (uPrefix := uPrefix)
          (sigmaTrunc := sigmaTrunc)
          (hsigma0Trunc := hsigma0Trunc)
          (hsigma1Trunc := hsigma1Trunc)
          (hsigmamonoTrunc := hsigmamonoTrunc)
          (hsigmaeqTrunc := hsigmaeqTrunc)
      have hcanonical_sub_prev :
          ∀ q : Fin kPrev.1,
            Set.range
                (γ.subpath
                  (shared_tuple_prefix_points
                    (shared_tuple_prefix_points w kPoint)
                    kPrev
                    q.castSucc)
                  (shared_tuple_prefix_points
                    (shared_tuple_prefix_points w kPoint)
                    kPrev
                    q.succ)) ⊆
              O (shared_tuple_cutpoint_labels
                uTrunc
                (by simp)
                sigmaPrev
                hsigma0Prev
                hsigma1Prev
                hsigmamonoPrev
                q) := by
        -- The transported predecessor tuple inherits the canonical cutpoint-block subordinacy data
        -- from the ambient prefix.
        exact
          shared_tuple_prefix_transport_cutpoint_block_subordinate
            (γ := γ)
            (w := shared_tuple_prefix_points w kPoint)
            (hwmono := shared_tuple_prefix_points_monotone w hwmono kPoint)
            (t := tPrefix)
            (u := uPrefix)
            (hu := huPrefix)
            (kPoint := kPrev)
            (sigmaTrunc := sigmaPrev)
            (hsigma0Trunc := hsigma0Prev)
            (hsigma1Trunc := hsigma1Prev)
            (hsigmamonoTrunc := hsigmamonoPrev)
            (hsigmaeqTrunc := hsigmaeqPrev)
      have hprevCollapse :
          subdivision_morphism O hO hinter S γ
              (t := shared_tuple_prefix_points
                (shared_tuple_prefix_points w kPoint)
                kPrev)
              (u := shared_tuple_cutpoint_labels
                uTrunc
                (by simp)
                sigmaPrev
                hsigma0Prev
                hsigma1Prev
                hsigmamonoPrev)
              hcanonical_sub_prev ≍
            subdivision_morphism O hO hinter S γ
              (t := tTrunc)
              (u := uTrunc)
              (fun q : Fin m.succ ↦ huPrefix q.castSucc) := by
        -- Apply the induction hypothesis to the transported predecessor prefix tuple.
        exact
          ih
            (w := shared_tuple_prefix_points w kPoint)
            (hwmono := shared_tuple_prefix_points_monotone w hwmono kPoint)
            (kPoint := kPrev)
            (tPrefix := tTrunc)
            (uPrefix := uTrunc)
            (huPrefix := fun q : Fin m.succ ↦ huPrefix q.castSucc)
            (sigmaTrunc := sigmaPrev)
            (hsigma0Trunc := hsigma0Prev)
            (hsigma1Trunc := hsigma1Prev)
            (hsigmamonoTrunc := hsigmamonoPrev)
            (hsigmaeqTrunc := hsigmaeqPrev)
            (hcanonical_sub := hcanonical_sub_prev)
      exact
        shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core_succ_step
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (hwmono := hwmono)
          (kPoint := kPoint)
          (tPrefix := tPrefix)
          (uPrefix := uPrefix)
          (huPrefix := huPrefix)
          (sigmaTrunc := sigmaTrunc)
          (hsigma0Trunc := hsigma0Trunc)
          (hsigma1Trunc := hsigma1Trunc)
          (hsigmamonoTrunc := hsigmamonoTrunc)
          (hsigmaeqTrunc := hsigmaeqTrunc)
          (hcanonical_sub := hcanonical_sub)
          (sigmaPrev := sigmaPrev)
          (hsigma0Prev := hsigma0Prev)
          (hsigma1Prev := hsigma1Prev)
          (hsigmamonoPrev := hsigmamonoPrev)
          (hsigmaeqPrev := hsigmaeqPrev)
          (hlabelsPrev := hlabelsPrev)
          (hcanonical_sub_prev := hcanonical_sub_prev)
          (hprevCollapse := hprevCollapse)

/-- Helper for Theorem 2.7.1: in the strict successor branch, the ambient shared-tuple composite
factors heterogeneously as the literal shared prefix up to the previous explicit cutpoint followed
by the literal terminal suffix starting at that cutpoint. -/
theorem shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (t : Fin ((m + 1).succ + 1) → I)
    (hn : (m + 1).succ ≠ 0)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (m + 1).succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin ((m + 1).succ + 1), w (sigma j) = t j) :
    let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
    let tPrefix : Fin (m.succ + 1) → I := fun q ↦ t q.castSucc
    let uPrefix : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ u q.castSucc
    subdivision_morphism O hO hinter S γ
        (t := shared_tuple_prefix_points w kPoint)
        (u := shared_tuple_prefix_labels
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          kPoint)
        (shared_tuple_prefix_subordinate
          γ
          w
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          (shared_tuple_cutpoint_block_subordinate
            (γ := γ)
            (t := t)
            (w := w)
            (hn := hn)
            (sigma := sigma)
            (hsigma0 := hsigma0)
            (hsigma1 := hsigma1)
            (hsigmamono := hsigmamono)
            (hsigmaeq := hsigmaeq)
            (hwmono := hwmono)
            (u := u)
            (hu := hu))
          kPoint) ≍
      subdivision_morphism O hO hinter S γ
        (t := tPrefix)
        (u := uPrefix)
        (fun q : Fin m.succ ↦ hu q.castSucc) := by
  -- Route correction: this helper works on the literal shared prefix ambient tuple itself, so the
  -- cutpoint-block induction has to be rebuilt after transporting the explicit prefix data to the
  -- truncated ambient endpoint.
  dsimp
  obtain ⟨sigmaTrunc, hsigma0Trunc, hsigma1Trunc, hsigmamonoTrunc, hsigmaeqTrunc, hlabels⟩ :=
    subdivision_morphism_prefix_transport_to_sigma_truncation
      (t := t)
      (w := w)
      (hn := hn)
      (u := u)
      (sigma := sigma)
      (hsigma0 := hsigma0)
      (hsigma1 := hsigma1)
      (hsigmamono := hsigmamono)
      (hsigmaeq := hsigmaeq)
  have hcanonical_sub :
      ∀ q : Fin (sigma (Fin.castSucc (Fin.last (m + 1)))).1,
        Set.range
            (γ.subpath
              (shared_tuple_prefix_points w (sigma (Fin.castSucc (Fin.last (m + 1)))) q.castSucc)
              (shared_tuple_prefix_points w (sigma (Fin.castSucc (Fin.last (m + 1)))) q.succ)) ⊆
          O (shared_tuple_cutpoint_labels
            (fun r : Fin m.succ ↦ u r.castSucc)
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc
            q) := by
    -- The transported breakpoint data already supply the canonical cutpoint-block labels on the
    -- literal shared prefix ambient tuple.
    exact
      shared_tuple_prefix_transport_cutpoint_block_subordinate
        (γ := γ)
        (w := w)
        (hwmono := hwmono)
        (t := t)
        (u := u)
        (hu := hu)
        (kPoint := sigma (Fin.castSucc (Fin.last (m + 1))))
        (sigmaTrunc := sigmaTrunc)
        (hsigma0Trunc := hsigma0Trunc)
        (hsigma1Trunc := hsigma1Trunc)
        (hsigmamonoTrunc := hsigmamonoTrunc)
        (hsigmaeqTrunc := hsigmaeqTrunc)
  have hrewrite :
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w (sigma (Fin.castSucc (Fin.last (m + 1)))))
          (u := shared_tuple_prefix_labels
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (sigma (Fin.castSucc (Fin.last (m + 1)))))
          (shared_tuple_prefix_subordinate
            γ
            w
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu))
            (sigma (Fin.castSucc (Fin.last (m + 1))))) =
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w (sigma (Fin.castSucc (Fin.last (m + 1)))))
          (u := shared_tuple_cutpoint_labels
            (fun r : Fin m.succ ↦ u r.castSucc)
            (by simp)
            sigmaTrunc
            hsigma0Trunc
            hsigma1Trunc
            hsigmamonoTrunc)
          hcanonical_sub := by
    -- On the literal shared prefix, the point tuple is fixed, so the only remaining freedom is
    -- which subordinate label family is used on each interval.
    exact
      subdivision_morphism_eq_of_same_points
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := shared_tuple_prefix_points w (sigma (Fin.castSucc (Fin.last (m + 1)))))
        (u := shared_tuple_prefix_labels
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          (sigma (Fin.castSucc (Fin.last (m + 1)))))
        (v := shared_tuple_cutpoint_labels
          (fun r : Fin m.succ ↦ u r.castSucc)
          (by simp)
          sigmaTrunc
          hsigma0Trunc
          hsigma1Trunc
          hsigmamonoTrunc)
        (hu := shared_tuple_prefix_subordinate
          γ
          w
          (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          (shared_tuple_cutpoint_block_subordinate
            (γ := γ)
            (t := t)
            (w := w)
            (hn := hn)
            (sigma := sigma)
            (hsigma0 := hsigma0)
            (hsigma1 := hsigma1)
            (hsigmamono := hsigmamono)
            (hsigmaeq := hsigmaeq)
            (hwmono := hwmono)
            (u := u)
            (hu := hu))
          (sigma (Fin.castSucc (Fin.last (m + 1)))))
        (hv := hcanonical_sub)
  rw [hrewrite]
  -- The transported literal prefix comparison is now isolated in the dedicated prefix-core
  -- helper, so this theorem is just the interface-alignment adapter back to the original
  -- shared-prefix statement.
  let _ := hlabels
  exact
    shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit_core
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (hwmono := hwmono)
      (kPoint := sigma (Fin.castSucc (Fin.last (m + 1))))
      (tPrefix := fun q ↦ t q.castSucc)
      (uPrefix := fun q ↦ u q.castSucc)
      (huPrefix := fun q : Fin m.succ ↦ hu q.castSucc)
      (sigmaTrunc := sigmaTrunc)
      (hsigma0Trunc := hsigma0Trunc)
      (hsigma1Trunc := hsigma1Trunc)
      (hsigmamonoTrunc := hsigmamonoTrunc)
      (hsigmaeqTrunc := hsigmaeqTrunc)
      (hcanonical_sub := hcanonical_sub)

/-- Helper for Theorem 2.7.1: in the strict successor branch, the ambient shared-tuple composite
factors heterogeneously as the literal shared prefix up to the previous explicit cutpoint followed
by the literal terminal suffix starting at that cutpoint. -/
theorem shared_tuple_cutpoint_reassembly_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (t : Fin ((m + 1).succ + 1) → I)
    (hn : (m + 1).succ ≠ 0)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (m + 1).succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin ((m + 1).succ + 1), w (sigma j) = t j)
    (hwmono : Monotone w)
    (hk : sigma (Fin.castSucc (Fin.last (m + 1))) ≠ Fin.last N) :
    let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
    subdivision_morphism O hO hinter S γ
        (t := w)
        (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
        (shared_tuple_cutpoint_block_subordinate
          (γ := γ)
          (t := t)
          (w := w)
          (hn := hn)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          (hwmono := hwmono)
          (u := u)
          (hu := hu)) ≍
      subdivision_morphism O hO hinter S γ
          (t := shared_tuple_prefix_points w kPoint)
          (u := shared_tuple_prefix_labels
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            kPoint)
          (shared_tuple_prefix_subordinate
            γ
            w
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu))
            kPoint) ≫
        subdivision_morphism O hO hinter S γ
          (t := shared_tuple_suffix_points w kPoint)
          (u := shared_tuple_suffix_labels
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            kPoint)
          (shared_tuple_suffix_subordinate
            γ
            w
            (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu))
            kPoint) := by
  -- This is now a direct specialization of the ambient literal cutpoint reassembly theorem to the
  -- shared tuple relabelled by its canonical cutpoint blocks.
  dsimp
  exact
    subdivision_morphism_literal_nonterminal_cutpoint_reassembly_heq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (w := w)
      (v := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
      (hv := shared_tuple_cutpoint_block_subordinate
        (γ := γ)
        (t := t)
        (w := w)
        (hn := hn)
        (sigma := sigma)
        (hsigma0 := hsigma0)
        (hsigma1 := hsigma1)
        (hsigmamono := hsigmamono)
        (hsigmaeq := hsigmaeq)
        (hwmono := hwmono)
        (u := u)
        (hu := hu))
      (kPoint := sigma (Fin.castSucc (Fin.last (m + 1))))
      hk

/-- Helper for Theorem 2.7.1: once the shared tuple is relabelled by canonical cutpoint blocks, its
subdivision composite should collapse block-by-block back to the original explicit subdivision. -/
theorem subdivision_morphism_eq_of_cutpoint_blocks_succ_step
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {N m : ℕ}
    (w : Fin (N + 1) → I)
    (hwmono : Monotone w)
    (t : Fin ((m + 1).succ + 1) → I)
    (hn : (m + 1).succ ≠ 0)
    (u : Fin (m + 1).succ → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin (m + 1).succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin ((m + 1).succ + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last (m + 1).succ) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin ((m + 1).succ + 1), w (sigma j) = t j)
    (ih :
      ∀ (t : Fin (m.succ + 1) → I) (hn : m.succ ≠ 0)
        (u : Fin m.succ → TopologicalSpace.IsOpenCover.Index O)
        (hu : ∀ k : Fin m.succ, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
        (sigma : Fin (m.succ + 1) → Fin (N + 1))
        (hsigma0 : sigma 0 = 0)
        (hsigma1 : sigma (Fin.last m.succ) = Fin.last N)
        (hsigmamono : Monotone sigma)
        (hsigmaeq : ∀ j : Fin (m.succ + 1), w (sigma j) = t j),
          subdivision_morphism O hO hinter S γ
              (t := w)
              (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              (shared_tuple_cutpoint_block_subordinate
                (γ := γ)
                (t := t)
                (w := w)
                (hn := hn)
                (sigma := sigma)
                (hsigma0 := hsigma0)
                (hsigma1 := hsigma1)
                (hsigmamono := hsigmamono)
                (hsigmaeq := hsigmaeq)
                (hwmono := hwmono)
                (u := u)
                (hu := hu)) ≍
            subdivision_morphism O hO hinter S γ
              (t := t)
              (u := u)
              hu) :
    subdivision_morphism O hO hinter S γ
        (t := w)
        (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
        (shared_tuple_cutpoint_block_subordinate
          (γ := γ)
          (t := t)
          (w := w)
          (hn := hn)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          (hwmono := hwmono)
          (u := u)
          (hu := hu)) ≍
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  -- Route correction: the remaining gap is no longer the semantic sigma-block collapse. The open
  -- step is the literal recursive reassembly at the terminal cutpoint, using `ih` on the shared
  -- prefix ending at `sigma (Fin.castSucc (Fin.last (m + 1)))`.
  let tPrefix : Fin (m.succ + 1) → I := fun q ↦ t q.castSucc
  let uPrefix : Fin m.succ → TopologicalSpace.IsOpenCover.Index O := fun q ↦ u q.castSucc
  let sigmaPrefix : Fin (m.succ + 1) → Fin (N + 1) := fun q ↦ sigma q.castSucc
  have hsigma0Prefix : sigmaPrefix 0 = 0 := by
    -- The truncated explicit prefix still starts at the first shared breakpoint.
    simpa [sigmaPrefix] using hsigma0
  have hsigmamonoPrefix : Monotone sigmaPrefix := by
    -- Monotonicity survives after deleting the final explicit breakpoint.
    intro a b hab
    exact hsigmamono (show a.castSucc ≤ b.castSucc by simpa using hab)
  by_cases hk : sigma (Fin.castSucc (Fin.last (m + 1))) = Fin.last N
  · have hsigma1Prefix : sigmaPrefix (Fin.last m.succ) = Fin.last N := by
      -- In the degenerate-terminal case, the truncated explicit prefix already reaches the final
      -- shared breakpoint.
      simpa [sigmaPrefix] using hk
    have hsigmaeqPrefix : ∀ j : Fin (m.succ + 1), w (sigmaPrefix j) = tPrefix j := by
      -- The truncated comparison data are inherited from the original breakpoint comparison.
      intro j
      simpa [sigmaPrefix, tPrefix] using hsigmaeq j.castSucc
    have hlabels :
        shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono =
          shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaPrefix
            hsigma0Prefix
            hsigma1Prefix
            hsigmamonoPrefix := by
      funext k
      let j :=
        shared_tuple_cutpoint_block
          (by simp)
          sigmaPrefix
          hsigma0Prefix
          hsigma1Prefix
          hsigmamonoPrefix
          k
      have hj :
          sigmaPrefix j.castSucc ≤ k.castSucc ∧
            k.succ ≤ sigmaPrefix j.succ := by
        -- The prefix cutpoint block already records the same consecutive shared-interval bounds.
        simpa [j] using
          shared_tuple_cutpoint_block_spec
            (by simp)
            sigmaPrefix
            hsigma0Prefix
            hsigma1Prefix
            hsigmamonoPrefix
            k
      have horig :
          shared_tuple_cutpoint_block hn sigma hsigma0 hsigma1 hsigmamono k = j.castSucc := by
        -- Those same bounds identify the original cutpoint block as the cast-successor of the
        -- truncated one.
        apply
          shared_tuple_cutpoint_block_eq_of_between
            (hn := hn)
            (sigma := sigma)
            (hsigma0 := hsigma0)
            (hsigma1 := hsigma1)
            (hsigmamono := hsigmamono)
        · simpa [sigmaPrefix, j] using hj.1
        · simpa [sigmaPrefix, j] using hj.2
      -- After rewriting the canonical cutpoint block, both label families are literally the same.
      simp [shared_tuple_cutpoint_labels, uPrefix, sigmaPrefix, j, horig]
    have hshared :
        subdivision_morphism O hO hinter S γ
            (t := w)
            (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu)) ≍
          subdivision_morphism O hO hinter S γ
            (t := w)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaPrefix
              hsigma0Prefix
              hsigma1Prefix
              hsigmamonoPrefix)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := tPrefix)
              (w := w)
              (hn := by simp)
              (sigma := sigmaPrefix)
              (hsigma0 := hsigma0Prefix)
              (hsigma1 := hsigma1Prefix)
              (hsigmamono := hsigmamonoPrefix)
              (hsigmaeq := hsigmaeqPrefix)
              (hwmono := hwmono)
              (u := uPrefix)
              (hu := fun k : Fin m.succ ↦ hu k.castSucc)) := by
      -- The shared tuple keeps the same breakpoints; only the now-superfluous terminal explicit
      -- label is removed.
      exact
        subdivision_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (t := w)
          (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
          (u' := shared_tuple_cutpoint_labels
            uPrefix
            (by simp)
            sigmaPrefix
            hsigma0Prefix
            hsigma1Prefix
            hsigmamonoPrefix)
          (ht := rfl)
          (hu := hlabels)
    have hprefix :
        subdivision_morphism O hO hinter S γ
            (t := w)
            (u := shared_tuple_cutpoint_labels
              uPrefix
              (by simp)
              sigmaPrefix
              hsigma0Prefix
              hsigma1Prefix
              hsigmamonoPrefix)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := tPrefix)
              (w := w)
              (hn := by simp)
              (sigma := sigmaPrefix)
              (hsigma0 := hsigma0Prefix)
              (hsigma1 := hsigma1Prefix)
              (hsigmamono := hsigmamonoPrefix)
              (hsigmaeq := hsigmaeqPrefix)
              (hwmono := hwmono)
              (u := uPrefix)
              (hu := fun k : Fin m.succ ↦ hu k.castSucc)) ≍
          subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun k : Fin m.succ ↦ hu k.castSucc) := by
      -- Once the degenerate terminal interval is deleted, the induction hypothesis applies to the
      -- truncated explicit subdivision.
      exact
        ih
          tPrefix
          (by simp)
          uPrefix
          (fun k : Fin m.succ ↦ hu k.castSucc)
          sigmaPrefix
          hsigma0Prefix
          hsigma1Prefix
          hsigmamonoPrefix
          hsigmaeqPrefix
    have hsigma_same :
        sigma (Fin.castSucc (Fin.last (m + 1))) =
          sigma ((Fin.last (m + 1)).succ) := by
      -- The degenerate terminal explicit interval has both endpoints at the final shared
      -- breakpoint.
      calc
        sigma (Fin.castSucc (Fin.last (m + 1))) = Fin.last N := hk
        _ = sigma ((Fin.last (m + 1)).succ) := by simpa using hsigma1.symm
    have hdeg :
        t (Fin.castSucc (Fin.last (m + 1))) =
          t ((Fin.last (m + 1)).succ) := by
      -- Therefore the terminal explicit interval is itself degenerate.
      exact
        explicit_interval_eq_of_sigma_eq
          t
          w
          sigma
          hsigmaeq
          (Fin.last (m + 1))
          hsigma_same
    have hconst_sub :
        Set.range
            (γ.subpath
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t (Fin.castSucc (Fin.last (m + 1))))) ⊆
          O (u (Fin.last (m + 1))) := by
      -- Rewriting the degenerate subpath by `hdeg` turns it into the original final explicit
      -- interval, whose cover containment is already `hu`.
      intro z hz
      have hz' :
          z ∈ Set.range
            (γ.subpath
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t ((Fin.last (m + 1)).succ))) := by
        rcases hz with ⟨s, rfl⟩
        refine ⟨s, ?_⟩
        change γ.subpath _ _ s = γ.subpath _ _ s
        rw [hdeg]
      exact hu (Fin.last (m + 1)) hz'
    have hlast_heq :
        local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t ((Fin.last (m + 1)).succ))
            (u (Fin.last (m + 1)))
            (hu (Fin.last (m + 1))) ≍
          local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t (Fin.castSucc (Fin.last (m + 1))))
            (u (Fin.last (m + 1)))
            hconst_sub := by
      -- Replacing the terminal target by the equal source isolates the constant-path case.
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := t (Fin.castSucc (Fin.last (m + 1))))
          (a' := t (Fin.castSucc (Fin.last (m + 1))))
          (b := t ((Fin.last (m + 1)).succ))
          (b' := t (Fin.castSucc (Fin.last (m + 1))))
          (i := u (Fin.last (m + 1)))
          (i' := u (Fin.last (m + 1)))
          rfl
          hdeg.symm
          rfl
          (hsub := hu (Fin.last (m + 1)))
          (hsub' := hconst_sub)
    have hlast_id :
        local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t (Fin.castSucc (Fin.last (m + 1))))
            (u (Fin.last (m + 1)))
            hconst_sub =
          𝟙 (chosen_cover_object O hO S
            (γ (t (Fin.castSucc (Fin.last (m + 1)))))) := by
      -- A degenerate local segment contributes the identity.
      exact
        local_subpath_morphism_eq_id_of_eq_endpoints
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := t (Fin.castSucc (Fin.last (m + 1))))
          (i := u (Fin.last (m + 1)))
          (hsub := hconst_sub)
    have hobj_last :
        chosen_cover_object O hO S (γ (t (Fin.castSucc (Fin.last (m + 1))))) =
          chosen_cover_object O hO S (γ (t ((Fin.last (m + 1)).succ))) := by
      -- The chosen endpoint objects agree because the terminal explicit interval is degenerate.
      exact congrArg (chosen_cover_object O hO S) (congrArg γ hdeg)
    have htail_heq :
        local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t ((Fin.last (m + 1)).succ))
            (u (Fin.last (m + 1)))
            (hu (Fin.last (m + 1))) ≍
          𝟙 (chosen_cover_object O hO S
            (γ (t (Fin.castSucc (Fin.last (m + 1)))))) := by
      -- Keep the terminal factor as a heterogeneous identity so the endpoint transport remains
      -- explicit in the final composition.
      exact hlast_heq.trans hlast_id.heq
    have hcomp_heq :
        subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun k : Fin m.succ ↦ hu k.castSucc) ≫
          local_subpath_morphism O hO hinter S γ
            (t (Fin.castSucc (Fin.last (m + 1))))
            (t ((Fin.last (m + 1)).succ))
            (u (Fin.last (m + 1)))
            (hu (Fin.last (m + 1))) ≍
          subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun k : Fin m.succ ↦ hu k.castSucc) := by
      have hcomp_to_id :
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              (fun k : Fin m.succ ↦ hu k.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t ((Fin.last (m + 1)).succ))
              (u (Fin.last (m + 1)))
              (hu (Fin.last (m + 1))) ≍
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              (fun k : Fin m.succ ↦ hu k.castSucc) ≫
            𝟙 (chosen_cover_object O hO S
              (γ (t (Fin.castSucc (Fin.last (m + 1)))))) := by
        -- Compose the unchanged prefix with the heterogeneous identity description of the terminal
        -- factor.
        exact CategoryTheory.heq_comp rfl rfl hobj_last.symm HEq.rfl htail_heq
      -- After replacing the terminal factor by the identity, the explicit prefix composite is
      -- unchanged.
      exact hcomp_to_id.trans
        (CategoryTheory.Category.comp_id
          (subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun k : Fin m.succ ↦ hu k.castSucc))).heq
    have hfull_explicit :
        subdivision_morphism O hO hinter S γ
            (t := t)
            (u := u)
            hu ≍
          subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun k : Fin m.succ ↦ hu k.castSucc) := by
      -- Unfold the explicit subdivision once and then use the heterogeneous `comp_id`
      -- normalization above.
      exact (rfl : subdivision_morphism O hO hinter S γ (t := t) (u := u) hu =
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              (fun k : Fin m.succ ↦ hu k.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last (m + 1))))
              (t ((Fin.last (m + 1)).succ))
              (u (Fin.last (m + 1)))
              (hu (Fin.last (m + 1)))).heq.trans hcomp_heq
    exact hshared.trans (hprefix.trans hfull_explicit.symm)
  · -- The only remaining case is the genuine terminal sigma-block reassembly where the previous
    -- explicit cutpoint lands strictly before the final shared breakpoint.
    let kPoint : Fin (N + 1) := sigma (Fin.castSucc (Fin.last (m + 1)))
    have hreassembly :
        subdivision_morphism O hO hinter S γ
            (t := w)
            (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
            (shared_tuple_cutpoint_block_subordinate
              (γ := γ)
              (t := t)
              (w := w)
              (hn := hn)
              (sigma := sigma)
              (hsigma0 := hsigma0)
              (hsigma1 := hsigma1)
              (hsigmamono := hsigmamono)
              (hsigmaeq := hsigmaeq)
              (hwmono := hwmono)
              (u := u)
              (hu := hu)) ≍
          subdivision_morphism O hO hinter S γ
              (t := shared_tuple_prefix_points w kPoint)
              (u := shared_tuple_prefix_labels
                (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
                kPoint)
              (shared_tuple_prefix_subordinate
                γ
                w
                (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
                (shared_tuple_cutpoint_block_subordinate
                  (γ := γ)
                  (t := t)
                  (w := w)
                  (hn := hn)
                  (sigma := sigma)
                  (hsigma0 := hsigma0)
                  (hsigma1 := hsigma1)
                  (hsigmamono := hsigmamono)
                  (hsigmaeq := hsigmaeq)
                  (hwmono := hwmono)
                  (u := u)
                  (hu := hu))
                kPoint) ≫
            subdivision_morphism O hO hinter S γ
              (t := shared_tuple_suffix_points w kPoint)
              (u := shared_tuple_suffix_labels
                (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
                kPoint)
              (shared_tuple_suffix_subordinate
                γ
                w
                (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
                (shared_tuple_cutpoint_block_subordinate
                  (γ := γ)
                  (t := t)
                  (w := w)
                  (hn := hn)
                  (sigma := sigma)
                  (hsigma0 := hsigma0)
                  (hsigma1 := hsigma1)
                  (hsigmamono := hsigmamono)
                  (hsigmaeq := hsigmaeq)
                  (hwmono := hwmono)
                  (u := u)
                  (hu := hu))
                kPoint) := by
      -- The ambient shared tuple now factors at the strict cutpoint into the literal prefix and
      -- the literal terminal suffix.
      exact
        shared_tuple_cutpoint_reassembly_heq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (t := t)
          (hn := hn)
          (u := u)
          (hu := hu)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          (hwmono := hwmono)
          hk
    have hkPoint_eq :
        w kPoint =
          tPrefix (Fin.last m.succ) := by
      -- The previous explicit cutpoint and the last breakpoint of the truncated explicit prefix
      -- are the same shared tuple point.
      simpa [kPoint, tPrefix] using hsigmaeq (Fin.castSucc (Fin.last (m + 1)))
    have hlast_eq :
        w (Fin.last N) =
          t (Fin.last (m + 1).succ) := by
      -- The terminal explicit breakpoint is the final shared breakpoint.
      calc
        w (Fin.last N) = w (sigma (Fin.last (m + 1).succ)) := by rw [← hsigma1]
        _ = t (Fin.last (m + 1).succ) := hsigmaeq (Fin.last (m + 1).succ)
    have hprefix :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              kPoint)
            (shared_tuple_prefix_subordinate
              γ
              w
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              (shared_tuple_cutpoint_block_subordinate
                (γ := γ)
                (t := t)
                (w := w)
                (hn := hn)
                (sigma := sigma)
                (hsigma0 := hsigma0)
                (hsigma1 := hsigma1)
                (hsigmamono := hsigmamono)
                (hsigmaeq := hsigmaeq)
                (hwmono := hwmono)
                (u := u)
                (hu := hu))
              kPoint) ≍
          subdivision_morphism O hO hinter S γ
            (t := tPrefix)
            (u := uPrefix)
            (fun q : Fin m.succ ↦ hu q.castSucc) := by
      -- The new prefix-model helper replaces the ambient shared tuple by the literal shared prefix
      -- ending at the previous explicit cutpoint.
      exact
        shared_tuple_prefix_cutpoint_blocks_eq_truncated_explicit
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (hwmono := hwmono)
          (t := t)
          (hn := hn)
          (u := u)
          (hu := hu)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
    obtain ⟨hterminal_sub, htailCollapse⟩ :=
      shared_tuple_cutpoint_terminal_suffix_collapse
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (w := w)
        (hwmono := hwmono)
        (t := t)
        (hn := hn)
        (u := u)
        (hu := hu)
        (sigma := sigma)
        (hsigma0 := hsigma0)
        (hsigma1 := hsigma1)
        (hsigmamono := hsigmamono)
        (hsigmaeq := hsigmaeq)
        hk
    have htailTransport :
        local_subpath_morphism O hO hinter S γ
            (w kPoint)
            (w (Fin.last N))
            (u (Fin.last (m + 1)))
            hterminal_sub ≍
          local_subpath_morphism O hO hinter S γ
            (tPrefix (Fin.last m.succ))
            (t (Fin.last (m + 1).succ))
            (u (Fin.last (m + 1)))
            (hu (Fin.last (m + 1))) := by
      -- Normalize the terminal suffix endpoints back to the final explicit interval.
      exact
        local_subpath_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (a := w kPoint)
          (a' := tPrefix (Fin.last m.succ))
          (b := w (Fin.last N))
          (b' := t (Fin.last (m + 1).succ))
          (i := u (Fin.last (m + 1)))
          (i' := u (Fin.last (m + 1)))
          hkPoint_eq
          hlast_eq
          rfl
          (hsub := hterminal_sub)
          (hsub' := hu (Fin.last (m + 1)))
    have hsource :
        chosen_cover_object O hO S
            (γ (shared_tuple_prefix_points w kPoint 0)) =
          chosen_cover_object O hO S (γ (tPrefix 0)) := by
      -- Both source objects are the chosen object of the initial path point.
      simpa [shared_tuple_prefix_points, tPrefix, hsigma0] using
        congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) (hsigmaeq 0)
    have hmid :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_prefix_points w kPoint
                (Fin.last kPoint.1))) =
          chosen_cover_object O hO S
            (γ (tPrefix (Fin.last m.succ))) := by
      -- The target of the literal shared prefix is the explicit breakpoint at the cutpoint.
      simpa [shared_tuple_prefix_points] using
        congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hkPoint_eq
    have htarget :
        chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points w kPoint
                (Fin.last (N - kPoint.1)))) =
          chosen_cover_object O hO S
            (γ (t (Fin.last (m + 1).succ))) := by
      -- The suffix target is the global terminal breakpoint, hence the terminal explicit point.
      have hsuffixLast :
          shared_tuple_suffix_points w kPoint
              (Fin.last (N - kPoint.1)) =
            w (Fin.last N) := by
        -- This is the same endpoint identification used in the terminal-suffix collapse.
        have hlastIndex :
            (⟨kPoint.1 + (Fin.last (N - kPoint.1)).1, by
              have hq : (Fin.last (N - kPoint.1)).1 < N - kPoint.1 + 1 :=
                (Fin.last (N - kPoint.1)).is_lt
              omega⟩ : Fin (N + 1)) =
              Fin.last N := by
          ext
          simp
          omega
        simpa [shared_tuple_suffix_points] using congrArg w hlastIndex
      calc
        chosen_cover_object O hO S
            (γ
              (shared_tuple_suffix_points w kPoint
                (Fin.last (N - kPoint.1)))) =
          chosen_cover_object O hO S (γ (w (Fin.last N))) := by
            rw [hsuffixLast]
        _ = chosen_cover_object O hO S
              (γ (t (Fin.last (m + 1).succ))) := by
            simpa using congrArg (fun z : I ↦ chosen_cover_object O hO S (γ z)) hlast_eq
    have hprefixTail :
        subdivision_morphism O hO hinter S γ
            (t := shared_tuple_prefix_points w kPoint)
            (u := shared_tuple_prefix_labels
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              kPoint)
            (shared_tuple_prefix_subordinate
              γ
              w
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              (shared_tuple_cutpoint_block_subordinate
                (γ := γ)
                (t := t)
                (w := w)
                (hn := hn)
                (sigma := sigma)
                (hsigma0 := hsigma0)
                (hsigma1 := hsigma1)
                (hsigmamono := hsigmamono)
                (hsigmaeq := hsigmaeq)
                (hwmono := hwmono)
                (u := u)
                (hu := hu))
              kPoint) ≫
          subdivision_morphism O hO hinter S γ
            (t := shared_tuple_suffix_points w kPoint)
            (u := shared_tuple_suffix_labels
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              kPoint)
            (shared_tuple_suffix_subordinate
              γ
              w
              (shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
              (shared_tuple_cutpoint_block_subordinate
                (γ := γ)
                (t := t)
                (w := w)
                (hn := hn)
                (sigma := sigma)
                (hsigma0 := hsigma0)
                (hsigma1 := hsigma1)
                (hsigmamono := hsigmamono)
                (hsigmaeq := hsigmaeq)
                (hwmono := hwmono)
                (u := u)
                (hu := hu))
              kPoint) ≍
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              (fun q : Fin m.succ ↦ hu q.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (tPrefix (Fin.last m.succ))
              (t (Fin.last (m + 1).succ))
              (u (Fin.last (m + 1)))
              (hu (Fin.last (m + 1))) := by
      -- Compose the shared-prefix comparison with the terminal-suffix collapse normalized back to
      -- the final explicit interval.
      exact
        CategoryTheory.heq_comp
          hsource
          hmid
          htarget
          hprefix
          (htailCollapse.trans htailTransport)
    have hfull_explicit :
        subdivision_morphism O hO hinter S γ
            (t := t)
            (u := u)
            hu =
          subdivision_morphism O hO hinter S γ
              (t := tPrefix)
              (u := uPrefix)
              (fun q : Fin m.succ ↦ hu q.castSucc) ≫
            local_subpath_morphism O hO hinter S γ
              (tPrefix (Fin.last m.succ))
              (t (Fin.last (m + 1).succ))
              (u (Fin.last (m + 1)))
              (hu (Fin.last (m + 1))) := by
      -- One recursive unfold of the explicit subdivision splits off the final explicit interval.
      rfl
    exact hreassembly.trans (hprefixTail.trans hfull_explicit.heq.symm)

/-- Helper for Theorem 2.7.1: once the shared tuple is relabelled by canonical cutpoint blocks, its
subdivision composite should collapse block-by-block back to the original explicit subdivision. -/
theorem subdivision_morphism_eq_of_cutpoint_blocks
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n N : ℕ}
    (t : Fin (n + 1) → I)
    (w : Fin (N + 1) → I)
    (hn : n ≠ 0)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (sigma : Fin (n + 1) → Fin (N + 1))
    (hsigma0 : sigma 0 = 0)
    (hsigma1 : sigma (Fin.last n) = Fin.last N)
    (hsigmamono : Monotone sigma)
    (hsigmaeq : ∀ j : Fin (n + 1), w (sigma j) = t j)
    (hwmono : Monotone w) :
    subdivision_morphism O hO hinter S γ
        (t := w)
        (u := shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono)
        (shared_tuple_cutpoint_block_subordinate
          (γ := γ)
          (t := t)
          (w := w)
          (hn := hn)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          (hwmono := hwmono)
          (u := u)
          (hu := hu)) ≍
    subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  induction m with
  | zero =>
      by_cases hN : N = 0
      · subst hN
        have hstart : w 0 = t 0 := by
          simpa [hsigma0] using hsigmaeq 0
        have hend : w 0 = t (Fin.last 1) := by
          have hsig1 : sigma (Fin.last 1) = 0 := by
            simpa using hsigma1
          calc
            w 0 = w (sigma (Fin.last 1)) := by rw [hsig1]
            _ = t (Fin.last 1) := hsigmaeq (Fin.last 1)
        have hsigma_same :
            sigma (Fin.last 0).castSucc = sigma (Fin.last 0).succ := by
          calc
            sigma (Fin.last 0).castSucc = 0 := by simpa [Fin.last] using hsigma0
            _ = sigma (Fin.last 0).succ := by
              symm
              simpa [Fin.last] using hsigma1
        have hdeg :
            t (Fin.last 0).castSucc = t (Fin.last 0).succ := by
          exact explicit_interval_eq_of_sigma_eq t w sigma hsigmaeq (Fin.last 0) hsigma_same
        have hmem :
            γ (w 0) ∈ O (u (Fin.last 0)) := by
          -- The degenerate explicit interval still lies in its cover member, so its unique point
          -- does as well.
          rw [hstart]
          exact
            subpath_source_mem_of_range_subset γ
              (t (Fin.last 0).castSucc)
              (t (Fin.last 0).succ)
              (hu (Fin.last 0))
        have hsub :
            Set.range (γ.subpath (w 0) (w 0)) ⊆ O (u (Fin.last 0)) := by
          -- The unique explicit interval is already degenerate, so its cover label also contains
          -- the constant shared tuple.
          intro z hz
          rcases hz with ⟨s, rfl⟩
          simpa [Path.subpath_self] using hmem
        have hw :
            subdivision_morphism O hO hinter S γ
                (t := w)
                (u := shared_tuple_cutpoint_labels u (by simp) sigma hsigma0 hsigma1 hsigmamono)
                (shared_tuple_cutpoint_block_subordinate
                  (γ := γ)
                  (t := t)
                  (w := w)
                  (hn := by simp)
                  (sigma := sigma)
                  (hsigma0 := hsigma0)
                  (hsigma1 := hsigma1)
                  (hsigmamono := hsigmamono)
                  (hsigmaeq := hsigmaeq)
                  (hwmono := hwmono)
                  (u := u)
                  (hu := hu)) =
              𝟙 (chosen_cover_object O hO S (γ (w 0))) := by
          -- A shared tuple with no intervals contributes the identity by definition.
          simp [subdivision_morphism]
        have ht :
            subdivision_morphism O hO hinter S γ
                (t := t)
                (u := u)
                hu =
              local_subpath_morphism O hO hinter S γ
                (t (Fin.last 0).castSucc)
                (t (Fin.last 0).succ)
                (u (Fin.last 0))
                (hu (Fin.last 0)) := by
          -- With one explicit interval, the recursive subdivision composite is exactly that single
          -- local segment morphism.
          simp [subdivision_morphism]
        have hlocal :
            local_subpath_morphism O hO hinter S γ
                (t (Fin.last 0).castSucc)
                (t (Fin.last 0).succ)
                (u (Fin.last 0))
                (hu (Fin.last 0)) ≍
              local_subpath_morphism O hO hinter S γ
                (w 0)
                (w 0)
                (u (Fin.last 0))
                hsub := by
          -- The explicit interval and the shared interval both reduce to the same degenerate
          -- endpoint in this case.
          exact
            local_subpath_morphism_heq_of_eq
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := γ)
              (a := t (Fin.last 0).castSucc)
              (a' := w 0)
              (b := t (Fin.last 0).succ)
              (b' := w 0)
              (i := u (Fin.last 0))
              (i' := u (Fin.last 0))
              hstart.symm
              hend.symm
              rfl
              (hsub := hu (Fin.last 0))
              (hsub' := hsub)
        have hlocal_id :
            local_subpath_morphism O hO hinter S γ
                (w 0)
                (w 0)
                (u (Fin.last 0))
                hsub =
              𝟙 (chosen_cover_object O hO S (γ (w 0))) := by
          -- The remaining local segment is a constant path.
          exact
            local_subpath_morphism_eq_id_of_eq_endpoints
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := γ)
              (a := w 0)
              (i := u (Fin.last 0))
              (hsub := hsub)
        exact hw.heq.trans (hlocal_id.heq.symm.trans (hlocal.symm.trans ht.heq.symm))
      ·
        have hstart : w 0 = t 0 := by
          simpa [hsigma0] using hsigmaeq 0
        have hend : w (Fin.last N) = t (Fin.last 1) := by
          have hsig1 : sigma (Fin.last 1) = Fin.last N := by
            simpa using hsigma1
          calc
            w (Fin.last N) = w (sigma (Fin.last 1)) := by rw [hsig1]
            _ = t (Fin.last 1) := hsigmaeq (Fin.last 1)
        have hsub :
            Set.range (γ.subpath (w 0) (w (Fin.last N))) ⊆ O (u (Fin.last 0)) := by
          -- The full shared tuple has the same endpoints as the unique explicit interval.
          intro z hz
          rcases hz with ⟨s, rfl⟩
          exact
            (hu (Fin.last 0)) ⟨s, by
              change γ.subpath (t 0) (t (Fin.last 1)) s =
                γ.subpath (w 0) (w (Fin.last N)) s
              rw [← hstart, ← hend]⟩
        have hwcollapse :
            subdivision_morphism O hO hinter S γ
                (t := w)
                (u := shared_tuple_cutpoint_labels u (by simp) sigma hsigma0 hsigma1 hsigmamono)
                (shared_tuple_cutpoint_block_subordinate
                  (γ := γ)
                  (t := t)
                  (w := w)
                  (hn := by simp)
                  (sigma := sigma)
                  (hsigma0 := hsigma0)
                  (hsigma1 := hsigma1)
                  (hsigmamono := hsigmamono)
                  (hsigmaeq := hsigmaeq)
                  (hwmono := hwmono)
                  (u := u)
                  (hu := hu)) =
              local_subpath_morphism O hO hinter S γ
                (w 0)
                (w (Fin.last N))
                (u (Fin.last 0))
                hsub := by
          -- The whole shared tuple lies in the unique explicit cover element, so the recursive
          -- subdivision composite collapses to one local segment morphism.
          exact
            subdivision_morphism_eq_local_subpath_morphism_of_range_subset
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := γ)
              (t := w)
              (u := shared_tuple_cutpoint_labels u (by simp) sigma hsigma0 hsigma1 hsigmamono)
              (hu := shared_tuple_cutpoint_block_subordinate
                (γ := γ)
                (t := t)
                (w := w)
                (hn := by simp)
                (sigma := sigma)
                (hsigma0 := hsigma0)
                (hsigma1 := hsigma1)
                (hsigmamono := hsigmamono)
                (hsigmaeq := hsigmaeq)
                (hwmono := hwmono)
                (u := u)
                (hu := hu))
              (hmono := hwmono)
              (hn := hN)
              (i := u (Fin.last 0))
              (hsub := hsub)
        have hlocal :
            local_subpath_morphism O hO hinter S γ
                (w 0)
                (w (Fin.last N))
                (u (Fin.last 0))
                hsub ≍
              local_subpath_morphism O hO hinter S γ
                (t (Fin.last 0).castSucc)
                (t (Fin.last 0).succ)
                (u (Fin.last 0))
                (hu (Fin.last 0)) := by
          -- The shared tuple and the explicit tuple have the same global endpoints.
          exact
            local_subpath_morphism_heq_of_eq
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := γ)
              (a := w 0)
              (a' := t (Fin.last 0).castSucc)
              (b := w (Fin.last N))
              (b' := t (Fin.last 0).succ)
              (i := u (Fin.last 0))
              (i' := u (Fin.last 0))
              hstart
              hend
              rfl
              (hsub := hsub)
              (hsub' := hu (Fin.last 0))
        have ht :
            subdivision_morphism O hO hinter S γ
                (t := t)
                (u := u)
                hu =
              local_subpath_morphism O hO hinter S γ
                (t (Fin.last 0).castSucc)
                (t (Fin.last 0).succ)
                (u (Fin.last 0))
                (hu (Fin.last 0)) := by
          -- With one explicit interval, the recursive composite is already the terminal segment.
          simp [subdivision_morphism]
        exact hwcollapse.heq.trans (hlocal.trans ht.heq.symm)
  | succ m ih =>
      -- Route correction: the semantic sigma-block collapse is already available, so the
      -- successor case is reduced to a single terminal-cutpoint reassembly step.
      exact
        subdivision_morphism_eq_of_cutpoint_blocks_succ_step
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (w := w)
          (hwmono := hwmono)
          (t := t)
          (hn := hn)
          (u := u)
          (hu := hu)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          ih

/-- Helper for Theorem 2.7.1: the chosen subdivision of a path can be replaced by any explicit
endpoint-normalized subordinate subdivision of the same path. -/
theorem chosen_subdivision_morphism_eq_explicit_subdivision
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (hmono : Monotone t)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hx : γ (t 0) = x)
    (hy : γ (t (Fin.last n)) = y) :
    chosen_subdivision_morphism O hO hinter S γ =
      normalized_subdivision_morphism O hO hinter S γ t u hu hx hy := by
  -- Route correction: the explicit subdivision must really be endpoint-normalized by the
  -- breakpoint tuple itself; endpoint equalities `γ (t 0) = x` and `γ (t (last n)) = y` alone
  -- are not enough because they would allow false `n = 0` loop cases.
  obtain ⟨N, w, vChosen, hvChosen, href_chosen, hwmono, hw0, hw1, hcontains⟩ :=
    chosen_explicit_subdivision_common_refinement
      (hO := hO)
      (γ := γ)
      (t := t)
      (hn := hn)
      (ht0 := ht0)
      (ht1 := ht1)
      (hmono := hmono)
      (u := u)
      (hu := hu)
  have hchosen_raw :
      chosen_subdivision_morphism O hO hinter S γ ≍
        subdivision_morphism O hO hinter S γ
          (t := chosen_subdivision_points O hO γ)
          (u := chosen_subdivision_labels O hO γ)
          (chosen_subdivision_subordinate O hO γ) := by
    -- Remove the outer endpoint transports from the chosen representative before comparing
    -- subdivision composites on a common tuple.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (chosen_subdivision_morphism O hO hinter S γ)
        (subdivision_morphism O hO hinter S γ
          (t := chosen_subdivision_points O hO γ)
          (u := chosen_subdivision_labels O hO γ)
          (chosen_subdivision_subordinate O hO γ))
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (chosen_subdivision_source_eq O hO γ).symm)
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (chosen_subdivision_target_eq O hO γ).symm)).1 rfl
  have hexplicit_raw :
      normalized_subdivision_morphism O hO hinter S γ t u hu hx hy ≍
        subdivision_morphism O hO hinter S γ
          (t := t)
          (u := u)
          hu := by
    -- The explicit endpoint transports can be stripped in exactly the same way.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (normalized_subdivision_morphism O hO hinter S γ t u hu hx hy)
        (subdivision_morphism O hO hinter S γ
          (t := t)
          (u := u)
          hu)
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hx).symm
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hy).symm).1 rfl
  have hchosen_ref :
      subdivision_morphism O hO hinter S γ
          (t := w)
          (u := vChosen)
          hvChosen ≍
        subdivision_morphism O hO hinter S γ
          (t := chosen_subdivision_points O hO γ)
          (u := chosen_subdivision_labels O hO γ)
          (chosen_subdivision_subordinate O hO γ) := by
  -- Send the chosen subdivision to the literal shared tuple produced above.
    exact subdivision_morphism_heq_of_refinement hO hinter S γ href_chosen
  have hshared_explicit :
      subdivision_morphism O hO hinter S γ
          (t := w)
          (u := vChosen)
          hvChosen ≍
        subdivision_morphism O hO hinter S γ
          (t := t)
          (u := u)
          hu := by
    obtain ⟨sigma, hsigma0, hsigma1, hsigmamono, hsigmaeq⟩ :=
      shared_tuple_breakpoint_cutpoints
        (t := t)
        (w := w)
        (hn := hn)
        (ht0 := ht0)
        (ht1 := ht1)
        (hw0 := hw0)
        (hw1 := hw1)
        (htmono := hmono)
        (hwmono := hwmono)
        (hcontains := hcontains)
    let vExplicit :=
      shared_tuple_cutpoint_labels u hn sigma hsigma0 hsigma1 hsigmamono
    have hvExplicit :
        ∀ k : Fin N, Set.range (γ.subpath (w k.castSucc) (w k.succ)) ⊆ O (vExplicit k) := by
      -- Replace the unstable owner labels by the canonical cutpoint-block labels determined by
      -- `sigma`.
      simpa [vExplicit] using
        shared_tuple_cutpoint_block_subordinate
          (γ := γ)
          (t := t)
          (w := w)
          (hn := hn)
          (sigma := sigma)
          (hsigma0 := hsigma0)
          (hsigma1 := hsigma1)
          (hsigmamono := hsigmamono)
          (hsigmaeq := hsigmaeq)
          (hwmono := hwmono)
          (u := u)
          (hu := hu)
    have hshared_labels :
        subdivision_morphism O hO hinter S γ
            (t := w)
            (u := vChosen)
            hvChosen =
          subdivision_morphism O hO hinter S γ
            (t := w)
            (u := vExplicit)
            hvExplicit := by
      -- On the literal shared tuple `w`, only the breakpoint geometry matters; once the explicit
      -- cutpoint-block labels are in place, the chosen labels can be replaced segmentwise.
      exact subdivision_morphism_eq_of_same_points hO hinter S γ w vChosen vExplicit hvChosen hvExplicit
    rw [hshared_labels]
    -- Collapse the canonically labelled shared tuple block-by-block along the cutpoints recorded
    -- by `sigma`.
    exact
      subdivision_morphism_eq_of_cutpoint_blocks
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (t := t)
        (w := w)
        (hn := hn)
        (u := u)
        (hu := hu)
        (sigma := sigma)
        (hsigma0 := hsigma0)
        (hsigma1 := hsigma1)
        (hsigmamono := hsigmamono)
        (hsigmaeq := hsigmaeq)
        (hwmono := hwmono)
  have hcompare :
      chosen_subdivision_morphism O hO hinter S γ ≍
        normalized_subdivision_morphism O hO hinter S γ t u hu hx hy := by
    -- Compare both representatives only after they have both been normalized to the same literal
    -- breakpoint tuple; the remaining explicit-side step is now isolated in `hshared_explicit`.
    exact
      hchosen_raw.trans <|
        hchosen_ref.symm.trans <|
          hshared_explicit.trans hexplicit_raw.symm
  exact eq_of_heq hcompare

/-- Helper for Theorem 2.7.1: on the left half of the unit interval, the concatenated path
evaluates exactly like the corresponding rescaled subpath of `γ`. -/
theorem trans_subpath_left_apply_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (a : ℝ) ≤ 1 / 2)
    (hb : (b : ℝ) ≤ 1 / 2)
    (s : I) :
    (γ.trans δ).subpath a b s =
      γ.subpath
        ⟨2 * a, (mul_pos_mem_iff zero_lt_two).2 ⟨a.2.1, ha⟩⟩
        ⟨2 * b, (mul_pos_mem_iff zero_lt_two).2 ⟨b.2.1, hb⟩⟩ s := by
  -- On the left half, `Path.trans_apply` always evaluates through `γ`, so the two formulas agree
  -- pointwise after rescaling.
  have hs : ((1 - (s : ℝ)) * a + (s : ℝ) * b : ℝ) ≤ 1 / 2 := by
    nlinarith [ha, hb, s.2.1, s.2.2]
  have hs' : ((1 - (s : ℝ)) * a + (s : ℝ) * b : ℝ) ≤ (2⁻¹ : ℝ) := by
    simpa using hs
  have hcombo :
      (⟨2 * ((1 - (s : ℝ)) * a + (s : ℝ) * b),
          (mul_pos_mem_iff zero_lt_two).2 ⟨by
            nlinarith [a.2.1, b.2.1, s.2.1, s.2.2], hs⟩⟩ : I) =
        Set.Icc.convexCombo
          ⟨2 * a, (mul_pos_mem_iff zero_lt_two).2 ⟨a.2.1, ha⟩⟩
          ⟨2 * b, (mul_pos_mem_iff zero_lt_two).2 ⟨b.2.1, hb⟩⟩
          s := by
    ext
    simp [Set.Icc.coe_convexCombo]
    ring
  simpa [Path.subpath, hs', hcombo] using
    (Path.trans_apply γ δ (Set.Icc.convexCombo a b s))

/-- Helper for Theorem 2.7.1: the midpoint of `γ.trans δ` is the common endpoint of `γ` and `δ`.
-/
theorem trans_midpoint_eq
    {x y z : X} (γ : Path x y) (δ : Path y z) :
    (γ.trans δ) (⟨(1 : ℝ) / 2, by norm_num⟩ : I) = y := by
  -- At the midpoint the left branch of `Path.trans_apply` is selected, so the value is `γ 1`.
  simpa [Path.trans_apply]

/-- Helper for Theorem 2.7.1: on the right half of the unit interval, the concatenated path
evaluates like the corresponding rescaled subpath of `δ`, with the midpoint case normalized to the
common endpoint. -/
theorem trans_subpath_right_apply_eq_or_midpoint
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (1 / 2 : ℝ) ≤ a)
    (hb : (1 / 2 : ℝ) ≤ b)
    (s : I) :
    (γ.trans δ).subpath a b s =
      δ.subpath
        ⟨2 * a - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, a.2.2⟩⟩
        ⟨2 * b - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, b.2.2⟩⟩ s := by
  let c : I := Set.Icc.convexCombo a b s
  let a' : I := ⟨2 * a - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, a.2.2⟩⟩
  let b' : I := ⟨2 * b - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, b.2.2⟩⟩
  have hc_lower : (1 / 2 : ℝ) ≤ c := by
    -- Convex combinations of right-half points stay on the right half as well.
    change (1 / 2 : ℝ) ≤ ((1 - (s : ℝ)) * a + (s : ℝ) * b)
    nlinarith [ha, hb, s.2.1, s.2.2]
  have hcombo :
      (⟨2 * c - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨hc_lower, c.2.2⟩⟩ : I) =
        Set.Icc.convexCombo a' b' s := by
    -- Rescaling `[1 / 2, 1]` back to `[0, 1]` commutes with the affine interpolation defining the
    -- subpath.
    ext
    simp [Set.Icc.coe_convexCombo, a', b', c]
    ring
  by_cases hc : (c : ℝ) ≤ 1 / 2
  · have hc_eq_real : (c : ℝ) = 1 / 2 := by
      linarith
    have hmid : (γ.trans δ) c = y := by
      -- If the interpolated point lands exactly at the midpoint, the two path pieces agree there.
      have hc_eq : c = (⟨(1 : ℝ) / 2, by norm_num⟩ : I) := by
        ext
        simpa using hc_eq_real
      rw [hc_eq]
      simpa using trans_midpoint_eq γ δ
    have hparam_zero :
        (⟨2 * c - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨hc_lower, c.2.2⟩⟩ : I) = 0 := by
      -- The right-half rescaling sends the midpoint to `0`.
      ext
      change 2 * (c : ℝ) - 1 = 0
      nlinarith [hc_eq_real]
    calc
      (γ.trans δ).subpath a b s = (γ.trans δ) c := by
        rfl
      _ = y := hmid
      _ = δ 0 := by
        simp
      _ = δ (⟨2 * c - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨hc_lower, c.2.2⟩⟩ : I) := by
        rw [hparam_zero]
      _ = δ (Set.Icc.convexCombo a' b' s) := by
        rw [hcombo]
      _ = δ.subpath a' b' s := by
        rfl
  · have hc' : ¬ (c : ℝ) ≤ (2⁻¹ : ℝ) := by
      simpa using hc
    have htrans :
        (γ.trans δ) c =
          δ (⟨2 * c - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨hc_lower, c.2.2⟩⟩ : I) := by
      -- Away from the midpoint, `Path.trans_apply` is already on the `δ` branch.
      rw [Path.trans_apply]
      simp [hc']
    calc
      (γ.trans δ).subpath a b s = (γ.trans δ) c := by
        rfl
      _ = δ (⟨2 * c - 1,
            unitInterval.two_mul_sub_one_mem_iff.2 ⟨hc_lower, c.2.2⟩⟩ : I) := htrans
      _ = δ (Set.Icc.convexCombo a' b' s) := by
        rw [hcombo]
      _ = δ.subpath a' b' s := by
        rfl

/-- Helper for Theorem 2.7.1: a left-half subpath of `γ.trans δ` has exactly the same image as
the corresponding rescaled subpath of `γ`. -/
theorem trans_subpath_left_range_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (a : ℝ) ≤ 1 / 2)
    (hb : (b : ℝ) ≤ 1 / 2) :
    Set.range ((γ.trans δ).subpath a b) =
      Set.range
        (γ.subpath
          ⟨2 * a, (mul_pos_mem_iff zero_lt_two).2 ⟨a.2.1, ha⟩⟩
          ⟨2 * b, (mul_pos_mem_iff zero_lt_two).2 ⟨b.2.1, hb⟩⟩) := by
  -- Compare the two ranges pointwise using the already-proved left-half evaluation formula.
  ext p
  constructor
  · intro hp
    rcases hp with ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    simpa using (trans_subpath_left_apply_eq γ δ a b ha hb s).symm
  · intro hp
    rcases hp with ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    simpa using trans_subpath_left_apply_eq γ δ a b ha hb s

/-- Helper for Theorem 2.7.1: any cover-subordinate left-half segment of `γ` yields the
corresponding cover-subordinate left-half segment of `γ.trans δ`. -/
theorem trans_subpath_left_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (a : ℝ) ≤ 1 / 2)
    (hb : (b : ℝ) ≤ 1 / 2)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub :
      Set.range
          (γ.subpath
            ⟨2 * a, (mul_pos_mem_iff zero_lt_two).2 ⟨a.2.1, ha⟩⟩
            ⟨2 * b, (mul_pos_mem_iff zero_lt_two).2 ⟨b.2.1, hb⟩⟩) ⊆
        O i) :
    Set.range ((γ.trans δ).subpath a b) ⊆ O i := by
  -- Rewrite the concatenated left-half segment to the rescaled `γ`-segment and reuse `hsub`.
  rw [trans_subpath_left_range_eq γ δ a b ha hb]
  exact hsub

/-- Helper for Theorem 2.7.1: a right-half subpath of `γ.trans δ` has exactly the same image as
the corresponding rescaled subpath of `δ`. -/
theorem trans_subpath_right_range_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (1 / 2 : ℝ) ≤ a)
    (hb : (1 / 2 : ℝ) ≤ b) :
    Set.range ((γ.trans δ).subpath a b) =
      Set.range
        (δ.subpath
          ⟨2 * a - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, a.2.2⟩⟩
          ⟨2 * b - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, b.2.2⟩⟩) := by
  -- The same pointwise comparison works on the right half after the affine reparameterization of
  -- `δ`.
  ext p
  constructor
  · intro hp
    rcases hp with ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    simpa using (trans_subpath_right_apply_eq_or_midpoint γ δ a b ha hb s).symm
  · intro hp
    rcases hp with ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    simpa using trans_subpath_right_apply_eq_or_midpoint γ δ a b ha hb s

/-- Helper for Theorem 2.7.1: any cover-subordinate right-half segment of `δ` yields the
corresponding cover-subordinate right-half segment of `γ.trans δ`. -/
theorem trans_subpath_right_range_subset
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a b : I)
    (ha : (1 / 2 : ℝ) ≤ a)
    (hb : (1 / 2 : ℝ) ≤ b)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub :
      Set.range
          (δ.subpath
            ⟨2 * a - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, a.2.2⟩⟩
            ⟨2 * b - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, b.2.2⟩⟩) ⊆
        O i) :
    Set.range ((γ.trans δ).subpath a b) ⊆ O i := by
  -- Rewrite the concatenated right-half segment to the rescaled `δ`-segment and reuse `hsub`.
  rw [trans_subpath_right_range_eq γ δ a b ha hb]
  exact hsub

/-- Helper for Theorem 2.7.1: halving a point of the unit interval stays inside the unit interval.
-/
theorem midpoint_left_half_mem (a : I) : 0 ≤ (a : ℝ) / 2 ∧ (a : ℝ) / 2 ≤ 1 := by
  constructor <;> nlinarith [a.2.1, a.2.2]

/-- Helper for Theorem 2.7.1: rescaling a point of `I` to the left half `[0, 1 / 2]`. -/
noncomputable def midpoint_left_half (a : I) : I :=
  ⟨(a : ℝ) / 2, midpoint_left_half_mem a⟩

/-- Helper for Theorem 2.7.1: shifting a point of the unit interval to the right half
`[1 / 2, 1]`. -/
theorem midpoint_right_half_mem (a : I) :
    0 ≤ ((a : ℝ) + 1) / 2 ∧ ((a : ℝ) + 1) / 2 ≤ 1 := by
  constructor <;> nlinarith [a.2.1, a.2.2]

/-- Helper for Theorem 2.7.1: rescaling a point of `I` to the right half `[1 / 2, 1]`. -/
noncomputable def midpoint_right_half (a : I) : I :=
  ⟨((a : ℝ) + 1) / 2, midpoint_right_half_mem a⟩

/-- Helper for Theorem 2.7.1: when a glued breakpoint lies on the right half, subtracting the
left-length recovers the corresponding right-hand breakpoint index. -/
theorem midpoint_glued_right_point_index_lt
    {n m : ℕ}
    (k : Fin (n + m + 1))
    (hk : ¬ k.1 < n) :
    k.1 - n < m + 1 := by
  have hklt : k.1 < n + m + 1 := k.is_lt
  omega

/-- Helper for Theorem 2.7.1: the right-half point index used by the midpoint-glued subdivision.
-/
noncomputable def midpoint_glued_right_point_index
    {n m : ℕ}
    (k : Fin (n + m + 1))
    (hk : ¬ k.1 < n) :
    Fin (m + 1) :=
  ⟨k.1 - n, midpoint_glued_right_point_index_lt k hk⟩

/-- Helper for Theorem 2.7.1: when a glued interval lies on the right half, subtracting the
left-length recovers the corresponding right-hand label index. -/
theorem midpoint_glued_right_label_index_lt
    {n m : ℕ}
    (k : Fin (n + m))
    (hk : ¬ k.1 < n) :
    k.1 - n < m := by
  have hklt : k.1 < n + m := k.is_lt
  omega

/-- Helper for Theorem 2.7.1: the right-half label index used by the midpoint-glued subdivision.
-/
noncomputable def midpoint_glued_right_label_index
    {n m : ℕ}
    (k : Fin (n + m))
    (hk : ¬ k.1 < n) :
    Fin m :=
  ⟨k.1 - n, midpoint_glued_right_label_index_lt k hk⟩

/-- Helper for Theorem 2.7.1: the explicit breakpoint tuple obtained by gluing the subdivision of
`γ` to the subdivision of `δ` at the midpoint. -/
noncomputable def midpoint_glued_points
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I) :
    Fin (n + m + 1) → I := fun k ↦
  if hk : k.1 < n then
    midpoint_left_half (t ⟨k.1, Nat.lt_succ_of_lt hk⟩)
  else
    midpoint_right_half (t' (midpoint_glued_right_point_index k hk))

/-- Helper for Theorem 2.7.1: the explicit cover-label family on the midpoint-glued subdivision.
-/
noncomputable def midpoint_glued_labels
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {n m : ℕ}
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O) :
    Fin (n + m) → TopologicalSpace.IsOpenCover.Index O := fun k ↦
  if hk : k.1 < n then
    u ⟨k.1, hk⟩
  else
    u' (midpoint_glued_right_label_index k hk)

/-- Helper for Theorem 2.7.1: the midpoint-glued breakpoint tuple starts at `0`. -/
theorem midpoint_glued_points_zero
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0) :
    midpoint_glued_points t t' 0 = 0 := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  ext
  simp [midpoint_glued_points, midpoint_left_half, ht0, hpos]

/-- Helper for Theorem 2.7.1: the midpoint-glued breakpoint tuple ends at `1`. -/
theorem midpoint_glued_points_last
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (ht'1 : t' (Fin.last m) = 1) :
    midpoint_glued_points t t' (Fin.last (n + m)) = 1 := by
  have hnot : ¬ (Fin.last (n + m)).1 < n := by
    simp [Fin.last]
  have hlast :
      midpoint_glued_right_point_index (Fin.last (n + m)) hnot = Fin.last m := by
    ext
    simp [midpoint_glued_right_point_index, Fin.last]
  rw [show midpoint_glued_points t t' (Fin.last (n + m)) =
      midpoint_right_half (t' (midpoint_glued_right_point_index (Fin.last (n + m)) hnot)) by
      simp [midpoint_glued_points, hnot]]
  rw [hlast, ht'1]
  ext
  simp [midpoint_right_half]

/-- Helper for Theorem 2.7.1: the midpoint-glued breakpoint tuple remains monotone. -/
theorem midpoint_glued_points_monotone
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (htmono : Monotone t)
    (ht'mono : Monotone t') :
    Monotone (midpoint_glued_points t t') := by
  intro a b hab
  change (((midpoint_glued_points t t' a : I) : ℝ)) ≤
      (((midpoint_glued_points t t' b : I) : ℝ))
  by_cases ha : a.1 < n
  · by_cases hb : b.1 < n
    · let ia : Fin (n + 1) := ⟨a.1, Nat.lt_succ_of_lt ha⟩
      let ib : Fin (n + 1) := ⟨b.1, Nat.lt_succ_of_lt hb⟩
      have hit : t ia ≤ t ib := by
        exact htmono (by simpa [ia, ib] using hab)
      have hscaled : (((t ia : I) : ℝ) / 2) ≤ (((t ib : I) : ℝ) / 2) := by
        exact div_le_div_of_nonneg_right hit (by positivity)
      simpa [midpoint_glued_points, ha, hb, midpoint_left_half, ia, ib] using hscaled
    · have hleft : (((midpoint_glued_points t t' a : I) : ℝ)) ≤ 1 / 2 := by
        let ia : Fin (n + 1) := ⟨a.1, Nat.lt_succ_of_lt ha⟩
        have hscaled : (((t ia : I) : ℝ) / 2) ≤ 1 / 2 := by
          nlinarith [(t ia).2.2]
        simpa [midpoint_glued_points, ha, midpoint_left_half, ia] using hscaled
      have hright : (1 / 2 : ℝ) ≤ (((midpoint_glued_points t t' b : I) : ℝ)) := by
        let jb : Fin (m + 1) := midpoint_glued_right_point_index b hb
        have hscaled : (1 / 2 : ℝ) ≤ ((((t' jb : I) : ℝ) + 1) / 2) := by
          nlinarith [(t' jb).2.1]
        simpa [midpoint_glued_points, hb, midpoint_right_half, jb] using hscaled
      nlinarith
  · have hb' : ¬ b.1 < n := by
      omega
    let ia : Fin (m + 1) := midpoint_glued_right_point_index a ha
    let ib : Fin (m + 1) := midpoint_glued_right_point_index b hb'
    have habNat : a.1 ≤ b.1 := hab
    have habSub : a.1 - n ≤ b.1 - n := Nat.sub_le_sub_right habNat n
    have hit : t' ia ≤ t' ib := by
      exact ht'mono (by simpa [ia, ib, midpoint_glued_right_point_index] using habSub)
    have hscaled : ((((t' ia : I) : ℝ) + 1) / 2) ≤ ((((t' ib : I) : ℝ) + 1) / 2) := by
      nlinarith [show ((t' ia : I) : ℝ) ≤ ((t' ib : I) : ℝ) from hit]
    simpa [midpoint_glued_points, ha, hb', midpoint_right_half, ia, ib] using hscaled

/-- Helper for Theorem 2.7.1: each interval of the midpoint-glued tuple stays inside the cover
member inherited from the corresponding interval of `γ` or `δ`. -/
theorem midpoint_glued_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (ht1 : t (Fin.last n) = 1)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (t' : Fin (m + 1) → I)
    (ht'0 : t' 0 = 0)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)) :
    ∀ k : Fin (n + m),
      Set.range
          (((γ.trans δ).subpath
            (midpoint_glued_points t t' k.castSucc)
            (midpoint_glued_points t t' k.succ))) ⊆
        O (midpoint_glued_labels u u' k) := by
  intro k
  by_cases hk : k.1 < n
  · let kLeft : Fin n := ⟨k.1, hk⟩
    have hsCast :
        midpoint_glued_points t t' k.castSucc =
          midpoint_left_half (t kLeft.castSucc) := by
      simpa [midpoint_glued_points, kLeft] using
        (show midpoint_glued_points t t' k.castSucc =
            midpoint_left_half (t ⟨k.1, Nat.lt_succ_of_lt hk⟩) by
          simp [midpoint_glued_points, hk])
    have hsSucc :
        midpoint_glued_points t t' k.succ =
          midpoint_left_half (t kLeft.succ) := by
      by_cases hkSuccNat : k.1 + 1 < n
      · simpa [midpoint_glued_points, kLeft] using
          (show midpoint_glued_points t t' k.succ =
              midpoint_left_half (t ⟨k.1 + 1, Nat.lt_succ_of_lt hkSuccNat⟩) by
            simp [midpoint_glued_points, hkSuccNat])
      · have hkEq : k.1 + 1 = n := by omega
        have hkLast : kLeft.succ = Fin.last n := by
          ext
          simp [kLeft, hkEq, Fin.last]
        have hkSuccNat' : ¬ k.succ.1 < n := by
          simpa using hkSuccNat
        have hkRightZero :
            midpoint_glued_right_point_index k.succ hkSuccNat' = 0 := by
          ext
          simp [midpoint_glued_right_point_index, hkEq]
        have hsSuccRaw :
            midpoint_glued_points t t' k.succ =
              midpoint_right_half (t' (midpoint_glued_right_point_index k.succ hkSuccNat')) := by
          change
            (if h : k.1 + 1 < n then
                midpoint_left_half (t ⟨k.1 + 1, Nat.lt_succ_of_lt h⟩)
              else
                midpoint_right_half (t' (midpoint_glued_right_point_index k.succ hkSuccNat'))) =
              midpoint_right_half (t' (midpoint_glued_right_point_index k.succ hkSuccNat'))
          simp [hkSuccNat]
        rw [hsSuccRaw, hkRightZero, hkLast, ht1, ht'0]
        ext
        simp [midpoint_left_half, midpoint_right_half]
    have ha : ((midpoint_glued_points t t' k.castSucc : I) : ℝ) ≤ 1 / 2 := by
      have hscaled : (((t kLeft.castSucc : I) : ℝ) / 2) ≤ 1 / 2 := by
        nlinarith [(t kLeft.castSucc).2.2]
      simpa [hsCast, midpoint_left_half] using hscaled
    have hb : ((midpoint_glued_points t t' k.succ : I) : ℝ) ≤ 1 / 2 := by
      have hscaled : (((t kLeft.succ : I) : ℝ) / 2) ≤ 1 / 2 := by
        nlinarith [(t kLeft.succ).2.2]
      simpa [hsSucc, midpoint_left_half] using hscaled
    have hstart :
        (⟨2 * midpoint_glued_points t t' k.castSucc,
            (mul_pos_mem_iff zero_lt_two).2
              ⟨(midpoint_glued_points t t' k.castSucc).2.1, ha⟩⟩ : I) =
          t kLeft.castSucc := by
      ext
      simp [hsCast, midpoint_left_half]
      ring
    have hend :
        (⟨2 * midpoint_glued_points t t' k.succ,
            (mul_pos_mem_iff zero_lt_two).2
              ⟨(midpoint_glued_points t t' k.succ).2.1, hb⟩⟩ : I) =
          t kLeft.succ := by
      ext
      simp [hsSucc, midpoint_left_half]
      ring
    have hsegment :
        Set.range
            (γ.subpath
              ⟨2 * midpoint_glued_points t t' k.castSucc,
                (mul_pos_mem_iff zero_lt_two).2
                  ⟨(midpoint_glued_points t t' k.castSucc).2.1, ha⟩⟩
              ⟨2 * midpoint_glued_points t t' k.succ,
                (mul_pos_mem_iff zero_lt_two).2
                  ⟨(midpoint_glued_points t t' k.succ).2.1, hb⟩⟩) ⊆
          O (u kLeft) := by
      simpa [hstart, hend] using hu kLeft
    -- The left block of the glued tuple is just the left subdivision scaled into `[0, 1 / 2]`.
    simpa [midpoint_glued_labels, hk, kLeft] using
      trans_subpath_left_range_subset γ δ
        (midpoint_glued_points t t' k.castSucc)
        (midpoint_glued_points t t' k.succ)
        ha
        hb
        hsegment
  · let kRight : Fin m := midpoint_glued_right_label_index k hk
    have hkCastSucc : ¬ k.castSucc.1 < n := by
      simpa using hk
    have hsCastRaw :
        midpoint_glued_points t t' k.castSucc =
          midpoint_right_half (t' (midpoint_glued_right_point_index k.castSucc hkCastSucc)) := by
      simp [midpoint_glued_points, hk, hkCastSucc]
    have hsCast :
        midpoint_glued_points t t' k.castSucc =
          midpoint_right_half (t' kRight.castSucc) := by
      simpa [midpoint_glued_points, kRight, midpoint_glued_right_label_index] using
        hsCastRaw
    have hsSucc :
        midpoint_glued_points t t' k.succ =
          midpoint_right_half (t' kRight.succ) := by
      have hkSuccNat : ¬ k.1 + 1 < n := by
        omega
      have hkRightSucc :
          midpoint_glued_right_point_index k.succ hkSuccNat = kRight.succ := by
        ext
        simp [midpoint_glued_right_point_index, kRight, midpoint_glued_right_label_index]
        omega
      have hsSuccRaw :
          midpoint_glued_points t t' k.succ =
            midpoint_right_half
              (t' (midpoint_glued_right_point_index k.succ hkSuccNat)) := by
        simp [midpoint_glued_points, hkSuccNat]
      simpa [hkRightSucc] using hsSuccRaw
    have ha : (1 / 2 : ℝ) ≤ ((midpoint_glued_points t t' k.castSucc : I) : ℝ) := by
      have hscaled : (1 / 2 : ℝ) ≤ ((((t' kRight.castSucc : I) : ℝ) + 1) / 2) := by
        nlinarith [(t' kRight.castSucc).2.1]
      simpa [hsCast, midpoint_right_half] using hscaled
    have hb : (1 / 2 : ℝ) ≤ ((midpoint_glued_points t t' k.succ : I) : ℝ) := by
      have hscaled : (1 / 2 : ℝ) ≤ ((((t' kRight.succ : I) : ℝ) + 1) / 2) := by
        nlinarith [(t' kRight.succ).2.1]
      simpa [hsSucc, midpoint_right_half] using hscaled
    have hstart :
        (⟨2 * midpoint_glued_points t t' k.castSucc - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨ha, (midpoint_glued_points t t' k.castSucc).2.2⟩⟩ : I) =
          t' kRight.castSucc := by
      ext
      simp [hsCast, midpoint_right_half]
      ring
    have hend :
        (⟨2 * midpoint_glued_points t t' k.succ - 1,
            unitInterval.two_mul_sub_one_mem_iff.2
              ⟨hb, (midpoint_glued_points t t' k.succ).2.2⟩⟩ : I) =
          t' kRight.succ := by
      ext
      simp [hsSucc, midpoint_right_half]
      ring
    have hsegment :
        Set.range
            (δ.subpath
              ⟨2 * midpoint_glued_points t t' k.castSucc - 1,
                unitInterval.two_mul_sub_one_mem_iff.2
                  ⟨ha, (midpoint_glued_points t t' k.castSucc).2.2⟩⟩
              ⟨2 * midpoint_glued_points t t' k.succ - 1,
                unitInterval.two_mul_sub_one_mem_iff.2
                  ⟨hb, (midpoint_glued_points t t' k.succ).2.2⟩⟩) ⊆
          O (u' kRight) := by
      simpa [hstart, hend] using hu' kRight
    -- The right block of the glued tuple is the right subdivision rescaled from `[0, 1]` to
    -- `[1 / 2, 1]`.
    simpa [midpoint_glued_labels, hk, kRight] using
      trans_subpath_right_range_subset γ δ
        (midpoint_glued_points t t' k.castSucc)
        (midpoint_glued_points t t' k.succ)
        ha
        hb
        hsegment

/-- Helper for Theorem 2.7.1: the midpoint-glued subdivision starts at the source of
`γ.trans δ`. -/
theorem midpoint_glued_source_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0) :
    (γ.trans δ) (midpoint_glued_points t t' 0) = x := by
  rw [midpoint_glued_points_zero t t' hn ht0]
  simp

/-- Helper for Theorem 2.7.1: the midpoint-glued subdivision ends at the target of
`γ.trans δ`. -/
theorem midpoint_glued_target_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (ht'1 : t' (Fin.last m) = 1) :
    (γ.trans δ) (midpoint_glued_points t t' (Fin.last (n + m))) = z := by
  rw [midpoint_glued_points_last t t' ht'1]
  simp

/-- Helper for Theorem 2.7.1: the cutpoint of the midpoint-glued tuple separating the left and
right halves. -/
noncomputable def midpoint_glued_cutpoint (n m : ℕ) : Fin (n + m + 1) :=
  ⟨n, Nat.lt_add_of_pos_right (Nat.succ_pos m)⟩

@[simp] theorem midpoint_glued_cutpoint_val (n m : ℕ) :
    (midpoint_glued_cutpoint n m).1 = n := rfl

/-- Helper for Theorem 2.7.1: every interval of the left-half-scaled breakpoint tuple for `γ`
already lies in the same cover member when viewed inside `γ.trans δ`. -/
theorem midpoint_left_half_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    ∀ k : Fin n,
      Set.range
          (((γ.trans δ).subpath
            (midpoint_left_half (t k.castSucc))
            (midpoint_left_half (t k.succ)))) ⊆
        O (u k) := by
  intro k
  have hleft : (((midpoint_left_half (t k.castSucc) : I) : ℝ)) ≤ 1 / 2 := by
    change (((t k.castSucc : I) : ℝ) / 2) ≤ 1 / 2
    nlinarith [(t k.castSucc).2.2]
  have hright : (((midpoint_left_half (t k.succ) : I) : ℝ)) ≤ 1 / 2 := by
    change (((t k.succ : I) : ℝ) / 2) ≤ 1 / 2
    nlinarith [(t k.succ).2.2]
  have hstart :
      (⟨2 * midpoint_left_half (t k.castSucc),
          (mul_pos_mem_iff zero_lt_two).2
            ⟨(midpoint_left_half (t k.castSucc)).2.1, hleft⟩⟩ : I) =
        t k.castSucc := by
    ext
    simp [midpoint_left_half]
    ring
  have hend :
      (⟨2 * midpoint_left_half (t k.succ),
          (mul_pos_mem_iff zero_lt_two).2
            ⟨(midpoint_left_half (t k.succ)).2.1, hright⟩⟩ : I) =
        t k.succ := by
    ext
    simp [midpoint_left_half]
    ring
  -- The left-half rescaling matches the original `γ`-subpath interval-by-interval.
  exact
    trans_subpath_left_range_subset γ δ
      (midpoint_left_half (t k.castSucc))
      (midpoint_left_half (t k.succ))
      hleft
      hright
      (by simpa [hstart, hend] using hu k)

/-- Helper for Theorem 2.7.1: every interval of the right-half-scaled breakpoint tuple for `δ`
already lies in the same cover member when viewed inside `γ.trans δ`. -/
theorem midpoint_right_half_subordinate
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {m : ℕ}
    (t' : Fin (m + 1) → I)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)) :
    ∀ k : Fin m,
      Set.range
          (((γ.trans δ).subpath
            (midpoint_right_half (t' k.castSucc))
            (midpoint_right_half (t' k.succ)))) ⊆
        O (u' k) := by
  intro k
  have hleft : (1 / 2 : ℝ) ≤ (((midpoint_right_half (t' k.castSucc) : I) : ℝ)) := by
    change (1 / 2 : ℝ) ≤ ((((t' k.castSucc : I) : ℝ) + 1) / 2)
    nlinarith [(t' k.castSucc).2.1]
  have hright : (1 / 2 : ℝ) ≤ (((midpoint_right_half (t' k.succ) : I) : ℝ)) := by
    change (1 / 2 : ℝ) ≤ ((((t' k.succ : I) : ℝ) + 1) / 2)
    nlinarith [(t' k.succ).2.1]
  have hstart :
      (⟨2 * midpoint_right_half (t' k.castSucc) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨hleft, (midpoint_right_half (t' k.castSucc)).2.2⟩⟩ : I) =
        t' k.castSucc := by
    ext
    simp [midpoint_right_half]
    ring
  have hend :
      (⟨2 * midpoint_right_half (t' k.succ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨hright, (midpoint_right_half (t' k.succ)).2.2⟩⟩ : I) =
        t' k.succ := by
    ext
    simp [midpoint_right_half]
    ring
  -- The right-half rescaling matches the original `δ`-subpath interval-by-interval.
  exact
    trans_subpath_right_range_subset γ δ
      (midpoint_right_half (t' k.castSucc))
      (midpoint_right_half (t' k.succ))
      hleft
      hright
      (by simpa [hstart, hend] using hu' k)

/-- Helper for Theorem 2.7.1: evaluating `γ.trans δ` at a left-half-scaled breakpoint of `γ`
recovers the original point of `γ`. -/
theorem trans_left_half_point_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a : I) :
    (γ.trans δ) (midpoint_left_half a) = γ a := by
  -- View the point evaluation as the degenerate left-half subpath formula at parameter `0`.
  have hleft : (((midpoint_left_half a : I) : ℝ)) ≤ 1 / 2 := by
    change (((a : I) : ℝ) / 2) ≤ 1 / 2
    nlinarith [a.2.2]
  have hparam :
      (⟨2 * midpoint_left_half a,
          (mul_pos_mem_iff zero_lt_two).2
            ⟨(midpoint_left_half a).2.1, hleft⟩⟩ : I) = a := by
    ext
    simp [midpoint_left_half]
    ring
  simpa [hparam] using
    trans_subpath_left_apply_eq γ δ
      (midpoint_left_half a)
      (midpoint_left_half a)
      hleft
      hleft
      0

/-- Helper for Theorem 2.7.1: evaluating `γ.trans δ` at a right-half-scaled breakpoint of `δ`
recovers the original point of `δ`. -/
theorem trans_right_half_point_eq
    {x y z : X} (γ : Path x y) (δ : Path y z)
    (a : I) :
    (γ.trans δ) (midpoint_right_half a) = δ a := by
  -- The right-half point formula is the degenerate right-half subpath formula at parameter `0`.
  have hright : (1 / 2 : ℝ) ≤ (((midpoint_right_half a : I) : ℝ)) := by
    change (1 / 2 : ℝ) ≤ ((((a : I) : ℝ) + 1) / 2)
    nlinarith [a.2.1]
  have hparam :
      (⟨2 * midpoint_right_half a - 1,
          unitInterval.two_mul_sub_one_mem_iff.2
            ⟨hright, (midpoint_right_half a).2.2⟩⟩ : I) = a := by
    ext
    simp [midpoint_right_half]
    ring
  simpa [hparam] using
    trans_subpath_right_apply_eq_or_midpoint γ δ
      (midpoint_right_half a)
      (midpoint_right_half a)
      hright
      hright
      0

/-- Helper for Theorem 2.7.1: subdividing `γ.trans δ` along the left-half-scaled tuple produces
the same raw subdivision composite as subdividing `γ` along the original tuple. -/
theorem subdivision_morphism_trans_left_half_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n : ℕ}
    (t : Fin (n + 1) → I)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k)) :
    subdivision_morphism O hO hinter S (γ.trans δ)
        (t := fun q : Fin (n + 1) ↦ midpoint_left_half (t q))
        (u := u)
        (midpoint_left_half_subordinate γ δ t u hu) ≍
      subdivision_morphism O hO hinter S γ
        (t := t)
        (u := u)
        hu := by
  induction n with
  | zero =>
      -- Both zero-step subdivision composites are identities once their source objects are
      -- identified by the left-half point evaluation.
      have hobj :
          chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t 0))) =
            chosen_cover_object O hO S (γ (t 0)) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_left_half_point_eq γ δ (t 0))
      exact
        (CategoryTheory.eqToHom_heq_id_dom
          (chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t 0))))
          (chosen_cover_object O hO S (γ (t 0)))
          hobj).symm.trans <|
          (CategoryTheory.eqToHom_heq_id_cod
            (chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t 0))))
            (chosen_cover_object O hO S (γ (t 0)))
            hobj)
  | succ n ih =>
      -- Unfold both recursive composites once, apply the induction hypothesis to the prefix, and
      -- compare the terminal local factors by pointwise equality of the rescaled subpaths.
      rw [subdivision_morphism, subdivision_morphism]
      have hprefix :
          subdivision_morphism O hO hinter S (γ.trans δ)
              (t := fun q : Fin (n + 1) ↦ midpoint_left_half (t q.castSucc))
              (u := fun q : Fin n ↦ u q.castSucc)
              (fun q : Fin n ↦ midpoint_left_half_subordinate γ δ t u hu q.castSucc) ≍
            subdivision_morphism O hO hinter S γ
              (t := fun q : Fin (n + 1) ↦ t q.castSucc)
              (u := fun q : Fin n ↦ u q.castSucc)
              (fun q : Fin n ↦ hu q.castSucc) := by
        simpa using
          ih
            (t := fun q : Fin (n + 1) ↦ t q.castSucc)
            (u := fun q : Fin n ↦ u q.castSucc)
            (hu := fun q : Fin n ↦ hu q.castSucc)
      have hlast :
          local_subpath_morphism O hO hinter S (γ.trans δ)
              (midpoint_left_half (t (Fin.castSucc (Fin.last n))))
              (midpoint_left_half (t (Fin.last (n + 1))))
              (u (Fin.last n))
              (midpoint_left_half_subordinate γ δ t u hu (Fin.last n)) ≍
            local_subpath_morphism O hO hinter S γ
              (t (Fin.castSucc (Fin.last n)))
              (t (Fin.last (n + 1)))
              (u (Fin.last n))
              (hu (Fin.last n)) := by
        have hleft :
            (((midpoint_left_half (t (Fin.castSucc (Fin.last n))) : I) : ℝ)) ≤ 1 / 2 := by
          change ((((t (Fin.castSucc (Fin.last n)) : I) : ℝ)) / 2) ≤ 1 / 2
          nlinarith [(t (Fin.castSucc (Fin.last n))).2.2]
        have hright :
            (((midpoint_left_half (t (Fin.last (n + 1))) : I) : ℝ)) ≤ 1 / 2 := by
          change ((((t (Fin.last (n + 1)) : I) : ℝ)) / 2) ≤ 1 / 2
          nlinarith [(t (Fin.last (n + 1))).2.2]
        have hstart :
            (⟨2 * midpoint_left_half (t (Fin.castSucc (Fin.last n))),
                (mul_pos_mem_iff zero_lt_two).2
                  ⟨(midpoint_left_half (t (Fin.castSucc (Fin.last n)))).2.1, hleft⟩⟩ : I) =
              t (Fin.castSucc (Fin.last n)) := by
          ext
          simp [midpoint_left_half]
          ring
        have hend :
            (⟨2 * midpoint_left_half (t (Fin.last (n + 1))),
                (mul_pos_mem_iff zero_lt_two).2
                  ⟨(midpoint_left_half (t (Fin.last (n + 1)))).2.1, hright⟩⟩ : I) =
              t (Fin.last (n + 1)) := by
          ext
          simp [midpoint_left_half]
          ring
        exact
          local_subpath_morphism_heq_of_subpath_eq
            (hO := hO)
            (hinter := hinter)
            (S := S)
            (γ := γ.trans δ)
            (a := midpoint_left_half (t (Fin.castSucc (Fin.last n))))
            (b := midpoint_left_half (t (Fin.last (n + 1))))
            (γ' := γ)
            (a' := t (Fin.castSucc (Fin.last n)))
            (b' := t (Fin.last (n + 1)))
            (i := u (Fin.last n))
            (hsub := midpoint_left_half_subordinate γ δ t u hu (Fin.last n))
            (hsub' := hu (Fin.last n))
            (fun s ↦ by
              calc
                (γ.trans δ).subpath
                    (midpoint_left_half (t (Fin.castSucc (Fin.last n))))
                    (midpoint_left_half (t (Fin.last (n + 1))))
                    s =
                  γ.subpath
                    ⟨2 * midpoint_left_half (t (Fin.castSucc (Fin.last n))),
                      (mul_pos_mem_iff zero_lt_two).2
                        ⟨(midpoint_left_half (t (Fin.castSucc (Fin.last n)))).2.1, hleft⟩⟩
                    ⟨2 * midpoint_left_half (t (Fin.last (n + 1))),
                      (mul_pos_mem_iff zero_lt_two).2
                        ⟨(midpoint_left_half (t (Fin.last (n + 1)))).2.1, hright⟩⟩
                    s := by
                  exact
                    trans_subpath_left_apply_eq γ δ
                      (midpoint_left_half (t (Fin.castSucc (Fin.last n))))
                      (midpoint_left_half (t (Fin.last (n + 1))))
                      hleft
                      hright
                      s
                _ =
                  γ.subpath
                    (t (Fin.castSucc (Fin.last n)))
                    (t (Fin.last (n + 1)))
                    s := by
                  rw [hstart, hend])
      have hsrc :
          chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t 0))) =
            chosen_cover_object O hO S (γ (t 0)) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_left_half_point_eq γ δ (t 0))
      have hmid :
          chosen_cover_object O hO S
              ((γ.trans δ) (midpoint_left_half (t (Fin.castSucc (Fin.last n))))) =
            chosen_cover_object O hO S (γ (t (Fin.castSucc (Fin.last n)))) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_left_half_point_eq γ δ (t (Fin.castSucc (Fin.last n))))
      have htgt :
          chosen_cover_object O hO S
              ((γ.trans δ) (midpoint_left_half (t (Fin.last (n + 1))))) =
            chosen_cover_object O hO S (γ (t (Fin.last (n + 1)))) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_left_half_point_eq γ δ (t (Fin.last (n + 1))))
      exact CategoryTheory.heq_comp hsrc hmid htgt hprefix hlast

/-- Helper for Theorem 2.7.1: subdividing `γ.trans δ` along the right-half-scaled tuple produces
the same raw subdivision composite as subdividing `δ` along the original tuple. -/
theorem subdivision_morphism_trans_right_half_heq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {m : ℕ}
    (t' : Fin (m + 1) → I)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)) :
    subdivision_morphism O hO hinter S (γ.trans δ)
        (t := fun q : Fin (m + 1) ↦ midpoint_right_half (t' q))
        (u := u')
        (midpoint_right_half_subordinate γ δ t' u' hu') ≍
      subdivision_morphism O hO hinter S δ
        (t := t')
        (u := u')
        hu' := by
  induction m with
  | zero =>
      -- The empty right-half subdivision is again just the identity after endpoint identification.
      have hobj :
          chosen_cover_object O hO S ((γ.trans δ) (midpoint_right_half (t' 0))) =
            chosen_cover_object O hO S (δ (t' 0)) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_right_half_point_eq γ δ (t' 0))
      exact
        (CategoryTheory.eqToHom_heq_id_dom
          (chosen_cover_object O hO S ((γ.trans δ) (midpoint_right_half (t' 0))))
          (chosen_cover_object O hO S (δ (t' 0)))
          hobj).symm.trans <|
          (CategoryTheory.eqToHom_heq_id_cod
            (chosen_cover_object O hO S ((γ.trans δ) (midpoint_right_half (t' 0))))
            (chosen_cover_object O hO S (δ (t' 0)))
            hobj)
  | succ m ih =>
      -- The recursive prefix and the terminal local factor both match the original subdivision of
      -- `δ` after the right-half reparameterization is normalized.
      rw [subdivision_morphism, subdivision_morphism]
      have hprefix :
          subdivision_morphism O hO hinter S (γ.trans δ)
              (t := fun q : Fin (m + 1) ↦ midpoint_right_half (t' q.castSucc))
              (u := fun q : Fin m ↦ u' q.castSucc)
              (fun q : Fin m ↦ midpoint_right_half_subordinate γ δ t' u' hu' q.castSucc) ≍
            subdivision_morphism O hO hinter S δ
              (t := fun q : Fin (m + 1) ↦ t' q.castSucc)
              (u := fun q : Fin m ↦ u' q.castSucc)
              (fun q : Fin m ↦ hu' q.castSucc) := by
        simpa using
          ih
            (t' := fun q : Fin (m + 1) ↦ t' q.castSucc)
            (u' := fun q : Fin m ↦ u' q.castSucc)
            (hu' := fun q : Fin m ↦ hu' q.castSucc)
      have hlast :
          local_subpath_morphism O hO hinter S (γ.trans δ)
              (midpoint_right_half (t' (Fin.castSucc (Fin.last m))))
              (midpoint_right_half (t' (Fin.last (m + 1))))
              (u' (Fin.last m))
              (midpoint_right_half_subordinate γ δ t' u' hu' (Fin.last m)) ≍
            local_subpath_morphism O hO hinter S δ
              (t' (Fin.castSucc (Fin.last m)))
              (t' (Fin.last (m + 1)))
              (u' (Fin.last m))
              (hu' (Fin.last m)) := by
        have hleft :
            (1 / 2 : ℝ) ≤ (((midpoint_right_half (t' (Fin.castSucc (Fin.last m))) : I) : ℝ)) := by
          change (1 / 2 : ℝ) ≤ ((((t' (Fin.castSucc (Fin.last m)) : I) : ℝ) + 1) / 2)
          nlinarith [(t' (Fin.castSucc (Fin.last m))).2.1]
        have hright :
            (1 / 2 : ℝ) ≤ (((midpoint_right_half (t' (Fin.last (m + 1))) : I) : ℝ)) := by
          change (1 / 2 : ℝ) ≤ ((((t' (Fin.last (m + 1)) : I) : ℝ) + 1) / 2)
          nlinarith [(t' (Fin.last (m + 1))).2.1]
        have hstart :
            (⟨2 * midpoint_right_half (t' (Fin.castSucc (Fin.last m))) - 1,
                unitInterval.two_mul_sub_one_mem_iff.2
                  ⟨hleft, (midpoint_right_half (t' (Fin.castSucc (Fin.last m)))).2.2⟩⟩ : I) =
              t' (Fin.castSucc (Fin.last m)) := by
          ext
          simp [midpoint_right_half]
          ring
        have hend :
            (⟨2 * midpoint_right_half (t' (Fin.last (m + 1))) - 1,
                unitInterval.two_mul_sub_one_mem_iff.2
                  ⟨hright, (midpoint_right_half (t' (Fin.last (m + 1)))).2.2⟩⟩ : I) =
              t' (Fin.last (m + 1)) := by
          ext
          simp [midpoint_right_half]
          ring
        exact
          local_subpath_morphism_heq_of_subpath_eq
            (hO := hO)
            (hinter := hinter)
            (S := S)
            (γ := γ.trans δ)
            (a := midpoint_right_half (t' (Fin.castSucc (Fin.last m))))
            (b := midpoint_right_half (t' (Fin.last (m + 1))))
            (γ' := δ)
            (a' := t' (Fin.castSucc (Fin.last m)))
            (b' := t' (Fin.last (m + 1)))
            (i := u' (Fin.last m))
            (hsub := midpoint_right_half_subordinate γ δ t' u' hu' (Fin.last m))
            (hsub' := hu' (Fin.last m))
            (fun s ↦ by
              calc
                (γ.trans δ).subpath
                    (midpoint_right_half (t' (Fin.castSucc (Fin.last m))))
                    (midpoint_right_half (t' (Fin.last (m + 1))))
                    s =
                  δ.subpath
                    ⟨2 * midpoint_right_half (t' (Fin.castSucc (Fin.last m))) - 1,
                      unitInterval.two_mul_sub_one_mem_iff.2
                        ⟨hleft, (midpoint_right_half (t' (Fin.castSucc (Fin.last m)))).2.2⟩⟩
                    ⟨2 * midpoint_right_half (t' (Fin.last (m + 1))) - 1,
                      unitInterval.two_mul_sub_one_mem_iff.2
                        ⟨hright, (midpoint_right_half (t' (Fin.last (m + 1)))).2.2⟩⟩
                    s := by
                  exact
                    trans_subpath_right_apply_eq_or_midpoint γ δ
                      (midpoint_right_half (t' (Fin.castSucc (Fin.last m))))
                      (midpoint_right_half (t' (Fin.last (m + 1))))
                      hleft
                      hright
                      s
                _ =
                  δ.subpath
                    (t' (Fin.castSucc (Fin.last m)))
                    (t' (Fin.last (m + 1)))
                    s := by
                  rw [hstart, hend])
      have hsrc :
          chosen_cover_object O hO S ((γ.trans δ) (midpoint_right_half (t' 0))) =
            chosen_cover_object O hO S (δ (t' 0)) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_right_half_point_eq γ δ (t' 0))
      have hmid :
          chosen_cover_object O hO S
              ((γ.trans δ) (midpoint_right_half (t' (Fin.castSucc (Fin.last m))))) =
            chosen_cover_object O hO S (δ (t' (Fin.castSucc (Fin.last m)))) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_right_half_point_eq γ δ (t' (Fin.castSucc (Fin.last m))))
      have htgt :
          chosen_cover_object O hO S
              ((γ.trans δ) (midpoint_right_half (t' (Fin.last (m + 1))))) =
            chosen_cover_object O hO S (δ (t' (Fin.last (m + 1)))) := by
        simpa using
          congrArg (fun p : X ↦ chosen_cover_object O hO S p)
            (trans_right_half_point_eq γ δ (t' (Fin.last (m + 1))))
      exact CategoryTheory.heq_comp hsrc hmid htgt hprefix hlast

/-- Helper for Theorem 2.7.1: the literal prefix of the midpoint-glued tuple up to the midpoint is
exactly the left-half rescaling of `t`. -/
theorem midpoint_glued_prefix_points_eq_left_half
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I)
    (ht1 : t (Fin.last n) = 1)
    (ht'0 : t' 0 = 0) :
    shared_tuple_prefix_points
        (midpoint_glued_points t t')
        (midpoint_glued_cutpoint n m) =
      fun q : Fin (n + 1) ↦ midpoint_left_half (t q) := by
  funext q
  cases q using Fin.lastCases with
  | last =>
      have hnot : ¬ n < n := by omega
      have hzero :
          midpoint_glued_right_point_index (midpoint_glued_cutpoint n m) hnot = 0 := by
        ext
        simp [midpoint_glued_right_point_index, midpoint_glued_cutpoint]
      change midpoint_glued_points t t' (midpoint_glued_cutpoint n m) =
          midpoint_left_half (t (Fin.last n))
      rw [show midpoint_glued_points t t' (midpoint_glued_cutpoint n m) =
          midpoint_right_half (t' (midpoint_glued_right_point_index (midpoint_glued_cutpoint n m) hnot)) by
          simp [midpoint_glued_points, midpoint_glued_cutpoint, hnot]]
      rw [hzero, ht'0, ht1]
      ext
      simp [midpoint_left_half, midpoint_right_half]
  | cast q =>
      have hq :
          (⟨q.1, by
            have hq' : q.1 < n := by
              simpa [midpoint_glued_cutpoint] using q.is_lt
            exact Nat.lt_succ_of_lt hq'⟩ : Fin (n + 1)) =
            q.castSucc := by
        ext
        simp [midpoint_glued_cutpoint]
      change midpoint_glued_points t t' ⟨q.1, by
          have hq' : q.1 < n := by
            simpa [midpoint_glued_cutpoint] using q.is_lt
          omega⟩ =
        midpoint_left_half (t q.castSucc)
      have hq' : q.1 < n := by
        simpa [midpoint_glued_cutpoint] using q.is_lt
      simpa [hq, midpoint_glued_points, midpoint_glued_cutpoint, hq', midpoint_left_half]

/-- Helper for Theorem 2.7.1: the literal prefix labels of the midpoint-glued tuple are exactly
the original labels `u`. -/
theorem midpoint_glued_prefix_labels_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {n m : ℕ}
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O) :
    shared_tuple_prefix_labels
        (midpoint_glued_labels u u')
        (midpoint_glued_cutpoint n m) =
      u := by
  funext q
  simp [shared_tuple_prefix_labels, midpoint_glued_labels, midpoint_glued_cutpoint, q.is_lt]

/-- Helper for Theorem 2.7.1: the literal suffix of the midpoint-glued tuple starting at the
midpoint is exactly the right-half rescaling of `t'`. -/
theorem midpoint_glued_suffix_points_cast_eq_right_half
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (t' : Fin (m + 1) → I) :
    (fun q : Fin (m + 1) ↦
      shared_tuple_suffix_points
          (midpoint_glued_points t t')
          (midpoint_glued_cutpoint n m)
          ⟨q.1, by
            have hlen : n + m - n + 1 = m + 1 := by omega
            simpa [hlen] using q.is_lt⟩) =
      fun q : Fin (m + 1) ↦ midpoint_right_half (t' q) := by
  funext q
  have hnot :
      ¬ (n + q.1) < n := by
    omega
  simp [shared_tuple_suffix_points, midpoint_glued_points, midpoint_glued_cutpoint, hnot,
    midpoint_glued_right_point_index]

/-- Helper for Theorem 2.7.1: the literal suffix labels of the midpoint-glued tuple are exactly
the original labels `u'`. -/
theorem midpoint_glued_suffix_labels_cast_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {n m : ℕ}
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O) :
    (fun q : Fin m ↦
      shared_tuple_suffix_labels
          (midpoint_glued_labels u u')
          (midpoint_glued_cutpoint n m)
          ⟨q.1, by
            have hlen : n + m - n = m := by omega
            simpa [hlen] using q.is_lt⟩) =
      u' := by
  funext q
  have hnot :
      ¬ (n + q.1) < n := by
    omega
  simp [shared_tuple_suffix_labels, midpoint_glued_labels, midpoint_glued_cutpoint, hnot,
    midpoint_glued_right_label_index]

/-- Helper for Theorem 2.7.1: the explicit midpoint-glued subdivision should split at the midpoint
into the original explicit subdivisions of `γ` and `δ`. -/
theorem midpoint_split_morphism_comparison
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (htmono : Monotone t)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hx : γ (t 0) = x)
    (hy : γ (t (Fin.last n)) = y)
    (t' : Fin (m + 1) → I)
    (hm : m ≠ 0)
    (ht'0 : t' 0 = 0)
    (ht'1 : t' (Fin.last m) = 1)
    (ht'mono : Monotone t')
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k))
    (hy' : δ (t' 0) = y)
    (hz : δ (t' (Fin.last m)) = z) :
    normalized_subdivision_morphism O hO hinter S (γ.trans δ)
        (midpoint_glued_points t t')
        (midpoint_glued_labels u u')
        (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
        (midpoint_glued_source_eq γ δ t t' hn ht0)
        (midpoint_glued_target_eq γ δ t t' ht'1) =
      normalized_subdivision_morphism O hO hinter S γ t u hu hx hy ≫
        normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz := by
  let _ := hm
  let _ := htmono
  let _ := ht'mono
  -- Route correction: the explicit midpoint tuple now has proved left/right subordinate families
  -- and literal prefix/suffix tuple normal forms. The remaining blocker is the morphism-level
  -- comparison that collapses those two literal halves back to the original subdivision composites
  -- of `γ` and `δ`.
  let kPoint := midpoint_glued_cutpoint n m
  have hkPoint : kPoint ≠ Fin.last (n + m) := by
    intro hk
    have hval := congrArg Fin.val hk
    simp [kPoint, midpoint_glued_cutpoint, Fin.last] at hval
    omega
  have hglued_raw :
      normalized_subdivision_morphism O hO hinter S (γ.trans δ)
          (midpoint_glued_points t t')
          (midpoint_glued_labels u u')
          (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
          (midpoint_glued_source_eq γ δ t t' hn ht0)
          (midpoint_glued_target_eq γ δ t t' ht'1) ≍
        subdivision_morphism O hO hinter S (γ.trans δ)
          (t := midpoint_glued_points t t')
          (u := midpoint_glued_labels u u')
          (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu') := by
    -- First strip the endpoint transports from the normalized glued subdivision.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (normalized_subdivision_morphism O hO hinter S (γ.trans δ)
          (midpoint_glued_points t t')
          (midpoint_glued_labels u u')
          (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
          (midpoint_glued_source_eq γ δ t t' hn ht0)
          (midpoint_glued_target_eq γ δ t t' ht'1))
        (subdivision_morphism O hO hinter S (γ.trans δ)
          (t := midpoint_glued_points t t')
          (u := midpoint_glued_labels u u')
          (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu'))
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (midpoint_glued_source_eq γ δ t t' hn ht0)).symm
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
          (midpoint_glued_target_eq γ δ t t' ht'1)).symm).1 rfl
  have hsplit :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := midpoint_glued_points t t')
          (u := midpoint_glued_labels u u')
          (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu') ≍
        subdivision_morphism O hO hinter S (γ.trans δ)
            (t := shared_tuple_prefix_points (midpoint_glued_points t t') kPoint)
            (u := shared_tuple_prefix_labels (midpoint_glued_labels u u') kPoint)
            (shared_tuple_prefix_subordinate
              (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≫
          subdivision_morphism O hO hinter S (γ.trans δ)
            (t := shared_tuple_suffix_points (midpoint_glued_points t t') kPoint)
            (u := shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint)
            (shared_tuple_suffix_subordinate
              (γ.trans δ)
              (midpoint_glued_points t t')
              (midpoint_glued_labels u u')
              (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
              kPoint) := by
    -- Split the raw glued subdivision once at the midpoint cutpoint.
    exact
      subdivision_morphism_literal_nonterminal_cutpoint_reassembly_heq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ.trans δ)
        (w := midpoint_glued_points t t')
        (v := midpoint_glued_labels u u')
        (hv := midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
        (kPoint := kPoint)
        hkPoint
  have hnormγ_raw :
      normalized_subdivision_morphism O hO hinter S γ t u hu hx hy ≍
        subdivision_morphism O hO hinter S γ
          (t := t)
          (u := u)
          hu := by
    -- Remove the endpoint transports from the explicit subdivision of `γ`.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (normalized_subdivision_morphism O hO hinter S γ t u hu hx hy)
        (subdivision_morphism O hO hinter S γ
          (t := t)
          (u := u)
          hu)
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hx).symm
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hy).symm).1 rfl
  have hnormδ_raw :
      normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz ≍
        subdivision_morphism O hO hinter S δ
          (t := t')
          (u := u')
          hu' := by
    -- Remove the endpoint transports from the explicit subdivision of `δ`.
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz)
        (subdivision_morphism O hO hinter S δ
          (t := t')
          (u := u')
          hu')
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hy').symm
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hz).symm).1 rfl
  have hprefix_half :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_prefix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_prefix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_prefix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≍
        subdivision_morphism O hO hinter S (γ.trans δ)
          (t := fun q : Fin (n + 1) ↦ midpoint_left_half (t q))
          (u := u)
          (midpoint_left_half_subordinate γ δ t u hu) := by
    -- Rewrite the literal midpoint prefix to the already normalized left-half tuple.
    exact
      subdivision_morphism_heq_of_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ.trans δ)
        (ht := midpoint_glued_prefix_points_eq_left_half t t' ht1 ht'0)
        (hu := midpoint_glued_prefix_labels_eq u u')
  have hsuffix_half :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_suffix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_suffix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≍
        subdivision_morphism O hO hinter S (γ.trans δ)
          (t := fun q : Fin (m + 1) ↦ midpoint_right_half (t' q))
          (u := u')
          (midpoint_right_half_subordinate γ δ t' u' hu') := by
    let tCast : Fin (m + 1) → I := fun q ↦
      shared_tuple_suffix_points (midpoint_glued_points t t') kPoint ⟨q.1, by
        have hlen : n + m - kPoint.1 + 1 = m + 1 := by
          simp [kPoint, midpoint_glued_cutpoint]
        simpa [hlen] using q.is_lt⟩
    let uCast : Fin m → TopologicalSpace.IsOpenCover.Index O := fun q ↦
      shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint ⟨q.1, by
        have hlen : n + m - kPoint.1 = m := by
          simp [kPoint, midpoint_glued_cutpoint]
        simpa [hlen] using q.is_lt⟩
    have hcast :
        subdivision_morphism O hO hinter S (γ.trans δ)
            (t := shared_tuple_suffix_points (midpoint_glued_points t t') kPoint)
            (u := shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint)
            (shared_tuple_suffix_subordinate
              (γ.trans δ)
              (midpoint_glued_points t t')
              (midpoint_glued_labels u u')
              (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
              kPoint) ≍
          subdivision_morphism O hO hinter S (γ.trans δ)
            (t := tCast)
            (u := uCast)
            (fun q : Fin m ↦
              shared_tuple_suffix_subordinate
                (γ.trans δ)
                (midpoint_glued_points t t')
                (midpoint_glued_labels u u')
                (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
                kPoint
                ⟨q.1, by
                  have hlen : n + m - kPoint.1 = m := by
                    simp [kPoint, midpoint_glued_cutpoint]
                  simpa [hlen] using q.is_lt⟩) := by
      -- Transport the literal midpoint suffix to the exact `Fin (m + 1)` / `Fin m` input lengths.
      have ht :
          shared_tuple_suffix_points (midpoint_glued_points t t') kPoint =
            fun q ↦ tCast (Fin.cast (by
              have hlen : n + m - kPoint.1 + 1 = m + 1 := by
                simp [kPoint, midpoint_glued_cutpoint]
              exact hlen) q) := by
        funext q
        simp [tCast]
      have huCast :
          shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint =
            fun q ↦ uCast (Fin.cast (by
              have hlen : n + m - kPoint.1 = m := by
                simp [kPoint, midpoint_glued_cutpoint]
              exact hlen) q) := by
        funext q
        simp [uCast]
      exact
        subdivision_morphism_heq_of_cast_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ.trans δ)
          (hn := by
            simp [kPoint, midpoint_glued_cutpoint])
          (ht := ht)
          (hu := huCast)
    have hcast_eq :
        subdivision_morphism O hO hinter S (γ.trans δ)
            (t := tCast)
            (u := uCast)
            (fun q : Fin m ↦
              shared_tuple_suffix_subordinate
                (γ.trans δ)
                (midpoint_glued_points t t')
                (midpoint_glued_labels u u')
                (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
                kPoint
                ⟨q.1, by
                  have hlen : n + m - kPoint.1 = m := by
                    simp [kPoint, midpoint_glued_cutpoint]
                  simpa [hlen] using q.is_lt⟩) ≍
          subdivision_morphism O hO hinter S (γ.trans δ)
            (t := fun q : Fin (m + 1) ↦ midpoint_right_half (t' q))
            (u := u')
            (midpoint_right_half_subordinate γ δ t' u' hu') := by
      -- Once the suffix is reindexed to length `m`, the explicit right-half tuple equality applies.
      exact
        subdivision_morphism_heq_of_eq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ.trans δ)
          (ht := midpoint_glued_suffix_points_cast_eq_right_half t t')
          (hu := midpoint_glued_suffix_labels_cast_eq u u')
    exact hcast.trans hcast_eq
  have hprefix_norm :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_prefix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_prefix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_prefix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≍
        normalized_subdivision_morphism O hO hinter S γ t u hu hx hy := by
    -- After normalizing the prefix tuple, the left-half comparison identifies it with `γ`.
    exact
      hprefix_half.trans <|
        (subdivision_morphism_trans_left_half_heq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (δ := δ)
          (t := t)
          (u := u)
          (hu := hu)).trans hnormγ_raw.symm
  have hsuffix_norm :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_suffix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_suffix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≍
        normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz := by
    -- The suffix comparison is symmetric on the right half.
    exact
      hsuffix_half.trans <|
        (subdivision_morphism_trans_right_half_heq
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := γ)
          (δ := δ)
          (t' := t')
          (u' := u')
          (hu' := hu')).trans hnormδ_raw.symm
  have hsrc :
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_prefix_points (midpoint_glued_points t t') kPoint 0)) =
        chosen_cover_object O hO S x := by
    have hpoint :
        shared_tuple_prefix_points (midpoint_glued_points t t') kPoint 0 =
          midpoint_left_half (t 0) := by
      simpa [kPoint] using
        congrArg (fun f : Fin (n + 1) → I ↦ f 0)
          (midpoint_glued_prefix_points_eq_left_half t t' ht1 ht'0)
    calc
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_prefix_points (midpoint_glued_points t t') kPoint 0)) =
        chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t 0))) := by
          rw [hpoint]
      _ = chosen_cover_object O hO S (γ (t 0)) := by
          simpa using
            congrArg (fun p : X ↦ chosen_cover_object O hO S p)
              (trans_left_half_point_eq γ δ (t 0))
      _ = chosen_cover_object O hO S x := by
          simpa [hx]
  have hmid :
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_prefix_points (midpoint_glued_points t t') kPoint
              (Fin.last n))) =
        chosen_cover_object O hO S y := by
    have hpoint :
        shared_tuple_prefix_points (midpoint_glued_points t t') kPoint (Fin.last n) =
          midpoint_left_half (t (Fin.last n)) := by
      simpa [kPoint] using
        congrArg (fun f : Fin (n + 1) → I ↦ f (Fin.last n))
          (midpoint_glued_prefix_points_eq_left_half t t' ht1 ht'0)
    calc
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_prefix_points (midpoint_glued_points t t') kPoint
              (Fin.last n))) =
        chosen_cover_object O hO S ((γ.trans δ) (midpoint_left_half (t (Fin.last n)))) := by
          rw [hpoint]
      _ = chosen_cover_object O hO S (γ (t (Fin.last n))) := by
          simpa using
            congrArg (fun p : X ↦ chosen_cover_object O hO S p)
              (trans_left_half_point_eq γ δ (t (Fin.last n)))
      _ = chosen_cover_object O hO S y := by
          simpa [hy]
  have htgt :
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_suffix_points (midpoint_glued_points t t') kPoint
              (Fin.last (n + m - kPoint.1)))) =
        chosen_cover_object O hO S z := by
    have hpoint :
        shared_tuple_suffix_points (midpoint_glued_points t t') kPoint
            (Fin.last (n + m - kPoint.1)) =
          midpoint_right_half (t' (Fin.last m)) := by
      let qLast : Fin (n + m - kPoint.1 + 1) := ⟨(Fin.last m).1, by
        have hlen : n + m - kPoint.1 + 1 = m + 1 := by
          simp [kPoint, midpoint_glued_cutpoint]
        simpa [hlen] using (Fin.last m).is_lt⟩
      have hqLast : qLast = Fin.last (n + m - kPoint.1) := by
        ext
        simp [qLast, kPoint, midpoint_glued_cutpoint, Fin.last]
      have hpointCast :
          shared_tuple_suffix_points (midpoint_glued_points t t') kPoint qLast =
            midpoint_right_half (t' (Fin.last m)) := by
        simpa [qLast, kPoint] using
          congrArg (fun f : Fin (m + 1) → I ↦ f (Fin.last m))
            (midpoint_glued_suffix_points_cast_eq_right_half t t')
      simpa [hqLast] using hpointCast
    calc
      chosen_cover_object O hO S
          ((γ.trans δ)
            (shared_tuple_suffix_points (midpoint_glued_points t t') kPoint
              (Fin.last (n + m - kPoint.1)))) =
        chosen_cover_object O hO S ((γ.trans δ) (midpoint_right_half (t' (Fin.last m)))) := by
          rw [hpoint]
      _ = chosen_cover_object O hO S (δ (t' (Fin.last m))) := by
          simpa using
            congrArg (fun p : X ↦ chosen_cover_object O hO S p)
              (trans_right_half_point_eq γ δ (t' (Fin.last m)))
      _ = chosen_cover_object O hO S z := by
          simpa [hz]
  have hsplit_norm :
      subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_prefix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_prefix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_prefix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≫
        subdivision_morphism O hO hinter S (γ.trans δ)
          (t := shared_tuple_suffix_points (midpoint_glued_points t t') kPoint)
          (u := shared_tuple_suffix_labels (midpoint_glued_labels u u') kPoint)
          (shared_tuple_suffix_subordinate
            (γ.trans δ)
            (midpoint_glued_points t t')
            (midpoint_glued_labels u u')
            (midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu')
            kPoint) ≍
        normalized_subdivision_morphism O hO hinter S γ t u hu hx hy ≫
          normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz := by
    -- Compose the two half-comparisons only after both halves have been normalized to the
    -- explicit subdivision composites of `γ` and `δ`.
    exact CategoryTheory.heq_comp hsrc hmid htgt hprefix_norm hsuffix_norm
  exact eq_of_heq (hglued_raw.trans (hsplit.trans hsplit_norm))

/-- Helper for Theorem 2.7.1: explicit subdivisions of two composable paths can be glued at the
midpoint to produce explicit breakpoint and cover-label data for the concatenated path. -/
theorem midpoint_glued_subdivision_data
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (htmono : Monotone t)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (t' : Fin (m + 1) → I)
    (ht'0 : t' 0 = 0)
    (ht'1 : t' (Fin.last m) = 1)
    (ht'mono : Monotone t')
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k)) :
    ∃ s : Fin (n + m + 1) → I,
      s 0 = 0 ∧
      s (Fin.last (n + m)) = 1 ∧
      Monotone s ∧
      ∃ v : Fin (n + m) → TopologicalSpace.IsOpenCover.Index O,
        (∀ k : Fin (n + m),
            Set.range (((γ.trans δ).subpath (s k.castSucc) (s k.succ))) ⊆ O (v k)) ∧
          (γ.trans δ) (s 0) = x ∧
          (γ.trans δ) (s (Fin.last (n + m))) = z := by
  let leftHalf : I → I := fun a ↦
    ⟨(a : ℝ) / 2, by
      constructor <;> nlinarith [a.2.1, a.2.2]⟩
  let rightHalf : I → I := fun a ↦
    ⟨((a : ℝ) + 1) / 2, by
      constructor <;> nlinarith [a.2.1, a.2.2]⟩
  let s : Fin (n + m + 1) → I := fun k ↦
    if hk : k.1 < n then
      leftHalf (t ⟨k.1, Nat.lt_succ_of_lt hk⟩)
    else
      rightHalf (t' ⟨k.1 - n, by omega⟩)
  let v : Fin (n + m) → TopologicalSpace.IsOpenCover.Index O := fun k ↦
    if hk : k.1 < n then
      u ⟨k.1, hk⟩
    else
      u' ⟨k.1 - n, by omega⟩
  have hposn : 0 < n := Nat.pos_of_ne_zero hn
  have hs0 : s 0 = 0 := by
    -- The glued tuple starts with the left subdivision point `t 0 = 0`.
    ext
    simp [s, leftHalf, ht0, hposn]
  have hs1 : s (Fin.last (n + m)) = 1 := by
    -- The glued tuple ends with the right subdivision point `t' (last) = 1`.
    have hnot : ¬ (Fin.last (n + m)).1 < n := by
      simp [Fin.last]
    have hlast :
        (⟨(Fin.last (n + m)).1 - n, by omega⟩ : Fin (m + 1)) = Fin.last m := by
      ext
      simp [Fin.last]
    have hsLast :
        s (Fin.last (n + m)) =
          rightHalf (t' ⟨(Fin.last (n + m)).1 - n, by omega⟩) := by
      simp [s]
    rw [hsLast, hlast, ht'1]
    ext
    simp [rightHalf]
  have hsmono : Monotone s := by
    intro a b hab
    change ((s a : I) : ℝ) ≤ ((s b : I) : ℝ)
    by_cases ha : a.1 < n
    · by_cases hb : b.1 < n
      · -- Both breakpoints lie on the left half, so monotonicity comes from `t`.
        let ia : Fin (n + 1) := ⟨a.1, Nat.lt_succ_of_lt ha⟩
        let ib : Fin (n + 1) := ⟨b.1, Nat.lt_succ_of_lt hb⟩
        have hit : t ia ≤ t ib := by
          exact htmono (by simpa [ia, ib] using hab)
        have hit' : ((t ia : I) : ℝ) ≤ ((t ib : I) : ℝ) := hit
        have hscaled : (((t ia : I) : ℝ) / 2) ≤ (((t ib : I) : ℝ) / 2) := by
          nlinarith
        simpa [s, ha, hb, leftHalf, ia, ib] using hscaled
      · -- A left-half breakpoint is always at most the midpoint, while a right-half breakpoint is
        -- always at least the midpoint.
        have hleft : ((s a : I) : ℝ) ≤ 1 / 2 := by
          let ia : Fin (n + 1) := ⟨a.1, Nat.lt_succ_of_lt ha⟩
          have hscaled : (((t ia : I) : ℝ) / 2) ≤ 1 / 2 := by
            nlinarith [(t ia).2.2]
          simpa [s, ha, leftHalf, ia] using hscaled
        have hright : (1 / 2 : ℝ) ≤ ((s b : I) : ℝ) := by
          let jb : Fin (m + 1) := ⟨b.1 - n, by omega⟩
          have hscaled : (1 / 2 : ℝ) ≤ ((((t' jb : I) : ℝ) + 1) / 2) := by
            nlinarith [(t' jb).2.1]
          simpa [s, hb, rightHalf, jb] using hscaled
        nlinarith
    · -- Once the glued tuple has crossed the midpoint, monotonicity comes from `t'`.
      have hb' : ¬ b.1 < n := by
        omega
      let ia : Fin (m + 1) := ⟨a.1 - n, by omega⟩
      let ib : Fin (m + 1) := ⟨b.1 - n, by omega⟩
      have habNat : a.1 ≤ b.1 := hab
      have habSub : a.1 - n ≤ b.1 - n := Nat.sub_le_sub_right habNat n
      have hit : t' ia ≤ t' ib := by
        exact ht'mono (by simpa [ia, ib] using habSub)
      have hit' : ((t' ia : I) : ℝ) ≤ ((t' ib : I) : ℝ) := hit
      have hscaled : ((((t' ia : I) : ℝ) + 1) / 2) ≤ ((((t' ib : I) : ℝ) + 1) / 2) := by
        nlinarith
      simpa [s, ha, hb', rightHalf, ia, ib] using hscaled
  have hv :
      ∀ k : Fin (n + m),
        Set.range (((γ.trans δ).subpath (s k.castSucc) (s k.succ))) ⊆ O (v k) := by
    intro k
    by_cases hk : k.1 < n
    · let kLeft : Fin n := ⟨k.1, hk⟩
      have hsCast :
          s k.castSucc = leftHalf (t kLeft.castSucc) := by
        simpa [s, kLeft] using
          (show s k.castSucc = leftHalf (t ⟨k.1, Nat.lt_succ_of_lt hk⟩) by
            simp [s, hk])
      have hsSucc :
          s k.succ = leftHalf (t kLeft.succ) := by
        by_cases hkSuccNat : k.1 + 1 < n
        · simpa [s, kLeft] using
            (show s k.succ = leftHalf (t ⟨k.1 + 1, Nat.lt_succ_of_lt hkSuccNat⟩) by
              simp [s, hkSuccNat])
        · have hkEq : k.1 + 1 = n := by omega
          have hkLast : kLeft.succ = Fin.last n := by
            ext
            simp [kLeft, hkEq, Fin.last]
          rw [show s k.succ = rightHalf (t' 0) by
            simp [s, hkEq]]
          rw [hkLast, ht1, ht'0]
          ext
          simp [leftHalf, rightHalf]
      have ha : ((s k.castSucc : I) : ℝ) ≤ 1 / 2 := by
        have hscaled : (((t kLeft.castSucc : I) : ℝ) / 2) ≤ 1 / 2 := by
          nlinarith [(t kLeft.castSucc).2.2]
        simpa [hsCast, leftHalf] using hscaled
      have hb : ((s k.succ : I) : ℝ) ≤ 1 / 2 := by
        have hscaled : (((t kLeft.succ : I) : ℝ) / 2) ≤ 1 / 2 := by
          nlinarith [(t kLeft.succ).2.2]
        simpa [hsSucc, leftHalf] using hscaled
      have hstart :
          (⟨2 * s k.castSucc,
              (mul_pos_mem_iff zero_lt_two).2 ⟨(s k.castSucc).2.1, ha⟩⟩ : I) =
            t kLeft.castSucc := by
        ext
        simp [hsCast, leftHalf]
        ring
      have hend :
          (⟨2 * s k.succ,
              (mul_pos_mem_iff zero_lt_two).2 ⟨(s k.succ).2.1, hb⟩⟩ : I) =
            t kLeft.succ := by
        ext
        simp [hsSucc, leftHalf]
        ring
      have hsegment :
          Set.range
              (γ.subpath
                ⟨2 * s k.castSucc,
                  (mul_pos_mem_iff zero_lt_two).2 ⟨(s k.castSucc).2.1, ha⟩⟩
                ⟨2 * s k.succ,
                  (mul_pos_mem_iff zero_lt_two).2 ⟨(s k.succ).2.1, hb⟩⟩) ⊆
            O (u kLeft) := by
        simpa [hstart, hend] using hu kLeft
      -- The left block of the glued tuple is just the left subdivision scaled into `[0, 1 / 2]`.
      simpa [v, hk, kLeft] using
        trans_subpath_left_range_subset γ δ (s k.castSucc) (s k.succ) ha hb hsegment
    · let kRight : Fin m := ⟨k.1 - n, by omega⟩
      have hsCast :
          s k.castSucc = rightHalf (t' kRight.castSucc) := by
        simpa [s, kRight] using
          (show s k.castSucc = rightHalf (t' ⟨k.1 - n, by omega⟩) by
            simp [s, hk])
      have hsSucc :
          s k.succ = rightHalf (t' kRight.succ) := by
        have hkSuccNat : ¬ k.1 + 1 < n := by
          omega
        have hkRightSucc :
            (⟨k.1 + 1 - n, by omega⟩ : Fin (m + 1)) = kRight.succ := by
          ext
          simp [kRight]
          omega
        have hsSuccRaw :
            s k.succ = rightHalf (t' ⟨k.1 + 1 - n, by omega⟩) := by
          simp [s, hkSuccNat]
        simpa [hkRightSucc] using hsSuccRaw
      have ha : (1 / 2 : ℝ) ≤ ((s k.castSucc : I) : ℝ) := by
        have hscaled : (1 / 2 : ℝ) ≤ ((((t' kRight.castSucc : I) : ℝ) + 1) / 2) := by
          nlinarith [(t' kRight.castSucc).2.1]
        simpa [hsCast, rightHalf] using hscaled
      have hb : (1 / 2 : ℝ) ≤ ((s k.succ : I) : ℝ) := by
        have hscaled : (1 / 2 : ℝ) ≤ ((((t' kRight.succ : I) : ℝ) + 1) / 2) := by
          nlinarith [(t' kRight.succ).2.1]
        simpa [hsSucc, rightHalf] using hscaled
      have hstart :
          (⟨2 * s k.castSucc - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, (s k.castSucc).2.2⟩⟩ : I) =
            t' kRight.castSucc := by
        ext
        simp [hsCast, rightHalf]
        ring
      have hend :
          (⟨2 * s k.succ - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, (s k.succ).2.2⟩⟩ : I) =
            t' kRight.succ := by
        ext
        simp [hsSucc, rightHalf]
        ring
      have hsegment :
          Set.range
              (δ.subpath
                ⟨2 * s k.castSucc - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨ha, (s k.castSucc).2.2⟩⟩
                ⟨2 * s k.succ - 1,
                  unitInterval.two_mul_sub_one_mem_iff.2 ⟨hb, (s k.succ).2.2⟩⟩) ⊆
            O (u' kRight) := by
        simpa [hstart, hend] using hu' kRight
      -- The right block of the glued tuple is the right subdivision rescaled from `[0, 1]` to
      -- `[1 / 2, 1]`.
      simpa [v, hk, kRight] using
        trans_subpath_right_range_subset γ δ (s k.castSucc) (s k.succ) ha hb hsegment
  have hsx : (γ.trans δ) (s 0) = x := by
    -- The glued subdivision starts at the source of `γ.trans δ`.
    rw [hs0]
    simp
  have hsz : (γ.trans δ) (s (Fin.last (n + m))) = z := by
    -- The glued subdivision ends at the target of `γ.trans δ`.
    rw [hs1]
    simp
  exact ⟨s, hs0, hs1, hsmono, v, hv, hsx, hsz⟩

/-- Helper for Theorem 2.7.1: explicit subordinate subdivisions of two composable paths glue to an
explicit subdivision of the concatenated path whose normalized composite is the composite of the
two normalized subdivision morphisms. -/
theorem subdivision_morphism_trans_of_concatenated_subdivisions
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y z : X} (γ : Path x y) (δ : Path y z)
    {n m : ℕ}
    (t : Fin (n + 1) → I)
    (hn : n ≠ 0)
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last n) = 1)
    (htmono : Monotone t)
    (u : Fin n → TopologicalSpace.IsOpenCover.Index O)
    (hu : ∀ k : Fin n, Set.range (γ.subpath (t k.castSucc) (t k.succ)) ⊆ O (u k))
    (hx : γ (t 0) = x)
    (hy : γ (t (Fin.last n)) = y)
    (t' : Fin (m + 1) → I)
    (hm : m ≠ 0)
    (ht'0 : t' 0 = 0)
    (ht'1 : t' (Fin.last m) = 1)
    (ht'mono : Monotone t')
    (u' : Fin m → TopologicalSpace.IsOpenCover.Index O)
    (hu' : ∀ k : Fin m, Set.range (δ.subpath (t' k.castSucc) (t' k.succ)) ⊆ O (u' k))
    (hy' : δ (t' 0) = y)
    (hz : δ (t' (Fin.last m)) = z) :
    ∃ N : ℕ,
      ∃ s : Fin (N + 1) → I,
        ∃ hN : N ≠ 0,
          ∃ hs0 : s 0 = 0,
            ∃ hs1 : s (Fin.last N) = 1,
              ∃ hsmono : Monotone s,
        ∃ v : Fin N → TopologicalSpace.IsOpenCover.Index O,
          ∃ hv :
            ∀ k : Fin N,
              Set.range (((γ.trans δ).subpath (s k.castSucc) (s k.succ))) ⊆ O (v k),
            ∃ hsx : (γ.trans δ) (s 0) = x,
              ∃ hsz : (γ.trans δ) (s (Fin.last N)) = z,
                normalized_subdivision_morphism O hO hinter S (γ.trans δ) s v hv hsx hsz =
                  normalized_subdivision_morphism O hO hinter S γ t u hu hx hy ≫
                    normalized_subdivision_morphism O hO hinter S δ t' u' hu' hy' hz := by
  -- Route correction: the existential witness is now the literal midpoint-glued tuple itself, so
  -- the main theorem only packages that explicit data and delegates the remaining midpoint split
  -- comparison to the dedicated helper above.
  refine
    ⟨n + m,
      midpoint_glued_points t t',
      by omega,
      midpoint_glued_points_zero t t' hn ht0,
      midpoint_glued_points_last t t' ht'1,
      midpoint_glued_points_monotone t t' htmono ht'mono,
      midpoint_glued_labels u u',
      midpoint_glued_subordinate γ δ t ht1 u hu t' ht'0 u' hu',
      midpoint_glued_source_eq γ δ t t' hn ht0,
      midpoint_glued_target_eq γ δ t t' ht'1,
      midpoint_split_morphism_comparison
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (δ := δ)
        (t := t)
        (hn := hn)
        (ht0 := ht0)
        (ht1 := ht1)
        (htmono := htmono)
        (u := u)
        (hu := hu)
        (hx := hx)
        (hy := hy)
        (t' := t')
        (hm := hm)
        (ht'0 := ht'0)
        (ht'1 := ht'1)
        (ht'mono := ht'mono)
        (u' := u')
        (hu' := hu')
        (hy' := hy')
        (hz := hz)⟩

/-- Helper for Theorem 2.7.1: inside one cover member, chosen-subdivision composites respect
concatenation. -/
theorem chosen_subdivision_morphism_trans_in_cover
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {i : TopologicalSpace.IsOpenCover.Index O}
    {x y z : O i} (γ : Path x y) (δ : Path y z) :
    chosen_subdivision_morphism O hO hinter S
        ((γ.trans δ).map (show Continuous ((↑) : O i → X) by continuity)) =
      chosen_subdivision_morphism O hO hinter S
        (γ.map (show Continuous ((↑) : O i → X) by continuity)) ≫
      chosen_subdivision_morphism O hO hinter S
        (δ.map (show Continuous ((↑) : O i → X) by continuity)) := by
  have hγ :
      chosen_subdivision_morphism O hO hinter S
          (γ.map (show Continuous ((↑) : O i → X) by continuity)) =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
          (show (x : X) ∈ O i by exact x.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)).symm := by
    -- Rewrite the first local path by the cocone leg on the fixed cover member.
    simpa using
      chosen_subdivision_morphism_eq_cover_leg_map
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (i := i)
        (x := x)
        (y := y)
        (γ := γ)
  have hδ :
      chosen_subdivision_morphism O hO hinter S
          (δ.map (show Continuous ((↑) : O i → X) by continuity)) =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
          (show (z : X) ∈ O i by exact z.property)).symm := by
    -- The same cover-leg description holds for the second local path.
    simpa using
      chosen_subdivision_morphism_eq_cover_leg_map
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (i := i)
        (x := y)
        (y := z)
        (γ := δ)
  have hγδ :
      chosen_subdivision_morphism O hO hinter S
          ((γ.trans δ).map (show Continuous ((↑) : O i → X) by continuity)) =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
          (show (x : X) ∈ O i by exact x.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ.trans δ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
          (show (z : X) ∈ O i by exact z.property)).symm := by
    -- Apply the same normalization to the concatenated path.
    simpa using
      chosen_subdivision_morphism_eq_cover_leg_map
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (i := i)
        (x := x)
        (y := z)
        (γ := γ.trans δ)
  have hmap :
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ.trans δ⟧) =
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧) := by
    have hpath :
        FundamentalGroupoid.fromPath ⟦γ.trans δ⟧ =
          FundamentalGroupoid.fromPath ⟦γ⟧ ≫ FundamentalGroupoid.fromPath ⟦δ⟧ := by
      -- Composition in the local fundamental groupoid is represented by path concatenation.
      rw [FundamentalGroupoid.comp_eq]
      simp [FundamentalGroupoid.fromPath, ← Path.Homotopic.Quotient.mk_trans]
    -- Convert the concatenated local path class to a composite in `Π(O i)` and then use
    -- functoriality of the cocone leg.
    calc
      (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ.trans δ⟧) =
        (S.ι.app i).map
          (FundamentalGroupoid.fromPath ⟦γ⟧ ≫ FundamentalGroupoid.fromPath ⟦δ⟧) := by
            exact congrArg (fun f ↦ (S.ι.app i).map f) hpath
      _ =
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧) := by
            rw [Functor.map_comp]
  -- Replace each chosen subdivision by its local cocone-leg description, then cancel the shared
  -- midpoint transport.
  calc
    chosen_subdivision_morphism O hO hinter S
        ((γ.trans δ).map (show Continuous ((↑) : O i → X) by continuity)) =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ.trans δ⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
        (show (z : X) ∈ O i by exact z.property)).symm := hγδ
    _ =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧)) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
        (show (z : X) ∈ O i by exact z.property)).symm := by
      exact
        congrArg
          (fun f ↦
            eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
              (show (x : X) ∈ O i by exact x.property)) ≫
              f ≫
            eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
              (show (z : X) ∈ O i by exact z.property)).symm)
          hmap
    _ =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
        (show (x : X) ∈ O i by exact x.property)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
        (show (z : X) ∈ O i by exact z.property)).symm := by
      simp [Category.assoc]
    _ =
      (eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x)
          (show (x : X) ∈ O i by exact x.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)).symm) ≫
      (eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y)
          (show (y : X) ∈ O i by exact y.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦δ⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := z)
          (show (z : X) ∈ O i by exact z.property)).symm) := by
      simp [Category.assoc]
    _ =
      chosen_subdivision_morphism O hO hinter S
          (γ.map (show Continuous ((↑) : O i → X) by continuity)) ≫
        chosen_subdivision_morphism O hO hinter S
          (δ.map (show Continuous ((↑) : O i → X) by continuity)) := by
      simpa [Category.assoc] using
        congrArg₂
          (fun f g ↦ f ≫ g)
          hγ.symm
          hδ.symm

/-- Helper for Theorem 2.7.1: a pointwise constant subpath contributes only the endpoint transport
forced by its constant value. -/
theorem local_subpath_morphism_eq_eqToHom_of_constant_subpath
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y)
    (a b c : I)
    (i : TopologicalSpace.IsOpenCover.Index O)
    (hsub : Set.range (γ.subpath a b) ⊆ O i)
    (hconst : ∀ s : I, γ.subpath a b s = γ c) :
    local_subpath_morphism O hO hinter S γ a b i hsub =
      eqToHom (congrArg (fun z : X ↦ chosen_cover_object O hO S z) (by simpa using hconst 0)) ≫
        eqToHom
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z) (by simpa using hconst 1)).symm := by
  have hmem : γ c ∈ O i := by
    -- Evaluate the constant subpath at any point to recover the ambient constant value.
    rw [← hconst 0]
    exact hsub ⟨0, rfl⟩
  have hsub_cc : Set.range (γ.subpath c c) ⊆ O i := by
    -- Once the constant value lies in `O i`, every point of the degenerate comparison subpath
    -- lies there as well.
    intro z hz
    rcases hz with ⟨s, rfl⟩
    simpa using hmem
  have hcompare :
      local_subpath_morphism O hO hinter S γ a b i hsub ≍
        local_subpath_morphism O hO hinter S γ c c i hsub_cc := by
    -- Replace the given constant subpath by the degenerate subpath at its common value.
    exact
      local_subpath_morphism_heq_of_subpath_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := γ)
        (a := a)
        (b := b)
        (γ' := γ)
        (a' := c)
        (b' := c)
        (i := i)
        (hsub := hsub)
        (hsub' := hsub_cc)
        (fun s ↦ by
          calc
            γ.subpath a b s = γ c := hconst s
            _ = γ.subpath c c s := by simp)
  have hid :
      local_subpath_morphism O hO hinter S γ c c i hsub_cc =
        𝟙 (chosen_cover_object O hO S (γ c)) := by
    -- The degenerate comparison subpath is already the identity by the existing endpoint lemma.
    exact local_subpath_morphism_eq_id_of_eq_endpoints hO hinter S γ c i hsub_cc
  -- Convert the heterogeneous identification with the degenerate constant segment into the explicit
  -- endpoint transport between the original source and target objects.
  simpa [Category.assoc] using
    (CategoryTheory.conj_eqToHom_iff_heq
      (local_subpath_morphism O hO hinter S γ a b i hsub)
      (𝟙 (chosen_cover_object O hO S (γ c)))
      (congrArg (fun z : X ↦ chosen_cover_object O hO S z) (by simpa using hconst 0))
      (congrArg (fun z : X ↦ chosen_cover_object O hO S z) (by simpa using hconst 1))).2
      (hcompare.trans hid.heq)

/-- Helper for Theorem 2.7.1: a subtype path in one cover member whose ambient image is a fixed
ambient subpath computes the corresponding `local_subpath_morphism`. -/
theorem chosen_subdivision_morphism_eq_local_subpath_of_subtype_path_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub : Set.range (γ.subpath a b) ⊆ O i)
    (η :
      Path
        (x := (⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ : O i))
        (y := (⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i)))
    (hη :
      ∀ s : I,
        ((η.map (show Continuous ((↑) : O i → X) by continuity)) s) = γ.subpath a b s) :
    chosen_subdivision_morphism O hO hinter S
        (η.map (show Continuous ((↑) : O i → X) by continuity)) =
      local_subpath_morphism O hO hinter S γ a b i hsub := by
  have hlift :
      η = lift_subpath_to_open O γ a b i hsub := by
    -- The subtype-valued path is determined by its ambient image, so pointwise agreement with the
    -- lifted ambient subpath identifies it with `lift_subpath_to_open`.
    apply Path.ext
    funext s
    apply Subtype.ext
    calc
      (((η.map (show Continuous ((↑) : O i → X) by continuity)) s) : X) = γ.subpath a b s := by
        exact hη s
      _ = ((lift_subpath_to_open O γ a b i hsub) s : X) := by
        symm
        simpa using lift_subpath_to_open_apply O γ a b s i hsub
  -- First rewrite the chosen-subdivision composite to the cocone leg on the local subtype path.
  calc
    chosen_subdivision_morphism O hO hinter S
        (η.map (show Continuous ((↑) : O i → X) by continuity)) =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦η⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub)).symm := by
      -- This is the one-open normalization already proved for subtype-valued paths.
      simpa using
        chosen_subdivision_morphism_eq_cover_leg_map
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (i := i)
          (x := (⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ : O i))
          (y := (⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i))
          (γ := η)
    _ =
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ a) (subpath_source_mem_of_range_subset γ a b hsub)) ≫
        (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦lift_subpath_to_open O γ a b i hsub⟧) ≫
      eqToHom (chosen_cover_object_eq_of_mem hO hinter S
          (i := i) (x := γ b) (subpath_target_mem_of_range_subset γ a b hsub)).symm := by
      -- Replacing `η` by the literal lifted subpath changes neither endpoints nor local path class.
      simpa [hlift]
    _ = local_subpath_morphism O hO hinter S γ a b i hsub := rfl

/-- Helper for Theorem 2.7.1: the lower horizontal edge of the unit square. -/
noncomputable def unit_square_bottom_path :
    Path ((0 : I), (0 : I)) ((1 : I), (0 : I)) :=
  Path.mk ((ContinuousMap.id I).prodMk (ContinuousMap.const I (0 : I))) rfl rfl

/-- Helper for Theorem 2.7.1: the right vertical edge of the unit square. -/
noncomputable def unit_square_right_path :
    Path ((1 : I), (0 : I)) ((1 : I), (1 : I)) :=
  Path.mk ((ContinuousMap.const I (1 : I)).prodMk (ContinuousMap.id I)) rfl rfl

/-- Helper for Theorem 2.7.1: the left vertical edge of the unit square. -/
noncomputable def unit_square_left_path :
    Path ((0 : I), (0 : I)) ((0 : I), (1 : I)) :=
  Path.mk ((ContinuousMap.const I (0 : I)).prodMk (ContinuousMap.id I)) rfl rfl

/-- Helper for Theorem 2.7.1: the upper horizontal edge of the unit square. -/
noncomputable def unit_square_top_path :
    Path ((0 : I), (1 : I)) ((1 : I), (1 : I)) :=
  Path.mk ((ContinuousMap.id I).prodMk (ContinuousMap.const I (1 : I))) rfl rfl

/-- Helper for Theorem 2.7.1: the two L-shaped boundary paths of the unit square are homotopic
rel endpoints. -/
theorem unit_square_boundary_paths_homotopic :
    (Path.trans unit_square_bottom_path unit_square_right_path).Homotopic
      (Path.trans unit_square_left_path unit_square_top_path) := by
  let pBottom := unit_square_bottom_path
  let pRight := unit_square_right_path
  let pLeft := unit_square_left_path
  let pTop := unit_square_top_path
  change (Path.trans pBottom pRight).Homotopic (Path.trans pLeft pTop)
  let pBR : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) := Path.trans pBottom pRight
  let pLT : Path ((0 : I), (0 : I)) ((1 : I), (1 : I)) := Path.trans pLeft pTop
  refine ⟨{
    toFun := fun x : I × I ↦
      (Set.Icc.convexCombo (pBR x.2).1 (pLT x.2).1 x.1,
        Set.Icc.convexCombo (pBR x.2).2 (pLT x.2).2 x.1)
    continuous_toFun := by
      fun_prop
    map_zero_left := by
      intro s
      ext <;> simp [pBR, pLT, Path.trans_apply]
    map_one_left := by
      intro s
      ext <;> simp [pBR, pLT, Path.trans_apply]
    prop' := by
      intro t s hs
      rcases hs with rfl | rfl
      · ext <;> simp [pBR, pLT, Path.trans_apply]
      · have hpBR : pBR 1 = ((1 : I), (1 : I)) := by
          simp [pBR, pBottom, pRight, Path.trans_apply]
        have hpLT : pLT 1 = ((1 : I), (1 : I)) := by
          simp [pLT, pLeft, pTop, Path.trans_apply]
        ext <;> simp [hpBR, hpLT]
  }⟩

/-- Helper for Theorem 2.7.1: a cover-subordinate rectangle lifts to a single cover member, and
its ambient image is the expected affine reparametrization of the original square map. -/
theorem cell_map_boundary_paths_eq_lifted_edges
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (f : C(I × I, X))
    {a b c d : I}
    (hab : a ≤ b) (hcd : c ≤ d)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hcell : Set.Icc a b ×ˢ Set.Icc c d ⊆ f ⁻¹' (O i : Set X)) :
    ∃ cellMap : C(I × I, O i),
      ∀ x : I × I,
        ((cellMap x : O i) : X) =
          f (Set.Icc.convexCombo a b x.1, Set.Icc.convexCombo c d x.2) := by
  refine ⟨?_, ?_⟩
  · refine
      { toFun := fun x ↦
          ⟨f (Set.Icc.convexCombo a b x.1, Set.Icc.convexCombo c d x.2), ?_⟩
        continuous_toFun := ?_ }
    · exact
        hcell
          ⟨⟨Set.Icc.le_convexCombo hab x.1, Set.Icc.convexCombo_le hab x.1⟩,
            ⟨Set.Icc.le_convexCombo hcd x.2, Set.Icc.convexCombo_le hcd x.2⟩⟩
    · refine (f.continuous.comp ?_).subtype_mk ?_
      · continuity
  · intro x
    rfl

/-- Helper for Theorem 2.7.1: after lifting one square cell into a single cover member, the four
mapped unit-square boundary paths recover the corresponding affine boundary edges of the original
square map in the ambient space. -/
theorem cell_map_boundary_paths_eq_local_subpaths
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (f : C(I × I, X))
    {a b c d : I}
    (hab : a ≤ b) (hcd : c ≤ d)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hcell : Set.Icc a b ×ˢ Set.Icc c d ⊆ f ⁻¹' (O i : Set X)) :
    ∃ cellMap : C(I × I, O i),
      (∀ s : I,
        ((unit_square_bottom_path.map cellMap.continuous).map
            (show Continuous ((↑) : O i → X) by continuity) s) =
          f (Set.Icc.convexCombo a b s, c)) ∧
      (∀ s : I,
        ((unit_square_right_path.map cellMap.continuous).map
            (show Continuous ((↑) : O i → X) by continuity) s) =
          f (b, Set.Icc.convexCombo c d s)) ∧
      (∀ s : I,
        ((unit_square_left_path.map cellMap.continuous).map
            (show Continuous ((↑) : O i → X) by continuity) s) =
          f (a, Set.Icc.convexCombo c d s)) ∧
      (∀ s : I,
        ((unit_square_top_path.map cellMap.continuous).map
            (show Continuous ((↑) : O i → X) by continuity) s) =
          f (Set.Icc.convexCombo a b s, d)) := by
  have hincl : Continuous ((↑) : O i → X) := by
    continuity
  obtain ⟨cellMap, hcellMap⟩ :=
    cell_map_boundary_paths_eq_lifted_edges
      (O := O)
      f
      hab
      hcd
      (i := i)
      hcell
  refine ⟨cellMap, ?_⟩
  constructor
  · intro s
    -- The lower unit-square edge keeps the second coordinate fixed at `c`.
    simpa [unit_square_bottom_path] using hcellMap (s, (0 : I))
  constructor
  · intro s
    -- The right unit-square edge keeps the first coordinate fixed at `b`.
    simpa [unit_square_right_path] using hcellMap ((1 : I), s)
  constructor
  · intro s
    -- The left unit-square edge keeps the first coordinate fixed at `a`.
    simpa [unit_square_left_path] using hcellMap ((0 : I), s)
  · intro s
    -- The upper unit-square edge keeps the second coordinate fixed at `d`.
    simpa [unit_square_top_path] using hcellMap (s, (1 : I))

/-- Helper for Theorem 2.7.1: if a subtype-valued path in one cover member has the same ambient
image as a prescribed ambient subpath, then its chosen subdivision computes the corresponding
local subpath morphism. -/
theorem mapped_cell_edge_chosen_subdivision_eq_local_subpath
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} (γ : Path x y) (a b : I)
    {i : TopologicalSpace.IsOpenCover.Index O}
    (hsub : Set.range (γ.subpath a b) ⊆ O i)
    {x₀ y₀ : O i}
    (η : Path x₀ y₀)
    (hη :
      ∀ s : I,
        ((η.map (show Continuous ((↑) : O i → X) by continuity)) s) = γ.subpath a b s) :
    chosen_subdivision_morphism O hO hinter S
        (η.map (show Continuous ((↑) : O i → X) by continuity)) ≍
      local_subpath_morphism O hO hinter S γ a b i hsub := by
  have hs :
      x₀ = (⟨γ a, subpath_source_mem_of_range_subset γ a b hsub⟩ : O i) := by
    -- Evaluate the ambient path identity at the source parameter to align the subtype source.
    apply Subtype.ext
    simpa using hη 0
  have ht :
      y₀ = (⟨γ b, subpath_target_mem_of_range_subset γ a b hsub⟩ : O i) := by
    -- Evaluating at the target parameter gives the matching subtype endpoint on the right.
    apply Subtype.ext
    simpa using hη 1
  subst x₀
  subst y₀
  -- Once the subtype endpoints are normalized, the existing one-open local-subpath theorem
  -- applies directly to the mapped edge.
  exact
    (chosen_subdivision_morphism_eq_local_subpath_of_subtype_path_eq
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (a := a)
      (b := b)
      (i := i)
      (hsub := hsub)
      (η := η)
      hη).heq

/-- Helper for Theorem 2.7.1: an interior horizontal slice of the homotopy grid yields the same
normalized subdivision morphism whether it is labelled from the strip below or from the strip
above. -/
theorem horizontal_slice_relabel_eq
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X}
    {m : ℕ}
    (horizontalPath : I → Path x y)
    (t : Fin (m + 2) → I)
    (u : Fin (m + 1) → Fin (m + 1) → TopologicalSpace.IsOpenCover.Index O)
    (hcell_top :
      ∀ k l : Fin (m + 1),
        Set.range (((horizontalPath (t k.succ)).subpath (t l.castSucc) (t l.succ))) ⊆
          O (u k l))
    (hcell_bottom :
      ∀ k l : Fin (m + 1),
        Set.range (((horizontalPath (t k.castSucc)).subpath (t l.castSucc) (t l.succ))) ⊆
          O (u k l))
    (ht0 : t 0 = 0)
    (ht1 : t (Fin.last (m + 1)) = 1)
    (hx :
      ∀ k : Fin m,
        horizontalPath (t k.succ.castSucc) (t 0) = x)
    (hy :
      ∀ k : Fin m,
        horizontalPath (t k.succ.castSucc) (t (Fin.last (m + 1))) = y) :
    ∀ k : Fin m,
      normalized_subdivision_morphism O hO hinter S
          (horizontalPath (t k.succ.castSucc))
          t
          (fun l ↦ u k.castSucc l)
          (hcell_top k.castSucc)
          (hx k)
          (hy k) =
        normalized_subdivision_morphism O hO hinter S
          (horizontalPath (t k.succ.castSucc))
          t
          (fun l ↦ u k.succ l)
          (hcell_bottom k.succ)
          (hx k)
          (hy k) := by
  intro k
  let _ := ht0
  let _ := ht1
  -- The breakpoint tuple is fixed, so changing only the row labels does not affect the normalized
  -- subdivision morphism.
  exact
    normalized_subdivision_morphism_eq_of_same_points
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := horizontalPath (t k.succ.castSucc))
      (t := t)
      (u := fun l ↦ u k.castSucc l)
      (v := fun l ↦ u k.succ l)
      (hu := hcell_top k.castSucc)
      (hv := hcell_bottom k.succ)
      (hx := hx k)
      (hy := hy k)

/-- Helper for Theorem 2.7.1: endpoint-fixed homotopic paths induce the same chosen-subdivision
composite in the cocone target. -/
theorem chosen_subdivision_morphism_eq_of_homotopic
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y : X} {γ γ' : Path x y}
    (hγ : Path.Homotopic γ γ') :
    chosen_subdivision_morphism O hO hinter S γ =
      chosen_subdivision_morphism O hO hinter S γ' := by
  rcases hγ with ⟨H⟩
  obtain ⟨n, t, ht0, ht1, htmono, u, hu⟩ :=
    square_subdivision_data_of_open_cover O hO H.toContinuousMap
  have hn : n ≠ 0 := by
    intro hzero
    subst hzero
    have h01 : (0 : I) = 1 := by
      simpa [ht0] using ht1
    exact zero_ne_one h01
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  let horizontalPath : (r : I) → Path x y := fun r ↦ H.eval r
  let verticalPath : (s : I) → Path (γ s) (γ' s) := fun s ↦
    Path.mk
      ⟨fun r : I ↦ H (r, s), by continuity⟩
      (by
        have hs := H.map_zero_left s
        simpa using hs)
      (by
        have hs := H.map_one_left s
        simpa using hs)
  have hcell_bottom :
      ∀ k l : Fin (m + 1),
        Set.range (((horizontalPath (t k.castSucc)).subpath (t l.castSucc) (t l.succ))) ⊆
          O (u k l) := by
    intro k l
    refine vertical_edge_subset_of_square_cell_subset H.toContinuousMap
      (a := t k.castSucc) (b := t k.succ) (c := t l.castSucc) (d := t l.succ)
      ?_ (htmono (Nat.le_succ _)) (i := u k l) (hu k l)
    exact ⟨le_rfl, htmono (Nat.le_succ _)⟩
  have hcell_top :
      ∀ k l : Fin (m + 1),
        Set.range (((horizontalPath (t k.succ)).subpath (t l.castSucc) (t l.succ))) ⊆
          O (u k l) := by
    intro k l
    refine vertical_edge_subset_of_square_cell_subset H.toContinuousMap
      (a := t k.castSucc) (b := t k.succ) (c := t l.castSucc) (d := t l.succ)
      ?_ (htmono (Nat.le_succ _)) (i := u k l) (hu k l)
    exact ⟨htmono (Nat.le_succ _), le_rfl⟩
  have hcell_left :
      ∀ k l : Fin (m + 1),
        Set.range (((verticalPath (t l.castSucc)).subpath (t k.castSucc) (t k.succ))) ⊆
          O (u k l) := by
    intro k l
    refine horizontal_edge_subset_of_square_cell_subset H.toContinuousMap
      (a := t k.castSucc) (b := t k.succ) (c := t l.castSucc) (d := t l.succ)
      (htmono (Nat.le_succ _)) ?_ (i := u k l) (hu k l)
    exact ⟨le_rfl, htmono (Nat.le_succ _)⟩
  have hcell_right :
      ∀ k l : Fin (m + 1),
        Set.range (((verticalPath (t l.succ)).subpath (t k.castSucc) (t k.succ))) ⊆
          O (u k l) := by
    intro k l
    refine horizontal_edge_subset_of_square_cell_subset H.toContinuousMap
      (a := t k.castSucc) (b := t k.succ) (c := t l.castSucc) (d := t l.succ)
      (htmono (Nat.le_succ _)) ?_ (i := u k l) (hu k l)
    exact ⟨htmono (Nat.le_succ _), le_rfl⟩
  have hrelabel :
      ∀ k : Fin m,
        normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ.castSucc))
            t
            (fun l ↦ u k.castSucc l)
            (hcell_top k.castSucc)
            (by
              simp [horizontalPath, ht0])
            (by
              simp [horizontalPath, ht1]) =
          normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ.castSucc))
            t
            (fun l ↦ u k.succ l)
            (hcell_bottom k.succ)
            (by
              simp [horizontalPath, ht0])
            (by
              simp [horizontalPath, ht1]) := by
    have hx_row :
        ∀ k : Fin m,
          horizontalPath (t k.succ.castSucc) (t 0) = x := by
      intro k
      -- Every horizontal slice starts at the left endpoint of the homotopy square.
      simp [horizontalPath, ht0]
    have hy_row :
        ∀ k : Fin m,
          horizontalPath (t k.succ.castSucc) (t (Fin.last (m + 1))) = y := by
      intro k
      -- Every horizontal slice ends at the right endpoint of the homotopy square.
      simp [horizontalPath, ht1]
    -- Route correction: isolate the adjacent-row relabelling step as a reusable strip helper
    -- before returning to the remaining cell-boundary telescope.
    exact
      horizontal_slice_relabel_eq
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (horizontalPath := horizontalPath)
        (t := t)
        (u := u)
        (hcell_top := hcell_top)
        (hcell_bottom := hcell_bottom)
        (ht0 := ht0)
        (ht1 := ht1)
        (hx := hx_row)
        (hy := hy_row)
  have hcell_boundary :
      ∀ k l : Fin (m + 1),
        local_subpath_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t l.castSucc)
            (t l.succ)
            (u k l)
            (hcell_bottom k l) ≫
          local_subpath_morphism O hO hinter S
            (verticalPath (t l.succ))
            (t k.castSucc)
            (t k.succ)
            (u k l)
            (hcell_right k l) =
        local_subpath_morphism O hO hinter S
            (verticalPath (t l.castSucc))
            (t k.castSucc)
            (t k.succ)
            (u k l)
            (hcell_left k l) ≫
          local_subpath_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t l.castSucc)
            (t l.succ)
            (u k l)
            (hcell_top k l) := by
    intro k l
    obtain ⟨cellMap, hbottomEdge, hrightEdge, hleftEdge, htopEdge⟩ :=
      cell_map_boundary_paths_eq_local_subpaths
        (O := O)
        H.toContinuousMap
        (a := t k.castSucc)
        (b := t k.succ)
        (c := t l.castSucc)
        (d := t l.succ)
        (htmono (Nat.le_succ _))
        (htmono (Nat.le_succ _))
        (i := u k l)
        (hu k l)
    have hincl : Continuous ((↑) : O (u k l) → X) := by
      continuity
    have hleft :
        chosen_subdivision_morphism O hO hinter S
            ((unit_square_left_path.map cellMap.continuous).map hincl) ≍
          local_subpath_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t l.castSucc)
            (t l.succ)
            (u k l)
            (hcell_bottom k l) := by
      -- The left unit-square edge is the left vertical side of the homotopy cell, namely the
      -- lower horizontal slice restricted to the current column interval.
      simpa [horizontalPath] using
        mapped_cell_edge_chosen_subdivision_eq_local_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := horizontalPath (t k.castSucc))
          (a := t l.castSucc)
          (b := t l.succ)
          (i := u k l)
          (hsub := hcell_bottom k l)
          (η := unit_square_left_path.map cellMap.continuous)
          hleftEdge
    have htop :
        chosen_subdivision_morphism O hO hinter S
            ((unit_square_top_path.map cellMap.continuous).map hincl) ≍
          local_subpath_morphism O hO hinter S
            (verticalPath (t l.succ))
            (t k.castSucc)
            (t k.succ)
            (u k l)
            (hcell_right k l) := by
      -- The upper unit-square edge is the vertical path over the terminal column breakpoint.
      simpa [verticalPath] using
        mapped_cell_edge_chosen_subdivision_eq_local_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := verticalPath (t l.succ))
          (a := t k.castSucc)
          (b := t k.succ)
          (i := u k l)
          (hsub := hcell_right k l)
          (η := unit_square_top_path.map cellMap.continuous)
          htopEdge
    have hbottom :
        chosen_subdivision_morphism O hO hinter S
            ((unit_square_bottom_path.map cellMap.continuous).map hincl) ≍
          local_subpath_morphism O hO hinter S
            (verticalPath (t l.castSucc))
            (t k.castSucc)
            (t k.succ)
            (u k l)
            (hcell_left k l) := by
      -- The lower unit-square edge is the vertical path over the initial column breakpoint.
      simpa [verticalPath] using
        mapped_cell_edge_chosen_subdivision_eq_local_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := verticalPath (t l.castSucc))
          (a := t k.castSucc)
          (b := t k.succ)
          (i := u k l)
          (hsub := hcell_left k l)
          (η := unit_square_bottom_path.map cellMap.continuous)
          hbottomEdge
    have hright :
        chosen_subdivision_morphism O hO hinter S
            ((unit_square_right_path.map cellMap.continuous).map hincl) ≍
          local_subpath_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t l.castSucc)
            (t l.succ)
            (u k l)
            (hcell_top k l) := by
      -- The right unit-square edge is the upper horizontal slice restricted to the same column.
      simpa [horizontalPath] using
        mapped_cell_edge_chosen_subdivision_eq_local_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := horizontalPath (t k.succ))
          (a := t l.castSucc)
          (b := t l.succ)
          (i := u k l)
          (hsub := hcell_top k l)
          (η := unit_square_right_path.map cellMap.continuous)
          hrightEdge
    have hleftTop :
        chosen_subdivision_morphism O hO hinter S
            (((unit_square_left_path.trans unit_square_top_path).map cellMap.continuous).map
              hincl) ≍
          local_subpath_morphism O hO hinter S
              (horizontalPath (t k.castSucc))
              (t l.castSucc)
              (t l.succ)
              (u k l)
              (hcell_bottom k l) ≫
            local_subpath_morphism O hO hinter S
              (verticalPath (t l.succ))
              (t k.castSucc)
              (t k.succ)
              (u k l)
              (hcell_right k l) := by
      have hcorner00 :
          chosen_cover_object O hO S ↑(cellMap (0, 0)) =
            chosen_cover_object O hO S ((horizontalPath (t k.castSucc)) (t l.castSucc)) := by
        -- The lower-left corner of the lifted cell is the source of the left edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (0, 0) : O (u k l)) : X) =
                    ((unit_square_left_path.map cellMap.continuous).map hincl) 0 := by
                      rfl
                _ = (horizontalPath (t k.castSucc)) (t l.castSucc) := by
                      simpa [horizontalPath] using hleftEdge 0)
      have hcorner01 :
          chosen_cover_object O hO S ↑(cellMap (0, 1)) =
            chosen_cover_object O hO S ((horizontalPath (t k.castSucc)) (t l.succ)) := by
        -- The upper-left corner is the target of the left edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (0, 1) : O (u k l)) : X) =
                    ((unit_square_left_path.map cellMap.continuous).map hincl) 1 := by
                      rfl
                _ = (horizontalPath (t k.castSucc)) (t l.succ) := by
                      simpa [horizontalPath] using hleftEdge 1)
      have hcorner11 :
          chosen_cover_object O hO S ↑(cellMap (1, 1)) =
            chosen_cover_object O hO S ((verticalPath (t l.succ)) (t k.succ)) := by
        -- The upper-right corner is the target of the top edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (1, 1) : O (u k l)) : X) =
                    ((unit_square_top_path.map cellMap.continuous).map hincl) 1 := by
                      rfl
                _ = (verticalPath (t l.succ)) (t k.succ) := by
                      simpa [verticalPath] using htopEdge 1)
      have htrans :
          chosen_subdivision_morphism O hO hinter S
              (((unit_square_left_path.trans unit_square_top_path).map cellMap.continuous).map
                hincl) ≍
            chosen_subdivision_morphism O hO hinter S
                ((unit_square_left_path.map cellMap.continuous).map hincl) ≫
              chosen_subdivision_morphism O hO hinter S
                ((unit_square_top_path.map cellMap.continuous).map hincl) := by
        -- Split the left-then-top boundary path inside the single cover member of the cell.
        simpa [Path.map_trans] using
          (chosen_subdivision_morphism_trans_in_cover
            (hO := hO)
            (hinter := hinter)
            (S := S)
            (i := u k l)
            (γ := unit_square_left_path.map cellMap.continuous)
            (δ := unit_square_top_path.map cellMap.continuous)).heq
      exact
        htrans.trans
          (CategoryTheory.heq_comp hcorner00 hcorner01 hcorner11 hleft htop)
    have hbottomRight :
        chosen_subdivision_morphism O hO hinter S
            (((unit_square_bottom_path.trans unit_square_right_path).map cellMap.continuous).map
              hincl) ≍
          local_subpath_morphism O hO hinter S
              (verticalPath (t l.castSucc))
              (t k.castSucc)
              (t k.succ)
              (u k l)
              (hcell_left k l) ≫
            local_subpath_morphism O hO hinter S
              (horizontalPath (t k.succ))
              (t l.castSucc)
              (t l.succ)
              (u k l)
              (hcell_top k l) := by
      have hcorner00 :
          chosen_cover_object O hO S ↑(cellMap (0, 0)) =
            chosen_cover_object O hO S ((verticalPath (t l.castSucc)) (t k.castSucc)) := by
        -- The lower-left corner is the source of the bottom edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (0, 0) : O (u k l)) : X) =
                    ((unit_square_bottom_path.map cellMap.continuous).map hincl) 0 := by
                      rfl
                _ = (verticalPath (t l.castSucc)) (t k.castSucc) := by
                      simpa [verticalPath] using hbottomEdge 0)
      have hcorner10 :
          chosen_cover_object O hO S ↑(cellMap (1, 0)) =
            chosen_cover_object O hO S ((verticalPath (t l.castSucc)) (t k.succ)) := by
        -- The lower-right corner is the target of the bottom edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (1, 0) : O (u k l)) : X) =
                    ((unit_square_bottom_path.map cellMap.continuous).map hincl) 1 := by
                      rfl
                _ = (verticalPath (t l.castSucc)) (t k.succ) := by
                      simpa [verticalPath] using hbottomEdge 1)
      have hcorner11 :
          chosen_cover_object O hO S ↑(cellMap (1, 1)) =
            chosen_cover_object O hO S ((horizontalPath (t k.succ)) (t l.succ)) := by
        -- The upper-right corner is the target of the right edge.
        exact
          congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by
              calc
                ((cellMap (1, 1) : O (u k l)) : X) =
                    ((unit_square_right_path.map cellMap.continuous).map hincl) 1 := by
                      rfl
                _ = (horizontalPath (t k.succ)) (t l.succ) := by
                      simpa [horizontalPath] using hrightEdge 1)
      have htrans :
          chosen_subdivision_morphism O hO hinter S
              (((unit_square_bottom_path.trans unit_square_right_path).map
                  cellMap.continuous).map hincl) ≍
            chosen_subdivision_morphism O hO hinter S
                ((unit_square_bottom_path.map cellMap.continuous).map hincl) ≫
              chosen_subdivision_morphism O hO hinter S
                ((unit_square_right_path.map cellMap.continuous).map hincl) := by
        -- Split the bottom-then-right boundary path in the same way.
        simpa [Path.map_trans] using
          (chosen_subdivision_morphism_trans_in_cover
            (hO := hO)
            (hinter := hinter)
            (S := S)
            (i := u k l)
            (γ := unit_square_bottom_path.map cellMap.continuous)
            (δ := unit_square_right_path.map cellMap.continuous)).heq
      exact
        htrans.trans
          (CategoryTheory.heq_comp hcorner00 hcorner10 hcorner11 hbottom hright)
    have hboundary :
        chosen_subdivision_morphism O hO hinter S
            (((unit_square_left_path.trans unit_square_top_path).map cellMap.continuous).map
              hincl) =
          chosen_subdivision_morphism O hO hinter S
            (((unit_square_bottom_path.trans unit_square_right_path).map cellMap.continuous).map
              hincl) := by
      -- The two L-shaped boundary paths of the cell are homotopic rel endpoints inside the same
      -- cover member, so their chosen subdivisions agree.
      simpa [Path.map_trans] using
        chosen_subdivision_morphism_eq_of_homotopic_in_cover
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (i := u k l)
          (γ := (unit_square_left_path.trans unit_square_top_path).map cellMap.continuous)
          (γ' := (unit_square_bottom_path.trans unit_square_right_path).map cellMap.continuous)
          ((unit_square_boundary_paths_homotopic.symm).map cellMap)
    -- The cell comparison is exactly the left/top versus bottom/right boundary equality after the
    -- four edge identifications.
    exact eq_of_heq <| hleftTop.symm.trans (hboundary.heq.trans hbottomRight)
  have hstrip_raw :
      ∀ k : Fin (m + 1),
        subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k) ≍
          subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_top k) := by
    intro k
    let bottomPrefix :=
      fun l : Fin (m + 1) ↦
        subdivision_morphism O hO hinter S
          (horizontalPath (t k.castSucc))
          (t := shared_tuple_prefix_points t l.succ)
          (u := shared_tuple_prefix_labels (fun q ↦ u k q) l.succ)
          (shared_tuple_prefix_subordinate
            (horizontalPath (t k.castSucc))
            t
            (fun q ↦ u k q)
            (hcell_bottom k)
            l.succ)
    let topPrefix :=
      fun l : Fin (m + 1) ↦
        subdivision_morphism O hO hinter S
          (horizontalPath (t k.succ))
          (t := shared_tuple_prefix_points t l.succ)
          (u := shared_tuple_prefix_labels (fun q ↦ u k q) l.succ)
          (shared_tuple_prefix_subordinate
            (horizontalPath (t k.succ))
            t
            (fun q ↦ u k q)
            (hcell_top k)
            l.succ)
    let leftOuter :
        chosen_cover_object O hO S ((horizontalPath (t k.castSucc)) (t 0)) ⟶
          chosen_cover_object O hO S ((horizontalPath (t k.succ)) (t 0)) :=
      local_subpath_morphism O hO hinter S
        (verticalPath (t 0))
        (t k.castSucc)
        (t k.succ)
        (u k 0)
        (hcell_left k 0)
    have hprefix_balance :
        ∀ l : Fin (m + 1),
          bottomPrefix l ≫
              local_subpath_morphism O hO hinter S
                (verticalPath (t l.succ))
                (t k.castSucc)
                (t k.succ)
                (u k l)
                (hcell_right k l) =
            leftOuter ≫ topPrefix l := by
      -- The strip comparison is the source proof's row-prefix telescope: each new cell extends
      -- the previously balanced prefix by one more bottom/top segment and one interior vertical
      -- overlap that cancels.
      intro l
      refine Fin.induction ?_ ?_ l
      · -- The first prefix contains exactly one cell, so the strip invariant is the corresponding
        -- cell-boundary equality.
        simpa [bottomPrefix, topPrefix, leftOuter, shared_tuple_prefix_points,
          shared_tuple_prefix_labels, subdivision_morphism]
          using hcell_boundary k 0
      · intro j ih
        have hbottom_decomp :
            bottomPrefix j.succ =
              bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                  (horizontalPath (t k.castSucc))
                  (t j.succ.castSucc)
                  (t j.succ.succ)
                  (u k j.succ)
                  (hcell_bottom k j.succ) := by
          -- One recursive unfold of the longer literal bottom prefix isolates its new terminal
          -- bottom edge.
          dsimp [bottomPrefix]
          simpa using
            (subdivision_morphism_prefix_decomposition_at_cutpoint
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := horizontalPath (t k.castSucc))
              (w := t)
              (v := fun q ↦ u k q)
              (hv := hcell_bottom k)
              (k := j.succ)).trans
            (by
              exact
              congrArg
                (fun f ↦
                  f ≫
                    local_subpath_morphism O hO hinter S
                      (horizontalPath (t k.castSucc))
                      (t j.succ.castSucc)
                      (t j.succ.succ)
                      (u k j.succ)
                      (hcell_bottom k j.succ))
                (subdivision_morphism_shared_prefix_recursive_eq
                  (hO := hO)
                  (hinter := hinter)
                  (S := S)
                  (γ := horizontalPath (t k.castSucc))
                  (w := t)
                  (v := fun q ↦ u k q)
                  (hv := hcell_bottom k)
                  (k := j.succ)))
        have htop_decomp :
            topPrefix j.succ =
              topPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                  (horizontalPath (t k.succ))
                  (t j.succ.castSucc)
                  (t j.succ.succ)
                  (u k j.succ)
                  (hcell_top k j.succ) := by
          -- The top prefix unfolds in the same way.
          dsimp [topPrefix]
          simpa using
            (subdivision_morphism_prefix_decomposition_at_cutpoint
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := horizontalPath (t k.succ))
              (w := t)
              (v := fun q ↦ u k q)
              (hv := hcell_top k)
              (k := j.succ)).trans
            (by
              exact
              congrArg
                (fun f ↦
                  f ≫
                    local_subpath_morphism O hO hinter S
                      (horizontalPath (t k.succ))
                      (t j.succ.castSucc)
                      (t j.succ.succ)
                      (u k j.succ)
                      (hcell_top k j.succ))
                (subdivision_morphism_shared_prefix_recursive_eq
                  (hO := hO)
                  (hinter := hinter)
                  (S := S)
                  (γ := horizontalPath (t k.succ))
                  (w := t)
                  (v := fun q ↦ u k q)
                  (hv := hcell_top k)
                  (k := j.succ)))
        have hoverlap :
            local_subpath_morphism O hO hinter S
                (verticalPath (t j.castSucc.succ))
                (t k.castSucc)
                (t k.succ)
                (u k j.castSucc)
                (hcell_right k j.castSucc) =
              local_subpath_morphism O hO hinter S
                (verticalPath (t j.succ.castSucc))
                (t k.castSucc)
                (t k.succ)
                (u k j.succ)
                (hcell_left k j.succ) := by
          -- The interior vertical edge shared by adjacent cells is independent of which cell label
          -- is used to view it.
          simpa using
            local_subpath_morphism_eq_of_overlap
              hO
              hinter
              S
              (verticalPath (t j.succ.castSucc))
              (t k.castSucc)
              (t k.succ)
              (u k j.castSucc)
              (u k j.succ)
              (hcell_right k j.castSucc)
              (hcell_left k j.succ)
        -- Reassociate the longer bottom prefix, replace the interior shared vertical factor by the
        -- adjacent-cell view, and then insert the next cell-boundary equality.
        have hstep₁ :
            bottomPrefix j.succ ≫
                local_subpath_morphism O hO hinter S
                  (verticalPath (t j.succ.succ))
                  (t k.castSucc)
                  (t k.succ)
                  (u k j.succ)
                  (hcell_right k j.succ) =
              bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.castSucc))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_bottom k j.succ) ≫
                  local_subpath_morphism O hO hinter S
                    (verticalPath (t j.succ.succ))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.succ)
                    (hcell_right k j.succ) := by
          rw [hbottom_decomp]
          exact Category.assoc _ _ _
        have hstep₂ :
            bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.castSucc))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_bottom k j.succ) ≫
                  local_subpath_morphism O hO hinter S
                    (verticalPath (t j.succ.succ))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.succ)
                    (hcell_right k j.succ) =
              bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (verticalPath (t j.succ.castSucc))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.succ)
                    (hcell_left k j.succ) ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦ bottomPrefix j.castSucc ≫ f)
              (hcell_boundary k j.succ)
        have hstep₃ :
            bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (verticalPath (t j.succ.castSucc))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.succ)
                    (hcell_left k j.succ) ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) =
              bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (verticalPath (t j.castSucc.succ))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.castSucc)
                    (hcell_right k j.castSucc) ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) := by
          simpa [Category.assoc] using
            congrArg
              (fun f ↦
                bottomPrefix j.castSucc ≫
                  f ≫
                    local_subpath_morphism O hO hinter S
                      (horizontalPath (t k.succ))
                      (t j.succ.castSucc)
                      (t j.succ.succ)
                      (u k j.succ)
                      (hcell_top k j.succ))
              hoverlap.symm
        have hstep₄ :
            bottomPrefix j.castSucc ≫
                local_subpath_morphism O hO hinter S
                    (verticalPath (t j.castSucc.succ))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.castSucc)
                    (hcell_right k j.castSucc) ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) =
              leftOuter ≫
                topPrefix j.castSucc ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) := by
          have hstep₄raw :
              (bottomPrefix j.castSucc ≫
                  local_subpath_morphism O hO hinter S
                    (verticalPath (t j.castSucc.succ))
                    (t k.castSucc)
                    (t k.succ)
                    (u k j.castSucc)
                    (hcell_right k j.castSucc)) ≫
                local_subpath_morphism O hO hinter S
                  (horizontalPath (t k.succ))
                  (t j.succ.castSucc)
                  (t j.succ.succ)
                  (u k j.succ)
                  (hcell_top k j.succ) =
              (leftOuter ≫ topPrefix j.castSucc) ≫
                local_subpath_morphism O hO hinter S
                  (horizontalPath (t k.succ))
                  (t j.succ.castSucc)
                  (t j.succ.succ)
                  (u k j.succ)
                  (hcell_top k j.succ) := by
            exact
              congrArg
                (fun f ↦
                  f ≫
                    local_subpath_morphism O hO hinter S
                      (horizontalPath (t k.succ))
                      (t j.succ.castSucc)
                      (t j.succ.succ)
                      (u k j.succ)
                      (hcell_top k j.succ))
                ih
          simpa [Category.assoc] using hstep₄raw
        have hstep₅ :
            leftOuter ≫
                topPrefix j.castSucc ≫
                  local_subpath_morphism O hO hinter S
                    (horizontalPath (t k.succ))
                    (t j.succ.castSucc)
                    (t j.succ.succ)
                    (u k j.succ)
                    (hcell_top k j.succ) =
              leftOuter ≫ topPrefix j.succ := by
          simpa [Category.assoc] using
            congrArg (fun f ↦ leftOuter ≫ f) htop_decomp.symm
        exact hstep₁.trans (hstep₂.trans (hstep₃.trans (hstep₄.trans hstep₅)))
    have hterminal :
        subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k) ≫
          local_subpath_morphism O hO hinter S
            (verticalPath (t (Fin.last (m + 1))))
            (t k.castSucc)
            (t k.succ)
            (u k (Fin.last m))
            (hcell_right k (Fin.last m)) =
        leftOuter ≫
          subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_top k) := by
      have hbottom_last :
          bottomPrefix (Fin.last m) =
            subdivision_morphism O hO hinter S
              (horizontalPath (t k.castSucc))
              (t := t)
              (u := fun l ↦ u k l)
              (hcell_bottom k) := by
        -- Specializing the literal prefix at the terminal column recovers the whole bottom row.
        have hbottom_last_heq :
            bottomPrefix (Fin.last m) ≍
              subdivision_morphism O hO hinter S
                (horizontalPath (t k.castSucc))
                (t := t)
                (u := fun l ↦ u k l)
                (hcell_bottom k) := by
          simpa [bottomPrefix] using
            subdivision_morphism_prefix_last_heq_self
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := horizontalPath (t k.castSucc))
              (w := t)
              (v := fun l ↦ u k l)
              (hv := hcell_bottom k)
        exact eq_of_heq hbottom_last_heq
      have htop_last :
          topPrefix (Fin.last m) =
            subdivision_morphism O hO hinter S
              (horizontalPath (t k.succ))
              (t := t)
              (u := fun l ↦ u k l)
                (hcell_top k) := by
        -- The same terminal-prefix normalization holds for the top row.
        have htop_last_heq :
            topPrefix (Fin.last m) ≍
              subdivision_morphism O hO hinter S
                (horizontalPath (t k.succ))
                (t := t)
                (u := fun l ↦ u k l)
                (hcell_top k) := by
          simpa [topPrefix] using
            subdivision_morphism_prefix_last_heq_self
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (γ := horizontalPath (t k.succ))
              (w := t)
              (v := fun l ↦ u k l)
              (hv := hcell_top k)
        exact eq_of_heq htop_last_heq
      simpa [hbottom_last, htop_last] using hprefix_balance (Fin.last m)
    have hleft_boundary :
        ∀ r : I, (verticalPath (t 0)) r = x := by
      -- The left side of the homotopy square is fixed at the common source point `x`.
      intro r
      have hr :=
        H.prop' r (t 0) (by
          left
          simpa [ht0])
      calc
        (verticalPath (t 0)) r = γ (t 0) := by
          simpa [verticalPath] using hr
        _ = x := by
          simpa [ht0]
    have hright_boundary :
        ∀ r : I, (verticalPath (t (Fin.last (m + 1)))) r = y := by
      -- The right side of the homotopy square is fixed at the common target point `y`.
      intro r
      have hr :=
        H.prop' r (t (Fin.last (m + 1))) (by
          right
          simpa using ht1)
      calc
        (verticalPath (t (Fin.last (m + 1)))) r = γ (t (Fin.last (m + 1))) := by
          simpa [verticalPath] using hr
        _ = y := by
          simpa [ht1]
    have hleft_obj_eq :
        (verticalPath (t 0)) (t k.castSucc) = (verticalPath (t 0)) (t k.succ) := by
      calc
        (verticalPath (t 0)) (t k.castSucc) = x := hleft_boundary (t k.castSucc)
        _ = (verticalPath (t 0)) (t k.succ) := by
          symm
          exact hleft_boundary (t k.succ)
    have hright_obj_eq :
        (verticalPath (t (Fin.last (m + 1)))) (t k.castSucc) =
          (verticalPath (t (Fin.last (m + 1)))) (t k.succ) := by
      calc
        (verticalPath (t (Fin.last (m + 1)))) (t k.castSucc) = y := hright_boundary (t k.castSucc)
        _ = (verticalPath (t (Fin.last (m + 1)))) (t k.succ) := by
          symm
          exact hright_boundary (t k.succ)
    have hleft_const :
        leftOuter =
          eqToHom
              (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hleft_obj_eq) := by
      have hconst :
          ∀ s : I,
            (verticalPath (t 0)).subpath (t k.castSucc) (t k.succ) s =
              (verticalPath (t 0)) 0 := by
        -- The left boundary of the homotopy square is fixed at the common source object.
        intro s
        calc
          (verticalPath (t 0)).subpath (t k.castSucc) (t k.succ) s = x := by
            simpa [Path.subpath] using hleft_boundary (Set.Icc.convexCombo (t k.castSucc) (t k.succ) s)
          _ = (verticalPath (t 0)) 0 := by
            symm
            simpa using hleft_boundary 0
      have hleft_raw :=
        local_subpath_morphism_eq_eqToHom_of_constant_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := verticalPath (t 0))
          (a := t k.castSucc)
          (b := t k.succ)
          (c := 0)
          (i := u k 0)
          (hsub := hcell_left k 0)
          hconst
      simpa [leftOuter, hleft_obj_eq, Category.assoc] using hleft_raw
    have hright_const :
        local_subpath_morphism O hO hinter S
            (verticalPath (t (Fin.last (m + 1))))
            (t k.castSucc)
            (t k.succ)
            (u k (Fin.last m))
            (hcell_right k (Fin.last m)) =
          eqToHom
              (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hright_obj_eq) := by
      have hconst :
          ∀ s : I,
            (verticalPath (t (Fin.last (m + 1)))).subpath (t k.castSucc) (t k.succ) s =
              (verticalPath (t (Fin.last (m + 1)))) 0 := by
        -- The right boundary of the homotopy square is fixed at the common target object.
        intro s
        calc
          (verticalPath (t (Fin.last (m + 1)))).subpath (t k.castSucc) (t k.succ) s = y := by
            simpa [Path.subpath] using
              hright_boundary (Set.Icc.convexCombo (t k.castSucc) (t k.succ) s)
          _ = (verticalPath (t (Fin.last (m + 1)))) 0 := by
            symm
            simpa using hright_boundary 0
      have hright_raw :=
        local_subpath_morphism_eq_eqToHom_of_constant_subpath
          (hO := hO)
          (hinter := hinter)
          (S := S)
          (γ := verticalPath (t (Fin.last (m + 1))))
          (a := t k.castSucc)
          (b := t k.succ)
          (c := 0)
          (i := u k (Fin.last m))
          (hsub := hcell_right k (Fin.last m))
          hconst
      simpa [hright_obj_eq, Category.assoc] using hright_raw
    -- After the strip telescope is specialized at the terminal column, the only remaining factors
    -- are the two constant outer vertical edges, so the result is exactly the endpoint transport
    -- conjugation form of the desired heterogeneous equality.
    have hconj :
        subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k) =
          (eqToHom
              (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hleft_obj_eq) ≫
            subdivision_morphism O hO hinter S
              (horizontalPath (t k.succ))
              (t := t)
              (u := fun l ↦ u k l)
              (hcell_top k)) ≫
            eqToHom
              (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hright_obj_eq).symm := by
      rw [hleft_const, hright_const] at hterminal
      exact
        (CategoryTheory.comp_eqToHom_iff
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hright_obj_eq)
          (subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k))
          (eqToHom (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hleft_obj_eq) ≫
            subdivision_morphism O hO hinter S
              (horizontalPath (t k.succ))
              (t := t)
              (u := fun l ↦ u k l)
              (hcell_top k))).mp hterminal
    exact
      (CategoryTheory.conj_eqToHom_iff_heq
        (subdivision_morphism O hO hinter S
          (horizontalPath (t k.castSucc))
          (t := t)
          (u := fun l ↦ u k l)
          (hcell_bottom k))
        (subdivision_morphism O hO hinter S
          (horizontalPath (t k.succ))
          (t := t)
          (u := fun l ↦ u k l)
          (hcell_top k))
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hleft_obj_eq)
        (congrArg (fun z : X ↦ chosen_cover_object O hO S z) hright_obj_eq)).1
        (by simpa [Category.assoc] using hconj)
  -- Route correction: the adjacent-row relabeling step is already verified, but the proof still
  -- needs the cell-boundary normalization and strip telescope to connect the explicit bottom and
  -- top subdivisions.
  have hbottom :
      chosen_subdivision_morphism O hO hinter S γ =
        normalized_subdivision_morphism O hO hinter S
          (horizontalPath (t 0))
          t
          (fun l ↦ u 0 l)
          (hcell_bottom 0)
          (by simp [horizontalPath, ht0])
          (by simp [horizontalPath, ht1]) := by
    -- Rewrite `γ` as the explicit bottom horizontal slice of the homotopy grid.
    simpa [horizontalPath, ht0] using
      (chosen_subdivision_morphism_eq_explicit_subdivision
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := horizontalPath (t 0))
        (t := t)
        (hn := hn)
        (ht0 := ht0)
        (ht1 := ht1)
        (hmono := htmono)
        (u := fun l ↦ u 0 l)
        (hu := hcell_bottom 0)
        (hx := by simp [horizontalPath, ht0])
        (hy := by simp [horizontalPath, ht1]))
  have hstrip :
      ∀ k : Fin (m + 1),
        normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            t
            (fun l ↦ u k l)
            (hcell_bottom k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]) =
          normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            t
            (fun l ↦ u k l)
            (hcell_top k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]) := by
    intro k
    -- Transport the raw strip comparison to the fixed endpoint objects `x` and `y`.
    have hleft_raw :
        normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            t
            (fun l ↦ u k l)
            (hcell_bottom k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]) ≍
          subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k) := by
      exact
        (CategoryTheory.conj_eqToHom_iff_heq
          (normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            t
            (fun l ↦ u k l)
            (hcell_bottom k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]))
          (subdivision_morphism O hO hinter S
            (horizontalPath (t k.castSucc))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_bottom k))
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by simp [horizontalPath, ht0])).symm
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by simp [horizontalPath, ht1])).symm).1
          rfl
    have hright_raw :
        normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            t
            (fun l ↦ u k l)
            (hcell_top k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]) ≍
          subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_top k) := by
      exact
        (CategoryTheory.conj_eqToHom_iff_heq
          (normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            t
            (fun l ↦ u k l)
            (hcell_top k)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]))
          (subdivision_morphism O hO hinter S
            (horizontalPath (t k.succ))
            (t := t)
            (u := fun l ↦ u k l)
            (hcell_top k))
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by simp [horizontalPath, ht0])).symm
          (congrArg (fun z : X ↦ chosen_cover_object O hO S z)
            (by simp [horizontalPath, ht1])).symm).1
          rfl
    exact eq_of_heq ((hleft_raw.trans (hstrip_raw k)).trans hright_raw.symm)
  have htop :
      chosen_subdivision_morphism O hO hinter S γ' =
        normalized_subdivision_morphism O hO hinter S
          (horizontalPath (t (Fin.last (m + 1))))
          t
          (fun l ↦ u (Fin.last m) l)
          (hcell_top (Fin.last m))
          (by simp [horizontalPath, ht0])
          (by simp [horizontalPath, ht1]) := by
    -- Rewrite `γ'` as the explicit top horizontal slice of the homotopy grid.
    simpa [horizontalPath, ht1] using
      (chosen_subdivision_morphism_eq_explicit_subdivision
        (hO := hO)
        (hinter := hinter)
        (S := S)
        (γ := horizontalPath (t (Fin.last (m + 1))))
        (t := t)
        (hn := hn)
        (ht0 := ht0)
        (ht1 := ht1)
        (hmono := htmono)
        (u := fun l ↦ u (Fin.last m) l)
        (hu := hcell_top (Fin.last m))
        (hx := by simp [horizontalPath, ht0])
        (hy := by simp [horizontalPath, ht1]))
  have hrows :
      ∀ r : ℕ, ∀ hr : r ≤ m,
        chosen_subdivision_morphism O hO hinter S γ =
          normalized_subdivision_morphism O hO hinter S
            (horizontalPath (t ⟨r + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hr)⟩))
            t
            (fun l ↦ u ⟨r, Nat.lt_succ_of_le hr⟩ l)
            (hcell_top ⟨r, Nat.lt_succ_of_le hr⟩)
            (by simp [horizontalPath, ht0])
            (by simp [horizontalPath, ht1]) := by
    intro r hr
    induction r with
    | zero =>
        -- The first strip compares the bottom row with the next horizontal slice.
        simpa using hbottom.trans (hstrip 0)
    | succ r ih =>
        have hr_le : r ≤ m := Nat.le_of_succ_le hr
        have hr_lt_m : r < m := by
          exact Nat.lt_of_succ_le hr
        -- Move from the current strip label to the next one on the shared intermediate row.
        calc
          chosen_subdivision_morphism O hO hinter S γ =
              normalized_subdivision_morphism O hO hinter S
                (horizontalPath (t ⟨r + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hr_le)⟩))
                t
                (fun l ↦ u ⟨r, Nat.lt_succ_of_le hr_le⟩ l)
                (hcell_top ⟨r, Nat.lt_succ_of_le hr_le⟩)
                (by simp [horizontalPath, ht0])
                (by simp [horizontalPath, ht1]) := by
            exact ih hr_le
          _ =
              normalized_subdivision_morphism O hO hinter S
                (horizontalPath (t ⟨r + 1, Nat.succ_lt_succ (Nat.lt_succ_of_le hr_le)⟩))
                t
                (fun l ↦ u ⟨r + 1, Nat.lt_succ_of_le hr⟩ l)
                (hcell_bottom ⟨r + 1, Nat.lt_succ_of_le hr⟩)
                (by simp [horizontalPath, ht0])
                (by simp [horizontalPath, ht1]) := by
            -- Relabel the shared row from the strip below to the strip above.
            simpa using hrelabel ⟨r, hr_lt_m⟩
          _ =
              normalized_subdivision_morphism O hO hinter S
                (horizontalPath (t ⟨r + 2, Nat.succ_lt_succ (Nat.lt_succ_of_le hr)⟩))
                t
                (fun l ↦ u ⟨r + 1, Nat.lt_succ_of_le hr⟩ l)
                (hcell_top ⟨r + 1, Nat.lt_succ_of_le hr⟩)
                (by simp [horizontalPath, ht0])
                (by simp [horizontalPath, ht1]) := by
            -- Then apply the strip comparison for the next cell row.
            simpa using hstrip ⟨r + 1, Nat.lt_succ_of_le hr⟩
  -- The bottom explicit subdivision reaches the top explicit subdivision after traversing all
  -- strips, and the top explicit subdivision is exactly `γ'`.
  simpa using (hrows m (Nat.le_refl m)).trans htop.symm

/-- Helper for Theorem 2.7.1: the chosen-subdivision composite of a constant path is the identity
of the chosen endpoint object. -/
theorem chosen_subdivision_morphism_refl
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    (x : X) :
    chosen_subdivision_morphism O hO hinter S (Path.refl x) =
      𝟙 (chosen_cover_object O hO S x) := by
  let i : TopologicalSpace.IsOpenCover.Index O := chosen_cover_index O hO x
  let x' : O i := ⟨x, mem_chosen_cover_index O hO x⟩
  have hcover :=
    chosen_subdivision_morphism_eq_cover_leg_map
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (i := i)
      (x := x')
      (y := x')
      (γ := Path.refl x')
  -- The ambient image of the constant subtype path is just `Path.refl x`, and the induced local
  -- path class is the identity.
  calc
    chosen_subdivision_morphism O hO hinter S (Path.refl x) =
        chosen_subdivision_morphism O hO hinter S
          ((Path.refl x').map (show Continuous ((↑) : O i → X) by continuity)) := by
      rfl
    _ =
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x')
          (show (x' : X) ∈ O i by exact x'.property)) ≫
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦Path.refl x'⟧) ≫
        eqToHom (chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x')
          (show (x' : X) ∈ O i by exact x'.property)).symm := hcover
    _ = 𝟙 (chosen_cover_object O hO S x) := by
      have hmap_id :
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦Path.refl x'⟧) =
            𝟙 ((S.ι.app i).obj (FundamentalGroupoid.mk x')) := by
        have hpath_id :
            FundamentalGroupoid.fromPath ⟦Path.refl x'⟧ =
              𝟙 (FundamentalGroupoid.mk x') := by
          simpa using (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk x')).symm
        have hmap_id' :
            (S.ι.app i).map (𝟙 (FundamentalGroupoid.mk x')) =
              𝟙 ((S.ι.app i).obj (FundamentalGroupoid.mk x')) := by
          exact (S.ι.app i).map_id (FundamentalGroupoid.mk x')
        simpa [hpath_id] using hmap_id'
      simpa [hmap_id, chosen_cover_object, i, x']

/-- Helper for Theorem 2.7.1: the chosen-subdivision composite of a concatenation is the composite
of the chosen-subdivision composites of the two factors. -/
theorem chosen_subdivision_morphism_trans
    {O : ι → TopologicalSpace.Opens (TopCat.of X)}
    (hO : TopologicalSpace.IsOpenCover O)
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O))
    {x y z : X} (γ : Path x y) (δ : Path y z) :
    chosen_subdivision_morphism O hO hinter S (γ.trans δ) =
      chosen_subdivision_morphism O hO hinter S γ ≫
        chosen_subdivision_morphism O hO hinter S δ := by
  have hxγ : γ (chosen_subdivision_points O hO γ 0) = x := by
    -- The chosen subdivision of `γ` starts at the source of `γ`.
    simpa using chosen_subdivision_source_eq O hO γ
  have hyγ :
      γ
          (chosen_subdivision_points O hO γ
            (Fin.last (chosen_subdivision_length O hO γ))) = y := by
    -- The chosen subdivision of `γ` ends at the target of `γ`.
    simpa using chosen_subdivision_target_eq O hO γ
  have hyδ : δ (chosen_subdivision_points O hO δ 0) = y := by
    -- The chosen subdivision of `δ` starts at the common midpoint.
    simpa using chosen_subdivision_source_eq O hO δ
  have hzδ :
      δ
          (chosen_subdivision_points O hO δ
            (Fin.last (chosen_subdivision_length O hO δ))) = z := by
    -- The chosen subdivision of `δ` ends at the target of `δ`.
    simpa using chosen_subdivision_target_eq O hO δ
  obtain ⟨N, s, hN, hs0, hs1, hsmono, v, hv, hsx, hsz, hglue⟩ :=
    subdivision_morphism_trans_of_concatenated_subdivisions
      (hO := hO)
      (hinter := hinter)
      (S := S)
      (γ := γ)
      (δ := δ)
      (t := chosen_subdivision_points O hO γ)
      (hn := chosen_subdivision_length_ne_zero O hO γ)
      (ht0 := chosen_subdivision_points_zero O hO γ)
      (ht1 := chosen_subdivision_points_last O hO γ)
      (htmono := chosen_subdivision_points_monotone O hO γ)
      (u := chosen_subdivision_labels O hO γ)
      (hu := chosen_subdivision_subordinate O hO γ)
      (hx := hxγ)
      (hy := hyγ)
      (t' := chosen_subdivision_points O hO δ)
      (hm := chosen_subdivision_length_ne_zero O hO δ)
      (ht'0 := chosen_subdivision_points_zero O hO δ)
      (ht'1 := chosen_subdivision_points_last O hO δ)
      (ht'mono := chosen_subdivision_points_monotone O hO δ)
      (u' := chosen_subdivision_labels O hO δ)
      (hu' := chosen_subdivision_subordinate O hO δ)
      (hy' := hyδ)
      (hz := hzδ)
  -- Route correction: first replace the chosen subdivision of `γ.trans δ` by the explicit glued
  -- subdivision produced above, then compare with the chosen subdivisions of `γ` and `δ`.
  calc
    chosen_subdivision_morphism O hO hinter S (γ.trans δ) =
      normalized_subdivision_morphism O hO hinter S (γ.trans δ) s v hv hsx hsz := by
        exact
          chosen_subdivision_morphism_eq_explicit_subdivision
            (hO := hO)
            (hinter := hinter)
            (S := S)
            (γ := γ.trans δ)
            (t := s)
            (hn := hN)
            (ht0 := hs0)
            (ht1 := hs1)
            (hmono := hsmono)
            (u := v)
            (hu := hv)
            (hx := hsx)
            (hy := hsz)
    _ =
      normalized_subdivision_morphism O hO hinter S γ
          (chosen_subdivision_points O hO γ)
          (chosen_subdivision_labels O hO γ)
          (chosen_subdivision_subordinate O hO γ)
          hxγ
          hyγ ≫
        normalized_subdivision_morphism O hO hinter S δ
          (chosen_subdivision_points O hO δ)
          (chosen_subdivision_labels O hO δ)
          (chosen_subdivision_subordinate O hO δ)
          hyδ
          hzδ := hglue
    _ =
      chosen_subdivision_morphism O hO hinter S γ ≫
        chosen_subdivision_morphism O hO hinter S δ := by
      -- For the chosen subdivisions of `γ` and `δ`, the normalized explicit model is literally the
      -- defining expression of `chosen_subdivision_morphism`.
      rfl

/-- Helper for Theorem 2.7.1: once the path-subdivision construction is implemented, every cocone
over the cover diagram receives a unique factorization from the canonical cocone. -/
theorem fundamental_groupoid_cover_existsUnique
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O)
    (S : Cocone (fundamental_groupoid_cover_diagram O)) :
    ∃! d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt,
      ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i := by
  classical
  -- Route correction: the remaining work is the source-faithful path subdivision construction, not
  -- the categorical naturality of the cover cocone.
  -- The proved helpers above already force any candidate factorization to agree with the fixed
  -- subdivision composite on every chosen representative path, so uniqueness is now reduced to the
  -- existence of one well-defined functor on `Π(X)`.
  let _ := hpath
  have hex : ∃ d : (fundamental_groupoid_cover_cocone O).pt ⟶ S.pt,
      ∀ i, (fundamental_groupoid_cover_cocone O).ι.app i ≫ d = S.ι.app i := by
    -- Build the candidate factorization by sending each point of `Π(X)` to the chosen-cover
    -- object and each path class to the subdivision composite of a chosen subordinate
    -- representative subdivision.
    refine ⟨
      { obj := fun x ↦ chosen_cover_object O hO S x.as
        map := ?_
        map_id := ?_
        map_comp := ?_ },
      ?_⟩
    · intro x y p
      -- Package the representative-level subdivision composite into a named construction before
      -- descending it to the path-homotopy quotient.
      refine Quotient.lift (fun γ : Path x.as y.as ↦ chosen_subdivision_morphism O hO hinter S γ) ?_ p
      · intro γ γ' hγ
        -- Delegate the quotient well-definedness proof to the source-faithful homotopy-invariance
        -- lemma for the chosen subdivision construction.
        exact chosen_subdivision_morphism_eq_of_homotopic hO hinter S hγ
    · intro x
      -- The chosen subdivision of a constant path computes the identity morphism.
      simpa [FundamentalGroupoid.id_eq_path_refl] using
        chosen_subdivision_morphism_refl hO hinter S x.as
    · intro x y z p q
      refine Quotient.inductionOn₂ p q ?_
      intro γ δ
      -- On representatives, the chosen subdivision of a concatenation is computed by composing
      -- the chosen subdivisions of the two factors.
      change
        chosen_subdivision_morphism O hO hinter S (γ.trans δ) =
          chosen_subdivision_morphism O hO hinter S γ ≫
            chosen_subdivision_morphism O hO hinter S δ
      exact chosen_subdivision_morphism_trans hO hinter S γ δ
    · intro i
      -- Compare the factorization and the `i`-th cocone leg objectwise by the chosen-cover
      -- overlap equality, and compare them on path classes using the one-open subdivision model.
      refine Functor.hext ?_ ?_
      · intro x
        simpa [fundamental_groupoid_cover_cocone, chosen_cover_object] using
          chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x.as.1)
            (show x.as.1 ∈ O i by exact x.as.2)
      · intro x y p
        refine Quotient.inductionOn p ?_
        intro γ
        have hxeq : chosen_cover_object O hO S x.as.1 = (S.ι.app i).obj x := by
          simpa using
            chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := x.as.1)
              (show x.as.1 ∈ O i by exact x.as.2)
        have hyeq : chosen_cover_object O hO S y.as.1 = (S.ι.app i).obj y := by
          simpa using
            chosen_cover_object_eq_of_mem hO hinter S (i := i) (x := y.as.1)
              (show y.as.1 ∈ O i by exact y.as.2)
        change chosen_subdivision_morphism O hO hinter S
            (γ.map (show Continuous ((↑) : O i → X) by continuity)) ≍
          (S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧)
        exact
          (CategoryTheory.conj_eqToHom_iff_heq
            (chosen_subdivision_morphism O hO hinter S
              (γ.map (show Continuous ((↑) : O i → X) by continuity)))
            ((S.ι.app i).map (FundamentalGroupoid.fromPath ⟦γ⟧))
            hxeq
            hyeq).1 <|
            chosen_subdivision_morphism_eq_cover_leg_map
              (hO := hO)
              (hinter := hinter)
              (S := S)
              (i := i)
              (x := x.as)
              (y := y.as)
              (γ := γ)
  rcases hex with ⟨d, hd⟩
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  -- Any two such factorizations agree on objects and on every representative path, hence are
  -- equal as functors out of the fundamental groupoid.
  exact (factorization_unique_of_cover_legs O hO hinter S (d := d) (d' := d') hd hd').symm

/-- Theorem 2.7.1: if `O` is an open cover of `X` by path-connected open subsets and `O` is
closed under finite intersections, then the canonical cocone from the diagram `U ↦ Π(U)` to
`Π(X)` is a colimit cocone. -/
-- Proof sketch: use the cocone induced by the inclusions `U ↪ X`. For a cocone from the cover
-- diagram into another groupoid `C`, define the induced functor `Π(X) ⥤ C` on objects by
-- choosing a cover element containing each point, and on morphisms by subdividing paths into
-- pieces lying in members of the cover. Path connectedness handles choices of objects inside a
-- cover element, while closure under finite intersections controls compatibility on overlaps and
-- independence of subdivisions, yielding the universal property.
def fundamental_groupoid_is_colimit_of_path_connected_open_cover
    (O : ι → TopologicalSpace.Opens (TopCat.of X))
    (hO : TopologicalSpace.IsOpenCover O)
    (hpath : ∀ i, PathConnectedSpace (O i))
    (hinter : TopologicalSpace.IsOpenCover.ClosedUnderNonemptyFiniteIntersections O) :
    IsColimit (fundamental_groupoid_cover_cocone O) :=
  -- Reduce the colimit claim to the unique factorization property isolated above.
  IsColimit.ofExistsUnique (fundamental_groupoid_cover_existsUnique O hO hpath hinter)
