module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Connected.Clopen

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

namespace ConnectedComponentClopenCounterexample

/- Domain-style sampling:
- primary domain: point-set topology, specifically connected components and clopen neighborhoods;
- same-domain declarations inspected:
  `maximal_isConnected_iff_eq_connectedComponent`,
  `connectedComponent`,
  `IsClopen.connectedComponent_subset`,
  `connectedComponent_subset_iInter_isClopen`,
  `connectedComponent_eq_iInter_isClopen`;
- best owner abstraction: the canonical owner `connectedComponent x`, with clopen neighborhoods
  expressed through `IsClopen` and the owner theorem
  `connectedComponent_subset_iInter_isClopen`;
- core/canonical: `connectedComponent x`, `IsClopen`, and
  `connectedComponent_subset_iInter_isClopen`;
- source-facing: the explicit Stacks counterexample space from Remark 5.7.4, together with
  the two concrete set computations showing the canonical inclusion can be strict;
- bridge/view layer: the final strict-inclusion theorem is obtained by comparing the source-facing
  computations with the canonical owner theorem above, so no separate local wrapper around that
  owner API is introduced here.

The only primitive data that belongs in this file is the point set and its generated topology; the
connected-component/clopen interface itself is already owned upstream by mathlib. -/

/-- The points of the Stacks counterexample space from Remark 5.7.4. -/
inductive Point where
  | x
  | y
  | z (n : ℕ)
deriving DecidableEq

open Point

/-- The singleton basic open containing only `z n`. -/
def zSingleton (n : ℕ) : Set Point := {z n}

/-- The tail of all points `z m` with `m ≥ n`. -/
def zTail (n : ℕ) : Set Point := range fun m ↦ z (n + m)

/-- The basic open `{x, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
def xTail (n : ℕ) : Set Point := insert x (zTail n)

/-- The basic open `{y, z_n, z_{n + 1}, ...}` from the counterexample topology. -/
def yTail (n : ℕ) : Set Point := insert y (zTail n)

/-- The canonical topology on the counterexample point set. -/
instance : TopologicalSpace Point :=
  TopologicalSpace.generateFrom
    (range zSingleton ∪ range xTail ∪ range yTail)

/- Canonical owner recall: in any topological space, the connected component of a point is
contained in the intersection of all clopen neighborhoods of that point. This file only supplies a
counterexample showing that the inclusion can be strict. -/
recall connectedComponent_subset_iInter_isClopen {α : Type u} [TopologicalSpace α] {point : α} :
    connectedComponent point ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ point ∈ Z }, Z

/-- Helper for Remark 5.7.4: a point `z m` lies in the tail starting at `n` exactly when `n ≤ m`. -/
@[simp] private lemma mem_zTail_iff {m n : ℕ} : z m ∈ zTail n ↔ n ≤ m := by
  constructor
  · rintro ⟨k, hk⟩
    injection hk with hkm
    simpa [hkm] using Nat.le_add_right n k
  · intro h
    rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- Helper for Remark 5.7.4: later `z`-tails are contained in earlier ones. -/
private lemma zTail_mono {m n : ℕ} (h : m ≤ n) : zTail n ⊆ zTail m := by
  intro p hp
  cases p with
  | x =>
      simp [zTail] at hp
  | y =>
      simp [zTail] at hp
  | z k =>
      rw [mem_zTail_iff] at hp ⊢
      exact h.trans hp

/-- Helper for Remark 5.7.4: later `x`-tails are contained in earlier ones. -/
private lemma xTail_mono {m n : ℕ} (h : m ≤ n) : xTail n ⊆ xTail m := by
  intro p hp
  simp only [xTail, mem_insert_iff] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (zTail_mono h hp)

/-- Helper for Remark 5.7.4: later `y`-tails are contained in earlier ones. -/
private lemma yTail_mono {m n : ℕ} (h : m ≤ n) : yTail n ⊆ yTail m := by
  intro p hp
  simp only [yTail, mem_insert_iff] at hp ⊢
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · exact Or.inr (zTail_mono h hp)

/-- Helper for Remark 5.7.4: each basic `x`-tail is open in the generated topology. -/
private lemma xTail_isOpen (n : ℕ) : IsOpen (xTail n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) (xTail n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inl (Or.inr ⟨n, rfl⟩))

/-- Helper for Remark 5.7.4: each basic `y`-tail is open in the generated topology. -/
private lemma yTail_isOpen (n : ℕ) : IsOpen (yTail n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) (yTail n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inr ⟨n, rfl⟩)

/-- Helper for Remark 5.7.4: each singleton `{z n}` is one of the generating opens. -/
private lemma zSingleton_isOpen (n : ℕ) : IsOpen (zSingleton n) := by
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail)
    (zSingleton n)
  exact TopologicalSpace.GenerateOpen.basic _ (Or.inl (Or.inl ⟨n, rfl⟩))

/-- Helper for Remark 5.7.4: the tail `xTail (n + 1)` avoids the isolated point `z n`. -/
private lemma xTail_succ_subset_zSingleton_compl (n : ℕ) :
    xTail (n + 1) ⊆ (zSingleton n)ᶜ := by
  intro p hp
  cases p with
  | x =>
      simp [zSingleton]
  | y =>
      simp [xTail, zTail] at hp
  | z m =>
      have hm : n + 1 ≤ m := by
        simpa [xTail, mem_zTail_iff] using hp
      simp [zSingleton, Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)]

/-- Helper for Remark 5.7.4: the tail `yTail (n + 1)` avoids the isolated point `z n`. -/
private lemma yTail_succ_subset_zSingleton_compl (n : ℕ) :
    yTail (n + 1) ⊆ (zSingleton n)ᶜ := by
  intro p hp
  cases p with
  | x =>
      simp [yTail, zTail] at hp
  | y =>
      simp [zSingleton]
  | z m =>
      have hm : n + 1 ≤ m := by
        simpa [yTail, mem_zTail_iff] using hp
      simp [zSingleton, Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self n) hm)]

/-- Helper for Remark 5.7.4: a different isolated point stays in the complement of `{z n}`. -/
private lemma zSingleton_subset_zSingleton_compl {m n : ℕ} (h : m ≠ n) :
    zSingleton m ⊆ (zSingleton n)ᶜ := by
  intro p hp
  simp [zSingleton] at hp ⊢
  simpa [hp] using h

/-- Helper for Remark 5.7.4: any open neighborhood of `x` contains one of the basic `x`-tails. -/
private lemma xTail_subset_of_isOpen_of_mem {U : Set Point} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ n : ℕ, xTail n ⊆ U := by
  -- The generated topology can only reach `x` through an `x`-tail, and this persists under
  -- finite intersections and arbitrary unions.
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) U at hU
  let P : Set Point → Prop := fun V => x ∈ V → ∃ n : ℕ, xTail n ⊆ V
  have hP : ∀ {V : Set Point},
      TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) V → P V := by
    intro V hV
    induction hV with
    | basic s hs =>
        intro hxS
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · rcases hs with ⟨n, rfl⟩
            simp [zSingleton] at hxS
          · rcases hs with ⟨n, rfl⟩
            exact ⟨n, Subset.rfl⟩
        · rcases hs with ⟨n, rfl⟩
          simp [yTail, zTail] at hxS
    | univ =>
        intro _
        exact ⟨0, subset_univ _⟩
    | inter s t hs ht ihs iht =>
        intro hxST
        rcases ihs hxST.1 with ⟨m, hm⟩
        rcases iht hxST.2 with ⟨n, hn⟩
        refine ⟨max m n, ?_⟩
        intro p hp
        exact ⟨hm (xTail_mono (Nat.le_max_left _ _) hp), hn (xTail_mono (Nat.le_max_right _ _) hp)⟩
    | sUnion S hS ih =>
        intro hxS
        rcases hxS with ⟨V, hV, hxV⟩
        rcases ih V hV hxV with ⟨n, hn⟩
        exact ⟨n, Subset.trans hn (subset_sUnion_of_mem hV)⟩
  exact hP hU hxU

/-- Helper for Remark 5.7.4: any open neighborhood of `y` contains one of the basic `y`-tails. -/
private lemma yTail_subset_of_isOpen_of_mem {U : Set Point} (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ n : ℕ, yTail n ⊆ U := by
  -- This is the symmetric neighborhood-basis statement at `y`.
  change TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) U at hU
  let P : Set Point → Prop := fun V => y ∈ V → ∃ n : ℕ, yTail n ⊆ V
  have hP : ∀ {V : Set Point},
      TopologicalSpace.GenerateOpen (range zSingleton ∪ range xTail ∪ range yTail) V → P V := by
    intro V hV
    induction hV with
    | basic s hs =>
        intro hyS
        rcases hs with hs | hs
        · rcases hs with hs | hs
          · rcases hs with ⟨n, rfl⟩
            simp [zSingleton] at hyS
          · rcases hs with ⟨n, rfl⟩
            simp [xTail, zTail] at hyS
        · rcases hs with ⟨n, rfl⟩
          exact ⟨n, Subset.rfl⟩
    | univ =>
        intro _
        exact ⟨0, subset_univ _⟩
    | inter s t hs ht ihs iht =>
        intro hyST
        rcases ihs hyST.1 with ⟨m, hm⟩
        rcases iht hyST.2 with ⟨n, hn⟩
        refine ⟨max m n, ?_⟩
        intro p hp
        exact ⟨hm (yTail_mono (Nat.le_max_left _ _) hp), hn (yTail_mono (Nat.le_max_right _ _) hp)⟩
    | sUnion S hS ih =>
        intro hyS
        rcases hyS with ⟨V, hV, hyV⟩
        rcases ih V hV hyV with ⟨n, hn⟩
        exact ⟨n, Subset.trans hn (subset_sUnion_of_mem hV)⟩
  exact hP hU hyU

/-- Helper for Remark 5.7.4: each isolated point `z n` is clopen. -/
private lemma zSingleton_isClopen (n : ℕ) : IsClopen (zSingleton n) := by
  refine ⟨?_, zSingleton_isOpen n⟩
  -- Every point outside `{z n}` has a basic neighborhood still avoiding `z n`.
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 ?_
  intro p hp
  cases p with
  | x =>
      refine mem_nhds_iff.mpr ⟨xTail (n + 1), xTail_succ_subset_zSingleton_compl n,
        xTail_isOpen (n + 1), ?_⟩
      simp [xTail]
  | y =>
      refine mem_nhds_iff.mpr ⟨yTail (n + 1), yTail_succ_subset_zSingleton_compl n,
        yTail_isOpen (n + 1), ?_⟩
      simp [yTail]
  | z m =>
      have hm : m ≠ n := by
        simpa [zSingleton] using hp
      refine mem_nhds_iff.mpr ⟨zSingleton m, zSingleton_subset_zSingleton_compl hm,
        zSingleton_isOpen m, ?_⟩
      simp [zSingleton]

/-- Helper for Remark 5.7.4: every clopen neighborhood of `x` also contains `y`. -/
private lemma clopen_neighborhood_of_x_contains_y {Z : Set Point} (hZ : IsClopen Z) (hxZ : x ∈ Z) :
    y ∈ Z := by
  -- The tail basis at `x` and `y` forces every clopen neighborhood of `x` to overlap every open
  -- neighborhood of `y`; taking complements yields the contradiction.
  rcases xTail_subset_of_isOpen_of_mem hZ.isOpen hxZ with ⟨n, hn⟩
  by_contra hyZ
  rcases yTail_subset_of_isOpen_of_mem hZ.compl.isOpen hyZ with ⟨m, hm⟩
  have hzZ : z (n + m) ∈ Z := by
    apply hn
    simp [xTail, mem_zTail_iff]
  have hzCompl : z (n + m) ∈ Zᶜ := by
    apply hm
    simp [yTail, mem_zTail_iff]
  exact hzCompl hzZ

/-- Helper for Remark 5.7.4: the two-point set `{x, y}` is separated by the basic tails. -/
private lemma pair_xy_not_preconnected : ¬ IsPreconnected ({x, y} : Set Point) := by
  intro hxy
  have hcover : ({x, y} : Set Point) ⊆ xTail 0 ∪ yTail 0 := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact Or.inl (by simp [xTail])
    · exact Or.inr (by simp [yTail])
  have hx_nonempty : (({x, y} : Set Point) ∩ xTail 0).Nonempty := by
    refine ⟨x, ?_⟩
    simp [xTail]
  have hy_nonempty : (({x, y} : Set Point) ∩ yTail 0).Nonempty := by
    refine ⟨y, ?_⟩
    simp [yTail]
  rcases hxy (xTail 0) (yTail 0) (xTail_isOpen 0) (yTail_isOpen 0) hcover hx_nonempty hy_nonempty
    with ⟨p, hp⟩
  -- The witness would have to be in `{x, y}` and simultaneously in both disjoint tails.
  cases p <;> simp [xTail, yTail, zTail] at hp

/-- Helper for Remark 5.7.4: clopen singletons exclude every `z n` from the component of `x`. -/
private lemma z_not_mem_connectedComponent_x (n : ℕ) : z n ∉ connectedComponent x := by
  -- The complement of `{z n}` is clopen and contains `x`, so the whole component stays there.
  have hsubset : connectedComponent x ⊆ (zSingleton n)ᶜ :=
    (zSingleton_isClopen n).compl.connectedComponent_subset (by simp [zSingleton])
  intro hz
  have hz' : z n ∈ (zSingleton n)ᶜ := hsubset hz
  simp [zSingleton] at hz'

/-- Helper for Remark 5.7.4: the connected component of `x` cannot also contain `y`. -/
private lemma y_not_mem_connectedComponent_x : y ∉ connectedComponent x := by
  intro hy
  have hsubset : connectedComponent x ⊆ ({x, y} : Set Point) := by
    intro p hp
    cases p with
    | x =>
        simp
    | y =>
        simp
    | z n =>
        exact False.elim (z_not_mem_connectedComponent_x n hp)
  have hsuperset : ({x, y} : Set Point) ⊆ connectedComponent x := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact mem_connectedComponent
    · exact hy
  have hEq : connectedComponent x = ({x, y} : Set Point) := Subset.antisymm hsubset hsuperset
  have hpre : IsPreconnected ({x, y} : Set Point) := by
    rw [← hEq]
    exact isPreconnected_connectedComponent
  exact pair_xy_not_preconnected hpre

/-- Helper for Remark 5.7.4: the clopen neighborhood `({z n})ᶜ` removes `z n` from the total
intersection of clopen neighborhoods of `x`. -/
private lemma z_not_mem_iInter_isClopen_x (n : ℕ) :
    z n ∉ ⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point) := by
  intro hz
  let Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z } :=
    ⟨(zSingleton n)ᶜ, (zSingleton_isClopen n).compl, by simp [zSingleton]⟩
  have hz' : z n ∈ (Z : Set Point) := Set.mem_iInter.mp hz Z
  simp [Z, zSingleton] at hz'

/-- The connected component of `x` is the singleton `{x}` in the counterexample space. -/
-- Proof sketch: any connected subset containing `x` cannot contain any `z n`, since `{z n}` is open
-- and closed inside the subset, and `y` is separated from `x` by the basic open tails. Maximality
-- of the connected component then forces `connectedComponent x = {x}`.
theorem connectedComponent_x :
    connectedComponent x = ({x} : Set Point) := by
  -- The component is computed by first removing all `z n` via clopen singletons and then removing
  -- `y` via the explicit separation of `{x, y}`.
  ext p
  cases p with
  | x =>
      -- A point always lies in its own connected component.
      simp [mem_connectedComponent]
  | y =>
      -- The two-point set `{x, y}` is not preconnected, so `y` cannot lie in the component of `x`.
      simp [y_not_mem_connectedComponent_x]
  | z n =>
      -- Each `z n` is cut off by the clopen singleton `{z n}`.
      simp [z_not_mem_connectedComponent_x n]

/-- The intersection of all clopen neighborhoods of `x` is `{x, y}` in the counterexample space. -/
-- Proof sketch: show every clopen neighborhood of `x` must also contain `y`, while the set
-- `{x, y}` itself is the intersection of the clopen supersets obtained from the displayed tails.
theorem iInter_isClopen_x :
    (⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point)) = ({x, y} : Set Point) := by
  -- The index type already forces every set in the intersection to contain `x`, and the previous
  -- helper upgrades this to `y`; the clopen complements of the singletons remove the `z n`.
  ext p
  cases p with
  | x =>
      constructor
      · intro _
        simp
      · intro _
        exact Set.mem_iInter.mpr fun Z ↦ Z.2.2
  | y =>
      constructor
      · intro _
        simp
      · intro _
        exact Set.mem_iInter.mpr fun Z ↦ clopen_neighborhood_of_x_contains_y Z.2.1 Z.2.2
  | z n =>
      simp [z_not_mem_iInter_isClopen_x n]

/-- Remark 5.7.4: in general the connected component of a point can be strictly smaller than the
intersection of all clopen neighborhoods containing that point; the space defined here is such a
counterexample. -/
-- Proof sketch: combine the explicit computations `connectedComponent_x` and `iInter_isClopen_x`;
-- equivalently, appeal to the canonical inclusion
-- `connectedComponent_subset_iInter_isClopen` and the explicit identifications of the two sets.
theorem connectedComponent_x_ssubset_iInter_isClopen :
    connectedComponent x ⊂ ⋂ Z : { Z : Set Point // IsClopen Z ∧ x ∈ Z }, (Z : Set Point) := by
  refine ⟨connectedComponent_subset_iInter_isClopen, ?_⟩
  simp [connectedComponent_x, iInter_isClopen_x]

end ConnectedComponentClopenCounterexample
