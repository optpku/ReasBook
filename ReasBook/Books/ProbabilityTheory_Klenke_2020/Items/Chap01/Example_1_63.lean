/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

variable {E : Type u}

/-- Helper for Example 1.63: a positive-length textbook cylinder coincides with the corresponding
`PiNat.cylinder`. -/
lemma initialWordSet_eq_piNatCylinder {n : ℕ} (x : Fin (n + 1) → E) :
    {ω | ∀ i : Fin (n + 1), ω i = x i} =
      PiNat.cylinder (fun k ↦ if hk : k < n + 1 then x ⟨k, hk⟩ else x 0) (n + 1) := by
  -- Rewrite membership in the textbook cylinder into the coordinatewise `PiNat.cylinder` form.
  ext ω
  rw [PiNat.mem_cylinder_iff]
  constructor
  · intro h i hi
    simpa [hi] using h ⟨i, hi⟩
  · intro h i
    simpa [i.is_lt] using h i i.is_lt

/-- Helper for Example 1.63: every member of `sequenceCylinderFamily E` is open for the discrete
product topology on `ℕ → E`. -/
lemma isOpen_of_mem_sequenceCylinderFamily [TopologicalSpace E] [DiscreteTopology E]
    {s : Set (ℕ → E)} (hs : s ∈ sequenceCylinderFamily E) : IsOpen s := by
  have hs' : s = ∅ ∨ ∃ n : ℕ, ∃ x : Fin (n + 1) → E, s = {ω | ∀ i : Fin (n + 1), ω i = x i} := by
    simpa [sequenceCylinderFamily] using hs
  -- Split into the empty cylinder and the positive-length cylinders from the definition.
  rcases hs' with rfl | ⟨n, x, rfl⟩
  · simp
  · -- Normalize to `PiNat.cylinder`, where openness is already available in mathlib.
    rw [initialWordSet_eq_piNatCylinder (x := x)]
    simpa using PiNat.isOpen_cylinder (E := fun _ : ℕ ↦ E)
      (fun k ↦ if hk : k < n + 1 then x ⟨k, hk⟩ else x 0) (n + 1)

/-- Helper for Example 1.63: every member of `sequenceCylinderFamily E` is closed for the discrete
product topology on `ℕ → E`. -/
lemma isClosed_of_mem_sequenceCylinderFamily [TopologicalSpace E] [DiscreteTopology E]
    {s : Set (ℕ → E)} (hs : s ∈ sequenceCylinderFamily E) : IsClosed s := by
  have hs' : s = ∅ ∨ ∃ n : ℕ, ∃ x : Fin (n + 1) → E, s = {ω | ∀ i : Fin (n + 1), ω i = x i} := by
    simpa [sequenceCylinderFamily] using hs
  -- The same case split as for openness reduces closedness to a finite product of singletons.
  rcases hs' with rfl | ⟨n, x, rfl⟩
  · simp
  · -- After rewriting to `Set.pi`, closedness follows from closed singleton coordinate slices.
    rw [initialWordSet_eq_piNatCylinder (x := x), PiNat.cylinder_eq_pi]
    exact isClosed_set_pi fun i _ ↦ isClosed_discrete ({(fun k ↦
      if hk : k < n + 1 then x ⟨k, hk⟩ else x 0) i} : Set E)

/-- Helper for Example 1.63: every member of `sequenceCylinderFamily E` is compact once `E` is
finite and given the discrete topology. -/
lemma isCompact_of_mem_sequenceCylinderFamily [Finite E] [TopologicalSpace E] [DiscreteTopology E]
    {s : Set (ℕ → E)} (hs : s ∈ sequenceCylinderFamily E) : IsCompact s := by
  -- Closed subsets of the compact ambient product `ℕ → E` are compact.
  exact (isClosed_of_mem_sequenceCylinderFamily hs).isCompact

-- Proof sketch: view `E^ℕ` with the product topology of the discrete finite space `E`; the
-- initial cylinders are clopen and hence compact. A countable open cover of a compact cylinder
-- therefore has a finite subcover.
/-- Example 1.63: If a cylinder set in `E^ℕ` is covered by countably many cylinder sets and `E` is
finite, then finitely many members of the cover already cover it. This is the compactness statement
used to verify (1.13) in the construction of the infinite product content. -/
theorem initialSequenceCylinder_finite_subcover_of_subset_iUnion [Finite E]
    {A : Set (ℕ → E)} (hA : A ∈ sequenceCylinderFamily E) (cover : ℕ → Set (ℕ → E))
    (hcover_mem : ∀ n, cover n ∈ sequenceCylinderFamily E) (hcover : A ⊆ ⋃ n, cover n) :
    ∃ s : Finset ℕ, A ⊆ ⋃ n ∈ s, cover n := by
  -- Equip `E` with the discrete topology so that the textbook cylinders become clopen.
  letI : TopologicalSpace E := ⊥
  letI : DiscreteTopology E := discreteTopology_bot E
  -- The covered cylinder is compact in the ambient product space.
  have hAcompact : IsCompact A := isCompact_of_mem_sequenceCylinderFamily hA
  -- Each cylinder in the cover is open in the same product topology.
  have hopen : ∀ n, IsOpen (cover n) := fun n ↦ isOpen_of_mem_sequenceCylinderFamily (hcover_mem n)
  -- Compactness upgrades the countable open cover to a finite subcover.
  exact hAcompact.elim_finite_subcover cover hopen hcover
