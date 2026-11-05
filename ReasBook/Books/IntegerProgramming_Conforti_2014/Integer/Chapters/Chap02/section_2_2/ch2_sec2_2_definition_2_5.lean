/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.Polyhedron

open scoped Matrix

section Definition25

/-- The mixed-integer set represented by the explicit real system `A *ᵥ x + G *ᵥ y ≤ b`, with the
first block constrained to lie in `mixed_integer_lattice n p`. -/
def realMixedIntegerLinearSet
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ) :
    Set (MixedRealPoint n p) :=
  real_mixed_polyhedron A G b ∩ mixed_integer_lattice n p

/-- Membership in `realMixedIntegerLinearSet A G b` is exactly the defining mixed system together
with integrality of the first block. -/
theorem mem_realMixedIntegerLinearSet_iff
    {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (xy : MixedRealPoint n p) :
    xy ∈ realMixedIntegerLinearSet A G b ↔
      A *ᵥ xy.1 + G *ᵥ xy.2 ≤ b ∧ xy ∈ mixed_integer_lattice n p := by
  -- Normalize membership in the defining intersection to the two intended constraints.
  rw [realMixedIntegerLinearSet, Set.mem_inter_iff, mem_real_mixed_polyhedron_iff]

/-- Definition 2.5 (1): the first mixed-integer representation is better than the second when the
two systems represent the same mixed-integer set and the first LP relaxation is contained in the
second. -/
structure mixedIntegerFormulationBetter
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) : Prop where
  sameRepresentedSet :
    realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂
  relaxationSubset :
    real_mixed_polyhedron A₁ G₁ b₁ ⊆ real_mixed_polyhedron A₂ G₂ b₂

/-- Construct `mixedIntegerFormulationBetter A₁ G₁ b₁ A₂ G₂ b₂` from equality of the represented
mixed-integer sets and inclusion of the first LP relaxation in the second. -/
def mixedIntegerFormulationBetter.ofIff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hSameRepresentedSet :
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂)
    (hRelaxationSubset :
      real_mixed_polyhedron A₁ G₁ b₁ ⊆ real_mixed_polyhedron A₂ G₂ b₂) :
    mixedIntegerFormulationBetter A₁ G₁ b₁ A₂ G₂ b₂ :=
  { sameRepresentedSet := hSameRepresentedSet
    relaxationSubset := hRelaxationSubset }

/-- Unfold `mixedIntegerFormulationBetter A₁ G₁ b₁ A₂ G₂ b₂` into common represented-set equality
and inclusion of the first LP relaxation in the second. -/
theorem mixedIntegerFormulationBetter_iff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) :
    mixedIntegerFormulationBetter A₁ G₁ b₁ A₂ G₂ b₂ ↔
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
        real_mixed_polyhedron A₁ G₁ b₁ ⊆ real_mixed_polyhedron A₂ G₂ b₂ := by
  constructor
  · intro h
    -- Project the two defining fields of the structure into the target conjunction.
    exact ⟨h.sameRepresentedSet, h.relaxationSubset⟩
  · rintro ⟨hSameRepresentedSet, hRelaxationSubset⟩
    -- Repackage the same data through the canonical constructor.
    exact mixedIntegerFormulationBetter.ofIff
      A₁ G₁ b₁ A₂ G₂ b₂ hSameRepresentedSet hRelaxationSubset

/-- Definition 2.5 (2): two mixed-integer representations are equivalent when they represent the
same mixed-integer set and have the same LP relaxation. -/
structure mixedIntegerFormulationEquivalent
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) : Prop where
  sameRepresentedSet :
    realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂
  sameRelaxation :
    real_mixed_polyhedron A₁ G₁ b₁ = real_mixed_polyhedron A₂ G₂ b₂

/-- Construct `mixedIntegerFormulationEquivalent A₁ G₁ b₁ A₂ G₂ b₂` from equality of both the
represented mixed-integer sets and the LP relaxations. -/
def mixedIntegerFormulationEquivalent.ofIff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hSameRepresentedSet :
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂)
    (hSameRelaxation :
      real_mixed_polyhedron A₁ G₁ b₁ = real_mixed_polyhedron A₂ G₂ b₂) :
    mixedIntegerFormulationEquivalent A₁ G₁ b₁ A₂ G₂ b₂ :=
  { sameRepresentedSet := hSameRepresentedSet
    sameRelaxation := hSameRelaxation }

/-- Unfold `mixedIntegerFormulationEquivalent A₁ G₁ b₁ A₂ G₂ b₂` into common represented-set
equality and equality of the two LP relaxations. -/
theorem mixedIntegerFormulationEquivalent_iff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) :
    mixedIntegerFormulationEquivalent A₁ G₁ b₁ A₂ G₂ b₂ ↔
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
        real_mixed_polyhedron A₁ G₁ b₁ = real_mixed_polyhedron A₂ G₂ b₂ := by
  constructor
  · intro h
    -- Project the represented-set and relaxation equalities from the structure.
    exact ⟨h.sameRepresentedSet, h.sameRelaxation⟩
  · rintro ⟨hSameRepresentedSet, hSameRelaxation⟩
    -- Reassemble the structure from those two equalities.
    exact mixedIntegerFormulationEquivalent.ofIff
      A₁ G₁ b₁ A₂ G₂ b₂ hSameRepresentedSet hSameRelaxation

/-- Definition 2.5 (3): two mixed-integer representations are incomparable when they represent
the same mixed-integer set, yet each LP relaxation contains a point outside the other. -/
structure mixedIntegerFormulationIncomparable
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) : Prop where
  sameRepresentedSet :
    realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂
  firstDifferenceNonempty :
    Set.Nonempty (real_mixed_polyhedron A₁ G₁ b₁ \ real_mixed_polyhedron A₂ G₂ b₂)
  secondDifferenceNonempty :
    Set.Nonempty (real_mixed_polyhedron A₂ G₂ b₂ \ real_mixed_polyhedron A₁ G₁ b₁)

/-- Construct `mixedIntegerFormulationIncomparable A₁ G₁ b₁ A₂ G₂ b₂` from equality of the
represented mixed-integer sets together with nonempty LP-relaxation differences in both
directions. -/
def mixedIntegerFormulationIncomparable.ofIff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ)
    (hSameRepresentedSet :
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂)
    (hFirstDifferenceNonempty :
      Set.Nonempty (real_mixed_polyhedron A₁ G₁ b₁ \ real_mixed_polyhedron A₂ G₂ b₂))
    (hSecondDifferenceNonempty :
      Set.Nonempty (real_mixed_polyhedron A₂ G₂ b₂ \ real_mixed_polyhedron A₁ G₁ b₁)) :
    mixedIntegerFormulationIncomparable A₁ G₁ b₁ A₂ G₂ b₂ :=
  { sameRepresentedSet := hSameRepresentedSet
    firstDifferenceNonempty := hFirstDifferenceNonempty
    secondDifferenceNonempty := hSecondDifferenceNonempty }

/-- Unfold `mixedIntegerFormulationIncomparable A₁ G₁ b₁ A₂ G₂ b₂` into common represented-set
equality together with nonempty differences in both directions between the two LP relaxations. -/
theorem mixedIntegerFormulationIncomparable_iff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) :
    mixedIntegerFormulationIncomparable A₁ G₁ b₁ A₂ G₂ b₂ ↔
      realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
        Set.Nonempty (real_mixed_polyhedron A₁ G₁ b₁ \ real_mixed_polyhedron A₂ G₂ b₂) ∧
          Set.Nonempty (real_mixed_polyhedron A₂ G₂ b₂ \ real_mixed_polyhedron A₁ G₁ b₁) := by
  constructor
  · intro h
    -- Project the shared represented set and the two strict-difference witnesses.
    exact ⟨h.sameRepresentedSet, h.firstDifferenceNonempty, h.secondDifferenceNonempty⟩
  · rintro ⟨hSameRepresentedSet, hFirstDifferenceNonempty, hSecondDifferenceNonempty⟩
    -- Repackage the same witnesses into the incomparable-formulation structure.
    exact mixedIntegerFormulationIncomparable.ofIff
      A₁ G₁ b₁ A₂ G₂ b₂ hSameRepresentedSet hFirstDifferenceNonempty
      hSecondDifferenceNonempty

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_2/ch2_sec2_2_definition_2_5.lean
Definition 2.5. The three comparison relations between two mixed-integer formulations are exactly
the represented-set equality together with, respectively, LP-relaxation inclusion, LP-relaxation
equality, and strict nonempty differences in both LP-relaxation directions. -/
theorem mixedIntegerFormulationComparisons_iff
    {m₁ m₂ n p : ℕ}
    (A₁ : Matrix (Fin m₁) (Fin n) ℝ)
    (G₁ : Matrix (Fin m₁) (Fin p) ℝ)
    (b₁ : Fin m₁ → ℝ)
    (A₂ : Matrix (Fin m₂) (Fin n) ℝ)
    (G₂ : Matrix (Fin m₂) (Fin p) ℝ)
    (b₂ : Fin m₂ → ℝ) :
    (mixedIntegerFormulationBetter A₁ G₁ b₁ A₂ G₂ b₂ ↔
        realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
          real_mixed_polyhedron A₁ G₁ b₁ ⊆ real_mixed_polyhedron A₂ G₂ b₂) ∧
      (mixedIntegerFormulationEquivalent A₁ G₁ b₁ A₂ G₂ b₂ ↔
        realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
          real_mixed_polyhedron A₁ G₁ b₁ = real_mixed_polyhedron A₂ G₂ b₂) ∧
        (mixedIntegerFormulationIncomparable A₁ G₁ b₁ A₂ G₂ b₂ ↔
          realMixedIntegerLinearSet A₁ G₁ b₁ = realMixedIntegerLinearSet A₂ G₂ b₂ ∧
            Set.Nonempty (real_mixed_polyhedron A₁ G₁ b₁ \ real_mixed_polyhedron A₂ G₂ b₂) ∧
              Set.Nonempty
                (real_mixed_polyhedron A₂ G₂ b₂ \ real_mixed_polyhedron A₁ G₁ b₁)) := by
  -- Bundle the three Definition 2.5 clauses into a single item-level summary theorem.
  refine ⟨?_, ?_⟩
  · exact mixedIntegerFormulationBetter_iff A₁ G₁ b₁ A₂ G₂ b₂
  · refine ⟨?_, ?_⟩
    · exact mixedIntegerFormulationEquivalent_iff A₁ G₁ b₁ A₂ G₂ b₂
    · exact mixedIntegerFormulationIncomparable_iff A₁ G₁ b₁ A₂ G₂ b₂

end Definition25
