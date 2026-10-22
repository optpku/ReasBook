/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped MeasureTheory

universe u

variable {Ω : Type u}

-- Proof sketch: `MeasurableSpace.DynkinSystem.ofMeasurableSpace` is the canonical lambda-system
-- attached to a measurable space, and its predicate of members is definitionally the measurable
-- sets of `m`.
/-- Theorem 1.12 (1): Part (i). The measurable sets of a sigma-algebra form the associated
lambda-system. -/
theorem dynkinSystem_ofMeasurableSpace_has_eq_measurableSet (m : MeasurableSpace Ω) :
    (MeasurableSpace.DynkinSystem.ofMeasurableSpace m).Has =
      {s : Set Ω | MeasurableSet[m] s} := by
  -- This Dynkin-system predicate is definitionally the measurable-set predicate.
  rfl

-- Proof sketch: the measurable sets are closed under `∅`, complements, and binary unions, so they
-- satisfy the fields of `MeasureTheory.IsSetAlgebra`.
/-- Theorem 1.12 (2): Part (i). Every sigma-algebra is an algebra of sets. -/
theorem measurableSet_isSetAlgebra (m : MeasurableSpace Ω) :
    IsSetAlgebra {s : Set Ω | MeasurableSet[m] s} := by
  refine {
    empty_mem := ?_,
    compl_mem := ?_,
    union_mem := ?_ }
  · -- A measurable space always contains the empty set.
    exact MeasurableSet.empty
  · -- Complements of measurable sets remain measurable.
    intro s hs
    exact hs.compl
  · -- Binary unions are measurable in every sigma-algebra.
    intro s t hs ht
    exact hs.union ht

-- Proof sketch: measurable sets contain `∅`, are closed under set difference via complement and
-- intersection, and are closed under countable unions by the `MeasurableSpace` axioms.
/-- Theorem 1.12 (3): Part (i). Every sigma-algebra is a sigma-ring of sets. -/
theorem measurableSet_isSetSigmaRing (m : MeasurableSpace Ω) :
    IsSetSigmaRing {s : Set Ω | MeasurableSet[m] s} := by
  refine { (measurableSet_isSetAlgebra m).isSetRing with
    iUnion_mem := ?_ }
  -- The extra sigma-ring axiom is exactly the measurable-space countable-union axiom.
  intro s hs
  exact m.measurableSet_iUnion s hs

-- Proof sketch: this is the forgetful implication from the extra countable-union closure in a
-- sigma-ring to the underlying ring-of-sets structure.
/-- Theorem 1.12 (4): Part (ii). Every sigma-ring is a ring of sets. -/
theorem isSetSigmaRing_isSetRing {A : Set (Set Ω)} (hA : IsSetSigmaRing A) :
    IsSetRing A := by
  -- Forget the extra countable-union structure.
  exact hA.toIsSetRing

-- Proof sketch: for a ring of sets, intersections are obtained from differences, and then the
-- semiring decomposition of a difference is the singleton finite partition `{s \\ t}`.
/-- Theorem 1.12 (5): Part (ii). Every ring of sets is a semiring of sets. -/
theorem isSetRing_isSetSemiring {A : Set (Set Ω)} (hA : IsSetRing A) :
    IsSetSemiring A := by
  -- This is the canonical ring-to-semiring coercion in mathlib.
  exact hA.isSetSemiring

-- Proof sketch: this is the canonical mathlib construction `MeasureTheory.IsSetAlgebra.isSetRing`
-- viewed as a standalone textbook clause.
/-- Theorem 1.12 (6): Part (iii). Every algebra of sets is a ring of sets. -/
theorem isSetAlgebra_isSetRing {A : Set (Set Ω)} (hA : IsSetAlgebra A) :
    IsSetRing A := by
  -- Mathlib already packages the derived ring structure for algebras of sets.
  exact hA.isSetRing

/-- Helper for Theorem 1.12: on a finite ambient type, every countable union of members of an
algebra of sets already reduces to a finite union. -/
lemma iUnion_mem_of_finite_isSetAlgebra {A : Set (Set Ω)} [Finite Ω] (hA : IsSetAlgebra A)
    (s : ℕ → Set Ω) (hs : ∀ n, s n ∈ A) : (⋃ n, s n) ∈ A := by
  classical
  -- The ambient space is finite, so the whole countable union is a finite set.
  have hfin : (⋃ n, s n : Set Ω).Finite := Set.finite_univ.subset (subset_univ _)
  -- Extract a finite index set whose union already covers the whole countable union.
  obtain ⟨I, hIfin, hIcover⟩ :=
    Set.finite_subset_iUnion hfin (by
      intro x hx
      simpa [mem_iUnion] using hx)
  let S : Finset ℕ := hIfin.toFinset
  have hsubset : (⋃ n, s n : Set Ω) ⊆ ⋃ i ∈ S, s i := by
    simpa [S] using hIcover
  have hsuperset : (⋃ i ∈ S, s i : Set Ω) ⊆ ⋃ n, s n := by
    -- Any point in the finite subunion lies in the original countable union.
    intro x hx
    rcases mem_iUnion.mp hx with ⟨i, hx⟩
    exact mem_iUnion.mpr ⟨i, by
      rcases mem_iUnion.mp hx with ⟨hi, hx⟩
      exact hx⟩
  have hfinite_union_mem : (⋃ i ∈ S, s i : Set Ω) ∈ A := by
    -- Algebras are closed under finite unions.
    exact hA.biUnion_mem S (fun i hi ↦ hs i)
  have hEq : (⋃ n, s n : Set Ω) = ⋃ i ∈ S, s i := Subset.antisymm hsubset hsuperset
  -- Replace the countable union by the equal finite union.
  simpa [hEq] using hfinite_union_mem

-- Proof sketch: on a finite ambient type, every countable union of members of `A` is a finite
-- union, so an algebra is already closed under the countable unions needed for the generated
-- sigma-algebra; hence `generateFrom A` has exactly the sets of `A` as measurable sets.
/-- Theorem 1.12 (7): Part (iii). On a finite ambient set, an algebra of sets already equals the
sigma-algebra it generates. -/
theorem generateFrom_eq_self_of_finite_isSetAlgebra {A : Set (Set Ω)} [Finite Ω]
    (hA : IsSetAlgebra A) : {s : Set Ω | MeasurableSet[MeasurableSpace.generateFrom A] s} = A :=
  by
  -- Route correction: instead of unfolding generated measurability recursively, encode `A`
  -- itself as a measurable space and use the universal property of `generateFrom`.
  let mA : MeasurableSpace Ω :=
    { MeasurableSet' := A
      measurableSet_empty := hA.empty_mem
      measurableSet_compl := fun s hs ↦ hA.compl_mem hs
      measurableSet_iUnion := fun s hs ↦ iUnion_mem_of_finite_isSetAlgebra hA s hs }
  have h_generateFrom_le : MeasurableSpace.generateFrom A ≤ mA := by
    -- Every generator is measurable in the measurable space defined by `A` itself.
    exact MeasurableSpace.generateFrom_le (fun t ht ↦ ht)
  ext s
  constructor
  · -- Any set measurable in the generated sigma-algebra is measurable in `mA`, hence belongs to `A`.
    intro hs
    exact h_generateFrom_le s hs
  · -- Each generator remains measurable in the sigma-algebra generated from `A`.
    intro hs
    exact MeasurableSpace.measurableSet_generateFrom hs
