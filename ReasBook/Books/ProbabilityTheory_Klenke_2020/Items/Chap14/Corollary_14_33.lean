/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

open scoped BigOperators

universe u

variable {Ω : ℕ → Type u} [∀ n, MeasurableSpace (Ω n)]

variable (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]

private theorem eq_infinitePi_of_apply_initialCylinders
    {P : Measure (∀ n, Ω n)}
    (hP :
      ∀ n (A : ∀ i, Set (Ω i)),
        (∀ i ∈ Finset.range (n + 1), MeasurableSet (A i)) →
          P (Set.pi (Finset.range (n + 1)) A) =
            ∏ i ∈ Finset.range (n + 1), μ i (A i)) :
    P = Measure.infinitePi μ := by
  apply Measure.eq_infinitePi μ
  intro s t ht
  let n := s.sup id
  let A : ∀ i, Set (Ω i) := fun i ↦ if i ∈ s then t i else Set.univ
  have hA :
      ∀ i ∈ Finset.range (n + 1), MeasurableSet (A i) := by
    intro i hi
    by_cases his : i ∈ s
    · simpa [A, his] using ht i
    · simp [A, his]
  have hs_range : s ⊆ Finset.range (n + 1) := by
    simpa [n] using Finset.subset_range_sup_succ s
  have hs : Set.pi s t = Set.pi (Finset.range (n + 1)) A := by
    ext x
    rw [Set.mem_pi, Set.mem_pi]
    constructor
    · intro hx i hi
      by_cases his : i ∈ s
      · simpa [A, his] using hx i his
      · simp [A, his]
    · intro hx i hi
      have hir : i ∈ Finset.range (n + 1) := hs_range hi
      have hxi : i ∈ s → x i ∈ t i := by
        simpa [A] using hx i hir
      exact hxi hi
  have hprod :
      ∏ i ∈ Finset.range (n + 1), μ i (A i) = ∏ i ∈ s, μ i (t i) := by
    calc
      ∏ i ∈ Finset.range (n + 1), μ i (A i) = ∏ i ∈ s, μ i (A i) := by
        symm
        exact Finset.prod_subset hs_range (by
          intro i hi hir
          simp [A, hir])
      _ = ∏ i ∈ s, μ i (t i) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp [A, hi]
  rw [hs, hP n A hA, hprod]

-- Proof sketch: use the canonical infinite product measure `Measure.infinitePi μ` for existence,
-- obtain the initial-cylinder formula by specializing the product-measure rectangle formula to
-- `Finset.range (n + 1)`, and prove uniqueness by reducing initial cylinders to the determining
-- π-system from the infinite-product construction.
/-- Corollary 14.33: a sequence of probability measures admits a unique product probability
measure on the countable product space, characterized by its values on initial cylinders. -/
theorem existsUnique_productProbabilityMeasure :
    ∃! P : Measure (∀ n, Ω n),
      ∀ n (A : ∀ i, Set (Ω i)),
        (∀ i ∈ Finset.range (n + 1), MeasurableSet (A i)) →
          P (Set.pi (Finset.range (n + 1)) A) =
            ∏ i ∈ Finset.range (n + 1), μ i (A i) := by
  refine ⟨Measure.infinitePi μ, ?_, ?_⟩
  · intro n A hA
    simpa using Measure.infinitePi_pi μ hA
  · intro P hP
    exact eq_infinitePi_of_apply_initialCylinders μ hP

/- Under the canonical product probability measure, the coordinate maps are independent by direct
recall of `iIndepFun_infinitePi` specialized to the identity maps on the factor spaces. -/
#check (iIndepFun_infinitePi (fun _ ↦ measurable_id) :
  iIndepFun Function.eval (Measure.infinitePi μ))
