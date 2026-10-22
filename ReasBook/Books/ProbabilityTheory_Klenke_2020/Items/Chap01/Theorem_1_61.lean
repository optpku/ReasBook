/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped BigOperators

/-- A Borel measure on `ℝ` is of the textbook type used in the finite-product theorem if it is
either finite or arises from a Stieltjes function. -/
def IsFiniteOrStieltjesMeasure (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∨ ∃ f : StieltjesFunction ℝ, μ = f.measure

-- Proof sketch: a finite measure is automatically sigma-finite, while a Stieltjes measure is
-- sigma-finite by the standard local finiteness properties of `StieltjesFunction.measure` on `ℝ`.
/-- Every finite-or-Stieltjes Borel measure on `ℝ` is sigma-finite. -/
lemma IsFiniteOrStieltjesMeasure.sigmaFinite {μ : Measure ℝ} (hμ : IsFiniteOrStieltjesMeasure μ) :
    SigmaFinite μ := by
  rcases hμ with hμ | ⟨f, rfl⟩
  · -- A finite measure is sigma-finite by the standard typeclass instance.
    letI : IsFiniteMeasure μ := hμ
    infer_instance
  · -- A Stieltjes measure is locally finite on `ℝ`, hence sigma-finite.
    infer_instance

/-- Helper for Theorem 1.61: every finite-or-Stieltjes measure on `ℝ` has finite spanning sets
inside the generating family of half-open intervals `Ioc`. -/
def IsFiniteOrStieltjesMeasure.finiteSpanningSetsIn_ioc
    {μ : Measure ℝ} (hμ : IsFiniteOrStieltjesMeasure μ) :
    μ.FiniteSpanningSetsIn {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S} := by
  refine ⟨fun n ↦ Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1), ?_, ?_, ?_⟩
  · intro n
    -- Each covering set is itself one of the generating half-open intervals.
    refine ⟨-((n : ℝ) + 1), (n : ℝ) + 1, ?_, rfl⟩
    linarith
  · intro n
    rcases hμ with hμ | ⟨f, rfl⟩
    · -- Finite measures assign finite mass to every set.
      exact @MeasureTheory.measure_lt_top _ _ μ hμ (Ioc (-((n : ℝ) + 1)) ((n : ℝ) + 1))
    · -- Stieltjes measures are finite on compactly bounded half-open intervals.
      rw [f.measure_Ioc]
      exact ENNReal.ofReal_lt_top
  · -- The symmetric intervals exhaust the real line.
    ext x
    simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    refine ⟨n, ?_, ?_⟩
    · have hx : -|x| ≤ x := neg_abs_le x
      linarith
    · have hx : x ≤ |x| := le_abs_self x
      linarith

/-- Helper for Theorem 1.61: agreement on all half-open coordinate rectangles determines the
finite product measure. -/
lemma product_measure_eq_of_ioc_rectangles
    {n : ℕ} (μs : Fin n → Measure ℝ)
    (hspan :
      ∀ i, (μs i).FiniteSpanningSetsIn {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S})
    {ν : Measure (Fin n → ℝ)}
    (hν : ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
      ν (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, μs i (Ioc (a i) (b i))) :
    Measure.pi μs = ν := by
  -- Uniqueness is the product-space version of measure extensionality on a generating π-system.
  refine Measure.pi_eq_generateFrom (μ := μs)
    (C := fun _ ↦ {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S})
    (fun _ ↦ ?_) (fun _ ↦ ?_) hspan ?_
  · simpa using (borel_eq_generateFrom_Ioc ℝ).symm
  · simpa using (isPiSystem_Ioc (α := ℝ) id id)
  · intro s hs
    choose a b hab hEq using hs
    -- Rewrite the abstract generating rectangle back to explicit endpoint functions.
    have hrect : univ.pi s = univ.pi (fun i ↦ Ioc (a i) (b i)) := by
      ext x
      simp [hEq]
    rw [hrect, hν a b hab]
    simp [hEq]

-- Proof sketch: use the canonical finite product measure `Measure.pi μs` for existence once each
-- factor is sigma-finite, obtain sigma-finiteness from `IsFiniteOrStieltjesMeasure.sigmaFinite`,
-- and prove uniqueness via `Measure.pi_eq` from agreement on measurable half-open rectangles.
/-- Theorem 1.61: For a finite family of Borel measures on `ℝ`, each of which is finite or a
Lebesgue--Stieltjes measure, there exists a unique sigma-finite measure on `ℝ^n`, represented as
`Fin n → ℝ`, whose value on every half-open rectangle `(a, b]` is the product of the one-dimensional
interval masses. -/
theorem existsUnique_sigmaFinite_product_measure_of_finite_or_stieltjes
    (n : ℕ) (μs : Fin n → Measure ℝ) (hμs : ∀ i, IsFiniteOrStieltjesMeasure (μs i)) :
    ∃! μ : Measure (Fin n → ℝ),
      SigmaFinite μ ∧
        ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
          μ (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, μs i (Ioc (a i) (b i)) := by
  let μ0 : Measure (Fin n → ℝ) := Measure.pi μs
  have hspan :
      ∀ i, (μs i).FiniteSpanningSetsIn {S : Set ℝ | ∃ l u, l < u ∧ Ioc l u = S} :=
    fun i ↦ (hμs i).finiteSpanningSetsIn_ioc
  have hμ0_sigma : SigmaFinite μ0 := by
    -- The one-dimensional spanning families lift to a finite spanning family in the product.
    simpa [μ0] using (Measure.FiniteSpanningSetsIn.pi (μ := μs) hspan).sigmaFinite
  have hμ0_rect :
      ∀ a b : Fin n → ℝ, (∀ i, a i < b i) →
        μ0 (univ.pi fun i ↦ Ioc (a i) (b i)) = ∏ i, μs i (Ioc (a i) (b i)) := by
    intro a b hab
    -- Install sigma-finiteness on the factors to invoke the rectangle formula for `Measure.pi`.
    letI : ∀ i, SigmaFinite (μs i) := fun i ↦ (hμs i).sigmaFinite
    exact Measure.pi_pi (μ := μs) (fun i ↦ Ioc (a i) (b i))
  refine ⟨μ0, ⟨hμ0_sigma, hμ0_rect⟩, ?_⟩
  intro ν hν
  rcases hν with ⟨_, hν_rect⟩
  -- Any competing sigma-finite measure agrees with the canonical product on the generating
  -- rectangle π-system, so uniqueness follows from the helper above.
  exact (product_measure_eq_of_ioc_rectangles μs hspan hν_rect).symm
