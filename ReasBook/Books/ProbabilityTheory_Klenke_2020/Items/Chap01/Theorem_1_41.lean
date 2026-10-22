/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open Set

open scoped ENNReal

namespace MeasureTheory

universe u

/-- If a measure on `MeasurableSpace.generateFrom A` agrees with an additive content `m` on a
countable cover in `A` on which `m` is finite, then this cover gives the canonical
`FiniteSpanningSetsIn` witness inside `A`. -/
def finiteSpanningSetsIn_of_eq_on_spanning_cover
    {α : Type u} {A : Set (Set α)} (m : AddContent ℝ≥0∞ A)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ)
    {μ : @Measure α (MeasurableSpace.generateFrom A)} (hμ : ∀ t ∈ A, μ t = m t) :
    μ.FiniteSpanningSetsIn A :=
  .mk s hs_mem (fun n ↦ by rw [hμ (s n) (hs_mem n)]; exact hs_finite n) hs_spanning

/-- Any measure on `MeasurableSpace.generateFrom A` that agrees with an additive content `m` on a
countable cover in `A` on which `m` is finite is sigma-finite. -/
theorem sigmaFinite_of_eq_on_spanning_cover
    {α : Type u} {A : Set (Set α)} (m : AddContent ℝ≥0∞ A)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ)
    {μ : @Measure α (MeasurableSpace.generateFrom A)} (hμ : ∀ t ∈ A, μ t = m t) :
    SigmaFinite μ :=
  (finiteSpanningSetsIn_of_eq_on_spanning_cover m s hs_mem hs_finite hs_spanning hμ).sigmaFinite

private theorem eq_of_eq_on_ring_of_spanning_cover
    {α : Type u} {A : Set (Set α)} (hA : IsSetRing A) (m : AddContent ℝ≥0∞ A)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ)
    {μ ν : @Measure α (MeasurableSpace.generateFrom A)}
    (hμ : ∀ t ∈ A, μ t = m t) (hν : ∀ t ∈ A, ν t = m t) :
    μ = ν := by
  let hμ_span : μ.FiniteSpanningSetsIn A :=
    finiteSpanningSetsIn_of_eq_on_spanning_cover m s hs_mem hs_finite hs_spanning hμ
  exact hμ_span.ext rfl hA.isSetSemiring.isPiSystem fun t ht ↦ by rw [hμ t ht, hν t ht]

/-- Theorem 1.41: Carathéodory's extension theorem for a sigma-finite premeasure on a ring of
sets. There is a unique measure on `σ(A)` extending the premeasure; its sigma-finiteness is given
by `sigmaFinite_of_eq_on_spanning_cover`. -/
-- Proof sketch: apply `AddContent.measure` to the sigma-subadditive additive content on the ring
-- `A` to obtain a measure on `MeasurableSpace.generateFrom A` agreeing with `m` on `A`. The
-- covering sequence yields `FiniteSpanningSetsIn` for every extension, hence sigma-finiteness.
-- For uniqueness, apply the standard `FiniteSpanningSetsIn.ext` theorem on the generating
-- π-system `A`.
theorem existsUnique_measure_generateFrom_eq_of_sigmaFinite
    {α : Type u} {A : Set (Set α)} (hA : IsSetRing A) (m : AddContent ℝ≥0∞ A)
    (hm_sigma : m.IsSigmaSubadditive)
    (s : ℕ → Set α) (hs_mem : ∀ n, s n ∈ A) (hs_finite : ∀ n, m (s n) < ∞)
    (hs_spanning : (⋃ n, s n) = Set.univ) :
    ∃! μ : @Measure α (MeasurableSpace.generateFrom A), ∀ t ∈ A, μ t = m t := by
  letI : MeasurableSpace α := MeasurableSpace.generateFrom A
  let μ0 : Measure α := m.measure hA.isSetSemiring le_rfl hm_sigma
  have hμ0 : ∀ t ∈ A, μ0 t = m t := by
    intro t ht
    simpa [μ0] using AddContent.measure_eq m hA.isSetSemiring rfl hm_sigma ht
  refine ⟨μ0, hμ0, ?_⟩
  intro ν hν
  exact eq_of_eq_on_ring_of_spanning_cover hA m s hs_mem hs_finite hs_spanning hν hμ0

end MeasureTheory
