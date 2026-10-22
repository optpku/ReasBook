/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open scoped BigOperators

-- Proof sketch: the canonical Bernoulli measure is the infinite product
-- `Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure)`. Its value on an initial cylinder is computed by
-- reducing that cylinder to a singleton in the finite restriction space `E^n`. The textbook
-- probability hypothesis is redundant: the cylinder formula already determines the measure.
/-- The canonical Bernoulli product measure assigns to an initial cylinder the product of the
corresponding one-step masses. -/
theorem bernoulliMeasure_apply_initialCylinder {E : Type u} [Finite E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) (n : ℕ) (x : Fin n → E) :
    Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure) {ω : ℕ → E | ∀ i : Fin n, ω i = x i} =
      ∏ i, p (x i) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let y : ∀ i : Finset.range n, E := fun i ↦ x ⟨i, Finset.mem_range.mp i.2⟩
  have hset :
      {ω : ℕ → E | ∀ i : Fin n, ω i = x i} =
        cylinder (Finset.range n) ({y} : Set (∀ i : Finset.range n, E)) := by
    ext ω
    rw [mem_cylinder, Set.mem_singleton_iff]
    constructor
    · intro h
      ext i
      exact h ⟨i, Finset.mem_range.mp i.2⟩
    · intro h i
      exact congr_fun h ⟨i, Finset.mem_range.mpr i.2⟩
  have hprod :
      (∏ i : Finset.range n, p.toMeasure ({y i} : Set E)) = ∏ i : Fin n, p (x i) := by
    have hsub :
        (∏ i : Finset.range n, p.toMeasure ({y i} : Set E)) =
          ∏ i : Fin n, p.toMeasure ({x i} : Set E) := by
      refine Fintype.prod_equiv
        (Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun i ↦ by simp)).symm
        (fun i ↦ p.toMeasure ({y i} : Set E))
        (fun i ↦ p.toMeasure ({x i} : Set E))
        ?_
      intro i
      simp [y]
    calc
      (∏ i : Finset.range n, p.toMeasure ({y i} : Set E))
          = ∏ i : Fin n, p.toMeasure ({x i} : Set E) := hsub
      _ = ∏ i : Fin n, p (x i) := by
        rw [show (∏ i : Fin n, p.toMeasure ({x i} : Set E)) =
            ∏ i ∈ (Finset.univ : Finset (Fin n)), p.toMeasure ({x i} : Set E) by rfl]
        rw [show (∏ i : Fin n, p (x i)) = ∏ i ∈ (Finset.univ : Finset (Fin n)), p (x i) by rfl]
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact p.toMeasure_apply_singleton (x i) (measurableSet_singleton (x i))
  let q : ℕ → Measure E := fun _ ↦ p.toMeasure
  let ν : Finset.range n → Measure E := fun _ ↦ p.toMeasure
  rw [hset]
  calc
    Measure.infinitePi q
        (cylinder (Finset.range n) ({y} : Set (∀ i : Finset.range n, E))) =
          Measure.pi ν ({y} : Set (∀ i : Finset.range n, E)) := by
            exact Measure.infinitePi_cylinder q (MeasurableSet.singleton y)
    _ = ∏ i : Finset.range n, ν i ({y i} : Set E) := by
          exact Measure.pi_singleton ν y
    _ = ∏ i : Fin n, p (x i) := by
          simpa [ν] using hprod

private theorem initialCylinder_eq_Iic_singletonCylinder {E : Type u} (a : ℕ)
    (y : ∀ _ : Finset.Iic a, E) :
    cylinder (Finset.Iic a) ({y} : Set (∀ _ : Finset.Iic a, E)) =
      {ω : ℕ → E | ∀ i : Fin (a + 1), ω i = y ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩} := by
  ext ω
  rw [mem_cylinder, Set.mem_singleton_iff]
  constructor
  · intro h i
    exact congr_fun h ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  · intro h
    ext i
    exact h ⟨i, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

private theorem map_restrict_Iic_eq_pi_of_apply_initialCylinder {E : Type u} [Finite E]
    [MeasurableSpace E] [MeasurableSingletonClass E] (p : PMF E) (μ : Measure (ℕ → E))
    (hμ : ∀ n : ℕ, ∀ x : Fin n → E, μ {ω | ∀ i : Fin n, ω i = x i} = ∏ i, p (x i)) (a : ℕ) :
    μ.map (Finset.Iic a).restrict = Measure.pi (fun _ : Finset.Iic a ↦ p.toMeasure) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  refine Measure.ext_of_singleton fun y ↦ ?_
  let x : Fin (a + 1) → E := fun i ↦ y ⟨i, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩
  have hset :
      (Finset.Iic a).restrict ⁻¹' ({y} : Set (∀ _ : Finset.Iic a, E)) =
        {ω : ℕ → E | ∀ i : Fin (a + 1), ω i = x i} := by
    simpa [cylinder, x] using initialCylinder_eq_Iic_singletonCylinder a y
  have hprod :
      (∏ i : Finset.Iic a, p (y i)) = ∏ i : Fin (a + 1), p (x i) := by
    refine Fintype.prod_equiv
      (Fin.equivSubtype.trans
        (Equiv.subtypeEquivRight fun i ↦ by simp [Finset.mem_Iic])).symm
      (fun i ↦ p (y i))
      (fun i ↦ p (x i))
      ?_
    intro i
    simp [x]
  rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton y), hset]
  calc
    μ {ω : ℕ → E | ∀ i : Fin (a + 1), ω i = x i} = ∏ i : Fin (a + 1), p (x i) := hμ (a + 1) x
    _ = ∏ i : Finset.Iic a, p (y i) := hprod.symm
    _ = ∏ i : Finset.Iic a, p.toMeasure ({y i} : Set E) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          symm
          exact p.toMeasure_apply_singleton (y i) (measurableSet_singleton (y i))
    _ = Measure.pi (fun _ : Finset.Iic a ↦ p.toMeasure) ({y} : Set (∀ i : Finset.Iic a, E)) := by
          symm
          exact Measure.pi_singleton _ _

/-- A measure on `E^ℕ` is the Bernoulli product measure as soon as it has the textbook
initial-cylinder masses. -/
theorem eq_bernoulliMeasure_of_apply_initialCylinder {E : Type u} [Finite E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) (μ : Measure (ℕ → E))
    (hμ : ∀ n : ℕ, ∀ x : Fin n → E, μ {ω | ∀ i : Fin n, ω i = x i} = ∏ i, p (x i)) :
    μ = Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure) := by
  have hμ_univ : μ Set.univ = 1 := by
    simpa using hμ 0 (fun i ↦ nomatch i)
  have hμ_finite : μ Set.univ < ⊤ := by
    rw [hμ_univ]
    simp
  letI : IsFiniteMeasure μ := ⟨hμ_finite⟩
  refine ext_of_generate_finite (measurableCylinders fun _ : ℕ ↦ E)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    have hnat :
        measurableCylinders (fun _ : ℕ ↦ E) =
          ⋃ (a : ℕ) (S : Set (∀ _ : Finset.Iic a, E)) (_ : MeasurableSet S),
            {cylinder (Finset.Iic a) S} :=
      measurableCylinders_nat
    rw [hnat] at hs
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hs
    rcases hs with ⟨a, S, hS, rfl⟩
    rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict _) hS,
      map_restrict_Iic_eq_pi_of_apply_initialCylinder p μ hμ a]
    let ν : ℕ → Measure E := fun _ ↦ p.toMeasure
    have hinf :
        Measure.infinitePi ν (cylinder (Finset.Iic a) S) =
          Measure.pi (fun i : Finset.Iic a ↦ ν i) S := by
      exact Measure.infinitePi_cylinder ν hS
    simpa [ν, cylinder] using hinf.symm
  · have hinf_univ : Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure) Set.univ = 1 := by
      exact measure_univ
    rw [hμ_univ, hinf_univ]

/-- Theorem 1.64: For a finite state space `E`, the initial-cylinder prescription already
determines a unique measure on `E^ℕ`; this measure is the Bernoulli product measure associated to
`p`, and hence in particular a probability measure. -/
theorem existsUnique_bernoulliMeasure {E : Type u} [Finite E] [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) :
    ∃! μ : Measure (ℕ → E),
      ∀ n : ℕ, ∀ x : Fin n → E, μ {ω | ∀ i : Fin n, ω i = x i} = ∏ i, p (x i) := by
  refine ⟨Measure.infinitePi (fun _ : ℕ ↦ p.toMeasure), ?_, ?_⟩
  · intro n x
    exact bernoulliMeasure_apply_initialCylinder p n x
  · intro μ hμ
    exact eq_bernoulliMeasure_of_apply_initialCylinder p μ hμ
