/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set MeasureTheory

open scoped BigOperators ENNReal

private def initialWord {E : Type u} {n : ℕ} (x : Fin n → E) : ∀ _ : Finset.range n, E :=
  fun i ↦ x ⟨i, Finset.mem_range.mp i.2⟩

private theorem setOf_eq_cylinder_singleton {E : Type u} {n : ℕ} (x : Fin n → E) :
    {ω : ℕ → E | ∀ i : Fin n, ω i = x i} =
      cylinder (Finset.range n) ({initialWord x} : Set (∀ _ : Finset.range n, E)) := by
  ext ω
  rw [mem_cylinder, Set.mem_singleton_iff]
  constructor
  · intro h
    ext i
    exact h ⟨i, Finset.mem_range.mp i.2⟩
  · intro h i
    exact congr_fun h ⟨i, Finset.mem_range.mpr i.2⟩


@[simp] theorem mem_sequenceCylinderLevel_zero_iff {E : Type u} {s : Set (ℕ → E)} :
    s ∈ sequenceCylinderLevel E 0 ↔ s = ∅ := by
  rfl


/-- The semiring `𝒜` from Example 1.40 is the union of the textbook levels `𝒜_n`, with
`𝒜₀ = {∅}` and `𝒜_(n+1)` the positive-length initial cylinders. -/
theorem mem_sequenceCylinderFamily_iff {E : Type u} {s : Set (ℕ → E)} :
    s ∈ sequenceCylinderFamily E ↔ ∃ n : ℕ, s ∈ sequenceCylinderLevel E n := by
  constructor
  · rintro (rfl | ⟨n, x, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨n + 1, by exact ⟨x, rfl⟩⟩
  · rintro ⟨n, hs⟩
    rcases n with _ | n
    · exact Or.inl (mem_sequenceCylinderLevel_zero_iff.mp hs)
    · rcases mem_sequenceCylinderLevel_succ_iff.mp hs with ⟨x, rfl⟩
      exact Or.inr ⟨n, x, rfl⟩

private theorem mem_measurableCylinders_of_mem_sequenceCylinderFamily {E : Type u}
    [MeasurableSpace E] [MeasurableSingletonClass E] {s : Set (ℕ → E)}
    (hs : s ∈ sequenceCylinderFamily E) :
    s ∈ measurableCylinders (fun _ : ℕ ↦ E) := by
  rcases mem_sequenceCylinderFamily_iff.mp hs with ⟨n, hs⟩
  rcases n with _ | n
  · rw [mem_sequenceCylinderLevel_zero_iff.mp hs]
    exact empty_mem_measurableCylinders (fun _ : ℕ ↦ E)
  · rcases mem_sequenceCylinderLevel_succ_iff.mp hs with ⟨x, rfl⟩
    exact (mem_measurableCylinders _).2
      ⟨Finset.range (n + 1), {initialWord x}, MeasurableSet.singleton (initialWord x),
        setOf_eq_cylinder_singleton x⟩

/-- Example 1.40: the cylinder prescription
`μ([ω₁, …, ωₙ]) = ∏ i, p_{ωᵢ}` defines an additive content on the semiring
`sequenceCylinderFamily E`. -/
noncomputable def bernoulliSequenceContent {E : Type u} [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) :
    AddContent ℝ≥0∞ (sequenceCylinderFamily E) where
  toFun := piContent (fun _ : ℕ ↦ p.toMeasure)
  empty' := by
    simp
  sUnion' I hI hdis hmem := by
    simpa using addContent_sUnion
      (fun s hs ↦ mem_measurableCylinders_of_mem_sequenceCylinderFamily (hI hs))
      hdis
      (mem_measurableCylinders_of_mem_sequenceCylinderFamily hmem)

private theorem bernoulliSequenceContent_apply_word_aux {E : Type u} [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) (n : ℕ) (x : Fin n → E) :
    bernoulliSequenceContent p {ω : ℕ → E | ∀ i : Fin n, ω i = x i} = ∏ i, p (x i) := by
  have hprod :
      (∏ i : Finset.range n, p.toMeasure ({initialWord x i} : Set E)) = ∏ i : Fin n, p (x i) := by
    have hsub :
        (∏ i : Finset.range n, p.toMeasure ({initialWord x i} : Set E)) =
          ∏ i : Fin n, p.toMeasure ({x i} : Set E) := by
      refine Fintype.prod_equiv
        (Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun i ↦ by simp)).symm
        (fun i ↦ p.toMeasure ({initialWord x i} : Set E))
        (fun i ↦ p.toMeasure ({x i} : Set E))
        ?_
      intro i
      simp [initialWord]
    calc
      (∏ i : Finset.range n, p.toMeasure ({initialWord x i} : Set E))
          = ∏ i : Fin n, p.toMeasure ({x i} : Set E) := hsub
      _ = ∏ i : Fin n, p (x i) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact p.toMeasure_apply_singleton (x i) (measurableSet_singleton (x i))
  rw [setOf_eq_cylinder_singleton x, bernoulliSequenceContent]
  calc
    piContent (fun _ : ℕ ↦ p.toMeasure)
        (cylinder (Finset.range n) ({initialWord x} : Set (∀ _ : Finset.range n, E))) =
      Measure.pi (fun _ : Finset.range n ↦ p.toMeasure)
        ({initialWord x} : Set (∀ _ : Finset.range n, E)) := by
          exact piContent_cylinder (fun _ : ℕ ↦ p.toMeasure) (MeasurableSet.singleton (initialWord x))
    _ = ∏ i : Finset.range n, p.toMeasure ({initialWord x i} : Set E) :=
          Measure.pi_singleton (fun _ : Finset.range n ↦ p.toMeasure) (initialWord x)
    _ = ∏ i : Fin n, p (x i) := hprod

/-- On a basic cylinder determined by a word of length `n + 1`, the Bernoulli content is the
product of the corresponding one-step masses. -/
theorem bernoulliSequenceContent_apply_word {E : Type u} [MeasurableSpace E]
    [MeasurableSingletonClass E] (p : PMF E) (n : ℕ) (x : Fin (n + 1) → E) :
    bernoulliSequenceContent p {ω : ℕ → E | ∀ i : Fin (n + 1), ω i = x i} = ∏ i, p (x i) :=
  bernoulliSequenceContent_apply_word_aux p (n + 1) x
