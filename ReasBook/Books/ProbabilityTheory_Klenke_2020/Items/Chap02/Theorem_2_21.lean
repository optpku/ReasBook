/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_16

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

variable {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]

/-- Helper for Theorem 2.21: the lower-orthant product formula is exactly independence of the
preimage family of the generating lower intervals `Iic a`. -/
private lemma iic_preimage_family_iIndepSets (μ : Measure Ω) (X : ι → Ω → ℝ)
    (h :
      ∀ (J : Finset ι) (x : J → ℝ),
        μ (⋂ j : J, X j ⁻¹' Iic (x j)) = ∏ j : J, μ (X j ⁻¹' Iic (x j))) :
    iIndepSets (fun i ↦ Set.preimage (X i) '' (range Iic : Set (Set ℝ))) μ := by
  rw [iIndepSets_iff]
  intro J s hs
  classical
  -- Each chosen generator set is some lower interval, so we repackage the witnesses as a finite
  -- vector `x : J → ℝ` and apply the assumed factorization formula.
  have hx : ∀ j : J, ∃ a : ℝ, s j.1 = X j.1 ⁻¹' Iic a := by
    intro j
    rcases hs j.1 j.2 with ⟨u, hu, hus⟩
    rcases hu with ⟨a, rfl⟩
    exact ⟨a, hus.symm⟩
  choose x hx using hx
  rw [show (⋂ i ∈ J, s i) = ⋂ j : J, s j.1 by
    ext ω
    simp]
  rw [show (⋂ j : J, s j.1) = ⋂ j : J, X j.1 ⁻¹' Iic (x j) by
    ext ω
    simp [hx]]
  rw [show (∏ i ∈ J, μ (s i)) = ∏ j : J, μ (s j.1) by
    exact (Finset.prod_attach J (fun i ↦ μ (s i))).symm]
  rw [show (∏ j : J, μ (s j.1)) = ∏ j : J, μ (X j.1 ⁻¹' Iic (x j)) by
    simp [hx]]
  exact h J x

/-- Helper for Theorem 2.21: independence on the lower-interval generators upgrades to
independence of the real-valued family. -/
private lemma iIndepFun_of_iIndepSets_preimage_Iic (μ : Measure Ω) (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i))
    (h :
      iIndepSets (fun i ↦ Set.preimage (X i) '' (range Iic : Set (Set ℝ))) μ) :
    iIndepFun X μ := by
  -- Route correction: use the earlier generator-extension theorem directly instead of rebuilding
  -- the `iIndepSets` to comap-σ-algebra upgrade inside this file.
  exact iIndepFun_of_iIndepSets_preimage_generators μ X hX
    (fun _ : ι ↦ (range Iic : Set (Set ℝ)))
    (fun _ ↦ isPiSystem_Iic)
    (fun _ ↦ by simpa using (borel_eq_generateFrom_Iic ℝ).symm)
    h

-- Proof sketch: the forward implication is the specialization of
-- `iIndepFun_iff_measure_inter_preimage_eq_mul` to the measurable lower intervals `Iic (x j)`.
-- For the converse, the rational lower intervals form a π-system generating `borel ℝ`, so the
-- π-system extension theorem upgrades independence of these lower-orthant preimages to
-- independence of the real-valued family.
/-- Theorem 2.21: A family of real random variables is independent if and only if, for every
finite `J ⊆ I` and every `x ∈ ℝ^J`, the finite-dimensional distribution function on the lower
orthant `∏ j ∈ J, (-∞, x_j]` factors as the product of the one-dimensional marginal distribution
functions, i.e. equation (2.8). -/
theorem iIndepFun_iff_joint_cdf_eq_prod_marginals (μ : Measure Ω := by volume_tac)
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i)) :
    iIndepFun X μ ↔
      ∀ (J : Finset ι) (x : J → ℝ),
        μ (⋂ j : J, X j ⁻¹' Iic (x j)) = ∏ j : J, μ (X j ⁻¹' Iic (x j)) := by
  constructor
  · intro h J x
    classical
    let A : ι → Set ℝ := fun i => if hi : i ∈ J then Iic (x ⟨i, hi⟩) else Set.univ
    have hA : ∀ i, i ∈ J → MeasurableSet (A i) := by
      intro i hi
      simp [A, hi]
    -- We specialize the general finite preimage product formula to the lower intervals indexed by
    -- the chosen finite family `x : J → ℝ`.
    have h_main := h.measure_inter_preimage_eq_mul J hA
    have h_inter₁ : (⋂ i ∈ J, X i ⁻¹' A i) = ⋂ j : J, X j.1 ⁻¹' A j.1 := by
      ext ω
      simp
    have h_inter₂ : (⋂ j : J, X j.1 ⁻¹' A j.1) = ⋂ j : J, X j.1 ⁻¹' Iic (x j) := by
      ext ω
      simp [A]
    have h_prod₁ : (∏ i ∈ J, μ (X i ⁻¹' A i)) = ∏ j : J, μ (X j.1 ⁻¹' A j.1) := by
      exact (Finset.prod_attach J (fun i ↦ μ (X i ⁻¹' A i))).symm
    have h_prod₂ : (∏ j : J, μ (X j.1 ⁻¹' A j.1)) = ∏ j : J, μ (X j.1 ⁻¹' Iic (x j)) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      simp [A, j.2]
    rw [h_inter₁, h_inter₂, h_prod₁, h_prod₂] at h_main
    exact h_main
  · intro h
    have h_iic :
        iIndepSets (fun i ↦ Set.preimage (X i) '' (range Iic : Set (Set ℝ))) μ :=
      iic_preimage_family_iIndepSets μ X h
    -- The lower-orthant factorization already gives independence on the generating π-system,
    -- so the revised closing helper finishes the converse without extra measurability hypotheses.
    exact iIndepFun_of_iIndepSets_preimage_Iic μ X hX h_iic
