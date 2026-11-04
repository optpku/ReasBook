/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_4.ch7_sec7_4_theorem_7_18
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_2.ch8_sec8_2_theorem_8_2

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

section Remark813

variable {α : Type*} [Fintype α]

/-- The binary master coefficients are the `0`-`1` multipliers whose total mass is `1`. -/
def binary_master_weights (lam : α → ℝ) : Prop :=
  (∑ a, lam a) = 1 ∧ ∀ a, lam a = 0 ∨ lam a = 1

/-- `binary_master_weights lam` unfolds to the convexity equation together with the `0`-`1`
restriction on every multiplier. -/
theorem binary_master_weights_iff {lam : α → ℝ} :
    binary_master_weights lam ↔
      (∑ a, lam a) = 1 ∧ ∀ a, lam a = 0 ∨ lam a = 1 :=
  Iff.rfl

/-- Helper for Remark 8.13: the one-hot family at `a` is a binary master family. -/
lemma binary_master_weights_single [DecidableEq α] (a : α) :
    binary_master_weights (fun b ↦ if b = a then 1 else 0) := by
  constructor
  · -- Only the anchor index contributes to the total mass.
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb
      simp
    · intro ha
      exact False.elim (ha (by simp))
  · -- Every coefficient of the one-hot family is either `0` or `1`.
    intro b
    by_cases hb : b = a
    · right
      simp [hb]
    · left
      simp [hb]

/-- A family of binary master coefficients has a unique active multiplier. -/
theorem existsUnique_eq_one_of_binary_master_weights {lam : α → ℝ}
    (hbin : binary_master_weights lam) :
    ∃! a, lam a = 1 := by
  classical
  rcases hbin with ⟨hsum, h01⟩
  -- First show that some coefficient must equal `1`, otherwise the total mass is `0`.
  have hexists : ∃ a, lam a = 1 := by
    by_contra hnot
    have hallZero : ∀ a, lam a = 0 := by
      intro a
      rcases h01 a with hzero | hone
      · exact hzero
      · exfalso
        exact hnot ⟨a, hone⟩
    have hsumZero : (∑ a, lam a) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro a ha
      exact hallZero a
    linarith
  rcases hexists with ⟨a, ha⟩
  -- Splitting off the active coefficient shows every other coefficient sums to `0`.
  have hsplit :
      (Finset.univ.erase a).sum lam + lam a = 1 := by
    calc
      (Finset.univ.erase a).sum lam + lam a = ∑ b, lam b := by
        exact Finset.univ.sum_erase_add lam (Finset.mem_univ a)
      _ = 1 := hsum
  have hsumEraseZero : (Finset.univ.erase a).sum lam = 0 := by
    linarith [ha, hsplit]
  have hzeroOff :
      ∀ b ∈ Finset.univ.erase a, lam b = 0 := by
    have hnonneg : ∀ b ∈ Finset.univ.erase a, 0 ≤ lam b := by
      intro b hb
      rcases h01 b with hzero | hone <;> linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsumEraseZero
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_cases hba : b = a
  · exact hba
  · exfalso
    have hbZero : lam b = 0 := hzeroOff b (by simp [hba])
    linarith

/-- Binary master weights are Dantzig-Wolfe coefficients once all ray variables vanish. -/
theorem dantzig_wolfe_coefficients_of_binary_master_weights
    {K H : ℕ} {lam : Fin K → ℝ} {mu : Fin H → ℝ}
    (hbin : binary_master_weights lam)
    (hmu : ∀ h, mu h = 0) :
    dantzig_wolfe_coefficients lam mu := by
  rcases hbin with ⟨hsum, h01⟩
  refine ⟨hsum, ?_, ?_⟩
  · intro k
    rcases h01 k with hzero | hone <;> linarith
  · intro h
    simp [hmu h]

/-- With binary master coefficients, the projected point is exactly one of the listed generators. -/
theorem sum_smul_eq_generator_of_binary_master_weights
    {β : Type*} [AddCommMonoid β] [Module ℝ β]
    (v : α → β) {lam : α → ℝ}
    (hbin : binary_master_weights lam) :
    ∃ a, (∑ b, lam b • v b) = v a := by
  classical
  rcases hbin with ⟨hsum, h01⟩
  rcases existsUnique_eq_one_of_binary_master_weights ⟨hsum, h01⟩ with ⟨a, ha, hunique⟩
  -- Any coefficient different from the active one must vanish.
  have hzeroOff : ∀ b, b ≠ a → lam b = 0 := by
    intro b hba
    rcases h01 b with hzero | hone
    · exact hzero
    · exfalso
      exact hba (hunique b hone)
  have hsumEraseZero : (Finset.univ.erase a).sum (fun b ↦ lam b • v b) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hbZero : lam b = 0 := hzeroOff b (Finset.mem_erase.mp hb).1
    simp [hbZero]
  refine ⟨a, ?_⟩
  -- Splitting the sum at the active index collapses the weighted average to `v a`.
  calc
    ∑ b, lam b • v b = (Finset.univ.erase a).sum (fun b ↦ lam b • v b) + lam a • v a := by
      simpa using (Finset.univ.sum_erase_add (fun b ↦ lam b • v b) (by simp : a ∈ Finset.univ)).symm
    _ = 0 + lam a • v a := by rw [hsumEraseZero]
    _ = v a := by simp [ha]

variable {p K H : ℕ}

/-- Remark 8.13 (1). In the pure-integer case, if the Dantzig-Wolfe ray variables vanish and the
master multipliers are binary, then the projected point is one of the original generators. -/
theorem dantzig_wolfe_point_eq_generator_of_binary_master_weights
    (v : Fin K → Fin p → ℝ)
    (r : Fin H → Fin p → ℝ)
    {lam : Fin K → ℝ}
    {mu : Fin H → ℝ}
    (hbin : binary_master_weights lam)
    (hmu : ∀ h, mu h = 0) :
    ∃ k, dantzig_wolfe_point v r lam mu = v k := by
  rcases sum_smul_eq_generator_of_binary_master_weights v hbin with ⟨k, hk⟩
  -- The ray part disappears because all ray coefficients are zero.
  have hsumMuZero : ∑ h, mu h • r h = 0 := by
    refine Finset.sum_eq_zero ?_
    intro h hh
    simp [hmu h]
  refine ⟨k, ?_⟩
  -- After removing the ray contribution, the Dantzig-Wolfe point is the selected generator.
  calc
    dantzig_wolfe_point v r lam mu = (∑ j, lam j • v j) + ∑ h, mu h • r h := rfl
    _ = (∑ j, lam j • v j) + 0 := by rw [hsumMuZero]
    _ = ∑ j, lam j • v j := by simp
    _ = v k := hk

/-- The projection of the traveling-salesman binary master is the set of Hamiltonian-tour
incidence vectors. -/
def traveling_salesman_binary_master_projection (n : ℕ) :
    Set (complete_graph_edges n → ℝ) :=
  {x |
    ∃ lam : Equiv.Perm (Fin n) → ℝ,
      binary_master_weights lam ∧
        x = ∑ σ, lam σ • hamiltonian_tour_incidence_vector σ}

/-- Membership in `traveling_salesman_binary_master_projection n` is exactly the existence of a
binary multiplier family summing to `1` whose weighted sum equals `x`. -/
theorem mem_traveling_salesman_binary_master_projection_iff
    {n : ℕ} {x : complete_graph_edges n → ℝ} :
    x ∈ traveling_salesman_binary_master_projection n ↔
      ∃ lam : Equiv.Perm (Fin n) → ℝ,
        binary_master_weights lam ∧
          x = ∑ σ, lam σ • hamiltonian_tour_incidence_vector σ :=
  Iff.rfl

/-- Remark 8.13 (2). Replacing the traveling-salesman master multipliers by binary variables makes
the projection equal to the set of Hamiltonian-tour incidence vectors. -/
theorem traveling_salesman_binary_master_projection_eq_tour_range
    (n : ℕ) :
    traveling_salesman_binary_master_projection n =
      Set.range (fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨lam, hbin, rfl⟩
    -- Binary master weights collapse the weighted tour sum to a single Hamiltonian tour vector.
    rcases
        sum_smul_eq_generator_of_binary_master_weights
          (fun σ : Equiv.Perm (Fin n) ↦ hamiltonian_tour_incidence_vector σ) hbin with
      ⟨σ, hσ⟩
    exact ⟨σ, hσ.symm⟩
  · rintro ⟨σ, rfl⟩
    classical
    refine ⟨fun τ : Equiv.Perm (Fin n) ↦ if τ = σ then 1 else 0, ?_, ?_⟩
    · -- The reverse inclusion uses the one-hot binary master family at `σ`.
      exact binary_master_weights_single σ
    · -- The one-hot weighted sum evaluates to the chosen Hamiltonian tour vector.
      symm
      rw [Finset.sum_eq_single σ]
      · simp
      · intro τ hτ hτσ
        simp [hτσ]
      · intro hσ
        exact False.elim (hσ (by simp))

/-- The convex hull of the traveling-salesman binary master projection is the traveling salesman
polytope. -/
theorem convexHull_traveling_salesman_binary_master_projection_eq_travelingSalesmanPolytope
    (n : ℕ) :
    convexHull ℝ (traveling_salesman_binary_master_projection n) =
      travelingSalesmanPolytope n := by
  rw [traveling_salesman_binary_master_projection_eq_tour_range,
    travelingSalesmanPolytope_eq_convexHull]

end Remark813
