/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Theorem_4_1_4

noncomputable section

/-- Helper for Theorem 4.1.8: a nonnegative scalar sequence satisfying the normalized cubic
one-step recurrence has the standard inverse-square decay. -/
lemma inverse_square_rate_of_normalized_cubic_recurrence
    {Δ : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k)
    (hgap0 : Δ 0 ≤ c)
    (hstep_gap :
      ∀ k : ℕ, ∀ α : ℝ, α ∈ Set.Icc (0 : ℝ) 1 →
        Δ (k + 1) ≤ (1 - α) * Δ k + c * ((1 / 3 : ℝ) * α ^ (3 : ℕ))) :
    ∀ k : ℕ,
      Δ k ≤ c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := by
  let α : ℕ → ℝ := fun k ↦ Real.sqrt (Δ k / c)
  have hΔ_le_c : ∀ k : ℕ, Δ k ≤ c := by
    intro k
    induction k with
    | zero =>
        simpa using hgap0
    | succ k hk =>
        have hstep_one :
            Δ (k + 1) ≤ c * ((1 / 3 : ℝ) * (1 : ℝ) ^ (3 : ℕ)) := by
          simpa using hstep_gap k 1 (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
        have hthird_le_c : c * ((1 / 3 : ℝ) * (1 : ℝ) ^ (3 : ℕ)) ≤ c := by
          nlinarith [hc]
        exact hstep_one.trans hthird_le_c
  have hα_mem : ∀ k : ℕ, α k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    refine ⟨?_, ?_⟩
    · simpa [α] using Real.sqrt_nonneg (Δ k / c)
    · have hsqrt_le_one : Real.sqrt (Δ k / c) ≤ 1 := by
        apply (Real.sqrt_le_iff).2
        constructor
        · norm_num
        · exact (div_le_iff₀ hc).2 (hΔ_le_c k)
      simpa [α] using hsqrt_le_one
  have hΔ_eq : ∀ k : ℕ, Δ k = c * α k ^ (2 : ℕ) := by
    intro k
    have hsq : α k ^ (2 : ℕ) = Δ k / c := by
      simp [α, Real.sq_sqrt, div_nonneg (hΔ_nonneg k) hc.le]
    have hmul := congrArg (fun t : ℝ ↦ c * t) hsq
    field_simp [hc.ne'] at hmul
    nlinarith [hmul]
  have hrecurrence :
      ∀ k : ℕ,
        Δ (k + 1) ≤ c * (α k ^ (2 : ℕ) - (2 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
    intro k
    have hstepk := hstep_gap k (α k) (hα_mem k)
    rw [hΔ_eq k] at hstepk
    nlinarith
  have hreciprocal_or_zero :
      ∀ k : ℕ, Δ k = 0 ∨ 1 / α k ≥ 1 + (k : ℝ) / 3 := by
    intro k
    induction k with
    | zero =>
        by_cases hΔ0 : Δ 0 = 0
        · exact Or.inl hΔ0
        · have hα0_nonneg : 0 ≤ α 0 := (hα_mem 0).1
          have hα0_ne : α 0 ≠ 0 := by
            intro hα0_zero
            have : Δ 0 = 0 := by
              rw [hΔ_eq 0, hα0_zero]
              ring
            exact hΔ0 this
          have hα0_pos : 0 < α 0 := lt_of_le_of_ne hα0_nonneg (Ne.symm hα0_ne)
          have hone : 1 ≤ 1 / α 0 := by
            simpa using one_div_le_one_div_of_le hα0_pos (hα_mem 0).2
          exact Or.inr (by nlinarith)
    | succ k hk =>
        rcases hk with hΔk_zero | hk_recip
        · have hαk_zero : α k = 0 := by
            rw [hΔ_eq k] at hΔk_zero
            have hsq_zero : α k ^ (2 : ℕ) = 0 := by
              nlinarith [hΔk_zero, hc]
            nlinarith [sq_nonneg (α k), hsq_zero]
          have hnext_le_zero : Δ (k + 1) ≤ 0 := by
            have hrec := hrecurrence k
            rw [hαk_zero] at hrec
            simpa using hrec
          exact Or.inl (le_antisymm hnext_le_zero (hΔ_nonneg (k + 1)))
        · have hgrowth :
              α (k + 1) ∈ Set.Icc (0 : ℝ) (α k) ∧
                (Δ (k + 1) = 0 ∨ 1 / α (k + 1) ≥ 1 / α k + 1 / 3) := by
            simpa [α] using
              reciprocal_alpha_growth_of_cubic_step hc (hα_mem k)
                (hΔ_nonneg (k + 1)) (hrecurrence k)
          rcases hgrowth with ⟨_, hgrowth⟩
          rcases hgrowth with hΔnext_zero | hnext_recip
          · exact Or.inl hΔnext_zero
          · have hsum : 1 / α (k + 1) ≥ 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
              have hsum' : 1 / α (k + 1) ≥ (1 + (k : ℝ) / 3) + 1 / 3 := by
                nlinarith [hk_recip, hnext_recip]
              have hcast :
                  (1 + (k : ℝ) / 3) + 1 / 3 = 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
                rw [Nat.cast_add]
                ring
              rw [← hcast]
              exact hsum'
            exact Or.inr hsum
  intro k
  rcases hreciprocal_or_zero k with hΔk_zero | hk_recip
  · simpa [hΔk_zero] using
      (show 0 ≤ c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) by positivity)
  · have hαk_nonneg : 0 ≤ α k := (hα_mem k).1
    have hαk_ne : α k ≠ 0 := by
      intro hαk_zero
      have hkfalse : ¬((0 : ℝ) ≥ 1 + (k : ℝ) / 3) := by
        have : (0 : ℝ) < 1 + (k : ℝ) / 3 := by
          positivity
        linarith
      have : (0 : ℝ) ≥ 1 + (k : ℝ) / 3 := by
        simpa [hαk_zero] using hk_recip
      exact hkfalse this
    have hαk_pos : 0 < α k := lt_of_le_of_ne hαk_nonneg (Ne.symm hαk_ne)
    have hs_pos : 0 < 1 + (k : ℝ) / 3 := by
      positivity
    have hsα : (1 + (k : ℝ) / 3) * α k ≤ 1 := by
      exact (le_div_iff₀ hαk_pos).1 (by simpa using hk_recip)
    have hαk_le : α k ≤ 1 / (1 + (k : ℝ) / 3) := by
      exact (le_div_iff₀ hs_pos).2 (by simpa [mul_comm] using hsα)
    have hsq_le :
        α k ^ (2 : ℕ) ≤ (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hαk_nonneg hαk_le 2
    calc
      Δ k = c * α k ^ (2 : ℕ) := hΔ_eq k
      _ ≤ c * (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) := by
        gcongr
      _ = c / (1 + (k : ℝ) / 3) ^ (2 : ℕ) := by
        have hs_ne : (1 + (k : ℝ) / 3) ≠ 0 := by
          positivity
        field_simp [hs_ne]
        ring
