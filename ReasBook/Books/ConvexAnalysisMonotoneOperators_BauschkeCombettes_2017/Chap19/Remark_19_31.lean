/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Corollary_19_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace ERealFunction

section MixedConstraints

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {m p : ℕ}

local notation "ConstraintSpace" => EuclideanSpace ℝ (Fin p ⊕ Fin (m - p))

-- Proof sketch: use the explicit branch formula for the mixed-constraint Lagrangian. A finite
-- comparison point of `f` rules out negative inequality multipliers, then rules out
-- `x̄ ∉ dom f`. After
-- that, replacing the `i`-th multiplier by `0` still preserves dual feasibility, and strict
-- inactivity makes the resulting Lagrangian value strictly larger unless `ν̄_i = 0`.
/-- Remark 19.31: in Corollary 19.30, the inequality-block coordinates of a saddle-point
parameter vector are the Lagrange multipliers associated with the primal solution, they satisfy
complementary slackness, and if `dom f` is nonempty then any strictly inactive inequality
constraint has zero multiplier. -/
theorem inequalityMultiplier_eq_zero_of_strictlyInactiveConstraint
    (f : H → Set.Ioi (⊥ : EReal))
    (g : Fin p → H → ℝ)
    (u : Fin (m - p) → H) (ρ : Fin (m - p) → ℝ)
    (hdom : (effectiveDomain f).Nonempty)
    {xbar : H} {νbar : ConstraintSpace}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H)
        (Set.univ : Set ConstraintSpace)
        (ℒ[mixedConstraintPerturbation f g u ρ]) xbar νbar)
    (i : Fin p) (hstrict : g i xbar < 0) :
    νbar (Sum.inl i) = 0 := by
  rcases hdom with ⟨x0, hx0_dom⟩
  have hνbar_nonneg : ∀ k : Fin p, 0 ≤ νbar (Sum.inl k) := by
    intro k
    by_contra hk
    have hnot_nonneg : ¬ ∀ j : Fin p, 0 ≤ νbar (Sum.inl j) := by
      intro h
      exact hk (h k)
    have hlag_x0_νbar : ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar = ⊥ := by
      rw [lagrangian_mixedConstraintPerturbation f g u ρ x0 νbar]
      simp [hx0_dom, hnot_nonneg]
    have hlag_xbar_zero_ne_bot :
        ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 ≠ ⊥ := by
      rw [lagrangian_mixedConstraintPerturbation f g u ρ xbar 0]
      by_cases hxbar : xbar ∈ effectiveDomain f
      · have hfxbar_ne_bot : (f xbar : EReal) ≠ ⊥ := by
          exact ne_of_gt ((f xbar).2)
        simp [hxbar, hfxbar_ne_bot]
      · simp [hxbar]
    have hle :
        ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 ≤ ⊥ := by
      calc
        ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 ≤
            ℒ[mixedConstraintPerturbation f g u ρ] xbar νbar :=
          hsaddle xbar (by simp) 0 (by simp)
        _ ≤ ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar :=
          hsaddle x0 (by simp) νbar (by simp)
        _ = ⊥ := hlag_x0_νbar
    exact hlag_xbar_zero_ne_bot (le_antisymm hle bot_le)
  have hlag_x0_νbar_ne_top :
      ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar ≠ ⊤ := by
    rw [lagrangian_mixedConstraintPerturbation f g u ρ x0 νbar]
    simp [hx0_dom, hνbar_nonneg]
    exact
      EReal.add_ne_top (ne_of_lt (mem_effectiveDomain_iff.mp hx0_dom)) <|
        EReal.add_ne_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
  have hxbar : xbar ∈ effectiveDomain f := by
    by_contra hxbar
    have hlag_xbar_zero : ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 = ⊤ := by
      rw [lagrangian_mixedConstraintPerturbation f g u ρ xbar 0]
      simp [hxbar]
    have hle :
        ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 ≤
          ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar := by
      calc
        ℒ[mixedConstraintPerturbation f g u ρ] xbar 0 ≤
            ℒ[mixedConstraintPerturbation f g u ρ] xbar νbar :=
          hsaddle xbar (by simp) 0 (by simp)
        _ ≤ ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar :=
          hsaddle x0 (by simp) νbar (by simp)
    have hlag_x0_νbar_top :
        ℒ[mixedConstraintPerturbation f g u ρ] x0 νbar = ⊤ := by
      rw [hlag_xbar_zero] at hle
      simpa using hle
    exact hlag_x0_νbar_ne_top hlag_x0_νbar_top
  let ν : ConstraintSpace :=
    (EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ).symm <|
      Function.update ((EuclideanSpace.equiv (Fin p ⊕ Fin (m - p)) ℝ) νbar) (Sum.inl i) 0
  have hν_nonneg : ∀ k : Fin p, 0 ≤ ν (Sum.inl k) := by
    intro k
    by_cases hk : k = i
    · subst hk
      simp [ν]
    · simp [ν, hk, hνbar_nonneg k]
  have hle :
      ℒ[mixedConstraintPerturbation f g u ρ] xbar ν ≤
        ℒ[mixedConstraintPerturbation f g u ρ] xbar νbar :=
    hsaddle xbar (by simp) ν (by simp)
  by_contra hνi
  have hνi_pos : 0 < νbar (Sum.inl i) := lt_of_le_of_ne (hνbar_nonneg i) <| by
    simpa [eq_comm] using hνi
  have hfxbar_ne_top : (f xbar : EReal) ≠ ⊤ :=
    ne_of_lt (mem_effectiveDomain_iff.mp hxbar)
  have hfxbar_ne_bot : (f xbar : EReal) ≠ ⊥ := by
    exact ne_of_gt ((f xbar).2)
  let fxbar : ℝ := (f xbar : EReal).toReal
  have hfxbar_eq : (fxbar : EReal) = (f xbar : EReal) := by
    simpa [fxbar] using (EReal.coe_toReal hfxbar_ne_top hfxbar_ne_bot)
  rw [lagrangian_mixedConstraintPerturbation f g u ρ xbar ν,
    lagrangian_mixedConstraintPerturbation f g u ρ xbar νbar] at hle
  simp [hxbar, hν_nonneg, hνbar_nonneg] at hle
  let inrSum : ConstraintSpace → ℝ := fun μ ↦
    ∑ j : Fin (m - p), μ (Sum.inr j) * (inner ℝ xbar (u j) - ρ j)
  rw [← hfxbar_eq] at hle
  have hle0 :
      (fxbar : EReal) + ((((∑ k : Fin p, ν (Sum.inl k) * g k xbar) : ℝ) : EReal) +
          ((inrSum ν : ℝ) : EReal)) ≤
        (fxbar : EReal) + ((((∑ k : Fin p, νbar (Sum.inl k) * g k xbar) : ℝ) : EReal) +
          ((inrSum νbar : ℝ) : EReal)) := by
    simpa [inrSum] using hle
  have hsum_inr :
      inrSum ν = inrSum νbar := by
    simp [inrSum, ν]
  rw [hsum_inr] at hle0
  have hle' :
      (((∑ k : Fin p, ν (Sum.inl k) * g k xbar) : ℝ) : EReal) +
          ((inrSum νbar : ℝ) : EReal) ≤
        (((∑ k : Fin p, νbar (Sum.inl k) * g k xbar) : ℝ) : EReal) +
          ((inrSum νbar : ℝ) : EReal) :=
    (EReal.addLECancellable_coe fxbar).add_le_add_iff_left.mp hle0
  have hle_real :
      (∑ k : Fin p, ν (Sum.inl k) * g k xbar) + inrSum νbar ≤
        (∑ k : Fin p, νbar (Sum.inl k) * g k xbar) + inrSum νbar := by
    exact_mod_cast (by simpa [← EReal.coe_add] using hle')
  have hsum_update :
      ∑ k : Fin p, ν (Sum.inl k) * g k xbar =
        (∑ k : Fin p, νbar (Sum.inl k) * g k xbar) - νbar (Sum.inl i) * g i xbar := by
    let φ : Fin p → ℝ := fun k ↦ νbar (Sum.inl k) * g k xbar
    have hν_sum :
        ∑ k : Fin p, ν (Sum.inl k) * g k xbar = ∑ k : Fin p, Function.update φ i 0 k := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      by_cases hk' : k = i
      · subst hk'
        simp [φ, ν]
      · simp [φ, ν, hk']
    have hupdate :
        ∑ k : Fin p, Function.update φ i 0 k = ∑ k ∈ Finset.univ \ {i}, φ k := by
      simpa using
        (Finset.sum_update_of_mem (Finset.mem_univ i) φ 0)
    have hsplit :
        (∑ k : Fin p, φ k) = φ i + ∑ k ∈ Finset.univ \ {i}, φ k := by
      exact
        Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ i) φ
    rw [hν_sum, hupdate]
    linarith
  have hmul : νbar (Sum.inl i) * g i xbar < 0 :=
    mul_neg_of_pos_of_neg hνi_pos hstrict
  linarith

end MixedConstraints

end ERealFunction
