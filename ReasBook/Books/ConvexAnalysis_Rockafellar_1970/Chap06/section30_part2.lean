/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part1

section Chap06
section Section30

/-- Helper for Theorem 6.30.13: a negative multiplier coordinate forces the adjoint value to be
`-∞` via the feasible ray `u = a + t e_{i0}`, `x = 0`. -/
lemma helperForTheorem_6_30_13_negativeMultiplierImpliesBot {m n : ℕ}
    (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hF : ConvexBifunction (linearProgramBifunction aStar a A))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (i0 : Fin m) (hneg : uStar i0 < 0) :
    adjointOfConvexBifunction ⟨linearProgramBifunction aStar a A, hF⟩ xStar uStar = (⊥ : EReal) := by
  -- Show the adjoint lies below every real bound by moving far enough along the feasible ray.
  rw [adjointOfConvexBifunction, EReal.eq_bot_iff_forall_lt]
  intro y
  let t : ℝ := |(((a ⬝ᵥ uStar : ℝ) - y) / (-uStar i0))| + 1
  have hden : 0 < -uStar i0 := by
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hratio :
      (((a ⬝ᵥ uStar : ℝ) - y) / (-uStar i0)) < t := by
    -- The choice `t = |r| + 1` dominates the threshold `r`.
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self _) ?_
    linarith [abs_nonneg (((a ⬝ᵥ uStar : ℝ) - y) / (-uStar i0))]
  have hmul :
      ((a ⬝ᵥ uStar : ℝ) - y) < t * (-uStar i0) := by
    exact (div_lt_iff₀ hden).mp hratio
  have hreal : (a ⬝ᵥ uStar : ℝ) + t * uStar i0 < y := by
    linarith
  have hwitness :
      sInf
          (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            linearProgramBifunction aStar a A p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
              (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
        (((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * uStar i0 : ℝ) : EReal)) := by
    -- Insert the explicit feasible witness from the ray into the defining infimum.
    apply sInf_le
    refine ⟨(a + (Pi.single i0 t : Fin m → ℝ), 0), ?_⟩
    simpa [t] using
      helperForTheorem_6_30_13_negativeMultiplierWitnessValue
        (aStar := aStar) (a := a) (A := A) (xStar := xStar) (uStar := uStar)
        (i0 := i0) (t := t) ht
  have hltWitness :
      ((((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * uStar i0 : ℝ) : EReal))) < ((y : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact lt_of_le_of_lt hwitness hltWitness

/-- Helper for Theorem 6.30.13: along the ray `x = t e_{j0}`, `u = a - A x`, the adjoint
integrand changes with slope `aStar j0 - (Aᵀ uStar) j0 - xStar j0`. -/
lemma helperForTheorem_6_30_13_negativeReducedCostWitnessValue {m n : ℕ}
    (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (j0 : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    let x : Fin n → ℝ := Pi.single j0 t
    let u : Fin m → ℝ := a - A.mulVec x
    linearProgramBifunction aStar a A u x - (((x ⬝ᵥ xStar : ℝ) : EReal)) +
        (((u ⬝ᵥ uStar : ℝ) : EReal)) =
      (((a ⬝ᵥ uStar : ℝ) : EReal)) +
        (((t * (aStar j0 - (A.transpose.mulVec uStar) j0 - xStar j0) : ℝ) : EReal)) := by
  -- This ray keeps primal feasibility and isolates the reduced-cost coefficient at coordinate `j0`.
  dsimp
  have hx_nonneg : ∀ j : Fin n, 0 ≤ (Pi.single j0 t : Fin n → ℝ) j := by
    intro j
    by_cases hj : j = j0
    · subst hj
      simp [ht]
    · simp [Pi.single_eq_of_ne hj]
  have hfeas : (∀ j : Fin n, 0 ≤ (Pi.single j0 t : Fin n → ℝ) j) ∧
      ∀ i : Fin m, a i - (A.mulVec (Pi.single j0 t : Fin n → ℝ)) i ≤
        (a - A.mulVec (Pi.single j0 t : Fin n → ℝ)) i := by
    constructor
    · exact hx_nonneg
    · intro i
      simp [Matrix.mulVec_single, sub_eq_add_neg, mul_comm]
  have haStar : (aStar ⬝ᵥ (Pi.single j0 t : Fin n → ℝ) : ℝ) = aStar j0 * t := by
    -- The objective term only sees the `j0`-th coordinate of the ray.
    rw [dotProduct_single]
  have hxStar : ((Pi.single j0 t : Fin n → ℝ) ⬝ᵥ xStar : ℝ) = t * xStar j0 := by
    rw [single_dotProduct]
  have hAterm :
      ((A.mulVec (Pi.single j0 t : Fin n → ℝ)) ⬝ᵥ uStar : ℝ) =
        t * (A.transpose.mulVec uStar) j0 := by
    -- Rewrite `⟪A x, uStar⟫` as `⟪x, Aᵀ uStar⟫` and evaluate the single-coordinate vector.
    rw [Matrix.mulVec_single]
    rw [dotProduct_comm, dotProduct_smul]
    simp [mul_comm, dotProduct, Matrix.mulVec]
  have hu :
      ((a - A.mulVec (Pi.single j0 t : Fin n → ℝ)) ⬝ᵥ uStar : ℝ) =
        (a ⬝ᵥ uStar : ℝ) - t * (A.transpose.mulVec uStar) j0 := by
    rw [sub_dotProduct, hAterm]
  rw [linearProgramBifunction, if_pos hfeas, haStar, hxStar, hu]
  exact_mod_cast (by
    ring :
      aStar j0 * t - t * xStar j0 + ((a ⬝ᵥ uStar : ℝ) - t * (A.transpose.mulVec uStar) j0) =
        (a ⬝ᵥ uStar : ℝ) + t * (aStar j0 - (A.transpose.mulVec uStar) j0 - xStar j0))

/-- Helper for Theorem 6.30.13: a negative reduced cost forces the adjoint value to be `-∞`
via the feasible ray `x = t e_{j0}`, `u = a - A x`. -/
lemma helperForTheorem_6_30_13_negativeReducedCostImpliesBot {m n : ℕ}
    (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hF : ConvexBifunction (linearProgramBifunction aStar a A))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ)
    (j0 : Fin n)
    (hneg : aStar j0 - (A.transpose.mulVec uStar) j0 < xStar j0) :
    adjointOfConvexBifunction ⟨linearProgramBifunction aStar a A, hF⟩ xStar uStar = (⊥ : EReal) := by
  -- Again it suffices to produce, below every real bound, one value from the feasible ray.
  rw [adjointOfConvexBifunction, EReal.eq_bot_iff_forall_lt]
  intro y
  let c : ℝ := aStar j0 - (A.transpose.mulVec uStar) j0 - xStar j0
  let t : ℝ := |(((a ⬝ᵥ uStar : ℝ) - y) / (-c))| + 1
  have hc : c < 0 := by
    dsimp [c]
    linarith
  have hden : 0 < -c := by
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hratio :
      (((a ⬝ᵥ uStar : ℝ) - y) / (-c)) < t := by
    -- The same `|r| + 1` choice dominates the required threshold.
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self _) ?_
    linarith [abs_nonneg (((a ⬝ᵥ uStar : ℝ) - y) / (-c))]
  have hmul :
      ((a ⬝ᵥ uStar : ℝ) - y) < t * (-c) := by
    exact (div_lt_iff₀ hden).mp hratio
  have hreal : (a ⬝ᵥ uStar : ℝ) + t * c < y := by
    linarith
  have hwitness :
      sInf
          (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            linearProgramBifunction aStar a A p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
              (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) ≤
        (((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * c : ℝ) : EReal)) := by
    -- The ray witness realizes the affine expression with negative slope `c`.
    apply sInf_le
    refine ⟨(a - A.mulVec (Pi.single j0 t : Fin n → ℝ), Pi.single j0 t), ?_⟩
    simpa [c, t] using
      helperForTheorem_6_30_13_negativeReducedCostWitnessValue
        (aStar := aStar) (a := a) (A := A) (xStar := xStar) (uStar := uStar)
        (j0 := j0) (t := t) ht

  have hltWitness :
      ((((a ⬝ᵥ uStar : ℝ) : EReal)) + (((t * c : ℝ) : EReal))) < ((y : ℝ) : EReal) := by
    exact_mod_cast hreal
  exact lt_of_le_of_lt hwitness hltWitness

/-- Theorem 6.30.13: if `F : ℝ^m → ℝ^n` is the polyhedral convex bifunction
`F_u(x) = ⟪aStar, x⟫ + δ(x | x ≥ 0, a - A x ≤ u)`, then its adjoint satisfies
`F*(xStar, uStar) = ⟪a, uStar⟫` when `uStar ≥ 0` and `xStar ≤ aStar - Aᵀ uStar`, and
`F*(xStar, uStar) = -∞` otherwise. -/
theorem adjointOfLinearProgramBifunction_eq {m n : ℕ} (aStar : Fin n → ℝ) (a : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hF : ConvexBifunction (linearProgramBifunction aStar a A))
    (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    adjointOfConvexBifunction ⟨linearProgramBifunction aStar a A, hF⟩ xStar uStar =
      if (∀ i : Fin m, 0 ≤ uStar i) ∧
          ∀ j : Fin n, xStar j ≤ aStar j - (A.transpose.mulVec uStar) j then
        ((a ⬝ᵥ uStar : ℝ) : EReal)
      else
        ⊥ := by
  by_cases hdual : (∀ i : Fin m, 0 ≤ uStar i) ∧
      ∀ j : Fin n, xStar j ≤ aStar j - (A.transpose.mulVec uStar) j
  · -- In the dual-feasible case, the adjoint infimum is squeezed by a global lower bound and
    -- the explicit witness `(u, x) = (a, 0)`.
    rw [if_pos hdual, adjointOfConvexBifunction]
    apply le_antisymm
    · apply sInf_le
      refine ⟨(a, 0), ?_⟩
      simpa using
        helperForTheorem_6_30_13_dualFeasibleWitness
          (aStar := aStar) (xStar := xStar) (a := a) (uStar := uStar) (A := A)
    · apply le_sInf
      rintro y ⟨⟨u, x⟩, rfl⟩
      by_cases hfeas : (∀ i : Fin n, 0 ≤ x i) ∧
          ∀ i : Fin m, a i - (A.mulVec x) i ≤ u i
      · -- Every feasible pair satisfies the Lagrangian lower bound from dual feasibility.
        simpa [linearProgramBifunction, hfeas] using
          helperForTheorem_6_30_13_dualFeasibleLowerBound
          (aStar := aStar) (xStar := xStar) (a := a) (uStar := uStar) (A := A)
          hdual hfeas.1 hfeas.2
      · -- Infeasible pairs contribute `⊤`, which is trivially above the desired lower bound.
        have hnotFeasible :
            ¬ ((∀ i : Fin n, 0 ≤ x i) ∧ ∀ i : Fin m, a i ≤ u i + (A.mulVec x) i) := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfeas
        simp [linearProgramBifunction, hnotFeasible]
  · -- Route correction: instead of trying to optimize the full infimum directly, split the
    -- infeasible case into the two textbook obstruction rays.
    rw [if_neg hdual]
    by_cases huNonneg : ∀ i : Fin m, 0 ≤ uStar i
    · have hnotReduced :
          ¬ ∀ j : Fin n, xStar j ≤ aStar j - (A.transpose.mulVec uStar) j := by
        intro hreduced
        exact hdual ⟨huNonneg, hreduced⟩
      push_neg at hnotReduced
      rcases hnotReduced with ⟨j0, hj0⟩
      exact helperForTheorem_6_30_13_negativeReducedCostImpliesBot
        (aStar := aStar) (a := a) (A := A) (hF := hF) (xStar := xStar) (uStar := uStar)
        (j0 := j0) hj0
    · push_neg at huNonneg
      rcases huNonneg with ⟨i0, hi0⟩
      exact helperForTheorem_6_30_13_negativeMultiplierImpliesBot
        (aStar := aStar) (a := a) (A := A) (hF := hF) (xStar := xStar) (uStar := uStar)
        (i0 := i0) hi0

end Section30
end Chap06
