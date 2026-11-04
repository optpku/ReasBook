/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Theorem 3.5. The system `A *ᵥ x = b, x ≥ 0` is feasible if and only if `u ⬝ᵥ b ≤ 0`
for every multiplier `u` satisfying `u ᵥ* A ≤ 0`. -/
theorem feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃ x : n → 𝕜, A *ᵥ x = b ∧ 0 ≤ x) ↔
      ∀ u : m → 𝕜, u ᵥ* A ≤ 0 → u ⬝ᵥ b ≤ 0 := by
  constructor
  · rintro ⟨x, rfl, hx_nonneg⟩ u huA
    calc
      u ⬝ᵥ (A *ᵥ x) = (u ᵥ* A) ⬝ᵥ x := by rw [Matrix.dotProduct_mulVec]
      _ ≤ 0 := by
        simpa [dotProduct] using
          Finset.sum_nonpos fun j _ ↦ by
            have hneg : 0 ≤ -((u ᵥ* A) j) := neg_nonneg.mpr (huA j)
            have hmul : 0 ≤ -((u ᵥ* A) j) * x j := mul_nonneg hneg (hx_nonneg j)
            nlinarith
  · intro h_multiplier
    by_contra h_feasible
    classical
    let M : Matrix ((m ⊕ m) ⊕ n) n 𝕜 :=
      Matrix.fromRows (Matrix.fromRows A (-A)) (-(1 : Matrix n n 𝕜))
    let c : ((m ⊕ m) ⊕ n) → 𝕜 :=
      Sum.elim (Sum.elim b (-b)) 0
    have h_system :
        (∃ x : n → 𝕜, M *ᵥ x ≤ c) ↔ ∃ x : n → 𝕜, A *ᵥ x = b ∧ 0 ≤ x := by
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, le_antisymm ?_ ?_, ?_⟩
        · intro i
          simpa [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using
            hx (Sum.inl (Sum.inl i))
        · intro i
          have hi :
              (-(A *ᵥ x)) i ≤ (-b) i := by
            simpa [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using
              hx (Sum.inl (Sum.inr i))
          simpa using (neg_le_neg_iff.mp hi)
        · intro i
          have hi : (-x) i ≤ (0 : n → 𝕜) i := by
            simpa [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using
              hx (Sum.inr i)
          simpa using (neg_nonpos.mp hi)
      · rintro ⟨x, hx_eq, hx_nonneg⟩
        refine ⟨x, ?_⟩
        intro s
        rcases s with (i | i) | j
        · simp [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, congrFun hx_eq i]
        · simp [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, congrFun hx_eq i]
        · simpa [M, c, Matrix.fromRows_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using
            neg_nonpos.mpr (hx_nonneg j)
    have h_infeasible : ¬ ∃ x : n → 𝕜, M *ᵥ x ≤ c := by
      exact fun hx ↦ h_feasible (h_system.mp hx)
    obtain ⟨v, hv⟩ := (farkas_lemma_linear_inequalities M c).mp h_infeasible
    let v₁ : m → 𝕜 := fun i ↦ v (Sum.inl (Sum.inl i))
    let v₂ : m → 𝕜 := fun i ↦ v (Sum.inl (Sum.inr i))
    let w : m → 𝕜 := v₂ - v₁
    have hw_eq :
        w ᵥ* A = -(fun j ↦ v (Sum.inr j)) := by
      ext j
      have h_ann :
          v₁ ᵥ* A + v₂ ᵥ* (-A) + (fun k ↦ v (Sum.inr k)) ᵥ* (-(1 : Matrix n n 𝕜)) = 0 :=
        by
          simpa [M, v₁, v₂, Matrix.vecMul_fromRows] using hv.annihilates
      have hj : (v₁ ᵥ* A) j - (v₂ ᵥ* A) j - v (Sum.inr j) = 0 := by
        simpa [Matrix.vecMul_neg, Matrix.vecMul_one, sub_eq_add_neg] using congrFun h_ann j
      have hwj : (w ᵥ* A) j = (v₂ ᵥ* A) j - (v₁ ᵥ* A) j := by
        simpa [w] using congrFun (Matrix.sub_vecMul A v₂ v₁) j
      have hj' : (v₂ ᵥ* A) j - (v₁ ᵥ* A) j = -v (Sum.inr j) := by
        linarith
      exact hwj.trans hj'
    have hw_nonpos : w ᵥ* A ≤ 0 := by
      intro j
      have hj_nonneg : 0 ≤ v (Sum.inr j) := hv.nonneg (Sum.inr j)
      have hj_eq : (w ᵥ* A) j = -v (Sum.inr j) := congrFun hw_eq j
      rw [hj_eq]
      exact neg_nonpos.mpr hj_nonneg
    have hw_pos : 0 < w ⬝ᵥ b := by
      have hv_rhs :
          v ⬝ᵥ c = v₁ ⬝ᵥ b - v₂ ⬝ᵥ b := by
        have hv_split :
            v = Sum.elim (Sum.elim v₁ v₂) (fun j ↦ v (Sum.inr j)) := by
          funext s
          rcases s with (i | i) | j <;> rfl
        calc
          v ⬝ᵥ c = v ⬝ᵥ Sum.elim (Sum.elim b (-b)) 0 := by rfl
          _ = (Sum.elim v₁ v₂) ⬝ᵥ Sum.elim b (-b) + (fun j ↦ v (Sum.inr j)) ⬝ᵥ 0 := by
            rw [hv_split, sumElim_dotProduct_sumElim]
            simp
          _ = (Sum.elim v₁ v₂) ⬝ᵥ Sum.elim b (-b) := by simp
          _ = v₁ ⬝ᵥ b + v₂ ⬝ᵥ (-b) := by rw [sumElim_dotProduct_sumElim]
          _ = v₁ ⬝ᵥ b - v₂ ⬝ᵥ b := by simp [sub_eq_add_neg]
      have hw_dot : w ⬝ᵥ b = v₂ ⬝ᵥ b - v₁ ⬝ᵥ b := by
        simp [w, sub_dotProduct]
      linarith [hv.negative_rhs, hv_rhs, hw_dot]
    exact not_lt_of_ge (h_multiplier w hw_nonpos) hw_pos
