/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4

open scoped Matrix

variable {𝕜 : Type*}

section OrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Theorem 3.6. The system `A *ᵥ x + B *ᵥ y ≤ f`, `C *ᵥ x + D *ᵥ y = g`, `0 ≤ x` is feasible if
and only if `u ⬝ᵥ f + v ⬝ᵥ g ≥ 0` for every pair `(u, v)` satisfying
`0 ≤ u`, `0 ≤ u ᵥ* A + v ᵥ* C`, and `u ᵥ* B + v ᵥ* D = 0`. -/
theorem mixed_linear_system_feasible_iff_nonnegative_multiplier_evaluation
    {m p n q : Type*} [Fintype m] [Fintype p] [Fintype n] [Fintype q]
    (A : Matrix m n 𝕜)
    (B : Matrix m p 𝕜)
    (C : Matrix q n 𝕜)
    (D : Matrix q p 𝕜)
    (f : m → 𝕜)
    (g : q → 𝕜) :
    (∃ x : n → 𝕜, ∃ y : p → 𝕜,
      0 ≤ x ∧ A *ᵥ x + B *ᵥ y ≤ f ∧ C *ᵥ x + D *ᵥ y = g) ↔
      ∀ u : m → 𝕜, ∀ v : q → 𝕜,
        0 ≤ u →
          0 ≤ u ᵥ* A + v ᵥ* C →
            u ᵥ* B + v ᵥ* D = 0 →
              0 ≤ u ⬝ᵥ f + v ⬝ᵥ g := by
  classical
  let M₁ : Matrix (m ⊕ q) (n ⊕ p) 𝕜 := Matrix.fromBlocks A B C D
  let M₂ : Matrix (q ⊕ n) (n ⊕ p) 𝕜 := Matrix.fromBlocks (-C) (-D) (-(1 : Matrix n n 𝕜)) 0
  let M : Matrix ((m ⊕ q) ⊕ (q ⊕ n)) (n ⊕ p) 𝕜 := Matrix.fromRows M₁ M₂
  let c : ((m ⊕ q) ⊕ (q ⊕ n)) → 𝕜 :=
    Sum.elim (Sum.elim f g) (Sum.elim (-g) 0)
  have h_feasible :
      (∃ z : n ⊕ p → 𝕜, M *ᵥ z ≤ c) ↔
        ∃ x : n → 𝕜, ∃ y : p → 𝕜,
          0 ≤ x ∧ A *ᵥ x + B *ᵥ y ≤ f ∧ C *ᵥ x + D *ᵥ y = g := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z ∘ Sum.inl, z ∘ Sum.inr, ?_, ?_, ?_⟩
      · intro i
        have hi : (M₂ *ᵥ z) (Sum.inr i) ≤ 0 := by
          simpa [M, c] using hz (Sum.inr (Sum.inr i))
        have hi' : -((z ∘ Sum.inl) i) ≤ 0 := by
          simpa [M₂, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hi
        exact neg_nonpos.mp hi'
      · intro i
        have hi : (M₁ *ᵥ z) (Sum.inl i) ≤ f i := by
          simpa [M, c] using hz (Sum.inl (Sum.inl i))
        simpa [M₁, Matrix.fromBlocks_mulVec] using hi
      · apply le_antisymm
        · intro i
          have hi : (M₁ *ᵥ z) (Sum.inr i) ≤ g i := by
            simpa [M, c] using hz (Sum.inl (Sum.inr i))
          simpa [M₁, Matrix.fromBlocks_mulVec] using hi
        · intro i
          have hi : (M₂ *ᵥ z) (Sum.inl i) ≤ -g i := by
            simpa [M, c] using hz (Sum.inr (Sum.inl i))
          have hi' :
              -((C *ᵥ (z ∘ Sum.inl)) i) + -((D *ᵥ (z ∘ Sum.inr)) i) ≤ -g i := by
            simpa [M₂, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, add_assoc, add_left_comm,
              add_comm] using hi
          have hi'' : -((C *ᵥ (z ∘ Sum.inl) + D *ᵥ (z ∘ Sum.inr)) i) ≤ -g i := by
            simpa [Pi.add_apply, add_comm] using hi'
          simpa [add_comm] using neg_le_neg_iff.mp hi''
    · rintro ⟨x, y, hx, hxy, hEq⟩
      refine ⟨Sum.elim x y, ?_⟩
      intro s
      rcases s with (i | i) | (i | i)
      · have hi : (A *ᵥ x + B *ᵥ y) i ≤ f i := hxy i
        simpa [M, M₁, Matrix.fromBlocks_mulVec] using hi
      · have hi : (C *ᵥ x + D *ᵥ y) i ≤ g i := le_of_eq (congrFun hEq i)
        simpa [M, c, M₁, Matrix.fromBlocks_mulVec] using hi
      · have hi : -((C *ᵥ x + D *ᵥ y) i) ≤ -g i := by
          rw [congrFun hEq i]
        simpa [M, c, M₂, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, add_assoc, add_left_comm,
          add_comm, Pi.add_apply] using hi
      · have hi : -(x i) ≤ 0 := neg_nonpos.mpr (hx i)
        simpa [M, c, M₂, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] using hi
  have h_certificate :
      (∃ w : ((m ⊕ q) ⊕ (q ⊕ n)) → 𝕜, IsFarkasCertificate M c w) ↔
        ∃ u : m → 𝕜, ∃ v : q → 𝕜,
          0 ≤ u ∧ 0 ≤ u ᵥ* A + v ᵥ* C ∧ u ᵥ* B + v ᵥ* D = 0 ∧ u ⬝ᵥ f + v ⬝ᵥ g < 0 := by
    constructor
    · rintro ⟨w, hw⟩
      let u : m → 𝕜 := (w ∘ Sum.inl) ∘ Sum.inl
      let v₁ : q → 𝕜 := (w ∘ Sum.inl) ∘ Sum.inr
      let v₂ : q → 𝕜 := (w ∘ Sum.inr) ∘ Sum.inl
      let s : n → 𝕜 := (w ∘ Sum.inr) ∘ Sum.inr
      let v : q → 𝕜 := v₁ - v₂
      have h_ann :
          (w ∘ Sum.inl) ᵥ* M₁ + (w ∘ Sum.inr) ᵥ* M₂ = 0 := by
        simpa [M, Matrix.vecMul_fromRows] using hw.annihilates
      have hs :
          u ᵥ* A + v ᵥ* C = s := by
        ext j
        have hj :
            (u ᵥ* A) j + (v₁ ᵥ* C) j + (-((v₂ ᵥ* C) j) + -(s j)) = 0 := by
          simpa [Function.comp, M₁, M₂, u, v₁, v₂, s, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg,
            Matrix.vecMul_one] using congrFun h_ann (Sum.inl j)
        have hvCj : (v ᵥ* C) j = (v₁ ᵥ* C) j - (v₂ ᵥ* C) j := by
          simpa [v] using congrFun (Matrix.sub_vecMul C v₁ v₂) j
        have hEq : (u ᵥ* A) j + ((v₁ ᵥ* C) j - (v₂ ᵥ* C) j) = s j := by
          linarith
        simpa [Pi.add_apply, hvCj] using hEq
      have huvd :
          u ᵥ* B + v ᵥ* D = 0 := by
        ext j
        have hj : (u ᵥ* B) j + ((v₁ ᵥ* D) j + -((v₂ ᵥ* D) j)) = 0 := by
          simpa [M₁, M₂, u, v₁, v₂, s, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg,
            add_assoc, add_left_comm, add_comm] using congrFun h_ann (Sum.inr j)
        have hvDj : (v ᵥ* D) j = (v₁ ᵥ* D) j - (v₂ ᵥ* D) j := by
          simpa [v] using congrFun (Matrix.sub_vecMul D v₁ v₂) j
        have hEq : (u ᵥ* B) j + ((v₁ ᵥ* D) j - (v₂ ᵥ* D) j) = 0 := by
          linarith
        simpa [Pi.add_apply, hvDj] using hEq
      have h_rhs : w ⬝ᵥ c = u ⬝ᵥ f + v ⬝ᵥ g := by
        have hw_split :
            w = Sum.elim (Sum.elim u v₁) (Sum.elim v₂ s) := by
          funext t
          rcases t with (i | i) | (i | i) <;> rfl
        calc
          w ⬝ᵥ c
              = Sum.elim (Sum.elim u v₁) (Sum.elim v₂ s) ⬝ᵥ
                  Sum.elim (Sum.elim f g) (Sum.elim (-g) 0) := by
                    rw [hw_split]
          _ = (Sum.elim u v₁) ⬝ᵥ Sum.elim f g + (Sum.elim v₂ s) ⬝ᵥ Sum.elim (-g) 0 := by
                rw [sumElim_dotProduct_sumElim]
          _ = (u ⬝ᵥ f + v₁ ⬝ᵥ g) + (v₂ ⬝ᵥ (-g) + s ⬝ᵥ 0) := by
                rw [sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
          _ = u ⬝ᵥ f + v ⬝ᵥ g := by
                simp [v, sub_eq_add_neg, add_assoc, add_comm]
      refine ⟨u, v, ?_, ?_, huvd, ?_⟩
      · intro i
        exact hw.nonneg (Sum.inl (Sum.inl i))
      · intro j
        rw [congrFun hs j]
        exact hw.nonneg (Sum.inr (Sum.inr j))
      · simpa [h_rhs] using hw.negative_rhs
    · rintro ⟨u, v, hu, huvC, huvd, hneg⟩
      let v₁ : q → 𝕜 := fun i ↦ max (v i) 0
      let v₂ : q → 𝕜 := fun i ↦ max (-v i) 0
      let s : n → 𝕜 := u ᵥ* A + v ᵥ* C
      let w : ((m ⊕ q) ⊕ (q ⊕ n)) → 𝕜 := Sum.elim (Sum.elim u v₁) (Sum.elim v₂ s)
      have hv : v₁ - v₂ = v := by
        funext i
        simp [v₁, v₂]
      refine ⟨w, ?_⟩
      refine
        { nonneg := ?_
          annihilates := ?_
          negative_rhs := ?_ }
      · intro t
        rcases t with (i | i) | (i | i)
        · exact hu i
        · exact le_max_right _ _
        · exact le_max_right _ _
        · exact huvC i
      · have h_ann :
            (w ∘ Sum.inl) ᵥ* M₁ + (w ∘ Sum.inr) ᵥ* M₂ = 0 := by
          ext j
          rcases j with j | j
          · have hvCj : (v ᵥ* C) j = (v₁ ᵥ* C) j - (v₂ ᵥ* C) j := by
              rw [← hv]
              simpa using congrFun (Matrix.sub_vecMul C v₁ v₂) j
            have hsj : (u ᵥ* A) j + (v₁ ᵥ* C) j - (v₂ ᵥ* C) j = s j := by
              have hsju : (u ᵥ* A + v ᵥ* C) j = s j := by
                simp [s]
              simpa [Pi.add_apply, hvCj, sub_eq_add_neg, add_assoc] using hsju
            have hj : (u ᵥ* A) j + (v₁ ᵥ* C) j - (v₂ ᵥ* C) j - s j = 0 := by
              linarith
            simpa [M₁, M₂, w, s, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg, Matrix.vecMul_one,
              sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hj
          · have hvDj : (v ᵥ* D) j = (v₁ ᵥ* D) j - (v₂ ᵥ* D) j := by
              rw [← hv]
              simpa using congrFun (Matrix.sub_vecMul D v₁ v₂) j
            have hBj : (u ᵥ* B) j + (v₁ ᵥ* D) j - (v₂ ᵥ* D) j = 0 := by
              have hBju : (u ᵥ* B + v ᵥ* D) j = 0 := by
                simpa using congrFun huvd j
              simpa [Pi.add_apply, hvDj, sub_eq_add_neg, add_assoc] using hBju
            have hj : (u ᵥ* B) j + (v₁ ᵥ* D) j - (v₂ ᵥ* D) j = 0 := by
              exact hBj
            simpa [M₁, M₂, w, Matrix.vecMul_fromBlocks, Matrix.vecMul_neg, sub_eq_add_neg,
              add_assoc, add_left_comm, add_comm] using hj
        simpa [M, Matrix.vecMul_fromRows] using h_ann
      · change
          Sum.elim (Sum.elim u v₁) (Sum.elim v₂ s) ⬝ᵥ
              Sum.elim (Sum.elim f g) (Sum.elim (-g) 0) < 0
        rw [sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim, sumElim_dotProduct_sumElim]
        have hneg' : u ⬝ᵥ f + (v₁ - v₂) ⬝ᵥ g < 0 := by
          rw [hv]
          exact hneg
        simpa [sub_dotProduct, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg'
  have h_multiplier :
      (¬ ∃ u : m → 𝕜, ∃ v : q → 𝕜,
        0 ≤ u ∧ 0 ≤ u ᵥ* A + v ᵥ* C ∧ u ᵥ* B + v ᵥ* D = 0 ∧ u ⬝ᵥ f + v ⬝ᵥ g < 0) ↔
        ∀ u : m → 𝕜, ∀ v : q → 𝕜,
          0 ≤ u →
            0 ≤ u ᵥ* A + v ᵥ* C →
              u ᵥ* B + v ᵥ* D = 0 →
                0 ≤ u ⬝ᵥ f + v ⬝ᵥ g := by
    constructor
    · intro h u v hu huvC huvd
      by_contra hneg
      exact h ⟨u, v, hu, huvC, huvd, lt_of_not_ge hneg⟩
    · intro h hneg
      rcases hneg with ⟨u, v, hu, huvC, huvd, hneg⟩
      exact not_lt_of_ge (h u v hu huvC huvd) hneg
  have h_farkas := farkas_lemma_linear_inequalities M c
  have h_no_certificate :
      (¬ ∃ w : ((m ⊕ q) ⊕ (q ⊕ n)) → 𝕜, IsFarkasCertificate M c w) ↔
        ∀ u : m → 𝕜, ∀ v : q → 𝕜,
          0 ≤ u →
            0 ≤ u ᵥ* A + v ᵥ* C →
              u ᵥ* B + v ᵥ* D = 0 →
                0 ≤ u ⬝ᵥ f + v ⬝ᵥ g :=
    (not_congr h_certificate).trans h_multiplier
  exact
    h_feasible.symm.trans <|
      ⟨(fun hz ↦ h_no_certificate.mp (fun hw ↦ (h_farkas.mpr hw) hz)),
        fun h ↦ by
          by_contra hz
          exact (h_no_certificate.mpr h) (h_farkas.mp hz)⟩

end OrderedField
