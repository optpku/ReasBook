/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_13
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Normed

public section

open scoped Matrix.Norms.Frobenius

noncomputable section

namespace Matrix

namespace Norms.Frobenius

/-- Helper for Proposition 5.14: view a real matrix in the nested `WithLp` model carrying the
Frobenius inner product. -/
def toFrobeniusVecReal
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℝ) :
    WithLp 2 (m → WithLp 2 (n → ℝ)) :=
  WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (A i)

/-- Helper for Proposition 5.14: the Frobenius-scoped inner product on real matrices is the
nested finite-product `L²` inner product. -/
@[instance_reducible] noncomputable def frobeniusInnerReal
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] : Inner ℝ (Matrix m n ℝ) where
  inner A B := inner ℝ (toFrobeniusVecReal A) (toFrobeniusVecReal B)

attribute [scoped instance] frobeniusInnerReal

/-- Helper for Proposition 5.14: the Frobenius scope on real matrices carries the corresponding
inner-product-space structure. -/
noncomputable scoped instance frobeniusInnerProductSpaceReal
    {m : Type*} {n : Type*} [Fintype m] [Fintype n] :
    InnerProductSpace ℝ (Matrix m n ℝ) where
  inner := Matrix.Norms.Frobenius.frobeniusInnerReal.inner
  norm_sq_eq_re_inner := by
    intro A
    -- Transport the Frobenius norm to the nested `PiLp` model.
    change ‖toFrobeniusVecReal A‖ ^ 2 =
      RCLike.re (inner ℝ (toFrobeniusVecReal A) (toFrobeniusVecReal A))
    simpa using norm_sq_eq_re_inner (𝕜 := ℝ) (toFrobeniusVecReal A)
  conj_inner_symm := by
    intro A B
    -- Hermitian symmetry is inherited from the ambient `PiLp` inner product.
    change star (inner ℝ (toFrobeniusVecReal B) (toFrobeniusVecReal A)) =
      inner ℝ (toFrobeniusVecReal A) (toFrobeniusVecReal B)
    simpa using inner_conj_symm (𝕜 := ℝ) (toFrobeniusVecReal A) (toFrobeniusVecReal B)
  add_left := by
    intro A B C
    -- Additivity is computed in the nested finite-product model.
    have hAdd :
        toFrobeniusVecReal (A + B) =
          toFrobeniusVecReal A + toFrobeniusVecReal B := by
      ext i j
      simp [toFrobeniusVecReal, Matrix.add_apply]
    change inner ℝ (toFrobeniusVecReal (A + B)) (toFrobeniusVecReal C) =
      inner ℝ (toFrobeniusVecReal A) (toFrobeniusVecReal C) +
        inner ℝ (toFrobeniusVecReal B) (toFrobeniusVecReal C)
    rw [hAdd]
    simpa using inner_add_left (𝕜 := ℝ)
      (toFrobeniusVecReal A) (toFrobeniusVecReal B) (toFrobeniusVecReal C)
  smul_left := by
    intro A B a
    -- Scalar compatibility is likewise inherited from the ambient `PiLp` model.
    have hSmul :
        toFrobeniusVecReal (a • A) = a • toFrobeniusVecReal A := by
      ext i j
      simp [toFrobeniusVecReal, Matrix.smul_apply]
    change inner ℝ (toFrobeniusVecReal (a • A)) (toFrobeniusVecReal B) =
      star a * inner ℝ (toFrobeniusVecReal A) (toFrobeniusVecReal B)
    rw [hSmul]
    simpa using inner_smul_left (𝕜 := ℝ) (toFrobeniusVecReal A) (toFrobeniusVecReal B) a

end Norms.Frobenius

/-- Helper for Proposition 5.14: left multiplication by the Chapter 5 right-shift matrix sends the
`k`th standard basis vector to the rotated basis vector at `finRotate n k`. -/
lemma circulantRightShift_mulVec_single
    {n : ℕ} (k : Fin n) :
    Matrix.circulantRightShift n *ᵥ Pi.single k (1 : ℝ) = Pi.single (finRotate n k) (1 : ℝ) := by
  ext i
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i.1) (Nat.succ_le_of_lt i.is_lt)
  -- Local instance justification (index arithmetic): `finRotate_symm_apply` and `sub_eq_iff_eq_add`
  -- on `Fin n` require `[NeZero n]`, and the witness `i : Fin n` supplies `0 < n`.
  letI : NeZero n := ⟨Nat.ne_of_gt hn_pos⟩
  have hi :=
    congrFun (Matrix.circulantRightShift_mulVec (n := n) (Pi.single k (1 : ℝ))) i
  by_cases h : i = k + 1
  · have hsub : i - 1 = k := by
      simpa using (sub_eq_iff_eq_add.mpr h)
    simpa [Function.comp_apply, Pi.single_apply, finRotate_symm_apply, h, hsub, add_comm] using hi
  · have hsub : i - 1 ≠ k := by
      intro hk
      apply h
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hk)
    simpa [Function.comp_apply, Pi.single_apply, finRotate_symm_apply, h, hsub, add_comm] using hi

/-- Helper for Proposition 5.14: the `m`th power of the Chapter 5 right-shift matrix sends the
`k`th standard basis vector to the basis vector indexed by `((finRotate n)^[m]) k`. -/
lemma rightShiftPow_mulVec_single
    {n : ℕ} (m : ℕ) (k : Fin n) :
    (Matrix.circulantRightShift n ^ m) *ᵥ Pi.single k (1 : ℝ) =
      Pi.single (((finRotate n)^[m]) k) (1 : ℝ) := by
  induction m generalizing k with
  | zero =>
      -- At power zero, the identity matrix fixes every basis vector.
      rw [pow_zero, Matrix.mulVec_single_one]
      ext i
      simp [Matrix.col, Matrix.one_apply, Pi.single_apply]
  | succ m ih =>
      -- One more factor of the shift advances the basis index by one more rotation.
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      rw [Function.iterate_succ_apply']
      simpa using circulantRightShift_mulVec_single (n := n) (((finRotate n)^[m]) k)

/-- Helper for Proposition 5.14: the circulant basis matrix generated by `Pi.single j 1` has a
single `1` in each column, located at the row `k + j`. -/
lemma circulantSingle_apply
    {n : ℕ} (j i k : Fin n) :
    Matrix.circulant (Pi.single j (1 : ℝ)) i k = if i = k + j then 1 else 0 := by
  have hn_pos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ i.1) (Nat.succ_le_of_lt i.is_lt)
  -- Local instance justification (index arithmetic): `sub_eq_iff_eq_add` on `Fin n` needs
  -- `[NeZero n]`, and the witness `i : Fin n` supplies `0 < n`.
  letI : NeZero n := ⟨Nat.ne_of_gt hn_pos⟩
  rw [Matrix.circulant_apply, Pi.single_apply]
  by_cases h : i = k + j
  · have hsub : i - k = j := by
      have h' : i = j + k := by simpa [add_comm] using h
      simpa using (sub_eq_iff_eq_add.mpr h')
    simp [h, hsub]
  · have hsub : i - k ≠ j := by
      intro hk
      apply h
      simpa [add_comm] using (sub_eq_iff_eq_add.mp hk)
    simp [h, hsub]

/-- Helper for Proposition 5.14: the `k`th column of the circulant basis matrix generated by
`Pi.single j 1` is the standard basis vector at `k + j`. -/
lemma circulantSingle_mulVec_single
    {n : ℕ} (j k : Fin n) :
    Matrix.circulant (Pi.single j (1 : ℝ)) *ᵥ Pi.single k (1 : ℝ) =
      Pi.single (k + j) (1 : ℝ) := by
  -- Expanding the `k`th column of the circulant basis matrix exposes the translated support.
  rw [Matrix.mulVec_single_one]
  ext i
  simpa [Matrix.col, Pi.single_apply] using circulantSingle_apply (j := j) i k

/-- Helper for Proposition 5.14: the `j`th power of the Chapter 5 right-shift matrix is the
circulant basis matrix generated by `Pi.single j 1`. -/
lemma circulantRightShift_pow_eq_circulant_single
    {n : ℕ} (j : Fin n) :
    Matrix.circulantRightShift n ^ (j : ℕ) = Matrix.circulant (Pi.single j (1 : ℝ)) := by
  -- Compare both matrices on the standard basis vectors, where both act by the same cyclic shift.
  apply Matrix.ext_of_mulVec_single
  intro k
  rw [rightShiftPow_mulVec_single, circulantSingle_mulVec_single]
  have hcycle : ((finRotate n)^[j.1]) k = k + j := by
    simpa using congrFun (finCycle_eq_finRotate_iterate (k := j)).symm k
  simpa [hcycle]

/-- Helper for Proposition 5.14: a circulant matrix is the finite linear combination of the
circulant basis matrices `Matrix.circulant (Pi.single j 1)` with the coefficients of its
generating vector. -/
lemma sum_smul_circulant_single_eq_circulant
    {n : ℕ} (c : Fin n → ℝ) :
    ∑ j : Fin n, c j • Matrix.circulant (Pi.single j (1 : ℝ)) = Matrix.circulant c := by
  classical
  -- Pull `Matrix.circulant` through the finite sum, then collapse the standard-basis expansion.
  have hsum :
      ∀ s : Finset (Fin n),
        Finset.sum s (fun j ↦ c j • Matrix.circulant (Pi.single j (1 : ℝ))) =
          Matrix.circulant (Finset.sum s (fun j ↦ c j • (Pi.single j (1 : ℝ)))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [Matrix.circulant_zero]
    | @insert a s ha ih =>
        simp [ha, ih, Matrix.circulant_add, Matrix.circulant_smul]
  calc
    ∑ j : Fin n, c j • Matrix.circulant (Pi.single j (1 : ℝ))
        = Matrix.circulant (∑ j : Fin n, c j • (Pi.single j (1 : ℝ))) := by
            simpa using hsum Finset.univ
    _ = Matrix.circulant c := by
        ext i k
        rw [Matrix.circulant_apply, Matrix.circulant_apply]
        rw [Finset.sum_apply]
        simp [Pi.smul_apply, Pi.single_apply]

/-- Helper for Proposition 5.14: the circulant basis matrices are orthogonal for the Frobenius
inner product, and each has squared Frobenius norm `n`. -/
lemma inner_circulant_single_circulant_single
    {n : ℕ} (j k : Fin n) :
    inner ℝ (Matrix.circulant (Pi.single j (1 : ℝ)))
      (Matrix.circulant (Pi.single k (1 : ℝ))) = if j = k then (n : ℝ) else 0 := by
  -- Expand the Frobenius inner product into a double sum and evaluate the supported entries.
  let A : Matrix (Fin n) (Fin n) ℝ := Matrix.circulant (Pi.single j (1 : ℝ))
  let B : Matrix (Fin n) (Fin n) ℝ := Matrix.circulant (Pi.single k (1 : ℝ))
  suffices hAB : Matrix.Norms.Frobenius.frobeniusInnerReal.inner A B =
      if j = k then (n : ℝ) else 0 by
    simpa [A, B] using hAB
  -- Route correction: compute in the explicit nested `PiLp` model rather than relying on a
  -- reducible instance to unfold automatically.
  change inner ℝ (Matrix.Norms.Frobenius.toFrobeniusVecReal A)
      (Matrix.Norms.Frobenius.toFrobeniusVecReal B) = if j = k then (n : ℝ) else 0
  have hFrob :
      inner ℝ (Matrix.Norms.Frobenius.toFrobeniusVecReal A)
        (Matrix.Norms.Frobenius.toFrobeniusVecReal B) =
      ∑ x : Fin n, ∑ i : Fin n, B x i * A x i := by
    simp [Matrix.Norms.Frobenius.toFrobeniusVecReal, PiLp.inner_apply, PiLp.toLp_apply,
      Real.inner_apply]
  rw [hFrob]
  rw [Finset.sum_comm]
  have hcol :
      ∀ x : Fin n,
        ∑ i : Fin n,
          B i x * A i x = if j = k then (1 : ℝ) else 0 := by
    intro x
    have hn_pos : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ x.1) (Nat.succ_le_of_lt x.is_lt)
    -- Local instance justification (index arithmetic): the `Fin` subtraction lemmas used to
    -- identify the unique supported row require `[NeZero n]`, and the witness `x : Fin n`
    -- supplies `0 < n`.
    letI : NeZero n := ⟨Nat.ne_of_gt hn_pos⟩
    by_cases h : j = k
    · subst h
      calc
        ∑ i : Fin n, B i x * A i x = B (x + j) x * A (x + j) x := by
          refine Finset.sum_eq_single (x + j) ?_ ?_
          · intro i _ hi
            have hix : i - x ≠ j := by
              intro hij
              apply hi
              simpa [add_comm] using (sub_eq_iff_eq_add.mp hij)
            have hAi : A i x = 0 := by
              simp [A, Matrix.circulant_apply, hix]
            simp [hAi]
          · simp
        _ = 1 := by
          have hBx : B (x + j) x = 1 := by
            simpa [B] using circulantSingle_apply (j := j) (i := x + j) (k := x)
          have hAx : A (x + j) x = 1 := by
            simpa [A] using circulantSingle_apply (j := j) (i := x + j) (k := x)
          simp [hBx, hAx]
        _ = if j = j then (1 : ℝ) else 0 := by
          simp
    · have hzero : ∑ i : Fin n, B i x * A i x = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i _
        by_cases hij : i = x + j
        · have hik : i ≠ x + k := by
            intro hik
            apply h
            exact add_left_cancel (hij.symm.trans hik)
          have hix : i - x ≠ k := by
            intro hik'
            apply hik
            simpa [add_comm] using (sub_eq_iff_eq_add.mp hik')
          have hBi : B i x = 0 := by
            simp [B, Matrix.circulant_apply, hix]
          simp [hBi]
        · have hix : i - x ≠ j := by
            intro hij'
            apply hij
            simpa [add_comm] using (sub_eq_iff_eq_add.mp hij')
          have hAi : A i x = 0 := by
            simp [A, Matrix.circulant_apply, hix]
          simp [hAi]
      simpa [h] using hzero
  simp_rw [hcol]
  by_cases h : j = k
  · subst h
    simp
  · simp [h]

/-- Proposition 5.14 (1). A real circulant matrix is the finite linear combination of the
powers of the Chapter 5 right-shift matrix with coefficients given by its generating vector. -/
theorem circulant_eq_sum_rightShift_pow
    {n : ℕ} (c : Fin n → ℝ) :
    Matrix.circulant c = ∑ j : Fin n, c j • (Matrix.circulantRightShift n ^ (j : ℕ)) := by
  -- Rewrite the right-shift powers into the circulant basis and then reassemble the basis sum.
  symm
  calc
    ∑ j : Fin n, c j • (Matrix.circulantRightShift n ^ (j : ℕ))
        = ∑ j : Fin n, c j • Matrix.circulant (Pi.single j (1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [circulantRightShift_pow_eq_circulant_single]
    _ = Matrix.circulant c := sum_smul_circulant_single_eq_circulant c

/-- Proposition 5.14 (2). Under the Frobenius inner product on real `n × n` matrices, the
normalized powers of the Chapter 5 right-shift matrix form an orthonormal family. -/
theorem orthonormal_circulantRightShift_powers
    {n : ℕ} :
    Orthonormal ℝ (fun j : Fin n ↦
      (1 / Real.sqrt (n : ℝ)) •
        ((Matrix.circulantRightShift n : Matrix (Fin n) (Fin n) ℝ) ^ (j : ℕ))) := by
  -- Replace the shift powers by the circulant basis and normalize the resulting delta inner product.
  rw [orthonormal_iff_ite]
  intro j k
  rw [circulantRightShift_pow_eq_circulant_single, circulantRightShift_pow_eq_circulant_single]
  simp_rw [inner_smul_left, inner_smul_right, inner_circulant_single_circulant_single]
  by_cases h : j = k
  · subst k
    have hn_nat : 0 < n := lt_of_lt_of_le (Nat.zero_lt_succ j.1) (Nat.succ_le_of_lt j.is_lt)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.2 hn_pos)
    have hsq : Real.sqrt (n : ℝ) ^ (2 : ℕ) = n := by
      -- The positive cardinality of `Fin n` lets us collapse the normalization scalar explicitly.
      rw [Real.sq_sqrt]
      positivity
    simp
    field_simp [hsqrt]
    simpa using hsq.symm
  · simp [h]

end Matrix
