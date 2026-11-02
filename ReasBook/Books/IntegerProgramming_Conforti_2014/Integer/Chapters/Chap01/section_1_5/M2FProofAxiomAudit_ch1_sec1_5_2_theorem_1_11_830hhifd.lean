module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_38

public section

open scoped Matrix
open Matrix

namespace RationalLinearSystem

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean`: after a column
reindexing exhibits a matrix as a block matrix with a zero tail, its action depends only on
the corresponding head coordinates. -/
private lemma Matrix.mulVec_eq_head_of_reindex_eq_fromCols
    {R ι κ κ₁ κ₂ : Type*}
    [Fintype κ] [Fintype κ₁] [Finite κ₂] [Semiring R]
    (e : κ ≃ κ₁ ⊕ κ₂) (M : Matrix ι κ R) (D : Matrix ι κ₁ R)
    (hblock : Matrix.reindex (Equiv.refl _) e M = Matrix.fromCols D 0)
    (z : κ → R) :
    M *ᵥ z = D *ᵥ (fun i ↦ z (e.symm (Sum.inl i))) := by
  classical
  -- Local instance justification (finite summand): block multiplication needs an enumeration.
  letI : Fintype κ₂ := Fintype.ofFinite κ₂
  -- Pull the vector through the column equivalence before using the block equation.
  have hreindex :=
    Matrix.submatrix_mulVec_equiv M (z ∘ e.symm) (Equiv.refl ι).symm e.symm
  have hcoordinates : (z ∘ e.symm) ∘ e = z := by
    funext j
    exact congrArg z (e.symm_apply_apply j)
  calc
    M *ᵥ z = Matrix.reindex (Equiv.refl _) e M *ᵥ (z ∘ e.symm) := by
      rw [Matrix.reindex_apply, hreindex, Equiv.symm_symm, hcoordinates,
        Equiv.refl_symm]
      rfl
    _ = Matrix.fromCols D 0 *ᵥ (z ∘ e.symm) := by rw [hblock]
    _ = D *ᵥ (fun i ↦ z (e.symm (Sum.inl i))) := by
      simp only [Matrix.fromCols_mulVec, Matrix.zero_mulVec, add_zero]
      rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean`: the head and tail selected
by the standard `Fin` sum equivalence reconstruct the original tuple. -/
private lemma finAppend_splitByEquiv
    {m n r : ℕ} {R : Type*} (h : n = m + r) (z : Fin n → R) :
    (fun j : Fin n ↦
      Fin.append
        (fun i ↦ z (((finCongr h).trans finSumFinEquiv.symm).symm (Sum.inl i)))
        (fun k ↦ z (((finCongr h).trans finSumFinEquiv.symm).symm (Sum.inr k)))
        (j.cast h)) = z := by
  -- Reduce to the canonical `Fin (m + r)` splitting identity.
  subst n
  simpa only [Equiv.trans_refl, Equiv.refl_trans, Equiv.symm_symm,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
    using (Fin.append_castAdd_natAdd (f := z))

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean`: the rational Hermite block
equation acts on an integer vector, after passage to `ℝ`, through the cast leading block. -/
private lemma hnfBlock_mulVec_cast
    (A : Matrix (Fin m) (Fin n) ℚ)
    (hmn : m ≤ n)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hblock :
      Matrix.reindex
          (Equiv.refl _)
          ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
          (A * U.map (Int.castRingHom ℚ)) =
        Matrix.fromCols (D.map (Int.castRingHom ℚ)) 0)
    (z : Fin n → ℤ) :
    (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ ((U *ᵥ z) j : ℝ)) =
      (D.map (Int.castRingHom ℝ)) *ᵥ
        (fun i ↦
          (z
            (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
              (Sum.inl i)) : ℝ)) := by
  -- First use the block presentation over `ℚ` on the cast integer vector.
  have hrat := Matrix.mulVec_eq_head_of_reindex_eq_fromCols
    ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
    (A * U.map (Int.castRingHom ℚ)) (D.map (Int.castRingHom ℚ)) hblock
    (fun j ↦ (z j : ℚ))
  have hcast :=
    congrArg (fun v : Fin m → ℚ ↦ fun i ↦ (v i : ℝ)) hrat
  have hUcast :
      (fun j ↦ ((U *ᵥ z) j : ℝ)) =
        U.map (Int.castRingHom ℝ) *ᵥ (fun j ↦ (z j : ℝ)) := by
    funext j
    exact RingHom.map_mulVec (Int.castRingHom ℝ) U z j
  have hcastInt :
      (Rat.castHom ℝ) ∘ (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    funext a
    exact Rat.cast_intCast a
  have hzcast :
      (Rat.castHom ℝ) ∘ (fun j ↦ (z j : ℚ)) = fun j ↦ (z j : ℝ) := by
    funext j
    exact Rat.cast_intCast (z j)
  have hheadCast :
      (Rat.castHom ℝ) ∘
          (fun i ↦
            (z
              (((finCongr (Nat.add_sub_of_le hmn).symm).trans
                finSumFinEquiv.symm).symm (Sum.inl i)) : ℚ)) =
        fun i ↦
          (z
            (((finCongr (Nat.add_sub_of_le hmn).symm).trans
              finSumFinEquiv.symm).symm (Sum.inl i)) : ℝ) := by
    funext i
    exact Rat.cast_intCast _
  -- Map the rational identity to `ℝ` and normalize both possible casts of integers.
  calc
    (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ ((U *ᵥ z) j : ℝ)) =
        (A.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ)) *ᵥ
          (fun j ↦ (z j : ℝ)) := by
      rw [hUcast, Matrix.mulVec_mulVec]
    _ = (D.map (Int.castRingHom ℝ)) *ᵥ
        (fun i ↦
          (z
            (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
              (Sum.inl i)) : ℝ)) := by
      funext i
      calc
        ((A.map (Rat.castHom ℝ) * U.map (Int.castRingHom ℝ)) *ᵥ
            (fun j ↦ (z j : ℝ))) i =
            ((Rat.castHom ℝ)
              (((A * U.map (Int.castRingHom ℚ)) *ᵥ (fun j ↦ (z j : ℚ))) i)) := by
          rw [RingHom.map_mulVec]
          rw [Matrix.map_mul, Matrix.map_map, hcastInt, hzcast]
        _ = (Rat.castHom ℝ)
            ((D.map (Int.castRingHom ℚ) *ᵥ
              (fun i ↦
                (z
                  (((finCongr (Nat.add_sub_of_le hmn).symm).trans
                    finSumFinEquiv.symm).symm (Sum.inl i)) : ℚ))) i) := congrFun hcast i
        _ = (D.map (Int.castRingHom ℝ) *ᵥ
            (fun i ↦
              (z
                (((finCongr (Nat.add_sub_of_le hmn).symm).trans
                  finSumFinEquiv.symm).symm (Sum.inl i)) : ℝ))) i := by
          rw [RingHom.map_mulVec]
          rw [Matrix.map_map, hcastInt, hheadCast]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean`: an integer solution has
leading transformed coordinates equal to the uniquely determined vector `D⁻¹b`. -/
private lemma inverseMulVec_eq_hnfHead
    (A : Matrix (Fin m) (Fin n) ℚ)
    (hmn : m ≤ n)
    (b : Fin m → ℝ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hD : (D.map (Int.castRingHom ℝ)).det ≠ 0)
    (hblock :
      Matrix.reindex
          (Equiv.refl _)
          ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
          (A * U.map (Int.castRingHom ℚ)) =
        Matrix.fromCols (D.map (Int.castRingHom ℚ)) 0)
    (x : Fin n → ℤ)
    (hx : (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (x j : ℝ)) = b) :
    ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b =
      fun i ↦
        ((U⁻¹ *ᵥ x)
          (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
            (Sum.inl i)) : ℝ) := by
  have hUrecover : U *ᵥ (U⁻¹ *ᵥ x) = x := by
    -- Cancel the unimodular matrix against its nonsingular inverse.
    calc
      U *ᵥ (U⁻¹ *ᵥ x) = (U * U⁻¹) *ᵥ x := Matrix.mulVec_mulVec x U U⁻¹
      _ = x := by rw [U.mul_nonsing_inv hU, Matrix.one_mulVec]
  have hleading :
      (D.map (Int.castRingHom ℝ)) *ᵥ
          (fun i ↦
            ((U⁻¹ *ᵥ x)
              (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                (Sum.inl i)) : ℝ)) = b := by
    -- The block-action identity turns the original equation into its leading square system.
    calc
      (D.map (Int.castRingHom ℝ)) *ᵥ
          (fun i ↦
            ((U⁻¹ *ᵥ x)
              (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                (Sum.inl i)) : ℝ)) =
          (A.map (Rat.castHom ℝ)) *ᵥ
            (fun j ↦ ((U *ᵥ (U⁻¹ *ᵥ x)) j : ℝ)) :=
        (hnfBlock_mulVec_cast A hmn U D hblock (U⁻¹ *ᵥ x)).symm
      _ = (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (x j : ℝ)) := by rw [hUrecover]
      _ = b := hx
  have hDunit : IsUnit (D.map (Int.castRingHom ℝ)).det := isUnit_iff_ne_zero.mpr hD
  -- Left multiplication by the nonsingular inverse now recovers the leading coordinates.
  calc
    ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b =
        ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ
          ((D.map (Int.castRingHom ℝ)) *ᵥ
            (fun i ↦
              ((U⁻¹ *ᵥ x)
                (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                  (Sum.inl i)) : ℝ))) := congrArg _ hleading.symm
    _ = ((D.map (Int.castRingHom ℝ))⁻¹ * D.map (Int.castRingHom ℝ)) *ᵥ
          (fun i ↦
            ((U⁻¹ *ᵥ x)
              (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                (Sum.inl i)) : ℝ)) :=
      Matrix.mulVec_mulVec _ _ _
    _ = fun i ↦
          ((U⁻¹ *ᵥ x)
            (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
              (Sum.inl i)) : ℝ) := by
      rw [(D.map (Int.castRingHom ℝ)).nonsing_inv_mul hDunit, Matrix.one_mulVec]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean`: every choice of integer tail
appended to the integral leading coordinates gives a solution after applying `U`. -/
private lemma hnfParametrization_satisfies
    (A : Matrix (Fin m) (Fin n) ℚ)
    (hmn : m ≤ n)
    (b : Fin m → ℝ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hD : (D.map (Int.castRingHom ℝ)).det ≠ 0)
    (hblock :
      Matrix.reindex
          (Equiv.refl _)
          ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
          (A * U.map (Int.castRingHom ℚ)) =
        Matrix.fromCols (D.map (Int.castRingHom ℚ)) 0)
    (ybar : Fin m → ℤ)
    (hybar : ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b = fun i ↦ (ybar i : ℝ))
    (k : Fin (n - m) → ℤ) :
    (A.map (Rat.castHom ℝ)) *ᵥ
        (fun j ↦
          ((U *ᵥ
            (fun q : Fin n ↦
              Fin.append ybar k (q.cast (Nat.add_sub_of_le hmn).symm))) j : ℝ)) = b := by
  have hDunit : IsUnit (D.map (Int.castRingHom ℝ)).det := isUnit_iff_ne_zero.mpr hD
  have hleading :
      (D.map (Int.castRingHom ℝ)) *ᵥ (fun i ↦ (ybar i : ℝ)) = b := by
    -- Cancel `D` against `D⁻¹` in the prescribed leading-coordinate equation.
    rw [← hybar, Matrix.mulVec_mulVec,
      (D.map (Int.castRingHom ℝ)).mul_nonsing_inv hDunit, Matrix.one_mulVec]
  have hhead :
      (fun i ↦
        ((fun q : Fin n ↦
            Fin.append ybar k (q.cast (Nat.add_sub_of_le hmn).symm))
          (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
            (Sum.inl i)) : ℝ)) =
        fun i ↦ (ybar i : ℝ) := by
    -- The leading coordinates of the appended tuple are exactly `ybar`.
    funext i
    simp
  -- Apply the block-action identity; its tail contribution is zero by construction.
  rw [hnfBlock_mulVec_cast A hmn U D hblock, hhead, hleading]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_theorem_1_11.lean.
Theorem 1.11 (1): under a full-row-rank right-unimodular column-Hermite block presentation of
`A`, the real right-hand side `b` admits an integer solution exactly when the transformed head
coordinates `((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b` are integral. -/
theorem hasIntegerSolution_iff_hnfHeadIntegral
    (A : Matrix (Fin m) (Fin n) ℚ)
    (_hA : A.rank = m)
    (hmn : m ≤ n)
    (b : Fin m → ℝ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det)
    (_hHNF : (A * U.map (Int.castRingHom ℚ)).IsColumnHermiteNormalForm)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hD : (D.map (Int.castRingHom ℝ)).det ≠ 0)
    (hblock :
      Matrix.reindex
          (Equiv.refl _)
          ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
          (A * U.map (Int.castRingHom ℚ)) =
        Matrix.fromCols (D.map (Int.castRingHom ℚ)) 0) :
    (∃ x : Fin n → ℤ, (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (x j : ℝ)) = b) ↔
      ∃ ybar : Fin m → ℤ,
        ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b = fun i ↦ (ybar i : ℝ) := by
  constructor
  · rintro ⟨x, hx⟩
    -- Transform an integer solution by `U⁻¹` and retain its leading coordinates.
    refine ⟨fun i ↦
      (U⁻¹ *ᵥ x)
        (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
          (Sum.inl i)), ?_⟩
    exact inverseMulVec_eq_hnfHead A hmn b U hU D hD hblock x hx
  · rintro ⟨ybar, hybar⟩
    -- Append a zero tail and transport the resulting block solution back through `U`.
    refine ⟨U *ᵥ
      (fun j : Fin n ↦
        Fin.append ybar (fun _ : Fin (n - m) ↦ (0 : ℤ))
          (j.cast (Nat.add_sub_of_le hmn).symm)), ?_⟩
    exact hnfParametrization_satisfies A hmn b U D hD hblock ybar hybar 0

/-- Theorem 1.11 (2): once `ȳ = ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b` is
integral, every integer solution is obtained by appending an arbitrary integer tail and applying
the unimodular change of variables `U`. -/
theorem integerSolutionSet_eq_hnfParametrization
    (A : Matrix (Fin m) (Fin n) ℚ)
    (_hA : A.rank = m)
    (hmn : m ≤ n)
    (b : Fin m → ℝ)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (hU : IsUnit U.det)
    (_hHNF : (A * U.map (Int.castRingHom ℚ)).IsColumnHermiteNormalForm)
    (D : Matrix (Fin m) (Fin m) ℤ)
    (hD : (D.map (Int.castRingHom ℝ)).det ≠ 0)
    (hblock :
      Matrix.reindex
          (Equiv.refl _)
          ((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm)
          (A * U.map (Int.castRingHom ℚ)) =
        Matrix.fromCols (D.map (Int.castRingHom ℚ)) 0)
    (ybar : Fin m → ℤ)
    (hybar : ((D.map (Int.castRingHom ℝ))⁻¹) *ᵥ b = fun i ↦ (ybar i : ℝ)) :
    {x : Fin n → ℤ | (A.map (Rat.castHom ℝ)) *ᵥ (fun j ↦ (x j : ℝ)) = b} =
      Set.range
        (fun k : Fin (n - m) → ℤ ↦
          U *ᵥ
            (fun j : Fin n ↦ Fin.append ybar k (j.cast (Nat.add_sub_of_le hmn).symm))) := by
  ext x
  constructor
  · intro hx
    have hinverse := inverseMulVec_eq_hnfHead A hmn b U hU D hD hblock x hx
    have hheadCast :
        (fun i ↦ (ybar i : ℝ)) =
          fun i ↦
            ((U⁻¹ *ᵥ x)
              (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                (Sum.inl i)) : ℝ) := hybar.symm.trans hinverse
    have hhead :
        ybar = fun i ↦
          (U⁻¹ *ᵥ x)
            (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
              (Sum.inl i)) := by
      -- Injectivity of the integer cast recovers equality of the integral leading coordinates.
      funext i
      exact Int.cast_injective (congrFun hheadCast i)
    have hsplit :
        (fun j : Fin n ↦
          Fin.append ybar
            (fun k ↦
              (U⁻¹ *ᵥ x)
                (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                  (Sum.inr k)))
            (j.cast (Nat.add_sub_of_le hmn).symm)) = U⁻¹ *ᵥ x := by
      -- Reassemble the transformed solution from the recovered head and its original tail.
      rw [hhead]
      exact finAppend_splitByEquiv (Nat.add_sub_of_le hmn).symm (U⁻¹ *ᵥ x)
    refine ⟨fun k ↦
      (U⁻¹ *ᵥ x)
        (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
          (Sum.inr k)), ?_⟩
    -- Applying `U` to the reconstructed tuple cancels `U⁻¹` and returns `x`.
    calc
      U *ᵥ
          (fun j : Fin n ↦
            Fin.append ybar
              (fun k ↦
                (U⁻¹ *ᵥ x)
                  (((finCongr (Nat.add_sub_of_le hmn).symm).trans finSumFinEquiv.symm).symm
                    (Sum.inr k)))
              (j.cast (Nat.add_sub_of_le hmn).symm)) = U *ᵥ (U⁻¹ *ᵥ x) :=
        congrArg (fun z ↦ U *ᵥ z) hsplit
      _ = (U * U⁻¹) *ᵥ x := Matrix.mulVec_mulVec x U U⁻¹
      _ = x := by rw [U.mul_nonsing_inv hU, Matrix.one_mulVec]
  · rintro ⟨k, rfl⟩
    -- The shared block computation proves that every parameter value is a solution.
    exact hnfParametrization_satisfies A hmn b U D hD hblock ybar hybar k

#print axioms hasIntegerSolution_iff_hnfHeadIntegral
#print axioms integerSolutionSet_eq_hnfParametrization

end RationalLinearSystem

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_60d9ca44132dd8f5e0fc"
#print axioms _root_.RationalLinearSystem.hasIntegerSolution_iff_hnfHeadIntegral
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_60d9ca44132dd8f5e0fc"
