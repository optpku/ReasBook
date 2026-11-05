/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Algebra.EuclideanDomain.Int

@[expose] public section

open scoped Matrix
open Module

namespace Matrix

section Theorem121

variable {n : ℕ}

/-- A Smith normal diagonal has positive entries and each entry divides the next one. -/
def IsSmithNormalDiagonal (d : Fin n → ℤ) : Prop :=
  (∀ i : Fin n, 0 < d i) ∧
    ∀ i : Fin (n - 1),
      d (i.castLT (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))) ∣
        d (i.succ.castLT
          (Nat.lt_of_lt_of_le i.succ.isLt
            (le_of_eq
              (Nat.sub_add_cancel
                (Nat.succ_le_of_lt
                  (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt i.isLt) (Nat.sub_le n 1)))))))

/-- The defining conditions for a Smith normal diagonal. -/
theorem isSmithNormalDiagonal_iff (d : Fin n → ℤ) :
    IsSmithNormalDiagonal d ↔
      (∀ i : Fin n, 0 < d i) ∧
        ∀ i : Fin (n - 1),
          d (i.castLT (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))) ∣
            d (i.succ.castLT
              (Nat.lt_of_lt_of_le i.succ.isLt
                (le_of_eq
                  (Nat.sub_add_cancel
                    (Nat.succ_le_of_lt
                      (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt i.isLt) (Nat.sub_le n 1))))))) := by
  -- Unfolding the predicate exposes precisely the two defining conditions.
  rfl

/-- Positivity of the diagonal entries in a Smith normal diagonal. -/
theorem IsSmithNormalDiagonal.pos {d : Fin n → ℤ} (hd : IsSmithNormalDiagonal d) (i : Fin n) :
    0 < d i := by
  -- The first component of the defining conjunction is entrywise positivity.
  exact hd.1 i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: every entry of a Smith normal
diagonal is nonzero. -/
lemma IsSmithNormalDiagonal.ne_zero {d : Fin n → ℤ} (hd : IsSmithNormalDiagonal d)
    (i : Fin n) : d i ≠ 0 := by
  -- Strict positivity rules out a zero diagonal entry.
  exact ne_of_gt (hd.pos i)

/-- Consecutive divisibility in a Smith normal diagonal. -/
theorem IsSmithNormalDiagonal.dvd_next
    {d : Fin n → ℤ} (hd : IsSmithNormalDiagonal d) (i : Fin (n - 1)) :
    d (i.castLT (Nat.lt_of_lt_of_le i.isLt (Nat.sub_le n 1))) ∣
      d (i.succ.castLT
        (Nat.lt_of_lt_of_le i.succ.isLt
          (le_of_eq
            (Nat.sub_add_cancel
              (Nat.succ_le_of_lt
                (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt i.isLt) (Nat.sub_le n 1))))))) := by
  -- The second component of the defining conjunction is consecutive divisibility.
  exact hd.2 i

end Theorem121

end Matrix

end

/- TEMPORARY TIMEOUT BISECTION

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: a nonsingular integer
matrix is diagonal between suitable bases, with every diagonal coefficient positive. -/
lemma existsPositiveDiagonalBases
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    ∃ bM bD : Basis (Fin n) ℤ (Fin n → ℤ), ∃ d : Fin n → ℤ,
      (∀ i, 0 < d i) ∧ ∀ i, A.toLin' (bD i) = d i • bM i := by
  classical
  -- Nonsingularity makes the associated endomorphism injective.
  have hinj : Function.Injective A.toLin' := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply A.eq_zero_of_mulVec_eq_zero hA
    rw [mulVec_sub, sub_eq_zero]
    simpa only [Matrix.toLin'_apply] using hxy
  -- Apply mathlib's full-rank PID diagonalization to the range of the endomorphism.
  have hrank : Module.finrank ℤ (LinearMap.range A.toLin') =
      Module.finrank ℤ (Fin n → ℤ) :=
    LinearMap.finrank_range_of_inj hinj
  obtain ⟨bM, a, bN, hdiag⟩ :=
    (LinearMap.range A.toLin').exists_smith_normal_form_of_rank_eq
      (Pi.basisFun ℤ (Fin n)) hrank
  have ha : ∀ i, a i ≠ 0 := by
    intro i hai
    apply Basis.ne_zero bN i
    apply Subtype.ext
    simpa only [hai, zero_smul] using hdiag i
  choose u hu habs using fun i ↦ Int.exists_unit_of_abs (a i)
  let e := LinearEquiv.ofInjective A.toLin' hinj
  let bN' := Basis.unitsSMul bN (fun i ↦ (hu i).unit)
  let bD := bN'.map e.symm
  refine ⟨bM, bD, fun i ↦ (a i).natAbs, ?_, ?_⟩
  · -- Absolute values of the nonzero coefficients are positive.
    intro i
    exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr (ha i))
  · -- Rescaling the range basis by the chosen signs normalizes every coefficient.
    intro i
    calc
      A.toLin' (bD i) = ((bN' i : LinearMap.range A.toLin') : Fin n → ℤ) := by
        exact congrArg Subtype.val (e.apply_symm_apply (bN' i))
      _ = ((hu i).unit : ℤ) • (bN i : Fin n → ℤ) := by
        rw [Basis.unitsSMul_apply]
        rfl
      _ = ((a i).natAbs : ℤ) • bM i := by
        rw [hdiag i, smul_smul, (hu i).unit_spec, ← habs]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the positive basis
diagonalization gives unimodular left and right change-of-basis matrices. -/
lemma existsPositiveDiagonalEquivalence
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    ∃ R C : Matrix (Fin n) (Fin n) ℤ, ∃ d : Fin n → ℤ,
      IsUnit R.det ∧ IsUnit C.det ∧ (∀ i, 0 < d i) ∧
        R * A * C = Matrix.diagonal d := by
  classical
  -- Use the positive diagonal bases and express both basis changes as matrices.
  obtain ⟨bM, bD, d, hd, hbasis⟩ := existsPositiveDiagonalBases A hA
  let std := Pi.basisFun ℤ (Fin n)
  let R := bM.toMatrix std
  let C := std.toMatrix bD
  refine ⟨R, C, d, ?_, ?_, hd, ?_⟩
  · -- The reverse change-of-basis matrix is a right inverse of `R`.
    exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip bM std)
  · -- The reverse change-of-basis matrix is a right inverse of `C`.
    exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip std bD)
  · -- The basis-change formula reduces the matrix identity to the diagonal basis relation.
    calc
      R * A * C = LinearMap.toMatrix bD bM A.toLin' := by
        simpa only [R, C, std, LinearMap.toMatrix_eq_toMatrix',
          LinearMap.toMatrix'_toLin'] using
            (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
              bD std bM std A.toLin')
      _ = Matrix.diagonal d := by
        ext i j
        rw [LinearMap.toMatrix_apply, hbasis j]
        simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
          Matrix.diagonal_apply, Finsupp.single_apply]
        by_cases hij : i = j
        · subst j
          rfl
        · simp only [hij, Ne.symm hij, ↓reduceIte]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the coefficient ideal of a
linear map is generated by all scalar evaluations of its values by linear functionals. -/
def coefficientIdeal {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) : Ideal R :=
  Ideal.span {r | ∃ (x : M) (φ : Module.Dual R N), φ (f x) = r}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: every scalar coefficient of
a linear map belongs to its coefficient ideal. -/
lemma coefficient_mem_coefficientIdeal {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (x : M)
    (φ : Module.Dual R N) : φ (f x) ∈ coefficientIdeal f := by
  -- Insert the displayed evaluation among the generators of the ideal.
  exact Ideal.subset_span ⟨x, φ, rfl⟩

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: precomposition by a linear
equivalence does not change the coefficient ideal. -/
lemma coefficientIdeal_comp_equiv {R M M' N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (e : M' ≃ₗ[R] M) :
    coefficientIdeal (f.comp e.toLinearMap) = coefficientIdeal f := by
  -- Surjectivity of `e` identifies the two generating sets.
  apply le_antisymm
  · rw [coefficientIdeal, Ideal.span_le]
    rintro r ⟨x, φ, rfl⟩
    exact coefficient_mem_coefficientIdeal f (e x) φ
  · rw [coefficientIdeal, Ideal.span_le]
    rintro r ⟨x, φ, rfl⟩
    have hmem := coefficient_mem_coefficientIdeal (f.comp e.toLinearMap) (e.symm x) φ
    have hx : e.toLinearMap (e.symm x) = x := e.apply_symm_apply x
    rw [LinearMap.comp_apply, hx] at hmem
    exact hmem

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: postcomposition by a linear
equivalence does not change the coefficient ideal. -/
lemma coefficientIdeal_equiv_comp {R M N N' : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (e : N ≃ₗ[R] N') (f : M →ₗ[R] N) :
    coefficientIdeal (e.toLinearMap.comp f) = coefficientIdeal f := by
  -- Pull functionals backward and forward through the equivalence.
  apply le_antisymm
  · rw [coefficientIdeal, Ideal.span_le]
    rintro r ⟨x, φ, rfl⟩
    exact coefficient_mem_coefficientIdeal f x (φ.comp e.toLinearMap)
  · rw [coefficientIdeal, Ideal.span_le]
    rintro r ⟨x, φ, rfl⟩
    have hmem := coefficient_mem_coefficientIdeal (e.toLinearMap.comp f) x
      (φ.comp e.symm.toLinearMap)
    have hx : φ (e.symm.toLinearMap (e.toLinearMap (f x))) = φ (f x) :=
      congrArg φ (e.symm_apply_apply (f x))
    rw [← hx]
    exact hmem

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the coefficient ideal of an
operator diagonal in a basis is generated by its diagonal coefficients. -/
lemma coefficientIdeal_eq_span_range_of_diagonal
    {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Basis ι R M) (f : M →ₗ[R] M) (d : ι → R)
    (hdiag : ∀ i, f (b i) = d i • b i) :
    coefficientIdeal f = Ideal.span (Set.range d) := by
  apply le_antisymm
  · -- Every evaluation is a linear combination of the displayed diagonal coefficients.
    rw [coefficientIdeal, Ideal.span_le]
    rintro r ⟨x, φ, rfl⟩
    let S : Submodule R M :=
      Submodule.comap (φ.comp f) (Ideal.span (Set.range d))
    have hS : S = ⊤ := by
      refine top_unique ?_
      rw [← b.span_eq]
      refine Submodule.span_le.mpr ?_
      rintro y ⟨i, rfl⟩
      change (φ.comp f) (b i) ∈ Ideal.span (Set.range d)
      rw [LinearMap.comp_apply]
      change φ (f (b i)) ∈ Ideal.span (Set.range d)
      rw [hdiag i, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))
    have hx : x ∈ S := by
      rw [hS]
      exact Submodule.mem_top
    simpa only [S, Submodule.mem_comap] using hx
  · -- Each diagonal coefficient is obtained using the matching basis coordinate.
    rw [Ideal.span_le]
    rintro r ⟨i, rfl⟩
    have hmem := coefficient_mem_coefficientIdeal f (b i) (b.coord i)
    rw [hdiag i, map_smul, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same, smul_eq_mul, mul_one] at hmem
    exact hmem

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: an equivalence induces a
bijective map on every exterior power. -/
lemma exteriorPowerMap_bijectiveOfEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (k : ℕ) (e : M ≃ₗ[R] N) :
    Function.Bijective (exteriorPower.map k e.toLinearMap) := by
  constructor
  · -- The exterior map of the inverse is a retraction.
    apply exteriorPower.map_injective (n := k) (f := e.toLinearMap)
      e.symm.toLinearMap
    ext x
    exact e.symm_apply_apply x
  · -- Exterior powers preserve surjective linear maps.
    exact exteriorPower.map_surjective e.surjective

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the exterior-power map of a
linear equivalence, bundled again as a linear equivalence. -/
noncomputable def exteriorPowerLinearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (k : ℕ) (e : M ≃ₗ[R] N) :
    ⋀[R]^k M ≃ₗ[R] ⋀[R]^k N :=
  LinearEquiv.ofBijective (exteriorPower.map k e.toLinearMap)
    (exteriorPowerMap_bijectiveOfEquiv k e)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the bundled exterior-power
equivalence has the canonical exterior map as its underlying linear map. -/
lemma exteriorPowerLinearEquiv_toLinearMap
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (k : ℕ) (e : M ≃ₗ[R] N) :
    (exteriorPowerLinearEquiv k e).toLinearMap = exteriorPower.map k e.toLinearMap := by
  -- This is the defining projection of `LinearEquiv.ofBijective`.
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the `k`th determinantal ideal
is the coefficient ideal of the induced map on `k`th exterior powers. -/
noncomputable def determinantalIdeal (k : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℤ) : Ideal ℤ :=
  coefficientIdeal (exteriorPower.map k A.toLin')

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: unimodular left and right
multiplication preserves every determinantal ideal. -/
lemma determinantalIdeal_mul_eq (k : ℕ) {m : ℕ}
    (A P Q : Matrix (Fin m) (Fin m) ℤ)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det) :
    determinantalIdeal k (P * A * Q) = determinantalIdeal k A := by
  classical
  let std := Pi.basisFun ℤ (Fin m)
  let eP := P.toLinearEquiv std hP
  let eQ := Q.toLinearEquiv std hQ
  let EP := exteriorPowerLinearEquiv k eP
  let EQ := exteriorPowerLinearEquiv k eQ
  -- Functoriality turns matrix multiplication into composition on exterior powers.
  have hmap : exteriorPower.map k (P * A * Q).toLin' =
      EP.toLinearMap.comp ((exteriorPower.map k A.toLin').comp EQ.toLinearMap) := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, exteriorPower.map_comp,
      exteriorPower.map_comp]
    rfl
  rw [determinantalIdeal, hmap, coefficientIdeal_equiv_comp,
    coefficientIdeal_comp_equiv]
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: on the exterior-power basis,
a diagonal endomorphism has eigenvalue equal to the product over the chosen subset. -/
lemma exteriorPowerMap_diagonal_apply_basis (k : ℕ) {m : ℕ}
    (d : Fin m → ℤ) (s : Set.powersetCard (Fin m) k) :
    exteriorPower.map k (Matrix.diagonal d).toLin'
        ((Pi.basisFun ℤ (Fin m)).exteriorPower k s) =
      (∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i)) •
        (Pi.basisFun ℤ (Fin m)).exteriorPower k s := by
  -- Evaluate the exterior map on a wedge of standard basis vectors.
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.ιMulti_family, exteriorPower.ιMulti_family]
  have hpoint :
      ((Matrix.diagonal d).toLin' ∘ Pi.basisFun ℤ (Fin m)) ∘
          Set.powersetCard.ofFinEmbEquiv.symm s =
        fun i ↦ d (Set.powersetCard.ofFinEmbEquiv.symm s i) •
          Pi.basisFun ℤ (Fin m) (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
    funext i
    ext j
    simp only [Function.comp_apply, Matrix.toLin'_apply, Pi.basisFun_apply,
      Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hji : j = Set.powersetCard.ofFinEmbEquiv.symm s i
    · subst j
      rfl
    · simp only [Pi.single_apply, hji, ↓reduceIte, mul_zero]
  rw [hpoint, AlternatingMap.map_smul_univ]
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the determinantal ideal of a
diagonal matrix is generated by the products over all subsets of the prescribed size. -/
lemma determinantalIdeal_diagonal_eq_span_products (k : ℕ) {m : ℕ}
    (d : Fin m → ℤ) :
    determinantalIdeal k (Matrix.diagonal d) =
      Ideal.span (Set.range fun s : Set.powersetCard (Fin m) k ↦
        ∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i)) := by
  -- Apply the general coefficient-ideal computation to the exterior-power basis.
  exact coefficientIdeal_eq_span_range_of_diagonal
    ((Pi.basisFun ℤ (Fin m)).exteriorPower k)
    (exteriorPower.map k (Matrix.diagonal d).toLin')
    (fun s : Set.powersetCard (Fin m) k ↦
      ∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i))
    (exteriorPowerMap_diagonal_apply_basis k d)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: consecutive divisibility in a
Smith diagonal extends to every ordered pair of indices. -/
lemma IsSmithNormalDiagonal.dvd_of_le {d : Fin n → ℤ}
    (hd : IsSmithNormalDiagonal d) {i j : Fin n} (hij : i ≤ j) : d i ∣ d j := by
  -- Induct along the finite interval from `i` to `j`.
  have hstep : ∀ k (hik : i.val ≤ k) (hkn : k < n), d i ∣ d ⟨k, hkn⟩ := by
    intro k hik
    induction k, hik using Nat.le_induction with
    | base =>
        intro hi
        have hval : i.val = (⟨i.val, hi⟩ : Fin n).val := rfl
        have hentry : d i = d ⟨i.val, hi⟩ := congrArg d (Fin.ext hval)
        rw [← hentry]
    | succ k hik ih =>
        intro hsucc
        have hk : k < n := Nat.lt_trans (Nat.lt_succ_self k) hsucc
        have hpred : k < n - 1 := by omega
        let p : Fin (n - 1) := ⟨k, hpred⟩
        have hadj := hd.dvd_next p
        have hfirstVal :
            (p.castLT (Nat.lt_of_lt_of_le p.isLt (Nat.sub_le n 1))).val =
              (⟨k, hk⟩ : Fin n).val := rfl
        have hfirst :
            p.castLT (Nat.lt_of_lt_of_le p.isLt (Nat.sub_le n 1)) =
              (⟨k, hk⟩ : Fin n) := Fin.ext hfirstVal
        have hsecondVal :
            (p.succ.castLT
              (Nat.lt_of_lt_of_le p.succ.isLt
                (le_of_eq
                  (Nat.sub_add_cancel
                    (Nat.succ_le_of_lt
                      (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt p.isLt)
                        (Nat.sub_le n 1))))))).val =
              (⟨k + 1, hsucc⟩ : Fin n).val := rfl
        have hsecond :
            p.succ.castLT
              (Nat.lt_of_lt_of_le p.succ.isLt
                (le_of_eq
                  (Nat.sub_add_cancel
                    (Nat.succ_le_of_lt
                      (Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt p.isLt)
                        (Nat.sub_le n 1)))))) =
              (⟨k + 1, hsucc⟩ : Fin n) := Fin.ext hsecondVal
        rw [hfirst, hsecond] at hadj
        exact (ih hk).trans hadj
  have hval : j.val = (⟨j.val, j.isLt⟩ : Fin n).val := rfl
  have hentry : d j = d ⟨j.val, j.isLt⟩ := congrArg d (Fin.ext hval)
  rw [hentry]
  exact hstep j.val hij j.isLt

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: an order embedding between
finite initial segments sends every index to an index at least as large. -/
lemma finOrderEmbedding_index_le {k m : ℕ} (f : Fin k ↪o Fin m) (i : Fin k) :
    i.val ≤ (f i).val := by
  -- Strict monotonicity raises the value by at least one at every successor.
  cases k with
  | zero => exact Fin.elim0 i
  | succ k =>
      induction i using Fin.induction with
      | zero => exact Nat.zero_le _
      | succ i ih =>
          have hmono := f.strictMono i.castSucc_lt_succ
          simpa only [Fin.val_succ] using Nat.succ_le_of_lt (lt_of_le_of_lt ih hmono)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the first `k` Smith entries'
product divides the product over every `k`-element subset. -/
lemma IsSmithNormalDiagonal.prefixProduct_dvd_subsetProduct
    {d : Fin n → ℤ} (hd : IsSmithNormalDiagonal d) {k : ℕ} (hk : k ≤ n)
    (s : Set.powersetCard (Fin n) k) :
    (∏ i : Fin k, d (Fin.castLE hk i)) ∣
      ∏ i : Fin k, d (Set.powersetCard.ofFinEmbEquiv.symm s i) := by
  -- Compare corresponding factors using the monotone enumeration of the subset.
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply hd.dvd_of_le
  exact finOrderEmbedding_index_le (Set.powersetCard.ofFinEmbEquiv.symm s) i

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: for a Smith diagonal, the
`k`th determinantal ideal is generated by the product of its first `k` entries. -/
lemma determinantalIdeal_diagonal_eq_span_prefixProduct
    {d : Fin n → ℤ} (hd : IsSmithNormalDiagonal d) {k : ℕ} (hk : k ≤ n) :
    determinantalIdeal k (Matrix.diagonal d) =
      Ideal.span {∏ i : Fin k, d (Fin.castLE hk i)} := by
  rw [determinantalIdeal_diagonal_eq_span_products]
  apply le_antisymm
  · -- The prefix product divides every generator indexed by a `k`-subset.
    rw [Ideal.span_le]
    rintro z ⟨s, rfl⟩
    exact Ideal.mem_span_singleton.mpr (hd.prefixProduct_dvd_subsetProduct hk s)
  · -- The initial `k`-subset realizes the prefix product itself.
    rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    let s : Set.powersetCard (Fin n) k :=
      Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hk)
    apply Ideal.subset_span
    refine ⟨s, ?_⟩
    dsimp only [s]
    rw [Equiv.symm_apply_apply]
    apply Finset.prod_congr rfl
    intro i hi
    rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: equality of all determinantal
ideals of two Smith diagonals gives equality of all positive prefix products. -/
lemma smithPrefixProduct_eq_of_determinantalIdeal_eq
    {d d' : Fin n → ℤ} (hd : IsSmithNormalDiagonal d)
    (hd' : IsSmithNormalDiagonal d')
    (hideal : ∀ k, k ≤ n →
      determinantalIdeal k (Matrix.diagonal d) =
        determinantalIdeal k (Matrix.diagonal d'))
    (k : ℕ) (hk : k ≤ n) :
    (∏ i : Fin k, d' (Fin.castLE hk i)) =
      ∏ i : Fin k, d (Fin.castLE hk i) := by
  -- Principal generators are associated, and positivity removes the unit ambiguity.
  have hassoc : Associated
      (∏ i : Fin k, d (Fin.castLE hk i))
      (∏ i : Fin k, d' (Fin.castLE hk i)) := by
    apply Ideal.span_singleton_eq_span_singleton.mp
    rw [← determinantalIdeal_diagonal_eq_span_prefixProduct hd hk,
      ← determinantalIdeal_diagonal_eq_span_prefixProduct hd' hk]
    exact hideal k hk
  have hpos : 0 < ∏ i : Fin k, d (Fin.castLE hk i) := by
    exact Finset.prod_pos fun i hi ↦ hd.pos _
  have hpos' : 0 < ∏ i : Fin k, d' (Fin.castLE hk i) := by
    exact Finset.prod_pos fun i hi ↦ hd'.pos _
  exact (Int.eq_of_associated_of_nonneg hassoc hpos.le hpos'.le).symm

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: extending a prefix by one
index multiplies its product by the new final entry. -/
lemma prefixProduct_succ (d : Fin n → ℤ) (i : Fin n)
    (hk : i.val ≤ n) (hks : i.val + 1 ≤ n) :
    (∏ j : Fin (i.val + 1), d (Fin.castLE hks j)) =
      (∏ j : Fin i.val, d (Fin.castLE hk j)) * d i := by
  rw [Fin.prod_univ_castSucc]
  have hprefix :
      (∏ j : Fin i.val, d (Fin.castLE hks j.castSucc)) =
        ∏ j : Fin i.val, d (Fin.castLE hk j) := by
    apply Finset.prod_congr rfl
    intro j hj
    have hval : (Fin.castLE hks j.castSucc).val = (Fin.castLE hk j).val := rfl
    exact congrArg d (Fin.ext hval)
  have hlastVal : (Fin.castLE hks (Fin.last i.val)).val = i.val := rfl
  have hlast : d (Fin.castLE hks (Fin.last i.val)) = d i :=
    congrArg d (Fin.ext hlastVal)
  rw [hprefix, hlast]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: equal prefix products of two
positive finite sequences imply pointwise equality. -/
lemma eq_of_positive_prefixProducts_eq
    {d d' : Fin n → ℤ} (hd' : ∀ i, 0 < d' i)
    (hp : ∀ k (hk : k ≤ n),
      (∏ i : Fin k, d' (Fin.castLE hk i)) =
        ∏ i : Fin k, d (Fin.castLE hk i)) : d' = d := by
  funext i
  -- Compare the prefixes ending immediately before and at `i`, then cancel the former.
  have hk : i.val ≤ n := (Nat.le_of_lt i.isLt)
  have hks : i.val + 1 ≤ n := i.isLt
  have hp0 := hp i.val hk
  have hp1 := hp (i.val + 1) hks
  rw [prefixProduct_succ d' i hk hks, prefixProduct_succ d i hk hks] at hp1
  have hprefixNe : (∏ j : Fin i.val, d' (Fin.castLE hk j)) ≠ 0 := by
    exact ne_of_gt (Finset.prod_pos fun j hj ↦ hd' _)
  rw [hp0] at hp1 hprefixNe
  exact mul_left_cancel₀ hprefixNe hp1

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: a maximal PID pivot divides
every coordinate of an element in the residual kernel. -/
lemma Submodule.generator_maximal_submoduleImage_dvd_of_mem_ker
    {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {N O : Submodule R M} (hNO : N ≤ O)
    {ϕ : O →ₗ[R] R}
    (hϕ : ∀ ψ : O →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    (y : M) (yN : y ∈ N)
    (hϕy : ϕ ⟨y, hNO yN⟩ = Submodule.IsPrincipal.generator (ϕ.submoduleImage N))
    (z : M) (zN : z ∈ N) (hϕz : ϕ ⟨z, hNO zN⟩ = 0)
    (ψ : O →ₗ[R] R) :
    Submodule.IsPrincipal.generator (ϕ.submoduleImage N) ∣ ψ ⟨z, hNO zN⟩ := by
  -- Compare the maximal-pivot divisibilities for `y` and `y + z`.
  have hy := generator_maximal_submoduleImage_dvd hNO hϕ y yN hϕy ψ
  have hyz := generator_maximal_submoduleImage_dvd hNO hϕ (y + z) (N.add_mem yN zN) ?_ ψ
  · obtain ⟨c, hc⟩ := hy
    obtain ⟨c', hc'⟩ := hyz
    have hψadd : ψ ⟨y + z, hNO (N.add_mem yN zN)⟩ =
        ψ ⟨y, hNO yN⟩ + ψ ⟨z, hNO zN⟩ :=
      ψ.map_add ⟨y, hNO yN⟩ ⟨z, hNO zN⟩
    refine ⟨c' - c, ?_⟩
    calc
      ψ ⟨z, hNO zN⟩ = ψ ⟨y + z, hNO (N.add_mem yN zN)⟩ - ψ ⟨y, hNO yN⟩ := by
        rw [hψadd, add_sub_cancel_left]
      _ = Submodule.IsPrincipal.generator (ϕ.submoduleImage N) * c' -
          Submodule.IsPrincipal.generator (ϕ.submoduleImage N) * c := by rw [hc', hc]
      _ = Submodule.IsPrincipal.generator (ϕ.submoduleImage N) * (c' - c) := by
        rw [mul_sub]
  · -- The residual summand is killed by the maximal functional.
    calc
      ϕ ⟨y + z, hNO (N.add_mem yN zN)⟩ =
          ϕ ⟨y, hNO yN⟩ + ϕ ⟨z, hNO zN⟩ :=
        ϕ.map_add ⟨y, hNO yN⟩ ⟨z, hNO zN⟩
      _ = Submodule.IsPrincipal.generator (ϕ.submoduleImage N) := by
        rw [hϕy, hϕz, add_zero]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: the maximal-pivot basis
extension over a PID also records that its head coefficient divides every tail coefficient. -/
theorem Submodule.basis_of_pid_aux_ordered
    {R ι O : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [Finite ι] [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Basis ι R M) (N_bot : N ≠ ⊥) (N_le_M : N ≤ M) :
    ∃ y ∈ M, ∃ a : R, a • y ∈ N ∧ ∃ M' ≤ M, ∃ N' ≤ N,
      N' ≤ M' ∧ (∀ (c : R) (z : O), z ∈ M' → c • y + z = 0 → c = 0) ∧
      (∀ (c : R) (z : O), z ∈ N' → c • a • y + z = 0 → c = 0) ∧
      ∀ (n') (bN' : Basis (Fin n') R N'),
        ∃ bN : Basis (Fin (n' + 1)) R N,
          ∀ (m') (hn'm' : n' ≤ m') (bM' : Basis (Fin m') R M'),
            ∃ (hnm : n' + 1 ≤ m' + 1) (bM : Basis (Fin (m' + 1)) R M),
              ∀ as : Fin n' → R,
                (∀ i : Fin n', (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)) →
                  (∀ i : Fin (n' + 1),
                    (bN i : O) = (Fin.cons (α := fun _ ↦ R) a as) i •
                      (bM (Fin.castLE hnm i) : O)) ∧
                  ∀ i : Fin n', a ∣ as i := by
  -- Choose a coordinate functional whose image of `N` is maximal.
  have hmax : ∃ ϕ : M →ₗ[R] R,
      ∀ ψ : M →ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M →ₗ[R] R ↦ ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ ↦ P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := hmax.choose
  have ϕ_max := hmax.choose_spec
  let a := Submodule.IsPrincipal.generator (ϕ.submoduleImage N)
  have a_mem : a ∈ ϕ.submoduleImage N := Submodule.IsPrincipal.generator_mem _
  by_cases a_zero : a = 0
  · have hbot := eq_bot_of_generator_maximal_submoduleImage_eq_zero
      b'M N_le_M ϕ_max a_zero
    contradiction
  -- Lift the generator to `N`, and divide all of its coordinates by the generator.
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  have hdvd : ∀ i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i ↦
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  cases nonempty_fintype ι
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' ∈ M := M.sum_mem fun i _ ↦ M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [map_sum, map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp
      (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y, N_le_M yN⟩, mk_y', Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_smul, ← hc]
    rfl
  refine ⟨y', y'M, a, a_smul_y'.symm ▸ yN, ?_⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', M.smul_mem a y'M⟩ :=
          (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm)
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ ≠ 0 := by
    simpa only [ϕy'_eq] using one_ne_zero
  -- Split off the pivot direction and recurse on the two residual kernels.
  let M' : Submodule R O := (LinearMap.ker ϕ).map M.subtype
  let N' : Submodule R O :=
    (LinearMap.ker (ϕ.comp (Submodule.inclusion N_le_M))).map N.subtype
  have M'_le_M : M' ≤ M := M.map_subtype_le (LinearMap.ker ϕ)
  have N'_le_M' : N' ≤ M' := by
    intro x hx
    simp only [N', Submodule.mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' ≤ N :=
    N.map_subtype_le (LinearMap.ker (ϕ.comp (Submodule.inclusion N_le_M)))
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', ?_⟩
  have y'_ortho_M' : ∀ (c : R), ∀ z ∈ M', c • y' + z = 0 → c = 0 := by
    intro c x xM' hcx
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by
      exact @Subtype.coe_injective O (· ∈ M) _ _ hcx
    simpa only [map_add, map_zero, map_smul, smul_eq_mul, add_zero, mul_eq_zero,
      ϕy'_ne_zero, hx', or_false] using congrArg ϕ hc'
  have ay'_ortho_N' : ∀ (c : R), ∀ z ∈ N', c • a • y' + z = 0 → c = 0 := by
    intro c z zN' hcz
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') ?_)).resolve_left a_zero
    rw [mul_comm, mul_smul, hcz]
  refine ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' ↦ ?_⟩
  -- Extend the residual basis of `N'` by the pivot vector.
  let bN : Basis (Fin (n' + 1)) R N :=
    Basis.mkFinConsOfLE y yN bN' N'_le_N
      (fun c z zN' hcz ↦ ay'_ortho_N' c z zN' (a_smul_y' ▸ hcz))
      (fun z zN ↦ by
        obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ :=
          Submodule.IsPrincipal.generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
        refine ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, ?_, ?_⟩⟩
        · refine LinearMap.mem_ker.mpr ?_
          have hincl : Submodule.inclusion N_le_M
              ⟨z - b • y, N.sub_mem zN (N.smul_mem b yN)⟩ =
              ⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩ := Subtype.ext rfl
          rw [LinearMap.comp_apply, hincl, map_sub, map_smul, hb, ϕy_eq,
            smul_eq_mul, mul_comm, sub_self]
        · simp only [sub_eq_add_neg, neg_smul, Submodule.coe_subtype])
  refine ⟨bN, ?_⟩
  intro m' hn'm' bM'
  let bM : Basis (Fin (m' + 1)) R M :=
    Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M'
      (fun z zM ↦ by
        refine ⟨-ϕ ⟨z, zM⟩,
          ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr ?_, ?_⟩⟩
        · rw [map_sub, map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
        · rw [map_sub, map_smul, sub_eq_add_neg, neg_smul]
          rfl)
  refine ⟨Nat.succ_le_succ hn'm', bM, ?_⟩
  intro as has
  constructor
  · -- The extended bases retain the diagonal relation.
    intro i
    simp only [bN, bM, Basis.coe_mkFinConsOfLE]
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [Fin.cons_zero, Fin.castLE_zero]
      exact a_smul_y'.symm
    · rw [Fin.castLE_succ]
      simp only [Fin.cons_succ, Function.comp_apply, Submodule.coe_inclusion, has j]
  · -- Evaluate residual basis vectors in the new ambient coordinates.
    intro i
    have ziN : (bN' i : O) ∈ N := N'_le_N (bN' i).property
    have hϕzi : ϕ ⟨(bN' i : O), N_le_M ziN⟩ = 0 := by
      obtain ⟨⟨z, zN⟩, hzker, hz⟩ := Submodule.mem_map.mp (bN' i).property
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hzker
      have hzM : (⟨z, N_le_M zN⟩ : M) =
          ⟨(bN' i : O), N_le_M ziN⟩ := Subtype.ext hz
      rwa [← hzM]
    let j : Fin (m' + 1) := (Fin.castLE hn'm' i).succ
    have hdvdCoord := generator_maximal_submoduleImage_dvd_of_mem_ker
      N_le_M ϕ_max y yN ϕy_eq (bN' i : O) ziN hϕzi (bM.coord j)
    have hcoord : bM.coord j ⟨(bN' i : O), N_le_M ziN⟩ = as i := by
      have hsub : (⟨(bN' i : O), N_le_M ziN⟩ : M) =
          as i • bM j := by
        apply Subtype.ext
        rw [has i]
        simp only [bM, Basis.coe_mkFinConsOfLE]
        rfl
      rw [hsub, map_smul, Basis.coord_apply, Basis.repr_self,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
    rwa [hcoord] at hdvdCoord

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: a submodule of a finite free
module over a PID has diagonal bases whose coefficients form a divisibility chain. -/
theorem Submodule.exists_ordered_smith_normal_form_of_le
    {R M ι : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Finite ι] (b : Basis ι R M)
    (N O : Submodule R M) (N_le_O : N ≤ O) :
    ∃ (n o : ℕ) (hno : n ≤ o) (bO : Basis (Fin o) R O)
      (bN : Basis (Fin n) R N) (a : Fin n → R),
      (∀ i, (bN i : M) = a i • bO (Fin.castLE hno i)) ∧
        ∀ i j : Fin n, i ≤ j → a i ∣ a j := by
  cases nonempty_fintype ι
  -- Induct on the ambient submodule, retaining the maximal pivot at each step.
  induction O using Submodule.inductionOnRank b generalizing N with
  | ih M₀ ih =>
      obtain ⟨m, b'M⟩ := M₀.basisOfPid b
      by_cases N_bot : N = ⊥
      · subst N_bot
        exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim,
          finZeroElim, finZeroElim⟩
      obtain ⟨y, hy, a, _, M', M'_le_M, N', _, N'_le_M', y_ortho, _, h⟩ :=
        Submodule.basis_of_pid_aux_ordered M₀ N b'M N_bot N_le_O
      obtain ⟨n', m', hn'm', bM', bN', as', has', hasOrder⟩ :=
        ih M' M'_le_M y hy y_ortho N' N'_le_M'
      obtain ⟨bN, h'⟩ := h n' bN'
      obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
      obtain ⟨has, hhead⟩ := h'' as' has'
      refine ⟨_, _, hmn, bM, bN, Fin.cons (α := fun _ ↦ R) a as', has, ?_⟩
      -- A prepended pivot divides the tail, while the tail remains ordered by induction.
      intro i
      refine Fin.cases ?_ (fun i' ↦ ?_) i
      · intro j hij
        revert hij
        refine Fin.cases ?_ (fun j' hij ↦ ?_) j
        · intro hij
          exact dvd_refl _
        · exact hhead j'
      · intro j hij
        revert hij
        refine Fin.cases ?_ (fun j' hij ↦ ?_) j
        · intro hij
          exact False.elim (Fin.succ_ne_zero i' (le_antisymm hij (Fin.zero_le _)))
        · exact hasOrder i' j' (Fin.succ_le_succ_iff.mp hij)

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: a full-rank integer
submodule has positive diagonal bases whose coefficients are ordered by divisibility. -/
lemma Submodule.existsPositiveOrderedSmithBasesOfRankEq
    {M : Type*} [AddCommGroup M]
    (b : Basis (Fin n) ℤ M) (N : Submodule ℤ M)
    (hrank : Module.finrank ℤ N = Module.finrank ℤ M) :
    ∃ (bM : Basis (Fin n) ℤ M) (bN : Basis (Fin n) ℤ N) (e : Fin n → ℤ),
      (∀ i, (bN i : M) = e i • bM i) ∧ (∀ i, 0 < e i) ∧
        ∀ i j : Fin n, i ≤ j → e i ∣ e j := by
  classical
  -- First obtain ordered diagonal bases with their natural finite ranks.
  obtain ⟨k, o, hko, bO, bN, a, hdiag, horder⟩ :=
    Submodule.exists_ordered_smith_normal_form_of_le b N ⊤ le_top
  have hk : k = n := by
    calc
      k = Module.finrank ℤ N := by
        simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis bN).symm
      _ = Module.finrank ℤ M := hrank
      _ = n := by
        simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  subst k
  have ho : o = n := by
    calc
      o = Module.finrank ℤ (⊤ : Submodule ℤ M) := by
        simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis bO).symm
      _ = Module.finrank ℤ M := finrank_top ℤ M
      _ = n := by
        simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  subst o
  let bM : Basis (Fin n) ℤ M :=
    bO.map (LinearEquiv.ofTop (⊤ : Submodule ℤ M) rfl)
  have hdiag' : ∀ i, (bN i : M) = a i • bM i := by
    intro i
    rw [hdiag i]
    have hi : Fin.castLE hko i = i := Fin.ext rfl
    rw [hi]
    rfl
  have ha : ∀ i, a i ≠ 0 := by
    intro i hai
    apply Basis.ne_zero bN i
    apply Subtype.ext
    simpa only [hai, zero_smul] using hdiag' i
  choose u hu habs using fun i ↦ Int.exists_unit_of_abs (a i)
  let bN' := Basis.unitsSMul bN (fun i ↦ (hu i).unit)
  refine ⟨bM, bN', fun i ↦ (a i).natAbs, ?_, ?_, ?_⟩
  · -- Rescale each source basis vector by the unit that fixes its sign.
    intro i
    calc
      ((bN' i : N) : M) = ((hu i).unit : ℤ) • (bN i : M) := by
        simp only [bN', Basis.unitsSMul_apply]
        rfl
      _ = ((a i).natAbs : ℤ) • bM i := by
        rw [hdiag' i, smul_smul, (hu i).unit_spec, ← habs]
  · -- Nonzero absolute values are positive.
    intro i
    exact Int.natCast_pos.mpr (Int.natAbs_pos.mpr (ha i))
  · -- Taking absolute values preserves divisibility.
    intro i j hij
    rw [Int.natCast_dvd_natCast, Int.natAbs_dvd_natAbs]
    exact horder i j hij

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: every positive
integer diagonal is unimodularly equivalent to a positive divisibility-chain diagonal. -/
lemma existsUnimodularSmithRefinement
    (d : Fin n → ℤ) (hd : ∀ i, 0 < d i) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℤ, ∃ e : Fin n → ℤ,
      IsUnit P.det ∧ IsUnit Q.det ∧ IsSmithNormalDiagonal e ∧
        P * Matrix.diagonal d * Q = Matrix.diagonal e := by
  classical
  -- Route correction: retain maximal PID pivots instead of iterating explicit gcd/lcm blocks.
  have hdet : (Matrix.diagonal d).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i hi ↦ ne_of_gt (hd i)
  have hinj : Function.Injective (Matrix.diagonal d).toLin' := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply (Matrix.diagonal d).eq_zero_of_mulVec_eq_zero hdet
    rw [mulVec_sub, sub_eq_zero]
    simpa only [Matrix.toLin'_apply] using hxy
  have hrank : Module.finrank ℤ (LinearMap.range (Matrix.diagonal d).toLin') =
      Module.finrank ℤ (Fin n → ℤ) :=
    LinearMap.finrank_range_of_inj hinj
  -- Ordered Smith bases for the range provide the desired positive diagonal entries.
  obtain ⟨bM, bN, e, hbasis, hepos, heorder⟩ :=
    Submodule.existsPositiveOrderedSmithBasesOfRankEq
      (Pi.basisFun ℤ (Fin n)) (LinearMap.range (Matrix.diagonal d).toLin') hrank
  let φ := LinearEquiv.ofInjective (Matrix.diagonal d).toLin' hinj
  let bD := bN.map φ.symm
  let std := Pi.basisFun ℤ (Fin n)
  let P := bM.toMatrix std
  let Q := std.toMatrix bD
  refine ⟨P, Q, e, ?_, ?_, ?_, ?_⟩
  · -- Each basis-change matrix has a basis-change matrix as a right inverse.
    exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip bM std)
  · exact Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip std bD)
  · -- All-pairs divisibility specializes to the target's adjacent-index condition.
    refine ⟨hepos, fun i ↦ heorder _ _ ?_⟩
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.le_succ i.val
  · -- Translate the ordered basis relation back to the matrix identity.
    have hbasis' : ∀ i, (Matrix.diagonal d).toLin' (bD i) = e i • bM i := by
      intro i
      calc
        (Matrix.diagonal d).toLin' (bD i) =
            ((bN i : LinearMap.range (Matrix.diagonal d).toLin') : Fin n → ℤ) := by
          exact congrArg Subtype.val (φ.apply_symm_apply (bN i))
        _ = e i • bM i := hbasis i
    calc
      P * Matrix.diagonal d * Q =
          LinearMap.toMatrix bD bM (Matrix.diagonal d).toLin' := by
        simpa only [P, Q, std, LinearMap.toMatrix_eq_toMatrix',
          LinearMap.toMatrix'_toLin'] using
            (basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
              bD std bM std (Matrix.diagonal d).toLin')
      _ = Matrix.diagonal e := by
        ext i j
        rw [LinearMap.toMatrix_apply, hbasis' j]
        simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
          Matrix.diagonal_apply, Finsupp.single_apply]
        by_cases hij : i = j
        · subst j
          rfl
        · simp only [hij, Ne.symm hij, ↓reduceIte]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean`: positive ordered
Smith diagonals that are related by unimodular matrices have identical entries. -/
lemma smithDiagonal_eq_of_unimodularEquivalence
    {d d' : Fin n → ℤ} (hd : IsSmithNormalDiagonal d)
    (hd' : IsSmithNormalDiagonal d')
    {P Q : Matrix (Fin n) (Fin n) ℤ}
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (heq : P * Matrix.diagonal d * Q = Matrix.diagonal d') : d' = d := by
  -- Unimodular invariance identifies every exterior-power determinantal ideal.
  have hideal : ∀ k (hk : k ≤ n),
      determinantalIdeal k (Matrix.diagonal d) =
        determinantalIdeal k (Matrix.diagonal d') := by
    intro k hk
    have hinv := determinantalIdeal_mul_eq k (Matrix.diagonal d) P Q hP hQ
    rw [heq] at hinv
    exact hinv.symm
  -- Their positive prefix products agree and successive cancellation recovers each entry.
  apply eq_of_positive_prefixProducts_eq hd'.pos
  intro k hk
  exact smithPrefixProduct_eq_of_determinantalIdeal_eq hd hd' hideal k hk

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_theorem_1_21.lean. See https://en.wikipedia.org/wiki/Smith_normal_form.
Theorem 1.21 (1). Every nonsingular integer square matrix admits a Smith normal form
`Matrix.diagonal d` obtained by unimodular left and right multiplication, with positive diagonal
entries forming a divisibility chain. -/
theorem existsSmithNormalFormOfDetNeZero
    (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) :
    ∃ R C : Matrix (Fin n) (Fin n) ℤ, ∃ d : Fin n → ℤ,
      ∃ _hR : IsUnit R.det,
      ∃ _hC : IsUnit C.det,
      ∃ _hd : IsSmithNormalDiagonal d,
      R * A * C = Matrix.diagonal d := by
  -- First diagonalize between bases and normalize the signs of all coefficients.
  obtain ⟨R, C, d, hR, hC, hd, hdiag⟩ := existsPositiveDiagonalEquivalence A hA
  -- Then refine the positive diagonal to the divisibility-chain normal form.
  obtain ⟨P, Q, e, hP, hQ, he, hrefine⟩ := existsUnimodularSmithRefinement d hd
  refine ⟨P * R, C * Q, e, ?_, ?_, he, ?_⟩
  · simpa only [det_mul] using hP.mul hR
  · simpa only [det_mul] using hC.mul hQ
  · calc
      (P * R) * A * (C * Q) = P * (R * A * C) * Q := by
        simp only [Matrix.mul_assoc]
      _ = P * Matrix.diagonal d * Q := by rw [hdiag]
      _ = Matrix.diagonal e := hrefine

/-- Theorem 1.21 (2). If two Smith normal forms of the same integer square matrix have
positive diagonal entries forming divisibility chains, then their diagonal entries agree. -/
theorem smithNormalFormUnique
    (A : Matrix (Fin n) (Fin n) ℤ)
    {R C R' C' : Matrix (Fin n) (Fin n) ℤ} {d d' : Fin n → ℤ}
    (hR : IsUnit R.det) (hC : IsUnit C.det)
    (hd : IsSmithNormalDiagonal d)
    (hdiag : R * A * C = Matrix.diagonal d)
    (hR' : IsUnit R'.det) (hC' : IsUnit C'.det)
    (hd' : IsSmithNormalDiagonal d')
    (hdiag' : R' * A * C' = Matrix.diagonal d') :
    d' = d := by
  -- Recover `A` from the first diagonalization using nonsingular inverses.
  have hrecover : A = R⁻¹ * Matrix.diagonal d * C⁻¹ := by
    calc
      A = 1 * A * 1 := by simp only [Matrix.one_mul, Matrix.mul_one]
      _ = (R⁻¹ * R) * A * (C * C⁻¹) := by
        rw [Matrix.nonsing_inv_mul R hR, Matrix.mul_nonsing_inv C hC]
      _ = R⁻¹ * (R * A * C) * C⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = R⁻¹ * Matrix.diagonal d * C⁻¹ := by rw [hdiag]
  -- Thus the two ordered diagonals differ only by unimodular factors.
  have heq : (R' * R⁻¹) * Matrix.diagonal d * (C⁻¹ * C') = Matrix.diagonal d' := by
    calc
      (R' * R⁻¹) * Matrix.diagonal d * (C⁻¹ * C') =
          R' * (R⁻¹ * Matrix.diagonal d * C⁻¹) * C' := by
            simp only [Matrix.mul_assoc]
      _ = R' * A * C' := by rw [← hrecover]
      _ = Matrix.diagonal d' := hdiag'
  have hleft : IsUnit (R' * R⁻¹).det := by
    simpa only [det_mul] using hR'.mul (Matrix.isUnit_nonsing_inv_det R hR)
  have hright : IsUnit (C⁻¹ * C').det := by
    simpa only [det_mul] using (Matrix.isUnit_nonsing_inv_det C hC).mul hC'
  -- Invoke uniqueness for unimodularly equivalent ordered positive diagonals.
  exact smithDiagonal_eq_of_unimodularEquivalence hd hd' hleft hright heq

end Theorem121

end Matrix

end

#print axioms Matrix.existsSmithNormalFormOfDetNeZero
#print axioms Matrix.smithNormalFormUnique
-/
