/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.FreeModule.Int
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_4.MixedSpace
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_definition_1_37

public section

open scoped IntegerVectorNotation Matrix

namespace RationalLinearSystem

variable {m n : ℕ}

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: an integer quotient is
an integer rational exactly when its denominator divides its numerator. -/
private lemma ratQuotient_mem_intCastRange_iff (z d : ℤ) (hd : d ≠ 0) :
    (z : ℚ) / (d : ℚ) ∈ Set.range (Int.cast : ℤ → ℚ) ↔ d ∣ z := by
  -- Express membership in the cast range by the canonical denominator-one criterion.
  constructor
  · rintro ⟨k, hk⟩
    have hden : ((z : ℚ) / (d : ℚ)).den = 1 := by
      rw [← hk]
      exact Rat.den_intCast k
    exact (Rat.den_div_intCast_eq_one_iff z d hd).mp hden
  · intro hdiv
    have hden : ((z : ℚ) / (d : ℚ)).den = 1 :=
      (Rat.den_div_intCast_eq_one_iff z d hd).mpr hdiv
    refine ⟨((z : ℚ) / (d : ℚ)).num, ?_⟩
    exact (Rat.den_eq_one_iff _).mp hden

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: the coefficients of an
integer linear functional in the standard basis compute its rational extension by dot product. -/
private lemma integerLinearMapRatio_dotProduct
    (L : (Fin m → ℤ) →ₗ[ℤ] ℤ) (d : ℤ) (x : Fin m → ℤ) :
    (fun j ↦ (L (Pi.single j 1) : ℚ) / (d : ℚ)) ⬝ᵥ (fun j ↦ (x j : ℚ)) =
      (L x : ℚ) / (d : ℚ) := by
  -- Expand the functional in the standard basis, then collect the common denominator.
  rw [LinearMap.pi_apply_eq_sum_univ]
  simp only [dotProduct, smul_eq_mul, Int.cast_sum, Int.cast_mul]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hbasis : (fun k : Fin m ↦ if j = k then (1 : ℤ) else 0) = Pi.single j 1 := by
    funext k
    by_cases hkj : k = j
    · subst k
      rw [Pi.single_eq_same]
      simp
    · rw [Pi.single_eq_of_ne hkj]
      simp [Ne.symm hkj]
  have hL : L (Pi.single j 1) = L (fun k ↦ if j = k then 1 else 0) :=
    congrArg L hbasis.symm
  rw [hL]
  ring

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: Smith coordinates
characterize membership in an integer submodule. -/
private lemma mem_submodule_iff_smithNormalFormCoordinates
    (N : Submodule ℤ (Fin m → ℤ)) (r : ℕ)
    (snf : Module.Basis.SmithNormalForm N (Fin m) r) (x : Fin m → ℤ) :
    x ∈ N ↔
      (∀ i, i ∉ Set.range snf.f → snf.bM.repr x i = 0) ∧
        ∀ k, snf.a k ∣ snf.bM.repr x (snf.f k) := by
  classical
  -- Necessity follows from the two coordinate formulas supplied by Smith normal form.
  constructor
  · intro hx
    constructor
    · intro i hi
      exact snf.repr_eq_zero_of_notMem_range ⟨x, hx⟩ hi
    · intro k
      refine ⟨snf.bN.repr ⟨x, hx⟩ k, ?_⟩
      calc
        snf.bM.repr x (snf.f k) =
            snf.bN.repr (snf.a k • ⟨x, hx⟩) k :=
          snf.repr_apply_embedding_eq_repr_smul ⟨x, hx⟩
        _ = snf.a k * snf.bN.repr ⟨x, hx⟩ k := by
          rw [map_smul]
          rfl
  · rintro ⟨houtside, hdiv⟩
    choose c hc' using hdiv
    have hbasis (k : Fin r) :
        snf.bM.repr (snf.bN k : Fin m → ℤ) =
          snf.a k • Finsupp.single (snf.f k) 1 := by
      rw [snf.snf, map_smul, snf.bM.repr_self]
    -- Reconstruct the vector from the divisible Smith coordinates.
    refine snf.bN.mem_submodule_iff'.mpr ⟨c, ?_⟩
    apply snf.bM.repr.injective
    ext i
    by_cases hi : i ∈ Set.range snf.f
    · rcases hi with ⟨k, rfl⟩
      rw [map_sum]
      simp_rw [map_smul, hbasis]
      simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul,
        Finsupp.single_apply]
      simpa [mul_comm] using hc' k
    · rw [houtside i hi]
      rw [map_sum]
      simp_rw [map_smul, hbasis]
      simp only [Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
      symm
      apply Finset.sum_eq_zero
      intro k hk'
      have hne : snf.f k ≠ i := by
        intro hki
        exact hi ⟨k, hki⟩
      simp [hne]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: a vector outside an
integer submodule is separated from it by a rational dot-product functional modulo `ℤ`. -/
private lemma exists_rationalDotProduct_separator
    (N : Submodule ℤ (Fin m → ℤ)) (c : Fin m → ℤ) (hc : c ∉ N) :
    ∃ v : Fin m → ℚ,
      (∀ y : Fin m → ℤ, y ∈ N →
        v ⬝ᵥ (fun i ↦ (y i : ℚ)) ∈ Set.range (Int.cast : ℤ → ℚ)) ∧
      v ⬝ᵥ (fun i ↦ (c i : ℚ)) ∉ Set.range (Int.cast : ℤ → ℚ) := by
  classical
  obtain ⟨r, snf⟩ := N.smithNormalForm (Pi.basisFun ℤ (Fin m))
  rw [mem_submodule_iff_smithNormalFormCoordinates N r snf c] at hc
  have hfailure :
      (∃ i, i ∉ Set.range snf.f ∧ snf.bM.repr c i ≠ 0) ∨
        ∃ k, ¬snf.a k ∣ snf.bM.repr c (snf.f k) := by
    by_cases houtside : ∀ i, i ∉ Set.range snf.f → snf.bM.repr c i = 0
    · right
      have hnotdiv : ¬∀ k, snf.a k ∣ snf.bM.repr c (snf.f k) := by
        intro hdiv
        exact hc ⟨houtside, hdiv⟩
      simpa only [not_forall] using hnotdiv
    · left
      rw [not_forall] at houtside
      rcases houtside with ⟨i, hi⟩
      rw [Classical.not_imp] at hi
      exact ⟨i, hi.1, hi.2⟩
  -- A failed coordinate is either outside the Smith support or fails its divisibility test.
  rcases hfailure with ⟨i, hi, hci⟩ | ⟨k, hck⟩
  · let L : (Fin m → ℤ) →ₗ[ℤ] ℤ := snf.bM.coord i
    let d : ℤ := 2 * L c
    have hLc : L c ≠ 0 := hci
    have hd : d ≠ 0 := mul_ne_zero (by norm_num) hLc
    refine ⟨fun j ↦ (L (Pi.single j 1) : ℚ) / (d : ℚ), ?_, ?_⟩
    · intro y hy
      have hLy : L y = 0 := snf.repr_eq_zero_of_notMem_range ⟨y, hy⟩ hi
      rw [integerLinearMapRatio_dotProduct]
      refine ⟨0, ?_⟩
      simp [hLy]
    · rw [integerLinearMapRatio_dotProduct, ratQuotient_mem_intCastRange_iff _ _ hd]
      rintro ⟨q, hq⟩
      have heq : L c * 1 = L c * (2 * q) := by
        calc
          L c * 1 = L c := mul_one _
          _ = (2 * L c) * q := hq
          _ = L c * (2 * q) := by ring
      have hone : (1 : ℤ) = 2 * q := mul_left_cancel₀ hLc heq
      omega
  · let L : (Fin m → ℤ) →ₗ[ℤ] ℤ := snf.bM.coord (snf.f k)
    have hd : snf.a k ≠ 0 := by
      intro ha
      have hb : (snf.bN k : Fin m → ℤ) = 0 := by
        rw [snf.snf, ha, zero_smul]
      have hb' : snf.bN k = 0 := Subtype.ext hb
      exact snf.bN.ne_zero k hb'
    refine ⟨fun j ↦ (L (Pi.single j 1) : ℚ) / (snf.a k : ℚ), ?_, ?_⟩
    · intro y hy
      have hdiv :=
        (mem_submodule_iff_smithNormalFormCoordinates N r snf y).mp hy |>.2 k
      rw [integerLinearMapRatio_dotProduct]
      exact (ratQuotient_mem_intCastRange_iff _ _ hd).mpr hdiv
    · rw [integerLinearMapRatio_dotProduct, ratQuotient_mem_intCastRange_iff _ _ hd]
      exact hck

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: the real dot product of
two integer vectors is the cast of an integer. -/
private lemma intCastDotProduct_mem_range
    {ι : Type*} [Fintype ι] (x z : ι → ℤ) :
    (fun i ↦ (x i : ℝ)) ⬝ᵥ (fun i ↦ (z i : ℝ)) ∈
      Set.range (Int.cast : ℤ → ℝ) := by
  -- The witness is the integer dot product before casting.
  refine ⟨x ⬝ᵥ z, ?_⟩
  simp [dotProduct]

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: casting a rational to
`ℝ` preserves and reflects whether it is an integer. -/
private lemma ratCast_mem_intCastRange_iff (q : ℚ) :
    (q : ℝ) ∈ Set.range (Int.cast : ℤ → ℝ) ↔
      q ∈ Set.range (Int.cast : ℤ → ℚ) := by
  -- Injectivity of the rational cast reflects the integer witness in either direction.
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact_mod_cast hz
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    exact_mod_cast hz

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean`: scaling one vector and
dividing the other by the same nonzero real leaves their dot product unchanged. -/
private lemma scale_dotProduct_div_cancel {ι : Type*} [Fintype ι]
    (d : ℝ) (hd : d ≠ 0) (v w : ι → ℝ) :
    (fun i ↦ d * v i) ⬝ᵥ (fun i ↦ w i / d) = v ⬝ᵥ w := by
  -- Cancel the common scale in each summand of the dot product.
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  calc
    d * v i * (w i / d) = (d * d⁻¹) * (v i * w i) := by ring
    _ = v i * w i := by rw [mul_inv_cancel₀ hd, one_mul]

-- Route correction: the earlier failure was label association, not the theorem proof.
-- Keep the verified proof and restore the raw label as one contiguous docstring prefix.
/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_theorem_1_13.lean.
Theorem 1.13 (Integer Farkas Lemma / Kronecker Approximation Theorem). For
`A : Matrix (Fin m) (Fin n) ℚ` and `b : Fin m → ℚ`, the rational linear system
`A x = b` has no integer solution if and only if there exists a real row multiplier
`u` such that `u ᵥ* (A.map (Rat.castHom ℝ)) ∈ ℤ^n` and
`u ⬝ᵥ (fun i ↦ (b i : ℝ)) ∉ Set.range (Int.cast : ℤ → ℝ)`. -/
theorem integerFarkasLemma
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ¬ hasIntegerSolution A b ↔
      ∃ u : Fin m → ℝ,
        u ᵥ* (A.map (Rat.castHom ℝ)) ∈ ℤ^n ∧
          u ⬝ᵥ (fun i ↦ (b i : ℝ)) ∉ Set.range (Int.cast : ℤ → ℝ) := by
  classical
  constructor
  · intro hNoSolution
    -- Clear the denominators of `A` and `b` simultaneously using one augmented matrix.
    let B : Matrix (Fin m) (Fin 1) ℚ := fun i _ ↦ b i
    let D : Matrix (Fin m) (Fin n ⊕ Fin 1) ℚ := Matrix.fromCols A B
    let C : Matrix (Fin m) (Fin n) ℤ := fun i j ↦ D.num i (Sum.inl j)
    let c : Fin m → ℤ := fun i ↦ D.num i (Sum.inr 0)
    let d : ℕ := D.den
    have hd : d ≠ 0 := D.den_ne_zero
    have hAcoeff (i : Fin m) (j : Fin n) :
        (C i j : ℚ) / (d : ℚ) = A i j := by
      exact Matrix.num_div_den D i (Sum.inl j)
    have hbcoeff (i : Fin m) : (c i : ℚ) / (d : ℚ) = b i := by
      exact Matrix.num_div_den D i (Sum.inr 0)
    have hcNotRange : c ∉ LinearMap.range C.mulVecLin := by
      intro hcRange
      rcases hcRange with ⟨x, hx⟩
      apply hNoSolution
      rw [hasIntegerSolution_iff]
      refine ⟨x, ?_⟩
      funext i
      have hxi := congrFun hx i
      simp only [Matrix.mulVecLin_apply] at hxi
      rw [← hbcoeff i, ← hxi]
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul]
      simp_rw [← hAcoeff i]
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    obtain ⟨v, hvRange, hvc⟩ :=
      exists_rationalDotProduct_separator (LinearMap.range C.mulVecLin) c hcNotRange
    have hcolRange (j : Fin n) : (fun i ↦ C i j) ∈ LinearMap.range C.mulVecLin := by
      refine ⟨Pi.single j 1, ?_⟩
      simpa only [Matrix.mulVecLin_apply] using Matrix.mulVec_single_one C j
    have hdr : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    have hAreal (i : Fin m) (j : Fin n) :
        (Rat.castHom ℝ) (A i j) = (C i j : ℝ) / (d : ℝ) := by
      have hcast := congrArg (Rat.castHom ℝ) (hAcoeff i j).symm
      simpa only [map_div₀, map_intCast, map_natCast] using hcast
    have hbreal (i : Fin m) : (b i : ℝ) = (c i : ℝ) / (d : ℝ) := by
      have hcast := congrArg (Rat.castHom ℝ) (hbcoeff i).symm
      simpa only [map_div₀, map_intCast, map_natCast] using hcast
    let u : Fin m → ℝ := fun i ↦ (d : ℝ) * (v i : ℝ)
    have hrow (j : Fin n) :
        (u ᵥ* A.map (Rat.castHom ℝ)) j =
          ((v ⬝ᵥ (fun i ↦ (C i j : ℚ)) : ℚ) : ℝ) := by
      have hcastDot :
          ((v ⬝ᵥ (fun i ↦ (C i j : ℚ)) : ℚ) : ℝ) =
            (fun i ↦ (v i : ℝ)) ⬝ᵥ (fun i ↦ (C i j : ℝ)) := by
        simpa only [Function.comp_apply, map_intCast] using
          RingHom.map_dotProduct (Rat.castHom ℝ) v (fun i ↦ (C i j : ℚ))
      rw [hcastDot]
      simp only [Matrix.vecMul, Matrix.map_apply, dotProduct, u]
      simp_rw [hAreal]
      exact scale_dotProduct_div_cancel (d : ℝ) hdr
        (fun i ↦ (v i : ℝ)) (fun i ↦ (C i j : ℝ))
    have hright :
        u ⬝ᵥ (fun i ↦ (b i : ℝ)) =
          ((v ⬝ᵥ (fun i ↦ (c i : ℚ)) : ℚ) : ℝ) := by
      have hcastDot :
          ((v ⬝ᵥ (fun i ↦ (c i : ℚ)) : ℚ) : ℝ) =
            (fun i ↦ (v i : ℝ)) ⬝ᵥ (fun i ↦ (c i : ℝ)) := by
        simpa only [Function.comp_apply, map_intCast] using
          RingHom.map_dotProduct (Rat.castHom ℝ) v (fun i ↦ (c i : ℚ))
      rw [hcastDot]
      simp only [u]
      simp_rw [hbreal]
      exact scale_dotProduct_div_cancel (d : ℝ) hdr
        (fun i ↦ (v i : ℝ)) (fun i ↦ (c i : ℝ))
    refine ⟨u, ?_, ?_⟩
    · rw [mem_integerVectors_iff_forall]
      intro j
      rw [hrow]
      exact ratCast_mem_intCastRange_iff _ |>.mpr (hvRange _ (hcolRange j))
    · rw [hright, ratCast_mem_intCastRange_iff]
      exact hvc
  · rintro ⟨u, huA, hub⟩ hSolution
    -- Any integer solution pairs with the integral row product to make `u ⬝ᵥ b` integral.
    rw [hasIntegerSolution_iff] at hSolution
    rcases hSolution with ⟨x, hx⟩
    rcases mem_integerVectors_iff.mp huA with ⟨z, hz⟩
    apply hub
    have hcastSolution :
        A.map (Rat.castHom ℝ) *ᵥ (fun j ↦ (x j : ℝ)) = fun i ↦ (b i : ℝ) := by
      funext i
      have hi := congrArg (Rat.castHom ℝ) (congrFun hx i)
      rw [RingHom.map_mulVec] at hi
      simpa only [Function.comp_apply, map_intCast] using hi
    rw [← hcastSolution, Matrix.dotProduct_mulVec, hz]
    exact intCastDotProduct_mem_range z x

end RationalLinearSystem

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_1bb6679f67b2126ca48f"
#print axioms _root_.RationalLinearSystem.integerFarkasLemma
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_1bb6679f67b2126ca48f"
