module

public import ReasLib.Analysis.Seminorm.Contracting
public import ReasLib.Analysis.Seminorm.Equivalence
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Finite

public section

universe u

namespace LinearMap

variable {E : Type u}

section Algebraic

variable [AddCommGroup E] [Module ℝ E]

/-- The spectral radius of a real endomorphism after extension of scalars to `ℂ`. -/
noncomputable def complexSpectralRadius (L : Module.End ℝ E) : ENNReal :=
  spectralRadius ℂ (L.baseChange ℂ)

/-- The midpoint between the complex spectral radius and a proposed contraction bound. -/
noncomputable def adaptedRate (L : Module.End ℝ E) (r : NNReal) : NNReal :=
  (L.complexSpectralRadius.toNNReal + r) / 2

/-- The adapted rate is strictly below the proposed contraction bound. -/
theorem adaptedRate_lt (L : Module.End ℝ E) (r : NNReal)
    (hρ : L.complexSpectralRadius < r) : L.adaptedRate r < r := by
  -- Convert the extended spectral-radius bound to `NNReal`, then use the midpoint inequality.
  unfold adaptedRate
  exact add_div_two_lt_right.2 (ENNReal.toNNReal_lt_of_lt_coe hρ)

/-- The complex spectral radius is strictly below the midpoint with any larger rate. -/
private theorem complexSpectralRadius_lt_adaptedRate (L : Module.End ℝ E) (r : NNReal)
    (hρ : L.complexSpectralRadius < r) : L.complexSpectralRadius < L.adaptedRate r := by
  rw [← ENNReal.coe_toNNReal (ne_top_of_lt hρ)]
  exact_mod_cast left_lt_add_div_two.2 (ENNReal.toNNReal_lt_of_lt_coe hρ)

end Algebraic

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted supremum of the ambient norm pulled back along all iterates of `L`. -/
noncomputable def adaptedSeminorm (L : Module.End ℝ E) (r : NNReal) : Seminorm ℝ E :=
  ⨆ n : ℕ, (L.adaptedRate r)⁻¹ ^ n • (normSeminorm ℝ E).comp (L ^ n)

variable [FiniteDimensional ℝ E]

/-- Weighted norms of the iterates of an endomorphism are uniformly bounded above every
rate strictly larger than its complex spectral radius. -/
private theorem weightedIterates_bounded (L : Module.End ℝ E) (q : NNReal)
    (hρ : L.complexSpectralRadius < q) :
    ∃ C : NNReal, 0 < C ∧ ∀ n x, q⁻¹ ^ n * ‖(L ^ n) x‖₊ ≤ C * ‖x‖₊ := by
  let V := TensorProduct ℝ ℂ E
  let b := Module.Free.chooseBasis ℂ V
  let e := b.equivFun
  -- Local instance justification (construction): the algebraic complexification has no canonical
  -- norm, so coordinates supply one solely for applying the finite-dimensional Gelfand formula.
  letI : NormedAddCommGroup V := NormedAddCommGroup.induced V _ e e.injective
  -- Local instance justification (construction): the transported coordinate norm is compatible
  -- with complex scalar multiplication by construction.
  letI : NormedSpace ℂ V := NormedSpace.induced ℂ V _ e
  -- Local instance justification (canonical tensor action): fixing the tensor product's real
  -- module before its normed structure prevents the scalar actions from diverging.
  letI : Module ℝ V := TensorProduct.leftModule
  -- Local instance justification (restriction of scalars): the comparison maps are real-linear,
  -- so the canonical tensor-product module is equipped with the restricted complex norm.
  letI : NormedSpace ℝ V :=
    { (TensorProduct.leftModule : Module ℝ V) with
      norm_smul_le := (NormedSpace.restrictScalars ℝ ℂ V).norm_smul_le }
  -- Local instance justification (restriction of scalars): finite dimension over ℂ and the
  -- two-dimensional real structure of ℂ make the complexification finite-dimensional over ℝ.
  letI : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let j : E →ₗ[ℝ] V := TensorProduct.mk ℝ ℂ E 1
  let p : V →ₗ[ℝ] E := TensorProduct.lift ((LinearMap.lsmul ℝ E).comp Complex.reLm)
  let T : V →L[ℂ] V := (Module.End.toContinuousLinearMap V) (L.baseChange ℂ)
  let jC : E →L[ℝ] V := LinearMap.toContinuousLinearMap j
  let pC : V →L[ℝ] E := LinearMap.toContinuousLinearMap p
  have hq : 0 < q := by
    rw [← ENNReal.coe_pos]
    exact zero_le.trans_lt hρ
  have hTρ : spectralRadius ℂ T < q := by
    have hT : T = (Module.End.toContinuousLinearMap V) (L.baseChange ℂ) := rfl
    have hspectrum : spectrum ℂ T = spectrum ℂ (L.baseChange ℂ) := by
      rw [hT]
      exact AlgEquiv.spectrum_eq (Module.End.toContinuousLinearMap V) (L.baseChange ℂ)
    unfold complexSpectralRadius at hρ
    unfold spectralRadius at hρ ⊢
    rwa [hspectrum]
  -- Local instance justification (completeness): the operator space is finite-dimensional over
  -- ℂ, hence complete for its operator norm.
  letI : CompleteSpace (V →L[ℂ] V) := FiniteDimensional.complete ℂ (V →L[ℂ] V)
  have hroot : ∀ᶠ (n : ℕ) in Filter.atTop,
      (‖T ^ n‖₊ : ENNReal) ^ (1 / n : ℝ) < (q : ENNReal) :=
    (tendsto_order.1 (spectrum.gelfand_formula T)).2 _ hTρ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hroot
  have hiterate (n : ℕ) (x : E) : (T ^ n) (jC x) = jC ((L ^ n) x) := by
    have hpow : T ^ n =
        (Module.End.toContinuousLinearMap V) ((L ^ n).baseChange ℂ) := by
      dsimp only [T]
      rw [← map_pow, LinearMap.baseChange_pow]
    rw [hpow]
    exact LinearMap.baseChange_tmul (f := L ^ n) (A := ℂ) 1 x
  have hretract (x : E) : pC (jC x) = x := by
    simp only [pC, jC, LinearMap.coe_toContinuousLinearMap', p, j]
    have hmk : ((TensorProduct.mk ℝ ℂ E) 1) x = (1 : ℂ) ⊗ₜ[ℝ] x := rfl
    rw [hmk, TensorProduct.lift.tmul]
    simp
  have hlarge (n : ℕ) (hn : N ≤ n) : q⁻¹ ^ n * ‖T ^ n‖₊ ≤ 1 := by
    by_cases hn0 : n = 0
    · subst n
      have hone : (1 : V →L[ℂ] V) = ContinuousLinearMap.id ℂ V := by
        ext
        rfl
      simp only [pow_zero, one_mul]
      rw [hone]
      exact_mod_cast ContinuousLinearMap.norm_id_le
    · have hpow : ‖T ^ n‖₊ < q ^ n := by
        have hN' : (‖T ^ n‖₊ : ENNReal) ^ (n : ℝ)⁻¹ < (q : ENNReal) := by
          simpa only [one_div] using hN n hn
        rw [← ENNReal.coe_lt_coe, ENNReal.coe_pow]
        rw [← ENNReal.rpow_inv_natCast_pow hn0 (‖T ^ n‖₊ : ENNReal)]
        exact ENNReal.pow_lt_pow_left hn0 hN'
      calc
        q⁻¹ ^ n * ‖T ^ n‖₊ ≤ q⁻¹ ^ n * q ^ n :=
          mul_le_mul_right hpow.le _
        _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hq.ne', one_pow]
  let B : NNReal := 1 + ∑ n ∈ Finset.range N, q⁻¹ ^ n * ‖T ^ n‖₊
  have hweight (n : ℕ) : q⁻¹ ^ n * ‖T ^ n‖₊ ≤ B := by
    by_cases hn : N ≤ n
    · have hone_le : 1 ≤ B := by
        simp [B]
      exact (hlarge n hn).trans hone_le
    · have hnmem : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
      calc
        q⁻¹ ^ n * ‖T ^ n‖₊ ≤ ∑ k ∈ Finset.range N, q⁻¹ ^ k * ‖T ^ k‖₊ := by
          exact Finset.single_le_sum
            (f := fun k ↦ q⁻¹ ^ k * ‖T ^ k‖₊) (fun _ _ ↦ zero_le) hnmem
        _ ≤ B := by simp [B]
  have hCpos : 0 < 1 + ‖pC‖₊ * ‖jC‖₊ * B := by
    positivity
  refine ⟨1 + ‖pC‖₊ * ‖jC‖₊ * B, hCpos, ?_⟩
  intro n x
  have hnorm : ‖(L ^ n) x‖₊ ≤ ‖pC‖₊ * ‖T ^ n‖₊ * ‖jC‖₊ * ‖x‖₊ := by
    calc
      ‖(L ^ n) x‖₊ = ‖pC ((T ^ n) (jC x))‖₊ := by rw [hiterate, hretract]
      _ ≤ ‖pC‖₊ * ‖(T ^ n) (jC x)‖₊ := pC.le_opNNNorm _
      _ ≤ ‖pC‖₊ * (‖T ^ n‖₊ * ‖jC x‖₊) := by
        gcongr
        exact (T ^ n).le_opNNNorm _
      _ ≤ ‖pC‖₊ * (‖T ^ n‖₊ * (‖jC‖₊ * ‖x‖₊)) := by
        gcongr
        exact jC.le_opNNNorm _
      _ = ‖pC‖₊ * ‖T ^ n‖₊ * ‖jC‖₊ * ‖x‖₊ := by ring
  calc
    q⁻¹ ^ n * ‖(L ^ n) x‖₊ ≤
        q⁻¹ ^ n * (‖pC‖₊ * ‖T ^ n‖₊ * ‖jC‖₊ * ‖x‖₊) :=
      mul_le_mul_right hnorm _
    _ = (‖pC‖₊ * ‖jC‖₊) * (q⁻¹ ^ n * ‖T ^ n‖₊) * ‖x‖₊ := by ring
    _ ≤ (‖pC‖₊ * ‖jC‖₊) * B * ‖x‖₊ := by
      gcongr
      exact hweight n
    _ ≤ (1 + ‖pC‖₊ * ‖jC‖₊ * B) * ‖x‖₊ := by
      gcongr
      exact le_add_self

/-- The weighted-iterate seminorm is equivalent to the ambient norm. -/
theorem adaptedSeminorm_isEquivalent (L : Module.End ℝ E) (r : NNReal)
    (hρ : L.complexSpectralRadius < r) :
    (L.adaptedSeminorm r).IsEquivalent (normSeminorm ℝ E) := by
  -- The zeroth iterate gives the lower bound; uniform weighted boundedness gives the upper one.
  obtain ⟨C, hC, hbound⟩ := weightedIterates_bounded L (L.adaptedRate r)
    (complexSpectralRadius_lt_adaptedRate L r hρ)
  have hbdd : BddAbove (Set.range fun n : ℕ ↦
      (L.adaptedRate r)⁻¹ ^ n • (normSeminorm ℝ E).comp (L ^ n)) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    refine ⟨(C : ℝ) * ‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact_mod_cast hbound n x
  rw [Seminorm.isEquivalent_iff]
  refine ⟨1, C, zero_lt_one, hC, ?_⟩
  intro x
  constructor
  · rw [adaptedSeminorm, Seminorm.iSup_apply hbdd]
    have hzero := le_ciSup (Seminorm.bddAbove_range_iff.mp hbdd x) 0
    simpa [Seminorm.comp_apply, coe_normSeminorm] using hzero
  · rw [adaptedSeminorm, Seminorm.iSup_apply hbdd]
    refine ciSup_le fun n ↦ ?_
    exact_mod_cast hbound n x

/-- The weighted-iterate seminorm makes `L` contract with a coefficient below `r`. -/
theorem adaptedSeminorm_isContracting (L : Module.End ℝ E) (r : NNReal)
    (hρ : L.complexSpectralRadius < r) :
    (L.adaptedSeminorm r).IsContracting L r := by
  -- Shifting the iterate index multiplies every weighted term by the adapted rate.
  let q := L.adaptedRate r
  have hq : 0 < q := by
    rw [← ENNReal.coe_pos]
    exact zero_le.trans_lt (complexSpectralRadius_lt_adaptedRate L r hρ)
  obtain ⟨C, -, hbound⟩ := weightedIterates_bounded L q
    (complexSpectralRadius_lt_adaptedRate L r hρ)
  have hbdd : BddAbove
      (Set.range fun n : ℕ ↦ q⁻¹ ^ n • (normSeminorm ℝ E).comp (L ^ n)) := by
    rw [Seminorm.bddAbove_range_iff]
    intro x
    refine ⟨(C : ℝ) * ‖x‖, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact_mod_cast hbound n x
  rw [Seminorm.isContracting_iff]
  refine ⟨q, L.adaptedRate_lt r hρ, ?_⟩
  intro x
  rw [adaptedSeminorm, Seminorm.iSup_apply hbdd, Seminorm.iSup_apply hbdd]
  change (⨆ i, (q⁻¹ ^ i : ℝ) * ‖(L ^ i) (L x)‖) ≤
    (q : ℝ) * (⨆ i, (q⁻¹ ^ i : ℝ) * ‖(L ^ i) x‖)
  refine ciSup_le fun n ↦ ?_
  calc
    (q⁻¹ ^ n : ℝ) * ‖(L ^ n) (L x)‖ =
        (q : ℝ) * ((q⁻¹ ^ (n + 1) : ℝ) * ‖(L ^ (n + 1)) x‖) := by
      rw [pow_succ L n, Module.End.mul_apply, pow_succ]
      push_cast
      field_simp
    _ ≤ (q : ℝ) * (⨆ k, (q⁻¹ ^ k : ℝ) * ‖(L ^ k) x‖) := by
      gcongr
      exact le_ciSup (Seminorm.bddAbove_range_iff.mp hbdd x) (n + 1)

/-- If the complex spectral radius of a real endomorphism is below `r < 1`, then its
weighted-iterate seminorm is equivalent to the ambient norm and contracts it below `r`. -/
theorem adaptedSeminorm_spec (L : Module.End ℝ E) (r : NNReal)
    (hρ : L.complexSpectralRadius < r) (hr : r < 1) :
    (L.adaptedSeminorm r).IsEquivalent (normSeminorm ℝ E) ∧
      (L.adaptedSeminorm r).IsContracting L r := by
  -- Combine the equivalence and contraction estimates supplied by the weighted construction.
  have _hr : r < 1 := hr
  exact ⟨L.adaptedSeminorm_isEquivalent r hρ, L.adaptedSeminorm_isContracting r hρ⟩

end Normed

end LinearMap
