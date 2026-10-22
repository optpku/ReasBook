/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_11.WeightedSeries
public import Mathlib.Algebra.Module.Submodule.Range

public section

/-!
Remark 7.11 (alternate source-condition discussion).

This item is formalized conservatively as source-facing bridge theorems in the
existing `ContinuousLinearMap.SingularSystem` layer. The item-owned foundation
module `Remark_7_11.WeightedSeries` exposes the `(7.54)` weighted source series
and its decay-threshold companion, while this target adds the Section 1.2.2
range-membership bridge. Under the Chapter 7 algebraic decay laws `(7.49)` and
`(7.53)`, summability of `(7.54)` is formalized as equivalent to `q > p + 1`
when the Fourier-side prefactor is nonzero. The exact displayed formula
`(7.55)` remains textually inconsistent in the recovered source, so this item
records the threshold criterion rather than committing to one coordinate-level
Lean encoding of that display.
-/

namespace ContinuousLinearMap.SingularSystem

universe u v

variable {H₁ : Type u} {H₂ : Type v}
variable [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
variable {K : H₁ →L[ℝ] H₂}

/-- Helper for Remark 7.11: when `S.length = ⊤`, the Chapter 7 positive-index
enumeration exhausts the singular-system index type. -/
private noncomputable def positiveIndexEquiv
    (S : SingularSystem K) (h_length : S.length = ⊤) : ℕ+ ≃ S.Index where
  toFun := S.positiveIndex h_length
  invFun := fun j ↦ j.1.toNat.succPNat
  left_inv := by
    intro i
    apply PNat.coe_injective
    simp [positiveIndex]
  right_inv := by
    intro j
    have hj_lt : (j : ℕ∞) < ⊤ := by
      simpa [h_length] using j.2
    apply Subtype.ext
    have hj_ne_top : (j : ℕ∞) ≠ ⊤ := ne_of_lt hj_lt
    simp [positiveIndex, ENat.coe_toNat hj_ne_top]

/-- Helper for Remark 7.11: on vectors coming from `K.range.topologicalClosure`,
the weighted source series is exactly the square-summable left-basis
coefficient sequence. -/
private theorem weightedSourceSeries_adjoint_apply
    (S : SingularSystem K) (h_length : S.length = ⊤)
    (y : K.range.topologicalClosure) (i : ℕ+) :
    S.weightedSourceSeries h_length (K.adjoint (y : H₂)) i =
      (inner ℝ (S.leftBasis (S.positiveIndex h_length i) : H₂) (y : H₂)) ^ 2 := by
  have hs_ne : S.singularValueSequence h_length i ≠ 0 := by
    exact ne_of_gt (S.singularValue_pos (S.positiveIndex h_length i))
  have hcoeff :
      S.generalizedFourierCoefficientSequence h_length (K.adjoint (y : H₂)) i =
        S.singularValueSequence h_length i *
          inner ℝ (S.leftBasis (S.positiveIndex h_length i) : H₂) (y : H₂) := by
    -- Rewrite the adjoint coefficient through the singular-system relation.
    rw [generalizedFourierCoefficientSequence, singularValueSequence]
    rw [K.adjoint_inner_right, S.map_right]
    simpa using
      (inner_smul_left
        (r := (S.singularValue (S.positiveIndex h_length i) : ℝ))
        (x := (S.leftBasis (S.positiveIndex h_length i) : H₂))
        (y := (y : H₂)))
  -- Cancel the nonzero singular value after rewriting the numerator.
  rw [weightedSourceSeries_apply, hcoeff]
  field_simp [hs_ne]

/-- Helper for Remark 7.11: summability of the weighted source series produces
an element of `K.range.topologicalClosure` with the normalized right-basis
coefficients prescribed by `fTrue`. -/
private theorem closureWitnessOfWeightedSourceSeriesSummable
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁)
    (hs : Summable (S.weightedSourceSeries h_length fTrue)) :
    ∃ y : K.range.topologicalClosure, ∀ j : S.Index,
      inner ℝ (S.leftBasis j : H₂) (y : H₂) =
        inner ℝ (S.rightBasis j : H₁) fTrue / S.singularValue j := by
  let e : ℕ+ ≃ S.Index := positiveIndexEquiv S h_length
  let coeff : S.Index → ℝ := fun j ↦
    inner ℝ (S.rightBasis j : H₁) fTrue / S.singularValue j
  have hs_reindexed :
      Summable fun j : S.Index ↦ S.weightedSourceSeries h_length fTrue (e.symm j) :=
    e.symm.summable_iff.mpr hs
  have hcoeffSq :
      Summable fun j : S.Index ↦ (coeff j) ^ 2 := by
    refine hs_reindexed.congr ?_
    intro j
    have hj_lt : (j : ℕ∞) < ⊤ := by
      simpa [h_length] using j.2
    have hindex : S.natIndex h_length (e.symm j).natPred = j := by
      apply Subtype.ext
      simp [e, positiveIndexEquiv, ENat.coe_toNat (ne_of_lt hj_lt)]
    have hs_ne : S.singularValue j ≠ 0 := ne_of_gt (S.singularValue_pos j)
    -- Route correction: rewrite the weighted series at the transported index
    -- once, then convert it to the square of the normalized coefficient.
    rw [weightedSourceSeries_apply, generalizedFourierCoefficientSequence_apply,
      singularValueSequence_apply, hindex]
    dsimp [coeff]
    field_simp [hs_ne]
  have hcoeffMem :
      Memℓp coeff (2 : ENNReal) := by
    have hcoeffNorm :
        Summable fun j : S.Index ↦ ‖coeff j‖ ^ (2 : ℝ) := by
      simpa [sq_abs] using hcoeffSq
    rw [memℓp_gen_iff (p := (2 : ENNReal)) (by norm_num : 0 < ((2 : ENNReal).toReal))]
    simpa using hcoeffNorm
  let coeffVec : lp (fun _ : S.Index ↦ ℝ) 2 := ⟨coeff, hcoeffMem⟩
  refine ⟨S.leftBasis.repr.symm coeffVec, ?_⟩
  intro j
  -- Read off the chosen coefficients from the Hilbert-basis representation.
  have hrepr_raw :
      S.leftBasis.repr (S.leftBasis.repr.symm coeffVec) = coeffVec := by
    exact S.leftBasis.repr.apply_symm_apply coeffVec
  calc
    inner ℝ (S.leftBasis j : H₂) (S.leftBasis.repr.symm coeffVec : H₂)
        = S.leftBasis.repr (S.leftBasis.repr.symm coeffVec) j := by
            symm
            exact HilbertBasis.repr_apply_apply S.leftBasis (S.leftBasis.repr.symm coeffVec) j
    _ = coeffVec j := by
          exact congrArg (fun f : lp (fun _ : S.Index ↦ ℝ) 2 => f j) hrepr_raw
    _ = inner ℝ (S.rightBasis j : H₁) fTrue / S.singularValue j := by
          rfl

/-- Helper for Remark 7.11: once a closure witness has the normalized
left-basis coefficients dictated by `fTrue`, its adjoint image is exactly
`fTrue`. -/
private theorem adjoint_eq_of_leftBasisCoefficients
    (S : SingularSystem K) (_h_length : S.length = ⊤) (fTrue : H₁)
    (h_mem_kerOrth : fTrue ∈ K.kerᗮ)
    (y : K.range.topologicalClosure)
    (hy : ∀ j : S.Index,
      inner ℝ (S.leftBasis j : H₂) (y : H₂) =
        inner ℝ (S.rightBasis j : H₁) fTrue / S.singularValue j) :
    K.adjoint (y : H₂) = fTrue := by
  have hy_adjoint_mem : K.adjoint (y : H₂) ∈ K.kerᗮ := by
    -- Vectors in `K.range.topologicalClosure` map into `K.kerᗮ` under the adjoint.
    rw [K.orthogonal_ker]
    exact subset_closure ⟨(y : H₂), rfl⟩
  let lhs : K.kerᗮ := ⟨K.adjoint (y : H₂), hy_adjoint_mem⟩
  let rhs : K.kerᗮ := ⟨fTrue, h_mem_kerOrth⟩
  have hrepr : lhs = rhs := by
    apply S.rightBasis.repr.injective
    ext j
    have hs_ne : S.singularValue j ≠ 0 := ne_of_gt (S.singularValue_pos j)
    -- Compare the right-basis coefficients on `K.kerᗮ`.
    calc
      S.rightBasis.repr lhs j
          = inner ℝ (S.rightBasis j : H₁) (K.adjoint (y : H₂)) := by
              simpa [lhs] using (HilbertBasis.repr_apply_apply S.rightBasis lhs j)
      _ = inner ℝ (K (S.rightBasis j : H₁)) (y : H₂) := by
            rw [K.adjoint_inner_right]
      _ = inner ℝ ((S.singularValue j : ℝ) • (S.leftBasis j : H₂)) (y : H₂) := by
            simpa using congrArg (fun x : H₂ ↦ inner ℝ x (y : H₂)) (S.map_right j)
      _ = S.singularValue j * inner ℝ (S.leftBasis j : H₂) (y : H₂) := by
            simpa using
              (inner_smul_left
                (r := (S.singularValue j : ℝ))
                (x := (S.leftBasis j : H₂))
                (y := (y : H₂)))
      _ = S.singularValue j * (inner ℝ (S.rightBasis j : H₁) fTrue / S.singularValue j) := by
            rw [hy j]
      _ = inner ℝ (S.rightBasis j : H₁) fTrue := by
            field_simp [hs_ne]
      _ = S.rightBasis.repr rhs j := by
            simpa [rhs] using (HilbertBasis.repr_apply_apply S.rightBasis rhs j).symm
  exact congrArg (fun z : K.kerᗮ ↦ (z : H₁)) hrepr

/-- Remark 7.11 (1). In the Section 1.2.2 source-condition setting, after
restricting to the orthogonal complement `K.kerᗮ`, `fTrue ∈ K.adjoint.range` is
equivalent to finiteness of the weighted singular-system coefficient series
from `(7.54)`. -/
theorem adjoint_mem_range_iff_weightedSourceSeriesSummable
    (S : SingularSystem K) (h_length : S.length = ⊤) (fTrue : H₁)
    (h_mem_kerOrth : fTrue ∈ K.kerᗮ) :
    fTrue ∈ K.adjoint.range ↔ Summable (S.weightedSourceSeries h_length fTrue) := by
  constructor
  · rintro ⟨g, rfl⟩
    let y : K.range.topologicalClosure := K.range.topologicalClosure.orthogonalProjectionOnto g
    let z : K.range.topologicalClosureᗮ := K.range.topologicalClosureᗮ.orthogonalProjectionOnto g
    have hy_eq : (y : H₂) = K.range.topologicalClosure.starProjection g := by
      rfl
    have hz_eq : (z : H₂) = K.range.topologicalClosureᗮ.starProjection g := by
      rfl
    have hy_split :
        (y : H₂) + (z : H₂) = g := by
      calc
        (y : H₂) + (z : H₂)
            = K.range.topologicalClosure.starProjection g +
                K.range.topologicalClosureᗮ.starProjection g := by
                  rw [hy_eq, hz_eq]
        _ = g := K.range.topologicalClosure.starProjection_add_starProjection_orthogonal g
    have hz_closureOrth : (z : H₂) ∈ K.range.topologicalClosureᗮ := z.property
    have hz_orth : (z : H₂) ∈ K.rangeᗮ := by
      simpa [Submodule.orthogonal_closure] using hz_closureOrth
    have hz_zero : K.adjoint (z : H₂) = 0 := by
      -- The orthogonal complement of the range is exactly the kernel of `K.adjoint`.
      have hz_ker : (z : H₂) ∈ K.adjoint.ker := by
        simpa [K.orthogonal_range] using hz_orth
      exact LinearMap.mem_ker.mp hz_ker
    have h_adjoint_eq :
        K.adjoint g = K.adjoint (y : H₂) := by
      -- Replace the witness by its range-closure component.
      calc
        K.adjoint g = K.adjoint ((y : H₂) + (z : H₂)) := by
          rw [hy_split]
        _ = K.adjoint (y : H₂) + K.adjoint (z : H₂) := by
          rw [map_add]
        _ = K.adjoint (y : H₂) := by simp [hz_zero]
    let e : ℕ+ ≃ S.Index := positiveIndexEquiv S h_length
    have hy_summable_idx :
        Summable fun j : S.Index ↦
          inner ℝ (S.leftBasis j : H₂) (y : H₂) *
            inner ℝ (S.leftBasis j : H₂) (y : H₂) := by
      simpa [real_inner_comm] using S.leftBasis.summable_inner_mul_inner y y
    have hy_summable :
        Summable fun i : ℕ+ ↦
          (inner ℝ (S.leftBasis (S.positiveIndex h_length i) : H₂) (y : H₂)) ^ 2 := by
      have := e.summable_iff.mpr hy_summable_idx
      refine this.congr ?_
      intro i
      change inner ℝ (S.leftBasis (e i) : H₂) (y : H₂) *
          inner ℝ (S.leftBasis (e i) : H₂) (y : H₂) =
        (inner ℝ (S.leftBasis (S.positiveIndex h_length i) : H₂) (y : H₂)) ^ 2
      rw [show e i = S.positiveIndex h_length i by rfl, pow_two]
    have hy_weighted :
        Summable (S.weightedSourceSeries h_length (K.adjoint (y : H₂))) := by
      exact hy_summable.congr (fun i ↦ (weightedSourceSeries_adjoint_apply S h_length y i).symm)
    have hweighted_eq :
        S.weightedSourceSeries h_length (K.adjoint g) =
          S.weightedSourceSeries h_length (K.adjoint (y : H₂)) := by
      ext i
      simp [weightedSourceSeries, generalizedFourierCoefficientSequence, h_adjoint_eq]
    -- Rewrite the weighted series using the projected witness.
    exact hweighted_eq.symm ▸ hy_weighted
  · intro hs
    rcases closureWitnessOfWeightedSourceSeriesSummable S h_length fTrue hs with ⟨y, hy⟩
    refine ⟨(y : H₂), ?_⟩
    -- The constructed closure witness has exactly the right adjoint image.
    exact adjoint_eq_of_leftBasisCoefficients S h_length fTrue h_mem_kerOrth y hy

/-
Remark 7.11 display note. The recovered displayed equation `(7.55)` is still
textually inconsistent, so this file does not fix one coordinate-level Lean
formula for that display. Instead it exposes the source-prose threshold bridge
through `weightedSourceSeriesSummable_iff_decayThreshold` on the concrete owner
`ContinuousLinearMap.SingularSystem.weightedSourceSeries`.
-/

#check weightedSourceSeries

#check weightedSourceSeriesSummable_iff_decayThreshold

end ContinuousLinearMap.SingularSystem
