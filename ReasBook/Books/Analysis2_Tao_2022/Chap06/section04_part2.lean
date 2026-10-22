/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap06.section04_part1

section Chap06
section Section04

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch, if one
assumes canonicity of within-derivative witnesses for `g ∘ f` at `x0`, then
the matrix identity follows. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_assumedCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  have hWitnessForm :
      DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
        ∃ L : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
          HasFDerivWithinAt (g ∘ f) L E x0 ∧
            LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
                L.toLinearMap =
              LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
                  (fderivWithin ℝ g F (f x0)).toLinearMap *
                LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
                  (fderivWithin ℝ f E x0).toLinearMap := by
    refine ⟨?_, ?_⟩
    · exact
        helperForTheorem_6_4_matrixForm_chainRule_differentiableWithin
          hMaps hf hg
    · refine
        ⟨(fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0), ?_, ?_⟩
      · exact
          helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives
            hMaps hf hg
      · simpa using
          (LinearMap.toMatrix_comp
            (Pi.basisFun ℝ (Fin n))
            (Pi.basisFun ℝ (Fin m))
            (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap
            (fderivWithin ℝ f E x0).toLinearMap)
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_witnessForm_and_canonicity
      hWitnessForm.1 hWitnessForm.2 hCanonicity

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch, an assumed
canonicity principle for within-derivative witnesses yields the full
conclusion pair (within-set differentiability and matrix identity). -/
theorem helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_not_uniqueDiff_of_assumedCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_differentiableWithin
        hMaps hf hg
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_assumedCanonicity
        hMaps hf hg hCanonicity

/-- Helper for Theorem 6.4: adding explicit pointwise canonicity for
within-derivative witnesses of `g ∘ f` yields the full matrix-form chain-rule
conclusion. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_with_pointCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hPointCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  by_cases hUnique : UniqueDiffWithinAt ℝ E x0
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_uniqueDiff
        hMaps hf hg hUnique
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_not_uniqueDiff_of_assumedCanonicity
        hMaps hf hg hPointCanonicity

/-- Helper for Theorem 6.4: if either `f` or `g` admits zero as a
within-derivative at the relevant basepoint, the matrix identity follows from
the corresponding zero-derivative fallback branch. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_f_or_g
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hZeroDerivFG :
      HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0 ∨
        HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  rcases hZeroDerivFG with hZeroDerivF | hZeroDerivG
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_from_fderivWithin_comp
        (helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_or_hasFDerivWithinAt_zero
          hMaps hf hg (Or.inr hZeroDerivF))
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_right
        hMaps hf hZeroDerivG

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch, proving the
matrix identity reduces to the residual case where neither zero-derivative
fallback applies for `f` or `g`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_by_zeroFallbackSplit
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hResidual :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0 →
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0) →
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  by_cases hZeroDerivF : HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_f_or_g
        hMaps hf hg (Or.inl hZeroDerivF)
  · by_cases hZeroDerivG :
        HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)
    · exact
        helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_f_or_g
          hMaps hf hg (Or.inr hZeroDerivG)
    · exact hResidual hZeroDerivF hZeroDerivG

/-- Helper for Theorem 6.4: proving the non-`UniqueDiffWithinAt` matrix
identity can be reduced to supplying a canonicity generator for the residual
branch where both zero-derivative fallbacks are excluded. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_residualCanonicityGenerator
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hResidualCanonicity :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0 →
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0) →
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  refine
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_by_zeroFallbackSplit
      hMaps hf hg ?_
  intro hNotZeroDerivF hNotZeroDerivG
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_nonzeroFallbacks_of_canonicity
      hMaps hf hg hNotZeroDerivF hNotZeroDerivG
      (hResidualCanonicity hNotZeroDerivF hNotZeroDerivG)

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch, proving the
matrix identity is reduced to providing pointwise canonicity of
within-derivative witnesses for `g ∘ f` at `x0`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_reducedToPointCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0)) :
    (∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
      HasFDerivWithinAt (g ∘ f) L1 E x0 →
      HasFDerivWithinAt (g ∘ f) L2 E x0 →
      L1 = L2) →
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  intro hPointCanonicity
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_assumedCanonicity
      hMaps hf hg hPointCanonicity

/-- Helper for Theorem 6.4: pointwise canonicity of within-derivative
witnesses for `g ∘ f` at `x0` yields equality between the selected
within-derivative and the composed selected within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_pointCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hPointCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  have hDerivSelected :
      HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 := by
    exact (hg.comp x0 hf hMaps).hasFDerivWithinAt
  have hDerivComp :
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives
        hMaps hf hg
  exact
    helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_twoHasFDerivWithinAt_witnesses_and_canonicity
      hDerivSelected hDerivComp hPointCanonicity

/-- Helper for Theorem 6.4: pointwise canonicity of within-derivative
witnesses for `g ∘ f` at `x0` yields the matrix identity directly. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_pointCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hPointCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  have hcomp :
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_pointCanonicity
        hMaps hf hg hPointCanonicity
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: if either `f` has zero within-derivative at `x0`
or `g` has zero within-derivative at `f x0`, then the matrix identity follows
from the corresponding zero-derivative branch. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_zeroDerivativeFallback
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hZeroDeriv :
      HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0 ∨
      HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  rcases hZeroDeriv with hZeroDerivF | hZeroDerivG
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero
        hMaps hg hZeroDerivF
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_right
        hMaps hf hZeroDerivG

/-- Helper for Theorem 6.4: remaining matrix-identity branch under
`¬ UniqueDiffWithinAt ℝ E x0`; this is the unresolved structural blocker. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_pointCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hPointCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_reducedToPointCanonicity
      hMaps hf hg hPointCanonicity

/-- Helper for Theorem 6.4: remaining matrix-identity branch under
`¬ UniqueDiffWithinAt ℝ E x0`, assuming a supplied pointwise canonicity
principle for within-derivative witnesses of `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hx0 : x0 ∈ E)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hfx0 : f x0 ∈ F)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotUnique : ¬ UniqueDiffWithinAt ℝ E x0)
    (hPointCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_pointCanonicity
      hMaps hf hg hPointCanonicity

/-- Helper for Theorem 6.4: with the exact hypotheses of `matrixForm_chainRule`
and an added `UniqueDiffWithinAt` hypothesis, the full conclusion follows. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_conclusion_with_uniqueDiff_mainHypotheses
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_uniqueDiff
      hMaps hf hg hUnique

/-- Helper for Theorem 6.4: a repaired variant of the theorem statement that
adds `UniqueDiffWithinAt` to ensure canonicity of within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_with_uniqueDiff
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_conclusion_with_uniqueDiff_mainHypotheses
      hMaps hf hg hUnique

/-- Helper for Theorem 6.4: a witness-form chain-rule conclusion that avoids
non-canonical selection of `fderivWithin` for `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_witnessForm
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0)) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      ∃ L : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L E x0 ∧
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
              L.toLinearMap =
            LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
                (fderivWithin ℝ g F (f x0)).toLinearMap *
              LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
                (fderivWithin ℝ f E x0).toLinearMap := by
  refine ⟨?_, ?_⟩
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_differentiableWithin
        hMaps hf hg
  · refine
      ⟨(fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0), ?_, ?_⟩
    · exact
        helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives
          hMaps hf hg
    · simpa using
        (LinearMap.toMatrix_comp
          (Pi.basisFun ℝ (Fin n))
          (Pi.basisFun ℝ (Fin m))
          (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap
          (fderivWithin ℝ f E x0).toLinearMap)

/-- Theorem 6.4: (Matrix form of the chain rule) let `E ⊆ ℝⁿ` and `F ⊆ ℝᵐ`,
`f : E → ℝᵐ`, and `g : F → ℝᵖ`. Assume `x₀ ∈ E`,
`f x₀ ∈ F`, `f` is differentiable within `E` at `x₀`, `g` is
differentiable within `F` at `f x₀`, and `f` maps `E` into `F`. Assume also
`UniqueDiffWithinAt ℝ E x₀` so the selected within-derivative is canonical.
Then `g ∘ f` is differentiable within `E` at `x₀`, and its within-derivative
matrix satisfies `D(g ∘ f)(x₀) = Dg(f(x₀)) Df(x₀)`. -/
theorem matrixForm_chainRule
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hx0 : x0 ∈ E)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hfx0 : f x0 ∈ F)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 ∧
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_with_uniqueDiff
      hMaps hf hg hUnique

end Section04
end Chap06
