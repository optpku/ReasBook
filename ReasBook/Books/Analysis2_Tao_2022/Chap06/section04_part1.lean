/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section04

/-- Theorem 6.3 (Several variable calculus chain rule): let `E ⊆ ℝⁿ` and `F ⊆ ℝᵐ`,
`f : E → F`, and `g : F → ℝᵖ`. If `x₀` is an interior point of `E` and `f` is
differentiable at `x₀`, and if `f x₀` is an interior point of `F` and `g` is
differentiable at `f x₀`, then `g ∘ f` is differentiable at `x₀` and
`(g ∘ f)'(x₀) = g'(f(x₀)) ∘ f'(x₀)`. -/
theorem severalVariableCalculus_chainRule
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (h_map : Set.MapsTo f E F)
    (hx0 : x0 ∈ interior E)
    (hf : DifferentiableAt ℝ f x0)
    (hfx0 : f x0 ∈ interior F)
    (hg : DifferentiableAt ℝ g (f x0)) :
    DifferentiableAt ℝ (g ∘ f) x0 ∧
      fderiv ℝ (g ∘ f) x0 = (fderiv ℝ g (f x0)).comp (fderiv ℝ f x0) := by
  constructor
  · exact hg.comp x0 hf
  · simpa using fderiv_comp x0 hg hf

/-- Helper for Theorem 6.4: a matrix identity follows from the corresponding
within-derivative composition identity. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hcomp :
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  rw [hcomp]
  simpa using
    (LinearMap.toMatrix_comp
      (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin p))
      (fderivWithin ℝ g F (f x0)).toLinearMap
      (fderivWithin ℝ f E x0).toLinearMap)

/-- Helper for Theorem 6.4: the matrix identity in the chain-rule statement
is equivalent to the corresponding equality of selected within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_iff_fderivWithin_comp
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ} :
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ g F (f x0)).toLinearMap *
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
            (fderivWithin ℝ f E x0).toLinearMap) ↔
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  constructor
  · intro hMatrix
    have hLinearEq :
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
          (fderivWithin ℝ g F (f x0)).toLinearMap.comp
            (fderivWithin ℝ f E x0).toLinearMap := by
      apply (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))).injective
      calc
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
            (fderivWithin ℝ (g ∘ f) E x0).toLinearMap
            =
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
              (fderivWithin ℝ g F (f x0)).toLinearMap *
            LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
              (fderivWithin ℝ f E x0).toLinearMap := hMatrix
        _ =
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
            ((fderivWithin ℝ g F (f x0)).toLinearMap.comp
              (fderivWithin ℝ f E x0).toLinearMap) := by
          simpa using
            (LinearMap.toMatrix_comp
              (Pi.basisFun ℝ (Fin n))
              (Pi.basisFun ℝ (Fin m))
              (Pi.basisFun ℝ (Fin p))
              (fderivWithin ℝ g F (f x0)).toLinearMap
              (fderivWithin ℝ f E x0).toLinearMap).symm
    ext x i
    simpa using congrArg (fun L : (Fin n → ℝ) →ₗ[ℝ] (Fin p → ℝ) => L x i) hLinearEq
  · intro hcomp
    exact
      helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
        hcomp

/-- Helper for Theorem 6.4: composing the selected within-derivatives of `g`
and `f` gives a within-derivative of `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0)) :
    HasFDerivWithinAt (g ∘ f)
      ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  exact hg.hasFDerivWithinAt.comp x0 hf.hasFDerivWithinAt hMaps

/-- Helper for Theorem 6.4: on a `UniqueDiffWithinAt` set, any two
within-derivative witnesses for the same map at the same point are equal. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_eq_of_two_hasFDerivWithinAt_of_uniqueDiff
    {n p : ℕ}
    {E : Set (Fin n → ℝ)}
    {h : (Fin n → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    {L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)}
    (hL1 : HasFDerivWithinAt h L1 E x0)
    (hL2 : HasFDerivWithinAt h L2 E x0)
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    L1 = L2 := by
  have hEq1 : fderivWithin ℝ h E x0 = L1 := by
    exact hL1.fderivWithin hUnique
  have hEq2 : fderivWithin ℝ h E x0 = L2 := by
    exact hL2.fderivWithin hUnique
  exact hEq1.symm.trans hEq2

/-- Helper for Theorem 6.4: `UniqueDiffWithinAt` provides a canonicity
principle for within-derivative witnesses at a fixed point. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_canonicity_of_uniqueDiff
    {n p : ℕ}
    {E : Set (Fin n → ℝ)}
    {h : (Fin n → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
      HasFDerivWithinAt h L1 E x0 →
      HasFDerivWithinAt h L2 E x0 →
      L1 = L2 := by
  intro L1 L2 hL1 hL2
  exact
    helperForTheorem_6_4_matrixForm_chainRule_eq_of_two_hasFDerivWithinAt_of_uniqueDiff
      hL1 hL2 hUnique

/-- Helper for Theorem 6.4: to prove the selected within-derivative
composition identity, it is enough to have the two derivative witnesses and a
canonicity principle identifying any two such witnesses. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_twoHasFDerivWithinAt_witnesses_and_canonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hDerivSelected :
      HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0)
    (hDerivComp :
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0)
    (hCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  exact hCanonicity _ _ hDerivSelected hDerivComp

/-- Helper for Theorem 6.4: under `UniqueDiffWithinAt`, the selected
within-derivative of `g ∘ f` agrees with the composition of selected
within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_from_selectedWithinDerivatives
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
  have hCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2 := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_canonicity_of_uniqueDiff
        hUnique
  exact
    helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_twoHasFDerivWithinAt_witnesses_and_canonicity
      hDerivSelected hDerivComp hCanonicity

/-- Helper for Theorem 6.4: under `UniqueDiffWithinAt`, the within-derivative
matrix of a composition is the product of within-derivative matrices. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_of_uniqueDiff
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
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_from_selectedWithinDerivatives
        hMaps hf hg hUnique
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: under `UniqueDiffWithinAt`, both the within-set
chain-rule differentiability and the matrix identity hold. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_uniqueDiff
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
  refine ⟨?_, ?_⟩
  · exact hg.comp x0 hf hMaps
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_of_uniqueDiff
        hMaps hf hg hUnique

/-- Helper for Theorem 6.4: the within-set differentiability conclusion for
the composition `g ∘ f` does not require `UniqueDiffWithinAt`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_differentiableWithin
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0)) :
    DifferentiableWithinAt ℝ (g ∘ f) E x0 := by
  exact hg.comp x0 hf hMaps

/-- Helper for Theorem 6.4: under `UniqueDiffWithinAt`, the matrix identity in
Theorem 6.4 is obtained from the corresponding conjunction helper. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_uniqueDiff
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
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    (helperForTheorem_6_4_matrixForm_chainRule_conclusion_of_uniqueDiff
      hMaps hf hg hUnique
    ).2

/-- Helper for Theorem 6.4: with the exact hypotheses of `matrixForm_chainRule`,
the matrix identity follows in the `UniqueDiffWithinAt` branch. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_uniqueDiff_mainHypotheses
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
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_uniqueDiff
      hMaps hf hg hUnique

/-- Helper for Theorem 6.4: if `f` has zero within-derivative at `x0`, then the
matrix identity for the chain rule holds. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hZeroDerivF : HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  have hZeroDerivComp :
      HasFDerivWithinAt (g ∘ f) (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) E x0 := by
    simpa using (hg.hasFDerivWithinAt.comp x0 hZeroDerivF hMaps)
  have hfderivWithinFZero :
      fderivWithin ℝ f E x0 = (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) := by
    simp [fderivWithin, hZeroDerivF]
  have hfderivWithinCompZero :
      fderivWithin ℝ (g ∘ f) E x0 = (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) := by
    simp [fderivWithin, hZeroDerivComp]
  rw [hfderivWithinCompZero, hfderivWithinFZero]
  simp

/-- Helper for Theorem 6.4: if either `UniqueDiffWithinAt` holds at `x0` or
`f` has zero within-derivative at `x0`, then the selected within-derivative of
`g ∘ f` is the composition of selected within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_or_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hUniqueOrZero :
      UniqueDiffWithinAt ℝ E x0 ∨
        HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  rcases hUniqueOrZero with hUnique | hZeroDerivF
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_from_selectedWithinDerivatives
        hMaps hf hg hUnique
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero
        hMaps hg hZeroDerivF

/-- Helper for Theorem 6.4: if `f` has zero within-derivative at `x0`, then the
matrix identity for the chain rule holds. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hZeroDerivF : HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0) :
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
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero
        hMaps hg hZeroDerivF
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: if `g` has zero within-derivative at `f x0`, then
the selected within-derivative of `g ∘ f` equals the composition of selected
within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero_right
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hZeroDerivG :
      HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  have hZeroDerivComp :
      HasFDerivWithinAt (g ∘ f) (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) E x0 := by
    simpa using (hZeroDerivG.comp x0 hf.hasFDerivWithinAt hMaps)
  have hfderivWithinCompZero :
      fderivWithin ℝ (g ∘ f) E x0 = (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) := by
    simp [fderivWithin, hZeroDerivComp]
  have hfderivWithinGZero :
      fderivWithin ℝ g F (f x0) = (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) := by
    simp [fderivWithin, hZeroDerivG]
  rw [hfderivWithinCompZero, hfderivWithinGZero]
  simp

/-- Helper for Theorem 6.4: if `g` has zero within-derivative at `f x0`, then
the matrix identity for the chain rule holds. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_right
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hZeroDerivG :
      HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
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
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero_right
        hMaps hf hZeroDerivG
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: for `g ∘ f`, both the selected within-derivative
and the composition of selected within-derivatives are valid within-derivatives. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_twoHasFDerivWithinAt_witnesses
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0)) :
    HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 ∧
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  refine ⟨?_, ?_⟩
  · exact (hg.comp x0 hf hMaps).hasFDerivWithinAt
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives
        hMaps hf hg

/-- Helper for Theorem 6.4: if zero is not a within-derivative and `h` is
within-differentiable at `x0`, then `fderivWithin` is the derivative selected
by `Classical.choose` from that differentiability witness. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_eq_choose_of_not_hasFDerivWithinAt_zero
    {n p : ℕ}
    {E : Set (Fin n → ℝ)}
    {h : (Fin n → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hh : DifferentiableWithinAt ℝ h E x0)
    (hNotZeroDerivH :
      ¬ HasFDerivWithinAt h (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) E x0) :
    fderivWithin ℝ h E x0 = Classical.choose hh := by
  simp [fderivWithin, hNotZeroDerivH, hh]

/-- Helper for Theorem 6.4: when zero is not a valid within-derivative for
`f` and `g`, the composition of selected within-derivatives is itself a
within-derivative of `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives_of_eq_choose
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hfEqChoose : fderivWithin ℝ f E x0 = Classical.choose hf)
    (hgEqChoose : fderivWithin ℝ g F (f x0) = Classical.choose hg) :
    HasFDerivWithinAt (g ∘ f)
      ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  rw [hfEqChoose, hgEqChoose]
  exact (Classical.choose_spec hg).comp x0 (Classical.choose_spec hf) hMaps

/-- Helper for Theorem 6.4: when zero is not a valid within-derivative for
`f` and `g`, the composition of selected within-derivatives is itself a
within-derivative of `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives_of_not_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    HasFDerivWithinAt (g ∘ f)
      ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  have hfEqChoose :
      fderivWithin ℝ f E x0 = Classical.choose hf := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_eq_choose_of_not_hasFDerivWithinAt_zero
        hf hNotZeroDerivF
  have hgEqChoose :
      fderivWithin ℝ g F (f x0) = Classical.choose hg := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_eq_choose_of_not_hasFDerivWithinAt_zero
        hg hNotZeroDerivG
  exact
    helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives_of_eq_choose
      hMaps hf hg hfEqChoose hgEqChoose

/-- Helper for Theorem 6.4: when zero is not a within-derivative for both
`f` and `g`, the selected within-derivative of `g ∘ f` and the composition of
the selected within-derivatives are both valid within-derivative witnesses. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_twoHasFDerivWithinAt_witnesses_of_not_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 ∧
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  refine ⟨?_, ?_⟩
  · exact (hg.comp x0 hf hMaps).hasFDerivWithinAt
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_comp_of_selectedWithinDerivatives_of_not_hasFDerivWithinAt_zero
        hMaps hf hg hNotZeroDerivF hNotZeroDerivG

/-- Helper for Theorem 6.4: when zero is not a within-derivative for both
`f` and `g`, the selected within-derivative of `g ∘ f` is a valid
within-derivative witness. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_selectedWitness_of_not_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 := by
  exact
    (helperForTheorem_6_4_matrixForm_chainRule_twoHasFDerivWithinAt_witnesses_of_not_hasFDerivWithinAt_zero
      hMaps hf hg hNotZeroDerivF hNotZeroDerivG).1

/-- Helper for Theorem 6.4: when zero is not a within-derivative for both
`f` and `g`, the composition of selected within-derivatives is a valid
within-derivative witness for `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_compWitness_of_not_hasFDerivWithinAt_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
    HasFDerivWithinAt (g ∘ f)
      ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
  exact
    (helperForTheorem_6_4_matrixForm_chainRule_twoHasFDerivWithinAt_witnesses_of_not_hasFDerivWithinAt_zero
      hMaps hf hg hNotZeroDerivF hNotZeroDerivG).2

/-- Helper for Theorem 6.4: if `f` is differentiable within `E` at `x0` and
`f` does not admit zero as a within-derivative there, then the selected
within-derivative `fderivWithin` is nonzero. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_ne_zero_of_not_hasFDerivWithinAt_zero
    {n m : ℕ}
    {E : Set (Fin n → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x0 : Fin n → ℝ}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0) :
    fderivWithin ℝ f E x0 ≠ (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) := by
  intro hEqZero
  apply hNotZeroDerivF
  exact hEqZero ▸ hf.hasFDerivWithinAt

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch, once the
selected within-derivative composition identity is available, the matrix
identity follows immediately. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_from_fderivWithin_comp
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hcomp :
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: if `g ∘ f` admits zero as a within-derivative and
the composition of selected within-derivatives is also zero, then the matrix
identity follows immediately. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_hasFDerivWithinAt_zero_and_comp_eq_zero
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hZeroDerivComp :
      HasFDerivWithinAt (g ∘ f) (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) E x0)
    (hCompZero :
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) =
        (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ))) :
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
        (fderivWithin ℝ (g ∘ f) E x0).toLinearMap =
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
          (fderivWithin ℝ g F (f x0)).toLinearMap *
        LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
          (fderivWithin ℝ f E x0).toLinearMap := by
  have hfderivWithinCompZero :
      fderivWithin ℝ (g ∘ f) E x0 = (0 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ)) := by
    simp [fderivWithin, hZeroDerivComp]
  rw [hfderivWithinCompZero, ← hCompZero]
  simpa using
    (LinearMap.toMatrix_comp
      (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin m))
      (Pi.basisFun ℝ (Fin p))
      (fderivWithin ℝ g F (f x0)).toLinearMap
      (fderivWithin ℝ f E x0).toLinearMap)

/-- Helper for Theorem 6.4: if zero is excluded as a within-derivative for
`f` and `g`, then any canonicity principle for within-derivative witnesses of
`g ∘ f` identifies the selected within-derivative with the composed one. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_not_hasFDerivWithinAt_zero_and_canonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0))
    (hCanonicity :
      ∀ L1 L2 : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L1 E x0 →
        HasFDerivWithinAt (g ∘ f) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  have hDerivSelected :
      HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_selectedWitness_of_not_hasFDerivWithinAt_zero
        hMaps hf hg hNotZeroDerivF hNotZeroDerivG
  have hDerivComp :
      HasFDerivWithinAt (g ∘ f)
        ((fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0)) E x0 := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_hasFDerivWithinAt_compWitness_of_not_hasFDerivWithinAt_zero
        hMaps hf hg hNotZeroDerivF hNotZeroDerivG
  exact
    helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_twoHasFDerivWithinAt_witnesses_and_canonicity
      hDerivSelected hDerivComp hCanonicity

/-- Helper for Theorem 6.4: assuming canonicity for within-derivative
witnesses of `g ∘ f`, the selected within-derivative composition identity
follows by splitting on the two zero-derivative fallback branches. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_canonicity_by_zeroFallbackSplit
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
    fderivWithin ℝ (g ∘ f) E x0 =
      (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
  by_cases hZeroDerivF : HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0
  · exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_uniqueDiff_or_hasFDerivWithinAt_zero
        hMaps hf hg (Or.inr hZeroDerivF)
  · by_cases hZeroDerivG :
        HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)
    · exact
        helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_hasFDerivWithinAt_zero_right
          hMaps hf hZeroDerivG
    · exact
        helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_not_hasFDerivWithinAt_zero_and_canonicity
          hMaps hf hg hZeroDerivF hZeroDerivG hCanonicity

/-- Helper for Theorem 6.4: in the non-`UniqueDiffWithinAt` branch with zero
within-derivatives excluded for `f` and `g`, the matrix identity follows from
the same canonicity principle used to identify derivative witnesses. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_not_hasFDerivWithinAt_zero_and_canonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0))
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
  have hcomp :
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_not_hasFDerivWithinAt_zero_and_canonicity
        hMaps hf hg hNotZeroDerivF hNotZeroDerivG hCanonicity
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_from_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: once canonicity for within-derivative witnesses
of `g ∘ f` is available, the matrix identity follows by splitting on whether
`f` or `g` admit the zero within-derivative at the relevant basepoints. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_canonicity
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
  have hcomp :
      fderivWithin ℝ (g ∘ f) E x0 =
        (fderivWithin ℝ g F (f x0)).comp (fderivWithin ℝ f E x0) := by
    exact
      helperForTheorem_6_4_matrixForm_chainRule_fderivWithin_comp_of_canonicity_by_zeroFallbackSplit
        hMaps hf hg hCanonicity
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_from_fderivWithin_comp
      hcomp

/-- Helper for Theorem 6.4: once the two zero-derivative fallback branches are
excluded, proving the non-`UniqueDiffWithinAt` matrix identity reduces to a
canonicity statement for within-derivative witnesses of `g ∘ f`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_nonzeroFallbacks_reducedToCanonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0)) :
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
  intro hCanonicity
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_of_not_hasFDerivWithinAt_zero_and_canonicity
      hMaps hf hg hNotZeroDerivF hNotZeroDerivG hCanonicity

/-- Helper for Theorem 6.4: once the two zero-derivative fallback branches are
excluded, any supplied canonicity principle for within-derivative witnesses of
`g ∘ f` yields the non-`UniqueDiffWithinAt` matrix identity directly. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_nonzeroFallbacks_of_canonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hMaps : Set.MapsTo f E F)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (hg : DifferentiableWithinAt ℝ g F (f x0))
    (hNotZeroDerivF :
      ¬ HasFDerivWithinAt f (0 : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) E x0)
    (hNotZeroDerivG :
      ¬ HasFDerivWithinAt g (0 : (Fin m → ℝ) →L[ℝ] (Fin p → ℝ)) F (f x0))
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
  exact
    helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_not_uniqueDiff_nonzeroFallbacks_reducedToCanonicity
      hMaps hf hg hNotZeroDerivF hNotZeroDerivG hCanonicity

/-- Helper for Theorem 6.4: a witness-form matrix identity for `g ∘ f`
upgrades to the selected-`fderivWithin` matrix identity once within-derivative
witnesses are canonical at `x0`. -/
theorem helperForTheorem_6_4_matrixForm_chainRule_matrixIdentity_of_witnessForm_and_canonicity
    {n m p : ℕ}
    {E : Set (Fin n → ℝ)}
    {F : Set (Fin m → ℝ)}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {g : (Fin m → ℝ) → (Fin p → ℝ)}
    {x0 : Fin n → ℝ}
    (hDiffComp : DifferentiableWithinAt ℝ (g ∘ f) E x0)
    (hWitness :
      ∃ L : (Fin n → ℝ) →L[ℝ] (Fin p → ℝ),
        HasFDerivWithinAt (g ∘ f) L E x0 ∧
          LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin p))
              L.toLinearMap =
            LinearMap.toMatrix (Pi.basisFun ℝ (Fin m)) (Pi.basisFun ℝ (Fin p))
                (fderivWithin ℝ g F (f x0)).toLinearMap *
              LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))
                (fderivWithin ℝ f E x0).toLinearMap)
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
  rcases hWitness with ⟨L, hLDeriv, hLMatrix⟩
  have hSelectedDeriv :
      HasFDerivWithinAt (g ∘ f) (fderivWithin ℝ (g ∘ f) E x0) E x0 := by
    exact hDiffComp.hasFDerivWithinAt
  have hSelectedEq : fderivWithin ℝ (g ∘ f) E x0 = L := by
    exact hCanonicity _ _ hSelectedDeriv hLDeriv
  simpa [hSelectedEq] using hLMatrix

end Section04
end Chap06
