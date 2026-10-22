/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap06.section04_part2

section Chap06
section Section04

/-- Helper for Proposition 6.10: pointwise gradient identity for the product of
two differentiable scalar functions on `ℝⁿ`. -/
lemma helperForProposition_6_10_gradientProduct_pointwiseIdentity
    {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun y => f y * g y) x =
      g x • gradient f x + f x • gradient g x := by
  calc
    gradient (fun y => f y * g y) x
        = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
            (fderiv ℝ (fun y => f y * g y) x) := rfl
    _ = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
          (f x • fderiv ℝ g x + g x • fderiv ℝ f x) := by
          rw [fderiv_fun_mul hf hg]
    _ = f x • gradient g x + g x • gradient f x := by
          simp [gradient]
    _ = g x • gradient f x + f x • gradient g x := by
          abel

/-- Helper for Proposition 6.10: packages the pointwise differentiability and
gradient product identity at a fixed point. -/
lemma helperForProposition_6_10_gradientProduct_pointwiseRule
    {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} :
    DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
      DifferentiableAt ℝ (fun y => f y * g y) x ∧
        gradient (fun y => f y * g y) x =
          g x • gradient f x + f x • gradient g x := by
  intro hf hg
  refine ⟨hf.mul hg, ?_⟩
  exact
    helperForProposition_6_10_gradientProduct_pointwiseIdentity
      (f := f) (g := g) (x := x) hf hg

/-- Helper for Proposition 6.10: global differentiability of the product and
the gradient product rule at every point. -/
lemma helperForProposition_6_10_gradientProduct_globalRule
    {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} :
    (Differentiable ℝ f ∧ Differentiable ℝ g) →
      Differentiable ℝ (fun y => f y * g y) ∧
        ∀ y : EuclideanSpace ℝ (Fin n),
          gradient (fun z => f z * g z) y =
            g y • gradient f y + f y • gradient g y := by
  intro hDiff
  rcases hDiff with ⟨hf, hg⟩
  refine ⟨hf.mul hg, ?_⟩
  intro y
  exact
    (helperForProposition_6_10_gradientProduct_pointwiseRule
      (f := f) (g := g) (x := y) (hf y) (hg y)).2

/-- Proposition 6.10 (Product rule for gradients): if `f, g : ℝⁿ → ℝ` are
differentiable at `x`, then `fg` is differentiable at `x` and
`∇(fg)(x) = g(x) • ∇f(x) + f(x) • ∇g(x)`. If `f` and `g` are differentiable on
all of `ℝⁿ`, then `fg` is differentiable on `ℝⁿ` and this identity holds for every
point. -/
theorem gradient_product_rule
    {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    :
    (∀ x : EuclideanSpace ℝ (Fin n),
      DifferentiableAt ℝ f x → DifferentiableAt ℝ g x →
        DifferentiableAt ℝ (fun y => f y * g y) x ∧
          gradient (fun y => f y * g y) x =
            g x • gradient f x + f x • gradient g x) ∧
    ((Differentiable ℝ f ∧ Differentiable ℝ g) →
      Differentiable ℝ (fun y => f y * g y) ∧
        ∀ y : EuclideanSpace ℝ (Fin n),
          gradient (fun z => f z * g z) y =
            g y • gradient f y + f y • gradient g y) := by
  constructor
  · intro x hf hg
    exact
      helperForProposition_6_10_gradientProduct_pointwiseRule
        (f := f) (g := g) (x := x) hf hg
  · intro hDiff
    exact
      helperForProposition_6_10_gradientProduct_globalRule
        (f := f) (g := g) hDiff

/-- Helper for Proposition 6.11: the chain-rule witness for composing a
within-differentiable map with a linear map. -/
theorem helperForProposition_6_11_hasFDerivWithinAt_linearMap_comp
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    HasFDerivWithinAt (fun x => T (f x))
      ((LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)) E x0 := by
  exact
    (LinearMap.toContinuousLinearMap T).hasFDerivAt.comp_hasFDerivWithinAt x0
      hf.hasFDerivWithinAt

/-- Helper for Proposition 6.11: the composition with a linear map is
within-differentiable at the base point. -/
theorem helperForProposition_6_11_differentiableWithinAt_linearMap_comp
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    DifferentiableWithinAt ℝ (fun x => T (f x)) E x0 := by
  exact
    (helperForProposition_6_11_hasFDerivWithinAt_linearMap_comp (hf := hf)
      (T := T)).differentiableWithinAt

/-- Helper for Proposition 6.11: witness-form chain-rule statement for
`fun x => T (f x)` within `E` at `x0`. -/
theorem helperForProposition_6_11_witnessForm_linearMap_comp
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt (fun x => T (f x)) L E x0 ∧
      L = (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  refine
    ⟨(LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0), ?_, rfl⟩
  exact
    helperForProposition_6_11_hasFDerivWithinAt_linearMap_comp (hf := hf)
      (T := T)

/-- Helper for Proposition 6.11: `UniqueDiffWithinAt` gives pointwise
canonicity of within-derivative witnesses for `fun x => T (f x)` at `x0`. -/
theorem helperForProposition_6_11_pointCanonicity_linearMap_comp_of_uniqueDiffWithinAt
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
      HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
      L1 = L2 := by
  intro L1 L2 hL1 hL2
  exact hUnique.eq hL1 hL2

/-- Helper for Proposition 6.11: under `UniqueDiffWithinAt`, the selected
within derivative of `fun x => T (f x)` is
`(LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)`. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_of_uniqueDiffWithinAt
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact
    (helperForProposition_6_11_hasFDerivWithinAt_linearMap_comp (hf := hf)
      (T := T)).fderivWithin hUnique

/-- Helper for Proposition 6.11: with `UniqueDiffWithinAt` at `x0`, the
composition with a linear map is within-differentiable and its selected within
derivative is the composition of selected within derivatives. -/
theorem helperForProposition_6_11_pairResult_of_uniqueDiffWithinAt
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (fun x => T (f x)) E x0 ∧
      fderivWithin ℝ (fun x => T (f x)) E x0 =
        (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForProposition_6_11_differentiableWithinAt_linearMap_comp
        (hf := hf) (T := T)
  · exact
      helperForProposition_6_11_fderivWithin_linearMap_comp_of_uniqueDiffWithinAt
        (hf := hf) (T := T) hUnique

/-- Helper for Proposition 6.11: a dependency-closed provable variant of the
main result under `UniqueDiffWithinAt` at `x0`. -/
theorem helperForProposition_6_11_withUniqueDiff
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (fun x => T (f x)) E x0 ∧
      fderivWithin ℝ (fun x => T (f x)) E x0 =
        (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact
    helperForProposition_6_11_pairResult_of_uniqueDiffWithinAt
      (hf := hf) (T := T) hUnique

/-- Helper for Proposition 6.11: if within-derivative witnesses for
`fun x => T (f x)` are canonical at `x0`, then the selected within derivative
is exactly `(LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)`. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_of_pointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  have hSelected :
      HasFDerivWithinAt (fun x => T (f x))
        (fderivWithin ℝ (fun x => T (f x)) E x0) E x0 := by
    exact
      (helperForProposition_6_11_differentiableWithinAt_linearMap_comp
        (hf := hf) (T := T)).hasFDerivWithinAt
  rcases helperForProposition_6_11_witnessForm_linearMap_comp (hf := hf)
      (T := T) with ⟨L, hLDeriv, hLDef⟩
  have hSelectedEqL : fderivWithin ℝ (fun x => T (f x)) E x0 = L := by
    exact hCanonicity _ _ hSelected hLDeriv
  calc
    fderivWithin ℝ (fun x => T (f x)) E x0 = L := hSelectedEqL
    _ = (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := hLDef

/-- Helper for Proposition 6.11: a zero within-derivative witness for `f` at
`x0` induces a zero within-derivative witness for `fun x => T (f x)`. -/
theorem helperForProposition_6_11_hasFDerivWithinAt_zero_linearMap_comp_of_hasFDerivWithinAt_zero
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hZeroF :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    HasFDerivWithinAt (fun x => T (f x))
      (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) E x0 := by
  simpa using
    (LinearMap.toContinuousLinearMap T).hasFDerivAt.comp_hasFDerivWithinAt x0 hZeroF

/-- Helper for Proposition 6.11: if `f` has zero within-derivative witness at
`x0`, then the selected within derivative of `f` at `(E, x0)` is zero. -/
theorem helperForProposition_6_11_fderivWithin_eq_zero_of_hasFDerivWithinAt_zero
    {k n : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hZeroF :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0) :
    fderivWithin ℝ f E x0 = 0 := by
  simp [fderivWithin, hZeroF]

/-- Helper for Proposition 6.11: if `f` has zero within-derivative witness at
`x0`, then the selected within derivative of `fun x => T (f x)` at `(E, x0)`
is zero. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_eq_zero_of_hasFDerivWithinAt_zero
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hZeroF :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    fderivWithin ℝ (fun x => T (f x)) E x0 = 0 := by
  have hZeroComp :
      HasFDerivWithinAt (fun x => T (f x))
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) E x0 :=
    helperForProposition_6_11_hasFDerivWithinAt_zero_linearMap_comp_of_hasFDerivWithinAt_zero
      (hZeroF := hZeroF) (T := T)
  simp [fderivWithin, hZeroComp]

/-- Helper for Proposition 6.11: if `f` has zero within-derivative witness at
`x0`, then the selected within derivative of `fun x => T (f x)` matches
`(LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)`. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_of_hasFDerivWithinAt_zero
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hZeroF :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  have hLhs : fderivWithin ℝ (fun x => T (f x)) E x0 = 0 := by
    exact
      helperForProposition_6_11_fderivWithin_linearMap_comp_eq_zero_of_hasFDerivWithinAt_zero
        (hZeroF := hZeroF) (T := T)
  have hRhs :
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) = 0 := by
    have hFderivZero : fderivWithin ℝ f E x0 = 0 := by
      exact
        helperForProposition_6_11_fderivWithin_eq_zero_of_hasFDerivWithinAt_zero
          (hZeroF := hZeroF)
    simp [hFderivZero]
  rw [hLhs, hRhs]

/-- Helper for Proposition 6.11: in the non-`UniqueDiffWithinAt` branch, if
either `f` has zero within-derivative witness at `x0` or within-derivative
witnesses for `fun x => T (f x)` are pointwise canonical, then the selected
within derivative identity follows. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_of_not_uniqueDiff_of_zeroOrPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hZeroOrCanonicity :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0 ∨
      (∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2)) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  rcases hZeroOrCanonicity with hZeroF | hCanonicity
  · exact
      helperForProposition_6_11_fderivWithin_linearMap_comp_of_hasFDerivWithinAt_zero
        (hZeroF := hZeroF) (T := T)
  · exact
      helperForProposition_6_11_fderivWithin_linearMap_comp_of_pointCanonicity
        (hf := hf) (T := T) hCanonicity

/-- Helper for Proposition 6.11: in the non-`UniqueDiffWithinAt` branch, the
zero-derivative or point-canonicity alternatives imply the full conclusion
pair. -/
theorem helperForProposition_6_11_pairResult_of_not_uniqueDiff_of_zeroOrPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hZeroOrCanonicity :
      HasFDerivWithinAt f
        (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0 ∨
      (∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2)) :
    DifferentiableWithinAt ℝ (fun x => T (f x)) E x0 ∧
      fderivWithin ℝ (fun x => T (f x)) E x0 =
        (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  refine ⟨?_, ?_⟩
  · exact
      helperForProposition_6_11_differentiableWithinAt_linearMap_comp
        (hf := hf) (T := T)
  · exact
      helperForProposition_6_11_fderivWithin_linearMap_comp_of_not_uniqueDiff_of_zeroOrPointCanonicity
        (hf := hf) (T := T) hZeroOrCanonicity

/-- Helper for Proposition 6.11: negating the zero-derivative-or-point-
canonicity alternative yields both residual negations. -/
theorem helperForProposition_6_11_not_zeroAndNotCanonicity_of_not_zeroOrPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotZeroOrCanonicity :
      ¬ (HasFDerivWithinAt f
            (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0 ∨
          (∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
            HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
            HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
            L1 = L2))) :
    (¬ HasFDerivWithinAt f
      (0 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin n)) E x0) ∧
      (¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2) := by
  constructor
  · intro hZeroF
    exact hNotZeroOrCanonicity (Or.inl hZeroF)
  · intro hCanonicity
    exact hNotZeroOrCanonicity (Or.inr hCanonicity)

/-- Helper for Proposition 6.11: in the residual branch, once pointwise
canonicity of within-derivative witnesses for `fun x => T (f x)` is supplied,
the selected within-derivative identity follows immediately. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_residual_of_pointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact
    helperForProposition_6_11_fderivWithin_linearMap_comp_of_pointCanonicity
      (hf := hf) (T := T) hCanonicity

/-- Helper for Proposition 6.11: both the selected within derivative and the
chain-rule candidate provide valid within-derivative witnesses for
`fun x => T (f x)` at `(E, x0)`. -/
theorem helperForProposition_6_11_selectedAndChainRuleCandidate_hasFDerivWithinAt_linearMap_comp
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    HasFDerivWithinAt (fun x => T (f x))
        (fderivWithin ℝ (fun x => T (f x)) E x0) E x0 ∧
      HasFDerivWithinAt (fun x => T (f x))
        ((LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)) E x0 := by
  refine ⟨?_, ?_⟩
  · exact
      (helperForProposition_6_11_differentiableWithinAt_linearMap_comp
        (hf := hf) (T := T)).hasFDerivWithinAt
  · exact
      helperForProposition_6_11_hasFDerivWithinAt_linearMap_comp (hf := hf)
        (T := T)

/-- Helper for Proposition 6.11: failure of pointwise canonicity for
within-derivative witnesses of `fun x => T (f x)` at `(E, x0)` yields two
valid witnesses that are distinct. -/
theorem helperForProposition_6_11_existsUnequalWitnesses_of_notPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotCanonicity :
      ¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2) :
    ∃ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt (fun x => T (f x)) L1 E x0 ∧
      HasFDerivWithinAt (fun x => T (f x)) L2 E x0 ∧
      L1 ≠ L2 := by
  classical
  by_contra hNoCounterexample
  apply hNotCanonicity
  intro L1 L2 hL1 hL2
  by_contra hNe
  apply hNoCounterexample
  exact ⟨L1, L2, hL1, hL2, hNe⟩

/-- Helper for Proposition 6.11: failure of pointwise canonicity yields a
within-derivative witness distinct from the selected `fderivWithin` witness
for `fun x => T (f x)` at `(E, x0)`. -/
theorem helperForProposition_6_11_existsWitnessNeSelected_of_notPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotCanonicity :
      ¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2) :
    ∃ L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt (fun x => T (f x)) L E x0 ∧
      L ≠ fderivWithin ℝ (fun x => T (f x)) E x0 := by
  rcases
      helperForProposition_6_11_existsUnequalWitnesses_of_notPointCanonicity
        (T := T) hNotCanonicity with ⟨L1, L2, hL1, hL2, hNe⟩
  by_cases hEq1 : L1 = fderivWithin ℝ (fun x => T (f x)) E x0
  · refine ⟨L2, hL2, ?_⟩
    intro hEq2
    apply hNe
    calc
      L1 = fderivWithin ℝ (fun x => T (f x)) E x0 := hEq1
      _ = L2 := hEq2.symm
  · exact ⟨L1, hL1, hEq1⟩

/-- Helper for Proposition 6.11: in the residual non-canonical branch, one can
collect the selected within-derivative witness, the chain-rule-candidate
witness, and a pair of distinct within-derivative witnesses. -/
theorem helperForProposition_6_11_residualWitnessData_noncanonical_branch
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotCanonicity :
      ¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2) :
    HasFDerivWithinAt (fun x => T (f x))
        (fderivWithin ℝ (fun x => T (f x)) E x0) E x0 ∧
      HasFDerivWithinAt (fun x => T (f x))
        ((LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)) E x0 ∧
      ∃ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 ∧
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 ∧
        L1 ≠ L2 := by
  rcases
      helperForProposition_6_11_selectedAndChainRuleCandidate_hasFDerivWithinAt_linearMap_comp
        (hf := hf) (T := T) with ⟨hSelected, hCandidate⟩
  refine ⟨hSelected, hCandidate, ?_⟩
  exact
    helperForProposition_6_11_existsUnequalWitnesses_of_notPointCanonicity
      (T := T) hNotCanonicity

/-- Helper for Proposition 6.11: failure of pointwise canonicity yields a
within-derivative witness distinct from the chain-rule candidate
`(LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)` for
`fun x => T (f x)` at `(E, x0)`. -/
theorem helperForProposition_6_11_existsWitnessNeChainRuleCandidate_of_notPointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotCanonicity :
      ¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2) :
    ∃ L : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
      HasFDerivWithinAt (fun x => T (f x)) L E x0 ∧
      L ≠ (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  rcases
      helperForProposition_6_11_residualWitnessData_noncanonical_branch
        (hf := hf) (T := T) hNotCanonicity with
      ⟨_hSelected, _hCandidate, hUnequalWitnesses⟩
  rcases hUnequalWitnesses with ⟨L1, L2, hL1, hL2, hNe⟩
  by_cases hEq1 :
      L1 = (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)
  · refine ⟨L2, hL2, ?_⟩
    intro hEq2
    apply hNe
    calc
      L1 = (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := hEq1
      _ = L2 := hEq2.symm
  · exact ⟨L1, hL1, hEq1⟩

/-- Helper for Proposition 6.11: pointwise canonicity of within-derivative
witnesses is incompatible with the existence of two distinct valid witnesses
at `(E, x0)`. -/
theorem helperForProposition_6_11_false_of_pointCanonicity_and_unequalWitnesses
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2)
    (hUnequalWitnesses :
      ∃ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 ∧
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 ∧
        L1 ≠ L2) :
    False := by
  rcases hUnequalWitnesses with ⟨L1, L2, hL1, hL2, hNe⟩
  exact hNe (hCanonicity L1 L2 hL1 hL2)

/-- Helper for Proposition 6.11: once canonicity is available for within-
derivative witnesses of `fun x => T (f x)` at `(E, x0)`, the selected
within derivative equals the chain-rule candidate witness. -/
theorem helperForProposition_6_11_selectedEq_chainRuleCandidate_of_pointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hSelected :
      HasFDerivWithinAt (fun x => T (f x))
        (fderivWithin ℝ (fun x => T (f x)) E x0) E x0)
    (hCandidate :
      HasFDerivWithinAt (fun x => T (f x))
        ((LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)) E x0)
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact hCanonicity _ _ hSelected hCandidate

/-- Helper for Proposition 6.11: a residual non-canonicity hypothesis is
incompatible with any asserted pointwise canonicity of within-derivative
witnesses for `fun x => T (f x)` at `(E, x0)`. -/
theorem helperForProposition_6_11_false_of_notPointCanonicity_and_pointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hNotCanonicity :
      ¬ ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
          HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
          HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
          L1 = L2)
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    False := by
  exact hNotCanonicity hCanonicity

/-- Helper for Proposition 6.11: if the selected within derivative and the
chain-rule candidate are both valid witnesses, then any supplied pointwise
canonicity identifies them. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_of_selectedCandidate_and_pointCanonicity
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hSelectedAndCandidate :
      HasFDerivWithinAt (fun x => T (f x))
          (fderivWithin ℝ (fun x => T (f x)) E x0) E x0 ∧
        HasFDerivWithinAt (fun x => T (f x))
          ((LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0)) E x0)
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact
    helperForProposition_6_11_selectedEq_chainRuleCandidate_of_pointCanonicity
      (T := T) hSelectedAndCandidate.1 hSelectedAndCandidate.2 hCanonicity

/-- Helper for Proposition 6.11: in the non-`UniqueDiffWithinAt` workflow, once
pointwise canonicity is supplied for `fun x => T (f x)` at `(E, x0)`, the
within-derivative identity follows. -/
theorem helperForProposition_6_11_fderivWithin_linearMap_comp_residual_noncanonical_branch
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hCanonicity :
      ∀ L1 L2 : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m),
        HasFDerivWithinAt (fun x => T (f x)) L1 E x0 →
        HasFDerivWithinAt (fun x => T (f x)) L2 E x0 →
        L1 = L2) :
    fderivWithin ℝ (fun x => T (f x)) E x0 =
      (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  exact
    helperForProposition_6_11_fderivWithin_linearMap_comp_of_pointCanonicity
      (hf := hf) (T := T) hCanonicity

/-- Proposition 6.11 (Derivative of a linear map composed with a differentiable
map): let E ⊆ ℝᵏ, let f : E → ℝⁿ be differentiable at x₀ ∈ E, and let
T : ℝⁿ → ℝᵐ be linear. Defining (Tf)(x) = T (f x), the map Tf is
differentiable at x₀, and D(Tf)(x₀) = T ∘ Df(x₀).

In Lean's `fderivWithin` setting, this selected-derivative identity needs
`UniqueDiffWithinAt` at `(E, x0)`. -/
theorem derivative_linearMap_comp_differentiableMap
    {k n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin n)}
    {x0 : EuclideanSpace ℝ (Fin k)}
    (hx0 : x0 ∈ E)
    (hf : DifferentiableWithinAt ℝ f E x0)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hUnique : UniqueDiffWithinAt ℝ E x0) :
    DifferentiableWithinAt ℝ (fun x => T (f x)) E x0 ∧
      fderivWithin ℝ (fun x => T (f x)) E x0 =
        (LinearMap.toContinuousLinearMap T).comp (fderivWithin ℝ f E x0) := by
  let _ := hx0
  exact
    helperForProposition_6_11_withUniqueDiff
      (hf := hf) (T := T) hUnique

/-- Helper for Proposition 6.12: the coordinate map
`γ(t) = (x₁(t), …, xₙ(t))` is differentiable when each coordinate is. -/
lemma helperForProposition_6_12_gammaDifferentiable
    {n : ℕ}
    {x : Fin n → ℝ → ℝ}
    (hx : ∀ j : Fin n, Differentiable ℝ (x j)) :
    Differentiable ℝ (fun t : ℝ => fun j : Fin n => x j t) := by
  refine (differentiable_pi).2 ?_
  intro j
  exact hx j

/-- Helper for Proposition 6.12: the derivative of `γ` is the tuple of
coordinate derivatives. -/
lemma helperForProposition_6_12_derivGamma_apply
    {n : ℕ}
    {x : Fin n → ℝ → ℝ}
    (hx : ∀ j : Fin n, Differentiable ℝ (x j)) :
    ∀ t : ℝ,
      deriv (fun s : ℝ => fun j : Fin n => x j s) t =
        fun j : Fin n => deriv (x j) t := by
  intro t
  simpa using
    (deriv_pi (x := t) (φ := fun s : ℝ => fun j : Fin n => x j s)
      (fun j => hx j t))

/-- Helper for Proposition 6.12: a continuous linear map on `ℝⁿ` applied to a
vector equals the sum of its actions on coordinate basis vectors. -/
lemma helperForProposition_6_12_clmApply_eq_sumPiSingle
    {n m : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (v : Fin n → ℝ) :
    L v =
      ∑ j : Fin n, (v j) • L (Pi.single j (1 : ℝ)) := by
  have hv :
      v = ∑ j : Fin n, (v j) • ((Pi.single j (1 : ℝ)) : Fin n → ℝ) := by
    simpa using (pi_eq_sum_univ' v)
  have hLv :
      L v =
        L (∑ j : Fin n, (v j) • ((Pi.single j (1 : ℝ)) : Fin n → ℝ)) := by
    simpa using congrArg L hv
  calc
    L v = L (∑ j : Fin n, (v j) • ((Pi.single j (1 : ℝ)) : Fin n → ℝ)) := hLv
    _ = ∑ j : Fin n, L ((v j) • ((Pi.single j (1 : ℝ)) : Fin n → ℝ)) := by
      simp
    _ = ∑ j : Fin n, (v j) • L ((Pi.single j (1 : ℝ)) : Fin n → ℝ) := by
      simp

/-- Helper for Proposition 6.12: chain-rule vector form for
`t ↦ f (γ(t))`. -/
lemma helperForProposition_6_12_chainRule_vectorForm
    {n m : ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x : Fin n → ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hx : ∀ j : Fin n, Differentiable ℝ (x j)) :
    ∀ t : ℝ,
      deriv (fun s => f ((fun u j => x j u) s)) t =
        (fderiv ℝ f ((fun u j => x j u) t))
          (deriv (fun s => fun j => x j s) t) := by
  intro t
  have hγ : Differentiable ℝ (fun s : ℝ => fun j : Fin n => x j s) :=
    helperForProposition_6_12_gammaDifferentiable (hx := hx)
  have hfAt : DifferentiableAt ℝ f ((fun u : ℝ => fun j : Fin n => x j u) t) :=
    hf ((fun u : ℝ => fun j : Fin n => x j u) t)
  have hγAt : DifferentiableAt ℝ (fun s : ℝ => fun j : Fin n => x j s) t :=
    hγ t
  simpa [Function.comp] using
    (fderiv_comp_deriv (𝕜 := ℝ)
      (f := fun s : ℝ => fun j : Fin n => x j s) (x := t)
      (l := f) hfAt hγAt)

/-- Proposition 6.12 (Chain rule along a differentiable curve): let
`f : ℝⁿ → ℝᵐ` be differentiable and let `xⱼ : ℝ → ℝ` be differentiable for
`j = 1, …, n`. Define `γ(t) = (x₁(t), …, xₙ(t))`. Then `f ∘ γ` is
differentiable, and for every `t`,
`d/dt f(γ(t)) = Df(γ(t)) γ'(t) = ∑ⱼ xⱼ'(t) ∂f/∂xⱼ (γ(t))`. -/

theorem chainRule_along_differentiableCurve
    {n m : ℕ}
    {f : (Fin n → ℝ) → (Fin m → ℝ)}
    {x : Fin n → ℝ → ℝ}
    (hf : Differentiable ℝ f)
    (hx : ∀ j : Fin n, Differentiable ℝ (x j)) :
    let γ : ℝ → (Fin n → ℝ) := fun t j => x j t
    Differentiable ℝ (fun t => f (γ t)) ∧
      ∀ t : ℝ,
        deriv (fun s => f (γ s)) t = (fderiv ℝ f (γ t)) (deriv γ t) ∧
          (fderiv ℝ f (γ t)) (deriv γ t) =
            ∑ j : Fin n, (deriv (x j) t) •
              (fderiv ℝ f (γ t)) (Pi.single j (1 : ℝ)) := by
  dsimp
  refine ⟨?_, ?_⟩
  · exact
      hf.comp
        (helperForProposition_6_12_gammaDifferentiable (hx := hx))
  · intro t
    refine ⟨?_, ?_⟩
    · exact
        helperForProposition_6_12_chainRule_vectorForm
          (hf := hf) (hx := hx) t
    · calc
        (fderiv ℝ f ((fun u : ℝ => fun j : Fin n => x j u) t))
            (deriv (fun s : ℝ => fun j : Fin n => x j s) t)
            =
            ∑ j : Fin n,
              ((deriv (fun s : ℝ => fun j : Fin n => x j s) t) j) •
                (fderiv ℝ f ((fun u : ℝ => fun j : Fin n => x j u) t))
                  (Pi.single j (1 : ℝ)) := by
              exact
                helperForProposition_6_12_clmApply_eq_sumPiSingle
                  (L := fderiv ℝ f ((fun u : ℝ => fun j : Fin n => x j u) t))
                  (v := deriv (fun s : ℝ => fun j : Fin n => x j s) t)
        _ =
            ∑ j : Fin n,
              (deriv (x j) t) •
                (fderiv ℝ f ((fun u : ℝ => fun j : Fin n => x j u) t))
                  (Pi.single j (1 : ℝ)) := by
              simp [helperForProposition_6_12_derivGamma_apply (hx := hx) (t := t)]

end Section04
end Chap06
