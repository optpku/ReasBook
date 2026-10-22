/-
Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap06
section Section05

/-- Definition 6.12 (Twice continuous differentiability): let `E ⊆ ℝⁿ` be open and
`f : ℝⁿ → ℝᵐ`. The map `f` is twice continuously differentiable (class `C²`) on `E`
when it is continuously differentiable on `E` and each first-order partial derivative
map is continuously differentiable on `E`. We encode this with the openness
hypothesis together with `ContDiffOn ℝ 2 f E`. -/
def IsTwiceContinuouslyDifferentiableOn
    {n m : ℕ}
    (E : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin m → ℝ)) : Prop :=
  IsOpen E ∧ ContDiffOn ℝ 2 f E

/-- Theorem 6.5: (Clairaut's theorem) let `E ⊆ ℝⁿ` be open and let
`f : ℝⁿ → ℝᵐ` be of class `C²` on `E`. Then for every `x₀ ∈ E` and all indices
`i, j`, the mixed second partial derivatives exist and commute. Componentwise,
for each `ℓ`,
`∂²f_ℓ/(∂xⱼ ∂xᵢ) (x₀) = ∂²f_ℓ/(∂xᵢ ∂xⱼ) (x₀)`;
equivalently, the corresponding vector-valued mixed derivatives are equal. -/
theorem clairaut_mixed_partials_within
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    (hE : IsOpen E)
    (hf : ContDiffOn ℝ 2 f E) :
    ∀ ⦃x₀ : EuclideanSpace ℝ (Fin n)⦄, x₀ ∈ E →
      ∀ i j : Fin n,
        DifferentiableWithinAt ℝ
          (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀ ∧
        DifferentiableWithinAt ℝ
          (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀ ∧
        (∀ ℓ : Fin m,
          (fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀
              (EuclideanSpace.single j (1 : ℝ))) ℓ
            =
          (fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀
              (EuclideanSpace.single i (1 : ℝ))) ℓ) ∧
        fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀
            (EuclideanSpace.single j (1 : ℝ))
          =
        fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀
            (EuclideanSpace.single i (1 : ℝ)) := by
  intro x₀ hx₀ i j
  have hcd : ContDiffWithinAt ℝ 2 f E x₀ := hf x₀ hx₀
  have hUniqueOn : UniqueDiffOn ℝ E := hE.uniqueDiffOn
  have hDirectionalMapDifferentiableWithin :
      ∀ k : Fin n,
        DifferentiableWithinAt ℝ
          (fun x => fderivWithin ℝ f E x (EuclideanSpace.single k (1 : ℝ))) E x₀ := by
    intro k
    have hContDiff :
        ContDiffWithinAt ℝ 1
          (fun x => fderivWithin ℝ f E x (EuclideanSpace.single k (1 : ℝ))) E x₀ := by
      exact hcd.fderivWithin_right_apply (m := 1) contDiffWithinAt_const hUniqueOn le_rfl hx₀
    exact hContDiff.differentiableWithinAt one_ne_zero
  have hFderivWithinDiff : DifferentiableWithinAt ℝ (fderivWithin ℝ f E) E x₀ := by
    exact (hcd.fderivWithin_right (m := 1) hUniqueOn le_rfl hx₀).differentiableWithinAt
      one_ne_zero
  have hDirectionalSecondRewrite :
      ∀ a b : Fin n,
        fderivWithin ℝ
            (fun x => fderivWithin ℝ f E x (EuclideanSpace.single a (1 : ℝ))) E x₀
            (EuclideanSpace.single b (1 : ℝ))
          =
        fderivWithin ℝ (fderivWithin ℝ f E) E x₀
            (EuclideanSpace.single b (1 : ℝ))
            (EuclideanSpace.single a (1 : ℝ)) := by
    intro a b
    have hDerivMap :
        fderivWithin ℝ
            (fun x => fderivWithin ℝ f E x (EuclideanSpace.single a (1 : ℝ))) E x₀
          =
        (fderivWithin ℝ (fderivWithin ℝ f E) E x₀).flip (EuclideanSpace.single a (1 : ℝ)) := by
      have hConstDiff :
          DifferentiableWithinAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => EuclideanSpace.single a (1 : ℝ)) E x₀ := by
        exact differentiableWithinAt_const (c := EuclideanSpace.single a (1 : ℝ))
      rw [fderivWithin_clm_apply (hUniqueOn x₀ hx₀) hFderivWithinDiff hConstDiff]
      rw [fderivWithin_const_apply]
      simp
    have hEval := congrArg (fun L => L (EuclideanSpace.single b (1 : ℝ))) hDerivMap
    simpa [ContinuousLinearMap.flip_apply] using hEval
  have hPointInClosureInterior : x₀ ∈ closure (interior E) := by
    rw [hE.interior_eq]
    exact subset_closure hx₀
  have hSymmSecondWithinOpen : IsSymmSndFDerivWithinAt ℝ f E x₀ := by
    exact hcd.isSymmSndFDerivWithinAt (n := 2) (by simp) hUniqueOn hPointInClosureInterior hx₀
  have hVectorEq :
      fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀
          (EuclideanSpace.single j (1 : ℝ))
        =
      fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀
          (EuclideanSpace.single i (1 : ℝ)) := by
    calc
      fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀
          (EuclideanSpace.single j (1 : ℝ))
          =
        fderivWithin ℝ (fderivWithin ℝ f E) E x₀
            (EuclideanSpace.single j (1 : ℝ))
            (EuclideanSpace.single i (1 : ℝ)) := hDirectionalSecondRewrite i j
      _ =
        fderivWithin ℝ (fderivWithin ℝ f E) E x₀
            (EuclideanSpace.single i (1 : ℝ))
            (EuclideanSpace.single j (1 : ℝ)) :=
        hSymmSecondWithinOpen.eq (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
      _ =
        fderivWithin ℝ (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀
            (EuclideanSpace.single i (1 : ℝ)) := by
        symm
        exact hDirectionalSecondRewrite j i
  have hComponentEq :
      ∀ ℓ : Fin m,
        (fderivWithin ℝ
              (fun x => fderivWithin ℝ f E x (EuclideanSpace.single i (1 : ℝ))) E x₀
              (EuclideanSpace.single j (1 : ℝ)))
            ℓ
          =
        (fderivWithin ℝ
              (fun x => fderivWithin ℝ f E x (EuclideanSpace.single j (1 : ℝ))) E x₀
              (EuclideanSpace.single i (1 : ℝ)))
            ℓ := by
    intro ℓ
    exact congrArg (fun v => v ℓ) hVectorEq
  exact And.intro (hDirectionalMapDifferentiableWithin i)
    (And.intro (hDirectionalMapDifferentiableWithin j)
      (And.intro hComponentEq hVectorEq))

end Section05
end Chap06
