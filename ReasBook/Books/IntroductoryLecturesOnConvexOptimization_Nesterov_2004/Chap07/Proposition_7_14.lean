/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Gradient

noncomputable section

universe u v

variable {ι : Type u}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 7.14 lies in the chapter's finite max-absolute-linear / symmetric log-sum-exp
smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, specialized to the finite objective
  `x ↦ max_i |⟪a_i, x⟫|`;
- `gradient` from `Mathlib/Analysis/Calculus/Gradient/Basic`, the canonical first-order owner on
  a real Hilbert space;
- `hessian` in `Chap01/Definition_1_4_16`, the chapter's intrinsic second-order owner.

Best owner abstraction:
- source-facing: the symmetric log-sum-exp smoothing of
  `maxTypeObjective (fun i x ↦ |⟪aᵢ, x⟫|)`;
- core/canonical: the positive-parameter finite-family smoothing owner
  `absLinearLogSumExp μ a : E → ℝ`;
- bridge/view: the gradient and Hessian formulas below.

Primitive data:
- a finite family `a : ι → E`;
- a positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the symmetric exponential summand `absLinearLogSumExpPairWeight`;
- the normalization factor `absLinearLogSumExpOmega`;
- the coefficient `absLinearLogSumExpLambda`;
- the smoothing owner `absLinearLogSumExp μ a`;
- the smoothness, gradient, and Hessian formulas.

This owner is kept at the finite-family real inner-product-space level. The coordinate model
`Fin m → EuclideanSpace ℝ (Fin n)` is a downstream specialization, not primitive data here. -/

section Definitions

/-- The `i`-th symmetric exponential term
`exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)` used in the smoothing formula. -/
def absLinearLogSumExpPairWeight
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) : ℝ :=
  Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))

-- Proof sketch: unfold `absLinearLogSumExpPairWeight`.
/-- Expanding `absLinearLogSumExpPairWeight μ a i x` gives the symmetric exponential summand
`exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)`. -/
theorem absLinearLogSumExpPairWeight_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) :
    absLinearLogSumExpPairWeight μ a i x =
      Real.exp (inner ℝ (a i) x / (μ : ℝ)) + Real.exp (-(inner ℝ (a i) x / (μ : ℝ))) := rfl

end Definitions

section FiniteFamily

variable [Fintype ι]

/-- The normalization factor
`ω_μ(x) = ∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)]`. -/
def absLinearLogSumExpOmega
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) : ℝ :=
  ∑ i, absLinearLogSumExpPairWeight μ a i x

-- Proof sketch: unfold `absLinearLogSumExpOmega`.
/-- Expanding `absLinearLogSumExpOmega μ a x` gives the finite sum of the symmetric exponential
terms. -/
theorem absLinearLogSumExpOmega_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    absLinearLogSumExpOmega μ a x = ∑ i, absLinearLogSumExpPairWeight μ a i x := rfl

/-- The coefficient
`λ_μ⁽ⁱ⁾(x) = (exp (⟪aᵢ, x⟫ / μ) - exp (-⟪aᵢ, x⟫ / μ)) / ω_μ(x)` appearing in the gradient
representation. -/
def absLinearLogSumExpLambda
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) : ℝ :=
  (Real.exp (inner ℝ (a i) x / (μ : ℝ)) - Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) /
    absLinearLogSumExpOmega μ a x

-- Proof sketch: unfold `absLinearLogSumExpLambda`.
/-- Expanding `absLinearLogSumExpLambda μ a i x` gives the normalized signed exponential
difference. -/
theorem absLinearLogSumExpLambda_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x : E) :
    absLinearLogSumExpLambda μ a i x =
      (Real.exp (inner ℝ (a i) x / (μ : ℝ)) - Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) /
        absLinearLogSumExpOmega μ a x := rfl

/-- The smoothing function
`f_μ(x) = μ log (∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
for the maximal absolute value of the linear forms `x ↦ ⟪aᵢ, x⟫`. -/
def absLinearLogSumExp
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) : E → ℝ :=
  fun x ↦ (μ : ℝ) * Real.log (absLinearLogSumExpOmega μ a x)

-- Proof sketch: unfold `absLinearLogSumExp`.
/-- Evaluating `absLinearLogSumExp μ a` at `x` gives
`μ log (absLinearLogSumExpOmega μ a x)`. -/
theorem absLinearLogSumExp_apply
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    absLinearLogSumExp μ a x = (μ : ℝ) * Real.log (absLinearLogSumExpOmega μ a x) := rfl

/-- Helper for Proposition 7.14: each symmetric exponential summand is `C²`. -/
theorem absLinearLogSumExpPairWeight_contDiff
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) :
    ContDiff ℝ 2 (absLinearLogSumExpPairWeight μ a i) := by
  -- Rewrite the scalar input map as a scaled continuous linear functional.
  have hlin : ContDiff ℝ 2 (fun x : E ↦ inner ℝ (a i) x / (μ : ℝ)) := by
    convert
      (((((1 / (μ : ℝ)) : ℝ) • innerSL ℝ (a i)).contDiff : ContDiff ℝ 2
        ((((1 / (μ : ℝ)) : ℝ) • innerSL ℝ (a i))))) using 1
    funext x
    simp [div_eq_mul_inv, mul_comm]
  -- Each branch is an exponential of that affine-linear scalar map.
  exact hlin.exp.add hlin.neg.exp

/-- Helper for Proposition 7.14: the normalizing sum `ω_μ` is `C²`. -/
theorem absLinearLogSumExpOmega_contDiff
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) :
    ContDiff ℝ 2 (absLinearLogSumExpOmega μ a) := by
  -- The finite sum is smooth because every summand is smooth.
  simpa [absLinearLogSumExpOmega] using
    (ContDiff.sum (s := Finset.univ)
      (f := fun i ↦ absLinearLogSumExpPairWeight μ a i)
      (fun i hi ↦ absLinearLogSumExpPairWeight_contDiff μ a i))

/-- Helper for Proposition 7.14: if the index family is empty, the smoothing function vanishes. -/
theorem absLinearLogSumExp_eq_zero_of_isEmpty
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (hι : IsEmpty ι) :
    absLinearLogSumExp μ a = fun _ ↦ 0 := by
  letI := hι
  -- In the empty-family branch, both the normalizer and the logarithmic smoothing collapse to `0`.
  funext x
  simp [absLinearLogSumExp, absLinearLogSumExpOmega]

/-- Helper for Proposition 7.14: for a nonempty finite family, the normalizer `ω_μ(x)` is
strictly positive. -/
theorem absLinearLogSumExpOmega_pos
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) [Nonempty ι] (x : E) :
    0 < absLinearLogSumExpOmega μ a x := by
  -- Every summand is the sum of two positive exponentials, so the finite sum is positive.
  refine Finset.sum_pos (fun i hi ↦ ?_) Finset.univ_nonempty
  exact add_pos (Real.exp_pos _) (Real.exp_pos _)

/-- Helper for Proposition 7.14: differentiating the scalar slice of `ω_μ` at `0` produces the
signed weighted sum from the textbook numerator. -/
theorem absLinearLogSumExpOmega_slice_hasDerivAt_zero
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x h : E) :
    HasDerivAt (fun t : ℝ ↦ absLinearLogSumExpOmega μ a (x + t • h))
      ((1 / (μ : ℝ)) *
        ∑ i,
          (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
            inner ℝ (a i) h) 0 := by
  -- Differentiate each finite summand on the slice and then sum the resulting scalar derivatives.
  simpa [absLinearLogSumExpOmega, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    (HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun i t ↦ absLinearLogSumExpPairWeight μ a i (x + t • h))
      (A' := fun i ↦
        (1 / (μ : ℝ)) *
          (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
            inner ℝ (a i) h)
      (x := 0)
      (fun i hi ↦ by
        -- The line `t ↦ x + t • h` has derivative `h`, so the chain rule reduces to scalar
        -- differentiation of the two exponential branches.
        have hline : HasDerivAt (fun t : ℝ ↦ x + t • h) h 0 := by
          simpa [one_smul, zero_smul] using
            ((((1 : ℝ →L[ℝ] ℝ)).smulRight h).hasFDerivAt).hasDerivAt.const_add x
        have hu₀ :=
          (((((1 / (μ : ℝ)) : ℝ) • innerSL ℝ (a i)).hasFDerivAt).comp 0 hline.hasFDerivAt).hasDerivAt
        have hu :
            HasDerivAt (fun t : ℝ ↦ inner ℝ (a i) (x + t • h) / (μ : ℝ))
              ((1 / (μ : ℝ)) * inner ℝ (a i) h) 0 := by
          -- This is the scalar affine piece `⟪aᵢ, x + t h⟫ / μ`.
          convert hu₀ using 1
          · funext t
            simp [div_eq_mul_inv, mul_comm]
          · simp [div_eq_mul_inv, mul_comm]
        have hneg :
            HasDerivAt (fun t : ℝ ↦ -(inner ℝ (a i) (x + t • h) / (μ : ℝ)))
              (-( (1 / (μ : ℝ)) * inner ℝ (a i) h)) 0 := by
          simpa using hu.neg
        have hsum := hu.exp.add hneg.exp
        -- The two scalar derivatives combine into the signed numerator from `λ_μ^{(i)}`.
        simpa [absLinearLogSumExpPairWeight, zero_smul, sub_eq_add_neg, mul_add, add_mul,
          mul_comm, mul_left_comm, mul_assoc] using hsum))

-- Proof sketch: each summand in `absLinearLogSumExpOmega μ a` is a smooth exponential of a
-- linear functional, so the finite sum is `C^∞`; positivity of `μ` allows composition with
-- `log`, hence `absLinearLogSumExp μ a` is twice continuously differentiable.
/-- Proposition 7.14 (1): for `μ > 0`, the smoothing function
`f_μ(x) = μ log (∑ᵢ [exp (⟪aᵢ, x⟫ / μ) + exp (-⟪aᵢ, x⟫ / μ)])`
is twice continuously differentiable on a real inner product space. -/
theorem absLinearLogSumExp_contDiff
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) :
    ContDiff ℝ 2 (absLinearLogSumExp μ a) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- In the empty branch the smoothing is the zero function, hence trivially smooth.
    simpa [absLinearLogSumExp_eq_zero_of_isEmpty μ a hι] using (contDiff_const : ContDiff ℝ 2 fun _ : E ↦ (0 : ℝ))
  · -- In the nonempty branch, `ω_μ` never vanishes, so `log ∘ ω_μ` is `C²`.
    have hlog :
        ContDiff ℝ 2 (fun x : E ↦ Real.log (absLinearLogSumExpOmega μ a x)) :=
      ContDiff.log (absLinearLogSumExpOmega_contDiff μ a)
        (fun x ↦ (absLinearLogSumExpOmega_pos (μ := μ) (a := a) x).ne')
    simpa [absLinearLogSumExp, smul_eq_mul] using (ContDiff.const_smul (μ : ℝ) hlog)

section Differential

variable [CompleteSpace E]

-- Proof sketch: differentiate `absLinearLogSumExp μ a x = μ log (ω_μ(x))`; the derivative of
-- `ω_μ` is the sum of the signed exponential coefficients times `aᵢ`, and dividing by `ω_μ(x)`
-- yields the coefficient `absLinearLogSumExpLambda μ a i x` in front of each `aᵢ`.
/-- Proposition 7.14 (2): for `μ > 0`, the gradient of the smoothing function is the weighted sum
`∇ f_μ(x) = ∑ᵢ λ_μ⁽ⁱ⁾(x) aᵢ`, equivalently giving the textbook pairing formula
`⟪∇ f_μ(x), h⟫ = ∑ᵢ λ_μ⁽ⁱ⁾(x) ⟪aᵢ, h⟫`. -/
theorem absLinearLogSumExp_gradient_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x : E) :
    ∇ (absLinearLogSumExp μ a) x =
      ∑ i, absLinearLogSumExpLambda μ a i x • a i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Route correction: the empty-family branch is the zero function, so both sides vanish.
    have hzero : absLinearLogSumExp μ a = fun _ ↦ 0 :=
      absLinearLogSumExp_eq_zero_of_isEmpty μ a hι
    letI := hι
    simp [hzero, absLinearLogSumExpOmega, absLinearLogSumExpLambda]
  · -- First identify the directional derivative with the scalar textbook pairing formula.
    have hdiff : DifferentiableAt ℝ (absLinearLogSumExp μ a) x :=
      (absLinearLogSumExp_contDiff μ a).differentiable (by norm_num) x
    apply ext_inner_right ℝ
    intro h
    have hωx : absLinearLogSumExpOmega μ a x ≠ 0 :=
      (absLinearLogSumExpOmega_pos (μ := μ) (a := a) x).ne'
    have hsliceOmega :=
      absLinearLogSumExpOmega_slice_hasDerivAt_zero (μ := μ) (a := a) x h
    have hsliceLog :
        HasDerivAt (fun t : ℝ ↦ Real.log (absLinearLogSumExpOmega μ a (x + t • h)))
          (((1 / (μ : ℝ)) *
            ∑ i,
              (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
                Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
                inner ℝ (a i) h) /
            absLinearLogSumExpOmega μ a x) 0 := by
      -- The logarithmic derivative contributes a division by `ω_μ(x)`.
      simpa [zero_smul] using hsliceOmega.log (by simpa [zero_smul] using hωx)
    have hslice :
        HasDerivAt (fun t : ℝ ↦ absLinearLogSumExp μ a (x + t • h))
          (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) 0 := by
      -- Multiplying by `μ` cancels the prefactor `1 / μ` from the derivative of `ω_μ`.
      have hmul :
          HasDerivAt (fun t : ℝ ↦ absLinearLogSumExp μ a (x + t • h))
            ((μ : ℝ) *
              (((1 / (μ : ℝ)) *
                ∑ i,
                  (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
                    Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
                    inner ℝ (a i) h) /
                absLinearLogSumExpOmega μ a x)) 0 := by
        simpa [absLinearLogSumExp] using hsliceLog.const_mul (μ : ℝ)
      convert hmul using 1
      have hμ : (μ : ℝ) ≠ 0 := μ.property.ne'
      field_simp [hμ, hωx]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [absLinearLogSumExpLambda]
      field_simp [hωx]
    have hline :
        lineDeriv ℝ (absLinearLogSumExp μ a) x h =
          ∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h := by
      exact (show HasLineDerivAt ℝ (absLinearLogSumExp μ a)
        (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) x h by
        simpa [HasLineDerivAt] using hslice).lineDeriv
    -- Convert the line derivative into the Fréchet derivative, then into the gradient pairing.
    calc
      inner ℝ (∇ (absLinearLogSumExp μ a) x) h
        = fderiv ℝ (absLinearLogSumExp μ a) x h := by
            simpa using (inner_gradient_left (y := h) hdiff)
      _ = lineDeriv ℝ (absLinearLogSumExp μ a) x h := by
            rw [hdiff.lineDeriv_eq_fderiv]
      _ = ∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h := hline
      _ = inner ℝ (∑ i, absLinearLogSumExpLambda μ a i x • a i) h := by
            simp [sum_inner, inner_smul_left]

/-- Helper for Proposition 7.14: a `C²` real-valued field on a Hilbert space has a differentiable
gradient at the base point. -/
theorem differentiableAt_gradient_of_contDiffAt_two
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (∇ f) x := by
  -- Rewrite the gradient through the inverse Riesz map so differentiability reduces to `fderiv`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    -- A `C²` function has a differentiable first derivative.
    exact
      (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun y ↦ D (fderiv ℝ f y)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Proposition 7.14: along an affine line, one symmetric exponential summand has
second derivative equal to its value times the squared normalized direction coefficient. -/
theorem absLinearLogSumExpPairWeight_slice_secondDeriv_zero
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (i : ι) (x h : E) :
    iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) 0 =
      ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (inner ℝ (a i) h) ^ (2 : ℕ) *
        absLinearLogSumExpPairWeight μ a i x := by
  let c : ℝ := inner ℝ (a i) h / (μ : ℝ)
  let d : ℝ := inner ℝ (a i) x / (μ : ℝ)
  have hexp_affine :
      ∀ c d : ℝ, iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0 = c ^ (2 : ℕ) * Real.exp d :=
    by
      intro c d
      have hg : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) := by
        simpa using
          (Real.contDiff_exp.contDiffAt : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d))
      have hf : ContDiffAt ℝ 2 (fun t : ℝ ↦ c * t + d) 0 := by
        fun_prop
      have hderiv_affine_fun : deriv (fun t : ℝ ↦ c * t + d) = fun _ ↦ c := by
        funext t
        rw [deriv_add_const]
        simpa using (deriv_const_mul_field (x := t) (u := c) (v := fun s : ℝ ↦ s))
      have hderiv_affine : deriv (fun t : ℝ ↦ c * t + d) 0 = c := by
        simpa using congrArg (fun f : ℝ → ℝ ↦ f 0) hderiv_affine_fun
      have hsecond_affine : iteratedDeriv 2 (fun t : ℝ ↦ c * t + d) 0 = 0 := by
        rw [iteratedDeriv_succ', hderiv_affine_fun]
        simp
      have hexp_second : iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) d = Real.exp d := by
        simpa [iteratedDeriv_eq_iterate] using
          congrArg (fun f : ℝ → ℝ ↦ f d) (Real.iter_deriv_exp 2)
      have hexp_second' : iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) = Real.exp d := by
        simpa using hexp_second
      -- Apply the scalar second-derivative composition formula to the affine input of `exp`.
      calc
        iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0
            = iteratedDeriv 2 (fun s : ℝ ↦ Real.exp s) (c * 0 + d) *
                deriv (fun t : ℝ ↦ c * t + d) 0 ^ (2 : ℕ) +
                deriv (fun s : ℝ ↦ Real.exp s) (c * 0 + d) *
                  iteratedDeriv 2 (fun t : ℝ ↦ c * t + d) 0 := by
                simpa [Function.comp] using
                  (iteratedDeriv_comp_two (g := fun s : ℝ ↦ Real.exp s) (f := fun t : ℝ ↦ c * t + d)
                    (x := 0) hg hf)
        _ = Real.exp d * c ^ (2 : ℕ) + Real.exp d * 0 := by
              rw [hderiv_affine, hsecond_affine, hexp_second']
              simp [Real.deriv_exp]
        _ = c ^ (2 : ℕ) * Real.exp d := by ring
  have hsplit :
      (fun t : ℝ ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) =
        fun t : ℝ ↦ Real.exp (c * t + d) + Real.exp ((-c) * t + (-d)) := by
    -- Expand the line slice into the two affine exponential branches.
    funext t
    have harg : inner ℝ (a i) (x + t • h) / (μ : ℝ) = c * t + d := by
      simp [c, d, inner_add_right, inner_smul_right, div_eq_mul_inv, mul_comm]
      ring_nf
    have hnegarg : -(inner ℝ (a i) (x + t • h) / (μ : ℝ)) = (-c) * t + (-d) := by
      rw [harg]
      have hneg : -(c * t + d) = (-c) * t + (-d) := by ring
      simpa using hneg
    calc
      absLinearLogSumExpPairWeight μ a i (x + t • h)
          = Real.exp (inner ℝ (a i) (x + t • h) / (μ : ℝ)) +
              Real.exp (-(inner ℝ (a i) (x + t • h) / (μ : ℝ))) := by
                rfl
      _ = Real.exp (c * t + d) + Real.exp ((-c) * t + (-d)) := by
            rw [harg]
            congr 1
            have hneg' : -(c * t + d) = (-c) * t + (-d) := by ring
            simpa using hneg'
  have hcont₁ : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0 := by
    fun_prop
  have hcont₂ : ContDiffAt ℝ 2 (fun t : ℝ ↦ Real.exp ((-c) * t + (-d))) 0 := by
    fun_prop
  -- Differentiate the two branches separately, then reassemble them into the symmetric weight.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) 0
        = iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d) + Real.exp ((-c) * t + (-d))) 0 := by
            rw [hsplit]
    _ = iteratedDeriv 2 (fun t : ℝ ↦ Real.exp (c * t + d)) 0 +
          iteratedDeriv 2 (fun t : ℝ ↦ Real.exp ((-c) * t + (-d))) 0 := by
            simpa using
              (iteratedDeriv_add (n := 2) (f := fun t : ℝ ↦ Real.exp (c * t + d))
                (g := fun t : ℝ ↦ Real.exp ((-c) * t + (-d))) (x := 0) hcont₁ hcont₂)
    _ = c ^ (2 : ℕ) * (Real.exp d + Real.exp (-d)) := by
          rw [hexp_affine, hexp_affine]
          ring
    _ = ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (inner ℝ (a i) h) ^ (2 : ℕ) *
          (Real.exp d + Real.exp (-d)) := by
          have hc : c = (1 / (μ : ℝ)) * inner ℝ (a i) h := by
            simp [c, div_eq_mul_inv, mul_comm]
          rw [hc]
          ring
    _ = ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (inner ℝ (a i) h) ^ (2 : ℕ) *
          absLinearLogSumExpPairWeight μ a i x := by
          rw [absLinearLogSumExpPairWeight]

/-- Helper for Proposition 7.14: the second slice derivative of the normalizing factor `ω_μ`
is the sum of the summand second derivatives. -/
theorem absLinearLogSumExpOmega_slice_secondDeriv_zero
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x h : E) :
    iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpOmega μ a (x + t • h)) 0 =
      ((1 / (μ : ℝ)) ^ (2 : ℕ)) *
        ∑ i, (inner ℝ (a i) h) ^ (2 : ℕ) * absLinearLogSumExpPairWeight μ a i x := by
  have hsum :
      iteratedDeriv 2 (fun t : ℝ ↦ ∑ i, absLinearLogSumExpPairWeight μ a i (x + t • h)) 0 =
        ∑ i, iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) 0 := by
    -- The iterated derivative commutes with the finite sum because each sliced summand is `C²`.
    simpa using
      (iteratedDeriv_fun_sum (n := 2) (I := Finset.univ)
        (f := fun i t ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) (x := 0)
        (fun i hi ↦ by
          have hline : ContDiff ℝ 2 (fun t : ℝ ↦ x + t • h) := by
            fun_prop
          exact (absLinearLogSumExpPairWeight_contDiff μ a i).contDiffAt.comp 0 hline.contDiffAt))
  -- Expand `ω_μ` as a finite sum, then substitute the single-summand second derivative formula.
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpOmega μ a (x + t • h)) 0
        = ∑ i, iteratedDeriv 2 (fun t : ℝ ↦ absLinearLogSumExpPairWeight μ a i (x + t • h)) 0 := by
            simpa [absLinearLogSumExpOmega] using hsum
    _ = ∑ i,
          ((1 / (μ : ℝ)) ^ (2 : ℕ)) * (inner ℝ (a i) h) ^ (2 : ℕ) *
            absLinearLogSumExpPairWeight μ a i x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [absLinearLogSumExpPairWeight_slice_secondDeriv_zero]
    _ = ((1 / (μ : ℝ)) ^ (2 : ℕ)) *
          ∑ i, (inner ℝ (a i) h) ^ (2 : ℕ) * absLinearLogSumExpPairWeight μ a i x := by
          simpa [mul_assoc] using
            (Finset.mul_sum Finset.univ
              (fun i ↦ (inner ℝ (a i) h) ^ (2 : ℕ) * absLinearLogSumExpPairWeight μ a i x)
              ((1 / (μ : ℝ)) ^ (2 : ℕ))).symm

/-- Helper for Proposition 7.14: differentiating the scalar slice of `μ log (ω_μ)` twice gives
the textbook quadratic-form expression before the final Hessian bridge. -/
theorem absLinearLogSumExp_secondDirectionalDerivative_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x h : E) :
    secondDirectionalDerivative (absLinearLogSumExp μ a) x h =
      (1 / (μ : ℝ)) *
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x -
        (1 / (μ : ℝ)) *
          (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    -- In the empty-family branch the smoothing is identically zero, so every second slice
    -- derivative and every finite sum in the formula vanishes.
    have hzero : absLinearLogSumExp μ a = fun _ ↦ 0 :=
      absLinearLogSumExp_eq_zero_of_isEmpty μ a hι
    have hleft : secondDirectionalDerivative (absLinearLogSumExp μ a) x h = 0 := by
      rw [hzero]
      rw [secondDirectionalDerivative]
      change iteratedDeriv 2 (fun _ : ℝ ↦ (0 : ℝ)) 0 = 0
      simp
    simp [hleft, absLinearLogSumExpOmega, absLinearLogSumExpLambda]
  · let omegaSlice : ℝ → ℝ := fun t ↦ absLinearLogSumExpOmega μ a (x + t • h)
    let signedMoment : ℝ :=
      ∑ i,
        (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
          Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
          inner ℝ (a i) h
    let quadraticMoment : ℝ :=
      ∑ i, (inner ℝ (a i) h) ^ (2 : ℕ) * absLinearLogSumExpPairWeight μ a i x
    have hμ : (μ : ℝ) ≠ 0 := μ.property.ne'
    have homega_pos : 0 < absLinearLogSumExpOmega μ a x :=
      absLinearLogSumExpOmega_pos (μ := μ) (a := a) x
    have hω_cont : ContDiffAt ℝ 2 omegaSlice 0 := by
      -- Restrict the `C²` normalizing factor to the affine line through `x` in direction `h`.
      have hline : ContDiff ℝ 2 (fun t : ℝ ↦ x + t • h) := by
        fun_prop
      simpa [omegaSlice] using (absLinearLogSumExpOmega_contDiff μ a).contDiffAt.comp 0 hline.contDiffAt
    have hlog_cont : ContDiffAt ℝ 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) := by
      -- Positivity of `ω_μ(x)` allows the scalar `log` composition theorem at the slice basepoint.
      simpa [omegaSlice] using (Real.contDiffAt_log.2 homega_pos.ne')
    have hω' : deriv omegaSlice 0 = (1 / (μ : ℝ)) * signedMoment := by
      -- The first derivative of the normalizing slice is the signed exponential moment.
      simpa [omegaSlice, signedMoment] using
        (absLinearLogSumExpOmega_slice_hasDerivAt_zero (μ := μ) (a := a) x h).deriv
    have hω'' : iteratedDeriv 2 omegaSlice 0 = ((1 / (μ : ℝ)) ^ (2 : ℕ)) * quadraticMoment := by
      -- The second derivative is the quadratic moment of the symmetric weights.
      simpa [omegaSlice, quadraticMoment] using
        absLinearLogSumExpOmega_slice_secondDeriv_zero (μ := μ) (a := a) x h
    have hlog₂ :
        iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 =
          iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * deriv omegaSlice 0 ^ (2 : ℕ) +
            deriv (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * iteratedDeriv 2 omegaSlice 0 := by
      -- Apply the scalar second-derivative chain rule to `log ∘ omegaSlice`.
      simpa [Function.comp] using
        (iteratedDeriv_comp_two (g := fun s : ℝ ↦ Real.log s) (f := omegaSlice) (x := 0)
          hlog_cont hω_cont)
    have hlog_base :
        iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) =
          -((absLinearLogSumExpOmega μ a x) ^ (2 : ℕ))⁻¹ := by
      -- Differentiate `log` once to `x ↦ x⁻¹`, then once more with `deriv_inv`.
      calc
        iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0)
            = deriv (deriv (fun s : ℝ ↦ Real.log s)) (omegaSlice 0) := by
                simp [iteratedDeriv_succ]
        _ = deriv (fun s : ℝ ↦ s⁻¹) (omegaSlice 0) := by
              congr 1
              ext s
              rw [Real.deriv_log]
        _ = -((omegaSlice 0) ^ (2 : ℕ))⁻¹ := by
              rw [deriv_inv]
        _ = -((absLinearLogSumExpOmega μ a x) ^ (2 : ℕ))⁻¹ := by
              simp [omegaSlice]
    have hmoment :
        quadraticMoment / absLinearLogSumExpOmega μ a x =
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x := by
      -- Move the constant denominator `ω_μ(x)` term-by-term inside the finite sum.
      change
        (∑ i, (inner ℝ (a i) h) ^ (2 : ℕ) * absLinearLogSumExpPairWeight μ a i x) /
            absLinearLogSumExpOmega μ a x =
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [div_eq_mul_inv]
      ring
    have hlambda :
        signedMoment / absLinearLogSumExpOmega μ a x =
          ∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h := by
      -- Rewrite each signed numerator term through the normalized coefficient `λ_μ^{(i)}(x)`.
      change
        (∑ i,
          (Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))) *
            inner ℝ (a i) h) /
          absLinearLogSumExpOmega μ a x =
        ∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [absLinearLogSumExpLambda, div_eq_mul_inv]
      ring
    have hconstmul :
        iteratedDeriv 2 (fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t)) 0 =
          (μ : ℝ) * iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 := by
      simpa [smul_eq_mul] using
        (iteratedDeriv_const_smul_field (n := 2) (x := 0) (c := (μ : ℝ))
          (f := fun t : ℝ ↦ Real.log (omegaSlice t)))
    have hslice :
        directionalSlice (absLinearLogSumExp μ a) x h = fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t) := by
      funext t
      simp [directionalSlice, absLinearLogSumExp, omegaSlice]
    -- Put the scalar `log` second-derivative formula into the textbook moment-minus-square form.
    calc
      secondDirectionalDerivative (absLinearLogSumExp μ a) x h
          = iteratedDeriv 2 (fun t : ℝ ↦ (μ : ℝ) * Real.log (omegaSlice t)) 0 := by
              rw [secondDirectionalDerivative, hslice]
      _ = (μ : ℝ) * iteratedDeriv 2 (fun t : ℝ ↦ Real.log (omegaSlice t)) 0 := hconstmul
      _ = (μ : ℝ) *
            (iteratedDeriv 2 (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * deriv omegaSlice 0 ^ (2 : ℕ) +
              deriv (fun s : ℝ ↦ Real.log s) (omegaSlice 0) * iteratedDeriv 2 omegaSlice 0) := by
            rw [hlog₂]
      _ = (μ : ℝ) *
            (-((absLinearLogSumExpOmega μ a x) ^ (2 : ℕ))⁻¹ * (((1 / (μ : ℝ)) * signedMoment) ^ (2 : ℕ)) +
              (absLinearLogSumExpOmega μ a x)⁻¹ * (((1 / (μ : ℝ)) ^ (2 : ℕ)) * quadraticMoment)) := by
            rw [hlog_base, Real.deriv_log, hω', hω'']
            simp [omegaSlice]
      _ = (1 / (μ : ℝ)) * (quadraticMoment / absLinearLogSumExpOmega μ a x) -
            (1 / (μ : ℝ)) * (signedMoment / absLinearLogSumExpOmega μ a x) ^ (2 : ℕ) := by
            field_simp [hμ, homega_pos.ne']
            ring
      _ = (1 / (μ : ℝ)) *
            ∑ i,
              ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
                absLinearLogSumExpPairWeight μ a i x -
          (1 / (μ : ℝ)) *
            (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) := by
            rw [hmoment, hlambda]

-- Proof sketch: apply the Hessian identity for `μ log (ω_μ)`:
-- `∇²(μ log ω_μ) = μ (ω_μ⁻¹ ∇²ω_μ - ω_μ⁻² ∇ω_μ ⊗ ∇ω_μ)`. Evaluating the resulting bilinear form
-- on `(h, h)` gives the weighted second-moment term minus the square of the gradient pairing.
/-- Proposition 7.14 (3): for `μ > 0`, the Hessian quadratic form of the smoothing function is
the weighted second-moment term minus the square of the gradient pairing:
`⟪∇² f_μ(x) h, h⟫`
equals the expression displayed in the textbook. -/
theorem absLinearLogSumExp_hessian_quadraticForm_eq
    (μ : {μ : ℝ // 0 < μ}) (a : ι → E) (x h : E) :
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h =
      (1 / (μ : ℝ)) *
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x -
        (1 / (μ : ℝ)) *
          (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) := by
  have hcont : ContDiffAt ℝ 2 (absLinearLogSumExp μ a) x :=
    (absLinearLogSumExp_contDiff μ a).contDiffAt
  have hdiff : DifferentiableAt ℝ (absLinearLogSumExp μ a) x :=
    hcont.differentiableAt (by norm_num)
  have hgrad : DifferentiableAt ℝ (∇ (absLinearLogSumExp μ a)) x :=
    differentiableAt_gradient_of_contDiffAt_two hcont
  -- Route correction: bridge the scalar slice formula back to the Hessian only after the slice
  -- computation is complete, rather than differentiating the vector-valued gradient directly.
  calc
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h
        = inner ℝ h (hessian (absLinearLogSumExp μ a) x h) := by
            rw [real_inner_comm]
    _ = secondDirectionalDerivative (absLinearLogSumExp μ a) x h := by
          symm
          exact secondDirectionalDerivative_eq_hessian_quadratic_form hdiff hgrad
    _ = (1 / (μ : ℝ)) *
          ∑ i,
            ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
              absLinearLogSumExpPairWeight μ a i x -
        (1 / (μ : ℝ)) *
          (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) :=
          absLinearLogSumExp_secondDirectionalDerivative_eq (μ := μ) (a := a) x h

end Differential

end FiniteFamily
