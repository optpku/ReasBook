/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerConeGeometricMean

/- Theorem 5.4.7.1 lies in the Chapter 5 power-cone / directional-derivative domain.

Sampled owner declarations:
* `powerConeGeometricMean` from `Definition_5_4_7_1`, the source-facing owner for the weighted
  geometric mean `ξ(x) = (x^(1))^α (x^(2))^(1 - α)`;
* mathlib `lineDeriv`, the canonical first directional-derivative owner;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D²f(x)[h,h]`;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for
  `D³f(x)[h,h,h]`.

Source/core/bridge triage:
* source-facing: the explicit directional-derivative formulas for the weighted geometric mean;
* core/canonical: `lineDeriv`, `secondDirectionalDerivative`, and `thirdDirectionalDerivative`
  applied to `powerConeGeometricMean α`;
* bridge/view: no extra wrapper beyond those direct owner specializations.

Primitive data:
* the exponent `α`;
* the base point `x` and direction `h`;
* positivity of the two coordinates of `x`.

Derived API:
* the explicit first-, second-, and third-directional-derivative identities below.

The file therefore keeps the source-facing formulas but states them directly on the canonical
directional-derivative owners already fixed earlier in the chapter, rather than introducing a
parallel local slice-level API.
-/

section

variable {α : ℝ} {x h : ℝ × ℝ}

local notation "ξ" => ξ[α]

local notation "gmean" => fun y : ℝ × ℝ ↦ ξ y

variable (α x h)

/-- Helper for Theorem 5.4.7.1: the affine reciprocal ratio `b / (a + t b)` differentiates to
the negative square of the same relative ratio. -/
theorem hasDerivAt_div_affine (a b t : ℝ) (ht : 0 < a + t * b) :
    HasDerivAt (fun s ↦ b / (a + s * b)) (-(b / (a + t * b)) ^ (2 : ℕ)) t := by
  -- Differentiate the affine denominator first, then apply the quotient rule.
  have haff : HasDerivAt (fun s : ℝ ↦ a + s * b) b t := by
    convert (hasDerivAt_const t a).add ((hasDerivAt_id t).mul_const b) using 1
    ring
  have hquot :
      HasDerivAt (fun s ↦ b / (a + s * b)) (((0 : ℝ) * (a + t * b) - b * b) / (a + t * b) ^ 2) t :=
    (hasDerivAt_const t b).div haff ht.ne'
  convert hquot using 1
  field_simp [ht.ne']
  ring

/-- Helper for Theorem 5.4.7.1: differentiating the scalar slice
`t ↦ ξ (x + t • h)` once produces the textbook relative-direction coefficient times the current
value of `ξ`. -/
theorem powerConeGeometricMean_slice_hasDerivAt
    (t : ℝ) (ht₁ : 0 < x.1 + t * h.1) (ht₂ : 0 < x.2 + t * h.2) :
    HasDerivAt (fun s ↦ ξ (x + s • h))
      ((α * (h.1 / (x.1 + t * h.1)) + (1 - α) * (h.2 / (x.2 + t * h.2))) * ξ (x + t • h)) t := by
  -- Differentiate each `Real.rpow` factor through its affine coordinate.
  have hcoord₁ : HasDerivAt (fun s : ℝ ↦ x.1 + s * h.1) h.1 t := by
    convert (hasDerivAt_const t x.1).add ((hasDerivAt_id t).mul_const h.1) using 1
    ring
  have hcoord₂ : HasDerivAt (fun s : ℝ ↦ x.2 + s * h.2) h.2 t := by
    convert (hasDerivAt_const t x.2).add ((hasDerivAt_id t).mul_const h.2) using 1
    ring
  have hpow₁ :
      HasDerivAt (fun s : ℝ ↦ (x.1 + s * h.1) ^ α)
        (α * (x.1 + t * h.1) ^ (α - 1) * h.1) t := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_rpow_const (x := x.1 + t * h.1) (p := α) (Or.inl ht₁.ne')).comp t hcoord₁
  have hpow₂ :
      HasDerivAt (fun s : ℝ ↦ (x.2 + s * h.2) ^ (1 - α))
        ((1 - α) * (x.2 + t * h.2) ^ ((1 - α) - 1) * h.2) t := by
    simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
      (Real.hasDerivAt_rpow_const (x := x.2 + t * h.2) (p := 1 - α) (Or.inl ht₂.ne')).comp t
        hcoord₂
  -- Rewrite the raw product-rule coefficient into the factored textbook form.
  have hraw :
      HasDerivAt (fun s ↦ ξ (x + s • h))
        (α * (x.1 + t * h.1) ^ (α - 1) * h.1 * (x.2 + t * h.2) ^ (1 - α) +
          (x.1 + t * h.1) ^ α * ((1 - α) * (x.2 + t * h.2) ^ ((1 - α) - 1) * h.2)) t := by
    simpa [powerConeGeometricMean_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hpow₁.mul hpow₂
  convert hraw using 1
  let A : ℝ := x.1 + t * h.1
  let B : ℝ := x.2 + t * h.2
  have hA : A ^ (α - 1) = A ^ α / A := by
    rw [Real.rpow_sub_one (by simpa [A] using ht₁.ne') α]
  have hB : B ^ (-α) = B ^ (1 - α) / B := by
    have hrewrite : -α = (1 - α) - 1 := by ring
    rw [hrewrite, Real.rpow_sub_one (by simpa [B] using ht₂.ne') (1 - α)]
  have hvalue : ξ (x + t • h) = A ^ α * B ^ (1 - α) := by
    simpa [A, B, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
      add_assoc] using powerConeGeometricMean_apply α (x.1 + t * h.1) (x.2 + t * h.2)
  rw [hvalue]
  simp [A, B, hA, hB, mul_comm, mul_left_comm, mul_assoc]
  field_simp [ht₁.ne', ht₂.ne']

/-- Helper for Theorem 5.4.7.1: differentiating the explicit first slice-derivative formula yields
the factored quadratic expression for the second slice derivative. -/
theorem powerConeGeometricMean_slice_firstFormula_hasDerivAt
    (t : ℝ) (ht₁ : 0 < x.1 + t * h.1) (ht₂ : 0 < x.2 + t * h.2) :
    HasDerivAt
      (fun s ↦
        (α * (h.1 / (x.1 + s * h.1)) + (1 - α) * (h.2 / (x.2 + s * h.2))) * ξ (x + s • h))
      ((-α * (1 - α) * (h.1 / (x.1 + t * h.1) - h.2 / (x.2 + t * h.2)) ^ (2 : ℕ)) *
        ξ (x + t • h)) t := by
  let delta1 : ℝ → ℝ := fun s ↦ h.1 / (x.1 + s * h.1)
  let delta2 : ℝ → ℝ := fun s ↦ h.2 / (x.2 + s * h.2)
  let coeff : ℝ → ℝ := fun s ↦ α * delta1 s + (1 - α) * delta2 s
  let g : ℝ → ℝ := fun s ↦ ξ (x + s • h)
  -- Differentiate the two relative-coordinate ratios, then the coefficient built from them.
  have hdelta1 : HasDerivAt delta1 (-(delta1 t) ^ (2 : ℕ)) t := by
    simpa [delta1] using hasDerivAt_div_affine (a := x.1) (b := h.1) (t := t) ht₁
  have hdelta2 : HasDerivAt delta2 (-(delta2 t) ^ (2 : ℕ)) t := by
    simpa [delta2] using hasDerivAt_div_affine (a := x.2) (b := h.2) (t := t) ht₂
  have hcoeff :
      HasDerivAt coeff (-(α * (delta1 t) ^ (2 : ℕ) + (1 - α) * (delta2 t) ^ (2 : ℕ))) t := by
    convert (hdelta1.const_mul α).add (hdelta2.const_mul (1 - α)) using 1
    ring
  have hg : HasDerivAt g (coeff t * g t) t := by
    simpa [coeff, g, delta1, delta2] using
      powerConeGeometricMean_slice_hasDerivAt (α := α) (x := x) (h := h) t ht₁ ht₂
  -- Combine the coefficient derivative with the slice derivative and simplify the algebra.
  have hraw :
      HasDerivAt (fun s ↦ coeff s * g s)
        (-(α * (delta1 t) ^ (2 : ℕ) + (1 - α) * (delta2 t) ^ (2 : ℕ)) * g t +
          coeff t * (coeff t * g t)) t :=
    hcoeff.mul hg
  have hraw' :
      HasDerivAt
        (fun s ↦
          (α * (h.1 / (x.1 + s * h.1)) + (1 - α) * (h.2 / (x.2 + s * h.2))) * ξ (x + s • h))
        (-(α * (delta1 t) ^ (2 : ℕ) + (1 - α) * (delta2 t) ^ (2 : ℕ)) * g t +
          coeff t * (coeff t * g t)) t := by
    simpa [g, delta1, delta2] using hraw
  convert hraw' using 1
  ring

/-- Helper for Theorem 5.4.7.1: on the positive-coordinate slice, the second iterated derivative
has the quadratic relative-direction factor from the textbook formula. -/
theorem powerConeGeometricMean_slice_secondIteratedDeriv_eq
    (t : ℝ) (ht₁ : 0 < x.1 + t * h.1) (ht₂ : 0 < x.2 + t * h.2) :
    iteratedDeriv 2 (fun s ↦ ξ (x + s • h)) t =
      (-α * (1 - α) * (h.1 / (x.1 + t * h.1) - h.2 / (x.2 + t * h.2)) ^ (2 : ℕ)) *
        ξ (x + t • h) := by
  let U : Set ℝ := {s | 0 < x.1 + s * h.1 ∧ 0 < x.2 + s * h.2}
  let g : ℝ → ℝ := fun s ↦ ξ (x + s • h)
  let g1 : ℝ → ℝ := fun s ↦
    (α * (h.1 / (x.1 + s * h.1)) + (1 - α) * (h.2 / (x.2 + s * h.2))) * g s
  have hUopen : IsOpen U := by
    simpa [U] using
      (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const h.1))).inter
        (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const h.2)))
  have hderiv_eq : Set.EqOn (deriv g) g1 U := by
    refine deriv_eqOn hUopen ?_
    intro s hs
    have hslice :=
      powerConeGeometricMean_slice_hasDerivAt (α := α) (x := x) (h := h) s hs.1 hs.2
    simpa [g, g1] using hslice.hasDerivWithinAt
  have hEventually : deriv g =ᶠ[nhds t] g1 := by
    filter_upwards [hUopen.mem_nhds (by simpa [U] using And.intro ht₁ ht₂)] with s hs
    exact hderiv_eq hs
  -- Replace `deriv g` near `t` by the explicit first-derivative formula and differentiate once
  -- more.
  calc
    iteratedDeriv 2 (fun s ↦ ξ (x + s • h)) t = deriv (deriv g) t := by
      simp [g, iteratedDeriv_succ]
    _ = deriv g1 t := hEventually.deriv_eq
    _ =
        (-α * (1 - α) * (h.1 / (x.1 + t * h.1) - h.2 / (x.2 + t * h.2)) ^ (2 : ℕ)) *
          ξ (x + t • h) := by
        simpa [g1, g] using
          (powerConeGeometricMean_slice_firstFormula_hasDerivAt (α := α) (x := x) (h := h) t
            ht₁ ht₂).deriv

/-- Helper for Theorem 5.4.7.1: differentiating the explicit second slice-derivative formula gives
the factored cubic expression used in the textbook third-derivative identity. -/
theorem powerConeGeometricMean_slice_secondFormula_hasDerivAt
    (t : ℝ) (ht₁ : 0 < x.1 + t * h.1) (ht₂ : 0 < x.2 + t * h.2) :
    HasDerivAt
      (fun s ↦
        (-α * (1 - α) * (h.1 / (x.1 + s * h.1) - h.2 / (x.2 + s * h.2)) ^ (2 : ℕ)) *
          ξ (x + s • h))
      (-((-α * (1 - α) * (h.1 / (x.1 + t * h.1) - h.2 / (x.2 + t * h.2)) ^ (2 : ℕ)) *
          ξ (x + t • h)) *
        ((2 - α) * (h.1 / (x.1 + t * h.1)) + (1 + α) * (h.2 / (x.2 + t * h.2)))) t := by
  let delta1 : ℝ → ℝ := fun s ↦ h.1 / (x.1 + s * h.1)
  let delta2 : ℝ → ℝ := fun s ↦ h.2 / (x.2 + s * h.2)
  let coeff1 : ℝ → ℝ := fun s ↦ α * delta1 s + (1 - α) * delta2 s
  let coeff2 : ℝ → ℝ := fun s ↦ -α * (1 - α) * (delta1 s - delta2 s) ^ (2 : ℕ)
  let g : ℝ → ℝ := fun s ↦ ξ (x + s • h)
  -- Differentiate the relative-direction difference and then the quadratic second-order factor.
  have hdelta1 : HasDerivAt delta1 (-(delta1 t) ^ (2 : ℕ)) t := by
    simpa [delta1] using hasDerivAt_div_affine (a := x.1) (b := h.1) (t := t) ht₁
  have hdelta2 : HasDerivAt delta2 (-(delta2 t) ^ (2 : ℕ)) t := by
    simpa [delta2] using hasDerivAt_div_affine (a := x.2) (b := h.2) (t := t) ht₂
  have hdiff :
      HasDerivAt (fun s ↦ delta1 s - delta2 s)
        (-(delta1 t) ^ (2 : ℕ) + (delta2 t) ^ (2 : ℕ)) t := by
    simpa using hdelta1.sub hdelta2
  have hcoeff2 :
      HasDerivAt coeff2
        (α * (1 - α) * (delta1 t - delta2 t) ^ (2 : ℕ) * (2 * (delta1 t + delta2 t))) t := by
    have hsquare :
        HasDerivAt (fun s ↦ (delta1 s - delta2 s) ^ (2 : ℕ))
          (2 * (delta1 t - delta2 t) * (-(delta1 t) ^ (2 : ℕ) + (delta2 t) ^ (2 : ℕ))) t := by
      simpa using hdiff.pow 2
    have hraw :
        HasDerivAt (fun s ↦ coeff2 s)
          ((-α * (1 - α)) *
            (2 * (delta1 t - delta2 t) * (-(delta1 t) ^ (2 : ℕ) + (delta2 t) ^ (2 : ℕ)))) t := by
      simpa [coeff2] using hsquare.const_mul (-α * (1 - α))
    convert hraw using 1
    ring
  have hg : HasDerivAt g (coeff1 t * g t) t := by
    simpa [coeff1, g, delta1, delta2] using
      powerConeGeometricMean_slice_hasDerivAt (α := α) (x := x) (h := h) t ht₁ ht₂
  -- Combine the second-order coefficient derivative with the derivative of `ξ`.
  have hraw :
      HasDerivAt (fun s ↦ coeff2 s * g s)
        (α * (1 - α) * (delta1 t - delta2 t) ^ (2 : ℕ) * (2 * (delta1 t + delta2 t)) * g t +
          coeff2 t * (coeff1 t * g t)) t :=
    hcoeff2.mul hg
  have hraw' :
      HasDerivAt
        (fun s ↦
          (-α * (1 - α) * (h.1 / (x.1 + s * h.1) - h.2 / (x.2 + s * h.2)) ^ (2 : ℕ)) *
            ξ (x + s • h))
        (α * (1 - α) * (delta1 t - delta2 t) ^ (2 : ℕ) * (2 * (delta1 t + delta2 t)) * g t +
          coeff2 t * (coeff1 t * g t)) t := by
    simpa [coeff1, coeff2, g, delta1, delta2] using hraw
  convert hraw' using 1
  ring

/-- Helper for Theorem 5.4.7.1: on the positive-coordinate slice, the third iterated derivative
is the negative of the second one times the stated affine relative-direction factor. -/
theorem powerConeGeometricMean_slice_thirdIteratedDeriv_eq
    (t : ℝ) (ht₁ : 0 < x.1 + t * h.1) (ht₂ : 0 < x.2 + t * h.2) :
    iteratedDeriv 3 (fun s ↦ ξ (x + s • h)) t =
      -iteratedDeriv 2 (fun s ↦ ξ (x + s • h)) t *
        ((2 - α) * (h.1 / (x.1 + t * h.1)) + (1 + α) * (h.2 / (x.2 + t * h.2))) := by
  let U : Set ℝ := {s | 0 < x.1 + s * h.1 ∧ 0 < x.2 + s * h.2}
  let g : ℝ → ℝ := fun s ↦ ξ (x + s • h)
  let g1 : ℝ → ℝ := fun s ↦
    (α * (h.1 / (x.1 + s * h.1)) + (1 - α) * (h.2 / (x.2 + s * h.2))) * g s
  let g2 : ℝ → ℝ := fun s ↦
    (-α * (1 - α) * (h.1 / (x.1 + s * h.1) - h.2 / (x.2 + s * h.2)) ^ (2 : ℕ)) * g s
  have hUopen : IsOpen U := by
    simpa [U] using
      (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const h.1))).inter
        (isOpen_lt continuous_const (continuous_const.add (continuous_id.mul_const h.2)))
  have hderiv_g_eq : Set.EqOn (deriv g) g1 U := by
    refine deriv_eqOn hUopen ?_
    intro s hs
    have hslice :=
      powerConeGeometricMean_slice_hasDerivAt (α := α) (x := x) (h := h) s hs.1 hs.2
    simpa [g, g1] using hslice.hasDerivWithinAt
  have hderiv_g1_eq : Set.EqOn (deriv g1) g2 U := by
    refine deriv_eqOn hUopen ?_
    intro s hs
    simpa [g1, g2, g] using
      (powerConeGeometricMean_slice_firstFormula_hasDerivAt (α := α) (x := x) (h := h) s hs.1
        hs.2).hasDerivWithinAt
  have hEventually1 : deriv g =ᶠ[nhds t] g1 := by
    filter_upwards [hUopen.mem_nhds (by simpa [U] using And.intro ht₁ ht₂)] with s hs
    exact hderiv_g_eq hs
  have hEventually2 : deriv g1 =ᶠ[nhds t] g2 := by
    filter_upwards [hUopen.mem_nhds (by simpa [U] using And.intro ht₁ ht₂)] with s hs
    exact hderiv_g1_eq hs
  -- Replace the lower derivatives by their explicit formulas in a neighborhood, then
  -- differentiate the quadratic slice formula once more.
  calc
    iteratedDeriv 3 (fun s ↦ ξ (x + s • h)) t = deriv (deriv (deriv g)) t := by
      simp [g, iteratedDeriv_succ]
    _ = deriv (deriv g1) t := hEventually1.deriv.deriv_eq
    _ = deriv g2 t := hEventually2.deriv_eq
    _ =
        -iteratedDeriv 2 (fun s ↦ ξ (x + s • h)) t *
          ((2 - α) * (h.1 / (x.1 + t * h.1)) + (1 + α) * (h.2 / (x.2 + t * h.2))) := by
        have hsecond :=
          powerConeGeometricMean_slice_secondIteratedDeriv_eq (α := α) (x := x) (h := h) t
            ht₁ ht₂
        rw [hsecond]
        simpa [g2, g] using
          (powerConeGeometricMean_slice_secondFormula_hasDerivAt (α := α) (x := x) (h := h) t
            ht₁ ht₂).deriv

variable {α x h}

-- Proof sketch: differentiate the directional slice
-- `t ↦ ξ (x + t • h)` at `t = 0`, use the positive coordinate assumptions to identify the
-- derivatives of the two `Real.rpow` factors, and factor out `ξ x`.
/-- Theorem 5.4.7.1 (1): the first directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`Dξ(x)[h] = [α (h^(1) / x^(1)) + (1 - α) (h^(2) / x^(2))] ξ(x)`. -/
theorem powerConeGeometricMean_firstDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    lineDeriv ℝ ξ x h =
      (α * (h.1 / x.1) + (1 - α) * (h.2 / x.2)) * ξ x := by
  -- The line derivative is the slice derivative at `t = 0`.
  have hline :
      HasLineDerivAt ℝ ξ ((α * (h.1 / x.1) + (1 - α) * (h.2 / x.2)) * ξ x) x h := by
    simpa [HasLineDerivAt] using
      (powerConeGeometricMean_slice_hasDerivAt (α := α) (x := x) (h := h) 0
        (by simpa using hx₁) (by simpa using hx₂))
  simpa using hline.lineDeriv

-- Proof sketch: differentiate the first-derivative identity once more along the same direction
-- `h`; the derivative of `h.1 / x.1` contributes `-(h.1 / x.1)^2` and similarly for the second
-- coordinate, after which the algebra simplifies to
-- `-α (1 - α) ((h.1 / x.1) - (h.2 / x.2))^2 ξ(x)`.
/-- Theorem 5.4.7.1 (2): the second directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D²ξ(x)[h,h] = -α (1 - α) ((h^(1) / x^(1)) - (h^(2) / x^(2)))² ξ(x)`. -/
theorem powerConeGeometricMean_secondDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    secondDirectionalDerivative ξ x h =
      (-α * (1 - α) * (h.1 / x.1 - h.2 / x.2) ^ (2 : ℕ)) * ξ x := by
  -- Evaluate the slice-level second-derivative formula at `t = 0`.
  simpa [secondDirectionalDerivative, directionalSlice] using
    powerConeGeometricMean_slice_secondIteratedDeriv_eq (α := α) (x := x) (h := h) 0
      (by simpa using hx₁) (by simpa using hx₂)

-- Proof sketch: differentiate the second-derivative identity from part `(2)` along `h`, use the
-- first-derivative formula from part `(1)` to rewrite the derivative of `ξ`, and factor out the
-- common term `D²ξ(x)[h,h]`.
/-- Theorem 5.4.7.1 (3): the third directional derivative of
`ξ(x) = (x^(1))^α (x^(2))^(1 - α)` at a point with positive coordinates satisfies
`D³ξ(x)[h,h,h] =
  -D²ξ(x)[h,h] ((2 - α) (h^(1) / x^(1)) + (1 + α) (h^(2) / x^(2)))`. -/
theorem powerConeGeometricMean_thirdDirectionalDerivative
    (hx₁ : 0 < x.1) (hx₂ : 0 < x.2)
    :
    thirdDirectionalDerivative ξ x h =
      -secondDirectionalDerivative ξ x h *
        ((2 - α) * (h.1 / x.1) + (1 + α) * (h.2 / x.2)) := by
  -- Evaluate the slice-level third-derivative formula at `t = 0`.
  simpa [thirdDirectionalDerivative, secondDirectionalDerivative, directionalSlice] using
    powerConeGeometricMean_slice_thirdIteratedDeriv_eq (α := α) (x := x) (h := h) 0
      (by simpa using hx₁) (by simpa using hx₂)

end
