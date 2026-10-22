/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_23
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient PositiveDefMatrixNorm SmoothConvex

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.15 lies in the Chapter 7 smoothing / weighted-seminorm smoothness domain.

Sampled owner-style declarations:
- `absLinearLogSumExp_contDiff` in `Proposition_7_14`
- `absLinearLogSumExp_hessian_quadraticForm_eq` in `Proposition_7_14`
- `positiveDefMatrixNorm` in `Definition_7_23`
- `ConvexC1SeminormSmooth.dualNorm_gradient_sub_le` in `Chap02/Theorem_2_5`

Best owner abstraction:
- source-facing: the weighted `G`-norm Hessian and gradient estimates for `absLinearLogSumExp μ a`
- core/canonical: `absLinearLogSumExp μ a ∈ 𝓕[L, positiveDefMatrixNorm G.1 G.2]¹¹`
- bridge/view: the explicit Hessian quadratic-form bound and its source-facing dual-gradient
  Lipschitz corollary

Primitive data:
- the family `a : Fin m → E`
- the positive-definite matrix owner `G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}`
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`
- the weighted dual-norm bound on the vectors `a i`

Derived API:
- `ContDiff ℝ 2 (absLinearLogSumExp μ a)`, already owned by `Proposition_7_14`
- the weighted Hessian quadratic-form upper bound
- the owner-level smooth-convex membership theorem
- the source-facing weighted dual-gradient Lipschitz estimate

Source/core/bridge triage:
- source-facing: the weighted Hessian and gradient bounds
- core/canonical: the smooth-convex owner `𝓕[L, p]¹¹`
- bridge/view: the explicit quadratic-form estimate needed to enter that owner API

The previous conjunction theorem duplicated the upstream owner `absLinearLogSumExp_contDiff` and
attached the weighted-norm hypothesis `ha` to a smoothness statement that does not use it. This
refinement keeps only the genuinely new weighted estimates and routes the gradient conclusion
through the Chapter 2 owner API. -/

section

variable (a : Fin m → E) (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) {ν : ℝ}
variable (μ : {μ : ℝ // 0 < μ})
variable (ha : ∀ i : Fin m, ‖a i‖[G,*] ≤ ν * Real.sqrt n)

/-- Helper for Proposition 7.15: the dual `G`-norm bound on `a i` controls each squared pairing
`⟪aᵢ, h⟫²` by `ν² n ‖h‖_G²`. -/
theorem sq_inner_le_weighted_dual_bound
    (ha_bound : ∀ i : Fin m, ‖a i‖[G,*] ≤ ν * Real.sqrt n) (h : E) (i : Fin m) :
    (inner ℝ (a i) h) ^ (2 : ℕ) ≤ ((ν ^ (2 : ℕ)) * (n : ℝ)) * ‖h‖[G] ^ (2 : ℕ) := by
  -- Control the pairing by the weighted dual norm and then square the resulting scalar bound.
  have habs :
      |inner ℝ (a i) h| ≤ ‖a i‖[G,*] * ‖h‖[G] := by
    refine abs_le.mpr ?_
    constructor
    · have hneg :=
        Seminorm.inner_le_dualNorm_mul
          (positiveDefMatrixNorm G.1 G.2) (-h) (a i)
      simpa [inner_neg_right, map_neg_eq_map, neg_mul] using hneg
    · simpa [mul_comm] using
        (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G.1 G.2) h (a i))
  have hnorm_nonneg : 0 ≤ ‖h‖[G] := by
    positivity
  have hweighted :
      |inner ℝ (a i) h| ≤ (ν * Real.sqrt n) * ‖h‖[G] :=
    habs.trans <| mul_le_mul_of_nonneg_right (ha_bound i) hnorm_nonneg
  have hsq :
      (inner ℝ (a i) h) ^ (2 : ℕ) ≤ ((ν * Real.sqrt n) * ‖h‖[G]) ^ (2 : ℕ) := by
    have hle := abs_le.mp hweighted
    nlinarith
  have hsqrt : (Real.sqrt n) ^ (2 : ℕ) = (n : ℝ) := by
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity))
  calc
    (inner ℝ (a i) h) ^ (2 : ℕ) ≤ ((ν * Real.sqrt n) * ‖h‖[G]) ^ (2 : ℕ) := hsq
    _ = ((ν ^ (2 : ℕ)) * (n : ℝ)) * ‖h‖[G] ^ (2 : ℕ) := by
      rw [mul_pow, mul_pow, hsqrt]

/-- Helper for Proposition 7.15: the squared gradient-pairing term in Proposition 7.14 is
bounded by the corresponding weighted second moment. -/
theorem lambda_pairing_sq_le_weighted_second_moment [Nonempty (Fin m)] (x h : E) :
    (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) ≤
      ∑ i,
        ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
          absLinearLogSumExpPairWeight μ a i x := by
  let ω : ℝ := absLinearLogSumExpOmega μ a x
  let pair : Fin m → ℝ := fun i ↦ absLinearLogSumExpPairWeight μ a i x
  let b : Fin m → ℝ := fun i ↦ inner ℝ (a i) h
  let w : Fin m → ℝ := fun i ↦ pair i / ω
  let c : Fin m → ℝ := fun i ↦ |b i|
  have hω_pos : 0 < ω := by
    simpa [ω] using absLinearLogSumExpOmega_pos (μ := μ) (a := a) x
  have hpair_pos : ∀ i : Fin m, 0 < pair i := by
    intro i
    dsimp [pair]
    exact add_pos (Real.exp_pos _) (Real.exp_pos _)
  have hw_pos : ∀ i : Fin m, 0 < w i := by
    intro i
    exact div_pos (hpair_pos i) hω_pos
  have hsum_w : ∑ i, w i = 1 := by
    calc
      ∑ i, w i = ∑ i, pair i / ω := by rfl
      _ = (∑ i, pair i) / ω := by rw [Finset.sum_div]
      _ = ω / ω := by rfl
      _ = 1 := by field_simp [hω_pos.ne']
  have hterm_abs :
      ∀ i : Fin m, |absLinearLogSumExpLambda μ a i x * b i| ≤ w i * c i := by
    intro i
    have hnum_abs :
        |Real.exp (inner ℝ (a i) x / (μ : ℝ)) -
            Real.exp (-(inner ℝ (a i) x / (μ : ℝ)))| ≤
          pair i := by
      refine abs_le.mpr ?_
      constructor <;> dsimp [pair] <;> nlinarith [Real.exp_pos (inner ℝ (a i) x / (μ : ℝ)),
        Real.exp_pos (-(inner ℝ (a i) x / (μ : ℝ)))]
    have hlambda_abs : |absLinearLogSumExpLambda μ a i x| ≤ w i := by
      have hdiv := div_le_div_of_nonneg_right hnum_abs hω_pos.le
      rw [absLinearLogSumExpLambda_eq, abs_div, abs_of_pos hω_pos]
      simpa [ω, w, pair] using hdiv
    calc
      |absLinearLogSumExpLambda μ a i x * b i| =
          |absLinearLogSumExpLambda μ a i x| * c i := by
            simp [b, c, abs_mul]
      _ ≤ w i * c i := mul_le_mul_of_nonneg_right hlambda_abs (abs_nonneg (b i))
  have hsum_abs :
      |∑ i, absLinearLogSumExpLambda μ a i x * b i| ≤
        ∑ i, w i * c i := by
    calc
      |∑ i, absLinearLogSumExpLambda μ a i x * b i| ≤
          ∑ i, |absLinearLogSumExpLambda μ a i x * b i| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun i : Fin m ↦ absLinearLogSumExpLambda μ a i x * b i) Finset.univ)
      _ ≤ ∑ i, w i * c i := Finset.sum_le_sum fun i hi ↦ hterm_abs i
  have hsum_sq :
      (∑ i, absLinearLogSumExpLambda μ a i x * b i) ^ (2 : ℕ) ≤
        (∑ i, w i * c i) ^ (2 : ℕ) := by
    have hle := abs_le.mp hsum_abs
    nlinarith
  have htitu :
      (∑ i, w i * c i) ^ (2 : ℕ) ≤ ∑ i, w i * c i ^ (2 : ℕ) := by
    have htitu0 :=
      Finset.sq_sum_div_le_sum_sq_div
        (Finset.univ : Finset (Fin m))
        (fun i ↦ w i * c i) (g := w) (fun i hi ↦ hw_pos i)
    calc
      (∑ i, w i * c i) ^ (2 : ℕ) = ((∑ i, w i * c i) ^ (2 : ℕ)) / (∑ i, w i) := by
        rw [hsum_w, div_one]
      _ ≤ ∑ i, (w i * c i) ^ (2 : ℕ) / w i := htitu0
      _ = ∑ i, w i * c i ^ (2 : ℕ) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hw_ne : w i ≠ 0 := (hw_pos i).ne'
        field_simp [pow_two, hw_ne]
  -- Route correction: package the variance bound with normalized weights before returning to the
  -- explicit Hessian formula from Proposition 7.14.
  calc
    (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) ≤
        (∑ i, w i * c i) ^ (2 : ℕ) := by simpa [b] using hsum_sq
    _ ≤ ∑ i, w i * c i ^ (2 : ℕ) := htitu
    _ = ∑ i, ((inner ℝ (a i) h) ^ (2 : ℕ) / absLinearLogSumExpOmega μ a x) *
          absLinearLogSumExpPairWeight μ a i x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [w, c, b, pair, ω]
          rw [sq_abs]
          ring

/-- Helper for Proposition 7.15: the Hessian quadratic form of `absLinearLogSumExp` is
nonnegative in every direction. -/
theorem absLinearLogSumExp_hessian_quadraticForm_nonneg (x h : E) :
    0 ≤ inner ℝ (hessian (absLinearLogSumExp μ a) x h) h := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · letI := hm
    -- In the empty-family branch the smoothing collapses to the zero function.
    have hzero : absLinearLogSumExp μ a = fun _ : E ↦ 0 :=
      absLinearLogSumExp_eq_zero_of_isEmpty μ a hm
    simpa [hzero]
  · let ω : ℝ := absLinearLogSumExpOmega μ a x
    let secondMoment : ℝ :=
      ∑ i,
        ((inner ℝ (a i) h) ^ (2 : ℕ) / ω) *
          absLinearLogSumExpPairWeight μ a i x
    let pairing : ℝ :=
      (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ)
    have hpairing_le : pairing ≤ secondMoment := by
      simpa [ω, secondMoment, pairing] using
        lambda_pairing_sq_le_weighted_second_moment (μ := μ) (a := a) x h
    have hmain :
        0 ≤ (1 / (μ : ℝ)) * secondMoment - (1 / (μ : ℝ)) * pairing := by
      have hμinv_nonneg : 0 ≤ 1 / (μ : ℝ) := by
        exact one_div_nonneg.mpr μ.property.le
      nlinarith [hpairing_le]
    -- Rewrite the Hessian using Proposition 7.14 and interpret it as a weighted variance.
    simpa [ω, secondMoment, pairing] using
      (show 0 ≤
        (1 / (μ : ℝ)) *
            ∑ i,
              ((inner ℝ (a i) h) ^ (2 : ℕ) / ω) *
                absLinearLogSumExpPairWeight μ a i x -
          (1 / (μ : ℝ)) *
            (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) by
          simpa using hmain)

include a G ν μ ha
-- Proof sketch: combine Proposition 7.14 with the chapter owner `positiveDefMatrixNorm`: the
-- smoothness is `absLinearLogSumExp_contDiff`, the Hessian quadratic form is
-- `absLinearLogSumExp_hessian_quadraticForm_eq`, and the weighted dual-norm bound on the `aᵢ`
-- controls the second-moment term by `ν² n / μ`.
/-- Proposition 7.15: if `‖aᵢ‖_G^* ≤ ν √n` for every `i`, then the Hessian quadratic form of
`f_μ(x) = μ log ∑ᵢ (exp(⟪aᵢ, x⟫ / μ) + exp(-⟪aᵢ, x⟫ / μ))`
is bounded above by `(ν² n / μ) ‖h‖_G²`. The `C²` regularity is already the owner theorem
`absLinearLogSumExp_contDiff` from `Proposition_7_14`. -/
theorem absLinearLogSumExp_hessian_quadraticForm_le (x h : E) :
    inner ℝ (hessian (absLinearLogSumExp μ a) x h) h ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖h‖[G] ^ (2 : ℕ) := by
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · letI := hm
    -- In the empty-family branch the smoothing is identically zero, so the Hessian vanishes.
    have hzero : absLinearLogSumExp μ a = fun _ : E ↦ 0 :=
      absLinearLogSumExp_eq_zero_of_isEmpty μ a hm
    simpa [hzero] using
      (show (0 : ℝ) ≤ (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖h‖[G] ^ (2 : ℕ) by positivity)
  · let ω : ℝ := absLinearLogSumExpOmega μ a x
    let secondMoment : ℝ :=
      ∑ i,
        ((inner ℝ (a i) h) ^ (2 : ℕ) / ω) *
          absLinearLogSumExpPairWeight μ a i x
    let pairing : ℝ :=
      (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ)
    let coeff : ℝ := ((ν ^ (2 : ℕ)) * (n : ℝ)) * ‖h‖[G] ^ (2 : ℕ)
    have hω_pos : 0 < ω := by
      simpa [ω] using absLinearLogSumExpOmega_pos (μ := μ) (a := a) x
    have hsecondMoment_le : secondMoment ≤ coeff := by
      calc
        secondMoment ≤
            ∑ i, (coeff / ω) * absLinearLogSumExpPairWeight μ a i x := by
              refine Finset.sum_le_sum fun i hi ↦ ?_
              have hdiv_le :
                  (inner ℝ (a i) h) ^ (2 : ℕ) / ω ≤ coeff / ω :=
                div_le_div_of_nonneg_right
                  (sq_inner_le_weighted_dual_bound
                    (a := a) (G := G) (ν := ν) ha h i)
                  hω_pos.le
              have hpair_nonneg : 0 ≤ absLinearLogSumExpPairWeight μ a i x := by
                exact (add_pos (Real.exp_pos _) (Real.exp_pos _)).le
              exact mul_le_mul_of_nonneg_right hdiv_le hpair_nonneg
        _ = (coeff / ω) * ∑ i, absLinearLogSumExpPairWeight μ a i x := by
            rw [Finset.mul_sum]
        _ = (coeff / ω) * ω := by rfl
        _ = coeff := by field_simp [hω_pos.ne']
    have hmain :
        (1 / (μ : ℝ)) * secondMoment - (1 / (μ : ℝ)) * pairing ≤
          (1 / (μ : ℝ)) * coeff := by
      have hpairing_nonneg : 0 ≤ pairing := by
        dsimp [pairing]
        positivity
      have hμinv_nonneg : 0 ≤ 1 / (μ : ℝ) := by
        exact one_div_nonneg.mpr μ.property.le
      nlinarith [hsecondMoment_le, hpairing_nonneg]
    -- Rewrite the Hessian using Proposition 7.14 and drop the nonnegative variance correction.
    simpa [ω, secondMoment, pairing, coeff] using
      (show
        (1 / (μ : ℝ)) *
            ∑ i,
              ((inner ℝ (a i) h) ^ (2 : ℕ) / ω) *
                absLinearLogSumExpPairWeight μ a i x -
          (1 / (μ : ℝ)) *
            (∑ i, absLinearLogSumExpLambda μ a i x * inner ℝ (a i) h) ^ (2 : ℕ) ≤
          (1 / (μ : ℝ)) * coeff by
          simpa using hmain)

-- Proof sketch: `absLinearLogSumExp_contDiff μ` gives the regularity input, while
-- `absLinearLogSumExp_hessian_quadraticForm_le` supplies the upper Hessian bound. Combine these
-- with the Chapter 2 owner bridge `convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded` to
-- place `absLinearLogSumExp μ a` in the smooth-convex class for the weighted norm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The Chapter 2 smooth-convex owner view of Proposition 7.15 for the weighted norm `‖·‖_G`. -/
theorem absLinearLogSumExp_mem_F11_positiveDefMatrixNorm :
    absLinearLogSumExp μ a ∈
      𝓕[Real.toNNReal ((((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ))), positiveDefMatrixNorm G.1 G.2]¹¹ :=
  by
    have hcoef_nonneg : 0 ≤ (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) := by
      exact div_nonneg (mul_nonneg (sq_nonneg ν) (show 0 ≤ (n : ℝ) by positivity)) μ.property.le
    -- Feed the lower and upper Hessian bounds into the Chapter 2 `𝓕[L, p]¹¹` bridge.
    refine
      (convexC1SeminormSmooth_iff_hessian_quadratic_form_bounded
        (p := positiveDefMatrixNorm G.1 G.2)
        (L := Real.toNNReal ((((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ))))
        (f := absLinearLogSumExp μ a)
        (hf_C2 := absLinearLogSumExp_contDiff μ a)).2 ?_
    intro x h
    constructor
    · have hnonneg :
          0 ≤ inner ℝ (hessian (absLinearLogSumExp μ a) x h) h :=
          absLinearLogSumExp_hessian_quadraticForm_nonneg (a := a) (μ := μ) x h
      exact hnonneg
    · simpa [Real.toNNReal_of_nonneg hcoef_nonneg] using
        absLinearLogSumExp_hessian_quadraticForm_le
          (a := a) (G := G) (ν := ν) (ha := ha) x h

-- Proof sketch: apply the owner theorem
-- `absLinearLogSumExp_mem_F11_positiveDefMatrixNorm`, then specialize the defining
-- `dualNorm_gradient_sub_le` consequence of `𝓕[L, p]¹¹` to the weighted seminorm
-- `positiveDefMatrixNorm G.1 G.2`.
/-- The gradient of the log-sum-exp smoothing is Lipschitz with respect to the `G`-norm and its
dual norm, with constant `ν² n / μ`. -/
theorem absLinearLogSumExp_dual_gradient_sub_le (x y : E) :
    ‖∇ (absLinearLogSumExp μ a) x - ∇ (absLinearLogSumExp μ a) y‖[G,*] ≤
      (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) * ‖x - y‖[G] := by
  have hcoef_nonneg : 0 ≤ (((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ)) := by
    exact div_nonneg (mul_nonneg (sq_nonneg ν) (show 0 ≤ (n : ℝ) by positivity)) μ.property.le
  have hf :
      absLinearLogSumExp μ a ∈
        𝓕[Real.toNNReal ((((ν ^ (2 : ℕ)) * (n : ℝ)) / (μ : ℝ))),
          positiveDefMatrixNorm G.1 G.2]¹¹ :=
    absLinearLogSumExp_mem_F11_positiveDefMatrixNorm
  -- The owner theorem immediately gives the weighted dual-gradient Lipschitz estimate.
  simpa [Real.toNNReal_of_nonneg hcoef_nonneg] using hf.dualNorm_gradient_sub_le x y

omit a G ν μ ha

end

end
