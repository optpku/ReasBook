/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_23
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Semantic recall: `lean_leansearch` surfaced `EuclideanSpace.basisFun`,
-- `EuclideanSpace.basisFun_apply`, and `pi_norm_le_iff_of_nonempty`; local
-- Chapter01 precedent keeps the Hessian Lipschitz hypothesis in the canonical
-- norm, with the `ℓ∞` statement treated as a downstream coordinatewise corollary.

noncomputable section

open scoped Gradient

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

/-- The centered finite-difference approximation of `∇ f x` with step `h`. -/
def centeredDifferenceGradientApprox (f : Point → ℝ) (x : Point) (h : ℝ) : Point :=
  WithLp.toLp 2
    (fun i ↦ (f (x + h • e i) - f (x - h • e i)) / (2 * h))

/-- The `i`-th component of `centeredDifferenceGradientApprox f x h` is the centered quotient
`(f (x + h • e_i) - f (x - h • e_i)) / (2 h)`. -/
theorem centeredDifferenceGradientApprox_apply
    (f : Point → ℝ) (x : Point) (h : ℝ) (i : Fin n) :
    centeredDifferenceGradientApprox f x h i =
      (f (x + h • e i) - f (x - h • e i)) / (2 * h) := by
  -- This is just the coordinate projection of the defining function.
  rfl

/-- Helper for Chapter03 Theorem 3.4.2: evaluating `fderiv ℝ f x` on the `i`-th coordinate
vector returns the `i`-th coordinate of `∇ f x`. -/
lemma gradient_coordinate_eq_fderiv_basisFun
    (f : Point → ℝ) (x : Point) (i : Fin n) :
    fderiv ℝ f x (e i) = (∇ f x) i := by
  -- Rewrite the derivative as the Euclidean inner product with the gradient.
  calc
    fderiv ℝ f x (e i) = inner ℝ (∇ f x) (e i) := by
      exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := e i)).symm
    _ = (∇ f x) i := by
      rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right]
      simp

/-- Helper for Chapter03 Theorem 3.4.2: a bilinear form evaluated on the repeated coordinate
step `h • e i` scales by `h ^ 2`. -/
lemma coordinate_step_hessian_eval
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ Point) ℝ)
    (h : ℝ) (i : Fin n) :
    A ![h • e i, h • e i] = h ^ 2 * A ![e i, e i] := by
  have hdiag : (![h • e i, h • e i] : Fin 2 → Point) = fun _ : Fin 2 ↦ h • e i := by
    ext j
    fin_cases j <;> rfl
  have hbasis : (![e i, e i] : Fin 2 → Point) = fun _ : Fin 2 ↦ e i := by
    ext j
    fin_cases j <;> rfl
  -- Pull the common scalar out of both slots by multilinearity.
  rw [hdiag, hbasis]
  simpa using (A.map_smul_univ (fun _ : Fin 2 ↦ h) (fun _ ↦ e i))

/-- Chapter03 Theorem 3.4.2 (1): specialized to the canonical norm used in
`Chapter01 Theorem 1.2.23`, if `f` is `C²` on an open convex set `D`, its Hessian is
`γ`-Lipschitz on `D`, and the two shifted points `x ± h • e_i` lie in `D`, then the centered
finite-difference quotient approximates the `i`-th gradient coordinate with error at most
`((γ : ℝ) / 6) * h ^ 2`. -/
theorem centeredDifferenceGradientApprox_component_error_bound
    (D : Set Point) (f : Point → ℝ) (x : Point) (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D) (hD_convex : Convex ℝ D) (hf : ContDiffOn ℝ 2 f D)
    (hHessianLipschitz :
      LipschitzOnWith γ (fun y ↦ iteratedFDeriv ℝ 2 f y) D)
    (hh : h ≠ 0)
    (i : Fin n)
    (h_add : x + h • e i ∈ D)
    (h_sub : x - h • e i ∈ D) :
    |(centeredDifferenceGradientApprox f x h - ∇ f x) i| ≤ ((γ : ℝ) / 6) * h ^ 2 := by
  let c : ℝ := (γ : ℝ) / 6
  let g : ℝ := (∇ f x) i
  let q : ℝ := (1 / 2 : ℝ) * h ^ 2 * (iteratedFDeriv ℝ 2 f x) ![e i, e i]
  let rPlus : ℝ := f (x + h • e i) - (f x + h * g + q)
  let rMinus : ℝ := f (x - h • e i) - (f x - h * g + q)
  let err : ℝ := (centeredDifferenceGradientApprox f x h - ∇ f x) i
  have he_norm : ‖e i‖ = 1 := by
    exact (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  have hmidpoint :
      AffineMap.lineMap (x + h • e i) (x - h • e i) (1 / 2 : ℝ) = x := by
    -- The current point is the midpoint of the two symmetric coordinate shifts.
    ext j
    by_cases hji : j = i
    · subst hji
      simp [AffineMap.lineMap_apply, sub_eq_add_neg]
      ring
    · simp [AffineMap.lineMap_apply, sub_eq_add_neg, EuclideanSpace.basisFun_apply, hji]
  have hx : x ∈ D := by
    -- The midpoint stays in the convex domain because both shifted endpoints do.
    have hline :
        AffineMap.lineMap (x + h • e i) (x - h • e i) (1 / 2 : ℝ) ∈ D :=
      hD_convex.lineMap_mem h_add h_sub (by constructor <;> norm_num)
    rw [hmidpoint] at hline
    exact hline
  have hplus :
      |rPlus| ≤ c * |h| ^ 3 := by
    -- Apply the Chapter 1 cubic Taylor remainder to the `+ h • e i` step and normalize it.
    have hplus0 :=
      cubicRemainderBound_of_hessian_lipschitzOn
        (D := D) (f := f) (x := x) (d := h • e i) (γ := γ)
        hD_open hD_convex hx hf hHessianLipschitz h_add
    have hgrad_plus : fderiv ℝ f x (h • e i) = h * g := by
      rw [map_smul, gradient_coordinate_eq_fderiv_basisFun]
      simp [g, smul_eq_mul]
    have hhess_plus :
        (iteratedFDeriv ℝ 2 f x) ![h • e i, h • e i] =
          h ^ 2 * (iteratedFDeriv ℝ 2 f x) ![e i, e i] :=
      coordinate_step_hessian_eval (A := iteratedFDeriv ℝ 2 f x) h i
    rw [hgrad_plus, hhess_plus] at hplus0
    simpa [c, rPlus, q, norm_smul, Real.norm_eq_abs, he_norm, mul_assoc] using hplus0
  have hminus :
      |rMinus| ≤ c * |h| ^ 3 := by
    -- Apply the same Taylor remainder to the `- h • e i` step so the quadratic term matches.
    have hminus0 :=
      cubicRemainderBound_of_hessian_lipschitzOn
        (D := D) (f := f) (x := x) (d := -h • e i) (γ := γ)
        hD_open hD_convex hx hf hHessianLipschitz (by simpa [sub_eq_add_neg] using h_sub)
    have hgrad_minus : fderiv ℝ f x (-h • e i) = -h * g := by
      rw [map_smul, gradient_coordinate_eq_fderiv_basisFun]
      simp [g, smul_eq_mul]
    have hhess_minus :
        (iteratedFDeriv ℝ 2 f x) ![-h • e i, -h • e i] =
          h ^ 2 * (iteratedFDeriv ℝ 2 f x) ![e i, e i] := by
      simpa using coordinate_step_hessian_eval (A := iteratedFDeriv ℝ 2 f x) (-h) i
    rw [hgrad_minus, hhess_minus] at hminus0
    simpa [c, rMinus, q, norm_smul, Real.norm_eq_abs, he_norm, sub_eq_add_neg, mul_assoc] using
      hminus0
  have htwoh : 2 * h ≠ 0 := mul_ne_zero (by norm_num) hh
  have hcore :
      rPlus - rMinus = (2 * h) * err := by
    -- Subtract the two Taylor expansions; the quadratic terms cancel, leaving the centered error.
    dsimp [rPlus, rMinus, q, g, err]
    rw [centeredDifferenceGradientApprox_apply]
    field_simp [htwoh]
    ring
  have hbound :
      |(2 * h) * err| ≤ 2 * (c * |h| ^ 3) := by
    -- The triangle inequality combines the two cubic remainders.
    calc
      |(2 * h) * err| = |rPlus - rMinus| := by rw [hcore]
      _ ≤ |rPlus| + |rMinus| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le rPlus (-rMinus)
      _ ≤ c * |h| ^ 3 + c * |h| ^ 3 := add_le_add hplus hminus
      _ = 2 * (c * |h| ^ 3) := by ring
  have hfactor :
      2 * (c * |h| ^ 3) = (2 * |h|) * (c * h ^ 2) := by
    -- Rewrite the cubic absolute value factor as `|h| * h^2` to cancel `2 * |h|`.
    rw [show |h| ^ 3 = |h| * h ^ 2 by
      rw [pow_succ, sq_abs]
      ring]
    ring
  have hbound' :
      (2 * |h|) * |err| ≤ (2 * |h|) * (c * h ^ 2) := by
    -- Express both sides with the same positive factor `2 * |h|`.
    rwa [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), hfactor] at hbound
  have hpos : 0 < 2 * |h| := by
    refine mul_pos (by norm_num) (abs_pos.mpr hh)
  have herr : |err| ≤ c * h ^ 2 := le_of_mul_le_mul_left hbound' hpos
  simpa [c, err] using herr

/-- Chapter03 Theorem 3.4.2 (2): under the same canonical hypotheses as part (1), the
Chapter01 coordinate `ℓ∞` owner packages the componentwise centered-difference error bounds into
a full vector estimate. -/
theorem centeredDifferenceGradientApprox_coordinateLinfty_error_bound
    (D : Set Point) (f : Point → ℝ) (x : Point) (h : ℝ) (γ : NNReal)
    (hD_open : IsOpen D) (hD_convex : Convex ℝ D) (hf : ContDiffOn ℝ 2 f D)
    (hHessianLipschitz :
      LipschitzOnWith γ (fun y ↦ iteratedFDeriv ℝ 2 f y) D)
    (hh : h ≠ 0)
    (h_step_mem :
      ∀ i : Fin n,
        x + h • e i ∈ D ∧ x - h • e i ∈ D) :
    ‖centeredDifferenceGradientApprox f x h - ∇ f x‖∞ ≤
      ((γ : ℝ) / 6) * h ^ 2 := by
  classical
  cases n with
  | zero =>
      -- In dimension `0`, there are no coordinates, so the error vector is identically zero.
      have hzero :
          centeredDifferenceGradientApprox f x h - ∇ f x = 0 := by
        ext i
        exact Fin.elim0 i
      rw [hzero, linftyNorm_eq_iSup_abs]
      simpa using (show (0 : ℝ) ≤ ((γ : ℝ) / 6) * h ^ 2 by positivity)
  | succ n' =>
      -- For `Fin (n' + 1)`, the `ℓ∞` norm is a finite maximum over coordinates.
      rw [linftyNorm_eq_finset_sup'_abs]
      refine Finset.sup'_le Finset.univ_nonempty
        (fun i : Fin (Nat.succ n') ↦ |(centeredDifferenceGradientApprox f x h - ∇ f x) i|) ?_
      intro i hi
      exact centeredDifferenceGradientApprox_component_error_bound
        D f x h γ hD_open hD_convex hf hHessianLipschitz hh i (h_step_mem i).1 (h_step_mem i).2

end
