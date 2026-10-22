/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Recall
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

section Generic

/- Definition 5.0.10 lies in the chapter's directional differential-calculus domain.

Sampled owner declarations:
* mathlib `HasLineDerivAt`, the canonical owner for first directional derivatives along affine
  lines;
* mathlib `lineDeriv`, the totalized directional derivative operator corresponding to
  `t ↦ f (x + t • u)` at `t = 0`;
* mathlib `DifferentiableAt.lineDeriv_eq_fderiv` and `inner_gradient_left`, the primitive
  first-order bridge from directional derivatives to gradient pairings;
* `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for the second Fréchet derivative of
  a real-valued function on a Hilbert space;
* `iteratedFDeriv`, the canonical multilinear owner for the third Fréchet derivative.

Source/core/bridge triage:
* source-facing: the directional slice `t ↦ f (x + t • u)` and its first, second, and third
  derivatives at `0`;
* core/canonical: `lineDeriv ℝ f x u` for the first derivative and `hessian f x` for the
  second-order quadratic form;
* bridge/view: the identification of the third directional derivative with
  `iteratedFDeriv ℝ 3 f x (fun _ ↦ u)` under `C³` regularity.

Primitive data:
* a function `f`;
* a base point `x`;
* a direction `u`.

Derived API:
* the source-facing slice `directionalSlice f x u`;
* the owner-level first directional derivative `lineDeriv ℝ f x u`;
* the Hessian quadratic form `inner ℝ u (hessian f x u)`;
* the Fréchet third-derivative bridge for smooth functions.

The slice itself remains source-facing, but the first- and second-order derived API should reuse
the canonical owners `lineDeriv` and `hessian` instead of repeating their raw formulas. -/

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Semantic recall: `iteratedDeriv_vcomp_two`, `iteratedDeriv_vcomp_three`, and
-- `iteratedFDeriv_two_apply` are the mathlib bridge lemmas for the `C²`/`C³` slice identities.

/-- Definition 5.0.10: the directional slice of `f` at `x` along `u` is the univariate function
`t ↦ f (x + t • u)`, from which the first, second, and third directional derivatives at `x` in
the direction `u` are taken at `t = 0`. -/
def directionalSlice (f : E → ℝ) (x u : E) : ℝ → ℝ :=
  fun t ↦ f (x + t • u)

/-- Evaluating the directional slice gives the textbook formula `φ(x; t) = f (x + t u)`. -/
@[simp] theorem directionalSlice_apply (f : E → ℝ) (x u : E) (t : ℝ) :
    directionalSlice f x u t = f (x + t • u) := rfl

/- The textbook first directional derivative at `x` along `u` is the canonical owner
`lineDeriv ℝ f x u`, i.e. the derivative at `0` of the slice `t ↦ f (x + t • u)`. -/
recall lineDeriv

/-- Eq. (5.u22): the textbook first directional derivative at `x` along `u` is the derivative at
`0` of the directional slice `φ(x; ·)`. -/
@[simp] theorem lineDeriv_eq_deriv_directionalSlice (f : E → ℝ) (x u : E) :
    lineDeriv ℝ f x u = deriv (directionalSlice f x u) 0 := rfl

/-- The second directional derivative is the second iterated derivative at `0` of the directional
slice. -/
def secondDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 2 (directionalSlice f x u) 0

/-- The third directional derivative is the third iterated derivative at `0` of the directional
slice. -/
def thirdDirectionalDerivative (f : E → ℝ) (x u : E) : ℝ :=
  iteratedDeriv 3 (directionalSlice f x u) 0

/-- The third directional derivative is odd in the direction argument. -/
@[simp] theorem thirdDirectionalDerivative_neg (f : E → ℝ) (x u : E) :
    thirdDirectionalDerivative f x (-u) = -thirdDirectionalDerivative f x u := by
  rw [thirdDirectionalDerivative]
  have hs : directionalSlice f x (-u) = fun t ↦ directionalSlice f x u (-t) := by
    funext t
    simp [directionalSlice]
  rw [hs]
  calc
    iteratedDeriv 3 (fun t ↦ directionalSlice f x u (-t)) 0
      = (-1 : ℝ) ^ (3 : ℕ) * iteratedDeriv 3 (directionalSlice f x u) 0 := by
          simpa [smul_eq_mul] using
            (iteratedDeriv_comp_neg 3 (directionalSlice f x u) 0)
    _ = -thirdDirectionalDerivative f x u := by
      norm_num [thirdDirectionalDerivative]

/-- Helper for Definition 5.0.10: affine lines in a real normed space differentiate to their
direction vector. -/
private theorem affineLineHasDerivAt
    (x u : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x + s • u) u t := by
  -- Differentiate scalar multiplication first and then translate by the base point.
  simpa [one_smul] using ((hasDerivAt_id t).smul_const u).const_add x

/-- Helper for Definition 5.0.10: affine lines have vanishing second iterated derivative. -/
private theorem affineLineIteratedDerivTwo
    (x u : E) :
    iteratedDeriv 2 (fun s : ℝ ↦ x + s • u) = fun _ : ℝ ↦ (0 : E) := by
  -- Differentiate the affine line once to a constant, then differentiate that constant again.
  funext t
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (fun s : ℝ ↦ x + s • u) = fun _ : ℝ ↦ u := by
    funext s
    exact (affineLineHasDerivAt x u s).deriv
  rw [hderiv, deriv_const]

/-- Helper for Definition 5.0.10: affine lines have vanishing third iterated derivative. -/
private theorem affineLineIteratedDerivThree
    (x u : E) :
    iteratedDeriv 3 (fun s : ℝ ↦ x + s • u) = fun _ : ℝ ↦ (0 : E) := by
  -- Once the second iterated derivative is zero, one more derivative stays zero.
  funext t
  rw [iteratedDeriv_succ, affineLineIteratedDerivTwo, deriv_const]

/-- For a `C³` function, the third directional derivative is the third Fréchet derivative of `f`
evaluated on the triple `(u, u, u)`. -/
-- Proof sketch: differentiate the slice three times and rewrite the result as evaluation of the
-- canonical trilinear map `iteratedFDeriv ℝ 3 f x` on the constant tuple `u`.
theorem thirdDirectionalDerivative_eq_iteratedFDeriv
    {f : E → ℝ} {x u : E} (hf : ContDiffAt ℝ 3 f x) :
    thirdDirectionalDerivative f x u = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) := by
  let line : ℝ → E := fun s ↦ x + s • u
  have hline₃ : ContDiffAt ℝ 3 line 0 := by
    -- The inner affine line is smooth, so the cubic chain rule applies to the slice.
    fun_prop
  have hcomp := iteratedDeriv_vcomp_three (by simpa [line] using hf) hline₃
  have hline_deriv : deriv line 0 = u := by
    -- The affine line has constant derivative equal to the direction vector.
    simpa [line] using (affineLineHasDerivAt x u 0).deriv
  have hzero_left : iteratedFDeriv ℝ 2 f x ![(0 : E), u] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 0 rfl
  have hzero_right : iteratedFDeriv ℝ 2 f x ![u, (0 : E)] = 0 := by
    exact (iteratedFDeriv ℝ 2 f x).map_coord_zero 1 rfl
  -- Collapse the cubic chain rule because every higher derivative of the affine line vanishes.
  rw [thirdDirectionalDerivative]
  calc
    iteratedDeriv 3 (fun s : ℝ ↦ f (x + s • u)) 0
        = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) +
            iteratedFDeriv ℝ 2 f x ![(0 : E), u] +
            2 • iteratedFDeriv ℝ 2 f x ![u, (0 : E)] := by
              simpa [line, directionalSlice, Function.comp, hline_deriv,
                affineLineIteratedDerivTwo, affineLineIteratedDerivThree] using hcomp
    _ = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) := by
      simp [hzero_left, hzero_right]

/-- Eq. (5.u24): on an open domain where `f` is `C³`, the third directional
derivative at `x ∈ dom` is the third Fréchet derivative evaluated on `(u, u, u)`. -/
theorem thirdDirectionalDerivative_eq_iteratedFDeriv_of_mem
    {dom : Set E} {f : E → ℝ} (hdom_open : IsOpen dom) (hcont : ContDiffOn ℝ 3 f dom)
    {x u : E} (hx : x ∈ dom) :
    thirdDirectionalDerivative f x u = iteratedFDeriv ℝ 3 f x (fun _ ↦ u) := by
  exact thirdDirectionalDerivative_eq_iteratedFDeriv (hcont.contDiffAt (hdom_open.mem_nhds hx))

end Generic

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Under differentiability, the textbook gradient pairing formula for the directional derivative is
the direct combination of the canonical bridge lemmas `DifferentiableAt.lineDeriv_eq_fderiv` and
`inner_gradient_left`. -/
recall DifferentiableAt.lineDeriv_eq_fderiv
recall inner_gradient_left

omit [CompleteSpace H] in
/-- Helper for Definition 5.0.10: differentiating the directional slice at `t` is the line
derivative of `f` at `x + t • u` along the same direction. -/
private theorem deriv_directionalSlice_eq_lineDeriv_shift
    (f : H → ℝ) (x u : H) (t : ℝ) :
    deriv (directionalSlice f x u) t = lineDeriv ℝ f (x + t • u) u := by
  -- Recenter the scalar slice so the derivative is taken at zero on the shifted affine line.
  calc
    deriv (directionalSlice f x u) t
        = deriv (fun s : ℝ ↦ directionalSlice f x u (s + t)) 0 := by
            simpa using (deriv_comp_add_const (directionalSlice f x u) t 0).symm
    _ = lineDeriv ℝ f (x + t • u) u := by
      congr 1
      funext s
      simp [directionalSlice, add_smul, add_assoc, add_comm]

omit [CompleteSpace H] in
/-- Helper for Definition 5.0.10: the second directional derivative is the derivative at `0` of
the shifted line-derivative profile. -/
private theorem secondDirectionalDerivative_eq_deriv_lineDerivProfile
    (f : H → ℝ) (x u : H) :
    secondDirectionalDerivative f x u = deriv (fun t : ℝ ↦ lineDeriv ℝ f (x + t • u) u) 0 := by
  -- Rewrite the second iterated derivative through the first derivative of the directional slice.
  rw [secondDirectionalDerivative, iteratedDeriv_succ, iteratedDeriv_one]
  congr 1
  funext t
  exact deriv_directionalSlice_eq_lineDeriv_shift f x u t

/-- Helper for Definition 5.0.10: if `f` is differentiable at the shifted base point, then the
derivative of the directional slice is the gradient pairing with the fixed direction. -/
private theorem deriv_directionalSlice_eq_gradientPairing_shift
    {f : H → ℝ} {x u : H} {t : ℝ}
    (hf : DifferentiableAt ℝ f (x + t • u)) :
    deriv (directionalSlice f x u) t = inner ℝ (∇ f (x + t • u)) u := by
  -- Rewrite the slice derivative as a line derivative, then use the gradient owner formula.
  calc
    deriv (directionalSlice f x u) t = lineDeriv ℝ f (x + t • u) u := by
      exact deriv_directionalSlice_eq_lineDeriv_shift f x u t
    _ = fderiv ℝ f (x + t • u) u := hf.lineDeriv_eq_fderiv
    _ = inner ℝ (∇ f (x + t • u)) u := by
      simpa using (inner_gradient_left hf).symm

/-- Helper for Definition 5.0.10: differentiating the gradient pairing along an affine line gives
the Hessian quadratic form at the base point. -/
private theorem gradientPairingAlongAffineLine_hasDerivAt
    {f : H → ℝ} {x u : H} (hgrad : DifferentiableAt ℝ (∇ f) x) :
    HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f (x + t • u)) u)
      (inner ℝ u (hessian f x u)) 0 := by
  have hLine :
      HasDerivAt (fun t : ℝ ↦ ∇ f (x + t • u))
        ((hessian f x) u) 0 := by
    -- Differentiate the gradient field along the affine line.
    simpa [hessian] using hgrad.hasFDerivAt.hasLineDerivAt u
  have hu : HasDerivAt (fun _ : ℝ ↦ u) 0 0 := hasDerivAt_const 0 u
  -- Pair the differentiated gradient with the fixed direction `u`.
  simpa [real_inner_comm] using hLine.inner ℝ hu

/-- Helper for Definition 5.0.10: the repeated second Fréchet derivative evaluated on `u` matches
the Hessian quadratic form at a `C²` point. -/
private theorem iteratedFDerivTwo_eq_hessian_quadratic_form
    {f : H → ℝ} {x u : H} (hcont : ContDiffAt ℝ 2 f x) :
    iteratedFDeriv ℝ 2 f x (fun _ ↦ u) = inner ℝ u (hessian f x u) := by
  let D : StrongDual ℝ H →L[ℝ] H :=
    (InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff_C1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := by
    exact hcont.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) x := by
    exact hfdiff_C1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hgradFDeriv :
      HasFDerivAt (∇ f) (D.comp (fderiv ℝ (fderiv ℝ f) x)) x := by
    -- Read the gradient through the inverse Riesz map applied to the Fréchet derivative.
    simpa [gradient, D] using D.hasFDerivAt.comp x hfdiff.hasFDerivAt
  have hhess :
      hessian f x = D.comp (fderiv ℝ (fderiv ℝ f) x) := by
    simpa [hessian] using hgradFDeriv.fderiv
  have hhess_apply :
      hessian f x u = D ((fderiv ℝ (fderiv ℝ f) x) u) := by
    simpa [ContinuousLinearMap.comp_apply] using congrArg (fun L : H →L[ℝ] H ↦ L u) hhess
  let y : StrongDual ℝ H := (fderiv ℝ (fderiv ℝ f) x) u
  have hRiesz : inner ℝ (D y) u = y u := InnerProductSpace.toDual_symm_apply
  calc
    iteratedFDeriv ℝ 2 f x (fun _ ↦ u) = ((fderiv ℝ (fderiv ℝ f) x) u) u := by
      simpa using iteratedFDeriv_two_apply f x (fun _ ↦ u)
    _ = inner ℝ (D ((fderiv ℝ (fderiv ℝ f) x) u)) u := by
      -- Rewrite the covector evaluation through the inverse Riesz map before commuting the
      -- real inner product.
      change ((fderiv ℝ (fderiv ℝ f) x) u) u = inner ℝ (D y) u
      exact hRiesz.symm
    _ = inner ℝ u (D ((fderiv ℝ (fderiv ℝ f) x) u)) := by
      rw [real_inner_comm]
    _ = inner ℝ u (hessian f x u) := by
      rw [hhess_apply]

/-- If `f` is `C²` at `x`, then the second directional derivative equals the Hessian quadratic
form in the direction `u`. -/
-- Proof sketch: apply the quadratic chain rule to the affine slice `t ↦ x + t • u`, then
-- identify the resulting repeated second Fréchet derivative with the Hessian quadratic form.
theorem secondDirectionalDerivative_eq_hessian_quadratic_form
    {f : H → ℝ} {x u : H} (hcont : ContDiffAt ℝ 2 f x) :
    secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := by
  let line : ℝ → H := fun t ↦ x + t • u
  have hline₂ : ContDiffAt ℝ 2 line 0 := by
    -- The affine line is `C²`, so the quadratic chain rule applies to the slice.
    fun_prop
  have hcomp := iteratedDeriv_vcomp_two (by simpa [line] using hcont) hline₂
  have hline_deriv : deriv line 0 = u := by
    simpa [line] using (affineLineHasDerivAt x u 0).deriv
  calc
    secondDirectionalDerivative f x u = iteratedFDeriv ℝ 2 f x (fun _ ↦ u) := by
      rw [secondDirectionalDerivative]
      have hs : directionalSlice f x u = f ∘ line := by
        funext t
        simp [directionalSlice, line]
      have hcomp' :
          iteratedDeriv 2 (f ∘ line) 0 = iteratedFDeriv ℝ 2 f x (fun _ ↦ u) := by
        simpa [line, directionalSlice, Function.comp, hline_deriv, affineLineIteratedDerivTwo] using
          hcomp
      simpa [hs] using hcomp'
    _ = inner ℝ u (hessian f x u) := by
      exact iteratedFDerivTwo_eq_hessian_quadratic_form hcont

/-- Eq. (5.u22): on an open domain where `f` is `C³`, the first directional
derivative at `x ∈ dom` is the gradient pairing `⟪∇ f(x), u⟫`. -/
theorem lineDeriv_eq_inner_gradient_of_mem
    {dom : Set H} {f : H → ℝ} (hdom_open : IsOpen dom) (hcont : ContDiffOn ℝ 3 f dom)
    {x u : H} (hx : x ∈ dom) :
    lineDeriv ℝ f x u = inner ℝ (∇ f x) u := by
  have hcontAt : ContDiffAt ℝ 3 f x := hcont.contDiffAt (hdom_open.mem_nhds hx)
  have hdiff : DifferentiableAt ℝ f x := hcontAt.differentiableAt (by norm_num)
  calc
    lineDeriv ℝ f x u = fderiv ℝ f x u := hdiff.lineDeriv_eq_fderiv
    _ = inner ℝ (∇ f x) u := by
      simpa using (inner_gradient_left hdiff).symm

/-- Eq. (5.u23): on an open domain where `f` is `C³`, the second directional
derivative at `x ∈ dom` is the Hessian quadratic form `⟪∇² f(x) u, u⟫`. -/
theorem secondDirectionalDerivative_eq_hessian_quadratic_form_of_mem
    {dom : Set H} {f : H → ℝ} (hdom_open : IsOpen dom) (hcont : ContDiffOn ℝ 3 f dom)
    {x u : H} (hx : x ∈ dom) :
    secondDirectionalDerivative f x u = inner ℝ u (hessian f x u) := by
  have hcont₂ : ContDiffOn ℝ 2 f dom := by
    exact hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  exact secondDirectionalDerivative_eq_hessian_quadratic_form
    (hcont₂.contDiffAt (hdom_open.mem_nhds hx))

end Hilbert

end
