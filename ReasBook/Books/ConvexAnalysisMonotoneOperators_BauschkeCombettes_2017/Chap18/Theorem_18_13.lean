/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped ERealFunction Gradient InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section StrongerDifferentiabilityBounds

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The scalar modulus `ψ` attached to a one-dimensional control function `φ`. -/
noncomputable def ψ (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun s ↦ if s = 0 then 0 else φ s / |s|

/-- The auxiliary modulus `ψ` vanishes at the origin by definition. -/
@[simp] theorem psi_zero (φ : ℝ → ℝ) :
    ψ φ 0 = 0 := by
  simp [ψ]

/-- Away from the origin, `ψ φ` is the quotient `φ(s) / |s|`. -/
theorem psi_eq_div_abs_of_ne (φ : ℝ → ℝ) {s : ℝ} (hs : s ≠ 0) :
    ψ φ s = φ s / |s| := by
  simp [ψ, hs]

/-- The scalar integral modulus `θ` attached to `φ`.

Lean's interval integral is total, so the source-facing owner is defined directly from `φ`; the
theorem-level convexity hypotheses are what make this the intended integral in the textbook
situation. -/
noncomputable def θ (φ : ℝ → ℝ) : ℝ → ℝ :=
  fun s ↦ ∫ t in (0 : ℝ)..1, φ (s * t) / t

/-- Evaluating `θ φ` at `s` gives the interval integral from its definition. -/
@[simp] theorem theta_apply (φ : ℝ → ℝ) (s : ℝ) :
    θ φ s = ∫ t in (0 : ℝ)..1, φ (s * t) / t := by
  simp [θ]

/-- The admissible nonnegative parameters in the defining inequality for the scalar control
function `ϱ`. -/
def varrhoSet (φ : ℝ → ℝ) (s : ℝ) : Set ℝ :=
  {ν : ℝ | 0 ≤ ν ∧ 2 * ((θ φ).toEReal.asEReal)∗ ν ≤ (ν * s : EReal)}

private theorem convexOn_toEReal_univ {φ : ℝ → ℝ}
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ) :
    ConvexOn φ.toEReal (effectiveDomain φ.toEReal) := by
  refine ⟨by simp [Function.effectiveDomain_toEReal], ?_, ?_⟩
  · simp [Function.effectiveDomain_toEReal]
  · intro x hx y hy α hα0 hα1
    have hx' : x ∈ Set.univ := by
      simp
    have hy' : y ∈ Set.univ := by
      simp
    have hineq :
        φ (α • x + (1 - α) • y) ≤ α * φ x + (1 - α) * φ y :=
      hφ_conv.2 hx' hy' hα0.le (sub_nonneg.mpr hα1.le) (by ring)
    have hineqE :
        (((φ (α • x + (1 - α) • y) : ℝ) : EReal)) ≤
          (((α * φ x + (1 - α) * φ y : ℝ) : EReal)) := by
      exact_mod_cast hineq
    have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    simpa [Function.toEReal_apply, smul_eq_mul, hsub_cast, EReal.coe_add, EReal.coe_mul] using
      hineqE

private theorem phi_nonneg_of_even_convex_eq_zero_iff
    {φ : ℝ → ℝ} (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) :
    ∀ s : ℝ, 0 ≤ φ s := by
  have hmin :
      (0 : ℝ) ∈ Argmin (φ.toEReal).asEReal :=
    zero_mem_argmin_of_even_convexOn φ.toEReal
      (convexOn_toEReal_univ hφ_conv) (by
        intro s
        simpa using hφ_even s)
  have hzero : φ 0 = 0 :=
    (hφ_zero 0).2 rfl
  intro s
  have hs_min :
      (φ.toEReal).asEReal 0 ≤ (φ.toEReal).asEReal s :=
    isMinOn_univ_iff.mp (mem_argmin_iff.mp hmin) s
  have hs_minE : ((φ 0 : ℝ) : EReal) ≤ ((φ s : ℝ) : EReal) := by
    simpa [Function.toEReal_apply, Function.asEReal_apply] using hs_min
  have hs_min' : φ 0 ≤ φ s := by
    exact_mod_cast hs_minE
  simpa [hzero] using hs_min'

/- Theorem 18.13 is source-facing. The scalar owners are the direct textbook functions `ψ`, `θ`,
and `ϱ`; `varrhoSet` is only their derived support API. -/

/-- Membership in the admissible set for `ϱ` is exactly the defining pair of conditions
`ν ≥ 0` and `2 θ*(ν) ≤ ν s`. -/
@[simp] theorem mem_varrhoSet
    (φ : ℝ → ℝ) (s ν : ℝ) :
    ν ∈ varrhoSet φ s ↔
      0 ≤ ν ∧ 2 * ((θ φ).toEReal.asEReal)∗ ν ≤ (ν * s : EReal) :=
  Iff.rfl

/-- Under the source hypotheses of Theorem 18.13, the admissible set defining `ϱ(s)` is
nonempty. -/
theorem varrhoSet_nonempty
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    (varrhoSet φ s).Nonempty := sorry

/-- Under the source hypotheses of Theorem 18.13, the admissible set defining `ϱ(s)` is bounded
above in `ℝ`. -/
theorem varrhoSet_bddAbove
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    BddAbove (varrhoSet φ s) := sorry

/-- The canonical `EReal` supremum underlying the scalar control function `ϱ`. -/
noncomputable def varrhoSup (φ : ℝ → ℝ) : ℝ → EReal :=
  fun s ↦ sSup ((((↑) : ℝ → EReal) '' varrhoSet φ s) : Set EReal)

/-- Evaluating the canonical `EReal` supremum owner for `ϱ` rewrites it as the corresponding image
supremum. -/
@[simp] theorem varrhoSup_apply (φ : ℝ → ℝ) (s : ℝ) :
    varrhoSup φ s = sSup ((((↑) : ℝ → EReal) '' varrhoSet φ s) : Set EReal) :=
  rfl

/-- Under the source hypotheses of Theorem 18.13, the canonical `EReal` supremum defining `ϱ(s)`
is not `-∞`. -/
theorem varrhoSup_ne_bot
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    varrhoSup φ s ≠ ⊥ := sorry

/-- Under the source hypotheses of Theorem 18.13, the canonical `EReal` supremum defining `ϱ(s)`
is finite. -/
theorem varrhoSup_lt_top
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    varrhoSup φ s < ⊤ := sorry

/-- Under the source hypotheses of Theorem 18.13, the scalar control function `ϱ` attached to `φ`
is the real number represented by the finite `EReal` supremum `varrhoSup φ s`. -/
noncomputable def ϱ
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) :
    ℝ → ℝ :=
  fun s ↦
    let _ := varrhoSup_ne_bot φ hφ_even hφ_conv hφ_zero s
    let _ := ne_of_lt (varrhoSup_lt_top φ hφ_even hφ_conv hφ_zero s)
    (varrhoSup φ s).toReal

/-- Evaluating `ϱ φ` at `s` gives the real representative of the finite `EReal` supremum
`varrhoSup φ s`. -/
@[simp] theorem varrho_apply
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    ϱ φ hφ_even hφ_conv hφ_zero s = (varrhoSup φ s).toReal :=
  rfl

/-- Coercing the real-valued source-facing owner `ϱ` to `EReal` recovers the canonical supremum
owner `varrhoSup`. -/
@[simp] theorem varrho_asEReal
    (φ : ℝ → ℝ) (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0) (s : ℝ) :
    ((ϱ φ hφ_even hφ_conv hφ_zero s : ℝ) : EReal) = varrhoSup φ s := by
  have hs_bot : varrhoSup φ s ≠ ⊥ :=
    varrhoSup_ne_bot φ hφ_even hφ_conv hφ_zero s
  have hs_top : varrhoSup φ s ≠ ⊤ :=
    ne_of_lt (varrhoSup_lt_top φ hφ_even hφ_conv hφ_zero s)
  simpa [ϱ] using (EReal.coe_toReal hs_top hs_bot)

variable (φ : ℝ → ℝ)

-- Proof sketch: apply Cauchy--Schwarz to bound the inner product by
-- `‖x - y‖ * ‖∇ f x - ∇ f y‖`, then invoke the assumed `ψ`-control and the identity
-- `ψ(r) * r = φ(r)` for `r = ‖x - y‖`.
/-- Theorem 18.13 (1): the pointwise gradient norm bound by `ψ` implies the scalar inner-product
bound by `φ`. -/
theorem gradient_inner_le_phi_of_gradient_norm_bound_by_psi
    (gradf : H → H)
    (hφ_zero_nonneg : 0 ≤ φ 0)
    (hi : ∀ x y : H, ‖gradf x - gradf y‖ ≤ ψ φ ‖x - y‖) (x y : H) :
    ⟪x - y, gradf x - gradf y⟫_ℝ ≤ φ ‖x - y‖ := sorry

-- Proof sketch: integrate along the segment `x + t • (y - x)`. The Fréchet derivative identifies
-- the derivative of `t ↦ f (x + t • (y - x))` with the inner product against `∇ f`, and the
-- hypothesis from clause (ii) bounds the integrand by `φ (t * ‖x - y‖) / t`, whose integral is
-- `θ φ ‖x - y‖`.
variable [CompleteSpace H]

/-- Theorem 18.13 (2): the scalar inner-product bound by `φ` implies the usual descent estimate
with remainder `θ`. -/
theorem descent_le_linearization_add_theta_of_gradient_inner_le_phi
    (f : H → ℝ) (gradf : H → H)
    (hgrad : ∀ x : H, HasGradientAt f (gradf x) x)
    (hii : ∀ x y : H, ⟪x - y, gradf x - gradf y⟫_ℝ ≤ φ ‖x - y‖) (x y : H) :
    f y ≤ f x + ⟪y - x, gradf x⟫_ℝ + θ φ ‖x - y‖ := sorry

omit [CompleteSpace H] in
/-- Theorem 18.13 (3): the descent estimate with remainder `θ` implies the Fenchel-conjugate
lower bound involving `θ*` along the gradient image. -/
theorem conjugate_gradient_ge_affine_add_thetaConjugate_of_descent_le_linearization_add_theta
    (f : H → ℝ) (gradf : H → H)
    (hφ_even : Function.Even φ)
    (hiii : ∀ x y : H, f y ≤ f x + ⟪y - x, gradf x⟫_ℝ + θ φ ‖x - y‖)
    (x y : H) :
    (f.toEReal.asEReal)∗ (gradf y) ≥
      (f.toEReal.asEReal)∗ (gradf x) +
        (⟪x, gradf y - gradf x⟫_ℝ : EReal) +
          ((θ φ).toEReal.asEReal)∗ ‖gradf x - gradf y‖ := sorry

omit [CompleteSpace H] in
/-- Theorem 18.13 (4): the Fenchel-conjugate lower bound implies the lower bound
`⟪x - y, ∇f(x) - ∇f(y)⟫ ≥ 2 θ*(‖∇f(x) - ∇f(y)‖)`. -/
theorem gradient_inner_ge_two_thetaConjugate_of_conjugate_gradient_ge_affine_add_thetaConjugate
    (f : H → ℝ) (gradf : H → H)
    (hiv :
      ∀ x y : H,
        (f.toEReal.asEReal)∗ (gradf y) ≥
          (f.toEReal.asEReal)∗ (gradf x) +
            (⟪x, gradf y - gradf x⟫_ℝ : EReal) +
              ((θ φ).toEReal.asEReal)∗ ‖gradf x - gradf y‖)
    (x y : H) :
    (⟪x - y, gradf x - gradf y⟫_ℝ : EReal) ≥
      2 * ((θ φ).toEReal.asEReal)∗ ‖gradf x - gradf y‖ := sorry

omit [CompleteSpace H] in
/-- Theorem 18.13 (5): the lower bound by `2 θ*` implies the gradient norm estimate controlled by
`ϱ`. -/
theorem gradient_norm_le_varrho_of_gradient_inner_ge_two_thetaConjugate
    (gradf : H → H)
    (hφ_even : Function.Even φ)
    (hφ_conv : _root_.ConvexOn ℝ Set.univ φ)
    (hφ_zero : ∀ s : ℝ, φ s = 0 ↔ s = 0)
    (hv :
      ∀ x y : H,
        (⟪x - y, gradf x - gradf y⟫_ℝ : EReal) ≥
          2 * ((θ φ).toEReal.asEReal)∗ ‖gradf x - gradf y‖)
    (x y : H) :
    ‖gradf x - gradf y‖ ≤ ϱ φ hφ_even hφ_conv hφ_zero ‖x - y‖ := sorry

end StrongerDifferentiabilityBounds

end

end ERealFunction
