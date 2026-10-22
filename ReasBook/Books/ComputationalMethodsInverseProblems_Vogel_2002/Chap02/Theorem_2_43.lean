/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Topology.Order.LocalExtr
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2.StronglyPositive
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_42.Taylor
import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_43.Comparison

public section

open scoped Topology

universe u v

variable {α : Type u} {β : Type v} [TopologicalSpace α] [Preorder β]

/-- Helper for Theorem 2.43: `f` has a strict local minimum at `a` when `a` is a
local minimizer and `f a < f x` holds eventually on the punctured neighborhood. -/
def IsStrictLocalMin (f : α → β) (a : α) : Prop :=
  IsLocalMin f a ∧ ∀ᶠ x in 𝓝[≠] a, f a < f x

namespace IsStrictLocalMin

/-- Helper for Theorem 2.43: a strict local minimizer is, in particular, a local
minimizer. -/
theorem isLocalMin {f : α → β} {a : α} (h : IsStrictLocalMin f a) :
    IsLocalMin f a :=
  h.1

/-- Helper for Theorem 2.43: a strict local minimizer satisfies the punctured
strict-inequality condition. -/
theorem eventually_lt {f : α → β} {a : α} (h : IsStrictLocalMin f a) :
    ∀ᶠ x in 𝓝[≠] a, f a < f x :=
  h.2

end IsStrictLocalMin

/-- Helper for Theorem 2.43: the defining specification of `IsStrictLocalMin`. -/
theorem isStrictLocalMin_iff (f : α → β) (a : α) :
    IsStrictLocalMin f a ↔ IsLocalMin f a ∧ ∀ᶠ x in 𝓝[≠] a, f a < f x :=
  Iff.rfl

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Theorem 2.43: the positive Hessian term dominates the second-order
Taylor remainder near `fStar`. -/
lemma eventuallyQuadraticLowerBoundAt
    (J : H → ℝ) (fStar : H)
    (hJ₁ : ∀ᶠ y in nhds fStar, HasFDerivAt J (fderiv ℝ J y) y)
    (hJ₂ : HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) fStar) fStar)
    (hgrad : gradient J fStar = 0)
    (hHess : (hessian J fStar).IsStronglyPositive) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x in 𝓝 fStar, J fStar + c * ‖x - fStar‖ ^ 2 ≤ J x := by
  -- Expand `J` to second order at the base point.
  rcases secondOrderTaylorFormulaAt J fStar hJ₁ hJ₂ with ⟨r, hr, hTaylor⟩
  -- Extract the quadratic coercivity constant from strong positivity.
  rcases hHess.exists_inner_lowerBound with ⟨c0, hc0, hlower⟩
  refine ⟨c0 / 4, by positivity, ?_⟩
  have hremNorm : ∀ᶠ h in 𝓝 (0 : H), ‖r h‖ ≤ (c0 / 4) * ‖‖h‖ ^ 2‖ :=
    hr.def (show 0 < c0 / 4 by positivity)
  have hrem : ∀ᶠ h in 𝓝 (0 : H), |r h| ≤ (c0 / 4) * ‖h‖ ^ 2 := by
    filter_upwards [hremNorm] with h hh
    simpa [Real.norm_eq_abs, Real.norm_of_nonneg (sq_nonneg ‖h‖)] using hh
  have hboundAtZero : ∀ᶠ h in 𝓝 (0 : H), J fStar + (c0 / 4) * ‖h‖ ^ 2 ≤ J (fStar + h) := by
    filter_upwards [hrem] with h hh
    have hremLower : -((c0 / 4) * ‖h‖ ^ 2) ≤ r h := (abs_le.mp hh).1
    have hlin : inner ℝ (gradient J fStar) h = 0 := by
      simp [hgrad]
    -- The positive quadratic Hessian term absorbs the small remainder.
    rw [hTaylor h, hlin]
    nlinarith [hlower h, hremLower]
  have hsub : Filter.Tendsto (fun x : H ↦ x - fStar) (𝓝 fStar) (𝓝 (0 : H)) := by
    have hadd :
        Filter.Tendsto (fun x : H ↦ x + -fStar) (𝓝 fStar) (𝓝 (fStar + -fStar)) := by
      exact
        (show Filter.Tendsto (fun x : H ↦ x) (𝓝 fStar) (𝓝 fStar) from Filter.tendsto_id).add
          tendsto_const_nhds
    simpa [sub_eq_add_neg] using
      hadd
  -- Transfer the lower bound from increments `h` back to points `x` near `fStar`.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    hsub.eventually hboundAtZero

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 2.43: an eventual quadratic lower bound implies local
minimality at the base point. -/
lemma isLocalMin_of_eventuallyQuadraticLowerBound
    (J : H → ℝ) (fStar : H) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ x in 𝓝 fStar, J fStar + c * ‖x - fStar‖ ^ 2 ≤ J x) :
    IsLocalMin J fStar := by
  have hconstLe : ∀ᶠ x in 𝓝 fStar, J fStar ≤ J fStar + c * ‖x - fStar‖ ^ 2 := by
    filter_upwards with x
    -- The quadratic correction term is nonnegative.
    nlinarith [hc, sq_nonneg ‖x - fStar‖]
  have hle : ∀ᶠ x in 𝓝 fStar, J fStar ≤ J x := by
    filter_upwards [hconstLe, hbound] with x hx1 hx2
    exact hx1.trans hx2
  exact Filter.EventuallyLE.isLocalMin hle rfl
    (isLocalMin_const (a := fStar) (b := J fStar))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 2.43: the same quadratic lower bound is strict on the
punctured neighborhood of `fStar`. -/
lemma eventuallyLt_of_eventuallyQuadraticLowerBound
    (J : H → ℝ) (fStar : H) {c : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ x in 𝓝 fStar, J fStar + c * ‖x - fStar‖ ^ 2 ≤ J x) :
    ∀ᶠ x in 𝓝[≠] fStar, J fStar < J x := by
  have hbound' : ∀ᶠ x in 𝓝[≠] fStar, J fStar + c * ‖x - fStar‖ ^ 2 ≤ J x :=
    hbound.filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ x in 𝓝[≠] fStar, x ≠ fStar := by
    filter_upwards [eventually_mem_nhdsWithin (s := ({fStar}ᶜ : Set H))] with x hx
    simpa using hx
  filter_upwards [hbound', hne] with x hxBound hxNe
  have hxnorm : 0 < ‖x - fStar‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxNe)
  have hxquad : 0 < c * ‖x - fStar‖ ^ 2 := by
    exact mul_pos hc (sq_pos_of_pos hxnorm)
  -- On the punctured neighborhood the positive quadratic correction is strictly positive.
  nlinarith

/-- Theorem 2.43. If `J` is twice Fréchet differentiable at `fStar`,
`gradient J fStar = 0`, and `(hessian J fStar).IsStronglyPositive`, then `fStar`
is a strict local minimizer of `J`. -/
theorem isStrictLocalMin_of_gradient_eq_zero_of_hessian_isStronglyPositive
    (J : H → ℝ) (fStar : H)
    (hJ₁ : ∀ᶠ y in nhds fStar, HasFDerivAt J (fderiv ℝ J y) y)
    (hJ₂ : HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) fStar) fStar)
    (hgrad : gradient J fStar = 0)
    (hHess : (hessian J fStar).IsStronglyPositive) :
    IsStrictLocalMin J fStar := by
  refine (isStrictLocalMin_iff J fStar).2 ?_
  -- First obtain the quantitative quadratic lower bound near `fStar`.
  rcases eventuallyQuadraticLowerBoundAt J fStar hJ₁ hJ₂ hgrad hHess with ⟨c, hc, hbound⟩
  -- Then combine the nonstrict and punctured strict conclusions.
  refine ⟨?_, ?_⟩
  · exact isLocalMin_of_eventuallyQuadraticLowerBound J fStar hc hbound
  · exact eventuallyLt_of_eventuallyQuadraticLowerBound J fStar hc hbound

namespace IsStrictLocalMin

/-- Canonical `ContDiffAt` formulation of Theorem 2.43. -/
theorem of_contDiffAt
    (J : H → ℝ) (fStar : H) (hJ : ContDiffAt ℝ 2 J fStar)
    (hgrad : gradient J fStar = 0)
    (hHess : (hessian J fStar).IsStronglyPositive) :
    IsStrictLocalMin J fStar := by
  -- Convert the `C²` assumption into the source derivative hypotheses.
  rcases hasSecondDerivativeData_of_contDiffAt J fStar hJ with ⟨hJ₁, hJ₂⟩
  exact isStrictLocalMin_of_gradient_eq_zero_of_hessian_isStronglyPositive
    J fStar hJ₁ hJ₂ hgrad hHess

end IsStrictLocalMin
