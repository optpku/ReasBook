/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Prop_2_34
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Convex.Basic

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 2.38. The source states this for a closed convex subset `C` of a real Hilbert
space `H`; the conclusion already follows from convexity alone. If `fStar ∈ C` is a local
constrained minimizer of `J` on `C` and `J` is Fréchet differentiable at `fStar`, then every
feasible displacement `f - fStar` with `f ∈ C` has nonnegative inner product with
`gradient J fStar`. -/
theorem inner_gradient_sub_nonneg_of_isLocalMinOn (J : H → ℝ) {C : Set H} {fStar f : H}
    (hC_convex : Convex ℝ C) (hfStar : fStar ∈ C)
    (hmin : IsLocalMinOn J C fStar) (hJ : DifferentiableAt ℝ J fStar) (hf : f ∈ C) :
    0 ≤ inner ℝ (gradient J fStar) (f - fStar) := by
  have h_endpoint : fStar + (f - fStar) ∈ C := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hf
  have h_tangent : f - fStar ∈ posTangentConeAt C fStar :=
    mem_posTangentConeAt_of_segment_subset (hC_convex.segment_subset hfStar h_endpoint)
  have h_nonneg : 0 ≤ (fderiv ℝ J fStar) (f - fStar) :=
    hmin.hasFDerivWithinAt_nonneg hJ.hasFDerivAt.hasFDerivWithinAt h_tangent
  rw [hJ.hasGradientAt.fderiv_apply] at h_nonneg
  exact h_nonneg
