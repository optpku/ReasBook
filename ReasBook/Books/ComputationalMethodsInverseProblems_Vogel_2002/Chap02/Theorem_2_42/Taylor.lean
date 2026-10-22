/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_40
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.InnerProductSpace.Rayleigh

public section

open Asymptotics

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Reusable Taylor-expansion helper for Theorem 2.42 and Theorem 2.43: explicit first- and
second-derivative data at `f` yield the second-order expansion with an `o (‖h‖ ^ 2)` remainder. -/
theorem secondOrderTaylorFormulaAt (J : H → ℝ) (f : H)
    (hJ₁ : ∀ᶠ y in nhds f, HasFDerivAt J (fderiv ℝ J y) y)
    (hJ₂ : HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) f) f) :
    ∃ r : H → ℝ,
      r =o[nhds (0 : H)] (fun h ↦ ‖h‖ ^ 2) ∧
      ∀ h : H,
        J (f + h) = J f + inner ℝ (gradient J f) h +
          (1 / 2 : ℝ) * inner ℝ (hessian J f h) h + r h := by
  let A : H →L[ℝ] H →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ J) f
  let r : H → ℝ := fun h ↦
    J (f + h) - J f - (fderiv ℝ J f) h -
      (1 / 2 : ℝ) * (hessian J f).reApplyInnerSelf h
  have hsymm : IsSymmSndFDerivAt ℝ J f := by
    intro v w
    exact second_derivative_symmetric_of_eventually hJ₁ hJ₂ v w
  have hHessSelfAdjoint : IsSelfAdjoint (hessian J f) :=
    hessian_isSelfAdjoint_of_isSymmSndFDerivAt J f hsymm
  have hquad :
      ∀ x : H,
        HasFDerivAt
          (fun h : H ↦ (1 / 2 : ℝ) * (hessian J f).reApplyInnerSelf h)
          (A x) x := by
    intro x
    have hstrict :
        HasStrictFDerivAt
          (fun h : H ↦ (1 / 2 : ℝ) * (hessian J f).reApplyInnerSelf h)
          ((1 / 2 : ℝ) • (2 • innerSL ℝ ((hessian J f) x))) x := by
      exact
        (LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf
          hHessSelfAdjoint.isSymmetric x).const_smul (1 / 2 : ℝ)
    refine hstrict.hasFDerivAt.congr_fderiv ?_
    ext y
    simp [A, hessian_inner]
  rcases Metric.mem_nhds_iff.mp hJ₁ with ⟨ε, hεpos, hε⟩
  let s : Set H := Metric.ball (0 : H) ε
  have hsConv : Convex ℝ s := by
    simpa [s] using convex_ball (0 : H) ε
  have h0s : (0 : H) ∈ s := by
    exact Metric.mem_ball_self hεpos
  have hsNhd : s ∈ nhds (0 : H) := by
    simpa [s] using Metric.ball_mem_nhds (0 : H) hεpos
  have hff' :
      ∀ x ∈ s,
        HasFDerivWithinAt r (fderiv ℝ J (f + x) - fderiv ℝ J f - A x) s x := by
    intro x hx
    have hxJ : HasFDerivAt J (fderiv ℝ J (f + x)) (f + x) := by
      apply hε
      simpa [s, Metric.mem_ball, dist_eq_norm] using hx
    have hshift :
        HasFDerivAt (fun h : H ↦ J (f + h)) (fderiv ℝ J (f + x)) x := by
      exact hxJ.comp x ((hasFDerivAt_id x).const_add f)
    have hlin :
        HasFDerivAt (fun h : H ↦ (fderiv ℝ J f) h) (fderiv ℝ J f) x := by
      simpa using (fderiv ℝ J f).hasFDerivAt
    exact (((hshift.sub_const (J f)).sub hlin).sub (hquad x)).hasFDerivWithinAt
  have hsmall0 :
      (fun x : H ↦ fderiv ℝ J (f + x) - fderiv ℝ J f - A x) =o[nhds (0 : H)]
        fun x ↦ x := by
    simpa [A] using (hasFDerivAt_iff_isLittleO_nhds_zero.1 hJ₂)
  have hsmall :
      (fun x : H ↦ fderiv ℝ J (f + x) - fderiv ℝ J f - A x) =o[nhdsWithin (0 : H) s]
        fun x ↦ ‖x - (0 : H)‖ ^ 1 := by
    have hnorm :
        (fun x : H ↦ fderiv ℝ J (f + x) - fderiv ℝ J f - A x) =o[nhds (0 : H)]
          fun x ↦ ‖x‖ := by
      rw [isLittleO_norm_right]
      simpa using hsmall0
    simpa [pow_one] using hnorm.mono nhdsWithin_le_nhds
  have hzero : r 0 = 0 := by
    simp [r, ContinuousLinearMap.reApplyInnerSelf_apply]
  have hrWithin' :
      (fun h ↦ r h - r 0) =o[nhdsWithin (0 : H) s] fun h ↦ ‖h‖ ^ 2 := by
    simpa [pow_two] using hsConv.isLittleO_pow_succ (x₀ := (0 : H)) h0s hff' hsmall
  have hrWithin : r =o[nhdsWithin (0 : H) s] fun h ↦ ‖h‖ ^ 2 := by
    simpa [hzero] using hrWithin'
  have hr : r =o[nhds (0 : H)] fun h ↦ ‖h‖ ^ 2 := by
    have hseq : s =ᶠ[nhds (0 : H)] (Set.univ : Set H) := by
      filter_upwards [hsNhd] with x hx
      exact propext <| by
        constructor
        · intro _
          exact trivial
        · intro _
          exact hx
    rw [show nhdsWithin (0 : H) s = nhds (0 : H) by
      calc
        nhdsWithin (0 : H) s = nhdsWithin (0 : H) (Set.univ : Set H) :=
          (nhdsWithin_eq_iff_eventuallyEq.2 hseq)
        _ = nhds (0 : H) := by simp] at hrWithin
    exact hrWithin
  refine ⟨r, hr, ?_⟩
  intro h
  have hEq :
      J (f + h) =
        J f + (fderiv ℝ J f) h +
          (1 / 2 : ℝ) * (hessian J f).reApplyInnerSelf h + r h := by
    dsimp [r]
    ring
  have hgrad : (fderiv ℝ J f) h = inner ℝ (gradient J f) h := by
    rw [← inner_gradient_left (f := J) (x := f) (y := h)]
  have hhess : (hessian J f).reApplyInnerSelf h = inner ℝ (hessian J f h) h := by
    simp [ContinuousLinearMap.reApplyInnerSelf_apply]
  calc
    J (f + h) =
        J f + (fderiv ℝ J f) h +
          (1 / 2 : ℝ) * (hessian J f).reApplyInnerSelf h + r h := hEq
    _ = J f + inner ℝ (gradient J f) h +
          (1 / 2 : ℝ) * inner ℝ (hessian J f h) h + r h := by
      rw [hgrad, hhess]

omit [CompleteSpace H] in
/-- Reusable Taylor-expansion helper: a `C²` hypothesis at `f` provides the first- and
second-derivative data required by `secondOrderTaylorFormulaAt`. -/
theorem hasSecondDerivativeData_of_contDiffAt
    (J : H → ℝ) (f : H) (hJ : ContDiffAt ℝ 2 J f) :
    (∀ᶠ y in nhds f, HasFDerivAt J (fderiv ℝ J y) y) ∧
      HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) f) f := by
  have hJevent : ∀ᶠ y in nhds f, ContDiffAt ℝ 2 J y :=
    hJ.eventually (by norm_num)
  have hJ₁ : ∀ᶠ y in nhds f, HasFDerivAt J (fderiv ℝ J y) y := by
    filter_upwards [hJevent] with y hy
    exact (hy.differentiableAt (by norm_num)).hasFDerivAt
  have hJfderiv : ContDiffAt ℝ 1 (fderiv ℝ J) f := by
    simpa using hJ.fderiv_right_succ
  have hJ₂ : HasFDerivAt (fderiv ℝ J) (fderiv ℝ (fderiv ℝ J) f) f :=
    hJfderiv.differentiableAt_one.hasFDerivAt
  exact ⟨hJ₁, hJ₂⟩
