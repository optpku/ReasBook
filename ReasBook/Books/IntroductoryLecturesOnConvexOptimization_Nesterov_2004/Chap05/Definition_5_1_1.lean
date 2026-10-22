/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.1.1 lies in the chapter's self-concordance / Hessian-local-norm domain.

Sampled owner declarations:
* `hessian` from `Chap01/Definition_1_4_16`, the intrinsic second-order owner used throughout the
  chapter;
* `thirdDirectionalDerivative` from `Definition_5_0_10`, the canonical cubic-derivative owner;
* `ConvexOn` from mathlib, the canonical owner for convexity on a fixed domain;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the downstream barrier owner that
  extends the standard-self-concordant case defined here.

Source/core/bridge triage:
* source-facing: `IsSelfConcordantOnWith dom Mf f`, the textbook bundled notion carrying the
  constant `M_f`;
* core/canonical: the Hessian owner `hessian f x`, the local norm owner `‖u‖[f; x]`, and the
  convexity owner `ConvexOn ℝ dom f`;
* bridge/view: the derived qualitative abbreviation `IsSelfConcordantOn dom f` and the standard
  specialization `IsStandardSelfConcordantOn dom f`.

Primitive data:
* the domain `dom`;
* the self-concordance constant `Mf`;
* the function `f`;
* openness of `dom`, `C³` regularity of `f` on `dom`, convexity on `dom`, and the cubic
  third-derivative bound.

Derived API:
* the local norm notation `‖u‖[f; x]`;
* domain convexity and Hessian positivity/semidefiniteness on `dom`;
* the qualitative and standard-self-concordant specializations.

This file keeps the quantitative owner as the public core. The qualitative and standard forms stay
as thin source-facing views, while Hessian positivity is exposed through inferable theorem-level
API rather than through an extra `Fact` wrapper around the defining class field. -/

/-- The Hessian local norm attached to `f` at `x`, evaluated on the direction `u`. -/
def hessianLocalNorm (f : E → ℝ) (x u : E) : ℝ :=
  Real.sqrt (inner ℝ u (hessian f x u))

namespace HessianLocalNorm

/-- Source-facing notation for the Hessian local norm of `u` at `x` for `f`. -/
scoped notation:max "‖" u "‖[" f "; " x "]" => hessianLocalNorm f x u

end HessianLocalNorm

open scoped HessianLocalNorm

-- Proof sketch: unfold `hessianLocalNorm`.
/-- Expanding `hessianLocalNorm f x u` gives the square root of the Hessian quadratic form. -/
theorem hessianLocalNorm_def (f : E → ℝ) (x u : E) :
    ‖u‖[f; x] = Real.sqrt (inner ℝ u (hessian f x u)) :=
  rfl

/-- The Hessian local norm is always nonnegative. -/
theorem hessianLocalNorm_nonneg (f : E → ℝ) (x u : E) :
    0 ≤ ‖u‖[f; x] := by
  rw [hessianLocalNorm_def]
  exact Real.sqrt_nonneg _

/-- The Hessian local norm is even in the direction argument. -/
@[simp] theorem hessianLocalNorm_neg (f : E → ℝ) (x u : E) :
    ‖-u‖[f; x] = ‖u‖[f; x] := by
  rw [hessianLocalNorm_def, hessianLocalNorm_def]
  congr 1
  simp

/-- Definition 5.1.1: `f` is self-concordant with constant `M_f` on the open convex domain `dom`
when `f` is a convex `C³` function on `dom` and the third directional derivative is bounded by
`2 M_f` times the cube of the local Hessian norm; the case `M_f = 1` is the standard
self-concordant condition. -/
class IsSelfConcordantOnWith (dom : Set E) (Mf : NNReal) (f : E → ℝ) : Prop where
  /-- The domain of definition is open. -/
  isOpen_domain : IsOpen dom
  /-- The objective is three-times continuously differentiable on `dom`. -/
  contDiffOn : ContDiffOn ℝ 3 f dom
  /-- The objective is convex on the domain. -/
  convexOn : ConvexOn ℝ dom f
  /-- The third directional derivative is controlled by the cube of the local Hessian norm. -/
  third_deriv_bound {x : E} (hx : x ∈ dom) (u : E) :
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)

namespace IsSelfConcordantOnWith

variable {dom : Set E} {f : E → ℝ}

/-- Increasing the self-concordance constant preserves self-concordance on the same domain. -/
theorem of_le
    {Mf Mg : NNReal} (h : IsSelfConcordantOnWith dom Mf f) (hMfMg : Mf ≤ Mg) :
    IsSelfConcordantOnWith dom Mg f where
  isOpen_domain := h.isOpen_domain
  contDiffOn := h.contDiffOn
  convexOn := h.convexOn
  third_deriv_bound {x} hx u := by
    calc
      |thirdDirectionalDerivative f x u| ≤
          2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
        h.third_deriv_bound hx u
      _ ≤ 2 * (Mg : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) := by
        have hMfMg' : (Mf : ℝ) ≤ (Mg : ℝ) := by
          exact_mod_cast hMfMg
        have hnorm : 0 ≤ ‖u‖[f; x] := hessianLocalNorm_nonneg f x u
        have hpow : 0 ≤ ‖u‖[f; x] ^ (3 : ℕ) := by
          exact pow_nonneg hnorm _
        nlinarith

/-- A self-concordant function has convex domain. -/
theorem convex_domain
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) :
    Convex ℝ dom :=
  h.convexOn.1

/-- The Hessian of a self-concordant function is positive on its domain. -/
theorem hessian_isPositive
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive := by
  have hC2 : ContDiffOn ℝ 2 f dom := h.contDiffOn.of_le (by norm_num)
  exact ((convexOn_iff_hessian_isPositive h.isOpen_domain h.convex_domain hC2).1 h.convexOn) x hx

/-- A self-concordant-on-with instance canonically supplies Hessian positivity at each point of
its domain. -/
theorem hessian_isPositive_of_mem
    (Mf : NNReal) [h : IsSelfConcordantOnWith dom Mf f] {x : E} (hx : x ∈ dom) :
    (hessian f x).IsPositive :=
  h.hessian_isPositive hx

/-- A self-concordant-on-with instance canonically supplies the defining cubic derivative bound on
its domain. -/
theorem third_deriv_bound_of_mem
    (Mf : NNReal) [h : IsSelfConcordantOnWith dom Mf f] {x : E} (hx : x ∈ dom) (u : E) :
    |thirdDirectionalDerivative f x u| ≤
      2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ) :=
  h.third_deriv_bound hx u

/-- The Hessian quadratic form of a self-concordant function is nonnegative on its domain. -/
theorem hessian_posSemidef
    {Mf : NNReal} (h : IsSelfConcordantOnWith dom Mf f) {x : E} (hx : x ∈ dom) (u : E) :
    0 ≤ inner ℝ u (hessian f x u) := by
  have hC2 : ContDiffOn ℝ 2 f dom := h.contDiffOn.of_le (by norm_num)
  simpa [real_inner_comm] using
    ((convexOn_iff_hessian_quadratic_form_nonneg h.isOpen_domain h.convex_domain hC2).1
      h.convexOn) x hx u

end IsSelfConcordantOnWith

/-- `f` is self-concordant on `dom` when it is self-concordant with some nonnegative constant. -/
abbrev IsSelfConcordantOn (dom : Set E) (f : E → ℝ) : Prop :=
  ∃ Mf : NNReal, IsSelfConcordantOnWith dom Mf f

/-- `f` is standard self-concordant on `dom` when the self-concordance constant is `1`. -/
abbrev IsStandardSelfConcordantOn (dom : Set E) (f : E → ℝ) : Prop :=
  IsSelfConcordantOnWith dom 1 f

end
