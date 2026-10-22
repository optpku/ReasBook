/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm

noncomputable section

universe u v

section Derivatives

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 5.4.6.2 lies in the chapter's cone-ordered higher-derivative / barrier-compatibility
domain for vector-valued maps.

Sampled owner declarations:
* mathlib `iteratedFDeriv`, the canonical multilinear owner for repeated Fréchet derivatives;
* `secondDirectionalDerivative` and `thirdDirectionalDerivative` from `Definition_5_0_10`, the
  chapter's scalar directional-derivative owners built from the same `iteratedFDeriv` data;
* `hessianLocalNorm` / notation `‖h‖[F; x]` from `Definition_5_1_1`, the chapter owner for the
  barrier-side Hessian factor;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the canonical owner for the barrier
  hypothesis.

Source/core/bridge triage:
* source-facing: `IsBetaCompatibleWith Q₁ K F β ξ`;
* core/canonical: `iteratedFDeriv` and `hessianLocalNorm`;
* bridge/view: the short vector-valued repeated-direction abbreviations below.

Primitive data:
* the domain `Q₁`, cone `K`, barrier `F`, parameter `β`, and map `ξ`;
* convexity and interior nonemptiness of `Q₁`;
* the lower bound `1 ≤ β`;
* existence of a self-concordant barrier structure on `interior Q₁`;
* `C³` regularity of `ξ` on `interior Q₁`;
* the cone-order compatibility inequality.

Derived API:
* `vectorSecondDirectionalDerivative` and `vectorThirdDirectionalDerivative`, which only package
  repeated evaluation of `iteratedFDeriv`;
* the theorem-level owner consequence exposing the defining compatibility inequality from an
  ambient instance.

The owner abstraction stays `IsBetaCompatibleWith`; only the repeated-direction bridge names are
kept as a small shared vocabulary for the subsection, so downstream files can reuse them instead
of re-declaring parallel local copies. -/

/-- The repeated second Fréchet derivative `D²ξ(x)[h, h]` of a vector-valued map `ξ`. -/
abbrev vectorSecondDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 2 ξ x (fun _ ↦ h)

/-- The repeated third Fréchet derivative `D³ξ(x)[h, h, h]` of a vector-valued map `ξ`. -/
abbrev vectorThirdDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 3 ξ x (fun _ ↦ h)

end Derivatives

section Compatibility

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/-- Definition 5.4.6.2: a map `ξ : E₁ → E₂` is `β`-compatible with the barrier `F` relative to
the cone `K` when `Q₁` is convex with nonempty interior, `β ≥ 1`, `F` is a self-concordant
barrier on `interior Q₁`, `ξ` is three-times continuously differentiable on `interior Q₁`, and
for every `x ∈ interior Q₁` and every direction `h` the cone-order inequality
`D^3 ξ(x)[h,h,h] \preceq_K -3 β D^2 ξ(x)[h,h] ⟨∇²F(x) h, h⟩^{1/2}` holds, encoded as membership
of the difference in `K`. -/
class IsBetaCompatibleWith
    (Q₁ : Set E₁) (K : ConvexCone ℝ E₂) (F : E₁ → ℝ) (β : NNReal) (ξ : E₁ → E₂) : Prop where
  /-- The domain set `Q₁` is convex. -/
  convex_domain : Convex ℝ Q₁
  /-- The domain set `Q₁` has nonempty interior. -/
  interior_nonempty : (interior Q₁).Nonempty
  /-- The compatibility parameter satisfies `β ≥ 1`. -/
  one_le_parameter : 1 ≤ β
  /-- The scalar function `F` is a self-concordant barrier on `interior Q₁` for some barrier
  parameter. -/
  selfConcordantBarrier :
    ∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₁) ν F
  /-- The map `ξ` is three-times continuously differentiable on `interior Q₁`. -/
  contDiffOn : ContDiffOn ℝ 3 ξ (interior Q₁)
  /-- The third derivative of `ξ` is dominated by the negated second derivative scaled by the
  local Hessian norm of the barrier, in the cone order induced by `K`. -/
  compatibility_bound {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
      (3 * (β : ℝ) * ‖h‖[F; x]) •
          (-vectorSecondDirectionalDerivative ξ x h) -
        vectorThirdDirectionalDerivative ξ x h ∈ K

namespace IsBetaCompatibleWith

/-- A `β`-compatibility instance canonically supplies the defining cone-order derivative bound on
`interior Q₁`. -/
theorem compatibility_bound_of_mem
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal} {ξ : E₁ → E₂}
    [hβ : IsBetaCompatibleWith Q₁ K F β ξ] {x : E₁} (hx : x ∈ interior Q₁) (h : E₁) :
    (3 * (β : ℝ) * ‖h‖[F; x]) •
        (-vectorSecondDirectionalDerivative ξ x h) -
      vectorThirdDirectionalDerivative ξ x h ∈ K :=
  hβ.compatibility_bound hx h

end IsBetaCompatibleWith

end Compatibility
