/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

-- Route repair: this file only needs the source-facing compatibility owner and its barrier-side
-- support classes. We restate that small owner layer here so the theorem does not depend on the
-- blocked Chapter 5 derivative import chain through `Definition_5_0_10`.

/-- The repeated second Fréchet derivative `D²f(x)[u, u]` of a scalar-valued map `f`. -/
abbrev secondDirectionalDerivative (f : E₁ → ℝ) (x u : E₁) : ℝ :=
  iteratedFDeriv ℝ 2 f x (fun _ ↦ u)

/-- The repeated third Fréchet derivative `D³f(x)[u, u, u]` of a scalar-valued map `f`. -/
abbrev thirdDirectionalDerivative (f : E₁ → ℝ) (x u : E₁) : ℝ :=
  iteratedFDeriv ℝ 3 f x (fun _ ↦ u)

/-- The Hessian local norm attached to `f` at `x`, evaluated on the direction `u`. -/
def hessianLocalNorm (f : E₁ → ℝ) (x u : E₁) : ℝ :=
  Real.sqrt (inner ℝ u (hessian f x u))

namespace HessianLocalNorm

/-- Source-facing notation for the Hessian local norm of `u` at `x` for `f`. -/
scoped notation:max "‖" u "‖[" f "; " x "]" => hessianLocalNorm f x u

end HessianLocalNorm

open scoped HessianLocalNorm

/-- Definition 5.1.1: `f` is self-concordant with constant `M_f` on the open convex domain `dom`
when `f` is a convex `C³` function on `dom` and the third directional derivative is bounded by
`2 M_f` times the cube of the local Hessian norm. -/
class IsSelfConcordantOnWith (dom : Set E₁) (Mf : NNReal) (f : E₁ → ℝ) : Prop where
  /-- The domain of definition is open. -/
  isOpen_domain : IsOpen dom
  /-- The objective is three-times continuously differentiable on `dom`. -/
  contDiffOn : ContDiffOn ℝ 3 f dom
  /-- The objective is convex on the domain. -/
  convexOn : ConvexOn ℝ dom f
  /-- The third directional derivative is controlled by the cube of the local Hessian norm. -/
  third_deriv_bound {x : E₁} (hx : x ∈ dom) (u : E₁) :
      |thirdDirectionalDerivative f x u| ≤
        2 * (Mf : ℝ) * ‖u‖[f; x] ^ (3 : ℕ)

/-- `f` is self-concordant on `dom` when it is self-concordant with some nonnegative constant. -/
abbrev IsSelfConcordantOn (dom : Set E₁) (f : E₁ → ℝ) : Prop :=
  ∃ Mf : NNReal, IsSelfConcordantOnWith dom Mf f

/-- `f` is standard self-concordant on `dom` when the self-concordance constant is `1`. -/
abbrev IsStandardSelfConcordantOn (dom : Set E₁) (f : E₁ → ℝ) : Prop :=
  IsSelfConcordantOnWith dom 1 f

/-- Definition 5.3.2: a standard self-concordant function `F` is a `ν`-self-concordant barrier
for `dom` when, for every `x ∈ dom`, every direction `u` satisfies the barrier inequality
`2 ⟪∇F(x), u⟫ - ⟪u, ∇²F(x)u⟫ ≤ ν`. -/
class IsSelfConcordantBarrierOnWith (dom : Set E₁) (ν : NNReal) (F : E₁ → ℝ) : Prop where
  /-- A self-concordant barrier is standard self-concordant on its open convex domain. -/
  toIsStandardSelfConcordantOn : IsStandardSelfConcordantOn dom F
  /-- The barrier parameter bounds the gradient term by the Hessian quadratic form at each point
  of the domain. -/
  barrier_parameter_bound {x : E₁} (hx : x ∈ dom) (u : E₁) :
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)

attribute [instance] IsSelfConcordantBarrierOnWith.toIsStandardSelfConcordantOn

/-- The repeated second Fréchet derivative `D²ξ(x)[h, h]` of a vector-valued map `ξ`. -/
abbrev vectorSecondDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 2 ξ x (fun _ ↦ h)

/-- The repeated third Fréchet derivative `D³ξ(x)[h, h, h]` of a vector-valued map `ξ`. -/
abbrev vectorThirdDirectionalDerivative (ξ : E₁ → E₂) (x h : E₁) : E₂ :=
  iteratedFDeriv ℝ 3 ξ x (fun _ ↦ h)

/-- Definition 5.4.6.2: a map `ξ : E₁ → E₂` is `β`-compatible with the barrier `F` relative to
the cone `K` when `Q₁` is convex with nonempty interior, `β ≥ 1`, `F` is a self-concordant
barrier on `interior Q₁`, `ξ` is three-times continuously differentiable on `interior Q₁`, and
for every `x ∈ interior Q₁` and every direction `h` the cone-order inequality is encoded as
membership of the difference in `K`. -/
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

/- Theorem 5.4.6.2 stays on the compatibility owner `IsBetaCompatibleWith`.

Sampled declarations in the same domain:
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the source-facing compatibility owner;
* mathlib `ConvexCone.smul_mem` and `ConvexCone.add_mem`, the ambient cone-owner closure API;
* `IsPositivelyHomogeneousOn.smul_mem` from `Chap03/Definition_3_1_7`, the chapter's bundled
  nonnegative-scalar owner surface;
* `IsThreeTimesContDiffConcaveOnWith` from `Definition_5_4_6_1`, the neighboring subsection owner
  on the same cone-ordered map space.

Source/core/bridge triage:
* source-facing: Theorem 5.4.6.2 on positive linear combinations of `β`-compatible maps;
* core/canonical: closure of `IsBetaCompatibleWith Q₁ K F β` under nonnegative scaling and
  addition, matching the cone-owner surface already used elsewhere in the chapter;
* bridge/view: the source-faithful positive-combination theorem built directly from that
  nonnegative closure API.

Primitive data:
* `Q₁`, `K`, `F`, `β`, and the map `ξ`.

Derived API:
* the owner-level closure theorems `IsBetaCompatibleWith.smul` and `IsBetaCompatibleWith.add`;
* the source-facing specialization `IsBetaCompatibleWith.pos_combination`.

The previous carrier-level cone wrapper duplicated the owner predicate with no extra mathematics, so
this refinement keeps only the closure statements on `IsBetaCompatibleWith` itself and aligns the
scalar-closure surface with the chapter's canonical nonnegative-scalar cone API. -/

namespace IsBetaCompatibleWith

variable {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {β : NNReal}

/-- Helper for Theorem 5.4.6.2: every `β`-compatible map has zero compatibility expression in
the cone, hence `(0 : E₂) ∈ K`. -/
private lemma zero_mem
    {ξ : E₁ → E₂} (hξ : IsBetaCompatibleWith Q₁ K F β ξ) :
    (0 : E₂) ∈ K := by
  -- Evaluate the compatibility bound at the zero direction to force the zero vector into `K`.
  rcases hξ.interior_nonempty with ⟨x, hx⟩
  have hD2 : vectorSecondDirectionalDerivative ξ x (0 : E₁) = 0 := by
    simpa [vectorSecondDirectionalDerivative] using
      (iteratedFDeriv ℝ 2 ξ x).map_coord_zero (0 : Fin 2) rfl
  have hD3 : vectorThirdDirectionalDerivative ξ x (0 : E₁) = 0 := by
    simpa [vectorThirdDirectionalDerivative] using
      (iteratedFDeriv ℝ 3 ξ x).map_coord_zero (0 : Fin 3) rfl
  simpa [hD2, hD3] using
    hξ.compatibility_bound hx (0 : E₁)

-- Proof sketch: scaling a `β`-compatible map by a bundled nonnegative scalar preserves convexity
-- and differentiability data, and multiplies both derivative terms in the compatibility
-- inequality by the same nonnegative factor. For `α > 0` this is the cone-owner closure
-- `K.smul_mem`; for `α = 0` the rescaled map is the zero map, whose compatibility expression is
-- the zero vector.
/-- `NNReal`-scalar multiples of a `β`-compatible map are again `β`-compatible with the same
barrier. -/
theorem smul
    {ξ : E₁ → E₂} (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (α : NNReal) :
    IsBetaCompatibleWith Q₁ K F β (α • ξ) := by
  refine
    { convex_domain := hξ.convex_domain
      interior_nonempty := hξ.interior_nonempty
      one_le_parameter := hξ.one_le_parameter
      selfConcordantBarrier := hξ.selfConcordantBarrier
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · -- Constant scaling preserves `C³` regularity on the interior.
    simpa using hξ.contDiffOn.const_smul (α : ℝ)
  · -- Split into the positive and zero scalar cases, then close by cone stability.
    intro x hx h
    have hξx : ContDiffAt ℝ 3 ξ x :=
      hξ.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξx₂ : ContDiffAt ℝ 2 ξ x := hξx.of_le (by norm_num)
    have hscaled :
        (3 * (β : ℝ) * hessianLocalNorm F x h) •
            (-vectorSecondDirectionalDerivative (α • ξ) x h) -
          vectorThirdDirectionalDerivative (α • ξ) x h =
          (α : ℝ) •
            ((3 * (β : ℝ) * hessianLocalNorm F x h) •
                (-vectorSecondDirectionalDerivative ξ x h) -
              vectorThirdDirectionalDerivative ξ x h) := by
      rw [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
        iteratedFDeriv_const_smul_apply hξx₂, iteratedFDeriv_const_smul_apply hξx]
      simp [NNReal.smul_def, sub_eq_add_neg, smul_add, smul_neg, smul_smul, mul_comm]
    rcases lt_or_eq_of_le α.2 with hα | hα
    · rw [hscaled]
      exact K.smul_mem hα (hξ.compatibility_bound hx h)
    · rw [hscaled]
      have hα' : (α : ℝ) = 0 := hα.symm
      simpa [hα'] using (hξ.zero_mem : (0 : E₂) ∈ K)

-- Proof sketch: the sum of two `β`-compatible maps preserves the shared convexity, interior,
-- parameter, and barrier data, while linearity of iterated derivatives turns the compatibility
-- expression for `ξ₁ + ξ₂` into the sum of the two corresponding expressions. Closure of `K`
-- under addition then gives the result.
/-- The sum of two `β`-compatible maps is again `β`-compatible with the same barrier. -/
theorem add
    {ξ₁ ξ₂ : E₁ → E₂}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂) :
    IsBetaCompatibleWith Q₁ K F β (ξ₁ + ξ₂) := by
  refine
    { convex_domain := hξ₁.convex_domain
      interior_nonempty := hξ₁.interior_nonempty
      one_le_parameter := hξ₁.one_le_parameter
      selfConcordantBarrier := hξ₁.selfConcordantBarrier
      contDiffOn := ?_
      compatibility_bound := ?_ }
  · -- Sum regularity is inherited from the two `C³` summands.
    simpa using hξ₁.contDiffOn.add hξ₂.contDiffOn
  · -- The compatibility expression distributes over addition, and `K` is additively closed.
    intro x hx h
    have hξ₁x : ContDiffAt ℝ 3 ξ₁ x :=
      hξ₁.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξ₂x : ContDiffAt ℝ 3 ξ₂ x :=
      hξ₂.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
    have hξ₁x₂ : ContDiffAt ℝ 2 ξ₁ x := hξ₁x.of_le (by norm_num)
    have hξ₂x₂ : ContDiffAt ℝ 2 ξ₂ x := hξ₂x.of_le (by norm_num)
    rw [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
      iteratedFDeriv_add_apply hξ₁x₂ hξ₂x₂, iteratedFDeriv_add_apply hξ₁x hξ₂x]
    simpa [vectorSecondDirectionalDerivative, vectorThirdDirectionalDerivative,
      sub_eq_add_neg, smul_add, add_comm, add_left_comm, add_assoc] using
      K.add_mem (hξ₁.compatibility_bound hx h) (hξ₂.compatibility_bound hx h)

-- Proof sketch: apply the owner-level closure lemmas `IsBetaCompatibleWith.smul` to the two
-- positive coefficients viewed as `NNReal`, then combine the two resulting hypotheses with
-- `IsBetaCompatibleWith.add`.
/-- Theorem 5.4.6.2: positive linear combinations of `β`-compatible functions are again
`β`-compatible with the same self-concordant barrier. -/
theorem pos_combination
    {ξ₁ ξ₂ : E₁ → E₂} {α₁ α₂ : ℝ}
    (hξ₁ : IsBetaCompatibleWith Q₁ K F β ξ₁)
    (hξ₂ : IsBetaCompatibleWith Q₁ K F β ξ₂)
    (hα₁ : 0 < α₁) (hα₂ : 0 < α₂) :
    IsBetaCompatibleWith Q₁ K F β (α₁ • ξ₁ + α₂ • ξ₂) :=
  by
    simpa using
      IsBetaCompatibleWith.add
        (IsBetaCompatibleWith.smul hξ₁ ⟨α₁, hα₁.le⟩)
        (IsBetaCompatibleWith.smul hξ₂ ⟨α₂, hα₂.le⟩)

end IsBetaCompatibleWith

end
