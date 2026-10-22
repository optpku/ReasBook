/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Gradient

noncomputable section

universe u v

/- Definition 5.4.6.4 lies in the Chapter 5 self-concordant-barrier / recession-direction /
product-gradient domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` from
  `Corollary_5_3_2`, the canonical barrier-owner recession-direction consequence;
* mathlib `WithLp 2 (E₂ × E₃)` together with `WithLp.toLp` / `WithLp.ofLp`, the canonical `L²`
  product owner and its bridge back to raw pairs;
* mathlib `Convex.interior` and `Convex.add_smul_mem_interior`, the canonical convex-interior API
  that transfers recession directions from a convex set to its interior;
* `sum_partialGradient_pairings_eq_inner_gradient_pair` from `Theorem_5_4_6_4`, the chapter's
  canonical `L²` product-gradient decomposition owner theorem on an arbitrary direction `(u, v)`.

Source/core/bridge triage:
* source-facing: the cone-indexed nonpositivity statement for the `y`-gradient pairing;
* core/canonical: the barrier owner `IsSelfConcordantBarrierOnWith Q ν Φ`;
* bridge/view: mathlib's convex-interior recession-direction transfer and the slice-gradient versus
  product-gradient pairing identity.

Primitive data:
* the convex set `Q₂`;
* the source-facing barrier existence datum
  `∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) ν Φ`;
* the cone `K` and the recession-direction hypothesis for `(s, 0)`.

Derived API:
* the internal affine-pullback barrier on the canonical `L²` product owner, obtained from
  `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` along `WithLp.ofLp`;
* the imported owner-method consequence
  `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction`;
* the product-gradient bridge `sum_partialGradient_pairings_eq_inner_gradient_pair`.

The barrier recession inequality already belongs to the barrier owner in `Corollary_5_3_2`, and
the convex-to-interior recession transfer already belongs to mathlib's convex-interior API, so
this file should not keep parallel public duplicates of either fact. The source-facing theorem
below is kept only as the finite-dimensional product bridge from those owner declarations to the
`(s, 0)` recession-direction situation, matching the product-gradient API that already exists in
`Theorem_5_4_6_4`. -/

section Product

variable {E₂ : Type u} {E₃ : Type v}
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
variable [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Definition_5_4_6_41 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Definition_5_4_6_42 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Definition_5_4_6_43 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Definition_5_4_6_41 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Definition_5_4_6_44 : CompleteSpace (E₂ × E₃) := inferInstance

local notation "Z" => WithLp 2 (E₂ × E₃)
local notation "ofZ" => (WithLp.ofLp : Z → E₂ × E₃)

-- Proof sketch: apply
-- `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` to pull the source-facing barrier
-- `Φ` on `interior Q₂` back along the canonical map `WithLp.ofLp`, then apply
-- `IsSelfConcordantBarrierOnWith.inner_gradient_nonpos_of_recession_direction` to that internal
-- `L²` product-owner barrier and the direction `WithLp.toLp 2 (s, 0)`. Use
-- mathlib's
-- `Convex.interior` and `Convex.add_smul_mem_interior` to pass from recession directions of `Q₂`
-- to recession directions of `interior Q₂`, then rewrite the resulting product-space pairing with
-- `sum_partialGradient_pairings_eq_inner_gradient_pair` specialized to the direction `(s, 0)`.
/-- Definition 5.4.6.4: if every direction `(s, 0)` with `s ∈ K` is a recession direction of the
convex set `Q₂`, then at every interior point `(y, z)` the pairing of the `y`-gradient of a
barrier `Φ` with `s` is nonpositive. The existence of a self-concordant barrier parameter for `Φ`
on `interior Q₂` is the only barrier input needed here. The `L²` product owner `WithLp 2
(E₂ × E₃)` is used only
internally through the canonical affine pullback along `WithLp.ofLp`. -/
theorem barrier_yGradient_pairing_nonpos
    {Q₂ : Set (E₂ × E₃)} (hQ₂_convex : Convex ℝ Q₂) (K : ConvexCone ℝ E₂)
    {Φ : E₂ × E₃ → ℝ}
    (hΦ : ∃ ν : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) ν Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄, s ∈ (K : Set E₂) →
        ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ → p + τ • (s, (0 : E₃)) ∈ Q₂)
    {y : E₂} {z : E₃} (hyz : (y, z) ∈ interior Q₂) {s : E₂} (hs : s ∈ (K : Set E₂)) :
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s ≤ 0 := by
  rcases hΦ with ⟨ν, hΦ⟩
  let g : Z →ᴬ[ℝ] E₂ × E₃ :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ E₂ E₃).toContinuousLinearMap).toContinuousAffineMap
  let hΦZ : IsSelfConcordantBarrierOnWith (ofZ ⁻¹' interior Q₂) ν (Φ ∘ ofZ) :=
    by
      simpa [g, Function.comp] using hΦ.comp_continuousAffineMap g
  have hyzZ : WithLp.toLp 2 (y, z) ∈ ofZ ⁻¹' interior Q₂ := by
    simpa using hyz
  have hrecessionZ :
      ∀ ⦃w : Z⦄, w ∈ ofZ ⁻¹' interior Q₂ →
        ∀ τ : ℝ, 0 ≤ τ → w + τ • WithLp.toLp 2 (s, (0 : E₃)) ∈ ofZ ⁻¹' interior Q₂ := by
    intro w hw τ hτ
    let p : E₂ × E₃ := w.ofLp
    let d : E₂ × E₃ := (s, (0 : E₃))
    let x : E₂ × E₃ := p + (2 * τ) • d
    have hp : p ∈ interior Q₂ := by
      simpa [p] using hw
    have hx : x ∈ Q₂ := by
      simpa [p, d, x] using hK_recession hs (interior_subset hp) (2 * τ) (by positivity)
    have hy : x + (-(2 * τ) • d) ∈ interior Q₂ := by
      convert hp using 1
      simp [p, d, x, add_assoc]
    have hmid :=
      hQ₂_convex.add_smul_mem_interior hx hy (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
    have hsum : (2 * τ) • d + -τ • d = τ • d := by
      rw [← add_smul]
      have h : (2 * τ : ℝ) + -τ = τ := by ring
      rw [h]
    have hinterior : p + τ • d ∈ interior Q₂ := by
      convert hmid using 1
      rw [show x = p + (2 * τ) • d by rfl, smul_smul]
      have hcoeff : (1 / 2 : ℝ) * (-(2 * τ)) = -τ := by ring
      rw [hcoeff]
      simpa [add_assoc] using congrArg (fun v : E₂ × E₃ ↦ p + v) hsum.symm
    simpa [p, d] using hinterior
  have hpair :
      inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s =
        inner ℝ
          (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)))
          (WithLp.toLp 2 (s, (0 : E₃))) := by
    let hstdZ : IsStandardSelfConcordantOn (ofZ ⁻¹' interior Q₂) (Φ ∘ ofZ) :=
      hΦZ.toIsStandardSelfConcordantOn
    have hdiffZ : DifferentiableAt ℝ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)) := by
      simpa using
        (hstdZ.contDiffOn.contDiffAt (hstdZ.isOpen_domain.mem_nhds hyzZ)).differentiableAt
          (by norm_num)
    have hpair0 :
        inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s +
            inner ℝ (∇ (fun z' : E₃ ↦ Φ (y, z')) z) (0 : E₃) =
          inner ℝ
            (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z)))
            (WithLp.toLp 2 (s, (0 : E₃))) :=
      sum_partialGradient_pairings_eq_inner_gradient_pair hdiffZ
    simpa using hpair0
  calc
    inner ℝ (∇ (fun y' : E₂ ↦ Φ (y', z)) y) s =
        inner ℝ (∇ (Φ ∘ ofZ) (WithLp.toLp 2 (y, z))) (WithLp.toLp 2 (s, (0 : E₃))) :=
      hpair
    _ ≤ 0 :=
      hΦZ.inner_gradient_nonpos_of_recession_direction hrecessionZ hyzZ

end Product

end
