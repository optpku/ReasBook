/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/- Definition 12.1.1 is `source-facing`: it packages the standing assumptions for the Chapter 12
dual-based proximal-gradient model `min_x {f x + g (A x)}`. Domain sampling in the surrounding
project fixes the owner abstractions already in play:
- `PosReal` from Chapter 6 for the primitive positive strong-convexity modulus,
- `IsProperExtendedRealFunction` from Chapter 2 for extended-real properness,
- `StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)` from Chapter 5 for strong
  convexity once the positive modulus is viewed in `ℝ`,
- `is_convex_function` from Chapter 2 for convexity, and
- `intrinsicInterior ℝ` for the relative-interior qualification.

Primitive data are therefore exactly the assumptions on `f`, `g`, and the qualification.
Derived API should stay small: the existential reformulation of the qualification, not an
auxiliary conjunction package or projection wrappers around fields that are already primitive. -/

-- Proof sketch: unpack the nonempty intersection as a point `x̂` lying in
-- `intrinsicInterior ℝ (effective_domain f)` whose image under `A` lies in
-- `intrinsicInterior ℝ (effective_domain g)`, and take `ẑ = A x̂`. The reverse direction rewrites
-- the image condition `A x̂ = ẑ` as membership in the preimage.
/-- The relative-interior qualification for the linear map `A` is equivalent to the source wording
that there exist `x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
theorem qualification_nonempty_iff_exists_ri_map_eq
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) :
    (intrinsicInterior ℝ (effective_domain f) ∩
      A ⁻¹' intrinsicInterior ℝ (effective_domain g)).Nonempty ↔
      ∃ xHat ∈ intrinsicInterior ℝ (effective_domain f),
        ∃ zHat ∈ intrinsicInterior ℝ (effective_domain g), A xHat = zHat := by
  constructor
  · rintro ⟨xHat, hxHat, hzHat⟩
    exact ⟨xHat, hxHat, A xHat, hzHat, rfl⟩
  · rintro ⟨xHat, hxHat, zHat, hzHat, hAz⟩
    refine ⟨xHat, hxHat, ?_⟩
    change A xHat ∈ intrinsicInterior ℝ (effective_domain g)
    simpa [hAz] using hzHat

/-- Definition 12.1.1: Assumption 12.1 means that `f : E → (-∞, ∞]` is proper, closed, and
`σ`-strongly convex for a positive parameter `σ : PosReal`; `g : V → (-∞, ∞]` is proper, closed,
and convex; `A : E →ₗ[ℝ] V` is linear; and the relative interiors of `dom f` and `dom g` satisfy
the qualification `ri (dom f) ∩ A⁻¹' (ri (dom g)) ≠ ∅`, equivalently there exist
`x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
class IsDualBasedProximalGradientProblem
    (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V) (σ : PosReal) : Prop
    extends IsProperExtendedRealFunction f where
  f_closed : LowerSemicontinuous f
  f_strongly_convex :
    StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)
  g_proper : IsProperExtendedRealFunction g
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  qualification :
    (intrinsicInterior ℝ (effective_domain f) ∩
      A ⁻¹' intrinsicInterior ℝ (effective_domain g)).Nonempty

namespace IsDualBasedProximalGradientProblem

/-- Assumption 12.1 packages primal strong convexity together with the relative-interior
qualification used throughout the Chapter 12 duality arguments. -/
theorem strongConvexOn_and_qualification
    {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V} {σ : PosReal}
    (h : IsDualBasedProximalGradientProblem f g A σ) :
    StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal) ∧
      (intrinsicInterior ℝ (effective_domain f) ∩
        A ⁻¹' intrinsicInterior ℝ (effective_domain g)).Nonempty :=
  ⟨h.f_strongly_convex, h.qualification⟩

/-- Assumption 12.1 provides a point `x̂ ∈ ri(dom f)` whose image `A x̂` lies in
`ri(dom g)`. Equivalently, there exist `x̂ ∈ ri(dom f)` and `ẑ ∈ ri(dom g)` with `A x̂ = ẑ`. -/
theorem exists_mem_intrinsicInterior_map_eq
    {f : E → EReal} {g : V → EReal} {A : E →ₗ[ℝ] V} {σ : PosReal}
    (h : IsDualBasedProximalGradientProblem f g A σ) :
    ∃ xHat ∈ intrinsicInterior ℝ (effective_domain f),
      ∃ zHat ∈ intrinsicInterior ℝ (effective_domain g), A xHat = zHat :=
  (qualification_nonempty_iff_exists_ri_map_eq f g A).1 h.qualification

end IsDualBasedProximalGradientProblem

end
