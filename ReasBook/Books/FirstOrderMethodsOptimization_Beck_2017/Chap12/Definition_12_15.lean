/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/- This item is `source-facing`: it packages the standing assumptions for the finite-sum model
`x ↦ f x + ∑ i, g i x` from the previous item. Domain sampling in the local convex-analysis API
shows that the correct owner abstractions are already present:
- `IsProperExtendedRealFunction` for properness,
- `PosReal` from Chapter 6 for the primitive positive strong-convexity modulus,
- `LowerSemicontinuous` for closedness,
- `StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)` for strong convexity,
- `is_convex_function` for convexity, and
- `intrinsicInterior ℝ` for the relative-interior qualification.

The new public API should therefore be the assumption package itself. Derived API should stay
small: the qualification reformulation, not a surrogate conjunction or auxiliary wrapper around
different owners. -/

/-- Definition 12.15: Assumption 12.14 for the dual block proximal-gradient model says that
`f : E → (-∞, ∞]` is proper, closed, and `σ`-strongly convex for a positive parameter
`σ : PosReal`; each `gᵢ : E → (-∞, ∞]` is proper, closed, and convex; and the qualification
`ri (dom f) ∩ ⋂ i, ri (dom gᵢ) ≠ ∅` holds. -/
class IsDualBlockProximalGradientProblem
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) (σ : PosReal) : Prop
    extends IsProperExtendedRealFunction f where
  f_closed : LowerSemicontinuous f
  f_strongly_convex :
    StrongConvexOn (effective_domain f) (σ : ℝ) (fun x ↦ (f x).toReal)
  g_proper (i : Fin p) : IsProperExtendedRealFunction (g i)
  g_closed (i : Fin p) : LowerSemicontinuous (g i)
  g_convex (i : Fin p) : is_convex_function (g i)
  qualification :
    (intrinsicInterior ℝ (effective_domain f) ∩
      ⋂ i : Fin p, intrinsicInterior ℝ (effective_domain (g i))).Nonempty

/-- The block relative-interior qualification is equivalent to the source wording that there is a
point lying in `ri (dom f)` and in `ri (dom gᵢ)` for every block `i`. -/
theorem qualification_nonempty_iff_exists_mem_intrinsicInterior
    {p : ℕ} (f : E → EReal) (g : Fin p → E → EReal) :
    (intrinsicInterior ℝ (effective_domain f) ∩
      ⋂ i : Fin p, intrinsicInterior ℝ (effective_domain (g i))).Nonempty ↔
      ∃ xHat,
        xHat ∈ intrinsicInterior ℝ (effective_domain f) ∧
        ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i)) := by
  constructor
  · rintro ⟨xHat, hxHat⟩
    exact ⟨xHat, hxHat.1, by simpa [Set.mem_iInter] using hxHat.2⟩
  · rintro ⟨xHat, hxHat, hxHatBlocks⟩
    refine ⟨xHat, ?_⟩
    exact ⟨hxHat, by simpa [Set.mem_iInter] using hxHatBlocks⟩

namespace IsDualBlockProximalGradientProblem

/-- Assumption 12.14 canonically provides properness of the primal term `f`. -/
instance instIsProperExtendedRealFunctionOfIsDualBlockProximalGradientProblem
    {p : ℕ} {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
    (h : IsDualBlockProximalGradientProblem f g σ) :
    IsProperExtendedRealFunction f :=
  h.toIsProperExtendedRealFunction

/-- Assumption 12.14 provides a point lying in `ri (dom f)` and in every block relative interior
`ri (dom gᵢ)`. -/
theorem exists_mem_intrinsicInterior
    {p : ℕ} {f : E → EReal} {g : Fin p → E → EReal} {σ : PosReal}
    (h : IsDualBlockProximalGradientProblem f g σ) :
    ∃ xHat,
      xHat ∈ intrinsicInterior ℝ (effective_domain f) ∧
      ∀ i : Fin p, xHat ∈ intrinsicInterior ℝ (effective_domain (g i)) :=
  (qualification_nonempty_iff_exists_mem_intrinsicInterior f g).1 h.qualification

end IsDualBlockProximalGradientProblem

end
