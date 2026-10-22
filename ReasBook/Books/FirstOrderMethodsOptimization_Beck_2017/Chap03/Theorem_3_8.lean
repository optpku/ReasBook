/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (f : E → EReal) (x d : E)

/- This file uses the source-facing owner `has_directional_derivative_at` from Definition 3.8.
The canonical totalized owner `directional_derivative` already comes with the bridge
`directional_derivative_eq_of_has_directional_derivative_at`, so the public entry remains an
existence statement rather than a parallel owner-level wrapper theorem. Within Chapter 3, the
reusable owner-level companion is the finite-domain interior formulation; the textbook
proper/effective-domain statement is a thin bridge obtained from
`finite_domain_eq_effective_domain`. -/
recall is_convex_function
recall has_directional_derivative_at
recall finite_domain
recall effective_domain

-- Proof sketch: restrict `f` to the affine line `t ↦ x + t • d`, obtaining a convex
-- extended-real-valued function on `ℝ`. Since `x` lies in the interior of `finite_domain f`,
-- this one-dimensional restriction is finite on some interval around `0`, so its secant slopes on
-- `(0, r]` are monotone and bounded. Their right limit at `0` therefore exists and is finite,
-- giving the desired directional derivative.
/-- Helper theorem: the stronger finite-domain interior hypothesis also yields a finite directional
derivative witness. -/
theorem exists_real_has_directional_derivative_at_of_convex_interior_point
    (hconvex : is_convex_function f) (hx : x ∈ interior (finite_domain f)) :
    ∃ ℓ : ℝ, has_directional_derivative_at f x d ℓ := by
  have hNeBot : ∀ y : E, f y ≠ ⊥ :=
    valueNeBotOfMemInteriorFiniteDomain f x hconvex hx
  have hxEff : x ∈ interior (effective_domain f) := by
    -- The no-`⊥` hypothesis identifies the finite and effective domains around `x`.
    simpa [finite_domain_eq_effective_domain hNeBot] using hx
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x (x + d)
  let g : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  let S : Set ℝ := {t : ℝ | line t ∈ effective_domain f}
  have hconvReal :
      ConvexOn ℝ (effective_domain f) (fun y ↦ (f y).toReal) :=
    convexOn_toReal_of_is_convex_function hconvex (fun y _ ↦ hNeBot y)
  have hconvLine : ConvexOn ℝ S g := by
    -- Restrict the ambient convex function to the affine line through `x` in direction `d`.
    simpa [g, S] using hconvReal.comp_affineMap line
  have hzeroInterior : (0 : ℝ) ∈ interior S := by
    -- Pull the interior membership of `x` back to the parameter value `t = 0`.
    have hzeroPre : (0 : ℝ) ∈ line ⁻¹' interior (effective_domain f) := by
      simpa [line, Set.preimage, AffineMap.lineMap_apply_zero] using hxEff
    have : (0 : ℝ) ∈ interior (line ⁻¹' effective_domain f) :=
      (preimage_interior_subset_interior_preimage AffineMap.lineMap_continuous) hzeroPre
    simpa [S, Set.preimage] using this
  have hderiv :
      HasDerivWithinAt g (derivWithin g (Set.Ioi 0) 0) (Set.Ioi 0) 0 :=
    hconvLine.hasDerivWithinAt_rightDeriv_of_mem_interior hzeroInterior
  refine ⟨derivWithin g (Set.Ioi 0) 0, ?_⟩
  -- Rewrite the one-variable derivative back into the chapter directional derivative predicate.
  have hderivLine :
      HasDerivWithinAt (fun t : ℝ ↦ (f (x + t • d)).toReal)
        (derivWithin g (Set.Ioi 0) 0) (Set.Ioi 0) 0 := by
    simpa [g, line, AffineMap.lineMap_apply_module', add_comm] using hderiv
  exact hasDirectionalDerivativeAtOfHasDerivWithinAtIoi f x d hx hderivLine

/-- Theorem 3.8: if `f` is a proper convex extended-real-valued function and `x` lies in the
interior of `effective_domain f`, then for every direction `d` there is a finite real number that
is the directional derivative of `f` at `x` along `d`. -/
theorem exists_real_has_directional_derivative_at_of_proper_convex_interior_point
    [IsProperExtendedRealFunction f] (hconvex : is_convex_function f)
    (hx : x ∈ interior (effective_domain f)) :
    ∃ ℓ : ℝ, has_directional_derivative_at f x d ℓ := by
  let h_ne_bot : ∀ y, f y ≠ ⊥ := IsProperExtendedRealFunction.ne_bot
  have hxFinite : x ∈ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain h_ne_bot] using hx
  exact exists_real_has_directional_derivative_at_of_convex_interior_point f x d hconvex hxFinite

end
