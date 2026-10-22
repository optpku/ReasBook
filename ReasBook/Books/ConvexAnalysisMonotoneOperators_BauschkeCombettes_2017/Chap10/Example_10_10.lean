/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_22

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

section Normed

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Example 10.10 uses the same radial primitive as Example 8.22, whose canonical global convexity
owner is `convexOn_univ_radialIntegral`; the present file records only the bounded-set
uniform-convex layer and the monotone-only obstruction. -/

-- Proof sketch: for the constant integrand `1`, the radial primitive is the norm. On the segment
-- from `0` to `u`, the midpoint Jensen gap at `0` and `u` vanishes, so any modulus positive away
-- from `0` contradicts the defining inequality for `UniformConvexOn`.
/-- Example 10.10 correction: monotonicity of `φ` alone does not force bounded-set uniform
convexity. For the constant choice `φ ≡ 1`, the radial primitive is not uniformly convex on any
nontrivial segment. -/
theorem radialIntegral_const_not_uniformlyConvexOn_segment {u : E} (hu : u ≠ 0) :
    ¬ ∃ ψ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧
        UniformConvexOn (segment ℝ (0 : E) u) ψ
          (fun x : E ↦ ∫ t in 0..‖x‖, (1 : ℝ)) := sorry

end Normed

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable {C : Set H}

-- Proof sketch: Example 8.22 gives the canonical strict-convexity owner
-- `strictConvexOn_univ_radialIntegral` for the radial primitive attached to a strictly increasing
-- `φ`; the bounded-set modulus is then extracted at the Chapter 10 uniform-convex layer.
/-- Example 10.10, corrected bounded-set form: if `φ : ℝ₊ → ℝ₊` is strictly increasing and `C` is
bounded convex, then the radial primitive is uniformly convex on `C`. -/
theorem uniformlyConvexOn_radialIntegral_of_strictMono
    (φ : NNReal → NNReal) (hφ_strict : StrictMono φ)
    (hC_bounded : Bornology.IsBounded C) (hC_convex : Convex ℝ C) :
    ∃ ψ : ℝ → ℝ,
      (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧
        UniformConvexOn C ψ
          (fun x : H ↦ ∫ t in 0..‖x‖, (φ (Real.toNNReal t) : ℝ)) := sorry

-- Proof sketch: specialize `uniformlyConvexOn_radialIntegral_of_strictMono` to the standard
-- integrand `φ(t) = p * t^(p - 1)`, whose radial primitive is `r ↦ r^p`.
/-- The `p`-power norm is uniformly convex on every bounded convex set; equivalently, the
indicator-augmented function `‖·‖^p + ι_C` has a modulus positive away from `0`. -/
theorem uniformlyConvexOn_norm_rpow_on_bounded_convex
    (hC_bounded : Bornology.IsBounded C) (hC_convex : Convex ℝ C) (p : ℝ) (hp : 1 < p) :
    ∃ ψ : ℝ → ℝ, (∀ ⦃r : ℝ⦄, r ≠ 0 → 0 < ψ r) ∧ UniformConvexOn C ψ (fun x : H ↦ ‖x‖ ^ p) :=
      sorry

end Hilbert
