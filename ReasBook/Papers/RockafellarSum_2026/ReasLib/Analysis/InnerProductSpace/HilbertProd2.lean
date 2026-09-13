/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Two-coordinate Hilbert products

This module defines the `WithLp 2` product of a Hilbert space with the real
line and its coordinate API.
-/

@[expose] public section

open scoped InnerProductSpace

universe u

/-- The `ℓ²` product of a type `H` with the real line. -/
abbrev HilbertProd2 (H : Type u) : Type u := WithLp 2 (H × ℝ)

namespace HilbertProd2

/-- Construct a point of `HilbertProd2 H` from its two coordinates. -/
def mk {H : Type u} (v : H) (r : ℝ) : HilbertProd2 H :=
  WithLp.toLp 2 (v, r)

/-- The `H`-coordinate of a point of `HilbertProd2 H`. -/
def fst {H : Type u} (x : HilbertProd2 H) : H :=
  (WithLp.ofLp x).1

/-- The real coordinate of a point of `HilbertProd2 H`. -/
def snd {H : Type u} (x : HilbertProd2 H) : ℝ :=
  (WithLp.ofLp x).2

/-- The first projection recovers the first coordinate supplied to `mk`. -/
@[simp]
theorem fst_mk {H : Type u} (v : H) (r : ℝ) : fst (mk v r) = v := by
  -- Unwrapping the `WithLp` constructor exposes the first component of the pair.
  rfl

/-- The second projection recovers the real coordinate supplied to `mk`. -/
@[simp]
theorem snd_mk {H : Type u} (v : H) (r : ℝ) : snd (mk v r) = r := by
  -- Unwrapping the `WithLp` constructor exposes the second component of the pair.
  rfl

/-- A point of `HilbertProd2 H` is reconstructed from its two projections. -/
@[simp]
theorem mk_fst_snd {H : Type u} (x : HilbertProd2 H) : mk (fst x) (snd x) = x := by
  -- The coordinate pair is `ofLp x`, so `toLp_ofLp` reconstructs `x`.
  simp only [mk, fst, snd]

/-- Two points of `HilbertProd2 H` are equal when both coordinates agree. -/
@[ext]
theorem ext {H : Type u} {x y : HilbertProd2 H}
    (hfst : fst x = fst y) (hsnd : snd x = snd y) : x = y := by
  -- Equality of both coordinates gives equality after applying the injective `ofLp` map.
  apply WithLp.ofLp_injective 2
  exact Prod.ext hfst hsnd

/-- The squared norm in `HilbertProd2 H` is the sum of the squared coordinate norms. -/
theorem norm_mk_sq {H : Type u} [NormedAddCommGroup H] (v : H) (r : ℝ) :
    ‖mk v r‖ ^ 2 = ‖v‖ ^ 2 + r ^ 2 := by
  -- Specialize the canonical `L²` product norm formula, then remove the real absolute value.
  simpa only [mk, WithLp.toLp_fst, WithLp.toLp_snd, Real.norm_eq_abs, sq_abs] using
    WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (v, r))

/-- The real inner product in `HilbertProd2 H` is the sum of the coordinate inner products. -/
theorem inner_mk {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v w : H) (r s : ℝ) :
    ⟪mk v r, mk w s⟫_ℝ = ⟪v, w⟫_ℝ + r * s := by
  -- Expand the canonical product inner product and evaluate both `toLp` coordinate pairs.
  simp only [mk, WithLp.prod_inner_apply, Real.inner_apply]

end HilbertProd2
