/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Definition_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

noncomputable section

section RealVectorSpace

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- The directional derivative of an extended-real-valued function at `x` along `y`, encoded as
the infimum of the positive directional difference quotients. -/
noncomputable def directionalDerivative
    (x y : H) : EReal :=
  sInf (Set.range (directionalDifferenceQuotient f x y))

notation:arg f "′(" x "; " y ")" => directionalDerivative f x y

/-- The right derivative of an extended-real-valued function on `ℝ`, viewed as the
one-dimensional specialization of the canonical directional derivative owner. -/
noncomputable abbrev rightDerivative (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  f′(x; 1)

notation:arg f "′₊(" x ")" => rightDerivative f x

/-- The left derivative of an extended-real-valued function on `ℝ`, viewed as the
one-dimensional specialization of the canonical directional derivative owner. -/
noncomputable abbrev leftDerivative (f : ℝ → Set.Ioi (⊥ : EReal)) (x : ℝ) : EReal :=
  -f′(x; -1)

notation:arg f "′₋(" x ")" => leftDerivative f x

/-- Proposition 17.2 (1): clause (i). At an effective-domain point of a convex function, the
directional derivative exists in the source sense, with value given by the infimum formula. -/
theorem hasDirectionalDerivativeAt_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    HasDirectionalDerivativeAt f x y (f′(x; y)) := by
  sorry

/-- Any source-facing directional derivative of a convex function agrees with the canonical
function-valued owner. -/
theorem directionalDerivative_eq_of_hasDirectionalDerivativeAt
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} {ξ : EReal} (hξ : HasDirectionalDerivativeAt f x y ξ) :
    f′(x; y) = ξ := by
  sorry

-- Proof sketch: apply the convexity inequality to the segment from `x` to `y` and then rewrite
-- the resulting bound in terms of the directional derivative along `y - x`.
/-- Proposition 17.2 (2): clause (ii). The directional derivative toward `y` controls the secant
increment from `x` to `y`. -/
theorem directionalDerivative_add_value_le
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (y : H) :
    f′(x; y - x) + (f x : EReal) ≤ (f y : EReal) := sorry

-- Proof sketch: apply clause (ii) twice, once at `x` toward `y` and once at `y` toward `x`, then
-- combine the two inequalities.
/-- Proposition 17.2 (3): clause (iii). At two effective-domain points, opposite directional
derivatives along the connecting segment bound each other. -/
theorem directionalDerivative_le_neg_swap
    (hconv : ConvexOn f (effectiveDomain f))
    {x y : H} (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    f′(x; y - x) ≤ -f′(y; x - y) := sorry

-- Proof sketch: use Proposition 9.27 to get monotonicity of the directional difference quotients,
-- then derive positive homogeneity and subadditivity from the infimum formula.
/-- Proposition 17.2 (4): clause (iv). For a convex function, the directional derivative map at a
fixed base point is sublinear. -/
theorem sublinear_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    Sublinear (directionalDerivative f x) := sorry

variable {f}

-- Proof sketch: at an effective-domain point, every zero-direction difference quotient is the
-- finite value `(f x - f x) / α = 0`, so the defining infimum is `0`.
/-- Proposition 17.2 (5): clause (iv). At an effective-domain point, the directional derivative in
the zero direction is `0`. -/
theorem directionalDerivative_zero
    {x : H} (hx : x ∈ effectiveDomain f) :
    f′(x; 0) = 0 := by
  rw [directionalDerivative]
  have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hfx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hquot : directionalDifferenceQuotient f x 0 = fun _ ↦ (0 : EReal) := by
    funext α
    simp [directionalDifferenceQuotient, EReal.sub_self hfx_top hfx_bot]
  simp [hquot]

-- Proof sketch: combine sublinearity with the effective-domain description from clause (v) to show
-- that the directional derivative never takes the value `⊥` and has nonempty domain.
/-- Proposition 17.2 (6): clause (v). The directional derivative is a proper extended-real-valued
function. -/
theorem directionalDerivative_isProper
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    IsProper (directionalDerivative f x) := sorry

-- Proof sketch: clause (4) gives sublinearity, hence positive homogeneity; Proposition 10.3 then
-- identifies sublinearity of an `EReal`-valued function with convexity of its epigraph.
/-- Proposition 17.2 (7): clause (v). The epigraph of the directional derivative is convex. -/
theorem convex_epigraph_directionalDerivative
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    Convex ℝ (epigraph (directionalDerivative f x)) := by
  have hsub : Sublinear (directionalDerivative f x) :=
    sublinear_directionalDerivative f hconv hx
  exact
    (sublinear_iff_convex_epigraph_of_positivelyHomogeneous
      (directionalDerivative f x) hsub.positivelyHomogeneous).1 hsub

-- Proof sketch: show that finite directional derivative values correspond exactly to directions in
-- the cone generated by `effectiveDomain f - x`.
/-- Proposition 17.2 (8): clause (v). The domain of the directional derivative is the cone
generated by the translated effective domain. -/
theorem dom_directionalDerivative_eq_cone_effectiveDomain_sub_singleton
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) :
    dom (directionalDerivative f x) =
      Set.cone (effectiveDomain f - ({x} : Set H)) := sorry

-- Proof sketch: use the core assumption to obtain a symmetric effective-domain segment
-- `[x - β • y, x + β • y]` for every direction `y`, then bound the directional derivative above
-- and below by finite secant quotients.
/-- Proposition 17.2 (9): clause (vi). At a core point of the effective domain, every directional
derivative value is a real number. -/
theorem directionalDerivative_eq_coe_real_of_mem_core
    (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcore : x ∈ Set.core (effectiveDomain f)) :
    ∀ y : H, ∃ r : ℝ, f′(x; y) = (r : EReal) := sorry

end RealVectorSpace

end

end ERealFunction
