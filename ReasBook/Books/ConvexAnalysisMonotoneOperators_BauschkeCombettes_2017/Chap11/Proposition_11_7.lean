/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Set

namespace ERealFunction

section EvenConvexOn

variable (φ : ℝ → Set.Ioi (⊥ : EReal))

/-- Proposition 11.7 (1): an even convex `]-∞,+∞]`-valued function on `ℝ` attains its global
minimum at `0`. -/
-- Proof sketch: apply the Jensen inequality to the midpoint decomposition
-- `0 = (1 / 2) • x + (1 / 2) • (-x)` and use evenness to identify the two endpoint values.
theorem zero_mem_argmin_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : (0 : ℝ) ∈ Argmin φ.asEReal := sorry

/-- Companion bridge: Proposition 11.7 (1) in `IsMinOn` form. -/
theorem isMinOn_zero_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : IsMinOn φ.asEReal univ 0 :=
  mem_argmin_iff.mp <| zero_mem_argmin_of_even_convexOn φ hconv heven

/-- Proposition 11.7 (2): an even convex `]-∞,+∞]`-valued function on `ℝ` is increasing on the
nonnegative ray. -/
-- Proof sketch: for `0 ≤ ξ < η`, write `ξ = (ξ / η) • η + (1 - ξ / η) • 0`, apply convexity, and
-- then use clause (1) to bound the value at `0` by the value at `η`.
theorem monotoneOn_nonnegative_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : MonotoneOn φ.asEReal (Ici 0) := sorry

/-- Proposition 11.7 (3): an even convex `]-∞,+∞]`-valued function on `ℝ` is decreasing on the
nonpositive ray. -/
-- Proof sketch: transport clause (2) from the nonnegative ray by the symmetry `x ↦ -x` and use
-- evenness to identify the corresponding function values.
theorem antitoneOn_nonpositive_of_even_convexOn
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    : AntitoneOn φ.asEReal (Iic 0) := by
  intro x hx y hy hxy
  have hmono := monotoneOn_nonnegative_of_even_convexOn φ hconv heven
  have hx' : -x ∈ Ici (0 : ℝ) := by
    simpa using hx
  have hy' : -y ∈ Ici (0 : ℝ) := by
    simpa using hy
  have hxy' : -y ≤ -x := by
    simpa using hxy
  simpa [heven x, heven y] using hmono hy' hx' hxy'

/-- Proposition 11.7 (4): if an even convex `]-∞,+∞]`-valued function on `ℝ` vanishes only at
`0`, then it is strictly increasing on the nonnegative ray. -/
-- Proof sketch: repeat the convex-combination argument from clause (2), but now use the
-- vanishing-only-at-zero hypothesis together with `η > 0` to get the strict inequality
-- `(φ 0 : EReal) < φ η`.
theorem strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0) :
    StrictMonoOn φ.asEReal (Ici 0) := sorry

/-- Proposition 11.7 (5): if an even convex `]-∞,+∞]`-valued function on `ℝ` vanishes only at
`0`, then it is strictly decreasing on the nonpositive ray. -/
-- Proof sketch: transport clause (4) from the nonnegative ray by the symmetry `x ↦ -x` and use
-- evenness to turn strict increase on `[0,+∞)` into strict decrease on `(-∞,0]`.
theorem strictAntiOn_nonpositive_of_even_convexOn_eq_zero_iff
    (hconv : ConvexOn φ (effectiveDomain φ))
    (heven : Function.Even φ.asEReal)
    (hzero : ∀ x : ℝ, φ.asEReal x = 0 ↔ x = 0) :
    StrictAntiOn φ.asEReal (Iic 0) := by
  intro x hx y hy hxy
  have hmono := strictMonoOn_nonnegative_of_even_convexOn_eq_zero_iff φ hconv heven hzero
  have hx' : -x ∈ Ici (0 : ℝ) := by
    simpa using hx
  have hy' : -y ∈ Ici (0 : ℝ) := by
    simpa using hy
  have hxy' : -y < -x := by
    simpa using hxy
  simpa [heven x, heven y] using hmono hy' hx' hxy'

end EvenConvexOn

end ERealFunction
