/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Fact 2.66: textbook open-neighborhood form of symmetry of the second Fréchet derivative.
If `T` admits a Fréchet derivative field `DT` on an open neighborhood `U` of `x`, and `DT` is
Fréchet differentiable at `x` with derivative `D2T`, then the bilinear map `(y, z) ↦ D2T y z`
is symmetric. -/
-- Proof sketch: because `U` is an open neighborhood of `x`, the hypotheses give a first
-- derivative field for `T` on some neighborhood of `x`; then apply
-- `second_derivative_symmetric_of_eventually_of_real` to the derivative field `DT`.
theorem secondFrechetDerivAt_symmetric
    {T : H → K} {DT : H → H →L[ℝ] K} {D2T : H →L[ℝ] H →L[ℝ] K}
    {U : Set H} {x : H}
    (hU : IsOpen U) (hx : x ∈ U)
    (hT : ∀ y ∈ U, HasFDerivAt T (DT y) y)
    (hDT : HasFDerivAt DT D2T x) :
    ∀ y z : H, D2T y z = D2T z y := by
  -- Route correction: use the abstract symmetry theorem for second Fréchet derivatives
  -- after converting the open-neighborhood derivative field into an eventual one at `x`.
  have hT_eventually : ∀ᶠ y in nhds x, HasFDerivAt T (DT y) y := by
    -- The openness of `U` gives a neighborhood of `x` contained in `U`.
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hT y hy
  intro y z
  -- The mathlib Schwarz theorem now gives symmetry of the bilinear second derivative.
  exact second_derivative_symmetric_of_eventually_of_real hT_eventually hDT y z
