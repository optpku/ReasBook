/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory
open MeasureTheory.L2
open scoped MeasureTheory InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {T : ℝ}

/- Example 2.8: the textbook interval space `L²([0,T]; H)` is the canonical mathlib `L²` space
for the restricted Lebesgue measure on `[0, T]`. -/
#check (ℝ →₂[volume.restrict (Set.Icc 0 T)] H)

-- Proof sketch: specialize `MeasureTheory.L2.inner_def` to the restricted Lebesgue measure
-- `volume.restrict (Set.Icc 0 T)` and rewrite the resulting integral as the set integral over
-- `[0, T]`.
/-- Example 2.8: for a real inner product space `H` and `T > 0`, the interval space
`L²([0,T]; H)` carries the canonical `L²` inner product given by integrating the pointwise inner
product over `[0,T]`. In particular, this applies to the textbook separable real Hilbert-space
setting, and specializing to `H = ℝ` recovers the usual real-valued space `L²([0,T])`. -/
theorem l2_interval_inner_eq_integral_inner (_hT : 0 < T)
    (x y : ℝ →₂[volume.restrict (Set.Icc 0 T)] H) :
    ⟪x, y⟫_ℝ = ∫ t in Set.Icc 0 T, ⟪x t, y t⟫_ℝ ∂volume := by
  simpa using (inner_def x y)
