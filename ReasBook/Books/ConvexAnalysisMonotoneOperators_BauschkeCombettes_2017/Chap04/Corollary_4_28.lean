/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Theorem_4_27

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: closed convex subsets of a real Hilbert space are weakly sequentially closed by
-- Theorem 3.34. Apply the demiclosedness principle from Theorem 4.27 to the residual map
-- `x ↦ x - T x` at `0`; the residual convergence hypothesis then forces `T x = x`.
/-- Corollary 4.28: if `D` is a closed convex subset of a real Hilbert space, `T : D → H` is
nonexpansive, `xₙ` converges weakly to `x` in `D`, and the residuals `xₙ - T xₙ` converge strongly
to `0`, then `x` is a fixed point of `T`. -/
theorem map_eq_of_tendsto_weakly_of_residual_tendsto_zero_of_nonexpansive
    {D : Set H} (_hD_closed : IsClosed D) (_hD_convex : Convex ℝ D)
    {T : D → H} (hT : LipschitzWith 1 T) {xₙ : ℕ → D} {x : D}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n : H)) atTop
      (𝓝 (toWeakSpace ℝ H (x : H))))
    (hres : Tendsto (fun n ↦ (xₙ n : H) - T (xₙ n)) atTop (𝓝 (0 : H))) :
    T x = (x : H) := by
  have hx_residual : (x : H) - T x = (0 : H) :=
    demiclosed_residual_of_nonexpansive hT 0 hweak hres
  exact (sub_eq_zero.mp hx_residual).symm
