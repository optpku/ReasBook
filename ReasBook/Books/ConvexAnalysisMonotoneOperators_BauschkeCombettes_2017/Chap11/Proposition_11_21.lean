/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- If an extended-real-valued function is weakly lower semicontinuous at the weak limit `x`, then
the weak limit of any weakly convergent minimizing sequence is a global minimizer. -/
-- Proof sketch: apply weak lower semicontinuity at the weak limit `x` to get
-- `f x ≤ liminf (f ∘ xₙ) atTop`, then use the minimizing-sequence convergence to identify this
-- liminf with `sInf (Set.range f)`. Since `sInf (Set.range f) ≤ f y` for every `y`, conclude that
-- `f x ≤ f y` for all `y`.
theorem mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_weaklyLowerSemicontinuousAt
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hf_wlsc : WeaklyLowerSemicontinuousAt f x) (hxₙ : IsMinimizingSequence f xₙ)
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    x ∈ Argmin f := by
  rw [mem_argmin_iff_eq_sInf]
  have hx_le_liminf :=
    (weaklyLowerSemicontinuousAt_iff_forall_net_le_liminf f x).1 hf_wlsc xₙ hweak
  have hliminf : liminf (f ∘ xₙ) atTop = sInf (Set.range f) := by
    simpa [Function.comp] using hxₙ.tendsto.liminf_eq
  refine le_antisymm ?_ ((isGLB_sInf (Set.range f)).1 (Set.mem_range_self x))
  calc
    f x ≤ liminf (f ∘ xₙ) atTop := hx_le_liminf
    _ = sInf (Set.range f) := hliminf

/-- Proposition 11.21: the weak limit of a weakly convergent minimizing sequence of a lower
semicontinuous quasiconvex `]-∞,+∞]`-valued function on a real Hilbert space is a global
minimizer. -/
-- Proof sketch: Proposition 10.25 upgrades lower semicontinuity of a quasiconvex function to weak
-- lower semicontinuity. Then apply the helper theorem above to the weakly convergent minimizing
-- sequence.
theorem mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
    {f : H → EReal} (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {x : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    x ∈ Argmin f := by
  have hf_wlsc : WeaklyLowerSemicontinuous f :=
    weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
  exact
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_weaklyLowerSemicontinuousAt
      ((weaklyLowerSemicontinuous_iff_forall_weaklyLowerSemicontinuousAt f).1 hf_wlsc x)
      hxₙ hweak

end ERealFunction
