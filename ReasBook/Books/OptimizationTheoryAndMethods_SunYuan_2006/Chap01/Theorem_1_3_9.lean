/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.List.TFAE
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.Semicontinuity.Basic

-- Semantic recall checked: mathlib has
-- `lowerSemicontinuous_iff_isClosed_epigraph` and
-- `lowerSemicontinuous_iff_isClosed_preimage`.
-- This item keeps the source's `WithTop ℝ` codomain together with the book's
-- `r : ℝ` epigraph and lower-level-set views, but uses the canonical owner
-- `LowerSemicontinuous` on an arbitrary topological domain.

open Set

section Theorem139

variable {α : Type*} [TopologicalSpace α]

/-- Companion theorem: for `f : α → WithTop ℝ`, lower semicontinuity of `f`
is equivalent to closedness of its real-height epigraph in `α × ℝ`. -/
theorem lowerSemicontinuous_iff_isClosed_realEpigraph (f : α → WithTop ℝ) :
    LowerSemicontinuous f ↔ IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)} := by
  constructor
  · intro hf
    have hcont : Continuous (fun p : α × ℝ ↦ (p.1, (p.2 : WithTop ℝ))) :=
      continuous_fst.prodMk (WithTop.continuous_coe.comp continuous_snd)
    simpa using hf.isClosed_epigraph.preimage hcont
  · intro h
    refine lowerSemicontinuous_iff_isClosed_preimage.2 ?_
    intro y
    rcases eq_or_ne y ⊤ with rfl | hy
    · simp
    · rcases WithTop.ne_top_iff_exists.mp hy with ⟨r, rfl⟩
      have hslice :
          f ⁻¹' Iic (r : WithTop ℝ) =
            (fun x : α ↦ (x, r)) ⁻¹' {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)} := by
        ext x
        simp
      have hclosed :
          IsClosed
            ((fun x : α ↦ (x, r)) ⁻¹' {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)}) :=
        h.preimage (continuous_id.prodMk continuous_const)
      rw [← hslice] at hclosed
      simpa using hclosed

/-- Companion theorem: for `f : α → WithTop ℝ`, lower semicontinuity of `f`
is equivalent to closedness of every real sublevel set `{x | f x ≤ r}` for `r : ℝ`. -/
theorem lowerSemicontinuous_iff_forall_isClosed_sublevelSet (f : α → WithTop ℝ) :
    LowerSemicontinuous f ↔ ∀ r : ℝ, IsClosed (f ⁻¹' Iic (r : WithTop ℝ)) := by
  constructor
  · intro hf r
    simpa using hf.isClosed_preimage (r : WithTop ℝ)
  · intro h
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    rcases eq_or_ne y ⊤ with rfl | hy
    · simp
    · rcases WithTop.ne_top_iff_exists.mp hy with ⟨r, rfl⟩
      simpa using h r

/-- A lower semicontinuous `WithTop ℝ`-valued function has closed real sublevel sets. -/
theorem LowerSemicontinuous.isClosed_sublevelSet {f : α → WithTop ℝ}
    (hf : LowerSemicontinuous f) (r : ℝ) : IsClosed (f ⁻¹' Iic (r : WithTop ℝ)) := by
  simpa using hf.isClosed_preimage (r : WithTop ℝ)

/-- Chapter01 Theorem 1.3.9: for `f : α → WithTop ℝ`, the following are equivalent:
1. `LowerSemicontinuous f`;
2. `IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)}`;
3. `∀ r : ℝ, IsClosed (f ⁻¹' Iic (r : WithTop ℝ))`. -/
theorem lowerSemicontinuous_realEpigraph_sublevelSet_tfae (f : α → WithTop ℝ) :
    List.TFAE [
      LowerSemicontinuous f,
      IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)},
      ∀ r : ℝ, IsClosed (f ⁻¹' Iic (r : WithTop ℝ))
    ] := by
  tfae_have 1 ↔ 2 := lowerSemicontinuous_iff_isClosed_realEpigraph f
  tfae_have 1 ↔ 3 := lowerSemicontinuous_iff_forall_isClosed_sublevelSet f
  tfae_finish

/-
The next two companion theorems package the remaining implications in the
three-way equivalence stated in the source.
-/
/-- Companion theorem: for `f : α → WithTop ℝ`, closedness of the real-height epigraph is
equivalent to closedness of all real sublevel sets `{x | f x ≤ r}` with `r : ℝ`. -/
theorem isClosed_realEpigraph_iff_forall_isClosed_sublevelSet (f : α → WithTop ℝ) :
    IsClosed {p : α × ℝ | f p.1 ≤ (p.2 : WithTop ℝ)} ↔
      ∀ r : ℝ, IsClosed (f ⁻¹' Iic (r : WithTop ℝ)) :=
  (lowerSemicontinuous_iff_isClosed_realEpigraph f).symm.trans
    (lowerSemicontinuous_iff_forall_isClosed_sublevelSet f)

end Theorem139
