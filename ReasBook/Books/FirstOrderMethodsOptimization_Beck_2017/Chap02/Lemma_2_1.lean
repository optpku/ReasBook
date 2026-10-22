/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Instances.EReal.Lemmas
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The primal-space support function of `C`, obtained by evaluating the chapter owner
`support_function` along the Riesz map `toDualMap`. This is the textbook support
function `σ_C` in Euclidean coordinates. -/
noncomputable abbrev support_function_primal (C : Set E) : E → EReal :=
  fun x ↦ support_function C (toDualMap ℝ E x)

/-- Textbook notation for the primal-space support function. -/
notation "σ[" C "]" => support_function_primal C

-- Proof sketch: unfold `support_function_primal`; this is exactly the specialization of
-- `support_function` along `InnerProductSpace.toDualMap`.
/-- Evaluating `σ[C]` at `x` is the same as evaluating the chapter owner `support_function C` at
the dual vector corresponding to `x`. -/
@[simp] theorem support_function_primal_apply (C : Set E) (x : E) :
    σ[C] x = support_function C (toDualMap ℝ E x) :=
  rfl

-- Proof sketch: specialize the chapter owner `support_function` along the canonical map
-- `InnerProductSpace.toDualMap ℝ E`; the resulting evaluation is exactly the supremum of the
-- pairings `c ↦ ⟪x, c⟫` over `C`.
/-- The inner-product-space support-function formula is the specialization of the chapter owner
`support_function` along `toDualMap`, written on the source-facing owner
`σ[C]`. -/
theorem support_function_eq_sSup (C : Set E) (x : E) :
    σ[C] x = sSup ((fun c : E ↦ (inner ℝ x c : EReal)) '' C) := by
  simp [support_function_primal, support_function_apply]

/-- Helper for Lemma 2.1: rewrite the primal support function as a subtype-indexed supremum of
dual evaluations. -/
lemma support_function_primal_eq_iSup (C : Set E) :
    σ[C] = fun x ↦ ⨆ c : C, ((((toDualMap ℝ E c.1) x : ℝ) : EReal)) := by
  -- Rewrite the support function as a supremum indexed directly by members of `C`.
  funext x
  rw [support_function_eq_sSup, sSup_image, iSup_subtype]
  simp [InnerProductSpace.toDualMap_apply_apply, real_inner_comm]

/-- Helper for Lemma 2.1: each fixed dual-evaluation slice is lower semicontinuous as an
`EReal`-valued function. -/
lemma lowerSemicontinuous_ereal_toDualEval (c : E) :
    LowerSemicontinuous (fun x : E ↦ ((((toDualMap ℝ E c) x : ℝ) : EReal))) := by
  -- Compose the continuous linear functional with the continuous coercion `ℝ → EReal`.
  simpa using
    (continuous_coe_real_ereal.comp ((toDualMap ℝ E c).continuous)).lowerSemicontinuous

/-- Helper for Lemma 2.1: each fixed dual-evaluation slice has a convex real epigraph. -/
lemma isConvexFunction_ereal_toDualEval (c : E) :
    is_convex_function (fun x : E ↦ ((((toDualMap ℝ E c) x : ℝ) : EReal))) := by
  -- Identify the real epigraph with the epigraph of a linear functional on the whole space.
  rw [is_convex_function_iff_convex_real_epigraph]
  simpa [Set.setOf_and, Set.mem_univ] using
    (show Convex ℝ {p : E × ℝ | p.1 ∈ Set.univ ∧ (((toDualMap ℝ E c) p.1 : ℝ)) ≤ p.2} from
      ((LinearMap.convexOn (toDualMap ℝ E c).toLinearMap convex_univ).convex_epigraph))

/-- Lemma 2.1: the primal-space support function `σ[C]` of a subset of a real inner product space
is closed, i.e. lower semicontinuous, and convex in the chapter-owner sense. The textbook states
this for nonempty `C`, but the same conclusion holds without that extra assumption. -/
theorem support_function_closed_and_convex (C : Set E) :
    LowerSemicontinuous (σ[C]) ∧ is_convex_function (σ[C]) := by
  constructor
  · -- Rewrite to a pointwise `iSup` and apply lower semicontinuity of arbitrary suprema.
    rw [support_function_primal_eq_iSup]
    exact lowerSemicontinuous_iSup (fun c ↦ lowerSemicontinuous_ereal_toDualEval c.1)
  · -- Rewrite the real epigraph as an intersection of convex affine slices.
    rw [is_convex_function_iff_convex_real_epigraph, support_function_primal_eq_iSup]
    let epigraphSlice : C → Set (E × ℝ) :=
      fun c ↦ {p : E × ℝ | ((((toDualMap ℝ E c.1) p.1 : ℝ) : EReal)) ≤ (p.2 : EReal)}
    have hslice : ∀ c : C, Convex ℝ (epigraphSlice c) := by
      intro c
      -- Each slice is the real epigraph of a linear functional.
      simpa [epigraphSlice] using
        (is_convex_function_iff_convex_real_epigraph _).mp (isConvexFunction_ereal_toDualEval c.1)
    have hepigraph :
        {p : E × ℝ | (⨆ c : C, ((((toDualMap ℝ E c.1) p.1 : ℝ) : EReal))) ≤ (p.2 : EReal)}
          = ⋂ c : C, epigraphSlice c := by
      -- A point lies above the supremum exactly when it lies above every slice.
      ext p
      simp [epigraphSlice, iSup_le_iff]
    rw [hepigraph]
    exact convex_iInter hslice

/-- Lemma 2.1 (1): the primal-space support function `σ[C]` is closed, i.e.
lower semicontinuous. The textbook's nonemptiness hypothesis is redundant. -/
theorem support_function_lowerSemicontinuous (C : Set E) :
    LowerSemicontinuous (σ[C]) :=
  (support_function_closed_and_convex C).1

/-- Lemma 2.1 (2): the primal-space support function `σ[C]` is convex in the chapter-owner sense
`is_convex_function`. The textbook's nonemptiness hypothesis is redundant. -/
theorem support_function_isConvexFunction (C : Set E) :
    is_convex_function (σ[C]) :=
  (support_function_closed_and_convex C).2

end
