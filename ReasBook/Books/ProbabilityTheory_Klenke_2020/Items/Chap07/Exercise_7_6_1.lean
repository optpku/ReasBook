/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory ENNReal

universe u

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : ℝ≥0∞} {μ : Measure Ω}

private theorem hp_ne_zero [Fact (1 ≤ p)] : p ≠ 0 :=
  ne_of_gt <| lt_of_lt_of_le zero_lt_one Fact.out

/-- The textbook simple functions with finite-measure support, viewed in the canonical owner
subspace `Lp.simpleFunc ℝ p μ`. -/
private abbrev finiteMeasureSimpleFuncToLpSimpleFunc (p : ℝ≥0∞) (μ : Measure Ω) [Fact (1 ≤ p)]
    (hp_ne_top : p ≠ ∞) : {g : Ω →ₛ ℝ // g.FinMeasSupp μ} → Lp.simpleFunc ℝ p μ := fun g ↦
  Lp.simpleFunc.toLp g.1 ((SimpleFunc.memLp_iff_finMeasSupp hp_ne_zero hp_ne_top).2 g.2)

/-- The canonical map from simple functions with finite-measure support to their `L^p(μ)`
equivalence classes. -/
abbrev finiteMeasureSimpleFuncToLp (p : ℝ≥0∞) (μ : Measure Ω) [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    {g : Ω →ₛ ℝ // g.FinMeasSupp μ} → Lp ℝ p μ := fun g ↦
  finiteMeasureSimpleFuncToLpSimpleFunc p μ hp_ne_top g

-- Proof sketch: pass through the canonical `Lp.simpleFunc` owner. The representative recovered by
-- `Lp.simpleFunc.toSimpleFunc` is a.e. equal both to the `Lp` class and to the original simple
-- function.
/-- The `L^p` class attached to a finite-measure simple function agrees with that simple function
almost everywhere. -/
theorem finiteMeasureSimpleFuncToLp_ae_eq [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞)
    (g : {g : Ω →ₛ ℝ // g.FinMeasSupp μ}) :
    finiteMeasureSimpleFuncToLp p μ hp_ne_top g =ᵐ[μ] g.1 := by
  simpa [finiteMeasureSimpleFuncToLp, finiteMeasureSimpleFuncToLpSimpleFunc] using
    (Lp.simpleFunc.toSimpleFunc_eq_toFun (finiteMeasureSimpleFuncToLpSimpleFunc p μ hp_ne_top g)).symm.trans
      (Lp.simpleFunc.toSimpleFunc_toLp g.1
        ((SimpleFunc.memLp_iff_finMeasSupp hp_ne_zero hp_ne_top).2 g.2))

private theorem range_finiteMeasureSimpleFuncToLp [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    Set.range (finiteMeasureSimpleFuncToLp p μ hp_ne_top) = (Lp.simpleFunc ℝ p μ : Set (Lp ℝ p μ)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (finiteMeasureSimpleFuncToLpSimpleFunc p μ hp_ne_top g).2
  · intro hf
    refine ⟨⟨Lp.simpleFunc.toSimpleFunc ⟨f, hf⟩, ?_⟩, ?_⟩
    · exact (SimpleFunc.memLp_iff_finMeasSupp hp_ne_zero hp_ne_top).1 (Lp.simpleFunc.memLp ⟨f, hf⟩)
    · simpa [finiteMeasureSimpleFuncToLp, finiteMeasureSimpleFuncToLpSimpleFunc] using
        congrArg (fun h : Lp.simpleFunc ℝ p μ ↦ (h : Lp ℝ p μ))
          (Lp.simpleFunc.toLp_toSimpleFunc ⟨f, hf⟩)

-- Proof sketch: identify the image of `finiteMeasureSimpleFuncToLp` with the canonical dense
-- subset `Lp.simpleFunc ℝ p μ`; the equivalence between `MemLp` and `FinMeasSupp` for simple
-- functions when `1 ≤ p < ∞` is provided by `SimpleFunc.memLp_iff_finMeasSupp`, and density then
-- follows from `Lp.simpleFunc.dense`.
/-- Exercise 7.6.1: the image in `L^p(μ)` of the textbook set `𝔼_f` of real-valued simple
functions with finite-measure nonzero set is dense for `1 ≤ p < ∞`. -/
theorem finiteMeasureSimpleFunc_dense [Fact (1 ≤ p)] (hp_ne_top : p ≠ ∞) :
    Dense (Set.range (finiteMeasureSimpleFuncToLp p μ hp_ne_top)) := by
  rw [range_finiteMeasureSimpleFuncToLp hp_ne_top]
  exact Lp.simpleFunc.dense hp_ne_top

end MeasureTheory
