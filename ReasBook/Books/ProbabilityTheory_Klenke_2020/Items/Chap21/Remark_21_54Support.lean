/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_52

open MeasureTheory Set
open scoped Topology ENNReal

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
attribute [local instance] Classical.propDecidable

/-- Helper for Remark 21.54: a locally integrable density has a continuous interval-integral
primitive. -/
theorem continuousPrimitiveOfLocallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) :
    Continuous (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, f s) := by
  -- Local integrability upgrades to interval integrability on each compact interval.
  refine intervalIntegral.continuous_primitive ?_ 0
  intro a b
  exact (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

/-- Helper for Remark 21.54: the path obtained by integrating a real function from `0` to `t`. -/
def indefiniteIntegralPath (f : ℝ → ℝ) : PathSpace :=
  if hf : LocallyIntegrable f volume then
    { toFun := fun t ↦ ∫ s in (0 : ℝ)..(t : ℝ), f s
      continuous_toFun := (continuousPrimitiveOfLocallyIntegrable hf).comp continuous_subtype_val }
  else 0

/-- Helper for Remark 21.54: under local integrability, the repaired path agrees with the intended
primitive `t ↦ ∫_0^t f`. -/
theorem indefiniteIntegralPath_apply_of_locallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (t : NNReal) :
    indefiniteIntegralPath f t = ∫ s in (0 : ℝ)..(t : ℝ), f s := by
  -- Rewrite through the totalized definition of `indefiniteIntegralPath`.
  simp [indefiniteIntegralPath, hf]

/-- Helper for Remark 21.54: a locally integrable density defines a path of locally bounded
variation on `[0, ∞)`. -/
theorem locallyBoundedVariationOn_univ_indefiniteIntegralPath
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyBoundedVariationOn (indefiniteIntegralPath f) univ := by
  -- It is enough to show bounded variation on each initial interval `[0, t]`.
  rw [locallyBoundedVariationOn_univ_iff_forall_boundedVariationOn_Icc_zero]
  intro t
  let F : ℝ → ℝ := fun x ↦ ∫ s in (0 : ℝ)..x, f s
  have hft : IntervalIntegrable f volume (0 : ℝ) t := by
    exact (hf.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hF_bv : BoundedVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- Absolute continuity of the primitive on `[0, t]` yields bounded variation there.
    have hF_ac : AbsolutelyContinuousOnInterval F 0 t := by
      simpa [F] using hft.absolutelyContinuousOnInterval_intervalIntegral (by simp)
    simpa [uIcc_of_le t.2] using hF_ac.boundedVariationOn
  have hEq :
      EqOn (indefiniteIntegralPath f) (fun x : NNReal ↦ F x) (Icc 0 t) := by
    -- On nonnegative times the path is exactly the primitive.
    intro x hx
    simpa [F] using indefiniteIntegralPath_apply_of_locallyIntegrable hf x
  have hcomp :
      eVariationOn (indefiniteIntegralPath f) (Icc 0 t) ≤
        eVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
    -- Compare the `NNReal`-indexed path with the real primitive through the monotone coercion.
    calc
      eVariationOn (indefiniteIntegralPath f) (Icc 0 t) =
          eVariationOn (fun x : NNReal ↦ F x) (Icc 0 t) :=
        eVariationOn.eq_of_eqOn hEq
      _ ≤ eVariationOn F (Set.Icc (0 : ℝ) (t : ℝ)) := by
        apply eVariationOn.comp_le_of_monotoneOn F (fun x : NNReal ↦ (x : ℝ))
        · intro x hx y hy hxy
          exact_mod_cast hxy
        · intro x hx
          simpa using hx
  exact (hcomp.trans_lt (lt_top_iff_ne_top.mpr hF_bv)).ne

/-- Helper for Remark 21.54: the signed Lebesgue-Stieltjes integral on `[0, t]`, defined from the
Jordan decomposition of a signed measure. -/
def signedLebesgueStieltjesIntegralUpTo
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
    ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart

/-- Helper for Remark 21.54: unfolding `signedLebesgueStieltjesIntegralUpTo` gives the
Jordan-decomposition formula on `[0, t]`. -/
theorem signedLebesgueStieltjesIntegralUpTo_eq
    (F : ℝ → ℝ) (μ : SignedMeasure ℝ) (t : NNReal) :
    signedLebesgueStieltjesIntegralUpTo F μ t =
      ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.posPart -
        ∫ x in Set.Icc (0 : ℝ) (t : ℝ), F x ∂μ.toJordanDecomposition.negPart :=
  rfl
