/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {P : Measure[mΩ] Ω} [IsProbabilityMeasure P]

-- Proof sketch: view `condExpL2` as the orthogonal projection of `L²(P)` onto the subspace of
-- `ℱ`-measurable classes, apply the projection minimality theorem there, and then rewrite the
-- resulting `edist` statement back to `eLpNorm` for the underlying functions.
/-- Remark 8.15: among all `ℱ`-measurable square-integrable real random variables, the conditional
expectation `P[X | ℱ]` minimizes the `L²` distance to `X`. -/
theorem condExp_is_best_l2_prediction {ℱ : MeasurableSpace Ω} (hℱ : ℱ ≤ mΩ) {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (hY_meas : Measurable[ℱ] Y) :
    eLpNorm (X - P[X | ℱ]) 2 P ≤ eLpNorm (X - Y) 2 P := by
  let X₂ : Lp ℝ 2 P := hX.toLp X
  let Y₂ : Lp ℝ 2 P := hY.toLp Y
  let U : Submodule ℝ (Lp ℝ 2 P) :=
    @lpMeas Ω ℝ ℝ inferInstance inferInstance inferInstance ℱ mΩ 2 P
  haveI := fact_one_le_two_ennreal
  haveI : Fact (ℱ ≤ mΩ) := ⟨hℱ⟩
  haveI : CompleteSpace U := by
    change
      CompleteSpace (@lpMeas Ω ℝ ℝ inferInstance inferInstance inferInstance ℱ mΩ 2 P)
    rw [(lpMeasSubgroupToLpMeasIso ℝ ℝ 2 P).symm.completeSpace_iff]
    infer_instance
  have hY_mem : Y₂ ∈ U := by
    change @AEStronglyMeasurable Ω ℝ inferInstance ℱ mΩ (Y₂ : Ω → ℝ) P
    refine ⟨Y, hY_meas.stronglyMeasurable, ?_⟩
    simpa [Y₂] using (hY.coeFn_toLp : (hY.toLp Y : Ω → ℝ) =ᵐ[P] Y)
  let Yℱ : U := ⟨Y₂, hY_mem⟩
  have hstar : U.starProjection X₂ = (condExpL2 ℝ ℝ hℱ X₂ : Lp ℝ 2 P) := by
    rfl
  have hmin :
      ‖X₂ - (condExpL2 ℝ ℝ hℱ X₂ : Lp ℝ 2 P)‖ =
        ⨅ Z : U, ‖X₂ - Z‖ := by
    rw [← hstar]
    exact Submodule.starProjection_minimal X₂
  have hproj :
      ‖X₂ - (condExpL2 ℝ ℝ hℱ X₂ : Lp ℝ 2 P)‖ ≤ ‖X₂ - Y₂‖ := by
    rw [hmin]
    refine (ciInf_le ?_ Yℱ).trans_eq ?_
    · exact ⟨0, Set.forall_mem_range.2 fun _ ↦ norm_nonneg _⟩
    · rfl
  have hdist :
      edist X₂ (condExpL2 ℝ ℝ hℱ X₂ : Lp ℝ 2 P) ≤ edist X₂ Y₂ := by
    simpa [Lp.edist_dist, dist_eq_norm] using ENNReal.ofReal_le_ofReal hproj
  have hcond : MemLp (P[X | ℱ]) 2 P := hX.condExp
  have hcond_toLp :
      hcond.toLp (P[X | ℱ]) = (condExpL2 ℝ ℝ hℱ X₂ : Lp ℝ 2 P) := by
    apply Lp.ext
    simpa [X₂] using hcond.coeFn_toLp.trans (hX.condExpL2_ae_eq_condExp hℱ).symm
  rw [← hcond_toLp] at hdist
  simpa [U, X₂, Y₂, Yℱ] using hdist
