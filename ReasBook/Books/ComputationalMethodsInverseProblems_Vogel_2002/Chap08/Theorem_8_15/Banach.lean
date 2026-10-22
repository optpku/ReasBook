/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.Normed
public import Mathlib.Topology.Semicontinuity.Basic

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

namespace BV

variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/-- Helper for Theorem 8.15: the underlying `L¹(Ω)` projection is linear. -/
def toL1LinearMap : BV(Ω) →ₗ[ℝ] MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  { toFun := BV.toL1
    map_add' := BV.toL1_add
    map_smul' := BV.toL1_smul }

/-- Helper for Theorem 8.15: the underlying `L¹(Ω)` projection is continuous with operator norm
at most `1` for the BV norm. -/
def toL1CLM : BV(Ω) →L[ℝ] MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  LinearMap.mkContinuous toL1LinearMap 1 fun u ↦ by
    change ‖u.toL1‖ ≤ 1 * ‖u‖
    simpa using (BV.normToL1_le (Ω := Ω) u)

end BV

/-- Helper for Theorem 8.15: each fixed admissible-field pairing is lower semicontinuous on the
strong `L¹(Ω)` topology after casting to `EReal`. -/
theorem lpTotalVariationPairing_lowerSemicontinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    LowerSemicontinuous
      (fun f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) ↦
        ((totalVariationPairingCLM v f) : EReal)) := by
  -- A continuous real-valued pairing remains lower semicontinuous after the `EReal` cast.
  exact continuous_coe_real_ereal.comp_lowerSemicontinuous
    (totalVariationPairingCLM v).continuous.lowerSemicontinuous
    EReal.coe_strictMono.monotone

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation is the supremum of the fixed-field
pairing functionals on `L¹(Ω)`. -/
theorem lpTotalVariation_eq_iSup
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    (fun f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) ↦ totalVariation f) =
      fun f ↦ ⨆ v : AdmissibleTestField Ω, ((totalVariationPairingCLM v f) : EReal) := by
  -- Expand the defining supremum and rewrite each term through the pairing CLM.
  funext f
  rw [totalVariation_def, sSup_range]
  simp [totalVariationPairingCLM_apply]

/-- Helper for Theorem 8.15: the raw Chapter 8 total variation is lower semicontinuous on the
strong `L¹(Ω)` topology. -/
theorem lpTotalVariation_lowerSemicontinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    LowerSemicontinuous (fun f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) ↦ totalVariation f) := by
  -- Rewrite `TV` as an `iSup` of fixed-field pairings and use stability under `iSup`.
  rw [lpTotalVariation_eq_iSup]
  exact lowerSemicontinuous_iSup fun v ↦ lpTotalVariationPairing_lowerSemicontinuous v

/-- Helper for Theorem 8.15: strong `L¹(Ω)` convergence yields the liminf lower bound for the raw
Chapter 8 total variation. -/
theorem lpTotalVariation_le_liminf_of_tendstoL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {u : ℕ → MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    {g : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)}
    (hu : Filter.Tendsto u Filter.atTop (nhds g)) :
    totalVariation g ≤ Filter.liminf (fun n ↦ totalVariation (u n)) Filter.atTop := by
  let Φ : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) → EReal := fun f ↦ totalVariation f
  -- Lower semicontinuity controls the neighborhood liminf at the strong limit point.
  have hsc :
      Φ g ≤ Filter.liminf Φ (nhds g) :=
    (lpTotalVariation_lowerSemicontinuous (Ω := Ω)).le_liminf g
  -- The sequence liminf dominates the neighborhood liminf along the convergent trajectory.
  have hcomp :
      Filter.liminf Φ (nhds g) ≤ Filter.liminf (fun n ↦ Φ (u n)) Filter.atTop :=
    hu.liminf_le_liminf_comp
  simpa [Φ] using le_trans hsc hcomp

end VariationalRegularization
