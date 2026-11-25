/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_16.ApproximationBridge
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

public section
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff
namespace VariationalRegularization
namespace BVCompactness
variable {d : ℕ}

/-- Ambient smooth recovery with one extension constant, uniform in the BV
function and in the approximation index. The derivative bound is on ambient
volume; the approximants are not required to vanish near `∂Ω`. -/
theorem existsSmoothCompactSupportRecoverySeq_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : BV Ω,
      ∃ φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ,
        ∀ n : ℕ,
          ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧
          eLpNorm (fun x ↦ u.toL1 x - φ n x) 1 (domainMeasure Ω) ≤
            ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
          (∫ x, ‖fderiv ℝ (φ n) x‖ ∂volume) ≤ C * ‖u‖ := by
  classical
  obtain ⟨C, hC, happrox⟩ := existsSmoothCompactSupportApprox_of_bv (Ω := Ω)
  refine ⟨C, hC, ?_⟩
  intro u
  have h : ∀ n : ℕ, ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (1 / (n + 1 : ℝ)) ∧
      (∫ x, ‖fderiv ℝ φ x‖ ∂volume) ≤ C * ‖u‖ :=
    fun n ↦ happrox u (1 / (n + 1 : ℝ)) (by positivity)
  choose φ hφ using h
  exact ⟨φ, hφ⟩

/-- The independent-budget interface follows directly from the constructed
ambient approximants, without a circular call through recovery sequences. -/
theorem existsSmoothCompactSupportApprox_of_bv_twoBudgets
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [HasBoundedBVExtension Ω] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : BV Ω) (δ η : ℝ), 0 < δ → 0 < η →
      ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
        eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal δ ∧
        (∫ x, ‖fderiv ℝ φ x‖ ∂volume) ≤ C * ‖u‖ + η :=
  existsSmoothCompactSupportApprox_of_bv_twoBudgetsDeriv

/-- The reciprocal `L¹` error budget implies convergence in measure on `Ω`.
This transfer uses no support condition at the boundary. -/
lemma recoverySeq_tendstoInMeasure
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) (φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hs : ∀ n, ContDiff ℝ ∞ (φ n))
    (herr : ∀ n, eLpNorm (fun x ↦ u.toL1 x - φ n x) 1 (domainMeasure Ω) ≤
      ENNReal.ofReal (1 / (n + 1 : ℝ))) :
    TendstoInMeasure (domainMeasure Ω) φ atTop u.toL1 := by
  have hbound (n : ℕ) : eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω) ≤
      ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    change eLpNorm (φ n - (u.toL1 : EuclideanSpace ℝ (Fin d) → ℝ)) 1 (domainMeasure Ω) ≤ _
    rw [eLpNorm_sub_comm]
    exact herr n
  have hupper : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (nhds 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have hlim : Tendsto (fun n ↦ eLpNorm (fun x ↦ φ n x - u.toL1 x) 1 (domainMeasure Ω)) atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun _ ↦ bot_le) hbound
  exact tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n ↦ (hs n).continuous.aestronglyMeasurable) (Lp.aestronglyMeasurable u.toL1) hlim

end BVCompactness
end VariationalRegularization
