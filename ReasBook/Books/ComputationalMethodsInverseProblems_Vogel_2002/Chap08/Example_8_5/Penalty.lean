/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- The smooth norm penalty `x ↦ √(‖x‖ ^ 2 + β ^ 2)` on `EuclideanSpace ℝ (Fin d)`. -/
def smoothNormPenalty (β : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x ↦ Real.sqrt (‖x‖ ^ 2 + β ^ 2)

/-- The defining formula for `smoothNormPenalty`. -/
theorem smoothNormPenalty_def (β : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    smoothNormPenalty β x = Real.sqrt (‖x‖ ^ 2 + β ^ 2) := by
  rfl

/-- For `0 < β`, the function `smoothNormPenalty β` is convex on all of
`EuclideanSpace ℝ (Fin d)`. -/
theorem convexOn_smoothNormPenalty (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin d))) (smoothNormPenalty β) := by
  have _ := hβ
  have smoothNormPenalty_eq_norm_toLpPair
      (x : EuclideanSpace ℝ (Fin d)) :
      smoothNormPenalty β x = ‖WithLp.toLp 2 (x, β)‖ := by
    refine (sq_eq_sq₀ (by
      rw [smoothNormPenalty_def]
      exact Real.sqrt_nonneg _) (norm_nonneg _)).1 ?_
    rw [smoothNormPenalty_def, Real.sq_sqrt (show 0 ≤ ‖x‖ ^ 2 + β ^ 2 by positivity)]
    simpa [pow_two] using
      (WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (x, β))).symm
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hpair :
      WithLp.toLp 2 (a • x + b • y, β) =
        a • WithLp.toLp 2 (x, β) + b • WithLp.toLp 2 (y, β) := by
    rw [← WithLp.toLp_add, ← WithLp.toLp_smul, ← WithLp.toLp_smul]
    apply congrArg (WithLp.toLp 2)
    change (a • x + b • y, β) = a • (x, β) + b • (y, β)
    refine Prod.ext ?_ ?_
    · simp
    · calc
        β = (a + b) * β := by rw [hab, one_mul]
        _ = a * β + b * β := by ring
  -- The claim is the norm convexity inequality for the `L²` pair `(x, β)`.
  calc
    smoothNormPenalty β (a • x + b • y)
      = ‖WithLp.toLp 2 (a • x + b • y, β)‖ := smoothNormPenalty_eq_norm_toLpPair _
    _ = ‖a • WithLp.toLp 2 (x, β) + b • WithLp.toLp 2 (y, β)‖ := by rw [hpair]
    _ ≤ ‖a • WithLp.toLp 2 (x, β)‖ + ‖b • WithLp.toLp 2 (y, β)‖ := norm_add_le _ _
    _ = a * ‖WithLp.toLp 2 (x, β)‖ + b * ‖WithLp.toLp 2 (y, β)‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ = a * smoothNormPenalty β x + b * smoothNormPenalty β y := by
          rw [← smoothNormPenalty_eq_norm_toLpPair, ← smoothNormPenalty_eq_norm_toLpPair]

end VariationalRegularization
