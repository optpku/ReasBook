module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import Mathlib.Analysis.CStarAlgebra.Matrix

public section

open scoped Matrix.Norms.L2Operator

namespace Asymptotics.IsUniformRemainderOn

universe u v

/-- Rectangular matrix multiplication preserves uniform remainder estimates for the scoped
Euclidean `L2Operator` norm. -/
theorem matrixMul {Θ : Type u} {𝕜 : Type v} [RCLike 𝕜] {m n l : ℕ}
    {R : Θ → ℝ → Matrix (Fin m) (Fin n) 𝕜}
    {S : Θ → ℝ → Matrix (Fin n) (Fin l) 𝕜} {s : Set Θ} {C D p q : ℝ}
    (hR : IsUniformRemainderOn R s C p) (hS : IsUniformRemainderOn S s D q)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    IsUniformRemainderOn (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q) := by
  -- Transport both hypotheses to the product filter and intersect their eventual bounds.
  refine (isBigOWith_iff (fun θ ε ↦ R θ ε * S θ ε) s (C * D) (p + q)).mp ?_
  have hR' := (isBigOWith_iff R s C p).mpr hR
  have hS' := (isBigOWith_iff S s D q).mpr hS
  refine IsBigOWith.of_bound ?_
  filter_upwards [hR'.bound, hS'.bound] with z hzR hzS
  have hzR' : ‖R z.1 z.2‖ ≤ C * |z.2| ^ p := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) p)] using hzR
  have hzS' : ‖S z.1 z.2‖ ≤ D * |z.2| ^ q := by
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) q)] using hzS
  -- Submultiplicativity of the scoped operator norm leaves only the standard gauge normalization.
  calc
    ‖R z.1 z.2 * S z.1 z.2‖ ≤ ‖R z.1 z.2‖ * ‖S z.1 z.2‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (C * |z.2| ^ p) * (D * |z.2| ^ q) := by
      exact mul_le_mul hzR' hzS' (norm_nonneg _)
        (mul_nonneg hC (Real.rpow_nonneg (abs_nonneg z.2) p))
    _ = (C * D) * |z.2| ^ (p + q) := by
      rw [Real.rpow_add_of_nonneg (abs_nonneg z.2) hp hq]
      ring
    _ = (C * D) * ‖|z.2| ^ (p + q)‖ := by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg z.2) (p + q))]

end Asymptotics.IsUniformRemainderOn
