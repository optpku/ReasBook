/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Remark_6_7

noncomputable section

open WithLp (toLp)
open scoped Pointwise

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Example 6.9 is `source-facing`: it computes the proximal map of the finite-product
logarithmic barrier. Domain sampling points to the existing owner abstractions
the Chapter 4 owner `negative_log_barrier`, the finite-product owner `separableSum` from
Theorem 6.6, and the singleton bridge
`prox_separableSum_eq_singleton_iff_coordinatewise` from Remark 6.7. The refined file therefore
keeps only the vector formula on the canonical finite-index owner surface `EuclideanSpace ℝ ι`,
whose specialization to `ι = Fin n` is the textbook `ℝ^n`, and reuses those owners directly
instead of duplicating a scalar barrier wrapper. -/

-- Proof sketch: apply the singleton bridge for separable proximal operators from Remark 6.7 to
-- the constant family given by the positive-ray scaling of `negative_log_barrier`. The no-`⊥`
-- side condition follows because `negative_log_barrier` never takes the value `⊥`, and positive
-- scalar multiplication preserves `⊤`. The coordinatewise singleton
-- formula is exactly Lemma 6.5 specialized with `0 < lam`.
/-- Example 6.9: for `λ > 0`, the proximal mapping of the coordinatewise logarithmic barrier on a
finite positive orthant is the singleton vector whose `j`-th coordinate is
`(x_j + √(x_j^2 + 4 λ)) / 2`. For `ι = Fin n`, this is the textbook formula on `ℝ^n`. -/
theorem prox_log_barrier_penalty_eq_singleton {lam : ℝ} (hlam : 0 < lam)
    (x : E) :
    prox[PiLp.separableSum (fun _ ↦ (lam : EReal) • negative_log_barrier)] x =
      {toLp 2 (fun j ↦ (x j + Real.sqrt (x j ^ 2 + 4 * lam)) / 2)} := by
  have hlamE : 0 < (lam : EReal) := by
    exact_mod_cast hlam
  have hproper :
      ∀ _ : ι, IsProperExtendedRealFunction ((lam : EReal) • negative_log_barrier) := by
    intro _
    refine ⟨?_, ?_⟩
    · intro t
      by_cases ht : 0 < t
      · simpa [negative_log_barrier, ht, Pi.smul_apply, smul_eq_mul] using
          EReal.coe_ne_bot (lam * (-Real.log t))
      · simp [negative_log_barrier, ht, Pi.smul_apply, smul_eq_mul,
          EReal.mul_top_of_pos hlamE]
    · refine ⟨1, ?_⟩
      rw [mem_effective_domain]
      simp [negative_log_barrier, Pi.smul_apply, smul_eq_mul, ← EReal.coe_mul]
  refine
    (prox_separableSum_eq_singleton_iff_coordinatewise
      (fun _ ↦ (lam : EReal) • negative_log_barrier)
      hproper
      x
      (toLp 2 (fun j ↦ (x j + Real.sqrt (x j ^ 2 + 4 * lam)) / 2))).2 ?_
  intro j
  simpa using prox_scalar_log_barrier_penalty_eq_singleton lam hlam (x j)

end
