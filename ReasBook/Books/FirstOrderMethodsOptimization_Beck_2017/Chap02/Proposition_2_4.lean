/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Proposition_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Proof sketch: specialize `support_function_eq_indicatorFunction_polarCone` to the nonnegative
-- orthant `Set.Ici (0 : Fin n → ℝ)`. Under the Euclidean identification
-- `dotProductEquiv ℝ (Fin n) : ℝ^n ≃ₗ (ℝ^n)*`, membership in the polar cone is exactly
-- coordinatewise nonpositivity, so the indicator becomes the one of the Euclidean-dual image of
-- `Set.Iic 0`.
private theorem polar_cone_nonnegative_orthant_eq_image_nonpositive_orthant (n : ℕ) :
    polar_cone (Set.Ici (0 : Fin n → ℝ)) =
      dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ) := by
  ext y
  constructor
  · intro hy
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm y, ?_, by simp⟩
    intro i
    have hyi : y (Pi.single i (1 : ℝ)) ≤ 0 :=
      (mem_polar_cone _ _).mp hy (Pi.single i 1) (by simp)
    simpa [dotProductEquiv] using hyi
  · rintro ⟨v, hv, rfl⟩
    change dotProductEquiv ℝ (Fin n) v ∈ polar_cone (Set.Ici (0 : Fin n → ℝ))
    rw [mem_polar_cone]
    intro x hx
    simpa [dotProductEquiv, zero_dotProduct] using
      dotProduct_le_dotProduct_of_nonneg_right hv hx

/-- Proposition 2.4: in `ℝ^n`, under the Euclidean identification of the dual with `ℝ^n`, the
support function of the nonnegative orthant is the indicator function of the nonpositive orthant. -/
theorem support_function_nonnegative_orthant_eq_indicator_nonpositive_dual_orthant
    (n : ℕ) :
    support_function (Set.Ici (0 : Fin n → ℝ)) =
      δ_(dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ)) := by
  calc
    support_function (Set.Ici (0 : Fin n → ℝ))
        = δ_(polar_cone (Set.Ici (0 : Fin n → ℝ))) :=
          support_function_eq_indicatorFunction_polarCone (Set.Ici (0 : Fin n → ℝ))
            (by
              rw [isCone_iff_smul_mem]
              intro a ha x hx i
              simpa using mul_nonneg ha (hx i))
            (by simp)
    _ = δ_(dotProductEquiv ℝ (Fin n) '' Set.Iic (0 : Fin n → ℝ)) := by
          congr 1
          simpa using polar_cone_nonnegative_orthant_eq_image_nonpositive_orthant n
