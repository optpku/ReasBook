/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_54
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_51

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Example 10.53 is `source-facing` in the Chapter 10 smoothing API. Domain sampling identifies:
- `H[μ]` from Definition 6.8 as the source-facing Huber owner;
- `moreau_envelope_real_is_smooth_approximation` from Theorem 10.51 as the core/canonical
  Moreau-envelope smoothing theorem for convex Lipschitz functions;
- `moreau_envelope_norm_penalty_toReal_eq_huber_function` from Example 6.54 as the bridge/view
  identifying the norm envelope with the Huber owner.

The primitive data are only the ambient norm and the existing Huber owner. The Euclidean
`ℝ^n` reading is a specialization of this intrinsic real inner-product-space statement, so the
main public theorem is stated at that owner level rather than through a separate Euclidean
bridge. -/
recall huber_function

-- Proof sketch: apply the general Moreau-envelope smooth-approximation theorem to `x ↦ ‖x‖`,
-- using `convexOn_univ_norm` and `lipschitzWith_one_norm`, then rewrite the resulting Moreau
-- envelope by the canonical Huber bridge `moreau_envelope_norm_penalty_toReal_eq_huber_function`.
/-- Example 10.53: for every `μ > 0`, the Huber function `H[μ]` is a `1 / μ`-smooth
approximation of the norm with parameters `(1, 1 / 2)`. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook statement on `ℝ^n`. -/
theorem norm_huber_is_smooth_approximation
    (μ : PosReal) :
    IsSmoothApproximation
      (fun x : E ↦ ‖x‖)
      (H[μ] : E → ℝ)
      1
      ((1 : PosReal) / (1 + 1))
      μ := by
  have hMoreau :
      EReal.toReal ∘ M[μ, norm_penalty 1] = (H[μ] : E → ℝ) :=
    moreau_envelope_norm_penalty_toReal_eq_huber_function μ
  have hH :
      (fun x : E ↦ (M[μ, (fun y : E ↦ ‖y‖).toEReal] x).toReal) = (H[μ] : E → ℝ) := by
    funext x
    simpa [Function.comp, norm_penalty] using congrFun hMoreau x
  have happrox :
      IsSmoothApproximationNonneg
        (fun x : E ↦ ‖x‖)
        (fun x ↦ (M[μ, (fun y : E ↦ ‖y‖).toEReal] x).toReal)
        1
        ((1 : NNReal) / 2)
        μ := by
    have hβ : (1 : NNReal) ^ (2 : ℕ) / 2 = (1 : NNReal) / 2 := by
      norm_num
    simpa only [hβ] using
      moreau_envelope_real_is_smooth_approximation
        (fun x : E ↦ ‖x‖)
        convexOn_univ_norm
        (1 : NNReal)
        (by
          change LipschitzWith 1 norm
          simpa using (lipschitzWith_one_norm : LipschitzWith 1 (norm : E → ℝ)))
        μ
  have hhalf :
      ((((1 : NNReal) / 2 : NNReal) : ℝ)) = (((((1 : PosReal) / (1 + 1)) : PosReal) : ℝ)) := by
    norm_num [PosReal.coe_one, PosReal.coe_add, PosReal.coe_div]
  refine
    { convex := ?_
      lower_le := ?_
      upper_le := ?_
      smooth := ?_ }
  · simpa only [hH] using happrox.convex
  · intro x
    calc
      H[μ] x = (M[μ, (fun y : E ↦ ‖y‖).toEReal] x).toReal := (congrFun hH x).symm
      _ ≤ ‖x‖ := happrox.lower_le x
  · intro x
    calc
      ‖x‖ ≤ (M[μ, (fun y : E ↦ ‖y‖).toEReal] x).toReal + ((((1 : NNReal) / 2 : NNReal) : ℝ) * (μ : ℝ)) :=
        happrox.upper_le x
      _ = H[μ] x + ((((1 : NNReal) / 2 : NNReal) : ℝ) * (μ : ℝ)) := by
        rw [congrFun hH x]
      _ = H[μ] x + ((((1 : PosReal) / (1 + 1) : PosReal) : ℝ) * (μ : ℝ)) := by
        rw [hhalf]
  · simpa only [hH] using happrox.smooth

end
