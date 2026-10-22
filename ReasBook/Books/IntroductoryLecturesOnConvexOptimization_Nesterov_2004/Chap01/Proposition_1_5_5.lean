/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {k p : ℕ}

namespace taylorCoeffLipschitzClass

/-- Proposition 1.5.5: if two functions belong to the textbook class `C^{k,p}_L(Q)`, written in
this file as `𝒞^{k,p}_{L}(Q)`, then any linear combination remains in the same class, with
Lipschitz constant `‖α₁‖₊ * L₁ + ‖α₂‖₊ * L₂`. -/
-- Proof sketch: extract the source-facing class data, transport the underlying Taylor witnesses
-- through scalar multiplication and addition, and combine the resulting Lipschitz bounds on the
-- `p`-th coefficient.
theorem smul_add
    {Q : Set E}
    {L₁ L₂ : NNReal}
    {f₁ f₂ : E → ℝ}
    {α₁ α₂ : ℝ}
    (hf₁ : f₁ ∈ 𝒞^{k,p}_{L₁}(Q))
    (hf₂ : f₂ ∈ 𝒞^{k,p}_{L₂}(Q)) :
    α₁ • f₁ + α₂ • f₂ ∈ 𝒞^{k,p}_{(‖α₁‖₊ * L₁ + ‖α₂‖₊ * L₂)}(Q) := by
  rcases exists_taylorSeries hf₁ with ⟨P₁, hP₁, hLip₁⟩
  rcases exists_taylorSeries hf₂ with ⟨P₂, hP₂, hLip₂⟩
  refine ⟨order_le hf₁, ⟨α₁ • P₁ + α₂ • P₂, ?_, ?_⟩⟩
  · simpa [Pi.smul_apply, Pi.add_apply] using
      (hP₁.continuousLinearMap_comp (ContinuousLinearMap.lsmul ℝ ℝ α₁)).add
        (hP₂.continuousLinearMap_comp (ContinuousLinearMap.lsmul ℝ ℝ α₂))
  · have hLip₁' : LipschitzOnWith (‖α₁‖₊ * L₁) (fun x ↦ α₁ • P₁ x p) Q := by
      simpa using (lipschitzWith_smul α₁).comp_lipschitzOnWith hLip₁
    have hLip₂' : LipschitzOnWith (‖α₂‖₊ * L₂) (fun x ↦ α₂ • P₂ x p) Q := by
      simpa using (lipschitzWith_smul α₂).comp_lipschitzOnWith hLip₂
    simpa [Pi.smul_apply, Pi.add_apply] using hLip₁'.add hLip₂'

end taylorCoeffLipschitzClass

end
