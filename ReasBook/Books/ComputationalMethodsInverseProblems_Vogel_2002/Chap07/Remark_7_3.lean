/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_1

public section

/- Remark 7.3. This remark is qualitative and partly numerical: even when `upre`
and the predictive-risk objective have the same expected value, a fixed noise
realization need not give the same pointwise values or the same minimizers. The
text further says that the minimizers should be close under small variability and
non-flat minima, and that predictive-risk minimization should correlate with small
estimation error, but those claims are only heuristic here and no precise owner
for minimizer closeness or estimation-error comparison is introduced in the
current Chapter 7 API.

Accordingly, this item records the existing formal anchors used by the
remark together with the exact pointwise UPRE objective and minimizer surface
already available in the current Chapter 7 API. -/

universe u w

section

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {τ : Type w}

/-- Remark 7.3 companion. Evaluating `upre` at a fixed parameter gives the exact
pointwise UPRE objective used in the qualitative comparison from the remark. -/
theorem upre_eq_predictiveRisk_regularizedResidual_add_trace
    (Afamily : τ → Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) (a : τ) :
    upre Afamily σ d a =
      predictiveRisk (regularizedResidual (Afamily a) d) +
        (2 * σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Afamily a) - σ ^ 2 := by
  rw [upre_eq_upreValue, upreValue_def]

/-- Remark 7.3 companion. The available formal notion of a UPRE-selected
parameter is minimization of the exact pointwise UPRE objective on `Set.univ`. -/
theorem IsUPREParameter_iff_isMinOn_upreFormula
    (Afamily : τ → Matrix n n ℝ) (σ : ℝ) (d : EuclideanSpace ℝ n) (a : τ) :
    IsUPREParameter Afamily σ d a ↔
      IsMinOn
        (fun b ↦
          predictiveRisk (regularizedResidual (Afamily b) d) +
            (2 * σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Afamily b) - σ ^ 2)
        Set.univ a := by
  rw [IsUPREParameter_iff]
  let F : τ → ℝ := fun b ↦
    predictiveRisk (regularizedResidual (Afamily b) d) +
      (2 * σ ^ 2 / (Fintype.card n : ℝ)) * Matrix.trace (Afamily b) - σ ^ 2
  have hF : upre Afamily σ d = F := by
    funext b
    exact upre_eq_predictiveRisk_regularizedResidual_add_trace Afamily σ d b
  constructor <;> intro h <;> simpa [hF, F] using h

end

#check upre
#check upreValue
#check predictiveRisk
#check IsUPREParameter
#check IsMinOn
