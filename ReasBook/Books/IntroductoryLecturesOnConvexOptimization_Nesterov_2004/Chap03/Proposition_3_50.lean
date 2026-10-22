/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Set
open scoped LevelMethodNotation

variable {α : Type u}

/- Proposition 3.50 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
* `LevelMethodHistory` in `Lemma_3_3_1`, the owner object for explicit real scalar sequences
  `(\hat f_k^*, f_k^*)`
* `LevelMethodHistory.gap`, `LevelMethodHistory.levelValue`, and
  `LevelMethodHistory.valueInterval` in `Lemma_3_3_1`, the derived owner API for
  `δ_k`, `ℓ_k(α)`, and `Δ_k`
* `bestFunctionValueUpTo` and `bestFunctionValueUpTo_antitone_step` in `Definition_3_55`, the
  chapter owner API for sampled prefix minima
* `SetConstrainedMinimizationProblem.optimalValue`,
  `SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image`,
  `SetConstrainedMinimizationProblem.optimalValue_eq_of_isMinOn`, and
  `SetConstrainedMinimizationProblem.optimalValue_le_of_mem_feasibleSet` in
  `Chap01/Definition_1_3_7`, the project owner API for exact constrained minima, faithfully
  valued in `EReal`

Best owner abstraction:
* source-facing: the exact constrained model problem at step `k` and the sampled prefix minimum
  `f_k^*`
* core/canonical: `SetConstrainedMinimizationProblem.optimalValue`, `LevelMethodHistory`, and
  `bestFunctionValueUpTo`
* bridge/view: the explicit real-history bridge
  `levelMethodHistoryFromApproximateValues hatf f xSeq`, together with its attained-minimum
  specialization `levelMethodHistoryFromApproximateValues (fun k ↦ model k (xHat k)) f xSeq`

Primitive data:
* the feasible set `Q`
* the model family `model`
* the objective `f`
* the sample sequence `xSeq`

Derived API:
* the canonical exact lower value
  `(levelMethodApproximateProblem Q model k).optimalValue`
* the explicit real-history bridge `levelMethodHistoryFromApproximateValues hatf f xSeq`
* the attained-minimum specialization
  `levelMethodHistoryFromApproximateValues (fun k ↦ model k (xHat k)) f xSeq`
* the stepwise monotonicity and gap comparisons for pointwise monotone models

Source/core/bridge triage:
* source-facing: Proposition 3.50 and the textbook chain
  `\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*`
* core/canonical: the `EReal` owner
  `(levelMethodApproximateProblem Q model k).optimalValue` together with
  `bestFunctionValueUpTo`
* bridge/view: explicit real lower-value histories
  `levelMethodHistoryFromApproximateValues hatf f xSeq` equipped with an exactness certificate to
  the canonical `EReal` owner; the attained-minimum specialization uses the same bridge with
  `hatf k = model k (xHat k)`

The refinement therefore moves the exact lower-value owner to
`SetConstrainedMinimizationProblem.optimalValue : EReal`. Real `LevelMethodHistory` objects are no
longer built unconditionally from the raw real infimum `⨅ x : Q, model k x`; instead they are
exposed only from explicit real lower-value data, together with bridge theorems relating those
data to the canonical `EReal` owner. Accordingly, the source-faithful stepwise order statement is
first proved on the canonical `EReal` owner, then transferred to arbitrary explicit real lower
values through an exactness certificate; the attained-minimum history is only a corollary.
-/

/-- The exact constrained model problem at step `k`, obtained by minimizing the model
`x ↦ model k x` over the feasible set `Q`. -/
abbrev levelMethodApproximateProblem
    (Q : Set α) (model : ℕ → α → ℝ) (k : ℕ) :
    SetConstrainedMinimizationProblem α :=
  .mk Q (model k)

/-- Explicit real scalar history attached to prescribed lower values `\hat f_k^*` and sampled
objective values. The mathematically faithful exact lower values remain the canonical `EReal`
owners `(levelMethodApproximateProblem Q model k).optimalValue`; this constructor is only the
real-history bridge used once those lower values have been supplied explicitly. -/
def levelMethodHistoryFromApproximateValues
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) :
    LevelMethodHistory where
  approximateOptimalValue := approximateOptimalValue
  optimalValue k := bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k

/-- The lower coordinate of `levelMethodHistoryFromApproximateValues` is the supplied real lower
value. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) (k : ℕ) :
    (levelMethodHistoryFromApproximateValues approximateOptimalValue f xSeq).approximateOptimalValue
        k =
      approximateOptimalValue k := rfl

/- The record value in `levelMethodHistoryFromApproximateValues` is the earlier chapter owner
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k` for the sampled minimum among `x₀, …, x_k`. -/
theorem levelMethodHistoryFromApproximateValues_optimalValue_eq
    (approximateOptimalValue : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α) (k : ℕ) :
    (levelMethodHistoryFromApproximateValues approximateOptimalValue f xSeq).optimalValue k =
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k := rfl

/-- If the supplied real lower values are exact, then the lower coordinate of
`levelMethodHistoryFromApproximateValues` agrees with the canonical `EReal` model minimum. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
    (Q : Set α) (model : ℕ → α → ℝ) (hatf : ℕ → ℝ) (f : α → ℝ) (xSeq : ℕ → α)
    (hhat :
      ∀ k : ℕ, ((hatf k : ℝ) : EReal) = (levelMethodApproximateProblem Q model k).optimalValue)
    (k : ℕ) :
    (((levelMethodHistoryFromApproximateValues hatf f xSeq).approximateOptimalValue k : ℝ) :
        EReal) =
      (levelMethodApproximateProblem Q model k).optimalValue := by
  simpa [levelMethodHistoryFromApproximateValues] using hhat k

/-- The attained-minimum specialization of `levelMethodHistoryFromApproximateValues` agrees with
the canonical `EReal` lower-value owner at each step, provided the chosen sequence `xHat` really
minimizes each model on `Q`. -/
theorem levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
    (Q : Set α) (model : ℕ → α → ℝ) (f : α → ℝ) (xSeq xHat : ℕ → α)
    (hxHat_mem : ∀ k : ℕ, xHat k ∈ Q)
    (hxHat_min : ∀ k : ℕ, IsMinOn (model k) Q (xHat k))
    (k : ℕ) :
    ((LevelMethodHistory.approximateOptimalValue
        (levelMethodHistoryFromApproximateValues (fun i ↦ model i (xHat i)) f xSeq)
        k : ℝ) : EReal) =
      (levelMethodApproximateProblem Q model k).optimalValue := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      ((levelMethodApproximateProblem Q model j).optimalValue_eq_of_isMinOn
        (hxHat_mem j)
        (hxHat_min j)).symm
  simpa using
    levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model (fun i ↦ model i (xHat i)) f xSeq hhat k

section

variable {Q : Set α} {model : ℕ → α → ℝ}

/-- Pointwise monotonicity of the model family makes the canonical exact lower values monotone. -/
theorem levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue := by
  simpa [levelMethodApproximateProblem] using
    (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      (levelMethodApproximateProblem Q model k)
      (levelMethodApproximateProblem Q model (k + 1))
      rfl
      (hmono k))

section History

variable (f : α → ℝ) (xSeq : ℕ → α)

/-- If every model is an underestimator on `Q`, then each canonical exact lower value is bounded
above by the best sampled objective value. This is stated first on the faithful `EReal` owner. -/
theorem levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k : EReal) := by
  obtain ⟨j, hj⟩ := bestFunctionValueUpTo_exists_eq (fun i ↦ f (xSeq i)) k
  have hsample :
      (levelMethodApproximateProblem Q model k).optimalValue ≤ (f (xSeq j) : EReal) := by
    have hmodel :
        (levelMethodApproximateProblem Q model k).optimalValue ≤ model k (xSeq j) :=
      (levelMethodApproximateProblem Q model k).optimalValue_le_of_mem_feasibleSet (hxSeq j)
    refine hmodel.trans ?_
    exact_mod_cast hunder k (xSeq j) (hxSeq j)
  have hj' :
      (f (xSeq j) : EReal) =
        (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k : EReal) := by
    exact_mod_cast hj
  exact hsample.trans_eq hj'

/-- Proposition 3.50, canonical form: the source-faithful stepwise order chain is stated on the
exact lower-value owner in `EReal`, so no extra attainment hypothesis is needed to express the
model lower values faithfully. -/
theorem levelMethodApproximateProblem_optimalValue_stepwiseBounds_of_monotoneUnderestimators
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    (levelMethodApproximateProblem Q model k).optimalValue ≤
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue ∧
      (levelMethodApproximateProblem Q model (k + 1)).optimalValue ≤
        (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) : EReal) ∧
      (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) : EReal) ≤
        bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k := by
  have hoptimal :
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
        bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k :=
    bestFunctionValueUpTo_antitone_step k
  refine ⟨?_, ?_, ?_⟩
  · exact levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono hmono k
  · exact
      levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
        f xSeq hxSeq hunder (k + 1)
  · exact_mod_cast hoptimal

section ExplicitHistory

variable (hatf : ℕ → ℝ)

local notation "history" =>
  (levelMethodHistoryFromApproximateValues hatf f xSeq : LevelMethodHistory)

/-- Under the exactness certificate `hhat`, pointwise monotonicity of the model family makes the
explicit real lower coordinates monotone. -/
theorem levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) := by
  have hmonoE :
      (levelMethodApproximateProblem Q model k).optimalValue ≤
        (levelMethodApproximateProblem Q model (k + 1)).optimalValue :=
    levelMethodApproximateProblem_optimalValue_mono_of_pointwiseModelMono hmono k
  rw [← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat k,
    ← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat (k + 1)] at hmonoE
  exact_mod_cast hmonoE

/-- Under the exactness certificate `hhat`, every model underestimator is bounded above by the
best sampled objective value in the explicit real history. -/
theorem
    levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    fhat(history, k) ≤ fstar(history, k) := by
  have hle :
      (levelMethodApproximateProblem Q model k).optimalValue ≤
        (fstar(history, k) : EReal) := by
    simpa [levelMethodHistoryFromApproximateValues] using
      (levelMethodApproximateProblem_optimalValue_le_bestFunctionValueUpTo_of_underestimator
        f xSeq hxSeq hunder k)
  rw [← levelMethodHistoryFromApproximateValues_approximateOptimalValue_eq_optimalValue
      Q model hatf f xSeq hhat k] at hle
  exact_mod_cast hle

/-- Proposition 3.50, source-facing real-history form: if the supplied lower values are exact,
then the textbook chain `\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*` holds for
`levelMethodHistoryFromApproximateValues hatf f xSeq`. -/
theorem levelMethodHistoryFromApproximateValues_stepwiseBounds_of_monotoneUnderestimators
    (hhat :
      ∀ j : ℕ, ((hatf j : ℝ) : EReal) = (levelMethodApproximateProblem Q model j).optimalValue)
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) ∧
      fhat(history, (k + 1)) ≤ fstar(history, (k + 1)) ∧
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
        f xSeq hatf hhat hmono k
  · exact
      levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
        f xSeq hatf hhat hxSeq hunder
        (k + 1)
  · simpa [levelMethodHistoryFromApproximateValues] using
      (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
          bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
        bestFunctionValueUpTo_antitone_step k)

end ExplicitHistory

section AttainedHistory

variable (xHat : ℕ → α)

local notation "history" =>
  levelMethodHistoryFromApproximateValues (fun i ↦ model i (xHat i)) f xSeq

/-- Companion bridge: under an explicit minimizing sequence `xHat`, pointwise monotonicity of the
model family makes the attained real lower coordinates monotone. -/
theorem attainedApproximateOptimalValue_mono_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_approximateOptimalValue_mono_of_pointwiseModelMono
      f xSeq (fun i ↦ model i (xHat i)) hhat hmono k

/-- Companion bridge: under an explicit minimizing sequence `xHat`, every model underestimator is
bounded above by the best sampled objective value in the attained real history. -/
theorem attainedApproximateOptimalValue_le_optimalValue_of_underestimator
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (k : ℕ) :
    fhat(history, k) ≤ fstar(history, k) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_fhat_le_fstar_of_underestimator
      f xSeq (fun i ↦ model i (xHat i)) hhat hxSeq hunder
      k

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the interval inclusion
`Δ_{k+1} ⊆ Δ_k` follows from pointwise monotonicity of the models. The underestimator hypothesis
from the textbook is redundant for this conclusion. -/
theorem attainedValueInterval_subset_step_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    Δ[history]((k + 1)) ⊆ Δ[history](k) := by
  intro t ht
  rw [LevelMethodHistory.mem_valueInterval_iff] at ht ⊢
  refine ⟨?_, ?_⟩
  · exact le_trans
      (attainedApproximateOptimalValue_mono_of_pointwiseModelMono
        f xSeq xHat hxHat_mem hxHat_min hmono k)
      ht.1
  · exact le_trans ht.2 <|
      by
        simpa using
          (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
              bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
            bestFunctionValueUpTo_antitone_step k)

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the level-method gap
`δ_k = f_k^* - \hat f_k^*` decreases from step `k` to step `k + 1` under pointwise monotone
models. The underestimator hypothesis is redundant for this conclusion. -/
theorem attainedGap_antitone_step_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    δ[history]((k + 1)) ≤ δ[history](k) := by
  have hoptimal :
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
    simpa using
      (show bestFunctionValueUpTo (fun i ↦ f (xSeq i)) (k + 1) ≤
          bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k from
        bestFunctionValueUpTo_antitone_step k)
  rw [LevelMethodHistory.gap_eq_sub, LevelMethodHistory.gap_eq_sub]
  linarith [attainedApproximateOptimalValue_mono_of_pointwiseModelMono
    f xSeq xHat hxHat_mem hxHat_min hmono k, hoptimal]

/-- Companion bridge: under an explicit minimizing sequence `xHat`, pointwise monotonicity of the
models makes the attained-history intervals nested downward and the attained-history gaps
nonincreasing. -/
theorem attainedLevelMethodValueInterval_subset_and_gap_antitone_of_pointwiseModelMono
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    Δ[history]((k + 1)) ⊆ Δ[history](k) ∧
      δ[history]((k + 1)) ≤ δ[history](k) := by
  exact ⟨attainedValueInterval_subset_step_of_pointwiseModelMono
      f xSeq xHat hxHat_mem hxHat_min hmono k,
    attainedGap_antitone_step_of_pointwiseModelMono
      f xSeq xHat hxHat_mem hxHat_min hmono k⟩

/-- Companion bridge: under an explicit minimizing sequence `xHat`, the textbook real chain
`\hat f_k^* ≤ \hat f_{k+1}^* ≤ f_{k+1}^* ≤ f_k^*` follows from the canonical `EReal` Proposition
3.50 theorem. -/
theorem attainedLevelMethodStepwiseBounds_of_monotoneUnderestimators
    (hxHat_mem : ∀ j : ℕ, xHat j ∈ Q)
    (hxHat_min : ∀ j : ℕ, IsMinOn (model j) Q (xHat j))
    (hxSeq : ∀ k : ℕ, xSeq k ∈ Q)
    (hunder : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ f x)
    (hmono : ∀ k : ℕ, ∀ x ∈ Q, model k x ≤ model (k + 1) x)
    (k : ℕ) :
    fhat(history, k) ≤ fhat(history, (k + 1)) ∧
      fhat(history, (k + 1)) ≤ fstar(history, (k + 1)) ∧
      fstar(history, (k + 1)) ≤ fstar(history, k) := by
  have hhat :
      ∀ j : ℕ,
        (((fun i ↦ model i (xHat i)) j : ℝ) : EReal) =
          (levelMethodApproximateProblem Q model j).optimalValue := fun j ↦
      levelMethodHistoryFromAttainedApproximateValues_approximateOptimalValue_eq_optimalValue
        Q model f xSeq xHat hxHat_mem hxHat_min j
  simpa using
    levelMethodHistoryFromApproximateValues_stepwiseBounds_of_monotoneUnderestimators
      f xSeq (fun i ↦ model i (xHat i)) hhat hxSeq hunder hmono k

end AttainedHistory

end History

end
