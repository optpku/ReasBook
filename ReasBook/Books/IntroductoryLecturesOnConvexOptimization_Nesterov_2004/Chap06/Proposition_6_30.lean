/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped StandardSimplex

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section

variable (m : ℕ+)

local notation "S" => EuclideanSpace ℝ (Fin (m : ℕ))

/- Proposition 6.30 lies in the finite simplex / entropy-smoothing specialization domain.

Sampled owner declarations:
* `entropyRegularizedSimplexObjective` in `Chap06/Lemma_6_4`, the canonical entropy-regularized
  simplex objective;
* `entropySimplexSoftmax` and `entropySimplexSoftmax_apply` in `Chap06/Lemma_6_4`, the canonical
  softmax maximizer and its coordinate formula;
* `entropyRegularizedSimplexObjective_isMaxOn_iff` in `Chap06/Lemma_6_4`, the canonical owner
  theorem characterizing maximizers of the entropy-regularized simplex objective.

Best owner abstraction:
* source-facing: the entropy-regularized affine maximization problem on `Δ[m]`;
* core/canonical: `entropyRegularizedSimplexObjective m μ s`, `entropySimplexSoftmax m μ s`, and
  `entropyRegularizedSimplexObjective_isMaxOn_iff`;
* bridge/view: the affine score vector `s_j = f_j + ⟪g_j, xBar - x_j⟫`.

Primitive data:
* the positive smoothing parameter `μ₂`;
* the affine-score data `xBar`, `f`, `g`, and `points`.

Derived API:
* the source-facing affine score vector in `EuclideanSpace ℝ (Fin m)`;
* its coordinate evaluation lemma;
* the canonical softmax point in `Δ[m]`;
* the source proposition's maximality and uniqueness statement, obtained from the owner theorem
  `entropyRegularizedSimplexObjective_isMaxOn_iff`.

Source/core/bridge triage:
* source-facing: Proposition 6.30's unique-maximizer statement for the affine entropy-smoothed
  simplex problem;
* core/canonical: `entropyRegularizedSimplexObjective_isMaxOn_iff`;
* bridge/view: the affine score specialization below.

The built Chapter 6 owner API already characterizes entropy-regularized simplex maximizers via
`entropyRegularizedSimplexObjective_isMaxOn_iff`. This file therefore adds only the source-facing
affine score specialization and then states Proposition 6.30 directly in terms of that canonical
owner, instead of introducing a parallel packaged maximizer notion.
-/

/-- The affine score vector with coordinates `f_j + ⟪g_j, xBar - x_j⟫`. The textbook
`ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def entropyRegularizedAffineScores (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) : S :=
  (EuclideanSpace.equiv (Fin (m : ℕ)) ℝ).symm fun j ↦
    f j + inner ℝ (g j) (xBar - points j)

/-- Evaluating `entropyRegularizedAffineScores` recovers the coordinate formula
`f_j + ⟪g_j, xBar - x_j⟫`. -/
-- Proof sketch: unfold `entropyRegularizedAffineScores` and evaluate the coordinate `j` through
-- `EuclideanSpace.equiv`.
@[simp] theorem entropyRegularizedAffineScores_apply (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (j : Fin (m : ℕ)) :
    entropyRegularizedAffineScores m xBar f g points j =
      f j + inner ℝ (g j) (xBar - points j) := by
  -- Evaluate the packaged Euclidean vector at the coordinate `j`.
  simp [entropyRegularizedAffineScores]

/-- Helper for Proposition 6.30: evaluating the canonical entropy-regularized simplex owner at the
affine score vector yields the affine objective without the additive constant `μ₂ log m`. -/
theorem entropyRegularizedAffineSimplexObjective_apply
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    entropyRegularizedSimplexObjective m ⟨μ₂, hμ₂⟩
      (entropyRegularizedAffineScores m xBar f g points) u =
        (∑ j : Fin (m : ℕ), u j * (f j + inner ℝ (g j) (xBar - points j))) -
          μ₂ * ∑ j : Fin (m : ℕ), u j * Real.log (u j) := by
  -- Unfold the owner objective and then simplify the affine score coordinates.
  simp [entropyRegularizedSimplexObjective_apply, entropyRegularizedAffineScores]

/-- Helper for Proposition 6.30: the affine entropy-smoothed simplex objective is maximized
exactly at the canonical softmax point associated to the affine score vector. -/
theorem entropyRegularizedAffineSimplexObjective_isMaxOn_iff
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) (u : Δ[m]) :
    IsMaxOn
        (fun v : Δ[m] ↦
          (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
            μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
        Set.univ u ↔
      u = entropySimplexSoftmax m ⟨μ₂, hμ₂⟩ (entropyRegularizedAffineScores m xBar f g points) := by
  let μ : {μ : ℝ // 0 < μ} := ⟨μ₂, hμ₂⟩
  let s : S := entropyRegularizedAffineScores m xBar f g points
  have hshift :
      IsMaxOn (fun v : Δ[m] ↦ entropyRegularizedSimplexObjective m μ s v - μ₂ * Real.log (m : ℝ))
        Set.univ u ↔
        IsMaxOn (entropyRegularizedSimplexObjective m μ s) Set.univ u := by
    constructor
    · intro h
      -- Add back the dropped constant to recover the canonical owner objective.
      simpa [sub_eq_add_neg] using
        h.add (isMaxOn_const : IsMaxOn (fun _ : Δ[m] ↦ μ₂ * Real.log (m : ℝ)) Set.univ u)
    · intro h
      -- Subtract the same constant to return to the source-facing objective.
      simpa using
        h.sub (isMinOn_const : IsMinOn (fun _ : Δ[m] ↦ μ₂ * Real.log (m : ℝ)) Set.univ u)
  have hsource :
      (fun v : Δ[m] ↦
        (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
          μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j))) =
        fun v : Δ[m] ↦ entropyRegularizedSimplexObjective m μ s v - μ₂ * Real.log (m : ℝ) := by
    -- Identify the source objective with the owner objective up to the additive constant.
    funext v
    rw [entropyRegularizedAffineSimplexObjective_apply]
    ring
  -- Transfer the owner theorem across the explicit source/objective identification.
  rw [hsource, hshift]
  simpa [μ, s] using entropyRegularizedSimplexObjective_isMaxOn_iff m μ s u

-- Proof sketch: apply the owner theorem
-- `entropyRegularizedSimplexObjective_isMaxOn_iff` to the affine score vector
-- `entropyRegularizedAffineScores m xBar f g points`. This identifies the canonical maximizer as
-- the corresponding softmax point, and the `iff` gives uniqueness of any other maximizer.
/-- Proposition 6.30 [Chapter6_1.json:99]: for the affine scores
`s_j = f_j + ⟪g_j, xBar - x_j⟫` and every `μ₂ > 0`, the problem
`max_{u ∈ Δ_m} {∑_j u_j s_j - μ₂ (log m + ∑_j u_j log u_j)}` is maximized by the canonical
softmax point, and every simplex maximizer equals that point. In particular, the maximizer is
unique and is given componentwise by the normalized exponential formula from
`entropySimplexSoftmax_apply`. -/
theorem entropyRegularizedAffineSimplexObjective_hasUniqueMaximizer
    {μ₂ : ℝ} (hμ₂ : 0 < μ₂) (xBar : E) (f : Fin (m : ℕ) → ℝ)
    (g points : Fin (m : ℕ) → E) :
    IsMaxOn
        (fun v : Δ[m] ↦
          (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
            μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
        Set.univ
        (entropySimplexSoftmax m ⟨μ₂, hμ₂⟩
          (entropyRegularizedAffineScores m xBar f g points)) ∧
      ∀ u : Δ[m],
        IsMaxOn
            (fun v : Δ[m] ↦
              (∑ j : Fin (m : ℕ), v j * (f j + inner ℝ (g j) (xBar - points j))) -
                μ₂ * (Real.log (m : ℝ) + ∑ j : Fin (m : ℕ), v j * Real.log (v j)))
            Set.univ u →
          u = entropySimplexSoftmax m ⟨μ₂, hμ₂⟩
            (entropyRegularizedAffineScores m xBar f g points) := by
  constructor
  · -- The source-facing iff shows that the canonical softmax point is a maximizer.
    exact
      (entropyRegularizedAffineSimplexObjective_isMaxOn_iff m hμ₂ xBar f g points
        (entropySimplexSoftmax m ⟨μ₂, hμ₂⟩ (entropyRegularizedAffineScores m xBar f g points))).2
        rfl
  · intro u hu
    -- Any other maximizer must coincide with the same canonical softmax point.
    exact (entropyRegularizedAffineSimplexObjective_isMaxOn_iff m hμ₂ xBar f g points u).1 hu

end
