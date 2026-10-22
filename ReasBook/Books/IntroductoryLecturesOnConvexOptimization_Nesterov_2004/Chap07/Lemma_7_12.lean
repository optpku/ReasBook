/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_57
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [AddCommGroup U] [Module ℝ U]

/- Lemma 7.12 lies in the barrier-subgradient / saddle-representation / Jensen-averaging domain.

Mandatory domain-style sampling:
- `Finset.centerMass` in mathlib, the canonical owner for normalized finite weighted averages;
- `ConcaveOn.le_map_centerMass` and `ConvexOn.map_centerMass_le` in mathlib, the canonical Jensen
  inequalities for passing between averaged points and averaged values;
- `SaddlePointRepresentation` in `Definition_7_59`, the Chapter 7 owner of the saddle data
  `(f, Ψ)`;
- `maximalValueOn` in `Definition_7_56`, the Chapter 7 `EReal` owner for maximization over a
  feasible set;
- `barrierSubgradientWeightSum` and `barrierSubgradientMaximalGap` in `Definition_7_57`, the
  Chapter 7 owners for `S_k` and `ℓ_k⋆`.

Best owner abstraction:
- source-facing: the averaged duality-gap estimate of Lemma 7.12;
- core/canonical: `SaddlePointRepresentation`, `Finset.centerMass`, `maximalValueOn`,
  `barrierSubgradientWeightSum`, and `barrierSubgradientMaximalGap`;
- bridge/view: the textbook symbols `\bar x_k`, `\bar w_k`, and `η`, which here are only views of
  those owners, not separate public declarations.

Primitive data:
- the feasible set `P`, an ambient objective extension `f`, the saddle representation owner
  `representation`, and a minimizing branch `w`;
- the iterate family `x`, chosen subgradients, weights `λ`, and index `k`.

Derived API:
- the primal and dual averages as direct `Finset.centerMass` expressions;
- the dual value as direct use of `maximalValueOn`.

The previous file exposed raw parameters `f`, `Ψ`, and `w` even though Definition 7.59 already
introduced the chapter owner surface for the saddle data. This refinement keeps only the ambient
objective extension `f : E → ℝ` needed to state concavity on the feasible set `P ⊆ E`, moves the
saddle data itself to `SaddlePointRepresentation`, removes the redundant standalone convexity
hypothesis because `ConcaveOn ℝ P f` already contains that convexity, and removes the redundant
owner-level minimizer-selection hypothesis because this averaged-gap estimate uses `w` only
through the assumed model inequality and the resulting weighted averages.
-/

-- Proof sketch: for each iterate `x_i`, use the assumed linearization inequality
-- `Ψ(y, w(x_i)) - f(x_i) ≤ ⟪g_i, y - x_i⟫`, weight by `λ_i`, sum over `i = 0, …, k`,
-- and divide by `S_k`. Then use convexity of the slices `Ψ(y, ·)` to pass from the weighted
-- average of the values `Ψ(y, w(x_i))` to `Ψ(y, \bar w_k)`, identify the resulting supremum with
-- `η(\bar w_k)`, and finally apply concavity of `f` on `P` to bound the weighted average of the
-- primal values by `f(\bar x_k)`.
/-- Helper for Lemma 7.12: the center of mass of pointwise differences is the difference of the
corresponding centers of mass. -/
lemma centerMass_sub_eq_sub_centerMass
    {ι : Type*} (t : Finset ι) (lam a b : ι → ℝ) :
    t.centerMass lam (fun i ↦ a i - b i) = t.centerMass lam a - t.centerMass lam b := by
  -- Expand every center-of-mass term to the common normalized weighted sum.
  rw [Finset.centerMass, Finset.centerMass, Finset.centerMass]
  simp only [smul_eq_mul, mul_sub, Finset.sum_sub_distrib]

/-- Helper for Lemma 7.12: Jensen's inequalities move the saddle value at the averaged dual point
and the primal value at the averaged primal point to the centerMass of the pointwise gaps. -/
lemma saddle_average_sub_objective_le_centerMass_difference
    {P : Set E} {f : E → ℝ} {representation : SaddlePointRepresentation ↥P U} {w : P → U}
    (hf_concave : ConcaveOn ℝ P f)
    (hsaddle_convex : ∀ y : P, ConvexOn ℝ Set.univ (representation.saddleFunction y))
    (x : ℕ → P) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k)
    (y : P) :
    representation.saddleFunction y
        ((Finset.range (k + 1)).centerMass lam fun i ↦ w (x i)) -
        f ((Finset.range (k + 1)).centerMass lam fun i ↦ (x i : E)) ≤
      (Finset.range (k + 1)).centerMass lam
        (fun i ↦ representation.saddleFunction y (w (x i)) - f (x i : E)) := by
  let t : Finset ℕ := Finset.range (k + 1)
  -- Jensen on the convex saddle slice controls the saddle value at the averaged dual point.
  have hsaddle :
      representation.saddleFunction y (t.centerMass lam fun i ↦ w (x i)) ≤
        t.centerMass lam (fun i ↦ representation.saddleFunction y (w (x i))) := by
    exact (hsaddle_convex y).map_centerMass_le
      (fun i hi ↦ hlam_nonneg i (by simpa [t] using hi))
      (by simpa [t, barrierSubgradientWeightSum_def] using hlam_sum_pos)
      (fun i _ ↦ by simp)
  -- Jensen on the concave primal objective controls the value at the averaged primal point.
  have hobjective :
      t.centerMass lam (fun i ↦ f (x i : E)) ≤
        f (t.centerMass lam fun i ↦ (x i : E)) := by
    exact hf_concave.le_map_centerMass
      (fun i hi ↦ hlam_nonneg i (by simpa [t] using hi))
      (by simpa [t, barrierSubgradientWeightSum_def] using hlam_sum_pos)
      (fun i _ ↦ (x i).2)
  -- Combine the two Jensen bounds and rewrite the centerMass of differences.
  have hcompare :
      representation.saddleFunction y (t.centerMass lam fun i ↦ w (x i)) -
          f (t.centerMass lam fun i ↦ (x i : E)) ≤
        t.centerMass lam (fun i ↦ representation.saddleFunction y (w (x i))) -
          t.centerMass lam (fun i ↦ f (x i : E)) := by
    linarith
  simpa [t, centerMass_sub_eq_sub_centerMass] using hcompare

/-- Helper for Lemma 7.12: averaging the model inequalities yields the normalized gap-function
bound. -/
lemma centerMass_difference_le_gap_div
    {P : Set E} {f : E → ℝ} {representation : SaddlePointRepresentation ↥P U} {w : P → U}
    (hobjective_eq : ∀ y : P, representation y = f y)
    (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k)
    (hsubgradient_model :
      ∀ i ∈ Finset.range (k + 1), ∀ y : P,
        representation.saddleFunction y (w (x i)) - representation (x i) ≤
          inner ℝ (subgradient i) ((y : E) - (x i : E)))
    (y : P) :
    (Finset.range (k + 1)).centerMass lam
        (fun i ↦ representation.saddleFunction y (w (x i)) - f (x i : E)) ≤
      barrierSubgradientGapFunction x subgradient lam k y / barrierSubgradientWeightSum lam k := by
  let t : Finset ℕ := Finset.range (k + 1)
  -- Weight each pointwise model inequality by `λ_i` and sum over the finite prefix.
  have hsum :
      ∑ i ∈ t, lam i * (representation.saddleFunction y (w (x i)) - f (x i : E)) ≤
        ∑ i ∈ t, lam i * inner ℝ (subgradient i) ((y : E) - (x i : E)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hmodel_i :
        representation.saddleFunction y (w (x i)) - f (x i : E) ≤
          inner ℝ (subgradient i) ((y : E) - (x i : E)) := by
      simpa [hobjective_eq (x i)] using hsubgradient_model i (by simpa [t] using hi) y
    exact mul_le_mul_of_nonneg_left hmodel_i (hlam_nonneg i (by simpa [t] using hi))
  -- Divide by the positive weight sum to convert the weighted sum bound into a centerMass bound.
  have hcenter :
      t.centerMass lam (fun i ↦ representation.saddleFunction y (w (x i)) - f (x i : E)) ≤
        t.centerMass lam (fun i ↦ inner ℝ (subgradient i) ((y : E) - (x i : E))) := by
    simpa [t, Finset.centerMass, smul_eq_mul] using
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (le_of_lt hlam_sum_pos))
  -- The right-hand centerMass is exactly the normalized gap function.
  have hgap :
      t.centerMass lam (fun i ↦ inner ℝ (subgradient i) ((y : E) - (x i : E))) =
        barrierSubgradientGapFunction x subgradient lam k y /
          barrierSubgradientWeightSum lam k := by
    rw [Finset.centerMass, barrierSubgradientGapFunction_apply, barrierSubgradientWeightSum_def]
    simp only [t, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hgap] at hcenter
  exact hcenter

/-- Helper for Lemma 7.12: each normalized gap value is bounded by the normalized maximal gap. -/
lemma gap_div_coe_le_maximalGap_div
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k) (y : P) :
    (((barrierSubgradientGapFunction x subgradient lam k y /
        barrierSubgradientWeightSum lam k : ℝ) : EReal)) ≤
      barrierSubgradientMaximalGap x subgradient lam k / barrierSubgradientWeightSum lam k := by
  -- Compare the pointwise gap value to the defining supremum before dividing by the positive sum.
  rw [EReal.coe_div, barrierSubgradientMaximalGap_def]
  exact EReal.div_le_div_right_of_nonneg
    (by exact_mod_cast le_of_lt hlam_sum_pos)
    (le_sSup (Set.mem_range_self y))

/-- Lemma 7.12: with the canonical weighted averages
`\bar w_k = (1 / S_k) ∑_{i=0}^k λ_i w(x_i)` and
`\bar x_k = (1 / S_k) ∑_{i=0}^k λ_i x_i`, one has
`η(\bar w_k) - f(\bar x_k) ≤ (1 / S_k) ℓ_k^⋆`. -/
theorem barrierSubgradientAverageDualityGap_le_maximalGap
    {P : Set E} {f : E → ℝ} {representation : SaddlePointRepresentation ↥P U} {w : P → U}
    (hobjective_eq : ∀ y : P, representation y = f y)
    (hf_concave : ConcaveOn ℝ P f)
    (hsaddle_convex : ∀ y : P, ConvexOn ℝ Set.univ (representation.saddleFunction y))
    (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ)
    (hlam_nonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ lam i)
    (hlam_sum_pos : 0 < barrierSubgradientWeightSum lam k)
    (hsubgradient_model :
      ∀ i ∈ Finset.range (k + 1), ∀ y : P,
        representation.saddleFunction y (w (x i)) - representation (x i) ≤
          inner ℝ (subgradient i) ((y : E) - (x i : E))) :
    maximalValueOn (Set.univ : Set ↥P)
        (fun y ↦
          representation.saddleFunction y
            ((Finset.range (k + 1)).centerMass lam fun i ↦ w (x i))) -
        f ((Finset.range (k + 1)).centerMass lam fun i ↦ (x i : E)) ≤
      barrierSubgradientMaximalGap x subgradient lam k / barrierSubgradientWeightSum lam k := by
  let t : Finset ℕ := Finset.range (k + 1)
  let wbar : U := t.centerMass lam fun i ↦ w (x i)
  let xbar : E := t.centerMass lam fun i ↦ (x i : E)
  have hmain :
      maximalValueOn (Set.univ : Set ↥P) (fun y ↦ representation.saddleFunction y wbar) ≤
        barrierSubgradientMaximalGap x subgradient lam k / barrierSubgradientWeightSum lam k +
          f xbar := by
    rw [maximalValueOn_eq_sSup_image]
    refine sSup_le ?_
    rintro _ ⟨y, -, rfl⟩
    -- First control the averaged duality gap for this fixed feasible point `y`.
    have hfixed :
        representation.saddleFunction y wbar - f xbar ≤
          barrierSubgradientGapFunction x subgradient lam k y /
            barrierSubgradientWeightSum lam k := by
      exact
        (saddle_average_sub_objective_le_centerMass_difference
          hf_concave hsaddle_convex x lam k hlam_nonneg hlam_sum_pos y).trans
          (centerMass_difference_le_gap_div
            hobjective_eq x subgradient lam k hlam_nonneg hlam_sum_pos hsubgradient_model y)
    have hfixed_add :
        representation.saddleFunction y wbar ≤
          barrierSubgradientGapFunction x subgradient lam k y /
            barrierSubgradientWeightSum lam k + f xbar := by
      linarith
    have hfixed_ereal :
        ((representation.saddleFunction y wbar : ℝ) : EReal) ≤
          (((barrierSubgradientGapFunction x subgradient lam k y /
              barrierSubgradientWeightSum lam k : ℝ) : EReal)) + f xbar := by
      simpa [EReal.coe_add] using (EReal.coe_le_coe hfixed_add)
    -- Then replace the pointwise gap by the normalized maximal gap.
    have hgap_added :
        (((barrierSubgradientGapFunction x subgradient lam k y /
            barrierSubgradientWeightSum lam k : ℝ) : EReal)) + f xbar ≤
          barrierSubgradientMaximalGap x subgradient lam k /
              barrierSubgradientWeightSum lam k +
            f xbar := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (gap_div_coe_le_maximalGap_div x subgradient lam k hlam_sum_pos y)
          (f xbar)
    exact hfixed_ereal.trans hgap_added
  -- Recast the target subtraction bound as the corresponding upper bound after adding `f(x̄_k)`.
  exact
    (EReal.sub_le_iff_le_add
      (a := maximalValueOn (Set.univ : Set ↥P) (fun y ↦ representation.saddleFunction y wbar))
      (b := f xbar) (c := barrierSubgradientMaximalGap x subgradient lam k /
        barrierSubgradientWeightSum lam k) (by simp) (by simp)).2 <|
      by simpa [t, wbar, xbar, add_comm, add_left_comm, add_assoc] using hmain

end
