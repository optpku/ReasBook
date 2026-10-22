/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_9

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Theorem 7.4 lies in the chapter's relative-accuracy / Euclidean direct-scheme domain.

Sampled owner-style declarations:
- `aPrioriRadiusEstimate` in `Definition_7_9.lean`, the Chapter 7 owner for the scalar radius
  parameter used by the lower-level scheme;
- `ConvexOn ℝ Set.univ f`, the chapter's standard whole-space convexity surface on `ℝⁿ`;
- `IsRelativeAccuracy` in `Definition_7_1.lean`, the chapter owner for the stronger two-sided
  relative-value notion;
- `relativeScaleSubgradientApproximationStep` in `Algorithm_7_2.lean`, which uses the same
  lower-level scheme surface `ℕ → ℝ → Eₙ`;
- `subgradient_approximation_scheme_value_le_one_add_delta_mul_optimal_value` in
  `Theorem_7_2.lean`, the sibling one-shot relative-value conversion theorem.

Best owner abstraction:
- source-facing: Theorem 7.4's conversion of the stagewise direct-structure estimate on `ℝⁿ` into
  a one-shot relative-value bound at a floor-chosen index;
- core/canonical: a lower-level scheme `S : ℕ → ℝ → Eₙ` evaluated at the Chapter 7 radius owner
  `aPrioriRadiusEstimate f γ0 x0`;
- bridge/view: the specific stage index `⌊2 / (α² δ)⌋`, with `IsRelativeAccuracy` remaining the
  ambient chapter owner for the stronger two-sided notion.

Primitive data:
- the convex objective `f : Eₙ → ℝ`;
- the direct-structure scheme `S : ℕ → ℝ → Eₙ`, the base point `x0`, and the scalars
  `α`, `γ0`, `δ`, and `fStar`;
- the stagewise estimate for `f (S k (aPrioriRadiusEstimate f γ0 x0))`;
- the source fact that `fStar` is the infimum value of `f`.

Derived API:
- the floor-chosen stage `⌊2 / (α² δ)⌋`;
- the final upper bound `f (S_N (aPrioriRadiusEstimate f γ0 x0)) ≤ (1 + δ) fStar`.

Source/core/bridge triage:
- source-facing: the theorem's upper-bound conclusion at the chosen stage;
- core/canonical: `aPrioriRadiusEstimate` and the lower-level scheme surface `ℕ → ℝ → Eₙ`;
- bridge/view: the arithmetic passage from the stagewise coefficient `2 / (α² (k + 1))` to the
  target coefficient `δ`.

The previous version over-generalized the labeled theorem to an arbitrary ambient type and omitted
the source convexity hypothesis. This repair restores the Chapter 7 Euclidean owner surface
`Eₙ = EuclideanSpace ℝ (Fin n)` together with the whole-space convexity assumption used in nearby
direct-structure items. The source lower-bound premise `IsGLB (Set.range f) fStar` is the only
optimal-value input: together with the stagewise estimate, it is what forces the nonnegativity
needed by the one-sided relative-value conversion.
-/

-- Semantic recall via `lean_leansearch` only surfaced generic owners such as `ConvexOn` and
-- `IsMinOn.isGLB`, so the local Chapter 7 direct-scheme surface remains the correct public API.

/-- Helper for Theorem 7.4: the floor-chosen stage is strictly below its successor bound. -/
lemma chosenDirectStructureFloorLtSucc (α δ : ℝ) :
    (2 / (α ^ (2 : ℕ) * δ) : ℝ) <
      (Nat.floor (2 / (α ^ (2 : ℕ) * δ)) : ℝ) + 1 := by
  -- The floor comparison is the bridge from the chosen integer stage to the real bound on `N + 1`.
  simpa using Nat.lt_floor_add_one (2 / (α ^ (2 : ℕ) * δ))

/-- Helper for Theorem 7.4: the floor-chosen stage makes the stagewise coefficient at most `δ`. -/
lemma chosenDirectStructureCoefficientLeDelta
    (α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ) :
    2 / (α ^ (2 : ℕ) * ((Nat.floor (2 / (α ^ (2 : ℕ) * δ)) : ℕ) + 1 : ℝ)) ≤ δ := by
  let N : ℕ := Nat.floor (2 / (α ^ (2 : ℕ) * δ))
  have hFloor : (2 / (α ^ (2 : ℕ) * δ) : ℝ) < (N : ℝ) + 1 := by
    -- The floor inequality identifies the lower bound on `N + 1` used in the source proof.
    simpa [N] using chosenDirectStructureFloorLtSucc α δ
  have hDenom_pos : 0 < α ^ (2 : ℕ) * δ := by
    positivity
  have hCoeffDenom_pos : 0 < α ^ (2 : ℕ) * ((N : ℝ) + 1) := by
    positivity
  have hMul : 2 < ((N : ℝ) + 1) * (α ^ (2 : ℕ) * δ) := by
    -- Multiplying by the positive denominator turns the floor estimate into the product bound.
    exact (div_lt_iff₀ hDenom_pos).1 hFloor
  have hMul' : 2 < δ * (α ^ (2 : ℕ) * ((N : ℝ) + 1)) := by
    -- Reordering the product exposes the exact denominator used in the coefficient.
    calc
      2 < ((N : ℝ) + 1) * (α ^ (2 : ℕ) * δ) := hMul
      _ = δ * (α ^ (2 : ℕ) * ((N : ℝ) + 1)) := by ring
  have hMul'' : 2 < δ * (α ^ (2 : ℕ) * ((N : ℝ) + 1)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hMul'
  have hMain : 2 / (α ^ (2 : ℕ) * ((N : ℝ) + 1)) < δ := by
    -- Dividing by the positive coefficient denominator gives the desired scalar bound.
    exact (div_lt_iff₀ hCoeffDenom_pos).2 hMul''
  simpa [N] using hMain.le

/-- Helper for Theorem 7.4: an upper bound above the optimal value forces `fStar` to be
nonnegative. -/
lemma optimalValueNonneg_ofIsGLBUpperBound
    {X : Type*} (f : X → ℝ) (x : X) (fStar c : ℝ)
    (hOptimalValue : IsGLB (Set.range f) fStar)
    (hc : 0 < c)
    (hx : f x ≤ fStar + c * fStar) :
    0 ≤ fStar := by
  have hx_mem_range : f x ∈ Set.range f := by
    -- The chosen point contributes a concrete function value to the range.
    exact ⟨x, rfl⟩
  have hLower : fStar ≤ f x := by
    -- The `IsGLB` hypothesis makes `fStar` a lower bound for every value in the range.
    exact hOptimalValue.1 hx_mem_range
  have hMul_nonneg : 0 ≤ c * fStar := by
    -- Comparing the lower and upper bounds isolates the error term.
    linarith
  -- Positivity of the coefficient transfers nonnegativity back to `fStar`.
  have hMul_nonneg' : 0 ≤ fStar * c := by
    simpa [mul_comm] using hMul_nonneg
  exact nonneg_of_mul_nonneg_left hMul_nonneg' hc

-- Proof sketch: evaluate the assumed stagewise estimate at
-- `N = Nat.floor (2 / (α ^ (2 : ℕ) * δ))`. The floor inequality implies
-- `2 / (α ^ (2 : ℕ) * (N + 1 : ℝ)) ≤ δ`, so the additive error term is at most `δ * fStar`.
-- The infimum witness records that `fStar` is the source optimal value; comparing it with the
-- stagewise estimate at the chosen iterate supplies the nonnegativity needed for the scalar step.
/-- Theorem 7.4 [Chapter7_1.json:27]: if `f : ℝⁿ → ℝ` is convex, `α > 0`, `γ0 > 0`,
`0 < δ < 1`, `fStar` is the infimum value of `f`, and every
direct-structure iterate at radius
`aPrioriRadiusEstimate f γ0 x0 = (1 / γ₀(F)) f(x₀)` satisfies the estimate
`f (S_k ((1 / γ₀(F)) f(x₀))) ≤ f* + (2 / (α(F)^2 (k + 1))) * f*`, then the iterate with index
`⌊2 / (α(F)^2 δ)⌋` satisfies
`f (S_N ((1 / γ₀(F)) f(x₀))) ≤ (1 + δ) f*`. -/
theorem direct_structure_iterate_value_le_one_add_delta_mul_optimal_value
    (f : Eₙ → ℝ) (S : ℕ → ℝ → Eₙ) (x0 : Eₙ) (α γ0 δ fStar : ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hα : 0 < α) (hγ0 : 0 < γ0) (hδ : 0 < δ) (hδ_lt_one : δ < 1)
    (hOptimalValue : IsGLB (Set.range f) fStar)
    (hEstimate :
      ∀ k : ℕ,
        f (S k (aPrioriRadiusEstimate f γ0 x0)) ≤
          fStar + (2 / (α ^ (2 : ℕ) * (k + 1 : ℝ))) * fStar) :
    f (S (Nat.floor (2 / (α ^ (2 : ℕ) * δ))) (aPrioriRadiusEstimate f γ0 x0)) ≤
      (1 + δ) * fStar := by
  let N : ℕ := Nat.floor (2 / (α ^ (2 : ℕ) * δ))
  let c : ℝ := 2 / (α ^ (2 : ℕ) * (N + 1 : ℝ))
  have hCoeff : c ≤ δ := by
    -- The floor choice of `N` gives exactly the coefficient bound needed at stage `N`.
    simpa [c, N] using chosenDirectStructureCoefficientLeDelta α δ hα hδ
  have hCoeff_pos : 0 < c := by
    -- The coefficient is positive because both `α` and `N + 1` are positive.
    dsimp [c]
    positivity
  have hStageEstimate : f (S N (aPrioriRadiusEstimate f γ0 x0)) ≤ fStar + c * fStar := by
    -- Specializing the source estimate at stage `N` isolates the one-step additive error term.
    simpa [c] using hEstimate N
  have hfStar_nonneg : 0 ≤ fStar := by
    -- The optimal-value lower bound and the stage estimate force the source optimum to be
    -- nonnegative, which is exactly what the scalar comparison needs.
    exact optimalValueNonneg_ofIsGLBUpperBound
      f (S N (aPrioriRadiusEstimate f γ0 x0)) fStar c hOptimalValue hCoeff_pos hStageEstimate
  have hScaled : c * fStar ≤ δ * fStar := by
    -- Scaling the coefficient bound by the nonnegative optimal value preserves the inequality.
    exact mul_le_mul_of_nonneg_right hCoeff hfStar_nonneg
  -- The final `calc` chain replaces the stagewise coefficient by `δ` and rewrites the target.
  calc
    f (S N (aPrioriRadiusEstimate f γ0 x0)) ≤ fStar + c * fStar := hStageEstimate
    _ ≤ fStar + δ * fStar := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_left hScaled fStar
    _ = (1 + δ) * fStar := by
      ring

end
