/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_25
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_2_1_Implementability_Assumptions_for_Primal_Dual_Structure

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin Gradient

universe u v

/-- The chapter excessive-gap condition on a feasible pair `(xBar, uBar)` is the inequality
`f_{μ₂}(xBar) ≤ φ_{μ₁}(uBar)`. -/
abbrev satisfiesExcessiveGapCondition
    {X : Type u} {U : Type v}
    (Q₁ : Set X) (Q₂ : Set U)
    (fμ₂ : X → ℝ) (φμ₁ : U → ℝ)
    (xBar : Q₁) (uBar : Q₂) : Prop :=
  fμ₂ xBar ≤ φμ₁ uBar

section Updates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]

/- Theorem 6.4 lies in the Chapter 6 excessive-gap / smoothing-update domain.

Mandatory domain-style sampling before refinement:
- `satisfiesExcessiveGapCondition` below, the source-facing owner for the excessive-gap
  certificate;
- `smoothedPrimalObjective` and `smoothedPrimalObjectiveArgmax` in `Chap06/Definition_6_30`, the
  Chapter 6 owners for the smoothed primal objective and the dual oracle maximizer set;
- `smoothedDualObjective` and `smoothedDualObjectiveMinimand` in `Chap06/Proposition_6_25`, whose
  finite real part and argmin surface give the real-valued dual quantity and primal oracle data
  used in the chapter;
- `constrainedArgmin` / `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the canonical feasible-minimizer owner and its membership bridge.

Best owner abstraction:
- source-facing: the update maps `\hat x`, `\bar u_+`, `\bar x_+` together with the preservation
  of `satisfiesExcessiveGapCondition`;
- core/canonical: `satisfiesExcessiveGapCondition`, `smoothedPrimalObjective`,
  `smoothedDualObjective`, `smoothedDualObjectiveMinimand`, `smoothedPrimalObjectiveArgmax`, and
  the direct argmin surface `xμ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand ... u)`;
- bridge/view: the subtype-valued update maps below, which turn the oracle-owner hypotheses into
  feasible updated points without introducing a second excessive-gap predicate.

Primitive data:
- the feasible sets `Q₁`, `Q₂` and their convexity;
- the Chapter 6 smoothing owners and oracle-selection hypotheses;
- the direct pointwise argmin data defining the primal oracle selections;
- the current feasible pair `(barx, baru)` and the step size `τ`.

Derived API:
- the updated smoothing parameter `μ₁⁺ = (1 - τ) μ₁`;
- the feasible updated points `\hat x`, `\bar u_+`, and `\bar x_+`;
- the source-facing preservation theorem stated directly through
  `satisfiesExcessiveGapCondition`.

The previous version rebuilt these notions through a new bundled owner `ExcessiveGapFramework`
and a second predicate `framework.excessive_gap_condition`. This file now keeps the textbook
update objects directly and states Theorem 6.4 on top of the existing Chapter 6 owners.
-/

/-- The updated primal smoothing parameter `μ₁⁺ = (1 - τ) μ₁`. -/
def reduced_primal_smoothing (μ₁ τ : ℝ) : ℝ :=
  (1 - τ) * μ₁

/-- Expanding `reduced_primal_smoothing` recovers the formula `μ₁⁺ = (1 - τ) μ₁`. -/
theorem reduced_primal_smoothing_def
    (μ₁ τ : ℝ) :
    reduced_primal_smoothing μ₁ τ = (1 - τ) * μ₁ := by
  -- This is the defining equation of the reduced smoothing parameter.
  rfl

/-- A step size in `(0, 1)` defines the convex-combination parameter used by the Chapter 6
updates. -/
theorem tau_mem_Icc
    {τ : ℝ} (hτ : 0 < τ) (hτ_lt : τ < 1) :
    τ ∈ Set.Icc (0 : ℝ) 1 := by
  -- Record the step size as a closed interval point for the convex-combination API.
  exact ⟨hτ.le, hτ_lt.le⟩

-- Proof sketch: unpack the selected point `xμ₁ baru` from the canonical argmin owner, use
-- `mem_constrainedArgmin_iff` to recover feasibility in `Q₁`, and then apply convexity of `Q₁`
-- to the convex combination with `barx`.
/-- The convex combination defining `\hat x` stays in the feasible primal set `Q₁`. -/
theorem predicted_primal_point_mem
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (barx : E₁) + τ • xμ₁ baru ∈ Q₁ := by
  -- First recover feasibility of the selected primal minimizer from the argmin owner.
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ baru) with ⟨hxμ₁_mem, _⟩
  -- Then use convexity of `Q₁` for the affine segment from `barx` to `xμ₁ baru`.
  have hx :
      (barx : E₁) + τ • (xμ₁ baru - (barx : E₁)) ∈ Q₁ :=
    hQ₁.add_smul_sub_mem barx.property hxμ₁_mem hτ
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using hx

/-- The intermediate primal point
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)` as a feasible point of `Q₁`. -/
def predicted_primal_point
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₁ :=
  ⟨(1 - τ) • (barx : E₁) + τ • xμ₁ baru,
    predicted_primal_point_mem hQ₁ hxμ₁ barx baru τ hτ⟩

/-- Expanding `predicted_primal_point` recovers
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)`. -/
@[simp] theorem predicted_primal_point_val
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (baru : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (predicted_primal_point hQ₁ hxμ₁ barx baru τ hτ : E₁) =
      (1 - τ) • (barx : E₁) + τ • xμ₁ baru := by
  -- The subtype wrapper stores exactly the displayed ambient point.
  rfl

-- Proof sketch: unpack the selected maximizer `uμ₂ xHat` with
-- `mem_smoothedPrimalObjectiveArgmax_iff` to recover feasibility in `Q₂`, and then use convexity
-- of `Q₂` for the convex combination with `baru`.
/-- The convex combination defining `\bar u_+` stays in the feasible dual set `Q₂`. -/
theorem updated_dual_point_mem
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (baru : E₂) + τ • uμ₂ xHat ∈ Q₂ := by
  -- Recover feasibility of the selected dual maximizer from the argmax owner.
  rcases
      (mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ₂ (xHat : E₁) (uμ₂ xHat)).mp
        (huμ₂ xHat.property) with
    ⟨huμ₂_mem, _⟩
  -- Convexity of `Q₂` keeps the update segment inside the feasible set.
  have hu :
      (baru : E₂) + τ • (uμ₂ xHat - (baru : E₂)) ∈ Q₂ :=
    hQ₂.add_smul_sub_mem baru.property huμ₂_mem hτ
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using hu

/-- The updated dual point
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)` as a feasible point of `Q₂`. -/
def updated_dual_point
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₂ :=
  ⟨(1 - τ) • (baru : E₂) + τ • uμ₂ xHat,
    updated_dual_point_mem hQ₂ huμ₂ baru xHat τ hτ⟩

/-- Expanding `updated_dual_point` recovers
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`. -/
@[simp] theorem updated_dual_point_val
    {Q₁ : Set E₁} {Q₂ : Set E₂} (hQ₂ : Convex ℝ Q₂)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatφ d₂ : E₂ → ℝ} {μ₂ : ℝ}
    {uμ₂ : E₁ → E₂}
    (huμ₂ : ∀ ⦃x : E₁⦄, x ∈ Q₁ → uμ₂ x ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ₂ x)
    (baru : Q₂) (xHat : Q₁)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updated_dual_point hQ₂ huμ₂ baru xHat τ hτ : E₂) =
      (1 - τ) • (baru : E₂) + τ • uμ₂ xHat := by
  -- The subtype wrapper stores exactly the displayed ambient point.
  rfl

-- Proof sketch: unpack the selected point `xμ₁ uBarPlus` from the canonical argmin owner, use
-- `mem_constrainedArgmin_iff` to recover feasibility in `Q₁`, and then apply convexity of `Q₁`
-- to the convex combination with `barx`.
/-- The convex combination defining `\bar x_+` stays in the feasible primal set `Q₁`. -/
theorem updated_primal_point_mem
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus ∈ Q₁ := by
  -- Recover feasibility of the selected updated primal minimizer from the argmin owner.
  rcases mem_constrainedArgmin_iff.mp (hxμ₁ uBarPlus) with ⟨hxμ₁_mem, _⟩
  -- Then apply convexity of `Q₁` to the update segment from `barx`.
  have hx :
      (barx : E₁) + τ • (xμ₁ uBarPlus - (barx : E₁)) ∈ Q₁ :=
    hQ₁.add_smul_sub_mem barx.property hxμ₁_mem hτ
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, smul_add, add_smul] using hx

/-- The updated primal point
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)` as a feasible point of `Q₁`. -/
def updated_primal_point
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Q₁ :=
  ⟨(1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus,
    updated_primal_point_mem hQ₁ hxμ₁ barx uBarPlus τ hτ⟩

/-- Expanding `updated_primal_point` recovers
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁⁺}(\bar u_+)`. -/
@[simp] theorem updated_primal_point_val
    {Q₁ : Set E₁} (hQ₁ : Convex ℝ Q₁)
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {hatf d₁ : E₁ → ℝ} {μ₁ : ℝ}
    {xμ₁ : E₂ → E₁}
    (hxμ₁ :
      ∀ u : E₂, xμ₁ u ∈ argmin[Q₁] (smoothedDualObjectiveMinimand A hatf d₁ μ₁ u))
    {Q₂ : Set E₂} (barx : Q₁) (uBarPlus : Q₂)
    (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    (updated_primal_point hQ₁ hxμ₁ barx uBarPlus τ hτ : E₁) =
      (1 - τ) • (barx : E₁) + τ • xμ₁ uBarPlus := by
  -- The subtype wrapper stores exactly the displayed ambient point.
  rfl

end Updates

section Theorem

section ElementaryUpdates

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Helper for Theorem 6 4: the two update formulas differ by the expected `τ`-scaled oracle
displacement. -/
theorem updated_points_displacement
    {Q : Set E₁}
    {barx xHat xBarPlus xμ xμPlus : Q}
    {τ : ℝ}
    (hxHat : (xHat : E₁) = (1 - τ) • (barx : E₁) + τ • (xμ : E₁))
    (hxBarPlus : (xBarPlus : E₁) = (1 - τ) • (barx : E₁) + τ • (xμPlus : E₁)) :
    (xBarPlus : E₁) - xHat = τ • ((xμPlus : E₁) - (xμ : E₁)) := by
  -- Expand both updates and collect the shared base point `barx`.
  rw [hxBarPlus, hxHat]
  calc
    (1 - τ) • (barx : E₁) + τ • (xμPlus : E₁) -
        ((1 - τ) • (barx : E₁) + τ • (xμ : E₁)) =
      τ • (xμPlus : E₁) - τ • (xμ : E₁) := by
        abel_nf
    _ = τ • ((xμPlus : E₁) - (xμ : E₁)) := by
        rw [smul_sub]

/-- Helper for Theorem 6 4: the step-size bound turns the quadratic remainder of the upper model
into the updated `μ₁⁺`-weighted oracle displacement term. -/
theorem stepSizeAbsorbsPredictedQuadraticError
    {Q : Set E₁}
    {xHat xBarPlus xμ xμPlus : Q}
    {μ₁ μ₁Plus τ L : ℝ}
    (hτ : 0 < τ) (hτ_lt : τ < 1) (hL_pos : 0 < L)
    (hdisp : (xBarPlus : E₁) - xHat = τ • ((xμPlus : E₁) - (xμ : E₁)))
    (hμ₁Plus : μ₁Plus = reduced_primal_smoothing μ₁ τ)
    (hstep : τ ^ (2 : ℕ) / (1 - τ) ≤ μ₁ / L) :
    (L / 2) * ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) ≤
      (μ₁Plus / 2) * ‖(xμPlus : E₁) - (xμ : E₁)‖ ^ (2 : ℕ) := by
  have hone_sub : 0 < 1 - τ := sub_pos.mpr hτ_lt
  have hcoeff :
      L * τ ^ (2 : ℕ) ≤ reduced_primal_smoothing μ₁ τ := by
    have hstep' : τ ^ (2 : ℕ) ≤ (μ₁ / L) * (1 - τ) := by
      exact (div_le_iff₀ hone_sub).mp hstep
    have hscaled :
        L * τ ^ (2 : ℕ) ≤ L * ((μ₁ / L) * (1 - τ)) :=
      mul_le_mul_of_nonneg_left hstep' hL_pos.le
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    calc
      L * τ ^ (2 : ℕ) ≤ L * ((μ₁ / L) * (1 - τ)) := hscaled
      _ = reduced_primal_smoothing μ₁ τ := by
        rw [reduced_primal_smoothing_def, div_eq_mul_inv]
        field_simp [hL_ne]
  have hnorm :
      ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) =
        τ ^ (2 : ℕ) * ‖(xμPlus : E₁) - (xμ : E₁)‖ ^ (2 : ℕ) := by
    rw [hdisp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.le]
    ring
  -- Rewrite the displacement norm through the `τ`-scaled oracle difference and compare the
  -- coefficients using the step-size inequality.
  calc
    (L / 2) * ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) =
      ((L * τ ^ (2 : ℕ)) / 2) * ‖(xμPlus : E₁) - (xμ : E₁)‖ ^ (2 : ℕ) := by
        rw [hnorm]
        ring
    _ ≤ (μ₁Plus / 2) * ‖(xμPlus : E₁) - (xμ : E₁)‖ ^ (2 : ℕ) := by
        rw [hμ₁Plus]
        have hsq_nonneg : 0 ≤ ‖(xμPlus : E₁) - (xμ : E₁)‖ ^ (2 : ℕ) := by
          positivity
        nlinarith

end ElementaryUpdates

section Main

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]

/-- Helper for Theorem 6 4: a normalized prox-center forces the prox function to be nonnegative
at every feasible point. -/
theorem proxFunction_nonneg_of_proxCenter
    {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ}
    (hproxCenter : ∃ z : E, NesterovIsProxCenter Q d z)
    {x : E} (hx : x ∈ Q) :
    0 ≤ d x := by
  rcases hproxCenter with ⟨z, hz⟩
  -- Compare the feasible point with the normalized minimizer supplied by the prox center.
  have hmin : d z ≤ d x :=
    hz.isMinOn hx
  rw [hz.value_eq_zero] at hmin
  simpa using hmin

/-- Helper for Theorem 6 4: strong convexity of the updated primal slice gives the quadratic gap
between the old comparison point and the updated minimizer. -/
theorem updatedPrimalSlice_quadraticLowerBound
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hprimalProx : StrongConvexOn problem.primalSet 1 problem.primalProxFunction)
    {μ₁Plus : ℝ} (hμ₁Plus_pos : 0 < μ₁Plus)
    {uBarPlus : problem.dualSet}
    {xμ₁uBar xμ₁PlusuBarPlus : problem.primalSet}
    (hxμ₁PlusuBarPlus :
      (xμ₁PlusuBarPlus : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁Plus
            (uBarPlus : E₂))) :
    -problem.dualPenalty uBarPlus +
        problem.linearMap xμ₁uBar (uBarPlus : E₂) +
        problem.smoothPart xμ₁uBar +
        μ₁Plus * problem.primalProxFunction xμ₁uBar ≥
      extendedRealRealPart
        (smoothedDualObjective
          problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
        uBarPlus +
        (μ₁Plus / 2) * ‖(xμ₁uBar : E₁) - xμ₁PlusuBarPlus‖ ^ (2 : ℕ) := by
  let slice := smoothedDualObjectiveMinimand
    problem.linearMap problem.smoothPart problem.primalProxFunction μ₁Plus (uBarPlus : E₂)
  have hstrong :
      StrongConvexOn problem.primalSet μ₁Plus slice :=
    smoothedDualObjectiveMinimand_slice_strongConvexOn
      problem.linearMap
      hμ₁Plus_pos
      problem.smoothPart_convex
      hprimalProx
      (uBarPlus : E₂)
  rcases mem_constrainedArgmin_iff.mp hxμ₁PlusuBarPlus with ⟨hxmin_mem, hxmin_min⟩
  -- Compare the old feasible point with the updated minimizer of the strongly convex slice.
  have hquad :
      slice xμ₁uBar ≥
        slice xμ₁PlusuBarPlus +
          (μ₁Plus / 2) * ‖(xμ₁uBar : E₁) - xμ₁PlusuBarPlus‖ ^ (2 : ℕ) :=
    hstrong.quadratic_growth_of_isMinOn_of_mem
      hxmin_mem hxmin_min (xμ₁uBar : E₁) xμ₁uBar.property
  have hvalue :
      extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
          uBarPlus =
        -problem.dualPenalty uBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (uBarPlus : E₂) +
          problem.smoothPart xμ₁PlusuBarPlus +
          μ₁Plus * problem.primalProxFunction xμ₁PlusuBarPlus := by
    -- Rewrite the finite real part of the smoothed dual objective using the selected minimizer.
    simpa using
      (smoothedDualObjective_value_at_selected_argmin
        problem.linearMap
        (hatφ := problem.dualPenalty)
        (d₁ := problem.primalProxFunction)
        (hx := hxμ₁PlusuBarPlus))
  -- Replace the slice values by the explicit Chapter 6 formulas and insert the attained dual
  -- value at the updated minimizer.
  calc
    -problem.dualPenalty uBarPlus +
        problem.linearMap xμ₁uBar (uBarPlus : E₂) +
        problem.smoothPart xμ₁uBar +
        μ₁Plus * problem.primalProxFunction xμ₁uBar =
      -problem.dualPenalty uBarPlus + slice xμ₁uBar := by
        simp [slice, smoothedDualObjectiveMinimand_apply, add_left_comm, add_comm]
    _ ≥
        -problem.dualPenalty uBarPlus +
          (slice xμ₁PlusuBarPlus +
            (μ₁Plus / 2) * ‖(xμ₁uBar : E₁) - xμ₁PlusuBarPlus‖ ^ (2 : ℕ)) := by
        gcongr
    _ =
        extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
          uBarPlus +
          (μ₁Plus / 2) * ‖(xμ₁uBar : E₁) - xμ₁PlusuBarPlus‖ ^ (2 : ℕ) := by
        rw [hvalue]
        simp [slice, smoothedDualObjectiveMinimand_apply, add_left_comm, add_comm]

/-- Helper for Theorem 6 4: the smoothed primal objective admits the exact integral remainder
formula along a feasible segment when a continuous within-gradient field is fixed on `Q`. -/
theorem increment_eq_linearization_add_integralRemainder_of_hasGradientWithinAt
    {Q : Set E₁} {f : E₁ → ℝ} {g : E₁ → E₁}
    (hgrad : ∀ ⦃x : E₁⦄, x ∈ Q → HasGradientWithinAt f (g x) Q x)
    (hg_cont : ContinuousOn g Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E₁} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y =
      f x + inner ℝ (g x) (y - x) +
        ∫ t : ℝ in 0..1, inner ℝ (g (AffineMap.lineMap x y t) - g x) (y - x) := by
  let gDual : E₁ → StrongDual ℝ E₁ := fun z ↦ (InnerProductSpace.toDual ℝ E₁) (g z)
  let seg : ℝ → E₁ := AffineMap.lineMap x y
  let remainder : ℝ → ℝ := fun t ↦ (gDual (seg t) - gDual x) (y - x)
  let ψ : ℝ → ℝ := fun t ↦ f (seg t) - t * (gDual x (y - x))
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    exact hQ_convex.lineMap_mem hx hy ht
  have hseg_deriv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun s ↦ f (seg s)) (gDual (seg t) (y - x)) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    -- Compose the within-gradient of `f` with the segment parameterization.
    simpa [seg, gDual, InnerProductSpace.toDual_apply_apply] using
      (hgrad (hseg ht)).hasFDerivWithinAt.comp_hasDerivWithinAt t
        AffineMap.hasDerivWithinAt_lineMap hseg
  have hseg_cont : ContinuousOn (fun t ↦ f (seg t)) (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact (hseg_deriv t ht).continuousWithinAt
  have hgDual_cont : ContinuousOn gDual Q := by
    intro z hz
    exact ContinuousAt.comp_continuousWithinAt
      ((LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E₁)).continuousAt)
      (hg_cont z hz)
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    have hgrad_cont : ContinuousOn (fun t ↦ gDual (seg t)) (Set.Icc (0 : ℝ) 1) :=
      hgDual_cont.comp AffineMap.lineMap_continuous.continuousOn hseg
    have hsub_cont :
        ContinuousOn (fun t ↦ gDual (seg t) - gDual x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    -- Evaluate the continuous dual field on the fixed segment direction.
    simpa [remainder] using
      hsub_cont.clm_apply
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 :=
    hremainder_cont_uIcc.intervalIntegrable
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    have hlin_cont : ContinuousOn (fun t : ℝ ↦ t * (gDual x (y - x))) (Set.Icc (0 : ℝ) 1) :=
      (continuous_id'.mul continuous_const).continuousOn
    simpa [ψ] using hseg_cont.sub hlin_cont
  have hψ_deriv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt ψ (remainder t) (Set.Ioi t) t := by
    intro t ht
    -- Work with right derivatives on `(t, +∞)` so the interval FTC applies on `[0, 1]`.
    have hseg_deriv_right :
        HasDerivWithinAt (fun s ↦ f (seg s)) (gDual (seg t) (y - x)) (Set.Ioi t) t :=
      (hseg_deriv t (Set.mem_Icc_of_Ioo ht)).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGT ht.2)
          (by
            intro s hs
            exact ⟨ht.1.le.trans hs.1, hs.2⟩))
    have hlin_deriv :
        HasDerivWithinAt (fun s : ℝ ↦ s * (gDual x (y - x))) (gDual x (y - x)) (Set.Ioi t) t := by
      simpa only [one_mul] using ((hasDerivAt_id' t).mul_const (gDual x (y - x))).hasDerivWithinAt
    simpa [ψ, remainder, sub_eq_add_neg, sub_mul] using hseg_deriv_right.sub hlin_deriv
  have hftc :
      ∫ t : ℝ in 0..1, remainder t = ψ 1 - ψ 0 := by
    -- Apply the one-dimensional fundamental theorem of calculus to the remainder function.
    exact intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      zero_le_one hψ_cont hψ_deriv hremainder_int
  have hftc' :
      ∫ t : ℝ in 0..1, remainder t =
        f y - f x - inner ℝ (g x) (y - x) := by
    simpa [ψ, remainder, seg, gDual, InnerProductSpace.toDual_apply_apply, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hftc
  have hftc'' :
      ∫ t : ℝ in 0..1, inner ℝ (g (AffineMap.lineMap x y t) - g x) (y - x) =
        f y - f x - inner ℝ (g x) (y - x) := by
    calc
      ∫ t : ℝ in 0..1, inner ℝ (g (AffineMap.lineMap x y t) - g x) (y - x) =
          ∫ t : ℝ in 0..1, (inner ℝ (g (AffineMap.lineMap x y t)) (y - x) -
            inner ℝ (g x) (y - x)) := by
              congr with t
              rw [inner_sub_left]
      _ = f y - f x - inner ℝ (g x) (y - x) := by
          simpa [remainder, seg, gDual, InnerProductSpace.toDual_apply_apply, sub_eq_add_neg]
            using hftc'
  rw [hftc'']
  ring

/-- Helper for Theorem 6 4: a Lipschitz within-gradient field on a convex feasible set yields the
standard quadratic upper model on that set. -/
theorem upper_model_of_hasGradientWithinAt_lipschitzOn
    {Q : Set E₁} {f : E₁ → ℝ} {g : E₁ → E₁} {L : NNReal}
    (hgrad : ∀ ⦃x : E₁⦄, x ∈ Q → HasGradientWithinAt f (g x) Q x)
    (hg_lipschitz : LipschitzOnWith L g Q)
    (hQ_convex : Convex ℝ Q)
    {x y : E₁} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y ≤
      f x + inner ℝ (g x) (y - x) +
        ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  let remainder : ℝ → ℝ := fun t ↦ inner ℝ (g (AffineMap.lineMap x y t) - g x) (y - x)
  let kernel : ℝ → ℝ := fun t ↦ (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ)
  have hincrement :=
    increment_eq_linearization_add_integralRemainder_of_hasGradientWithinAt
      hgrad hg_lipschitz.continuousOn hQ_convex hx hy
  have hremainder_cont : ContinuousOn remainder (Set.Icc (0 : ℝ) 1) := by
    have hgrad_cont :
        ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t)) (Set.Icc (0 : ℝ) 1) := by
      refine hg_lipschitz.continuousOn.comp AffineMap.lineMap_continuous.continuousOn ?_
      intro t ht
      exact hQ_convex.lineMap_mem hx hy ht
    have hsub_cont :
        ContinuousOn (fun t ↦ g (AffineMap.lineMap x y t) - g x) (Set.Icc (0 : ℝ) 1) :=
      hgrad_cont.sub continuousOn_const
    -- Evaluate the continuous vector-field difference against the fixed direction `y - x`.
    simpa [remainder] using
      hsub_cont.inner
        (show ContinuousOn (fun _ : ℝ ↦ y - x) (Set.Icc (0 : ℝ) 1) from continuousOn_const)
  have hremainder_cont_uIcc : ContinuousOn remainder (Set.uIcc (0 : ℝ) 1) := by
    simpa [Set.uIcc_of_le zero_le_one] using hremainder_cont
  have hremainder_int : IntervalIntegrable remainder MeasureTheory.volume 0 1 := by
    exact hremainder_cont_uIcc.intervalIntegrable
  have hkernel_int : IntervalIntegrable kernel MeasureTheory.volume 0 1 := by
    have hint :
        IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
      Continuous.intervalIntegrable continuous_id 0 1
    convert hint.const_mul ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) using 1
    ext t
    simp [kernel, mul_assoc, mul_comm]
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) 1, remainder t ≤ kernel t := by
    intro t ht
    have hline_mem : AffineMap.lineMap x y t ∈ Q :=
      hQ_convex.lineMap_mem hx hy ht
    have hgrad_bound :
        ‖g (AffineMap.lineMap x y t) - g x‖ ≤
          (L : ℝ) * ‖AffineMap.lineMap x y t - x‖ := by
      simpa [dist_eq_norm] using hg_lipschitz.norm_sub_le hline_mem hx
    have hseg_norm : ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
      calc
        ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
          simp [AffineMap.lineMap_apply_module']
        _ = |t| * ‖y - x‖ := norm_smul t (y - x)
        _ = t * ‖y - x‖ := by rw [abs_of_nonneg ht.1]
    -- Bound the scalar remainder by the operator norm of the gradient increment.
    calc
      remainder t ≤ |remainder t| := le_abs_self _
      _ ≤ ‖g (AffineMap.lineMap x y t) - g x‖ * ‖y - x‖ := by
        simpa [remainder, real_inner_comm] using
          abs_real_inner_le_norm (g (AffineMap.lineMap x y t) - g x) (y - x)
      _ ≤ ((L : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
        gcongr
      _ = ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by rw [hseg_norm]
      _ = kernel t := by
        simp [kernel]
        ring
  have hmono :
      ∫ t : ℝ in 0..1, remainder t ≤ ∫ t : ℝ in 0..1, kernel t := by
    exact intervalIntegral.integral_mono_on
      (hf := hremainder_int) (hg := hkernel_int) (hab := zero_le_one) hpoint
  -- Compare the exact integral remainder with the quadratic kernel and evaluate `∫₀¹ t dt`.
  calc
    f y = f x + inner ℝ (g x) (y - x) + ∫ t : ℝ in 0..1, remainder t := hincrement
    _ ≤ f x + inner ℝ (g x) (y - x) + ∫ t : ℝ in 0..1, kernel t := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_left hmono (f x + inner ℝ (g x) (y - x))
    _ = f x + inner ℝ (g x) (y - x) +
        ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      calc
        f x + inner ℝ (g x) (y - x) + ∫ t : ℝ in 0..1, kernel t =
            f x + inner ℝ (g x) (y - x) +
              (((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * ∫ t : ℝ in 0..1, t) := by
              simp [kernel, mul_assoc, mul_comm]
        _ = f x + inner ℝ (g x) (y - x) +
              (((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) / 2) := by
              rw [integral_id]
              ring_nf
        _ = f x + inner ℝ (g x) (y - x) +
              ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
              ring_nf

/-- Helper for Theorem 6 4: the Chapter 6 smoothed primal objective is convex on the primal
feasible set. -/
theorem smoothedPrimalObjective_convexOn
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (μ : {μ : ℝ // 0 < μ}) :
    ConvexOn ℝ problem.primalSet
      (smoothedPrimalObjective
        problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction μ) := by
  let zeroPart :=
    smoothedPrimalObjective
      problem.linearMap problem.dualSet
      (fun _ : E₁ ↦ 0) problem.dualPenalty problem.dualProxFunction μ
  have hzeroConv :
      ConvexOn ℝ problem.primalSet zeroPart := by
    refine ⟨problem.primalSet_convex, ?_⟩
    intro x hx y hy a b ha hb hab
    let z : E₁ := a • x + b • y
    have hz : z ∈ problem.primalSet :=
      problem.primalSet_convex hx hy ha hb hab
    let uz : E₂ := problem.dualOracleSolver ⟨z, hz⟩ μ
    have huz :
        uz ∈ smoothedPrimalObjectiveArgmax
          problem.linearMap problem.dualSet
          problem.dualPenalty problem.dualProxFunction μ z :=
      problem.dualOracleSolver_spec ⟨z, hz⟩ μ
    rcases
        (mem_smoothedPrimalObjectiveArgmax_iff
          problem.linearMap problem.dualSet
          problem.dualPenalty problem.dualProxFunction μ z uz).mp huz with
      ⟨huz_mem, _⟩
    have hux :
        (problem.dualOracleSolver ⟨x, hx⟩ μ : E₂) ∈
          smoothedPrimalObjectiveArgmax
            problem.linearMap problem.dualSet
            problem.dualPenalty problem.dualProxFunction μ x :=
      problem.dualOracleSolver_spec ⟨x, hx⟩ μ
    have huy :
        (problem.dualOracleSolver ⟨y, hy⟩ μ : E₂) ∈
          smoothedPrimalObjectiveArgmax
            problem.linearMap problem.dualSet
            problem.dualPenalty problem.dualProxFunction μ y :=
      problem.dualOracleSolver_spec ⟨y, hy⟩ μ
    rcases
        (mem_smoothedPrimalObjectiveArgmax_iff
          problem.linearMap problem.dualSet
          problem.dualPenalty problem.dualProxFunction μ x
          (problem.dualOracleSolver ⟨x, hx⟩ μ)).mp hux with
      ⟨_, hux_max⟩
    rcases
        (mem_smoothedPrimalObjectiveArgmax_iff
          problem.linearMap problem.dualSet
          problem.dualPenalty problem.dualProxFunction μ y
          (problem.dualOracleSolver ⟨y, hy⟩ μ)).mp huy with
      ⟨_, huy_max⟩
    have hslicewise :
        smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction μ z uz ≤
          a *
              smoothedPrimalObjectiveMaximand
                problem.linearMap problem.dualPenalty problem.dualProxFunction μ x uz +
            b *
              smoothedPrimalObjectiveMaximand
                problem.linearMap problem.dualPenalty problem.dualProxFunction μ y uz := by
      -- The fixed-`u` slice is affine in the primal variable, hence convex.
      simpa [z] using
        (smoothedPrimalObjectiveMaximand_convexOn
          problem.linearMap problem.dualPenalty problem.dualProxFunction (μ : ℝ) uz).2
          (by simp) (by simp) ha hb hab
    have hupper_x :
        smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction μ x uz ≤
          zeroPart x := by
      have hmax := (isMaxOn_iff.mp hux_max) uz huz_mem
      exact hmax.trans_eq <| by
        simpa [zeroPart] using (smoothedPrimalObjectiveArgmax.value_eq hux).symm
    have hupper_y :
        smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction μ y uz ≤
          zeroPart y := by
      have hmax := (isMaxOn_iff.mp huy_max) uz huz_mem
      exact hmax.trans_eq <| by
        simpa [zeroPart] using (smoothedPrimalObjectiveArgmax.value_eq huy).symm
    -- Compare the chosen oracle at `z` with the maximized zero-part values at `x` and `y`.
    calc
      zeroPart z =
          smoothedPrimalObjectiveMaximand
            problem.linearMap problem.dualPenalty problem.dualProxFunction μ z uz := by
          simpa [zeroPart] using smoothedPrimalObjectiveArgmax.value_eq huz
      _ ≤ a * zeroPart x + b * zeroPart y := by
          exact hslicewise.trans <| add_le_add (mul_le_mul_of_nonneg_left hupper_x ha)
            (mul_le_mul_of_nonneg_left hupper_y hb)
  -- Add the convex smooth part to the convex zero-smoothing part.
  convert problem.smoothPart_convex.add hzeroConv using 1
  ext x
  simp [zeroPart, smoothedPrimalObjective, add_comm]

/-- Helper for Theorem 6 4: the quadratic upper model at `xHat` splits into the old excessive-gap
term at `barx` and the updated selected-dual slice at `x_{μ₁⁺}(\bar u_+)`. -/
theorem predictedUpperModel_le_weightedGapAndUpdatedDualSlice
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    {barx : problem.primalSet}
    {xHat xBarPlus xμ₁PlusuBarPlus : problem.primalSet}
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (hdualProx_nonneg :
      0 ≤ problem.dualProxFunction (problem.dualOracleSolver xHat μ₂))
    (hxBarPlus :
      (xBarPlus : E₁) = (1 - τ) • (barx : E₁) + τ • (xμ₁PlusuBarPlus : E₁)) :
    smoothedPrimalObjective
        problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂ xBarPlus ≤
      (1 - τ) *
          smoothedPrimalObjective
            problem.linearMap problem.dualSet
            problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂ barx +
        τ *
          (problem.smoothPart xμ₁PlusuBarPlus +
            problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
            problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
        (((problem.smoothPartGradientLipschitzConstant +
            Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ) / 2) *
          ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) := by
  classical
  let fμ₂ :=
    smoothedPrimalObjective
      problem.linearMap problem.dualSet
      problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂
  let uSel : E₁ → E₂ := fun x ↦
    if hx : x ∈ problem.primalSet then
      problem.dualOracleSolver ⟨x, hx⟩ μ₂
    else
      problem.dualOracleSolver xHat μ₂
  let gField : E₁ → E₁ := fun x ↦
    gradientWithin problem.smoothPart problem.primalSet x +
      (InnerProductSpace.toDual ℝ E₁).symm (problem.linearMap.flip (uSel x))
  have huSel :
      ∀ ⦃x : E₁⦄, x ∈ problem.primalSet →
        uSel x ∈
          smoothedPrimalObjectiveArgmax
            problem.linearMap problem.dualSet
            problem.dualPenalty problem.dualProxFunction μ₂ x := by
    intro x hx
    simpa [uSel, hx] using problem.dualOracleSolver_spec ⟨x, hx⟩ μ₂
  have hgrad_pair :=
    smoothedPrimalObjective_argmax_unique_and_hasGradientWithinAt
      problem.linearMap
      (hμ₂ := μ₂.property)
      problem.dualPenalty_convex
      hdualProx
      problem.smoothPart_hasGradientWithinAt
      (uμ₂ := uSel)
      huSel
  have hgrad_all :
      ∀ ⦃x : E₁⦄, x ∈ problem.primalSet →
        HasGradientWithinAt fμ₂ (gField x) problem.primalSet x := by
    intro x hx
    simpa [fμ₂, gField, uSel, hx] using (hgrad_pair.2 hx)
  have hgrad :
      HasGradientWithinAt fμ₂ (gField xHat) problem.primalSet xHat := by
    -- Specialize Proposition 6.24 to the predicted point `xHat`.
    exact hgrad_all xHat.property
  have hgrad_lipschitz :
      LipschitzOnWith
        (problem.smoothPartGradientLipschitzConstant +
          Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ)))
        gField
        problem.primalSet := by
    -- The Chapter 6 gradient field of `f_{μ₂}` is Lipschitz on the feasible set.
    simpa [gField, uSel] using
      (smoothedPrimalObjective_gradientWithin_lipschitzOn
        problem.linearMap
        (hμ₂ := μ₂.property)
        problem.dualPenalty_convex
        hdualProx
        problem.smoothPart_hasGradientWithinAt
        (uμ₂ := uSel)
        huSel
        problem.smoothPart_gradient_lipschitz)
  have hupper :=
    upper_model_of_hasGradientWithinAt_lipschitzOn
      (Q := problem.primalSet)
      (f := fμ₂)
      (g := gField)
      hgrad_all
      hgrad_lipschitz
      problem.primalSet_convex
      xHat.property
      xBarPlus.property
  have hbar_support :
      fμ₂ xHat + inner ℝ (gField xHat) ((barx : E₁) - xHat) ≤ fμ₂ barx := by
    -- Convexity of `f_{μ₂}` controls the tangent plane at `xHat` by the old value at `barx`.
    exact
      (smoothedPrimalObjective_convexOn problem μ₂).lower_tangent_plane_of_hasGradientWithinAt
        xHat xHat.property (gField xHat) hgrad barx barx.property
  have hselected :
      fμ₂ xHat +
          inner ℝ (gField xHat) ((xμ₁PlusuBarPlus : E₁) - xHat) ≤
        problem.smoothPart xμ₁PlusuBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
          problem.dualPenalty (problem.dualOracleSolver xHat μ₂) := by
    -- Lemma 6.2.2 rewrites the explicit `xHat`-linearization into the selected-dual slice.
    simpa [fμ₂, gField, uSel, xHat.property] using
      (smoothedPrimalObjective_linearization_le_selected_dual_value_of_explicit_gradient
        problem.linearMap
        problem.smoothPart_convex
        μ₂.property.le
        xμ₁PlusuBarPlus.property
        xHat.property
        (problem.dualOracleSolver_spec xHat μ₂)
        (problem.smoothPart_hasGradientWithinAt xHat.property)
        hdualProx_nonneg)
  have hsplit :
      fμ₂ xHat + inner ℝ (gField xHat) ((xBarPlus : E₁) - xHat) =
        (1 - τ) * (fμ₂ xHat + inner ℝ (gField xHat) ((barx : E₁) - xHat)) +
          τ * (fμ₂ xHat +
            inner ℝ (gField xHat) ((xμ₁PlusuBarPlus : E₁) - xHat)) := by
    -- Expand `xBarPlus` into the convex combination from the update formula.
    rw [hxBarPlus]
    simp [sub_eq_add_neg, inner_add_right, inner_smul_right, add_comm, add_left_comm]
    ring
  have hone_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_lt.le
  calc
    fμ₂ xBarPlus ≤
        fμ₂ xHat +
          inner ℝ (gField xHat) ((xBarPlus : E₁) - xHat) +
          (((problem.smoothPartGradientLipschitzConstant +
              Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ) / 2) *
            ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) := hupper
    _ =
        (1 - τ) * (fμ₂ xHat + inner ℝ (gField xHat) ((barx : E₁) - xHat)) +
          τ * (fμ₂ xHat +
            inner ℝ (gField xHat) ((xμ₁PlusuBarPlus : E₁) - xHat)) +
          (((problem.smoothPartGradientLipschitzConstant +
              Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ) / 2) *
            ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) := by
        rw [hsplit]
    _ ≤
        (1 - τ) * fμ₂ barx +
          τ *
            (problem.smoothPart xμ₁PlusuBarPlus +
              problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
              problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
          (((problem.smoothPartGradientLipschitzConstant +
              Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ) / 2) *
            ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) := by
        have hone_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_lt.le
        nlinarith [hbar_support, hselected]

/-- Helper for Theorem 6 4: convexity of the dual penalty transports the weighted negative
dual term directly to the updated dual point. -/
theorem updatedDualPenalty_convex_neg
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    {baru uBarPlus : problem.dualSet}
    {xHat : problem.primalSet}
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (huBarPlus :
      (uBarPlus : E₂) =
        (1 - τ) • (baru : E₂) + τ • (problem.dualOracleSolver xHat μ₂ : E₂)) :
    -(1 - τ) * problem.dualPenalty baru -
        τ * problem.dualPenalty (problem.dualOracleSolver xHat μ₂) ≤
      -problem.dualPenalty uBarPlus := by
  have hdual_conv :
      problem.dualPenalty uBarPlus ≤
        (1 - τ) * problem.dualPenalty baru +
          τ * problem.dualPenalty (problem.dualOracleSolver xHat μ₂) := by
    -- Rewrite `uBarPlus` into the update formula and apply convexity of `\hat φ`.
    rw [huBarPlus]
    refine problem.dualPenalty_convex.2 baru.property
      (problem.dualOracleSolver xHat μ₂).property
      (sub_nonneg.mpr hτ_lt.le) hτ.le ?_
    ring
  -- Negating the convexity bound puts the dual term in the sign used by the final assembly.
  linarith

/-- Helper for Theorem 6 4: the weighted old excessive-gap term and the updated selected-dual
slice land directly on the new dual value, with the old `μ₁`-slice strong-convexity gain carried
as a subtractive quadratic correction. -/
theorem weightedGapAndUpdatedDualSlice_le_newDualValue_subquadratic
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {μ₁ : ℝ} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    {barx : problem.primalSet} {baru uBarPlus : problem.dualSet}
    {xHat xμ₁uBar xμ₁PlusuBarPlus : problem.primalSet}
    (hμ₁_pos : 0 < μ₁)
    (hprimalProx : StrongConvexOn problem.primalSet 1 problem.primalProxFunction)
    (hgap :
      satisfiesExcessiveGapCondition
        problem.primalSet problem.dualSet
        (smoothedPrimalObjective
          problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂)
        (extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁))
        barx baru)
    (hxμ₁uBar :
      (xμ₁uBar : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁ (baru : E₂)))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (huBarPlus :
      (uBarPlus : E₂) =
        (1 - τ) • (baru : E₂) + τ • (problem.dualOracleSolver xHat μ₂ : E₂))
    {μ₁Plus : ℝ}
    (hμ₁Plus : μ₁Plus = reduced_primal_smoothing μ₁ τ)
    (hxμ₁PlusuBarPlus :
      (xμ₁PlusuBarPlus : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁Plus
            (uBarPlus : E₂))) :
    (1 - τ) *
        smoothedPrimalObjective
          problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂ barx +
      τ *
        (problem.smoothPart xμ₁PlusuBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
          problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) ≤
      extendedRealRealPart
        (smoothedDualObjective
          problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
        uBarPlus -
        (μ₁Plus / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) := by
  let fμ₂ :=
    smoothedPrimalObjective
      problem.linearMap problem.dualSet
      problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂
  let oldSlice :=
    smoothedDualObjectiveMinimand
      problem.linearMap problem.smoothPart problem.primalProxFunction μ₁ (baru : E₂)
  have hgap_old :
      fμ₂ barx ≤
        -problem.dualPenalty baru +
          problem.linearMap xμ₁uBar (baru : E₂) +
          problem.smoothPart xμ₁uBar +
          μ₁ * problem.primalProxFunction xμ₁uBar := by
    -- Rewrite the old dual value by the selected minimizer at `\bar u`.
    simpa [fμ₂] using hgap.trans_eq
      (smoothedDualObjective_value_at_selected_argmin
        problem.linearMap
        (hatφ := problem.dualPenalty)
        (d₁ := problem.primalProxFunction)
        (hx := hxμ₁uBar))
  have hold_min :
      IsMinOn oldSlice problem.primalSet xμ₁uBar :=
    (mem_constrainedArgmin_iff.mp hxμ₁uBar).2
  have hold_strong :
      StrongConvexOn problem.primalSet μ₁ oldSlice :=
    smoothedDualObjectiveMinimand_slice_strongConvexOn
      problem.linearMap
      hμ₁_pos
      problem.smoothPart_convex
      hprimalProx
      (baru : E₂)
  have hold_subquadratic :
      problem.linearMap xμ₁uBar (baru : E₂) +
          problem.smoothPart xμ₁uBar +
          μ₁ * problem.primalProxFunction xμ₁uBar ≤
        problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
          problem.smoothPart xμ₁PlusuBarPlus +
          μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
          (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) := by
    have hquad :
        oldSlice xμ₁uBar +
            (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) ≤
          oldSlice xμ₁PlusuBarPlus := by
      exact hold_strong.quadratic_growth_of_isMinOn_of_mem
        xμ₁uBar.property
        hold_min
        (xμ₁PlusuBarPlus : E₁)
        xμ₁PlusuBarPlus.property
    -- Rewrite the old `μ₁`-slice inequality into the explicit Chapter 6 formula.
    have hquad' :
        problem.linearMap xμ₁uBar (baru : E₂) +
            problem.smoothPart xμ₁uBar +
            μ₁ * problem.primalProxFunction xμ₁uBar +
            (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) ≤
          problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
            problem.smoothPart xμ₁PlusuBarPlus +
            μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus := by
      simpa [oldSlice, smoothedDualObjectiveMinimand_apply, add_assoc, add_left_comm, add_comm]
        using hquad
    linarith
  have hold_total :
      -problem.dualPenalty baru +
          problem.linearMap xμ₁uBar (baru : E₂) +
          problem.smoothPart xμ₁uBar +
          μ₁ * problem.primalProxFunction xμ₁uBar ≤
        -problem.dualPenalty baru +
          problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
          problem.smoothPart xμ₁PlusuBarPlus +
          μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
          (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) := by
    -- Keep the dual term fixed while inserting the old-slice strong-convexity gain.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_left hold_subquadratic (-problem.dualPenalty baru)
  have hgap_subquadratic :
      fμ₂ barx ≤
        -problem.dualPenalty baru +
          problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
          problem.smoothPart xμ₁PlusuBarPlus +
          μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
          (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) := by
    -- Insert the strong-convexity gain before transporting from `\bar u` to `\bar u_+`.
    exact hgap_old.trans hold_total
  have hgap_scaled :
      (1 - τ) * fμ₂ barx ≤
        (1 - τ) *
          (-problem.dualPenalty baru +
            problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
            problem.smoothPart xμ₁PlusuBarPlus +
            μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
            (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ)) := by
    -- Keep the strengthened old excessive-gap estimate at weight `1 - τ`.
    exact mul_le_mul_of_nonneg_left hgap_subquadratic (sub_nonneg.mpr hτ_lt.le)
  have hnew_value :
      extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
          uBarPlus =
        -problem.dualPenalty uBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (uBarPlus : E₂) +
          problem.smoothPart xμ₁PlusuBarPlus +
          μ₁Plus * problem.primalProxFunction xμ₁PlusuBarPlus := by
    -- Evaluate the new dual value at the selected updated primal minimizer.
    simpa using
      (smoothedDualObjective_value_at_selected_argmin
        problem.linearMap
        (hatφ := problem.dualPenalty)
        (d₁ := problem.primalProxFunction)
        (hx := hxμ₁PlusuBarPlus))
  have hdual_conv_neg :=
    updatedDualPenalty_convex_neg
      problem
      (hτ := hτ)
      (hτ_lt := hτ_lt)
      (huBarPlus := huBarPlus)
  let tail : ℝ :=
    problem.linearMap xμ₁PlusuBarPlus (uBarPlus : E₂) +
      problem.smoothPart xμ₁PlusuBarPlus +
      μ₁Plus * problem.primalProxFunction xμ₁PlusuBarPlus -
      (μ₁Plus / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ)
  have hmix :
      (1 - τ) * fμ₂ barx +
          τ *
            (problem.smoothPart xμ₁PlusuBarPlus +
              problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
              problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) ≤
        (1 - τ) *
            (-problem.dualPenalty baru +
              problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
              problem.smoothPart xμ₁PlusuBarPlus +
              μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
              (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ)) +
          τ *
            (problem.smoothPart xμ₁PlusuBarPlus +
              problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
              problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) := by
    -- Add the updated selected-dual term to the strengthened weighted excessive-gap estimate.
    simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hgap_scaled
      (τ *
        (problem.smoothPart xμ₁PlusuBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
          problem.dualPenalty (problem.dualOracleSolver xHat μ₂)))
  have hdual_tail :
      (-(1 - τ) * problem.dualPenalty baru -
            τ * problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
          tail ≤
        -problem.dualPenalty uBarPlus + tail :=
    by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hdual_conv_neg tail
  have hmix_eq :
      (1 - τ) *
          (-problem.dualPenalty baru +
            problem.linearMap xμ₁PlusuBarPlus (baru : E₂) +
            problem.smoothPart xμ₁PlusuBarPlus +
            μ₁ * problem.primalProxFunction xμ₁PlusuBarPlus -
            (μ₁ / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ)) +
        τ *
          (problem.smoothPart xμ₁PlusuBarPlus +
            problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
            problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) =
      (-(1 - τ) * problem.dualPenalty baru -
            τ * problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
          tail := by
    simp [tail, huBarPlus, hμ₁Plus, reduced_primal_smoothing_def]
    ring
  -- Route correction: the closing bridge now stays in the new-slice owner, so the quadratic gain
  -- keeps the sign needed for the final absorption step.
  calc
    (1 - τ) * fμ₂ barx +
        τ *
          (problem.smoothPart xμ₁PlusuBarPlus +
            problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
            problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) ≤
      (-(1 - τ) * problem.dualPenalty baru -
            τ * problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
          tail := by
        exact hmix.trans_eq hmix_eq
    _ ≤ -problem.dualPenalty uBarPlus + tail := hdual_tail
    _ =
        extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
          uBarPlus -
          (μ₁Plus / 2) * ‖(xμ₁PlusuBarPlus : E₁) - xμ₁uBar‖ ^ (2 : ℕ) := by
        rw [hnew_value]
        simp [tail, sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Theorem 6 4: after adding the predicted quadratic remainder, the sign-correct
subquadratic bridge lands exactly on the new dual value. -/
theorem weightedGapAndUpdatedDualSlice_addPredictedQuadratic_le_newDualValue
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {μ₁ : ℝ} {μ₂ : {μ : ℝ // 0 < μ}} {τ L : ℝ}
    {barx : problem.primalSet} {baru uBarPlus : problem.dualSet}
    {xHat xBarPlus xμ₁uBar xμ₁PlusuBarPlus : problem.primalSet}
    (hμ₁_pos : 0 < μ₁)
    (hprimalProx : StrongConvexOn problem.primalSet 1 problem.primalProxFunction)
    (hgap :
      satisfiesExcessiveGapCondition
        problem.primalSet problem.dualSet
        (smoothedPrimalObjective
          problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂)
        (extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁))
        barx baru)
    (hxμ₁uBar :
      (xμ₁uBar : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁ (baru : E₂)))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    (huBarPlus :
      (uBarPlus : E₂) =
        (1 - τ) • (baru : E₂) + τ • (problem.dualOracleSolver xHat μ₂ : E₂))
    {μ₁Plus : ℝ}
    (hμ₁Plus : μ₁Plus = reduced_primal_smoothing μ₁ τ)
    (hxμ₁PlusuBarPlus :
      (xμ₁PlusuBarPlus : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁Plus
            (uBarPlus : E₂)))
    (hquad_absorb :
      (L / 2) * ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) ≤
        (μ₁Plus / 2) * ‖(xμ₁PlusuBarPlus : E₁) - (xμ₁uBar : E₁)‖ ^ (2 : ℕ)) :
    (1 - τ) *
        smoothedPrimalObjective
          problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂ barx +
      τ *
        (problem.smoothPart xμ₁PlusuBarPlus +
          problem.linearMap xμ₁PlusuBarPlus (problem.dualOracleSolver xHat μ₂) -
          problem.dualPenalty (problem.dualOracleSolver xHat μ₂)) +
      (L / 2) * ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) ≤
      extendedRealRealPart
        (smoothedDualObjective
          problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus)
        uBarPlus := by
  have hsubquadratic :=
    weightedGapAndUpdatedDualSlice_le_newDualValue_subquadratic
      problem
      hμ₁_pos
      hprimalProx
      hgap
      hxμ₁uBar
      hτ
      hτ_lt
      huBarPlus
      hμ₁Plus
      hxμ₁PlusuBarPlus
  have hadd := add_le_add hsubquadratic hquad_absorb
  -- The quadratic correction produced by strong convexity cancels with the predicted remainder.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

-- Proof sketch: work over the chapter's structured primal-dual owner so the convexity and
-- implementability assumptions on `Q₁`, `Q₂`, `\hat f`, `\hat φ`, `d₁`, `d₂`, and the oracle
-- data come from one source-facing object, then use the named update points
-- `\hat x`, `\bar u_+`, `\bar x_+` and `μ₁⁺` from the textbook formulas.
/-- Theorem 6 4: let `problem` be the chapter's implementable primal-dual structure, let
`(\bar x, \bar u)` satisfy the excessive-gap condition for the actual Chapter 6 smoothed owners,
let `μ₁ > 0`, assume the source prox terms `d₁` and `d₂` are `1`-strongly convex on `Q₁` and
`Q₂`, and assume both prox terms admit normalized Chapter 6 prox-centers on `Q₁` and `Q₂`; let
`μ₂ > 0`, let
`\hat x = (1 - τ) \bar x + τ x_{μ₁}(\bar u)`,
`\bar u_+ = (1 - τ) \bar u + τ u_{μ₂}(\hat x)`,
`\mu₁^+ = (1 - τ) μ₁`, and
`\bar x_+ = (1 - τ) \bar x + τ x_{μ₁^+}(\bar u_+)`,
where `x_{μ₁}(\bar u)` and `x_{μ₁^+}(\bar u_+)` are the selected canonical primal minimizers and
`u_{μ₂}` is the chapter dual oracle owned by `problem`. Assume also that the canonical Chapter 6
denominator `L₁(\hat f) + μ₂⁻¹ ‖A‖²` is positive. If
`τ² / (1 - τ) ≤ μ₁ / L₁(f_{μ₂})`, written here with the canonical Chapter 6 denominator
`L₁(\hat f) + μ₂⁻¹ ‖A‖²`, then the updated pair
`(\bar x_+, \bar u_+)` again satisfies `satisfiesExcessiveGapCondition` with smoothing
parameters `μ₁⁺` and `μ₂`. -/
theorem satisfiesExcessiveGapCondition_preserved_under_update
    (problem : ImplementablePrimalDualStructure E₁ E₂)
    {μ₁ : ℝ} {μ₂ : {μ : ℝ // 0 < μ}} {τ : ℝ}
    {barx : problem.primalSet} {baru : problem.dualSet}
    (hμ₁_pos : 0 < μ₁)
    (hprimalProx : StrongConvexOn problem.primalSet 1 problem.primalProxFunction)
    (hdualProx : StrongConvexOn problem.dualSet 1 problem.dualProxFunction)
    (hprimalProxCenter :
      ∃ x₀ : E₁, NesterovIsProxCenter problem.primalSet problem.primalProxFunction x₀)
    (hdualProxCenter :
      ∃ u₀ : E₂, NesterovIsProxCenter problem.dualSet problem.dualProxFunction u₀)
    (hgap :
      satisfiesExcessiveGapCondition
        problem.primalSet problem.dualSet
        (smoothedPrimalObjective
          problem.linearMap problem.dualSet
          problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂)
        (extendedRealRealPart
          (smoothedDualObjective
            problem.linearMap problem.primalSet
            problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁))
        barx baru)
    {xμ₁uBar : problem.primalSet}
    (hxμ₁uBar :
      (xμ₁uBar : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁ (baru : E₂)))
    (hτ : 0 < τ) (hτ_lt : τ < 1)
    {xHat : problem.primalSet}
    (hxHat :
      (xHat : E₁) = (1 - τ) • (barx : E₁) + τ • (xμ₁uBar : E₁))
    {uBarPlus : problem.dualSet}
    (huBarPlus :
      (uBarPlus : E₂) =
        (1 - τ) • (baru : E₂) + τ • (problem.dualOracleSolver xHat μ₂ : E₂))
    {μ₁Plus : ℝ}
    (hμ₁Plus : μ₁Plus = reduced_primal_smoothing μ₁ τ)
    {xμ₁PlusuBarPlus : problem.primalSet}
    (hxμ₁PlusuBarPlus :
      (xμ₁PlusuBarPlus : E₁) ∈
        argmin[problem.primalSet]
          (smoothedDualObjectiveMinimand
            problem.linearMap problem.smoothPart problem.primalProxFunction μ₁Plus
            (uBarPlus : E₂)))
    {xBarPlus : problem.primalSet}
    (hxBarPlus :
      (xBarPlus : E₁) = (1 - τ) • (barx : E₁) + τ • (xμ₁PlusuBarPlus : E₁))
    (hstep_denom_pos :
      0 <
        ((problem.smoothPartGradientLipschitzConstant +
            Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ))
    (hstep :
      τ ^ (2 : ℕ) / (1 - τ) ≤
        μ₁ /
          ((problem.smoothPartGradientLipschitzConstant +
              Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ)) :
    satisfiesExcessiveGapCondition
      problem.primalSet problem.dualSet
      (smoothedPrimalObjective
        problem.linearMap problem.dualSet
        problem.smoothPart problem.dualPenalty problem.dualProxFunction μ₂)
      (extendedRealRealPart
        (smoothedDualObjective
          problem.linearMap problem.primalSet
          problem.smoothPart problem.dualPenalty problem.primalProxFunction μ₁Plus))
      xBarPlus
      uBarPlus := by
  let L : ℝ :=
    ((problem.smoothPartGradientLipschitzConstant +
      Real.toNNReal ((1 / (μ₂ : ℝ)) * ‖problem.linearMap‖ ^ (2 : ℕ))) : ℝ)
  have _ : 0 ≤ problem.primalProxFunction xμ₁PlusuBarPlus := by
    -- Record the primal prox-center normalization as the matching primal-side nonnegativity fact.
    exact proxFunction_nonneg_of_proxCenter hprimalProxCenter xμ₁PlusuBarPlus.property
  have hdualProx_nonneg :
      0 ≤ problem.dualProxFunction (problem.dualOracleSolver xHat μ₂) := by
    -- The prox-center normalization gives the nonnegativity side condition for the dual oracle.
    exact proxFunction_nonneg_of_proxCenter hdualProxCenter
      (problem.dualOracleSolver xHat μ₂).property
  have hdisp :
      (xBarPlus : E₁) - xHat =
        τ • ((xμ₁PlusuBarPlus : E₁) - (xμ₁uBar : E₁)) :=
    updated_points_displacement hxHat hxBarPlus
  have hquad_absorb :
      (L / 2) * ‖(xBarPlus : E₁) - xHat‖ ^ (2 : ℕ) ≤
        (μ₁Plus / 2) * ‖(xμ₁PlusuBarPlus : E₁) - (xμ₁uBar : E₁)‖ ^ (2 : ℕ) := by
    -- The step-size hypothesis absorbs the quadratic upper-model remainder.
    simpa [L, norm_sub_rev] using
      (stepSizeAbsorbsPredictedQuadraticError
        (hτ := hτ)
        (hτ_lt := hτ_lt)
        (hL_pos := hstep_denom_pos)
        (hdisp := hdisp)
        (hμ₁Plus := hμ₁Plus)
        (hstep := hstep))
  have hupper_bridge :=
    predictedUpperModel_le_weightedGapAndUpdatedDualSlice
      problem
      hdualProx
      hτ
      hτ_lt
      hdualProx_nonneg
      hxBarPlus
  have hslice_bridge :=
    weightedGapAndUpdatedDualSlice_addPredictedQuadratic_le_newDualValue
      problem
      hμ₁_pos
      hprimalProx
      hgap
      hxμ₁uBar
      hτ
      hτ_lt
      huBarPlus
      hμ₁Plus
      hxμ₁PlusuBarPlus
      hquad_absorb
  -- Route correction: the final chain now lands directly on the new dual value, so the quadratic
  -- remainder is absorbed before the last transitivity step instead of after an old-slice detour.
  exact hupper_bridge.trans hslice_bridge

end Main

end Theorem

end
