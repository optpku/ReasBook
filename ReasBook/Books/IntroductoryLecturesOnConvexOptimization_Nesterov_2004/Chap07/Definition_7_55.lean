/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/-
Definition 7.55 lies in Chapter 7's barrier-regularized affine-maximization domain.

Sampled owner-style declarations:
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for `EReal`-valued maximal
  values of real objectives on feasible sets;
- `maximalValueOn_eq_sSup_image` in `Chap07/Definition_7_56`, the canonical expansion theorem for
  that owner;
- `affineBarrierRegularizedPayoff` and `affineBarrierRegularizedPayoff_def` in `Chap07/Lemma_7_11`,
  the source-facing payoff surface specialized by this definition.

Best owner abstraction:
- source-facing: the textbook barrier-regularized value `ℓ⋆(β)`;
- core/canonical: `maximalValueOn`;
- bridge/view: the specialization to `hatP ∩ interior Q` and
  `affineBarrierRegularizedPayoff x0 β ℓ F`, together with the explicit `sSup` formula.

Primitive data:
- the sets `hatP` and `Q`;
- the barrier term `F`, base point `x₀`, affine functional `ℓ`, and parameter `β`.

Derived API:
- the direct specialization of `maximalValueOn` to the barrier-regularized payoff;
- the `sSup` expansion and the two basic comparison lemmas below.

Definition 7.55 does not introduce a second maximal-value owner: the mathematical content is the
existing Chapter 7 owner `maximalValueOn` evaluated at the barrier-regularized affine payoff on
the strict feasible set. The refinement therefore deletes the duplicate wrapper and keeps only the
source-specific companion theorems on that canonical owner.
-/

variable (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ)

/-- Definition 7.55: the barrier-regularized maximal affine value `ℓ⋆(β)` is the Chapter 7
canonical maximal value of the payoff `x ↦ ℓ x - β (F x - F x₀)` over the strict feasible set
`hatP ∩ interior Q`. -/
abbrev affineBarrierRegularizedMaximalValue : EReal :=
  maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)

/- Definition 7.55 uses the Chapter 7 maximal-value owner directly at the barrier-regularized
affine payoff on the strict feasible set `hatP ∩ interior Q`. -/
set_option linter.hashCommand false in
#check maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)

section

variable {hatP Q : Set E} {F : E → ℝ} {x0 : E} {ℓ : AffineMap ℝ E ℝ} {β : ℝ}

-- Proof sketch: expand `maximalValueOn` by
-- `maximalValueOn_eq_sSup_image` and the payoff by `affineBarrierRegularizedPayoff_def`.
/-- Expanding the canonical maximal-value owner at the barrier-regularized affine payoff gives the
supremum formula defining the textbook value `ℓ⋆(β)` on `P₀`. -/
theorem maximalValueOn_affineBarrierRegularizedPayoff_eq_sSup_image
    (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ) :
    maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F) =
      sSup
        ((fun x : E ↦ ((ℓ x - β * (F x - F x0) : ℝ) : EReal)) ''
          (hatP ∩ interior Q)) := by
  -- Expand the canonical owner, then unfold the source-facing payoff once.
  simpa [affineBarrierRegularizedPayoff_def] using
    maximalValueOn_eq_sSup_image (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F)

-- Proof sketch: evaluate the defining supremum at the feasible point `x₀`; the barrier term
-- vanishes there because `F x0 - F x0 = 0`.
/-- If the base point `x₀` lies in the strict feasible set `P₀`, then the canonical maximal value
of the barrier-regularized payoff is at least the textbook base value `ℓ₀ = ℓ(x₀)`. -/
theorem baseAffineValue_le_maximalValueOn_affineBarrierRegularizedPayoff
    (hatP Q : Set E) (F : E → ℝ) (x0 : E) (ℓ : AffineMap ℝ E ℝ) (β : ℝ)
    (hx0 : x0 ∈ hatP ∩ interior Q) :
    (ℓ x0 : EReal) ≤
      maximalValueOn (hatP ∩ interior Q) (affineBarrierRegularizedPayoff x0 β ℓ F) := by
  -- Rewrite the maximal value as the supremum of the explicit payoff image.
  rw [maximalValueOn_affineBarrierRegularizedPayoff_eq_sSup_image]
  -- Evaluate the supremum at the feasible base point `x₀`.
  have hx0_image :
      ((ℓ x0 - β * (F x0 - F x0) : ℝ) : EReal) ∈
        (fun x : E ↦ ((ℓ x - β * (F x - F x0) : ℝ) : EReal)) '' (hatP ∩ interior Q) :=
    Set.mem_image_of_mem
      (fun x : E ↦ ((ℓ x - β * (F x - F x0) : ℝ) : EReal))
      hx0
  -- The barrier correction vanishes at `x₀`, so this image point is exactly `ℓ x₀`.
  simpa using (le_sSup hx0_image)

-- Proof sketch: the `β = 0` specialization of Definition 7.55 is just the ordinary affine
-- objective `ℓ`; then apply `maximalValueOn_eq_of_closure_eq` with `P₀ = hatP ∩ interior Q` and
-- `P = hatP ∩ Q`.
/-- When the regularization parameter is `0`, Definition 7.55 reduces to the ordinary maximal
value of `ℓ`; if `hatP ∩ Q` is the closure of `hatP ∩ interior Q` and `ℓ` is continuous there,
the two owner values coincide. -/
theorem maximalValueOn_affineBarrierRegularizedPayoff_zero
    (hatP Q : Set E) (ℓ : AffineMap ℝ E ℝ)
    (hℓ : ContinuousOn ℓ (hatP ∩ Q))
    (hclosure : closure (hatP ∩ interior Q) = hatP ∩ Q) :
    maximalValueOn (hatP ∩ interior Q) ℓ =
      maximalValueOn (hatP ∩ Q) ℓ := by
  -- At `β = 0`, the source-facing value is just the closure-invariant owner for `ℓ`.
  simpa using maximalValueOn_eq_of_closure_eq hclosure hℓ

end

end
