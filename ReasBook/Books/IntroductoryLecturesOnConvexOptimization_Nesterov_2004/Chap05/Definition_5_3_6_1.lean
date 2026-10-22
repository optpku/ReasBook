/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_5_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement

noncomputable section

universe u

section CentralPath

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The penalty objective `z ↦ t ⟪c, z⟫ + F(z)` used to define a central path for minimizing the
linear functional `⟪c, z⟫` over the barrier domain of `F`. -/
def centralPathPenaltyObjective
    (c : E) (F : E → ℝ) (t : ℝ) : E → ℝ :=
  fun z ↦ t * inner ℝ c z + F z

-- Proof sketch: unfold `centralPathPenaltyObjective`.
/-- Evaluating `centralPathPenaltyObjective c F t` recovers the penalty formula
`t ⟪c, z⟫ + F(z)`. -/
theorem centralPathPenaltyObjective_apply
    (c : E) (F : E → ℝ) (t : ℝ) (z : E) :
    centralPathPenaltyObjective c F t z = t * inner ℝ c z + F z :=
  rfl

/-- A trajectory indexed by `t ≥ 0` is a central path for minimizing `⟪c, z⟫` over `dom` with
barrier `F` when each point minimizes the corresponding penalty objective. -/
def IsCentralPath
    (dom : Set E) (c : E) (F : E → ℝ) (zStar : Set.Ici (0 : ℝ) → dom) : Prop :=
  ∀ t : Set.Ici (0 : ℝ),
    IsMinOn (centralPathPenaltyObjective c F t) dom (zStar t : E)

-- Proof sketch: unfold `IsCentralPath`.
/-- Expanding `IsCentralPath dom c F zStar` states that `zStar t` minimizes the penalty objective
for every nonnegative path parameter `t`. -/
theorem isCentralPath_iff
    (dom : Set E) (c : E) (F : E → ℝ) (zStar : Set.Ici (0 : ℝ) → dom) :
    IsCentralPath dom c F zStar ↔
      ∀ t : Set.Ici (0 : ℝ),
        IsMinOn (centralPathPenaltyObjective c F t) dom (zStar t : E) :=
  Iff.rfl

end CentralPath

section FunctionalConstraint

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
Definition 5.3.6.1 lies in the Chapter 5 self-concordant-barrier / path-following domain.

Sampled owner declarations in this domain:
* `StoppedIntermediateSelfConcordantNewtonMethod` in `Definition_5_3_5_1`, the owner for the
  analytic-center preprocessing stage;
* `IsCentralPath` in this file, the owner predicate for the continuous path-following stages;
* `IsMinOn` in mathlib and `Definition_5_3_3`, the canonical owner for exact analytic centers;
* `NewtonDecrement.ofPosDefMem` in `Definition_5_0_24`, the canonical owner for
  approximate-centering bounds on a positive-definite Hessian domain.

Best owner abstraction:
* source-facing: the functional-constraint path-following method with its two branch shapes;
* core/canonical: the inherited analytic-center preprocessing owner, used only through the
  stage-compatibility facts that connect it to the auxiliary and final central paths;
* bridge/view: the branch-sign hypotheses, the exact reduced-center time formula, and the
  approximate-centering statement at the start of the final path.

Primitive data:
* the canonical slack parameter `α = ⟪d, z₀⟫ + Δ`;
* in each branch, the source-facing central paths together with the fact that their initial points
  come from a stopped intermediate Newton preprocessing method.

Derived API:
* the starting-point compatibility between adjacent stages;
* existence of an exact reduced analytic center on the auxiliary central path;
* approximate-centering of the reduced endpoint that starts the final central path, read through
  the reduced-barrier Newton decrement.

The branch owners below therefore avoid separate public control fields for step sizes, avoid
primitive witness fields for chosen times or centers, and do not package the internal update
parameter of an unrelated path-following scheme into the public owner surface. Those remain
theorem-shaped bridge facts derived from the owner data.
-/

/-- The canonical slack parameter `α = ⟪d, z₀⟫ + Δ` attached to the source data of
Definition 5.3.6.1. -/
def functionalConstraintAlpha
    (d z0 : E) (Δ : ℝ) : ℝ :=
  inner ℝ d z0 + Δ

@[simp] theorem functionalConstraintAlpha_def
    (d z0 : E) (Δ : ℝ) :
    functionalConstraintAlpha d z0 Δ = inner ℝ d z0 + Δ :=
  rfl

/-- The shifted feasible set `S(α)` appearing in the preprocessing step for the additional
functional constraint `⟪d, z⟫ ≤ 0`; it is the portion of `S` where the logarithmic slack
`α - ⟪d, z⟫` stays positive. -/
def functionalConstraintAuxiliarySet (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ S ∧ inner ℝ d z < α}

-- Proof sketch: unfold `functionalConstraintAuxiliarySet`; membership in the defining set-builder
-- is exactly the conjunction `z ∈ S ∧ ⟪d, z⟫ < α`.
/-- Membership in `functionalConstraintAuxiliarySet S d α` means belonging to `S` and satisfying
the strict slack inequality `⟪d, z⟫ < α`. -/
theorem mem_functionalConstraintAuxiliarySet_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintAuxiliarySet S d α ↔
      z ∈ S ∧ inner ℝ d z < α :=
  Iff.rfl

/-- The auxiliary barrier `F(z) - log (α - ⟪d, z⟫)` on the shifted set `S(α)`. -/
def functionalConstraintAuxiliaryBarrier
    (F : E → ℝ) (d : E) (α : ℝ) : E → ℝ :=
  fun z ↦ F z - Real.log (α - inner ℝ d z)

-- Proof sketch: unfold `functionalConstraintAuxiliaryBarrier`.
/-- Evaluating `functionalConstraintAuxiliaryBarrier F d α` reproduces the textbook formula
`F(z) - log (α - ⟪d, z⟫)`. -/
theorem functionalConstraintAuxiliaryBarrier_apply
    (F : E → ℝ) (d z : E) (α : ℝ) :
    functionalConstraintAuxiliaryBarrier F d α z =
      F z - Real.log (α - inner ℝ d z) :=
  rfl

/-- The reduced feasible set `{z ∈ S(α) | ⟪d, z⟫ ≤ 0}` from Definition 5.3.6.1. -/
def functionalConstraintReducedSet (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ functionalConstraintAuxiliarySet S d α ∧ inner ℝ d z ≤ 0}

-- Proof sketch: unfold `functionalConstraintReducedSet` and then use
-- `mem_functionalConstraintAuxiliarySet_iff`.
/-- Membership in `functionalConstraintReducedSet S d α` means `z ∈ S`, `⟪d, z⟫ < α`, and
`⟪d, z⟫ ≤ 0`. -/
theorem mem_functionalConstraintReducedSet_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintReducedSet S d α ↔
      z ∈ S ∧ inner ℝ d z < α ∧ inner ℝ d z ≤ 0 := by
  constructor
  · rintro ⟨hz, hneg⟩
    exact ⟨hz.1, hz.2, hneg⟩
  · rintro ⟨hzS, hzAlpha, hzNeg⟩
    exact ⟨⟨hzS, hzAlpha⟩, hzNeg⟩

/-- The strict barrier domain inside the reduced feasible set on which the logarithmic term
`-log (-⟪d, z⟫)` is defined. -/
def functionalConstraintReducedBarrierDomain (S : Set E) (d : E) (α : ℝ) : Set E :=
  {z | z ∈ functionalConstraintAuxiliarySet S d α ∧ inner ℝ d z < 0}

-- Proof sketch: unfold `functionalConstraintReducedBarrierDomain` and then use
-- `mem_functionalConstraintAuxiliarySet_iff`.
/-- Membership in `functionalConstraintReducedBarrierDomain S d α` means `z ∈ S`,
`⟪d, z⟫ < α`, and `⟪d, z⟫ < 0`. -/
theorem mem_functionalConstraintReducedBarrierDomain_iff
    {S : Set E} {d z : E} {α : ℝ} :
    z ∈ functionalConstraintReducedBarrierDomain S d α ↔
      z ∈ S ∧ inner ℝ d z < α ∧ inner ℝ d z < 0 := by
  constructor
  · rintro ⟨hz, hneg⟩
    exact ⟨hz.1, hz.2, hneg⟩
  · rintro ⟨hzS, hzAlpha, hzNeg⟩
    exact ⟨⟨hzS, hzAlpha⟩, hzNeg⟩

/-- Every point of the strict reduced barrier domain belongs to the closed reduced feasible set. -/
theorem functionalConstraintReducedBarrierDomain_subset_reducedSet
    (S : Set E) (d : E) (α : ℝ) :
    functionalConstraintReducedBarrierDomain S d α ⊆
      functionalConstraintReducedSet S d α := by
  intro z hz
  rw [mem_functionalConstraintReducedBarrierDomain_iff] at hz
  rw [mem_functionalConstraintReducedSet_iff]
  exact ⟨hz.1, hz.2.1, le_of_lt hz.2.2⟩

/-- For the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` with `Δ > 0`, the source point `z₀`
lies in `S(α)`. -/
theorem z0_mem_functionalConstraintAuxiliarySet_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ) :
    (z0 : E) ∈ functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintAuxiliarySet_iff, functionalConstraintAlpha]
  exact ⟨z0.2, by linarith⟩

/-- If the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive, then `z₀` already lies in
the reduced domain. -/
theorem z0_mem_functionalConstraintReducedSet_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) :
    (z0 : E) ∈
      functionalConstraintReducedSet S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintReducedSet_iff, functionalConstraintAlpha]
  have hα : inner ℝ d (z0 : E) + Δ ≤ 0 := by
    simpa [functionalConstraintAlpha] using alpha_nonpos
  exact ⟨z0.2, by linarith, by linarith⟩

/-- If the canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive, then `z₀` lies in the
strict reduced barrier domain as well. -/
theorem z0_mem_functionalConstraintReducedBarrierDomain_alpha
    {S : Set E} (d : E) {z0 : S} {Δ : ℝ} (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) :
    (z0 : E) ∈
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ) := by
  rw [mem_functionalConstraintReducedBarrierDomain_iff, functionalConstraintAlpha]
  have hα : inner ℝ d (z0 : E) + Δ ≤ 0 := by
    simpa [functionalConstraintAlpha] using alpha_nonpos
  exact ⟨z0.2, by linarith, by linarith⟩

/-- The barrier obtained from `F` by adding the logarithmic slack barriers for
`⟪d, z⟫ < α` and `⟪d, z⟫ < 0`. -/
def functionalConstraintReducedBarrier
    (F : E → ℝ) (d : E) (α : ℝ) : E → ℝ :=
  fun z ↦ functionalConstraintAuxiliaryBarrier F d α z - Real.log (-inner ℝ d z)

-- Proof sketch: unfold `functionalConstraintReducedBarrier` and
-- `functionalConstraintAuxiliaryBarrier`.
/-- Evaluating `functionalConstraintReducedBarrier F d α` gives the textbook barrier
`F(z) - log (α - ⟪d, z⟫) - log (-⟪d, z⟫)`. -/
theorem functionalConstraintReducedBarrier_apply
    (F : E → ℝ) (d z : E) (α : ℝ) :
    functionalConstraintReducedBarrier F d α z =
      F z - Real.log (α - inner ℝ d z) - Real.log (-inner ℝ d z) :=
  rfl

variable [FiniteDimensional ℝ E]

private def functionalConstraintSlackMap (d : E) (α : ℝ) : E →ᴬ[ℝ] ℝ :=
  (-innerSL ℝ d).toContinuousAffineMap +ᵥ ContinuousAffineMap.const ℝ E α

omit [FiniteDimensional ℝ E] in
@[simp] private theorem functionalConstraintSlackMap_apply (d z : E) (α : ℝ) :
    functionalConstraintSlackMap d α z = α - inner ℝ d z := by
  simp [functionalConstraintSlackMap, innerSL_apply_apply]
  ring

private def functionalConstraintNegInnerMap (d : E) : E →ᴬ[ℝ] ℝ :=
  (-innerSL ℝ d).toContinuousAffineMap

omit [FiniteDimensional ℝ E] in
@[simp] private theorem functionalConstraintNegInnerMap_apply (d z : E) :
    functionalConstraintNegInnerMap d z = -inner ℝ d z := by
  simp [functionalConstraintNegInnerMap, innerSL_apply_apply]

instance functionalConstraintAuxiliaryBarrier_isSelfConcordantBarrierOnWith
    (S : Set E) (d : E) (α : ℝ) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] :
    IsSelfConcordantBarrierOnWith
      (functionalConstraintAuxiliarySet S d α)
      (ν + 1)
      (functionalConstraintAuxiliaryBarrier F d α) := by
  have hdom :
      functionalConstraintAuxiliarySet S d α =
        S ∩ ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext z
    simp [functionalConstraintAuxiliarySet, Set.preimage]
  have hbarrier :
      functionalConstraintAuxiliaryBarrier F d α =
        F + ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := by
    funext z
    simp [functionalConstraintAuxiliaryBarrier, sub_eq_add_neg]
  letI :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := by
    simpa using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap
        (functionalConstraintSlackMap d α))
  have hS : IsSelfConcordantBarrierOnWith S ν F := inferInstance
  have hslack :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintSlackMap d α) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintSlackMap d α) := inferInstance
  simpa [hdom, hbarrier] using
    hS.add hslack

instance functionalConstraintReducedBarrier_isSelfConcordantBarrierOnWith
    (S : Set E) (d : E) (α : ℝ) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] :
    IsSelfConcordantBarrierOnWith
      (functionalConstraintReducedBarrierDomain S d α)
      (ν + 2)
      (functionalConstraintReducedBarrier F d α) := by
  have hdom :
      functionalConstraintReducedBarrierDomain S d α =
        functionalConstraintAuxiliarySet S d α ∩
          ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ)) := by
    ext z
    simp [functionalConstraintReducedBarrierDomain, functionalConstraintAuxiliarySet, Set.preimage]
  have hbarrier :
      functionalConstraintReducedBarrier F d α =
        functionalConstraintAuxiliaryBarrier F d α +
          ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := by
    funext z
    simp [functionalConstraintReducedBarrier, sub_eq_add_neg, functionalConstraintNegInnerMap]
  letI :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := by
    simpa using
      (negLog_isSelfConcordantBarrierOnWith_nonnegativeRay.comp_continuousAffineMap
        (functionalConstraintNegInnerMap d))
  have hnu : ν + 1 + 1 = ν + 2 := by
    ext
    norm_num [add_assoc]
  have haux :
      IsSelfConcordantBarrierOnWith
        (functionalConstraintAuxiliarySet S d α)
        (ν + 1)
        (functionalConstraintAuxiliaryBarrier F d α) := inferInstance
  have hslack :
      IsSelfConcordantBarrierOnWith
        ((functionalConstraintNegInnerMap d) ⁻¹' Set.Ioi (0 : ℝ))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ functionalConstraintNegInnerMap d) := inferInstance
  simpa [hdom, hbarrier, hnu] using
    haux.add hslack

section PathFollowingScheme

variable (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
variable [IsSelfConcordantBarrierOnWith S ν F]
variable (z0 : S) (β Δ : ℝ)

/-- The fallback branch for the additional functional constraint `⟪d, z⟫ ≤ 0`, used when the
canonical slack parameter `α = ⟪d, z₀⟫ + Δ` is nonpositive: first run the Chapter 5
analytic-center scheme on the reduced barrier starting from the canonical source point `z₀`, then
follow the final `c`-central path on the reduced domain. -/
structure NonpositiveFunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0) where
  /-- Stage 2 follows the `c`-central path for the reduced problem. -/
  finalCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-2 trajectory is a central path for minimizing `⟪c, z⟫` over the reduced
  feasible set. -/
  finalCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      c
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      finalCentralPath
  /-- The reduced-domain analytic-center preprocessing method from Definition 5.3.5.3, started at
  the canonical source point `z₀`. -/
  preprocessing :
    StoppedIntermediateSelfConcordantNewtonMethod
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      ⟨(z0 : E), z0_mem_functionalConstraintReducedBarrierDomain_alpha d delta_pos alpha_nonpos⟩
      β
  /-- The initial point of the final path is the stopping iterate of the preprocessing stage. -/
  finalCentralPath_zero_eq_preprocessing :
    (finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E) =
      preprocessing.toMethod preprocessing.stopIndex

/-- The positive-`α` branch for the additional functional constraint `⟪d, z⟫ ≤ 0`: first run
the Chapter 5 analytic-center scheme on `S(α)`, then follow the auxiliary `d`-central path to
the reduced set, and finally follow the `c`-central path on that reduced domain. -/
structure PositiveFunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (alpha_pos : 0 < functionalConstraintAlpha d z0 Δ) where
  /-- Stage 2 follows the `d`-central path for the auxiliary barrier on `S(α)`. -/
  auxiliaryCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-2 trajectory is a central path for the penalty objective
  `z ↦ t ⟪d, z⟫ + F(z) - log (α - ⟪d, z⟫)`. -/
  auxiliaryCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintAuxiliarySet S d (functionalConstraintAlpha d z0 Δ))
      d
      (functionalConstraintAuxiliaryBarrier F d (functionalConstraintAlpha d z0 Δ))
      auxiliaryCentralPath
  /-- The auxiliary analytic-center preprocessing method from Definition 5.3.5.3, started from
  the canonical source point `z₀`. -/
  preprocessing :
    StoppedIntermediateSelfConcordantNewtonMethod
      (functionalConstraintAuxiliaryBarrier F d (functionalConstraintAlpha d z0 Δ))
      ⟨(z0 : E), z0_mem_functionalConstraintAuxiliarySet_alpha d delta_pos⟩
      β
  /-- The initial point of the auxiliary central path is the stopping iterate of the preprocessing
  stage. -/
  auxiliaryCentralPath_zero_eq_preprocessing :
    (auxiliaryCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E) =
      preprocessing.toMethod preprocessing.stopIndex
  /-- The distinguished stage-2 point `z_*`, viewed in the source-facing reduced feasible set
  `{z ∈ S(α) | ⟪d, z⟫ ≤ 0}`. -/
  zStar :
    functionalConstraintReducedSet S d (functionalConstraintAlpha d z0 Δ)
  /-- The distinguished stage-2 point `z_*` lies in the strict reduced barrier domain. -/
  zStar_mem_barrierDomain :
    (zStar : E) ∈
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The distinguished stage-2 time `t_*`. -/
  tStar : Set.Ici (0 : ℝ)
  /-- The distinguished point `z_*` lies on the auxiliary central path at time `t_*`. -/
  zStar_on_auxiliaryPath :
    (auxiliaryCentralPath tStar : E) = zStar
  /-- The distinguished point `z_*` is the exact analytic center of the reduced barrier domain. -/
  zStar_isAnalyticCenter :
    IsMinOn
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      (zStar : E)
  /-- The distinguished time `t_*` satisfies the source formula
  `t_* = -1 / ⟪d, z_*⟫`. -/
  tStar_eq :
    (tStar : ℝ) = -1 / inner ℝ d (zStar : E)
  /-- Stage 3 follows the `c`-central path for the reduced problem. -/
  finalCentralPath :
    Set.Ici (0 : ℝ) →
      functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ)
  /-- The stage-3 trajectory is a central path for minimizing `⟪c, z⟫` over the reduced
  feasible set. -/
  finalCentralPath_isCentral :
    IsCentralPath
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      c
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
      finalCentralPath
  /-- The stage-2 endpoint that starts the final central path lies on the auxiliary central
  path. -/
  finalCentralPath_zero_on_auxiliaryPath :
    ∃ t : Set.Ici (0 : ℝ),
      (auxiliaryCentralPath t : E) = (finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩ : E)
  /-- The reduced barrier on its strict domain carries the canonical positive-definite-Hessian
  owner needed for reduced-domain Newton decrement. -/
  reducedBarrier_hasPositiveDefiniteHessianOn :
    HasPositiveDefiniteHessianOn
      (functionalConstraintReducedBarrierDomain S d (functionalConstraintAlpha d z0 Δ))
      (functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ))
  /-- The starting point of the final path is `β`-approximately centered for the reduced barrier,
  expressed directly through the reduced-domain Newton decrement. -/
  finalCentralPath_zero_isApproximate :
    let z := finalCentralPath ⟨0, Set.mem_Ici.mpr le_rfl⟩
    letI := reducedBarrier_hasPositiveDefiniteHessianOn
    λ[functionalConstraintReducedBarrier F d (functionalConstraintAlpha d z0 Δ); (z : E) | z.2] ≤
      β

/-- Definition 5.3.6.1: for the problem `min {(c, z) : z ∈ S, ⟪d, z⟫ ≤ 0}`, choose
`α = ⟪d, z₀⟫ + Δ` with `Δ > 0`; if `α ≤ 0`, the method falls back to the two-stage process of
Definition 5.3.5.3, and if `α > 0`, it first finds a `β`-approximate analytic center of `S(α)`,
then follows the `d`-central path to a `β`-approximate analytic center of the reduced set
`{z ∈ S(α) | ⟪d, z⟫ ≤ 0}`, and finally follows the `c`-central path for the reduced problem. -/
inductive FunctionalConstraintPathFollowingScheme
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ)
    (delta_pos : 0 < Δ) : Type u where
  | fallback
      {alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0}
      (scheme :
        NonpositiveFunctionalConstraintPathFollowingScheme
          S c d F ν z0 β Δ delta_pos alpha_nonpos) :
      FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos
  | positive
      {alpha_pos : 0 < functionalConstraintAlpha d z0 Δ}
      (scheme :
        PositiveFunctionalConstraintPathFollowingScheme
          S c d F ν z0 β Δ delta_pos alpha_pos) :
      FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos

end PathFollowingScheme

namespace FunctionalConstraintPathFollowingScheme

/-- Every functional-constraint path-following scheme is either the fallback branch, determined by
the actual nonpositive-`α` two-stage process, or the positive three-stage branch. -/
theorem eq_fallback_or_eq_positive
    (S : Set E) (c d : E) (F : E → ℝ) (ν : NNReal)
    [IsSelfConcordantBarrierOnWith S ν F] (z0 : S) (β Δ : ℝ) (delta_pos : 0 < Δ)
    (scheme : FunctionalConstraintPathFollowingScheme S c d F ν z0 β Δ delta_pos) :
    (∃ (alpha_nonpos : functionalConstraintAlpha d z0 Δ ≤ 0)
        (fallbackScheme :
          NonpositiveFunctionalConstraintPathFollowingScheme
            S c d F ν z0 β Δ delta_pos alpha_nonpos),
        scheme = fallback fallbackScheme) ∨
      ∃ (alpha_pos : 0 < functionalConstraintAlpha d z0 Δ)
        (positiveScheme :
          PositiveFunctionalConstraintPathFollowingScheme
            S c d F ν z0 β Δ delta_pos alpha_pos),
        scheme = positive positiveScheme := by
  cases scheme with
  | fallback fallbackScheme =>
      exact Or.inl ⟨_, fallbackScheme, rfl⟩
  | positive positiveScheme =>
      exact Or.inr ⟨_, positiveScheme, rfl⟩

end FunctionalConstraintPathFollowingScheme

end FunctionalConstraint

end
