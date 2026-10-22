/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin ConvexAnalysis WithTopConvexAnalysis

universe u v w

section MinimizerSelection

variable {P : Type u} {S : Type v}

/- This item belongs to the Chapter 7 saddle-representation / selected-subgradient domain.

Relevant owner declarations:
- `SaddlePointRepresentation` in `Definition_7_59`;
- `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`;
- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` in
  `Chap03/Theorem_3_1_25`.

The source-facing auxiliary data are:
- a minimizing branch `w : P → S` for the saddle slices `Ψ(x, ·)`;
- a chosen first-argument saddle subgradient evaluated along that branch.

The canonical owner remains `SaddlePointRepresentation`; the minimizer-selection predicate and the
selected subgradient field are thin source-facing layers over that owner. -/

namespace SaddlePointRepresentation

/-- A function `w : P → S` is a barrier-subproblem minimizer selection for a saddle-point
representation when each chosen point `w x` belongs to the canonical minimizing fiber of the
saddle slice `Ψ(x, ·)`. -/
def IsBarrierSubproblemMinimizerSelection
    (representation : SaddlePointRepresentation P S) (w : P → S) : Prop :=
  ∀ x : P, w x ∈ argmin[Set.univ] (representation.saddleFunction x)

namespace IsBarrierSubproblemMinimizerSelection

variable {representation : SaddlePointRepresentation P S} {w : P → S}

/-- Evaluating a barrier-subproblem minimizer selection at `x` yields a point of the canonical
argmin set of the saddle slice `Ψ(x, ·)`. -/
-- Proof sketch: unfold `IsBarrierSubproblemMinimizerSelection`.
theorem apply
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    w x ∈ argmin[Set.univ] (representation.saddleFunction x) := by
  -- Evaluating the selection predicate at `x` is exactly the desired argmin membership.
  exact hw x

/-- The selected point `w x` minimizes the saddle slice `Ψ(x, ·)` on the whole parameter space
`S`. -/
-- Proof sketch: rewrite argmin membership with `mem_constrainedArgmin_iff`.
theorem isMinOn
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    IsMinOn (representation.saddleFunction x) Set.univ (w x) := by
  -- Unpack argmin membership into the canonical minimizing predicate.
  exact (mem_constrainedArgmin_iff.mp (hw.apply x)).2

/-- Along a minimizing branch, the represented objective value equals the saddle value at the
selected minimizer. -/
-- Proof sketch: compare the least-value witness `representation.objective_isLeast x` with the
-- least-value witness induced by `hw.isMinOn x`.
theorem objective_eq_saddleFunction
    (hw : representation.IsBarrierSubproblemMinimizerSelection w) (x : P) :
    representation x = representation.saddleFunction x (w x) := by
  rcases (representation.objective_isLeast x).1 with ⟨s, hs⟩
  -- The selected minimizer cannot exceed any realized saddle value, in particular the attained
  -- least value recorded by `objective_isLeast`.
  have h_selected_le : representation.saddleFunction x (w x) ≤ representation x := by
    rw [← hs]
    exact hw.isMinOn x (by simp : s ∈ Set.univ)
  -- The represented objective is a lower bound for every saddle value in the slice.
  have h_objective_le : representation x ≤ representation.saddleFunction x (w x) :=
    (representation.objective_isLeast x).2 ⟨w x, rfl⟩
  exact le_antisymm h_objective_le h_selected_le

end IsBarrierSubproblemMinimizerSelection

end SaddlePointRepresentation

end MinimizerSelection

section SelectedSubgradient

variable {P : Type u} {S : Type v}

namespace SaddlePointRepresentation

/-- The selected field attached to Definition 7.60 sends `x` to the chosen first-argument saddle
subgradient `∇₁Ψ(x, w(x))`. -/
def barrierSubgradientSelection
    (firstSubgradient : P → S → P) (w : P → S) : P → P :=
  fun x ↦ firstSubgradient x (w x)

/-- Evaluating `barrierSubgradientSelection` at `x` returns the chosen first-argument saddle
subgradient at `(x, w(x))`. -/
-- Proof sketch: unfold `barrierSubgradientSelection`.
theorem barrierSubgradientSelection_apply
    (firstSubgradient : P → S → P) (w : P → S) (x : P) :
    barrierSubgradientSelection firstSubgradient w x = firstSubgradient x (w x) := by
  -- This is just evaluation of the defining function.
  rfl

section Transfer

/-- The canonical `EReal` partial-infimum projection attached to a saddle-point representation. -/
private def saddlePartialInfProjection
    (representation : SaddlePointRepresentation P S) : P → EReal :=
  partialInfProjection (Set.univ : Set (P × S))
    (withTopToEReal ∘ fun z : P × S ↦
      ((representation.saddleFunction z.1 z.2 : ℝ) : WithTop ℝ))

/-- The image of the `x`-fiber under a two-variable function is the range of its `x`-slice. -/
-- Proof sketch: unpack membership in the image and in the range and rewrite by the equation
-- `z.1 = x`.
private theorem image_saddleFiber_eq_range
    {α : Type w} (f : P → S → α) (x : P) :
    (fun z : P × S ↦ f z.1 z.2) '' {z : P × S | z.1 = x} = Set.range (f x) := by
  ext a
  constructor
  · rintro ⟨⟨x', s⟩, hx', rfl⟩
    have hx' : x' = x := by
      simpa using hx'
    subst x'
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨(x, s), ?_, rfl⟩
    simp

/-- Helper for Definition 7.60: the canonical partial-infimum projection of a saddle-point
representation takes the finite `EReal` value `representation x` on each fiber. -/
private theorem saddlePartialInfProjection_eq_coeObjective
    (representation : SaddlePointRepresentation P S) (x : P) :
    saddlePartialInfProjection representation x = ((representation x : ℝ) : EReal) := by
  let T : Set EReal := ((↑) : ℝ → EReal) '' Set.range (representation.saddleFunction x)
  have himage :
      (withTopToEReal ∘
          fun z : P × S ↦ ((representation.saddleFunction z.1 z.2 : ℝ) : WithTop ℝ)) ''
        {z : P × S | z ∈ (Set.univ : Set (P × S)) ∧ z.1 = x} = T := by
    -- Normalize the actual fiber used by `partialInfProjection`, including the ambient
    -- `Set.univ` constraint.
    ext a
    constructor
    · rintro ⟨⟨x', s⟩, hz, rfl⟩
      rcases hz with ⟨_, hx'⟩
      have hx' : x' = x := by
        simpa using hx'
      subst x'
      exact ⟨representation.saddleFunction x s, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨s, rfl⟩, rfl⟩
      refine ⟨(x, s), ?_, rfl⟩
      simp
  have hglb : IsGLB T (((representation x : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · intro b hb
      rcases hb with ⟨y, ⟨s, rfl⟩, rfl⟩
      exact_mod_cast (representation.objective_isLeast x).2 ⟨s, rfl⟩
    · intro b hb
      rcases (representation.objective_isLeast x).1 with ⟨s, hs⟩
      have hs_mem : ((representation.saddleFunction x s : ℝ) : EReal) ∈ T := by
        exact ⟨representation.saddleFunction x s, ⟨s, rfl⟩, rfl⟩
      simpa [T, hs] using hb hs_mem
  have hT_nonempty : T.Nonempty := by
    rcases (representation.objective_isLeast x).1 with ⟨s, hs⟩
    exact ⟨((representation.saddleFunction x s : ℝ) : EReal), ⟨representation.saddleFunction x s,
      ⟨s, rfl⟩, rfl⟩⟩
  -- The owner `partialInfProjection` is the `sInf` of that normalized fiber image.
  rw [saddlePartialInfProjection, partialInfProjection_eq_sInf, himage]
  exact hglb.csInf_eq hT_nonempty

/-- Every point `x` lies in the effective domain of the canonical partial-infimum projection
attached to a saddle-point representation. -/
-- Proof sketch: rewrite the partial-infimum projection as the infimum of the slice
-- `representation.saddleFunction x`, then use `representation.objective_isLeast x` to witness a
-- finite attained infimum.
private theorem saddlePartialInfProjection_mem_dom
    (representation : SaddlePointRepresentation P S) (x : P) :
    x ∈ dom (saddlePartialInfProjection representation) := by
  -- The previous value formula shows the projection is a finite real `EReal` value.
  rw [mem_extendedRealEffectiveDomain_iff, saddlePartialInfProjection_eq_coeObjective]
  simp

/-- The finite real part of the canonical partial-infimum projection agrees with the represented
objective. -/
-- Proof sketch: identify both sides with the infimum of the slice
-- `representation.saddleFunction x`, using `representation.objective_eq x` on one side and
-- `extendedRealRealPart_partialInfProjection_eq_sInf` on the other.
private theorem objective_eq_saddlePartialInfProjection
    (representation : SaddlePointRepresentation P S) :
    representation = extendedRealRealPart (saddlePartialInfProjection representation) := by
  funext x
  -- Read the finite `EReal` projection value back through `extendedRealRealPart`.
  apply EReal.coe_injective
  rw [coe_extendedRealRealPart (saddlePartialInfProjection_mem_dom representation x)]
  rw [saddlePartialInfProjection_eq_coeObjective]

variable [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- A selected barrier subgradient field is a pointwise subgradient of the represented objective
on the whole-space relative subdifferential `∂[Set.univ] representation(x)`. -/
def IsBarrierSubgradientSelection
    (representation : SaddlePointRepresentation P S) (g : P → P) : Prop :=
  ∀ x : P, g x ∈ ∂[Set.univ] representation(x)

namespace IsBarrierSubgradientSelection

variable {representation : SaddlePointRepresentation P S} {g : P → P}

/-- Evaluating a selected barrier subgradient field at `x` gives a subgradient of the represented
objective at `x`. -/
-- Proof sketch: unfold `IsBarrierSubgradientSelection`.
theorem apply
    (hg : representation.IsBarrierSubgradientSelection g) (x : P) :
    g x ∈ ∂[Set.univ] representation(x) := by
  -- Evaluating the selection predicate at `x` gives the desired pointwise subgradient.
  exact hg x

end IsBarrierSubgradientSelection

variable [NormedAddCommGroup S] [InnerProductSpace ℝ S]

/-- Definition 7.60: [Subgradient selection] if `w(x)` is a chosen minimizer of the saddle slice
`Ψ(x, ·)` and `∇₁Ψ` is a chosen subgradient with respect to the first argument, then the selected
field `x ↦ ∇₁Ψ(x, w(x))` is a subgradient selection of the represented objective. -/
-- Proof sketch: apply
-- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` to the
-- canonical partial-infimum projection of `representation`, then rewrite the resulting objective
-- with `objective_eq_saddlePartialInfProjection`.
theorem barrierSubgradientSelection_isBarrierSubgradientSelection
    {representation : SaddlePointRepresentation P S}
    {w : P → S}
    (hw : representation.IsBarrierSubproblemMinimizerSelection w)
    (saddleSubgradient : P → S → P × S)
    (hsub :
      ∀ x : P,
        WithLp.toLp 2 (saddleSubgradient x (w x)) ∈
          subdifferential
            (fun z : WithLp 2 (P × S) ↦
              ((representation.saddleFunction z.1.1 z.1.2 : ℝ) : WithTop ℝ))
            (WithLp.toLp 2 (x, w x)))
    (hvar :
      ∀ x : P, ∀ y : S,
        inner ℝ (saddleSubgradient x (w x)).2 (y - w x) ≥ 0) :
    representation.IsBarrierSubgradientSelection
      (barrierSubgradientSelection (fun x s ↦ (saddleSubgradient x s).1) w) := by
  intro x
  rw [mem_subdifferentialWithin_iff]
  refine ⟨by simp, ?_⟩
  intro x₁ hx₁
  -- The ambient saddle-subgradient inequality at `(x, w x)` controls every comparison point
  -- `(x₁, w x₁)` in the product space.
  have hsupport :=
    (mem_subdifferential_coe_real_iff.mp (hsub x)) (WithLp.toLp 2 (x₁, w x₁))
  have hsupport' :
      representation.saddleFunction x₁ (w x₁) ≥
        representation.saddleFunction x (w x) +
          inner ℝ (saddleSubgradient x (w x)).1 (x₁ - x) +
            inner ℝ (saddleSubgradient x (w x)).2 (w x₁ - w x) := by
    simpa [WithLp.prod_inner_apply, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using
      hsupport
  -- The second-coordinate term is nonnegative by the variational inequality, so it can be
  -- discarded.
  have hsecond_nonneg : 0 ≤ inner ℝ (saddleSubgradient x (w x)).2 (w x₁ - w x) :=
    hvar x (w x₁)
  have hsaddle :
      representation.saddleFunction x₁ (w x₁) ≥
        representation.saddleFunction x (w x) +
          inner ℝ (saddleSubgradient x (w x)).1 (x₁ - x) := by
    linarith
  -- Finally rewrite both saddle values back to the represented objective along the minimizing
  -- branch `w`.
  simpa [barrierSubgradientSelection_apply, hw.objective_eq_saddleFunction x,
    hw.objective_eq_saddleFunction x₁] using hsaddle

end Transfer

end SaddlePointRepresentation

end SelectedSubgradient
