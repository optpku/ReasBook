/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_52
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_53
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_42
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Gradient WeightSequenceNotation

universe u

section InitialLinearizationGap

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : Set E}

/- Definition 6.54 lies in the Chapter 6 conditional-gradient / linearization-gap domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Theorem_6_11`, the chapter owner of the feasible-set
  affine-plus-regularizer objective `x ↦ ⟨s, x⟩ + Ψ(x)`;
- `IsLinearOptimizationOracle` in `Definition_6_52`, the source-facing oracle-selection owner
  built on that objective;
- `LinearOracleCompositeMethod.oraclePoint_mem_argmin` in `Algorithm_6_4`, the direct downstream
  chapter surface using `gradientWithin f Q` together with
  `linearOptimizationOracleObjective`;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the ambient
  extended-valued chosen-dual gap owner obtained after extending `Ψ : Q → ℝ` to `E`.

Best owner abstraction:
- source-facing: the initial gap `V₀` together with the error term `B_{ν,t}` from Definition 6.54;
- core/canonical: `linearOptimizationOracleObjective` together with the canonical constrained
  gradient `gradientWithin f Q`, and `linearOptimizationOracleErrorBound` for the weighted
  error term;
- bridge/view: `linearizedCompositeGap Q (Function.extend Subtype.val Ψ 0)
    (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x₀)) x₀`.

Primitive data:
- the feasible set `Q`, objective `f`, regularizer `Ψ : Q → ℝ`, and starting point `x₀ : Q`.
- the weight sequence `a`, Hölder constant `G_ν`, diameter term `D`, and exponent `ν` for
  `B_{ν,t}`.

Derived API:
- the source-facing maximized owner `initialLinearizationGap` for the displayed quantity `V₀`;
- the real-supremum bridge `initialLinearizationGapSup` and its displayed
  affine-plus-regularizer expansion;
- the finite-attained comparison from `initialLinearizationGap` to the ambient owner;
- a source-facing bridge from `B_{ν,t}` to the canonical Chapter 6 owner
  `linearOptimizationOracleErrorBound`.
-/

/-- Auxiliary ambient Chapter 6 bridge for the Definition 6.54 gap: extend `Ψ : Q → ℝ` to `E`
and take the corresponding chosen-dual `EReal` supremum. -/
abbrev initialLinearizationGapEReal
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) : EReal :=
  ConditionalGradientContraction.linearizedCompositeGap Q
    (Function.extend Subtype.val Ψ 0)
    (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) x0

/-- The feasible-point affine-composite gap family from Definition 6.54 at the initial point
`x₀`, written with the canonical constrained gradient `gradientWithin f Q x₀`. -/
def initialLinearizationGapFamily
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) : Q → ℝ :=
  fun x : Q ↦
    linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x0 -
      linearOptimizationOracleObjective
        (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x

/-- The real-valued supremum bridge attached to the Definition 6.54 affine-composite gap family.
This is a companion bridge owner, not the main source-facing `max_x` quantity. -/
def initialLinearizationGapSup
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) : ℝ :=
  sSup (Set.range (initialLinearizationGapFamily Q f Ψ x0))

/-- Auxiliary maximizing certificate for the textbook quantity `V₀`, represented by the canonical
within-gradient at `x₀` together with an attained maximum of the Definition 6.54 gap family. -/
class InitialLinearizationGapMaximizer
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) where
  /-- The constrained gradient used in the definition is the actual displayed gradient datum. -/
  hasGradientWithinAt : HasGradientWithinAt f (gradientWithin f Q x0) Q x0
  /-- A feasible maximizer of the affine-composite gap family. -/
  maximizer : Q
  /-- The chosen feasible point attains the textbook maximum. -/
  isGreatest :
    IsGreatest (Set.range (initialLinearizationGapFamily Q f Ψ x0))
      (initialLinearizationGapFamily Q f Ψ x0 maximizer)

/-- A linear-oracle composite method supplies canonical maximizing data for the Definition 6.54
initial gap via the oracle point at iteration `0`. -/
instance (method : LinearOracleCompositeMethod Q f Ψ) :
    InitialLinearizationGapMaximizer Q f Ψ method.x0 where
  hasGradientWithinAt := method.hasGradientWithinAt method.x0
  maximizer := method.oraclePoint 0
  isGreatest := by
    refine ⟨?_, ?_⟩
    · exact ⟨method.oraclePoint 0, rfl⟩
    · intro y hy
      rcases hy with ⟨x, rfl⟩
      exact sub_le_sub_left
        (method.oraclePoint_linearOptimizationOracleObjective_le 0 x)
        (linearOptimizationOracleObjective
          (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q method.x0)) Ψ method.x0)

/-- The source-facing quantity `V₀` from Definition 6.54 is the attained maximum of the
feasible-point linearization gap at the starting point `x₀`, expressed using the canonical
constrained gradient once the displayed gradient side condition and a maximizing feasible point
are available. The same definition then introduces
`B_{ν,t} = a₀ V₀ + (\sum_{k=1}^t a_k^{1+ν} / A_k^ν) G_ν D^{1+ν}`. -/
def initialLinearizationGap
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] : ℝ :=
  initialLinearizationGapFamily Q f Ψ x0 hData.maximizer

/-- The maximizing data for `V₀` include the gradient side condition needed for
`gradientWithin f Q x₀` to stand for the displayed gradient in Definition 6.54. -/
theorem initialLinearizationGap_hasGradientWithinAt
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    HasGradientWithinAt f (gradientWithin f Q x0) Q x0 :=
  hData.hasGradientWithinAt

/-- The source-facing quantity `V₀` is the greatest element of the Definition 6.54 gap family. -/
theorem initialLinearizationGap_isGreatest
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    IsGreatest (Set.range (initialLinearizationGapFamily Q f Ψ x0))
      (initialLinearizationGap Q f Ψ x0) := by
  simpa [initialLinearizationGap] using hData.isGreatest

/-- `initialLinearizationGapReal` is the real-supremum bridge attached to the Definition 6.54
gap family, retained as a companion name for compatibility with the old scalar-supremum surface.
-/
abbrev initialLinearizationGapReal
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) : ℝ :=
  initialLinearizationGapSup Q f Ψ x0

/-- The source-facing maximum `V₀` agrees with the real supremum of the Chapter 6
oracle-objective drop family at the starting point. -/
theorem initialLinearizationGap_eq_oracleObjectiveGapSup
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    initialLinearizationGap Q f Ψ x0 =
      sSup (Set.range fun x : Q ↦
        linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x0 -
          linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x) := by
  simpa [initialLinearizationGapSup, initialLinearizationGapFamily] using
    (initialLinearizationGap_isGreatest Q f Ψ x0).csSup_eq.symm

/-- Helper for Definition 6.54: expanding the feasible-point gap family yields the displayed
affine-plus-regularizer expression with the constrained gradient at `x₀`. -/
private lemma initialLinearizationGapFamily_apply
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) (x : Q) :
    initialLinearizationGapFamily Q f Ψ x0 x =
      inner ℝ (gradientWithin f Q x0) ((x0 : E) - x) + Ψ x0 - Ψ x := by
  -- Expand the two oracle-objective values and evaluate the chosen dual map on the displacement.
  simp [initialLinearizationGapFamily, linearOptimizationOracleObjective_apply,
    InnerProductSpace.toDualMap_apply_apply, inner_sub_right]
  ring_nf

/-- Helper for Definition 6.54: taking the range of the gap family is unchanged by replacing the
oracle-objective difference with its affine-plus-regularizer normal form. -/
private lemma initialLinearizationGapFamily_range_eq_affineGapRange
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    Set.range (initialLinearizationGapFamily Q f Ψ x0) =
      Set.range (fun x : Q ↦
        inner ℝ (gradientWithin f Q x0) ((x0 : E) - x) + Ψ x0 - Ψ x) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    -- Normalize the family value at the same feasible witness.
    refine ⟨x, ?_⟩
    rw [initialLinearizationGapFamily_apply]
  · intro hy
    rcases hy with ⟨x, rfl⟩
    -- Reuse the same feasible witness after rewriting the family value back.
    refine ⟨x, ?_⟩
    rw [initialLinearizationGapFamily_apply]

/-- Helper for Definition 6.54: the ambient `EReal` image defining the chosen-dual gap is exactly
the casted range of the feasible-point gap family. -/
private lemma initialLinearizationGapERealImage_eq_range
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    ((fun x : E ↦
        (((InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) ((x0 : E) - x) +
              Function.extend Subtype.val Ψ 0 x0 -
              Function.extend Subtype.val Ψ 0 x : ℝ) : EReal)) '' Q) =
      Set.range (fun x : Q ↦ ((initialLinearizationGapFamily Q f Ψ x0 x : ℝ) : EReal)) := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hxQ, rfl⟩
    -- Turn an ambient feasible witness into a subtype witness and simplify the extension on `Q`.
    refine ⟨⟨x, hxQ⟩, ?_⟩
    simp [initialLinearizationGapFamily_apply, Function.extend_val_apply hxQ,
      InnerProductSpace.toDualMap_apply_apply]
  · intro hy
    rcases hy with ⟨x, rfl⟩
    -- Forget the subtype witness back to the ambient feasible point and simplify on `Q`.
    refine ⟨x, x.property, ?_⟩
    simp [initialLinearizationGapFamily_apply, InnerProductSpace.toDualMap_apply_apply]

/-- Helper for Definition 6.54: casting the attained real maximum gives an `EReal` greatest
element for the casted gap-family range. -/
private lemma initialLinearizationGapEReal_isGreatest
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    IsGreatest
      (Set.range (fun x : Q ↦ ((initialLinearizationGapFamily Q f Ψ x0 x : ℝ) : EReal)))
      ((initialLinearizationGap Q f Ψ x0 : ℝ) : EReal) := by
  refine ⟨?_, ?_⟩
  · -- The chosen maximizer still witnesses membership after casting to `EReal`.
    refine ⟨hData.maximizer, ?_⟩
    simp [initialLinearizationGap]
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    -- Cast the real upper bound supplied by the attained maximum.
    have hle :
        initialLinearizationGapFamily Q f Ψ x0 x ≤
          initialLinearizationGap Q f Ψ x0 :=
      (initialLinearizationGap_isGreatest Q f Ψ x0).2 ⟨x, rfl⟩
    simpa using (show
      (((initialLinearizationGapFamily Q f Ψ x0 x : ℝ) : EReal)) ≤
        (((initialLinearizationGap Q f Ψ x0 : ℝ) : EReal)) from
      by
        exact_mod_cast hle)

/-- Definition 6.54: when the maximizing data certify the textbook maximum and displayed gradient
at `x₀`,
coercing the scalar source quantity `V₀` to `EReal` agrees with the ambient chosen-dual gap
owner `linearizedCompositeGap`, specialized to `Function.extend Subtype.val Ψ 0`. -/
theorem initialLinearizationGap_eq_linearizedCompositeGap
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    (initialLinearizationGap Q f Ψ x0 : EReal) =
      initialLinearizationGapEReal Q f Ψ x0 := by
  -- Rewrite the ambient owner to its concrete image formula and transport that image to the
  -- casted subtype range of the source-facing gap family.
  rw [initialLinearizationGapEReal, ConditionalGradientContraction.linearizedCompositeGap,
    initialLinearizationGapERealImage_eq_range]
  -- The real attained maximum remains the greatest element after coercion to `EReal`.
  exact (initialLinearizationGapEReal_isGreatest Q f Ψ x0).csSup_eq.symm

/-- `initialLinearizationGapReal` is the real supremum bridge for the Chapter 6 oracle-objective
drop family at the starting point, formed with the canonical constrained gradient
`gradientWithin f Q x₀`. -/
theorem initialLinearizationGapReal_eq_oracleObjectiveGapSup
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    initialLinearizationGapReal Q f Ψ x0 =
      sSup (Set.range fun x : Q ↦
        linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x0 -
          linearOptimizationOracleObjective
            (InnerProductSpace.toDualMap ℝ E (gradientWithin f Q x0)) Ψ x) :=
  rfl

/-- Expanding the source-facing quantity `V₀` at the chosen maximizing point gives the displayed
affine-plus-regularizer gap value
`⟪∇_Q f(x₀), x₀ - x⟫ + Ψ(x₀) - Ψ(x)` from Definition 6.54. -/
theorem initialLinearizationGap_def
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    initialLinearizationGap Q f Ψ x0 =
      inner ℝ (gradientWithin f Q x0) ((x0 : E) - hData.maximizer) +
        Ψ x0 - Ψ hData.maximizer := by
  -- Evaluate the normalized gap family at the chosen maximizing feasible point.
  rw [initialLinearizationGap, initialLinearizationGapFamily_apply]

/-- Expanding the real-supremum bridge gives the supremum of the affine-plus-regularizer gap
values `⟪∇_Q f(x₀), x₀ - x⟫ + Ψ(x₀) - Ψ(x)` over `x ∈ Q`. -/
theorem initialLinearizationGapReal_def
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q) :
    initialLinearizationGapReal Q f Ψ x0 =
      sSup (Set.range fun x : Q ↦
        inner ℝ (gradientWithin f Q x0) ((x0 : E) - x) + Ψ x0 - Ψ x) := by
  -- Replace the oracle-objective range by its normalized affine-plus-regularizer range.
  rw [initialLinearizationGapReal, initialLinearizationGapSup,
    initialLinearizationGapFamily_range_eq_affineGapRange]

/-- The real-supremum bridge agrees with the source-facing quantity `V₀` when the maximum is
attained. -/
theorem initialLinearizationGapReal_eq_initialLinearizationGap
    (Q : Set E) (f : E → ℝ) (Ψ : Q → ℝ) (x0 : Q)
    [hData : InitialLinearizationGapMaximizer Q f Ψ x0] :
    initialLinearizationGapReal Q f Ψ x0 =
      initialLinearizationGap Q f Ψ x0 := by
  rw [initialLinearizationGapReal_eq_oracleObjectiveGapSup,
    ← initialLinearizationGap_eq_oracleObjectiveGapSup]

/-- The Definition 6.54 error quantity `B_{ν,t}` attached to the scalar initial gap `V₀`. This
is the same Chapter 6 owner as `linearOptimizationOracleErrorBound`; the present name only
records its role in the source definition. -/
abbrev initialLinearizationErrorBound
    (V0 : ℝ) (a : ℕ → ℝ) (Gν D ν : ℝ) (t : ℕ) : ℝ :=
  linearOptimizationOracleErrorBound V0 a Gν D ν t

/-- Expanding `initialLinearizationErrorBound V₀ a G_ν D ν t` gives the exact Definition 6.54
formula for `B_{ν,t}` with `A_k = A[a](k)`. -/
theorem initialLinearizationErrorBound_def
    (V0 : ℝ) (a : ℕ → ℝ) (Gν D ν : ℝ) (t : ℕ) :
    initialLinearizationErrorBound V0 a Gν D ν t =
      a 0 * V0 +
        Finset.sum (Finset.Icc 1 t)
            (fun k ↦ Real.rpow (a k) (1 + ν) / Real.rpow (A[a](k)) ν) *
          Gν * Real.rpow D (1 + ν) :=
  rfl

end InitialLinearizationGap
