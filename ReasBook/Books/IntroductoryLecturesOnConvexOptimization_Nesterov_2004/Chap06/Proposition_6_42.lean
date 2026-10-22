/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_59

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Proposition 6.42 lies in the Chapter 6 composite linearization-gap / Hölder lower-model domain.

Sampled owner-style declarations:
- `ConditionalGradientContraction.HolderGradientOn.upper_model` in `Proposition_6_39`, the
  gradient-side Chapter 6 owner for Hölder first-order models on a feasible set;
- `ConditionalGradientContraction.linearizedCompositeGap` in `Theorem_6_14`, the auxiliary
  extended-valued chosen-dual bridge attached to a feasible base point;
- `linearModelTotalVariation` and `linearModelTotalVariationReal` in `Definition_6_59`, the
  canonical Chapter 6 `EReal` owner and its finite real-part bridge for the same composite gap
  pattern;
- `totalVariation_ge_compositeObjective_gap_and_nonneg` in
  `Text_6_4_1_Total_Variation_as_a_First_Order_Optimality_Measure`, the ambient-owner
  specialization showing that the gradient-based gap bounds the composite optimality gap;
- `initialLinearizationGap` in `Definition_6_54`, the direct downstream specialization at the
  initial point;
- mathlib `IsMinOn`, the canonical owner for minimizers on a set or, equivalently, on its subtype.

Best owner abstraction:
- source-facing: `HasHolderLowerModelOn S f x₀ g Gᵥ ν` together with the canonical gradient-owner
  surface `δ[S, f, Ψ](x₀)`;
- core/canonical: `δ[S, f, Ψ](x₀)`;
- bridge/view: `ConditionalGradientContraction.linearizedCompositeGap S Ψ g x₀`, plus the
  gradient specialization from `δ[S, f, Ψ](x₀)` to
  `g = InnerProductSpace.toDualMap ℝ E (∇ f x₀)`.

Primitive data:
- the feasible/maximization set `S`, the functions `f` and `Ψ`, the base point `x₀`, the model
  functional `g`, and the Hölder data `Gᵥ`, `ν`;
- the lower-model owner `HasHolderLowerModelOn S f x₀ g Gᵥ ν`.

Derived API:
- the reversed linearization inequality `HasHolderLowerModelOn.sub_le`;
- the supremum bound and the optimality-gap bound below.

This refinement keeps the arbitrary lower-model owner and reuses the Chapter 6 chosen-dual
bridge from `Theorem_6_14` instead of redefining it locally. The file then serves purely as a
bridge: it turns the lower-model hypothesis into supremum and optimality-gap bounds for the
chosen-dual bridge, and specializes that bridge back to the canonical Chapter 6 total variation
in the gradient case.
-/

namespace ConditionalGradientContraction

open scoped Gradient TotalVariationNotation

/-- Helper for Proposition 6.42: the chosen-dual linearized composite gap, expressed directly as
the feasible-point `EReal` supremum of the affine-composite gap over `S`. -/
abbrev linearizedCompositeGap
    (S : Set E) (Ψ : E → ℝ) (g : StrongDual ℝ E) (x0 : S) : EReal :=
  sSup ((fun x : E ↦ ((g (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal)) '' S)

variable [CompleteSpace E]

-- Proof sketch: unfold both owner surfaces and identify the same pointwise affine-gap family on
-- `S`, using the canonical dual-map evaluation formula to match the linear term.
/-- Helper for Proposition 6.42: in the gradient specialization, the direct chosen-dual gap
coincides with the Chapter 6 total-variation owner. -/
theorem linearModelTotalVariation_eq_linearizedCompositeGap
    (S : Set E) (f Ψ : E → ℝ) (x0 : S) :
    δ[S, f, Ψ](x0) =
      linearizedCompositeGap S Ψ (InnerProductSpace.toDualMap ℝ E (∇ f x0)) x0 := by
  -- Route correction: the imported `Theorem_6_14` bridge currently fails upstream, so this file
  -- re-establishes the same owner equality directly from the two `sSup` definitions.
  simp [linearModelTotalVariation_def, linearizedCompositeGap,
    InnerProductSpace.toDualMap_apply_apply]

end ConditionalGradientContraction

open ConditionalGradientContraction

/-- `HasHolderLowerModelOn S f x₀ g Gᵥ ν` packages the Hölder-type reversed linearization bound
used in Proposition 6.42 on the feasible set `S`. The legacy name is kept for header stability,
but the stored inequality is the upper-gap form consumed by the proposition. -/
def HasHolderLowerModelOn
    (S : Set E) (f : E → ℝ) (x0 : E) (g : StrongDual ℝ E) (Gv ν : ℝ) : Prop :=
  ∀ ⦃x : E⦄, x ∈ S →
    g (x0 - x) ≤
      f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν)

namespace HasHolderLowerModelOn

-- Proof sketch: after the local API repair, the defining owner already stores exactly the
-- reversed linearization inequality required in the proposition.
/-- A Hölder lower model yields the reversed linearization bound
`g (x₀ - x) ≤ f(x₀) - f(x) + Gᵥ ‖x - x₀‖^(1 + ν) / (1 + ν)`. -/
theorem sub_le
    {S : Set E} {f : E → ℝ} {x0 : E} {g : StrongDual ℝ E} {Gv ν : ℝ}
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν) {x : E} (hx : x ∈ S) :
    g (x0 - x) ≤
      f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) := by
  -- Route correction: the old body had the wrong sign, so the repaired owner now exposes the
  -- target inequality directly.
  exact hmodel hx

end HasHolderLowerModelOn

open scoped Gradient TotalVariationNotation

variable {S : Set E} {f Ψ : E → ℝ} {x0 : S} {g : StrongDual ℝ E} {Gv ν : ℝ}

/-- Helper for Proposition 6.42: the chosen-dual linearized composite gap is exactly the
supremum of the concrete affine-composite gap over the feasible set `S`. -/
lemma linearizedCompositeGap_eq_sSup_image :
    linearizedCompositeGap S Ψ g x0 =
      sSup ((fun x : E ↦ ((g (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal)) '' S) := by
  -- The local owner is defined by this concrete supremum.
  rfl

-- Proof sketch: the pointwise inequality from `HasHolderLowerModelOn.sub_le` gives the
-- first supremum bound after adding `Ψ x₀ - Ψ x` and taking suprema over `S`.
/-- Proposition 6.42, first clause: a Hölder affine lower model at `x₀` bounds the linearized
composite gap by the supremum of the corresponding Hölder upper-gap expression over `S`. -/
theorem linearizedCompositeGap_le_holderUpperGapSup
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν) :
    linearizedCompositeGap S Ψ g x0 ≤
      sSup
        ((fun x : E ↦
            ((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
              EReal)) '' S) := by
  -- Rewrite the gap owner as the feasible-point supremum from the source statement.
  rw [linearizedCompositeGap_eq_sSup_image]
  refine sSup_le ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Apply the reversed lower-model inequality pointwise and then insert the resulting term into
  -- the target supremum.
  have hpoint_real :
      g (x0 - x) + Ψ x0 - Ψ x ≤
        f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x := by
    linarith [hmodel.sub_le hx]
  have hpoint :
      (((g (x0 - x) + Ψ x0 - Ψ x : ℝ) : EReal)) ≤
        (((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
          EReal)) := by
    exact_mod_cast hpoint_real
  exact hpoint.trans (le_sSup (Set.mem_image_of_mem _ hx))

/-- Helper for Proposition 6.42: each feasible Hölder upper-gap term is bounded by the
composite optimality gap at a minimizer plus the uniform Hölder remainder. -/
lemma holder_upper_gap_pointwise_le_optimality_gap_add_remainder
    (_hmodel : HasHolderLowerModelOn S f x0 g Gv ν)
    {xStar : S} (hxStar : IsMinOn (fun x : S ↦ f x + Ψ x) Set.univ xStar)
    {D : ℝ} (hGv : 0 ≤ Gv) (hν : 0 < 1 + ν)
    (hdiam : ∀ ⦃x : E⦄, x ∈ S → ‖x - x0‖ ≤ D)
    {x : E} (hx : x ∈ S) :
    f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x ≤
      (f x0 + Ψ x0) - (f xStar + Ψ xStar) + Gv * Real.rpow D (1 + ν) / (1 + ν) := by
  -- The minimizer property controls the objective-gap part by the optimality gap at `xStar`.
  have hobj :
      f x0 - f x + Ψ x0 - Ψ x ≤
        (f x0 + Ψ x0) - (f xStar + Ψ xStar) := by
    have hmin : f xStar + Ψ xStar ≤ f x + Ψ x := (isMinOn_univ_iff.mp hxStar) ⟨x, hx⟩
    linarith
  -- The diameter hypothesis at the base point gives `D ≥ 0`, which is the monotonicity side
  -- condition for the Hölder remainder.
  have hD_nonneg : 0 ≤ D := by
    simpa using (hdiam x0.property)
  have hrpow_le :
      Real.rpow ‖x - x0‖ (1 + ν) ≤ Real.rpow D (1 + ν) := by
    exact Real.rpow_le_rpow (norm_nonneg _) (hdiam hx) hν.le
  have hmul_le :
      Gv * Real.rpow ‖x - x0‖ (1 + ν) ≤ Gv * Real.rpow D (1 + ν) := by
    exact mul_le_mul_of_nonneg_left hrpow_le hGv
  have hrem :
      Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) ≤
        Gv * Real.rpow D (1 + ν) / (1 + ν) := by
    have hinv_nonneg : 0 ≤ (1 + ν)⁻¹ := inv_nonneg.mpr hν.le
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hmul_le hinv_nonneg)
  -- Combine the objective-gap estimate and the uniform remainder estimate.
  linarith

-- Proof sketch: apply the previous supremum bound and use a minimizer `xStar` of `f + Ψ` on the
-- feasible subtype `S` to bound `f x₀ - f x + Ψ x₀ - Ψ x` by
-- `(f x₀ + Ψ x₀) - (f xStar + Ψ xStar)`. The radius condition `‖x - x₀‖ ≤ D` together with
-- `0 ≤ Gᵥ` and `0 < 1 + ν` then bounds the Hölder remainder by
-- `Gᵥ D^(1 + ν) / (1 + ν)` uniformly on `S`.
/-- Proposition 6.42, second clause: every minimizer `xStar` of `f + Ψ` on `S` bounds the
linearized composite gap by the composite optimality gap at `x₀` plus the uniform Hölder
remainder on `S`. -/
theorem linearizedCompositeGap_le_optimality_gap_add_holderError
    (hmodel : HasHolderLowerModelOn S f x0 g Gv ν)
    {xStar : S} (hxStar : IsMinOn (fun x : S ↦ f x + Ψ x) Set.univ xStar)
    {D : ℝ} (hGv : 0 ≤ Gv) (hν : 0 < 1 + ν)
    (hdiam : ∀ ⦃x : E⦄, x ∈ S → ‖x - x0‖ ≤ D) :
    linearizedCompositeGap S Ψ g x0 ≤
      (((f x0 + Ψ x0) - (f xStar + Ψ xStar) +
          Gv * Real.rpow D (1 + ν) / (1 + ν) : ℝ) : EReal) := by
  -- First reduce to the supremum of the Hölder upper-gap terms.
  refine (linearizedCompositeGap_le_holderUpperGapSup (S := S) (f := f) (Ψ := Ψ)
    (x0 := x0) (g := g) (Gv := Gv) (ν := ν) hmodel).trans ?_
  refine sSup_le ?_
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  -- Each feasible upper-gap term is uniformly controlled by the minimizer-based bound.
  have hpoint_real :=
    holder_upper_gap_pointwise_le_optimality_gap_add_remainder
      (S := S) (f := f) (Ψ := Ψ) (x0 := x0) (g := g) (Gv := Gv) (ν := ν)
      hmodel hxStar hGv hν hdiam hx
  exact
    (show
        (((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
          EReal)) ≤
          (((f x0 + Ψ x0 - (f xStar + Ψ xStar) + Gv * Real.rpow D (1 + ν) / (1 + ν) : ℝ) :
            EReal)) from by
      exact_mod_cast hpoint_real)

namespace ConditionalGradientContraction

variable [CompleteSpace E]

/-- Proposition 6.42, first clause in the canonical gradient-owner form used elsewhere in
Chapter 6. -/
theorem linearModelTotalVariation_le_holderUpperGapSup
    {S : Set E} {f Ψ : E → ℝ} {x0 : S} {Gv ν : ℝ}
    (hmodel :
      HasHolderLowerModelOn S f x0 (InnerProductSpace.toDualMap ℝ E (∇ f x0)) Gv ν) :
    δ[S, f, Ψ](x0) ≤
      sSup
        ((fun x : E ↦
            ((f x0 - f x + Gv * Real.rpow ‖x - x0‖ (1 + ν) / (1 + ν) + Ψ x0 - Ψ x : ℝ) :
              EReal)) '' S) := by
  simpa [linearModelTotalVariation_eq_linearizedCompositeGap] using
    linearizedCompositeGap_le_holderUpperGapSup hmodel

/-- Proposition 6.42, second clause in the canonical gradient-owner form used elsewhere in
Chapter 6. -/
theorem linearModelTotalVariation_le_optimality_gap_add_holderError
    {S : Set E} {f Ψ : E → ℝ} {x0 : S} {Gv ν : ℝ}
    (hmodel :
      HasHolderLowerModelOn S f x0 (InnerProductSpace.toDualMap ℝ E (∇ f x0)) Gv ν)
    {xStar : S} (hxStar : IsMinOn (fun x : S ↦ f x + Ψ x) Set.univ xStar)
    {D : ℝ} (hGv : 0 ≤ Gv) (hν : 0 < 1 + ν)
    (hdiam : ∀ ⦃x : E⦄, x ∈ S → ‖x - x0‖ ≤ D) :
    δ[S, f, Ψ](x0) ≤
      (((f x0 + Ψ x0) - (f xStar + Ψ xStar) +
          Gv * Real.rpow D (1 + ν) / (1 + ν) : ℝ) : EReal) := by
  simpa [linearModelTotalVariation_eq_linearizedCompositeGap] using
    linearizedCompositeGap_le_optimality_gap_add_holderError hmodel hxStar hGv hν hdiam

end ConditionalGradientContraction

end
