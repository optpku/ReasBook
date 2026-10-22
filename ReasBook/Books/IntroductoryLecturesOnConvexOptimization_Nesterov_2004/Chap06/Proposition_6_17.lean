/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_32
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped BigOperators SeminormOperatorNorm

universe u v

variable {ι : Type v}

/- Proposition 6.17 lies in the induced operator-norm domain for the weighted tuple geometry of
the continuous location model.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between source and target
  seminorm geometries;
* `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, the owner-side source formula for the
  two-ball pairing supremum;
* `continuousLocationSmoothingMap`, the chapter owner for the weighted pairing
  `(x, u) ↦ ∑_j m_j ⟪u_j, x⟫`;
* `continuousLocationDualTupleNorm`, the source-facing weighted tuple norm on `ι → E`.

Best owner abstraction:
* source-facing: the textbook supremum of `∑_j m_j ⟪u_j, x⟫` over unit vectors `x` in the ambient
  real inner-product space `E` and weighted-dual unit tuples `u : ι → E`;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to the `PiLp`-transport of
  `continuousLocationSmoothingMap E weights` and the pullback seminorm
  `continuousLocationDualTupleSeminorm E weights`;
* bridge/view kept in this file: the weighted scaling map on `PiLp 2 (fun _ : ι ↦ E)` and the
  transported smoothing operator `continuousLocationSmoothingMapPiLp E weights`.

Primitive data:
* the population weights `weights`;
* the ambient real inner-product space `E`;
* the weighted tuple scaling linear map on `PiLp 2 (fun _ : ι ↦ E)`.

Derived API:
* the pairing map `continuousLocationSmoothingMap`;
* the transported pairing map `continuousLocationSmoothingMapPiLp`;
* the pullback seminorm owner `continuousLocationDualTupleSeminorm`;
* the canonical primal-dual operator norm of `continuousLocationSmoothingMap`;
* the source-facing sphere formula of Proposition 6.17 as a thin bridge.
-/

section Scale

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The componentwise scaling `u_j ↦ √m_j • u_j` on the Hilbert product
`PiLp 2 (fun _ : ι ↦ E)` behind the weighted tuple geometry. -/
def continuousLocationDualTupleScale
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :
    PiLp 2 (fun _ : ι ↦ E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).symm.toContinuousLinearMap) :
      (ι → E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E)).comp
    ((ContinuousLinearMap.pi fun j ↦
      Real.sqrt (weights j : ℝ) • PiLp.proj 2 (fun _ : ι ↦ E) j) :
      PiLp 2 (fun _ : ι ↦ E) →L[ℝ] (ι → E))

/-- The `j`-th coordinate of `continuousLocationDualTupleScale E weights u` is
`√m_j • u_j`. -/
theorem continuousLocationDualTupleScale_apply
    (weights : ContinuousLocationWeights ι) (u : E₂) (j : ι) :
    continuousLocationDualTupleScale E weights u j =
      Real.sqrt (weights j : ℝ) • u j := by
  simp [continuousLocationDualTupleScale]

end Scale

section Geometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The weighted tuple geometry of Proposition 6.17, owned canonically as the pullback of the
ambient Hilbert norm on `PiLp 2 (fun _ : ι ↦ E)` along `continuousLocationDualTupleScale
E weights`. -/
def continuousLocationDualTupleSeminorm
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) : Seminorm ℝ (PiLp 2 fun _ : ι ↦ E) :=
  Seminorm.comp
    (normSeminorm ℝ (PiLp 2 fun _ : ι ↦ E))
    (continuousLocationDualTupleScale E weights).toLinearMap

/-- Evaluating `continuousLocationDualTupleSeminorm E weights` gives the ambient norm of the
weighted scaling of the tuple. -/
theorem continuousLocationDualTupleSeminorm_eq_norm_scale
    (weights : ContinuousLocationWeights ι) (u : E₂) :
    continuousLocationDualTupleSeminorm E weights u =
      ‖continuousLocationDualTupleScale E weights u‖ :=
  rfl

/-- The seminorm owner `continuousLocationDualTupleSeminorm E weights` recovers the textbook
weighted tuple norm `continuousLocationDualTupleNorm E weights` after identifying coordinate
tuples with the Hilbert product `PiLp 2 (fun _ : ι ↦ E)`. -/
theorem continuousLocationDualTupleSeminorm_apply
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 u) =
      continuousLocationDualTupleNorm E weights u := by
  -- Unfold the pulled-back seminorm and evaluate the ambient `PiLp` norm after scaling.
  rw [continuousLocationDualTupleSeminorm_eq_norm_scale]
  rw [PiLp.norm_eq_of_L2]
  -- Each coordinate contributes `m_j * ‖u_j‖^2`, matching the textbook weighted tuple norm.
  rw [continuousLocationDualTupleNorm_def]
  apply congrArg Real.sqrt
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [continuousLocationDualTupleScale_apply, norm_smul, Real.norm_eq_abs]
  have hweight_nonneg : 0 ≤ (weights j : ℝ) := le_of_lt (ContinuousLocationWeights.weights_pos weights j)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (weights j : ℝ) := Real.sqrt_nonneg _
  have hsqrt_mul :
      Real.sqrt (weights j : ℝ) * Real.sqrt (weights j : ℝ) = (weights j : ℝ) := by
    nlinarith [Real.sq_sqrt hweight_nonneg]
  simp only [abs_of_nonneg hsqrt_nonneg, sq, mul_assoc, mul_left_comm, mul_comm]
  rw [hsqrt_mul]
  ring

/-- Positive weights make the pullback seminorm `continuousLocationDualTupleSeminorm E weights`
nondegenerate, so the weighted tuple geometry is a genuine norm. -/
instance continuousLocationDualTupleSeminorm.isNorm
    (weights : ContinuousLocationWeights ι) :
    Seminorm.IsNorm (continuousLocationDualTupleSeminorm E weights : Seminorm ℝ E₂) := by
  constructor
  intro u hu
  -- Vanishing of the pulled-back seminorm forces the scaled tuple to be zero in the ambient norm.
  have hscale_zero : continuousLocationDualTupleScale E weights u = 0 := by
    apply norm_eq_zero.mp
    simpa [continuousLocationDualTupleSeminorm_eq_norm_scale] using hu
  -- Positive weights make the componentwise scaling map injective.
  ext j
  have hcoord :
      Real.sqrt (weights j : ℝ) • u j = 0 := by
    simpa [continuousLocationDualTupleScale_apply] using
      congrArg (fun v : E₂ ↦ v j) hscale_zero
  have hsqrt_ne_zero : Real.sqrt (weights j : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (ContinuousLocationWeights.weights_pos weights j))
  exact (smul_eq_zero.mp hcoord).resolve_left hsqrt_ne_zero

/-- The canonical `PiLp` transport of `continuousLocationSmoothingMap E weights`, viewed in the
weighted tuple geometry on `PiLp 2 (fun _ : ι ↦ E)`. This is a thin bridge from the
source-facing coordinate-tuple owner to the Hilbert-product realization used by
`continuousLocationDualTupleSeminorm E weights`. -/
abbrev continuousLocationSmoothingMapPiLp
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :=
  (ContinuousLinearMap.precomp ℝ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap).comp
    (continuousLocationSmoothingMap E weights)

/-- Evaluating the transported smoothing operator on a `PiLp` tuple recovers the same weighted
pairing formula as `continuousLocationSmoothingMap_apply`. -/
theorem continuousLocationSmoothingMapPiLp_apply
    (weights : ContinuousLocationWeights ι) (x : E) (u : E₂) :
    continuousLocationSmoothingMapPiLp E weights x u =
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x := by
  simpa [continuousLocationSmoothingMapPiLp] using
    continuousLocationSmoothingMap_apply weights x
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap u)

/-- Helper for Proposition 6.17: if the index type is nonempty, then the total population weight
is strictly positive. -/
lemma continuousLocation_totalPopulation_pos
    (weights : ContinuousLocationWeights ι) [Nonempty ι] :
    0 < continuousLocationTotalPopulation weights := by
  classical
  obtain ⟨j0⟩ := ‹Nonempty ι›
  rw [continuousLocationTotalPopulation_def]
  have hnonneg : ∀ j : ι, 0 ≤ (weights j : ℝ) := by
    intro j
    exact le_of_lt (ContinuousLocationWeights.weights_pos weights j)
  exact lt_of_lt_of_le (ContinuousLocationWeights.weights_pos weights j0) <|
    Finset.single_le_sum (fun j _ ↦ hnonneg j) (by simp [hnonneg])

/-- Helper for Proposition 6.17: the weighted constant tuple has ambient `PiLp` norm
`√P * ‖x‖`. -/
lemma continuousLocation_weighted_constant_tuple_norm
    (weights : ContinuousLocationWeights ι) (x : E) :
    ‖WithLp.toLp 2 (fun j : ι ↦ Real.sqrt (weights j : ℝ) • x)‖ =
      Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖ := by
  -- Compute the ambient `PiLp` norm coordinatewise and factor out the common `‖x‖²` term.
  rw [PiLp.norm_eq_of_L2]
  have hsum :
      ∑ j : ι, ‖Real.sqrt (weights j : ℝ) • x‖ ^ 2 =
        continuousLocationTotalPopulation weights * ‖x‖ ^ 2 := by
    calc
      ∑ j : ι, ‖Real.sqrt (weights j : ℝ) • x‖ ^ 2
          = ∑ j : ι, (weights j : ℝ) * ‖x‖ ^ 2 := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [norm_smul, Real.norm_eq_abs]
              have hweight_nonneg : 0 ≤ (weights j : ℝ) := by
                exact le_of_lt (ContinuousLocationWeights.weights_pos weights j)
              have hsqrt_nonneg : 0 ≤ Real.sqrt (weights j : ℝ) := Real.sqrt_nonneg _
              have hsqrt_mul :
                  Real.sqrt (weights j : ℝ) * Real.sqrt (weights j : ℝ) = (weights j : ℝ) := by
                nlinarith [Real.sq_sqrt hweight_nonneg]
              simp only [abs_of_nonneg hsqrt_nonneg, sq, mul_left_comm, mul_comm]
              rw [hsqrt_mul]
              ring
      _ = (∑ j : ι, (weights j : ℝ)) * ‖x‖ ^ 2 := by
          rw [Finset.sum_mul]
      _ = continuousLocationTotalPopulation weights * ‖x‖ ^ 2 := by
          rw [continuousLocationTotalPopulation_def]
  have htotal_nonneg : 0 ≤ continuousLocationTotalPopulation weights := by
    rw [continuousLocationTotalPopulation_def]
    refine Finset.sum_nonneg ?_
    intro j hj
    exact le_of_lt (ContinuousLocationWeights.weights_pos weights j)
  -- Separate the square root of the product and simplify `√(‖x‖²)` back to `‖x‖`.
  rw [hsum, Real.sqrt_mul htotal_nonneg, Real.sqrt_sq (norm_nonneg x)]

/-- Helper for Proposition 6.17: the weighted pairing is controlled by the product of the source
norm and the weighted tuple seminorm. -/
lemma continuousLocation_pairing_le_sqrt_total_mul_norm_mul_seminorm
    (weights : ContinuousLocationWeights ι) (x : E) (u : E₂) :
    ∑ j, (weights j : ℝ) * inner ℝ (u j) x ≤
      Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖ *
        continuousLocationDualTupleSeminorm E weights u := by
  -- Rewrite the pairing as a `PiLp` inner product between the scaled tuple and a weighted
  -- constant tuple.
  have hpair :
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x =
        inner ℝ (continuousLocationDualTupleScale E weights u)
          (WithLp.toLp 2 (fun j : ι ↦ Real.sqrt (weights j : ℝ) • x)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hweight_nonneg : 0 ≤ (weights j : ℝ) := by
      exact le_of_lt (ContinuousLocationWeights.weights_pos weights j)
    have hsqrt_mul :
        Real.sqrt (weights j : ℝ) * Real.sqrt (weights j : ℝ) = (weights j : ℝ) := by
      nlinarith [Real.sq_sqrt hweight_nonneg]
    rw [continuousLocationDualTupleScale_apply, real_inner_smul_left, real_inner_smul_right]
    calc
      (weights j : ℝ) * inner ℝ (u j) x
          = (Real.sqrt (weights j : ℝ) * Real.sqrt (weights j : ℝ)) * inner ℝ (u j) x := by
              rw [hsqrt_mul]
      _ = Real.sqrt (weights j : ℝ) * (Real.sqrt (weights j : ℝ) * inner ℝ (u j) x) := by
              ring
  -- Apply Cauchy-Schwarz and then evaluate the norm of the weighted constant tuple exactly.
  calc
    ∑ j, (weights j : ℝ) * inner ℝ (u j) x
        = inner ℝ (continuousLocationDualTupleScale E weights u)
            (WithLp.toLp 2 (fun j : ι ↦ Real.sqrt (weights j : ℝ) • x)) := hpair
    _ ≤ ‖continuousLocationDualTupleScale E weights u‖ *
          ‖WithLp.toLp 2 (fun j : ι ↦ Real.sqrt (weights j : ℝ) • x)‖ :=
        real_inner_le_norm _ _
    _ = continuousLocationDualTupleSeminorm E weights u *
          (Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖) := by
        rw [continuousLocationDualTupleSeminorm_eq_norm_scale,
          continuousLocation_weighted_constant_tuple_norm]
    _ = Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖ *
          continuousLocationDualTupleSeminorm E weights u := by
        ring

/-- Helper for Proposition 6.17: the normalized constant tuple has weighted norm `1` and attains
the pairing value `√P` against the same unit vector. -/
lemma continuousLocation_constant_unit_witness
    (weights : ContinuousLocationWeights ι) [Nonempty ι] {e : E} (he : ‖e‖ = 1) :
    continuousLocationDualTupleNorm E weights
        (fun _ : ι ↦ ((Real.sqrt (continuousLocationTotalPopulation weights))⁻¹ : ℝ) • e) = 1 ∧
      (∑ j, (weights j : ℝ) *
          inner ℝ ((((Real.sqrt (continuousLocationTotalPopulation weights))⁻¹ : ℝ) • e)) e) =
        Real.sqrt (continuousLocationTotalPopulation weights) := by
  let P := continuousLocationTotalPopulation weights
  let uStar : ι → E := fun _ ↦ ((Real.sqrt P)⁻¹ : ℝ) • e
  have hP_pos : 0 < P := continuousLocation_totalPopulation_pos (weights := weights)
  have hsqrt_pos : 0 < Real.sqrt P := Real.sqrt_pos.2 hP_pos
  have huStar_norm :
      continuousLocationDualTupleNorm E weights uStar = 1 := by
    -- Transport the weighted tuple norm to the ambient `PiLp` norm of the scaled constant tuple.
    rw [← continuousLocationDualTupleSeminorm_apply (E := E) weights uStar,
      continuousLocationDualTupleSeminorm_eq_norm_scale]
    have hscale :
        continuousLocationDualTupleScale E weights (WithLp.toLp 2 uStar) =
          WithLp.toLp 2 (fun j : ι ↦ Real.sqrt (weights j : ℝ) • (((Real.sqrt P)⁻¹ : ℝ) • e)) := by
      ext j
      simp [uStar, continuousLocationDualTupleScale_apply, smul_smul]
    rw [hscale]
    rw [show
      ‖WithLp.toLp 2
          (fun j : ι ↦ Real.sqrt (weights j : ℝ) • (((Real.sqrt P)⁻¹ : ℝ) • e))‖ =
        Real.sqrt P * ‖((Real.sqrt P)⁻¹ : ℝ) • e‖ by
          simpa [P] using
            (continuousLocation_weighted_constant_tuple_norm (E := E) weights
              (((Real.sqrt P)⁻¹ : ℝ) • e))]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt_pos), he]
    field_simp [hsqrt_pos.ne']
  have huStar_pair :
      ∑ j, (weights j : ℝ) * inner ℝ (uStar j) e = Real.sqrt P := by
    -- The witness is constant, so the pairing collapses to `P / √P = √P`.
    calc
      ∑ j, (weights j : ℝ) * inner ℝ (uStar j) e
          = ∑ j, (weights j : ℝ) * (((Real.sqrt P)⁻¹ : ℝ) * inner ℝ e e) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [uStar, real_inner_smul_left, mul_assoc]
      _ = (∑ j, (weights j : ℝ)) * (((Real.sqrt P)⁻¹ : ℝ) * inner ℝ e e) := by
          rw [Finset.sum_mul]
      _ = P * (((Real.sqrt P)⁻¹ : ℝ) * 1) := by
          simpa [P, continuousLocationTotalPopulation_def, real_inner_self_eq_norm_sq, he]
      _ = Real.sqrt P := by
          have hP_sq : P = Real.sqrt P * Real.sqrt P := by
            calc
              P = (Real.sqrt P) ^ 2 := by symm; exact Real.sq_sqrt hP_pos.le
              _ = Real.sqrt P * Real.sqrt P := by ring
          nth_rw 1 [hP_sq]
          field_simp [hsqrt_pos.ne']
  simpa [uStar, P] using And.intro huStar_norm huStar_pair

/-- Canonical owner form of Proposition 6.17: the induced norm of the continuous-location
smoothing map from the ambient norm on `E` to the weighted dual-tuple geometry is `√P`, where
`P = \sum_j m_j` is the total population weight. The `PiLp` realization is exposed through the
thin bridge `continuousLocationSmoothingMapPiLp E weights`, so the public theorem stays on
`Seminorm.primalDualOperatorNorm` without leaking the transport term. -/
theorem continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    ‖(continuousLocationSmoothingMapPiLp E weights).toLinearMap‖[
        normSeminorm ℝ E ⇀ continuousLocationDualTupleSeminorm E weights,*] =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  classical
  rw [Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing]
  change
    sSup ((fun xu : E × E₂ ↦ continuousLocationSmoothingMapPiLp E weights xu.1 xu.2) ''
      Set.prod {x : E | ‖x‖ ≤ 1} {u : E₂ | continuousLocationDualTupleSeminorm E weights u ≤ 1}) =
      Real.sqrt (continuousLocationTotalPopulation weights)
  by_cases hι : IsEmpty ι
  · letI := hι
    have himage :
        ((fun xu : E × E₂ ↦ continuousLocationSmoothingMapPiLp E weights xu.1 xu.2) ''
          Set.prod {x : E | ‖x‖ ≤ 1}
            {u : E₂ | continuousLocationDualTupleSeminorm E weights u ≤ 1}) = {0} := by
      ext y
      constructor
      · intro hy
        rcases hy with ⟨⟨x, u⟩, hxu, rfl⟩
        change continuousLocationSmoothingMapPiLp E weights x u = 0
        rw [continuousLocationSmoothingMapPiLp_apply]
        simp
      · intro hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        refine ⟨(0, 0), ?_, ?_⟩
        · exact ⟨by simp, by simp⟩
        · change continuousLocationSmoothingMapPiLp E weights 0 0 = 0
          rw [continuousLocationSmoothingMapPiLp_apply]
          simp
    have hP0 : continuousLocationTotalPopulation weights = 0 := by
      simp [continuousLocationTotalPopulation_def]
    rw [himage, csSup_singleton, hP0]
    simp
  · letI : Nonempty ι := not_isEmpty_iff.mp hι
    let S : Set ℝ :=
      ((fun xu : E × E₂ ↦ continuousLocationSmoothingMapPiLp E weights xu.1 xu.2) ''
        Set.prod {x : E | ‖x‖ ≤ 1}
          {u : E₂ | continuousLocationDualTupleSeminorm E weights u ≤ 1})
    have hS_nonempty : S.Nonempty := by
      refine ⟨0, ?_⟩
      refine ⟨(0, 0), ?_, ?_⟩
      · exact ⟨by simp, by simp⟩
      · change continuousLocationSmoothingMapPiLp E weights 0 0 = 0
        rw [continuousLocationSmoothingMapPiLp_apply]
        simp
    have hUpper :
        ∀ y ∈ S, y ≤ Real.sqrt (continuousLocationTotalPopulation weights) := by
      intro y hy
      rcases hy with ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
      have hx' : ‖x‖ ≤ 1 := hx
      have hu' : continuousLocationDualTupleSeminorm E weights u ≤ 1 := hu
      have hdu_nonneg : 0 ≤ continuousLocationDualTupleSeminorm E weights u := by
        exact apply_nonneg _ _
      have hmul :
          ‖x‖ * continuousLocationDualTupleSeminorm E weights u ≤ 1 := by
        simpa using mul_le_mul hx' hu' hdu_nonneg (show 0 ≤ (1 : ℝ) by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt (continuousLocationTotalPopulation weights) :=
        Real.sqrt_nonneg _
      calc
        continuousLocationSmoothingMapPiLp E weights x u
            = ∑ j, (weights j : ℝ) * inner ℝ (u j) x := by
                rw [continuousLocationSmoothingMapPiLp_apply]
        _ ≤ Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖ *
              continuousLocationDualTupleSeminorm E weights u :=
            continuousLocation_pairing_le_sqrt_total_mul_norm_mul_seminorm weights x u
        _ = Real.sqrt (continuousLocationTotalPopulation weights) *
              (‖x‖ * continuousLocationDualTupleSeminorm E weights u) := by
              ring
        _ ≤ Real.sqrt (continuousLocationTotalPopulation weights) * 1 :=
            mul_le_mul_of_nonneg_left hmul hsqrt_nonneg
        _ = Real.sqrt (continuousLocationTotalPopulation weights) := by ring
    obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
    let e : E := (‖x0‖⁻¹ : ℝ) • x0
    have he_norm : ‖e‖ = 1 := by
      simpa [e] using (norm_smul_inv_norm (𝕜 := ℝ) (x := x0) hx0)
    let uStar : ι → E :=
      fun _ ↦ ((Real.sqrt (continuousLocationTotalPopulation weights))⁻¹ : ℝ) • e
    have hwitness := continuousLocation_constant_unit_witness (weights := weights) (e := e) he_norm
    rcases hwitness with ⟨huStar_norm, huStar_pair⟩
    have huStar_ball :
        continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 uStar) ≤ 1 := by
      rw [continuousLocationDualTupleSeminorm_apply]
      exact le_of_eq huStar_norm
    have hvalue :
        continuousLocationSmoothingMapPiLp E weights e (WithLp.toLp 2 uStar) =
          Real.sqrt (continuousLocationTotalPopulation weights) := by
      rw [continuousLocationSmoothingMapPiLp_apply]
      simpa [uStar] using huStar_pair
    have hwitness_mem :
        Real.sqrt (continuousLocationTotalPopulation weights) ∈ S := by
      refine ⟨(e, WithLp.toLp 2 uStar), ?_, ?_⟩
      refine ⟨by simpa [he_norm], huStar_ball⟩
      simpa using hvalue
    have hS_bdd : BddAbove S := ⟨Real.sqrt (continuousLocationTotalPopulation weights), hUpper⟩
    have hsSup :
        sSup S = Real.sqrt (continuousLocationTotalPopulation weights) := by
      refine le_antisymm ?_ ?_
      · exact csSup_le hS_nonempty hUpper
      · exact le_csSup hS_bdd hwitness_mem
    simpa [S] using hsSup

/-- Proposition 6.17: rewriting the canonical induced-norm statement through
`continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation`,
`Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, `continuousLocationSmoothingMap_apply`, and
`continuousLocationDualTupleSeminorm_apply`, and then transporting back along
`PiLp.continuousLinearEquiv`, gives the source-facing unit-sphere formula for the weighted
pairing. -/
theorem continuousLocation_sSup_pairing_unitSpheres_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    sSup ((fun xu : E × (ι → E) ↦ ∑ j, (weights j : ℝ) * inner ℝ (xu.2 j) xu.1) ''
      Set.prod (sphere (0 : E) 1) {u | continuousLocationDualTupleNorm E weights u = 1}) =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  classical
  by_cases hι : IsEmpty ι
  · letI := hι
    have hdual_empty : {u | continuousLocationDualTupleNorm E weights u = 1} = (∅ : Set (ι → E)) := by
      ext u
      simp [continuousLocationDualTupleNorm_def, continuousLocationTotalPopulation_def]
    rw [hdual_empty]
    have hprod_empty :
        Set.prod (sphere (0 : E) 1) (∅ : Set (ι → E)) = (∅ : Set (E × (ι → E))) := by
      ext xu
      constructor
      · intro h
        exact h.2
      · intro h
        exact False.elim h
    have himage :
        ((fun xu : E × (ι → E) ↦ ∑ j, (weights j : ℝ) * inner ℝ (xu.2 j) xu.1) ''
          Set.prod (sphere (0 : E) 1) (∅ : Set (ι → E))) = (∅ : Set ℝ) := by
      rw [hprod_empty, Set.image_empty]
    have hP0 : continuousLocationTotalPopulation weights = 0 := by
      simp [continuousLocationTotalPopulation_def]
    rw [himage, Real.sSup_empty, hP0]
    simp
  · letI : Nonempty ι := not_isEmpty_iff.mp hι
    let S : Set ℝ :=
      ((fun xu : E × (ι → E) ↦ ∑ j, (weights j : ℝ) * inner ℝ (xu.2 j) xu.1) ''
        Set.prod (sphere (0 : E) 1) {u | continuousLocationDualTupleNorm E weights u = 1})
    obtain ⟨x0, hx0⟩ := exists_ne (0 : E)
    let e : E := (‖x0‖⁻¹ : ℝ) • x0
    have he_norm : ‖e‖ = 1 := by
      simpa [e] using (norm_smul_inv_norm (𝕜 := ℝ) (x := x0) hx0)
    have he_mem : e ∈ sphere (0 : E) 1 := by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, he_norm]
    let uStar : ι → E :=
      fun _ ↦ ((Real.sqrt (continuousLocationTotalPopulation weights))⁻¹ : ℝ) • e
    have hwitness := continuousLocation_constant_unit_witness (weights := weights) (e := e) he_norm
    rcases hwitness with ⟨huStar_norm, huStar_pair⟩
    have hS_nonempty : S.Nonempty := by
      refine ⟨Real.sqrt (continuousLocationTotalPopulation weights), ?_⟩
      refine ⟨(e, uStar), ?_, ?_⟩
      · exact ⟨he_mem, huStar_norm⟩
      · simpa [S, uStar] using huStar_pair
    have hUpper :
        ∀ y ∈ S, y ≤ Real.sqrt (continuousLocationTotalPopulation weights) := by
      intro y hy
      rcases hy with ⟨⟨x, u⟩, ⟨hx, hu⟩, rfl⟩
      have hx_norm : ‖x‖ = 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
        exact hx
      have hu_seminorm :
          continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 u) = 1 := by
        simpa [continuousLocationDualTupleSeminorm_apply] using hu
      calc
        ∑ j, (weights j : ℝ) * inner ℝ (u j) x
            = continuousLocationSmoothingMapPiLp E weights x (WithLp.toLp 2 u) := by
                symm
                rw [continuousLocationSmoothingMapPiLp_apply]
        _ = ∑ j, (weights j : ℝ) * inner ℝ ((WithLp.toLp 2 u) j) x := by
            rw [continuousLocationSmoothingMapPiLp_apply]
        _ ≤ Real.sqrt (continuousLocationTotalPopulation weights) * ‖x‖ *
              continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 u) := by
            exact continuousLocation_pairing_le_sqrt_total_mul_norm_mul_seminorm weights x
              (WithLp.toLp 2 u)
        _ = Real.sqrt (continuousLocationTotalPopulation weights) := by
            rw [hx_norm, hu_seminorm]
            ring
    have hwitness_mem :
        Real.sqrt (continuousLocationTotalPopulation weights) ∈ S := by
      refine ⟨(e, uStar), ?_, ?_⟩
      · exact ⟨he_mem, huStar_norm⟩
      · simpa [uStar] using huStar_pair
    have hS_bdd : BddAbove S := ⟨Real.sqrt (continuousLocationTotalPopulation weights), hUpper⟩
    refine le_antisymm ?_ ?_
    · exact csSup_le hS_nonempty hUpper
    · exact le_csSup hS_bdd hwitness_mem

end Geometry

end
