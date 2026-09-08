module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
public import ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- The shape and scale increments of the exact mixed two-leg map along
`b = ε`, `r = ε ^ 2`, with input coefficients `z = (P, J)`. -/
@[expose] def transverseIncrement (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  let y := map ε (input (ε, z.1, z.2) (ε ^ 2))
  (y.2.1 - 2, y.2.2 - 1)

/-- The exact weighted-path transverse increment evaluates by specializing the mixed map. -/
theorem transverseIncrement_apply (ε P J : ℝ) :
    transverseIncrement ε (P, J) =
      let y := map ε (input (ε, P, J) (ε ^ 2))
      (y.2.1 - 2, y.2.2 - 1) := by
  rfl

/-- The affine leading map on the transverse coefficients `(P, J)`. -/
@[expose] def leadingTransverse (z : ℝ × ℝ) : ℝ × ℝ :=
  ((6 * z.2 - z.1 + 348) / 9, 8)

/-- The affine leading transverse map sends `(P, J)` to
`((6 * J - P + 348) / 9, 8)`. -/
theorem leadingTransverse_apply (P J : ℝ) :
    leadingTransverse (P, J) = ((6 * J - P + 348) / 9, 8) := by
  rfl

/-- After normalization by `ε ^ 3`, the exact transverse increment along
`b = ε` and `r = ε ^ 2` is asymptotic to the affine leading transverse map. -/
theorem transverseIncrement_asymptotic (P J : ℝ) :
    (fun ε ↦
      (ε ^ 3)⁻¹ • transverseIncrement ε (P, J) - leadingTransverse (P, J))
      =o[𝓝[≠] 0] (fun _ ↦ (1 : ℝ)) := by
  let β : ℝ := 1 / 8
  let B : ℝ := dist (P, J) (0 : ℝ × ℝ)
  let shapeRemainder : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
    let y := map θ.1 (input θ r)
    y.2.1 - 2 - (θ.1 * (6 * θ.2.2 - θ.2.1 + 348) / 9) * r
  let scaleRemainder : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
    let y := map θ.1 (input θ r)
    y.2.2 - 1 - 8 * θ.1 * r
  have hβ : 0 < β := by
    norm_num [β]
  have hβsmall : β < 1 / 4 := by
    norm_num [β]
  have hB : 0 ≤ B := dist_nonneg
  obtain ⟨Cshape, _, hshapeRaw⟩ := shapeExpansion β B hβ hβsmall hB
  obtain ⟨Cscale, _, hscaleRaw⟩ := scaleExpansion β B hβ hβsmall hB
  have hshape : Asymptotics.IsUniformRemainderOn
      shapeRemainder (parameterSet β B) Cshape 2 := by
    simpa only [shapeRemainder] using hshapeRaw
  have hscale : Asymptotics.IsUniformRemainderOn
      scaleRemainder (parameterSet β B) Cscale 2 := by
    simpa only [scaleRemainder] using hscaleRaw
  have habsTendsto : Tendsto (fun ε : ℝ ↦ |ε|) (𝓝 0) (𝓝 0) := by
    have habsContinuous : ContinuousAt (fun ε : ℝ ↦ |ε|) 0 :=
      continuous_abs.continuousAt
    simpa [ContinuousAt] using habsContinuous
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < β :=
    (habsTendsto.eventually (Iio_mem_nhds hβ)).filter_mono inf_le_left
  have hcoeff : dist (P, J) (0 : ℝ × ℝ) ≤ B := by
    simp [B]
  have hparameter : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), (ε, P, J) ∈ parameterSet β B := by
    filter_upwards [hsmall] with ε hε
    rw [mem_parameterSet]
    refine ⟨abs_le.mp hε.le, ?_⟩
    simpa only [Metric.mem_closedBall] using hcoeff
  have diagonalLittleO (R : (ℝ × ℝ × ℝ) → ℝ → ℝ) (C : ℝ)
      (hR : Asymptotics.IsUniformRemainderOn R (parameterSet β B) C 2) :
      (fun ε : ℝ ↦ (ε ^ 3)⁻¹ • R (ε, P, J) (ε ^ 2))
        =o[𝓝[≠] 0] (fun _ ↦ (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    unfold Asymptotics.IsUniformRemainderOn at hR
    obtain ⟨δ, hδ, hbound⟩ := hR
    have hsquareTendsto :
        Tendsto (fun ε : ℝ ↦ |ε ^ 2|) (𝓝 0) (𝓝 0) := by
      have hsquareContinuous : ContinuousAt (fun ε : ℝ ↦ |ε ^ 2|) 0 :=
        (continuousAt_id.pow 2).abs
      simpa [ContinuousAt] using hsquareContinuous
    have hsquare : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε ^ 2| < δ :=
      (hsquareTendsto.eventually (Iio_mem_nhds hδ)).filter_mono inf_le_left
    have hcoefficientTendsto :
        Tendsto (fun ε : ℝ ↦ |C| * |ε|) (𝓝 0) (𝓝 0) := by
      have hconstant : ContinuousAt (fun _ : ℝ ↦ |C|) 0 :=
        continuousAt_const
      have habsContinuous : ContinuousAt (fun ε : ℝ ↦ |ε|) 0 :=
        continuous_abs.continuousAt
      have hcontinuous : ContinuousAt (fun ε : ℝ ↦ |C| * |ε|) 0 :=
        hconstant.mul habsContinuous
      simpa [ContinuousAt] using hcontinuous
    have hcoefficient : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |C| * |ε| < c :=
      (hcoefficientTendsto.eventually (Iio_mem_nhds hc)).filter_mono inf_le_left
    filter_upwards [hparameter, hsquare, hcoefficient, self_mem_nhdsWithin] with
        ε hεparameter hεδ hεcoefficient hεoutside
    have hε : ε ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hεoutside
    have hboundAt := hbound (ε, P, J) hεparameter (ε ^ 2) hεδ
    have hboundAbs :
        ‖R (ε, P, J) (ε ^ 2)‖ ≤ |C| * |ε ^ 2| ^ (2 : ℝ) :=
      hboundAt.trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (Real.rpow_nonneg (abs_nonneg _) _))
    calc
      ‖(ε ^ 3)⁻¹ • R (ε, P, J) (ε ^ 2)‖ =
          |(ε ^ 3)⁻¹| * ‖R (ε, P, J) (ε ^ 2)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |(ε ^ 3)⁻¹| * (|C| * |ε ^ 2| ^ (2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hboundAbs (abs_nonneg _)
      _ = |C| * |ε| := by
        rw [abs_inv, abs_pow, Real.rpow_two, abs_pow]
        field_simp [abs_ne_zero.mpr hε]
      _ ≤ c := hεcoefficient.le
      _ = c * ‖(1 : ℝ)‖ := by
        norm_num
  have hshapeLittleO := diagonalLittleO shapeRemainder Cshape hshape
  have hscaleLittleO := diagonalLittleO scaleRemainder Cscale hscale
  have hpair := hshapeLittleO.prod_left hscaleLittleO
  have hnormalized (ε : ℝ) (hε : ε ≠ 0) :
      (ε ^ 3)⁻¹ • transverseIncrement ε (P, J) - leadingTransverse (P, J) =
        ((ε ^ 3)⁻¹ • shapeRemainder (ε, P, J) (ε ^ 2),
          (ε ^ 3)⁻¹ • scaleRemainder (ε, P, J) (ε ^ 2)) := by
    rw [transverseIncrement_apply, leadingTransverse_apply]
    ext <;> simp [shapeRemainder, scaleRemainder]
    · field_simp [hε]
    · field_simp [hε]
  have hfunctions :
      (fun ε : ℝ ↦
        ((ε ^ 3)⁻¹ • shapeRemainder (ε, P, J) (ε ^ 2),
          (ε ^ 3)⁻¹ • scaleRemainder (ε, P, J) (ε ^ 2))) =ᶠ[𝓝[≠] 0]
        (fun ε ↦
          (ε ^ 3)⁻¹ • transverseIncrement ε (P, J) - leadingTransverse (P, J)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεne : ε ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hε
    exact (hnormalized ε hεne).symm
  have hone :
      (fun _ : ℝ ↦ (1 : ℝ)) =ᶠ[𝓝[≠] 0] (fun _ : ℝ ↦ (1 : ℝ)) := by
    rfl
  exact hpair.congr' hfunctions hone

/-- The derivative of the affine leading transverse map acts with matrix rows
`(-1 / 9, 2 / 3)` and `(0, 0)`. -/
theorem leadingTransverse_fderiv_apply (z v : ℝ × ℝ) :
    fderiv ℝ leadingTransverse z v =
      ((-(1 : ℝ) / 9) * v.1 + ((2 : ℝ) / 3) * v.2, 0) := by
  let L₁ : (ℝ × ℝ) →L[ℝ] ℝ :=
    ((-(1 : ℝ) / 9) • ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (((2 : ℝ) / 3) • ContinuousLinearMap.snd ℝ ℝ ℝ)
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := L₁.prod 0
  let c : ℝ × ℝ := ((348 : ℝ) / 9, 8)
  have hfun : leadingTransverse = fun w => L w + c := by
    funext w
    rcases w with ⟨P, J⟩
    rw [leadingTransverse_apply]
    simp [L, L₁, c]
    ring
  have hderiv : HasFDerivAt (fun w => L w + c) L z :=
    L.hasFDerivAt.add_const c
  rw [hfun, hderiv.fderiv]
  simp [L, L₁]

/-- The coefficient pair `(198 / 5, 8)` is fixed by the affine leading transverse map. -/
theorem leadingTransverse_fixedCoefficient :
    leadingTransverse ((198 / 5 : ℝ), 8) = ((198 / 5 : ℝ), 8) := by
  rw [leadingTransverse_apply]
  norm_num

end DFP.TwoLeg.Mixed
