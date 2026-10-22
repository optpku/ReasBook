/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_3_1

open scoped Gradient

noncomputable section

/-- Classical decidability for propositions, used to evaluate the interior-membership branch in the
source-facing ambient universal-barrier formula. -/
local instance {p : Prop} : Decidable p := Classical.propDecidable p

/-- Helper for Theorem 5.4.2.2: the intrinsic universal-barrier owner
`x ↦ c₁ * log (V(x))` on `interior Q`. -/
def universalBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (Q : Set E) :
    interior Q → ℝ :=
  fun x ↦ c₁ * Real.log (universalBarrierVolume Q x)

/-- Helper for Theorem 5.4.2.2: evaluating `universalBarrier` recovers the scaled log-volume
formula on the intrinsic owner. -/
@[simp] theorem universalBarrier_eq_log_volume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (Q : Set E) (x : interior Q) :
    universalBarrier c₁ Q x =
      c₁ * Real.log (universalBarrierVolume Q x) := by
  -- The intrinsic owner is defined by the textbook `c₁ * log V` formula.
  simp [universalBarrier]

/-- Helper for Theorem 5.4.2.2: the ambient zero-extension of the intrinsic universal barrier. -/
def universalBarrierAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      universalBarrier c₁ Q ⟨x, hx⟩
    else
      0

/-- Helper for Theorem 5.4.2.2: on `interior Q`, the ambient owner agrees with the intrinsic
universal barrier. -/
@[simp] theorem universalBarrierAmbient_eq_universalBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    universalBarrierAmbient c₁ Q x = universalBarrier c₁ Q ⟨x, hx⟩ := by
  -- Freeze the ambient `if` branch once at an interior point.
  simp [universalBarrierAmbient, hx]

/-- Helper for Theorem 5.4.2.2: on `interior Q`, the ambient owner reduces all the way to the
scaled log-volume branch. -/
@[simp] theorem universalBarrierAmbient_eq_log_volume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    universalBarrierAmbient c₁ Q x =
      c₁ * Real.log (universalBarrierVolume Q ⟨x, hx⟩) := by
  -- Compose the ambient-to-intrinsic bridge with the intrinsic evaluation formula.
  rw [universalBarrierAmbient_eq_universalBarrier hx, universalBarrier_eq_log_volume]

/-- Helper for Theorem 5.4.2.2: outside `interior Q`, the ambient owner is the zero branch. -/
@[simp] theorem universalBarrierAmbient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∉ interior Q) :
    universalBarrierAmbient c₁ Q x = 0 := by
  -- Outside the interior, the ambient owner is exactly its totalizing zero branch.
  simp [universalBarrierAmbient, hx]

/-- Helper for Theorem 5.4.2.2: the source-facing ambient owner for the universal barrier formula,
written directly in the explicit `if x ∈ interior Q then c₁ * log V(x) else 0` normal form used by
the pointwise slice argument. -/
def explicitUniversalBarrierAmbient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (c₁ : ℝ) (Q : Set E) :
    E → ℝ :=
  fun x ↦
    if hx : x ∈ interior Q then
      c₁ * Real.log (universalBarrierVolume Q ⟨x, hx⟩)
    else
      0

/-- Helper for Theorem 5.4.2.2: on `interior Q`, the explicit ambient owner reduces to the scaled
log-volume branch. -/
@[simp] theorem explicitUniversalBarrierAmbient_eq_log_volume
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) :
    explicitUniversalBarrierAmbient c₁ Q x =
      c₁ * Real.log (universalBarrierVolume Q ⟨x, hx⟩) := by
  -- On the domain, the source-facing ambient owner takes its intended log-volume branch.
  simp [explicitUniversalBarrierAmbient, hx]

/-- Helper for Theorem 5.4.2.2: outside `interior Q`, the explicit ambient owner is the zero
extension used only to totalize the source formula. -/
@[simp] theorem explicitUniversalBarrierAmbient_eq_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∉ interior Q) :
    explicitUniversalBarrierAmbient c₁ Q x = 0 := by
  -- Off the domain, the source-facing ambient owner is exactly the totalizing zero branch.
  simp [explicitUniversalBarrierAmbient, hx]

/-- Helper for Theorem 5.4.2.2: an interior point stays inside `interior Q` along a short
segment in any fixed direction. -/
theorem lineMap_eventually_mem_interior
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ), x + t • u ∈ interior Q := by
  -- Open interior gives a neighborhood of `x`, and continuity of the line map pulls it back to
  -- a neighborhood of `0`.
  have hinterior : interior Q ∈ nhds x := isOpen_interior.mem_nhds hx
  have hlineCont : Continuous (fun t : ℝ ↦ x + t • u) := by
    -- The affine line map is continuous in the scalar parameter.
    simpa using
      ((continuous_const : Continuous fun _ : ℝ ↦ x).add
        ((continuous_id : Continuous fun t : ℝ ↦ t).smul
          (continuous_const : Continuous fun _ : ℝ ↦ u)))
  have hline :
      Filter.Tendsto (fun t : ℝ ↦ x + t • u) (nhds (0 : ℝ)) (nhds x) := by
    -- The line map is continuous and takes `0` to `x`.
    simpa [zero_smul, add_zero] using
      hlineCont.tendsto (0 : ℝ)
  exact hline hinterior

/-- Helper for Theorem 5.4.2.2: near `t = 0`, the explicit ambient owner stays on its log-volume
branch along the line `t ↦ x + t • u`. -/
theorem explicitUniversalBarrierAmbient_hasLogVolumeBranchAlongLine
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {c₁ : ℝ} {Q : Set E} {x : E} (hx : x ∈ interior Q) (u : E) :
    ∀ᶠ t : ℝ in nhds (0 : ℝ),
      ∃ hxt : x + t • u ∈ interior Q,
        explicitUniversalBarrierAmbient c₁ Q (x + t • u) =
          c₁ * Real.log (universalBarrierVolume Q ⟨x + t • u, hxt⟩) := by
  -- Route correction: freeze the `if x ∈ interior Q` branch once on a neighborhood of `0`
  -- instead of re-unfolding the ambient owner inside every slice calculation.
  filter_upwards [lineMap_eventually_mem_interior (Q := Q) hx u] with t ht
  refine ⟨ht, ?_⟩
  -- Once the line stays in the interior branch, the source-facing owner is literally `c₁ log V`.
  simp [explicitUniversalBarrierAmbient, ht]

/-- Helper for Theorem 5.4.2.2: pointwise `C³` data on the open domain `interior Q` upgrades
directly to `ContDiffOn ℝ 3`. -/
theorem explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) := by
  -- The interior is open, so pointwise `C³` control is exactly the `ContDiffOn` owner.
  exact (isOpen_interior.contDiffOn_iff).2 hcontAt

/-- Helper for Theorem 5.4.2.2: a `C²` scalar field has a differentiable gradient at the base
point because the gradient is the Fréchet derivative transported through the Riesz isomorphism. -/
theorem differentiableAt_gradient_of_contDiffAt_two
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → ℝ} {x : E} (hF : ContDiffAt ℝ 2 F x) :
    DifferentiableAt ℝ (∇ F) x := by
  -- Rewrite the gradient through the continuous linear Riesz map and differentiate `fderiv`.
  let D : StrongDual ℝ E →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ F) x := by
    exact
      (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
        one_ne_zero
  change DifferentiableAt ℝ (fun z ↦ D (fderiv ℝ F z)) x
  exact (D.hasFDerivAt.comp x hfdiff.hasFDerivAt).differentiableAt

/-- Helper for Theorem 5.4.2.2: at a `C³` base point, the first three derivatives of the
directional slice at `0` agree with the ambient gradient, Hessian quadratic form, and third
directional-derivative owners. -/
theorem directionalSliceDerivativesAtZero_eq_ambientOwners
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → ℝ} {x u : E} (hFx : ContDiffAt ℝ 3 F x) :
    deriv (directionalSlice F x u) 0 = inner ℝ (∇ F x) u ∧
      iteratedDeriv 2 (directionalSlice F x u) 0 = inner ℝ u (hessian F x u) ∧
      iteratedDeriv 3 (directionalSlice F x u) 0 = thirdDirectionalDerivative F x u := by
  -- Route correction: freeze the scalar slice owners once so the packaging theorem can rewrite
  -- them directly instead of redoing gradient/Hessian transports in every branch.
  have hdiff : DifferentiableAt ℝ F x := by
    exact hFx.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · -- The first slice derivative is the gradient pairing in the slice direction.
    calc
      deriv (directionalSlice F x u) 0 = lineDeriv ℝ F x u := by
        rfl
      _ = fderiv ℝ F x u := hdiff.lineDeriv_eq_fderiv
      _ = inner ℝ (∇ F x) u := by
        rw [← inner_gradient_left hdiff]
  · -- The second slice derivative is the Hessian quadratic form.
    simpa [secondDirectionalDerivative] using
      (secondDirectionalDerivative_eq_hessian_quadratic_form
        (f := F) (x := x) (u := u) (hFx.of_le (by norm_num)))
  · -- The third slice derivative is definitionally the chapter owner.
    rfl

/-- Helper for Theorem 5.4.2.2: a one-dimensional barrier witness on `Set.Ioo (-ε) ε` supplies
the scalar `C³` data and pointwise Hessian/third-derivative/barrier inequalities at `0`. -/
theorem slicePointwiseCoreAtZero_of_barrierOnInterval
    {ε : ℝ} (hεpos : 0 < ε) {ν : NNReal} {ψ : ℝ → ℝ}
    (hbarrier : IsSelfConcordantBarrierOnWith (Set.Ioo (-ε) ε) ν ψ) :
    ContDiffAt ℝ 3 ψ 0 ∧
      0 ≤ iteratedDeriv 2 ψ 0 ∧
      |iteratedDeriv 3 ψ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) ∧
      (deriv ψ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
  -- The interval barrier owner is centered at `0`, so all owner fields can be read there.
  have h0 : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> nlinarith
  have hcont :
      ContDiffAt ℝ 3 ψ 0 := by
    -- Read the pointwise `C³` owner from the standard-self-concordance parent on the interval.
    exact hbarrier.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt (isOpen_Ioo.mem_nhds h0)
  have hPos : (hessian ψ 0).IsPositive :=
    hbarrier.toIsStandardSelfConcordantOn.hessian_isPositive h0
  have hquad :
      0 ≤ inner ℝ (1 : ℝ) (hessian ψ 0 (1 : ℝ)) :=
    hbarrier.toIsStandardSelfConcordantOn.hessian_posSemidef h0 1
  have hthirdBound :
      |thirdDirectionalDerivative ψ 0 (1 : ℝ)| ≤
        2 * hessianLocalNorm ψ 0 (1 : ℝ) ^ (3 : ℕ) :=
    by
      simpa [one_mul] using
        hbarrier.toIsStandardSelfConcordantOn.third_deriv_bound h0 1
  have hgradSq :
      (inner ℝ (∇ ψ 0) (1 : ℝ)) ^ (2 : ℕ) ≤
        (ν : ℝ) * inner ℝ (1 : ℝ) (hessian ψ 0 (1 : ℝ)) := by
    -- Convert the owner barrier inequality into the gradient-square estimate and specialize to `1`.
    exact
      (IsSelfConcordantBarrierOnWith.gradient_sq_le_mul_hessian_iff_barrier_bound
          (F := ψ) (x := 0) (μ := ν) hPos).1
        (fun u ↦ hbarrier.barrier_parameter_bound h0 u) 1
  rcases
    directionalSliceDerivativesAtZero_eq_ambientOwners
      (F := ψ) (x := (0 : ℝ)) (u := (1 : ℝ)) hcont with
    ⟨hderiv, hsecond, hthirdEq⟩
  have hsliceId : directionalSlice ψ (0 : ℝ) (1 : ℝ) = ψ := by
    -- On `ℝ`, the affine slice through `0` in direction `1` is the identity parameterization.
    funext t
    simp [directionalSlice]
  have hderiv' : deriv ψ 0 = inner ℝ (∇ ψ 0) (1 : ℝ) := by
    -- The scalar line slice `t ↦ 0 + t • 1` is just the identity parameterization.
    rw [hsliceId] at hderiv
    exact hderiv
  have hsecond' : iteratedDeriv 2 ψ 0 = inner ℝ (1 : ℝ) (hessian ψ 0 (1 : ℝ)) := by
    -- The second slice derivative is the Hessian quadratic form in direction `1`.
    rw [hsliceId] at hsecond
    exact hsecond
  have hthirdEq' : iteratedDeriv 3 ψ 0 = thirdDirectionalDerivative ψ 0 (1 : ℝ) := by
    -- The third slice owner collapses to the scalar third iterated derivative at the origin.
    rw [hsliceId] at hthirdEq
    exact hthirdEq
  refine ⟨hcont, ?_, ?_, ?_⟩
  · -- Rewrite the interval Hessian positivity to the raw second derivative at `0`.
    rwa [← hsecond'] at hquad
  · -- Rewrite the owner cubic bound to the scalar third-derivative inequality at `0`.
    calc
      |iteratedDeriv 3 ψ 0| = |thirdDirectionalDerivative ψ 0 (1 : ℝ)| := by
        rw [hthirdEq']
      _ ≤ 2 * hessianLocalNorm ψ 0 (1 : ℝ) ^ (3 : ℕ) := hthirdBound
      _ = 2 * (Real.sqrt (iteratedDeriv 2 ψ 0)) ^ (3 : ℕ) := by
        rw [hessianLocalNorm_def, ← hsecond']
  · -- The barrier parameter inequality becomes the scalar gradient-square bound at `0`.
    calc
      (deriv ψ 0) ^ (2 : ℕ) = (inner ℝ (∇ ψ 0) (1 : ℝ)) ^ (2 : ℕ) := by
        rw [hderiv']
      _ ≤ (ν : ℝ) * inner ℝ (1 : ℝ) (hessian ψ 0 (1 : ℝ)) := hgradSq
      _ = (ν : ℝ) * iteratedDeriv 2 ψ 0 := by
        rw [← hsecond']

/-- Helper for Theorem 5.4.2.2: pointwise `ContDiffAt` and scalar directional-slice inequalities
package directly into the ambient explicit universal-barrier pointwise core. -/
theorem explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndSliceData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hslice :
      ∀ x ∈ interior Q, ∀ u,
        let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
        0 ≤ iteratedDeriv 2 φ 0 ∧
          |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) ∧
          (deriv φ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 φ 0) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  have hcont :
      ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) :=
    explicitUniversalBarrierAmbient_contDiffOn_of_pointwiseData hcontAt
  have hpointwise :
      ∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) ∧
          |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
            2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) ∧
          (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
            (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
    intro x hx u
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hslice_xu := hslice x hx u
    dsimp [φ] at hslice_xu
    rcases
      directionalSliceDerivativesAtZero_eq_ambientOwners
        (F := explicitUniversalBarrierAmbient c₁ Q) (x := x) (u := u) (hcontAt x hx) with
      ⟨hderiv, hsecond, hthird⟩
    refine ⟨?_, ?_, ?_⟩
    · -- The scalar second-derivative inequality is exactly Hessian quadratic-form nonnegativity.
      rw [← hsecond]
      exact hslice_xu.1
    · -- Rewrite the scalar cubic estimate into the ambient local-norm owner.
      calc
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u|
            = |iteratedDeriv 3 φ 0| := by
                rw [← hthird]
        _ ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) := hslice_xu.2.1
        _ = 2 * (Real.sqrt (inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)))
              ^ (3 : ℕ) := by
                rw [hsecond]
        _ = 2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ) := by
                rw [hessianLocalNorm_def]
    · -- The scalar barrier-parameter inequality rewrites to the ambient gradient/Hessian owners.
      calc
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ)
            = (deriv φ 0) ^ (2 : ℕ) := by
                rw [hderiv]
        _ ≤ (ν : ℝ) * iteratedDeriv 2 φ 0 := hslice_xu.2.2
        _ = (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u) := by
                rw [hsecond]
  refine ⟨hcont, ?_, ?_, ?_⟩
  · -- Read off the Hessian quadratic-form nonnegativity from the packaged pointwise data.
    intro x hx u
    exact (hpointwise x hx u).1
  · -- Read off the cubic third-derivative bound from the same packaged pointwise data.
    intro x hx u
    exact (hpointwise x hx u).2.1
  · -- The barrier-parameter inequality is the third field of the packaged pointwise data.
    intro x hx u
    exact (hpointwise x hx u).2.2

/-- Helper for Theorem 5.4.2.2: interval-local barrier witnesses on directional slices package
directly into the ambient explicit universal-barrier pointwise core. -/
theorem explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndBarrierSliceData
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} {c₁ : ℝ} {ν : NNReal}
    (hcontAt :
      ∀ x ∈ interior Q, ContDiffAt ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) x)
    (hsliceBarrier :
      ∀ x ∈ interior Q, ∀ u,
        ∃ ε > 0, ∃ ψ : ℝ → ℝ,
          directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u =ᶠ[nhds (0 : ℝ)] ψ ∧
          IsSelfConcordantBarrierOnWith (Set.Ioo (-ε) ε) ν ψ) :
    ContDiffOn ℝ 3 (explicitUniversalBarrierAmbient c₁ Q) (interior Q) ∧
      (∀ x ∈ interior Q, ∀ u,
        0 ≤ inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) ∧
      (∀ x ∈ interior Q, ∀ u,
        |thirdDirectionalDerivative (explicitUniversalBarrierAmbient c₁ Q) x u| ≤
          2 * hessianLocalNorm (explicitUniversalBarrierAmbient c₁ Q) x u ^ (3 : ℕ)) ∧
      (∀ x ∈ interior Q, ∀ u,
        (inner ℝ (∇ (explicitUniversalBarrierAmbient c₁ Q) x) u) ^ (2 : ℕ) ≤
          (ν : ℝ) * inner ℝ u (hessian (explicitUniversalBarrierAmbient c₁ Q) x u)) := by
  have hslice :
      ∀ x ∈ interior Q, ∀ u,
        let φ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
        0 ≤ iteratedDeriv 2 φ 0 ∧
          |iteratedDeriv 3 φ 0| ≤ 2 * (Real.sqrt (iteratedDeriv 2 φ 0)) ^ (3 : ℕ) ∧
          (deriv φ 0) ^ (2 : ℕ) ≤ (ν : ℝ) * iteratedDeriv 2 φ 0 := by
    intro x hx u
    rcases hsliceBarrier x hx u with ⟨ε, hεpos, ψ, heq, hbarrier⟩
    rcases
      slicePointwiseCoreAtZero_of_barrierOnInterval hεpos hbarrier with
      ⟨_, hsecond, hthird, hgradSq⟩
    let φ : ℝ → ℝ := directionalSlice (explicitUniversalBarrierAmbient c₁ Q) x u
    have hderiv_eq : deriv φ 0 = deriv ψ 0 := by
      simpa [φ] using Filter.EventuallyEq.deriv_eq heq
    have hsecond_eq : iteratedDeriv 2 φ 0 = iteratedDeriv 2 ψ 0 := by
      simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 2 heq
    have hthird_eq : iteratedDeriv 3 φ 0 = iteratedDeriv 3 ψ 0 := by
      simpa [φ] using Filter.EventuallyEq.iteratedDeriv_eq 3 heq
    dsimp [φ]
    refine ⟨?_, ?_, ?_⟩
    · -- Transport the scalar Hessian lower bound across the neighborhood equality.
      rw [hsecond_eq]
      exact hsecond
    · -- Transport the scalar cubic bound across the neighborhood equality.
      rw [hsecond_eq, hthird_eq]
      exact hthird
    · -- Transport the scalar barrier-parameter inequality across the neighborhood equality.
      rw [hderiv_eq, hsecond_eq]
      exact hgradSq
  -- The generic slice-data packaging theorem finishes the ambient pointwise core.
  exact explicitUniversalBarrierAmbient_pointwiseCore_of_contDiffAtAndSliceData hcontAt hslice
