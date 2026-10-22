/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.ActualObjective
public import ReasLib.Optimization.DFP.Polar.PhysicalRealization
public import ReasLib.Optimization.DFP.Polar.HolderSharpness
public import ReasLib.Optimization.DFP.Polar.WolfeRatios
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample

public section

noncomputable section

open Set Filter
open scoped Matrix Topology ContDiff

namespace DFP.Polar.PlanarCounterexample

/-- Helper for thm:main: the actual objective's canonical gradient sequence is
exactly the original prescribed polar gradient sequence. -/
theorem gradients_eq_source {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) :
    DFP.gradients (InterpolationSum.polarObjective p κ) p.point = p.gradient := by
  funext k
  rw [DFP.gradients_apply]
  exact (h.endpoints k).2.1

/-- Helper for thm:main: the source physical search law is the canonical inverse-DFP
step, with the original positive step length and inverse Hessian unchanged. -/
theorem step_eq_source_chord (p : Parameters)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    DFP.steps (PhysicalRealization.prescribedStepLength p)
      (DFP.directions p.inverseHessian p.gradient) k = p.point (k + 1) - p.point k := by
  apply WithLp.ofLp_injective
  simpa only [DFP.steps_apply, DFP.directions_apply, WithLp.ofLp_smul, WithLp.ofLp_neg,
    WithLp.ofLp_toLp, PhysicalRealization.chord_def, neg_smul, smul_neg] using
    (hphysical k).search.symm

/-- Helper for thm:main: interpolation identifies the canonical search step with
the exact source point difference at every iteration. -/
theorem canonical_step_eq_chord {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    DFP.steps (PhysicalRealization.prescribedStepLength p)
      (DFP.directions p.inverseHessian
        (DFP.gradients (InterpolationSum.polarObjective p κ) p.point)) k =
      p.point (k + 1) - p.point k := by
  rw [gradients_eq_source h]
  exact step_eq_source_chord p hphysical k

/-- Helper for thm:main: the canonical gradient change has exactly the original
source physical secant coordinates. -/
theorem canonical_gradientChange_eq_secant {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) (k : ℕ) :
    WithLp.ofLp (DFP.gradientChanges
      (DFP.gradients (InterpolationSum.polarObjective p κ) p.point) k) =
        PhysicalRealization.secant p k := by
  rw [gradients_eq_source h, DFP.gradientChanges_apply, PhysicalRealization.secant_def]

/-- Helper for thm:main: the source positive secant pairing discharges the canonical
DFP denominator without assuming it in the final theorem. -/
theorem canonical_secantDenominator_ne {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    WithLp.ofLp (DFP.steps (PhysicalRealization.prescribedStepLength p)
        (DFP.directions p.inverseHessian
          (DFP.gradients (InterpolationSum.polarObjective p κ) p.point)) k) ⬝ᵥ
      WithLp.ofLp (DFP.gradientChanges
        (DFP.gradients (InterpolationSum.polarObjective p κ) p.point) k) ≠ 0 := by
  rw [canonical_step_eq_chord h hphysical, canonical_gradientChange_eq_secant h,
    ← PhysicalRealization.chord_def]
  exact ne_of_gt (hphysical k).curvature_pos

/-- Helper for thm:main: the exact source point sequence obeys the canonical
inverse-DFP point successor law. -/
theorem canonical_point_succ {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    p.point (k + 1) = p.point k +
      DFP.steps (PhysicalRealization.prescribedStepLength p)
        (DFP.directions p.inverseHessian
          (DFP.gradients (InterpolationSum.polarObjective p κ) p.point)) k := by
  rw [canonical_step_eq_chord h hphysical]
  abel

/-- Helper for thm:main: the original rotated inverse-Hessian sequence satisfies
the canonical classical inverse-DFP update with the actual objective gradients. -/
theorem canonical_inverseHessian_succ {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    p.inverseHessian (k + 1) = Matrix.inverseDFPUpdate (p.inverseHessian k)
      (WithLp.ofLp (DFP.steps (PhysicalRealization.prescribedStepLength p)
        (DFP.directions p.inverseHessian
          (DFP.gradients (InterpolationSum.polarObjective p κ) p.point)) k))
      (WithLp.ofLp (DFP.gradientChanges
        (DFP.gradients (InterpolationSum.polarObjective p κ) p.point) k)) := by
  rw [canonical_step_eq_chord h hphysical, canonical_gradientChange_eq_secant h,
    ← PhysicalRealization.chord_def]
  exact (hphysical k).inverseDFPUpdate

/-- Helper for thm:main: the C² actual objective is differentiable at each
original prescribed point. -/
theorem objective_differentiableAt {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) (k : ℕ) :
    DifferentiableAt ℝ (InterpolationSum.polarObjective p κ) (p.point k) := by
  exact (h.objective_contDiff.differentiable two_ne_zero).differentiableAt

/-- Helper for thm:main: the canonical inverse-DFP trajectory stores the exact
original polar sequences. All proof obligations are separately named source laws. -/
def iteration {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) : DFP.InverseIteration (Fin 2) :=
  DFP.InverseIteration.ofSequences (InterpolationSum.polarObjective p κ)
    (PhysicalRealization.prescribedStepLength p) p.point p.inverseHessian
    (objective_differentiableAt h) (fun k ↦ (hphysical k).inverseHessian_posDef)
    (canonical_secantDenominator_ne h hphysical) (canonical_point_succ h hphysical)
    (canonical_inverseHessian_succ h hphysical)

/-- Helper for thm:main: the packaged iteration's objective is the unchanged
explicit cutoff objective. -/
theorem iteration_objective {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    (iteration h hphysical).objective = InterpolationSum.polarObjective p κ := by
  rw [iteration, DFP.InverseIteration.ofSequences_objective]

/-- Helper for thm:main: the packaged iteration stores the original positive
source step-length sequence. -/
theorem iteration_stepLength {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    (iteration h hphysical).stepLength = PhysicalRealization.prescribedStepLength p := by
  rw [iteration, DFP.InverseIteration.ofSequences_stepLength]

/-- Helper for thm:main: each packaged iterate is the corresponding original
polar point, rather than a transported or independently chosen point. -/
theorem iteration_point {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    (iteration h hphysical).point k = p.point k := by
  rw [iteration, DFP.InverseIteration.ofSequences_point]

/-- Helper for thm:main: the full packaged point sequence is exactly the source sequence. -/
theorem iteration_point_eq {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    (iteration h hphysical).point = p.point := by
  funext k
  exact iteration_point h hphysical k

/-- Helper for thm:main: the packaged inverse Hessians are the original
source matrices expressed in fixed physical coordinates. -/
theorem iteration_inverseHessian {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    (iteration h hphysical).inverseHessian k = p.inverseHessian k := by
  rw [iteration, DFP.InverseIteration.ofSequences_inverseHessian]

/-- Helper for thm:main: the full inverse-Hessian sequence retains the original construction. -/
theorem iteration_inverseHessian_eq {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    (iteration h hphysical).inverseHessian = p.inverseHessian := by
  funext k
  exact iteration_inverseHessian h hphysical k

/-- Helper for thm:main: the packaged canonical gradient sequence equals the
actual prescribed source gradients at every index. -/
theorem iteration_gradients_eq {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    DFP.gradients (iteration h hphysical).objective (iteration h hphysical).point =
      p.gradient := by
  rw [iteration_objective, iteration_point_eq, gradients_eq_source h]

/-- Helper for thm:main: the canonical actual trajectory has the exact source
gradient-norm limit one. -/
theorem iteration_gradientNorm_tendsto_one {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    Tendsto (fun k ↦ ‖DFP.gradients (iteration h hphysical).objective
      (iteration h hphysical).point k‖) atTop (𝓝 1) := by
  rw [iteration_gradients_eq]
  exact h.gradient_limit

/-- Helper for thm:main: exact interpolation and C² regularity certify each
original prescribed gradient as a genuine objective gradient. -/
theorem objective_hasGradientAt {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) (k : ℕ) :
    HasGradientAt (InterpolationSum.polarObjective p κ) (p.gradient k) (p.point k) := by
  have hgradient := (objective_differentiableAt h k).hasGradientAt
  rwa [(h.endpoints k).2.1] at hgradient

/-- Helper for thm:main: adding the source displacement reaches exactly its next point. -/
theorem point_add_chord (p : Parameters) (k : ℕ) :
    p.point k + (p.point (k + 1) - p.point k) = p.point (k + 1) := by
  abel

/-- Helper for thm:main: the exact model endpoint inequalities and original
interpolated gradients give the canonical standard strong Wolfe predicate. -/
theorem strongWolfe_of_endpoint_inequalities {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hc₁ : 0 < c₁) (horder : c₁ < c₂) (hc₂ : c₂ < 1)
    (harmijo : ∀ k, InterpolationSum.polarObjective p κ (p.point (k + 1)) ≤
      InterpolationSum.polarObjective p κ (p.point k) +
        c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k))
    (hcurvature : ∀ k, |inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)| ≤
      c₂ * |inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)|) (k : ℕ) :
    LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k) := by
  have hnext : HasGradientAt (InterpolationSum.polarObjective p κ) (p.gradient (k + 1))
      (p.point k + (p.point (k + 1) - p.point k)) := by
    rw [point_add_chord]
    exact objective_hasGradientAt h (k + 1)
  have harmijoNext : InterpolationSum.polarObjective p κ
      (p.point k + (p.point (k + 1) - p.point k)) ≤
      InterpolationSum.polarObjective p κ (p.point k) +
        c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k) := by
    rw [point_add_chord]
    exact harmijo k
  exact LineSearch.IsStrongWolfe.ofHasGradientAt hc₁ horder hc₂
    (objective_hasGradientAt h k) hnext harmijoNext (hcurvature k)

/-- Helper for thm:main: the exact interpolated endpoint value has the scalar
radius-squared form used by the source Wolfe ratios. -/
theorem objective_value_eq_radial_model {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) (k : ℕ) :
    InterpolationSum.polarObjective p κ (p.point k) = p.radius k ^ 2 / 2 := by
  rw [(h.endpoints k).1]
  ring

/-- Helper for thm:main: the original scalar radial-model Wolfe endpoints
transport to canonical standard strong Wolfe without altering the objective or step. -/
theorem strongWolfe_of_radial_endpoints {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hc₁ : 0 < c₁) (horder : c₁ < c₂) (hc₂ : c₂ < 1)
    (harmijo : ∀ k, p.radius (k + 1) ^ 2 / 2 ≤ p.radius k ^ 2 / 2 +
      c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k))
    (hcurvature : ∀ k, |inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)| ≤
      c₂ * |inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)|) (k : ℕ) :
    LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k) := by
  have harmijoActual : ∀ k,
      InterpolationSum.polarObjective p κ (p.point (k + 1)) ≤
      InterpolationSum.polarObjective p κ (p.point k) +
        c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k) := by
    intro k
    rw [objective_value_eq_radial_model h, objective_value_eq_radial_model h]
    exact harmijo k
  exact strongWolfe_of_endpoint_inequalities h hc₁ horder hc₂ harmijoActual hcurvature k

/-- Helper for thm:main: the canonical trajectory inherits each standard strong
Wolfe endpoint certificate through its exact source projections. -/
theorem iteration_strongWolfe {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) (k : ℕ) :
    LineSearch.IsStrongWolfe c₁ c₂ (iteration h hphysical).objective
      ((iteration h hphysical).point k)
      ((iteration h hphysical).point (k + 1) - (iteration h hphysical).point k) := by
  simpa only [iteration_objective, iteration_point] using hwolfe k

/-- Helper for thm:main: the actual positive inverse-Hessian search step is a
strict descent displacement for the interpolated objective. -/
theorem source_descent {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k)
    (hr : ∀ k, 0 < p.radius k) (k : ℕ) :
    inner ℝ (gradient (InterpolationSum.polarObjective p κ) (p.point k))
      (p.point (k + 1) - p.point k) < 0 := by
  rw [(h.endpoints k).2.1, EuclideanSpace.inner_eq_star_dotProduct]
  simpa only [star_trivial, PhysicalRealization.chord_def, dotProduct_comm] using
    PhysicalRealization.RealizesStep.descent p k (hphysical k) (hr k)

/-- Helper for thm:main: standard strong Wolfe implies standard weak Wolfe for
the actual descent steps, as required by the reusable counterexample type. -/
theorem iteration_weakWolfe {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) (k : ℕ) :
    LineSearch.IsWeakWolfe c₁ c₂ (iteration h hphysical).objective
      ((iteration h hphysical).point k)
      ((iteration h hphysical).point (k + 1) - (iteration h hphysical).point k) := by
  apply (iteration_strongWolfe h hphysical hwolfe k).toWeakWolfe
  simpa only [iteration_objective, iteration_point] using (source_descent h hphysical hr k).le

/-- Helper for thm:main: global Hessian bounds remain valid when the lower bound
is decreased and the upper bound is increased. -/
theorem hessianBounds_mono {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] {f : F → ℝ} {m M m' M' : ℝ} (hf : ContDiff ℝ 2 f)
    (h : HasHessianBounds m M f) (hm : m' ≤ m) (hM : M ≤ M') :
    HasHessianBounds m' M' f := by
  apply HasHessianBounds.of_forall
  intro x
  apply HasHessianBoundsAt.of_quadraticForm (hessian_isSelfAdjoint hf.contDiffAt)
  intro v
  have hquad := (h.at x).quadraticForm v
  exact ⟨(mul_le_mul_of_nonneg_right hm (sq_nonneg _)).trans hquad.1,
    hquad.2.trans (mul_le_mul_of_nonneg_right hM (sq_nonneg _))⟩

/-- Helper for thm:main: choosing source accuracy at most one half gives the
literal fixed Hessian bounds `I/2` and `3I/2`. -/
theorem iteration_hessianBounds {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hδ : δ ≤ 1 / 2) :
    HasHessianBounds (1 / 2) (3 / 2) (iteration h hphysical).objective := by
  rw [iteration_objective]
  have hlower : (1 / 2 : ℝ) ≤ 1 - δ := by linarith
  have hupper : 1 + δ ≤ (3 / 2 : ℝ) := by linarith
  exact hessianBounds_mono h.objective_contDiff h.hessian_bounds hlower hupper

/-- Helper for thm:main: C² regularity is preserved exactly in the canonical trajectory. -/
theorem iteration_contDiff {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) :
    ContDiff ℝ 2 (iteration h hphysical).objective := by
  rw [iteration_objective]
  exact h.objective_contDiff

/-- Helper for thm:main: every canonical trajectory step length is the proved
positive original source step length. -/
theorem iteration_stepLength_pos {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (k : ℕ) :
    0 < (iteration h hphysical).stepLength k := by
  rw [iteration_stepLength]
  exact (hphysical k).stepLength_pos

/-- Helper for thm:main: a canonical weak certificate is built only from the
actual source trajectory, with its gradient-limit field exactly one. -/
def weakCertificate {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hδ : δ ≤ 1 / 2)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    DFP.WolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂ where
  iteration := iteration h hphysical
  gradientLimit := 1
  objectiveContDiff := iteration_contDiff h hphysical
  stepLengthPos := iteration_stepLength_pos h hphysical
  hessianBounds := iteration_hessianBounds h hphysical hδ
  weakWolfe := iteration_weakWolfe h hphysical hr hwolfe
  gradientLimitPos := zero_lt_one
  gradientNormTendsto := iteration_gradientNorm_tendsto_one h hphysical

/-- Helper for thm:main: the canonical strong certificate attaches the actual
standard strong Wolfe laws without selecting any older witness or orbit. -/
def strongCertificate {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hδ : δ ≤ 1 / 2)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂ where
  toWolfeCounterexample := weakCertificate h hphysical hr hδ hwolfe
  strongWolfe := iteration_strongWolfe h hphysical hwolfe

/-- Helper for thm:main: a source identity certificate exposes the concrete data
stored in the standard counterexample interface. It contains no replacement sequences. -/
structure SourceIdentity (p : Parameters) (κ : ℝ) {c₁ c₂ : ℝ}
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) : Prop where
  /-- Helper for thm:main: the exact original cutoff-times-affine objective. -/
  objective : w.iteration.objective = InterpolationSum.polarObjective p κ
  /-- Helper for thm:main: the exact original unreduced-angle polar points. -/
  point : w.iteration.point = p.point
  /-- Helper for thm:main: the exact original physical inverse-Hessian sequence. -/
  inverseHessian : w.iteration.inverseHessian = p.inverseHessian
  /-- Helper for thm:main: the exact original positive source step-length sequence. -/
  stepLength : w.iteration.stepLength = PhysicalRealization.prescribedStepLength p
  /-- Helper for thm:main: the actual original prescribed gradient sequence. -/
  gradients : DFP.gradients w.iteration.objective w.iteration.point = p.gradient

/-- Helper for thm:main: the constructed strong certificate has the same canonical
iteration as the direct source trajectory package. -/
theorem strongCertificate_iteration {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hδ : δ ≤ 1 / 2)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    (strongCertificate h hphysical hr hδ hwolfe).iteration = iteration h hphysical := by
  rfl

/-- Helper for thm:main: the source strong certificate has gradientLimit exactly1. -/
theorem strongCertificate_gradientLimit {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hδ : δ ≤ 1 / 2)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    (strongCertificate h hphysical hr hδ hwolfe).gradientLimit = 1 := by
  rfl

/-- Helper for thm:main: all source identities for the constructed canonical
strong certificate follow from the small trajectory projection interface. -/
theorem strongCertificate_source {p : Parameters} {κ δ C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hδ : δ ≤ 1 / 2)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    SourceIdentity p κ (strongCertificate h hphysical hr hδ hwolfe) := by
  constructor
  · rw [strongCertificate_iteration, iteration_objective]
  · rw [strongCertificate_iteration, iteration_point_eq]
  · rw [strongCertificate_iteration, iteration_inverseHessian_eq]
  · rw [strongCertificate_iteration, iteration_stepLength]
  · rw [strongCertificate_iteration, iteration_gradients_eq]

/-- Helper for thm:main: the exact initial objective level set of a canonical trajectory. -/
def initialLevelSet (it : DFP.InverseIteration (Fin 2)) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | it.objective x ≤ it.objective (it.point 0)}

/-- Helper for thm:main: the source initial level is the level through the actual initial point. -/
theorem initialLevelSet_def (it : DFP.InverseIteration (Fin 2)) :
    initialLevelSet it = {x | it.objective x ≤ it.objective (it.point 0)} := by
  rfl

/-- Helper for eq:counterexample-nonlipschitz: the canonical even-step secant residual
ratio, with the same gradient difference, Hessian and exponent as the source proof. -/
def secantResidualRatio (it : DFP.InverseIteration (Fin 2)) (β : ℝ) (j : ℕ) : ℝ :=
  ‖DFP.gradientChanges (DFP.gradients it.objective it.point) (2 * j) -
      hessian it.objective (it.point (2 * j)) (it.point (2 * j + 1) - it.point (2 * j))‖ /
    ‖it.point (2 * j + 1) - it.point (2 * j)‖ ^ (1 + β)

/-- Helper for eq:counterexample-nonlipschitz: the exact canonical residual-ratio formula. -/
theorem secantResidualRatio_def (it : DFP.InverseIteration (Fin 2)) (β : ℝ) (j : ℕ) :
    secantResidualRatio it β j =
      ‖DFP.gradientChanges (DFP.gradients it.objective it.point) (2 * j) -
          hessian it.objective (it.point (2 * j)) (it.point (2 * j + 1) - it.point (2 * j))‖ /
        ‖it.point (2 * j + 1) - it.point (2 * j)‖ ^ (1 + β) := by
  rfl

/-- Helper for eq:counterexample-nonlipschitz: the source identity certificate
identifies the canonical secant ratio with the original polar residual quotient. -/
theorem SourceIdentity.secantResidualRatio {p : Parameters} {κ c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : SourceIdentity p κ w) (β : ℝ) (j : ℕ) :
    secantResidualRatio w.iteration β j =
      ‖p.gradient (2 * j + 1) - p.gradient (2 * j) -
          hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j))
            (p.point (2 * j + 1) - p.point (2 * j))‖ /
        ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β) := by
  rw [secantResidualRatio_def, h.gradients, DFP.gradientChanges_apply, h.objective, h.point]

/-- Helper for thm:main: the additional planar conclusions attached to the standard
strong-Wolfe certificate, independently of its exact source projection certificate. -/
structure CounterexampleProperties (ε : ℝ) {c₁ c₂ : ℝ}
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂) : Prop where
  /-- Helper for thm:main: the limiting gradient-norm field is exactly one. -/
  gradientLimit : w.gradientLimit = 1
  /-- Helper for thm:main: the Hessian is uniformly as close to identity as requested. -/
  near_identity : ∀ x, ‖hessian w.iteration.objective x - 1‖ ≤ ε
  /-- Helper for thm:main: the same refinement has the source spectral Hessian bounds. -/
  accuracy_bounds : HasHessianBounds (1 - ε) (1 + ε) w.iteration.objective
  /-- Helper for thm:main: the objective Hessian is globally half-Hölder continuous. -/
  half_holder : ∃ H ≥ 0, ∀ x y,
    ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
      H * ‖x - y‖ ^ (1 / 2 : ℝ)
  /-- Helper for thm:main: the original normalization at the origin is preserved. -/
  origin : w.iteration.objective 0 = 0
  /-- Helper for thm:main: the origin is the unique global objective minimizer. -/
  unique_minimizer : ∀ x,
    (∀ y, w.iteration.objective x ≤ w.iteration.objective y) ↔ x = 0
  /-- Helper for thm:main: the exact unit circle is the point-sequence cluster set. -/
  cluster : ∀ x, MapClusterPt x atTop w.iteration.point ↔ ‖x‖ = 1
  /-- Helper for thm:main: no exponent β in the source range works on the initial level. -/
  no_holder_initial : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    ¬ ∃ L ≥ 0, ∀ x ∈ initialLevelSet w.iteration, ∀ y ∈ initialLevelSet w.iteration,
      ‖hessian w.iteration.objective x - hessian w.iteration.objective y‖ ≤
        L * ‖x - y‖ ^ β
  /-- Helper for eq:counterexample-nonlipschitz: the source even secant ratios diverge. -/
  residual_diverges : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
    Tendsto (secantResidualRatio w.iteration β) atTop atTop

/-- Helper for thm:main: the standard certificate's gradient norms converge to
exactly one once the source value of its limit field is recorded. -/
theorem CounterexampleProperties.gradientNorm_tendsto_one {ε c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : CounterexampleProperties ε w) :
    Tendsto (fun k ↦ ‖DFP.gradients w.iteration.objective w.iteration.point k‖)
      atTop (𝓝 1) := by
  simpa only [h.gradientLimit] using w.gradientNormTendsto

/-- Helper for thm:main: source projections transfer all analytic, geometric and
sharpness conclusions to the canonical certificate. The two sharpness inputs are
explicit intermediate obligations, to be discharged by the actual source proof. -/
theorem properties_of_source {p : Parameters} {κ δ ε C H c₁ c₂ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hcluster : ∀ x, MapClusterPt x atTop p.point ↔ ‖x‖ = 1)
    (hsource : SourceIdentity p κ w) (hlimit : w.gradientLimit = 1)
    (hδε : δ ≤ ε) (hH : 0 ≤ H)
    (hnoHolder : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      ¬ ∃ L ≥ 0,
        ∀ x ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ∀ y ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ‖hessian (InterpolationSum.polarObjective p κ) x -
          hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β)
    (hdiverge : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Tendsto (fun j ↦
        ‖p.gradient (2 * j + 1) - p.gradient (2 * j) -
            hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j))
              (p.point (2 * j + 1) - p.point (2 * j))‖ /
          ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β)) atTop atTop) :
    CounterexampleProperties ε w := by
  constructor
  · exact hlimit
  · intro x
    rw [hsource.objective, hessian_def]
    exact (h.near_identity x).trans hδε
  · rw [hsource.objective]
    have hlower : 1 - ε ≤ 1 - δ := by linarith
    have hupper : 1 + δ ≤ 1 + ε := by linarith
    exact hessianBounds_mono h.objective_contDiff h.hessian_bounds hlower hupper
  · refine ⟨H, hH, ?_⟩
    intro x y
    rw [hsource.objective, hessian_def, hessian_def]
    exact h.hessian_holder x y
  · rw [hsource.objective]
    exact h.origin
  · rw [hsource.objective]
    exact h.unique_minimizer
  · rw [hsource.point]
    exact hcluster
  · rw [initialLevelSet_def, hsource.objective, hsource.point]
    exact hnoHolder
  · intro β hβ
    rw [funext (hsource.secantResidualRatio β)]
    exact hdiverge β hβ

/-- Helper for thm:main: the actual physical laws and the actual point geometry
hold on one positive source parameter neighborhood before a starting index is chosen. -/
theorem physicalGeometryNeighborhood :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ lower > 0, ∃ upper > 0, ∃ separation > 0, ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        let p := Parameters.of j₀ νStar
        (∀ k, PhysicalRealization.RealizesStep p k) ∧
          PointGeometry.PointEstimates p lower upper separation ∧ (∀ k, 0 < p.radius k) := by
  obtain ⟨η₀, hη₀, hphysical⟩ := PhysicalRealization.polarPhysicalRealization
  obtain ⟨η₁, hη₁, hgeometry⟩ := PointGeometry.polarPointGeometry
  refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨J₀, hJ₀, hsteps⟩ := hphysical νStar hnear₀
  obtain ⟨_, _, _, _, _, _, _, lower, hlower, upper, hupper, separation, hseparation,
    J₁, _, hpoints⟩ := hgeometry νStar hnear₁
  refine ⟨lower, hlower, upper, hupper, separation, hseparation,
    max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hstep := hsteps j₀ ((le_max_left J₀ J₁).trans hj₀)
  obtain ⟨hradii, hpoint⟩ := hpoints j₀ ((le_max_right J₀ J₁).trans hj₀)
  exact ⟨fun k ↦ (hstep k).1, hpoint, fun k ↦ zero_lt_one.trans (hradii.above_one k)⟩

/-- Helper for thm:main: exact source laws, scalar Wolfe inequalities and the
source secant contradiction assemble a standard planar strong-Wolfe certificate.
This intermediate adapter never selects an orbit or assumes objective regularity. -/
theorem certificate_of_source {p : Parameters} {κ δ ε C H c₁ c₂ : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H)
    (hphysical : ∀ k, PhysicalRealization.RealizesStep p k) (hr : ∀ k, 0 < p.radius k)
    (hcluster : ∀ x, MapClusterPt x atTop p.point ↔ ‖x‖ = 1)
    (hδhalf : δ ≤ 1 / 2) (hδε : δ ≤ ε) (hH : 0 ≤ H)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k))
    (hnoHolder : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      ¬ ∃ L ≥ 0,
        ∀ x ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ∀ y ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ‖hessian (InterpolationSum.polarObjective p κ) x -
          hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β)
    (hdiverge : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Tendsto (fun j ↦
        ‖p.gradient (2 * j + 1) - p.gradient (2 * j) -
            hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j))
              (p.point (2 * j + 1) - p.point (2 * j))‖ /
          ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β)) atTop atTop) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
      SourceIdentity p κ w ∧ CounterexampleProperties ε w := by
  let w := strongCertificate h hphysical hr hδhalf hwolfe
  have hsource : SourceIdentity p κ w := strongCertificate_source h hphysical hr hδhalf hwolfe
  have hlimit : w.gradientLimit = 1 := strongCertificate_gradientLimit h hphysical hr hδhalf hwolfe
  exact ⟨w, hsource,
    properties_of_source h hcluster hsource hlimit hδε hH hnoHolder hdiverge⟩

/-- Helper for thm:main: the original source data and decisive sharpness conclusions
collected before the final scalar Wolfe parameter choice. -/
structure SourceData (p : Parameters) (κ δ C H : ℝ) : Prop where
  /-- Helper for thm:main: the exact actual interpolation objective conclusions. -/
  objective : ActualObjective.ObjectiveEstimates p κ δ C H
  /-- Helper for thm:main: the original positive physical inverse-DFP laws at every index. -/
  physical : ∀ k, PhysicalRealization.RealizesStep p k
  /-- Helper for thm:main: the original actual radii are positive. -/
  radius_pos : ∀ k, 0 < p.radius k
  /-- Helper for thm:main: the exact source unit-circle cluster set. -/
  cluster : ∀ x, MapClusterPt x atTop p.point ↔ ‖x‖ = 1
  /-- Helper for eq:counterexample-nonlipschitz: the actual source residual and initial-level
  sharpness certificate for the SAME interpolation support parameter. -/
  sharpness : ∃ cResidual CResidual lower upper,
    HolderSharpness.SharpnessEstimates p κ cResidual CResidual lower upper

/-- Helper for thm:main: the accepted sharpness initial level set is exactly
the source objective level through its original initial point. -/
theorem sharpness_initialLevelSet_eq (p : Parameters) (κ : ℝ) :
    HolderSharpness.initialLevelSet p κ =
      {x | InterpolationSum.polarObjective p κ x ≤
        InterpolationSum.polarObjective p κ (p.point 0)} := by
  ext x
  exact HolderSharpness.mem_initialLevelSet p κ x

/-- Helper for eq:counterexample-nonlipschitz: the accepted sharpness quotient
uses precisely the original prescribed gradients realized by the actual objective. -/
theorem sharpness_evenResidualRatio_eq {p : Parameters} {κ δ C H : ℝ}
    (h : ActualObjective.ObjectiveEstimates p κ δ C H) (β : ℝ) (j : ℕ) :
    HolderSharpness.evenResidualRatio p κ β j =
      ‖p.gradient (2 * j + 1) - p.gradient (2 * j) -
          hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j))
            (p.point (2 * j + 1) - p.point (2 * j))‖ /
        ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β) := by
  rw [HolderSharpness.evenResidualRatio_def, HolderSharpness.evenResidual_def,
    HolderSharpness.evenStep_def, (h.endpoints (2 * j + 1)).2.1,
    (h.endpoints (2 * j)).2.1]

/-- Helper for thm:main: all actual objective, physical, geometric and sharpness
estimates share one positive parameter neighborhood, with support fixed before
accuracy and every later natural starting index. -/
theorem sourceDataNeighborhood :
    ∃ η > 0, ∀ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ κ > 0, ∃ C > 0, ∃ H > 0, ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J, SourceData (Parameters.of j₀ νStar) κ δ C H := by
  obtain ⟨η₀, hη₀, hsharpness⟩ := HolderSharpness.polarHolderSharpness
  obtain ⟨η₁, hη₁, hphysical⟩ := physicalGeometryNeighborhood
  refine ⟨min η₀ η₁, lt_min hη₀ hη₁, ?_⟩
  intro νStar hnear
  have hnear₀ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₀) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_left _ _))⟩
  have hnear₁ : νStar ∈ Set.Ioo baseAngle (baseAngle + η₁) :=
    ⟨hnear.1, hnear.2.trans_le (add_le_add le_rfl (min_le_right _ _))⟩
  obtain ⟨κ, hκ, C, hC, H, hH, cResidual, _, CResidual, _, lower, _, upper, _, haccuracy⟩ :=
    hsharpness νStar hnear₀
  obtain ⟨lowerG, _, upperG, _, separationG, _, J₁, hJ₁, hrealizes⟩ := hphysical νStar hnear₁
  refine ⟨κ, hκ, C, hC, H, hH, ?_⟩
  intro δ hδ hδone
  obtain ⟨J₀, hJ₀, hsharp⟩ := haccuracy δ hδ hδone
  refine ⟨max J₀ J₁, hJ₀.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  obtain ⟨hobjective, hsourceSharpness⟩ := hsharp j₀ ((le_max_left J₀ J₁).trans hj₀)
  obtain ⟨hsteps, hpoints, hradii⟩ := hrealizes j₀ ((le_max_right J₀ J₁).trans hj₀)
  exact ⟨hobjective, hsteps, hradii, hpoints.cluster,
    cResidual, CResidual, lower, upper, hsourceSharpness⟩

/-- Helper for thm:main: the accepted original source certificates discharge all
analytic, geometric and sharpness fields; only the source Wolfe endpoints remain
as this intermediate adapter's explicit scalar input. -/
theorem certificateOfSourceData {p : Parameters} {κ δ ε C H c₁ c₂ : ℝ}
    (h : SourceData p κ δ C H) (hδhalf : δ ≤ 1 / 2) (hδε : δ ≤ ε) (hH : 0 ≤ H)
    (hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ (InterpolationSum.polarObjective p κ)
      (p.point k) (p.point (k + 1) - p.point k)) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
      SourceIdentity p κ w ∧ CounterexampleProperties ε w := by
  obtain ⟨cResidual, CResidual, lower, upper, hsharp⟩ := h.sharpness
  have hnoHolder : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      ¬ ∃ L ≥ 0,
        ∀ x ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ∀ y ∈ {x | InterpolationSum.polarObjective p κ x ≤
          InterpolationSum.polarObjective p κ (p.point 0)},
        ‖hessian (InterpolationSum.polarObjective p κ) x -
          hessian (InterpolationSum.polarObjective p κ) y‖ ≤ L * ‖x - y‖ ^ β := by
    simpa only [sharpness_initialLevelSet_eq] using hsharp.no_holder_initial
  have hdiverge : ∀ β ∈ Set.Ioc (1 / 2 : ℝ) 1,
      Tendsto (fun j ↦
        ‖p.gradient (2 * j + 1) - p.gradient (2 * j) -
            hessian (InterpolationSum.polarObjective p κ) (p.point (2 * j))
              (p.point (2 * j + 1) - p.point (2 * j))‖ /
          ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β)) atTop atTop := by
    intro β hβ
    rw [← funext (sharpness_evenResidualRatio_eq h.objective β)]
    exact hsharp.ratio_diverges β hβ
  exact certificate_of_source h.objective h.physical h.radius_pos h.cluster
    hδhalf hδε hH hwolfe hnoHolder hdiverge

/-- Helper for thm:main: a uniform scalar endpoint selector completes the exact
source parameter order. This intermediate adapter keeps that selector explicit;
the final source theorem must discharge it from the actual Wolfe-ratio proof. -/
theorem counterexampleFamilyOfUniformEndpoints (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (horder : c₁ < c₂) (hc₂ : c₂ < 1)
    (hselect : ∀ η > 0, ∃ νStar ∈ Set.Ioo baseAngle (baseAngle + η),
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J, ∀ k : ℕ,
        let p := Parameters.of j₀ νStar
        (p.radius (k + 1) ^ 2 / 2 ≤ p.radius k ^ 2 / 2 +
          c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)) ∧
        |inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)| ≤
          c₂ * |inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)|) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
          SourceIdentity (Parameters.of j₀ νStar) κ w ∧ CounterexampleProperties ε w := by
  obtain ⟨η, hη, hdata⟩ := sourceDataNeighborhood
  obtain ⟨νStar, hνStar, Jw, hJw, hmodel⟩ := hselect η hη
  obtain ⟨κ, hκ, C, _, H, hH, haccuracy⟩ := hdata νStar hνStar
  refine ⟨νStar, hνStar.1, κ, hκ, ?_⟩
  intro ε hε _
  let δ := min ε (1 / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) < 1 := by norm_num
  have hδ : 0 < δ := lt_min hε hhalf
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have hδone : δ < 1 := hδhalf.trans_lt hhalfOne
  obtain ⟨Js, hJs, hsource⟩ := haccuracy δ hδ hδone
  refine ⟨max Js Jw, hJs.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hj₀
  have hactual := hsource j₀ ((le_max_left Js Jw).trans hj₀)
  have hstep := hmodel j₀ ((le_max_right Js Jw).trans hj₀)
  have hwolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂
      (InterpolationSum.polarObjective (Parameters.of j₀ νStar) κ)
      ((Parameters.of j₀ νStar).point k)
      ((Parameters.of j₀ νStar).point (k + 1) - (Parameters.of j₀ νStar).point k) := by
    intro k
    exact strongWolfe_of_radial_endpoints hactual.objective hc₁ horder hc₂
      (fun k ↦ (hstep k).1) (fun k ↦ (hstep k).2) k
  exact certificateOfSourceData hactual hδhalf hδε hH.le hwolfe

/-- Helper for thm:main: the accepted original model-Wolfe certificate exposes
exactly the radial value and gradient-pairing inequalities used by the canonical adapter. -/
theorem modelStrongWolfe_radial_endpoints (p : Parameters) (k : ℕ) {c₁ c₂ : ℝ}
    (h : WolfeRatios.ModelStrongWolfe p k c₁ c₂) :
    (p.radius (k + 1) ^ 2 / 2 ≤ p.radius k ^ 2 / 2 +
      c₁ * inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)) ∧
      |inner ℝ (p.gradient (k + 1)) (p.point (k + 1) - p.point k)| ≤
        c₂ * |inner ℝ (p.gradient k) (p.point (k + 1) - p.point k)| := by
  constructor
  · simpa only [WolfeRatios.modelValue_def, WolfeRatios.startSlope_def] using
      LineSearch.Wolfe.isArmijo_iff.mp h.armijo
  · simpa only [WolfeRatios.startSlope_def, WolfeRatios.endSlope_def] using
      LineSearch.Wolfe.isStrongCurvature_iff.mp h.curvature

/-- Helper for thm:main: one original source parameter and one fixed support
coefficient work for every later requested near-identity accuracy. Each accuracy
chooses one natural threshold, uniformly for every larger original starting index. -/
theorem planarCounterexampleFamily (c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ J : ℕ, 0 < J ∧ ∀ j₀ ≥ J,
        ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
          SourceIdentity (Parameters.of j₀ νStar) κ w ∧ CounterexampleProperties ε w := by
  apply counterexampleFamilyOfUniformEndpoints c₁ c₂ hc₁ (hc₁lim.trans_le hc₂lim) hc₂
  intro η hη
  obtain ⟨νStar, hνStar, _, J, hJ, hmodel⟩ :=
    WolfeRatios.existsUniformModelWolfe c₁ c₂ η hc₁ hc₁lim hc₂lim hc₂ hη
  refine ⟨νStar, hνStar, J, hJ, ?_⟩
  intro j₀ hj₀ k
  exact modelStrongWolfe_radial_endpoints (Parameters.of j₀ νStar) k (hmodel j₀ hj₀ k)

/-- thm:main (PLANAR) and eq:objective and eq:counterexample-nonlipschitz:
for every source Wolfe pair and every `0 < ε < 1`, the exact original polar objective
and sequences give a canonical classical strong-Wolfe DFP counterexample with gradient
limit exactly one, fixed Hessian bounds `I/2` and `3I/2`, global half-Hölder Hessian,
uniform ε-nearness to identity, unique origin minimum and normalization, exact unit-circle
cluster set, and failure of every β-Hölder bound on the INITIAL level set for `1/2 < β ≤ 1`.
The concrete source parameters and all original sequence projections are retained. -/
theorem planarCounterexample (c₁ c₂ ε : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hε : 0 < ε) (hεone : ε < 1) :
    ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
      ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
        SourceIdentity (Parameters.of j₀ νStar) κ w ∧ CounterexampleProperties ε w := by
  obtain ⟨νStar, hνStar, κ, hκ, haccuracy⟩ :=
    planarCounterexampleFamily c₁ c₂ hc₁ hc₁lim hc₂lim hc₂
  obtain ⟨J, hJ, hfamily⟩ := haccuracy ε hε hεone
  obtain ⟨w, hsource, hproperties⟩ := hfamily J le_rfl
  exact ⟨νStar, hνStar, κ, hκ, J, hJ, w, hsource, hproperties⟩

/-- Helper for thm:main: the standard-certificate-first form retains the concrete
source witness, for subsequent dimension extension or coordinate transport. -/
theorem planarCounterexampleCertificate (c₁ c₂ ε : ℝ)
    (hc₁ : 0 < c₁) (hc₁lim : c₁ < 2 / 3) (hc₂lim : 2 / 3 ≤ c₂) (hc₂ : c₂ < 1)
    (hε : 0 < ε) (hεone : ε < 1) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
      CounterexampleProperties ε w ∧ ∃ νStar > baseAngle, ∃ κ > 0, ∃ j₀ : ℕ, 0 < j₀ ∧
        SourceIdentity (Parameters.of j₀ νStar) κ w := by
  obtain ⟨νStar, hνStar, κ, hκ, j₀, hj₀, w, hsource, hproperties⟩ :=
    planarCounterexample c₁ c₂ ε hc₁ hc₁lim hc₂lim hc₂ hε hεone
  exact ⟨w, hproperties, νStar, hνStar, κ, hκ, j₀, hj₀, hsource⟩

end DFP.Polar.PlanarCounterexample
