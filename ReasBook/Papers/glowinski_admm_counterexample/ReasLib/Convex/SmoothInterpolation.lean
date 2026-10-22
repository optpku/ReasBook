/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Convex.SmoothInterpolation.Strong

@[expose] public section

open Set Filter
open scoped Topology RealInnerProductSpace

namespace SmoothInterpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A complete finite interpolation certificate, including the supporting
inequalities used by the ADMM realization and a quantitative origin minimum. -/
structure StrongInterpolation (z q : ι → E) (φ : ι → ℝ)
    (f : E → ℝ) (μ : ℝ) (L : NNReal) : Prop where
  positive : 0 < μ
  stronglyConvex : StrongConvexOn univ μ f
  contDiff : ContDiff ℝ 1 f
  lipschitz : LipschitzWith L (fderiv ℝ f)
  values : ∀ i, f (z i) = φ i
  derivatives : ∀ i, HasFDerivAt f (innerSL ℝ (q i)) (z i)
  zero : f 0 = 0
  origin_derivative : HasFDerivAt f (0 : E →L[ℝ] ℝ) 0
  lower : ∀ x, μ/2 * ‖x‖^2 ≤ f x
  supports : ∀ i x, f (z i) + ⟪q i, x-z i⟫ ≤ f x

/-- Finite strictly supported data with a zero datum admit a finite, globally
C¹, strongly convex interpolant with globally Lipschitz derivative.  A common
small positive parameter supplies both quadratic margins; finiteness ensures
that all strict inequalities survive this perturbation simultaneously. -/
theorem exists_strongInterpolation (z q : ι → E) (φ : ι → ℝ)
    (o : ι) (hz : z o = 0) (hq : q o = 0) (hφ : φ o = 0)
    (hstrict : ∀ i j, i ≠ j → 0 < φ i - φ j - ⟪q j, z i-z j⟫) :
    ∃ f : E → ℝ, ∃ μ : ℝ, ∃ L : NNReal, StrongInterpolation z q φ f μ L := by
  classical
  let defect : ℝ → ι → ι → ℝ := fun μ i j ↦
    (φ i - μ/2 * ‖z i‖^2) - (φ j - μ/2 * ‖z j‖^2) -
      ⟪q j - μ • z j, z i-z j⟫ -
      μ/2 * ‖(q i - μ • z i) - (q j - μ • z j)‖^2
  have hev : ∀ᶠ μ : ℝ in 𝓝 0, ∀ i j, i ≠ j → 0 < defect μ i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun μ h ↦ False.elim (h hij)
    · have hd : ContinuousAt (fun μ ↦ defect μ i j) 0 := by dsimp [defect]; fun_prop
      have hp : 0 < defect 0 i j := by simpa [defect] using hstrict i j hij
      exact (continuousAt_const.eventually_lt hd hp).mono fun μ h _ ↦ h
  have hpos : ∀ᶠ μ : ℝ in 𝓝[>] 0, 0 < μ := self_mem_nhdsWithin
  obtain ⟨μ, hμall, hμ⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and hpos).exists
  have hμpos : 0 < μ := hμ
  let p : ι → E := fun i ↦ q i - μ • z i
  let ψ : ι → ℝ := fun i ↦ φ i - μ/2 * ‖z i‖^2
  have hc : InterpolationCondition z p ψ μ := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [p, ψ]
    · have hh := hμall i j hij
      dsimp [defect] at hh
      dsimp [p, ψ]
      linarith
  have hp0 : p o = 0 := by simp [p, hz, hq]
  have hψ0 : ψ o = 0 := by simp [ψ, hz, hφ]
  let core : QuadraticCore (quadraticEnvelope z p ψ μ) μ :=
    quadraticEnvelope_core hμpos hc o hz hp0 hψ0
  have hg (i : ι) : core.gradient (z i) = p i :=
    core.gradient_eq_of_subgradient (quadraticEnvelope_subgradient hμpos.le hc i)
  have hv (i : ι) : core.conjugate (z i) = ψ i := by
    rw [QuadraticCore.conjugate, hg i, quadraticEnvelope_at hc i]
    have hi := real_inner_comm (z i) (p i)
    linarith
  have hg' (i : ι) : core.gradient (z i) + μ • z i = q i := by
    rw [hg i]
    exact sub_add_cancel _ _
  refine ⟨core.shift μ, μ, core.constant + ⟨μ, hμpos.le⟩, ?_⟩
  refine ⟨hμpos, core.shift_stronglyConvex μ, core.shift_contDiff μ,
    core.shift_fderiv_lipschitz μ hμpos.le, ?_, ?_, core.shift_zero μ, ?_,
    core.shift_lower μ, ?_⟩
  · intro i
    simp only [QuadraticCore.shift, hv i, ψ, sub_add_cancel]
  · intro i
    simpa only [hg' i] using core.hasFDerivAt_shift μ (z i)
  · simpa only [core.gradient_zero, smul_zero, add_zero, map_zero] using
      core.hasFDerivAt_shift μ 0
  · intro i x
    have hs := core.shift_support μ (z i) x
    rw [hg' i] at hs
    have hp : 0 ≤ μ/2 * ‖x-z i‖^2 := by positivity
    linarith

end SmoothInterpolation
