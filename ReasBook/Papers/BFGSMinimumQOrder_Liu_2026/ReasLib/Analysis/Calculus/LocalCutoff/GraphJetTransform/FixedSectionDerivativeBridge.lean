module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

public section

open Filter
open scoped Topology

universe u

namespace LocalCutoff.GraphTransform

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Infrastructure I.16a: convergence of a scaled nonzero secant identifies the
derivative of a scalar-valued-parameter map at a translated base point. -/
theorem hasDerivAt_of_tendsto_slope_smul
    (f : ℝ → Y) (x c : ℝ) (s : ℝ → Y) (v : Y)
    (hs : Tendsto s (𝓝 0) (𝓝 v))
    (hsecant :
      (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
        (fun t => c • s t)) :
    HasDerivAt f (c • v) x := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hscaled : Tendsto (fun t : ℝ => c • s t)
      (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (𝓝 (c • v)) := by
    exact (hs.const_smul c).mono_left nhdsWithin_le_nhds
  exact hscaled.congr' hsecant.symm

/-- Infrastructure I.16a: a fixed bounded section can be evaluated at a point
before the scaled-secant derivative bridge is applied. -/
theorem hasDerivAt_of_tendsto_boundedSection_eval_smul
    {α : Type*} [TopologicalSpace α]
    (f : ℝ → Y) (x c : ℝ)
    (sections : ℝ → BoundedContinuousFunction α Y)
    (w : α) (v : BoundedContinuousFunction α Y)
    (hsections : Tendsto sections (𝓝 0) (𝓝 v))
    (hsecant :
      (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
        (fun t => c • sections t w)) :
    HasDerivAt f (c • v w) x := by
  have heval : Tendsto (fun t : ℝ => sections t w) (𝓝 0) (𝓝 (v w)) := by
    exact ((BoundedContinuousFunction.lipschitz_eval_const w).continuous.continuousAt.tendsto).comp
      hsections
  exact hasDerivAt_of_tendsto_slope_smul f x c (fun t => sections t w) (v w) heval hsecant

/-- Infrastructure I.16a: uniform convergence of bounded scalar-source sections
gives the full predecessor derivative equation when every center has the same
nonzero-secant representation. -/
theorem hasDerivAt_of_tendsto_boundedSection_slope_smul
    (f : ℝ → Y) (c : ℝ)
    (sections : ℝ → BoundedContinuousFunction ℝ Y)
    (v : BoundedContinuousFunction ℝ Y)
    (hsections : Tendsto sections (𝓝 0) (𝓝 v))
    (hsecant : ∀ x : ℝ,
      (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
        (fun t => c • sections t x)) :
    ∀ x, HasDerivAt f (c • v x) x := by
  intro x
  exact hasDerivAt_of_tendsto_boundedSection_eval_smul f x c sections x v
    hsections (hsecant x)

/-- Infrastructure I.16a: a fixed-section secant certificate records the
uniform section limit and the translated nonzero-secant formula needed for
holonomicity. -/
structure FixedSectionSecantCertificate (f : ℝ → Y) where
  scale : ℝ
  sections : ℝ → BoundedContinuousFunction ℝ Y
  limitSection : BoundedContinuousFunction ℝ Y
  sections_tendsto : Tendsto sections (𝓝 0) (𝓝 limitSection)
  secant_formula : ∀ x : ℝ,
    (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
      (fun t => scale • sections t x)

/-- Infrastructure I.16a: the fixed-section secant certificate supplies the
pointwise derivative equation for its limiting section. -/
theorem FixedSectionSecantCertificate.hasDerivAt
    {f : ℝ → Y} (certificate : FixedSectionSecantCertificate f) :
    ∀ x, HasDerivAt f (certificate.scale • certificate.limitSection x) x := by
  exact hasDerivAt_of_tendsto_boundedSection_slope_smul f certificate.scale
    certificate.sections certificate.limitSection certificate.sections_tendsto
    certificate.secant_formula

/-- Helper for Infrastructure I.16a: the fixed-section derivative certificate exposes
the translated little-o remainder in the form used by Fréchet derivative criteria. -/
theorem FixedSectionSecantCertificate.isLittleO_shift
    {f : ℝ → Y} (certificate : FixedSectionSecantCertificate f) :
    ∀ x, (fun h : ℝ => f (x + h) - f x -
      (ContinuousLinearMap.toSpanSingleton ℝ
        (certificate.scale • certificate.limitSection x)) h) =o[𝓝 0]
      (fun h : ℝ => h) := by
  intro x
  have hderiv := (certificate.hasDerivAt x).hasFDerivAt
  exact (hasFDerivAt_iff_isLittleO_nhds_zero.mp hderiv)

/-- Helper for Infrastructure I.16a: a uniform translated-remainder estimate gives the
corresponding little-o statement at each base point. -/
theorem isLittleO_shift_of_uniform_remainder
    {f : ℝ → Y} (A : ℝ →L[ℝ] Y)
    (hbound : ∀ ε > 0, ∃ δ > 0, ∀ x h : ℝ, ‖h‖ < δ →
      ‖f (x + h) - f x - A h‖ ≤ ε * ‖h‖) :
    ∀ x, (fun h : ℝ => f (x + h) - f x - A h) =o[𝓝 0]
      (fun h : ℝ => h) := by
  intro x
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hεbound⟩ := hbound ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hh' : ‖h‖ < δ := by
    simpa only [Metric.mem_ball, dist_zero_right] using hh
  exact hεbound x h hh'

/-- Helper for Infrastructure I.16a: a translated first-order little-o remainder determines the
Fréchet derivative at the translated base point. -/
theorem hasFDerivAt_of_isLittleO_shift_bridge
    (p : ℝ → Y) (u : ℝ) (A : ℝ →L[ℝ] Y)
    (h : (fun h : ℝ => p (u + h) - p u - A h) =o[𝓝 0] (fun h : ℝ => h)) :
    HasFDerivAt p A u := by
  have hg : HasFDerivAt (fun h : ℝ => p (u + h)) A 0 := by
    apply (hasFDerivAt_iff_isLittleO_nhds_zero
      (f := fun h : ℝ => p (u + h)) (f' := A) (x := 0)).mpr
    simpa only [zero_add, add_zero, sub_zero] using h
  have htranslate : HasFDerivAt (fun y : ℝ => y - u)
      (ContinuousLinearMap.id ℝ ℝ) u := by
    simpa only [id_eq] using (hasFDerivAt_id (𝕜 := ℝ) u).sub_const u
  have hg' : HasFDerivAt (fun h : ℝ => p (u + h)) A (u - u) := by
    simpa only [sub_self] using hg
  have hcomp : HasFDerivAt ((fun h : ℝ => p (u + h)) ∘ (fun y : ℝ => y - u))
      (A.comp (ContinuousLinearMap.id ℝ ℝ)) u := by
    apply HasFDerivAt.comp u
    · simpa only [sub_self] using hg'
    · exact htranslate
  have hA : A.comp (ContinuousLinearMap.id ℝ ℝ) = A := by
    ext
    simp
  rw [hA] at hcomp
  change HasFDerivAt (fun y : ℝ => p (u + (y - u))) A u at hcomp
  have hcongr : ∀ y : ℝ, p y = p (u + (y - u)) := by
    intro y
    congr 1
    ring
  exact hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall hcongr)

omit [NormedSpace ℝ Y] in
/-- Helper for Infrastructure I.16a: a strict scalar contraction absorbs an eventual
norm inequality with a little-o additive error. -/
theorem isLittleO_of_norm_le_mul_self_add_bridge
    {R e : ℝ → Y} {q : ℝ} (hq : q < 1)
    (hineq : ∀ᶠ h in 𝓝 0, ‖R h‖ ≤ q * ‖R h‖ + ‖e h‖)
    (he : e =o[𝓝 0] (fun h : ℝ ↦ h)) :
    R =o[𝓝 0] (fun h : ℝ ↦ h) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hgap : 0 < (1 - q) * ε := mul_pos (sub_pos.mpr hq) hε
  filter_upwards [hineq, Asymptotics.isLittleO_iff.mp he hgap] with h hR heh
  have habsorbed : (1 - q) * ‖R h‖ ≤ ‖e h‖ := by
    nlinarith
  nlinarith [norm_nonneg (R h), norm_nonneg h]

omit [NormedSpace ℝ Y] in
/-- Helper for Infrastructure I.16a: an eventual scalar envelope that is little-o of a comparison
scale also controls a vector-valued remainder in the same little-o sense. -/
theorem isLittleO_of_norm_le_of_isLittleO_bridge
    {α : Type*} [TopologicalSpace α] {R : α → Y} {a b : α → ℝ}
    {l : Filter α} (hR : ∀ᶠ x in l, ‖R x‖ ≤ a x)
    (ha : a =o[l] b) :
    R =o[l] b := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hR, Asymptotics.isLittleO_iff.mp ha hε] with x hx hax
  exact hx.trans ((le_abs_self (a x)).trans hax)

omit [NormedSpace ℝ Y] in
/-- Helper for Infrastructure I.16a: a norm recurrence with a translated successor
and a little-o forcing term transfers little-o control to the current remainder. -/
theorem isLittleO_of_norm_le_const_mul_add
    {R S e : ℝ → Y} {q : ℝ}
    (hineq : ∀ᶠ h in 𝓝 0, ‖R h‖ ≤ q * ‖S h‖ + ‖e h‖)
    (hS : S =o[𝓝 0] (fun h : ℝ ↦ h))
    (he : e =o[𝓝 0] (fun h : ℝ ↦ h)) :
    R =o[𝓝 0] (fun h : ℝ ↦ h) := by
  have hSnorm : (fun h : ℝ ↦ ‖S h‖) =o[𝓝 0] (fun h : ℝ ↦ h) :=
    hS.norm_left
  have hqS : (fun h : ℝ ↦ |q| * ‖S h‖) =o[𝓝 0] (fun h : ℝ ↦ h) :=
    hSnorm.const_mul_left |q|
  have henorm : (fun h : ℝ ↦ ‖e h‖) =o[𝓝 0] (fun h : ℝ ↦ h) :=
    he.norm_left
  have hsum :
      (fun h : ℝ ↦ |q| * ‖S h‖ + ‖e h‖) =o[𝓝 0] (fun h : ℝ ↦ h) :=
    hqS.add henorm
  have hbound : ∀ᶠ h in 𝓝 0,
      ‖R h‖ ≤ |q| * ‖S h‖ + ‖e h‖ := by
    filter_upwards [hineq] with h hh
    calc
      ‖R h‖ ≤ q * ‖S h‖ + ‖e h‖ := hh
      _ ≤ |q| * ‖S h‖ + ‖e h‖ := by
        exact add_le_add_left
          (mul_le_mul_of_nonneg_right (le_abs_self q) (norm_nonneg (S h))) _
  exact isLittleO_of_norm_le_of_isLittleO_bridge hbound hsum

/-- Helper for Infrastructure I.16a: a fixed-section secant certificate with a bounded continuous
limit section upgrades its map to a globally first-order continuously differentiable map. -/
theorem FixedSectionSecantCertificate.contDiff_one
    {f : ℝ → Y} (certificate : FixedSectionSecantCertificate f) :
    ContDiff ℝ 1 f := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro x
    exact (certificate.hasDerivAt x).differentiableAt
  · have hderiv : deriv f =
        fun x ↦ certificate.scale • certificate.limitSection x := by
      funext x
      exact (certificate.hasDerivAt x).deriv
    rw [hderiv]
    exact continuous_const.smul certificate.limitSection.continuous

end LocalCutoff.GraphTransform
