module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedSectionDerivativeBridge
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.UniformRemainderCertificate

public section

open Filter
open scoped Topology

universe u

namespace LocalCutoff.GraphTransform

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Infrastructure I.16a: a finite family of compact-uniform linear branch bounds
has one common radius for the non-distinguished composition sum. -/
theorem JetTransform.finiteComposition_nonOnes_uniformBoundOn
    {α Θ Y : Type*} [Fintype α] [DecidableEq α]
    [NormedAddCommGroup Y]
    (distinguished : α) (K : Set Θ) (b : α → Θ → ℝ → Y) (C : α → ℝ)
    (hbranch : ∀ c, c ≠ distinguished → ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ,
      ‖t‖ < δ → ‖b c u t‖ ≤ C c * ‖t‖) :
    ∃ δ > 0, ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < δ →
      ‖∑ c : α, if c = distinguished then 0 else b c u t‖ ≤
        (∑ c : α, if c = distinguished then 0 else C c) * ‖t‖ := by
  exact UniformRemainder.finiteNonDistinguishedSum_uniformBoundOn
    distinguished K b C hbranch

/-!
The next lemma is the metric stability interface for approximate fixed sections.
It is independent of the source-specific construction of a graph-jet operator.
-/

/-- Helper for Infrastructure I.16a: a strict bounded-section contraction turns a
vanishing operator residual into convergence toward its canonical fixed section. -/
theorem tendsto_boundedSection_of_tendsto_operator_residual
    {α β : Type*} [TopologicalSpace α] [Nonempty α]
    [NormedAddCommGroup β] [CompleteSpace β]
    {T : (BoundedContinuousFunction α β) → BoundedContinuousFunction α β}
    (certificate : BoundedSectionContractionCertificate T)
    (sections : ℝ → BoundedContinuousFunction α β)
    (hresidual : Tendsto (fun t => dist (T (sections t)) (sections t))
      (𝓝 0) (𝓝 0)) :
    Tendsto sections (𝓝 0)
      (𝓝 (ContractingWith.fixedPoint T certificate.contractingWith)) := by
  have hcontract := certificate.contractingWith
  have hfixed : Function.IsFixedPt T (ContractingWith.fixedPoint T hcontract) :=
    hcontract.fixedPoint_isFixedPt
  have hdist : ∀ t : ℝ,
      dist (sections t) (ContractingWith.fixedPoint T hcontract) ≤
        dist (sections t) (T (sections t)) /
          (1 - (certificate.contractionFactor : ℝ)) := by
    intro t
    exact hcontract.dist_le_of_fixedPoint (sections t) hfixed
  have hresidual' : Tendsto (fun t => dist (sections t) (T (sections t)))
      (𝓝 0) (𝓝 0) := by
    simpa only [dist_comm] using hresidual
  have hquot : Tendsto
      (fun t => dist (sections t) (T (sections t)) /
        (1 - (certificate.contractionFactor : ℝ)))
      (𝓝 0) (𝓝 0) := by
    simpa only [zero_div] using hresidual'.div_const
      (1 - (certificate.contractionFactor : ℝ))
  have hdist0 : Tendsto
      (fun t => dist (sections t) (ContractingWith.fixedPoint T hcontract))
      (𝓝 0) (𝓝 0) := by
    exact squeeze_zero (fun t => dist_nonneg) hdist hquot
  exact tendsto_iff_dist_tendsto_zero.mpr hdist0

/-- Helper for Infrastructure I.16a: an operator residual and a translated secant
formula assemble the canonical fixed-section secant certificate. -/
noncomputable def fixedSectionSecantCertificate_of_operator_residual
    {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    {T : (BoundedContinuousFunction ℝ Y) → BoundedContinuousFunction ℝ Y}
    (certificate : BoundedSectionContractionCertificate T)
    (f : ℝ → Y) (scale : ℝ)
    (sections : ℝ → BoundedContinuousFunction ℝ Y)
    (hresidual : Tendsto (fun t => dist (T (sections t)) (sections t))
      (𝓝 0) (𝓝 0))
    (hsecant : ∀ x : ℝ,
      (fun t : ℝ => t⁻¹ • (f (x + t) - f x)) =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
        (fun t => scale • sections t x)) :
    FixedSectionSecantCertificate f :=
  { scale := scale
    sections := sections
    limitSection := ContractingWith.fixedPoint T certificate.contractingWith
    sections_tendsto := tendsto_boundedSection_of_tendsto_operator_residual
      certificate sections hresidual
    secant_formula := hsecant }

/-!
This module gives the owner-level interface between a contracted top-section
operator and the normalized secants of the predecessor Taylor coefficient.
The source-specific construction of the operator and secants remains outside
the context; the closing theorem only uses their declared compatibility.
-/

/-- Infrastructure I.16a: a fixed graph context records the contracted top-section
operator, its bounded fixed section, and a normalized secant certificate whose
limit is the curry-left derivative represented by that section. -/
structure FixedGraphJetContext (r : ℕ) (ζ : ℝ → X) where
  operatorData : BoundedTopSectionOperatorData (X := X) (r - 1 + 1)
  fixedSection : BoundedContinuousFunction ℝ ((ℝ [×(r - 1 + 1)]→L[ℝ] X))
  fixedSection_is_fixed : operatorData.operator fixedSection = fixedSection
  secant : FixedSectionSecantCertificate
    (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
  secant_curry_eq : ∀ u,
    (fixedSection u).curryLeft =
      ContinuousLinearMap.toSpanSingleton ℝ (secant.scale • secant.limitSection u)

/-- Infrastructure I.16a: the fixed section stored in a graph context is the
canonical contraction fixed point for its recorded operator data. -/
theorem FixedGraphJetContext.fixedSection_eq_canonical
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ) :
    context.fixedSection = canonicalFixedTopSection context.operatorData := by
  exact fixedTopSection_eq_canonical context.operatorData context.fixedSection
    context.fixedSection_is_fixed

/-- Helper for Infrastructure I.16a: the secant certificate in a fixed graph
context supplies the predecessor derivative equation for its stored section. -/
theorem FixedGraphJetContext.fixedSection_derivative
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ) :
    ∀ u, HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      ((context.fixedSection u).curryLeft) u := by
  intro u
  rw [context.secant_curry_eq u]
  exact (context.secant.hasDerivAt u).hasFDerivAt

/-- Helper for Infrastructure I.16a: the secant certificate makes the scalar predecessor
coefficient `iteratedDeriv (r - 1) ζ` continuously differentiable to first order. -/
theorem FixedGraphJetContext.predecessor_iteratedDeriv_contDiff_one
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ) :
    ContDiff ℝ 1 (iteratedDeriv (r - 1) ζ) := by
  have hsection : ContDiff ℝ 1
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1)) :=
    context.secant.contDiff_one
  let evaluator :
      (ℝ [×(r - 1)]→L[ℝ] X) →L[ℝ] X :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin (r - 1) ↦ ℝ) X
      (fun _ ↦ (1 : ℝ))
  have heval := evaluator.contDiff.comp hsection
  have heq :
      (fun y ↦ evaluator ((ftaylorSeries ℝ ζ y) (r - 1))) =
        iteratedDeriv (r - 1) ζ := by
    funext y
    change (ftaylorSeries ℝ ζ y) (r - 1)
        (fun _ : Fin (r - 1) ↦ (1 : ℝ)) =
      iteratedDeriv (r - 1) ζ y
    rw [iteratedDeriv_eq_iteratedFDeriv]
    rfl
  rw [← heq]
  simpa only [Function.comp_def, evaluator,
    ContinuousMultilinearMap.apply_apply] using heval

/-- Infrastructure I.16a: a fixed graph context projects to the generic
holonomic top-section data interface used by orderwise smoothness assembly. -/
noncomputable def FixedGraphJetContext.toHolonomicTopSectionData
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ) :
    HolonomicTopSectionData ζ r :=
  { value := context.fixedSection
    continuous_value := context.fixedSection.continuous
    derivative := context.fixedSection_derivative }

/-- Infrastructure I.16a: the projected holonomic top-section data supplies
successor smoothness and the corresponding iterated derivative identification. -/
theorem FixedGraphJetContext.contDiff_succ_and_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ContDiff ℝ r ζ ∧
      ∀ u, context.fixedSection u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  exact (context.toHolonomicTopSectionData).contDiff_succ_and_eq_iteratedFDeriv hr hprev

/-- Infrastructure I.16a: a fixed graph context closes to the holonomic
top-section certificate consumed by the finite-smooth successor theorem. -/
noncomputable def FixedGraphJetContext.toHolonomicFixedTopSectionCertificate
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ) :
    HolonomicFixedTopSectionCertificate r ζ :=
  { data := context.operatorData
    fixedSection := context.fixedSection
    fixedSection_is_fixed := context.fixedSection_is_fixed
    fixedSection_derivative := context.fixedSection_derivative }

/-- Infrastructure I.16a: the fixed graph context simultaneously supplies
successor smoothness and identifies its stored section with the next derivative. -/
theorem FixedGraphJetContext.contDiff_succ_and_fixedSection_eq_iteratedFDeriv
    {r : ℕ} {ζ : ℝ → X} (context : FixedGraphJetContext r ζ)
    (hr : 1 ≤ r) (hprev : ContDiff ℝ (r - 1) ζ) :
    ContDiff ℝ r ζ ∧
      ∀ u, context.fixedSection u = iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  have hresult :=
    (context.toHolonomicFixedTopSectionCertificate).contDiff_succ_and_fixedSection_eq_iteratedFDeriv
      hr hprev
  constructor
  · exact hresult.1
  · intro u
    simpa only [FixedGraphJetContext.toHolonomicFixedTopSectionCertificate] using hresult.2 u

/-- Infrastructure I.16a: an orderwise family of fixed graph contexts upgrades a
continuous base graph through every supplied finite order. -/
theorem contDiff_of_fixedGraphJetContexts
    {ν : ℕ} {ζ : ℝ → X}
    (contexts : ∀ r : ℕ, 1 ≤ r → r ≤ ν → FixedGraphJetContext r ζ)
    (hbase : ContDiff ℝ 0 ζ) :
    ContDiff ℝ ν ζ := by
  induction ν with
  | zero => exact hbase
  | succ ν ih =>
      have hprev : ContDiff ℝ ν ζ := by
        apply ih
        intro r hr hrν
        exact contexts r hr (hrν.trans (Nat.le_succ ν))
      have hsucc : 1 ≤ ν + 1 := by omega
      have hsucc_bound : ν + 1 ≤ Nat.succ ν := by omega
      have context := contexts (ν + 1) hsucc hsucc_bound
      exact (context.contDiff_succ_and_fixedSection_eq_iteratedFDeriv
        hsucc hprev).1

/-- Infrastructure I.16a: after the orderwise bootstrap, every supplied fixed
section is the corresponding iterated derivative of the graph. -/
theorem fixedSection_eq_iteratedFDeriv_of_fixedGraphJetContexts
    {ν : ℕ} {ζ : ℝ → X}
    (contexts : ∀ r : ℕ, 1 ≤ r → r ≤ ν → FixedGraphJetContext r ζ)
    (hbase : ContDiff ℝ 0 ζ) :
    ∀ (r : ℕ) (hr : 1 ≤ r) (hrν : r ≤ ν) (u : ℝ),
      (contexts r hr hrν).fixedSection u =
        iteratedFDeriv ℝ (r - 1 + 1) ζ u := by
  have hcont : ContDiff ℝ ν ζ := contDiff_of_fixedGraphJetContexts contexts hbase
  intro r hr hrν u
  have hprevOrder : ((r - 1 : ℕ) : WithTop ENat) ≤ (ν : WithTop ENat) := by
    exact_mod_cast (Nat.sub_le r 1).trans hrν
  have hprev : ContDiff ℝ (r - 1) ζ := hcont.of_le hprevOrder
  exact (contexts r hr hrν).contDiff_succ_and_fixedSection_eq_iteratedFDeriv
    hr hprev |>.2 u

/-- Infrastructure I.16a: an orderwise family of fixed graph contexts projects
to the holonomic fixed-section certificates required by downstream assembly. -/
noncomputable def holonomicFixedTopSectionCertificates_of_fixedGraphJetContexts
    {ν : ℕ} {ζ : ℝ → X}
    (contexts : ∀ r : ℕ, 1 ≤ r → r ≤ ν → FixedGraphJetContext r ζ) :
    ∀ r : ℕ, 1 ≤ r → r ≤ ν → HolonomicFixedTopSectionCertificate r ζ :=
  fun r hr hrν => (contexts r hr hrν).toHolonomicFixedTopSectionCertificate

end LocalCutoff.GraphTransform
