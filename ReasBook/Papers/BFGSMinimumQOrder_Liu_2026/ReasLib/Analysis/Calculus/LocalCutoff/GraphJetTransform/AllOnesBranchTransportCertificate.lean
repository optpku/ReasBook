module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ResidualCompositionCertificate
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.BoundedHolonomicFixedSectionAdapter

public section

open scoped BigOperators

universe u v w

namespace LocalCutoff.GraphTransform

/-- Infrastructure I.16a: the distinguished all-ones branch and its transported
predecessor expression are identified by an explicit coefficient-level bridge. -/
structure AllOnesBranchTransportCertificate
    (Θ : Type u) (E : Type v) [NormedAddCommGroup E] where
  principal : Θ → ℝ → E
  transported : Θ → ℝ → E
  principal_eq_transported : ∀ u t, principal u t = transported u t

/-- Infrastructure I.16a: a bound for the transported all-ones expression
transfers to the original principal branch. -/
theorem AllOnesBranchTransportCertificate.principal_norm_le
    {Θ : Type u} {E : Type v} [NormedAddCommGroup E]
    (certificate : AllOnesBranchTransportCertificate Θ E)
    {C : ℝ} (htransport : ∀ u t, ‖certificate.transported u t‖ ≤ C) :
    ∀ u t, ‖certificate.principal u t‖ ≤ C := by
  intro u t
  rw [certificate.principal_eq_transported]
  exact htransport u t

/-- Infrastructure I.16a: an all-ones transport bridge feeds directly into the
finite non-distinguished residual estimate. -/
theorem residual_norm_le_of_allOnesTransport
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (certificate : AllOnesBranchTransportCertificate Θ E)
    (distinguished : ι) (branches : ι → Θ → ℝ → E)
    (K : Set Θ) (radius ε δ : ℝ)
    (htransport : ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < radius →
      ‖certificate.transported u t‖ ≤ ε / 2)
    (hbranch : ∀ i, i ≠ distinguished → ∀ u ∈ K, ∀ t : ℝ,
      ‖t‖ < radius → ‖branches i u t‖ ≤ δ)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * δ ≤ ε / 2) :
    ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < radius →
      ‖certificate.principal u t +
          ∑ i, if i = distinguished then 0 else branches i u t‖ ≤ ε := by
  intro u hu t ht
  apply residual_norm_le_of_principal_and_nonDistinguished distinguished
    (certificate.principal u t) (fun i ↦ branches i u t) δ ε
  · rw [certificate.principal_eq_transported]
    exact htransport u hu t ht
  · intro i hi
    exact hbranch i hi u hu t ht
  · exact hbudget

/-- Infrastructure I.16a: a residual-composition certificate can use an explicit
transport certificate for its principal branch without unfolding composition data. -/
theorem ResidualCompositionCertificate.norm_residual_le_of_allOnesTransport
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    {K : Set Θ}
    (composition : ResidualCompositionCertificate ι Θ E K)
    (transport : AllOnesBranchTransportCertificate Θ E)
    (hprincipal_eq : ∀ u t, composition.principal u t = transport.principal u t)
    (ε : ℝ)
    (htransport : ∀ u ∈ K, ∀ t : ℝ, ‖transport.transported u t‖ ≤ ε / 2)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * composition.branchBound ≤ ε / 2) :
    ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < composition.radius →
      ‖composition.principal u t +
          ∑ i, if i = composition.distinguished then 0 else composition.branch i u t‖ ≤ ε := by
  intro u hu t ht
  have hprincipal : ‖composition.principal u t‖ ≤ ε / 2 := by
    rw [hprincipal_eq, transport.principal_eq_transported]
    exact htransport u hu t
  exact residual_norm_le_of_principal_and_nonDistinguished composition.distinguished
    (composition.principal u t) (fun i ↦ composition.branch i u t)
    composition.branchBound ε hprincipal
    (fun i hi ↦ composition.branch_norm_le i hi u hu t ht) hbudget

end LocalCutoff.GraphTransform
