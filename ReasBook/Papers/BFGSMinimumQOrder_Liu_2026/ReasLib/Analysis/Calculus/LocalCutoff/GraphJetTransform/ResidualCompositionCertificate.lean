module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.ResidualBranchAdapter
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.UniformRemainderCertificate

public section

open scoped BigOperators

universe u v w

namespace LocalCutoff.GraphTransform

/-- Infrastructure I.16a: source-facing data for a finite composition residual.
The distinguished branch is kept separate from the finite non-distinguished
branches, while all analytic estimates remain explicit certificate fields. -/
structure ResidualCompositionCertificate
    (ι : Type u) (Θ : Type v) (E : Type w)
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    (K : Set Θ) where
  distinguished : ι
  principal : Θ → ℝ → E
  branch : ι → Θ → ℝ → E
  radius : ℝ
  principalBound : ℝ
  branchBound : ℝ
  principal_norm_le : ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < radius →
    ‖principal u t‖ ≤ principalBound
  branch_norm_le : ∀ i, i ≠ distinguished → ∀ u ∈ K, ∀ t : ℝ,
    ‖t‖ < radius → ‖branch i u t‖ ≤ branchBound

/-- Infrastructure I.16a: a residual composition certificate yields a uniform
norm bound once the principal and finite-branch budgets fit the target error. -/
theorem ResidualCompositionCertificate.norm_residual_le
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    {K : Set Θ}
    (certificate : ResidualCompositionCertificate ι Θ E K)
    (ε : ℝ)
    (hprincipal : certificate.principalBound ≤ ε / 2)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * certificate.branchBound ≤ ε / 2) :
    ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < certificate.radius →
      ‖certificate.principal u t +
          ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t‖ ≤ ε := by
  intro u hu t ht
  have hsum :
      ‖∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t‖ ≤
        ((Fintype.card ι : ℝ) - 1) * certificate.branchBound := by
    exact norm_sum_if_eq_zero_le (fun i ↦ certificate.branch i u t)
      certificate.distinguished certificate.branchBound
      (((Fintype.card ι : ℝ) - 1) * certificate.branchBound)
      (fun i hi ↦ certificate.branch_norm_le i hi u hu t ht) le_rfl
  let localCertificate :
      UniformRemainder.ResidualNormCertificate Unit E :=
    { residual := fun _ ↦ certificate.principal u t +
        ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t
      principal := fun _ ↦ certificate.principal u t
      remainder := fun _ ↦
        ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t
      decomposition := fun _ ↦ rfl
      principalBound := certificate.principalBound
      remainderBound := ((Fintype.card ι : ℝ) - 1) * certificate.branchBound
      principal_norm_le := fun _ ↦ certificate.principal_norm_le u hu t ht
      remainder_norm_le := fun _ ↦ hsum }
  have hlocal := localCertificate.residual_norm_le ()
  change ‖certificate.principal u t +
      ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t‖ ≤
    certificate.principalBound + ((Fintype.card ι : ℝ) - 1) * certificate.branchBound at hlocal
  calc
    ‖certificate.principal u t +
        ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t‖ ≤
        certificate.principalBound + ((Fintype.card ι : ℝ) - 1) * certificate.branchBound := hlocal
    _ ≤ ε / 2 + ε / 2 := add_le_add hprincipal hbudget
    _ = ε := by ring

/-- Infrastructure I.16a: the certificate API exposes the parent call shape
with `Composition.ones r` as the distinguished branch. -/
theorem composition_residual_norm_le
    {ι : Type u} {Θ : Type v} {E : Type w}
    [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E]
    {K : Set Θ}
    (certificate : ResidualCompositionCertificate ι Θ E K)
    (ε : ℝ)
    (hprincipal : certificate.principalBound ≤ ε / 2)
    (hbudget : ((Fintype.card ι : ℝ) - 1) * certificate.branchBound ≤ ε / 2) :
    ∀ u ∈ K, ∀ t : ℝ, ‖t‖ < certificate.radius →
      ‖certificate.principal u t +
          ∑ i, if i = certificate.distinguished then 0 else certificate.branch i u t‖ ≤ ε := by
  exact certificate.norm_residual_le ε hprincipal hbudget

end LocalCutoff.GraphTransform
