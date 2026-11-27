/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15.Normed

public section

noncomputable section

namespace VariationalRegularization

/-- The analytic extension hypothesis used by the BV embeddings and compactness
theorem. There is a bounded linear extension from `BV(Ω)` to ambient `BV`,
agreeing almost everywhere on `Ω`, whose images all vanish outside one compact
set. Bounded Lipschitz domains admit such extensions (after a fixed cutoff).

This definition specifies the extension property directly; no geometric
extension theorem is asserted here. In particular it assumes neither compactness
nor finite approximation of a BV ball. It does not require zero boundary trace:
the extension may be nonzero on both sides of the boundary. -/
class HasBoundedBVExtension {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) : Prop where
  exists_extension :
    ∃ E : BV Ω →L[ℝ] BV (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))),
      ∃ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K ∧
        (∀ u : BV Ω, (E u).toL1 =ᵐ[domainMeasure Ω] u.toL1) ∧
        (∀ u : BV Ω,
          ∀ᵐ x ∂domainMeasure (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))),
            x ∉ K → (E u).toL1 x = 0)

/-- The extension controls the full BV norm, hence both its ambient `L¹` norm
and its variation, by a fixed multiple of the original BV norm. -/
theorem HasBoundedBVExtension.exists_extension_with_bound {d : ℕ}
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))
    [HasBoundedBVExtension Ω] :
    ∃ E : BV Ω →L[ℝ] BV (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))),
      ∃ K : Set (EuclideanSpace ℝ (Fin d)), ∃ C : ℝ,
        IsCompact K ∧ 0 ≤ C ∧
        (∀ u : BV Ω, (E u).toL1 =ᵐ[domainMeasure Ω] u.toL1) ∧
        (∀ u : BV Ω,
          ∀ᵐ x ∂domainMeasure (⊤ : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))),
            x ∉ K → (E u).toL1 x = 0) ∧
        (∀ u : BV Ω, ‖E u‖ ≤ C * ‖u‖) := by
  obtain ⟨E, K, hK, hrestrict, hsupport⟩ :=
    HasBoundedBVExtension.exists_extension (Ω := Ω)
  exact ⟨E, K, ‖E‖, hK, norm_nonneg E, hrestrict, hsupport, E.le_opNorm⟩

end VariationalRegularization
