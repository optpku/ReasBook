/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

universe u v

namespace Submodule

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Definition 2-extra-1 (1). A vector `sStar` is a best approximation to `f` from a subspace `S`
if it minimizes `s ↦ ‖s - f‖` on `S`. -/
structure IsBestApproximation (S : Submodule 𝕜 E) (f sStar : E) : Prop where
  /-- A best approximation lies in the approximating subspace. -/
  mem : sStar ∈ S
  /-- A best approximation minimizes the distance to `f` over the whole subspace. -/
  norm_le : ∀ s ∈ S, ‖sStar - f‖ ≤ ‖s - f‖

namespace IsBestApproximation

set_option linter.defProp false

/-- Builds a best approximation from the source membership and pointwise minimality conditions. -/
def ofMemAndNormLE {S : Submodule 𝕜 E} {f sStar : E} (hsStar_mem : sStar ∈ S)
    (hmin : ∀ s ∈ S, ‖sStar - f‖ ≤ ‖s - f‖) :
    S.IsBestApproximation f sStar :=
  ⟨hsStar_mem, hmin⟩

set_option linter.defProp true

/-- A best approximation determines the corresponding `IsMinOn` statement on `S`. -/
theorem isMinOn {S : Submodule 𝕜 E} {f sStar : E} (hsStar : S.IsBestApproximation f sStar) :
    IsMinOn (fun s : E ↦ ‖s - f‖) (S : Set E) sStar := by
  rw [isMinOn_iff]
  exact hsStar.norm_le

end IsBestApproximation

/-- Rewrites `S.IsBestApproximation f sStar` as the source minimality inequality over `S`. -/
theorem isBestApproximation_iff {S : Submodule 𝕜 E} {f sStar : E} :
    S.IsBestApproximation f sStar ↔
      sStar ∈ S ∧ ∀ s ∈ S, ‖sStar - f‖ ≤ ‖s - f‖ := by
  constructor
  · intro hsStar
    exact ⟨hsStar.mem, hsStar.norm_le⟩
  · rintro ⟨hsStar_mem, hmin⟩
    exact IsBestApproximation.ofMemAndNormLE hsStar_mem hmin

/-- Rewrites `S.IsBestApproximation f sStar` as membership in `S` together with realization of the
distance infimum over the subspace. -/
theorem isBestApproximation_iff_mem_norm_eq_iInf {S : Submodule 𝕜 E} {f sStar : E} :
    S.IsBestApproximation f sStar ↔
      sStar ∈ S ∧ ‖f - sStar‖ = ⨅ s : S, ‖f - s‖ := by
  constructor
  · intro hsStar
    rcases isBestApproximation_iff.1 hsStar with ⟨hsStar_mem, hmin⟩
    refine ⟨hsStar_mem, le_antisymm ?_ ?_⟩
    · refine le_ciInf fun s ↦ ?_
      simpa [norm_sub_rev] using hmin s s.property
    · have hbounded : BddBelow (Set.range fun s : S ↦ ‖f - s‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨s, rfl⟩
        exact norm_nonneg _
      exact ciInf_le hbounded ⟨sStar, hsStar_mem⟩
  · rintro ⟨hsStar_mem, hsStar_eq⟩
    refine isBestApproximation_iff.2 ⟨hsStar_mem, ?_⟩
    intro s hs
    have hbounded : BddBelow (Set.range fun t : S ↦ ‖f - t‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact norm_nonneg _
    calc
      ‖sStar - f‖ = ‖f - sStar‖ := by rw [norm_sub_rev]
      _ = ⨅ t : S, ‖f - t‖ := hsStar_eq
      _ ≤ ‖f - (⟨s, hs⟩ : S)‖ := ciInf_le hbounded ⟨s, hs⟩
      _ = ‖f - s‖ := rfl
      _ = ‖s - f‖ := by rw [norm_sub_rev]

namespace IsBestApproximation

/-- A best approximation realizes the distance infimum over the approximating subspace. -/
theorem norm_eq_iInf {S : Submodule 𝕜 E} {f sStar : E}
    (hsStar : S.IsBestApproximation f sStar) :
    ‖f - sStar‖ = ⨅ s : S, ‖f - s‖ :=
  (isBestApproximation_iff_mem_norm_eq_iInf.1 hsStar).2

end IsBestApproximation

/-- Definition 2-extra-1 (2). If a best approximation to `f` from `S` exists, then it is unique. -/
theorem eq_of_isBestApproximation {S : Submodule 𝕜 E} {f s₁ s₂ : E}
    (hs₁ : S.IsBestApproximation f s₁) (hs₂ : S.IsBestApproximation f s₂) :
    s₁ = s₂ := by
  rcases isBestApproximation_iff_mem_norm_eq_iInf.1 hs₁ with ⟨hs₁_mem, hs₁_eq⟩
  rcases isBestApproximation_iff_mem_norm_eq_iInf.1 hs₂ with ⟨hs₂_mem, hs₂_eq⟩
  have horth₁ : f - s₁ ∈ Sᗮ := by
    rw [S.mem_orthogonal']
    intro s hs
    exact (S.norm_eq_iInf_iff_inner_eq_zero hs₁_mem).1 hs₁_eq s hs
  have horth₂ : f - s₂ ∈ Sᗮ := by
    rw [S.mem_orthogonal']
    intro s hs
    exact (S.norm_eq_iInf_iff_inner_eq_zero hs₂_mem).1 hs₂_eq s hs
  have hsub_mem : s₁ - s₂ ∈ S := S.sub_mem hs₁_mem hs₂_mem
  have hsub_orth : s₁ - s₂ ∈ Sᗮ := by
    have h : (f - s₂) - (f - s₁) ∈ Sᗮ := Submodule.sub_mem _ horth₂ horth₁
    have hEq : (f - s₂) - (f - s₁) = s₁ - s₂ := by
      rw [sub_sub_sub_cancel_left]
    exact hEq ▸ h
  rw [S.mem_orthogonal'] at hsub_orth
  exact sub_eq_zero.1 (inner_self_eq_zero.1 (hsub_orth _ hsub_mem))

/-- If `S` admits an orthogonal projection, the canonical best approximation to `f` is
`S.starProjection f`. -/
theorem isBestApproximation_starProjection (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    (f : E) :
    S.IsBestApproximation f (S.starProjection f) := by
  exact
    isBestApproximation_iff_mem_norm_eq_iInf.2
      ⟨S.starProjection_apply_mem f, S.starProjection_minimal f⟩

/-- A best approximation in a subspace with orthogonal projection is the canonical projection. -/
theorem eq_starProjection_of_isBestApproximation (S : Submodule 𝕜 E) [S.HasOrthogonalProjection]
    {f sStar : E} (hsStar : S.IsBestApproximation f sStar) :
    S.starProjection f = sStar := by
  rcases isBestApproximation_iff_mem_norm_eq_iInf.1 hsStar with ⟨hsStar_mem, hsStar_eq⟩
  exact
    S.eq_starProjection_of_mem_of_inner_eq_zero hsStar_mem
      ((S.norm_eq_iInf_iff_inner_eq_zero hsStar_mem).1 hsStar_eq)

/-- Best approximations exist in a complete subspace. -/
theorem exists_isBestApproximation_of_isComplete {S : Submodule 𝕜 E}
    (hS : IsComplete (S : Set E)) (f : E) :
    ∃ sStar, S.IsBestApproximation f sStar := by
  rcases S.exists_norm_eq_iInf_of_complete_subspace hS f with ⟨sStar, hsStar_mem, hsStar_eq⟩
  exact
    ⟨sStar, isBestApproximation_iff_mem_norm_eq_iInf.2 ⟨hsStar_mem, hsStar_eq⟩⟩

/-- Definition 2-extra-1 (3). A closed subspace `S` of a complete inner product space admits a
best approximation to every `f`. -/
theorem exists_isBestApproximation_of_isClosed {S : Submodule 𝕜 E} [CompleteSpace E]
    (hS : IsClosed (S : Set E)) (f : E) :
    ∃ sStar, S.IsBestApproximation f sStar :=
  exists_isBestApproximation_of_isComplete hS.isComplete f

/-- Definition 2-extra-1 (4). A finite-dimensional subspace `S` admits a best approximation to
every `f`. -/
theorem exists_isBestApproximation_of_finiteDimensional {S : Submodule 𝕜 E}
    [FiniteDimensional 𝕜 S] (f : E) :
    ∃ sStar, S.IsBestApproximation f sStar :=
  exists_isBestApproximation_of_isComplete
    (completeSpace_coe_iff_isComplete.mp (FiniteDimensional.complete 𝕜 S))
    f

end Submodule
