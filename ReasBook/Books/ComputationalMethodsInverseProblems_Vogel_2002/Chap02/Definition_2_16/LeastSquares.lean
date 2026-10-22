/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

universe u v w

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}

section Objective

variable [NormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- The residual objective `‖K f - g‖` for the least-squares problem `K f = g`. -/
def leastSquaresObjective (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) : ℝ :=
  ‖K f - g‖

/-- The defining formula for `ContinuousLinearMap.leastSquaresObjective`. -/
theorem leastSquaresObjective_def (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    K.leastSquaresObjective g f = ‖K f - g‖ := by
  simp [leastSquaresObjective]

/-- A vector `f` is a least-squares solution of `K f = g` when it minimizes the residual norm on
all of `H₁`. -/
def IsLeastSquaresSolution (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) : Prop :=
  IsMinOn (K.leastSquaresObjective g) Set.univ f

/-- The defining characterization of `ContinuousLinearMap.IsLeastSquaresSolution`. -/
theorem isLeastSquaresSolution_iff (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    K.IsLeastSquaresSolution g f ↔ ∀ h : H₁, ‖K f - g‖ ≤ ‖K h - g‖ := by
  rw [IsLeastSquaresSolution, isMinOn_iff]
  simp [leastSquaresObjective_def]

/-- Minimizing the squared residual recovers the same least-squares predicate as minimizing the
residual norm itself. -/
theorem isMinOn_residualNormSq_iff_isLeastSquaresSolution
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    IsMinOn (fun h : H₁ ↦ ‖K h - g‖ ^ 2) Set.univ f ↔ K.IsLeastSquaresSolution g f := by
  rw [IsLeastSquaresSolution, isMinOn_iff, isMinOn_iff]
  simp_rw [leastSquaresObjective_def]
  constructor
  · intro h x hx
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h x hx)
  · intro h x hx
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (h x hx)

end Objective

section AffineSubspace

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂]

/-- Helper for Definition 2.16: a least-squares solution realizes the best-approximation value in
`K.range`. -/
private theorem residualNorm_eq_iInf_range
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    ‖g - K f_ls‖ = ⨅ s : K.range, ‖g - s‖ := by
  rw [K.isLeastSquaresSolution_iff] at hls
  refine le_antisymm ?_ ?_
  · refine le_ciInf fun s ↦ ?_
    rcases s with ⟨s, ⟨h, rfl⟩⟩
    simpa [norm_sub_rev] using hls h
  · have hbdd : BddBelow (Set.range fun s : K.range ↦ ‖g - s‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbdd ⟨K f_ls, ⟨f_ls, rfl⟩⟩

/-- Helper for Definition 2.16: the residual of a least-squares solution is orthogonal to
`K.range`. -/
private theorem residual_mem_range_orthogonal
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    g - K f_ls ∈ K.rangeᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  have hf_ls_range : K f_ls ∈ K.range := ⟨f_ls, rfl⟩
  exact
    ((K.range.norm_eq_iInf_iff_inner_eq_zero hf_ls_range).1
      (K.residualNorm_eq_iInf_range g hls)) y hy

/-- All least-squares solutions form the affine subspace `AffineSubspace.mk' f_ls K.ker` through a
chosen least-squares solution `f_ls`. -/
theorem isLeastSquaresSolution_iff_mem_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresSolution g f ↔ f ∈ AffineSubspace.mk' f_ls K.ker := by
  constructor
  · intro hf
    -- Compare residuals of two least-squares solutions through orthogonality to the range.
    have horth_ls : g - K f_ls ∈ K.rangeᗮ := K.residual_mem_range_orthogonal g hls
    have horth_f : g - K f ∈ K.rangeᗮ := K.residual_mem_range_orthogonal g hf
    have hKsub_orth : K f - K f_ls ∈ K.rangeᗮ := by
      have hsub : (g - K f_ls) - (g - K f) ∈ K.rangeᗮ :=
        Submodule.sub_mem _ horth_ls horth_f
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hKsub_eq : K (f - f_ls) = K f - K f_ls := by
      simp [map_sub]
    have hKsub_range : K f - K f_ls ∈ K.range := by
      exact ⟨f - f_ls, hKsub_eq⟩
    rw [Submodule.mem_orthogonal'] at hKsub_orth
    have hzero : K f - K f_ls = 0 := by
      exact inner_self_eq_zero.mp (hKsub_orth _ hKsub_range)
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.sub_mem_ker_iff]
    exact sub_eq_zero.mp hzero
  · intro hf
    -- Any vector in the affine translate has the same image under `K`.
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.sub_mem_ker_iff] at hf
    rw [K.isLeastSquaresSolution_iff] at hls ⊢
    intro h
    have hres : ‖K f_ls - g‖ ≤ ‖K h - g‖ := hls h
    have hf' : K f_ls = K f := by
      simpa using hf.symm
    simpa [hf'] using hres

end AffineSubspace

end ContinuousLinearMap
