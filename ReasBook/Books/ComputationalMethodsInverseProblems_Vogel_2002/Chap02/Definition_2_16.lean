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

section MinimumNorm

variable [NormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂]

/-- A vector `f` is a least-squares minimum-norm solution for `K f = g` when it is a
least-squares solution and has minimal norm among all least-squares solutions. -/
structure IsLeastSquaresMinimumNormSolution
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) : Prop where
  /-- A least-squares minimum-norm solution is, in particular, a least-squares solution. -/
  leastSquares : K.IsLeastSquaresSolution g f
  /-- Among least-squares solutions, a least-squares minimum-norm solution has minimal norm. -/
  norm_le : ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖

namespace IsLeastSquaresMinimumNormSolution

set_option linter.defProp false in
/-- Constructs a least-squares minimum-norm solution from least-squares solvability and the
minimal-norm inequality over all least-squares solutions. -/
def ofLeastSquaresAndNormLE
    {K : H₁ →L[𝕜] H₂} {g : H₂} {f : H₁}
    (hLeastSquares : K.IsLeastSquaresSolution g f)
    (hNormLE : ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖) :
    K.IsLeastSquaresMinimumNormSolution g f :=
  ⟨hLeastSquares, hNormLE⟩

end IsLeastSquaresMinimumNormSolution

/-- The defining characterization of
`ContinuousLinearMap.IsLeastSquaresMinimumNormSolution`. -/
theorem isLeastSquaresMinimumNormSolution_iff
    (K : H₁ →L[𝕜] H₂) (g : H₂) (f : H₁) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        ∀ h : H₁, K.IsLeastSquaresSolution g h → ‖f‖ ≤ ‖h‖ := by
  constructor
  · intro hf
    exact ⟨hf.leastSquares, hf.norm_le⟩
  · rintro ⟨hf, hnorm⟩
    exact ⟨hf, hnorm⟩

end MinimumNorm

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
  exact
    ((K.range.norm_eq_iInf_iff_inner_eq_zero (show K f_ls ∈ K.range from ⟨f_ls, rfl⟩)).1
      (K.residualNorm_eq_iInf_range g hls)) y hy

/-- All least-squares solutions form the affine subspace `AffineSubspace.mk' f_ls K.ker` through a
chosen least-squares solution `f_ls`. -/
theorem isLeastSquaresSolution_iff_mem_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresSolution g f ↔ f ∈ AffineSubspace.mk' f_ls K.ker := by
  constructor
  · intro hf
    have horth_ls : g - K f_ls ∈ K.rangeᗮ := K.residual_mem_range_orthogonal g hls
    have horth_f : g - K f ∈ K.rangeᗮ := K.residual_mem_range_orthogonal g hf
    have hKsub_orth : K f - K f_ls ∈ K.rangeᗮ := by
      have hsub : (g - K f_ls) - (g - K f) ∈ K.rangeᗮ :=
        Submodule.sub_mem _ horth_ls horth_f
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub
    have hKsub_range : K f - K f_ls ∈ K.range := by
      exact ⟨f - f_ls, by simp [map_sub]⟩
    rw [Submodule.mem_orthogonal'] at hKsub_orth
    have hzero : K f - K f_ls = 0 := by
      exact inner_self_eq_zero.mp (hKsub_orth _ hKsub_range)
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.sub_mem_ker_iff]
    exact sub_eq_zero.mp hzero
  · intro hf
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.sub_mem_ker_iff] at hf
    rw [K.isLeastSquaresSolution_iff] at hls ⊢
    intro h
    have hres : ‖K f_ls - g‖ ≤ ‖K h - g‖ := hls h
    have hf' : K f_ls = K f := by simpa using hf.symm
    simpa [hf'] using hres

end AffineSubspace

/- Definition 2.16 (1). Least-squares solutions of `K f = g` are represented by the canonical
predicate `ContinuousLinearMap.IsLeastSquaresSolution`. -/
#check ContinuousLinearMap.IsLeastSquaresSolution

/- Definition 2.16 (2). If `f_ls` is a least-squares solution, then all least-squares solutions
are exactly the points of `AffineSubspace.mk' f_ls K.ker`. -/
#check ContinuousLinearMap.isLeastSquaresSolution_iff_mem_affineSubspace

/- Definition 2.16 (3). The least-squares minimum-norm notion is represented by the existing
predicate `ContinuousLinearMap.IsLeastSquaresMinimumNormSolution`. -/
#check ContinuousLinearMap.IsLeastSquaresMinimumNormSolution

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Definition 2.16 (4). For a chosen least-squares solution `f_ls`, a vector `f` is a
least-squares minimum-norm solution of `K f = g` exactly when it is a least-squares solution and
its norm is minimal on `AffineSubspace.mk' f_ls K.ker`, expressed by `IsMinOn`. -/
theorem isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        IsMinOn (fun h : H₁ ↦ ‖h‖) (AffineSubspace.mk' f_ls K.ker) f := by
  let _ : CompleteSpace H₁ := inferInstance
  let _ : CompleteSpace H₂ := inferInstance
  -- Rewrite the bundled minimum-norm predicate into its least-squares and pointwise norm parts.
  rw [K.isLeastSquaresMinimumNormSolution_iff]
  have hmemiff (h : H₁) :
      K.IsLeastSquaresSolution g h ↔ h ∈ AffineSubspace.mk' f_ls K.ker :=
    K.isLeastSquaresSolution_iff_mem_affineSubspace (g := g) (f_ls := f_ls) (f := h) hls
  constructor
  · rintro ⟨hf, hnorm⟩
    refine ⟨hf, ?_⟩
    -- Restrict the global norm comparison to the affine subspace of least-squares solutions.
    rw [isMinOn_iff]
    intro h hh
    exact hnorm h ((hmemiff h).mpr hh)
  · rintro ⟨hf, hmin⟩
    refine ⟨hf, ?_⟩
    -- Move each least-squares competitor into the affine subspace and apply minimality there.
    rw [isMinOn_iff] at hmin
    intro h hh
    exact hmin h ((hmemiff h).mp hh)

/-- Companion form of Definition 2.16 (4) unpacking
`ContinuousLinearMap.isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace`
through `isMinOn_iff`. -/
theorem isLeastSquaresMinimumNormSolution_iff_norm_le_on_affineSubspace
    (K : H₁ →L[𝕜] H₂) (g : H₂) {f_ls f : H₁}
    (hls : K.IsLeastSquaresSolution g f_ls) :
    K.IsLeastSquaresMinimumNormSolution g f ↔
      K.IsLeastSquaresSolution g f ∧
        ∀ h ∈ AffineSubspace.mk' f_ls K.ker, ‖f‖ ≤ ‖h‖ := by
  simpa [isMinOn_iff] using
    K.isLeastSquaresMinimumNormSolution_iff_isMinOn_norm_affineSubspace g hls

end ContinuousLinearMap
