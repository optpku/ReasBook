/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_16.LeastSquares

public section

noncomputable section

universe u v w

open scoped InnerProduct

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}

variable [RCLike 𝕜]
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- A least-squares solution is equivalently characterized by the normal equation
`T† (T f) = T† d`. -/
theorem isLeastSquaresSolution_iff_normalEquation
    (T : H₁ →L[𝕜] H₂) (d : H₂) (f : H₁) :
    T.IsLeastSquaresSolution d f ↔ ((T†) (T f) = (T†) d) := by
  constructor
  · intro hls
    rw [T.isLeastSquaresSolution_iff] at hls
    have hf_range : T f ∈ T.range := ⟨f, rfl⟩
    -- First identify `T f` as a best approximation to `d` inside `T.range`.
    have hbest : ‖d - T f‖ = ⨅ s : T.range, ‖d - s‖ := by
      refine le_antisymm ?_ ?_
      · refine le_ciInf fun s ↦ ?_
        rcases s with ⟨s, ⟨h, rfl⟩⟩
        simpa [norm_sub_rev] using hls h
      · have hbdd : BddBelow (Set.range fun s : T.range ↦ ‖d - s‖) := by
          refine ⟨0, ?_⟩
          rintro _ ⟨s, rfl⟩
          exact norm_nonneg _
        exact ciInf_le hbdd ⟨T f, hf_range⟩
    -- Then rewrite the orthogonality condition of the residual as the normal equation.
    have horth : d - T f ∈ T.rangeᗮ := by
      rw [Submodule.mem_orthogonal']
      intro y hy
      exact ((T.range.norm_eq_iInf_iff_inner_eq_zero hf_range).1 hbest) y hy
    rw [T.orthogonal_range, LinearMap.mem_ker] at horth
    have hsub : (T†) d - (T†) (T f) = 0 := by
      simpa [map_sub] using horth
    exact (sub_eq_zero.mp hsub).symm
  · intro hnormal
    have hf_range : T f ∈ T.range := ⟨f, rfl⟩
    -- Convert the normal equation back to orthogonality of the residual to `T.range`.
    have horth : d - T f ∈ T.rangeᗮ := by
      have hsub : (T†) d - (T†) (T f) = 0 := sub_eq_zero.mpr hnormal.symm
      have hker : (T†) (d - T f) = 0 := by
        simpa [map_sub] using hsub
      rw [T.orthogonal_range, LinearMap.mem_ker]
      exact hker
    have hbest : ‖d - T f‖ = ⨅ s : T.range, ‖d - s‖ := by
      refine (T.range.norm_eq_iInf_iff_inner_eq_zero hf_range).2 ?_
      rw [Submodule.mem_orthogonal'] at horth
      exact horth
    rw [T.isLeastSquaresSolution_iff]
    intro h
    have hbdd : BddBelow (Set.range fun s : T.range ↦ ‖d - s‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact norm_nonneg _
    calc
      ‖T f - d‖ = ‖d - T f‖ := norm_sub_rev _ _
      _ = ⨅ s : T.range, ‖d - s‖ := hbest
      _ ≤ ‖d - T h‖ := ciInf_le hbdd ⟨T h, ⟨h, rfl⟩⟩
      _ = ‖T h - d‖ := norm_sub_rev _ _

/-- Remark 5.34. Minimizing the unregularized least-squares cost functional
`f ↦ ‖T f - d‖ ^ 2` is equivalent to solving the normal equation
`T† (T f) = T† d`. -/
theorem isMinOn_residualNormSq_iff_normalEquation
    (T : H₁ →L[𝕜] H₂) (d : H₂) (f : H₁) :
    IsMinOn (fun h : H₁ ↦ ‖T h - d‖ ^ 2) Set.univ f ↔
      ((T†) (T f) = (T†) d) := by
  exact (T.isMinOn_residualNormSq_iff_isLeastSquaresSolution d f).trans
    (T.isLeastSquaresSolution_iff_normalEquation d f)

end ContinuousLinearMap
