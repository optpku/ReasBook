/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProduct InnerProductSpace

universe u v

open ContinuousLinearMap

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Fact 2.25: on real Hilbert spaces, the adjoint operation is involutive. -/
#check ContinuousLinearMap.adjoint_adjoint

/- Fact 2.25: the orthogonal complement of `ker T` is the closure of `range T†`. -/
#check ContinuousLinearMap.orthogonal_ker

/- Fact 2.25: the orthogonal complement of `range T` is `ker T†`. -/
#check ContinuousLinearMap.orthogonal_range

/- Fact 2.25: `ker (T† ∘L T)` agrees with `ker T`. -/
#check ContinuousLinearMap.ker_adjoint_comp_self

namespace ContinuousLinearMap

/-- Fact 2.25: taking adjoints preserves the operator norm. -/
theorem norm_adjoint_eq (T : H →L[ℝ] K) :
    ‖T†‖ = ‖T‖ := by
  exact LinearIsometryEquiv.norm_map adjoint T

/-- Fact 2.25: the operator norm is the square root of the norm of the Gram operator `T†T`. -/
theorem norm_eq_sqrt_norm_adjoint_comp (T : H →L[ℝ] K) :
    ‖T‖ = Real.sqrt ‖T† ∘L T‖ := by
  calc
    ‖T‖ = Real.sqrt (‖T‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt ‖T† ∘L T‖ := by rw [sq, T.norm_adjoint_comp_self]

/-- Fact 2.25: the closures of the ranges of `TT†` and `T` coincide. -/
theorem closure_range_self_comp_adjoint (T : H →L[ℝ] K) :
    (T ∘L T†).range.topologicalClosure = T.range.topologicalClosure := by
  calc
    (T ∘L T†).range.topologicalClosure = ((T ∘L T†).rangeᗮ)ᗮ := by
      rw [Submodule.orthogonal_orthogonal_eq_closure]
    _ = ((T ∘L T†)†.ker)ᗮ := by rw [(T ∘L T†).orthogonal_range]
    _ = ((T ∘L T†).ker)ᗮ := by rw [adjoint_comp, adjoint_adjoint]
    _ = (T†.ker)ᗮ := by rw [T.ker_self_comp_adjoint]
    _ = T.range.topologicalClosure := by
      rw [T†.orthogonal_ker, adjoint_adjoint]

/-- Fact 2.25: in the Hilbert direct sum `H ⊕ K`, the orthogonal complement of the graph of `T`
is the kernel of the canonical graph map `fst + T† ∘ snd`. -/
theorem orthogonal_hilbertGraph (T : H →L[ℝ] K) :
    (T.toLinearMap.graph.map (WithLp.linearEquiv 2 ℝ (H × K)).symm.toLinearMap)ᗮ =
      (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K).ker := by
  ext z
  constructor
  · intro hz
    change (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K) z = 0
    apply ext_inner_right ℝ
    intro x
    have hz' := (Submodule.mem_orthogonal' _ _).mp hz (WithLp.toLp 2 (x, T x))
    have hgraph : WithLp.toLp 2 (x, T x) ∈
        T.toLinearMap.graph.map (WithLp.linearEquiv 2 ℝ (H × K)).symm.toLinearMap := by
      refine Submodule.mem_map.2 ?_
      exact ⟨(x, T x), by simp, rfl⟩
    simpa [WithLp.prod_inner_apply, inner_add_left, T.adjoint_inner_left] using hz' hgraph
  · intro hz
    change (WithLp.fstL 2 ℝ H K + T† ∘L WithLp.sndL 2 ℝ H K) z = 0 at hz
    rw [Submodule.mem_orthogonal']
    intro z hz'
    rcases Submodule.mem_map.1 hz' with ⟨w, hw, rfl⟩
    rw [LinearMap.mem_graph_iff] at hw
    rcases w with ⟨x, y⟩
    have hy : y = T x := by simpa using hw
    have hz0 := congrArg (fun v : H ↦ ⟪v, x⟫_ℝ) hz
    simpa [hy, WithLp.prod_inner_apply, inner_add_left, T.adjoint_inner_left] using hz0

end ContinuousLinearMap

namespace IsSelfAdjoint

/-- For a self-adjoint operator, the norm is the supremum of the quadratic form on the unit ball. -/
theorem norm_eq_sSup_abs_inner_closedBall {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    ‖T‖ = sSup ((fun x : H ↦ |⟪T x, x⟫_ℝ|) '' Metric.closedBall (0 : H) 1) := by
  let s : Set ℝ := (fun x : H ↦ |⟪T x, x⟫_ℝ|) '' Metric.closedBall (0 : H) 1
  have hs_bound : ∀ r ∈ s, r ≤ ‖T‖ := by
    rintro _ ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hx_sq : ‖x‖ * ‖x‖ ≤ 1 := by
      nlinarith [norm_nonneg x, hx_norm]
    calc
      |⟪T x, x⟫_ℝ| ≤ ‖T x‖ * ‖x‖ := by
        simpa [Real.norm_eq_abs] using (norm_inner_le_norm (T x) x : ‖⟪T x, x⟫_ℝ‖ ≤ ‖T x‖ * ‖x‖)
      _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by gcongr; exact le_opNorm T x
      _ = ‖T‖ * (‖x‖ * ‖x‖) := by ring
      _ ≤ ‖T‖ * 1 := by gcongr
      _ = ‖T‖ := by ring
  have hs_bdd : BddAbove s := ⟨‖T‖, hs_bound⟩
  have hs_nonempty : s.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨0, by simp, by simp⟩
  refine le_antisymm ?_ ?_
  · change ‖T‖ ≤ sSup s
    exact (Real.le_sSup_iff hs_bdd hs_nonempty).2 fun ε hε ↦ by
      have hlt : ‖T‖ + ε < ⨆ x, |T.rayleighQuotient x| := by
        simpa [T.norm_eq_iSup_rayleighQuotient hT.isSymmetric] using add_lt_add_left hε ‖T‖
      have hlt' : ‖T‖ + ε < sSup (Set.range fun x : H ↦ |T.rayleighQuotient x|) := by
        simpa [sSup_image'] using hlt
      have hs_range_nonempty : (Set.range fun x : H ↦ |T.rayleighQuotient x|).Nonempty := by
        exact ⟨0, ⟨0, by simp⟩⟩
      obtain ⟨r, hr, hrlt⟩ := exists_lt_of_lt_csSup hs_range_nonempty hlt'
      rcases hr with ⟨x, rfl⟩
      by_cases hx : x = 0
      · refine ⟨0, ?_, ?_⟩
        · exact ⟨0, by simp, by simp⟩
        · simpa [hx] using hrlt
      · let y : H := ‖x‖⁻¹ • x
        have hx_norm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        have hy_norm : ‖y‖ = 1 := by
          calc
            ‖y‖ = ‖x‖⁻¹ * ‖x‖ := by
              simp [y, norm_smul]
            _ = 1 := by field_simp [hx_norm]
        have hy_sphere : y ∈ Metric.sphere (0 : H) 1 := by
          simpa [Metric.mem_sphere, dist_eq_norm] using hy_norm
        have hy_mem : |⟪T y, y⟫_ℝ| ∈ s := by
          refine ⟨y, Metric.sphere_subset_closedBall hy_sphere, rfl⟩
        have hy_rq : T.rayleighQuotient y = ⟪T y, y⟫_ℝ := by
          calc
            T.rayleighQuotient y = T.reApplyInnerSelf y / ‖y‖ ^ 2 := rfl
            _ = T.reApplyInnerSelf y := by simp [hy_norm]
            _ = ⟪T y, y⟫_ℝ := by simpa using hT.isSymmetric.coe_reApplyInnerSelf_apply y
        refine ⟨|⟪T y, y⟫_ℝ|, hy_mem, ?_⟩
        calc
          ‖T‖ + ε < |T.rayleighQuotient x| := hrlt
          _ = |T.rayleighQuotient y| := by
            simpa [y] using congrArg abs (T.rayleigh_smul x (inv_ne_zero hx_norm)).symm
          _ = |⟪T y, y⟫_ℝ| := by rw [hy_rq]
  · change sSup s ≤ ‖T‖
    exact csSup_le hs_nonempty fun r hr ↦ by
      exact hs_bound r hr

end IsSelfAdjoint
