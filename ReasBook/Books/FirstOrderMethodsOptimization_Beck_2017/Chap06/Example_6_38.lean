/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Example_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.EuclideanL1Norm
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped SoftThreshold

noncomputable section

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι
local notation "l1NormFn" => (fun y : E ↦ ‖y‖₁)

/- Example 6.38 is `bridge/view` in the Chapter 6 epigraph-projection domain. The reusable core
owners already live upstream as `euclideanProductPoint`, `euclideanRealEpigraph`,
`epigraph_projection_residual`, and the Euclidean epigraph projection theorem from Theorem 6.36.
This file should therefore keep only the source-facing `ℓ¹` specialization of those owners,
reusing the soft-thresholding singleton from Example 6.8 rather than introducing a second local
Euclidean product model. -/

-- Proof sketch: specialize `euclideanRealEpigraph` to the Euclidean `ℓ¹` norm and evaluate it at
-- the canonical Euclidean product point `(y, t)`.
/-- A Euclidean product point `(y, t)` belongs to the Euclidean `ℓ¹` epigraph exactly when
`‖y‖₁ ≤ t`, specializing to the textbook `ℝ^n × ℝ` model when `ι = Fin n`. -/
@[simp] theorem mem_euclideanRealEpigraph_l1Norm_iff (y : E) (t : ℝ) :
    euclideanProductPoint y t ∈ euclideanRealEpigraph l1NormFn ↔ ‖y‖₁ ≤ t := by
  exact mem_euclideanRealEpigraph_point_iff l1NormFn y t

/-- Helper for Example 6.38: the Euclidean `ℓ¹` norm is convex on the whole finite-dimensional
space. -/
  lemma convexOn_univ_euclidean_l1_norm :
    ConvexOn ℝ Set.univ l1NormFn := by
  let l1Map : E →ₗ[ℝ] WithLp (1 : ENNReal) (ι → ℝ) :=
    ((WithLp.linearEquiv (1 : ENNReal) ℝ (ι → ℝ)).symm.toLinearMap).comp
      ((WithLp.linearEquiv (2 : ENNReal) ℝ (ι → ℝ)).toLinearMap)
  have hconv : ConvexOn ℝ Set.univ (fun y : E ↦ ‖l1Map y‖) := by
    simpa using convexOn_univ_norm.comp_linearMap l1Map
  simpa [EuclideanSpace.l1Norm, l1Map] using hconv

/-- On the nonnegative branch relevant for Example 6.38, the chapter owner
`epigraph_projection_residual` specializes to the textbook scalar residual
`φ(λ) = ‖T_[λ] x‖₁ - λ - s`. -/
theorem epigraph_projection_residual_euclidean_l1_eq
    (x : E) (s lam : ℝ) (hlam : 0 ≤ lam) :
    epigraph_projection_residual l1NormFn x s lam =
      ((‖T_[lam] x‖₁ - lam - s : ℝ) : EReal) := by
  -- Example 6.8 identifies the scaled proximal singleton after normalizing the objective.
  have hprox :
      prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x = {T_[lam] x} := by
    change prox[fun y : E ↦ ((lam * ‖y‖₁ : ℝ) : EReal)] x = {T_[lam] x}
    simpa using prox_euclidean_l1_eq_singleton_softThreshold hlam x
  -- Singleton collapse turns the canonical residual into the displayed scalar formula.
  simpa using
    epigraph_projection_residual_eq_of_scaled_prox_eq_singleton
      l1NormFn x s lam (T_[lam] x) hprox

-- Proof sketch: invoke the public monotonicity theorem for `epigraph_projection_residual` and
-- specialize its convexity hypothesis to `‖·‖₁`.
/-- The canonical epigraph residual for the Euclidean `ℓ¹` norm is nonincreasing on `[0, ∞)`.
Via `epigraph_projection_residual_euclidean_l1_eq`, this is exactly the textbook monotonicity of
`φ(λ) = ‖T_[λ] x‖₁ - λ - s`. -/
theorem epigraph_projection_residual_euclidean_l1_antitoneOn_nonneg
    (x : E) (s : ℝ) :
    AntitoneOn (epigraph_projection_residual l1NormFn x s) (Set.Ici 0) := by
  exact
    epigraph_projection_residual_antitoneOn_nonneg
      l1NormFn convexOn_univ_euclidean_l1_norm x s

-- Proof sketch: apply the Euclidean epigraph projection theorem from Theorem 6.36 to
-- `g = ‖·‖₁`, then collapse the active branch using Example 6.8's singleton proximal formula.
/-- Example 6.38: let
`C = {(y, t) | ‖y‖₁ ≤ t}` be represented by
`euclideanRealEpigraph (fun y : E ↦ ‖y‖₁)` inside `EuclideanSpace ℝ (Option ι)`, specializing to
the textbook `ℝ^n × ℝ` with its Euclidean product norm when `ι = Fin n`. Then the set-valued
orthogonal projection onto `C` is `{(x, s)}` when `‖x‖₁ ≤ s`; otherwise, if `λ` is a positive
root of the canonical residual `epigraph_projection_residual l1NormFn x s`, equivalently of the
nonincreasing function `φ(λ) = ‖T_[λ] x‖₁ - λ - s` by
`epigraph_projection_residual_euclidean_l1_eq`, then the projection is the singleton
`{(T_[λ] x, s + λ)}` in the Euclidean product model. -/
theorem projection_mapping_euclidean_l1Epigraph_eq_singleton_piecewise
    (x : E) (s lam : ℝ)
    (hactive : s < ‖x‖₁ →
      0 < lam ∧ epigraph_projection_residual l1NormFn x s lam = 0) :
    P[euclideanRealEpigraph l1NormFn] (euclideanProductPoint x s) =
      if hfeas : ‖x‖₁ ≤ s then
        {euclideanProductPoint x s}
      else
        {euclideanProductPoint (T_[lam] x) (s + lam)} := by
  by_cases hfeas : ‖x‖₁ ≤ s
  · -- On the feasible branch, Theorem 6.36 already returns the singleton `{(x, s)}`.
    have hpiece :=
      projection_mapping_realEpigraph_eq_piecewise_lifted_scaled_prox
        l1NormFn convexOn_univ_euclidean_l1_norm x s lam hactive
    have hfeas' : ∑ i, |x.ofLp i| ≤ s := by
      simpa using hfeas
    have hpiece' :
        P[euclideanRealEpigraph l1NormFn] (euclideanProductPoint x s) =
          {euclideanProductPoint x s} := by
      simpa [hfeas'] using hpiece
    rw [dif_pos hfeas]
    exact hpiece'
  · have hsx : s < ‖x‖₁ := lt_of_not_ge hfeas
    rcases hactive hsx with ⟨hlam_pos, _hres⟩
    have hlam_nonneg : 0 ≤ lam := le_of_lt hlam_pos
    -- Collapse the lifted proximal image using the soft-threshold singleton from Example 6.8.
    have hlift :
        (fun y : E ↦ euclideanProductPoint y (s + lam)) ''
            prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x =
          {euclideanProductPoint (T_[lam] x) (s + lam)} := by
      have hprox :
          prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x = {T_[lam] x} := by
        change prox[fun y : E ↦ ((lam * ‖y‖₁ : ℝ) : EReal)] x = {T_[lam] x}
        simpa using prox_euclidean_l1_eq_singleton_softThreshold hlam_nonneg x
      rw [hprox, Set.image_singleton]
    have hpiece :=
      projection_mapping_realEpigraph_eq_piecewise_lifted_scaled_prox
        l1NormFn convexOn_univ_euclidean_l1_norm x s lam hactive
    have hfeas' : ¬ ∑ i, |x.ofLp i| ≤ s := by
      simpa using hfeas
    have hpiece' :
        P[euclideanRealEpigraph l1NormFn] (euclideanProductPoint x s) =
          (fun y : E ↦ euclideanProductPoint y (s + lam)) ''
            prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x := by
      simpa [hfeas'] using hpiece
    -- The infeasible branch of Theorem 6.36 is exactly the lifted scaled proximal formula.
    calc
      P[euclideanRealEpigraph l1NormFn] (euclideanProductPoint x s) =
          (fun y : E ↦ euclideanProductPoint y (s + lam)) ''
            prox[fun y : E ↦ (lam : EReal) * (l1NormFn y : EReal)] x := hpiece'
      _ = {euclideanProductPoint (T_[lam] x) (s + lam)} := hlift
      _ =
          if hfeas : ‖x‖₁ ≤ s then
            {euclideanProductPoint x s}
          else
            {euclideanProductPoint (T_[lam] x) (s + lam)} := by
        rw [dif_neg hfeas]

end
