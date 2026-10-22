/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_3_2

open Matrix

noncomputable section

-- Domain-style sampling for this file:
-- * primary domain: equality-constrained quadratic forms and positive-definite penalty shifts.
-- * core/canonical owners inspected: `Matrix.PosDef`,
--   `Matrix.PosDef.of_dotProduct_mulVec_pos`, and `Matrix.posDef_iff_dotProduct_mulVec`.
-- * project owner inspected for the null-space layer: Chapter 9 `IsReducedNullMatrix`, which
--   packages the source condition that a matrix `Z` parametrizes `ker Aᵀ`.
-- * layer triage:
--   - source-facing: positivity of the quadratic form `d ↦ dotProduct d (H.mulVec d)` on
--     `ker Aᵀ`, and the conclusion that a penalty shift `H + σ A Aᵀ` is positive definite.
--   - core/canonical: `Matrix.PosDef`.
--   - bridge/view: the reduced-null-space basis API `IsReducedNullMatrix`.
-- * primitive data vs derived API: the primitive data here are only `H`, `A`, symmetry of `H`,
--   and positivity on `ker Aᵀ`; the reduced-null-space formulation is derived bridge API.

variable {n m : ℕ}

section

local notation "Point" => Fin n → ℝ
local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ

/-- Helper for Chapter10 Lemma 10.1.1: expanding the penalty-shifted quadratic form rewrites the
penalty term as the self-dot-product of the constraint residual `Aᵀ d`. -/
lemma penaltyShiftQuadratic_apply
    (H : HessianMatrix) (A : ConstraintMatrix) (σ : ℝ) (d : Point) :
    dotProduct d ((H + σ • (A * Aᵀ)).mulVec d) =
      dotProduct d (H.mulVec d) + σ * dotProduct (Aᵀ.mulVec d) (Aᵀ.mulVec d) := by
  have hPenalty :
      dotProduct d ((A * Aᵀ).mulVec d) = dotProduct (Aᵀ.mulVec d) (Aᵀ.mulVec d) := by
    have htranspose : d ᵥ* A = Aᵀ.mulVec d := by
      simpa using Matrix.vecMul_transpose Aᵀ d
    calc
      dotProduct d ((A * Aᵀ).mulVec d) = dotProduct d (A.mulVec (Aᵀ.mulVec d)) := by
          simp [Matrix.mulVec_mulVec]
      _ = dotProduct (d ᵥ* A) (Aᵀ.mulVec d) := by
          rw [Matrix.dotProduct_mulVec]
      _ = dotProduct (Aᵀ.mulVec d) (Aᵀ.mulVec d) := by
          rw [htranspose]
  -- Expand the penalty shift once and isolate the quadratic contribution of `A Aᵀ`.
  calc
    dotProduct d ((H + σ • (A * Aᵀ)).mulVec d)
      = dotProduct d (H.mulVec d) + σ * dotProduct d ((A * Aᵀ).mulVec d) := by
          rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
          simp [smul_eq_mul]
    _ = dotProduct d (H.mulVec d) + σ * dotProduct (Aᵀ.mulVec d) (Aᵀ.mulVec d) := by
          rw [hPenalty]

/-- Helper for Chapter10 Lemma 10.1.1: on the unit sphere, a sufficiently large nonnegative
penalty shift makes the quadratic form strictly positive. -/
lemma exists_nonneg_penalty_strictPos_on_unitSphere
    (H : HessianMatrix) (A : ConstraintMatrix)
    (hpos : ∀ d : Point, d ≠ 0 → Aᵀ.mulVec d = 0 → 0 < dotProduct d (H.mulVec d))
    [Nontrivial Point] :
    ∃ σ : ℝ, 0 ≤ σ ∧
      ∀ d : Point, ‖d‖ = 1 → 0 < dotProduct d ((H + σ • (A * Aᵀ)).mulVec d) := by
  classical
  let q : Point → ℝ := fun d ↦ dotProduct d (H.mulVec d)
  let p : Point → ℝ := fun d ↦ dotProduct (Aᵀ.mulVec d) (Aᵀ.mulVec d)
  let K : Set Point := Metric.sphere (0 : Point) 1 ∩ { d : Point | q d ≤ 0 }
  have hq_cont : Continuous q := by
    -- The source quadratic form is continuous on the finite-dimensional ambient space.
    fun_prop
  have hp_cont : Continuous p := by
    -- The penalty term is continuous because it is a quadratic polynomial in `d`.
    fun_prop
  have hsphere_compact : IsCompact (Metric.sphere (0 : Point) 1) := isCompact_sphere _ _
  have hsphere_nonempty : (Metric.sphere (0 : Point) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_rfl, ?_⟩
    intro d hd_norm
    have hd_sphere : d ∈ Metric.sphere (0 : Point) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_norm
    have hq_pos : 0 < q d := by
      by_contra hq_nonpos
      have hk : d ∈ K := ⟨hd_sphere, le_of_not_gt hq_nonpos⟩
      have hK_not_nonempty : ¬ K.Nonempty := by simpa [hK_empty]
      exact hK_not_nonempty ⟨d, hk⟩
    -- If the bad set is empty, the unshifted quadratic form is already positive on the sphere.
    simpa [q, penaltyShiftQuadratic_apply] using hq_pos
  · have hK_compact : IsCompact K := by
      -- The bad set is the compact sphere intersected with a closed sublevel set of `q`.
      dsimp [K]
      exact hsphere_compact.inter_right (isClosed_le hq_cont continuous_const)
    have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    obtain ⟨d0, hd0K, hd0min⟩ := hK_compact.exists_isMinOn hK_nonempty hp_cont.continuousOn
    have hd0_norm : ‖d0‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd0K.1
    have hd0_ne : d0 ≠ 0 := by
      intro hd0_zero
      have : ‖d0‖ = 0 := by simpa [hd0_zero]
      linarith
    have hp_d0_ne : p d0 ≠ 0 := by
      intro hp_zero
      have hd0_ker : Aᵀ.mulVec d0 = 0 := by
        exact dotProduct_self_eq_zero.mp (by simpa [p] using hp_zero)
      have hq_d0_pos : 0 < q d0 := hpos d0 hd0_ne hd0_ker
      have hd0q_nonpos : q d0 ≤ 0 := hd0K.2
      exact (not_lt_of_ge hd0q_nonpos) hq_d0_pos
    let δ : ℝ := p d0
    have hδ_nonneg : 0 ≤ δ := by
      dsimp [δ, p, dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hp_d0_ne)
    obtain ⟨d1, hd1sphere, hd1min⟩ :=
      hsphere_compact.exists_isMinOn hsphere_nonempty hq_cont.continuousOn
    let m : ℝ := q d1
    have hm_nonpos : m ≤ 0 := by
      have hm_le_d0 : m ≤ q d0 := hd1min hd0K.1
      exact le_trans hm_le_d0 hd0K.2
    let σ : ℝ := (1 - m) / δ
    have hσ_nonneg : 0 ≤ σ := by
      -- The sphere minimum of `q` over `K` lies below zero, so the chosen penalty is nonnegative.
      dsimp [σ]
      apply div_nonneg
      linarith
      exact hδ_nonneg
    refine ⟨σ, hσ_nonneg, ?_⟩
    intro d hd_norm
    have hd_sphere : d ∈ Metric.sphere (0 : Point) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_norm
    by_cases hqd : q d ≤ 0
    · have hδ_le : δ ≤ p d := hd0min ⟨hd_sphere, hqd⟩
      have hm_le_d : m ≤ q d := hd1min hd_sphere
      have hσ_mul_eq : σ * δ = 1 - m := by
        have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
        calc
          σ * δ = ((1 - m) / δ) * δ := by rfl
          _ = 1 - m := by field_simp [hδ_ne]
      have hσ_mul_le : σ * δ ≤ σ * p d := mul_le_mul_of_nonneg_left hδ_le hσ_nonneg
      have hbound : 1 ≤ q d + σ * p d := by
        calc
          1 = m + σ * δ := by
            linarith [hσ_mul_eq]
          _ ≤ q d + σ * p d := by
            linarith [hm_le_d, hσ_mul_le]
      -- On the bad set, the penalty term is bounded below by a positive compactness gap.
      have hpenalty : 1 ≤ dotProduct d ((H + σ • (A * Aᵀ)).mulVec d) := by
        simpa [q, p, penaltyShiftQuadratic_apply] using hbound
      linarith
    · have hq_pos : 0 < q d := lt_of_not_ge hqd
      have hp_nonneg : 0 ≤ p d := by
        dsimp [p, dotProduct]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hextra_nonneg : 0 ≤ σ * p d := mul_nonneg hσ_nonneg hp_nonneg
      have hpenalty : 0 < q d + σ * p d := by
        linarith
      -- Outside the bad set, the source quadratic form is already strictly positive.
      simpa [q, p, penaltyShiftQuadratic_apply] using hpenalty

/-- Chapter10 Lemma 10.1.1: let `H ∈ ℝ^(n × n)` be symmetric and `A ∈ ℝ^(n × m)`. If
`dotProduct d (H.mulVec d) > 0` for every nonzero `d` with `A.transpose.mulVec d = 0`, then
there exists `σ ≥ 0` such that `H + σ A Aᵀ` is positive definite. -/
theorem exists_nonneg_penalty_posDef_of_posOn_transposeKer
    (H : HessianMatrix) (A : ConstraintMatrix)
    (hHsymm : H.IsSymm)
    (hpos : ∀ d : Point, d ≠ 0 → Aᵀ.mulVec d = 0 → 0 < dotProduct d (H.mulVec d)) :
    ∃ σ : ℝ, 0 ≤ σ ∧ (H + σ • (A * Aᵀ)).PosDef := by
  classical
  rcases subsingleton_or_nontrivial Point with hPoint | hPoint
  · refine ⟨0, le_rfl, ?_⟩
    -- In the degenerate zero-dimensional case, every nonzero-vector obligation is vacuous.
    have hPos : H.PosDef :=
      Matrix.PosDef.of_dotProduct_mulVec_pos ((Matrix.isHermitian_iff_isSymm).2 hHsymm)
        (fun x hx ↦ False.elim (hx (hPoint.elim x 0)))
    simpa using hPos
  · letI : Nontrivial Point := hPoint
    obtain ⟨σ, hσ_nonneg, hSpherePos⟩ :=
      exists_nonneg_penalty_strictPos_on_unitSphere H A hpos
    refine ⟨σ, hσ_nonneg, Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_⟩
    · have hAAT_symm : (A * Aᵀ).IsSymm := by
        simpa [Matrix.IsSymm, Matrix.transpose_mul]
      -- The penalty shift preserves symmetry because `A Aᵀ` is symmetric.
      exact (Matrix.isHermitian_iff_isSymm).2 <| hHsymm.add (hAAT_symm.smul σ)
    · intro x hx
      let M : HessianMatrix := H + σ • (A * Aᵀ)
      let u : Point := ‖x‖⁻¹ • x
      have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hx_eq : ‖x‖ • u = x := by
        -- Recover the original vector from its normalized direction.
        simp [u, hx_norm_pos.ne', smul_smul]
      have hu_norm : ‖u‖ = 1 := by
        -- Normalizing a nonzero vector lands on the unit sphere.
        simp [u, norm_smul, hx_norm_pos.ne']
      have hu_pos : 0 < dotProduct u (M.mulVec u) := by
        simpa [M] using hSpherePos u hu_norm
      have hscale :
          dotProduct (‖x‖ • u) (M.mulVec (‖x‖ • u)) =
            ‖x‖ ^ (2 : ℕ) * dotProduct u (M.mulVec u) := by
        -- Separate the radial factor from the unit-sphere direction.
        rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
        ring
      have hscaled_pos : 0 < dotProduct (‖x‖ • u) (M.mulVec (‖x‖ • u)) := by
        have hnorm_sq_pos : 0 < ‖x‖ ^ (2 : ℕ) := by
          positivity
        have hprod_pos : 0 < ‖x‖ ^ (2 : ℕ) * dotProduct u (M.mulVec u) :=
          mul_pos hnorm_sq_pos hu_pos
        simpa [hscale] using hprod_pos
      -- Homogeneity transfers the unit-sphere positivity back to the original nonzero vector.
      simpa [M, hx_eq] using hscaled_pos

/-- Bridge to the Chapter 9 reduced-null-space owner: if `Z` parametrizes `ker Aᵀ` and the
reduced Hessian `Zᵀ H Z` is positive definite, then the source quadratic form is positive on
`ker Aᵀ`. -/
theorem posOn_transposeKer_of_reducedHessian_posDef
    {k : ℕ}
    (H : HessianMatrix) (A : ConstraintMatrix) (Z : Matrix (Fin n) (Fin k) ℝ)
    (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Zᵀ * H * Z).PosDef) :
    ∀ d : Point, d ≠ 0 → Aᵀ.mulVec d = 0 → 0 < dotProduct d (H.mulVec d) := by
  intro d hd hker
  obtain ⟨u, hu⟩ := hZ.eq_mulVec d hker
  have hu_ne : u ≠ 0 := by
    -- A zero reduced coordinate vector would force the original kernel vector to vanish.
    intro hu_zero
    apply hd
    simpa [hu_zero] using hu.symm
  have htransport :
      dotProduct u (((Zᵀ * H * Z).mulVec u)) = dotProduct d (H.mulVec d) := by
    calc
      dotProduct u (((Zᵀ * H * Z).mulVec u))
          = dotProduct u (Zᵀ.mulVec (H.mulVec (Z.mulVec u))) := by
              simp [Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = dotProduct (Z.mulVec u) (H.mulVec (Z.mulVec u)) := by
              rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = dotProduct d (H.mulVec d) := by
              simpa [hu]
  -- Transport the quadratic form to the reduced coordinates, where positivity is available.
  have hReducedPos : 0 < dotProduct u (((Zᵀ * H * Z).mulVec u)) :=
    hReduced.dotProduct_mulVec_pos hu_ne
  simpa [htransport] using hReducedPos

/-- Under the stronger Chapter 9 reduced-null-space hypothesis that some `Z` parametrizes
`ker Aᵀ` with positive-definite reduced Hessian `Zᵀ H Z`, Lemma 10.1.1 applies directly. -/
theorem exists_nonneg_penalty_posDef_of_reducedHessian_posDef
    {k : ℕ}
    (H : HessianMatrix) (A : ConstraintMatrix) (Z : Matrix (Fin n) (Fin k) ℝ)
    (hHsymm : H.IsSymm)
    (hZ : IsReducedNullMatrix A Z)
    (hReduced : (Zᵀ * H * Z).PosDef) :
    ∃ σ : ℝ, 0 ≤ σ ∧ (H + σ • (A * Aᵀ)).PosDef :=
  exists_nonneg_penalty_posDef_of_posOn_transposeKer H A hHsymm
    (posOn_transposeKer_of_reducedHessian_posDef H A Z hZ hReduced)

end
