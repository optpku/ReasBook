/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Lemma_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_10
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9

-- Declarations for this item will be appended below by the statement pipeline.

open Metric
open Matrix
open WithLp (toLp)

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: maximize the continuous linear functional `y` on the compact closed unit ball.
-- The dual-pairing inequality gives the upper bound `support_function ≤ dualNorm`, while the
-- maximizing point gives the reverse inequality.
/-- Example 2.9 (1): the support function of the closed unit ball of a normed space is the dual
norm. -/
theorem support_function_unit_ball_eq_dualNorm (y : Module.Dual ℝ E) :
    support_function (closedBall (0 : E) 1) y = (dualNorm y : EReal) := by
  let f : E →L[ℝ] ℝ := y.toContinuousLinearMap
  have hcompact : IsCompact (closedBall (0 : E) 1) := isCompact_closedBall (0 : E) 1
  have hnonempty : (closedBall (0 : E) 1).Nonempty := nonempty_closedBall.2 zero_le_one
  obtain ⟨x, hx_mem, hx_max⟩ := hcompact.exists_isMaxOn hnonempty f.continuous.continuousOn
  have hdual_nonneg : 0 ≤ dualNorm y := by
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact norm_nonneg y.toContinuousLinearMap
  have hyx_nonneg : 0 ≤ y x := by
    simpa [f] using hx_max (by simp : (0 : E) ∈ closedBall (0 : E) 1)
  have hdual_le : dualNorm y ≤ y x := by
    change ‖y‖ ≤ y x
    refine (ContinuousLinearMap.opNorm_le_iff hyx_nonneg).2 fun z ↦ ?_
    by_cases hz : z = 0
    · simp [hz]
    · let u : E := ‖z‖⁻¹ • z
      have hu_mem : u ∈ closedBall (0 : E) 1 := by
        refine mem_closedBall_zero_iff.mpr ?_
        dsimp [u]
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      have hneg_u_mem : -u ∈ closedBall (0 : E) 1 := by
        refine mem_closedBall_zero_iff.mpr ?_
        simpa using (mem_closedBall_zero_iff.mp hu_mem)
      have hu_le : y u ≤ y x := by
        simpa [f] using hx_max hu_mem
      have hneg_u_le : y (-u) ≤ y x := by
        simpa [f] using hx_max hneg_u_mem
      have hu_abs_le : |y u| ≤ y x := by
        refine abs_le.2 ⟨?_, hu_le⟩
        have hneg : -(y u) ≤ y x := by
          simpa using hneg_u_le
        simpa using neg_le_neg hneg
      have hz_decomp : ‖z‖ • u = z := by
        dsimp [u]
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]
      calc
        ‖y z‖ = ‖y (‖z‖ • u)‖ := by rw [hz_decomp]
        _ = ‖‖z‖ • y u‖ := by rw [map_smul]
        _ = ‖z‖ * ‖y u‖ := by simp
        _ ≤ ‖z‖ * y x := by
          gcongr
          simpa [Real.norm_eq_abs] using hu_abs_le
        _ = y x * ‖z‖ := by ring
  have hyx_le : y x ≤ dualNorm y := by
    calc
      y x ≤ |y x| := le_abs_self _
      _ ≤ dualNorm y * ‖x‖ := abs_apply_le_dual_norm_mul_norm y x
      _ ≤ dualNorm y := by
        simpa [mul_one] using
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx_mem) hdual_nonneg
  rw [support_function_apply]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro z ⟨z, hz_mem, rfl⟩
    change (y z : EReal) ≤ (dualNorm y : EReal)
    exact_mod_cast
      calc
        y z ≤ |y z| := le_abs_self _
        _ ≤ dualNorm y * ‖z‖ := abs_apply_le_dual_norm_mul_norm y z
        _ ≤ dualNorm y := by
          simpa [mul_one] using
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hz_mem) hdual_nonneg
  · calc
      (dualNorm y : EReal) = (y x : EReal) := by
        exact_mod_cast (le_antisymm hyx_le hdual_le).symm
      _ ≤ sSup ((fun z : E ↦ (y z : EReal)) '' closedBall (0 : E) 1) := by
        exact le_sSup ⟨x, hx_mem, rfl⟩

end

section

variable {n : ℕ} {p q : ENNReal}

-- Proof sketch: rewrite `support_function` by its defining `sSup` formula, identify the result
-- with the canonical `conjExponent` owner formula, and then rewrite the exponent using `hpq`.
/-- Example 2.9 (2): in `ℝ^n` with the `l_p` norm, the support function of the closed unit ball is
the conjugate `l_q` norm. -/
theorem support_function_lp_unit_ball_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : Fin n → ℝ) :
    support_function {x : Fin n → ℝ | ‖toLp p x‖ ≤ 1} (dotProductBilin ℝ ℝ y) =
      (‖toLp q y‖ : EReal) := by
  let hp : 1 ≤ p := by
    letI : ENNReal.HolderConjugate p q := hpq
    simpa using ENNReal.HolderConjugate.one_le p q
  letI : Fact (1 ≤ p) := ⟨hp⟩
  rw [support_function_apply]
  let S : Set (Fin n → ℝ) := {x : Fin n → ℝ | ‖toLp p x‖ ≤ 1}
  let T : Set ℝ := (fun x : Fin n → ℝ ↦ dotProduct x y) '' S
  have hq : ENNReal.conjExponent p = q := by
    letI : ENNReal.HolderConjugate p q := hpq
    exact ENNReal.HolderConjugate.conjExponent_eq
  have hS_nonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    simp [S]
  have hS_eq :
      S = WithLp.ofLp '' closedBall (0 : WithLp p (Fin n → ℝ)) 1 := by
    ext x
    constructor
    · intro hx
      refine ⟨toLp p x, ?_, rfl⟩
      exact mem_closedBall_zero_iff.mpr hx
    · rintro ⟨x, hx, rfl⟩
      simpa [S] using (mem_closedBall_zero_iff.mp hx)
  have hS_compact : IsCompact S := by
    rw [hS_eq]
    exact (isCompact_closedBall (0 : WithLp p (Fin n → ℝ)) 1).image
      (PiLp.continuous_ofLp (p := p) (β := fun _ : Fin n ↦ ℝ))
  have hT_bdd : BddAbove T := by
    exact hS_compact.bddAbove_image
      (by
        simpa [dotProduct_comm] using
          (((dotProductBilin ℝ ℝ y).toContinuousLinearMap.continuous).continuousOn :
            ContinuousOn (fun x : Fin n → ℝ ↦ ((dotProductBilin ℝ ℝ y) x : ℝ)) S))
  have himage :
      ((fun x : Fin n → ℝ ↦ ((((dotProductBilin ℝ ℝ) y) x : ℝ) : EReal)) '' S) =
        ((fun x : Fin n → ℝ ↦ ((dotProduct x y : ℝ) : EReal)) '' S) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [dotProduct_comm]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [dotProduct_comm]
  rw [himage]
  let f : S → ℝ := fun x ↦ dotProduct x.1 y
  have hT_range : Set.range f = T := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rcases hS_nonempty with ⟨x0, hx0⟩
  letI : Nonempty S := ⟨⟨x0, hx0⟩⟩
  have hsup_coe_top :
      (⨆ x : S, ((f x : ℝ) : WithTop ℝ)) = ((⨆ x : S, f x : ℝ) : WithTop ℝ) := by
    symm
    exact WithTop.coe_iSup (f := f) (by simpa [hT_range] using hT_bdd)
  have hsup_coe :
      (⨆ x : S, ((f x : ℝ) : EReal)) = ((⨆ x : S, f x : ℝ) : EReal) := by
    change (⨆ x : S, ((f x : ℝ) : WithBot (WithTop ℝ))) =
      ((⨆ x : S, f x : ℝ) : WithBot (WithTop ℝ))
    simpa using
      ((WithBot.coe_iSup (f := fun x : S ↦ ((f x : ℝ) : WithTop ℝ))
          (OrderTop.bddAbove _)).symm.trans
        (congrArg (fun t : WithTop ℝ ↦ (t : WithBot (WithTop ℝ))) hsup_coe_top))
  calc
    sSup ((fun x : Fin n → ℝ ↦ ((dotProduct x y : ℝ) : EReal)) '' S) =
        (⨆ x : S, ((f x : ℝ) : EReal)) := by
          rw [sSup_image']
    _ = ((⨆ x : S, f x : ℝ) : EReal) := hsup_coe
    _ = ((sSup T : ℝ) : EReal) := by
          congr 1
          symm
          simpa [T, f] using
            (sSup_image' (s := S) (f := fun x : Fin n → ℝ ↦ dotProduct x y))
    _ = (‖toLp (ENNReal.conjExponent p) y‖ : EReal) := by
          exact_mod_cast unit_lp_pairing_sSup_eq_conjExponent_lp_norm (p := p) y
    _ = (‖toLp q y‖ : EReal) := by rw [hq]

-- Proof sketch: rewrite the `Q`-unit ball using the source-facing owner `Q.qNorm hQ`, apply the
-- unit-ball support-function formula from part (1) in the induced `Q`-geometry, and then identify
-- the resulting owner dual norm using `dual_qNorm_eq_sqrt_dotProduct_inv_mulVec`.
/-- Example 2.9 (3): for the norm induced by a positive definite matrix `Q`, the support function
of the closed unit ball is the `Q⁻¹`-norm, written here as `√(yᵀ Q⁻¹ y)`. -/
theorem support_function_posDef_unit_ball_eq_sqrt_dotProduct_inv_mulVec
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) (y : Fin n → ℝ) :
    support_function {x : Fin n → ℝ | Q.qNorm hQ x ≤ 1} (dotProductBilin ℝ ℝ y) =
      (Real.sqrt (dotProduct y (Q⁻¹.mulVec y)) : EReal) := by
  let qSeminormed : SeminormedAddCommGroup (Fin n → ℝ) := Q.toSeminormedAddCommGroup hQ.posSemidef
  letI := qSeminormed
  let qNormed : NormedAddCommGroup (Fin n → ℝ) := Q.toNormedAddCommGroup hQ
  letI := qNormed
  letI : PseudoMetricSpace (Fin n → ℝ) := qNormed.toSeminormedAddCommGroup.toPseudoMetricSpace
  letI : Norm (Fin n → ℝ) := qNormed.toNorm
  letI : InnerProductSpace ℝ (Fin n → ℝ) := Q.toInnerProductSpace hQ.posSemidef
  have hunitBall : (closedBall (0 : Fin n → ℝ) 1) = {x : Fin n → ℝ | ‖x‖ ≤ 1} := by
    ext x
    simp [dist_eq_norm]
  have hqBall :
      {x : Fin n → ℝ | Q.qNorm hQ x ≤ 1} = {x : Fin n → ℝ | ‖x‖ ≤ 1} := by
    ext x
    simp [Matrix.qNorm]
  calc
    support_function {x : Fin n → ℝ | Q.qNorm hQ x ≤ 1} (dotProductBilin ℝ ℝ y) =
        support_function {x : Fin n → ℝ | ‖x‖ ≤ 1} (dotProductBilin ℝ ℝ y) := by
      rw [hqBall]
    _ = support_function (closedBall (0 : Fin n → ℝ) 1) (dotProductBilin ℝ ℝ y) := by
      rw [hunitBall]
    _ =
        (dualNorm (dotProductBilin ℝ ℝ y) : EReal) := by
      simpa using
        support_function_unit_ball_eq_dualNorm (dotProductBilin ℝ ℝ y)
    _ = (Real.sqrt (dotProduct y (Q⁻¹.mulVec y)) : EReal) := by
      exact_mod_cast dual_qNorm_eq_sqrt_dotProduct_inv_mulVec Q hQ y

end
