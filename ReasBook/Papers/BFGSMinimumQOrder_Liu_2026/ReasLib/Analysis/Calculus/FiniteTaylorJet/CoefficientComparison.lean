module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet
public import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped Topology

universe u

namespace FiniteTaylorJet

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed vector multiplied by a strictly higher scalar power is little-o of
the lower scalar power at zero. -/
private lemma pow_smul_isLittleO_pow {n k : ℕ} (hnk : n < k) (a : F) :
    (fun h : ℝ ↦ h ^ k • a) =o[𝓝 0] fun h : ℝ ↦ h ^ n := by
  -- First bound the vector-valued monomial by its scalar monomial.
  refine (Asymptotics.IsBigO.of_bound ‖a‖ ?_).trans_isLittleO
    (Asymptotics.isLittleO_pow_pow hnk)
  filter_upwards
  intro h
  simp only [norm_smul]
  rw [mul_comm]

/-- If a fixed vector times a scalar power is little-o of that same power at
zero, then the vector vanishes. -/
private lemma eq_zero_of_pow_smul_isLittleO {n : ℕ} {a : F}
    (ha : (fun h : ℝ ↦ h ^ n • a) =o[𝓝 0] fun h : ℝ ↦ h ^ n) : a = 0 := by
  -- A nonzero coefficient would make the scalar power big-O of the vector monomial.
  by_contra ha0
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hreverse :
      (fun h : ℝ ↦ h ^ n) =O[𝓝 0] fun h : ℝ ↦ h ^ n • a := by
    refine Asymptotics.IsBigO.of_bound ‖a‖⁻¹ ?_
    filter_upwards
    intro h
    calc
      ‖h ^ n‖ = ‖h ^ n‖ * (‖a‖⁻¹ * ‖a‖) := by
        rw [inv_mul_cancel₀ hnorm.ne', mul_one]
      _ = ‖a‖⁻¹ * (‖h ^ n‖ * ‖a‖) := by ring
      _ = ‖a‖⁻¹ * ‖h ^ n • a‖ := by rw [norm_smul]
      _ ≤ ‖a‖⁻¹ * ‖h ^ n • a‖ := le_rfl
  have hfrequent : ∃ᶠ h : ℝ in 𝓝 0, h ^ n ≠ 0 := by
    -- Every neighborhood of zero contains a nonzero real number.
    rw [Metric.nhds_basis_ball.frequently_iff]
    intro ε hε
    refine ⟨ε / 2, ?_, pow_ne_zero n (ne_of_gt (half_pos hε))⟩
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)] using
      half_lt_self hε
  exact Asymptotics.isLittleO_irrefl hfrequent (hreverse.trans_isLittleO ha)

/-- If the diagonal evaluations of two one-variable jets differ by `o(h ^ m)`,
then all of their scalar coefficients through degree `m` agree. -/
theorem scalarCoeff_eq_of_eval_sub_isLittleO {m : ℕ}
    (J K : FiniteTaylorJet ℝ ℝ F m)
    (hJK : (fun h : ℝ ↦ J.eval h - K.eval h) =o[𝓝 0] fun h : ℝ ↦ h ^ m)
    (n : Fin (m + 1)) :
    J.scalarCoeff n = K.scalarCoeff n := by
  -- Normalize the evaluation difference to a finite power sum of coefficient differences.
  have hpoly :
      (fun h : ℝ ↦ ∑ i : Fin (m + 1),
        h ^ (i : ℕ) • (J.scalarCoeff i - K.scalarCoeff i)) =o[𝓝 0]
        fun h : ℝ ↦ h ^ m := by
    simpa only [eval_eq_sum_smul_scalarCoeff, ← Finset.sum_sub_distrib, smul_sub] using hJK
  have hcoeff : ∀ k (hk : k ≤ m),
      J.scalarCoeff ⟨k, Nat.lt_succ_of_le hk⟩ =
        K.scalarCoeff ⟨k, Nat.lt_succ_of_le hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
      let nk : Fin (m + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
      have hpoly_k :
          (fun h : ℝ ↦ ∑ i : Fin (m + 1),
            h ^ (i : ℕ) • (J.scalarCoeff i - K.scalarCoeff i)) =o[𝓝 0]
            fun h : ℝ ↦ h ^ k := by
        by_cases hkm : k < m
        · exact hpoly.trans (Asymptotics.isLittleO_pow_pow hkm)
        · simpa only [Nat.le_antisymm hk (Nat.le_of_not_gt hkm)] using hpoly
      have hrest :
          (fun h : ℝ ↦ ∑ i ∈ Finset.univ.erase nk,
            h ^ (i : ℕ) • (J.scalarCoeff i - K.scalarCoeff i)) =o[𝓝 0]
            fun h : ℝ ↦ h ^ k := by
        apply Asymptotics.IsLittleO.sum
        intro i hi
        have hin : i ≠ nk := (Finset.mem_erase.mp hi).1
        rcases lt_or_gt_of_ne hin with hik | hki
        · have hprevious := ih (i : ℕ) hik (Nat.le_trans (Nat.le_of_lt hik) hk)
          simpa only [hprevious, sub_self, smul_zero] using
            (Asymptotics.isLittleO_zero (fun h : ℝ ↦ h ^ k) (𝓝 0))
        · exact pow_smul_isLittleO_pow hki (J.scalarCoeff i - K.scalarCoeff i)
      have hleading :
          (fun h : ℝ ↦ h ^ k • (J.scalarCoeff nk - K.scalarCoeff nk)) =o[𝓝 0]
            fun h : ℝ ↦ h ^ k := by
        -- Subtracting the higher-degree tail leaves precisely the degree-`k` term.
        refine (hpoly_k.sub hrest).congr' ?_ Filter.EventuallyEq.rfl
        filter_upwards
        intro h
        rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ nk)]
        abel
      exact sub_eq_zero.mp (eq_zero_of_pow_smul_isLittleO hleading)
  -- Specialize the degreewise induction to the requested finite index.
  exact hcoeff (n : ℕ) (Nat.le_of_lt_succ n.isLt)

end FiniteTaylorJet
