/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Corollary_6_52
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_5
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Proposition_11_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

open Filter

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

private theorem tendsto_level_upperBounds (ξ η : ℝ) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (((((n + 2 : ℕ) : ℝ)⁻¹) * η + (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) * ξ : ℝ) : EReal))
      Filter.atTop (nhds (ξ : EReal)) := by
  have hα :
      Filter.Tendsto (fun n : ℕ ↦ ((((n + 2 : ℕ) : ℝ)⁻¹) : ℝ))
        Filter.atTop (nhds (0 : ℝ)) := by
    have hshift : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) Filter.atTop Filter.atTop :=
      tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hβ :
      Filter.Tendsto (fun n : ℕ ↦ 1 - ((((n + 2 : ℕ) : ℝ)⁻¹) : ℝ))
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hα
  have hreal :
      Filter.Tendsto
        (fun n : ℕ ↦ ((((n + 2 : ℕ) : ℝ)⁻¹) * η + (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) * ξ : ℝ))
        Filter.atTop (nhds ξ) := by
    simpa [zero_mul, one_mul, mul_comm] using (hα.const_mul η).add (hβ.const_mul ξ)
  exact (continuous_coe_real_ereal.tendsto ξ).comp hreal

omit [FiniteDimensional ℝ H] in
private theorem recessionCone_lowerLevelSet_mono_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {ξ η : ℝ} (hξη : ξ ≤ η) :
    Set.recessionCone (lowerLevelSet f.asEReal η) ⊆
      Set.recessionCone (lowerLevelSet f.asEReal ξ) := by
  intro v hv
  have hconv_epi : Convex ℝ (epigraph f.asEReal) :=
    convex_epigraph_asEReal_of_mem_gammaZero hf
  rw [Set.mem_recessionCone_iff]
  intro s hs
  rcases Set.mem_add.1 hs with ⟨w, hw, z, hzξ, rfl⟩
  have hw' : w = v := by
    simpa using hw
  subst w
  have hη_convex : Convex ℝ (lowerLevelSet f.asEReal η) :=
    convex_lowerLevelSet_of_convex_epigraph f.asEReal hconv_epi η
  have hzη : z ∈ lowerLevelSet f.asEReal η := by
    rw [mem_lowerLevelSet_iff] at hzξ ⊢
    exact le_trans hzξ (by exact_mod_cast hξη)
  have hz_dom : z ∈ effectiveDomain f := by
    rw [mem_lowerLevelSet_iff] at hzξ
    exact lt_of_le_of_lt hzξ (EReal.coe_lt_top ξ)
  have hpointwise :
      ∀ n : ℕ,
        (f (z + v) : EReal) ≤
          (((((n + 2 : ℕ) : ℝ)⁻¹) * η + (1 - (((n + 2 : ℕ) : ℝ)⁻¹)) * ξ : ℝ) : EReal) := by
    intro n
    have hray_mem :
        z + ((n + 2 : ℕ) : ℝ) • v ∈ lowerLevelSet f.asEReal η := by
      simpa [add_comm, add_left_comm, add_assoc] using
        Set.nat_ray_point_mem_of_mem_recessionCone hη_convex hv hzη (n + 2)
    have hray_dom : z + ((n + 2 : ℕ) : ℝ) • v ∈ effectiveDomain f := by
      rw [mem_lowerLevelSet_iff] at hray_mem
      exact lt_of_le_of_lt hray_mem (EReal.coe_lt_top η)
    let α : ℝ := (((n + 2 : ℕ) : ℝ)⁻¹)
    have hα_pos : 0 < α := by
      dsimp [α]
      positivity
    have hden_gt_one : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_lt_succ_succ n
    have hα_lt_one : α < 1 := by
      dsimp [α]
      simpa [one_div] using inv_lt_one_of_one_lt₀ hden_gt_one
    have hα_ne : ((n + 2 : ℕ) : ℝ) ≠ 0 := by
      positivity
    have hcombo :
        α • (z + ((n + 2 : ℕ) : ℝ) • v) + (1 - α) • z = z + v := by
      have hαc : α * ((n + 2 : ℕ) : ℝ) = 1 := by
        dsimp [α]
        field_simp [hα_ne]
      calc
        α • (z + ((n + 2 : ℕ) : ℝ) • v) + (1 - α) • z
            = α • z + α • (((n + 2 : ℕ) : ℝ) • v) + (1 - α) • z := by
                rw [smul_add]
        _ = (α • z + (1 - α) • z) + α • (((n + 2 : ℕ) : ℝ) • v) := by
              abel
        _ = (α + (1 - α)) • z + α • (((n + 2 : ℕ) : ℝ) • v) := by
              rw [add_smul]
        _ = z + (α * ((n + 2 : ℕ) : ℝ)) • v := by
              simp [smul_smul]
        _ = z + v := by
              rw [hαc, one_smul]
    have hcombo_symm :
        α • (z + ((n + 2 : ℕ) : ℝ) • v) + (1 - α) • z = v + z := by
      simpa [add_comm] using hcombo
    have hconv :
        (f (z + v) : EReal) ≤
          (α : EReal) * (f (z + ((n + 2 : ℕ) : ℝ) • v) : EReal) +
            ((1 - α : ℝ) : EReal) * (f z : EReal) := by
      calc
        (f (z + v) : EReal) = (f (v + z) : EReal) := by
          rw [add_comm]
        _ = (f (α • (z + ((n + 2 : ℕ) : ℝ) • v) + (1 - α) • z) : EReal) := by
          rw [hcombo_symm]
        _ ≤ (α : EReal) * (f (z + ((n + 2 : ℕ) : ℝ) • v) : EReal) +
              ((1 - α : ℝ) : EReal) * (f z : EReal) :=
          hf.2.ineq hray_dom hz_dom hα_pos hα_lt_one
    have hweighted :
        (α : EReal) * (f (z + ((n + 2 : ℕ) : ℝ) • v) : EReal) +
            ((1 - α : ℝ) : EReal) * (f z : EReal) ≤
          (((α * η + (1 - α) * ξ : ℝ)) : EReal) := by
      have hterm1 :
          (α : EReal) * (f (z + ((n + 2 : ℕ) : ℝ) • v) : EReal) ≤
            (α : EReal) * (η : EReal) :=
        mul_le_mul_of_nonneg_left ((mem_lowerLevelSet_iff _ _ _).1 hray_mem)
          (EReal.coe_nonneg.mpr hα_pos.le)
      have hterm2 :
          ((1 - α : ℝ) : EReal) * (f z : EReal) ≤
            ((1 - α : ℝ) : EReal) * (ξ : EReal) :=
        mul_le_mul_of_nonneg_left hzξ
          (EReal.coe_nonneg.mpr (sub_nonneg.mpr hα_lt_one.le))
      calc
        (α : EReal) * (f (z + ((n + 2 : ℕ) : ℝ) • v) : EReal) +
            ((1 - α : ℝ) : EReal) * (f z : EReal)
            ≤ (α : EReal) * (η : EReal) + ((1 - α : ℝ) : EReal) * (ξ : EReal) :=
          add_le_add hterm1 hterm2
        _ = (((α * η + (1 - α) * ξ : ℝ)) : EReal) := by
          rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simpa [α, mul_comm, mul_left_comm, mul_assoc] using hconv.trans hweighted
  have hconst :
      Filter.Tendsto (fun _ : ℕ ↦ (f (z + v) : EReal))
        Filter.atTop (nhds (f (z + v) : EReal)) :=
    tendsto_const_nhds
  rw [mem_lowerLevelSet_iff]
  simpa [add_comm] using
    le_of_tendsto_of_tendsto' hconst (tendsto_level_upperBounds ξ η) hpointwise

-- Proof sketch: if `f` is coercive, Proposition 11.12 makes every real lower level set bounded, so
-- any point of the nonempty effective domain gives a nonempty bounded one. Conversely, use
-- lower semicontinuity to make that level set closed and `Γ₀`-convexity to apply the finite-
-- dimensional recession-cone criterion from Corollary 6.52; this forces every higher lower level
-- set to be bounded, and then Proposition 11.12 yields coercivity.
/-- Proposition 11.13: for a function `f ∈ Γ₀(H)` on a finite-dimensional real normed
space, coercivity is equivalent to the existence of a nonempty bounded real lower level set. -/
theorem coercive_iff_exists_nonempty_bounded_lowerLevelSet_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Coercive f.asEReal ↔
      ∃ ξ : ℝ,
        (lowerLevelSet f.asEReal ξ).Nonempty ∧
          Bornology.IsBounded (lowerLevelSet f.asEReal ξ) := by
  constructor
  · intro hcoe
    rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨(f x : EReal).toReal, ?_, ?_⟩
    · refine ⟨x, ?_⟩
      exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx))
    · exact (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hcoe _
  · rintro ⟨ξ, hξ_nonempty, hξ_bounded⟩
    refine (coercive_iff_bounded_lowerLevelSet f.asEReal).2 ?_
    intro η
    by_cases hη_nonempty : (lowerLevelSet f.asEReal η).Nonempty
    · by_cases hηξ : η ≤ ξ
      · exact hξ_bounded.subset <| by
          intro x hx
          rw [mem_lowerLevelSet_iff] at hx ⊢
          exact le_trans hx (by exact_mod_cast hηξ)
      · have hξη : ξ ≤ η := le_of_not_ge hηξ
        have hconv_epi : Convex ℝ (epigraph f.asEReal) :=
          convex_epigraph_asEReal_of_mem_gammaZero hf
        have hη_closed :
            IsClosed (lowerLevelSet f.asEReal η) :=
          (lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1 η
        have hη_convex : Convex ℝ (lowerLevelSet f.asEReal η) :=
          convex_lowerLevelSet_of_convex_epigraph f.asEReal hconv_epi η
        by_contra hη_bounded
        have hξ_closed :
            IsClosed (lowerLevelSet f.asEReal ξ) :=
          (lowerSemicontinuous_iff_isClosed_lowerLevelSet f.asEReal).1 hf.1 ξ
        have hξ_convex : Convex ℝ (lowerLevelSet f.asEReal ξ) :=
          convex_lowerLevelSet_of_convex_epigraph f.asEReal hconv_epi ξ
        have hξ_rec :
            Set.recessionCone (lowerLevelSet f.asEReal ξ) = ({0} : Set H) :=
          (Set.bounded_iff_recessionCone_eq_singleton_zero_of_nonempty_isClosed_convex
            (lowerLevelSet f.asEReal ξ) hξ_nonempty hξ_closed hξ_convex).1
            hξ_bounded
        have hη_rec_ne :
            Set.recessionCone (lowerLevelSet f.asEReal η) ≠ ({0} : Set H) := by
          intro hη_rec
          exact hη_bounded <|
            (Set.bounded_iff_recessionCone_eq_singleton_zero_of_nonempty_isClosed_convex
              (lowerLevelSet f.asEReal η) hη_nonempty hη_closed hη_convex).2
              hη_rec
        have hy_exists :
            ∃ y : H,
              y ∈ Set.recessionCone (lowerLevelSet f.asEReal η) ∧ y ≠ 0 := by
          by_contra hy_exists
          apply hη_rec_ne
          ext y
          constructor
          · intro hy
            by_cases hy0 : y = 0
            · simp [hy0]
            · exfalso
              exact hy_exists ⟨y, hy, hy0⟩
          · intro hy
            rcases Set.mem_singleton_iff.1 hy with rfl
            exact Set.zero_mem_recessionCone _
        rcases hy_exists with ⟨y, hy, hy_ne_zero⟩
        have hyξ :
            y ∈ Set.recessionCone (lowerLevelSet f.asEReal ξ) :=
          recessionCone_lowerLevelSet_mono_of_mem_gammaZero hf hξη hy
        have hy_zero : y = 0 := by
          have : y ∈ ({0} : Set H) := by
            simpa [hξ_rec] using hyξ
          simpa using this
        exact hy_ne_zero hy_zero
    · have hempty :
          lowerLevelSet f.asEReal η = (∅ : Set H) :=
        Set.not_nonempty_iff_eq_empty.mp hη_nonempty
      simp [hempty]

end ERealFunction
