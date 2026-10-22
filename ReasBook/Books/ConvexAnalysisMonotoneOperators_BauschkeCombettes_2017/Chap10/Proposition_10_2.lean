/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

private lemma smul_mem_of_isCone {X : Type*} [AddCommGroup X] [Module ℝ X] {C : Set X}
    (hC : IsCone C) {a : ℝ} (ha : 0 < a) {x : X} (hx : x ∈ C) :
    a • x ∈ C := by
  rw [isCone_iff] at hC
  rw [hC]
  exact Set.mem_smul.mpr ⟨a, ha, x, hx, rfl⟩

private lemma mem_epigraph_smul_iff_of_isCone {f : H → EReal} (h_epi : IsCone (epigraph f))
    {a : ℝ} (ha : 0 < a) {x : H} {ξ : ℝ} :
    (a • x, a • ξ) ∈ epigraph f ↔ (x, ξ) ∈ epigraph f := by
  constructor
  · intro h
    have h' : a⁻¹ • (a • x, a • ξ) ∈ epigraph f :=
      smul_mem_of_isCone h_epi (inv_pos.mpr ha) h
    simpa [Prod.smul_mk, smul_smul, ha.ne', mul_assoc] using h'
  · intro h
    have h' : a • (x, ξ) ∈ epigraph f :=
      smul_mem_of_isCone h_epi ha h
    simpa [Prod.smul_mk] using h'

-- Proof sketch: for the forward direction, rewrite epigraph membership with
-- `mem_epigraph_iff` and transport the defining inequality along positive dilations using
-- positive homogeneity. For the reverse direction, apply the cone property to epigraph points on
-- the graph of `f` and read off the exact scaled value from the minimal epigraph height.
/-- Proposition 10.2: an extended-real-valued function is positively homogeneous if and only if
its epigraph is a cone. -/
theorem positivelyHomogeneous_iff_isCone_epigraph (f : H → EReal) :
    PositivelyHomogeneous f ↔ IsCone (epigraph f) := by
  constructor
  · intro hf
    rw [isCone_iff]
    ext p
    rcases p with ⟨x, ξ⟩
    constructor
    · intro hp
      exact Set.mem_smul.mpr ⟨1, by simp, (x, ξ), hp, by simp⟩
    · intro hp
      rcases Set.mem_smul.mp hp with ⟨a, ha, p, hp_mem, hp_eq⟩
      rcases p with ⟨y, η⟩
      rw [Prod.smul_mk] at hp_eq
      injection hp_eq with hx hξ
      subst hx hξ
      rw [mem_epigraph_iff] at hp_mem ⊢
      simpa [Prod.smul_mk, EReal.real_smul_def, smul_eq_mul, hf ha y] using
        mul_le_mul_of_nonneg_left hp_mem (show (0 : EReal) ≤ a by exact_mod_cast ha.le)
  · intro h_epi a ha x
    by_cases hx_top : f x = ⊤
    · have hax_top : f (a • x) = ⊤ := by
        by_contra hax_top
        have hax_epi : (a • x, (f (a • x)).toReal) ∈ epigraph f := by
          rw [mem_epigraph_iff]
          exact EReal.le_coe_toReal hax_top
        have hx_epi : (x, a⁻¹ • (f (a • x)).toReal) ∈ epigraph f := by
          have hscaled : (a • x, a • (a⁻¹ • (f (a • x)).toReal)) ∈ epigraph f := by
            simpa [smul_smul, ha.ne', mul_assoc] using hax_epi
          exact (mem_epigraph_smul_iff_of_isCone h_epi ha).1 hscaled
        have hx_le : f x ≤ (a⁻¹ • (f (a • x)).toReal : ℝ) := (mem_epigraph_iff _ _ _).1 hx_epi
        rw [hx_top] at hx_le
        exact (not_le.mpr (EReal.coe_lt_top _)) hx_le
      simpa [EReal.real_smul_def, hx_top, EReal.coe_mul_top_of_pos ha] using hax_top
    · by_cases hx_bot : f x = ⊥
      · have hax_bot : f (a • x) = ⊥ := by
          refine (EReal.eq_bot_iff_forall_lt _).2 ?_
          intro y
          have hx_epi : (x, a⁻¹ • (y - 1)) ∈ epigraph f := by
            rw [mem_epigraph_iff, hx_bot]
            simp
          have hax_epi : (a • x, a • (a⁻¹ • (y - 1))) ∈ epigraph f :=
            (mem_epigraph_smul_iff_of_isCone h_epi ha).2 hx_epi
          have hax_le : f (a • x) ≤ (a • (a⁻¹ • (y - 1)) : ℝ) :=
            (mem_epigraph_iff _ _ _).1 hax_epi
          have hy_lt : (((a • (a⁻¹ • (y - 1)) : ℝ)) : EReal) < y := by
            have hy : (y - 1 : ℝ) < y := sub_lt_self y zero_lt_one
            simpa [smul_smul, ha.ne', mul_assoc] using (show ((y - 1 : ℝ) : EReal) < y by
              exact_mod_cast hy)
          exact lt_of_le_of_lt hax_le hy_lt
        simpa [EReal.real_smul_def, hx_bot, EReal.coe_mul_bot_of_pos ha] using hax_bot
      · have hx_coe : ((f x).toReal : EReal) = f x := EReal.coe_toReal hx_top hx_bot
        have hx_epi : (x, (f x).toReal) ∈ epigraph f := by
          rw [mem_epigraph_iff]
          simp [hx_coe]
        have hax_epi : (a • x, a • (f x).toReal) ∈ epigraph f :=
          (mem_epigraph_smul_iff_of_isCone h_epi ha).2 hx_epi
        have hax_le : f (a • x) ≤ (a • (f x).toReal : ℝ) := (mem_epigraph_iff _ _ _).1 hax_epi
        have hax_top : f (a • x) ≠ ⊤ := by
          exact ne_of_lt <| lt_of_le_of_lt hax_le (EReal.coe_lt_top _)
        have hax_bot : f (a • x) ≠ ⊥ := by
          intro hax_bot
          have hx_bot' : f x = ⊥ := by
            refine (EReal.eq_bot_iff_forall_lt _).2 ?_
            intro y
            have hax_epi' : (a • x, a • (y - 1)) ∈ epigraph f := by
              rw [mem_epigraph_iff, hax_bot]
              simp
            have hx_epi' : (x, y - 1) ∈ epigraph f :=
              (mem_epigraph_smul_iff_of_isCone h_epi ha).1 hax_epi'
            have hx_le : f x ≤ (y - 1 : ℝ) := (mem_epigraph_iff _ _ _).1 hx_epi'
            have hy : ((y - 1 : ℝ) : EReal) < y := by
              exact_mod_cast sub_lt_self y zero_lt_one
            exact lt_of_le_of_lt hx_le hy
          exact hx_bot hx_bot'
        have hax_toReal_epi : (a • x, (f (a • x)).toReal) ∈ epigraph f := by
          rw [mem_epigraph_iff]
          exact EReal.le_coe_toReal hax_top
        have hx_from_ax_epi : (x, a⁻¹ • (f (a • x)).toReal) ∈ epigraph f := by
          have hscaled : (a • x, a • (a⁻¹ • (f (a • x)).toReal)) ∈ epigraph f := by
            simpa [smul_smul, ha.ne', mul_assoc] using hax_toReal_epi
          exact (mem_epigraph_smul_iff_of_isCone h_epi ha).1 hscaled
        have hx_le_toReal : f x ≤ (a⁻¹ • (f (a • x)).toReal : ℝ) :=
          (mem_epigraph_iff _ _ _).1 hx_from_ax_epi
        have hmul_le_toReal : (a • (f x).toReal : ℝ) ≤ (f (a • x)).toReal := by
          have hx_le_toReal' : (f x).toReal ≤ a⁻¹ * (f (a • x)).toReal := by
            rw [← EReal.coe_le_coe_iff]
            simpa [hx_coe, smul_eq_mul]
          simpa [smul_eq_mul, mul_assoc, ha.ne'] using
            mul_le_mul_of_nonneg_left hx_le_toReal' ha.le
        have htoReal_le : ((a • (f x).toReal : ℝ) : EReal) ≤ (f (a • x)).toReal := by
          exact_mod_cast hmul_le_toReal
        have hmul_le : ((a • (f x).toReal : ℝ) : EReal) ≤ f (a • x) :=
          le_trans htoReal_le (EReal.coe_toReal_le hax_bot)
        have hEq : f (a • x) = ((a • (f x).toReal : ℝ) : EReal) := le_antisymm hax_le hmul_le
        simpa [EReal.real_smul_def, hx_coe, smul_eq_mul] using hEq

-- Proof sketch: if the epigraph is a cone and `x ∈ dom f`, choose a real height above `f x` to
-- obtain an epigraph point. Apply the cone property to positive dilations and project to the
-- first coordinate to see that the dilated point still lies in the domain.
/-- The domain of an extended-real-valued function with conic epigraph is itself a cone. -/
theorem isCone_dom_of_isCone_epigraph {f : H → EReal} (h_epi : IsCone (epigraph f)) :
    IsCone (dom f) := by
  have hph : PositivelyHomogeneous f := (positivelyHomogeneous_iff_isCone_epigraph f).2 h_epi
  rw [isCone_iff]
  ext x
  constructor
  · intro hx
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · intro hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    rw [mem_dom_iff] at hy ⊢
    rw [hph ha y, EReal.real_smul_def]
    have ha_pos : 0 < a := ha
    exact lt_top_iff_ne_top.mpr <| by
      intro htop
      rw [EReal.mul_eq_top] at htop
      simp [ha_pos, not_lt.mpr ha_pos.le, ne_of_lt hy] at htop

end ERealFunction
