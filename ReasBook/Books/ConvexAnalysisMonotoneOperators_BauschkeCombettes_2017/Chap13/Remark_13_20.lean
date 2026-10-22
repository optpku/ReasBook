/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Proposition_13_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Example_7_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ERealFunction InnerProductSpace Pointwise
open ERealFunction

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [Nontrivial H]

-- Proof sketch: if a cone were self-polar, then `0 ∈ K`, so the indicator of `K` would be
-- self-conjugate by the standard indicator/polar-cone correspondence for nonempty cones,
-- contradicting the uniqueness of self-conjugate functions on a nontrivial Hilbert space.
/-- Remark 13.20 (1): clause (i). A cone in a nontrivial real inner-product space cannot be
self-polar. In particular, a convex cone cannot be self-polar. -/
theorem isCone_ne_polarCone_of_nontrivial
    {K : Set H} (hK_cone : IsCone K) :
    K ≠ Kᵒ⊖ := by
  intro hK
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK, Set.mem_polarCone_iff_forall_inner_nonpos]
    intro x hx
    simp
  have hself : ((ι[K]).asEReal) = ((ι[K]).asEReal)∗ := by
    have hindicator :
        ((ι[K]).asEReal)∗ = ((ι[K]).asEReal) := by
      have hindicator :=
        conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone K hK_nonempty hK_cone
      rw [hK.symm] at hindicator
      exact hindicator
    exact hindicator.symm
  have hhalf :=
    (self_conjugate_iff_eq_half_squared_norm ((ι[K]).asEReal)).mp hself
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  have hxval := congrFun hhalf x
  by_cases hxK : x ∈ K
  · simp [ERealFunction.indicator, hxK] at hxval
    exact hx hxval
  · simp [ERealFunction.indicator, hxK] at hxval
    have hne : (⊤ : EReal) ≠ (((2 : ℝ)⁻¹ * ‖x‖ ^ 2 : ℝ) : EReal) :=
      EReal.top_ne_coe _
    exact hne (by simpa using hxval)

-- Proof sketch: a linear subspace is a convex cone, so the previous theorem excludes equality
-- between the subspace and the corresponding polar object; for subspaces this is the
-- self-orthogonality statement.
/-- A linear subspace of a nontrivial real inner-product space cannot equal its orthogonal
complement. -/
theorem submodule_not_self_orthogonal_of_nontrivial (V : Submodule ℝ H) :
    Vᗮ ≠ V := by
  intro hV
  apply isCone_ne_polarCone_of_nontrivial (Set.submodule_isCone V)
  calc
    (V : Set H) = (Vᗮ : Set H) := congrArg (fun W : Submodule ℝ H ↦ (W : Set H)) hV.symm
    _ = (V : Set H)ᵒ⊖ := (Set.polarSet_and_polarCone_eq_orthogonal_of_submodule V).2.symm

end

end Set

namespace ERealFunction

section HilbertSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
private theorem reverse_indicator_asEReal (K : Set H) :
    ((ι[K]).asEReal)ᵛ = (ι[-K]).asEReal := by
  ext x
  by_cases hx : -x ∈ K
  · have hx' : x ∈ -K := Set.mem_neg.mpr hx
    simp [ERealFunction.reverse, ERealFunction.indicator, hx, hx']
  · have hx' : x ∉ -K := by
      simpa using hx
    simp [ERealFunction.reverse, ERealFunction.indicator, hx, hx']

private theorem dualCone_isCone (K : Set H) : IsCone (Set.dualCone K) := by
  change Set.dualCone K = (Set.Ioi (0 : ℝ) : Set ℝ) • Set.dualCone K
  ext u
  constructor
  · intro hu
    exact Set.mem_smul.mpr ⟨1, by simp, u, hu, by simp⟩
  · intro hu
    rcases Set.mem_smul.mp hu with ⟨a, ha, v, hv, rfl⟩
    rw [Set.mem_dualCone_iff] at hv ⊢
    rw [Set.mem_polarCone_iff_forall_inner_nonpos] at hv ⊢
    intro x hx
    have hvx : ⟪x, -v⟫_ℝ ≤ 0 := hv x hx
    simpa [real_inner_smul_right] using mul_nonpos_of_nonneg_of_nonpos ha.le hvx

-- Proof sketch: identify the conjugate of the indicator of `K` with the support function of `K`,
-- rewrite that support function as the indicator of the polar cone, and then use self-duality to
-- recognize the reflected indicator; the closed convex-cone structure is already carried by the
-- self-dual owner abstraction.
/-- Remark 13.20 (2): clause (ii). If `f = ι_K` for a self-dual cone `K`, then `f^* = f^∨`. -/
theorem conjugate_indicator_eq_reflection_of_isSelfDual
    {K : Set H} (hK_selfDual : K.IsSelfDual) :
    ((ι[K]).asEReal)∗ = ((ι[K]).asEReal)ᵛ := by
  have hK : K = Set.dualCone K := Set.isSelfDual_iff.mp hK_selfDual
  have hK_nonempty : K.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK, Set.mem_dualCone_iff, Set.mem_polarCone_iff_forall_inner_nonpos]
    intro x hx
    simp
  have hK_cone : IsCone K :=
    hK.symm ▸ dualCone_isCone K
  have hpolar : Set.polarCone K = -K := by
    have hneg := congrArg (fun S : Set H ↦ -S) hK
    simpa [Set.dualCone] using hneg.symm
  calc
    ((ι[K]).asEReal)∗ = (ι[Set.polarCone K]).asEReal :=
      conjugate_indicator_eq_indicator_polarCone_of_nonempty_isCone K hK_nonempty hK_cone
    _ = (ι[-K]).asEReal := by rw [hpolar]
    _ = ((ι[K]).asEReal)ᵛ := by
      simpa using (reverse_indicator_asEReal K).symm

end HilbertSpace

-- Proof sketch: unfold `negativeBurgEntropy` and simplify the added constant.
private theorem negativeBurgEntropy_sub_half_apply (x : ℝ) :
    negativeBurgEntropy x + ((-(1 / 2 : ℝ)) : EReal) =
      if 0 < x then ((-Real.log x - (1 / 2 : ℝ) : ℝ) : EReal) else ⊤ := by
  by_cases hx : 0 < x
  · simp [negativeBurgEntropy, hx]
    norm_num [sub_eq_add_neg]
  · simp [negativeBurgEntropy, hx]

-- Proof sketch: start from the explicit conjugate formula for the negative Burg entropy and use
-- that subtracting `1 / 2` from the function shifts the conjugate by `1 / 2`, yielding the same
-- reflected logarithmic barrier.
/-- Remark 13.20 (3): clause (iii). The translate of the negative Burg entropy by `-1 / 2`
satisfies `f^* = f^∨`. -/
theorem conjugate_negativeBurgEntropy_sub_half_eq_reflection :
    (fun x : ℝ ↦ negativeBurgEntropy x + ((-(1 / 2 : ℝ)) : EReal))∗ =
      (fun x : ℝ ↦ negativeBurgEntropy x + ((-(1 / 2 : ℝ)) : EReal))ᵛ := by
  ext u
  have hshift :
      (fun x : ℝ ↦ negativeBurgEntropy x + ((-(1 / 2 : ℝ)) : EReal))∗ u =
        negativeBurgEntropy∗ u + ((1 / 2 : ℝ) : EReal) := by
    simpa using
      congrFun (conjugate_translate_add_inner_add_const negativeBurgEntropy 0 0 (-(1 / 2 : ℝ))) u
  rw [hshift]
  by_cases hu : u < 0
  · have hneg : 0 < -u := neg_pos.mpr hu
    rw [ERealFunction.reverse, negativeBurgEntropy_sub_half_apply, if_pos hneg]
    rw [conjugate_negativeBurgEntropy, if_pos hu]
    have hcoe :
        (((-Real.log (-u) - 1 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal)) =
          (((-Real.log (-u) - 1 : ℝ) + 1 / 2 : ℝ) : EReal) := by
      norm_num
    rw [hcoe]
    congr 1
    ring
  · have hnonneg : 0 ≤ u := le_of_not_gt hu
    have hnot : ¬0 < -u := by
      simpa using hnonneg
    rw [ERealFunction.reverse, negativeBurgEntropy_sub_half_apply, if_neg hnot]
    rw [conjugate_negativeBurgEntropy, if_neg hu]
    simp

end ERealFunction
