/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_47
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Example_16_62
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open ERealFunction
open scoped InnerProductSpace Pointwise

universe u

namespace Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.22 is the three-way equivalence between vanishing Gâteaux
  derivative of `Metric.infDist · C` at `x`, non-support-point membership, and the tangent-cone
  condition `T[C] x = univ`.
- `core/canonical`: the owner declarations are `Metric.infDist`, `spts`, `N[C] x`, `T[C] x`, and
  the Chapter 16/17 subdifferential and differentiability criteria.
- `bridge/view`: the pairwise equivalences below are thin consequences connecting the source-facing
  clauses to the canonical normal-cone and tangent-cone owners.
-/

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem distanceToSet_toEReal_continuousAtOnEffectiveDomain (C : Set H) (x : H) :
    ERealFunction.ContinuousAtOnEffectiveDomain
      (fun y : H ↦ Metric.infDist y C).toEReal x := by
  refine ⟨by simp [Function.effectiveDomain_toEReal], ?_⟩
  simpa [Function.effectiveDomain_toEReal] using
    (Metric.continuous_infDist_pt C).continuousAt.continuousWithinAt

omit [CompleteSpace H] in
private theorem normalized_mem_normalCone_inter_closedBall_of_nonzero
    {C : Set H} {x u : H} (hx : x ∈ C) (hu : u ∈ N[C] x) (hu_ne : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ N[C] x ∩ Metric.closedBall (0 : H) 1 := by
  constructor
  · rw [Set.normalCone_of_mem hx] at hu ⊢
    have hu_inner : innerSupremumOn (C - ({x} : Set H)) u ≤ 0 := by
      simpa using hu
    have hu_pointwise : ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
      have hsep :
          innerSupremumOn (C - ({x} : Set H)) u ≤ innerInfimumOn ({0} : Set H) u := by
        simpa using hu_inner
      have hinner :=
        (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
          (C - ({x} : Set H)) ({0} : Set H) u).1 hsep
      intro y hy
      have hy_sub : y - x ∈ C - ({x} : Set H) := ⟨y, hy, x, by simp, rfl⟩
      simpa using hinner (y - x) hy_sub 0 (by simp)
    change innerSupremumOn (C - ({x} : Set H)) (‖u‖⁻¹ • u) ≤ 0
    have hsep :
        innerSupremumOn (C - ({x} : Set H)) (‖u‖⁻¹ • u) ≤
          innerInfimumOn ({0} : Set H) (‖u‖⁻¹ • u) :=
      (innerSupremumOn_le_innerInfimumOn_iff_forall_inner_le
        (C - ({x} : Set H)) ({0} : Set H) (‖u‖⁻¹ • u)).2
        (fun v hv z hz ↦ by
          rcases hv with ⟨y, hy, z', hz', rfl⟩
          have hz'' : z' = x := by simpa using hz'
          have hz0 : z = 0 := by simpa using hz
          subst hz''
          subst hz0
          simpa [real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
            mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg u)) (hu_pointwise y hy))
    simpa using hsep
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using (norm_smul_inv_norm hu_ne).le

omit [CompleteSpace H] in
/-- At a point of `C`, not being a support point is equivalent to the normal cone being trivial. -/
theorem not_mem_supportPoints_iff_normalCone_eq_singleton_zero_of_mem
    {C : Set H} {x : H} (hx : x ∈ C) :
    x ∉ spts C ↔ N[C] x = ({0} : Set H) := by
  have hzero : (0 : H) ∈ N[C] x := by
    rw [normalCone_of_mem hx]
    simp [innerSupremumOn_eq_sSup_image]
  rw [supportPoints_eq_setOf_nontrivial_normalCone]
  constructor
  · intro hx_support
    have hdiff : N[C] x \ ({0} : Set H) = ∅ := by
      simpa using hx_support
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr hzero)
    rwa [diff_eq_empty] at hdiff
  · intro hN
    simp [hN]

/-- For a convex set, a point of `C` is not a support point exactly when its tangent cone is all
of `H`. -/
theorem not_mem_supportPoints_iff_tangentCone_eq_univ_of_convex
    {C : Set H} {x : H} (hC_convex : Convex ℝ C) (hx : x ∈ C) :
    x ∉ spts C ↔ T[C] x = (univ : Set H) := by
  exact
    (not_mem_supportPoints_iff_normalCone_eq_singleton_zero_of_mem hx).trans
      (tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem hC_convex hx).symm

-- Proof sketch: `(i) → (ii)` uses Example 16.62 to identify `∂ d_C(x)` and Proposition 17.31 to
-- read Gâteaux differentiability of `Metric.infDist · C` with zero gradient as the singleton
-- subdifferential `{0}`; this
-- rules out nonzero supporting directions. `(ii) → (iii)` is the separation argument from the
-- source, showing that failure of `T[C] x = univ` yields a nonzero `u` with
-- `σ[C] u ≤ ⟪x, u⟫`. `(iii) → (i)` uses Proposition 17.31 again after Example 16.62 reduces the
-- subdifferential to `{0}` when the tangent cone is all of `H`.
/-- Proposition 18.22: for a closed convex subset `C` of a real Hilbert space and `x ∈ C`, the
following are equivalent: the distance function to `C` has Gâteaux derivative `0` at `x`, the
point `x` is not a support point of `C`, and the tangent cone `T[C] x` is the whole space. -/
theorem distanceToSet_zeroGateauxDerivative_tfae_not_mem_supportPoints_tangentCone_eq_univ
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    List.TFAE
      [ HasGateauxDerivativeAt
          (fun y ↦ Metric.infDist y C)
          (toDual ℝ H (0 : H)) x,
        x ∉ spts C,
        T[C] x = (univ : Set H) ] := by
  let f : H → Set.Ioi (⊥ : EReal) := (fun y : H ↦ Metric.infDist y C).toEReal
  have hxcont : ERealFunction.ContinuousAtOnEffectiveDomain f x :=
    distanceToSet_toEReal_continuousAtOnEffectiveDomain C x
  have h12 :
      HasGateauxDerivativeAt (fun y ↦ Metric.infDist y C) (toDual ℝ H (0 : H)) x →
        x ∉ spts C := by
    intro hgrad hx_support
    have hsubd : (∂ f) x = ({0} : Set H) := by
      have hxdom : x ∈ ERealFunction.effectiveDomain f := by
        simp [f, Function.effectiveDomain_toEReal]
      simpa [f] using
        ERealFunction.subdifferential_eq_singleton_of_hasGateauxDerivativeAt
          f hxdom (0 : H) hgrad
    have hnontrivial : N[C] x \ ({0} : Set H) ≠ ∅ := by
      rw [Set.supportPoints_eq_setOf_nontrivial_normalCone] at hx_support
      exact hx_support
    obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hnontrivial
    have hu' : u ∈ N[C] x ∧ u ∉ ({0} : Set H) := by
      simpa [Set.mem_diff] using hu
    have hu_ne : u ≠ 0 := by
      simpa using hu'.2
    have huN : u ∈ N[C] x := hu'.1
    have hu_inner : innerSupremumOn (C - ({x} : Set H)) u ≤ 0 := by
      simpa [Set.normalCone_of_mem hx] using huN
    have hx_frontier : x ∈ frontier C := by
      have hx_notInterior : x ∉ interior C := by
        intro hx_int
        have hC_int_nonempty : (interior C).Nonempty := ⟨x, hx_int⟩
        have hNzero : N[C] x = ({0} : Set H) :=
          (mem_interior_iff_normalCone_eq_singleton_zero_of_convex
            hC_convex hC_int_nonempty hx).1 hx_int
        exact hnontrivial (by simp [hNzero])
      exact (mem_frontier_iff_notMem_interior hx).2 hx_notInterior
    have hv_subd : ‖u‖⁻¹ • u ∈ (∂ f) x := by
      rw [subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
        hC_closed hC_convex hx_frontier]
      exact normalized_mem_normalCone_inter_closedBall_of_nonzero hx huN hu_ne
    rw [hsubd] at hv_subd
    have hzero : ‖u‖⁻¹ • u = (0 : H) := by
      simpa using hv_subd
    have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu_ne
    have hone : (1 : ℝ) = 0 := by
      have := congrArg norm hzero
      simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), hnorm_pos.ne'] at this
    linarith
  have h23 : (x ∉ spts C) ↔ T[C] x = (univ : Set H) :=
    not_mem_supportPoints_iff_tangentCone_eq_univ_of_convex hC_convex hx
  have h31 :
      T[C] x = (univ : Set H) →
        HasGateauxDerivativeAt (fun y ↦ Metric.infDist y C) (toDual ℝ H (0 : H)) x := by
    intro hT
    have hN : N[C] x = ({0} : Set H) :=
      (tangentCone_eq_univ_iff_normalCone_eq_singleton_zero_of_mem hC_convex hx).1 hT
    have hsubd : (∂ f) x = ({0} : Set H) := by
      by_cases hx_frontier : x ∈ frontier C
      · rw [subdifferential_distanceToSet_eq_normalCone_inter_closedBall_of_mem_frontier
          hC_closed hC_convex hx_frontier]
        simp [hN]
      · have hx_int : x ∈ interior C := by
          rw [mem_frontier_iff_notMem_interior hx] at hx_frontier
          exact not_not.mp hx_frontier
        simpa [f] using subdifferential_distanceToSet_eq_singleton_zero_of_mem_interior hx_int
    simpa [f] using
      hasGateauxDerivativeAt_of_subdifferential_eq_singleton_of_continuousAtOnEffectiveDomain
        f hxcont hsubd
  tfae_have 1 → 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_have 3 → 1 := h31
  tfae_finish

/-- Proposition 18.22, clauses (i) and (ii): for a closed convex set, the distance function has
Gâteaux derivative `0` at `x ∈ C` exactly when `x` is not a support point. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_iff_not_mem_supportPoints
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDual ℝ H (0 : H)) x ↔
      x ∉ spts C := by
  have h₁ :
      [ HasGateauxDerivativeAt
            (fun y ↦ Metric.infDist y C)
            (toDual ℝ H (0 : H)) x,
        x ∉ spts C,
        T[C] x = (univ : Set H) ][0]? =
        some
          (HasGateauxDerivativeAt
            (fun y ↦ Metric.infDist y C)
            (toDual ℝ H (0 : H)) x) := by
    rfl
  exact
    List.TFAE.out
      (distanceToSet_zeroGateauxDerivative_tfae_not_mem_supportPoints_tangentCone_eq_univ
        hC_closed hC_convex hx) 0 1 h₁ rfl

/-- Proposition 18.22, clauses (i) and (iii): for a closed convex set, the distance function has
Gâteaux derivative `0` at `x ∈ C` exactly when `T[C] x = univ`. -/
theorem distanceToSet_hasGateauxDerivativeAt_zero_iff_tangentCone_eq_univ
    {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {x : H} (hx : x ∈ C) :
    HasGateauxDerivativeAt
        (fun y ↦ Metric.infDist y C)
        (toDual ℝ H (0 : H)) x ↔
      T[C] x = (univ : Set H) := by
  have h₁ :
      [ HasGateauxDerivativeAt
            (fun y ↦ Metric.infDist y C)
            (toDual ℝ H (0 : H)) x,
        x ∉ spts C,
        T[C] x = (univ : Set H) ][0]? =
        some
          (HasGateauxDerivativeAt
            (fun y ↦ Metric.infDist y C)
            (toDual ℝ H (0 : H)) x) := by
    rfl
  exact
    List.TFAE.out
      (distanceToSet_zeroGateauxDerivative_tfae_not_mem_supportPoints_tangentCone_eq_univ
        hC_closed hC_convex hx) 0 2 h₁ rfl

end

end Set
