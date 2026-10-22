/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric

universe u v

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

/- Definition 6.3 lies in the operator-norm / dual-pairing domain for dual-valued continuous
linear maps between real normed spaces.

Primary domain:
- operator norms of continuous linear maps `E₁ →L[ℝ] StrongDual ℝ E₂`
- dual-pairing support formulas on unit spheres

Sampled owner-style declarations:
- mathlib `ContinuousLinearMap.opNorm`
- mathlib `ContinuousLinearMap.sSup_sphere_eq_norm`
- project `dual_norm_eq_sSup_closedUnitBall` in `Chap04/Definition_4_4_4`
- project `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing` and
  `Seminorm.primalDualOperatorNorm_normSeminorm_eq_opNorm` in `Chap02/Definition_2_32`

Best owner abstraction:
- core/canonical: the ambient norm `‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ`

Primitive data:
- a continuous linear map `A : E₁ →L[ℝ] StrongDual ℝ E₂`

Derived API:
- the one-sphere norm formula `ContinuousLinearMap.sSup_sphere_eq_norm`
- the two-ball pairing formula from `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`
- the textbook two-sphere pairing formula as a source-facing bridge

Source/core/bridge triage:
- source-facing: the textbook max/sup formula over `sphere (0 : E₁) 1 × sphere (0 : E₂) 1`
- core/canonical: `ContinuousLinearMap.opNorm`
- bridge/view: rewriting the canonical norm as the two-sphere dual-pairing supremum

This item is therefore refined so that the main entry is the canonical operator norm owner, while
the textbook two-sphere formula remains only as a companion bridge theorem. -/

/- Definition 6.3: the textbook operator norm `‖A‖_{1,2}` of a dual-valued map
`A : E₁ → E₂*` is the canonical ambient norm on `E₁ →L[ℝ] StrongDual ℝ E₂`. -/
#check (‖·‖ : (E₁ →L[ℝ] StrongDual ℝ E₂) → ℝ)

/- The unit-sphere formula for the codomain norm of `A` is already the canonical mathlib bridge
from the owner `‖A‖` to a source-facing supremum. -/
recall ContinuousLinearMap.sSup_sphere_eq_norm

/-- Helper for Definition 6.3: any strict lower bound on `‖s‖` is attained strictly below some
evaluation `s u` on the unit sphere after choosing the sign of `u`. -/
lemma strongDual_exists_gt_on_unitSphere [Nontrivial E₂] (s : StrongDual ℝ E₂) {b : ℝ}
    (hb : b < ‖s‖) :
    ∃ u : E₂, u ∈ sphere (0 : E₂) 1 ∧ b < s u := by
  by_cases hs0 : ‖s‖ = 0
  · obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (x := (0 : E₂)) (r := (1 : ℝ)) |>.mpr zero_le_one
    have hs_zero : s = 0 := (ContinuousLinearMap.opNorm_zero_iff s).mp hs0
    refine ⟨u, hu, ?_⟩
    simpa [hs_zero] using hb
  · have hnorm_pos : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg s) fun h ↦ hs0 h.symm
    let r : NNReal := ⟨max b 0, le_max_right _ _⟩
    have hr_lt : (r : ℝ) < ‖s‖ := by
      dsimp [r]
      exact max_lt_iff.mpr ⟨hb, hnorm_pos⟩
    have hr_lt' : r < ‖s‖₊ := by
      exact_mod_cast hr_lt
    obtain ⟨u, hu, hsu⟩ := s.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hr_lt'
    have hu_norm : ‖u‖ = 1 := by
      simpa using congrArg NNReal.toReal hu
    have hu_sphere : u ∈ sphere (0 : E₂) 1 := mem_sphere_zero_iff_norm.mpr hu_norm
    have hsu_real : (r : ℝ) < ‖s u‖ := by
      exact_mod_cast hsu
    -- Normalize the sign to remove the absolute value from the sphere witness.
    by_cases hnonneg : 0 ≤ s u
    · refine ⟨u, hu_sphere, ?_⟩
      calc
        b ≤ r := le_max_left _ _
        _ < ‖s u‖ := hsu_real
        _ = s u := by rw [Real.norm_of_nonneg hnonneg]
    · have hneg : s u < 0 := lt_of_not_ge hnonneg
      refine ⟨-u, by simpa [mem_sphere_zero_iff_norm, norm_neg] using hu_sphere, ?_⟩
      calc
        b ≤ r := le_max_left _ _
        _ < ‖s u‖ := hsu_real
        _ = -s u := by rw [Real.norm_of_nonpos hneg.le]
        _ = s (-u) := by simp

/-- Helper for Definition 6.3: the norm of a continuous dual vector is the supremum of its
evaluation pairing over the unit sphere. -/
lemma strongDual_norm_eq_sSup_unitSphere (s : StrongDual ℝ E₂) :
    ‖s‖ = sSup (s '' sphere (0 : E₂) 1) := by
  classical
  by_cases hE₂ : Subsingleton E₂
  · letI : Subsingleton E₂ := hE₂
    -- In the degenerate branch, the unit sphere is empty and every functional is zero.
    simp [sphere_eq_empty_of_subsingleton one_ne_zero]
  · letI : Nontrivial E₂ := not_subsingleton_iff_nontrivial.mp hE₂
    let S : Set ℝ := s '' sphere (0 : E₂) 1
    have hS_nonempty : S.Nonempty := by
      obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (x := (0 : E₂)) (r := (1 : ℝ)) |>.mpr zero_le_one
      exact ⟨s u, ⟨u, hu, rfl⟩⟩
    have hS_le : ∀ y ∈ S, y ≤ ‖s‖ := by
      intro y hy
      rcases hy with ⟨u, hu, rfl⟩
      have hu_norm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
      -- Every sphere evaluation is bounded by the functional norm.
      calc
        s u ≤ |s u| := le_abs_self _
        _ = ‖s u‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖s‖ * ‖u‖ := s.le_opNorm u
        _ = ‖s‖ := by rw [hu_norm, mul_one]
    have hS_eq : sSup S = ‖s‖ := by
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hS_nonempty hS_le ?_
      intro b hb
      obtain ⟨u, hu, hbu⟩ := strongDual_exists_gt_on_unitSphere (s := s) hb
      exact ⟨s u, ⟨u, hu, rfl⟩, hbu⟩
    simpa [S] using hS_eq.symm

/-- Helper for Definition 6.3: every dual-pairing value over the product of the source and target
unit spheres is bounded above by the operator norm of `A`. -/
lemma dualPairingImage_unitSpheres_bddAbove (A : E₁ →L[ℝ] StrongDual ℝ E₂) :
    BddAbove ((fun xu : E₁ × E₂ ↦ A xu.1 xu.2) ''
      Set.prod (sphere (0 : E₁) 1) (sphere (0 : E₂) 1)) := by
  refine ⟨‖A‖, ?_⟩
  intro r hr
  rcases hr with ⟨⟨x, u⟩, hxu, rfl⟩
  rcases hxu with ⟨hx, hu⟩
  have hx_norm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
  have hu_norm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
  -- First bound the target-side evaluation by the norm of the slice `A x`.
  calc
    A x u ≤ |A x u| := le_abs_self _
    _ = ‖A x u‖ := by rw [Real.norm_eq_abs]
    _ ≤ ‖A x‖ * ‖u‖ := (A x).le_opNorm u
    _ = ‖A x‖ := by rw [hu_norm, mul_one]
    _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
    _ = ‖A‖ := by rw [hx_norm, mul_one]

-- Proof sketch: combine mathlib's one-sphere operator-norm formula for `A` with the chapter's
-- closed-unit-ball dual-norm formula for each `A x`, then pass from closed balls to spheres by
-- radial rescaling and identify the iterated supremum with the supremum over the product of unit
-- spheres.
/-- Companion bridge for Definition 6.3: the canonical operator norm of a dual-valued continuous
linear map is the supremum of the dual pairing over the product of the unit spheres; under the
textbook finite-dimensional hypotheses, this supremum is a maximum. -/
theorem operatorNorm_eq_sSup_dualPairing_unitSpheres (A : E₁ →L[ℝ] StrongDual ℝ E₂) :
    ‖A‖ =
      sSup ((fun xu : E₁ × E₂ ↦ A xu.1 xu.2) ''
        Set.prod (sphere (0 : E₁) 1) (sphere (0 : E₂) 1)) := by
  classical
  by_cases hE₁ : Subsingleton E₁
  · letI : Subsingleton E₁ := hE₁
    have hsphere : sphere (0 : E₁) 1 = (∅ : Set E₁) := sphere_eq_empty_of_subsingleton one_ne_zero
    have hA : A = 0 := by
      ext x
      have hx : x = 0 := Subsingleton.elim _ _
      subst hx
      simp
    -- In the degenerate source branch, both the norm and the product image collapse to zero.
    subst hA
    rw [hsphere]
    have himage :
        ((fun xu : E₁ × E₂ ↦ (0 : E₁ →L[ℝ] StrongDual ℝ E₂) xu.1 xu.2) ''
          (∅ : Set E₁).prod (sphere (0 : E₂) 1)) = (∅ : Set ℝ) := by
      have hprod : (∅ : Set E₁).prod (sphere (0 : E₂) 1) = (∅ : Set (E₁ × E₂)) := by
        ext xu
        constructor
        · intro h
          exact h.1
        · intro h
          cases h
      rw [hprod]
      simp
    rw [himage]
    rw [Real.sSup_empty]
    exact ContinuousLinearMap.opNorm_zero
  · letI : Nontrivial E₁ := not_subsingleton_iff_nontrivial.mp hE₁
    by_cases hE₂ : Subsingleton E₂
    · letI : Subsingleton E₂ := hE₂
      have hsphere : sphere (0 : E₂) 1 = (∅ : Set E₂) := sphere_eq_empty_of_subsingleton one_ne_zero
      have hA : A = 0 := by
        ext x u
        have hu : u = 0 := Subsingleton.elim _ _
        subst hu
        simp
      -- In the degenerate target branch, every dual value is zero and the target sphere is empty.
      subst hA
      rw [hsphere]
      have himage :
          ((fun xu : E₁ × E₂ ↦ (0 : E₁ →L[ℝ] StrongDual ℝ E₂) xu.1 xu.2) ''
            (sphere (0 : E₁) 1).prod (∅ : Set E₂)) = (∅ : Set ℝ) := by
        have hprod : (sphere (0 : E₁) 1).prod (∅ : Set E₂) = (∅ : Set (E₁ × E₂)) := by
          ext xu
          constructor
          · intro h
            exact h.2
          · intro h
            cases h
        rw [hprod]
        simp
      rw [himage]
      rw [Real.sSup_empty]
      exact ContinuousLinearMap.opNorm_zero
    · letI : Nontrivial E₂ := not_subsingleton_iff_nontrivial.mp hE₂
      let S : Set ℝ := ((fun xu : E₁ × E₂ ↦ A xu.1 xu.2) ''
        Set.prod (sphere (0 : E₁) 1) (sphere (0 : E₂) 1))
      have hS_nonempty : S.Nonempty := by
        obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (x := (0 : E₁)) (r := (1 : ℝ)) |>.mpr zero_le_one
        obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (x := (0 : E₂)) (r := (1 : ℝ)) |>.mpr zero_le_one
        exact ⟨A x u, ⟨(x, u), ⟨hx, hu⟩, rfl⟩⟩
      have hS_le : ∀ y ∈ S, y ≤ ‖A‖ := by
        intro y hy
        rcases hy with ⟨⟨x, u⟩, hxu, rfl⟩
        rcases hxu with ⟨hx, hu⟩
        have hx_norm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.1 hx
        have hu_norm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
        -- Bound each product-sphere value by the operator norm of `A`.
        calc
          A x u ≤ |A x u| := le_abs_self _
          _ = ‖A x u‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖A x‖ * ‖u‖ := (A x).le_opNorm u
          _ = ‖A x‖ := by rw [hu_norm, mul_one]
          _ ≤ ‖A‖ * ‖x‖ := A.le_opNorm x
          _ = ‖A‖ := by rw [hx_norm, mul_one]
      have hS_eq : sSup S = ‖A‖ := by
        refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hS_nonempty hS_le ?_
        intro b hb
        by_cases hA0 : ‖A‖ = 0
        · obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (x := (0 : E₁)) (r := (1 : ℝ)) |>.mpr zero_le_one
          obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (x := (0 : E₂)) (r := (1 : ℝ)) |>.mpr zero_le_one
          have hA_zero : A = 0 := (ContinuousLinearMap.opNorm_zero_iff A).mp hA0
          refine ⟨0, ⟨(x, u), ⟨hx, hu⟩, by simp [hA_zero]⟩, ?_⟩
          simpa [hA0] using hb
        · have hnorm_pos : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) fun h ↦ hA0 h.symm
          let r : NNReal := ⟨max b 0, le_max_right _ _⟩
          have hr_lt : (r : ℝ) < ‖A‖ := by
            dsimp [r]
            exact max_lt_iff.mpr ⟨hb, hnorm_pos⟩
          have hr_lt' : r < ‖A‖₊ := by
            exact_mod_cast hr_lt
          obtain ⟨x, hx_nnnorm, hrx⟩ := A.exists_nnnorm_eq_one_lt_apply_of_lt_opNNNorm hr_lt'
          have hx_norm : ‖x‖ = 1 := by
            simpa using congrArg NNReal.toReal hx_nnnorm
          have hx_sphere : x ∈ sphere (0 : E₁) 1 := mem_sphere_zero_iff_norm.mpr hx_norm
          have hrx_real : (r : ℝ) < ‖A x‖ := by
            exact_mod_cast hrx
          -- Use the target-side sphere witness to turn the slice norm gap into a product witness.
          obtain ⟨u, hu, hxu⟩ := strongDual_exists_gt_on_unitSphere (s := A x) hrx_real
          exact ⟨A x u, ⟨(x, u), ⟨hx_sphere, hu⟩, rfl⟩, lt_of_le_of_lt (le_max_left _ _) hxu⟩
      simpa [S] using hS_eq.symm

end
