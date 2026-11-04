/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5

open scoped BigOperators

-- Remark 6.13 adds the gauge reformulation on top of the Chapter 6.2 corner-polyhedron owner
-- API already introduced in `ch6_sec6_2_theorem_6_5`.

noncomputable section

section Remark613

variable {n p k : ℕ}

/-- Helper for Remark 6.13: rewriting the gauge of the translated set
`K := {r : Fin n → ℝ | xbar + r ∈ C}` at a ray gives the infimum over positive inverse
ray-scalings. -/
theorem translated_set_gauge_def_at_ray
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    gauge {r : Fin n → ℝ | xbar + r ∈ C} (rays j) =
      sInf {t : ℝ | 0 < t ∧ xbar + t⁻¹ • rays j ∈ C} := by
  -- The gauge side is exactly Mathlib's scalar-on-the-point infimum formula.
  rw [gauge_def']
  simp

/-- Helper for Remark 6.13: the gauge candidate set obtained from the translated set
`K := {r : Fin n → ℝ | xbar + r ∈ C}` is the pointwise inverse of the positive admissible
ray-parameter set. -/
lemma gaugeCandidateSet_eq_invImage_positiveRayParameters
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    {u : ℝ | 0 < u ∧ xbar + u⁻¹ • rays j ∈ C} =
      Inv.inv '' {t : ℝ | 0 < t ∧ xbar + t • rays j ∈ C} := by
  -- Membership on both sides is the same positive parameter after inverting once.
  ext u
  constructor
  · intro hu
    refine ⟨u⁻¹, ?_, by simp⟩
    simpa [hu.1.ne', inv_inv] using hu
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨ht_pos, ht_mem⟩
    simpa [ht_pos.ne', inv_inv] using And.intro ht_pos ht_mem

/-- Helper for Remark 6.13: inverting a positive real set exchanges its infimum and the reciprocal
of its supremum. In the unbounded case, both sides collapse to `0`. -/
lemma sInf_invImage_eq_inv_sSup_of_positive
    {S : Set ℝ}
    (hSpos : ∀ ⦃t : ℝ⦄, t ∈ S → 0 < t) :
    sInf (Inv.inv '' S) = (sSup S)⁻¹ := by
  by_cases hSempty : S = ∅
  · -- The empty-set case is the default `0 = 0` convention for `ℝ`.
    simp [hSempty, Real.sInf_empty, Real.sSup_empty]
  have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
  by_cases hSbdd : BddAbove S
  · have hInv_bddBelow : BddBelow (Inv.inv '' S) := by
      refine ⟨0, ?_⟩
      rintro y ⟨t, ht, rfl⟩
      exact inv_nonneg.mpr (hSpos ht).le
    have hInv_nonempty : (Inv.inv '' S).Nonempty := by
      rcases hSnonempty with ⟨t, ht⟩
      exact ⟨t⁻¹, ⟨t, ht, rfl⟩⟩
    have hSup_pos : 0 < sSup S := by
      rcases hSnonempty with ⟨t, ht⟩
      exact lt_of_lt_of_le (hSpos ht) (le_csSup hSbdd ht)
    apply le_antisymm
    · -- Any lower bound on the inverse image yields an upper bound on the original set.
      rw [csInf_le_iff hInv_bddBelow hInv_nonempty]
      intro b hb
      by_cases hb_nonpos : b ≤ 0
      · exact hb_nonpos.trans (inv_nonneg.mpr hSup_pos.le)
      · have hb_pos : 0 < b := lt_of_not_ge hb_nonpos
        have hUpper : ∀ t ∈ S, t ≤ b⁻¹ := by
          intro t ht
          exact (le_inv_comm₀ hb_pos (hSpos ht)).1 (hb ⟨t, ht, rfl⟩)
        exact (le_inv_comm₀ hSup_pos hb_pos).1 (csSup_le hSnonempty hUpper)
    · -- The inverse of the supremum is itself a lower bound of the inverse image.
      rw [le_csInf_iff hInv_bddBelow hInv_nonempty]
      intro y hy
      rcases hy with ⟨t, ht, rfl⟩
      exact (inv_le_inv₀ hSup_pos (hSpos ht)).2 (le_csSup hSbdd ht)
  have hInv_bddBelow : BddBelow (Inv.inv '' S) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact inv_nonneg.mpr (hSpos ht).le
  have hInv_nonempty : (Inv.inv '' S).Nonempty := by
    rcases hSnonempty with ⟨t, ht⟩
    exact ⟨t⁻¹, ⟨t, ht, rfl⟩⟩
  have hInf_nonneg : 0 ≤ sInf (Inv.inv '' S) := by
    -- Every inverse image point is nonnegative because the source set is positive.
    exact le_csInf hInv_nonempty fun y hy ↦ by
      rcases hy with ⟨t, ht, rfl⟩
      exact inv_nonneg.mpr (hSpos ht).le
  have hInf_not_pos : ¬ 0 < sInf (Inv.inv '' S) := by
    intro hInf_pos
    have hlarge :
        ∃ t ∈ S, (sInf (Inv.inv '' S))⁻¹ < t := by
      by_contra hcontra
      apply hSbdd
      refine ⟨(sInf (Inv.inv '' S))⁻¹, ?_⟩
      intro t ht
      by_contra ht_bound
      exact hcontra ⟨t, ht, lt_of_not_ge ht_bound⟩
    rcases hlarge with ⟨t, htS, ht_large⟩
    have ht_pos : 0 < t := hSpos htS
    have htInv_lt : t⁻¹ < sInf (Inv.inv '' S) := by
      exact (inv_lt_comm₀ hInf_pos ht_pos).1 ht_large
    exact (not_lt_of_ge (csInf_le hInv_bddBelow ⟨t, htS, rfl⟩)) htInv_lt
  have hSup_zero : sSup S = 0 := by
    simpa [Real.sSup_empty] using (csSup_of_not_bddAbove hSbdd : sSup S = sSup (∅ : Set ℝ))
  have hInf_zero : sInf (Inv.inv '' S) = 0 := by
    exact le_antisymm (le_of_not_gt hInf_not_pos) hInf_nonneg
  rw [hSup_zero]
  simpa [Set.image_inv_eq_inv] using hInf_zero

/-- Helper for Remark 6.13: adding the zero ray-parameter does not change the supremum of the
admissible ray lengths. -/
lemma sSup_nonnegativeRayParameters_eq_sSup_positiveRayParameters
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    sSup {t : ℝ | 0 ≤ t ∧ xbar + t • rays j ∈ C} =
      sSup {t : ℝ | 0 < t ∧ xbar + t • rays j ∈ C} := by
  set A : Set ℝ := {t : ℝ | 0 ≤ t ∧ xbar + t • rays j ∈ C}
  set B : Set ℝ := {t : ℝ | 0 < t ∧ xbar + t • rays j ∈ C}
  by_cases hBbdd : BddAbove B
  · by_cases hBnonempty : B.Nonempty
    · have hAnonempty : A.Nonempty := by
        rcases hBnonempty with ⟨t, ht⟩
        exact ⟨t, ⟨ht.1.le, ht.2⟩⟩
      have hAbdd : BddAbove A := by
        rcases hBbdd with ⟨b, hb⟩
        refine ⟨max 0 b, ?_⟩
        intro t htA
        rcases lt_or_eq_of_le htA.1 with ht_pos | rfl
        · exact (hb ⟨ht_pos, htA.2⟩).trans (le_max_right _ _)
        · exact le_max_left _ _
      apply le_antisymm
      · -- A nonnegative admissible parameter is either positive or equal to `0`.
        refine csSup_le hAnonempty ?_
        intro t htA
        rcases lt_or_eq_of_le htA.1 with ht_pos | rfl
        · exact le_csSup hBbdd ⟨ht_pos, htA.2⟩
        · rcases hBnonempty with ⟨u, hu⟩
          exact le_trans hu.1.le (le_csSup hBbdd hu)
      · -- The positive admissible parameters form a subset of the nonnegative ones.
        refine csSup_le hBnonempty ?_
        intro t ht
        exact le_csSup hAbdd ⟨ht.1.le, ht.2⟩
    · have hBempty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hBnonempty
      by_cases hxbar : xbar ∈ C
      · have hAeq : A = ({0} : Set ℝ) := by
          ext t
          constructor
          · intro htA
            have hnot_pos : ¬ 0 < t := by
              intro ht_pos
              exact hBnonempty ⟨t, ⟨ht_pos, htA.2⟩⟩
            have ht_zero : t = 0 := le_antisymm (le_of_not_gt hnot_pos) htA.1
            simp [ht_zero]
          · intro ht
            simp only [Set.mem_singleton_iff] at ht
            subst ht
            simpa [A] using hxbar
        rw [hAeq, hBempty, csSup_singleton, Real.sSup_empty]
      · have hAeq : A = ∅ := by
          ext t
          constructor
          · intro htA
            have hnot_pos : ¬ 0 < t := by
              intro ht_pos
              exact hBnonempty ⟨t, ⟨ht_pos, htA.2⟩⟩
            have ht_zero : t = 0 := le_antisymm (le_of_not_gt hnot_pos) htA.1
            subst ht_zero
            exact (hxbar (by simpa using htA.2)).elim
          · intro ht
            simp at ht
        simp [hAeq, hBempty, Real.sSup_empty]
  · have hAbdd : ¬ BddAbove A := by
      intro hA
      rcases hA with ⟨a, ha⟩
      exact hBbdd ⟨a, fun t ht ↦ ha ⟨ht.1.le, ht.2⟩⟩
    -- If the positive set is unbounded above, adjoining `0` keeps the set unbounded.
    simp [csSup_of_not_bddAbove hAbdd, csSup_of_not_bddAbove hBbdd]

/-- Helper for Remark 6.13: the intersection-cut coefficient is the reciprocal of the supremum of
the positive admissible ray parameters. -/
lemma intersectionCutCoeff_eq_inv_sSup_positiveRayParameters
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    IntersectionCut.intersection_cut_coeff C xbar rays j =
      (sSup {t : ℝ | 0 < t ∧ xbar + t • rays j ∈ C})⁻¹ := by
  -- First convert the ENNReal supremum defining the coefficient back to a real supremum.
  have hfinite :
      ∀ r ∈ ENNReal.ofReal '' IntersectionCut.ray_admissible_parameters C xbar rays j, r ≠ ⊤ := by
    intro r hr
    rcases hr with ⟨t, ht, rfl⟩
    exact ENNReal.ofReal_ne_top
  rw [IntersectionCut.intersection_cut_coeff_eq_inv_ray_intersection_parameter,
    IntersectionCut.ray_intersection_parameter_def, ENNReal.toReal_sSup _ hfinite]
  have himage :
      ENNReal.toReal ''
          (ENNReal.ofReal '' IntersectionCut.ray_admissible_parameters C xbar rays j) =
        IntersectionCut.ray_admissible_parameters C xbar rays j := by
    -- The admissible parameters are already nonnegative, so `toReal ∘ ofReal` is identity.
    ext t
    constructor
    · rintro ⟨u, ⟨s, hs, rfl⟩, rfl⟩
      rcases hs with ⟨hs_nonneg, hs_mem⟩
      simp [IntersectionCut.ray_admissible_parameters, hs_nonneg, hs_mem]
    · intro ht
      have ht_nonneg : 0 ≤ t := ht.1
      refine ⟨ENNReal.ofReal t, ⟨t, ht, rfl⟩, ?_⟩
      simp [ht_nonneg]
  rw [himage]
  congr 1
  simpa [IntersectionCut.ray_admissible_parameters] using
    sSup_nonnegativeRayParameters_eq_sSup_positiveRayParameters C xbar rays j

/-- Remark 6.13. The coefficient of the intersection cut along the ray `rays j` is precisely the
gauge of the translated set `K := {r : Fin n → ℝ | xbar + r ∈ C} = C - xbar` evaluated at that
ray. -/
theorem intersection_cut_coeff_eq_gauge_translated_set
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k) :
    IntersectionCut.intersection_cut_coeff C xbar rays j =
      gauge {r : Fin n → ℝ | xbar + r ∈ C} (rays j) := by
  have hPos :
      ∀ ⦃t : ℝ⦄, t ∈ {t : ℝ | 0 < t ∧ xbar + t • rays j ∈ C} → 0 < t := by
    intro t ht
    exact ht.1
  -- Rewrite both sides to the same inverse-of-supremum normal form along the chosen ray.
  rw [translated_set_gauge_def_at_ray, gaugeCandidateSet_eq_invImage_positiveRayParameters,
    sInf_invImage_eq_inv_sSup_of_positive hPos]
  -- The coefficient owner already computes this reciprocal supremum.
  exact intersectionCutCoeff_eq_inv_sSup_positiveRayParameters C xbar rays j

/-- Rewriting the intersection-cut coefficients by Remark 6.13 yields the canonical valid lower
inequality on the corner polyhedron whose coefficient vector is `j ↦ γ_K(r̄^j)`, with `Fin k`
enumerating the ray index set `N`. -/
theorem gauge_intersection_cut_inequality
    (hpn : p ≤ n)
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C)
    (hxbar_mem : xbar ∈ interior C)
    (hC_lattice_free : Disjoint (interior C) (mixed_integer_prefix_lattice hpn)) :
    ∀ ⦃coeffs : Fin k → ℝ⦄,
      coeffs ∈ IntersectionCut.corner_polyhedron hpn xbar rays →
        1 ≤ (fun j ↦ gauge {r : Fin n → ℝ | xbar + r ∈ C} (rays j)) ⬝ᵥ coeffs := by
  intro coeffs hcoeffs
  have hGauge :
      IntersectionCut.intersection_cut_coeff C xbar rays =
        fun j ↦ gauge {r : Fin n → ℝ | xbar + r ∈ C} (rays j) := by
    -- The coefficient vector agrees pointwise with the translated-set gauge.
    funext j
    exact intersection_cut_coeff_eq_gauge_translated_set C xbar rays j
  -- The geometric work is already done by Theorem 6.5; only the coefficient rewrite remains.
  simpa [hGauge] using
    (IntersectionCut.intersection_cut_valid_for_corner_polyhedron
      hpn C xbar rays hC_closed hC_convex hxbar_mem hC_lattice_free hcoeffs)

end Remark613
