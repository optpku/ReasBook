/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_1.ch6_sec6_1_lemma_6_4.Inequalities
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2.ch6_sec6_2_theorem_6_12.RaySeparation

open IntersectionCut
open scoped BigOperators Matrix

-- This theorem extends the Section 6.2 corner/intersection-cut owner API from
-- `ch6_sec6_2_theorem_6_5` by adding the Theorem 6.12 source-facing notions while reusing the
-- current import path's equality-face owner `face_set` and the Chapter 3
-- `facet_defining_inequality` owner.

noncomputable section

section Theorem612

variable {n p k : ℕ}

/-- The equality face of the lower inequality `δ ≤ γ ⬝ᵥ x` is the same as the equality face of
the canonical valid-inequality owner `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem face_set_neg_eq
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    face_set P (-γ) (-δ) = face_set P γ δ := by
  ext x
  simp [mem_face_set_iff]

/-- A lower inequality `δ ≤ γ ⬝ᵥ x` is a nontrivial facet-defining inequality for `P` when the
equivalent Chapter 3 inequality `(-γ) ⬝ᵥ x ≤ -δ` is facet-defining and the original lower
inequality does not already hold on the whole nonnegative orthant. -/
def IsNontrivialFacetDefiningGeInequality
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) : Prop :=
  facet_defining_inequality P (-γ) (-δ) ∧
    ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x

/-- `IsNontrivialFacetDefiningGeInequality P γ δ` unfolds to the canonical facet-defining owner for
`(-γ) ⬝ᵥ x ≤ -δ`, together with failure of `δ ≤ γ ⬝ᵥ x` on the whole nonnegative orthant. -/
theorem isNontrivialFacetDefiningGeInequality_iff
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsNontrivialFacetDefiningGeInequality P γ δ ↔
      facet_defining_inequality P (-γ) (-δ) ∧
        ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  Iff.rfl

/-- A nontrivial facet-defining lower inequality is equivalently a nontrivial valid lower
inequality together with the canonical Chapter 3 facet-defining owner for `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem isNontrivialFacetDefiningGeInequality_iff_isNontrivialValidGeInequality
    (P : Set (Fin k → ℝ))
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsNontrivialFacetDefiningGeInequality P γ δ ↔
      facet_defining_inequality P (-γ) (-δ) ∧
        IsNontrivialValidGeInequality P γ δ := by
  rw [isNontrivialFacetDefiningGeInequality_iff,
    isNontrivialValidGeInequality_iff_is_valid_inequality_neg]
  constructor
  · rintro ⟨hfacet, hnontrivial⟩
    exact ⟨hfacet, facet_defining_inequality_valid hfacet, hnontrivial⟩
  · rintro ⟨hfacet, hvalid, hnontrivial⟩
    exact ⟨hfacet, hnontrivial⟩

namespace IsNontrivialFacetDefiningGeInequality

/-- A nontrivial facet-defining lower inequality is, in particular, nontrivially valid. -/
theorem nontrivialValid
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    IsNontrivialValidGeInequality P γ δ :=
  (isNontrivialFacetDefiningGeInequality_iff_isNontrivialValidGeInequality P γ δ).mp h |>.2

/-- The canonical Chapter 3 facet-defining owner attached to a nontrivial facet-defining lower
inequality. -/
theorem facetDefiningNeg
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    facet_defining_inequality P (-γ) (-δ) :=
  h.1

/-- A nontrivial facet-defining lower inequality does not already hold on the whole nonnegative
orthant. -/
theorem not_validOnNonnegativeOrthant
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    ¬ ∀ x : Fin k → ℝ, (∀ j : Fin k, 0 ≤ x j) → δ ≤ γ ⬝ᵥ x :=
  h.2

/-- A nontrivial facet-defining lower inequality yields the canonical Chapter 3 valid-inequality
owner for `(-γ) ⬝ᵥ x ≤ -δ`. -/
theorem isValidInequalityNeg
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    is_valid_inequality P (-γ) (-δ) :=
  facet_defining_inequality_valid h.facetDefiningNeg

/-- The equality face of a nontrivial facet-defining lower inequality is a Chapter 3 facet in the
`is_facet` sense. -/
theorem isFacet
    {P : Set (Fin k → ℝ)}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsNontrivialFacetDefiningGeInequality P γ δ) :
    is_facet P (face_set P γ δ) := by
  simpa [face_set_neg_eq] using facet_defining_inequality_is_facet h.facetDefiningNeg

end IsNontrivialFacetDefiningGeInequality

/-- An inequality `γ ⬝ᵥ x ≥ δ` for `corner(B)` is an intersection cut when `δ > 0` and, after
normalizing the right-hand side to `1`, its coefficient vector is the intersection-cut
coefficient vector of some closed convex `ℤ^p × ℝ^(n - p)`-free set containing the apex in its
interior. -/
def IsIntersectionCutInequality
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ) : Prop :=
  0 < δ ∧
    ∃ C : Set (Fin n → ℝ),
      IsClosed C ∧
        Convex ℝ C ∧
          xbar ∈ interior C ∧
            Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
              γ = δ • intersection_cut_coeff C xbar rays

/-- `IsIntersectionCutInequality hpn xbar rays γ δ` unfolds to a positive right-hand side and a
closed convex lattice-free set whose intersection-cut coefficients, scaled by `δ`, give `γ`. -/
theorem isIntersectionCutInequality_iff
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ) :
    IsIntersectionCutInequality hpn xbar rays γ δ ↔
      0 < δ ∧
        ∃ C : Set (Fin n → ℝ),
          IsClosed C ∧
            Convex ℝ C ∧
              xbar ∈ interior C ∧
                Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
                  γ = δ • intersection_cut_coeff C xbar rays :=
  Iff.rfl

namespace IsIntersectionCutInequality

/-- An intersection cut has positive right-hand side. -/
theorem rhs_pos
    {hpn : p ≤ n}
    {xbar : Fin n → ℝ}
    {rays : Fin k → Fin n → ℝ}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsIntersectionCutInequality hpn xbar rays γ δ) :
    0 < δ :=
  h.1

/-- An intersection cut comes from a closed convex `ℤ^p × ℝ^(n - p)`-free set containing the apex
in its interior. -/
theorem exists_closed_convexSet
    {hpn : p ≤ n}
    {xbar : Fin n → ℝ}
    {rays : Fin k → Fin n → ℝ}
    {γ : Fin k → ℝ}
    {δ : ℝ}
    (h : IsIntersectionCutInequality hpn xbar rays γ δ) :
    ∃ C : Set (Fin n → ℝ),
      IsClosed C ∧
        Convex ℝ C ∧
          xbar ∈ interior C ∧
            Disjoint (interior C) (mixed_integer_prefix_lattice hpn) ∧
              γ = δ • intersection_cut_coeff C xbar rays :=
  h.2

end IsIntersectionCutInequality

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: the rays of the source-facing
`corner(B)` has positive lattice periods when each ray can be scaled by some positive real
number into `ℤ^p × ℝ^(n - p)`. This is the abstract form of the denominator-clearing property
used for rational tableau rays in Lemma 6.4. -/
def HasPositiveLatticePeriods
    (hpn : p ≤ n)
    (rays : Fin k → Fin n → ℝ) : Prop :=
  ∀ j : Fin k, ∃ t : ℝ, 0 < t ∧ t • rays j ∈ mixed_integer_prefix_lattice hpn

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean:
`HasPositiveLatticePeriods hpn rays` unfolds to positivity and lattice membership of a scaling
factor for each ray. -/
theorem hasPositiveLatticePeriods_iff
    (hpn : p ≤ n)
    (rays : Fin k → Fin n → ℝ) :
    HasPositiveLatticePeriods hpn rays ↔
      ∀ j : Fin k, ∃ t : ℝ, 0 < t ∧ t • rays j ∈ mixed_integer_prefix_lattice hpn :=
  Iff.rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: adding a natural multiple of a
positive lattice period in one ray coordinate preserves membership in the corner polyhedron. -/
private lemma cornerPolyhedron_addNatPeriodSingle
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    {s : Fin k → ℝ}
    (hs : s ∈ corner_polyhedron hpn xbar rays)
    (j : Fin k)
    (t : ℝ)
    (ht : 0 < t)
    (htlattice : t • rays j ∈ mixed_integer_prefix_lattice hpn)
    (m : ℕ) :
    s + ((m : ℝ) * t) • Pi.single j (1 : ℝ) ∈
      corner_polyhedron hpn xbar rays := by
  classical
  rw [mem_corner_polyhedron_iff] at hs ⊢
  constructor
  · -- The translated coefficient vector remains coordinatewise nonnegative.
    intro i
    by_cases hij : i = j
    · subst i
      simpa [Pi.single_apply] using
        add_nonneg (hs.1 j) (mul_nonneg (Nat.cast_nonneg m) ht.le)
    · simpa [Pi.single_apply, hij] using hs.1 i
  · -- Its ambient point differs from the original one by an integral multiple of a lattice
    -- period, so every constrained coordinate remains integral.
    have hcornerShift :
        corner_point xbar rays (s + ((m : ℝ) * t) • Pi.single j (1 : ℝ)) =
          corner_point xbar rays s + (m : ℝ) • (t • rays j) := by
      ext q
      have hsum :
          ∑ x : Fin k, (((m : ℝ) * t) * (Pi.single j (1 : ℝ) : Fin k → ℝ) x) * rays x q =
            (m : ℝ) * (t * rays j q) := by
        rw [Finset.sum_eq_single j]
        · simp [mul_assoc]
        · intro i hi hij
          simp [hij]
        · simp
      simp only [corner_point_def, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        add_mul, Finset.sum_add_distrib]
      rw [hsum]
      ring
    rw [mem_mixed_integer_prefix_lattice_iff] at hs htlattice ⊢
    intro i
    rcases hs.2 i with ⟨z, hz⟩
    rcases htlattice i with ⟨w, hw⟩
    refine ⟨z + (m : ℤ) * w, ?_⟩
    rw [hcornerShift]
    simp [hz, hw]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: a nontrivial facet inequality
with positive lattice periods has positive right-hand side and a nonnegative normalized valid
coefficient vector. -/
private lemma normalizedDataOfNontrivialFacetWithPeriods
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ)
    (hperiods : HasPositiveLatticePeriods hpn rays)
    (hfacet :
      IsNontrivialFacetDefiningGeInequality (corner_polyhedron hpn xbar rays) γ δ) :
    0 < δ ∧
      (∀ j : Fin k, 0 ≤ (δ⁻¹ • γ) j) ∧
        ∀ ⦃s : Fin k → ℝ⦄,
          s ∈ corner_polyhedron hpn xbar rays → 1 ≤ (δ⁻¹ • γ) ⬝ᵥ s := by
  classical
  have hP_nonempty : (corner_polyhedron hpn xbar rays).Nonempty := by
    -- A facet is a nonempty proper face, hence its ambient corner set is nonempty.
    rcases (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet.isFacet)).2.1 with
      ⟨s, hsface⟩
    exact ⟨s, hsface.1⟩
  have hγ_nonneg : ∀ j : Fin k, 0 ≤ γ j := by
    intro j
    by_contra hj
    have hγj_neg : γ j < 0 := lt_of_not_ge hj
    rcases hP_nonempty with ⟨s, hs⟩
    rcases hperiods j with ⟨t, ht, htlattice⟩
    have hden_pos : 0 < -(t * γ j) := by
      exact neg_pos.mpr (mul_neg_of_pos_of_neg ht hγj_neg)
    rcases exists_nat_gt ((γ ⬝ᵥ s - δ) / (-(t * γ j))) with ⟨m, hm⟩
    have hm_mul : γ ⬝ᵥ s - δ < (m : ℝ) * (-(t * γ j)) := by
      exact (div_lt_iff₀ hden_pos).mp hm
    have hshift_mem :=
      cornerPolyhedron_addNatPeriodSingle hpn xbar rays hs j t ht htlattice m
    have hshift_valid := hfacet.nontrivialValid.valid hshift_mem
    have hshift_value :
        γ ⬝ᵥ (s + ((m : ℝ) * t) • Pi.single j (1 : ℝ)) =
          γ ⬝ᵥ s + (m : ℝ) * t * γ j := by
      rw [dotProduct_add, dotProduct_smul, dotProduct_single_one]
      ring
    rw [hshift_value] at hshift_valid
    nlinarith
  have hδ_pos : 0 < δ := by
    -- Otherwise nonnegative coefficients make the inequality valid on the whole orthant.
    by_contra hδ
    have hδ_nonpos : δ ≤ 0 := le_of_not_gt hδ
    apply hfacet.not_validOnNonnegativeOrthant
    intro s hs_nonneg
    exact hδ_nonpos.trans (dotProduct_nonneg_of_nonneg hγ_nonneg hs_nonneg)
  refine ⟨hδ_pos, ?_, ?_⟩
  · -- Positive inverse scaling preserves coefficientwise nonnegativity.
    intro j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hδ_pos.le) (hγ_nonneg j)
  · intro s hs
    -- Scale the original valid inequality by `δ⁻¹` to normalize its right-hand side to one.
    have hscaled :=
      mul_le_mul_of_nonneg_left (hfacet.nontrivialValid.valid hs) (inv_nonneg.mpr hδ_pos.le)
    simpa [smul_dotProduct, ne_of_gt hδ_pos] using hscaled

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: moving along one coefficient
axis realizes the corresponding ambient ray. -/
private lemma cornerPoint_smul_single
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (j : Fin k)
    (t : ℝ) :
    corner_point xbar rays (t • Pi.single j (1 : ℝ)) = xbar + t • rays j := by
  classical
  -- Collapse the finite ray sum to its unique nonzero coordinate.
  rw [corner_point_def]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i hi hij
    simp [hij]
  · simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: if a closed-set candidate
contains every ray combination in a nonnegative coefficient sublevel, then each of its
intersection-cut coefficients is bounded by the corresponding sublevel coefficient. -/
private lemma intersectionCutCoeff_le_of_raySublevel_mem
    (C : Set (Fin n → ℝ))
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (a : Fin k → ℝ)
    (ha : ∀ j : Fin k, 0 ≤ a j)
    (hsublevel :
      ∀ (s : Fin k → ℝ),
        (∀ i : Fin k, 0 ≤ s i) →
          a ⬝ᵥ s ≤ 1 →
            corner_point xbar rays s ∈ C)
    (j : Fin k) :
    intersection_cut_coeff C xbar rays j ≤ a j := by
  classical
  by_cases haj_zero : a j = 0
  · -- A zero coefficient makes the entire nonnegative ray admissible, hence its parameter is
    -- infinite and the associated cut coefficient is zero.
    have hparameter_top : ray_intersection_parameter C xbar rays j = ⊤ := by
      rw [ray_intersection_parameter_def, sSup_eq_top]
      intro b hb
      have hbtop : b ≠ ⊤ := lt_top_iff_ne_top.mp hb
      have ht_nonneg : 0 ≤ b.toReal + 1 := by
        exact add_nonneg ENNReal.toReal_nonneg zero_le_one
      have ht_pos : 0 < b.toReal + 1 := by
        linarith [ENNReal.toReal_nonneg (a := b)]
      refine ⟨ENNReal.ofReal (b.toReal + 1), ?_, ?_⟩
      · refine ⟨b.toReal + 1, ⟨ht_nonneg, ?_⟩, rfl⟩
        rw [← cornerPoint_smul_single xbar rays j]
        apply hsublevel
        · intro i
          by_cases hij : i = j
          · subst i
            simpa using ht_nonneg
          · simp [hij]
        · rw [dotProduct_smul, dotProduct_single_one, haj_zero]
          simp
      · have hb_eq : b = ENNReal.ofReal b.toReal := by
          symm
          exact ENNReal.ofReal_toReal hbtop
        calc
          b = ENNReal.ofReal b.toReal := hb_eq
          _ < ENNReal.ofReal (b.toReal + 1) :=
            (ENNReal.ofReal_lt_ofReal_iff ht_pos).2 (by linarith)
    rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter, hparameter_top, haj_zero]
    simp
  · -- For a positive coefficient, the reciprocal coefficient length is an admissible endpoint.
    have haj_pos : 0 < a j := lt_of_le_of_ne (ha j) (Ne.symm haj_zero)
    let t : ℝ := (a j)⁻¹
    have ht_nonneg : 0 ≤ t := inv_nonneg.mpr haj_pos.le
    have ht_pos : 0 < t := inv_pos.mpr haj_pos
    have ht_admissible : t ∈ ray_admissible_parameters C xbar rays j := by
      refine ⟨ht_nonneg, ?_⟩
      rw [← cornerPoint_smul_single xbar rays j]
      apply hsublevel
      · intro i
        by_cases hij : i = j
        · subst i
          simpa [t] using ht_nonneg
        · simp [hij]
      · rw [dotProduct_smul, dotProduct_single_one]
        simp [t, haj_zero]
    have hparameter_lower :
        ENNReal.ofReal t ≤ ray_intersection_parameter C xbar rays j := by
      rw [ray_intersection_parameter_def]
      exact le_sSup ⟨t, ht_admissible, rfl⟩
    by_cases hparameter_top : ray_intersection_parameter C xbar rays j = ⊤
    · rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter, hparameter_top]
      simp [ha j]
    · have htoReal_lower :
          t ≤ (ray_intersection_parameter C xbar rays j).toReal := by
        calc
          t = (ENNReal.ofReal t).toReal := by simp [ht_nonneg]
          _ ≤ (ray_intersection_parameter C xbar rays j).toReal :=
            ENNReal.toReal_mono hparameter_top hparameter_lower
      have htoReal_pos :
          0 < (ray_intersection_parameter C xbar rays j).toReal :=
        ht_pos.trans_le htoReal_lower
      rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter]
      calc
        (ray_intersection_parameter C xbar rays j).toReal⁻¹ ≤ t⁻¹ := by
          rw [inv_le_inv₀ htoReal_pos ht_pos]
          exact htoReal_lower
        _ = a j := by simp [t]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean: two normalized nonnegative
valid lower inequalities agree when the first defines a facet, the second is componentwise
smaller, and every coordinate direction has a positive lattice period. -/
private lemma normalizedFacet_eq_of_valid_le
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (hperiods : HasPositiveLatticePeriods hpn rays)
    (a b : Fin k → ℝ)
    (hb_nonneg : ∀ j : Fin k, 0 ≤ b j)
    (hb_valid :
      ∀ ⦃s : Fin k → ℝ⦄,
        s ∈ corner_polyhedron hpn xbar rays → 1 ≤ b ⬝ᵥ s)
    (ha_facet :
      is_facet
        (corner_polyhedron hpn xbar rays)
        (face_set (corner_polyhedron hpn xbar rays) a 1))
    (hba : ∀ j : Fin k, b j ≤ a j) :
    a = b := by
  classical
  let P := corner_polyhedron hpn xbar rays
  let Fa := face_set P a 1
  let Fb := face_set P b 1
  have hFa_nonempty : Fa.Nonempty :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face ha_facet)).2.1
  have hFa_subset_Fb : Fa ⊆ Fb := by
    -- On a nonnegative facet point, coefficientwise domination and validity squeeze the second
    -- dot product to the same normalized value.
    intro s hsFa
    rw [mem_face_set_iff] at hsFa ⊢
    have hs_nonneg : ∀ i : Fin k, 0 ≤ s i :=
      (mem_corner_polyhedron_iff hpn xbar rays s).mp hsFa.1 |>.1
    have hdot_le : b ⬝ᵥ s ≤ a ⬝ᵥ s :=
      dotProduct_le_dotProduct_of_nonneg_right hba hs_nonneg
    exact ⟨hsFa.1, le_antisymm (hsFa.2 ▸ hdot_le) (hb_valid hsFa.1)⟩
  have hFb_proper : is_proper_face P Fb := by
    have hb_valid_neg : is_valid_inequality P (-b) (-1) :=
      valid_ge_inequality_iff_is_valid_inequality_neg.mp hb_valid
    have hFb_exposed : IsExposed ℝ P Fb := by
      simpa [Fb, face_set_neg_eq] using
        isExposed_face_set_of_valid_inequality hb_valid_neg
    have hFb_nonempty : Fb.Nonempty := hFa_nonempty.mono hFa_subset_Fb
    refine (is_proper_face_iff.mpr ⟨hFb_exposed, hFb_nonempty, ?_⟩)
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro s hs
      exact (mem_face_set_iff.mp hs).1
    · intro hFb_eq
      rcases hFa_nonempty with ⟨s, hsFa⟩
      have hsFb : s ∈ Fb := hFa_subset_Fb hsFa
      have hsP : s ∈ P := (mem_face_set_iff.mp hsFb).1
      have hb_dot : b ⬝ᵥ s = 1 := (mem_face_set_iff.mp hsFb).2
      have hb_ne : b ≠ 0 := by
        intro hb_zero
        rw [hb_zero, zero_dotProduct] at hb_dot
        norm_num at hb_dot
      have hexists_bpos : ∃ j : Fin k, 0 < b j := by
        by_contra hnot
        push Not at hnot
        apply hb_ne
        funext j
        exact le_antisymm (hnot j) (hb_nonneg j)
      rcases hexists_bpos with ⟨j, hbj_pos⟩
      rcases hperiods j with ⟨t, ht, htlattice⟩
      have hshiftP : s + t • Pi.single j (1 : ℝ) ∈ P := by
        simpa [P] using
          cornerPolyhedron_addNatPeriodSingle hpn xbar rays hsP j t ht htlattice 1
      have hshiftFb : s + t • Pi.single j (1 : ℝ) ∈ Fb := by
        rw [hFb_eq]
        exact hshiftP
      have hshift_dot : b ⬝ᵥ (s + t • Pi.single j (1 : ℝ)) = 1 :=
        (mem_face_set_iff.mp hshiftFb).2
      rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, hb_dot] at hshift_dot
      simp only [smul_eq_mul] at hshift_dot
      nlinarith
  have hfaces_eq : Fb = Fa :=
    is_facet_maximal ha_facet hFb_proper hFa_subset_Fb
  by_contra hab_ne
  have hstrict : ∃ j : Fin k, b j < a j := by
    by_contra hnot
    push Not at hnot
    apply hab_ne
    funext j
    exact le_antisymm (hnot j) (hba j)
  rcases hstrict with ⟨j, hj_strict⟩
  let Gj := face_set P (Pi.single j (1 : ℝ)) 0
  have hFa_subset_Gj : Fa ⊆ Gj := by
    -- Equality of both normalized dot products makes every nonnegative gap term vanish; the
    -- strict gap at `j` therefore forces the `j`th coordinate to vanish on the facet.
    intro s hsFa
    have hsFb : s ∈ Fb := hFa_subset_Fb hsFa
    have hsP : s ∈ P := (mem_face_set_iff.mp hsFa).1
    have hs_nonneg : ∀ i : Fin k, 0 ≤ s i :=
      (mem_corner_polyhedron_iff hpn xbar rays s).mp hsP |>.1
    have ha_dot : a ⬝ᵥ s = 1 := (mem_face_set_iff.mp hsFa).2
    have hb_dot : b ⬝ᵥ s = 1 := (mem_face_set_iff.mp hsFb).2
    have hgap_nonneg :
        ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ (a i - b i) * s i := by
      intro i hi
      exact mul_nonneg (sub_nonneg.mpr (hba i)) (hs_nonneg i)
    have hgap_sum : ∑ i : Fin k, (a i - b i) * s i = 0 := by
      calc
        ∑ i : Fin k, (a i - b i) * s i = a ⬝ᵥ s - b ⬝ᵥ s := by
          simp only [dotProduct]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := by rw [ha_dot, hb_dot]; ring
    have hj_term_zero : (a j - b j) * s j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hgap_nonneg).mp hgap_sum j (Finset.mem_univ j)
    have hsj_zero : s j = 0 := by
      exact (mul_eq_zero.mp hj_term_zero).resolve_left (sub_ne_zero.mpr (ne_of_gt hj_strict))
    rw [mem_face_set_iff]
    refine ⟨hsP, ?_⟩
    simp [dotProduct, Pi.single_apply, hsj_zero]
  have hGj_proper : is_proper_face P Gj := by
    have hcoordinate_valid :
        ∀ ⦃s : Fin k → ℝ⦄, s ∈ P → 0 ≤ (Pi.single j (1 : ℝ)) ⬝ᵥ s := by
      intro s hsP
      have hs_nonneg : ∀ i : Fin k, 0 ≤ s i :=
        (mem_corner_polyhedron_iff hpn xbar rays s).mp hsP |>.1
      simpa [dotProduct, Pi.single_apply] using hs_nonneg j
    have hcoordinate_valid_neg :
        is_valid_inequality P (-Pi.single j (1 : ℝ)) 0 := by
      simpa using valid_ge_inequality_iff_is_valid_inequality_neg.mp hcoordinate_valid
    have hGj_exposed : IsExposed ℝ P Gj := by
      -- Unfold the local face name before transporting it to the canonical upper inequality.
      dsimp only [Gj]
      rw [← face_set_neg_eq P (Pi.single j (1 : ℝ)) 0]
      simpa using isExposed_face_set_of_valid_inequality hcoordinate_valid_neg
    have hGj_nonempty : Gj.Nonempty := hFa_nonempty.mono hFa_subset_Gj
    refine is_proper_face_iff.mpr ⟨hGj_exposed, hGj_nonempty, ?_⟩
    refine Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · intro s hsGj
      exact (mem_face_set_iff.mp hsGj).1
    · intro hGj_eq
      rcases hFa_nonempty with ⟨s, hsFa⟩
      have hsGj : s ∈ Gj := hFa_subset_Gj hsFa
      have hsP : s ∈ P := (mem_face_set_iff.mp hsGj).1
      have hsj_zero : s j = 0 := by
        have := (mem_face_set_iff.mp hsGj).2
        simpa [dotProduct, Pi.single_apply] using this
      rcases hperiods j with ⟨t, ht, htlattice⟩
      have hshiftP : s + t • Pi.single j (1 : ℝ) ∈ P := by
        simpa [P] using
          cornerPolyhedron_addNatPeriodSingle hpn xbar rays hsP j t ht htlattice 1
      have hshiftGj : s + t • Pi.single j (1 : ℝ) ∈ Gj := by
        rw [hGj_eq]
        exact hshiftP
      have hshift_zero := (mem_face_set_iff.mp hshiftGj).2
      simp [dotProduct, Pi.single_apply, hsj_zero] at hshift_zero
      linarith
  have hGj_eq_Fa : Gj = Fa :=
    is_facet_maximal ha_facet hGj_proper hFa_subset_Gj
  rcases hFa_nonempty with ⟨s, hsFa⟩
  have hsGj : s ∈ Gj := hFa_subset_Gj hsFa
  have hsP : s ∈ P := (mem_face_set_iff.mp hsFa).1
  have hsFa_dot : a ⬝ᵥ s = 1 := (mem_face_set_iff.mp hsFa).2
  have hsj_zero : s j = 0 := by
    have := (mem_face_set_iff.mp hsGj).2
    simpa [dotProduct, Pi.single_apply] using this
  have hai_zero : ∀ i : Fin k, i ≠ j → a i = 0 := by
    intro i hij
    rcases hperiods i with ⟨t, ht, htlattice⟩
    have hshiftP : s + t • Pi.single i (1 : ℝ) ∈ P := by
      simpa [P] using
        cornerPolyhedron_addNatPeriodSingle hpn xbar rays hsP i t ht htlattice 1
    have hshiftGj : s + t • Pi.single i (1 : ℝ) ∈ Gj := by
      rw [mem_face_set_iff]
      refine ⟨hshiftP, ?_⟩
      simp [dotProduct, Pi.single_apply, Ne.symm hij, hsj_zero]
    have hshiftFa : s + t • Pi.single i (1 : ℝ) ∈ Fa := by
      rw [← hGj_eq_Fa]
      exact hshiftGj
    have hshift_dot : a ⬝ᵥ (s + t • Pi.single i (1 : ℝ)) = 1 :=
      (mem_face_set_iff.mp hshiftFa).2
    rw [dotProduct_add, dotProduct_smul, dotProduct_single_one, hsFa_dot] at hshift_dot
    simp only [smul_eq_mul] at hshift_dot
    nlinarith
  have ha_dot_zero : a ⬝ᵥ s = 0 := by
    simp only [dotProduct]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hij : i = j
    · subst i
      simp [hsj_zero]
    · simp [hai_zero i hij]
  linarith

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_2/ch6_sec6_2_theorem_6_12.lean

Theorem 6.12. For a source-faithful `corner(B)` whose rays have positive lattice periods,
recorded in Lean by the premise `HasPositiveLatticePeriods hpn rays`, every nontrivial
facet-defining inequality is an intersection cut. Concretely, after normalizing the right-hand
side to `1`, the coefficient vector comes from the intersection-cut coefficients of a closed
convex `ℤ^p × ℝ^(n - p)`-free set containing the apex in its interior. -/
theorem nontrivial_facet_defining_inequality_is_intersection_cut
    (hpn : p ≤ n)
    (xbar : Fin n → ℝ)
    (rays : Fin k → Fin n → ℝ)
    (γ : Fin k → ℝ)
    (δ : ℝ)
    (hperiods : HasPositiveLatticePeriods hpn rays)
    (hfacet :
      IsNontrivialFacetDefiningGeInequality (corner_polyhedron hpn xbar rays) γ δ) :
    IsIntersectionCutInequality hpn xbar rays γ δ := by
  classical
  -- Normalize the facet inequality, retaining positivity, nonnegativity, and validity.
  rcases normalizedDataOfNontrivialFacetWithPeriods
      hpn xbar rays γ δ hperiods hfacet with
    ⟨hδ_pos, ha_nonneg, ha_valid⟩
  let a : Fin k → ℝ := δ⁻¹ • γ
  have ha_nonneg' : 0 ≤ a := by
    simpa [a] using ha_nonneg
  have ha_valid' :
      ∀ ⦃s : Fin k → ℝ⦄,
        s ∈ corner_polyhedron hpn xbar rays → 1 ≤ a ⬝ᵥ s := by
    intro s hs
    simpa [a] using ha_valid hs
  have hperiods_facet := hperiods
  choose t ht_pos ht_lattice using hperiods
  obtain ⟨κ, hκ_pos, hseparate⟩ :=
    existsPeriodicPrefixSlackBound
      hpn xbar rays t ht_pos ht_lattice a ha_nonneg' ha_valid'
  let C : Set (Fin n → ℝ) := closure (periodicPrefixTube hpn xbar rays a κ)
  obtain ⟨hC_closed, hC_convex, hxbar_interior, hC_free, hsublevel⟩ :=
    closedPeriodicPrefixTubeWitness
      hpn xbar rays a κ hκ_pos ha_nonneg' hseparate
  have hb_nonneg : ∀ j : Fin k, 0 ≤ intersection_cut_coeff C xbar rays j := by
    intro j
    rw [intersection_cut_coeff_eq_inv_ray_intersection_parameter]
    exact inv_nonneg.mpr ENNReal.toReal_nonneg
  have hb_valid :
      ∀ ⦃s : Fin k → ℝ⦄,
        s ∈ corner_polyhedron hpn xbar rays →
          1 ≤ intersection_cut_coeff C xbar rays ⬝ᵥ s :=
    intersection_cut_valid_for_corner_polyhedron
      hpn C xbar rays hC_closed hC_convex hxbar_interior hC_free
  have hb_le_a : ∀ j : Fin k, intersection_cut_coeff C xbar rays j ≤ a j := by
    -- The tube closure contains the whole normalized coefficient sublevel, giving the reverse
    -- coefficient comparison needed for facet rigidity.
    exact intersectionCutCoeff_le_of_raySublevel_mem
      C xbar rays a ha_nonneg' hsublevel
  have ha_facet :
      is_facet
        (corner_polyhedron hpn xbar rays)
        (face_set (corner_polyhedron hpn xbar rays) a 1) := by
    have hfaces :
        face_set (corner_polyhedron hpn xbar rays) a 1 =
          face_set (corner_polyhedron hpn xbar rays) γ δ := by
      ext s
      simp only [mem_face_set_iff]
      apply and_congr_right
      intro hs
      dsimp only [a]
      rw [smul_dotProduct]
      constructor
      · intro hnormalized
        have hscaled := congrArg (fun r : ℝ ↦ δ * r) hnormalized
        simpa [hδ_pos.ne'] using hscaled
      · intro horiginal
        rw [horiginal]
        exact inv_mul_cancel₀ hδ_pos.ne'
    rw [hfaces]
    exact hfacet.isFacet
  have ha_eq_cut : a = intersection_cut_coeff C xbar rays :=
    normalizedFacet_eq_of_valid_le
      hpn xbar rays hperiods_facet a (intersection_cut_coeff C xbar rays)
      hb_nonneg hb_valid ha_facet hb_le_a
  -- Rescale the normalized coefficient identity and package the geometric witness.
  rw [isIntersectionCutInequality_iff]
  refine ⟨hδ_pos, C, hC_closed, hC_convex, hxbar_interior, hC_free, ?_⟩
  calc
    γ = δ • a := by
      funext j
      simp [a, hδ_pos.ne']
    _ = δ • intersection_cut_coeff C xbar rays :=
      congrArg (fun b : Fin k → ℝ ↦ δ • b) ha_eq_cut

#print axioms nontrivial_facet_defining_inequality_is_intersection_cut

end Theorem612
