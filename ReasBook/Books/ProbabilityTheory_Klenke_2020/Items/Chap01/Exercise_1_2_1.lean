/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_28
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped ENNReal Topology

universe u

/-- The subset of `ℚ` cut out by the half-open real interval `(a, b]`. -/
def rationalRightClosedInterval (a b : ℝ) : Set ℚ :=
  ((↑) : ℚ → ℝ) ⁻¹' Ioc a b

/-- The family of subsets of `ℚ` of the form `(a, b] ∩ ℚ` with `a ≤ b`. -/
def rationalRightClosedIntervalFamily : Set (Set ℚ) :=
  {s | ∃ a b : ℝ, a ≤ b ∧ s = rationalRightClosedInterval a b}

/-- The image in `ℝ` of a set of rationals. -/
private def rationalRealImage (s : Set ℚ) : Set ℝ :=
  ((↑) : ℚ → ℝ) '' s

/-- The interval length attached to a set of rationals, computed from the infimum and supremum of
its real image and defined to be `0` on the empty set. -/
private noncomputable def rationalIntervalLength (s : Set ℚ) : ℝ≥0∞ :=
  if s = ∅ then 0 else ENNReal.ofReal (sSup (rationalRealImage s) - sInf (rationalRealImage s))

/-- Helper for Exercise 1.2.1: a real number lies in the real image of
`rationalRightClosedInterval a b` exactly when it is rational and belongs to `Ioc a b`. -/
private theorem rationalRealImage_interval_iff {a b x : ℝ} :
    x ∈ rationalRealImage (rationalRightClosedInterval a b) ↔
      x ∈ Set.range ((↑) : ℚ → ℝ) ∧ x ∈ Ioc a b := by
  -- Unpack membership in the image and then rewrite the defining preimage condition.
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, rfl⟩, hq⟩
  · rintro ⟨⟨q, rfl⟩, hq⟩
    exact ⟨q, hq, rfl⟩

-- Proof sketch: unfold `rationalIntervalLength` and use the `if` branch for `s = ∅`.
/-- The interval-length function vanishes on the empty set. -/
private theorem rationalIntervalLength_empty :
    rationalIntervalLength ∅ = 0 := by
  -- The definition takes the explicit `0` branch on the empty set.
  simp [rationalIntervalLength]

/-- Helper for Exercise 1.2.1: the interval-length function evaluates to the endpoint difference on
`rationalRightClosedInterval a b`. -/
private theorem rationalIntervalLength_eq_length {a b : ℝ} (hab : a ≤ b) :
    rationalIntervalLength (rationalRightClosedInterval a b) = ENNReal.ofReal (b - a) := by
  rcases hab.eq_or_lt with rfl | hab_lt
  · -- The degenerate interval is empty, so the `if`-definition returns `0 = ofReal (a - a)`.
    have hempty : rationalRightClosedInterval a a = ∅ := by
      ext q
      simp [rationalRightClosedInterval]
    simp [rationalIntervalLength, hempty]
  · -- For a genuine interval, identify the extremal points of its real image via density of `ℚ`.
    have hne : rationalRightClosedInterval a b ≠ ∅ := by
      intro hempty
      obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab_lt
      have hq : q ∈ rationalRightClosedInterval a b := ⟨hqa, hqb.le⟩
      simp [hempty] at hq
    have himage_nonempty : (rationalRealImage (rationalRightClosedInterval a b)).Nonempty := by
      obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab_lt
      exact ⟨q, ⟨q, ⟨hqa, hqb.le⟩, rfl⟩⟩
    have hsInf :
        sInf (rationalRealImage (rationalRightClosedInterval a b)) = a := by
      refine csInf_eq_of_forall_ge_of_forall_gt_exists_lt himage_nonempty ?_ ?_
      · intro y hy
        exact (rationalRealImage_interval_iff.1 hy).2.1.le
      · intro w haw
        obtain ⟨q, hqa, hqw⟩ := exists_rat_btwn (lt_min haw hab_lt)
        refine ⟨q, ?_, hqw.trans_le (min_le_left _ _)⟩
        exact rationalRealImage_interval_iff.2
          ⟨⟨q, rfl⟩, ⟨hqa, hqw.trans_le (min_le_right _ _) |>.le⟩⟩
    have hsSup :
        sSup (rationalRealImage (rationalRightClosedInterval a b)) = b := by
      refine csSup_eq_of_forall_le_of_forall_lt_exists_gt himage_nonempty ?_ ?_
      · intro y hy
        exact (rationalRealImage_interval_iff.1 hy).2.2
      · intro w hwb
        obtain ⟨q, hmq, hqb⟩ := exists_rat_btwn (max_lt_iff.2 ⟨hab_lt, hwb⟩)
        refine ⟨q, ?_, (le_max_right _ _).trans_lt hmq⟩
        exact rationalRealImage_interval_iff.2
          ⟨⟨q, rfl⟩, ⟨(le_max_left _ _).trans_lt hmq, hqb.le⟩⟩
    -- Substituting the extremal values reduces the definition to `ofReal (b - a)`.
    simp [rationalIntervalLength, hne, hsInf, hsSup]

/-- Helper for Exercise 1.2.1: a nonempty rational half-open interval contained in another one has
ordered endpoints compatible with the ambient interval. -/
private theorem rationalRightClosedInterval_subset_endpoints {a b u v : ℝ}
    (hne : (rationalRightClosedInterval u v).Nonempty)
    (hsub : rationalRightClosedInterval u v ⊆ rationalRightClosedInterval a b) :
    a ≤ u ∧ v ≤ b := by
  constructor
  · -- If `u < a`, density of `ℚ` produces a rational in the smaller interval but outside the
    -- ambient one, contradicting the inclusion.
    by_contra hau
    have huv : u < v := by
      rcases hne with ⟨q, hq⟩
      exact lt_of_lt_of_le hq.1 hq.2
    obtain ⟨q, huq, hqa⟩ := exists_rat_btwn (lt_min (lt_of_not_ge hau) huv)
    have hq : q ∈ rationalRightClosedInterval u v := ⟨huq, (hqa.trans_le (min_le_right _ _)).le⟩
    have hq' := hsub hq
    exact (not_lt_of_ge hq'.1.le) (hqa.trans_le (min_le_left _ _))
  · -- If `b < v`, density again gives a rational point of the smaller interval that lies to the
    -- right of `b`, so it cannot belong to the ambient interval.
    by_contra hvb
    have huv : u < v := by
      rcases hne with ⟨q, hq⟩
      exact lt_of_lt_of_le hq.1 hq.2
    obtain ⟨q, hq, hqv⟩ := exists_rat_btwn (max_lt_iff.2 ⟨huv, lt_of_not_ge hvb⟩)
    have hq_mem : q ∈ rationalRightClosedInterval u v := by
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hq, hqv.le⟩
    have hq' := hsub hq_mem
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hq)) hq'.2

/-- Helper for Exercise 1.2.1: removing the rightmost interval `(u, b] ∩ ℚ` from
`(a, b] ∩ ℚ` leaves `(a, u] ∩ ℚ`. -/
private theorem rationalRightClosedInterval_diff_rightmost {a u b : ℝ}
    (_hau : a ≤ u) (hub : u ≤ b) :
    rationalRightClosedInterval a b \ rationalRightClosedInterval u b =
      rationalRightClosedInterval a u := by
  -- Compare membership pointwise and translate everything to inequalities in `ℝ`.
  ext q
  constructor
  · intro hq
    rcases hq with ⟨hqab, hqub⟩
    refine ⟨hqab.1, ?_⟩
    by_contra huq
    exact hqub ⟨lt_of_not_ge huq, hqab.2⟩
  · intro hq
    refine ⟨⟨hq.1, hq.2.trans hub⟩, ?_⟩
    intro hqub
    exact not_lt_of_ge hq.2 hqub.1

/-- Helper for Exercise 1.2.1: a finite union equal to `(a, b] ∩ ℚ` with `a < b` contains a
member of the form `(u, b] ∩ ℚ`. -/
private theorem rationalUnionRightmostPiece (I : Finset (Set ℚ))
    (hI : ↑I ⊆ rationalRightClosedIntervalFamily)
    (_hdis : PairwiseDisjoint (I : Set (Set ℚ)) id)
    {a b : ℝ} (hab : a < b)
    (hUnion : ⋃₀ ↑I = rationalRightClosedInterval a b) :
    ∃ t ∈ I, ∃ u, a ≤ u ∧ u ≤ b ∧ t = rationalRightClosedInterval u b := by
  classical
  choose left right hle hrepr using hI
  let J := I.filter fun t ↦ t.Nonempty
  have hJne : J.Nonempty := by
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
    have hqUnion : q ∈ ⋃₀ ↑I := by
      simpa [hUnion, rationalRightClosedInterval] using
        (show q ∈ rationalRightClosedInterval a b from ⟨hqa, hqb.le⟩)
    rcases mem_sUnion.mp hqUnion with ⟨t, htI, hqt⟩
    exact ⟨t, Finset.mem_filter.mpr ⟨htI, ⟨q, hqt⟩⟩⟩
  let endpoint : {t // t ∈ J} → ℝ := fun t ↦
    right (a := t.1) ((Finset.mem_filter.mp t.2).1)
  let R : Finset ℝ := J.attach.image endpoint
  have hRne : R.Nonempty := by
    rcases hJne with ⟨t, htJ⟩
    refine ⟨endpoint ⟨t, htJ⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨t, htJ⟩, by simp [endpoint]⟩
  let rmax : ℝ := R.max' hRne
  have hrmax_mem : rmax ∈ R := by
    exact Finset.max'_mem R hRne
  rcases Finset.mem_image.mp hrmax_mem with ⟨tmax, htmax, hrmax⟩
  have hmax :
      ∀ ⦃s⦄ (hsJ : s ∈ J), right (a := s) ((Finset.mem_filter.mp hsJ).1) ≤
        right (a := tmax.1) ((Finset.mem_filter.mp tmax.2).1) := by
    intro s hsJ
    have hsR : right (a := s) ((Finset.mem_filter.mp hsJ).1) ∈ R := by
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨s, hsJ⟩, by simp [endpoint]⟩
    calc
      right (a := s) ((Finset.mem_filter.mp hsJ).1) ≤ rmax := Finset.le_max' _ _ hsR
      _ = right (a := tmax.1) ((Finset.mem_filter.mp tmax.2).1) := hrmax.symm
  have htI : tmax.1 ∈ I := (Finset.mem_filter.mp tmax.2).1
  have htne : tmax.1.Nonempty := (Finset.mem_filter.mp tmax.2).2
  have ht_subset :
      rationalRightClosedInterval (left (a := tmax.1) htI) (right (a := tmax.1) htI) ⊆
        rationalRightClosedInterval a b := by
    -- Membership in a family element pushes into the total union, hence into `(a, b] ∩ ℚ`.
    intro q hq
    have hqUnion : q ∈ ⋃₀ ↑I := by
      refine mem_sUnion.mpr ⟨tmax.1, htI, ?_⟩
      rw [hrepr (a := tmax.1) htI]
      exact hq
    simpa [hUnion] using hqUnion
  have hends :=
    rationalRightClosedInterval_subset_endpoints
      (by
        rcases htne with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        rw [hrepr (a := tmax.1) htI] at hq
        exact hq) ht_subset
  have hright_eq : right (a := tmax.1) htI = b := by
    apply le_antisymm hends.2
    by_contra hlt
    obtain ⟨q, hq, hqb⟩ := exists_rat_btwn (max_lt_iff.2 ⟨hab, lt_of_not_ge hlt⟩)
    have hq_target : q ∈ rationalRightClosedInterval a b := by
      exact ⟨lt_of_le_of_lt (le_max_left _ _) hq, hqb.le⟩
    have hqUnion : q ∈ ⋃₀ ↑I := by simpa [hUnion] using hq_target
    rcases mem_sUnion.mp hqUnion with ⟨s, hsI, hqs⟩
    have hsJ : s ∈ J := by
      exact Finset.mem_filter.mpr ⟨hsI, ⟨q, hqs⟩⟩
    have hs_le :
        right (a := s) hsI ≤ right (a := tmax.1) htI := by
      simpa using hmax (s := s) hsJ
    have hq_le :
        q ≤ right (a := s) hsI := by
      rw [hrepr (a := s) hsI] at hqs
      exact hqs.2
    exact (not_le_of_gt (lt_of_le_of_lt (le_max_right _ _) hq)) (hq_le.trans hs_le)
  refine ⟨tmax.1, htI, left (a := tmax.1) htI, hends.1, ?_, ?_⟩
  · simpa [hright_eq] using hle (a := tmax.1) htI
  · simpa [hright_eq] using (hrepr (a := tmax.1) htI)

-- Proof sketch: express each member of the finite disjoint family as `(a, b] ∩ ℚ`, order the
-- endpoints, and use finite additivity of interval lengths under disjoint concatenation.
/-- The interval-length function is finitely additive on finite pairwise disjoint unions whose
union is again a rational half-open interval. -/
private theorem rationalIntervalLength_sUnion (I : Finset (Set ℚ))
    (hI : ↑I ⊆ rationalRightClosedIntervalFamily)
    (hdis : PairwiseDisjoint (I : Set (Set ℚ)) id)
    (hmem : ⋃₀ ↑I ∈ rationalRightClosedIntervalFamily) :
    rationalIntervalLength (⋃₀ ↑I) = ∑ u ∈ I, rationalIntervalLength u := by
  classical
  revert hI hdis hmem
  induction hn : Finset.card I generalizing I with
  | zero =>
      intro hI hdis hmem
      -- With no intervals in the family, both the union and the sum are empty.
      have hIeq : I = ∅ := Finset.card_eq_zero.mp hn
      subst hIeq
      simp [rationalIntervalLength_empty]
  | succ n ih =>
      intro hI hdis hmem
      rcases hmem with ⟨a, b, hab, hUnion⟩
      rcases hab.eq_or_lt with rfl | hab_lt
      · -- If the target interval is empty, every family member is empty as well.
        have hUnion_empty : ⋃₀ (↑I : Set (Set ℚ)) = ∅ := by
          simpa [rationalRightClosedInterval] using hUnion
        rw [hUnion_empty, rationalIntervalLength_empty]
        have hzero : ∀ u ∈ I, rationalIntervalLength u = (0 : ℝ≥0∞) := by
          intro u hu
          have hu_empty : u = ∅ := by
            ext q
            constructor
            · intro hq
              have hqUnion : q ∈ ⋃₀ (↑I : Set (Set ℚ)) := mem_sUnion.mpr ⟨u, hu, hq⟩
              simp [hUnion_empty] at hqUnion
            · intro hq
              cases hq
          simpa [hu_empty] using rationalIntervalLength_empty
        symm
        simpa using Finset.sum_eq_zero hzero
      · -- Route correction: the union is a set of rationals, so the rightmost interval must be
        -- extracted by maximal right endpoint rather than by direct membership of the real point
        -- `b` in the union.
        obtain ⟨t, htI, u, hau, hub, htu⟩ :=
          rationalUnionRightmostPiece I hI hdis hab_lt hUnion
        let I' := I.erase t
        have hI' : ↑I' ⊆ rationalRightClosedIntervalFamily := by
          intro s hs
          exact hI (Finset.mem_of_mem_erase hs)
        have hIeq : I = insert t I' := by
          simp [I', htI]
        have hdisj_union : Disjoint (⋃₀ ↑I') t := by
          refine Set.disjoint_sUnion_left.2 ?_
          intro s hs
          exact hdis (Finset.mem_of_mem_erase hs) htI (Finset.ne_of_mem_erase hs)
        have hUnion' : ⋃₀ ↑I' = rationalRightClosedInterval a u := by
          calc
            ⋃₀ ↑I' = (t ∪ ⋃₀ ↑I') \ t := by
              symm
              exact Disjoint.sup_sdiff_cancel_left hdisj_union.symm
            _ = rationalRightClosedInterval a b \ t := by
              rw [← hUnion, hIeq, Finset.coe_insert, Set.sUnion_insert]
            _ = rationalRightClosedInterval a u := by
              rw [htu, rationalRightClosedInterval_diff_rightmost hau hub]
        have hmem' : ⋃₀ ↑I' ∈ rationalRightClosedIntervalFamily := by
          exact ⟨a, u, hau, hUnion'⟩
        have hdis' : PairwiseDisjoint (I' : Set (Set ℚ)) id := by
          intro s hs t' ht hst
          exact hdis (Finset.mem_of_mem_erase hs) (Finset.mem_of_mem_erase ht) hst
        have hcard : Finset.card I' = n := by
          have hcard_succ : Finset.card I' + 1 = n + 1 := by
            simpa [I', hn] using Finset.card_erase_add_one (s := I) htI
          exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hcard_succ)
        have hIH :
            rationalIntervalLength (⋃₀ ↑I') = ∑ s ∈ I', rationalIntervalLength s :=
          ih I' hcard hI' hdis' hmem'
        calc
          rationalIntervalLength (⋃₀ ↑I)
              = ENNReal.ofReal (b - a) := by
                  rw [hUnion, rationalIntervalLength_eq_length hab]
          _ = ENNReal.ofReal (b - u) + ENNReal.ofReal (u - a) := by
                rw [show b - a = (b - u) + (u - a) by linarith]
                rw [ENNReal.ofReal_add (sub_nonneg.mpr hub) (sub_nonneg.mpr hau)]
          _ = rationalIntervalLength t + rationalIntervalLength (⋃₀ ↑I') := by
                rw [htu, rationalIntervalLength_eq_length hub, hUnion',
                  rationalIntervalLength_eq_length hau]
          _ = ∑ s ∈ I, rationalIntervalLength s := by
                rw [hIeq, Finset.sum_insert, hIH]
                simp [I']

/-- The additive content on rational half-open intervals defined by interval length. -/
noncomputable def rationalIntervalContent :
    AddContent ℝ≥0∞ rationalRightClosedIntervalFamily :=
  { toFun := rationalIntervalLength
    empty' := rationalIntervalLength_empty
    sUnion' := rationalIntervalLength_sUnion }

-- Proof sketch: compute the infimum and supremum of `(a, b] ∩ ℚ` inside `ℝ`; density of `ℚ`
-- gives `sInf = a` and `sSup = b`, so the definition reduces to `b - a`.
/-- The rational interval content assigns the length `b - a` to `(a, b] ∩ ℚ`. -/
theorem rationalIntervalContent_apply (a b : ℝ) (hab : a ≤ b) :
    rationalIntervalContent (rationalRightClosedInterval a b) = ENNReal.ofReal (b - a) := by
  -- The bundled content is just `rationalIntervalLength` on the underlying set.
  simpa [rationalIntervalContent] using rationalIntervalLength_eq_length hab

/-- Helper for Exercise 1.2.1: preimages of a semiring family along a map form a semiring. -/
private theorem isSetSemiring_preimage {α β : Type*} (f : α → β) {C : Set (Set β)}
    (hC : IsSetSemiring C) :
    IsSetSemiring {s : Set α | ∃ t ∈ C, s = f ⁻¹' t} := by
  classical
  refine
    { empty_mem := ?_
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- Pull back the empty set.
    exact ⟨∅, hC.empty_mem, by simp⟩
  · -- Pull back intersections pointwise.
    rintro s ⟨u, hu, rfl⟩ t ⟨v, hv, rfl⟩
    exact ⟨u ∩ v, hC.inter_mem _ hu _ hv, by ext x; simp⟩
  · -- Pull back a finite disjoint decomposition of the difference upstairs.
    rintro s ⟨u, hu, rfl⟩ t ⟨v, hv, rfl⟩
    obtain ⟨I, hI, hdis, hdiff⟩ := hC.diff_eq_sUnion' u hu v hv
    refine ⟨I.image (fun w ↦ f ⁻¹' w), ?_, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_image.mp hw with ⟨w', hw', rfl⟩
      exact ⟨w', hI hw', rfl⟩
    · intro s hs t ht hst
      rcases Finset.mem_image.mp hs with ⟨s', hs', rfl⟩
      rcases Finset.mem_image.mp ht with ⟨t', ht', rfl⟩
      by_cases hEq : s' = t'
      · subst hEq
        exact (hst rfl).elim
      · exact (hdis hs' ht' hEq).preimage f
    · ext x
      constructor
      · intro hx
        have hx' : f x ∈ u \ v := by
          simpa [Set.mem_diff, Set.mem_preimage] using hx
        rw [hdiff] at hx'
        rcases mem_sUnion.mp hx' with ⟨i, hiI, hxi⟩
        exact mem_sUnion.mpr ⟨f ⁻¹' i, by exact Finset.mem_image.mpr ⟨i, hiI, rfl⟩, hxi⟩
      · intro hx
        rcases mem_sUnion.mp hx with ⟨j, hj, hxj⟩
        rcases Finset.mem_image.mp hj with ⟨i, hiI, rfl⟩
        have hx' : f x ∈ ⋃₀ ↑I := mem_sUnion.mpr ⟨i, hiI, hxj⟩
        have hxuv : f x ∈ u \ v := by rwa [← hdiff] at hx'
        simpa [Set.mem_diff, Set.mem_preimage] using hxuv

-- Proof sketch: intersections of half-open intervals remain half-open, and set differences split
-- into finite disjoint unions of half-open intervals after intersecting with `ℚ`.
/-- For Exercise 1.2.1, the family of sets `(a, b] ∩ ℚ` with `a ≤ b` is a semiring of sets on
`ℚ`. -/
instance rationalRightClosedIntervalFamily_isSetSemiring :
    IsSetSemiring rationalRightClosedIntervalFamily := by
  -- Transport the standard real `Ioc` semiring along the coercion `ℚ → ℝ`.
  simpa [rationalRightClosedIntervalFamily, rationalRightClosedInterval] using
    isSetSemiring_preimage ((↑) : ℚ → ℝ) (MeasureTheory.IsSetSemiring.Ioc (α := ℝ))

/-- Helper for Exercise 1.2.1: a rational half-open interval is nonempty exactly when its endpoints
are strictly ordered. -/
private theorem rationalRightClosedInterval_nonempty_iff {a b : ℝ} :
    (rationalRightClosedInterval a b).Nonempty ↔ a < b := by
  constructor
  · rintro ⟨q, hq⟩
    exact lt_of_lt_of_le hq.1 hq.2
  · intro hab
    obtain ⟨q, hqa, hqb⟩ := exists_rat_btwn hab
    exact ⟨q, ⟨hqa, hqb.le⟩⟩

/-- Helper for Exercise 1.2.1: if an increasing family converges to a nonempty rational half-open
interval, then all sufficiently large terms are nonempty. -/
private theorem rationalIncreasesTo_eventually_nonempty {s : ℕ → Set ℚ} {a b : ℝ}
    (hs : Set.IncreasesTo s (rationalRightClosedInterval a b)) (hab : a < b) :
    ∃ N, ∀ n ≥ N, (s n).Nonempty := by
  -- Pick one rational point in the limit interval and wait until the increasing family captures
  -- it; monotonicity then keeps the point in every later term.
  obtain ⟨q, hq⟩ : (rationalRightClosedInterval a b).Nonempty :=
    rationalRightClosedInterval_nonempty_iff.mpr hab
  have hqUnion : q ∈ ⋃ n, s n := by
    simpa [hs.iUnion_eq] using hq
  rcases mem_iUnion.mp hqUnion with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact ⟨q, hs.mono hn hN⟩

/-- Helper for Exercise 1.2.1: a decreasing family of nonempty rational half-open intervals with
empty intersection has widths tending to `0`. -/
private theorem rationalWidth_tendsto_zero_of_decreasesTo_empty_nonempty
    {s : ℕ → Set ℚ} {l r : ℕ → ℝ} (hs_repr : ∀ n, s n = rationalRightClosedInterval (l n) (r n))
    (hs_decr : Set.DecreasesTo s (∅ : Set ℚ)) (hne : ∀ n, (s n).Nonempty) :
    Tendsto (fun n ↦ r n - l n) atTop (𝓝 0) := by
  have hleft_mono : Monotone l := by
    intro m n hmn
    have hsub : s n ⊆ s m := hs_decr.antitone hmn
    have hsub' :
        rationalRightClosedInterval (l n) (r n) ⊆ rationalRightClosedInterval (l m) (r m) := by
      intro q hq
      have hq' : q ∈ s n := by simpa [hs_repr n] using hq
      have hq'' : q ∈ s m := hsub hq'
      simpa [hs_repr m] using hq''
    exact
      (rationalRightClosedInterval_subset_endpoints
        (by simpa [hs_repr n] using hne n) hsub').1
  have hright_anti : Antitone r := by
    intro m n hmn
    have hsub : s n ⊆ s m := hs_decr.antitone hmn
    have hsub' :
        rationalRightClosedInterval (l n) (r n) ⊆ rationalRightClosedInterval (l m) (r m) := by
      intro q hq
      have hq' : q ∈ s n := by simpa [hs_repr n] using hq
      have hq'' : q ∈ s m := hsub hq'
      simpa [hs_repr m] using hq''
    exact
      (rationalRightClosedInterval_subset_endpoints
        (by simpa [hs_repr n] using hne n) hsub').2
  have hwidth_nonneg : ∀ n, 0 ≤ r n - l n := by
    intro n
    have hlt : l n < r n :=
      rationalRightClosedInterval_nonempty_iff.mp (by simpa [hs_repr n] using hne n)
    exact sub_nonneg.mpr hlt.le
  -- Route correction: the empty-target branch does not have canonical endpoint limits, so the
  -- proof works directly at the width level.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  by_contra hε_tail
  push Not at hε_tail
  have hwidth_ge : ∀ n, ε ≤ r n - l n := by
    intro n
    rcases hε_tail n with ⟨m, hnm, hmε⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hwidth_nonneg m)] at hmε
    have hmono :
        r m - l m ≤ r n - l n := by
      have hl : l n ≤ l m := hleft_mono hnm
      have hr : r m ≤ r n := hright_anti hnm
      linarith
    exact hmε.trans hmono
  have hRangeL_nonempty : (Set.range l).Nonempty := ⟨l 0, ⟨0, rfl⟩⟩
  have hRangeR_nonempty : (Set.range r).Nonempty := ⟨r 0, ⟨0, rfl⟩⟩
  have hRangeL_bddAbove : BddAbove (Set.range l) := by
    refine ⟨r 0 - ε, ?_⟩
    rintro y ⟨m, rfl⟩
    have hmε : ε ≤ r m - l m := hwidth_ge m
    have hr : r m ≤ r 0 := hright_anti (Nat.zero_le m)
    linarith
  have hRangeR_bddBelow : BddBelow (Set.range r) := by
    refine ⟨l 0 + ε, ?_⟩
    rintro y ⟨m, rfl⟩
    have hmε : ε ≤ r m - l m := hwidth_ge m
    have hl : l 0 ≤ l m := hleft_mono (Nat.zero_le m)
    linarith
  let L : ℝ := sSup (Set.range l)
  let R : ℝ := sInf (Set.range r)
  have hL_le_each : ∀ n, L ≤ r n - ε := by
    intro n
    dsimp [L]
    refine csSup_le hRangeL_nonempty ?_
    intro y hy
    rcases hy with ⟨m, rfl⟩
    by_cases hmn : m ≤ n
    · have hmn' : l m ≤ l n := hleft_mono hmn
      have hnε : ε ≤ r n - l n := hwidth_ge n
      linarith
    · have hnm : n ≤ m := le_of_not_ge hmn
      have hr : r m ≤ r n := hright_anti hnm
      have hmε : ε ≤ r m - l m := hwidth_ge m
      linarith
  have hL_lt_R : L < R := by
    have hLeps : L + ε ≤ R := by
      dsimp [R]
      refine le_csInf hRangeR_nonempty ?_
      intro y hy
      rcases hy with ⟨n, rfl⟩
      have hLn : L ≤ r n - ε := hL_le_each n
      linarith
    linarith
  obtain ⟨q, hLq, hqR⟩ := exists_rat_btwn hL_lt_R
  have hq_mem_all : q ∈ ⋂ n, s n := by
    refine mem_iInter.mpr ?_
    intro n
    have hl : l n ≤ L := by
      dsimp [L]
      exact le_csSup hRangeL_bddAbove ⟨n, rfl⟩
    have hr : R ≤ r n := by
      dsimp [R]
      exact csInf_le hRangeR_bddBelow ⟨n, rfl⟩
    have hq_mem :
        q ∈ rationalRightClosedInterval (l n) (r n) := by
      refine ⟨lt_of_le_of_lt hl hLq, hqR.le.trans hr⟩
    simpa [hs_repr n] using hq_mem
  have : False := by
    simp [hs_decr.iInter_eq] at hq_mem_all
  exact this

-- Proof sketch: for an increasing sequence of rational half-open intervals with union again in the
-- family, the left endpoints decrease, the right endpoints increase, and the corresponding lengths
-- converge to the limiting interval length.
/-- For Exercise 1.2.1, the interval-length content on the rational half-open-interval semiring is
lower semicontinuous. -/
instance rationalIntervalContent_isLowerSemicontinuous :
    AddContent.IsLowerSemicontinuous rationalIntervalContent := by
  refine ⟨?_⟩
  intro A hA s hs hs_inc
  classical
  choose a b hA_le hA_repr using hA
  choose l r hs_le hs_repr using hs
  rcases hA_le.eq_or_lt with rfl | hab
  · have hA_empty : rationalRightClosedInterval a a = ∅ := by
      ext q
      simp [rationalRightClosedInterval]
    have hs_empty : ∀ n, s n = ∅ := by
      intro n
      apply Set.eq_empty_iff_forall_notMem.2
      intro q hq
      have hqUnion : q ∈ ⋃ m, s m := mem_iUnion.mpr ⟨n, hq⟩
      simp [hs_inc.iUnion_eq, hA_repr, hA_empty] at hqUnion
    have hs_zero : (rationalIntervalContent ∘ s) = fun _ : ℕ ↦ (0 : ℝ≥0∞) := by
      funext n
      rw [Function.comp, hs_empty n, addContent_empty]
    have hA_zero : rationalIntervalContent A = 0 := by
      rw [hA_repr, hA_empty, addContent_empty]
    -- If the limit interval is empty, every member of the increasing family is already empty.
    rw [hs_zero, hA_zero]
    exact tendsto_const_nhds
  · have hs_inc_target : Set.IncreasesTo s (rationalRightClosedInterval a b) := by
      refine ⟨hs_inc.mono, ?_⟩
      simpa [hA_repr] using hs_inc.iUnion_eq
    obtain ⟨N, hN⟩ := rationalIncreasesTo_eventually_nonempty hs_inc_target hab
    have hAμ :
        rationalIntervalContent A = ENNReal.ofReal (b - a) := by
      simpa [hA_repr] using rationalIntervalContent_apply a b hA_le
    have hwidth_tendsto :
        Tendsto (fun n ↦ r n - l n) atTop (𝓝 (b - a)) := by
      -- Route correction: after normalizing to a nonempty tail, approximate the target width by
      -- inserting two rational witnesses near the limiting endpoints.
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      let δ : ℝ := min (ε / 4) ((b - a) / 4)
      have hδ_pos : 0 < δ := by
        dsimp [δ]
        refine lt_min ?_ ?_
        · positivity
        · linarith
      have hδ_le_eps : δ ≤ ε / 4 := by
        dsimp [δ]
        exact min_le_left _ _
      have hδ_le_gap : δ ≤ (b - a) / 4 := by
        dsimp [δ]
        exact min_le_right _ _
      obtain ⟨qL, hqLa, hqLδ⟩ := exists_rat_btwn (by linarith [hδ_pos] : a < a + δ)
      obtain ⟨qR, hqRδ, hqRb⟩ := exists_rat_btwn (by linarith [hδ_pos] : b - δ < b)
      have hqL_mem : qL ∈ rationalRightClosedInterval a b := by
        refine ⟨hqLa, ?_⟩
        have : a + δ < b := by linarith
        exact hqLδ.le.trans this.le
      have hqR_mem : qR ∈ rationalRightClosedInterval a b := by
        refine ⟨?_, hqRb.le⟩
        have : a < b - δ := by linarith
        exact this.trans hqRδ
      have hqL_union : qL ∈ ⋃ n, s n := by
        simpa [hs_inc_target.iUnion_eq] using hqL_mem
      have hqR_union : qR ∈ ⋃ n, s n := by
        simpa [hs_inc_target.iUnion_eq] using hqR_mem
      rcases mem_iUnion.mp hqL_union with ⟨NL, hNL⟩
      rcases mem_iUnion.mp hqR_union with ⟨NR, hNR⟩
      let M : ℕ := max N (max NL NR)
      refine ⟨M, ?_⟩
      intro n hn
      have hMn : M ≤ n := hn
      have hNn : N ≤ n := le_trans (le_max_left _ _) hMn
      have hNLe : NL ≤ n := by
        exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hMn
      have hNRe : NR ≤ n := by
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hMn
      have hs_nonempty : (s n).Nonempty := hN n hNn
      have hsub :
          rationalRightClosedInterval (l n) (r n) ⊆ rationalRightClosedInterval a b := by
        intro q hq
        have hq' : q ∈ s n := by simpa [hs_repr n] using hq
        have hq'' : q ∈ ⋃ m, s m := mem_iUnion.mpr ⟨n, hq'⟩
        simpa [hs_inc_target.iUnion_eq] using hq''
      have hends := rationalRightClosedInterval_subset_endpoints
        (by simpa [hs_repr n] using hs_nonempty) hsub
      have hqLn : qL ∈ s n := hs_inc.mono hNLe hNL
      have hqRn : qR ∈ s n := hs_inc.mono hNRe hNR
      rw [hs_repr n] at hqLn hqRn
      have hlower : b - a - ε < r n - l n := by
        have hq_gap : b - a - ε < qR - qL := by
          have hδ_lt_eps : 2 * δ < ε := by
            have : 2 * δ ≤ ε / 2 := by
              nlinarith [hδ_le_eps]
            linarith
          linarith
        have hq_width : qR - qL < r n - l n := by
          linarith [hqLn.1, hqRn.2]
        exact lt_trans hq_gap hq_width
      have hupper : r n - l n ≤ b - a := by
        linarith
      have hdist :
          dist (r n - l n) (b - a) < ε := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hupper)]
        linarith
      simpa using hdist
    have hrewrite :
        ∀ᶠ n in atTop, ENNReal.ofReal (r n - l n) = rationalIntervalContent (s n) := by
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa [Function.comp, hs_repr n] using
          (rationalIntervalContent_apply (l n) (r n) (hs_le n)).symm
    -- Rewrite the eventually nonempty tail to explicit widths and apply continuity of `ofReal`.
    simpa [Function.comp, hAμ] using
      (ENNReal.tendsto_ofReal hwidth_tendsto).congr' hrewrite

-- Proof sketch: for a decreasing sequence of rational half-open intervals with nonempty finite
-- mass at some stage, the endpoints converge monotonically to the limiting interval and the
-- lengths converge from above.
/-- For Exercise 1.2.1, the interval-length content on the rational half-open-interval semiring is
upper semicontinuous. -/
instance rationalIntervalContent_isUpperSemicontinuous :
    AddContent.IsUpperSemicontinuous rationalIntervalContent := by
  refine ⟨?_⟩
  intro A hA s hs hs_decr _hfin
  classical
  choose a b hA_le hA_repr using hA
  choose l r hs_le hs_repr using hs
  rcases hA_le.eq_or_lt with rfl | hab
  · have hA_empty : rationalRightClosedInterval a a = ∅ := by
      ext q
      simp [rationalRightClosedInterval]
    have hs_decr_empty : Set.DecreasesTo s (∅ : Set ℚ) := by
      refine ⟨hs_decr.antitone, ?_⟩
      simpa [hA_repr, hA_empty] using hs_decr.iInter_eq
    by_cases hEventually : ∃ N, s N = ∅
    · rcases hEventually with ⟨N, hN⟩
      have hs_tail_empty : ∀ n ≥ N, s n = ∅ := by
        intro n hn
        apply Set.eq_empty_iff_forall_notMem.2
        intro q hq
        have hqN : q ∈ s N := hs_decr.antitone hn hq
        simp [hN] at hqN
      have hs_zero :
          ∀ᶠ n in atTop, (rationalIntervalContent ∘ s) n = (0 : ℝ≥0∞) := by
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        rw [Function.comp, hs_tail_empty n hn, addContent_empty]
      have hs_zero' :
          ∀ᶠ n in atTop, (fun _ : ℕ ↦ (0 : ℝ≥0∞)) n = (rationalIntervalContent ∘ s) n := by
        filter_upwards [hs_zero] with n hn
        exact hn.symm
      have hA_zero : rationalIntervalContent A = 0 := by
        rw [hA_repr, hA_empty, addContent_empty]
      -- Once one term is empty, antitonicity makes the whole tail constantly `0`.
      rw [hA_zero]
      exact tendsto_const_nhds.congr' hs_zero'
    · have hs_nonempty : ∀ n, (s n).Nonempty := by
        intro n
        by_contra hne
        exact hEventually ⟨n, Set.not_nonempty_iff_eq_empty.mp hne⟩
      have hAμ : rationalIntervalContent A = 0 := by
        rw [hA_repr, hA_empty, addContent_empty]
      have hwidth_tendsto :
          Tendsto (fun n ↦ r n - l n) atTop (𝓝 0) :=
        rationalWidth_tendsto_zero_of_decreasesTo_empty_nonempty hs_repr hs_decr_empty hs_nonempty
      have hrewrite :
          ∀ᶠ n in atTop, ENNReal.ofReal (r n - l n) = rationalIntervalContent (s n) := by
        exact Filter.Eventually.of_forall fun n ↦ by
          simpa [Function.comp, hs_repr n] using
            (rationalIntervalContent_apply (l n) (r n) (hs_le n)).symm
      -- In the never-empty branch, rewrite every term by the explicit width formula.
      simpa [Function.comp, hAμ] using
        (ENNReal.tendsto_ofReal hwidth_tendsto).congr'
          hrewrite
  · have hAμ :
        rationalIntervalContent A = ENNReal.ofReal (b - a) := by
      simpa [hA_repr] using rationalIntervalContent_apply a b hA_le
    have hs_decr_target : Set.DecreasesTo s (rationalRightClosedInterval a b) := by
      refine ⟨hs_decr.antitone, ?_⟩
      simpa [hA_repr] using hs_decr.iInter_eq
    have hA_nonempty : (rationalRightClosedInterval a b).Nonempty :=
      rationalRightClosedInterval_nonempty_iff.mpr hab
    have hs_nonempty : ∀ n, (s n).Nonempty := by
      intro n
      rcases hA_nonempty with ⟨q, hq⟩
      have hq_inter : q ∈ ⋂ m, s m := by
        rw [hs_decr_target.iInter_eq]
        exact hq
      exact ⟨q, mem_iInter.mp hq_inter n⟩
    have hwidth_tendsto :
        Tendsto (fun n ↦ r n - l n) atTop (𝓝 (b - a)) := by
      have hleft_mono : Monotone l := by
        intro m n hmn
        have hsub : s n ⊆ s m := hs_decr.antitone hmn
        have hsub' :
            rationalRightClosedInterval (l n) (r n) ⊆ rationalRightClosedInterval (l m) (r m) := by
          intro q hq
          have hq' : q ∈ s n := by simpa [hs_repr n] using hq
          have hq'' : q ∈ s m := hsub hq'
          simpa [hs_repr m] using hq''
        exact
          (rationalRightClosedInterval_subset_endpoints
            (by simpa [hs_repr n] using hs_nonempty n) hsub').1
      have hright_anti : Antitone r := by
        intro m n hmn
        have hsub : s n ⊆ s m := hs_decr.antitone hmn
        have hsub' :
            rationalRightClosedInterval (l n) (r n) ⊆ rationalRightClosedInterval (l m) (r m) := by
          intro q hq
          have hq' : q ∈ s n := by simpa [hs_repr n] using hq
          have hq'' : q ∈ s m := hsub hq'
          simpa [hs_repr m] using hq''
        exact
          (rationalRightClosedInterval_subset_endpoints
            (by simpa [hs_repr n] using hs_nonempty n) hsub').2
      have hwidth_lower : ∀ n, b - a ≤ r n - l n := by
        intro n
        have hsub :
            rationalRightClosedInterval a b ⊆ rationalRightClosedInterval (l n) (r n) := by
          intro q hq
          have hq_inter : q ∈ ⋂ m, s m := by
            rw [hs_decr_target.iInter_eq]
            exact hq
          have hq' : q ∈ s n := mem_iInter.mp hq_inter n
          simpa [hs_repr n] using hq'
        have hends := rationalRightClosedInterval_subset_endpoints hA_nonempty hsub
        linarith
      have hA_subset :
          ∀ n, rationalRightClosedInterval a b ⊆ rationalRightClosedInterval (l n) (r n) := by
        intro n q hq
        have hq_inter : q ∈ ⋂ m, s m := by
          rw [hs_decr.iInter_eq, hA_repr]
          exact hq
        have hq' : q ∈ s n := mem_iInter.mp hq_inter n
        simpa [hs_repr n] using hq'
      have hleft_bound : ∀ n, l n ≤ a := by
        intro n
        exact (rationalRightClosedInterval_subset_endpoints hA_nonempty (hA_subset n)).1
      have hright_bound : ∀ n, b ≤ r n := by
        intro n
        exact (rationalRightClosedInterval_subset_endpoints hA_nonempty (hA_subset n)).2
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      by_contra hε_tail
      push Not at hε_tail
      have hwidth_ge : ∀ n, b - a + ε ≤ r n - l n := by
        intro n
        rcases hε_tail n with ⟨m, hnm, hmε⟩
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hwidth_lower m))] at hmε
        have hl : l n ≤ l m := hleft_mono hnm
        have hr : r m ≤ r n := hright_anti hnm
        have hmono : r m - l m ≤ r n - l n := by
          linarith
        linarith
      have hleft_or_right :
          (∀ n, ε / 2 ≤ a - l n) ∨ ∀ n, ε / 2 ≤ r n - b := by
        by_cases hleft : ∀ n, ε / 2 ≤ a - l n
        · exact Or.inl hleft
        · push Not at hleft
          refine Or.inr ?_
          intro n
          rcases hleft with ⟨m, hm⟩
          let k := max n m
          have hk_left : a - l k < ε / 2 := by
            have hmle : m ≤ k := le_max_right _ _
            have hlm : l m ≤ l k := hleft_mono hmle
            linarith
          have hk_right : ε / 2 ≤ r k - b := by
            have hkε : b - a + ε ≤ r k - l k := hwidth_ge k
            linarith
          have hkn : k ≥ n := le_max_left _ _
          have hrnk : r k ≤ r n := hright_anti hkn
          linarith
      rcases hleft_or_right with hleft | hright
      · obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn (by linarith [hε] : a - ε / 2 < a)
        have hq_mem_all : q ∈ ⋂ n, s n := by
          refine mem_iInter.mpr ?_
          intro n
          have hl : l n < q := by
            have hnleft : ε / 2 ≤ a - l n := hleft n
            linarith
          have hq_mem :
              q ∈ rationalRightClosedInterval (l n) (r n) := by
            refine ⟨hl, ?_⟩
            have hqa : q ≤ a := hqUpper.le
            exact hqa.trans (hab.le.trans (hright_bound n))
          simpa [hs_repr n] using hq_mem
        have : q ∈ A := by
          rw [hA_repr]
          simpa [hs_decr_target.iInter_eq] using hq_mem_all
        rw [hA_repr, rationalRightClosedInterval] at this
        exact not_lt_of_ge this.1.le hqUpper
      · obtain ⟨q, hqLower, hqUpper⟩ := exists_rat_btwn (by linarith [hε] : b < b + ε / 2)
        have hq_mem_all : q ∈ ⋂ n, s n := by
          refine mem_iInter.mpr ?_
          intro n
          have hl : l n < q := by
            have hleftn : l n ≤ a := hleft_bound n
            linarith
          have hr : q ≤ r n := by
            have hrightn : ε / 2 ≤ r n - b := hright n
            linarith
          have hq_mem :
              q ∈ rationalRightClosedInterval (l n) (r n) := ⟨hl, hr⟩
          simpa [hs_repr n] using hq_mem
        have : q ∈ A := by
          rw [hA_repr]
          simpa [hs_decr_target.iInter_eq] using hq_mem_all
        rw [hA_repr, rationalRightClosedInterval] at this
        exact not_le_of_gt hqLower this.2
      -- The contradiction branch closes the tail estimate.
    have hrewrite :
        ∀ᶠ n in atTop, ENNReal.ofReal (r n - l n) = rationalIntervalContent (s n) := by
      exact Filter.Eventually.of_forall fun n ↦ by
        simpa [Function.comp, hs_repr n] using
          (rationalIntervalContent_apply (l n) (r n) (hs_le n)).symm
    -- Rewrite every term to the explicit interval width and pass the real limit through `ofReal`.
    simpa [Function.comp, hAμ] using
      (ENNReal.tendsto_ofReal hwidth_tendsto).congr' hrewrite

-- Proof sketch: decompose `(0, 1] ∩ ℚ` into the disjoint countable union of singleton rational
-- sets; each singleton has length `0`, but the whole interval has length `1`.
/-- Exercise 1.2.1: The interval-length content on `(a, b] ∩ ℚ` fails countable additivity on
disjoint unions in the semiring, so it is not a premeasure. -/
theorem rationalIntervalContent_not_isPremeasureOn :
    ¬ rationalIntervalContent.IsSigmaSubadditive :=
  by
    classical
    let Q01 : Type := {q : ℚ // (0 : ℝ) < q ∧ (q : ℝ) ≤ 1}
    -- Route correction: singletons are not semiring members here, so use a countable cover by
    -- tiny rational half-open intervals with total length strictly less than `1`.
    let cover : ℕ → Set ℚ := fun n =>
      match Encodable.decode (α := Q01) n with
      | none => ∅
      | some q =>
          rationalRightClosedInterval
            (max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n))) (q : ℝ)
    intro hσ
    have hcover_mem : ∀ n, cover n ∈ rationalRightClosedIntervalFamily := by
      intro n
      rcases hq : Encodable.decode (α := Q01) n with _ | q
      · refine ⟨0, 0, le_rfl, ?_⟩
        ext x
        simp [cover, hq, rationalRightClosedInterval]
      · refine ⟨max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n)), (q : ℝ), ?_, ?_⟩
        · refine max_le_iff.mpr ⟨?_, ?_⟩
          · exact q.property.1.le
          · linarith [show (0 : ℝ) ≤ ((1 / 2 : ℝ) / 2 / 2 ^ n) by positivity]
        · simp [cover, hq]
    have hcover_union :
        (⋃ n, cover n) = rationalRightClosedInterval 0 1 := by
      ext x
      constructor
      · intro hx
        rcases mem_iUnion.mp hx with ⟨n, hn⟩
        rcases hq : Encodable.decode (α := Q01) n with _ | q
        · simp [cover, hq] at hn
        · have hn' :
              x ∈ rationalRightClosedInterval
                (max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n))) (q : ℝ) := by
              simpa [cover, hq] using hn
          -- Every covering interval stays inside `(0, 1] ∩ ℚ`.
          exact ⟨lt_of_le_of_lt (le_max_left _ _) hn'.1, hn'.2.trans q.property.2⟩
      · intro hx
        -- Every rational in `(0,1]` appears at its own encoded index and belongs to the
        -- corresponding tiny interval.
        let q : Q01 := ⟨x, hx⟩
        refine mem_iUnion.mpr ⟨Encodable.encode q, ?_⟩
        have hδpos : 0 < ((1 / 2 : ℝ) / 2 / 2 ^ Encodable.encode q) := by
          positivity
        have hxmem :
            x ∈ rationalRightClosedInterval
              (max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ Encodable.encode q))) (q : ℝ) := by
          refine ⟨?_, ?_⟩
          · exact max_lt_iff.mpr ⟨q.property.1, sub_lt_self _ hδpos⟩
          · exact le_rfl
        simpa [cover, q] using hxmem
    have hcover_union_mem : (⋃ n, cover n) ∈ rationalRightClosedIntervalFamily := by
      rw [hcover_union]
      exact ⟨0, 1, by norm_num, rfl⟩
    have hwhole :
        rationalIntervalContent (⋃ n, cover n) = (1 : ℝ≥0∞) := by
      rw [hcover_union]
      simpa using rationalIntervalContent_apply 0 1 (by norm_num)
    have hcover_bound :
        ∀ n,
          rationalIntervalContent (cover n) ≤
            ENNReal.ofReal ((1 / 2 : ℝ) / 2 / 2 ^ n) := by
      intro n
      rcases hq : Encodable.decode (α := Q01) n with _ | q
      · simp [cover, hq]
      · -- The chosen interval ends at `q` and has length at most the prescribed geometric bound.
        have hleft :
            max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n)) ≤ (q : ℝ) := by
          refine max_le_iff.mpr ⟨?_, ?_⟩
          · exact q.property.1.le
          · linarith [show (0 : ℝ) ≤ ((1 / 2 : ℝ) / 2 / 2 ^ n) by positivity]
        calc
          rationalIntervalContent (cover n)
              =
                rationalIntervalContent
                  (rationalRightClosedInterval
                    (max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n))) (q : ℝ)) := by
                      simp [cover, hq]
          _ = ENNReal.ofReal
                ((q : ℝ) - max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n))) := by
                rw [rationalIntervalContent_apply _ _ hleft]
          _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) / 2 / 2 ^ n) := by
                refine ENNReal.ofReal_le_ofReal ?_
                have hmax : (q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n) ≤
                    max 0 ((q : ℝ) - ((1 / 2 : ℝ) / 2 / 2 ^ n)) := le_max_right _ _
                linarith
    have hsum_le_half :
        ∑' n, rationalIntervalContent (cover n) ≤ ENNReal.ofReal ((1 / 2 : ℝ)) := by
      calc
        ∑' n, rationalIntervalContent (cover n)
            ≤ ∑' n, ENNReal.ofReal ((1 / 2 : ℝ) / 2 / 2 ^ n) := by
              exact ENNReal.tsum_le_tsum hcover_bound
        _ = ENNReal.ofReal (∑' n : ℕ, ((1 / 2 : ℝ) / 2 / 2 ^ n)) := by
              rw [ENNReal.ofReal_tsum_of_nonneg]
              · intro n
                positivity
              · exact summable_geometric_two' (1 / 2 : ℝ)
        _ = ENNReal.ofReal ((1 / 2 : ℝ)) := by
              congr 1
              simpa using tsum_geometric_two' (1 / 2 : ℝ)
    have hmain : (1 : ℝ≥0∞) ≤ ∑' n, rationalIntervalContent (cover n) := by
      simpa [hwhole] using hσ hcover_mem hcover_union_mem
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 / 2 : ℝ)) := hmain.trans hsum_le_half
    exact (not_le_of_gt (by norm_num : ENNReal.ofReal ((1 / 2 : ℝ)) < (1 : ℝ≥0∞))) this
