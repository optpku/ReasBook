import Mathlib

noncomputable section

open scoped BigOperators

namespace FinitePairSlice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Helper for Proposition 8.9: the indicator vector of two distinct coordinates. -/
def pairIndicator (e f : ι) : ι → ℝ :=
  fun i ↦ if i = e ∨ i = f then 1 else 0

/-- Helper for Proposition 8.9: all two-coordinate indicators supported in `S`. -/
def pairIndicatorSet (S : Finset ι) : Set (ι → ℝ) :=
  {x | ∃ e f : ι, e ∈ S ∧ f ∈ S ∧ e ≠ f ∧ x = pairIndicator e f}

/-- Helper for Proposition 8.9: the rank-two unit-box slice supported in `S`. -/
def pairSlice (S : Finset ι) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧
    (∀ i, i ∉ S → x i = 0) ∧ S.sum x = 2}

/-- Helper for Proposition 8.9: coordinates strictly between the two unit-box endpoints. -/
def fractionalSupport (S : Finset ι) (x : ι → ℝ) : Finset ι :=
  S.filter fun i ↦ x i ≠ 0 ∧ x i ≠ 1

/-- Helper for Proposition 8.9: the sum of binary coordinates is the cardinality of their
nonzero support. -/
lemma sum_eq_card_filter_of_binary
    (S : Finset ι)
    (x : ι → ℝ)
    (hx : ∀ i ∈ S, x i = 0 ∨ x i = 1) :
    S.sum x = ((S.filter fun i ↦ x i ≠ 0).card : ℝ) := by
  -- Replace each binary coordinate by the indicator of its nonzero support.
  calc
    S.sum x = S.sum fun i ↦ if x i ≠ 0 then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rcases hx i hi with hxi | hxi
      · simp [hxi]
      · simp [hxi]
    _ = ((S.filter fun i ↦ x i ≠ 0).card : ℝ) :=
      (Finset.natCast_card_filter (fun i : ι ↦ x i ≠ 0) S).symm

/-- Helper for Proposition 8.9: a feasible rank-two slice has either no fractional coordinate
or at least two distinct fractional coordinates. -/
lemma fractionalSupport_eq_empty_or_pair
    (S : Finset ι)
    (x : ι → ℝ)
    (hx : x ∈ pairSlice S) :
    fractionalSupport S x = ∅ ∨
      ∃ e f : ι, e ∈ fractionalSupport S x ∧ f ∈ fractionalSupport S x ∧ e ≠ f := by
  by_cases hempty : fractionalSupport S x = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have heData : e ∈ S ∧ x e ≠ 0 ∧ x e ≠ 1 := by
      simpa [fractionalSupport] using he
    by_contra hpair
    have hOnly : ∀ f, f ∈ fractionalSupport S x → f = e := by
      intro f hf
      by_contra hfe
      exact hpair ⟨e, f, he, hf, Ne.symm hfe⟩
    have hOtherBinary : ∀ f ∈ S.erase e, x f = 0 ∨ x f = 1 := by
      intro f hf
      have hfS : f ∈ S := Finset.mem_of_mem_erase hf
      have hfe : f ≠ e := Finset.ne_of_mem_erase hf
      by_cases hf0 : x f = 0
      · exact Or.inl hf0
      · by_cases hf1 : x f = 1
        · exact Or.inr hf1
        · have hfFrac : f ∈ fractionalSupport S x := by
            simp [fractionalSupport, hfS, hf0, hf1]
          exact (hfe (hOnly f hfFrac)).elim
    have hRest := sum_eq_card_filter_of_binary (S.erase e) x hOtherBinary
    have hDecomp :
        S.sum x = (((S.erase e).filter fun f ↦ x f ≠ 0).card : ℝ) + x e := by
      rw [← Finset.sum_erase_add _ _ heData.1, hRest]
    have hLowerReal :
        (((S.erase e).filter fun f ↦ x f ≠ 0).card : ℝ) < 2 := by
      have hePos : 0 < x e := lt_of_le_of_ne (hx.1 e |>.1) (Ne.symm heData.2.1)
      linarith [hx.2.2, hDecomp]
    have hUpperReal :
        (2 : ℝ) < (((S.erase e).filter fun f ↦ x f ≠ 0).card : ℝ) + 1 := by
      have heLt : x e < 1 := lt_of_le_of_ne (hx.1 e |>.2) heData.2.2
      linarith [hx.2.2, hDecomp]
    have hLowerNat : ((S.erase e).filter fun f ↦ x f ≠ 0).card < 2 := by
      exact_mod_cast hLowerReal
    have hUpperNat : 2 < ((S.erase e).filter fun f ↦ x f ≠ 0).card + 1 := by
      exact_mod_cast hUpperReal
    omega

/-- Helper for Proposition 8.9: the rank-two slice is convex. -/
lemma pairSlice_convex (S : Finset ι) : Convex ℝ (pairSlice S) := by
  rintro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    -- Unit-box bounds are preserved coordinatewise by convex combinations.
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i |>.1)) (mul_nonneg hb (hy.1 i |>.1))
    · nlinarith [hx.1 i |>.2, hy.1 i |>.2]
  · intro i hi
    -- Both summands vanish away from the prescribed support.
    simp [hx.2.1 i hi, hy.2.1 i hi]
  · -- The fixed rank equation is affine-linear.
    calc
      S.sum (a • x + b • y) = a * S.sum x + b * S.sum y := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ = a * 2 + b * 2 := by rw [hx.2.2, hy.2.2]
      _ = 2 := by nlinarith

/-- Helper for Proposition 8.9: the finite-dimensional rank-two slice is compact. -/
lemma pairSlice_isCompact (S : Finset ι) : IsCompact (pairSlice S) := by
  have hSupportClosed : IsClosed {x : ι → ℝ | ∀ i, i ∉ S → x i = 0} := by
    have hEach : ∀ i : ι, IsClosed {x : ι → ℝ | i ∉ S → x i = 0} := by
      intro i
      by_cases hi : i ∈ S
      · simp [hi]
      · have hEval : Continuous (fun x : ι → ℝ ↦ x i) := continuous_apply i
        have hZero : Continuous (fun _ : ι → ℝ ↦ (0 : ℝ)) := continuous_const
        simpa [hi] using isClosed_eq hEval hZero
    rw [show {x : ι → ℝ | ∀ i, i ∉ S → x i = 0} =
        ⋂ i : ι, {x : ι → ℝ | i ∉ S → x i = 0} by ext; simp]
    exact isClosed_iInter hEach
  have hSumContinuous : Continuous (fun x : ι → ℝ ↦ S.sum x) := by
    fun_prop
  have hSumClosed : IsClosed {x : ι → ℝ | S.sum x = 2} :=
    isClosed_eq hSumContinuous continuous_const
  have hBoxCompact : IsCompact (Set.Icc (0 : ι → ℝ) (1 : ι → ℝ)) :=
    isCompact_Icc
  have hSlice :
      pairSlice S =
        (Set.Icc (0 : ι → ℝ) 1 ∩ {x | ∀ i, i ∉ S → x i = 0}) ∩
          {x | S.sum x = 2} := by
    ext x
    constructor
    · rintro ⟨hBounds, hSupport, hSum⟩
      refine ⟨⟨?_, hSupport⟩, hSum⟩
      exact ⟨fun i ↦ hBounds i |>.1, fun i ↦ hBounds i |>.2⟩
    · rintro ⟨⟨hBox, hSupport⟩, hSum⟩
      exact ⟨fun i ↦ ⟨hBox.1 i, hBox.2 i⟩, hSupport, hSum⟩
  -- The slice is a closed subset of the compact unit box.
  rw [hSlice]
  exact (hBoxCompact.inter_right hSupportClosed).inter_right hSumClosed

/-- Helper for Proposition 8.9: every extreme point of the rank-two slice is a two-coordinate
indicator. -/
lemma extremePoints_subset_pairIndicatorSet (S : Finset ι) :
    (pairSlice S).extremePoints ℝ ⊆ pairIndicatorSet S := by
  intro z hzExtreme
  have hz : z ∈ pairSlice S := extremePoints_subset hzExtreme
  have hzBinary : ∀ i, z i = 0 ∨ z i = 1 := by
    by_contra hBinary
    push Not at hBinary
    obtain ⟨i, hi0, hi1⟩ := hBinary
    have hiS : i ∈ S := by
      by_contra hiS
      exact hi0 (hz.2.1 i hiS)
    have hiFrac : i ∈ fractionalSupport S z := by
      simp [fractionalSupport, hiS, hi0, hi1]
    rcases fractionalSupport_eq_empty_or_pair S z hz with hempty | ⟨e, f, he, hf, hef⟩
    · exact (by simpa [hempty] using hiFrac)
    · have heData : e ∈ S ∧ z e ≠ 0 ∧ z e ≠ 1 := by
        simpa [fractionalSupport] using he
      have hfData : f ∈ S ∧ z f ≠ 0 ∧ z f ≠ 1 := by
        simpa [fractionalSupport] using hf
      have hePos : 0 < z e := lt_of_le_of_ne (hz.1 e |>.1) (Ne.symm heData.2.1)
      have heLt : z e < 1 := lt_of_le_of_ne (hz.1 e |>.2) heData.2.2
      have hfPos : 0 < z f := lt_of_le_of_ne (hz.1 f |>.1) (Ne.symm hfData.2.1)
      have hfLt : z f < 1 := lt_of_le_of_ne (hz.1 f |>.2) hfData.2.2
      let ε : ℝ := min (z e) (min (1 - z e) (min (z f) (1 - z f))) / 2
      have hεPos : 0 < ε := by
        dsimp [ε]
        positivity
      have hεLeE : ε ≤ z e := by
        dsimp [ε]
        nlinarith [min_le_left (z e) (min (1 - z e) (min (z f) (1 - z f)))]
      have hεLeEGap : ε ≤ 1 - z e := by
        dsimp [ε]
        nlinarith [min_le_right (z e) (min (1 - z e) (min (z f) (1 - z f))),
          min_le_left (1 - z e) (min (z f) (1 - z f))]
      have hεLeF : ε ≤ z f := by
        dsimp [ε]
        nlinarith [min_le_right (z e) (min (1 - z e) (min (z f) (1 - z f))),
          min_le_right (1 - z e) (min (z f) (1 - z f)),
          min_le_left (z f) (1 - z f)]
      have hεLeFGap : ε ≤ 1 - z f := by
        dsimp [ε]
        nlinarith [min_le_right (z e) (min (1 - z e) (min (z f) (1 - z f))),
          min_le_right (1 - z e) (min (z f) (1 - z f)),
          min_le_right (z f) (1 - z f)]
      let v : ι → ℝ := Pi.single e ε - Pi.single f ε
      have hsumV : S.sum v = 0 := by
        simp [v, Finset.sum_sub_distrib, heData.1, hfData.1]
      have hminus : z - v ∈ pairSlice S := by
        refine ⟨?_, ?_, ?_⟩
        · intro q
          by_cases hqe : q = e
          · subst q
            simp [v, hef]
            constructor <;> linarith
          · by_cases hqf : q = f
            · subst q
              simp [v, hef]
              constructor <;> linarith
            · simpa [v, hqe, hqf] using hz.1 q
        · intro q hqS
          have hqe : q ≠ e := fun h ↦ hqS (h ▸ heData.1)
          have hqf : q ≠ f := fun h ↦ hqS (h ▸ hfData.1)
          simp [v, hqe, hqf, hz.2.1 q hqS]
        · calc
            S.sum (z - v) = S.sum z - S.sum v := by
              simp only [Pi.sub_apply, Finset.sum_sub_distrib]
            _ = 2 := by rw [hz.2.2, hsumV, sub_zero]
      have hplus : z + v ∈ pairSlice S := by
        refine ⟨?_, ?_, ?_⟩
        · intro q
          by_cases hqe : q = e
          · subst q
            simp [v, hef]
            constructor <;> linarith
          · by_cases hqf : q = f
            · subst q
              simp [v, hef]
              constructor <;> linarith
            · simpa [v, hqe, hqf] using hz.1 q
        · intro q hqS
          have hqe : q ≠ e := fun h ↦ hqS (h ▸ heData.1)
          have hqf : q ≠ f := fun h ↦ hqS (h ▸ hfData.1)
          simp [v, hqe, hqf, hz.2.1 q hqS]
        · calc
            S.sum (z + v) = S.sum z + S.sum v := by
              simp only [Pi.add_apply, Finset.sum_add_distrib]
            _ = 2 := by rw [hz.2.2, hsumV, add_zero]
      have hminusNe : z - v ≠ z := by
        intro heq
        have heEq := congrFun heq e
        simp [v, hef, hεPos.ne'] at heEq
      exact hminusNe (hzExtreme.2 hminus hplus (mem_openSegment_sub_add z v))
  let U := S.filter fun i ↦ z i ≠ 0
  have hsumCard : S.sum z = (U.card : ℝ) := by
    simpa [U] using sum_eq_card_filter_of_binary S z (fun i _ ↦ hzBinary i)
  have hcard : U.card = 2 := by
    exact_mod_cast hsumCard.symm.trans hz.2.2
  obtain ⟨e, f, hef, hU⟩ := Finset.card_eq_two.mp hcard
  have heU : e ∈ U := by simp [hU]
  have hfU : f ∈ U := by simp [hU]
  have heS : e ∈ S := (Finset.mem_filter.mp heU).1
  have hfS : f ∈ S := (Finset.mem_filter.mp hfU).1
  refine ⟨e, f, heS, hfS, hef, ?_⟩
  -- The two nonzero binary coordinates determine the whole vector.
  ext q
  by_cases hqe : q = e
  · subst q
    rcases hzBinary e with he0 | he1
    · exact ((Finset.mem_filter.mp heU).2 he0).elim
    · simp [pairIndicator, he1]
  · by_cases hqf : q = f
    · subst q
      rcases hzBinary f with hf0 | hf1
      · exact ((Finset.mem_filter.mp hfU).2 hf0).elim
      · simp [pairIndicator, hf1]
    · have hzq : z q = 0 := by
        by_contra hzq
        have hqS : q ∈ S := by
          by_contra hqS
          exact hzq (hz.2.1 q hqS)
        have hqU : q ∈ U := Finset.mem_filter.mpr ⟨hqS, hzq⟩
        have hqPair : q = e ∨ q = f := by
          simpa [hU] using hqU
        exact hqPair.elim hqe hqf
      simp [pairIndicator, hqe, hqf, hzq]

/-- Helper for Proposition 8.9: the set of two-coordinate indicators on a finite support is
finite. -/
lemma pairIndicatorSet_finite (S : Finset ι) : (pairIndicatorSet S).Finite := by
  -- Every constrained generator lies in the finite range of the pair-indicator map.
  apply (Set.finite_range fun p : ι × ι ↦ pairIndicator p.1 p.2).subset
  rintro z ⟨e, f, _, _, _, rfl⟩
  exact ⟨(e, f), rfl⟩

/-- Helper for Proposition 8.9: every point of the rank-two unit-box slice is in the convex hull
of its two-coordinate indicator vectors. -/
theorem mem_convexHull_pairIndicatorSet
    (S : Finset ι)
    (x : ι → ℝ)
    (hxBounds : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hxSupport : ∀ i, i ∉ S → x i = 0)
    (hxSum : S.sum x = 2) :
    x ∈ convexHull ℝ (pairIndicatorSet S) := by
  have hx : x ∈ pairSlice S := ⟨hxBounds, hxSupport, hxSum⟩
  have hClosureSubset :
      closure (convexHull ℝ ((pairSlice S).extremePoints ℝ)) ⊆
        convexHull ℝ (pairIndicatorSet S) := by
    apply closure_minimal
    · exact convexHull_mono (extremePoints_subset_pairIndicatorSet S)
    · exact (pairIndicatorSet_finite S).isClosed_convexHull ℝ
  have hxClosure : x ∈ closure (convexHull ℝ ((pairSlice S).extremePoints ℝ)) := by
    rw [closure_convexHull_extremePoints (pairSlice_isCompact S) (pairSlice_convex S)]
    exact hx
  exact hClosureSubset hxClosure

end FinitePairSlice
