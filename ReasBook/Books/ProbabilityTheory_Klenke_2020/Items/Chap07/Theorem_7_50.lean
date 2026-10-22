/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_2_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_5_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Lemma_7_49

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ContinuousLinearMap ENNReal Filter
open scoped BigOperators Topology symmDiff

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

local instance : Fact (1 ≤ conjExponent p) :=
  ⟨HolderConjugate.one_le (conjExponent p) p⟩

section Duality

variable [SigmaFinite μ]
variable [Fact (p < ∞)]

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: pairing against the indicator of a finite-measure set recovers the
corresponding set integral. -/
lemma lpPairing_indicatorConstLp_one
    (f : Lp ℝ (conjExponent p) μ) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    (mul ℝ ℝ).lpPairing μ (conjExponent p) p f
        (indicatorConstLp p hs hμs (1 : ℝ)) = ∫ x in s, f x ∂μ := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  calc
    ∫ x, f x * indicatorConstLp p hs hμs (1 : ℝ) x ∂μ = ∫ x, s.indicator f x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards
        [show (indicatorConstLp p hs hμs (1 : ℝ) : Ω → ℝ) =ᵐ[μ] s.indicator fun _ ↦ (1 : ℝ) from
          indicatorConstLp_coeFn] with x hx
      simp [hx, Set.indicator]
    _ = ∫ x in s, f x ∂μ := integral_indicator hs

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: pairing against a constant indicator function is the corresponding
set integral with that constant pulled into the integrand. -/
lemma lpPairing_indicatorConstLp_const
    (f : Lp ℝ (conjExponent p) μ) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) :
    (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (indicatorConstLp p hs hμs c)
      = ∫ x in s, c * f x ∂μ := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  calc
    ∫ x, f x * indicatorConstLp p hs hμs c x ∂μ = ∫ x, s.indicator (fun x ↦ c * f x) x ∂μ := by
      -- Replace the `Lp` indicator by its pointwise representative.
      refine integral_congr_ae ?_
      filter_upwards
        [show (indicatorConstLp p hs hμs c : Ω → ℝ) =ᵐ[μ] s.indicator fun _ ↦ c from
          indicatorConstLp_coeFn] with x hx
      by_cases hxs : x ∈ s
      · simp [hx, hxs, Set.indicator_of_mem, mul_comm]
      · simp [hx, hxs, Set.indicator_of_notMem]
    _ = ∫ x in s, c * f x ∂μ := integral_indicator hs

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: every continuous linear functional on `L^p(μ)` satisfies the
indicator estimate used to build the localized signed measures in the surjectivity argument. -/
lemma indicator_functional_bound
    (F : StrongDual ℝ (Lp ℝ p μ)) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ‖F (indicatorConstLp p hs hμs (1 : ℝ))‖ ≤ ‖F‖ * μ.real s ^ (1 / p.toReal) := by
  calc
    ‖F (indicatorConstLp p hs hμs (1 : ℝ))‖
      ≤ ‖F‖ * ‖indicatorConstLp p hs hμs (1 : ℝ)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖F‖ * (‖(1 : ℝ)‖ * μ.real s ^ (1 / p.toReal)) := by
      gcongr
      exact
        (show ‖indicatorConstLp p hs hμs (1 : ℝ)‖
            ≤ ‖(1 : ℝ)‖ * μ.real s ^ (1 / p.toReal) from norm_indicatorConstLp_le)
    _ = ‖F‖ * μ.real s ^ (1 / p.toReal) := by simp

omit [SigmaFinite μ] in
/-- Helper for Theorem 7.50: once a candidate density matches a functional on indicator constants,
`Lp.induction` upgrades that agreement to all of `L^p(μ)`. -/
lemma functional_eq_lpPairing_of_indicatorConst
    (F : StrongDual ℝ (Lp ℝ p μ)) (f : Lp ℝ (conjExponent p) μ)
    (hind :
      ∀ (c : ℝ) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s < ∞),
        F (indicatorConstLp p hs hμs.ne c) =
          (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (indicatorConstLp p hs hμs.ne c)) :
    F = (mul ℝ ℝ).lpPairing μ (conjExponent p) p f := by
  let motive : Lp ℝ p μ → Prop := fun g ↦
    F g = (mul ℝ ℝ).lpPairing μ (conjExponent p) p f g
  have hclosed : IsClosed {g : Lp ℝ p μ | motive g} := by
    -- Equality sets of continuous maps are closed.
    simpa [motive] using isClosed_eq F.continuous
      ((mul ℝ ℝ).lpPairing μ (conjExponent p) p f).continuous
  have hall : ∀ g : Lp ℝ p μ, motive g := by
    refine MeasureTheory.Lp.induction ((Fact.out : p < ∞).ne) motive ?_ ?_ hclosed
    · intro c s hs hμs
      -- The induction starts from indicator constants, where the hypothesis gives the formula.
      simpa [motive] using hind c hs hμs
    · intro g h hg hhg hdisj hh hh'
      -- The motive is stable under disjoint sums because both sides are linear.
      calc
        F (hg.toLp g + hhg.toLp h) = F (hg.toLp g) + F (hhg.toLp h) := by
          rw [map_add]
        _ = (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (hg.toLp g) +
              (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (hhg.toLp h) := by
          rw [hh, hh']
        _ = (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (hg.toLp g + hhg.toLp h) := by
          rw [map_add]
  ext g
  exact hall g

omit [SigmaFinite μ] in
/-- Helper for Theorem 7.50: transporting an `Lp` vector across an equality of exponents preserves
its norm. -/
lemma lpNorm_cast_eq {p q : ℝ≥0∞} (h : p = q) (f : Lp ℝ p μ) :
    ‖cast (by rw [h]) f‖ = ‖f‖ := by
  -- After rewriting the exponent, the casted `Lp` term is definitionally the same vector.
  subst h
  rfl

omit [SigmaFinite μ] in
/-- Helper for Theorem 7.50: transporting an `Lp` vector across an equality of exponents preserves
its almost-everywhere representative. -/
lemma lpCast_coeFn_aeEq {p q : ℝ≥0∞} (h : p = q) (f : Lp ℝ p μ) :
    ((cast (by rw [h]) f : Lp ℝ q μ) : Ω → ℝ) =ᵐ[μ] f := by
  -- After rewriting the exponent, the casted `Lp` term has the same underlying `AEEqFun`.
  subst h
  rfl

/-- Helper for Theorem 7.50: the disjoint finite exhaustion piece obtained from the sigma-finite
spanning sets of `μ`. -/
def dualityPiece (μ : Measure Ω) [SigmaFinite μ] (n : ℕ) : Set Ω :=
  disjointed (spanningSets μ) n

/-- Helper for Theorem 7.50: each `dualityPiece μ n` is measurable. -/
lemma measurableSet_dualityPiece (n : ℕ) :
    MeasurableSet (dualityPiece μ n) := by
  -- The disjointed refinement preserves measurability of the sigma-finite exhaustion pieces.
  simpa [dualityPiece] using
    (MeasurableSet.disjointed fun i ↦ measurableSet_spanningSets μ i) n

/-- Helper for Theorem 7.50: each `dualityPiece μ n` has finite `μ`-measure. -/
lemma measure_dualityPiece_lt_top (n : ℕ) :
    μ (dualityPiece μ n) < ∞ := by
  -- Each disjointed piece sits inside the corresponding spanning set, which already has finite
  -- measure.
  refine lt_of_le_of_lt (measure_mono ?_) (measure_spanningSets_lt_top μ n)
  simpa [dualityPiece] using (disjointed_subset (spanningSets μ) n)

/-- Helper for Theorem 7.50: the pieces `dualityPiece μ n` are pairwise disjoint. -/
lemma pairwiseDisjoint_dualityPiece :
    Pairwise fun i j ↦ Disjoint (dualityPiece μ i) (dualityPiece μ j) := by
  -- The `disjointed` construction removes all earlier overlap by design.
  simpa [dualityPiece] using (disjoint_disjointed (spanningSets μ))

/-- Helper for Theorem 7.50: the disjoint pieces `dualityPiece μ n` still cover the whole space. -/
lemma iUnion_dualityPiece :
    (⋃ n, dualityPiece μ n) = Set.univ := by
  -- Disjointifying the spanning sets keeps their union unchanged.
  simpa [dualityPiece] using
    (iUnion_disjointed : (⋃ n, disjointed (spanningSets μ) n) = ⋃ n, spanningSets μ n)

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: the `Lp` indicator of a finite disjoint union is the sum of the
indicators of its pieces. -/
lemma indicatorConstLp_finset_biUnion
    (B : ℕ → Set Ω) (hB_meas : ∀ k, MeasurableSet (B k))
    (hB_finite : ∀ k, μ (B k) < ∞)
    (hB_disj : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (s : Finset ℕ) (hsUnion : MeasurableSet (⋃ k ∈ s, B k))
    (hμUnion : μ (⋃ k ∈ s, B k) < ∞) :
    indicatorConstLp p hsUnion hμUnion.ne (1 : ℝ) =
      ∑ k ∈ s, indicatorConstLp p (hB_meas k) (hB_finite k).ne (1 : ℝ) := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty finite union gives the zero indicator, matching the empty sum.
      simp [MeasureTheory.indicatorConstLp_empty]
  | @insert a s ha hs =>
      have hs_meas : MeasurableSet (⋃ k ∈ s, B k) := by
        -- The remaining finite union is measurable because each piece is measurable.
        exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ : k ∈ s ↦ hB_meas k
      have hμs : μ (⋃ k ∈ s, B k) < ∞ :=
        measure_biUnion_lt_top s.finite_toSet fun i _hi ↦ hB_finite i
      have hdisj : Disjoint (B a) (⋃ k ∈ s, B k) := by
        -- Pairwise disjointness of the family makes the inserted piece disjoint from the old union.
        refine Set.disjoint_iUnion_right.2 ?_
        intro k
        refine Set.disjoint_iUnion_right.2 ?_
        intro hk
        exact hB_disj (by exact fun h ↦ ha (h ▸ hk))
      have hμinsert : μ (B a ∪ ⋃ k ∈ s, B k) < ∞ := measure_union_lt_top (hB_finite a) hμs
      -- Reassociate the inserted union into a binary disjoint union, then use the induction
      -- hypothesis on the old finite part.
      simpa [Finset.set_biUnion_insert, Finset.sum_insert, ha] using
        (show indicatorConstLp p ((hB_meas a).union hs_meas) hμinsert.ne (1 : ℝ) =
            indicatorConstLp p (hB_meas a) (hB_finite a).ne (1 : ℝ) +
              ∑ k ∈ s, indicatorConstLp p (hB_meas k) (hB_finite k).ne (1 : ℝ) by
          rw [MeasureTheory.indicatorConstLp_disjoint_union
            (hB_meas a) hs_meas (hB_finite a).ne hμs.ne hdisj]
          rw [hs hs_meas hμs])

/-- Helper for Theorem 7.50: every finite union of localized sets stays inside the chosen
duality piece. -/
lemma biUnion_finset_inter_dualityPiece_subset
    (A : ℕ → Set Ω) (n : ℕ) (s : Finset ℕ) :
    (⋃ k ∈ s, A k ∩ dualityPiece μ n) ⊆ dualityPiece μ n := by
  -- Each summand is already intersected with the piece, so the finite union remains inside it.
  intro x hx
  simp only [Set.mem_iUnion] at hx
  rcases hx with ⟨k, hk, hxk⟩
  exact hxk.2

/-- Helper for Theorem 7.50: every localized measurable set has finite measure because it lies in
one duality piece of finite measure. -/
lemma measure_inter_dualityPiece_lt_top
    (A : Set Ω) (n : ℕ) :
    μ (A ∩ dualityPiece μ n) < ∞ := by
  -- Measure monotonicity reduces the claim to the ambient finiteness of the chosen duality piece.
  refine lt_of_le_of_lt (measure_mono Set.inter_subset_right)
    (measure_dualityPiece_lt_top n)

/-- Helper for Theorem 7.50: every finite localized union has finite measure because it stays
inside one duality piece. -/
lemma measure_biUnion_finset_inter_dualityPiece_lt_top
    (A : ℕ → Set Ω) (n : ℕ) (s : Finset ℕ) :
    μ (⋃ k ∈ s, A k ∩ dualityPiece μ n) < ∞ := by
  -- Measure monotonicity reduces the claim to the finiteness of the ambient duality piece.
  have hpiece : μ (dualityPiece μ n) < ∞ := by
    show μ (dualityPiece μ n) < ∞
    exact measure_dualityPiece_lt_top n
  refine lt_of_le_of_lt ?_ hpiece
  exact
    (measure_mono (biUnion_finset_inter_dualityPiece_subset A n s) :
      μ (⋃ k ∈ s, A k ∩ dualityPiece μ n) ≤ μ (dualityPiece μ n))

/-- Helper for Theorem 7.50: every finite union of localized sets stays inside the chosen
duality piece. -/
lemma biUnion_range_inter_dualityPiece_subset
    (A : ℕ → Set Ω) (n N : ℕ) :
    (⋃ k ∈ Finset.range N, A k ∩ dualityPiece μ n) ⊆ dualityPiece μ n := by
  -- Each summand is already intersected with the piece, so the finite union remains inside it.
  exact biUnion_finset_inter_dualityPiece_subset A n (Finset.range N)

/-- Helper for Theorem 7.50: the localized finite unions have finite measure because they are
contained in one finite duality piece. -/
lemma measure_biUnion_range_inter_dualityPiece_lt_top
    (A : ℕ → Set Ω) (n N : ℕ) :
    μ (⋃ k ∈ Finset.range N, A k ∩ dualityPiece μ n) < ∞ := by
  -- Measure monotonicity reduces the claim to the finiteness of the ambient duality piece.
  exact measure_biUnion_finset_inter_dualityPiece_lt_top A n (Finset.range N)

/-- Helper for Theorem 7.50: every localized tail union still stays inside the chosen duality
piece. -/
lemma iUnion_Ici_inter_dualityPiece_subset
    (A : ℕ → Set Ω) (n N : ℕ) :
    (⋃ k ≥ N, A k ∩ dualityPiece μ n) ⊆ dualityPiece μ n := by
  -- Every point in the tail already lies in one set intersected with the ambient piece.
  intro x hx
  simp only [Set.mem_iUnion, exists_prop] at hx
  rcases hx with ⟨k, hk, hxk⟩
  exact hxk.2

/-- Helper for Theorem 7.50: the localized tail unions have finite measure because they are also
contained in one finite duality piece. -/
lemma measure_iUnion_Ici_inter_dualityPiece_lt_top
    (A : ℕ → Set Ω) (n N : ℕ) :
    μ (⋃ k ≥ N, A k ∩ dualityPiece μ n) < ∞ := by
  -- The same monotonicity argument as for finite unions applies to the countable tail.
  have hpiece : μ (dualityPiece μ n) < ∞ := by
    show μ (dualityPiece μ n) < ∞
    exact measure_dualityPiece_lt_top n
  refine lt_of_le_of_lt ?_ hpiece
  exact
    (measure_mono (iUnion_Ici_inter_dualityPiece_subset A n N) :
      μ (⋃ k ≥ N, A k ∩ dualityPiece μ n) ≤ μ (dualityPiece μ n))

/-- Helper for Theorem 7.50: on each fixed duality piece, the measures of the localized tails of a
pairwise disjoint family tend to `0`. -/
lemma localizedTailMeasureInterDualityPieceTendstoZero
    (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j)) (n : ℕ) :
    Filter.Tendsto (fun N ↦ μ (⋃ k ≥ N, A k ∩ dualityPiece μ n)) atTop (𝓝 0) := by
  let ν : Measure Ω := μ.restrict (dualityPiece μ n)
  letI : IsFiniteMeasure ν :=
    ⟨by
      -- The restricted measure is finite because each duality piece has finite ambient measure.
      simpa [ν, Measure.restrict_apply, measurableSet_dualityPiece n] using
        measure_dualityPiece_lt_top n⟩
  have hν_tendsto : Filter.Tendsto (fun N ↦ ν (⋃ k ≥ N, A k)) atTop (𝓝 0) := by
    -- On the finite restricted measure, continuity from above for pairwise disjoint tails applies
    -- directly to the original family `A`.
    simpa [Function.comp] using
      (tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
        (fun k ↦ (hA_meas k).nullMeasurableSet)
        hA_disj)
  refine hν_tendsto.congr' ?_
  refine Filter.Eventually.of_forall ?_
  intro N
  have hTailMeas : MeasurableSet (⋃ k ≥ N, A k) := by
    -- The tail union is measurable because it is a countable union of measurable sets.
    exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ : N ≤ k ↦ hA_meas k
  -- Rewrite the restricted-measure tail back into the ambient localized tail.
  simp [ν, Measure.restrict_apply, hTailMeas, Set.iUnion₂_inter]

/-- Helper for Theorem 7.50: normalize a limit target of the form `0 ^ r` back to `0`. -/
lemma tendstoZeroRpowTarget {α : Type*} {l : Filter α} {u : α → ℝ} {r : ℝ}
    (hr : r ≠ 0) (h : Filter.Tendsto u l (𝓝 ((0 : ℝ) ^ r))) :
    Filter.Tendsto u l (𝓝 0) := by
  -- Rewrite the target once with `Real.zero_rpow` so later tail proofs can stay in the `𝓝 0`
  -- normal form.
  simpa [Real.zero_rpow hr] using h

/-- Helper for Theorem 7.50: after converting localized tail measures to real numbers, raising
them to the exponent `1 / p.toReal` still tends to `0`. -/
lemma localizedTailRealRpowTendstoZero
    (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j)) (n : ℕ) :
    Filter.Tendsto
      (fun N ↦ μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) ^ (1 / p.toReal))
      atTop (𝓝 0) := by
  let r : ℝ := 1 / p.toReal
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp_finite : p < ∞ := Fact.out
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp_one).ne' hp_finite.ne
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg zero_le_one hp_toReal_pos.le
  have hr_ne_zero : r ≠ 0 := by
    dsimp [r]
    exact one_div_ne_zero hp_toReal_pos.ne'
  have htoReal :
      Filter.Tendsto
        (fun N ↦ μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n))
        atTop
        (𝓝 0) := by
    -- First move the localized tail measure from `ℝ≥0∞` to `ℝ`.
    simpa [MeasureTheory.measureReal_def, measure_iUnion_Ici_inter_dualityPiece_lt_top A n]
      using
        ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
          (localizedTailMeasureInterDualityPieceTendstoZero A hA_meas hA_disj n))
  have hrpow :
      Filter.Tendsto
        (fun N ↦ μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) ^ r)
        atTop
        (𝓝 ((0 : ℝ) ^ r)) := by
    -- Then apply the continuous `rpow` map at the nonnegative exponent `r`.
    exact htoReal.rpow_const (Or.inr hr_nonneg)
  -- Finally normalize the target back to `𝓝 0`.
  simpa [r] using tendstoZeroRpowTarget hr_ne_zero hrpow

/-- Helper for Theorem 7.50: on each fixed duality piece, the localized indicator tails are sent to
`0` by the functional. -/
lemma localizedIndicatorTailTendstoZero
    (F : StrongDual ℝ (Lp ℝ p μ)) (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j)) (n : ℕ) :
    Filter.Tendsto
      (fun N ↦
        F
          (indicatorConstLp p
            (MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun (_ : N ≤ k) ↦
              (hA_meas k).inter (measurableSet_dualityPiece n))
            (measure_iUnion_Ici_inter_dualityPiece_lt_top A n N).ne
            (1 : ℝ)))
      atTop (𝓝 0) := by
  let tailSet : ℕ → Set Ω := fun N ↦
    ⋃ k ≥ N, A k ∩ dualityPiece μ n
  have hTail : Filter.Tendsto (fun N ↦ μ (tailSet N ∆ (∅ : Set Ω))) atTop (𝓝 0) := by
    -- The underlying localized sets shrink to the empty set in measure on the fixed duality piece.
    simpa [tailSet, Set.symmDiff_def] using
      localizedTailMeasureInterDualityPieceTendstoZero A hA_meas hA_disj n
  let tailIndicator : ℕ → Lp ℝ p μ := fun N ↦
    indicatorConstLp p
      (MeasurableSet.iUnion fun k ↦
        MeasurableSet.iUnion fun (_ : N ≤ k) ↦
          (hA_meas k).inter (measurableSet_dualityPiece n))
      (measure_iUnion_Ici_inter_dualityPiece_lt_top A n N).ne
      (1 : ℝ)
  let emptyIndicator : Lp ℝ p μ := indicatorConstLp p MeasurableSet.empty (by simp) (1 : ℝ)
  have hIndicator : Filter.Tendsto tailIndicator atTop (𝓝 emptyIndicator) := by
    -- Indicator functions vary continuously in `Lp` with respect to the measure of the symmetric
    -- difference of the underlying sets.
    exact
      @MeasureTheory.tendsto_indicatorConstLp_set
        Ω ℝ _ p μ _ (∅ : Set Ω) MeasurableSet.empty (by simp) (1 : ℝ) _ ℕ atTop tailSet
        (fun N ↦
          MeasurableSet.iUnion fun k ↦
            MeasurableSet.iUnion fun (_ : N ≤ k) ↦
              (hA_meas k).inter (measurableSet_dualityPiece n))
        (fun N ↦ (measure_iUnion_Ici_inter_dualityPiece_lt_top A n N).ne)
        ((Fact.out : p < ∞).ne) hTail
  -- Compose the `Lp` convergence with continuity of the functional `F`.
  simpa [tailIndicator, emptyIndicator, MeasureTheory.indicatorConstLp_empty] using
    (F.continuous.tendsto _).comp hIndicator

omit [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: on one duality piece, the finite partial sum of disjoint indicators is
the indicator of the corresponding finite union. -/
lemma sum_indicatorConstLp_range_inter_dualityPiece
    (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j))
    (n N : ℕ) (hsUnion : MeasurableSet (⋃ k ∈ Finset.range N, A k ∩ dualityPiece μ n))
    (hμUnion : μ (⋃ k ∈ Finset.range N, A k ∩ dualityPiece μ n) < ∞) :
    ∑ k ∈ Finset.range N,
      indicatorConstLp p
        ((hA_meas k).inter (measurableSet_dualityPiece n))
        (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
          (measure_dualityPiece_lt_top n)).ne
        (1 : ℝ)
      = indicatorConstLp p hsUnion hμUnion.ne (1 : ℝ) := by
  -- Package the finite partial sum as a single indicator on the finite localized union.
  symm
  refine indicatorConstLp_finset_biUnion (fun k ↦ A k ∩ dualityPiece μ n)
    (fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
    (fun k ↦
      lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_dualityPiece_lt_top n))
    ?_ (Finset.range N) hsUnion hμUnion
  -- Intersecting a pairwise disjoint family with a fixed piece keeps it pairwise disjoint.
  intro i j hij
  refine Set.disjoint_left.2 ?_
  intro x hxi hxj
  exact (Set.disjoint_left.mp (hA_disj hij) hxi.1) hxj.1

/-- Helper for Theorem 7.50: once a finite set contains `range N`, the omitted localized support
is contained in the localized `N`-tail. -/
lemma localizedResidualSubset_tail
    (A : ℕ → Set Ω) (n N : ℕ) (s : Finset ℕ) (hNs : Finset.range N ⊆ s) :
    ((⋃ k, A k ∩ dualityPiece μ n) \ (⋃ k ∈ s, A k ∩ dualityPiece μ n))
      ⊆ ⋃ k ≥ N, A k ∩ dualityPiece μ n := by
  -- Any omitted point still lies in one localized piece, and that index cannot be below `N`.
  intro x hx
  rcases Set.mem_iUnion.1 hx.1 with ⟨k, hk⟩
  have hk_not_mem : k ∉ s := by
    intro hks
    exact hx.2 <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hks, hk⟩⟩
  have hNk : N ≤ k := by
    by_contra hNk
    have hk_range : k ∈ Finset.range N := by
      simpa [Finset.mem_range] using Nat.lt_of_not_ge hNk
    exact hk_not_mem (hNs hk_range)
  exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hNk, hk⟩⟩

/-- Helper for Theorem 7.50: localizing a countable union to one duality piece distributes over the
union. -/
lemma iUnion_inter_dualityPiece_eq
    (A : ℕ → Set Ω) (n : ℕ) :
    (⋃ i, A i) ∩ dualityPiece μ n = ⋃ i, A i ∩ dualityPiece μ n := by
  -- Both descriptions say exactly that a point lies in some `A i` and in the chosen duality piece.
  ext x
  simp

/-- Helper for Theorem 7.50: once a finite set contains `range N`, the remaining localized
indicator error is supported inside the `N`-tail on the chosen duality piece. -/
lemma localizedIndicatorFiniteSetResidualBound
    (F : StrongDual ℝ (Lp ℝ p μ)) (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j))
    (n N : ℕ) (s : Finset ℕ) (hNs : Finset.range N ⊆ s) :
    ‖F
        (indicatorConstLp p
          (MeasurableSet.iUnion fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
          (by
            have hμ : μ (⋃ k, A k ∩ dualityPiece μ n) < ∞ := by
              simpa using measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
            exact hμ.ne)
          (1 : ℝ)) -
      ∑ k ∈ s,
        F
          (indicatorConstLp p
            ((hA_meas k).inter (measurableSet_dualityPiece n))
            (measure_inter_dualityPiece_lt_top (A k) n).ne
            (1 : ℝ))‖
      ≤ ‖F‖ * μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) ^ (1 / p.toReal) := by
  let fullSet : Set Ω := ⋃ k, A k ∩ dualityPiece μ n
  let partialSet : Set Ω := ⋃ k ∈ s, A k ∩ dualityPiece μ n
  let residualSet : Set Ω := fullSet \ partialSet
  let tailSet : Set Ω := ⋃ k ≥ N, A k ∩ dualityPiece μ n
  let fullIndicator : Lp ℝ p μ :=
    indicatorConstLp p
      (MeasurableSet.iUnion fun k ↦
        (hA_meas k).inter (measurableSet_dualityPiece n))
      (by
        have hμ : μ fullSet < ∞ := by
          simpa [fullSet] using measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
        exact hμ.ne)
      (1 : ℝ)
  let partialIndicator : Lp ℝ p μ :=
    indicatorConstLp p
      (MeasurableSet.iUnion fun k ↦
        MeasurableSet.iUnion fun (_ : k ∈ s) ↦
          (hA_meas k).inter (measurableSet_dualityPiece n))
      (measure_biUnion_finset_inter_dualityPiece_lt_top A n s).ne
      (1 : ℝ)
  let residualIndicator : Lp ℝ p μ :=
    indicatorConstLp p
      ((MeasurableSet.iUnion fun k ↦
          (hA_meas k).inter (measurableSet_dualityPiece n)).diff
        (MeasurableSet.iUnion fun k ↦
          MeasurableSet.iUnion fun (_ : k ∈ s) ↦
            (hA_meas k).inter (measurableSet_dualityPiece n)))
      (by
        have hμ : μ residualSet < ∞ := by
          refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
          have hμfull : μ fullSet < ∞ := by
            simpa [fullSet] using
              measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
          exact hμfull
        exact hμ.ne)
      (1 : ℝ)
  let pieceIndicator : ℕ → Lp ℝ p μ := fun k ↦
    indicatorConstLp p
      ((hA_meas k).inter (measurableSet_dualityPiece n))
      (measure_inter_dualityPiece_lt_top (A k) n).ne
      (1 : ℝ)
  have hPartial_subset_full : partialSet ⊆ fullSet := by
    -- Every localized point chosen by the finite union also belongs to the full localized union.
    intro x hx
    simp only [partialSet, fullSet, Set.mem_iUnion] at hx ⊢
    rcases hx with ⟨k, hk, hxk⟩
    exact ⟨k, hxk⟩
  have hPartial_eq_sum :
      partialIndicator = ∑ k ∈ s, pieceIndicator k := by
    -- Collapse the disjoint finite localized union to one `indicatorConstLp`.
    simpa [partialSet, partialIndicator, pieceIndicator] using
      indicatorConstLp_finset_biUnion
        (fun k ↦ A k ∩ dualityPiece μ n)
        (fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
        (fun k ↦ measure_inter_dualityPiece_lt_top (A k) n)
        (by
          intro i j hij
          refine Set.disjoint_left.2 ?_
          intro x hxi hxj
          exact (Set.disjoint_left.mp (hA_disj hij) hxi.1) hxj.1)
        s
        (MeasurableSet.iUnion fun k ↦
          MeasurableSet.iUnion fun (_ : k ∈ s) ↦
            (hA_meas k).inter (measurableSet_dualityPiece n))
        (measure_biUnion_finset_inter_dualityPiece_lt_top A n s)
  have hIndicator_split :
      fullIndicator = residualIndicator + partialIndicator := by
    -- Split the full localized union into the finite part already summed and the omitted residual.
    have hUnion : residualSet ∪ partialSet = fullSet := by
      simpa [residualSet] using Set.diff_union_of_subset hPartial_subset_full
    have hSplitRaw :
        indicatorConstLp p
            ((MeasurableSet.iUnion fun k ↦
                (hA_meas k).inter (measurableSet_dualityPiece n)).diff
              (MeasurableSet.iUnion fun k ↦
                MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                  (hA_meas k).inter (measurableSet_dualityPiece n)))
            (by
              have hμ : μ residualSet < ∞ := by
                refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
                have hμfull : μ fullSet < ∞ := by
                  simpa [fullSet] using
                    measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
                exact hμfull
              exact hμ.ne)
            (1 : ℝ) +
          indicatorConstLp p
            (MeasurableSet.iUnion fun k ↦
              MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                (hA_meas k).inter (measurableSet_dualityPiece n))
            (measure_biUnion_finset_inter_dualityPiece_lt_top A n s).ne
            (1 : ℝ) =
          indicatorConstLp p
            (((MeasurableSet.iUnion fun k ↦
                (hA_meas k).inter (measurableSet_dualityPiece n)).diff
              (MeasurableSet.iUnion fun k ↦
                MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                  (hA_meas k).inter (measurableSet_dualityPiece n))).union
              (MeasurableSet.iUnion fun k ↦
                MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                  (hA_meas k).inter (measurableSet_dualityPiece n)))
            (by
              have hμ : μ (residualSet ∪ partialSet) < ∞ := by
                simpa [hUnion] using
                  measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
              exact hμ.ne)
            (1 : ℝ) := by
      symm
      exact
        @MeasureTheory.indicatorConstLp_disjoint_union
          Ω ℝ _ p μ _
          residualSet partialSet
          ((MeasurableSet.iUnion fun k ↦
              (hA_meas k).inter (measurableSet_dualityPiece n)).diff
            (MeasurableSet.iUnion fun k ↦
              MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                (hA_meas k).inter (measurableSet_dualityPiece n)))
          (MeasurableSet.iUnion fun k ↦
            MeasurableSet.iUnion fun (_ : k ∈ s) ↦
              (hA_meas k).inter (measurableSet_dualityPiece n))
          (by
            have hμ : μ residualSet < ∞ := by
              refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
              have hμfull : μ fullSet < ∞ := by
                simpa [fullSet] using
                  measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
              exact hμfull
            exact hμ.ne)
          (measure_biUnion_finset_inter_dualityPiece_lt_top A n s).ne
          Set.disjoint_sdiff_left
          (1 : ℝ)
    simpa [fullSet, partialSet, residualSet, fullIndicator, partialIndicator, residualIndicator,
      hUnion, Set.union_comm] using hSplitRaw.symm
  have hSub :
      fullIndicator - partialIndicator = residualIndicator := by
    -- Convert the disjoint-union decomposition into the subtraction form used by `map_sub`.
    exact (sub_eq_iff_eq_add).2 hIndicator_split
  have hExp_nonneg : 0 ≤ 1 / p.toReal := by
    have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
    have hp_finite : p < ∞ := Fact.out
    have hp_toReal_pos : 0 < p.toReal :=
      ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp_one).ne' hp_finite.ne
    exact div_nonneg zero_le_one hp_toReal_pos.le
  calc
    ‖F
        (indicatorConstLp p
          (MeasurableSet.iUnion fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
          (by
            have hμ : μ (⋃ k, A k ∩ dualityPiece μ n) < ∞ := by
              simpa using measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
            exact hμ.ne)
          (1 : ℝ)) -
      ∑ k ∈ s,
        F
          (indicatorConstLp p
            ((hA_meas k).inter (measurableSet_dualityPiece n))
            (measure_inter_dualityPiece_lt_top (A k) n).ne
            (1 : ℝ))‖
      = ‖F fullIndicator - F partialIndicator‖ := by
          change
            ‖F fullIndicator - ∑ k ∈ s, F (pieceIndicator k)‖ =
              ‖F fullIndicator - F partialIndicator‖
          rw [← map_sum, hPartial_eq_sum]
    _ = ‖F (fullIndicator - partialIndicator)‖ := by
          rw [map_sub]
    _ = ‖F residualIndicator‖ := by
          rw [hSub]
    _ ≤ ‖F‖ * μ.real residualSet ^ (1 / p.toReal) := by
          exact indicator_functional_bound F
            (((MeasurableSet.iUnion fun k ↦
                (hA_meas k).inter (measurableSet_dualityPiece n)).diff
              (MeasurableSet.iUnion fun k ↦
                MeasurableSet.iUnion fun (_ : k ∈ s) ↦
                  (hA_meas k).inter (measurableSet_dualityPiece n))))
            (by
              have hμ : μ residualSet < ∞ := by
                refine lt_of_le_of_lt (measure_mono Set.diff_subset) ?_
                have hμfull : μ fullSet < ∞ := by
                  simpa [fullSet] using
                    measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
                exact hμfull
              exact hμ.ne)
    _ ≤ ‖F‖ * μ.real tailSet ^ (1 / p.toReal) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact Real.rpow_le_rpow
            (show 0 ≤ μ.real residualSet from by simp)
            (MeasureTheory.measureReal_mono
              (localizedResidualSubset_tail A n N s hNs)
              (measure_iUnion_Ici_inter_dualityPiece_lt_top A n N).ne)
            hExp_nonneg
    _ = ‖F‖ * μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) ^ (1 / p.toReal) := by
          rfl

/-- Helper for Theorem 7.50: a finset net converges once every sufficiently large finite superset
of `range N` has error controlled by a scalar tail bound tending to `0`. -/
lemma tendstoFinsetOfTailControl
    (u : Finset ℕ → ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hb_tendsto : Filter.Tendsto b atTop (𝓝 0))
    (hb_nonneg : ∀ N, 0 ≤ b N)
    (hbound : ∀ N s, Finset.range N ⊆ s → ‖u s - a‖ ≤ b N) :
    Filter.Tendsto u atTop (𝓝 a) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  rcases Metric.tendsto_atTop.1 hb_tendsto ε hε with ⟨N, hN⟩
  have hbN_lt : b N < ε := by
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (hb_nonneg N)] using hN N le_rfl
  refine ⟨Finset.range N, ?_⟩
  intro s hs
  have hs' : Finset.range N ⊆ s := by
    simpa [Finset.le_iff_subset] using hs
  exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hbound N s hs') hbN_lt

/-- Helper for Theorem 7.50: the localized indicator functional is countably additive on one fixed
duality piece in the unconditional `HasSum` sense required by `SignedMeasure`. -/
lemma localizedIndicatorFunctionalHasSumOnDualityPiece
    (F : StrongDual ℝ (Lp ℝ p μ)) (A : ℕ → Set Ω) (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j)) (n : ℕ) :
    HasSum
      (fun k ↦
        F
          (indicatorConstLp p
            ((hA_meas k).inter (measurableSet_dualityPiece n))
            (measure_inter_dualityPiece_lt_top (A k) n).ne
            (1 : ℝ)))
      (F
        (indicatorConstLp p
          (MeasurableSet.iUnion fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
          (by
            have hμ : μ (⋃ k, A k ∩ dualityPiece μ n) < ∞ := by
              simpa using measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
            exact hμ.ne)
          (1 : ℝ))) := by
  let u : Finset ℕ → ℝ := fun s ↦
    ∑ k ∈ s,
      F
        (indicatorConstLp p
          ((hA_meas k).inter (measurableSet_dualityPiece n))
          (measure_inter_dualityPiece_lt_top (A k) n).ne
          (1 : ℝ))
  let a : ℝ :=
    F
      (indicatorConstLp p
        (MeasurableSet.iUnion fun k ↦ (hA_meas k).inter (measurableSet_dualityPiece n))
        (by
          have hμ : μ (⋃ k, A k ∩ dualityPiece μ n) < ∞ := by
            simpa using measure_iUnion_Ici_inter_dualityPiece_lt_top A n 0
          exact hμ.ne)
        (1 : ℝ))
  let b : ℕ → ℝ := fun N ↦
    ‖F‖ * μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) ^ (1 / p.toReal)
  -- Route correction: keep the proof in the finset-net world until the last line, then read it as
  -- the unconditional `HasSum` convergence required by `SignedMeasure`.
  have hb_tendsto : Filter.Tendsto b atTop (𝓝 0) := by
    -- The tail control from the localized measure estimate is scalar, so a constant multiple still
    -- tends to `0`.
    simpa [b] using
      (tendsto_const_nhds.mul
        (localizedTailRealRpowTendstoZero A hA_meas hA_disj n))
  have hb_nonneg : ∀ N, 0 ≤ b N := by
    intro N
    dsimp [b]
    exact mul_nonneg (norm_nonneg _) <|
      Real.rpow_nonneg
        (show 0 ≤ μ.real (⋃ k ≥ N, A k ∩ dualityPiece μ n) from by simp) _
  have hbound : ∀ N s, Finset.range N ⊆ s → ‖u s - a‖ ≤ b N := by
    intro N s hNs
    -- The localized finite-support error is exactly the tail estimate already proved above.
    dsimp [u, a, b]
    simpa [Real.norm_eq_abs, abs_sub_comm] using
      localizedIndicatorFiniteSetResidualBound F A hA_meas hA_disj n N s hNs
  change Filter.Tendsto u atTop (𝓝 a)
  exact tendstoFinsetOfTailControl u a b hb_tendsto hb_nonneg hbound

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 7.50: the localized set function used in the signed-measure constructor. -/
def localizedIndicatorSetFunction
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) (A : Set Ω) : ℝ :=
  if hA : MeasurableSet A then
    F
      (indicatorConstLp p
        (hA.inter (measurableSet_dualityPiece n))
        (measure_inter_dualityPiece_lt_top A n).ne
        (1 : ℝ))
  else
    0

omit [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: the localized set function vanishes on the empty set. -/
lemma localizedIndicatorSetFunction_empty
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) :
    localizedIndicatorSetFunction F n ∅ = 0 := by
  -- On the empty set, the indicator function is zero in `Lp`.
  simp [localizedIndicatorSetFunction]

omit [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: the localized set function is zero on nonmeasurable sets. -/
lemma localizedIndicatorSetFunction_not_measurable
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) {A : Set Ω} (hA : ¬MeasurableSet A) :
    localizedIndicatorSetFunction F n A = 0 := by
  -- The definition uses the zero branch outside the measurable σ-algebra.
  simp [localizedIndicatorSetFunction, hA]

omit [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: on measurable sets, the localized set function is the original
functional applied to the localized indicator. -/
lemma localizedIndicatorSetFunction_apply
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    localizedIndicatorSetFunction F n A =
      F
        (indicatorConstLp p
          (hA.inter (measurableSet_dualityPiece n))
          (measure_inter_dualityPiece_lt_top A n).ne
          (1 : ℝ)) := by
  -- Inside the measurable branch, the set function is exactly the localized indicator functional.
  simp [localizedIndicatorSetFunction, hA]

/-- Helper for Theorem 7.50: the localized set function is countably additive on measurable
pairwise disjoint families. -/
lemma localizedIndicatorSetFunction_m_iUnion
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) {A : ℕ → Set Ω}
    (hA_meas : ∀ k, MeasurableSet (A k))
    (hA_disj : Pairwise fun i j ↦ Disjoint (A i) (A j)) :
    HasSum
      (fun k ↦ localizedIndicatorSetFunction F n (A k))
      (localizedIndicatorSetFunction F n (⋃ k, A k)) := by
  have hUnion_meas : MeasurableSet (⋃ k, A k) := MeasurableSet.iUnion hA_meas
  -- Rewrite the measurable branches to the explicit localized indicator evaluations.
  rw [localizedIndicatorSetFunction_apply F n hUnion_meas]
  convert localizedIndicatorFunctionalHasSumOnDualityPiece
    F A hA_meas hA_disj n using 1
  · ext k
    rw [localizedIndicatorSetFunction_apply F n (hA_meas k)]
  · congr 1
    exact MeasureTheory.indicatorConstLp.congr_simp
      (iUnion_inter_dualityPiece_eq A n)
      p
      ((MeasurableSet.iUnion hA_meas).inter (measurableSet_dualityPiece n))
      (by
        have hμ : μ ((⋃ k, A k) ∩ dualityPiece μ n) < ∞ := by
          refine lt_of_le_of_lt (measure_mono Set.inter_subset_right) ?_
          exact measure_dualityPiece_lt_top n
        exact hμ.ne)
      (1 : ℝ)
      (1 : ℝ)
      rfl

/-- Helper for Theorem 7.50: on one finite duality piece, the localized indicator functional
packages into a signed measure. -/
def localizedIndicatorSignedMeasure
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) : SignedMeasure Ω :=
  { measureOf' := localizedIndicatorSetFunction F n
    empty' := localizedIndicatorSetFunction_empty F n
    not_measurable' := fun _ hA ↦
      localizedIndicatorSetFunction_not_measurable F n hA
    m_iUnion' := fun _ hA_meas hA_disj ↦
      localizedIndicatorSetFunction_m_iUnion F n hA_meas hA_disj }

/-- Helper for Theorem 7.50: evaluation of the localized signed measure reduces to the original
functional on the corresponding localized indicator. -/
lemma localizedIndicatorSignedMeasure_apply
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    localizedIndicatorSignedMeasure F n A =
      F
        (indicatorConstLp p
          (hA.inter (measurableSet_dualityPiece n))
          (measure_inter_dualityPiece_lt_top A n).ne
          (1 : ℝ)) := by
  -- The signed measure is defined from the measurable branch of `localizedIndicatorSetFunction`.
  simpa [localizedIndicatorSignedMeasure] using
    localizedIndicatorSetFunction_apply F n hA

/-- Helper for Theorem 7.50: each localized signed measure is absolutely continuous with respect to
`μ`, so its canonical Radon-Nikodym derivative is available. -/
lemma localizedIndicatorSignedMeasure_absolutelyContinuous
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) :
    localizedIndicatorSignedMeasure F n ≪ᵥ μ.toENNRealVectorMeasure := by
  have hp_one : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hp_finite : p < ∞ := Fact.out
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos (lt_of_lt_of_le zero_lt_one hp_one).ne' hp_finite.ne
  have hzero_rpow : (0 : ℝ) ^ (1 / p.toReal) = 0 := by
    exact Real.zero_rpow (one_div_ne_zero hp_toReal_pos.ne')
  refine VectorMeasure.AbsolutelyContinuous.mk ?_
  intro A hA hA_zero
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA] at hA_zero
  have hAinter_zero : μ (A ∩ dualityPiece μ n) = 0 :=
    measure_mono_null Set.inter_subset_left hA_zero
  have hbound :=
    indicator_functional_bound F
      (hA.inter (measurableSet_dualityPiece n))
      (measure_inter_dualityPiece_lt_top A n).ne
  rw [localizedIndicatorSignedMeasure_apply F n hA]
  -- The indicator bound collapses to `0` on a `μ`-null set, forcing the localized measure to
  -- vanish there as well.
  apply norm_eq_zero.mp
  refine le_antisymm ?_ (norm_nonneg _)
  calc
    ‖F
        (indicatorConstLp p
          (hA.inter (measurableSet_dualityPiece n))
          (measure_inter_dualityPiece_lt_top A n).ne
          (1 : ℝ))‖
      ≤ ‖F‖ * μ.real (A ∩ dualityPiece μ n) ^ (1 / p.toReal) := hbound
    _ = ‖F‖ * 0 ^ (1 / p.toReal) := by
      simp [MeasureTheory.measureReal_def, hAinter_zero]
    _ = 0 := by
      rw [hzero_rpow, mul_zero]

/-- Helper for Theorem 7.50: evaluating the canonical Radon-Nikodym density on a measurable set
recovers the localized indicator functional. -/
lemma localizedIndicatorSignedMeasure_rnDeriv_apply
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ x in A, (localizedIndicatorSignedMeasure F n).rnDeriv μ x ∂μ =
      F
        (indicatorConstLp p
          (hA.inter (measurableSet_dualityPiece n))
          (measure_inter_dualityPiece_lt_top A n).ne
          (1 : ℝ)) := by
  have hac :=
    localizedIndicatorSignedMeasure_absolutelyContinuous F n
  -- Replace the set integral by the value of the vector measure obtained from the RN density.
  rw [← withDensityᵥ_apply
    (SignedMeasure.integrable_rnDeriv (localizedIndicatorSignedMeasure F n) μ)
    hA]
  rw [SignedMeasure.withDensityᵥ_rnDeriv_eq
    (localizedIndicatorSignedMeasure F n) μ hac]
  exact localizedIndicatorSignedMeasure_apply F n hA

/-- Helper for Theorem 7.50: the Radon-Nikodym density of the localized signed measure, truncated
to its own duality piece. -/
abbrev localizedPieceDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) : Ω → ℝ :=
  Set.indicator (dualityPiece μ n)
    ((localizedIndicatorSignedMeasure F n).rnDeriv μ)

/-- Helper for Theorem 7.50: the finite partial sum of the localized piece densities. -/
def partialLocalizedDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) : Ω → ℝ :=
  fun x ↦ ∑ k ∈ s, localizedPieceDensity F k x

/-- Helper for Theorem 7.50: glue the disjoint localized Radon-Nikodym densities into one
pointwise density by selecting the unique duality piece containing the point. -/
def localizedDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) : Ω → ℝ :=
  fun x ↦
    if hx : ∃ n, x ∈ dualityPiece μ n then
      localizedPieceDensity F (Nat.find hx) x
    else
      0

/-- Helper for Theorem 7.50: on any duality piece, the glued density reduces to that piece's
localized Radon-Nikodym density. -/
lemma localizedDensity_eq_localizedPieceDensity_of_mem
    (F : StrongDual ℝ (Lp ℝ p μ)) {n : ℕ} {x : Ω} (hx : x ∈ dualityPiece μ n) :
    localizedDensity F x =
      localizedPieceDensity F n x := by
  -- Route correction: compare the glued density and the finite truncations through the canonical
  -- disjoint `dualityPiece μ n` decomposition instead of the earlier `Classical.choose` scaffold.
  have hx_exists : ∃ m, x ∈ dualityPiece μ m := ⟨n, hx⟩
  have hfind_mem : x ∈ dualityPiece μ (Nat.find hx_exists) := Nat.find_spec hx_exists
  have hfind_eq : Nat.find hx_exists = n := by
    by_contra hne
    exact (Set.disjoint_left.mp (pairwiseDisjoint_dualityPiece hne) hfind_mem) hx
  -- The chosen witness must be the current piece because the duality pieces are pairwise disjoint.
  simp [localizedDensity, hx_exists, hfind_eq]

/-- Helper for Theorem 7.50: inserting one new index into a finite partial density splits off the
corresponding localized piece density. -/
lemma partialLocalizedDensity_insert
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) {n : ℕ} (hn : n ∉ s) :
    partialLocalizedDensity F (insert n s) =
      fun x ↦
        localizedPieceDensity F n x +
          partialLocalizedDensity F s x := by
  funext x
  -- Normalize the inserted finite sum once, so the induction proofs can reuse this bridge.
  rw [partialLocalizedDensity, Finset.sum_insert hn, partialLocalizedDensity]

/-- Helper for Theorem 7.50: outside the finite union of selected duality pieces, the finite
partial density vanishes. -/
lemma partialLocalizedDensity_eq_zero_of_not_mem_biUnion
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) {x : Ω}
    (hx : x ∉ ⋃ k ∈ s, dualityPiece μ k) :
    partialLocalizedDensity F s x = 0 := by
  unfold partialLocalizedDensity
  -- Each localized summand is an indicator on its own duality piece, so all terms vanish away
  -- from the finite union.
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hxk : x ∉ dualityPiece μ k := by
    intro hxk
    exact hx <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk⟩⟩
  simp [localizedPieceDensity, hxk]

/-- Helper for Theorem 7.50: on one chosen duality piece, the finite partial density collapses to
the corresponding localized piece density because the other pieces are disjoint. -/
lemma partialLocalizedDensity_eq_localizedPieceDensity_of_mem
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) {n : ℕ} (hn : n ∈ s) {x : Ω}
    (hx : x ∈ dualityPiece μ n) :
    partialLocalizedDensity F s x =
      localizedPieceDensity F n x := by
  unfold partialLocalizedDensity
  -- The `n`-summand is the only surviving term, because points in `dualityPiece μ n` do not lie
  -- in any other duality piece.
  refine Finset.sum_eq_single_of_mem n hn ?_
  intro k hk hkn
  have hxk : x ∉ dualityPiece μ k := by
    intro hxk
    exact (Set.disjoint_left.mp (pairwiseDisjoint_dualityPiece hkn) hxk) hx
  simp [localizedPieceDensity, hxk]

/-- Helper for Theorem 7.50: each truncated local Radon-Nikodym density is integrable because it
is an indicator truncation of an integrable density. -/
lemma integrable_localizedPieceDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) :
    Integrable (localizedPieceDensity F n) μ := by
  -- The ambient Radon-Nikodym derivative is integrable, and restricting it to a measurable piece
  -- preserves integrability.
  simpa [localizedPieceDensity] using
    (SignedMeasure.integrable_rnDeriv
      (localizedIndicatorSignedMeasure F n) μ).indicator
      (measurableSet_dualityPiece n)

/-- Helper for Theorem 7.50: every finite partial density is integrable by finite additivity of
integrability. -/
lemma integrable_partialLocalizedDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) :
    ∀ s : Finset ℕ, Integrable (partialLocalizedDensity F s) μ := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- Normalize the empty finite sum to the literal zero function before applying the zero
      -- integrability lemma.
      change Integrable (fun _ : Ω ↦ (0 : ℝ)) μ
      exact integrable_zero Ω ℝ μ
  | insert n s hn hs =>
      -- Split off the newly inserted localized piece and reuse finite additivity of integrability.
      rw [partialLocalizedDensity_insert F s hn]
      exact (integrable_localizedPieceDensity F n).add hs

/-- Helper for Theorem 7.50: evaluating a finite sum of localized signed measures on one set is
the finite sum of the individual evaluations. -/
lemma finsetSumLocalizedIndicatorSignedMeasure_apply
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) (A : Set Ω) :
    (∑ k ∈ s, localizedIndicatorSignedMeasure F k) A =
      ∑ k ∈ s, localizedIndicatorSignedMeasure F k A := by
  induction s using Finset.induction_on with
  | empty =>
      -- The empty signed-measure sum evaluates to `0`.
      simp
  | insert n s hn hs =>
      -- Peel off the inserted signed measure and evaluate the remaining finite sum inductively.
      simp [Finset.sum_insert, hn, hs, VectorMeasure.add_apply]

/-- Helper for Theorem 7.50: after truncating the Radon-Nikodym derivative to its own duality
piece, `withDensityᵥ` recovers the localized signed measure. -/
lemma localizedIndicatorSignedMeasure_withDensityPieceRnDeriv
    (F : StrongDual ℝ (Lp ℝ p μ)) (n : ℕ) :
    μ.withDensityᵥ (localizedPieceDensity F n) =
      localizedIndicatorSignedMeasure F n := by
  ext A hA
  have hpiece : MeasurableSet (dualityPiece μ n) := measurableSet_dualityPiece n
  -- Evaluate the truncated density on a measurable set and rewrite it as the localized RN
  -- derivative on `A ∩ dualityPiece μ n`.
  rw [withDensityᵥ_apply (integrable_localizedPieceDensity F n) hA,
    setIntegral_indicator hpiece]
  calc
    ∫ x in A ∩ dualityPiece μ n,
        (localizedIndicatorSignedMeasure F n).rnDeriv μ x ∂μ
      = F
          (indicatorConstLp p
            ((hA.inter hpiece).inter hpiece)
            (measure_inter_dualityPiece_lt_top (A ∩ dualityPiece μ n) n).ne
            (1 : ℝ)) := by
          -- The one-piece Radon-Nikodym formula applies on the localized set `A ∩ dualityPiece`.
          exact localizedIndicatorSignedMeasure_rnDeriv_apply
            F n (hA.inter hpiece)
    _ = F
          (indicatorConstLp p
            (hA.inter hpiece)
            (measure_inter_dualityPiece_lt_top A n).ne
            (1 : ℝ)) := by
          -- Intersecting the localized set with the same piece again does not change the
          -- indicator function.
          congr 1
          exact MeasureTheory.indicatorConstLp.congr_simp
            (by
              ext x
              simp [Set.inter_assoc])
            p ((hA.inter hpiece).inter hpiece)
            (measure_inter_dualityPiece_lt_top (A ∩ dualityPiece μ n) n).ne
            (1 : ℝ) (1 : ℝ) rfl
    _ = localizedIndicatorSignedMeasure F n A := by
          -- The localized signed measure was defined to agree with this indicator evaluation.
          rw [localizedIndicatorSignedMeasure_apply F n hA]

/-- Helper for Theorem 7.50: finite sums of truncated local densities match the corresponding
finite sums of localized signed measures under `withDensityᵥ`. -/
lemma partialLocalizedDensity_withDensity_finset
    (F : StrongDual ℝ (Lp ℝ p μ)) :
    ∀ s : Finset ℕ,
      μ.withDensityᵥ (partialLocalizedDensity F s) =
        ∑ k ∈ s, localizedIndicatorSignedMeasure F k := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      -- Both the empty partial density and the empty signed-measure sum are zero.
      change μ.withDensityᵥ (fun _ : Ω ↦ (0 : ℝ)) = 0
      exact (withDensityᵥ_zero : μ.withDensityᵥ (fun _ : Ω ↦ (0 : ℝ)) = 0)
  | @insert n s hn hs =>
      -- Split the inserted finite density, then use additivity of `withDensityᵥ`.
      rw [partialLocalizedDensity_insert F s hn]
      change μ.withDensityᵥ
          (localizedPieceDensity F n +
            partialLocalizedDensity F s) =
        ∑ k ∈ insert n s, localizedIndicatorSignedMeasure F k
      rw [withDensityᵥ_add
        (integrable_localizedPieceDensity F n)
        (integrable_partialLocalizedDensity F s)]
      rw [hs, localizedIndicatorSignedMeasure_withDensityPieceRnDeriv]
      simp [Finset.sum_insert, hn]

/-- Helper for Theorem 7.50: evaluating a finite partial density on a measurable set collapses to
the functional applied to the indicator of the corresponding finite localized union. -/
lemma partialLocalizedDensity_apply
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) {A : Set Ω} (hA : MeasurableSet A) :
    ∫ x in A, partialLocalizedDensity F s x ∂μ =
      F
        (indicatorConstLp p
          (s.measurableSet_biUnion fun k _hk ↦ hA.inter (measurableSet_dualityPiece k))
          ((measure_biUnion_lt_top
            s.finite_toSet
            (fun k _hk ↦ measure_inter_dualityPiece_lt_top A k)).ne)
          (1 : ℝ)) := by
  rw [← withDensityᵥ_apply (integrable_partialLocalizedDensity F s) hA]
  rw [partialLocalizedDensity_withDensity_finset F s]
  rw [finsetSumLocalizedIndicatorSignedMeasure_apply F s A]
  have happly :
      ∀ k,
        localizedIndicatorSignedMeasure F k A =
          F
            (indicatorConstLp p
              (hA.inter (measurableSet_dualityPiece k))
              (measure_inter_dualityPiece_lt_top A k).ne
              (1 : ℝ)) := by
    intro k
    exact localizedIndicatorSignedMeasure_apply F k hA
  simp_rw [happly]
  rw [← map_sum]
  -- Collapse the finite localized indicator sum back to the indicator of the whole finite union.
  congr 1
  symm
  exact indicatorConstLp_finset_biUnion
    (fun k ↦ A ∩ dualityPiece μ k)
    (fun k ↦ hA.inter (measurableSet_dualityPiece k))
    (fun k ↦ measure_inter_dualityPiece_lt_top A k)
    (by
      intro i j hij
      refine Set.disjoint_left.2 ?_
      intro x hxi hxj
      exact (Set.disjoint_left.mp (pairwiseDisjoint_dualityPiece hij) hxi.2) hxj.2)
    s
    (s.measurableSet_biUnion fun k _hk ↦
      hA.inter (measurableSet_dualityPiece k))
    (measure_biUnion_lt_top
      s.finite_toSet
      (fun k _hk ↦ measure_inter_dualityPiece_lt_top A k))

/-- Helper for Theorem 7.50: the finite union of the selected duality pieces has finite
measure. -/
lemma measure_biUnion_dualityPiece_lt_top
    (s : Finset ℕ) :
    μ (⋃ k ∈ s, dualityPiece μ k) < ∞ := by
  -- The selected support is a finite union of finite-measure duality pieces.
  exact measure_biUnion_lt_top
    s.finite_toSet
    (fun k hk ↦ measure_dualityPiece_lt_top k)

omit [Fact (1 ≤ p)] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: a bounded measurable real function supported on the finite union
`⋃ k ∈ s, dualityPiece μ k` belongs to `MemLp`. -/
lemma memLp_of_measurable_bounded_support_biUnion
    (s : Finset ℕ) {g : Ω → ℝ} (hg_meas : Measurable g)
    (hbound : ∃ M : NNReal, ∀ x, |g x| ≤ M)
    (h_support : Function.support g ⊆ ⋃ k ∈ s, dualityPiece μ k) :
    MemLp g p μ := by
  let U : Set Ω := ⋃ k ∈ s, dualityPiece μ k
  have hU_meas : MeasurableSet U := by
    exact s.measurableSet_biUnion fun k _hk ↦ measurableSet_dualityPiece k
  have hU_finite : μ U < ∞ := by
    simpa [U] using measure_biUnion_dualityPiece_lt_top s
  letI : Fact (μ U < ∞) := ⟨hU_finite⟩
  rcases hbound with ⟨M, hM⟩
  have hmem_restrict : MemLp g p (μ.restrict U) := by
    -- On the finite restricted measure, the uniform bound on `g` is enough to put it in `L^p`.
    refine MemLp.of_bound hg_meas.aestronglyMeasurable (M : ℝ) ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      simpa [Real.norm_eq_abs] using hM x
  have hmem_indicator : MemLp (U.indicator g) p μ := by
    -- Move the restricted-space `L^p` witness back to the ambient measure through the indicator.
    rw [memLp_indicator_iff_restrict hU_meas]
    exact hmem_restrict
  have hIndicator_eq : U.indicator g = g := Set.indicator_eq_self.2 h_support
  -- The support hypothesis lets us replace the indicator-cutoff function by `g` itself.
  simpa [U, hIndicator_eq] using hmem_indicator

/-- Helper for Theorem 7.50: every finite partial density is supported on the corresponding finite
union of duality pieces. -/
lemma partialLocalizedDensity_ae_eq_indicator_biUnion
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) :
    partialLocalizedDensity F s =ᵐ[μ]
      Set.indicator (⋃ k ∈ s, dualityPiece μ k)
        (partialLocalizedDensity F s) := by
  -- Outside the chosen finite union, the partial density is already zero.
  filter_upwards with x
  by_cases hx : x ∈ ⋃ k ∈ s, dualityPiece μ k
  · simp [hx]
  · simp [hx, partialLocalizedDensity_eq_zero_of_not_mem_biUnion F s hx]

/-- Helper for Theorem 7.50: every finite partial density is exactly the truncation of the glued
localized density to the corresponding finite union of duality pieces. -/
lemma partialLocalizedDensity_ae_eq_indicator_localizedDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) :
    partialLocalizedDensity F s =ᵐ[μ]
      Set.indicator (⋃ k ∈ s, dualityPiece μ k)
        (localizedDensity F) := by
  -- On the chosen finite union, both densities reduce to the same localized piece density.
  filter_upwards with x
  by_cases hxu : x ∈ ⋃ k ∈ s, dualityPiece μ k
  · rcases Set.mem_iUnion.1 hxu with ⟨n, hxns⟩
    rcases Set.mem_iUnion.1 hxns with ⟨hn, hxn⟩
    have hind :
        Set.indicator (⋃ k ∈ s, dualityPiece μ k) (localizedDensity F) x =
          localizedDensity F x := by
      simp [hxu]
    calc
      partialLocalizedDensity F s x = localizedDensity F x := by
        exact
          (partialLocalizedDensity_eq_localizedPieceDensity_of_mem F s hn hxn).trans
            (localizedDensity_eq_localizedPieceDensity_of_mem F hxn).symm
      _ = Set.indicator (⋃ k ∈ s, dualityPiece μ k) (localizedDensity F) x := hind.symm
  · -- Outside the finite union, the partial density already vanishes and so does the indicator.
    rw [Set.indicator_of_notMem hxu]
    exact partialLocalizedDensity_eq_zero_of_not_mem_biUnion F s hxu

/-- Helper for Theorem 7.50: if the finite union supporting the partial density has `μ`-measure
zero, then the partial density itself vanishes almost everywhere. -/
lemma partialLocalizedDensity_zero_ae_of_measure_union_eq_zero
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ)
    (hμ_zero : μ (⋃ k ∈ s, dualityPiece μ k) = 0) :
    partialLocalizedDensity F s =ᵐ[μ] 0 := by
  let U : Set Ω := ⋃ k ∈ s, dualityPiece μ k
  have hU_ae : ∀ᵐ x ∂μ, x ∉ U := by
    rw [ae_iff]
    simpa only [Set.setOf_mem_eq, not_not, U] using hμ_zero
  -- Combine the support truncation with the null-measure support to force the density to vanish.
  filter_upwards [partialLocalizedDensity_ae_eq_indicator_biUnion F s, hU_ae] with x hx hxU
  simp [U, hxU] at hx
  simp [hx]

/-- Helper for Theorem 7.50: the finite partial density already represents `F` on simple test
functions whose support stays inside the same finite union of duality pieces. -/
lemma partialLocalizedDensity_pairing_eq_simpleFunc
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) (φ : MeasureTheory.SimpleFunc Ω ℝ)
    (hφ_support : Function.support (φ : Ω → ℝ) ⊆ ⋃ k ∈ s, dualityPiece μ k)
    (hφ_memLp : MemLp (φ : Ω → ℝ) p μ) :
    F (hφ_memLp.toLp (φ : Ω → ℝ)) =
      ∫ x, partialLocalizedDensity F s x * φ x ∂μ := by
  let U : Set Ω := ⋃ k ∈ s, dualityPiece μ k
  have hU_finite : μ U < ∞ := measure_biUnion_dualityPiece_lt_top s
  have hp_ne_zero : p ≠ 0 := by
    exact (lt_of_lt_of_le zero_lt_one (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne'
  have hp_ne_top : p ≠ ∞ := (Fact.out : p < ∞).ne
  -- Work by the standard simple-function induction into disjoint indicator pieces.
  refine
    MeasureTheory.SimpleFunc.induction
      (motive := fun ψ : MeasureTheory.SimpleFunc Ω ℝ ↦
        Function.support (ψ : Ω → ℝ) ⊆ U →
          ∀ hψ_memLp : MemLp (ψ : Ω → ℝ) p μ,
            F (hψ_memLp.toLp (ψ : Ω → ℝ)) =
              ∫ x, partialLocalizedDensity F s x * ψ x ∂μ)
      ?_ ?_ φ hφ_support hφ_memLp
  · intro c t ht hsupport hmem
    by_cases hc : c = 0
    · -- The zero indicator contributes nothing on either side.
      have hzero_fun : (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
          (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x) = fun _ ↦ 0 := by
        funext x
        by_cases hxt : x ∈ t
        · simp [hc]
        · simp [hc]
      have hzero_ae :
          (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
            (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x) =ᵐ[μ] 0 := by
        exact Filter.Eventually.of_forall (fun x ↦ by
          simpa using congrFun hzero_fun x)
      have hLp_zero :
          hmem.toLp
              (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x)
            = 0 := by
        exact MemLp.toLp_congr hmem MemLp.zero hzero_ae
      have hintegral_zero :
          ∫ x,
              partialLocalizedDensity F s x *
                (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                  (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ∂μ
            = 0 := by
        have hprod_zero :
            (fun x ↦
              partialLocalizedDensity F s x *
                (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                  (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x) =ᵐ[μ]
              (0 : Ω → ℝ) := by
          exact Filter.Eventually.of_forall (fun x ↦ by
            change
              partialLocalizedDensity F s x *
                  (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                    (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x =
                (0 : ℝ)
            rw [congrFun hzero_fun x]
            simp)
        calc
          ∫ x,
              partialLocalizedDensity F s x *
                (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                  (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ∂μ
              = ∫ x, (0 : ℝ) ∂μ := integral_congr_ae hprod_zero
          _ = 0 := by simp
      rw [hLp_zero, map_zero, hintegral_zero]
    · -- A nonzero simple indicator is supported on `t`, hence `t` inherits the finite support.
      have ht_subset : t ⊆ U := by
        intro x hxt
        apply hsupport
        change (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
          (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ≠ 0
        simp [MeasureTheory.SimpleFunc.piecewise_apply, hxt, hc]
      have hμt : μ t < ∞ := lt_of_le_of_lt (measure_mono ht_subset) hU_finite
      have hindicator_ae :
          (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
            (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x) =ᵐ[μ]
            Set.indicator t (fun _ ↦ c) := by
        exact Filter.Eventually.of_forall (fun x ↦ by
          by_cases hxt : x ∈ t
          · simp [MeasureTheory.SimpleFunc.piecewise_apply, hxt]
          · simp [MeasureTheory.SimpleFunc.piecewise_apply, hxt])
      have hLp_indicator :
          hmem.toLp
              (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x)
            = indicatorConstLp p ht hμt.ne c := by
        rw [MeasureTheory.indicatorConstLp]
        exact MemLp.toLp_congr hmem (memLp_indicator_const p ht c (Or.inr hμt.ne)) hindicator_ae
      have hIndicatorSmul :
          indicatorConstLp p ht hμt.ne c = c • indicatorConstLp p ht hμt.ne (1 : ℝ) := by
        rw [MeasureTheory.indicatorConstLp, MeasureTheory.indicatorConstLp]
        refine MemLp.toLp_congr
          (memLp_indicator_const p ht c (Or.inr hμt.ne))
          ((memLp_indicator_const p ht (1 : ℝ) (Or.inr hμt.ne)).const_smul c) ?_
        exact Filter.Eventually.of_forall (fun x ↦ by
          by_cases hxt : x ∈ t
          · simp [hxt]
          · simp [hxt])
      have hIntegralIndicator :
          ∫ x,
              partialLocalizedDensity F s x *
                (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                  (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ∂μ
            = c * ∫ x in t, partialLocalizedDensity F s x ∂μ := by
        calc
          ∫ x,
              partialLocalizedDensity F s x *
                (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                  (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ∂μ
              = ∫ x, t.indicator (fun x ↦ c * partialLocalizedDensity F s x) x ∂μ := by
                  refine integral_congr_ae ?_
                  exact Filter.Eventually.of_forall (fun x ↦ by
                    by_cases hxt : x ∈ t
                    · simp [MeasureTheory.SimpleFunc.piecewise_apply, hxt, mul_comm]
                    · simp [MeasureTheory.SimpleFunc.piecewise_apply, hxt])
          _ = ∫ x in t, c * partialLocalizedDensity F s x ∂μ := integral_indicator ht
          _ = c * ∫ x in t, partialLocalizedDensity F s x ∂μ := by
                rw [integral_const_mul]
      have hLocalizedUnionEq :
          (⋃ k ∈ s, t ∩ dualityPiece μ k) = t := by
        ext x
        constructor
        · intro hx
          simp only [Set.mem_iUnion] at hx
          rcases hx with ⟨k, hk, hxk⟩
          exact hxk.1
        · intro hxt
          have hxU : x ∈ U := ht_subset hxt
          simp only [U, Set.mem_iUnion] at hxU
          rcases hxU with ⟨k, hk, hxk⟩
          exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ⟨hxt, hxk⟩⟩⟩
      have hIndicatorOne :
          indicatorConstLp p
              (s.measurableSet_biUnion fun k _hk ↦ ht.inter (measurableSet_dualityPiece k))
              ((measure_biUnion_lt_top
                s.finite_toSet
                (fun k hk ↦ measure_inter_dualityPiece_lt_top t k)).ne)
              (1 : ℝ)
            = indicatorConstLp p ht hμt.ne (1 : ℝ) := by
        exact MeasureTheory.indicatorConstLp.congr_simp
          hLocalizedUnionEq
          p
          (s.measurableSet_biUnion fun k _hk ↦ ht.inter (measurableSet_dualityPiece k))
          ((measure_biUnion_lt_top
            s.finite_toSet
            (fun k hk ↦ measure_inter_dualityPiece_lt_top t k)).ne)
          (1 : ℝ)
          (1 : ℝ)
          rfl
      calc
        F (hmem.toLp
            (fun x ↦ (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
              (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x))
            = F (indicatorConstLp p ht hμt.ne c) := by
                rw [hLp_indicator]
        _ = c * F (indicatorConstLp p ht hμt.ne (1 : ℝ)) := by
              rw [hIndicatorSmul, map_smul]
              simp [smul_eq_mul]
        _ = c * ∫ x in t, partialLocalizedDensity F s x ∂μ := by
              rw [← hIndicatorOne]
              rw [partialLocalizedDensity_apply F s ht]
        _ = ∫ x, partialLocalizedDensity F s x *
              (((MeasureTheory.SimpleFunc.const Ω c).piecewise t ht
                (MeasureTheory.SimpleFunc.const Ω 0)) : MeasureTheory.SimpleFunc Ω ℝ) x ∂μ := by
              rw [hIntegralIndicator]
  · intro f g hdisj hf hg hfg_support hfg_mem
    have hf_support' : Function.support (f : Ω → ℝ) ⊆ U := by
      intro x hx
      apply hfg_support
      change f x + g x ≠ 0
      have hxg : g x = 0 := by
        by_contra hxg
        have hxg' : x ∈ Function.support (g : Ω → ℝ) := by
          simpa [Function.mem_support] using hxg
        exact (Set.disjoint_left.mp hdisj hx hxg')
      simpa [hxg] using hx
    have hg_support' : Function.support (g : Ω → ℝ) ⊆ U := by
      intro x hx
      apply hfg_support
      change f x + g x ≠ 0
      have hxf : f x = 0 := by
        by_contra hxf
        have hxf' : x ∈ Function.support (f : Ω → ℝ) := by
          simpa [Function.mem_support] using hxf
        exact (Set.disjoint_left.mp hdisj hxf' hx)
      simpa [hxf] using hx
    have hmem_split :=
      (memLp_add_of_disjoint hdisj f.stronglyMeasurable g.stronglyMeasurable).mp hfg_mem
    have hf_mem : MemLp (f : Ω → ℝ) p μ := hmem_split.1
    have hg_mem : MemLp (g : Ω → ℝ) p μ := hmem_split.2
    have hfg_mem :
        MemLp (fun x ↦ f x + g x) p μ := by
      exact hf_mem.add hg_mem
    have hf_prod_int :
        Integrable (fun x ↦ partialLocalizedDensity F s x * f x) μ := by
      rcases (f.map fun y ↦ |y|).exists_forall_le with ⟨Cf, hCf⟩
      exact (integrable_partialLocalizedDensity F s).mul_bdd f.aestronglyMeasurable <|
        Filter.Eventually.of_forall fun x ↦ by
          simpa using hCf x
    have hg_prod_int :
        Integrable (fun x ↦ partialLocalizedDensity F s x * g x) μ := by
      rcases (g.map fun y ↦ |y|).exists_forall_le with ⟨Cg, hCg⟩
      exact (integrable_partialLocalizedDensity F s).mul_bdd g.aestronglyMeasurable <|
        Filter.Eventually.of_forall fun x ↦ by
          simpa using hCg x
    -- The disjoint decomposition keeps both the `Lp` class and the integral side additive.
    calc
      F (hfg_mem.toLp (fun x ↦ f x + g x))
          = F ((hf_mem.add hg_mem).toLp ((f : Ω → ℝ) + (g : Ω → ℝ))) := by
              rfl
      _ = F (hf_mem.toLp (f : Ω → ℝ) + hg_mem.toLp (g : Ω → ℝ)) := by
            rw [← MemLp.toLp_add]
      _ = F (hf_mem.toLp (f : Ω → ℝ)) + F (hg_mem.toLp (g : Ω → ℝ)) := by
            rw [map_add]
      _ = ∫ x, partialLocalizedDensity F s x * f x ∂μ +
            ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
              rw [hf hf_support' hf_mem, hg hg_support' hg_mem]
      _ = ∫ x, partialLocalizedDensity F s x * (f x + g x) ∂μ := by
            rw [← integral_add hf_prod_int hg_prod_int]
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x ↦ by simp [mul_add])

/-- Helper for Theorem 7.50: the simple-function pairing identity extends to bounded measurable
tests supported on the same finite union of duality pieces. -/
lemma partialLocalizedDensity_pairing_eq_boundedSupport
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) {g : Ω → ℝ}
    (hg_meas : Measurable g)
    (hbound : ∃ M : NNReal, ∀ x, |g x| ≤ M)
    (h_support : Function.support g ⊆ ⋃ k ∈ s, dualityPiece μ k) :
    F ((memLp_of_measurable_bounded_support_biUnion s hg_meas hbound h_support).toLp g) =
      ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
  let φ : ℕ → MeasureTheory.SimpleFunc Ω ℝ := fun n ↦
    MeasureTheory.SimpleFunc.approxOn g hg_meas (Set.range g ∪ {0}) 0 (by simp) n
  have hg_mem : MemLp g p μ :=
    memLp_of_measurable_bounded_support_biUnion s hg_meas hbound h_support
  rcases hbound with ⟨M, hM⟩
  have hφ_support : ∀ n, Function.support (φ n : Ω → ℝ) ⊆ ⋃ k ∈ s, dualityPiece μ k := by
    intro n x hx
    by_contra hxU
    have hxg : g x = 0 := by
      by_contra hxg
      exact hxU <| h_support <| by simpa [Function.mem_support] using hxg
    have hzero_mem : (0 : ℝ) ∈ Set.range g ∪ ({0} : Set ℝ) := by
      exact Or.inr (by simp)
    have hdist :=
      MeasureTheory.SimpleFunc.edist_approxOn_le hg_meas hzero_mem x n
    have hφx : φ n x = 0 := by
      have hzero_rhs : edist (0 : ℝ) (g x) = 0 := by
        rw [hxg, edist_self]
      have hdist_zero : edist (φ n x) (g x) ≤ 0 := by
        rw [← hzero_rhs]
        exact hdist
      have hEq : φ n x = g x := by
        exact edist_eq_zero.mp <| le_antisymm hdist_zero bot_le
      simpa [hxg] using hEq
    exact hx <| by simp [hφx]
  have hφ_bound : ∀ n x, |φ n x| ≤ (((M + M : NNReal)) : ℝ) := by
    intro n x
    have hnorm :
        ‖φ n x‖ ≤ ‖g x‖ + ‖g x‖ := by
      simpa [φ] using
        MeasureTheory.SimpleFunc.norm_approxOn_zero_le
          hg_meas (by simp) x n
    calc
      |φ n x| = ‖φ n x‖ := by simp
      _ ≤ ‖g x‖ + ‖g x‖ := hnorm
      _ = |g x| + |g x| := by simp [Real.norm_eq_abs]
      _ ≤ (M : ℝ) + M := add_le_add (hM x) (hM x)
      _ = (((M + M : NNReal)) : ℝ) := by rfl
  have hφ_pair :
      ∀ n,
        F ((MeasureTheory.SimpleFunc.memLp_approxOn_range hg_meas hg_mem n).toLp (φ n)) =
          ∫ x, partialLocalizedDensity F s x * φ n x ∂μ := by
    intro n
    -- Each approximant is a simple bounded-support test, so the simple-function bridge applies.
    exact partialLocalizedDensity_pairing_eq_simpleFunc
      F s (φ n) (hφ_support n) (MeasureTheory.SimpleFunc.memLp_approxOn_range hg_meas hg_mem n)
  have hφ_tendsto :
      Tendsto
        (fun n ↦ (MeasureTheory.SimpleFunc.memLp_approxOn_range hg_meas hg_mem n).toLp (φ n))
        atTop (𝓝 (hg_mem.toLp g)) := by
    have hp_ne_top : p ≠ ∞ := (Fact.out : p < ∞).ne
    simpa [φ] using
      MeasureTheory.SimpleFunc.tendsto_approxOn_range_Lp
        hp_ne_top hg_meas hg_mem
  have hF_tendsto :
      Tendsto
        (fun n ↦ F ((MeasureTheory.SimpleFunc.memLp_approxOn_range hg_meas hg_mem n).toLp (φ n)))
        atTop (𝓝 (F (hg_mem.toLp g))) := by
    exact (F.continuous.tendsto (hg_mem.toLp g)).comp hφ_tendsto
  have hbound_integrable :
      Integrable (fun x ↦ ((M + M : NNReal) : ℝ) * |partialLocalizedDensity F s x|) μ := by
    -- The product is dominated by a constant multiple of the integrable partial density.
    simpa [Real.norm_eq_abs, mul_comm] using
      (integrable_partialLocalizedDensity F s).norm.const_mul (((M + M : NNReal)) : ℝ)
  have hInt_tendsto :
      Tendsto
        (fun n ↦ ∫ x, partialLocalizedDensity F s x * φ n x ∂μ)
        atTop (𝓝 (∫ x, partialLocalizedDensity F s x * g x ∂μ)) := by
    -- Dominated convergence is available because the approximants stay uniformly bounded by `2M`.
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x ↦ (((M + M : NNReal)) : ℝ) * |partialLocalizedDensity F s x|) ?_
      hbound_integrable ?_ ?_
    · intro n
      exact (integrable_partialLocalizedDensity F s).aestronglyMeasurable.mul
        (MeasureTheory.SimpleFunc.measurable (φ n)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun x ↦ ?_
      calc
        ‖partialLocalizedDensity F s x * φ n x‖
            = |partialLocalizedDensity F s x| * |φ n x| := by
                simp [Real.norm_eq_abs]
        _ ≤ |partialLocalizedDensity F s x| * (((M + M : NNReal)) : ℝ) := by
              gcongr
              exact hφ_bound n x
        _ = (((M + M : NNReal)) : ℝ) * |partialLocalizedDensity F s x| := by ring
    · filter_upwards with x
      have hφx_tendsto :
          Tendsto (fun n ↦ φ n x) atTop (𝓝 (g x)) := by
        exact MeasureTheory.SimpleFunc.tendsto_approxOn
          hg_meas (by simp) (subset_closure (by simp))
      exact hφx_tendsto.const_mul (partialLocalizedDensity F s x)
  -- The simple approximants converge to the target on both sides, so their common limits agree.
  exact tendsto_nhds_unique hF_tendsto <| by simpa [hφ_pair] using hInt_tendsto

omit [SigmaFinite μ] [Fact (p < ∞)] in
/-- Helper for Theorem 7.50: on a probability space, a bounded-test pairing estimate recovers both
`MemLp X (ENNReal.ofReal a)` and the quantitative bound `lpNorm X (ENNReal.ofReal a) ≤ C`. -/
lemma memLpAndLpNorm_le_of_boundedMeasurablePairingBound
    {P : Measure Ω} [IsProbabilityMeasure P] {a b : ℝ} {X : Ω → ℝ} (C : NNReal)
    (hab : a.HolderConjugate b)
    (hpair :
      ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (X * Y) P ∧
          |∫ ω, X ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal b) P) :
    MemLp X (ENNReal.ofReal a) P ∧ lpNorm X (ENNReal.ofReal a) P ≤ C := by
  have ha : 1 < a := (Real.holderConjugate_iff.mp hab).1
  have hb : 1 < b := (Real.holderConjugate_iff.mp hab.symm).1
  have ha_pos : 0 < a := lt_trans zero_lt_one ha
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have hb_nonneg : 0 ≤ b := le_of_lt (lt_trans zero_lt_one hb)
  -- Proof comment: first recover integrability of `X`, then replace it by a measurable
  -- representative so the cutoff machinery from Exercise 7.2.3 applies directly.
  have hX_int : Integrable X P := by
    have hOne_meas : Measurable (fun _ : Ω ↦ (1 : ℝ)) := measurable_const
    have hconst :=
      hpair hOne_meas ⟨1, fun _ ↦ by norm_num⟩
    simpa using (show Integrable (fun ω ↦ X ω * (1 : ℝ)) P from hconst.1)
  let Xm : Ω → ℝ := hX_int.aestronglyMeasurable.mk X
  have hXm_meas : Measurable Xm := hX_int.aestronglyMeasurable.measurable_mk
  have hXm_eq : X =ᵐ[P] Xm := hX_int.aestronglyMeasurable.ae_eq_mk
  have hpairXm :
      ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
        (∃ M : NNReal, ∀ ω, |Y ω| ≤ M) →
        Integrable (Xm * Y) P ∧
          |∫ ω, Xm ω * Y ω ∂P| ≤ (C : ℝ) * lpNorm Y (ENNReal.ofReal b) P := by
    intro Y hY_meas hY_bdd
    rcases hpair hY_meas hY_bdd with ⟨hXY_int, hXY_bound⟩
    have hXmY_int : Integrable (Xm * Y) P := by
      refine hXY_int.congr ?_
      filter_upwards [hXm_eq] with ω hω
      simp [hω]
    have hIntegral_eq : ∫ ω, Xm ω * Y ω ∂P = ∫ ω, X ω * Y ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hXm_eq] with ω hω
      simp [hω]
    refine ⟨hXmY_int, ?_⟩
    rw [hIntegral_eq]
    exact hXY_bound
  -- Proof comment: the cutoff powers turn the pairing estimate into a uniform bound on the
  -- truncated `a`-moments of the measurable representative `Xm`.
  have hcutoff_int_bound : ∀ n : ℕ,
      Integrable (cutoffPower a Xm n) P ∧
        ∫ ω, cutoffPower a Xm n ω ∂P ≤ (C : ℝ) ^ a := by
    intro n
    rcases cutoffSignedPower_measurable_bound ha hXm_meas n with ⟨hYn_meas, hYn_bdd⟩
    have hYn_memLp : MemLp (cutoffSignedPower a Xm n) (ENNReal.ofReal b) P := by
      rcases hYn_bdd with ⟨M, hM⟩
      refine MemLp.of_bound hYn_meas.aestronglyMeasurable (M : ℝ) ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs] using hM ω
    have hcutoff_int : Integrable (cutoffPower a Xm n) P := by
      have hnorm_int :
          Integrable
            (fun ω ↦ ‖cutoffSignedPower a Xm n ω‖ ^ (ENNReal.ofReal b).toReal) P :=
        (integrable_norm_rpow_iff hYn_meas.aestronglyMeasurable
          (show ENNReal.ofReal b ≠ 0 by positivity) (by simp)).2 hYn_memLp
      refine hnorm_int.congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hb_nonneg] using
          cutoffSignedPower_abs_rpow_eq_cutoffPower hab n ω
    have hcutoff_nonneg : 0 ≤ᵐ[P] cutoffPower a Xm n :=
      Filter.Eventually.of_forall fun ω ↦
        Real.rpow_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg n)) _
    rcases hpairXm hYn_meas hYn_bdd with ⟨hpair_int, hpair_bound⟩
    have hpair_lower :
        ∫ ω, cutoffPower a Xm n ω ∂P ≤
          ∫ ω, Xm ω * cutoffSignedPower a Xm n ω ∂P := by
      refine integral_mono hcutoff_int hpair_int ?_
      intro ω
      exact cutoffPower_le_mul_cutoffSignedPower ha n ω
    have hLp_eq :
        lpNorm (cutoffSignedPower a Xm n) (ENNReal.ofReal b) P =
          (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
      calc
        lpNorm (cutoffSignedPower a Xm n) (ENNReal.ofReal b) P
            = (∫ ω, ‖cutoffSignedPower a Xm n ω‖ ^ b ∂P) ^ (1 / b) := by
                rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
                  hYn_meas.aestronglyMeasurable]
                simp [ENNReal.toReal_ofReal hb_nonneg]
        _ = (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
            congr 1
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              simpa [Real.norm_eq_abs] using
                cutoffSignedPower_abs_rpow_eq_cutoffPower hab n ω
    have hmoment_le :
        ∫ ω, cutoffPower a Xm n ω ∂P ≤
          (C : ℝ) * (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
      calc
        ∫ ω, cutoffPower a Xm n ω ∂P
            ≤ ∫ ω, Xm ω * cutoffSignedPower a Xm n ω ∂P := hpair_lower
        _ ≤ |∫ ω, Xm ω * cutoffSignedPower a Xm n ω ∂P| := le_abs_self _
        _ ≤ (C : ℝ) * lpNorm (cutoffSignedPower a Xm n) (ENNReal.ofReal b) P := hpair_bound
        _ = (C : ℝ) * (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by rw [hLp_eq]
    have hcutoff_nonneg_int : 0 ≤ ∫ ω, cutoffPower a Xm n ω ∂P :=
      integral_nonneg_of_ae hcutoff_nonneg
    refine ⟨hcutoff_int, ?_⟩
    by_cases hzero : ∫ ω, cutoffPower a Xm n ω ∂P = 0
    · simpa [hzero] using Real.rpow_nonneg (show 0 ≤ (C : ℝ) from C.2) a
    · have hpos_int : 0 < ∫ ω, cutoffPower a Xm n ω ∂P := by
        exact lt_of_le_of_ne hcutoff_nonneg_int (by simpa [eq_comm] using hzero)
      have hsplit :
          ∫ ω, cutoffPower a Xm n ω ∂P =
            (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a) *
              (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
        have hinv : 1 / a + 1 / b = 1 := by
          simpa [one_div] using hab.inv_add_inv_eq_one
        calc
          ∫ ω, cutoffPower a Xm n ω ∂P
              = (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 : ℝ) := by
                  rw [Real.rpow_one]
          _ = (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a + 1 / b) := by
                  rw [hinv]
          _ = (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a) *
                (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
                  rw [Real.rpow_add hpos_int]
      have hroot_le : (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a) ≤ (C : ℝ) := by
        have hbpow_pos :
            0 < (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) :=
          Real.rpow_pos_of_pos hpos_int _
        have hmul_le :
            (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a) *
                (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) ≤
              (C : ℝ) * (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := by
          calc
            (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / a) *
                (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b)
                = ∫ ω, cutoffPower a Xm n ω ∂P := hsplit.symm
            _ ≤ (C : ℝ) * (∫ ω, cutoffPower a Xm n ω ∂P) ^ (1 / b) := hmoment_le
        exact le_of_mul_le_mul_right hmul_le hbpow_pos
      have hroot_le' : (∫ ω, cutoffPower a Xm n ω ∂P) ^ a⁻¹ ≤ (C : ℝ) := by
        simpa [one_div] using hroot_le
      exact (Real.rpow_inv_le_iff_of_pos hcutoff_nonneg_int (show 0 ≤ (C : ℝ) from C.2)
        ha_pos).1 hroot_le'
  have hcutoff_nonneg : ∀ n : ℕ, 0 ≤ᵐ[P] cutoffPower a Xm n :=
    fun n ↦ Filter.Eventually.of_forall fun ω ↦
      Real.rpow_nonneg (le_min (abs_nonneg _) (Nat.cast_nonneg n)) _
  -- Proof comment: monotone convergence upgrades the uniform cutoff estimate to the full
  -- `a`-moment bound, and then the `L^a` norm is controlled by `C`.
  have hpower_lintegral :
      ∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ a) ∂P ≤ ENNReal.ofReal ((C : ℝ) ^ a) := by
    have hcutoff_meas : ∀ n : ℕ, Measurable fun ω ↦ ENNReal.ofReal (cutoffPower a Xm n ω) :=
      fun n ↦ by
        simpa [cutoffPower] using ((hXm_meas.abs.min measurable_const).pow_const a).ennreal_ofReal
    have hcutoff_mono :
        Monotone fun n : ℕ ↦ fun ω ↦ ENNReal.ofReal (cutoffPower a Xm n ω) := by
      intro n m hnm ω
      apply ENNReal.ofReal_le_ofReal
      refine Real.rpow_le_rpow (le_min (abs_nonneg _) (Nat.cast_nonneg n)) ?_ ha_nonneg
      exact min_le_min le_rfl (by exact_mod_cast hnm)
    calc
      ∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ a) ∂P
          = ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal (cutoffPower a Xm n ω) ∂P := by
              congr with ω
              symm
              exact iSup_cutoffPower_eq ha_nonneg ω
      _ = ⨆ n : ℕ, ∫⁻ ω, ENNReal.ofReal (cutoffPower a Xm n ω) ∂P := by
            rw [lintegral_iSup hcutoff_meas hcutoff_mono]
      _ ≤ ENNReal.ofReal ((C : ℝ) ^ a) := by
            refine iSup_le fun n ↦ ?_
            have hcutoff_int := (hcutoff_int_bound n).1
            have hcutoff_bound := (hcutoff_int_bound n).2
            rw [← ofReal_integral_eq_lintegral_ofReal hcutoff_int (hcutoff_nonneg n)]
            exact ENNReal.ofReal_le_ofReal hcutoff_bound
  have hpower_integrable : Integrable (fun ω ↦ |Xm ω| ^ a) P := by
    refine (lintegral_ofReal_ne_top_iff_integrable
      ((hXm_meas.abs.pow_const a).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ Real.rpow_nonneg (abs_nonneg _) _)).1 ?_
    exact ne_top_of_le_ne_top (by simp) hpower_lintegral
  have hXm_memLp : MemLp Xm (ENNReal.ofReal a) P := by
    rw [← integrable_norm_rpow_iff hXm_meas.aestronglyMeasurable (by positivity) (by simp)]
    simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal ha_nonneg] using hpower_integrable
  have hXm_lpNorm_le : lpNorm Xm (ENNReal.ofReal a) P ≤ C := by
    have hIntegral_eq :
        ENNReal.ofReal (∫ ω, |Xm ω| ^ a ∂P) =
          ∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ a) ∂P := by
      rw [ofReal_integral_eq_lintegral_ofReal hpower_integrable]
      exact Filter.Eventually.of_forall fun ω ↦ Real.rpow_nonneg (abs_nonneg _) _
    have hIntegral_toReal :
        (∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ a) ∂P).toReal =
          ∫ ω, |Xm ω| ^ a ∂P := by
      rw [← hIntegral_eq, ENNReal.toReal_ofReal]
      positivity
    have hmoment_toReal_le :
        (∫⁻ ω, ENNReal.ofReal (|Xm ω| ^ a) ∂P).toReal ≤ (C : ℝ) ^ a := by
      exact ENNReal.toReal_le_of_le_ofReal
        (Real.rpow_nonneg (show 0 ≤ (C : ℝ) from C.2) a) hpower_lintegral
    have hmoment_le : ∫ ω, |Xm ω| ^ a ∂P ≤ (C : ℝ) ^ a := by
      simpa [hIntegral_toReal] using hmoment_toReal_le
    have hmoment_nonneg : 0 ≤ ∫ ω, |Xm ω| ^ a ∂P := by
      refine integral_nonneg ?_
      intro ω
      exact Real.rpow_nonneg (abs_nonneg _) _
    have hnorm_eq :
        lpNorm Xm (ENNReal.ofReal a) P = (∫ ω, |Xm ω| ^ a ∂P) ^ (1 / a) := by
      rw [lpNorm_eq_integral_norm_rpow_toReal (by positivity) (by simp)
        hXm_meas.aestronglyMeasurable]
      simp [Real.norm_eq_abs, ENNReal.toReal_ofReal ha_nonneg]
    have hC_eq : ((C : ℝ) ^ a) ^ (1 / a) = C := by
      calc
        ((C : ℝ) ^ a) ^ (1 / a) = (C : ℝ) ^ (a * (1 / a)) := by
          rw [← Real.rpow_mul (show 0 ≤ (C : ℝ) from C.2)]
        _ = (C : ℝ) ^ (1 : ℝ) := by
          congr 1
          field_simp [ha_pos.ne']
        _ = C := by
          rw [Real.rpow_one]
    rw [hnorm_eq]
    calc
      (∫ ω, |Xm ω| ^ a ∂P) ^ (1 / a) ≤ ((C : ℝ) ^ a) ^ (1 / a) := by
        exact Real.rpow_le_rpow hmoment_nonneg hmoment_le (by positivity)
      _ = C := hC_eq
  have hX_memLp : MemLp X (ENNReal.ofReal a) P :=
    (memLp_congr_ae hXm_eq).2 hXm_memLp
  have hlpNorm_eq :
      lpNorm X (ENNReal.ofReal a) P = lpNorm Xm (ENNReal.ofReal a) P := by
    calc
      lpNorm X (ENNReal.ofReal a) P = (eLpNorm X (ENNReal.ofReal a) P).toReal := by
        symm
        exact toReal_eLpNorm hX_memLp.aestronglyMeasurable
      _ = (eLpNorm Xm (ENNReal.ofReal a) P).toReal := by
        congr 1
        exact eLpNorm_congr_ae hXm_eq
      _ = lpNorm Xm (ENNReal.ofReal a) P := by
        exact toReal_eLpNorm hXm_memLp.aestronglyMeasurable
  exact ⟨hX_memLp, by simpa [hlpNorm_eq] using hXm_lpNorm_le⟩

/-- Helper for Theorem 7.50: on a nonzero finite measure, the `Lp` norm is the total-mass factor
times the `Lp` norm on the normalized probability measure. -/
lemma lpNorm_eq_mass_rpow_mul_lpNorm_normalize
    [Nonempty Ω] (ν : FiniteMeasure Ω) (_hν : ν ≠ 0) {r : ℝ≥0∞} (hr : r ≠ ∞) (Y : Ω → ℝ) :
    lpNorm Y r (ν : Measure Ω) =
      (ν.mass ^ (1 / r.toReal) : NNReal) * lpNorm Y r (ν.normalize : Measure Ω) := by
  -- Proof comment: rewrite the finite measure as its mass times the normalized probability
  -- measure, then apply the standard `lpNorm` scaling rule once.
  have hmeasure :
      (ν : Measure Ω) = ν.mass • (ν.normalize : Measure Ω) := by
    simpa using congrArg (fun ν' : FiniteMeasure Ω ↦ (ν' : Measure Ω))
      ν.self_eq_mass_smul_normalize
  rw [hmeasure, MeasureTheory.lpNorm_smul_measure_of_ne_top hr]
  simp [NNReal.smul_def]

/-- Helper for Theorem 7.50: in the endpoint case `p = 1`, every finite partial density defines an
`L^∞` element of norm at most `‖F‖`. -/
lemma partialLocalizedDensityLpApprox_pOne
    (hp1 : p = 1) (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) :
    ∃ fs : Lp ℝ (conjExponent p) μ,
      (fs : Ω → ℝ) =ᵐ[μ] partialLocalizedDensity F s ∧ ‖fs‖ ≤ ‖F‖ := by
  subst hp1
  let g : Ω → ℝ := partialLocalizedDensity F s
  have hg_int : Integrable g μ :=
    integrable_partialLocalizedDensity F s
  have habs_int :
      ∀ A : Set Ω, MeasurableSet A → μ A < ∞ → ‖∫ x in A, g x ∂μ‖ ≤ ‖F‖ * μ.real A := by
    intro A hA hμA
    let U : Set Ω := ⋃ k ∈ s, A ∩ dualityPiece μ k
    have hU_meas : MeasurableSet U := by
      -- The localized finite union is measurable because each piece is measurable.
      exact s.measurableSet_biUnion fun k _hk ↦ hA.inter (measurableSet_dualityPiece k)
    have hμU : μ U < ∞ := by
      -- Each localized piece lies in one finite duality piece.
      exact measure_biUnion_lt_top
        s.finite_toSet
        (fun k _hk ↦ measure_inter_dualityPiece_lt_top A k)
    have hU_subset : U ⊆ A := by
      -- Dropping the piece intersection shows the finite union stays inside `A`.
      intro x hx
      simp only [U, Set.mem_iUnion] at hx
      rcases hx with ⟨k, hk, hxk⟩
      exact hxk.1
    calc
      ‖∫ x in A, g x ∂μ‖
        = ‖F (indicatorConstLp 1 hU_meas hμU.ne (1 : ℝ))‖ := by
            rw [partialLocalizedDensity_apply F s hA]
      _ ≤ ‖F‖ * μ.real U ^ (1 / (1 : ℝ≥0∞).toReal) := by
            exact indicator_functional_bound F hU_meas hμU.ne
      _ = ‖F‖ * μ.real U := by simp
      _ ≤ ‖F‖ * μ.real A := by
            exact mul_le_mul_of_nonneg_left
              (MeasureTheory.measureReal_mono hU_subset hμA.ne)
              (norm_nonneg _)
  have h_upper_nonneg : 0 ≤ᵐ[μ] fun x ↦ ‖F‖ - g x := by
    -- The localized set-integral estimate upgrades to an a.e. upper bound on the density.
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
    · intro A hA hμA
      exact (integrableOn_const hμA.ne).sub hg_int.integrableOn
    · intro A hA hμA
      have hconst : IntegrableOn (fun _ : Ω ↦ ‖F‖) A μ := integrableOn_const hμA.ne
      change 0 ≤ ∫ x in A, ((fun _ : Ω ↦ ‖F‖) - g) x ∂μ
      rw [integral_sub' hconst hg_int.integrableOn, setIntegral_const, smul_eq_mul, sub_nonneg]
      exact le_trans (le_abs_self _) <| by
        simpa [Real.norm_eq_abs, mul_comm] using habs_int A hA hμA
  have h_lower_nonneg : 0 ≤ᵐ[μ] fun x ↦ ‖F‖ + g x := by
    -- Applying the same integral control to the negative part gives the matching lower bound.
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite ?_ ?_
    · intro A hA hμA
      exact (integrableOn_const hμA.ne).add hg_int.integrableOn
    · intro A hA hμA
      have hconst : IntegrableOn (fun _ : Ω ↦ ‖F‖) A μ := integrableOn_const hμA.ne
      rw [integral_add hconst hg_int.integrableOn, setIntegral_const, smul_eq_mul]
      have hneg : -(‖F‖ * μ.real A) ≤ -‖∫ x in A, g x ∂μ‖ := by
        linarith [habs_int A hA hμA]
      linarith [hneg.trans (neg_abs_le (∫ x in A, g x ∂μ))]
  have hbound_ae : ∀ᵐ x ∂μ, ‖g x‖ ≤ ‖F‖ := by
    -- Combine the upper and lower pointwise inequalities into the absolute-value bound.
    filter_upwards [h_upper_nonneg, h_lower_nonneg] with x hx_upper hx_lower
    have hx_upper' : 0 ≤ ‖F‖ - g x := by simpa using hx_upper
    have hx_lower' : 0 ≤ ‖F‖ + g x := by simpa using hx_lower
    have h_upper : g x ≤ ‖F‖ := sub_nonneg.mp hx_upper'
    have h_lower : -‖F‖ ≤ g x := by linarith
    simpa [Real.norm_eq_abs] using abs_le.2 ⟨h_lower, h_upper⟩
  have hmem : MemLp g ∞ μ :=
    memLp_top_of_bound hg_int.aestronglyMeasurable ‖F‖ hbound_ae
  have hendpoint : ∃ fs : Lp ℝ ∞ μ, (fs : Ω → ℝ) =ᵐ[μ] g ∧ ‖fs‖ ≤ ‖F‖ := by
    refine ⟨hmem.toLp g, MemLp.coeFn_toLp hmem, ?_⟩
    -- The a.e. bound on `g` turns directly into the `L∞` norm bound of its `toLp` class.
    rw [Lp.norm_toLp, eLpNorm_exponent_top, MeasureTheory.eLpNormEssSup_eq_essSup_enorm]
    calc
      (essSup (fun x ↦ ‖g x‖ₑ) μ).toReal ≤ (ENNReal.ofReal ‖F‖).toReal := by
        exact ENNReal.toReal_mono (by simp) <|
          essSup_le_of_ae_le (ENNReal.ofReal ‖F‖) <| by
            filter_upwards [hbound_ae] with x hx
            simpa [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal hx
      _ = ‖F‖ := by simp
  rcases hendpoint with ⟨fs, hfs_ae, hfs_norm⟩
  have hq : conjExponent (1 : ℝ≥0∞) = ∞ := by
    simpa using
      (ENNReal.HolderConjugate.conjExponent_eq : conjExponent (1 : ℝ≥0∞) = ∞)
  refine ⟨cast (by rw [hq.symm]) fs, ?_, ?_⟩
  · exact (lpCast_coeFn_aeEq hq.symm fs).trans <| by simpa [g] using hfs_ae
  · calc
      ‖cast (by rw [hq.symm]) fs‖ = ‖fs‖ := lpNorm_cast_eq hq.symm fs
      _ ≤ ‖F‖ := hfs_norm

/-- Helper for Theorem 7.50: every finite partial density should admit an `L^q` representative
with the same almost-everywhere values and norm controlled by `‖F‖`. -/
lemma integral_normalize_eq_inv_mass_integral
    [Nonempty Ω] (ν : FiniteMeasure Ω) (hν : ν ≠ 0) (f : Ω → ℝ) :
    ∫ x, f x ∂(ν.normalize : Measure Ω) = (ν.mass : ℝ)⁻¹ * ∫ x, f x ∂(ν : Measure Ω) := by
  -- Proof comment: first rewrite the normalized integral as the finite-measure average.
  rw [← ν.average_eq_integral_normalize hν]
  -- Proof comment: expanding the average gives exactly the real scalar normal form needed later.
  rw [MeasureTheory.average_eq]
  simp [smul_eq_mul]

/-- Helper for Theorem 7.50: every finite partial density should admit an `L^q` representative
with the same almost-everywhere values and norm controlled by `‖F‖`. -/
lemma partialLocalizedDensityLpApprox
    (F : StrongDual ℝ (Lp ℝ p μ)) (s : Finset ℕ) :
    ∃ fs : Lp ℝ (conjExponent p) μ,
      (fs : Ω → ℝ) =ᵐ[μ] partialLocalizedDensity F s ∧ ‖fs‖ ≤ ‖F‖ := by
  by_cases hp1 : p = 1
  · -- The endpoint `q = ∞` route is now handled directly by a.e. bounds on finite partial
    -- densities.
    exact partialLocalizedDensityLpApprox_pOne hp1 F s
  · -- Route correction: the endpoint is closed, so the only remaining branch is `1 < p < ∞`.
    let U : Set Ω := ⋃ k ∈ s, dualityPiece μ k
    have hU_meas : MeasurableSet U := by
      exact s.measurableSet_biUnion fun k _hk ↦ measurableSet_dualityPiece k
    have hU_finite : μ U < ∞ := by
      simpa [U] using measure_biUnion_dualityPiece_lt_top s
    by_cases hU_zero : μ U = 0
    · have hzero_ae : partialLocalizedDensity F s =ᵐ[μ] 0 :=
        partialLocalizedDensity_zero_ae_of_measure_union_eq_zero F s <| by simpa [U] using hU_zero
      refine ⟨0, ?_, by simp⟩
      change ((0 : Lp ℝ (conjExponent p) μ) : Ω → ℝ) =ᵐ[μ] partialLocalizedDensity F s
      exact (Lp.coeFn_zero ℝ (conjExponent p) μ).trans hzero_ae.symm
    · have hp_gt_one : 1 < p := lt_of_le_of_ne (Fact.out : 1 ≤ p) <| by simpa [eq_comm] using hp1
      have hp_toReal_gt_one : 1 < p.toReal := by
        exact (ENNReal.toReal_lt_toReal (by simp) (Fact.out : p < ∞).ne).2 hp_gt_one
      have hq_gt_one : 1 < conjExponent p := by
        exact
          (ENNReal.HolderConjugate.lt_top_iff_one_lt p (conjExponent p)).1
            (Fact.out : p < ∞)
      have hq_lt_top : conjExponent p < ∞ := by
        exact
          (ENNReal.HolderConjugate.lt_top_iff_one_lt (conjExponent p) p).2 hp_gt_one
      have hq_ne_top : conjExponent p ≠ ∞ := hq_lt_top.ne
      have hq_toReal_gt_one : 1 < (conjExponent p).toReal := by
        exact (ENNReal.toReal_lt_toReal (by simp) hq_lt_top.ne).2 hq_gt_one
      have habReal : (conjExponent p).toReal.HolderConjugate p.toReal := by
        exact ENNReal.HolderConjugate.toReal hq_toReal_gt_one
      have hinv : 1 / (conjExponent p).toReal + 1 / p.toReal = 1 := by
        simpa using habReal.inv_add_inv_eq_one
      letI : Nonempty Ω := ⟨(nonempty_of_measure_ne_zero hU_zero).choose⟩
      let ν0 : FiniteMeasure Ω := ⟨μ.restrict U, by
        refine IsFiniteMeasure.mk ?_
        simpa [Measure.restrict_apply_univ, hU_meas] using hU_finite⟩
      let ν : Measure Ω := (ν0.normalize : Measure Ω)
      have hν0_mass_ne_zero : ν0.mass ≠ 0 := by
        intro hmass
        have hzero : ν0 = 0 := (MeasureTheory.FiniteMeasure.mass_zero_iff ν0).1 hmass
        have huniv : ((ν0 : Measure Ω) Set.univ) = 0 := by
          simpa using congrArg (fun ν' : FiniteMeasure Ω ↦ ((ν' : Measure Ω) Set.univ)) hzero
        exact hU_zero <| by
          simpa [ν0, U, Measure.restrict_apply_univ, hU_meas] using huniv
      have hν0_ne : ν0 ≠ 0 := by
        exact fun hν ↦ hν0_mass_ne_zero <| (MeasureTheory.FiniteMeasure.mass_zero_iff ν0).2 hν
      have hν_eq : ν = ν0.mass⁻¹ • μ.restrict U := by
        simpa [ν, ν0] using ν0.toMeasure_normalize_eq_of_nonzero hν0_ne
      have hrestrict_eq : μ.restrict U = ν0.mass • ν := by
        change (ν0 : Measure Ω) = ν0.mass • ν
        simpa [ν] using congrArg (fun ν' : FiniteMeasure Ω ↦ (ν' : Measure Ω))
          ν0.self_eq_mass_smul_normalize
      let C : NNReal := ⟨‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1), by positivity⟩
      have hpair_prob :
          ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
            (∃ M : NNReal, ∀ x, |Y x| ≤ M) →
            Integrable (fun x ↦ partialLocalizedDensity F s x * Y x) ν ∧
              |∫ x, partialLocalizedDensity F s x * Y x ∂ν| ≤
                (‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1)) * lpNorm Y p ν := by
        intro Y hY_meas hY_bdd
        let g : Ω → ℝ := Set.indicator U Y
        have hg_meas : Measurable g := hY_meas.indicator hU_meas
        have hg_bdd : ∃ M : NNReal, ∀ x, |g x| ≤ M := by
          rcases hY_bdd with ⟨M, hM⟩
          refine ⟨M, fun x ↦ ?_⟩
          by_cases hx : x ∈ U
          · simpa [g, hx] using hM x
          · simp [g, hx]
        have hg_support : Function.support g ⊆ U := by
          dsimp [g]
          intro x hx
          by_contra hxU
          simp [hxU] at hx
        have hLp_g : MemLp g p μ :=
          memLp_of_measurable_bounded_support_biUnion s hg_meas hg_bdd <| by
            simpa [U] using hg_support
        have hLp_Y_restrict : MemLp Y p (μ.restrict U) := by
          simpa [g] using
            (memLp_indicator_iff_restrict hU_meas).1 hLp_g
        have hlp_g :
            lpNorm g p μ = lpNorm Y p (μ.restrict U) := by
          calc
            lpNorm g p μ = (eLpNorm g p μ).toReal := by
              symm
              exact toReal_eLpNorm hLp_g.aestronglyMeasurable
            _ = (eLpNorm Y p (μ.restrict U)).toReal := by
              congr 1
              simpa [g] using
                MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU_meas
            _ = lpNorm Y p (μ.restrict U) := by
              exact toReal_eLpNorm hLp_Y_restrict.aestronglyMeasurable
        have hpair_g :
            F (hLp_g.toLp g) = ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
          exact partialLocalizedDensity_pairing_eq_boundedSupport F s hg_meas hg_bdd <| by
            simpa [U] using hg_support
        have hbound_g :
            |∫ x, partialLocalizedDensity F s x * g x ∂μ| ≤
              ‖F‖ * lpNorm Y p (μ.restrict U) := by
          calc
            |∫ x, partialLocalizedDensity F s x * g x ∂μ| = ‖F (hLp_g.toLp g)‖ := by
              rw [← hpair_g, Real.norm_eq_abs]
            _ ≤ ‖F‖ * ‖hLp_g.toLp g‖ := ContinuousLinearMap.le_opNorm _ _
            _ = ‖F‖ * (eLpNorm g p μ).toReal := by rw [Lp.norm_toLp]
            _ = ‖F‖ * lpNorm g p μ := by rw [toReal_eLpNorm hLp_g.aestronglyMeasurable]
            _ = ‖F‖ * lpNorm Y p (μ.restrict U) := by rw [hlp_g]
        have hprod_int_mu : Integrable (fun x ↦ partialLocalizedDensity F s x * Y x) μ := by
          rcases hY_bdd with ⟨M, hM⟩
          exact (integrable_partialLocalizedDensity F s).mul_bdd hY_meas.aestronglyMeasurable <|
            Filter.Eventually.of_forall fun x ↦ by
              simpa [Real.norm_eq_abs] using hM x
        have hprod_int_restrict :
            Integrable (fun x ↦ partialLocalizedDensity F s x * Y x) (μ.restrict U) :=
          hprod_int_mu.restrict
        have hprod_int_ν :
            Integrable (fun x ↦ partialLocalizedDensity F s x * Y x) ν := by
          -- Proof comment: the normalized measure differs from the restricted measure by one
          -- scalar, so integrability transports directly.
          rw [hν_eq]
          exact hprod_int_restrict.smul_measure (by simp)
        have hset_integral :
            ∫ x in U, partialLocalizedDensity F s x * Y x ∂μ =
              ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
          calc
            ∫ x in U, partialLocalizedDensity F s x * Y x ∂μ =
                ∫ x, U.indicator (fun x ↦ partialLocalizedDensity F s x * Y x) x ∂μ := by
                  symm
                  exact integral_indicator hU_meas
            _ = ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
                  refine integral_congr_ae ?_
                  exact Filter.Eventually.of_forall fun x ↦ by
                    by_cases hx : x ∈ U
                    · simp [g, hx]
                    · simp [g, hx]
        have hnorm_Y :
            lpNorm Y p (μ.restrict U) =
              (ν0.mass : ℝ) ^ (1 / p.toReal) * lpNorm Y p ν := by
          simpa [ν, NNReal.coe_rpow] using
            lpNorm_eq_mass_rpow_mul_lpNorm_normalize ν0 hν0_ne (Fact.out : p < ∞).ne Y
        have hν_integral :
            ∫ x, partialLocalizedDensity F s x * Y x ∂ν =
              (ν0.mass : ℝ)⁻¹ * ∫ x, partialLocalizedDensity F s x * g x ∂μ := by
          -- Proof comment: rewrite the normalized integral through the average-based bridge,
          -- then identify the remaining restricted integral with the ambient indicator test.
          rw [integral_normalize_eq_inv_mass_integral ν0 hν0_ne]
          rw [show ∫ x, partialLocalizedDensity F s x * Y x ∂(ν0 : Measure Ω) =
              ∫ x in U, partialLocalizedDensity F s x * Y x ∂μ by
            rfl]
          rw [hset_integral]
        refine ⟨hprod_int_ν, ?_⟩
        calc
          |∫ x, partialLocalizedDensity F s x * Y x ∂ν|
              = (ν0.mass : ℝ)⁻¹ * |∫ x, partialLocalizedDensity F s x * g x ∂μ| := by
                  rw [hν_integral, abs_mul, abs_of_nonneg]
                  positivity
          _ ≤ (ν0.mass : ℝ)⁻¹ * (‖F‖ * lpNorm Y p (μ.restrict U)) := by
                gcongr
          _ = (ν0.mass : ℝ)⁻¹ *
                (‖F‖ * ((ν0.mass : ℝ) ^ (1 / p.toReal) * lpNorm Y p ν)) := by
                rw [hnorm_Y]
          _ = (‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1)) * lpNorm Y p ν := by
                have hmass_pos : 0 < (ν0.mass : ℝ) := by
                  exact_mod_cast (show 0 < ν0.mass from pos_iff_ne_zero.mpr hν0_mass_ne_zero)
                calc
                  (ν0.mass : ℝ)⁻¹ *
                      (‖F‖ * ((ν0.mass : ℝ) ^ (1 / p.toReal) * lpNorm Y p ν))
                      = ‖F‖ * (((ν0.mass : ℝ)⁻¹ * (ν0.mass : ℝ) ^ (1 / p.toReal)) *
                          lpNorm Y p ν) := by ring
                  _ = ‖F‖ * (((ν0.mass : ℝ) ^ (1 / p.toReal - 1)) * lpNorm Y p ν) := by
                        congr 1
                        congr 1
                        calc
                          (ν0.mass : ℝ)⁻¹ * (ν0.mass : ℝ) ^ (1 / p.toReal)
                              = (ν0.mass : ℝ) ^ (-1 : ℝ) * (ν0.mass : ℝ) ^ (1 / p.toReal) := by
                                  rw [Real.rpow_neg_one]
                          _ = (ν0.mass : ℝ) ^ (-1 + 1 / p.toReal) := by
                                rw [← Real.rpow_add hmass_pos]
                          _ = (ν0.mass : ℝ) ^ (1 / p.toReal - 1) := by
                                congr 1
                                ring
                  _ = (‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1)) * lpNorm Y p ν := by ring
      have hpair_C :
          ∀ ⦃Y : Ω → ℝ⦄, Measurable Y →
            (∃ M : NNReal, ∀ x, |Y x| ≤ M) →
            Integrable (fun x ↦ partialLocalizedDensity F s x * Y x) ν ∧
              |∫ x, partialLocalizedDensity F s x * Y x ∂ν| ≤
                (C : ℝ) * lpNorm Y (ENNReal.ofReal p.toReal) ν := by
        intro Y hY_meas hY_bdd
        rcases hpair_prob hY_meas hY_bdd with ⟨hint, hbound⟩
        refine ⟨hint, ?_⟩
        simpa [C, ENNReal.ofReal_toReal (Fact.out : p < ∞).ne] using hbound
      letI : IsProbabilityMeasure ν := by
        dsimp [ν]
        infer_instance
      have hq_ofReal : ENNReal.ofReal (conjExponent p).toReal = conjExponent p := by
        exact ENNReal.ofReal_toReal hq_ne_top
      rcases memLpAndLpNorm_le_of_boundedMeasurablePairingBound
          C habReal hpair_C with
        ⟨hmem_ν, hnorm_ν⟩
      have hmem_ν' : MemLp (partialLocalizedDensity F s) (conjExponent p) ν := by
        simpa [hq_ofReal] using hmem_ν
      have hnorm_ν' :
          lpNorm (partialLocalizedDensity F s) (conjExponent p) ν ≤
            ‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1) := by
        simpa [C, hq_ofReal] using hnorm_ν
      have hmem_restrict : MemLp (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) := by
        -- Proof comment: transport the `L^q` witness back from the normalized probability measure
        -- to the original finite restricted measure using the same mass factor.
        rw [hrestrict_eq]
        exact hmem_ν'.smul_measure (by simp)
      have hnorm_restrict :
          lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) ≤ ‖F‖ := by
        have hmass_pos : 0 < (ν0.mass : ℝ) := by
          exact_mod_cast (show 0 < ν0.mass from pos_iff_ne_zero.mpr hν0_mass_ne_zero)
        have hexp : (conjExponent p).toReal⁻¹ + (p.toReal⁻¹ - 1) = 0 := by
          have htmp : 1 / (conjExponent p).toReal + (1 / p.toReal - 1) = 0 := by
            linarith [hinv]
          simpa [one_div] using htmp
        have hlp_restrict :
            lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) =
              (ν0.mass : ℝ) ^ (1 / (conjExponent p).toReal) *
                lpNorm (partialLocalizedDensity F s) (conjExponent p) ν := by
          simpa [ν, NNReal.coe_rpow] using
            lpNorm_eq_mass_rpow_mul_lpNorm_normalize ν0 hν0_ne hq_ne_top
              (partialLocalizedDensity F s)
        calc
          lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U)
              = (ν0.mass : ℝ) ^ (1 / (conjExponent p).toReal) *
                  lpNorm (partialLocalizedDensity F s) (conjExponent p) ν := hlp_restrict
          _ ≤ (ν0.mass : ℝ) ^ (1 / (conjExponent p).toReal) *
                (‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1)) := by
                  gcongr
          _ = ‖F‖ := by
                calc
                  (ν0.mass : ℝ) ^ (1 / (conjExponent p).toReal) *
                      (‖F‖ * (ν0.mass : ℝ) ^ (1 / p.toReal - 1))
                      =
                    ‖F‖ * ((ν0.mass : ℝ) ^ (1 / (conjExponent p).toReal) *
                      (ν0.mass : ℝ) ^ (1 / p.toReal - 1)) := by ring
                  _ =
                      ‖F‖ *
                        (ν0.mass : ℝ) ^
                          (1 / (conjExponent p).toReal + (1 / p.toReal - 1)) := by
                            rw [← Real.rpow_add hmass_pos]
                  _ = ‖F‖ * (ν0.mass : ℝ) ^ 0 := by
                        simpa [one_div] using
                          congrArg (fun t : ℝ ↦ ‖F‖ * (ν0.mass : ℝ) ^ t) hexp
                  _ = ‖F‖ := by simp
      have hmem_indicator :
          MemLp (Set.indicator U (partialLocalizedDensity F s)) (conjExponent p) μ := by
        exact (memLp_indicator_iff_restrict hU_meas).2 hmem_restrict
      have hmem_ambient : MemLp (partialLocalizedDensity F s) (conjExponent p) μ := by
        exact
          (memLp_congr_ae (partialLocalizedDensity_ae_eq_indicator_biUnion F s)).2
            hmem_indicator
      have hlp_ambient :
          lpNorm (partialLocalizedDensity F s) (conjExponent p) μ =
            lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) := by
        calc
          lpNorm (partialLocalizedDensity F s) (conjExponent p) μ =
              lpNorm (Set.indicator U (partialLocalizedDensity F s)) (conjExponent p) μ := by
                rw [← toReal_eLpNorm hmem_ambient.aestronglyMeasurable,
                  eLpNorm_congr_ae (partialLocalizedDensity_ae_eq_indicator_biUnion F s),
                  toReal_eLpNorm hmem_indicator.aestronglyMeasurable]
          _ = lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) := by
                rw [← toReal_eLpNorm hmem_indicator.aestronglyMeasurable,
                  MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict hU_meas,
                  toReal_eLpNorm hmem_restrict.aestronglyMeasurable]
      refine ⟨hmem_ambient.toLp (partialLocalizedDensity F s), MemLp.coeFn_toLp hmem_ambient, ?_⟩
      calc
        ‖hmem_ambient.toLp (partialLocalizedDensity F s)‖
            = lpNorm (partialLocalizedDensity F s) (conjExponent p) μ := by
                rw [Lp.norm_toLp, ← toReal_eLpNorm hmem_ambient.aestronglyMeasurable]
        _ = lpNorm (partialLocalizedDensity F s) (conjExponent p) (μ.restrict U) := hlp_ambient
        _ ≤ ‖F‖ := hnorm_restrict

/-- Helper for Theorem 7.50: the truncation error between a finite-measure set and its first `N`
duality pieces is exactly the corresponding localized tail. -/
lemma symmDiff_biUnion_range_inter_dualityPiece_eq_iUnion_Ici_inter_dualityPiece
    (A : Set Ω) (N : ℕ) :
    (⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k) ∆ A = ⋃ k ≥ N, A ∩ dualityPiece μ k := by
  -- The range truncation misses exactly those points whose unique duality piece index is at least
  -- `N`.
  have hsubset : (⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k) ⊆ A := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    rcases hx with ⟨k, hx⟩
    rcases hx with ⟨hk, hxk⟩
    exact hxk.1
  ext x
  constructor
  · intro hx
    have hx' :
        (x ∈ ⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k ∧ x ∉ A) ∨
          (x ∈ A ∧ x ∉ ⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k) := by
      simpa [Set.symmDiff_def]
        using hx
    have hxA : x ∈ A := by
      rcases hx' with hx_left | hx_right
      · exfalso
        exact hx_left.2 (hsubset hx_left.1)
      · exact hx_right.1
    have hx_not_mem :
        x ∉ ⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k := by
      rcases hx' with hx_left | hx_right
      · exfalso
        exact hx_left.2 (hsubset hx_left.1)
      · exact hx_right.2
    have hx_piece : x ∈ ⋃ n, dualityPiece μ n := by
      simp [iUnion_dualityPiece]
    rcases Set.mem_iUnion.1 hx_piece with ⟨k, hxk⟩
    have hk_ge : N ≤ k := by
      by_contra hk_ge
      have hk_range : k ∈ Finset.range N := by
        simpa [Finset.mem_range] using Nat.lt_of_not_ge hk_ge
      exact hx_not_mem <| Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk_range, ⟨hxA, hxk⟩⟩⟩
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk_ge, ⟨hxA, hxk⟩⟩⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
    rcases Set.mem_iUnion.1 hxk with ⟨hkN, hxk⟩
    right
    refine ⟨hxk.1, ?_⟩
    intro hx_mem
    rcases Set.mem_iUnion.1 hx_mem with ⟨j, hxj⟩
    rcases Set.mem_iUnion.1 hxj with ⟨hj_range, hxj⟩
    have hjk : j ≠ k := by
      intro hEq
      have : k < N := by simpa [hEq] using (Finset.mem_range.1 hj_range)
      exact (not_lt_of_ge hkN) this
    have hdisj : Disjoint (dualityPiece μ j) (dualityPiece μ k) := by
      exact pairwiseDisjoint_dualityPiece hjk
    exact hdisj.le_bot ⟨hxj.2, hxk.2⟩

/-- Helper for Theorem 7.50: truncating a finite-measure measurable set by the first `N` duality
pieces converges to the original indicator in `L^p`. -/
lemma tendsto_indicatorConstLp_biUnion_range_inter_dualityPiece
    {A : Set Ω} (hA : MeasurableSet A) (hμA : μ A < ∞) (c : ℝ) :
    Filter.Tendsto
      (fun N ↦
        indicatorConstLp p
          ((Finset.range N).measurableSet_biUnion
            fun k _hk ↦ hA.inter (measurableSet_dualityPiece k))
          ((measure_biUnion_lt_top
            (Finset.range N).finite_toSet
            (fun k _hk ↦ measure_inter_dualityPiece_lt_top A k)).ne)
          c)
      atTop
      (𝓝 (indicatorConstLp p hA hμA.ne c)) := by
  let t : ℕ → Set Ω := fun N ↦ ⋃ k ∈ Finset.range N, A ∩ dualityPiece μ k
  have ht_meas :
      ∀ N, MeasurableSet (t N) := by
    intro N
    exact (Finset.range N).measurableSet_biUnion fun k _hk ↦
      hA.inter (measurableSet_dualityPiece k)
  have hμt :
      ∀ N, μ (t N) ≠ ∞ := by
    intro N
    exact
      (measure_biUnion_lt_top
        (Finset.range N).finite_toSet
        (fun k _hk ↦ measure_inter_dualityPiece_lt_top A k)).ne
  have hTail :
      Filter.Tendsto (fun N ↦ μ (t N ∆ A)) atTop (𝓝 0) := by
    let ν : Measure Ω := μ.restrict A
    letI : IsFiniteMeasure ν :=
      ⟨by simpa [ν, Measure.restrict_apply, hA] using hμA⟩
    have hν :
        Filter.Tendsto (fun N ↦ ν (⋃ k ≥ N, dualityPiece μ k)) atTop (𝓝 0) := by
      simpa using
        (tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
          (fun k ↦ (measurableSet_dualityPiece k).nullMeasurableSet)
          pairwiseDisjoint_dualityPiece)
    refine hν.congr' <| Filter.Eventually.of_forall fun N ↦ ?_
    have hTailMeas : MeasurableSet (⋃ k ≥ N, dualityPiece μ k) := by
      exact MeasurableSet.iUnion fun k ↦
        MeasurableSet.iUnion fun _ : N ≤ k ↦ measurableSet_dualityPiece k
    calc
      ν (⋃ k ≥ N, dualityPiece μ k)
          = μ (((⋃ k ≥ N, dualityPiece μ k)) ∩ A) := by
              simp [ν, Measure.restrict_apply, hTailMeas, Set.inter_comm]
      _ = μ (⋃ k ≥ N, A ∩ dualityPiece μ k) := by
            congr 1
            ext x
            constructor
            · intro hx
              rcases hx with ⟨hx_union, hxA⟩
              rcases Set.mem_iUnion.1 hx_union with ⟨k, hxk⟩
              rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
              exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, ⟨hxA, hxk⟩⟩⟩
            · intro hx
              rcases Set.mem_iUnion.1 hx with ⟨k, hxk⟩
              rcases Set.mem_iUnion.1 hxk with ⟨hk, hxk⟩
              exact ⟨Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk.2⟩⟩, hxk.1⟩
      _ = μ (t N ∆ A) := by
            rw [symmDiff_biUnion_range_inter_dualityPiece_eq_iUnion_Ici_inter_dualityPiece]
  -- Continuity of `indicatorConstLp` with respect to the symmetric-difference measure gives the
  -- desired `Lp` convergence.
  simpa [t, ht_meas, hμt] using
    @MeasureTheory.tendsto_indicatorConstLp_set
      Ω ℝ _ p μ _ A hA hμA.ne c _ ℕ atTop t ht_meas hμt ((Fact.out : p < ∞).ne) hTail

/-- Helper for Theorem 7.50: once a global `L^q` witness agrees almost everywhere with the glued
localized density, indicator constants already identify the functional with `lpPairing`. -/
lemma lpPairing_eq_on_indicatorConst_of_aeEq_localizedDensity
    (F : StrongDual ℝ (Lp ℝ p μ)) {f : Lp ℝ (conjExponent p) μ}
    (hf : (f : Ω → ℝ) =ᵐ[μ] localizedDensity F) :
    ∀ (c : ℝ) {s : Set Ω} (hs : MeasurableSet s) (hμs : μ s < ∞),
      F (indicatorConstLp p hs hμs.ne c) =
        (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (indicatorConstLp p hs hμs.ne c) := by
  intro c s hs hμs
  let t : ℕ → Set Ω := fun N ↦ ⋃ k ∈ Finset.range N, s ∩ dualityPiece μ k
  let truncIndicator : ℕ → Lp ℝ p μ := fun N ↦
    indicatorConstLp p
      ((Finset.range N).measurableSet_biUnion
        fun k _hk ↦ hs.inter (measurableSet_dualityPiece k))
      ((measure_biUnion_lt_top
        (Finset.range N).finite_toSet
        (fun k hk ↦ measure_inter_dualityPiece_lt_top s k)).ne)
      c
  have ht_meas :
      ∀ N, MeasurableSet (t N) := by
    intro N
    exact (Finset.range N).measurableSet_biUnion fun k _hk ↦
      hs.inter (measurableSet_dualityPiece k)
  have hμt :
      ∀ N, μ (t N) < ∞ := by
    intro N
    exact measure_biUnion_lt_top
      (Finset.range N).finite_toSet
      (fun k hk ↦ measure_inter_dualityPiece_lt_top s k)
  have hIndicatorTendsto :
      Filter.Tendsto truncIndicator atTop (𝓝 (indicatorConstLp p hs hμs.ne c)) := by
    -- The duality-piece truncations exhaust the target set in symmetric-difference measure.
    simpa [truncIndicator, t] using
      tendsto_indicatorConstLp_biUnion_range_inter_dualityPiece hs hμs c
  have hFtendsto :
      Filter.Tendsto (fun N ↦ F (truncIndicator N)) atTop
        (𝓝 (F (indicatorConstLp p hs hμs.ne c))) := by
    exact (F.continuous.tendsto _).comp hIndicatorTendsto
  have hPairTendsto :
      Filter.Tendsto
        (fun N ↦ (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (truncIndicator N))
        atTop
        (𝓝 ((mul ℝ ℝ).lpPairing μ (conjExponent p) p f (indicatorConstLp p hs hμs.ne c))) := by
    exact (((mul ℝ ℝ).lpPairing μ (conjExponent p) p f).continuous.tendsto _).comp
      hIndicatorTendsto
  have hstage :
      ∀ N,
        F (truncIndicator N) =
          (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (truncIndicator N) := by
    intro N
    have hIndicatorSmul :
        truncIndicator N =
          c • indicatorConstLp p (ht_meas N) (hμt N).ne (1 : ℝ) := by
      dsimp [truncIndicator]
      rw [MeasureTheory.indicatorConstLp]
      refine MemLp.toLp_congr
        (memLp_indicator_const p (ht_meas N) c (Or.inr (hμt N).ne))
        ((memLp_indicator_const p (ht_meas N) (1 : ℝ) (Or.inr (hμt N).ne)).const_smul c) ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hxt : x ∈ t N
        · simp [Set.indicator_of_mem, hxt, smul_eq_mul]
        · simp [Set.indicator_of_notMem, hxt, smul_eq_mul]
    have hLocalizedUnionEq :
        (⋃ k ∈ Finset.range N, t N ∩ dualityPiece μ k) = t N := by
      ext x
      constructor
      · intro hx
        simp only [t, Set.mem_iUnion] at hx
        rcases hx with ⟨k, hk, hxk⟩
        exact hxk.1
      · intro hxt
        simp only [t, Set.mem_iUnion] at hxt ⊢
        rcases hxt with ⟨k, hk, hxk⟩
        exact ⟨k, hk, ⟨Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk⟩⟩, hxk.2⟩⟩
    have hIndicatorOne :
        indicatorConstLp p
            ((Finset.range N).measurableSet_biUnion
              fun k _hk ↦ (ht_meas N).inter (measurableSet_dualityPiece k))
            ((measure_biUnion_lt_top
              (Finset.range N).finite_toSet
              (fun k hk ↦ measure_inter_dualityPiece_lt_top (t N) k)).ne)
            (1 : ℝ)
          = indicatorConstLp p (ht_meas N) (hμt N).ne (1 : ℝ) := by
      exact MeasureTheory.indicatorConstLp.congr_simp
        hLocalizedUnionEq
        p
        ((Finset.range N).measurableSet_biUnion
          fun k _hk ↦ (ht_meas N).inter (measurableSet_dualityPiece k))
        ((measure_biUnion_lt_top
          (Finset.range N).finite_toSet
          (fun k hk ↦ measure_inter_dualityPiece_lt_top (t N) k)).ne)
        (1 : ℝ)
        (1 : ℝ)
        rfl
    have hIntegralLocalized :
        ∫ x in t N, c * partialLocalizedDensity F (Finset.range N) x ∂μ =
          ∫ x in t N, c * localizedDensity F x ∂μ := by
      calc
        ∫ x in t N, c * partialLocalizedDensity F (Finset.range N) x ∂μ
            = ∫ x, (t N).indicator
                (fun x ↦ c * partialLocalizedDensity F (Finset.range N) x) x ∂μ := by
                  rw [integral_indicator (ht_meas N)]
        _ = ∫ x, (t N).indicator (fun x ↦ c * localizedDensity F x) x ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards
                [partialLocalizedDensity_ae_eq_indicator_localizedDensity F (Finset.range N)] with
                  x hx
              by_cases hxt : x ∈ t N
              · have hxU :
                  x ∈ ⋃ k ∈ Finset.range N, dualityPiece μ k := by
                    simp only [t, Set.mem_iUnion] at hxt
                    rcases hxt with ⟨k, hk, hxk⟩
                    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨hk, hxk.2⟩⟩
                have hx' :
                    partialLocalizedDensity F (Finset.range N) x = localizedDensity F x := by
                  have hxIndicator :
                      (⋃ k ∈ Finset.range N, dualityPiece μ k).indicator
                          (localizedDensity F) x =
                        localizedDensity F x :=
                    Set.indicator_of_mem hxU (localizedDensity F)
                  exact hx.trans hxIndicator
                simp [hxt, hx']
              · simp [hxt]
        _ = ∫ x in t N, c * localizedDensity F x ∂μ := by
              rw [integral_indicator (ht_meas N)]
    have hIntegralTof :
        ∫ x in t N, c * localizedDensity F x ∂μ =
          ∫ x in t N, c * f x ∂μ := by
      calc
        ∫ x in t N, c * localizedDensity F x ∂μ
            = ∫ x, (t N).indicator (fun x ↦ c * localizedDensity F x) x ∂μ := by
                  rw [integral_indicator (ht_meas N)]
        _ = ∫ x, (t N).indicator (fun x ↦ c * f x) x ∂μ := by
              refine integral_congr_ae ?_
              filter_upwards [hf] with x hx
              by_cases hxt : x ∈ t N <;> simp [hxt, hx]
        _ = ∫ x in t N, c * f x ∂μ := by
              rw [integral_indicator (ht_meas N)]
    calc
      F (truncIndicator N)
          = c * F (indicatorConstLp p (ht_meas N) (hμt N).ne (1 : ℝ)) := by
              rw [hIndicatorSmul, map_smul]
              simp [smul_eq_mul]
      _ = c * ∫ x in t N, partialLocalizedDensity F (Finset.range N) x ∂μ := by
            rw [← hIndicatorOne, partialLocalizedDensity_apply F (Finset.range N) (ht_meas N)]
      _ = ∫ x in t N, c * partialLocalizedDensity F (Finset.range N) x ∂μ := by
            rw [integral_const_mul]
      _ = ∫ x in t N, c * localizedDensity F x ∂μ := hIntegralLocalized
      _ = ∫ x in t N, c * f x ∂μ := hIntegralTof
      _ = (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (truncIndicator N) := by
            symm
            exact lpPairing_indicatorConstLp_const f (ht_meas N) (hμt N).ne c
  have hSeq :
      (fun N ↦ F (truncIndicator N)) =
        fun N ↦ (mul ℝ ℝ).lpPairing μ (conjExponent p) p f (truncIndicator N) := by
    funext N
    exact hstage N
  exact tendsto_nhds_unique hFtendsto (hSeq ▸ hPairTendsto)

/-- Helper for Theorem 7.50: the glued localized density should define the global `L^q` witness
once the finite-support `L^q` upgrades are available. -/
lemma localizedDensity_memLp
    (F : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ f : Lp ℝ (conjExponent p) μ,
      (f : Ω → ℝ) =ᵐ[μ] localizedDensity F ∧ ‖f‖ ≤ ‖F‖ := by
  let truncDensity : ℕ → Ω → ℝ := fun N ↦
    Set.indicator (⋃ k ∈ Finset.range N, dualityPiece μ k) (localizedDensity F)
  have htrunc_mem :
      ∀ N, MemLp (truncDensity N) (conjExponent p) μ := by
    intro N
    rcases partialLocalizedDensityLpApprox F (Finset.range N) with ⟨fs, hfs_ae, _hfs_norm⟩
    have htrunc_ae :
        (fs : Ω → ℝ) =ᵐ[μ] truncDensity N := by
      exact
        hfs_ae.trans
          (partialLocalizedDensity_ae_eq_indicator_localizedDensity F (Finset.range N))
    -- Each truncation inherits the `L^q` class from the corresponding finite partial density.
    exact (memLp_congr_ae htrunc_ae).1 (Lp.memLp fs)
  have htrunc_bound :
      ∀ N, eLpNorm (truncDensity N) (conjExponent p) μ ≤ ‖F‖ₑ := by
    intro N
    rcases partialLocalizedDensityLpApprox F (Finset.range N) with ⟨fs, hfs_ae, hfs_norm⟩
    have htrunc_ae :
        (fs : Ω → ℝ) =ᵐ[μ] truncDensity N := by
      exact
        hfs_ae.trans
          (partialLocalizedDensity_ae_eq_indicator_localizedDensity F (Finset.range N))
    -- Rewrite the truncation through the finite-stage `Lp` representative, then read off the norm
    -- bound in `eLpNorm`.
    have hfs_enorm : ‖fs‖ₑ ≤ ‖F‖ₑ := by
      simpa using ENNReal.ofReal_le_ofReal hfs_norm
    calc
      eLpNorm (truncDensity N) (conjExponent p) μ = ‖fs‖ₑ := by
        rw [eLpNorm_congr_ae htrunc_ae.symm, Lp.enorm_def]
      _ ≤ ‖F‖ₑ := hfs_enorm
  have htrunc_aestronglyMeasurable :
      ∀ N, AEStronglyMeasurable (truncDensity N) μ := by
    intro N
    exact (htrunc_mem N).aestronglyMeasurable
  have htrunc_tendsto :
      ∀ x, Tendsto (fun N ↦ truncDensity N x) atTop (𝓝 (localizedDensity F x)) := by
    intro x
    have hx_union : x ∈ ⋃ n, dualityPiece μ n := by
      simp [iUnion_dualityPiece]
    rcases Set.mem_iUnion.1 hx_union with ⟨n, hxn⟩
    have hEventually :
        (fun N ↦ truncDensity N x) =ᶠ[atTop] fun _ ↦ localizedDensity F x := by
      exact Filter.eventually_atTop.2 ⟨n + 1, fun N hN ↦ by
        have hnN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hN
        have hxN : x ∈ ⋃ k ∈ Finset.range N, dualityPiece μ k := by
          exact Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Finset.mem_range.2 hnN, hxn⟩⟩
        exact Set.indicator_of_mem hxN (localizedDensity F)⟩
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ localizedDensity F x) atTop
      (𝓝 (localizedDensity F x))).congr' hEventually.symm
  have hlocalized_aestronglyMeasurable :
      AEStronglyMeasurable (localizedDensity F) μ := by
    exact aestronglyMeasurable_of_tendsto_ae atTop htrunc_aestronglyMeasurable
      (Filter.Eventually.of_forall htrunc_tendsto)
  have hlocalized_bound :
      eLpNorm (localizedDensity F) (conjExponent p) μ ≤ ‖F‖ₑ := by
    -- The finite truncations converge pointwise to the glued density and have a uniform `L^q`
    -- bound, so the limit keeps the same `eLpNorm` bound.
    exact Lp.eLpNorm_le_of_ae_tendsto
      (Filter.Eventually.of_forall htrunc_bound)
      htrunc_aestronglyMeasurable
      (Filter.Eventually.of_forall htrunc_tendsto)
  have hlocalized_mem : MemLp (localizedDensity F) (conjExponent p) μ := by
    exact ⟨hlocalized_aestronglyMeasurable, lt_of_le_of_lt hlocalized_bound (by simp)⟩
  refine ⟨hlocalized_mem.toLp (localizedDensity F), MemLp.coeFn_toLp hlocalized_mem, ?_⟩
  -- The `Lp` norm is the real part of the `eLpNorm`, so the uniform truncation bound descends to
  -- the final witness.
  calc
    ‖hlocalized_mem.toLp (localizedDensity F)‖
        = ENNReal.toReal
            (eLpNorm ((hlocalized_mem.toLp (localizedDensity F) : Lp ℝ (conjExponent p) μ) :
              Ω → ℝ) (conjExponent p) μ) := by
            rw [Lp.norm_def]
    _ = ENNReal.toReal (eLpNorm (localizedDensity F) (conjExponent p) μ) := by
          congr 1
          exact eLpNorm_congr_ae (MemLp.coeFn_toLp hlocalized_mem)
    _ ≤ ENNReal.toReal ‖F‖ₑ := by
          exact ENNReal.toReal_mono ENNReal.coe_ne_top hlocalized_bound
    _ = ‖F‖ := by simp

/-- Helper for Theorem 7.50: surjectivity is reduced to constructing, for each functional on
`L^p(μ)`, a representing `L^(conjExponent p)` density. -/
lemma exists_lpPairing_preimage
    (F : StrongDual ℝ (Lp ℝ p μ)) :
    ∃ f : Lp ℝ (conjExponent p) μ,
      (mul ℝ ℝ).lpPairing μ (conjExponent p) p f = F := by
  -- Route correction: the overlapping-`spanningSets` route was the wrong normalization, so the
  -- remaining surjectivity proof proceeds through the disjoint `dualityPiece μ n` exhaustion.
  rcases localizedDensity_memLp F with ⟨f, hf, _hf_norm⟩
  refine ⟨f, ?_⟩
  -- Once the global `L^q` witness matches the glued density, indicator functions determine the
  -- functional.
  symm
  exact functional_eq_lpPairing_of_indicatorConst F f
    (lpPairing_eq_on_indicatorConst_of_aeEq_localizedDensity F hf)

-- Proof sketch: injectivity follows from `lpDualityMap_isometry`. For surjectivity, represent a
-- continuous linear functional on `L^p(μ)` by the signed measure `ν(A) = F(1_A)`, apply the
-- Radon-Nikodym theorem to obtain a density `f`, prove `f ∈ L^{p'}(μ)` by the usual `p = 1` and
-- `1 < p < ∞` cases, and then identify the resulting integral functional with `F` on a dense
-- class of simple functions.
/-- Theorem 7.50: under the ambient sigma-finite hypothesis on `μ`, if `1 ≤ p < ∞` and `q`
satisfies `1 / p + 1 / q = 1`, then the canonical map `κ : L^q(μ) → (L^p(μ))'` is bijective.
Here `q` is represented by `ENNReal.conjExponent p`. -/
theorem lpDualityMap_bijective :
    Function.Bijective
      ((mul ℝ ℝ).lpPairing μ (conjExponent p) p :
        Lp ℝ (conjExponent p) μ → StrongDual ℝ (Lp ℝ p μ)) := by
  have hκ :
      Isometry
        ((mul ℝ ℝ).lpPairing μ (conjExponent p) p :
          Lp ℝ (conjExponent p) μ → StrongDual ℝ (Lp ℝ p μ)) :=
    lpDualityMap_isometry
  constructor
  · exact hκ.injective
  · intro F
    -- The remaining work is exactly the construction of the representing density.
    exact exists_lpPairing_preimage F

end Duality
