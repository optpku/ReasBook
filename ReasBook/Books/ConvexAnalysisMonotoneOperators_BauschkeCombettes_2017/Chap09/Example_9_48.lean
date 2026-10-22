/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_32
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Example_8_26
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Remark_9_47

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped BigOperators

namespace ERealFunction

/-- The scalar generator whose coordinate perspective sum yields the finite-dimensional
Kullback-Leibler divergence. -/
noncomputable def kullbackLeiblerGenerator : ℝ → EReal :=
  fun t ↦ if 0 < t then ((t * Real.log t : ℝ) : EReal) else ⊤

/-- The Kullback-Leibler divergence on the canonical `Fin N → ℝ` model of `ℝ^N × ℝ^N`, expressed
as the coordinate perspective sum attached to `kullbackLeiblerGenerator`. -/
noncomputable def kullbackLeiblerDivergence (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  coordinatePerspectiveSum (Fin N) kullbackLeiblerGenerator

-- Proof sketch: unfold `kullbackLeiblerDivergence`; it is defined to be the coordinate perspective
-- sum associated with `kullbackLeiblerGenerator`.
/-- Evaluating `kullbackLeiblerDivergence` amounts to evaluating the corresponding coordinate
perspective sum. -/
@[simp] theorem kullbackLeiblerDivergence_apply (N : ℕ) (x y : Fin N → ℝ) :
    kullbackLeiblerDivergence N (x, y) =
      coordinatePerspectiveSum (Fin N) kullbackLeiblerGenerator (x, y) := by
  -- This is just the defining equation of `kullbackLeiblerDivergence`.
  rfl

/-- The positive coordinate indices of a vector in `Fin N → ℝ`. -/
noncomputable def positiveIndices {N : ℕ} (x : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ 0 < x i

/-- The negative coordinate indices of a vector in `Fin N → ℝ`. -/
noncomputable def negativeIndices {N : ℕ} (y : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ y i < 0

/-- The coordinates that obstruct finiteness in the lower semicontinuous extension of the
finite-dimensional relative entropy. -/
noncomputable def relativeEntropyExceptionalIndices {N : ℕ} (x y : Fin N → ℝ) : Finset (Fin N) :=
  Finset.univ.filter fun i ↦ (x i ≠ 0 ∧ y i = 0) ∨ (x i < 0 ∧ 0 < y i)

/-- The explicit extended-real-valued formula of Example 9.48 for the lower semicontinuous hull of
the finite-dimensional relative entropy. -/
noncomputable def relativeEntropyLowerSemicontinuousHull (N : ℕ) :
    ((Fin N → ℝ) × (Fin N → ℝ)) → EReal :=
  fun p ↦
    let x := p.1
    let y := p.2
    if negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅ then
      ∑ i ∈ positiveIndices x ∩ positiveIndices y,
        (((x i) * Real.log (x i / y i) : ℝ) : EReal)
    else
      ⊤

-- Proof sketch: unfold `relativeEntropyLowerSemicontinuousHull`; the statement is exactly the
-- defining `if`-then-else expression specialized to the pair `(x, y)`.
/-- Evaluating `relativeEntropyLowerSemicontinuousHull` at `(x, y)` gives the explicit coordinate
formula from Example 9.48. -/
@[simp] theorem relativeEntropyLowerSemicontinuousHull_apply (N : ℕ) (x y : Fin N → ℝ) :
    relativeEntropyLowerSemicontinuousHull N (x, y) =
      if negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅ then
        ∑ i ∈ positiveIndices x ∩ positiveIndices y,
          (((x i) * Real.log (x i / y i) : ℝ) : EReal)
      else
        ⊤ := by
  -- This is just the defining equation of `relativeEntropyLowerSemicontinuousHull`.
  rfl

/-- Helper for Example 9.48: a finite `EReal` sum avoids `-∞` when each summand does. -/
private lemma finset_sum_ne_bot_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊥ := by
  classical
  -- Induct over the finite set and use the two-term characterization of `EReal` sums avoiding
  -- `⊥`.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    rw [Finset.sum_insert his, EReal.add_ne_bot_iff]
    constructor
    · exact hbot i (Finset.mem_insert_self i s)
    · exact ih (fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj))

/-- Helper for Example 9.48: under a coordinatewise non-`⊥` hypothesis, a finite `EReal` sum is
finite-above exactly when each summand is. -/
private lemma finset_sum_ne_top_iff_of_forall_ne_bot_local {ι : Type*} {s : Finset ι}
    {a : ι → EReal} (hbot : ∀ i ∈ s, a i ≠ ⊥) :
    s.sum a ≠ ⊤ ↔ ∀ i ∈ s, a i ≠ ⊤ := by
  classical
  -- Induct over the finite set and reduce to the two-term `EReal` criterion.
  revert hbot
  refine Finset.induction_on s ?_ ?_
  · intro hbot
    simp
  · intro i s his ih hbot
    have hbot_i : a i ≠ ⊥ := hbot i (Finset.mem_insert_self i s)
    have hbot_s : ∀ j ∈ s, a j ≠ ⊥ := fun j hj ↦ hbot j (Finset.mem_insert_of_mem hj)
    have hsum_s_ne_bot : s.sum a ≠ ⊥ := finset_sum_ne_bot_of_forall_ne_bot_local hbot_s
    rw [Finset.sum_insert his, EReal.add_ne_top_iff_ne_top₂ hbot_i hsum_s_ne_bot, ih hbot_s]
    constructor
    · intro h j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact h.1
      · exact h.2 j hj'
    · intro h
      constructor
      · exact h i (Finset.mem_insert_self i s)
      · intro j hj
        exact h j (Finset.mem_insert_of_mem hj)

/-- Helper for Example 9.48: a positive finite weight times a Kullback-Leibler scalar summand
still avoids `-∞`. -/
private theorem scaled_kullbackLeiblerGenerator_ne_bot {y t : ℝ} (hy : 0 < y) :
    (y : EReal) * kullbackLeiblerGenerator t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch, the value is a real cast.
    rw [kullbackLeiblerGenerator, if_pos ht, EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · -- On the nonpositive branch, the weighted value is `⊤`.
    rw [kullbackLeiblerGenerator, if_neg ht, EReal.coe_mul_top_of_pos hy]
    simp

/-- Helper for Example 9.48: the closed scalar entropy generator used in the lower semicontinuous
extension has value `t log t` on `t > 0`, value `0` at `t = 0`, and value `+∞` on `t < 0`. -/
noncomputable def closed_relative_entropy_generator_ereal : ℝ → EReal :=
  fun t ↦ if 0 < t then ((t * Real.log t : ℝ) : EReal) else if t = 0 then 0 else ⊤

/-- Helper for Example 9.48: the closed scalar entropy generator never takes the value `-∞`. -/
private theorem closed_relative_entropy_generator_ereal_ne_bot (t : ℝ) :
    closed_relative_entropy_generator_ereal t ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch the value is represented by a real number.
    simpa [closed_relative_entropy_generator_ereal, ht] using
      (EReal.coe_ne_bot (t * Real.log t))
  · by_cases hzero : t = 0
    · -- At the origin the value is exactly `0`.
      simp [closed_relative_entropy_generator_ereal, hzero]
    · -- On the negative half-line the value is `⊤`.
      simp [closed_relative_entropy_generator_ereal, ht, hzero]

/-- Helper for Example 9.48: the subtype-valued closed scalar entropy generator. -/
noncomputable def closed_relative_entropy_generator : ℝ → Set.Ioi (⊥ : EReal) :=
  fun t ↦
    ⟨closed_relative_entropy_generator_ereal t,
      lt_of_le_of_ne bot_le (closed_relative_entropy_generator_ereal_ne_bot t).symm⟩

/-- Helper for Example 9.48: coercing the closed scalar entropy generator to `EReal` recovers its
piecewise formula. -/
@[simp] theorem closed_relative_entropy_generator_coe (t : ℝ) :
    (closed_relative_entropy_generator t : EReal) = closed_relative_entropy_generator_ereal t := by
  rfl

/-- Helper for Example 9.48: on the positive half-line, the closed scalar entropy generator agrees
with `t ↦ t log t`. -/
@[simp] theorem closed_relative_entropy_generator_apply_of_pos {t : ℝ} (ht : 0 < t) :
    (closed_relative_entropy_generator t : EReal) = ((t * Real.log t : ℝ) : EReal) := by
  -- The positive branch of the defining `if` is active.
  simp [closed_relative_entropy_generator, closed_relative_entropy_generator_ereal, ht]

/-- Helper for Example 9.48: at the origin, the closed scalar entropy generator is `0`. -/
@[simp] theorem closed_relative_entropy_generator_apply_zero :
    (closed_relative_entropy_generator 0 : EReal) = 0 := by
  -- The zero branch of the defining `if` is active.
  simp [closed_relative_entropy_generator, closed_relative_entropy_generator_ereal]

/-- Helper for Example 9.48: on the negative half-line, the closed scalar entropy generator is
`+∞`. -/
@[simp] theorem closed_relative_entropy_generator_apply_of_neg {t : ℝ} (ht : t < 0) :
    (closed_relative_entropy_generator t : EReal) = ⊤ := by
  have hnot_pos : ¬ 0 < t := not_lt.mpr ht.le
  have hnot_zero : t ≠ 0 := ne_of_lt ht
  -- Away from the positive and zero branches, the definition returns `⊤`.
  simp [closed_relative_entropy_generator, closed_relative_entropy_generator_ereal, hnot_pos,
    hnot_zero]

/-- Helper for Example 9.48: on the nonnegative half-line, the closed scalar entropy generator is
the real function `t ↦ t log t`. -/
@[simp] theorem closed_relative_entropy_generator_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    (closed_relative_entropy_generator t : EReal) = ((t * Real.log t : ℝ) : EReal) := by
  rcases lt_or_eq_of_le ht with ht_pos | rfl
  · -- Positive arguments use the logarithmic branch directly.
    exact closed_relative_entropy_generator_apply_of_pos ht_pos
  · -- At the origin the logarithmic expression is `0` in Lean.
    simp [closed_relative_entropy_generator, closed_relative_entropy_generator_ereal]

/-- Helper for Example 9.48: real-height epigraph membership for the closed scalar entropy
generator is exactly nonnegativity together with the logarithmic height bound. -/
private lemma mem_epigraph_closed_relative_entropy_generator_iff {t r : ℝ} :
    (t, r) ∈ epigraph (fun s : ℝ ↦ (closed_relative_entropy_generator s : EReal)) ↔
      0 ≤ t ∧ t * Real.log t ≤ r := by
  constructor
  · intro h
    rw [mem_epigraph_iff] at h
    by_cases ht : 0 < t
    · constructor
      · exact ht.le
      · have h' : ((t * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
          simpa [closed_relative_entropy_generator_ereal, ht] using h
        exact_mod_cast h'
    · by_cases hzero : t = 0
      · constructor
        · simpa [hzero]
        · have h' : (0 : EReal) ≤ (r : EReal) := by
            simpa [closed_relative_entropy_generator_ereal, ht, hzero] using h
          simpa [hzero] using (show (0 : ℝ) ≤ r from by exact_mod_cast h')
      · have ht_neg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) hzero
        have : False := by
          have h' : (⊤ : EReal) ≤ (r : EReal) := by
            simpa [closed_relative_entropy_generator_ereal, ht, hzero] using h
          simpa using h'
        exact False.elim this
  · rintro ⟨ht, htr⟩
    rw [mem_epigraph_iff]
    by_cases ht_pos : 0 < t
    · have h' : ((t * Real.log t : ℝ) : EReal) ≤ (r : EReal) := by
        exact_mod_cast htr
      simpa [closed_relative_entropy_generator_ereal, ht_pos] using h'
    · have hzero : t = 0 := le_antisymm (le_of_not_gt ht_pos) ht
      have h' : (0 : EReal) ≤ (r : EReal) := by
        have htr' : (0 : ℝ) ≤ r := by simpa [hzero] using htr
        exact_mod_cast htr'
      simpa [closed_relative_entropy_generator_ereal, ht_pos, hzero] using h'

/-- Helper for Example 9.48: the effective domain of the closed scalar entropy generator is the
nonnegative half-line. -/
@[simp] private theorem effectiveDomain_closed_relative_entropy_generator :
    effectiveDomain closed_relative_entropy_generator = Set.Ici (0 : ℝ) := by
  ext t
  constructor
  · intro ht
    rw [mem_effectiveDomain_iff] at ht
    by_contra hneg
    have ht_neg : t < 0 := lt_of_not_ge hneg
    have hval : (closed_relative_entropy_generator t : EReal) = ⊤ :=
      closed_relative_entropy_generator_apply_of_neg ht_neg
    have hlt : (⊤ : EReal) < ⊤ := by
      rw [hval] at ht
      exact ht
    exact (lt_irrefl (⊤ : EReal)) hlt
  · intro ht
    rw [mem_effectiveDomain_iff]
    rw [closed_relative_entropy_generator_apply_of_nonneg ht]
    exact EReal.coe_lt_top _

/-- Helper for Example 9.48: the quotient by the norm eventually dominates `log ‖t‖`. -/
private theorem closed_relative_entropy_generator_div_norm_eventually_ge_log_norm :
    ∀ᶠ t in Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop,
      ((Real.log ‖t‖ : ℝ) : EReal) ≤
        (closed_relative_entropy_generator t : EReal) / ‖t‖ := by
  have htail :
      ∀ᶠ t in Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop, 1 ≤ ‖t‖ := by
    exact
      (Filter.tendsto_comap :
        Filter.Tendsto (fun t : ℝ ↦ ‖t‖)
          (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) Filter.atTop).eventually_ge_atTop 1
  filter_upwards [htail] with t ht
  by_cases ht_neg : t < 0
  · -- On the negative half-line the numerator is already `⊤`.
    have hnorm_pos : 0 < ((‖t‖ : ℝ) : EReal) := by
      exact_mod_cast norm_pos_iff.mpr (ne_of_lt ht_neg)
    rw [closed_relative_entropy_generator_apply_of_neg ht_neg,
      EReal.top_div_of_pos_ne_top hnorm_pos (EReal.coe_ne_top _)]
    exact le_top
  · have ht_nonneg : 0 ≤ t := le_of_not_gt ht_neg
    have hnorm_eq : ‖t‖ = t := abs_of_nonneg ht_nonneg
    have ht_one : 1 ≤ t := by simpa [hnorm_eq] using ht
    have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht_one
    rw [hnorm_eq, closed_relative_entropy_generator_apply_of_pos ht_pos, ← EReal.coe_div]
    have hquot : (t * Real.log t) / t = Real.log t := by
      field_simp [ht_pos.ne']
    simpa [hnorm_eq, hquot]

/-- Helper for Example 9.48: the explicit branch formula is a pointwise minorant of the original
Kullback-Leibler divergence. -/
private theorem relativeEntropyLowerSemicontinuousHull_le_kullbackLeiblerDivergence (N : ℕ) :
    relativeEntropyLowerSemicontinuousHull N ≤ kullbackLeiblerDivergence N := by
  intro p
  rcases p with ⟨x, y⟩
  by_cases hy : ∀ i, 0 < y i
  · by_cases hx : ∀ i, 0 < x i
    · have hbranch :
          negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅ := by
        -- In the strictly positive regime, neither the negative-index set nor the exceptional set
        -- contributes any coordinates.
        ext i
        simp [negativeIndices, relativeEntropyExceptionalIndices, hy i, (hx i).ne', (hy i).ne',
          not_lt.mpr (hy i).le, not_lt.mpr (le_of_lt (hx i))]
      have hpositive_univ : positiveIndices x ∩ positiveIndices y = Finset.univ := by
        -- Every coordinate belongs to both positive-index sets in this branch.
        ext i
        simp [positiveIndices, hx i, hy i]
      rw [relativeEntropyLowerSemicontinuousHull_apply, if_pos hbranch]
      rw [kullbackLeiblerDivergence_apply,
        coordinatePerspectiveSum_apply_of_pos (Fin N) kullbackLeiblerGenerator x y hy]
      rw [hpositive_univ]
      have hsum_eq :
          (∑ i, (((x i) * Real.log (x i / y i) : ℝ) : EReal)) =
            ∑ i, (y i : EReal) * kullbackLeiblerGenerator (x i / y i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hdiv_pos : 0 < x i / y i := div_pos (hx i) (hy i)
        rw [kullbackLeiblerGenerator, if_pos hdiv_pos, EReal.coe_mul]
        have hcoord :
            y i * ((x i / y i) * Real.log (x i / y i)) =
              x i * Real.log (x i / y i) := by
          -- Clearing the positive denominator reduces the coordinate identity to a ring
          -- normalization.
          field_simp [(hy i).ne']
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcoord.symm
      simpa using hsum_eq.le
    · have hx_nonpos : ∃ i, x i ≤ 0 := by
        classical
        -- Failing coordinatewise positivity means one coordinate is nonpositive.
        by_contra hx_nonpos
        apply hx
        intro i
        exact lt_of_not_ge (fun hxi_nonpos ↦ hx_nonpos ⟨i, hxi_nonpos⟩)
      rcases hx_nonpos with ⟨i, hxi_nonpos⟩
      have hsum_top :
          (∑ j, (y j : EReal) * kullbackLeiblerGenerator (x j / y j)) = ⊤ := by
        have hdiv_nonpos : x i / y i ≤ 0 := by
          exact div_nonpos_of_nonpos_of_nonneg hxi_nonpos (hy i).le
        have hterm_top :
            (y i : EReal) * kullbackLeiblerGenerator (x i / y i) = ⊤ := by
          -- A nonpositive ratio lands in the `+∞` branch of the open generator.
          rw [kullbackLeiblerGenerator, if_neg (not_lt_of_ge hdiv_nonpos)]
          exact EReal.coe_mul_top_of_pos (hy i)
        -- If the whole finite sum were finite, then every coordinate term would be finite.
        by_contra hsum_ne_top
        have hcoord_ne_top :
            ∀ j ∈ (Finset.univ : Finset (Fin N)),
              (y j : EReal) * kullbackLeiblerGenerator (x j / y j) ≠ ⊤ := by
          exact
            (finset_sum_ne_top_iff_of_forall_ne_bot_local
              (s := (Finset.univ : Finset (Fin N)))
              (a := fun j ↦ (y j : EReal) * kullbackLeiblerGenerator (x j / y j))
              (hbot := fun j _ ↦ scaled_kullbackLeiblerGenerator_ne_bot (hy j))).1 hsum_ne_top
        exact (hcoord_ne_top i (by simp)) hterm_top
      have hk_top : kullbackLeiblerDivergence N (x, y) = ⊤ := by
        rw [kullbackLeiblerDivergence_apply,
          coordinatePerspectiveSum_apply_of_pos (Fin N) kullbackLeiblerGenerator x y hy,
          hsum_top]
      -- Once the original divergence is already `+∞`, the minorant inequality is automatic.
      rw [hk_top]
      exact le_top
  · have hk_top : kullbackLeiblerDivergence N (x, y) = ⊤ := by
      -- A nonpositive coordinate of `y` immediately forces the open-perspective formula to `+∞`.
      simp [kullbackLeiblerDivergence, coordinatePerspectiveSum, hy]
    rw [hk_top]
    exact le_top

/-- Helper for Example 9.48: the closed scalar entropy generator belongs to `Γ₀(ℝ)`. -/
theorem closed_relative_entropy_generator_mem_gammaZero :
    closed_relative_entropy_generator ∈ Γ₀(ℝ) := by
  -- The real-height epigraph is cut out by two closed inequalities, so lower semicontinuity comes
  -- from the closed-epigraph criterion. Convexity then reduces to the usual Jensen inequality for
  -- `t ↦ t log t` on `[0, ∞)`.
  refine ⟨?_, ?_⟩
  · have hepigraph :
        epigraph (fun s : ℝ ↦ (closed_relative_entropy_generator s : EReal)) =
          {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 * Real.log p.1 ≤ p.2} := by
        ext p
        rcases p with ⟨t, r⟩
        exact mem_epigraph_closed_relative_entropy_generator_iff
    have hnonneg_closed : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} :=
      isClosed_le continuous_const continuous_fst
    have hineq_closed : IsClosed {p : ℝ × ℝ | p.1 * Real.log p.1 ≤ p.2} :=
      isClosed_le (Real.continuous_mul_log.comp continuous_fst) continuous_snd
    have hclosed_epi :
        IsClosed (epigraph (fun s : ℝ ↦ (closed_relative_entropy_generator s : EReal))) := by
      rw [hepigraph]
      exact hnonneg_closed.inter hineq_closed
    exact
      (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph
        (f := fun s : ℝ ↦ (closed_relative_entropy_generator s : EReal))).2
          hclosed_epi
  · refine ⟨?_, subset_rfl, ?_⟩
    · rw [effectiveDomain_closed_relative_entropy_generator]
      exact ⟨0, by simp⟩
    intro x hx y hy α hα0 hα1
    rw [effectiveDomain_closed_relative_entropy_generator] at hx hy
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hβ0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
    have hcombo0 : 0 ≤ α * x + (1 - α) * y :=
      add_nonneg (mul_nonneg hα0.le hx0) (mul_nonneg hβ0 hy0)
    have hconv :
        (α * x + (1 - α) * y) * Real.log (α * x + (1 - α) * y) ≤
          α * (x * Real.log x) + (1 - α) * (y * Real.log y) :=
      Real.convexOn_mul_log.2 hx0 hy0 hα0.le hβ0 (by ring)
    have hmain :
        (closed_relative_entropy_generator (α * x + (1 - α) * y) : EReal) ≤
          (α : EReal) * (closed_relative_entropy_generator x : EReal) +
            (1 - α : EReal) * (closed_relative_entropy_generator y : EReal) := by
      rw [closed_relative_entropy_generator_apply_of_nonneg hcombo0,
        closed_relative_entropy_generator_apply_of_nonneg hx0,
        closed_relative_entropy_generator_apply_of_nonneg hy0]
      have hleft :
          (((α * x + (1 - α) * y) * Real.log (α * x + (1 - α) * y) : ℝ) : EReal) ≤
            ((α * (x * Real.log x) + (1 - α) * (y * Real.log y) : ℝ) : EReal) := by
        exact_mod_cast hconv
      have hright :
          ((α * (x * Real.log x) + (1 - α) * (y * Real.log y) : ℝ) : EReal) =
            (α : EReal) * (((x * Real.log x : ℝ) : EReal)) +
              (1 - α : EReal) * (((y * Real.log y : ℝ) : EReal)) := by
        have hcoef :
            (((1 - α : ℝ) : EReal)) = (1 - α : EReal) := by
          norm_num
        calc
          ((α * (x * Real.log x) + (1 - α) * (y * Real.log y) : ℝ) : EReal)
              = (((α * (x * Real.log x) : ℝ) : EReal) +
                  (((1 - α) * (y * Real.log y) : ℝ) : EReal)) := by
                  rw [EReal.coe_add]
          _ = (α : EReal) * (((x * Real.log x : ℝ) : EReal)) +
                (((1 - α) * (y * Real.log y) : ℝ) : EReal) := by
                  rfl
          _ = (α : EReal) * (((x * Real.log x : ℝ) : EReal)) +
                (((1 - α : ℝ) : EReal) * (((y * Real.log y : ℝ) : EReal))) := by
                  rfl
          _ = (α : EReal) * (((x * Real.log x : ℝ) : EReal)) +
                (1 - α : EReal) * (((y * Real.log y : ℝ) : EReal)) := by
                  rw [hcoef]
      simpa [hright] using hleft
    change (closed_relative_entropy_generator (α * x + (1 - α) * y) : EReal) ≤
      (α : EReal) * (closed_relative_entropy_generator x : EReal) +
        (1 - α : EReal) * (closed_relative_entropy_generator y : EReal)
    exact hmain

/-- Helper for Example 9.48: the closed scalar entropy generator is supercoercive. -/
theorem closed_relative_entropy_generator_supercoercive :
    Filter.Tendsto (fun t : ℝ ↦ (closed_relative_entropy_generator t : EReal) / ‖t‖)
      (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) (nhds (⊤ : EReal)) := by
  -- Route correction: instead of forcing a global exact quotient formula on both signs, compare
  -- with `log ‖t‖` on the tail `1 ≤ ‖t‖` and use that `log ‖t‖ → +∞`.
  have hlog_top :
      Filter.Tendsto (fun t : ℝ ↦ ((Real.log ‖t‖ : ℝ) : EReal))
        (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) (nhds (⊤ : EReal)) := by
    rw [EReal.tendsto_nhds_top_iff_real]
    intro x
    have hlog_real :
        ∀ᶠ a : ℝ in Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop, x < Real.log ‖a‖ :=
      (Real.tendsto_log_atTop.comp <|
          (Filter.tendsto_comap :
            Filter.Tendsto (fun t : ℝ ↦ ‖t‖)
              (Filter.comap (fun t : ℝ ↦ ‖t‖) Filter.atTop) Filter.atTop)).eventually_gt_atTop x
    exact hlog_real.mono fun a ha ↦ by exact_mod_cast ha
  rw [EReal.tendsto_nhds_top_iff_real] at hlog_top ⊢
  intro x
  exact (hlog_top x).and closed_relative_entropy_generator_div_norm_eventually_ge_log_norm |>.mono
    (fun t ht ↦ lt_of_lt_of_le ht.1 ht.2)

/-- Helper for Example 9.48: a positive finite weight times a closed entropy scalar summand still
avoids `-∞`. -/
private theorem scaled_closed_relative_entropy_generator_ne_bot {y t : ℝ} (hy : 0 < y) :
    (y : EReal) * (closed_relative_entropy_generator t : EReal) ≠ ⊥ := by
  by_cases ht : 0 < t
  · -- On the positive branch the weighted value is a finite real cast.
    rw [closed_relative_entropy_generator_apply_of_pos ht, EReal.coe_mul]
    exact EReal.coe_ne_bot _
  · by_cases hzero : t = 0
    · -- At the origin the scalar value is `0`, so the product is `0`.
      rw [hzero, closed_relative_entropy_generator_apply_zero]
      simp
    · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) hzero
      -- On the negative branch the scalar value is `+∞`, and the positive weight preserves `+∞`.
      rw [closed_relative_entropy_generator_apply_of_neg htneg, EReal.coe_mul_top_of_pos hy]
      simp

/-- Helper for Example 9.48: the explicit branch formula is exactly the finite-dimensional
`coordinatePhiDivergence` attached to the closed scalar entropy generator. -/
theorem relativeEntropyLowerSemicontinuousHull_eq_coordinatePhiDivergence
    (N : ℕ) (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    (coordinatePhiDivergence N closed_relative_entropy_generator
      closed_relative_entropy_generator_mem_gammaZero.2.nonempty p : EReal) =
      relativeEntropyLowerSemicontinuousHull N p := by
  classical
  rcases p with ⟨x, y⟩
  -- Route correction: the reduced formula from Remark 9.47 is the right global skeleton. The only
  -- remaining work here is to rewrite its branch condition and positive-coordinate sum into the
  -- explicit Example 9.48 formula.
  rw [coordinatePhiDivergence_eq_reduced_formula_of_supercoercive N
    closed_relative_entropy_generator closed_relative_entropy_generator_mem_gammaZero
    closed_relative_entropy_generator_supercoercive x y]
  by_cases hbranch :
      negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅
  · -- When the exceptional union is empty, the reduced formula is finite and only the common
    -- positive coordinates contribute.
    have hneg_empty : coordinatePhiDivergenceNegativeIndices y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro i hi
      have hi' : i ∈ negativeIndices y := by
        simpa [coordinatePhiDivergenceNegativeIndices, negativeIndices] using hi
      have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
        Finset.mem_union.mpr (Or.inl hi')
      rw [hbranch] at this
      simpa using this
    have hzero_branch :
        ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0 := by
      intro i hi
      by_cases hxi : x i = 0
      · exact hxi
      · have hy0 : y i = 0 := by
          simpa [coordinatePhiDivergenceZeroIndices] using hi
        have hi' : i ∈ relativeEntropyExceptionalIndices x y := by
          simp [relativeEntropyExceptionalIndices, hy0, hxi]
        have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
          Finset.mem_union.mpr (Or.inr hi')
        rw [hbranch] at this
        simpa using this
    rw [if_pos ⟨hneg_empty, hzero_branch⟩, relativeEntropyLowerSemicontinuousHull_apply,
      if_pos hbranch]
    have hsum_terms :
        ∀ i ∈ coordinatePhiDivergencePositiveIndices y,
          (y i : EReal) * (closed_relative_entropy_generator (x i / y i) : EReal) =
            if 0 < x i then (((x i) * Real.log (x i / y i) : ℝ) : EReal) else 0 := by
      intro i hi
      have hyi : 0 < y i := by
        simpa [coordinatePhiDivergencePositiveIndices] using hi
      by_cases hxi : 0 < x i
      · have hdiv_pos : 0 < x i / y i := div_pos hxi hyi
        rw [closed_relative_entropy_generator_apply_of_pos hdiv_pos, EReal.coe_mul]
        have hcoord :
            y i * ((x i / y i) * Real.log (x i / y i)) =
              x i * Real.log (x i / y i) := by
          field_simp [(hyi.ne')]
        simp [hxi, congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcoord.symm]
      · have hx_nonneg : 0 ≤ x i := by
          by_contra hx_neg
          have hxi_neg : x i < 0 := lt_of_not_ge hx_neg
          have hi' : i ∈ relativeEntropyExceptionalIndices x y := by
            simp [relativeEntropyExceptionalIndices, hxi_neg, hyi, hxi_neg.ne']
          have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
            Finset.mem_union.mpr (Or.inr hi')
          rw [hbranch] at this
          simpa using this
        have hx_zero : x i = 0 := le_antisymm (le_of_not_gt hxi) hx_nonneg
        rw [hx_zero, zero_div, closed_relative_entropy_generator_apply_zero]
        simp [hxi]
    calc
      ∑ i ∈ coordinatePhiDivergencePositiveIndices y,
          (y i : EReal) * (closed_relative_entropy_generator (x i / y i) : EReal)
          = ∑ i ∈ coordinatePhiDivergencePositiveIndices y,
              if 0 < x i then (((x i) * Real.log (x i / y i) : ℝ) : EReal) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hsum_terms i hi
      _ = ∑ i ∈ (coordinatePhiDivergencePositiveIndices y).filter (fun i ↦ 0 < x i),
            (((x i) * Real.log (x i / y i) : ℝ) : EReal) := by
            rw [Finset.sum_filter]
      _ = ∑ i ∈ positiveIndices x ∩ positiveIndices y,
            (((x i) * Real.log (x i / y i) : ℝ) : EReal) := by
            congr 1
            ext i
            simp [coordinatePhiDivergencePositiveIndices, positiveIndices, and_comm,
              and_left_comm, and_assoc]
  · by_cases hreduced :
      coordinatePhiDivergenceNegativeIndices y = ∅ ∧
        ∀ i ∈ coordinatePhiDivergenceZeroIndices y, x i = 0
    · -- If the reduced branch is still active, the only possible obstruction is a positive
      -- coordinate with `x i < 0`, which forces one summand to be `+∞`.
      rw [if_pos hreduced, relativeEntropyLowerSemicontinuousHull_apply, if_neg hbranch]
      have hex :
          ∃ i, x i < 0 ∧ 0 < y i := by
        have hunion_nonempty :
            (negativeIndices y ∪ relativeEntropyExceptionalIndices x y).Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr hbranch
        rcases hunion_nonempty.exists_mem with ⟨i, hi⟩
        rcases Finset.mem_union.mp hi with hi_neg | hi_exc
        · have : i ∈ coordinatePhiDivergenceNegativeIndices y := by
            simpa [coordinatePhiDivergenceNegativeIndices, negativeIndices] using hi_neg
          simpa [hreduced.1] using this
        · have hi_cases :
              (x i ≠ 0 ∧ y i = 0) ∨ (x i < 0 ∧ 0 < y i) := by
            simpa [relativeEntropyExceptionalIndices] using hi_exc
          rcases hi_cases with hzero | hposneg
          · have hi_zero : i ∈ coordinatePhiDivergenceZeroIndices y := by
              simpa [coordinatePhiDivergenceZeroIndices, hzero.2]
          -- The zero-coordinate obstruction is excluded by the reduced branch hypothesis.
            exact False.elim (hzero.1 (hreduced.2 i hi_zero))
          · exact ⟨i, hposneg.1, hposneg.2⟩
      rcases hex with ⟨i, hxi_neg, hyi⟩
      have hi_pos : i ∈ coordinatePhiDivergencePositiveIndices y := by
        simpa [coordinatePhiDivergencePositiveIndices] using hyi
      have hterm_top :
          (y i : EReal) * (closed_relative_entropy_generator (x i / y i) : EReal) = ⊤ := by
        have hdiv_neg : x i / y i < 0 := by
          exact div_neg_of_neg_of_pos hxi_neg hyi
        rw [closed_relative_entropy_generator_apply_of_neg hdiv_neg, EReal.coe_mul_top_of_pos hyi]
      by_contra hsum_ne_top
      have hterm_ne_top :
          ∀ j ∈ coordinatePhiDivergencePositiveIndices y,
            (y j : EReal) * (closed_relative_entropy_generator (x j / y j) : EReal) ≠ ⊤ := by
        exact
          (finset_sum_ne_top_iff_of_forall_ne_bot_local
            (s := coordinatePhiDivergencePositiveIndices y)
            (a := fun j ↦ (y j : EReal) * (closed_relative_entropy_generator (x j / y j) : EReal))
            (hbot := fun j hj ↦ by
              have hyj : 0 < y j := by
                simpa [coordinatePhiDivergencePositiveIndices] using hj
              exact scaled_closed_relative_entropy_generator_ne_bot hyj)).1 hsum_ne_top
      exact (hterm_ne_top i hi_pos) hterm_top
    · -- Away from the reduced branch, Remark 9.47 already returns `+∞`, matching the explicit
      -- Example 9.48 formula on the nonempty exceptional union branch.
      simpa [relativeEntropyLowerSemicontinuousHull_apply, hbranch, hreduced]

/-- Helper for Example 9.48: the explicit lower semicontinuous hull never takes the value
`-∞`. -/
private theorem relativeEntropyLowerSemicontinuousHull_ne_bot (N : ℕ)
    (p : (Fin N → ℝ) × (Fin N → ℝ)) :
    relativeEntropyLowerSemicontinuousHull N p ≠ ⊥ := by
  rcases p with ⟨x, y⟩
  rw [relativeEntropyLowerSemicontinuousHull_apply]
  by_cases hbranch : negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅
  · rw [if_pos hbranch]
    exact
      finset_sum_ne_bot_of_forall_ne_bot_local
        (s := positiveIndices x ∩ positiveIndices y)
        (a := fun i ↦ (((x i) * Real.log (x i / y i) : ℝ) : EReal))
        (hbot := fun i hi ↦ EReal.coe_ne_bot _)
  · simp [hbranch]

/-- Helper for Example 9.48: a finite upper bound on the explicit hull forces the exceptional
branch to be empty and exposes the coordinatewise sign constraints used in the regularization
argument. -/
private theorem relativeEntropyLowerSemicontinuousHull_finite_branch_conditions
    {N : ℕ} {x y : Fin N → ℝ} {ξ : ℝ}
    (hξ : relativeEntropyLowerSemicontinuousHull N (x, y) ≤ (ξ : EReal)) :
    negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅ ∧
      (∀ i, 0 ≤ y i) ∧
      (∀ i, y i = 0 → x i = 0) ∧
      (∀ i, 0 < y i → 0 ≤ x i) := by
  have hbranch : negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅ := by
    rw [relativeEntropyLowerSemicontinuousHull_apply] at hξ
    by_cases hcase : negativeIndices y ∪ relativeEntropyExceptionalIndices x y = ∅
    · exact hcase
    · simp [hcase] at hξ
  refine ⟨hbranch, ?_, ?_, ?_⟩
  · intro i
    by_contra hy_neg
    have hy_neg' : y i < 0 := lt_of_not_ge hy_neg
    have hi : i ∈ negativeIndices y := by
      simp [negativeIndices, hy_neg']
    have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
      Finset.mem_union.mpr (Or.inl hi)
    rw [hbranch] at this
    simpa using this
  · intro i hy0
    by_contra hx0
    have hi : i ∈ relativeEntropyExceptionalIndices x y := by
      simp [relativeEntropyExceptionalIndices, hy0, hx0]
    have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
      Finset.mem_union.mpr (Or.inr hi)
    rw [hbranch] at this
    simpa using this
  · intro i hy_pos
    by_contra hx_nonneg
    have hx_neg : x i < 0 := lt_of_not_ge hx_nonneg
    have hi : i ∈ relativeEntropyExceptionalIndices x y := by
      simp [relativeEntropyExceptionalIndices, hx_neg, hy_pos, hx_neg.ne']
    have : i ∈ negativeIndices y ∪ relativeEntropyExceptionalIndices x y :=
      Finset.mem_union.mpr (Or.inr hi)
    rw [hbranch] at this
    simpa using this

/-- Helper for Example 9.48: a finite sum of real casts in `EReal` is the cast of the
corresponding real sum. -/
private theorem finset_sum_coe_real_local {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, ((f i : ℝ) : EReal)) = ((∑ i ∈ s, f i : ℝ) : EReal) := by
  classical
  -- Induct over the finite set and combine the distinguished real cast with the induction
  -- hypothesis using `EReal.coe_add`.
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ih, EReal.coe_add]

/-- Helper for Example 9.48: when the denominator stays positive, the regularized scalar entropy
term converges to the finite branch value. -/
private theorem regularized_coordinate_term_tendsto_of_pos_denominator
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Filter.Tendsto (fun eps : ℝ ↦ (a + eps ^ 2) * Real.log ((a + eps ^ 2) / (b + eps)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * Real.log (a / b))) := by
  let u : ℝ → ℝ := fun eps ↦ (a + eps ^ 2) / (b + eps)
  let v : ℝ → ℝ := fun eps ↦ b + eps
  -- The quotient `u` tends to `a / b`, while `v` tends to `b`; continuity of `x ↦ x log x`
  -- packages the positive-denominator branch into a product limit.
  have hu_cont : ContinuousAt u 0 := by
    dsimp [u]
    exact
      ((continuous_const.add (continuous_id.pow 2)).continuousAt.div
        (continuous_const.add continuous_id).continuousAt (by simpa using hb.ne'))
  have hv_tendsto : Filter.Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (nhds b) := by
    simpa [v] using
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ))
        ((continuous_const.add continuous_id).tendsto 0))
  have hu_mul_log_tendsto :
      Filter.Tendsto (fun eps : ℝ ↦ u eps * Real.log (u eps))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((a / b) * Real.log (a / b))) := by
    simpa [Function.comp, u] using
      (tendsto_nhdsWithin_of_tendsto_nhds
        ((Real.continuous_mul_log.continuousAt.comp hu_cont).tendsto))
  have hprod :
      Filter.Tendsto (fun eps : ℝ ↦ v eps * (u eps * Real.log (u eps)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (b * ((a / b) * Real.log (a / b)))) := by
    exact hv_tendsto.mul hu_mul_log_tendsto
  have hrew :
      (fun eps : ℝ ↦ (a + eps ^ 2) * Real.log ((a + eps ^ 2) / (b + eps))) =ᶠ[
        nhdsWithin 0 (Set.Ioi 0)] fun eps ↦ v eps * (u eps * Real.log (u eps)) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have heps_pos : 0 < eps := heps
    have hden : b + eps ≠ 0 := by
      linarith
    dsimp [u, v]
    field_simp [hden]
  have hmain :
      Filter.Tendsto (fun eps : ℝ ↦ (a + eps ^ 2) * Real.log ((a + eps ^ 2) / (b + eps)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (b * ((a / b) * Real.log (a / b)))) :=
    Filter.Tendsto.congr' hrew.symm hprod
  have htarget : b * ((a / b) * Real.log (a / b)) = a * Real.log (a / b) := by
    field_simp [hb.ne']
  simpa [htarget] using hmain

/-- Helper for Example 9.48: the zero-coordinate regularization contributes vanishing entropy. -/
private theorem regularized_zero_coordinate_tendsto :
    Filter.Tendsto (fun eps : ℝ ↦ (eps ^ 2) * Real.log eps)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Rewrite as `eps * (eps log eps)` so that continuity of `x ↦ x log x` at the origin closes
  -- the limit.
  have hcont :
      Continuous (fun eps : ℝ ↦ eps * (eps * Real.log eps)) := by
    simpa [mul_assoc] using continuous_id.mul Real.continuous_mul_log
  have hmain :
      Filter.Tendsto (fun eps : ℝ ↦ eps * (eps * Real.log eps))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 * (0 * Real.log 0))) := by
    exact tendsto_nhdsWithin_of_tendsto_nhds (hcont.tendsto 0)
  have hrew :
      (fun eps : ℝ ↦ (eps ^ 2) * Real.log eps) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun eps ↦ eps * (eps * Real.log eps) := by
    exact Filter.Eventually.of_forall fun eps ↦ by
      ring
  simpa using Filter.Tendsto.congr' hrew.symm hmain

/-- Helper for Example 9.48: the regularized finite-dimensional Kullback-Leibler sums converge to
the finite branch of the explicit lower semicontinuous hull. -/
private theorem regularized_kullbackLeibler_sum_tendsto
    {N : ℕ} {x y : Fin N → ℝ}
    (hy_nonneg : ∀ i, 0 ≤ y i)
    (hxy_zero : ∀ i, y i = 0 → x i = 0)
    (hx_nonneg : ∀ i, 0 < y i → 0 ≤ x i) :
    Filter.Tendsto (fun eps : ℝ ↦ ∑ i, (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∑ i ∈ positiveIndices x ∩ positiveIndices y, x i * Real.log (x i / y i))) := by
  -- Route correction: split the coordinate limit into the `y_i > 0` branch and the `y_i = 0`
  -- branch, then sum those limits over `Finset.univ`.
  have hcoord :
      ∀ i,
        Filter.Tendsto (fun eps : ℝ ↦ (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (if 0 < y i then x i * Real.log (x i / y i) else 0)) := by
    intro i
    by_cases hyi : 0 < y i
    · -- Positive coordinates stay in the finite branch and are handled by continuity.
      simpa [hyi] using
        regularized_coordinate_term_tendsto_of_pos_denominator (hx_nonneg i hyi) hyi
    · have hyi_zero : y i = 0 := le_antisymm (le_of_not_gt hyi) (hy_nonneg i)
      have hxi_zero : x i = 0 := hxy_zero i hyi_zero
      -- Zero coordinates reduce to the scalar model `eps^2 * log eps`.
      have hrew :
          (fun eps : ℝ ↦ (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps))) =ᶠ[
            nhdsWithin 0 (Set.Ioi 0)] fun eps ↦ (eps ^ 2) * Real.log eps := by
        filter_upwards [self_mem_nhdsWithin] with eps heps
        have heps_pos : 0 < eps := heps
        have hdiv : (0 + eps ^ 2) / (0 + eps) = eps := by
          field_simp [heps_pos.ne']
          ring
        rw [hxi_zero, hyi_zero, hdiv]
        ring
      have hzero :
          Filter.Tendsto
            (fun eps : ℝ ↦ (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        Filter.Tendsto.congr' hrew.symm regularized_zero_coordinate_tendsto
      simpa [hyi] using hzero
  have hsum_piecewise :
      Filter.Tendsto (fun eps : ℝ ↦
        ∑ i, (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i, if 0 < y i then x i * Real.log (x i / y i) else 0)) := by
    exact tendsto_finset_sum Finset.univ (fun i _ ↦ hcoord i)
  let term : Fin N → ℝ := fun i ↦ x i * Real.log (x i / y i)
  have htarget :
      Finset.sum Finset.univ (fun i ↦ if 0 < y i then term i else 0) =
        Finset.sum (positiveIndices x ∩ positiveIndices y) term := by
    calc
      Finset.sum Finset.univ (fun i ↦ if 0 < y i then term i else 0)
          = Finset.sum (positiveIndices y) term := by
              rw [positiveIndices, Finset.sum_filter]
      _ = Finset.sum (positiveIndices y) (fun i ↦ if 0 < x i then term i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hyi : 0 < y i := by
              simpa [positiveIndices] using hi
            by_cases hxi : 0 < x i
            · simp [hxi]
            · have hxi_zero : x i = 0 := by
                exact le_antisymm (le_of_not_gt hxi) (hx_nonneg i hyi)
              simp [term, hxi, hxi_zero]
      _ = Finset.sum ((positiveIndices y).filter (fun i ↦ 0 < x i)) term := by
            rw [Finset.sum_filter]
      _ = Finset.sum (positiveIndices x ∩ positiveIndices y) term := by
            have hfilter_eq :
                (positiveIndices y).filter (fun i ↦ 0 < x i) = positiveIndices x ∩ positiveIndices y := by
              ext i
              simp [positiveIndices, and_comm, and_left_comm, and_assoc]
            rw [hfilter_eq]
  rw [htarget] at hsum_piecewise
  simpa [term] using hsum_piecewise

/-- Helper for Example 9.48: any finite-height epigraph point of the explicit lower semicontinuous
formula lies in the closure of the epigraph of the original Kullback-Leibler divergence. -/
theorem mem_closure_epigraph_kullbackLeiblerDivergence_of_mem_relativeEntropyHull_epigraph
    {N : ℕ} {p : (Fin N → ℝ) × (Fin N → ℝ)} {ξ : ℝ}
    (hξ : relativeEntropyLowerSemicontinuousHull N p ≤ (ξ : EReal)) :
    (p, ξ) ∈ closure (epigraph (kullbackLeiblerDivergence N)) := by
  rcases p with ⟨x, y⟩
  rcases
    relativeEntropyLowerSemicontinuousHull_finite_branch_conditions
      (N := N) (x := x) (y := y) (ξ := ξ) hξ with
    ⟨hbranch, hy_nonneg, hxy_zero, hx_nonneg⟩
  let sigma : ℝ := ∑ i ∈ positiveIndices x ∩ positiveIndices y, x i * Real.log (x i / y i)
  have hsigma_le : sigma ≤ ξ := by
    -- On the finite branch, the hull value is the real cast of the explicit sum `sigma`.
    have hsigma_eq :
        (∑ i ∈ positiveIndices x ∩ positiveIndices y,
          (((x i) * Real.log (x i / y i) : ℝ) : EReal)) = ((sigma : ℝ) : EReal) := by
      simpa [sigma] using
        (finset_sum_coe_real_local
          (s := positiveIndices x ∩ positiveIndices y)
          (f := fun i ↦ x i * Real.log (x i / y i)))
    rw [relativeEntropyLowerSemicontinuousHull_apply, if_pos hbranch, hsigma_eq] at hξ
    exact EReal.coe_le_coe_iff.mp hξ
  have hx_nonneg_all : ∀ i, 0 ≤ x i := by
    -- Every coordinate of `x` is nonnegative: either `y_i > 0` and the finite-branch condition
    -- gives it directly, or `y_i = 0` and then `x_i = 0`.
    intro i
    by_cases hyi : 0 < y i
    · exact hx_nonneg i hyi
    · have hyi_zero : y i = 0 := le_antisymm (le_of_not_gt hyi) (hy_nonneg i)
      simpa [hxy_zero i hyi_zero] using (show (0 : ℝ) ≤ 0 by norm_num)
  let xeps : ℝ → Fin N → ℝ := fun eps i ↦ x i + eps ^ 2
  let yeps : ℝ → Fin N → ℝ := fun eps i ↦ y i + eps
  let KLeps : ℝ → ℝ := fun eps ↦
    ∑ i, (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps))
  let zeta : ℝ → ℝ := fun eps ↦ KLeps eps + (ξ - sigma)
  have hKLeps_tendsto :
      Filter.Tendsto KLeps (nhdsWithin 0 (Set.Ioi 0)) (nhds sigma) := by
    -- The regularized coordinate sum converges to the explicit finite branch.
    simpa [KLeps] using
      regularized_kullbackLeibler_sum_tendsto
        (x := x) (y := y) hy_nonneg hxy_zero hx_nonneg
  have hzeta_tendsto : Filter.Tendsto zeta (nhdsWithin 0 (Set.Ioi 0)) (nhds ξ) := by
    -- The extra slack `ξ - sigma` shifts the limiting height from the minimal value `sigma` to
    -- the requested epigraph height `ξ`.
    have hconst :
        Filter.Tendsto (fun _ : ℝ ↦ ξ - sigma) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ξ - sigma)) := by
      exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_const_nhds
    simpa [zeta, sigma, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hKLeps_tendsto.add hconst
  have hxeps_tendsto : Filter.Tendsto xeps (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
    -- The first variable is regularized by the quadratic perturbation `eps^2`.
    refine tendsto_pi_nhds.mpr ?_
    intro i
    dsimp [xeps]
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ))
        ((continuous_const.add (continuous_id.pow 2)).tendsto 0))
  have hyeps_tendsto : Filter.Tendsto yeps (nhdsWithin 0 (Set.Ioi 0)) (nhds y) := by
    -- The second variable is regularized by the linear perturbation `eps`.
    refine tendsto_pi_nhds.mpr ?_
    intro i
    dsimp [yeps]
    simpa using
      (tendsto_nhdsWithin_of_tendsto_nhds (s := Set.Ioi (0 : ℝ))
        ((continuous_const.add continuous_id).tendsto 0))
  have hxyeps_tendsto :
      Filter.Tendsto (fun eps : ℝ ↦ (xeps eps, yeps eps))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (x, y)) := by
    exact hxeps_tendsto.prodMk_nhds hyeps_tendsto
  have hpath_tendsto :
      Filter.Tendsto (fun eps : ℝ ↦ ((xeps eps, yeps eps), zeta eps))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((x, y), ξ)) := by
    exact hxyeps_tendsto.prodMk_nhds hzeta_tendsto
  have hpath_mem :
      ∀ᶠ eps : ℝ in nhdsWithin 0 (Set.Ioi 0),
        ((xeps eps, yeps eps), zeta eps) ∈ epigraph (kullbackLeiblerDivergence N) := by
    filter_upwards [self_mem_nhdsWithin] with eps heps
    have heps_pos : 0 < eps := heps
    have hyeps_pos : ∀ i, 0 < yeps eps i := by
      intro i
      dsimp [yeps]
      linarith [hy_nonneg i]
    have hxeps_pos : ∀ i, 0 < xeps eps i := by
      intro i
      dsimp [xeps]
      exact add_pos_of_nonneg_of_pos (hx_nonneg_all i) (sq_pos_of_pos heps_pos)
    have hKLeps_formula :
        kullbackLeiblerDivergence N (xeps eps, yeps eps) = ((KLeps eps : ℝ) : EReal) := by
      rw [kullbackLeiblerDivergence_apply,
        coordinatePerspectiveSum_apply_of_pos (Fin N) kullbackLeiblerGenerator
          (xeps eps) (yeps eps) hyeps_pos]
      calc
        ∑ i, (yeps eps i : EReal) * kullbackLeiblerGenerator (xeps eps i / yeps eps i)
            = ∑ i, (((x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)) : ℝ) : EReal) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                have hratio_pos : 0 < xeps eps i / yeps eps i := by
                  exact div_pos (hxeps_pos i) (hyeps_pos i)
                rw [kullbackLeiblerGenerator, if_pos hratio_pos, EReal.coe_mul]
                have hcoord :
                    (yeps eps i) * ((xeps eps i / yeps eps i) * Real.log (xeps eps i / yeps eps i)) =
                      (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps)) := by
                  have hden : y i + eps ≠ 0 := ne_of_gt (hyeps_pos i)
                  dsimp [xeps, yeps]
                  field_simp [hden]
                exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) hcoord
        _ = ((KLeps eps : ℝ) : EReal) := by
              simpa [KLeps] using
                (finset_sum_coe_real_local (s := (Finset.univ : Finset (Fin N)))
                  (f := fun i ↦ (x i + eps ^ 2) * Real.log ((x i + eps ^ 2) / (y i + eps))))
    have hzeta_ge : KLeps eps ≤ zeta eps := by
      dsimp [zeta]
      linarith [hsigma_le]
    rw [mem_epigraph_iff, hKLeps_formula]
    exact_mod_cast hzeta_ge
  exact mem_closure_of_tendsto hpath_tendsto hpath_mem

-- Proof sketch: compare the explicit branch formula with `kullbackLeiblerDivergence N` on the
-- strictly positive orthant by unfolding the coordinate perspective sum; then show that the
-- displayed extension is lower semicontinuous and is the greatest lower semicontinuous minorant of
-- `kullbackLeiblerDivergence N`, so it agrees with `lowerSemicontinuousEnvelope`.
/-- Example 9.48: the explicit formula obtained by allowing zero coordinates in the second variable
and summing only over the common positive coordinates is the lower semicontinuous hull of the
Kullback-Leibler divergence of Example 8.27. -/
theorem lowerSemicontinuousEnvelope_kullbackLeiblerDivergence_eq_relativeEntropyLowerSemicontinuousHull
    (N : ℕ) :
    lowerSemicontinuousEnvelope (kullbackLeiblerDivergence N) =
      relativeEntropyLowerSemicontinuousHull N := by
  -- The coordinate-divergence identification packages the explicit formula as a `Γ₀` function, so
  -- it is a lower semicontinuous minorant of the original divergence.
  have hcoord_mem_gammaZero :
      coordinatePhiDivergence N closed_relative_entropy_generator
        closed_relative_entropy_generator_mem_gammaZero.2.nonempty ∈
          Γ₀((Fin N → ℝ) × (Fin N → ℝ)) :=
    coordinatePhiDivergence_mem_gammaZero N closed_relative_entropy_generator
      closed_relative_entropy_generator_mem_gammaZero
  have hrewrite :
      (fun p ↦
        (coordinatePhiDivergence N closed_relative_entropy_generator
          closed_relative_entropy_generator_mem_gammaZero.2.nonempty p : EReal)) =
        relativeEntropyLowerSemicontinuousHull N := by
    funext p
    exact relativeEntropyLowerSemicontinuousHull_eq_coordinatePhiDivergence N p
  have hHull_lsc : LowerSemicontinuous (relativeEntropyLowerSemicontinuousHull N) := by
    rw [← hrewrite]
    exact hcoord_mem_gammaZero.1
  have hHull_minorant :
      relativeEntropyLowerSemicontinuousHull N ∈
        {g : ((Fin N → ℝ) × (Fin N → ℝ)) → EReal |
          LowerSemicontinuous g ∧ g ≤ kullbackLeiblerDivergence N} := by
    exact ⟨hHull_lsc, relativeEntropyLowerSemicontinuousHull_le_kullbackLeiblerDivergence N⟩
  have hHull_le_envelope :
      relativeEntropyLowerSemicontinuousHull N ≤
        lowerSemicontinuousEnvelope (kullbackLeiblerDivergence N) := by
    exact (lowerSemicontinuousHull_isGreatest (kullbackLeiblerDivergence N)).2 hHull_minorant
  have hclosure_eq :
      closure (epigraph (kullbackLeiblerDivergence N)) =
        epigraph (lowerSemicontinuousEnvelope (kullbackLeiblerDivergence N)) := by
    simpa using
      (epi_lowerSemicontinuousHull_eq_closure_epi (kullbackLeiblerDivergence N)).symm
  funext p
  apply le_antisymm
  · by_cases hp_top : relativeEntropyLowerSemicontinuousHull N p = ⊤
    · rw [hp_top]
      exact le_top
    · have hp_not_bot : relativeEntropyLowerSemicontinuousHull N p ≠ ⊥ :=
        relativeEntropyLowerSemicontinuousHull_ne_bot N p
      have hmem_closure :
          (p, (relativeEntropyLowerSemicontinuousHull N p).toReal) ∈
            closure (epigraph (kullbackLeiblerDivergence N)) := by
        apply mem_closure_epigraph_kullbackLeiblerDivergence_of_mem_relativeEntropyHull_epigraph
        exact EReal.le_coe_toReal hp_top
      have hmem_envelope :
          (p, (relativeEntropyLowerSemicontinuousHull N p).toReal) ∈
            epigraph (lowerSemicontinuousEnvelope (kullbackLeiblerDivergence N)) := by
        rw [← hclosure_eq]
        exact hmem_closure
      have henv_le_toReal :
          lowerSemicontinuousEnvelope (kullbackLeiblerDivergence N) p ≤
            (((relativeEntropyLowerSemicontinuousHull N p).toReal : ℝ) : EReal) := by
        simpa [epigraph] using hmem_envelope
      exact le_trans henv_le_toReal (EReal.coe_toReal_le hp_not_bot)
  · exact hHull_le_envelope p

end ERealFunction
