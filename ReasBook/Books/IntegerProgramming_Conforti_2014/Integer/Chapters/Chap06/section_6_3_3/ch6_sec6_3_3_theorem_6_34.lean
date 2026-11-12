/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.Real
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3.ch6_sec6_3_definition_6_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_theorem_6_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_3.ch6_sec6_3_3_lemma_6_33

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: `tool_search` exposed no deferred Lean semantic-search tool such as
-- `lean_leansearch` in this environment, so this file uses the existing Chapter 6 mixed-pair and
-- pure-integer minimality APIs by direct repository inspection.

noncomputable section

section Theorem634

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "NatAssignment" => Rq →₀ ℕ
local notation "IntAssignment" => Rq →₀ ℤ
local notation "ContAssignment" => Rq →₀ NNReal

/-- The right-hand limsup formula from (6.27), viewed as the lifting induced by a pure-integer
minimal valid function `π`. -/
def gomory_johnson_limsup_lifting (π : Rq → ℝ) : Rq → ℝ :=
  fun r ↦ Filter.limsup (fun ε : ℝ ↦ π (ε • r) / ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- Evaluating `gomory_johnson_limsup_lifting π` at `r` gives the right-hand limsup
`limsup_{ε → 0^+} π(ε r) / ε`. -/
@[simp]
theorem gomory_johnson_limsup_lifting_apply
    (π : Rq → ℝ) (r : Rq) :
    gomory_johnson_limsup_lifting π r =
      Filter.limsup (fun ε : ℝ ↦ π (ε • r) / ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
  rfl

/-- Helper for Theorem 6.34: a sublinear function dominates its value on any finitely supported
nonnegative weighted sum by the corresponding weighted cut sum. -/
lemma sublinear_le_continuous_finsupp_sum
    {ψ : Rq → ℝ} (hψ : ψ.Sublinear) (y : ContAssignment) :
    ψ (y.sum (fun r a ↦ (a : ℝ) • r)) ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  classical
  -- Induct on the finite support so the sublinear estimate is used one coefficient at a time.
  induction y using Finsupp.induction with
  | zero =>
      simp [Function.Sublinear.map_zero hψ]
  | @single_add r a y hr ha ih =>
      have hsum_vec :
          (Finsupp.single r a + y).sum (fun s b ↦ (b : ℝ) • s) =
            (a : ℝ) • r + y.sum (fun s b ↦ (b : ℝ) • s) := by
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro s b₁ b₂
          simp [NNReal.coe_add, add_smul]
      have hsum_cut :
          (Finsupp.single r a + y).sum (fun s b ↦ ψ s * (b : ℝ)) =
            ψ r * (a : ℝ) + y.sum (fun s b ↦ ψ s * (b : ℝ)) := by
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro s b₁ b₂
          simp [NNReal.coe_add, left_distrib]
      -- Split off the singleton contribution, then use homogeneity on that one coefficient.
      calc
        ψ ((Finsupp.single r a + y).sum (fun s b ↦ (b : ℝ) • s)) =
            ψ ((a : ℝ) • r + y.sum (fun s b ↦ (b : ℝ) • s)) := by
              rw [hsum_vec]
        _ ≤ ψ ((a : ℝ) • r) + ψ (y.sum (fun s b ↦ (b : ℝ) • s)) :=
          hψ.subadditive _ _
        _ = (a : ℝ) * ψ r + ψ (y.sum (fun s b ↦ (b : ℝ) • s)) := by
              rw [hψ.smul_nonneg r (a : ℝ) (by exact_mod_cast a.2)]
        _ ≤ (a : ℝ) * ψ r + y.sum (fun s b ↦ ψ s * (b : ℝ)) := by
              gcongr
        _ = (Finsupp.single r a + y).sum (fun s b ↦ ψ s * (b : ℝ)) := by
              rw [hsum_cut]
              ring

/-- Helper for Theorem 6.34: aggregating the continuous part of a mixed feasible point into one
pure-integer atom preserves feasibility in `G_f`. -/
lemma mixedIntegerAggregatedPureFeasible
    {f : Rq} {x : NatAssignment} {y : ContAssignment}
    (hxy : (x, y) ∈ mixed_integer_relaxation_set f) :
    nat_assignment_to_int_assignment x +
        Finsupp.single (y.sum (fun r a ↦ (a : ℝ) • r)) (1 : ℤ) ∈
      pure_integer_feasible_set f := by
  let rbar : Rq := y.sum (fun r a ↦ (a : ℝ) • r)
  rw [mem_pure_integer_feasible_set_iff]
  constructor
  · -- Only the aggregated atom changes the natural assignment, and it adds one nonnegative unit.
    intro r
    by_cases hr : r = rbar
    · subst hr
      have hx_nonneg : 0 ≤ (x rbar : ℤ) := by
        exact_mod_cast Nat.zero_le (x rbar)
      simp [rbar]
      linarith
    · simp [rbar, hr]
  · rw [mem_mixed_integer_relaxation_set_iff] at hxy
    rcases hxy with ⟨z, hz⟩
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨z, ?_⟩
    have hxsum :
        (nat_assignment_to_int_assignment x).sum (fun r n ↦ (n : ℝ) • r) =
          x.sum (fun r n ↦ (n : ℝ) • r) := by
      -- The integer-valued lift of the natural assignment keeps the same real weighted sum.
      simpa [nat_assignment_to_int_assignment] using
        (Finsupp.sum_mapRange_index
          (f := fun n : ℕ ↦ (n : ℤ))
          (hf := by simp)
          (g := x)
          (h := fun r (n : ℤ) ↦ (n : ℝ) • r)
          (h0 := fun r ↦ by simp))
    -- Rewrite the pure balance so it matches the original mixed balance exactly.
    calc
      pure_integer_balance f
          (nat_assignment_to_int_assignment x + Finsupp.single rbar (1 : ℤ)) =
          f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r) := by
            rw [pure_integer_balance, Finsupp.sum_add_index]
            · simp [hxsum, rbar, add_assoc]
            · simp
            · intro r n₁ n₂
              simp [Int.cast_add, add_smul]
      _ = fun i ↦ (z i : ℝ) := hz

/-- Helper for Theorem 6.34: if `π` is valid for `G_f`, `ψ` is sublinear, and `π ≤ ψ`, then the
pair `(π, ψ)` is valid for `M_f`. -/
lemma mixedIntegerValidPair_of_pureIntegerValid_sublinear_le
    {f : Rq} {π ψ : Rq → ℝ}
    (hπ : pure_integer_valid_function f π)
    (hψsub : ψ.Sublinear)
    (hle : π ≤ ψ) :
    IsValidGomoryJohnsonPair f π ψ := by
  refine
    { nonneg := hπ.nonneg
      one_le := ?_ }
  intro x y hxy
  let rbar : Rq := y.sum (fun r a ↦ (a : ℝ) • r)
  have hagg :
      nat_assignment_to_int_assignment x + Finsupp.single rbar (1 : ℤ) ∈
        pure_integer_feasible_set f :=
    mixedIntegerAggregatedPureFeasible hxy
  have hxsum :
      (nat_assignment_to_int_assignment x).sum (fun r n ↦ π r * (n : ℝ)) =
        x.sum (fun r n ↦ π r * (n : ℝ)) := by
    -- The weighted cut sum is unchanged after widening the natural coefficients to integers.
    simpa [nat_assignment_to_int_assignment] using
      (Finsupp.sum_mapRange_index
        (f := fun n : ℕ ↦ (n : ℤ))
        (hf := by simp)
        (g := x)
        (h := fun r (n : ℤ) ↦ π r * (n : ℝ))
        (h0 := fun r ↦ by simp))
  have hagg_sum :
      (nat_assignment_to_int_assignment x + Finsupp.single rbar (1 : ℤ)).sum
          (fun r n ↦ (n : ℝ) * π r) =
        x.sum (fun r n ↦ π r * (n : ℝ)) + π rbar := by
    -- Isolate the single aggregated pure atom from the integer cut sum.
    rw [Finsupp.sum_add_index]
    · simp [hxsum, rbar, mul_comm]
    · simp
    · intro r n₁ n₂ b₂
      calc
        (((n₂ + b₂ : ℤ) : ℝ) * π r) = ((((n₂ : ℤ) : ℝ) + ((b₂ : ℤ) : ℝ)) * π r) := by
          norm_num
        _ = π r * (n₂ : ℝ) + π r * (b₂ : ℝ) := by
          ring
        _ = (n₂ : ℝ) * π r + (b₂ : ℝ) * π r := by
          ring
  have hrbar_le :
      π rbar ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
    -- First compare `π` with `ψ`, then use sublinearity on the aggregated continuous support.
    calc
      π rbar ≤ ψ rbar := hle rbar
      _ ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
            simpa [rbar] using sublinear_le_continuous_finsupp_sum hψsub y
  calc
    1 ≤ (nat_assignment_to_int_assignment x + Finsupp.single rbar (1 : ℤ)).sum
          (fun r n ↦ (n : ℝ) * π r) :=
      pure_integer_valid_function_one_le_sum hπ hagg
    _ = x.sum (fun r n ↦ π r * (n : ℝ)) + π rbar := hagg_sum
    _ ≤ x.sum (fun r n ↦ π r * (n : ℝ)) +
          y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
            gcongr
    _ = x.sum (fun r n ↦ π r * (n : ℝ)) +
          y.sum (fun r a ↦ ψ r * (a : ℝ)) := rfl

/-- Helper for Theorem 6.34: minimal mixed validity forces the `π`-component to be pure-integer
minimal. -/
lemma pureIntegerMinimal_of_minimalGomoryJohnsonPair
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    pure_integer_minimal_valid_function f π := by
  refine
    { nonneg := hπψ.nonneg
      one_le_sum := hπψ.toIsValidGomoryJohnsonPair.toPureIntegerValidFunction.one_le_sum
      eq_of_le := ?_ }
  intro π' hπ' hle'
  have hπ'ψ :
      IsValidGomoryJohnsonPair f π' ψ :=
    mixedIntegerValidPair_of_pureIntegerValid_sublinear_le
      hπ' hπψ.psi_sublinear (fun r ↦ (hle' r).trans (hπψ.pi_le_psi r))
  -- Route correction: compare `(π', ψ)` directly against the minimal mixed pair.
  exact (hπψ.eq_of_le hπ'ψ hle' (fun r ↦ le_rfl)).1

/-- Helper for Theorem 6.34: the one-atom mixed feasible point gives the basic quotient upper
bound `π (ε • r) / ε ≤ ψ r`. -/
lemma piQuotient_le_of_validPair
    {f : Rq} {π ψ : Rq → ℝ} {r : Rq} {ε : ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hvalid : IsValidGomoryJohnsonPair f π ψ)
    (hε : 0 < ε) :
    π (ε • r) / ε ≤ ψ r := by
  let x : NatAssignment := Finsupp.single (-f - ε • r) 1
  let a : NNReal := ⟨ε, hε.le⟩
  let y : ContAssignment := Finsupp.single r a
  have hxy : (x, y) ∈ mixed_integer_relaxation_set f := by
    rw [mem_mixed_integer_relaxation_set_iff]
    refine ⟨0, ?_⟩
    -- This special mixed point has zero total balance.
    funext i
    have hcoord :
        f i + (-f i - ε * r i + r i * (a : ℝ)) = 0 := by
      rw [show (a : ℝ) = ε by rfl, mul_comm]
      ring
    simpa [x, y, a, smul_eq_mul, add_assoc, add_comm, add_left_comm, mul_comm, mul_left_comm,
      mul_assoc] using hcoord
  have hcut :
      1 ≤ ψ r * (a : ℝ) + π (-f - ε • r) := by
    -- Evaluating mixed validity on the one-atom point produces the basic quotient estimate.
    simpa [x, y, a, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      using hvalid.one_le hxy
  have hsym :
      π (ε • r) + π (-f - ε • r) = 1 :=
    pure_integer_minimal_valid_function_symmetry hπ (ε • r)
  have hmul' :
      π (ε • r) ≤ ψ r * (a : ℝ) := by
    linarith
  have hmul :
      π (ε • r) ≤ ψ r * ε := by
    simpa [a] using hmul'
  simpa [mul_comm] using (div_le_iff₀ hε).2 hmul

/-- Helper for Theorem 6.34: a right-hand limsup is bounded above by any constant that bounds a
nonnegative quotient function on every positive real. -/
lemma limsupLeOfPointwiseIoiBound
    {q : ℝ → ℝ} {c : ℝ}
    (hq_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q ε)
    (hq_le : ∀ ⦃ε : ℝ⦄, 0 < ε → q ε ≤ c) :
    Filter.limsup q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤ c := by
  have hq_cobdd :
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)).IsCoboundedUnder (· ≤ ·) q := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    exact (show ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 ≤ q ε by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hq_nonneg hε).frequently
  have hq_event :
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), q ε ≤ c := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hq_le hε
  -- Convert the pointwise right-neighborhood bound into the filter-level limsup bound.
  exact Filter.limsup_le_of_le hq_cobdd hq_event

/-- Helper for Theorem 6.34: every valid mixed lift dominates the limsup lifting pointwise. -/
lemma limsupLifting_le_of_validPair
    {f : Rq} {π ψ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hvalid : IsValidGomoryJohnsonPair f π ψ) :
    gomory_johnson_limsup_lifting π ≤ ψ := by
  intro r
  -- Package the pointwise quotient estimate into the right-limit filter bound.
  exact limsupLeOfPointwiseIoiBound
    (q := fun ε : ℝ ↦ π (ε • r) / ε)
    (hq_nonneg := fun {_} hε ↦ div_nonneg (hπ.nonneg _) hε.le)
    (hq_le := fun {ε} hε ↦ piQuotient_le_of_validPair (r := r) (ε := ε) hπ hvalid hε)

/-- Helper for Theorem 6.34: the limsup lifting dominates `π` pointwise once any valid mixed lift
is available to bound the quotients from above. -/
lemma pureIntegerMinimal_le_limsupLifting_of_validPair
    {f : Rq} {π ψ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hvalid : IsValidGomoryJohnsonPair f π ψ) :
    π ≤ gomory_johnson_limsup_lifting π := by
  intro r
  let εSeq : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  let q : ℝ → ℝ := fun ε ↦ π (ε • r) / ε
  let seq : ℕ → ℝ := fun n ↦ q (εSeq n)
  have hzero : π 0 = 0 := pure_integer_minimal_valid_function_zero_eq_zero hπ
  have hsub : π.Subadditive := pure_integer_minimal_valid_function_subadditive hπ
  have hseq_ge : ∀ n, π r ≤ seq n := by
    intro n
    have hnat :
        π (((n + 1 : ℕ) : ℝ) • (εSeq n • r)) ≤
          ((n + 1 : ℕ) : ℝ) * π (εSeq n • r) :=
      subadditive_le_nat_smul (π := π) hzero hsub (εSeq n • r) (n + 1)
    have hscale :
        (((n + 1 : ℕ) : ℝ) • (εSeq n • r)) = r := by
      calc
        (((n + 1 : ℕ) : ℝ) • (εSeq n • r)) =
            (((n + 1 : ℕ) : ℝ) * εSeq n) • r := by
              rw [smul_smul]
        _ = (1 : ℝ) • r := by
              congr 1
              dsimp [εSeq]
              field_simp
              norm_num
        _ = r := one_smul ℝ r
    have hquot :
        ((n + 1 : ℕ) : ℝ) * π (εSeq n • r) = π (εSeq n • r) / εSeq n := by
      dsimp [εSeq]
      have hden : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp [hden]
      norm_num [Nat.cast_add]
    calc
      π r = π (((n + 1 : ℕ) : ℝ) • (εSeq n • r)) := by rw [hscale]
      _ ≤ ((n + 1 : ℕ) : ℝ) * π (εSeq n • r) := hnat
      _ = π (εSeq n • r) / εSeq n := hquot
      _ = seq n := rfl
  have hseq_le : ∀ n, seq n ≤ ψ r := by
    intro n
    have hε : 0 < εSeq n := by
      dsimp [εSeq]
      positivity
    exact piQuotient_le_of_validPair (r := r) (ε := εSeq n) hπ hvalid hε
  have hseq_bdd :
      Filter.IsBoundedUnder (· ≤ ·) Filter.atTop seq :=
    Filter.isBoundedUnder_of_eventually_le (a := ψ r) (Filter.Eventually.of_forall hseq_le)
  have hseq_limsup :
      π r ≤ Filter.limsup seq Filter.atTop :=
    Filter.le_limsup_of_frequently_le (Filter.Frequently.of_forall hseq_ge) hseq_bdd
  have hε_tendsto :
      Filter.Tendsto εSeq Filter.atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have htmp :
          Filter.Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
            simpa [one_div] using
              (tendsto_one_div_add_atTop_nhds_zero_nat :
                Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)))
      simpa [εSeq] using htmp
    · exact Filter.Eventually.of_forall (fun n ↦ by
        dsimp [εSeq]
        simpa using inv_pos.mpr (show 0 < (n : ℝ) + 1 by positivity))
  have hq_cobdd :
      (Filter.map εSeq Filter.atTop).IsCoboundedUnder (· ≤ ·) q := by
    apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
    rw [Filter.frequently_map]
    exact Filter.Frequently.of_forall (fun n ↦ by
      dsimp [q, εSeq]
      have hε : 0 < εSeq n := by
        dsimp [εSeq]
        positivity
      exact div_nonneg (hπ.nonneg _) hε.le)
  have hq_bdd :
      Filter.IsBoundedUnder (· ≤ ·) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) q := by
    refine Filter.isBoundedUnder_of_eventually_le (a := ψ r) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact piQuotient_le_of_validPair (r := r) (ε := ε) hπ hvalid hε
  have hseq_to_lift :
      Filter.limsup seq Filter.atTop ≤ gomory_johnson_limsup_lifting π r := by
    simpa [seq, q, gomory_johnson_limsup_lifting_apply] using
      hε_tendsto.limsup_comp_le_limsup (u := q) hq_cobdd hq_bdd
  exact hseq_limsup.trans hseq_to_lift

/-- Helper for Theorem 6.34: the right-hand limsup lifting of a pure-integer minimal valid
function is sublinear once any valid mixed lift provides the needed upper bounds near `0⁺`. -/
lemma limsupLifting_sublinear_of_validPair
    {f : Rq} {π ψ : Rq → ℝ}
    (hπ : pure_integer_minimal_valid_function f π)
    (hvalid : IsValidGomoryJohnsonPair f π ψ) :
    (gomory_johnson_limsup_lifting π).Sublinear := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  refine ⟨?_, ?_⟩
  · intro r₁ r₂
    let q₁ : ℝ → ℝ := fun ε ↦ π (ε • r₁) / ε
    let q₂ : ℝ → ℝ := fun ε ↦ π (ε • r₂) / ε
    let q₁₂ : ℝ → ℝ := fun ε ↦ π (ε • (r₁ + r₂)) / ε
    have hsub : π.Subadditive := pure_integer_minimal_valid_function_subadditive hπ
    have hq₁_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q₁ ε := by
      intro ε hε
      exact div_nonneg (hπ.nonneg _) hε.le
    have hq₂_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q₂ ε := by
      intro ε hε
      exact div_nonneg (hπ.nonneg _) hε.le
    have hq₁₂_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q₁₂ ε := by
      intro ε hε
      exact div_nonneg (hπ.nonneg _) hε.le
    have hq₁₂_le : ∀ ⦃ε : ℝ⦄, 0 < ε → q₁₂ ε ≤ q₁ ε + q₂ ε := by
      intro ε hε
      have hdiv :
          π (ε • (r₁ + r₂)) ≤ (q₁ ε + q₂ ε) * ε := by
        calc
          π (ε • (r₁ + r₂)) = π (ε • r₁ + ε • r₂) := by
            rw [smul_add]
          _ ≤ π (ε • r₁) + π (ε • r₂) := hsub _ _
          _ = ε * q₁ ε + ε * q₂ ε := by
            dsimp [q₁, q₂]
            field_simp [hε.ne']
          _ = (q₁ ε + q₂ ε) * ε := by
            ring
      exact (div_le_iff₀ hε).2 hdiv
    have hq₁_below :
        F.IsBoundedUnder (· ≥ ·) q₁ := by
      refine Filter.isBoundedUnder_of_eventually_ge (a := 0) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hq₁_nonneg hε
    have hq₁_bdd :
        F.IsBoundedUnder (· ≤ ·) q₁ := by
      refine Filter.isBoundedUnder_of_eventually_le (a := ψ r₁) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact piQuotient_le_of_validPair (r := r₁) (ε := ε) hπ hvalid hε
    have hq₂_cobdd :
        F.IsCoboundedUnder (· ≤ ·) q₂ := by
      apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      exact
        (show ∀ᶠ ε in F, 0 ≤ q₂ ε by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          exact hq₂_nonneg hε).frequently
    have hq₂_bdd :
        F.IsBoundedUnder (· ≤ ·) q₂ := by
      refine Filter.isBoundedUnder_of_eventually_le (a := ψ r₂) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact piQuotient_le_of_validPair (r := r₂) (ε := ε) hπ hvalid hε
    have hq₁₂_cobdd :
        F.IsCoboundedUnder (· ≤ ·) q₁₂ := by
      apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      exact
        (show ∀ᶠ ε in F, 0 ≤ q₁₂ ε by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          exact hq₁₂_nonneg hε).frequently
    have hqsum_bdd :
        F.IsBoundedUnder (· ≤ ·) (fun ε ↦ q₁ ε + q₂ ε) := by
      refine Filter.isBoundedUnder_of_eventually_le (a := ψ r₁ + ψ r₂) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have h₁ := piQuotient_le_of_validPair (r := r₁) (ε := ε) hπ hvalid hε
      have h₂ := piQuotient_le_of_validPair (r := r₂) (ε := ε) hπ hvalid hε
      linarith
    have hq₁₂_event :
        ∀ᶠ ε in F, q₁₂ ε ≤ q₁ ε + q₂ ε := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hq₁₂_le hε
    -- Compare the limsup of the quotient at `r₁ + r₂` with the sum of the separate limsups.
    calc
      gomory_johnson_limsup_lifting π (r₁ + r₂) = Filter.limsup q₁₂ F := by
        simp [gomory_johnson_limsup_lifting_apply, q₁₂, F]
      _ ≤ Filter.limsup (fun ε ↦ q₁ ε + q₂ ε) F :=
        Filter.limsup_le_limsup hq₁₂_event hq₁₂_cobdd hqsum_bdd
      _ ≤ Filter.limsup q₁ F + Filter.limsup q₂ F :=
        limsup_add_le hq₁_below hq₁_bdd hq₂_cobdd hq₂_bdd
      _ = gomory_johnson_limsup_lifting π r₁ + gomory_johnson_limsup_lifting π r₂ := by
        simp [gomory_johnson_limsup_lifting_apply, q₁, q₂, F]
  · intro r c hc
    let q : ℝ → ℝ := fun ε ↦ π (ε • r) / ε
    let scale : ℝ → ℝ := fun ε ↦ ε * c
    let scaled : ℝ → ℝ := q ∘ scale
    have hq_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q ε := by
      intro ε hε
      exact div_nonneg (hπ.nonneg _) hε.le
    have hq_bdd :
        F.IsBoundedUnder (· ≤ ·) q := by
      refine Filter.isBoundedUnder_of_eventually_le (a := ψ r) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact piQuotient_le_of_validPair (r := r) (ε := ε) hπ hvalid hε
    have hscaled_cobdd :
        (Filter.map scale F).IsCoboundedUnder (· ≤ ·) q := by
      apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
      exact
        (show ∀ᶠ ε in F, 0 ≤ q (scale ε) by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          simpa [scale] using hq_nonneg (mul_pos hε hc)).frequently
    have hscaled_bdd :
        F.IsBoundedUnder (· ≤ ·) scaled := by
      refine Filter.isBoundedUnder_of_eventually_le (a := ψ r) ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεc : 0 < ε * c := mul_pos hε hc
      exact piQuotient_le_of_validPair (r := r) (ε := ε * c) hπ hvalid hεc
    have hscale_tendsto :
        Filter.Tendsto scale F F := by
      have hcont : ContinuousWithinAt scale (Set.Ioi 0) 0 := by
        simpa [scale] using (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
      simpa [F, scale] using
        hcont.tendsto_nhdsWithin (by
          intro ε hε
          simpa [scale, Set.mem_Ioi] using mul_pos hε hc)
    have hscale_le :
        Filter.limsup scaled F ≤ Filter.limsup q F := by
      exact hscale_tendsto.limsup_comp_le_limsup (u := q) hscaled_cobdd hq_bdd
    have hscaled_eq :
        Filter.limsup (fun ε ↦ c * scaled ε) F = c * Filter.limsup scaled F := by
      symm
      simpa using
        (Monotone.map_limsup_of_continuousAt
          (F := F)
          (f := fun x : ℝ ↦ c * x)
          (f_incr := fun x y hxy ↦ mul_le_mul_of_nonneg_left hxy (le_of_lt hc))
          (a := scaled)
          ((continuous_const.mul continuous_id).continuousAt)
          hscaled_bdd hscaled_cobdd)
    have hforward :
        gomory_johnson_limsup_lifting π (c • r) ≤ c * gomory_johnson_limsup_lifting π r := by
      -- Rewrite the quotient at `c • r`, then push the constant factor through the limsup.
      calc
        gomory_johnson_limsup_lifting π (c • r) =
            Filter.limsup (fun ε ↦ c * scaled ε) F := by
              rw [gomory_johnson_limsup_lifting_apply]
              refine Filter.limsup_congr ?_
              filter_upwards [self_mem_nhdsWithin] with ε hε
              have hc_ne : c ≠ 0 := ne_of_gt hc
              have hε_ne : ε ≠ 0 := ne_of_gt hε
              dsimp [scaled, q, scale]
              rw [smul_smul]
              field_simp [hc_ne, hε_ne]
        _ = c * Filter.limsup scaled F := hscaled_eq
        _ ≤ c * Filter.limsup q F := by
              gcongr
        _ = c * gomory_johnson_limsup_lifting π r := by
              simp [gomory_johnson_limsup_lifting_apply, q, F]
    have hback :
        gomory_johnson_limsup_lifting π r ≤
          c⁻¹ * gomory_johnson_limsup_lifting π (c • r) := by
      simpa [smul_smul, inv_mul_cancel₀ (ne_of_gt hc)] using
        (show gomory_johnson_limsup_lifting π (c⁻¹ • (c • r)) ≤
            c⁻¹ * gomory_johnson_limsup_lifting π (c • r) from
          by
            have hc_inv : 0 < c⁻¹ := inv_pos.mpr hc
            exact
              (by
                have hpos := hc_inv
                exact
                  (show gomory_johnson_limsup_lifting π (c⁻¹ • (c • r)) ≤
                      c⁻¹ * gomory_johnson_limsup_lifting π (c • r) by
                    clear hforward
                    let q' : ℝ → ℝ := fun ε ↦ π (ε • (c • r)) / ε
                    let scale' : ℝ → ℝ := fun ε ↦ ε * c⁻¹
                    let scaled' : ℝ → ℝ := q' ∘ scale'
                    have hq'_nonneg : ∀ ⦃ε : ℝ⦄, 0 < ε → 0 ≤ q' ε := by
                      intro ε hε
                      exact div_nonneg (hπ.nonneg _) hε.le
                    have hq'_bdd :
                        F.IsBoundedUnder (· ≤ ·) q' := by
                      refine Filter.isBoundedUnder_of_eventually_le
                        (a := ψ (c • r)) ?_
                      filter_upwards [self_mem_nhdsWithin] with ε hε
                      exact piQuotient_le_of_validPair (r := c • r) (ε := ε) hπ hvalid hε
                    have hscaled'_cobdd :
                        (Filter.map scale' F).IsCoboundedUnder (· ≤ ·) q' := by
                      apply Filter.IsCoboundedUnder.of_frequently_ge (a := 0)
                      exact
                        (show ∀ᶠ ε in F, 0 ≤ q' (scale' ε) by
                          filter_upwards [self_mem_nhdsWithin] with ε hε
                          simpa [scale'] using hq'_nonneg (mul_pos hε hc_inv)).frequently
                    have hscaled'_bdd :
                        F.IsBoundedUnder (· ≤ ·) scaled' := by
                      refine Filter.isBoundedUnder_of_eventually_le
                        (a := ψ (c • r)) ?_
                      filter_upwards [self_mem_nhdsWithin] with ε hε
                      have hεc : 0 < ε * c⁻¹ := mul_pos hε hc_inv
                      exact piQuotient_le_of_validPair
                        (r := c • r) (ε := ε * c⁻¹) hπ hvalid hεc
                    have hscale'_tendsto :
                        Filter.Tendsto scale' F F := by
                      have hcont : ContinuousWithinAt scale' (Set.Ioi 0) 0 := by
                        simpa [scale'] using
                          (continuous_id.mul continuous_const).continuousAt.continuousWithinAt
                      simpa [F, scale'] using
                        hcont.tendsto_nhdsWithin (by
                          intro ε hε
                          simpa [scale', Set.mem_Ioi] using mul_pos hε hc_inv)
                    have hscale'_le :
                        Filter.limsup scaled' F ≤ Filter.limsup q' F := by
                      exact hscale'_tendsto.limsup_comp_le_limsup
                        (u := q') hscaled'_cobdd hq'_bdd
                    have hscaled'_eq :
                        Filter.limsup (fun ε ↦ c⁻¹ * scaled' ε) F =
                          c⁻¹ * Filter.limsup scaled' F := by
                      symm
                      simpa using
                        (Monotone.map_limsup_of_continuousAt
                          (F := F)
                          (f := fun x : ℝ ↦ c⁻¹ * x)
                          (f_incr := fun x y hxy ↦
                            mul_le_mul_of_nonneg_left hxy (le_of_lt hc_inv))
                          (a := scaled')
                          ((continuous_const.mul continuous_id).continuousAt)
                          hscaled'_bdd hscaled'_cobdd)
                    calc
                      gomory_johnson_limsup_lifting π (c⁻¹ • (c • r)) =
                          Filter.limsup (fun ε ↦ c⁻¹ * scaled' ε) F := by
                            rw [gomory_johnson_limsup_lifting_apply]
                            refine Filter.limsup_congr ?_
                            filter_upwards [self_mem_nhdsWithin] with ε hε
                            have hc_inv_ne : c⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hc)
                            have hε_ne : ε ≠ 0 := ne_of_gt hε
                            dsimp [scaled', q', scale']
                            rw [smul_smul]
                            field_simp [hc_inv_ne, hε_ne]
                      _ = c⁻¹ * Filter.limsup scaled' F := hscaled'_eq
                      _ ≤ c⁻¹ * Filter.limsup q' F := by
                            gcongr
                      _ = c⁻¹ * gomory_johnson_limsup_lifting π (c • r) := by
                            simp [gomory_johnson_limsup_lifting_apply, q', F])))
    have hreverse :
        c * gomory_johnson_limsup_lifting π r ≤
          gomory_johnson_limsup_lifting π (c • r) := by
      have hmul :
          c * (c⁻¹ * gomory_johnson_limsup_lifting π (c • r)) =
            gomory_johnson_limsup_lifting π (c • r) := by
        ring_nf
        simp [ne_of_gt hc]
      have htmp :
          c * gomory_johnson_limsup_lifting π r ≤
            c * (c⁻¹ * gomory_johnson_limsup_lifting π (c • r)) :=
        mul_le_mul_of_nonneg_left hback (le_of_lt hc)
      rw [hmul] at htmp
      exact htmp
    exact le_antisymm hforward hreverse

/-- Theorem 6.34. Let `(π, ψ)` be a valid function for `M_f`. Then `(π, ψ)` is minimal for `M_f`
if and only if `π` is a minimal valid function for `G_f` and `ψ` is given by the right-hand
limsup formula `ψ(r) = limsup_{ε → 0^+} π(ε r) / ε`. -/
theorem minimal_valid_gomory_johnson_pair_iff_pure_integer_minimal_and_eq_limsup_lifting
    (f : Rq) (π ψ : Rq → ℝ)
    (hvalid : IsValidGomoryJohnsonPair f π ψ) :
    IsMinimalValidGomoryJohnsonPair f π ψ ↔
      pure_integer_minimal_valid_function f π ∧
        ψ = gomory_johnson_limsup_lifting π := by
  constructor
  · intro hmin
    refine ⟨pureIntegerMinimal_of_minimalGomoryJohnsonPair hmin, ?_⟩
    have hπmin : pure_integer_minimal_valid_function f π :=
      pureIntegerMinimal_of_minimalGomoryJohnsonPair hmin
    have hlift_le : gomory_johnson_limsup_lifting π ≤ ψ :=
      limsupLifting_le_of_validPair hπmin hvalid
    have hπvalid : pure_integer_valid_function f π :=
      { nonneg := hπmin.nonneg
        one_le_sum := hπmin.one_le_sum }
    have hpi_le_lift : π ≤ gomory_johnson_limsup_lifting π :=
      pureIntegerMinimal_le_limsupLifting_of_validPair hπmin hvalid
    have hlift_sub : (gomory_johnson_limsup_lifting π).Sublinear :=
      limsupLifting_sublinear_of_validPair hπmin hvalid
    have hvalid_lift : IsValidGomoryJohnsonPair f π (gomory_johnson_limsup_lifting π) :=
      mixedIntegerValidPair_of_pureIntegerValid_sublinear_le hπvalid hlift_sub hpi_le_lift
    -- Compare the original minimal pair with the limsup lift, which already lies below `ψ`.
    exact (hmin.eq_of_le hvalid_lift (fun r ↦ le_rfl) hlift_le).2.symm
  · rintro ⟨hπmin, hψeq⟩
    refine
      { toIsValidGomoryJohnsonPair := hvalid
        eq_of_le := ?_ }
    intro π' ψ' hπ'ψ' hπle hψle
    -- First force the pure part to agree with `π` by pure minimality.
    have hπ'eq : π' = π :=
      pure_integer_minimal_valid_function_eq_of_le hπmin
        hπ'ψ'.toPureIntegerValidFunction hπle
    have hvalid' : IsValidGomoryJohnsonPair f π ψ' := by
      simpa [hπ'eq] using hπ'ψ'
    -- Then compare `ψ'` with the limsup lift from both sides.
    have hlift_le : gomory_johnson_limsup_lifting π ≤ ψ' :=
      limsupLifting_le_of_validPair hπmin hvalid'
    have hψ'eq : ψ' = ψ := by
      funext r
      apply le_antisymm (hψle r)
      rw [hψeq]
      exact hlift_le r
    exact ⟨hπ'eq, hψ'eq⟩

namespace IsMinimalValidGomoryJohnsonPair

/-- The `π`-component of a minimal valid Gomory--Johnson pair is a minimal valid function for the
pure-integer relaxation `G_f`. -/
theorem toPureIntegerMinimalValidFunction
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    pure_integer_minimal_valid_function f π :=
  (minimal_valid_gomory_johnson_pair_iff_pure_integer_minimal_and_eq_limsup_lifting
      f π ψ hπψ.toIsValidGomoryJohnsonPair).mp hπψ |>.1

/-- In a minimal valid Gomory--Johnson pair, `ψ` is the right-hand limsup lifting of `π`. -/
theorem eq_limsup_lifting
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ = gomory_johnson_limsup_lifting π :=
  (minimal_valid_gomory_johnson_pair_iff_pure_integer_minimal_and_eq_limsup_lifting
      f π ψ hπψ.toIsValidGomoryJohnsonPair).mp hπψ |>.2

end IsMinimalValidGomoryJohnsonPair

namespace IsValidGomoryJohnsonPair

/-- A valid Gomory--Johnson pair is minimal once its `π`-component is pure-integer minimal and its
`ψ`-component is the right-hand limsup lifting of `π`. -/
theorem minimal_of_pure_integer_minimal_and_eq_limsup_lifting
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (hπ : pure_integer_minimal_valid_function f π)
    (hψ : ψ = gomory_johnson_limsup_lifting π) :
    IsMinimalValidGomoryJohnsonPair f π ψ :=
  (minimal_valid_gomory_johnson_pair_iff_pure_integer_minimal_and_eq_limsup_lifting
      f π ψ hπψ).mpr ⟨hπ, hψ⟩

end IsValidGomoryJohnsonPair

end Theorem634
