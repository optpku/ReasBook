/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped BigOperators ENNReal

universe u v

variable {E : Type u}

/-- Helper for Example 12.5: inside the moved prefix, `permutePrefix` acts by the given
permutation. -/
lemma permutePrefix_apply_fin {k : ℕ} (ρ : Equiv.Perm (Fin k)) (x : ℕ → E) (i : Fin k) :
    permutePrefix k ρ x i = x (ρ i) := by
  -- Unfold the extended permutation only on the prefix where it is controlled by `ρ`.
  simp [permutePrefix, Equiv.Perm.extendDomain_apply_subtype]

/-- Helper for Example 12.5: outside the moved prefix, `permutePrefix` leaves the sequence
unchanged. -/
lemma permutePrefix_apply_of_ge {k : ℕ} (ρ : Equiv.Perm (Fin k)) (x : ℕ → E) {j : ℕ} (hj : k ≤ j) :
    permutePrefix k ρ x j = x j := by
  -- The extension of `ρ` fixes every index that does not lie in the first `k` coordinates.
  exact congrArg x
    (Equiv.Perm.extendDomain_apply_not_subtype (e := ρ) (f := Fin.equivSubtype)
      (b := j) (h := Nat.not_lt.mpr hj))

/-- Helper for Example 12.5: once the averaging window contains the moved prefix, the arithmetic
mean is unchanged by permuting that prefix. -/
lemma arithmeticMean_prefixInvariant {k : ℕ} (ρ : Equiv.Perm (Fin k)) (x : ℕ → ℝ)
    (N : ℕ+) (hkN : k ≤ (N : ℕ)) :
    (∑ i : Fin (N : ℕ), permutePrefix k ρ x i) / (N : ℝ) =
      (∑ i : Fin (N : ℕ), x i) / (N : ℝ) := by
  -- Split the finite sum into the moved prefix and the untouched tail.
  have hsum :
      (∑ i : Fin (N : ℕ), permutePrefix k ρ x i) = (∑ i : Fin (N : ℕ), x i) := by
    rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range,
      ← Finset.sum_range_add_sum_Ico _ hkN, ← Finset.sum_range_add_sum_Ico _ hkN]
    have hprefix :
        Finset.sum (Finset.range k) (fun j ↦ permutePrefix k ρ x j) =
          Finset.sum (Finset.range k) (fun j ↦ x j) := by
      -- Reindex the prefix part by the permutation `ρ`.
      rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
      calc
        (∑ j : Fin k, permutePrefix k ρ x j) = ∑ j : Fin k, x (ρ j) := by
          simp [permutePrefix_apply_fin]
        _ = ∑ j : Fin k, x j := by
          exact Fintype.sum_bijective ρ ρ.bijective _ _ (fun j ↦ rfl)
    have htail :
        Finset.sum (Finset.Ico k (N : ℕ)) (fun j ↦ permutePrefix k ρ x j) =
          Finset.sum (Finset.Ico k (N : ℕ)) (fun j ↦ x j) := by
      -- Every term in the tail is fixed pointwise.
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact permutePrefix_apply_of_ge (ρ := ρ) (x := x) (Finset.mem_Ico.mp hj).1
    rw [hprefix, htail]
  simpa using congrArg (fun t : ℝ ↦ t / (N : ℝ)) hsum

/-- Helper for Example 12.5: reindexing a tuple by a permutation does not change its empirical
distribution. -/
lemma empiricalDistributionTuple_compPermLocal [MeasurableSpace E] {n : ℕ+}
    (ρ : Equiv.Perm (Fin n)) (x : Fin n → E) :
    empiricalDistributionTuple (x ∘ ρ) = empiricalDistributionTuple x := by
  -- Compare the two probability measures on arbitrary measurable sets.
  apply ProbabilityMeasure.eq_of_forall_toMeasure_apply_eq
  intro s hs
  rw [empiricalDistributionTuple, empiricalDistributionTuple]
  rw [empiricalDistribution_toMeasure, empiricalDistribution_toMeasure]
  simp only [Measure.smul_apply, hs, Function.comp_apply, Measure.finset_sum_apply,
    Measure.dirac_apply']
  congr 1
  exact Fintype.sum_bijective ρ ρ.bijective _ _ (fun i ↦ rfl)

/-- Helper for Example 12.5: restricting `permutePrefix` to `Fin n` is composition with the
finite permutation. -/
lemma restrictPermutePrefix_eq_comp {n : ℕ+} (ρ : Equiv.Perm (Fin n)) (x : ℕ → E) :
    (fun i : Fin n ↦ permutePrefix (n : ℕ) ρ x i) = (fun i : Fin n ↦ x i) ∘ ρ := by
  -- On the first `n` coordinates, the extended permutation coincides with `ρ`.
  funext i
  exact permutePrefix_apply_fin (ρ := ρ) (x := x) i

/-- Helper for Example 12.5: the symmetrized average over the first `n` coordinates of a
sequence functional. -/
noncomputable def exchangeableAverage (n : ℕ) (φ : (ℕ → E) → ℝ) : (ℕ → E) → ℝ :=
  fun x ↦ (∑ ρ : Equiv.Perm (Fin n), φ (permutePrefix n ρ x)) / Nat.factorial n

/-- Helper for Example 12.5: composing two finite prefix permutations multiplies the underlying
permutations in the corresponding order. -/
lemma permutePrefix_mul {n : ℕ} (ρ τ : Equiv.Perm (Fin n)) (x : ℕ → E) :
    permutePrefix n ρ (permutePrefix n τ x) = permutePrefix n (τ * ρ) x := by
  -- Normalize both sides to the action of the extended permutation on `ℕ`.
  funext i
  have hmul :
      τ.extendDomain Fin.equivSubtype * ρ.extendDomain Fin.equivSubtype =
        (τ * ρ).extendDomain Fin.equivSubtype := by
    exact Equiv.Perm.extendDomain_mul (f := Fin.equivSubtype) τ ρ
  change x (((τ.extendDomain Fin.equivSubtype) * (ρ.extendDomain Fin.equivSubtype)) i) =
      x (((τ * ρ).extendDomain Fin.equivSubtype) i)
  exact congrArg (fun σ : Equiv.Perm ℕ ↦ x (σ i)) hmul

/-- Helper for Example 12.5: the finite permutation average is invariant under prefix
permutations. -/
theorem exchangeableAverage_isNSymmetric (n : ℕ) (φ : (ℕ → E) → ℝ) :
    IsNSymmetricSequenceMap n (exchangeableAverage n φ) := by
  intro ρ x
  -- Rewrite the inner action as left multiplication on `Equiv.Perm (Fin n)`.
  have hsum :
      (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ (permutePrefix n ρ x))) =
        (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ x)) := by
    calc
      (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ (permutePrefix n ρ x))) =
          (∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n (ρ * τ) x)) := by
            apply Fintype.sum_congr
            intro τ
            rw [permutePrefix_mul (ρ := τ) (τ := ρ)]
      _ = ∑ τ : Equiv.Perm (Fin n), φ (permutePrefix n τ x) := by
            simpa using
              (Function.Bijective.sum_comp (Group.mulLeft_bijective ρ)
                (fun τ : Equiv.Perm (Fin n) ↦ φ (permutePrefix n τ x)))
  -- The denominator is constant, so numerator invariance proves the claim.
  simp [exchangeableAverage, hsum]

-- Proof sketch: reindex the finite sum over `Fin n` by the permutation `σ`; the value of the
-- arithmetic mean is unchanged because the numerator is permutation-invariant. Use the owner
-- theorem `exchangeableAverage_isNSymmetric` together with
-- `exchangeableAverage_apply_zero`.
/-- Item (i) of Example 12.5: the `n`th arithmetic mean is `n`-symmetric for positive `n`. -/
theorem arithmeticMean_isNSymmetric (n : ℕ+) :
    IsNSymmetricSequenceMap (n : ℕ)
      (fun x : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), x i) / (n : ℝ)) := by
  intro ρ x
  -- This is the special case of prefix invariance where the averaging window has size `n`.
  simpa using arithmeticMean_prefixInvariant (ρ := ρ) (x := x) (N := n) le_rfl

-- Proof sketch: choose a sequence that is zero on the first `n` coordinates and nonzero at one
-- extra coordinate below `m`; a permutation of the first `m` coordinates can move that value into
-- the averaging window and change the mean.
/-- Item (i) of Example 12.5: for positive prefix lengths, the `n`th arithmetic mean is not
`m`-symmetric for any `m > n`. -/
theorem arithmeticMean_not_isNSymmetric_of_lt {n m : ℕ+} (hnm : n < m) :
    ¬ IsNSymmetricSequenceMap (m : ℕ)
      (fun x : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), x i) / (n : ℝ)) := by
  intro hsym
  let witness : Fin (m : ℕ) := ⟨n, hnm⟩
  let ρ : Equiv.Perm (Fin (m : ℕ)) := Equiv.swap 0 witness
  let x : ℕ → ℝ := fun j ↦ if j = 0 then 1 else 0
  have horig :
      ((∑ i : Fin (n : ℕ), x i) / (n : ℝ)) = 1 / (n : ℝ) := by
    -- The original mean sees the single nonzero entry at index `0`.
    have hsum : (∑ i : Fin (n : ℕ), x i) = 1 := by
      rw [Fintype.sum_eq_single 0]
      · simp [x]
      · intro i hi
        simp [x, hi]
    simp [hsum]
  have hperm :
      ((∑ i : Fin (n : ℕ), permutePrefix (m : ℕ) ρ x i) / (n : ℝ)) = 0 := by
    -- After swapping `0` with the witness coordinate, the averaging window contains only zeros.
    have hsum : (∑ i : Fin (n : ℕ), permutePrefix (m : ℕ) ρ x i) = 0 := by
      rw [Fin.sum_univ_eq_sum_range]
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hi_lt_n : i < (n : ℕ) := Finset.mem_range.mp hi
      have hi_lt_m : i < (m : ℕ) := lt_of_lt_of_le hi_lt_n (Nat.le_of_lt hnm)
      have hi_ne_witness : (⟨i, hi_lt_m⟩ : Fin (m : ℕ)) ≠ witness := by
        intro hiw
        exact (ne_of_lt hi_lt_n) (Fin.mk.inj hiw)
      have happly :=
        permutePrefix_apply_fin (ρ := ρ) (x := x) (i := ⟨i, hi_lt_m⟩)
      by_cases hi0 : i = 0
      · -- The image of `0` under the swap is `witness`, where the sequence vanishes.
        simpa [ρ, x, witness, hi0, hnm.ne'] using happly
      · -- Every other index below `n` is fixed by the swap and still maps to `0`.
        have hi_ne_zero : (⟨i, hi_lt_m⟩ : Fin (m : ℕ)) ≠ 0 := by
          intro hizero
          exact hi0 (Fin.mk.inj hizero)
        have hfixed : ρ ⟨i, hi_lt_m⟩ = ⟨i, hi_lt_m⟩ := by
          simpa [ρ, witness] using
            Equiv.swap_apply_of_ne_of_ne (a := (0 : Fin (m : ℕ))) (b := witness)
              (x := ⟨i, hi_lt_m⟩) hi_ne_zero hi_ne_witness
        calc
          permutePrefix (m : ℕ) ρ x i = x i := by simpa [hfixed] using happly
          _ = 0 := by simp [x, hi0]
    simp [hsum]
  have hneq : (1 : ℝ) / (n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (1 : ℝ) / (n : ℝ) := by
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast n.pos
      positivity
    exact ne_of_gt hpos
  have hs := hsym ρ x
  have hleft :
      (fun y : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), y i) / (n : ℝ)) (permutePrefix (m : ℕ) ρ x) = 0 := by
    simpa using hperm
  have hright :
      (fun y : ℕ → ℝ ↦ (∑ i : Fin (n : ℕ), y i) / (n : ℝ)) x = 1 / (n : ℝ) := by
    simpa using horig
  rw [hleft, hright] at hs
  exact hneq hs.symm

-- Proof sketch: permuting the first `n` coordinates changes only finitely many terms of the
-- sequence of arithmetic means, so the limsup at `atTop` is unchanged; since `n` was arbitrary,
-- the map is symmetric in the sense of Definition 12.4.
/-- Example 12.5: item (i). The limsup of the arithmetic means defines a symmetric map
`ℝ^ℕ → ℝ ∪ {-∞, +∞}`. -/
theorem limsupArithmeticMean_isSymmetric :
    IsSymmetricSequenceMap
      (fun x : ℕ → ℝ ↦
        Filter.limsup
          (fun n ↦
            (((∑ i : Fin (Nat.succPNat n : ℕ), x i) / (Nat.succPNat n : ℝ)) : EReal))
          Filter.atTop) := by
  intro k ρ x
  have hEventually :
      ∀ᶠ n in Filter.atTop,
        (((∑ i : Fin (Nat.succPNat n : ℕ), permutePrefix k ρ x i) / (Nat.succPNat n : ℝ)) :
            EReal) =
          (((∑ i : Fin (Nat.succPNat n : ℕ), x i) / (Nat.succPNat n : ℝ)) : EReal) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨k, ?_⟩
    intro n hn
    -- Once the averaging window contains the permuted prefix, the arithmetic means agree exactly.
    have hk : k ≤ (Nat.succPNat n : ℕ) := le_trans hn (Nat.le_succ n)
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (arithmeticMean_prefixInvariant (ρ := ρ) (x := x) (N := Nat.succPNat n) hk)
  -- Eventual equality of the mean sequence gives equality of its limsup.
  simpa using Filter.limsup_congr hEventually

-- Proof sketch: permuting any finite prefix only reindexes finitely many terms of the nonnegative
-- series `∑' n, |x n|`, so the `tsum` is unchanged at every stage.
/-- Item (ii) of Example 12.5: the map `x ↦ ∑' n, |x n|` is symmetric. -/
theorem absoluteSeries_isSymmetric :
    IsSymmetricSequenceMap (fun x : ℕ → ℝ ↦ ∑' n, ENNReal.ofReal |x n|) := by
  intro n ρ x
  -- Reindex the nonnegative series by the extended permutation of `ℕ`.
  simpa [permutePrefix, Function.comp_apply] using
    ((ρ.extendDomain Fin.equivSubtype).tsum_eq (fun j : ℕ ↦ ENNReal.ofReal |x j|))

-- Proof sketch: permuting the first `n` coordinates only reorders the finite sum of Dirac masses
-- defining the empirical distribution of the first `n` coordinates, so the resulting probability
-- measure is unchanged.
/-- Item (iii) of Example 12.5: the empirical distribution of the first `n` coordinates,
realized as the deterministic specialization of Definition 12.25, is `n`-symmetric. -/
theorem empiricalDistribution_isNSymmetric [MeasurableSpace E] (n : ℕ+) :
    IsNSymmetricSequenceMap (n : ℕ)
      (fun x : ℕ → E ↦ empiricalDistributionTuple (fun i : Fin n ↦ x i)) := by
  intro ρ x
  -- The empirical distribution only depends on the multiset of tuple entries.
  simpa [restrictPermutePrefix_eq_comp (ρ := ρ) (x := x)] using
    empiricalDistributionTuple_compPermLocal ρ (fun i : Fin n ↦ x i)

-- Proof sketch: average `φ` over all permutations of `Fin n`; left-multiplication by a fixed
-- permutation merely reindexes the finite sum over `Equiv.Perm (Fin n)`. This is the same owner
-- symmetry theorem for `exchangeableAverage`, now specialized to the finite-coordinate functional
-- induced by `φ`.
/-- Item (iv) of Example 12.5: the `n`th symmetrized average associated with `φ : E^k → ℝ` is
`n`-symmetric. -/
theorem symmetrizedAverage_isNSymmetric (n k : ℕ) (φ : (Fin k → E) → ℝ) :
    IsNSymmetricSequenceMap n (exchangeableAverage n (fun x ↦ φ (fun i ↦ x i))) := by
  -- The owner finite-permutation average is already invariant under every prefix permutation.
  simpa using exchangeableAverage_isNSymmetric n (fun x ↦ φ (fun i ↦ x i))
