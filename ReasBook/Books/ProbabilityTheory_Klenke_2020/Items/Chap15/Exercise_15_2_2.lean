/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

universe u

noncomputable section

/- Exercise 15.2.2 is `source-facing`: the public item is the existence statement. The relevant
owner abstractions are the canonical mathlib notions `PMF`, `IdentDistrib`, and `IndepFun`. The
finite-support data below stay private; they only record a concrete witness built from a
non-product coupling on `Fin 4 × Fin 4` whose row sums, column sums, and anti-diagonal sums agree
with the uniform product law. -/

private def sameSumCounterexampleWeight : (Fin 4 × Fin 4) → ℝ≥0
  | (0, 0) => 1 / 16
  | (0, 1) => 1 / 32
  | (0, 2) => 3 / 32
  | (0, 3) => 1 / 16
  | (1, 0) => 3 / 32
  | (1, 1) => 1 / 16
  | (1, 2) => 1 / 32
  | (1, 3) => 1 / 16
  | (2, 0) => 1 / 32
  | (2, 1) => 3 / 32
  | (2, 2) => 1 / 16
  | (2, 3) => 1 / 16
  | (_, _) => 1 / 16

private theorem sameSumCounterexampleWeight_sum :
    (∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x) = 1 := by
  rw [Fintype.sum_prod_type]
  norm_num [sameSumCounterexampleWeight, Fin.sum_univ_four]

private def sameSumCounterexampleCoupling : PMF (Fin 4 × Fin 4) :=
  PMF.ofFintype (fun x ↦ (sameSumCounterexampleWeight x : ℝ≥0∞)) <| by
    change ((∑ x : Fin 4 × Fin 4, sameSumCounterexampleWeight x : ℝ≥0) : ℝ≥0∞) = 1
    exact_mod_cast sameSumCounterexampleWeight_sum

/-- Helper for Exercise 15.2.2: the comparison pair is the uniform law on `Fin 4 × Fin 4`. -/
private def sameSumCounterexampleUniformPair : PMF (Fin 4 × Fin 4) :=
  PMF.uniformOfFintype (Fin 4 × Fin 4)

/-- Helper for Exercise 15.2.2: the relevant finite sum statistic on `Fin 4 × Fin 4` is
`(x.1 : ℕ) + x.2`. -/
private def sameSumCounterexampleNatSum : Fin 4 × Fin 4 → ℕ
  | (i, j) => (i : ℕ) + j

/-- Helper for Exercise 15.2.2: the sum statistic on `Fin 4 × Fin 4` always lies in `{0, …, 6}`. -/
private theorem sameSumCounterexampleNatSum_le_six (x : Fin 4 × Fin 4) :
    sameSumCounterexampleNatSum x ≤ 6 := by
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;> decide

/-- Helper for Exercise 15.2.2: on a finite product, `PMF.map Prod.fst` evaluates to the
corresponding row sum. -/
private theorem map_fst_apply_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (x : α) :
    (p.map Prod.fst) x = ∑ y : β, p (x, y) := by
  classical
  -- Proof comment: expand the pushforward mass at `x` and then collapse the indicator to the
  -- chosen row.
  rw [PMF.map_apply, tsum_fintype]
  calc
    (∑ a : α × β, if x = a.1 then p a else 0) =
        ∑ x' : α, ∑ y : β, if x = x' then p (x', y) else 0 := by
      simpa using
        (Fintype.sum_prod_type' fun x' : α => fun y : β ↦ if x = x' then p (x', y) else 0)
    _ = ∑ y : β, p (x, y) := by
      simp

/-- Helper for Exercise 15.2.2: on a finite product, `PMF.map Prod.snd` evaluates to the
corresponding column sum. -/
private theorem map_snd_apply_eq_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (y : β) :
    (p.map Prod.snd) y = ∑ x : α, p (x, y) := by
  classical
  -- Proof comment: expand the pushforward mass at `y` and then collapse the indicator to the
  -- chosen column.
  rw [PMF.map_apply, tsum_fintype]
  calc
    (∑ a : α × β, if y = a.2 then p a else 0) =
        ∑ x : α, ∑ y' : β, if y = y' then p (x, y') else 0 := by
      simpa using
        (Fintype.sum_prod_type' fun x : α => fun y' : β ↦ if y = y' then p (x, y') else 0)
    _ = ∑ x : α, p (x, y) := by
      simp

/-- Helper for Exercise 15.2.2: each row of the dependent coupling has total mass `1 / 4`. -/
private theorem sameSumCounterexampleRowMass (i : Fin 4) :
    ∑ j : Fin 4, sameSumCounterexampleWeight (i, j) = (1 / 4 : ℝ≥0) := by
  -- Proof comment: the four explicit row masses are finite arithmetic in `ℝ≥0`.
  fin_cases i <;> norm_num [sameSumCounterexampleWeight, Fin.sum_univ_four]

/-- Helper for Exercise 15.2.2: each column of the dependent coupling has total mass `1 / 4`. -/
private theorem sameSumCounterexampleColumnMass (j : Fin 4) :
    ∑ i : Fin 4, sameSumCounterexampleWeight (i, j) = (1 / 4 : ℝ≥0) := by
  -- Proof comment: the column computation is the same finite check, now along the second index.
  fin_cases j <;> norm_num [sameSumCounterexampleWeight, Fin.sum_univ_four]

/-- Helper for Exercise 15.2.2: every atom of the comparison pair has mass `1 / 16`. -/
private theorem sameSumCounterexampleUniformAtomMass (x : Fin 4 × Fin 4) :
    sameSumCounterexampleUniformPair x = ((1 / 16 : ℝ≥0) : ℝ≥0∞) := by
  -- Proof comment: `uniformOfFintype` is constant on the 16-point state space.
  norm_num [sameSumCounterexampleUniformPair, PMF.uniformOfFintype_apply]

/-- Helper for Exercise 15.2.2: four atoms of mass `1 / 16` add up to `1 / 4`. -/
private theorem sameSumCounterexampleUniformFourAtomMass :
    ∑ _j : Fin 4, (1 / 16 : ℝ≥0) = (1 / 4 : ℝ≥0) := by
  -- Proof comment: this is the one-dimensional marginal mass of the uniform product law.
  norm_num [Fin.sum_univ_four]

/-- Helper for Exercise 15.2.2: the dependent coupling and the uniform pair assign the same
finite mass to each fiber of `sameSumCounterexampleNatSum`. -/
private theorem sameSumCounterexampleNatSumFiberMass (n : ℕ) :
    ∑ x : Fin 4 × Fin 4,
        (if n = sameSumCounterexampleNatSum x then sameSumCounterexampleWeight x else 0) =
      ∑ x : Fin 4 × Fin 4,
        (if n = sameSumCounterexampleNatSum x then (1 / 16 : ℝ≥0) else 0) := by
  by_cases hle : n ≤ 6
  · -- Proof comment: once `n` is one of `0, …, 6`, the fiber masses are a finite enumeration.
    interval_cases n <;>
      simp [sameSumCounterexampleNatSum, sameSumCounterexampleWeight, Fintype.sum_prod_type,
        Fin.sum_univ_four] <;>
      norm_num
  · have hgt : 6 < n := Nat.lt_of_not_ge hle
    have hneq : ∀ x : Fin 4 × Fin 4, n ≠ sameSumCounterexampleNatSum x := by
      intro x
      exact ne_of_gt (lt_of_le_of_lt (sameSumCounterexampleNatSum_le_six x) hgt)
    -- Proof comment: outside `{0, …, 6}` both fibers are empty, so both finite sums vanish.
    simp [hneq]

/-- Helper for Exercise 15.2.2: the first marginal of the dependent coupling agrees with the first
marginal of the uniform pair. -/
private theorem sameSumCounterexampleFirstMarginal :
    sameSumCounterexampleCoupling.toMeasure.map Prod.fst =
      sameSumCounterexampleUniformPair.toMeasure.map Prod.fst := by
  -- Route correction: compare the mapped PMFs first, and do the arithmetic only on the row sums.
  have hMapLeft :
      Measure.map Prod.fst sameSumCounterexampleCoupling.toMeasure =
        (sameSumCounterexampleCoupling.map Prod.fst).toMeasure := by
    simpa using PMF.toMeasure_map (f := Prod.fst) sameSumCounterexampleCoupling measurable_fst
  have hMapRight :
      Measure.map Prod.fst sameSumCounterexampleUniformPair.toMeasure =
        (sameSumCounterexampleUniformPair.map Prod.fst).toMeasure := by
    simpa using PMF.toMeasure_map (f := Prod.fst) sameSumCounterexampleUniformPair measurable_fst
  rw [hMapLeft, hMapRight, PMF.toMeasure_inj]
  ext i
  -- Proof comment: after evaluating the pushforwards pointwise, each row is a finite four-term
  -- computation.
  rw [map_fst_apply_eq_sum, map_fst_apply_eq_sum]
  have hCoupling :
      ∑ j : Fin 4, sameSumCounterexampleCoupling (i, j) =
        ((∑ j : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
    calc
      ∑ j : Fin 4, sameSumCounterexampleCoupling (i, j) =
          ∑ j : Fin 4, ((sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
            simp [sameSumCounterexampleCoupling, PMF.ofFintype_apply]
      _ = ((∑ j : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hUniform :
      ∑ j : Fin 4, sameSumCounterexampleUniformPair (i, j) =
        ((∑ j : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
    calc
      ∑ j : Fin 4, sameSumCounterexampleUniformPair (i, j) =
          ∑ j : Fin 4, (((1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
            simp [sameSumCounterexampleUniformAtomMass]
      _ = ((∑ j : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hRowMass :
      ((∑ j : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) =
        ((1 / 4 : ℝ≥0) : ℝ≥0∞) :=
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (sameSumCounterexampleRowMass i)
  have hUniformQuarter :
      ((∑ j : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) :=
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) sameSumCounterexampleUniformFourAtomMass
  exact hCoupling.trans (hRowMass.trans (hUniformQuarter.symm.trans hUniform.symm))

/-- Helper for Exercise 15.2.2: the second marginal of the dependent coupling agrees with the
second marginal of the uniform pair. -/
private theorem sameSumCounterexampleSecondMarginal :
    sameSumCounterexampleCoupling.toMeasure.map Prod.snd =
      sameSumCounterexampleUniformPair.toMeasure.map Prod.snd := by
  -- Route correction: use the PMF normal form again, now with the column sums.
  have hMapLeft :
      Measure.map Prod.snd sameSumCounterexampleCoupling.toMeasure =
        (sameSumCounterexampleCoupling.map Prod.snd).toMeasure := by
    simpa using PMF.toMeasure_map (f := Prod.snd) sameSumCounterexampleCoupling measurable_snd
  have hMapRight :
      Measure.map Prod.snd sameSumCounterexampleUniformPair.toMeasure =
        (sameSumCounterexampleUniformPair.map Prod.snd).toMeasure := by
    simpa using PMF.toMeasure_map (f := Prod.snd) sameSumCounterexampleUniformPair measurable_snd
  rw [hMapLeft, hMapRight, PMF.toMeasure_inj]
  ext j
  -- Proof comment: the second marginal is the analogous finite computation on the columns.
  rw [map_snd_apply_eq_sum, map_snd_apply_eq_sum]
  have hCoupling :
      ∑ i : Fin 4, sameSumCounterexampleCoupling (i, j) =
        ((∑ i : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
    calc
      ∑ i : Fin 4, sameSumCounterexampleCoupling (i, j) =
          ∑ i : Fin 4, ((sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
            simp [sameSumCounterexampleCoupling, PMF.ofFintype_apply]
      _ = ((∑ i : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hUniform :
      ∑ i : Fin 4, sameSumCounterexampleUniformPair (i, j) =
        ((∑ i : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
    calc
      ∑ i : Fin 4, sameSumCounterexampleUniformPair (i, j) =
          ∑ i : Fin 4, (((1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
            simp [sameSumCounterexampleUniformAtomMass]
      _ = ((∑ i : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hColumnMass :
      ((∑ i : Fin 4, sameSumCounterexampleWeight (i, j) : ℝ≥0) : ℝ≥0∞) =
        ((1 / 4 : ℝ≥0) : ℝ≥0∞) :=
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (sameSumCounterexampleColumnMass j)
  have hUniformQuarter :
      ((∑ i : Fin 4, (1 / 16 : ℝ≥0)) : ℝ≥0∞) = ((1 / 4 : ℝ≥0) : ℝ≥0∞) :=
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) sameSumCounterexampleUniformFourAtomMass
  exact hCoupling.trans (hColumnMass.trans (hUniformQuarter.symm.trans hUniform.symm))

/-- Helper for Exercise 15.2.2: the dependent pair and the uniform pair have the same
distribution for the natural-number sum statistic. -/
private theorem sameSumCounterexampleNatSumMarginal :
    sameSumCounterexampleCoupling.toMeasure.map sameSumCounterexampleNatSum =
      sameSumCounterexampleUniformPair.toMeasure.map sameSumCounterexampleNatSum := by
  -- Route correction: reduce to equality of mapped PMFs and compare the finite fiber masses.
  have hMeasNatSum : Measurable sameSumCounterexampleNatSum :=
    measurable_of_countable sameSumCounterexampleNatSum
  have hMapLeft :
      Measure.map sameSumCounterexampleNatSum sameSumCounterexampleCoupling.toMeasure =
        (sameSumCounterexampleCoupling.map sameSumCounterexampleNatSum).toMeasure := by
    simpa using
      PMF.toMeasure_map (f := sameSumCounterexampleNatSum) sameSumCounterexampleCoupling hMeasNatSum
  have hMapRight :
      Measure.map sameSumCounterexampleNatSum sameSumCounterexampleUniformPair.toMeasure =
        (sameSumCounterexampleUniformPair.map sameSumCounterexampleNatSum).toMeasure := by
    simpa using
      PMF.toMeasure_map (f := sameSumCounterexampleNatSum)
        sameSumCounterexampleUniformPair hMeasNatSum
  rw [hMapLeft, hMapRight, PMF.toMeasure_inj]
  ext n
  -- Proof comment: both mapped pmfs assign the same mass to every anti-diagonal fiber.
  rw [PMF.map_apply, PMF.map_apply, tsum_fintype, tsum_fintype]
  classical
  have hLeft :
      (∑ x : Fin 4 × Fin 4,
          @ite ℝ≥0∞ (n = sameSumCounterexampleNatSum x)
            (Classical.propDecidable (n = sameSumCounterexampleNatSum x))
            (sameSumCounterexampleCoupling x) 0) =
        ((∑ x : Fin 4 × Fin 4,
            if n = sameSumCounterexampleNatSum x then sameSumCounterexampleWeight x else 0 :
              ℝ≥0) : ℝ≥0∞) := by
    calc
      (∑ x : Fin 4 × Fin 4,
          @ite ℝ≥0∞ (n = sameSumCounterexampleNatSum x)
            (Classical.propDecidable (n = sameSumCounterexampleNatSum x))
            (sameSumCounterexampleCoupling x) 0) =
          ∑ x : Fin 4 × Fin 4,
            (((if n = sameSumCounterexampleNatSum x then sameSumCounterexampleWeight x else 0 :
              ℝ≥0)) : ℝ≥0∞) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases h : n = sameSumCounterexampleNatSum x <;>
                simp [sameSumCounterexampleCoupling, PMF.ofFintype_apply, h]
      _ = ((∑ x : Fin 4 × Fin 4,
            if n = sameSumCounterexampleNatSum x then sameSumCounterexampleWeight x else 0 :
              ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hRight :
      (∑ x : Fin 4 × Fin 4,
          @ite ℝ≥0∞ (n = sameSumCounterexampleNatSum x)
            (Classical.propDecidable (n = sameSumCounterexampleNatSum x))
            (sameSumCounterexampleUniformPair x) 0) =
        ((∑ x : Fin 4 × Fin 4,
            if n = sameSumCounterexampleNatSum x then (1 / 16 : ℝ≥0) else 0 :
              ℝ≥0) : ℝ≥0∞) := by
    calc
      (∑ x : Fin 4 × Fin 4,
          @ite ℝ≥0∞ (n = sameSumCounterexampleNatSum x)
            (Classical.propDecidable (n = sameSumCounterexampleNatSum x))
            (sameSumCounterexampleUniformPair x) 0) =
          ∑ x : Fin 4 × Fin 4,
            (((if n = sameSumCounterexampleNatSum x then (1 / 16 : ℝ≥0) else 0 :
              ℝ≥0)) : ℝ≥0∞) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases h : n = sameSumCounterexampleNatSum x <;>
                simp [sameSumCounterexampleUniformAtomMass, h]
      _ = ((∑ x : Fin 4 × Fin 4,
            if n = sameSumCounterexampleNatSum x then (1 / 16 : ℝ≥0) else 0 :
              ℝ≥0) : ℝ≥0∞) := by
            rw [← ENNReal.coe_finset_sum]
  have hFiberMass :
      ((∑ x : Fin 4 × Fin 4,
          if n = sameSumCounterexampleNatSum x then sameSumCounterexampleWeight x else 0 :
            ℝ≥0) : ℝ≥0∞) =
        ((∑ x : Fin 4 × Fin 4,
            if n = sameSumCounterexampleNatSum x then (1 / 16 : ℝ≥0) else 0 :
              ℝ≥0) : ℝ≥0∞) :=
    congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (sameSumCounterexampleNatSumFiberMass n)
  -- Proof comment: the cast transport now matches the goal's `if` shape exactly, so the three
  -- identities compose directly.
  exact hLeft.trans (hFiberMass.trans hRight.symm)

/-- Helper for Exercise 15.2.2: the real-valued coordinate sum is the cast of the finite
sum statistic `sameSumCounterexampleNatSum`. -/
private theorem sameSumCounterexampleRealSum_eq_natCast (z : Fin 4 × Fin 4) :
    ((z.1 : ℝ) + z.2) = (sameSumCounterexampleNatSum z : ℝ) := by
  rcases z with ⟨i, j⟩
  -- Proof comment: `sameSumCounterexampleNatSum` is the ordinary nat sum, so the real identity is
  -- exactly `Nat.cast_add`.
  simpa [sameSumCounterexampleNatSum] using (Nat.cast_add (i : ℕ) (j : ℕ)).symm

/-- Helper for Exercise 15.2.2: the uniform pair law is the product of the one-dimensional
uniform marginals. -/
private theorem sameSumCounterexampleUniformPair_eq_prod :
    sameSumCounterexampleUniformPair.toMeasure =
      (PMF.uniformOfFintype (Fin 4)).toMeasure.prod (PMF.uniformOfFintype (Fin 4)).toMeasure := by
  -- Compare the two measures on singleton atoms of `Fin 4 × Fin 4`.
  rw [Measure.ext_iff_singleton]
  intro x
  rcases x with ⟨i, j⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (i, j)),
    ← Set.singleton_prod_singleton, Measure.prod_prod,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  simp [sameSumCounterexampleUniformPair, PMF.uniformOfFintype_apply]
  rw [← ENNReal.mul_inv (Or.inl (by norm_num : (4 : ℝ≥0∞) ≠ 0))
    (Or.inl (by simp : (4 : ℝ≥0∞) ≠ ∞))]
  norm_num

/-- Helper for Exercise 15.2.2: the dependent coupling is not itself the uniform product law. -/
private theorem sameSumCounterexampleCoupling_ne_uniformPair :
    sameSumCounterexampleCoupling.toMeasure ≠ sameSumCounterexampleUniformPair.toMeasure := by
  intro hEq
  have hAtom :=
    congrArg (fun ν : Measure (Fin 4 × Fin 4) ↦ ν ({(0, 1)} : Set (Fin 4 × Fin 4))) hEq
  -- Proof comment: the two candidate joint laws already disagree on the singleton atom `(0, 1)`.
  have hAtom' :
      sameSumCounterexampleCoupling (0, 1) = sameSumCounterexampleUniformPair (0, 1) := by
    simpa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (0, 1))] using hAtom
  norm_num [sameSumCounterexampleCoupling, sameSumCounterexampleUniformPair,
    sameSumCounterexampleWeight, PMF.ofFintype_apply, PMF.uniformOfFintype_apply] at hAtom'

/-- Helper for Exercise 15.2.2: the explicit `Fin 4 × Fin 4` witness can be reused via its three
canonical pushforwards and the fact that the two joint laws are distinct. -/
theorem sameSumCounterexampleCore :
    ∃ p q : PMF (Fin 4 × Fin 4),
      Measure.map Prod.fst p.toMeasure = Measure.map Prod.fst q.toMeasure ∧
        Measure.map Prod.snd p.toMeasure = Measure.map Prod.snd q.toMeasure ∧
        Measure.map (fun z : Fin 4 × Fin 4 ↦ (z.1 : ℕ) + z.2) p.toMeasure =
          Measure.map (fun z : Fin 4 × Fin 4 ↦ (z.1 : ℕ) + z.2) q.toMeasure ∧
        p.toMeasure ≠ q.toMeasure := by
  -- Proof comment: expose the private coupling and the uniform comparison law through the three
  -- source-facing pushforwards that later arguments actually use.
  refine ⟨sameSumCounterexampleCoupling, sameSumCounterexampleUniformPair, ?_, ?_, ?_, ?_⟩
  · exact sameSumCounterexampleFirstMarginal
  · exact sameSumCounterexampleSecondMarginal
  · simpa [sameSumCounterexampleNatSum] using sameSumCounterexampleNatSumMarginal
  · exact sameSumCounterexampleCoupling_ne_uniformPair

-- Proof sketch: let `(X, Y)` have the private coupling `sameSumCounterexampleCoupling` on
-- `Fin 4 × Fin 4`, and let `(X', Y')` have the uniform product law
-- `PMF.uniformOfFintype (Fin 4 × Fin 4)`. The row and column sums of the dependent coupling are
-- the same as the marginals of the uniform product law, so `X =ᵈ X'` and `Y =ᵈ Y'`. Its
-- anti-diagonal sums also match those of the uniform product law, so `X + Y =ᵈ X' + Y'`. Since
-- the uniform pair is a product law, `X'` and `Y'` are independent, while the dependent coupling
-- is not the product law, so `X` and `Y` are not independent.
/-- Exercise 15.2.2: there exists a probability space carrying real random variables `X`, `X'`,
`Y`, and `Y'` such that `X =ᵈ X'`, `Y =ᵈ Y'`, `X'` and `Y'` are independent,
`X + Y =ᵈ X' + Y'`, but `X` and `Y` are not independent. -/
theorem exists_same_sum_independent_copy_counterexample :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ ∧
      ∃ X X' Y Y' : Ω → ℝ,
        IdentDistrib X X' μ μ ∧
        IdentDistrib Y Y' μ μ ∧
        IndepFun X' Y' μ ∧
        IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X' ω + Y' ω) μ μ ∧
        ¬ IndepFun X Y μ := by
  let Ω₀ := (Fin 4 × Fin 4) × (Fin 4 × Fin 4)
  let Ω : Type u := ULift Ω₀
  let μbase : Measure Ω₀ :=
    sameSumCounterexampleCoupling.toMeasure.prod sameSumCounterexampleUniformPair.toMeasure
  let μ : Measure Ω := μbase.map ULift.up
  let leftPair : Ω → Fin 4 × Fin 4 := fun ω ↦ ω.down.1
  let rightPair : Ω → Fin 4 × Fin 4 := fun ω ↦ ω.down.2
  let leftFst : Ω → Fin 4 := fun ω ↦ (leftPair ω).1
  let leftSnd : Ω → Fin 4 := fun ω ↦ (leftPair ω).2
  let rightFst : Ω → Fin 4 := fun ω ↦ (rightPair ω).1
  let rightSnd : Ω → Fin 4 := fun ω ↦ (rightPair ω).2
  let leftNatSum : Ω → ℕ := sameSumCounterexampleNatSum ∘ leftPair
  let rightNatSum : Ω → ℕ := sameSumCounterexampleNatSum ∘ rightPair
  let X : Ω → ℝ := fun ω ↦ (leftFst ω : ℝ)
  let X' : Ω → ℝ := fun ω ↦ (rightFst ω : ℝ)
  let Y : Ω → ℝ := fun ω ↦ (leftSnd ω : ℝ)
  let Y' : Ω → ℝ := fun ω ↦ (rightSnd ω : ℝ)
  have hμ_prob : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (μbase.map ULift.up)
    infer_instance
  letI : IsProbabilityMeasure μ := hμ_prob
  have hdownLaw : HasLaw ULift.down μbase μ := by
    refine ⟨measurable_down.aemeasurable, ?_⟩
    change Measure.map ULift.down (μbase.map ULift.up) = μbase
    rw [Measure.map_map measurable_down measurable_up]
    rw [show ULift.down ∘ ULift.up = (fun x : Ω₀ ↦ x) by funext x; rfl]
    exact Measure.map_id
  have hLeftBaseLaw : HasLaw Prod.fst sameSumCounterexampleCoupling.toMeasure μbase := by
    simpa [μbase] using
      (measurePreserving_fst (μ := sameSumCounterexampleCoupling.toMeasure)
        (ν := sameSumCounterexampleUniformPair.toMeasure)).hasLaw
  have hRightBaseLaw : HasLaw Prod.snd sameSumCounterexampleUniformPair.toMeasure μbase := by
    simpa [μbase] using
      (measurePreserving_snd (μ := sameSumCounterexampleCoupling.toMeasure)
        (ν := sameSumCounterexampleUniformPair.toMeasure)).hasLaw
  -- Proof comment: compose the lifted-space projection `ULift.down` with the two ambient
  -- projections to recover the left and right pair laws on the common witness space.
  have hLeftPairLaw : HasLaw leftPair sameSumCounterexampleCoupling.toMeasure μ := by
    simpa [leftPair, Function.comp] using HasLaw.comp hLeftBaseLaw hdownLaw
  have hRightPairLaw : HasLaw rightPair sameSumCounterexampleUniformPair.toMeasure μ := by
    simpa [rightPair, Function.comp] using HasLaw.comp hRightBaseLaw hdownLaw
  have hCouplingFstLaw :
      HasLaw Prod.fst (sameSumCounterexampleCoupling.toMeasure.map Prod.fst)
        sameSumCounterexampleCoupling.toMeasure := by
    exact ⟨measurable_fst.aemeasurable, rfl⟩
  have hCouplingSndLaw :
      HasLaw Prod.snd (sameSumCounterexampleCoupling.toMeasure.map Prod.snd)
        sameSumCounterexampleCoupling.toMeasure := by
    exact ⟨measurable_snd.aemeasurable, rfl⟩
  have hCouplingNatSumLaw :
      HasLaw sameSumCounterexampleNatSum
        (sameSumCounterexampleCoupling.toMeasure.map sameSumCounterexampleNatSum)
        sameSumCounterexampleCoupling.toMeasure := by
    exact ⟨(measurable_of_countable sameSumCounterexampleNatSum).aemeasurable, rfl⟩
  have hUniformFstLaw :
      HasLaw Prod.fst (sameSumCounterexampleUniformPair.toMeasure.map Prod.fst)
        sameSumCounterexampleUniformPair.toMeasure := by
    exact ⟨measurable_fst.aemeasurable, rfl⟩
  have hUniformSndLaw :
      HasLaw Prod.snd (sameSumCounterexampleUniformPair.toMeasure.map Prod.snd)
        sameSumCounterexampleUniformPair.toMeasure := by
    exact ⟨measurable_snd.aemeasurable, rfl⟩
  have hUniformNatSumLaw :
      HasLaw sameSumCounterexampleNatSum
        (sameSumCounterexampleUniformPair.toMeasure.map sameSumCounterexampleNatSum)
        sameSumCounterexampleUniformPair.toMeasure := by
    exact ⟨(measurable_of_countable sameSumCounterexampleNatSum).aemeasurable, rfl⟩
  have hLeftFstLaw :
      HasLaw leftFst (sameSumCounterexampleCoupling.toMeasure.map Prod.fst) μ := by
    simpa [leftFst, leftPair, Function.comp] using HasLaw.comp hCouplingFstLaw hLeftPairLaw
  have hLeftSndLaw :
      HasLaw leftSnd (sameSumCounterexampleCoupling.toMeasure.map Prod.snd) μ := by
    simpa [leftSnd, leftPair, Function.comp] using HasLaw.comp hCouplingSndLaw hLeftPairLaw
  have hLeftNatSumLaw :
      HasLaw leftNatSum (sameSumCounterexampleCoupling.toMeasure.map sameSumCounterexampleNatSum)
        μ := by
    simpa [leftNatSum, leftPair, Function.comp] using
      HasLaw.comp hCouplingNatSumLaw hLeftPairLaw
  have hRightFstLaw :
      HasLaw rightFst (sameSumCounterexampleUniformPair.toMeasure.map Prod.fst) μ := by
    simpa [rightFst, rightPair, Function.comp] using HasLaw.comp hUniformFstLaw hRightPairLaw
  have hRightSndLaw :
      HasLaw rightSnd (sameSumCounterexampleUniformPair.toMeasure.map Prod.snd) μ := by
    simpa [rightSnd, rightPair, Function.comp] using HasLaw.comp hUniformSndLaw hRightPairLaw
  have hRightNatSumLaw :
      HasLaw rightNatSum
        (sameSumCounterexampleUniformPair.toMeasure.map sameSumCounterexampleNatSum) μ := by
    simpa [rightNatSum, rightPair, Function.comp] using
      HasLaw.comp hUniformNatSumLaw hRightPairLaw
  have hFstIdent : IdentDistrib leftFst rightFst μ μ := by
    -- Proof comment: the first coordinate laws agree because the two pair laws have the same first
    -- marginal.
    refine
      { aemeasurable_fst := hLeftFstLaw.aemeasurable
        aemeasurable_snd := hRightFstLaw.aemeasurable
        map_eq := ?_ }
    calc
      Measure.map leftFst μ = sameSumCounterexampleCoupling.toMeasure.map Prod.fst :=
        hLeftFstLaw.map_eq
      _ = sameSumCounterexampleUniformPair.toMeasure.map Prod.fst :=
        sameSumCounterexampleFirstMarginal
      _ = Measure.map rightFst μ := hRightFstLaw.map_eq.symm
  have hSndIdent : IdentDistrib leftSnd rightSnd μ μ := by
    -- Proof comment: the second coordinate laws agree by the same marginal comparison on the
    -- second projection.
    refine
      { aemeasurable_fst := hLeftSndLaw.aemeasurable
        aemeasurable_snd := hRightSndLaw.aemeasurable
        map_eq := ?_ }
    calc
      Measure.map leftSnd μ = sameSumCounterexampleCoupling.toMeasure.map Prod.snd :=
        hLeftSndLaw.map_eq
      _ = sameSumCounterexampleUniformPair.toMeasure.map Prod.snd :=
        sameSumCounterexampleSecondMarginal
      _ = Measure.map rightSnd μ := hRightSndLaw.map_eq.symm
  have hNatSumIdent : IdentDistrib leftNatSum rightNatSum μ μ := by
    -- Proof comment: the finite sum statistic has the same pushforward under both joint laws.
    refine
      { aemeasurable_fst := hLeftNatSumLaw.aemeasurable
        aemeasurable_snd := hRightNatSumLaw.aemeasurable
        map_eq := ?_ }
    calc
      Measure.map leftNatSum μ =
          sameSumCounterexampleCoupling.toMeasure.map sameSumCounterexampleNatSum :=
        hLeftNatSumLaw.map_eq
      _ = sameSumCounterexampleUniformPair.toMeasure.map sameSumCounterexampleNatSum :=
        sameSumCounterexampleNatSumMarginal
      _ = Measure.map rightNatSum μ := hRightNatSumLaw.map_eq.symm
  have hXIdent : IdentDistrib X X' μ μ := by
    simpa [X, X', Function.comp] using
      hFstIdent.comp (by fun_prop : Measurable fun i : Fin 4 ↦ (i : ℝ))
  have hYIdent : IdentDistrib Y Y' μ μ := by
    simpa [Y, Y', Function.comp] using
      hSndIdent.comp (by fun_prop : Measurable fun i : Fin 4 ↦ (i : ℝ))
  have hCastNatSumIdent :
      IdentDistrib (fun ω ↦ (leftNatSum ω : ℝ)) (fun ω ↦ (rightNatSum ω : ℝ)) μ μ := by
    simpa [Function.comp] using
      hNatSumIdent.comp (by fun_prop : Measurable fun n : ℕ ↦ (n : ℝ))
  have hUniformFirstMarginal :
      sameSumCounterexampleUniformPair.toMeasure.map Prod.fst =
        (PMF.uniformOfFintype (Fin 4)).toMeasure := by
    calc
      sameSumCounterexampleUniformPair.toMeasure.map Prod.fst =
          ((PMF.uniformOfFintype (Fin 4)).toMeasure.prod
            (PMF.uniformOfFintype (Fin 4)).toMeasure).map Prod.fst := by
              rw [sameSumCounterexampleUniformPair_eq_prod]
      _ = (PMF.uniformOfFintype (Fin 4)).toMeasure := by
            simpa using
              (Measure.map_fst_prod (μ := (PMF.uniformOfFintype (Fin 4)).toMeasure)
                (ν := (PMF.uniformOfFintype (Fin 4)).toMeasure))
  have hUniformSecondMarginal :
      sameSumCounterexampleUniformPair.toMeasure.map Prod.snd =
        (PMF.uniformOfFintype (Fin 4)).toMeasure := by
    calc
      sameSumCounterexampleUniformPair.toMeasure.map Prod.snd =
          ((PMF.uniformOfFintype (Fin 4)).toMeasure.prod
            (PMF.uniformOfFintype (Fin 4)).toMeasure).map Prod.snd := by
              rw [sameSumCounterexampleUniformPair_eq_prod]
      _ = (PMF.uniformOfFintype (Fin 4)).toMeasure := by
            simpa using
              (Measure.map_snd_prod (μ := (PMF.uniformOfFintype (Fin 4)).toMeasure)
                (ν := (PMF.uniformOfFintype (Fin 4)).toMeasure))
  have hRightFstLawUniform :
      HasLaw rightFst (PMF.uniformOfFintype (Fin 4)).toMeasure μ := by
    refine ⟨hRightFstLaw.aemeasurable, ?_⟩
    calc
      Measure.map rightFst μ = sameSumCounterexampleUniformPair.toMeasure.map Prod.fst :=
        hRightFstLaw.map_eq
      _ = (PMF.uniformOfFintype (Fin 4)).toMeasure := hUniformFirstMarginal
  have hRightSndLawUniform :
      HasLaw rightSnd (PMF.uniformOfFintype (Fin 4)).toMeasure μ := by
    refine ⟨hRightSndLaw.aemeasurable, ?_⟩
    calc
      Measure.map rightSnd μ = sameSumCounterexampleUniformPair.toMeasure.map Prod.snd :=
        hRightSndLaw.map_eq
      _ = (PMF.uniformOfFintype (Fin 4)).toMeasure := hUniformSecondMarginal
  have hLeftRealSum :
      (fun ω ↦ X ω + Y ω) = fun ω ↦ (leftNatSum ω : ℝ) := by
    -- Proof comment: on the left pair, the real sum is exactly the cast of
    -- `sameSumCounterexampleNatSum`.
    funext ω
    simpa [X, Y, leftNatSum, leftFst, leftSnd] using
      sameSumCounterexampleRealSum_eq_natCast (leftPair ω)
  have hRightRealSum :
      (fun ω ↦ X' ω + Y' ω) = fun ω ↦ (rightNatSum ω : ℝ) := by
    -- Proof comment: the same cast-normalization identifies the right-hand real sum.
    funext ω
    simpa [X', Y', rightNatSum, rightFst, rightSnd] using
      sameSumCounterexampleRealSum_eq_natCast (rightPair ω)
  have hLeftRealSumEq :
      IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ (leftNatSum ω : ℝ)) μ μ := by
    exact IdentDistrib.of_ae_eq (hXIdent.aemeasurable_fst.add hYIdent.aemeasurable_fst)
      (Filter.EventuallyEq.of_eq hLeftRealSum)
  have hRightRealSumEq :
      IdentDistrib (fun ω ↦ X' ω + Y' ω) (fun ω ↦ (rightNatSum ω : ℝ)) μ μ := by
    exact IdentDistrib.of_ae_eq (hXIdent.aemeasurable_snd.add hYIdent.aemeasurable_snd)
      (Filter.EventuallyEq.of_eq hRightRealSum)
  have hSumIdent : IdentDistrib (fun ω ↦ X ω + Y ω) (fun ω ↦ X' ω + Y' ω) μ μ := by
    exact hLeftRealSumEq.trans (hCastNatSumIdent.trans hRightRealSumEq.symm)
  have hRightEta : (fun ω ↦ (rightFst ω, rightSnd ω)) = rightPair := by
    -- Proof comment: pairing the two right coordinate projections reconstructs the full right
    -- pair random variable.
    funext ω
    exact Prod.eta (rightPair ω)
  have hRightIndepFin : IndepFun rightFst rightSnd μ := by
    -- Proof comment: the right pair already has the product law, so the map-to-product
    -- characterization gives independence of its coordinates.
    refine (indepFun_iff_map_prod_eq_prod_map_map hRightFstLaw.aemeasurable
      hRightSndLaw.aemeasurable).2 ?_
    calc
      Measure.map (fun ω ↦ (rightFst ω, rightSnd ω)) μ =
          sameSumCounterexampleUniformPair.toMeasure := by
            rw [hRightEta, hRightPairLaw.map_eq]
      _ = (PMF.uniformOfFintype (Fin 4)).toMeasure.prod
            (PMF.uniformOfFintype (Fin 4)).toMeasure :=
            sameSumCounterexampleUniformPair_eq_prod
      _ = (Measure.map rightFst μ).prod (Measure.map rightSnd μ) := by
            rw [hRightFstLawUniform.map_eq, hRightSndLawUniform.map_eq]
  have hRightIndep : IndepFun X' Y' μ := by
    simpa [X', Y', Function.comp] using
      hRightIndepFin.comp
        (by fun_prop : Measurable fun i : Fin 4 ↦ (i : ℝ))
        (by fun_prop : Measurable fun i : Fin 4 ↦ (i : ℝ))
  have hLeftEta : (fun ω ↦ (leftFst ω, leftSnd ω)) = leftPair := by
    -- Proof comment: pairing the two left coordinate projections reconstructs the full left
    -- pair random variable.
    funext ω
    exact Prod.eta (leftPair ω)
  have hLeftNotIndepFin : ¬ IndepFun leftFst leftSnd μ := by
    intro hIndep
    -- Proof comment: if the left coordinates were independent, their joint law would equal the
    -- product of its marginals; the marginal identities then rewrite this product to the uniform
    -- pair law, contradicting the atom computation above.
    have hJointEq :
        sameSumCounterexampleCoupling.toMeasure = sameSumCounterexampleUniformPair.toMeasure := by
      calc
        sameSumCounterexampleCoupling.toMeasure =
            Measure.map (fun ω ↦ (leftFst ω, leftSnd ω)) μ := by
              rw [hLeftEta, hLeftPairLaw.map_eq]
        _ = (Measure.map leftFst μ).prod (Measure.map leftSnd μ) := by
              exact (indepFun_iff_map_prod_eq_prod_map_map hLeftFstLaw.aemeasurable
                hLeftSndLaw.aemeasurable).1 hIndep
        _ = (sameSumCounterexampleCoupling.toMeasure.map Prod.fst).prod
            (sameSumCounterexampleCoupling.toMeasure.map Prod.snd) := by
              rw [hLeftFstLaw.map_eq, hLeftSndLaw.map_eq]
        _ = (PMF.uniformOfFintype (Fin 4)).toMeasure.prod
            (PMF.uniformOfFintype (Fin 4)).toMeasure := by
              rw [sameSumCounterexampleFirstMarginal, sameSumCounterexampleSecondMarginal]
              rw [hUniformFirstMarginal, hUniformSecondMarginal]
        _ = sameSumCounterexampleUniformPair.toMeasure := by
              exact sameSumCounterexampleUniformPair_eq_prod.symm
    exact sameSumCounterexampleCoupling_ne_uniformPair hJointEq
  let decodeFin4 : ℝ → Fin 4 := fun x ↦
    if x = 0 then 0 else if x = 1 then 1 else if x = 2 then 2 else 3
  have hDecodeCast : ∀ i : Fin 4, decodeFin4 (i : ℝ) = i := by
    intro i
    fin_cases i <;> norm_num [decodeFin4] <;> decide
  have hNotIndep : ¬ IndepFun X Y μ := by
    intro hIndep
    have hDecodeMeas : Measurable decodeFin4 := by
      dsimp [decodeFin4]
      refine Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const ?_
      refine Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const ?_
      exact Measurable.ite (measurableSet_singleton (2 : ℝ)) measurable_const measurable_const
    have hDecoded : IndepFun (decodeFin4 ∘ X) (decodeFin4 ∘ Y) μ :=
      hIndep.comp hDecodeMeas hDecodeMeas
    have hLeftIndepFin : IndepFun leftFst leftSnd μ := by
      convert hDecoded using 1
      · funext ω
        simpa [Function.comp, X] using (hDecodeCast (leftFst ω)).symm
      · funext ω
        simpa [Function.comp, Y] using (hDecodeCast (leftSnd ω)).symm
    exact hLeftNotIndepFin hLeftIndepFin
  exact ⟨Ω, inferInstance, μ, hμ_prob, X, X', Y, Y', hXIdent, hYIdent, hRightIndep,
    hSumIdent, hNotIndep⟩
