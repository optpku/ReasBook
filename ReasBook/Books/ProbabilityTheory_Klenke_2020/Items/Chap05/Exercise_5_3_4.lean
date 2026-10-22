/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open InformationTheory
open scoped BigOperators

universe u v

variable {E₁ : Type u} {E₂ : Type v} [Finite E₁] [Finite E₂]

/-- Helper for Exercise 5.3.4: coercion from `ENNReal` to `EReal` commutes with finite sums. -/
private theorem coeENNReal_finsetSum {α : Type*} (s : Finset α) (f : α → ENNReal) :
    ((s.sum f : ENNReal) : EReal) = s.sum fun x ↦ (f x : EReal) := by
  -- Induct on the finite set to move the coercion through one summand at a time.
  induction s using Finset.cons_induction with
  | empty =>
      simp
  | @cons a s ha ih =>
      simp [ih]

/-- Helper for Exercise 5.3.4: coercion from `ℝ` to `EReal` commutes with finite sums. -/
private theorem coeReal_finsetSum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((s.sum f : ℝ) : EReal) = s.sum fun x ↦ ((f x : ℝ) : EReal) := by
  -- Induct on the finite set to move the coercion through one real summand at a time.
  induction s using Finset.cons_induction with
  | empty =>
      simp
  | @cons a s ha ih =>
      simp [ih]

/-- Helper for Exercise 5.3.4: coercion from `ℝ` to `EReal` commutes with negated finite sums. -/
private theorem coeReal_neg_finsetSum {α : Type*} (s : Finset α) (f : α → ℝ) :
    ((-s.sum f : ℝ) : EReal) = -s.sum fun x ↦ ((f x : ℝ) : EReal) := by
  -- First pull the negation outside the coercion, then use the finite-sum coercion lemma.
  rw [EReal.coe_neg, coeReal_finsetSum]

/-- Helper for Exercise 5.3.4: on a finite alphabet, the real masses of a probability mass
function sum to `1`. -/
private theorem sumToRealPmf {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a : α, (p a).toReal = 1 := by
  -- Rewrite the finite sum as a `tsum` and use `ENNReal.tsum_toReal_eq`.
  have htsum :
      (∑' a : α, p a).toReal = ∑' a : α, (p a).toReal :=
    ENNReal.tsum_toReal_eq fun a ↦ p.apply_ne_top a
  rw [p.tsum_coe, ENNReal.toReal_one, tsum_fintype] at htsum
  simpa using htsum.symm

section Fintype

variable [Fintype E₁] [Fintype E₂]

/-- Helper for Exercise 5.3.4: the first marginal is the row sum of the joint law. -/
private theorem map_fst_apply_eq_sum (p : PMF (E₁ × E₂)) (x : E₁) :
    (p.map Prod.fst) x = ∑ y : E₂, p (x, y) := by
  classical
  -- Expand `PMF.map` and collapse the indicator to the chosen row.
  rw [PMF.map_apply, tsum_fintype]
  calc
    (∑ a : E₁ × E₂, if x = a.1 then p a else 0) =
        ∑ x' : E₁, ∑ y : E₂, if x = x' then p (x', y) else 0 := by
      simpa using
        (Fintype.sum_prod_type' fun x' : E₁ => fun y : E₂ ↦
          if x = x' then p (x', y) else 0)
    _ = ∑ y : E₂, p (x, y) := by
      simp

/-- Helper for Exercise 5.3.4: the second marginal is the column sum of the joint law. -/
private theorem map_snd_apply_eq_sum (p : PMF (E₁ × E₂)) (y : E₂) :
    (p.map Prod.snd) y = ∑ x : E₁, p (x, y) := by
  classical
  -- Expand `PMF.map` and collapse the indicator to the chosen column.
  rw [PMF.map_apply, tsum_fintype]
  calc
    (∑ a : E₁ × E₂, if y = a.2 then p a else 0) =
        ∑ x : E₁, ∑ y' : E₂, if y = y' then p (x, y') else 0 := by
      simpa using
        (Fintype.sum_prod_type' fun x : E₁ => fun y' : E₂ ↦
          if y = y' then p (x, y') else 0)
    _ = ∑ x : E₁, p (x, y) := by
      simp

/-- Helper for Exercise 5.3.4: the real masses of the product of two marginal laws sum to `1`. -/
private theorem sum_productMarginals_eq_one (p₁ : PMF E₁) (p₂ : PMF E₂) :
    ∑ z : E₁ × E₂, (p₁ z.1 * p₂ z.2).toReal = 1 := by
  -- Separate the product sum into the product of the two one-dimensional mass sums.
  calc
    ∑ z : E₁ × E₂, (p₁ z.1 * p₂ z.2).toReal =
        ∑ x : E₁, ∑ y : E₂, (p₁ x).toReal * (p₂ y).toReal := by
      simpa [ENNReal.toReal_mul] using
        (Fintype.sum_prod_type' fun x : E₁ => fun y : E₂ ↦ (p₁ x * p₂ y).toReal)
    _ = ∑ x : E₁, (p₁ x).toReal * ∑ y : E₂, (p₂ y).toReal := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [← Finset.mul_sum]
    _ = ∑ x : E₁, (p₁ x).toReal := by
      simp [sumToRealPmf p₂]
    _ = 1 := by
      simpa using sumToRealPmf p₁

/-- Helper for Exercise 5.3.4: the product of the two marginals is positive on the support of the
joint law. -/
private theorem productMarginal_ne_zero_of_mem_support (p : PMF (E₁ × E₂))
    (z : E₁ × E₂) (hz : z ∈ p.support) :
    (p.map Prod.fst) z.1 * (p.map Prod.snd) z.2 ≠ 0 := by
  -- Compare the chosen joint mass with its row and column sums to force both marginals to be
  -- nonzero at the corresponding coordinates.
  have hpz_row :
      p z ≤ (p.map Prod.fst) z.1 := by
    rw [map_fst_apply_eq_sum]
    exact Finset.single_le_sum
      (f := fun y : E₂ ↦ p (z.1, y))
      (fun _ _ ↦ zero_le _)
      (Finset.mem_univ _)
  have hpz_col :
      p z ≤ (p.map Prod.snd) z.2 := by
    rw [map_snd_apply_eq_sum]
    exact Finset.single_le_sum
      (f := fun x : E₁ ↦ p (x, z.2))
      (fun _ _ ↦ zero_le _)
      (Finset.mem_univ _)
  have hp₁_ne_zero : (p.map Prod.fst) z.1 ≠ 0 := by
    intro hp₁_zero
    have hpz_zero : p z = 0 := by
      have : p z ≤ 0 := by simpa [hp₁_zero] using hpz_row
      exact le_antisymm this (by simp)
    exact hz hpz_zero
  have hp₂_ne_zero : (p.map Prod.snd) z.2 ≠ 0 := by
    intro hp₂_zero
    have hpz_zero : p z = 0 := by
      have : p z ≤ 0 := by simpa [hp₂_zero] using hpz_col
      exact le_antisymm this (by simp)
    exact hz hpz_zero
  exact mul_ne_zero hp₁_ne_zero hp₂_ne_zero

/-- Helper for Exercise 5.3.4: entropy is bounded above by the logarithmic sum against the product
of the two marginals. -/
private theorem entropy_le_productMarginalLogSum (p : PMF (E₁ × E₂)) :
    entropy p ≤
      -∑ z : E₁ × E₂,
        ((p z : EReal) * ENNReal.log ((p.map Prod.fst) z.1 * (p.map Prod.snd) z.2)) := by
  let p₁ : PMF E₁ := p.map Prod.fst
  let p₂ : PMF E₂ := p.map Prod.snd
  let q : E₁ × E₂ → ENNReal := fun z ↦ p₁ z.1 * p₂ z.2
  have hq_sum : ∑ z : E₁ × E₂, (q z).toReal = 1 := by
    -- The product of the marginals is itself normalized.
    simpa [q] using sum_productMarginals_eq_one p₁ p₂
  have hpointwise :
      ∀ z : E₁ × E₂,
        (p z).toReal * (Real.log (p z).toReal - Real.log (q z).toReal) ≥
          (p z).toReal - (q z).toReal := by
    intro z
    by_cases hpz : p z = 0
    · -- When the joint mass vanishes, only the nonnegativity of `q z` remains.
      simpa [hpz] using neg_nonpos.mpr (show 0 ≤ (q z).toReal by exact ENNReal.toReal_nonneg)
    · -- On the support of `p`, rewrite the logarithmic gap through `klFun`.
      have hz : z ∈ p.support := (PMF.mem_support_iff p z).2 hpz
      have hqz : q z ≠ 0 := by
        simpa [q, p₁, p₂] using productMarginal_ne_zero_of_mem_support p z hz
      have hpz_real : 0 < (p z).toReal := ENNReal.toReal_pos hpz (p.apply_ne_top z)
      have hqz_top : q z ≠ ⊤ := by
        dsimp [q]
        exact ENNReal.mul_ne_top (p₁.apply_ne_top _) (p₂.apply_ne_top _)
      have hqz_real : 0 < (q z).toReal := ENNReal.toReal_pos hqz hqz_top
      have hkl_nonneg : 0 ≤ (q z).toReal * klFun ((p z).toReal / (q z).toReal) := by
        refine mul_nonneg ENNReal.toReal_nonneg ?_
        exact klFun_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      have hidentity :
          (q z).toReal * klFun ((p z).toReal / (q z).toReal) =
            (p z).toReal * (Real.log (p z).toReal - Real.log (q z).toReal) +
              (q z).toReal - (p z).toReal := by
        rw [klFun_apply, Real.log_div hpz_real.ne' hqz_real.ne']
        field_simp [hqz_real.ne']
      linarith
  have hgap_nonneg :
      0 ≤ ∑ z : E₁ × E₂,
        (p z).toReal * (Real.log (p z).toReal - Real.log (q z).toReal) := by
    -- Summing the pointwise bound cancels the mass defect because both total masses are `1`.
    have hsum_lower :
        ∑ z : E₁ × E₂, ((p z).toReal - (q z).toReal) ≤
          ∑ z : E₁ × E₂,
            (p z).toReal * (Real.log (p z).toReal - Real.log (q z).toReal) := by
      exact Finset.sum_le_sum fun z _ ↦ hpointwise z
    have hp_sum : ∑ z : E₁ × E₂, (p z).toReal = 1 := sumToRealPmf p
    have hmass : ∑ z : E₁ × E₂, ((p z).toReal - (q z).toReal) = 0 := by
      rw [Finset.sum_sub_distrib, hp_sum, hq_sum]
      ring
    simpa [hmass] using hsum_lower
  have hgap_eq :
      ∑ z : E₁ × E₂,
          (p z).toReal * (Real.log (p z).toReal - Real.log (q z).toReal) =
        ∑ z : E₁ × E₂, (p z).toReal * Real.log (p z).toReal -
          ∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal := by
    -- Expand the difference inside the finite sum once.
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  have hreal :
      (-∑ z : E₁ × E₂, (p z).toReal * Real.log (p z).toReal : ℝ) ≤
        -∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal := by
    have hdiff_nonneg :
        0 ≤ ∑ z : E₁ × E₂, (p z).toReal * Real.log (p z).toReal -
            ∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal := by
      simpa [hgap_eq] using hgap_nonneg
    linarith
  have hq_term :
      ∀ z : E₁ × E₂,
        ((p z : EReal) * ENNReal.log (q z)) =
          (((p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
    intro z
    by_cases hpz : p z = 0
    · -- Zero-weight terms vanish on both sides.
      simp [hpz]
    · -- On the support, convert the `ENNReal` logarithm to an ordinary real logarithm.
      have hz : z ∈ p.support := (PMF.mem_support_iff p z).2 hpz
      have hqz : q z ≠ 0 := by
        simpa [q, p₁, p₂] using productMarginal_ne_zero_of_mem_support p z hz
      have hqz_top : q z ≠ ⊤ := by
        dsimp [q]
        exact ENNReal.mul_ne_top (p₁.apply_ne_top _) (p₂.apply_ne_top _)
      rw [ENNReal.log_pos_real hqz hqz_top]
      rw [← EReal.coe_ennreal_toReal (p.apply_ne_top z), ← EReal.coe_mul]
  -- Route correction: replace the broken imported cross-entropy inequality with this
  -- theorem-local finite Gibbs inequality against the product of the marginals.
  calc
    entropy p = ((-∑ z : E₁ × E₂, (p z).toReal * Real.log (p z).toReal : ℝ) : EReal) := by
      rw [entropy_eq_sum]
    _ ≤ ((-∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
      exact EReal.coe_le_coe hreal
    _ = -∑ z : E₁ × E₂, (((p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
      rw [coeReal_neg_finsetSum]
    _ = -∑ z : E₁ × E₂, ((p z : EReal) * ENNReal.log (q z)) := by
      simp_rw [hq_term]
    _ = -∑ z : E₁ × E₂,
          ((p z : EReal) * ENNReal.log ((p.map Prod.fst) z.1 * (p.map Prod.snd) z.2)) := by
      simp [q, p₁, p₂]

/-- Helper for Exercise 5.3.4: the logarithmic sum against the product of the marginals splits
into the sum of the two marginal entropies. -/
private theorem productMarginalLogSum_eq_entropy_add_entropy (p : PMF (E₁ × E₂)) :
    -∑ z : E₁ × E₂,
        ((p z : EReal) * ENNReal.log ((p.map Prod.fst) z.1 * (p.map Prod.snd) z.2)) =
      entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
  let p₁ : PMF E₁ := p.map Prod.fst
  let p₂ : PMF E₂ := p.map Prod.snd
  let q : E₁ × E₂ → ENNReal := fun z ↦ p₁ z.1 * p₂ z.2
  have hp₁_apply_real (x : E₁) :
      (p₁ x).toReal = ∑ y : E₂, (p (x, y)).toReal := by
    -- Rewrite the first marginal as a row sum and move `toReal` through the finite sum.
    calc
      (p₁ x).toReal = (∑ y : E₂, p (x, y)).toReal := by
        rw [map_fst_apply_eq_sum]
      _ = ∑ y : E₂, (p (x, y)).toReal := by
        exact ENNReal.toReal_sum (fun y _ ↦ p.apply_ne_top (x, y))
  have hp₂_apply_real (y : E₂) :
      (p₂ y).toReal = ∑ x : E₁, (p (x, y)).toReal := by
    -- Rewrite the second marginal as a column sum and move `toReal` through the finite sum.
    calc
      (p₂ y).toReal = (∑ x : E₁, p (x, y)).toReal := by
        rw [map_snd_apply_eq_sum]
      _ = ∑ x : E₁, (p (x, y)).toReal := by
        exact ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top (x, y))
  have hsplit_term :
      ∀ z : E₁ × E₂,
        (p z).toReal * Real.log (q z).toReal =
          (p z).toReal * Real.log (p₁ z.1).toReal +
            (p z).toReal * Real.log (p₂ z.2).toReal := by
    intro z
    by_cases hpz : p z = 0
    · -- Zero-weight terms vanish regardless of the logarithms.
      simp [hpz, q]
    · -- On the support of `p`, both marginals are positive at the corresponding coordinates.
      have hz : z ∈ p.support := (PMF.mem_support_iff p z).2 hpz
      have hp₁z : p₁ z.1 ≠ 0 := by
        intro hp₁z
        have : q z = 0 := by simp [q, hp₁z]
        exact (productMarginal_ne_zero_of_mem_support p z hz) this
      have hp₂z : p₂ z.2 ≠ 0 := by
        intro hp₂z
        have : q z = 0 := by simp [q, hp₂z]
        exact (productMarginal_ne_zero_of_mem_support p z hz) this
      rw [show (q z).toReal = (p₁ z.1).toReal * (p₂ z.2).toReal by
        simp [q, ENNReal.toReal_mul]]
      rw [Real.log_mul
        ((ENNReal.toReal_ne_zero).2 ⟨hp₁z, p₁.apply_ne_top _⟩)
        ((ENNReal.toReal_ne_zero).2 ⟨hp₂z, p₂.apply_ne_top _⟩)]
      ring
  have hfst_sum_real :
      ∑ z : E₁ × E₂, (p z).toReal * Real.log (p₁ z.1).toReal =
        ∑ x : E₁, (p₁ x).toReal * Real.log (p₁ x).toReal := by
    -- Collapse the product-indexed sum along each row in `ℝ`.
    calc
      ∑ z : E₁ × E₂, (p z).toReal * Real.log (p₁ z.1).toReal =
          ∑ x : E₁, ∑ y : E₂, (p (x, y)).toReal * Real.log (p₁ x).toReal := by
        simpa using
          (Fintype.sum_prod_type' fun x : E₁ => fun y : E₂ ↦
            (p (x, y)).toReal * Real.log (p₁ x).toReal)
      _ = ∑ x : E₁, (∑ y : E₂, (p (x, y)).toReal) * Real.log (p₁ x).toReal := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [← Finset.sum_mul]
      _ = ∑ x : E₁, (p₁ x).toReal * Real.log (p₁ x).toReal := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [← hp₁_apply_real x]
  have hsnd_sum_real :
      ∑ z : E₁ × E₂, (p z).toReal * Real.log (p₂ z.2).toReal =
        ∑ y : E₂, (p₂ y).toReal * Real.log (p₂ y).toReal := by
    -- Collapse the product-indexed sum along each column in `ℝ`.
    calc
      ∑ z : E₁ × E₂, (p z).toReal * Real.log (p₂ z.2).toReal =
          ∑ y : E₂, ∑ x : E₁, (p (x, y)).toReal * Real.log (p₂ y).toReal := by
        simpa using
          (Fintype.sum_prod_type_right' fun x : E₁ => fun y : E₂ ↦
            (p (x, y)).toReal * Real.log (p₂ y).toReal)
      _ = ∑ y : E₂, (∑ x : E₁, (p (x, y)).toReal) * Real.log (p₂ y).toReal := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        rw [← Finset.sum_mul]
      _ = ∑ y : E₂, (p₂ y).toReal * Real.log (p₂ y).toReal := by
        refine Finset.sum_congr rfl ?_
        intro y hy
        rw [← hp₂_apply_real y]
  have hq_term :
      ∀ z : E₁ × E₂,
        ((p z : EReal) * ENNReal.log (q z)) =
          (((p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
    intro z
    by_cases hpz : p z = 0
    · -- Zero-weight terms vanish on both sides.
      simp [hpz]
    · -- On the support, convert the `ENNReal` logarithm to an ordinary real logarithm.
      have hz : z ∈ p.support := (PMF.mem_support_iff p z).2 hpz
      have hqz : q z ≠ 0 := by
        simpa [q, p₁, p₂] using productMarginal_ne_zero_of_mem_support p z hz
      have hqz_top : q z ≠ ⊤ := by
        dsimp [q]
        exact ENNReal.mul_ne_top (p₁.apply_ne_top _) (p₂.apply_ne_top _)
      rw [ENNReal.log_pos_real hqz hqz_top]
      rw [← EReal.coe_ennreal_toReal (p.apply_ne_top z), ← EReal.coe_mul]
  have hreal :
      (-∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal : ℝ) =
        (-∑ x : E₁, (p₁ x).toReal * Real.log (p₁ x).toReal : ℝ) +
          (-∑ y : E₂, (p₂ y).toReal * Real.log (p₂ y).toReal : ℝ) := by
    -- Split the product logarithm into the sum of the two marginal logarithms and collapse both
    -- product-indexed sums in `ℝ`.
    calc
      (-∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal : ℝ) =
          (-∑ z : E₁ × E₂,
              ((p z).toReal * Real.log (p₁ z.1).toReal +
                (p z).toReal * Real.log (p₂ z.2).toReal) : ℝ) := by
        refine congrArg Neg.neg ?_
        exact Finset.sum_congr rfl fun z _ ↦ hsplit_term z
      _ = (-∑ z : E₁ × E₂, (p z).toReal * Real.log (p₁ z.1).toReal : ℝ) +
            (-∑ z : E₁ × E₂, (p z).toReal * Real.log (p₂ z.2).toReal : ℝ) := by
        rw [Finset.sum_add_distrib]
        ring
      _ = (-∑ x : E₁, (p₁ x).toReal * Real.log (p₁ x).toReal : ℝ) +
            (-∑ y : E₂, (p₂ y).toReal * Real.log (p₂ y).toReal : ℝ) := by
        rw [hfst_sum_real, hsnd_sum_real]
  have hq_sum_cast :
      -∑ z : E₁ × E₂, ((p z : EReal) * ENNReal.log (q z)) =
        ((-∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
    rw [show
        -∑ z : E₁ × E₂, ((p z : EReal) * ENNReal.log (q z)) =
          -∑ z : E₁ × E₂, (((p z).toReal * Real.log (q z).toReal : ℝ) : EReal) by
        simp_rw [hq_term]]
    rw [← coeReal_neg_finsetSum]
  -- Convert the explicit finite real identity back to the `EReal` entropy formulation.
  calc
    -∑ z : E₁ × E₂, ((p z : EReal) * ENNReal.log ((p.map Prod.fst) z.1 * (p.map Prod.snd) z.2)) =
        -∑ z : E₁ × E₂, ((p z : EReal) * ENNReal.log (q z)) := by
      simp [q, p₁, p₂]
    _ = ((-∑ z : E₁ × E₂, (p z).toReal * Real.log (q z).toReal : ℝ) : EReal) := by
      exact hq_sum_cast
    _ = ((-∑ x : E₁, (p₁ x).toReal * Real.log (p₁ x).toReal : ℝ) : EReal) +
          ((-∑ y : E₂, (p₂ y).toReal * Real.log (p₂ y).toReal : ℝ) : EReal) := by
      simpa [EReal.coe_add] using congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    _ = entropy p₁ + entropy p₂ := by
      rw [entropy_eq_sum, entropy_eq_sum]
    _ = entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
      simp [p₁, p₂]

end Fintype

-- Proof sketch: compare the joint law with the product of its marginals by a finite Gibbs
-- inequality, then identify the resulting logarithmic sum with the sum of the two marginal
-- entropies.
/-- Exercise 5.3.4: the entropy of a joint probability mass function on a finite product is at
most the sum of the entropies of its two marginal probability mass functions. -/
theorem entropy_le_entropy_map_fst_add_entropy_map_snd
    (p : PMF (E₁ × E₂)) :
    entropy p ≤ entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
  classical
  letI : Fintype E₁ := Fintype.ofFinite E₁
  letI : Fintype E₂ := Fintype.ofFinite E₂
  -- Route correction: avoid the broken imported cross-entropy API and assemble the result from
  -- the local Gibbs inequality plus the marginal logarithmic decomposition.
  calc
    entropy p ≤
        -∑ z : E₁ × E₂,
          ((p z : EReal) * ENNReal.log ((p.map Prod.fst) z.1 * (p.map Prod.snd) z.2)) := by
      exact entropy_le_productMarginalLogSum p
    _ = entropy (p.map Prod.fst) + entropy (p.map Prod.snd) := by
      exact productMarginalLogSum_eq_entropy_add_entropy p
