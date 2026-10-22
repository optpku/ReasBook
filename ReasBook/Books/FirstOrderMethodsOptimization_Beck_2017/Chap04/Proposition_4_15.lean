/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_22
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_8
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.15 is `source-facing`: the textbook barrier on `ℝ^n` is the finite separable sum
of the scalar Chapter 4 owner `negative_log_barrier`. The `core/canonical` Fenchel owner is
`conjugate_function`, and the relevant `bridge/view` owner is
`conjugate_function_separable_sum_eq_sum_conjugate_function`. The positive-orthant description is
therefore derived API, and the finite-sum formula is stated directly on the textbook coordinate
space `Fin n → ℝ`. -/

section

variable {n : ℕ}

local notation "E" => Fin n → ℝ

/-- The coordinatewise negative-log barrier on `ℝ^n`, modeled as `Fin n → ℝ`, obtained by summing
the scalar barrier `negative_log_barrier` over the coordinates. -/
def sum_negative_log_barrier (n : ℕ) : (Fin n → ℝ) → EReal :=
  fun x ↦ ∑ i, negative_log_barrier (x i)

/-- Helper for Proposition 4.15: coercing a finite real sum into `EReal` agrees with summing the
coerced real terms. -/
lemma ereal_coe_finset_sum {α : Type*} (s : Finset α) (φ : α → ℝ) :
    ((s.sum φ : ℝ) : EReal) = s.sum (fun i ↦ ((φ i : ℝ) : EReal)) := by
  classical
  -- Push the coercion through the finite sum one inserted term at a time.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, hs]

/-- Helper for Proposition 4.15: the scalar negative-log barrier is proper as an extended-real
function. -/
lemma isProperExtendedRealFunction_negative_log_barrier :
    IsProperExtendedRealFunction negative_log_barrier := by
  refine ⟨?_, ?_⟩
  · intro x
    -- The scalar barrier takes only finite real values or `⊤`, never `⊥`.
    by_cases hx : 0 < x
    · simp [negative_log_barrier, hx]
    · simp [negative_log_barrier, hx]
  · -- The point `x = 1` belongs to the effective domain.
    refine ⟨1, ?_⟩
    simp [effective_domain, negative_log_barrier]

/-- Helper for Proposition 4.15: on `ℝ`, the coordinate functional
`LinearMap.toSpanSingleton ℝ ℝ y` equals the Euclidean dual vector
`InnerProductSpace.toDualMap ℝ ℝ y`. -/
lemma toSpanSingletonReal_eq_toDualMap (y : ℝ) :
    LinearMap.toSpanSingleton ℝ ℝ y = (InnerProductSpace.toDualMap ℝ ℝ y : Module.Dual ℝ ℝ) := by
  -- A linear functional on `ℝ` is determined by its value at `1`.
  apply LinearMap.ext_ring
  calc
    LinearMap.toSpanSingleton ℝ ℝ y 1 = y := by simp
    _ = inner ℝ y (1 : ℝ) := by
          calc
            y = y * 1 := by ring
            _ = y * inner ℝ (1 : ℝ) (1 : ℝ) := by simp
            _ = inner ℝ (y • (1 : ℝ)) (1 : ℝ) := by rw [real_inner_smul_left]
            _ = inner ℝ y (1 : ℝ) := by simp
    _ = InnerProductSpace.toDualMap ℝ ℝ y 1 := by
          rw [InnerProductSpace.toDualMap_apply_apply]

-- Proof sketch: each summand is `-log (x i)` for `x i > 0` and `⊤` otherwise. Thus the finite sum
-- is finite exactly when every coordinate is positive, and on that positive orthant it collapses
-- to `-∑ i, log (x i)`.
/-- The finite separable sum of the scalar negative-log barrier is the textbook barrier on `ℝ^n`:
`-∑ i, log (x i)` on the positive orthant and `∞` outside it. -/
theorem sum_negative_log_barrier_apply (x : E) :
    sum_negative_log_barrier n x =
      if ∀ i : Fin n, 0 < x i then ((-∑ i : Fin n, Real.log (x i) : ℝ) : EReal) else ⊤ := by
  classical
  by_cases hx : ∀ i : Fin n, 0 < x i
  · -- On the positive orthant, every summand is the finite value `-log (x i)`.
    rw [if_pos hx]
    calc
      sum_negative_log_barrier n x
          = ∑ i : Fin n, ((-Real.log (x i) : ℝ) : EReal) := by
              simp [sum_negative_log_barrier, negative_log_barrier, hx]
      _ = (((∑ i : Fin n, -Real.log (x i) : ℝ)) : EReal) := by
            symm
            simpa using (ereal_coe_finset_sum Finset.univ (fun i : Fin n ↦ -Real.log (x i)))
      _ = ((-∑ i : Fin n, Real.log (x i) : ℝ) : EReal) := by
            congr 1
            simp [Finset.sum_neg_distrib]
  · -- If one coordinate is nonpositive, its scalar barrier is `⊤`, so the whole sum is `⊤`.
    rw [if_neg hx]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    have hrest_ne_bot :
        Finset.sum (Finset.univ.erase i) (fun j : Fin n ↦ negative_log_barrier (x j)) ≠ ⊥ := by
      -- Every remaining scalar barrier stays away from `⊥`.
      exact finset_ereal_sum_ne_bot (Finset.univ.erase i)
        (fun j : Fin n ↦ negative_log_barrier (x j)) (fun j hj ↦ by
          by_cases hj' : 0 < x j
          · simp [negative_log_barrier, hj']
          · simp [negative_log_barrier, hj'])
    calc
      sum_negative_log_barrier n x
          = negative_log_barrier (x i) +
              Finset.sum (Finset.univ.erase i) (fun j : Fin n ↦ negative_log_barrier (x j)) := by
                rw [sum_negative_log_barrier]
                symm
                exact Finset.add_sum_erase Finset.univ
                  (fun j : Fin n ↦ negative_log_barrier (x j)) (Finset.mem_univ i)
      _ = ⊤ := by
            rw [show negative_log_barrier (x i) = ⊤ by simp [negative_log_barrier, hi]]
            exact EReal.top_add_of_ne_bot hrest_ne_bot

/-- On the positive orthant `positiveOrthant n`, the finite separable negative-log barrier is the
textbook finite sum `-∑ i, log (x i)`. -/
@[simp] theorem sum_negative_log_barrier_of_mem_positiveOrthant
    {x : E} (hx : x ∈ positiveOrthant n) :
    sum_negative_log_barrier n x = ((-∑ i : Fin n, Real.log (x i) : ℝ) : EReal) := by
  have hx' : ∀ i : Fin n, 0 < x i := by
    simpa [positiveOrthant] using hx
  rw [sum_negative_log_barrier_apply]
  simp [hx']

/-- Outside the positive orthant `positiveOrthant n`, the finite separable negative-log barrier is
`∞`. -/
@[simp] theorem sum_negative_log_barrier_of_not_mem_positiveOrthant
    {x : E} (hx : x ∉ positiveOrthant n) :
    sum_negative_log_barrier n x = (⊤ : EReal) := by
  have hx' : ¬ ∀ i : Fin n, 0 < x i := by
    simpa [positiveOrthant] using hx
  rw [sum_negative_log_barrier_apply]
  simp [hx']

/-- Helper for Proposition 4.15: summing the scalar conjugate formula from Proposition 4.8 over
the coordinates yields the textbook finite-dimensional formula. -/
lemma sum_negative_log_barrier_scalar_conjugates (y : E) :
    (∑ i : Fin n, if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤) =
      if ∀ i : Fin n, y i < 0 then
        ((-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) : EReal)
      else ⊤ := by
  classical
  by_cases hy : ∀ i : Fin n, y i < 0
  · -- If every coordinate is negative, the scalar finite values sum inside `EReal`.
    rw [if_pos hy]
    have hconst : (∑ _i : Fin n, (-1 : ℝ)) = -(n : ℝ) := by
      calc
        (∑ _i : Fin n, (-1 : ℝ)) = (Fintype.card (Fin n) : ℕ) • (-1 : ℝ) := by simp
        _ = -((Fintype.card (Fin n) : ℕ) : ℝ) := by
              rw [nsmul_eq_mul]
              ring
        _ = -(n : ℝ) := by simp
    have hreal :
        (∑ i : Fin n, (-1 - Real.log (-y i) : ℝ)) =
          (-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) := by
      -- Separate the constant `-1` contribution from the logarithmic sum.
      rw [Finset.sum_sub_distrib, hconst]
    calc
      (∑ i : Fin n, if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤)
          = ∑ i : Fin n, ((-1 - Real.log (-y i) : ℝ) : EReal) := by
              simp [hy]
      _ = (((∑ i : Fin n, (-1 - Real.log (-y i) : ℝ)) : ℝ) : EReal) := by
            symm
            simpa using
              (ereal_coe_finset_sum Finset.univ (fun i : Fin n ↦ -1 - Real.log (-y i)))
      _ = ((-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) : EReal) := by
            rw [hreal]
  · -- If one coordinate violates negativity, the corresponding scalar conjugate is `⊤`.
    rw [if_neg hy]
    obtain ⟨i, hi⟩ := not_forall.mp hy
    have hrest_ne_bot :
        Finset.sum (Finset.univ.erase i)
            (fun j : Fin n ↦ if y j < 0 then ((-1 - Real.log (-y j) : ℝ) : EReal) else ⊤) ≠ ⊥ :=
      by
        -- Each scalar conjugate value is either a real coercion or `⊤`, so never `⊥`.
        exact finset_ereal_sum_ne_bot (Finset.univ.erase i)
          (fun j : Fin n ↦ if y j < 0 then ((-1 - Real.log (-y j) : ℝ) : EReal) else ⊤)
          (fun j hj ↦ by
            by_cases hj' : y j < 0
            · simpa [hj'] using (EReal.coe_ne_bot (-1 - Real.log (-y j) : ℝ))
            · simp [hj'])
    calc
      (∑ i : Fin n, if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤)
          = (if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤) +
              Finset.sum (Finset.univ.erase i)
                (fun j : Fin n ↦ if y j < 0 then ((-1 - Real.log (-y j) : ℝ) : EReal) else ⊤) := by
                  symm
                  exact Finset.add_sum_erase Finset.univ
                    (fun j : Fin n ↦
                      if y j < 0 then ((-1 - Real.log (-y j) : ℝ) : EReal) else ⊤)
                    (Finset.mem_univ i)
      _ = ⊤ := by
            rw [show (if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤) = ⊤ by
                  simp [hi]]
            exact EReal.top_add_of_ne_bot hrest_ne_bot

-- Proof sketch: apply the Chapter 4 bridge
-- `conjugate_function_separable_sum_eq_sum_conjugate_function` to the separable sum
-- `x ↦ ∑ i, negative_log_barrier (x i)` and the coordinate dual family
-- `i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)`. Then use Proposition 4.8 coordinatewise. If every
-- `y i < 0`, the scalar conjugates sum to `-n - ∑ i, log (-y i)`; if some `y i ≥ 0`, one scalar
-- conjugate is `⊤`, so the whole sum is `⊤`.
/-- Proposition 4.15: the Fenchel conjugate of the separable sum of the scalar negative-log
barrier, equivalently by [sum_negative_log_barrier_apply] the textbook barrier
`x ↦ -∑ i, log (x i)` on `positiveOrthant n` and `∞` outside, is `-n - ∑ i, log (-y i)` on the
negative orthant and `∞` otherwise. The dual argument is expressed through the Euclidean pairing
`dotProductEquiv`. -/
theorem sum_negative_log_barrier_conjugate_eq
    (y : E) :
    conjugate_function (sum_negative_log_barrier n) (dotProductEquiv ℝ (Fin n) y) =
      if ∀ i : Fin n, y i < 0 then
        ((-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) : EReal)
      else ⊤ := by
  have hseparable :
      conjugate_function (sum_negative_log_barrier n)
          (LinearMap.lsum ℝ (fun _ : Fin n ↦ ℝ) ℝ
            (fun i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i))) =
        ∑ i : Fin n, conjugate_function negative_log_barrier
          (LinearMap.toSpanSingleton ℝ ℝ (y i)) := by
    -- Rewrite the textbook barrier as a separable sum and apply Theorem 4.3.
    simpa [sum_negative_log_barrier] using
      (conjugate_function_separable_sum_eq_sum_conjugate_function
        (f := fun _ : Fin n ↦ negative_log_barrier)
        (h_proper := fun _ ↦ isProperExtendedRealFunction_negative_log_barrier)
        (y := fun i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)))
  -- Convert the Euclidean pairing dual into the product dual used by Theorem 4.3.
  rw [← lsum_toSpanSingleton_eq_dotProductEquiv y, hseparable]
  calc
    (∑ i : Fin n, conjugate_function negative_log_barrier
        (LinearMap.toSpanSingleton ℝ ℝ (y i)))
        = ∑ i : Fin n, if y i < 0 then ((-1 - Real.log (-y i) : ℝ) : EReal) else ⊤ := by
            -- Identify each scalar conjugate with Proposition 4.8.
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [toSpanSingletonReal_eq_toDualMap]
            simpa [conjugate_function_primal_apply] using negative_log_barrier_conjugate_eq (y i)
    _ = if ∀ i : Fin n, y i < 0 then
          ((-(n : ℝ) - ∑ i : Fin n, Real.log (-y i) : ℝ) : EReal)
        else ⊤ := sum_negative_log_barrier_scalar_conjugates y

end
