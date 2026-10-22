/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Matrix.Dual

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

noncomputable section

/- Proposition 4.4 is `source-facing`. Its owner abstractions already exist upstream in the
project: `extendedIndicator` from Chapter 2, `support_function` from Chapter 2,
`conjugate_function` from Definition 4.1, and the coordinatewise max function
`coordinatewiseMax` from Chapter 3. Because this file stays on the coordinate model `Fin n → ℝ`,
the Euclidean pairing enters through the explicit bridge `dotProductEquiv`. The main proposition is
therefore the coordinate-space function equality, and the pointwise rewrite lemmas below are its
usable companion API. -/

-- Proof sketch: `support_function_unit_simplex_eq_coordinate_max` already identifies the support
-- function of the standard simplex with the coordinate supremum. Rewrite that supremum using the
-- project owner `coordinatewiseMax`.
/-- Helper for Proposition 4.4: the coordinatewise maximum of a constant vector is that constant. -/
lemma coordinatewiseMax_const {n : ℕ} [Nonempty (Fin n)] (c : ℝ) :
    coordinatewiseMax (fun _ : Fin n ↦ c) = c := by
  -- Rewrite the maximum as the finite supremum over `Finset.univ`.
  rw [coordinatewiseMax_eq_sup']
  simp

/-- Helper for Proposition 4.4: pairing `y` with a constant vector scales the coordinate sum of
`y` by that constant. -/
lemma dotProductEquiv_apply_const {n : ℕ} (y : Fin n → ℝ) (c : ℝ) :
    ((dotProductEquiv ℝ (Fin n) y) (fun _ ↦ c) : ℝ) = c * ∑ i, y i := by
  -- Expand the dot product and factor the constant out of the finite sum.
  calc
    ((dotProductEquiv ℝ (Fin n) y) (fun _ ↦ c) : ℝ)
        = dotProduct y (fun _ ↦ c) := by
            simp [dotProductEquiv]
    _ = ∑ i, y i * c := by
          simp [dotProduct]
    _ = (∑ i, y i) * c := by
          rw [Finset.sum_mul]
    _ = c * ∑ i, y i := by
          ring

/-- The coordinatewise maximum is the support function of the standard simplex. -/
theorem coordinatewiseMax_eq_support_function_stdSimplex {n : ℕ} [Nonempty (Fin n)]
    (x : Fin n → ℝ) :
    (coordinatewiseMax x : EReal) =
      support_function (stdSimplex ℝ (Fin n)) (dotProductEquiv ℝ (Fin n) x) := by
  obtain ⟨i0, hi0⟩ := Finite.exists_max x
  rw [support_function_apply]
  apply le_antisymm
  · have hmax_le : (coordinatewiseMax x : EReal) ≤ x i0 := by
      -- The maximizing coordinate `i0` bounds the coordinatewise supremum from above.
      exact_mod_cast
        (show coordinatewiseMax x ≤ x i0 from by
          rw [coordinatewiseMax_eq_sup']
          exact Finset.sup'_le Finset.univ_nonempty x (fun i _ ↦ hi0 i))
    refine hmax_le.trans ?_
    -- Evaluate the support function at the simplex vertex selecting the maximizing coordinate.
    refine le_sSup ?_
    refine ⟨Pi.single i0 1, single_mem_stdSimplex ℝ i0, ?_⟩
    simp [dotProductEquiv]
  · apply sSup_le
    rintro _ ⟨z, hz, rfl⟩
    have hdot : dotProduct x z ≤ coordinatewiseMax x := by
      -- Every simplex point is a convex combination of the coordinates of `x`.
      calc
        dotProduct x z = ∑ i, x i * z i := by
          simp [dotProduct]
        _ ≤ ∑ i, coordinatewiseMax x * z i := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          exact mul_le_mul_of_nonneg_right (le_coordinatewiseMax x i) (hz.1 i)
        _ = coordinatewiseMax x * ∑ i, z i := by
          rw [Finset.mul_sum]
        _ = coordinatewiseMax x := by
          rw [hz.2, mul_one]
    have hdotE : ((dotProduct x z : ℝ) : EReal) ≤ (coordinatewiseMax x : EReal) := by
      exact_mod_cast hdot
    simpa [dotProductEquiv] using hdotE

-- Proof sketch: rewrite `fun x ↦ (coordinatewiseMax x : EReal)` as the support function of the
-- standard simplex using `coordinatewiseMax_eq_support_function_stdSimplex`. Then identify the
-- conjugate of that support function with the indicator of the simplex; because the standard
-- simplex is closed and convex, the general support-function conjugacy formula specializes to
-- `extendedIndicator (stdSimplex ℝ (Fin n))`.
/-- Proposition 4.4: for the function `f(x) = max {x_1, x_2, ..., x_n}` on `ℝ^n`, the Fenchel
conjugate, expressed on `ℝ^n` through the Euclidean pairing `dotProductEquiv`, is the indicator
function of the standard simplex `Δ_n`. -/
theorem conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex {n : ℕ}
    [Nonempty (Fin n)] :
    (fun y : Fin n → ℝ ↦
      conjugate_function (fun x : Fin n → ℝ ↦ (coordinatewiseMax x : EReal))
        (dotProductEquiv ℝ (Fin n) y)) =
      extendedIndicator (stdSimplex ℝ (Fin n)) := by
  funext y
  by_cases hy : y ∈ stdSimplex ℝ (Fin n)
  · rw [extendedIndicator_of_mem hy, conjugate_function_apply]
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, rfl⟩
      have hdot : dotProduct y x ≤ coordinatewiseMax x := by
        -- Simplex weights form a convex combination of the coordinates of `x`.
        calc
          dotProduct y x = ∑ i, y i * x i := by
            simp [dotProduct]
          _ ≤ ∑ i, y i * coordinatewiseMax x := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            exact mul_le_mul_of_nonneg_left (le_coordinatewiseMax x i) (hy.1 i)
          _ = (∑ i, y i) * coordinatewiseMax x := by
            rw [← Finset.sum_mul]
          _ = coordinatewiseMax x := by
            rw [hy.2, one_mul]
      have hdotE :
          (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) ≤ (coordinatewiseMax x : EReal) := by
        have hreal : ((dotProduct y x : ℝ) : EReal) ≤ (coordinatewiseMax x : EReal) := by
          exact_mod_cast hdot
        simpa [dotProductEquiv] using hreal
      change (((((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x : ℝ) : EReal) ≤ 0)
      have hsub : ((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x ≤ 0 := by
        simpa [dotProductEquiv] using sub_nonpos.mpr hdot
      exact_mod_cast hsub
    · refine le_sSup ?_
      refine ⟨0, ?_⟩
      simp [dotProductEquiv, coordinatewiseMax]
  · rw [extendedIndicator_of_not_mem hy, conjugate_function_apply]
    by_cases hsum : ∑ i, y i = 1
    · have hneg : ∃ j : Fin n, y j < 0 := by
        by_contra hnonneg
        apply hy
        refine ⟨?_, hsum⟩
        intro i
        exact le_of_not_gt (fun hi ↦ hnonneg ⟨i, hi⟩)
      rcases hneg with ⟨j, hyj⟩
      have hother : ∃ k : Fin n, k ≠ j := by
        by_contra hnot
        have huniq : ∀ k : Fin n, k = j := by
          intro k
          by_contra hkj
          exact hnot ⟨k, hkj⟩
        have huniv : (Finset.univ : Finset (Fin n)) = {j} := by
          ext b
          simp [huniq b]
        have hsum_single : ∑ i : Fin n, y i = y j := by
          rw [huniv]
          simp
        linarith [hyj, hsum, hsum_single]
      rcases hother with ⟨k, hkj⟩
      let gap : ℝ := -y j
      have hgap : 0 < gap := by
        simpa [gap] using neg_pos.mpr hyj
      refine (sSup_eq_top).2 ?_
      intro b hb
      rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
      obtain ⟨m, hm⟩ := exists_nat_gt (r / gap)
      have hr_lt : r < (m : ℝ) * gap := by
        have hm' : r / gap < (m : ℝ) := by
          exact_mod_cast hm
        exact (div_lt_iff₀ hgap).1 hm'
      let x : Fin n → ℝ := Pi.single j (-(m : ℝ))
      have hxmax : coordinatewiseMax x = 0 := by
        -- The selected coordinate is negative and the other witness coordinate stays at `0`.
        rw [coordinatewiseMax_eq_sup']
        apply le_antisymm
        · refine Finset.sup'_le Finset.univ_nonempty x ?_
          intro i hi
          by_cases hij : i = j
          · simp [x, hij]
          · simp [x, hij]
        · simpa [x, hkj] using
            (Finset.le_sup' (s := Finset.univ) (f := x) (Finset.mem_univ k))
      have hvalue :
          (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) =
            (((m : ℝ) * gap : ℝ) : EReal) := by
        have hreal :
            ((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x = (m : ℝ) * gap := by
          rw [hxmax]
          have hdot :
              ((dotProductEquiv ℝ (Fin n) y) x : ℝ) = -(y j * (m : ℝ)) := by
            calc
              ((dotProductEquiv ℝ (Fin n) y) x : ℝ)
                  = dotProduct y x := by
                      simp [dotProductEquiv]
              _ = -(y j * (m : ℝ)) := by
                    rw [dotProduct]
                    rw [Finset.sum_eq_single j]
                    · simp [x]
                    · intro i hi hij
                      simp [x, hij]
                    · intro hj
                      exact (hj (Finset.mem_univ j)).elim
          rw [hdot]
          dsimp [gap]
          ring
        change (((((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x : ℝ) : EReal) =
            (((m : ℝ) * gap : ℝ) : EReal))
        exact_mod_cast hreal
      refine ⟨_, Set.mem_range.mpr ⟨x, rfl⟩, ?_⟩
      calc
        b < (r : EReal) := hbr
        _ < (((m : ℝ) * gap : ℝ) : EReal) := by
          exact_mod_cast hr_lt
        _ = (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) := by
          simpa using hvalue.symm
    · have hsum_lt_or_gt : ∑ i, y i < 1 ∨ 1 < ∑ i, y i := by
        exact lt_or_gt_of_ne hsum
      rcases hsum_lt_or_gt with hsum_lt | hsum_gt
      · let gap : ℝ := 1 - ∑ i, y i
        have hgap : 0 < gap := by
          dsimp [gap]
          linarith
        refine (sSup_eq_top).2 ?_
        intro b hb
        rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
        obtain ⟨m, hm⟩ := exists_nat_gt (r / gap)
        have hr_lt : r < (m : ℝ) * gap := by
          have hm' : r / gap < (m : ℝ) := by
            exact_mod_cast hm
          exact (div_lt_iff₀ hgap).1 hm'
        let x : Fin n → ℝ := fun _ ↦ -(m : ℝ)
        have hvalue :
            (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) =
              (((m : ℝ) * gap : ℝ) : EReal) := by
          have hreal :
              ((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x = (m : ℝ) * gap := by
            rw [dotProductEquiv_apply_const, coordinatewiseMax_const]
            dsimp [x, gap]
            ring
          change (((((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x : ℝ) : EReal) =
              (((m : ℝ) * gap : ℝ) : EReal))
          exact_mod_cast hreal
        refine ⟨_, Set.mem_range.mpr ⟨x, rfl⟩, ?_⟩
        calc
          b < (r : EReal) := hbr
          _ < (((m : ℝ) * gap : ℝ) : EReal) := by
            exact_mod_cast hr_lt
          _ = (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) := by
            simpa using hvalue.symm
      · let gap : ℝ := ∑ i, y i - 1
        have hgap : 0 < gap := by
          dsimp [gap]
          linarith
        refine (sSup_eq_top).2 ?_
        intro b hb
        rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
        obtain ⟨m, hm⟩ := exists_nat_gt (r / gap)
        have hr_lt : r < (m : ℝ) * gap := by
          have hm' : r / gap < (m : ℝ) := by
            exact_mod_cast hm
          exact (div_lt_iff₀ hgap).1 hm'
        let x : Fin n → ℝ := fun _ ↦ (m : ℝ)
        have hvalue :
            (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) =
              (((m : ℝ) * gap : ℝ) : EReal) := by
          have hreal :
              ((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x = (m : ℝ) * gap := by
            rw [dotProductEquiv_apply_const, coordinatewiseMax_const]
            dsimp [x, gap]
            ring
          change (((((dotProductEquiv ℝ (Fin n) y) x : ℝ) - coordinatewiseMax x : ℝ) : EReal) =
              (((m : ℝ) * gap : ℝ) : EReal))
          exact_mod_cast hreal
        refine ⟨_, Set.mem_range.mpr ⟨x, rfl⟩, ?_⟩
        calc
          b < (r : EReal) := hbr
          _ < (((m : ℝ) * gap : ℝ) : EReal) := by
            exact_mod_cast hr_lt
          _ = (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - (coordinatewiseMax x : EReal) := by
            simpa using hvalue.symm

-- Proof sketch: evaluate the function equality
-- `conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex` at `y`.
/-- Pointwise form of Proposition 4.4. -/
theorem conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex_apply {n : ℕ}
    [Nonempty (Fin n)] (y : Fin n → ℝ) :
    conjugate_function (fun x : Fin n → ℝ ↦ (coordinatewiseMax x : EReal))
        (dotProductEquiv ℝ (Fin n) y) =
      extendedIndicator (stdSimplex ℝ (Fin n)) y := by
  simpa using
    congrArg (fun f : (Fin n → ℝ) → EReal ↦ f y)
      conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex

-- Proof sketch: combine the pointwise conjugacy formula with the defining values of
-- `extendedIndicator` on and off the simplex.
section

attribute [local instance] Classical.propDecidable

/-- The conjugate of the coordinatewise maximum is `0` on `stdSimplex ℝ (Fin n)` and `∞`
outside it. -/
theorem conjugate_coordinatewiseMax_eq_if_mem_stdSimplex {n : ℕ} [Nonempty (Fin n)]
    (y : Fin n → ℝ) :
    conjugate_function (fun x : Fin n → ℝ ↦ (coordinatewiseMax x : EReal))
        (dotProductEquiv ℝ (Fin n) y) =
      if y ∈ stdSimplex ℝ (Fin n) then (0 : EReal) else ⊤ := by
  by_cases hy : y ∈ stdSimplex ℝ (Fin n)
  · simpa [hy] using
      conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex_apply y
  · simpa [hy] using
      conjugate_coordinatewiseMax_eq_extendedIndicator_stdSimplex_apply y

end
