/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap14.Lemma_14_1

-- Declarations for this item will be appended below by the statement pipeline.

section

/- Definition 14.3 is `source-facing`: the textbook item first gives Powell's explicit
three-variable formula. For the coordinate-section minimizer sets, the relevant Chapter 14 owner
abstraction is the fixed-base block argmin set `alternating_minimization_argmin` from Lemma 14.1.
Accordingly, the primitive data here are just the curried scalar formula together with its thin
`bridge/view` to the Chapter 14 block-objective API on `Fin 3 → ℝ`; the `x`, `y`, and `z`
section argmin sets are derived API and should be stated through that owner rather than as
separate local set definitions. -/

/-- Definition 14.3: Powell's example objective for the failure of alternating minimization,
defined by
`φ(x, y, z) = -xy - yz - zx + [x - 1]_+^2 + [-x - 1]_+^2 + [y - 1]_+^2 + [-y - 1]_+^2 +
[z - 1]_+^2 + [-z - 1]_+^2`. -/
def powell_example_objective (x y z : ℝ) : ℝ :=
  -(x * y) - y * z - z * x +
    (x - 1)⁺ ^ 2 + (-x - 1)⁺ ^ 2 +
    (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 +
    (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2

local notation "φ" => powell_example_objective

/-- The Chapter 14 block-objective view of Powell's example, obtained by regarding the displayed
three-variable formula as an extended-real function on `Fin 3 → ℝ`. This is the canonical bridge
to `alternating_minimization_argmin`. -/
def powell_example (u : Fin 3 → ℝ) : EReal :=
  (φ (u 0) (u 1) (u 2) : EReal)

/-- Evaluating `powell_example` on the block vector `![x, y, z]` recovers the original
three-variable objective, viewed in `EReal`. -/
@[simp] theorem powell_example_apply (x y z : ℝ) :
    powell_example ![x, y, z] = (φ x y z : EReal) := by
  simp [powell_example]

-- Proof sketch: unfold `φ` at `(x, y, z)` and read off the displayed scalar formula.
/-- Evaluating `powell_example_objective` at `(x, y, z)` reproduces the displayed formula for
Powell's example. -/
@[simp] theorem powell_example_objective_apply (x y z : ℝ) :
    φ x y z =
      -(x * y) - y * z - z * x +
        (x - 1)⁺ ^ 2 + (-x - 1)⁺ ^ 2 +
        (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 +
        (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2 := rfl

-- Proof sketch: expand both sides with `powell_example_objective_apply`, then use commutativity
-- of addition and multiplication to match the cyclically permuted terms.
/-- Powell's example objective is invariant under the cyclic permutation
`(x, y, z) ↦ (y, z, x)`. -/
theorem powell_example_objective_cyclic (x y z : ℝ) :
    φ x y z = φ y z x := by
  -- Expand the displayed formula and reorder the cyclically permuted summands.
  unfold powell_example_objective
  ring_nf

/-- Helper for Definition 14.3: the one-dimensional Powell slice with linear parameter `a`. -/
def powell_scalar_slice (a x : ℝ) : ℝ :=
  -a * x + (x - 1)⁺ ^ 2 + (-x - 1)⁺ ^ 2

/-- Helper for Definition 14.3: on the left region `x ≤ -1`, only the `[-x - 1]_+^2` penalty is
active. -/
lemma powell_scalar_slice_of_le_neg_one {a x : ℝ} (hx : x ≤ -1) :
    powell_scalar_slice a x = -a * x + (x + 1) ^ 2 := by
  -- On `x ≤ -1`, `x - 1 ≤ 0` and `-x - 1 ≥ 0`, so the two positive-part terms simplify.
  have hx1 : x - 1 ≤ 0 := by linarith
  have hx2 : 0 ≤ -x - 1 := by linarith
  rw [powell_scalar_slice, posPart_eq_zero.2 hx1, posPart_eq_self.2 hx2]
  ring

/-- Helper for Definition 14.3: on the middle region `[-1, 1]`, both penalty terms vanish. -/
lemma powell_scalar_slice_of_mem_Icc {a x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    powell_scalar_slice a x = -a * x := by
  -- Inside `[-1, 1]`, both arguments of the positive-part operator are nonpositive.
  have hx1 : x - 1 ≤ 0 := by linarith [hx.2]
  have hx2 : -x - 1 ≤ 0 := by linarith [hx.1]
  rw [powell_scalar_slice, posPart_eq_zero.2 hx1, posPart_eq_zero.2 hx2]
  simp

/-- Helper for Definition 14.3: on the right region `1 ≤ x`, only the `[x - 1]_+^2` penalty is
active. -/
lemma powell_scalar_slice_of_one_le {a x : ℝ} (hx : 1 ≤ x) :
    powell_scalar_slice a x = -a * x + (x - 1) ^ 2 := by
  -- On `1 ≤ x`, `x - 1 ≥ 0` and `-x - 1 ≤ 0`, so only the right penalty remains.
  have hx1 : 0 ≤ x - 1 := by linarith
  have hx2 : -x - 1 ≤ 0 := by linarith
  rw [powell_scalar_slice, posPart_eq_self.2 hx1, posPart_eq_zero.2 hx2]
  simp

/-- Helper for Definition 14.3: for positive `a`, the right-hand candidate `1 + a / 2` has the
expected scalar-slice value. -/
lemma powell_scalar_slice_pos_candidate {a : ℝ} (ha : 0 < a) :
    powell_scalar_slice a (1 + a / 2) = -a - a ^ 2 / 4 := by
  -- The positive candidate lies in the right active region, so the slice is a completed square.
  have hc : 1 ≤ 1 + a / 2 := by linarith
  rw [powell_scalar_slice_of_one_le (a := a) hc]
  ring

/-- Helper for Definition 14.3: for negative `a`, the left-hand candidate `-1 + a / 2` has the
expected scalar-slice value. -/
lemma powell_scalar_slice_neg_candidate {a : ℝ} (ha : a < 0) :
    powell_scalar_slice a (-1 + a / 2) = a - a ^ 2 / 4 := by
  -- The negative candidate lies in the left active region, so the slice is again a completed
  -- square after simplification.
  have hc : -1 + a / 2 ≤ -1 := by linarith
  rw [powell_scalar_slice_of_le_neg_one (a := a) hc]
  ring

/-- Helper for Definition 14.3: adding a finite real constant does not change global minimizers on
`Set.univ` after coercing to `EReal`. -/
lemma isMinOn_univ_ereal_add_const_iff {α : Type*} (f : α → ℝ) (c : ℝ) (x : α) :
    IsMinOn (fun t ↦ ((f t + c : ℝ) : EReal)) Set.univ x ↔
      IsMinOn (fun t ↦ ((f t : ℝ) : EReal)) Set.univ x := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hx t
    -- Cancel the common constant by moving the `EReal` inequality back to `ℝ`.
    have hxt : ((f x + c : ℝ) : EReal) ≤ ((f t + c : ℝ) : EReal) := hx t
    have hxt' : f x + c ≤ f t + c := by
      exact_mod_cast hxt
    have hcancel : f x ≤ f t := (add_le_add_iff_right c).mp hxt'
    exact_mod_cast hcancel
  · intro hx t
    -- Reinsert the same constant after proving the real inequality.
    have hxt : ((f x : ℝ) : EReal) ≤ ((f t : ℝ) : EReal) := hx t
    have hxt' : f x ≤ f t := by
      exact_mod_cast hxt
    have hshift : f x + c ≤ f t + c := (add_le_add_iff_right c).mpr hxt'
    exact_mod_cast hshift

/-- Helper for Definition 14.3: updating the first coordinate exposes Powell's objective as the
scalar slice with parameter `y + z`, plus a constant depending only on the frozen coordinates. -/
lemma powell_example_update_zero_apply (t y z : ℝ) :
    powell_example (Function.update ![0, y, z] 0 t) =
      ((powell_scalar_slice (y + z) t +
        (-y * z + (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 + (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2) : ℝ) : EReal) := by
  -- Expanding the update shows that only the linear coefficient of `t` changes; the remaining
  -- terms are constant in the first-coordinate slice.
  have hupdate : Function.update ![0, y, z] 0 t = ![t, y, z] := by
    ext j
    fin_cases j <;> simp [Function.update]
  rw [hupdate, powell_example_apply]
  have hreal :
      φ t y z =
        powell_scalar_slice (y + z) t +
          (-y * z + (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 + (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2) := by
    unfold powell_example_objective powell_scalar_slice
    ring
  have hrealE :
      ((φ t y z : ℝ) : EReal) =
        ((powell_scalar_slice (y + z) t +
          (-y * z + (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 + (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2) : ℝ) : EReal) := by
    exact_mod_cast hreal
  simpa [powell_example_objective] using hrealE

/-- Helper for Definition 14.3: every point of `[-1, 1]` minimizes the zero-parameter scalar
slice. -/
lemma powell_scalar_slice_zero_isMinOn {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    IsMinOn (fun t ↦ ((powell_scalar_slice 0 t : ℝ) : EReal)) Set.univ x := by
  -- On the central interval the slice value is `0`, while away from the interval the slice is a
  -- sum of squares.
  rw [isMinOn_univ_iff]
  intro t
  have hx0 : powell_scalar_slice 0 x = 0 := by
    simp [powell_scalar_slice_of_mem_Icc (a := 0) hx]
  have ht_nonneg : 0 ≤ powell_scalar_slice 0 t := by
    rw [powell_scalar_slice]
    nlinarith [sq_nonneg ((t - 1)⁺), sq_nonneg ((-t - 1)⁺)]
  simpa [hx0] using ht_nonneg

/-- Helper for Definition 14.3: the zero-parameter scalar slice has `[-1, 1]` as its full
minimizer set. -/
lemma powell_scalar_slice_isMinOn_zero_iff {x : ℝ} :
    IsMinOn (fun t ↦ ((powell_scalar_slice 0 t : ℝ) : EReal)) Set.univ x ↔
      x ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · intro hx
    -- Compare the putative minimizer with the boundary points `1` and `-1`.
    rw [isMinOn_univ_iff] at hx
    by_cases hx1 : x ≤ 1
    · by_cases hneg1 : -1 ≤ x
      · exact ⟨hneg1, hx1⟩
      · have hxlt : x < -1 := by linarith
        have hxmin :
            ((powell_scalar_slice 0 x : ℝ) : EReal) ≤
              ((powell_scalar_slice 0 (-1) : ℝ) : EReal) :=
          hx (-1)
        have hxmin' : powell_scalar_slice 0 x ≤ powell_scalar_slice 0 (-1) := by
          exact_mod_cast hxmin
        have hvalx : powell_scalar_slice 0 x = (x + 1) ^ 2 := by
          rw [powell_scalar_slice_of_le_neg_one (a := 0) (show x ≤ -1 by linarith)]
          ring
        have hvalm1 : powell_scalar_slice 0 (-1) = 0 := by
          rw [powell_scalar_slice_of_mem_Icc (a := 0) (by constructor <;> norm_num)]
          ring
        have hsquare : 0 < (x + 1) ^ 2 := by
          nlinarith
        rw [hvalx, hvalm1] at hxmin'
        linarith
    · have hxgt : 1 < x := by linarith
      have hxmin :
          ((powell_scalar_slice 0 x : ℝ) : EReal) ≤
            ((powell_scalar_slice 0 1 : ℝ) : EReal) :=
        hx 1
      have hxmin' : powell_scalar_slice 0 x ≤ powell_scalar_slice 0 1 := by
        exact_mod_cast hxmin
      have hvalx : powell_scalar_slice 0 x = (x - 1) ^ 2 := by
        rw [powell_scalar_slice_of_one_le (a := 0) (show 1 ≤ x by linarith)]
        ring
      have hval1 : powell_scalar_slice 0 1 = 0 := by
        rw [powell_scalar_slice_of_mem_Icc (a := 0) (by constructor <;> norm_num)]
        ring
      have hsquare : 0 < (x - 1) ^ 2 := by
        nlinarith
      rw [hvalx, hval1] at hxmin'
      linarith
  · intro hx
    -- The forward direction is the direct interval-minimizer statement above.
    exact powell_scalar_slice_zero_isMinOn hx

/-- Helper for Definition 14.3: for positive `a`, the point `1 + a / 2` minimizes the scalar
slice globally. -/
lemma powell_scalar_slice_pos_isMinOn {a : ℝ} (ha : 0 < a) :
    IsMinOn (fun t ↦ ((powell_scalar_slice a t : ℝ) : EReal)) Set.univ (1 + a / 2) := by
  -- Split the competitor `x` into the three textbook regions and compare against the completed
  -- square centered at `1 + a / 2`.
  rw [isMinOn_univ_iff]
  intro x
  have hvalc : powell_scalar_slice a (1 + a / 2) = -a - a ^ 2 / 4 :=
    powell_scalar_slice_pos_candidate ha
  by_cases hxneg : x ≤ -1
  · have hvalx : powell_scalar_slice a x = -a * x + (x + 1) ^ 2 :=
      powell_scalar_slice_of_le_neg_one (a := a) hxneg
    have hlin : 0 ≤ a * (1 - x) := by
      have hx1 : 0 ≤ 1 - x := by linarith
      exact mul_nonneg ha.le hx1
    have hcomp : -a - a ^ 2 / 4 ≤ -a * x + (x + 1) ^ 2 := by
      nlinarith [sq_nonneg (x + 1), hlin]
    have hcompE :
        (((-a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x + (x + 1) ^ 2 : ℝ)) : EReal) := by
      exact_mod_cast hcomp
    simpa [hvalc, hvalx] using hcompE
  · by_cases hxone : x ≤ 1
    · have hmid : x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      have hvalx : powell_scalar_slice a x = -a * x :=
        powell_scalar_slice_of_mem_Icc (a := a) hmid
      have hlin : 0 ≤ a * (1 - x) := by
        have hx1 : 0 ≤ 1 - x := by linarith
        exact mul_nonneg ha.le hx1
      have hcomp : -a - a ^ 2 / 4 ≤ -a * x := by
        nlinarith [hlin]
      have hcompE : (((-a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x : ℝ)) : EReal) := by
        exact_mod_cast hcomp
      simpa [hvalc, hvalx] using hcompE
    · have hxge : 1 ≤ x := by linarith
      have hvalx : powell_scalar_slice a x = -a * x + (x - 1) ^ 2 :=
        powell_scalar_slice_of_one_le (a := a) hxge
      have hcomp : -a - a ^ 2 / 4 ≤ -a * x + (x - 1) ^ 2 := by
        nlinarith [sq_nonneg (x - (1 + a / 2))]
      have hcompE :
          (((-a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x + (x - 1) ^ 2 : ℝ)) : EReal) := by
        exact_mod_cast hcomp
      simpa [hvalc, hvalx] using hcompE

/-- Helper for Definition 14.3: for positive `a`, the scalar slice has the unique minimizer
`1 + a / 2`. -/
lemma powell_scalar_slice_isMinOn_pos_iff {a x : ℝ} (ha : 0 < a) :
    IsMinOn (fun t ↦ ((powell_scalar_slice a t : ℝ) : EReal)) Set.univ x ↔
      x = 1 + a / 2 := by
  constructor
  · intro hx
    -- Compare a putative minimizer with the known minimizer and rule out the two off-center
    -- regions by strict positivity of the gap.
    have hc := powell_scalar_slice_pos_isMinOn ha
    rw [isMinOn_univ_iff] at hx hc
    have hxc : ((powell_scalar_slice a x : ℝ) : EReal) ≤
        ((powell_scalar_slice a (1 + a / 2) : ℝ) : EReal) := hx (1 + a / 2)
    have hcx : ((powell_scalar_slice a (1 + a / 2) : ℝ) : EReal) ≤
        ((powell_scalar_slice a x : ℝ) : EReal) := hc x
    have hxc' : powell_scalar_slice a x ≤ powell_scalar_slice a (1 + a / 2) := by
      exact_mod_cast hxc
    have hcx' : powell_scalar_slice a (1 + a / 2) ≤ powell_scalar_slice a x := by
      exact_mod_cast hcx
    have heq : powell_scalar_slice a x = powell_scalar_slice a (1 + a / 2) :=
      le_antisymm hxc' hcx'
    have hvalc : powell_scalar_slice a (1 + a / 2) = -a - a ^ 2 / 4 :=
      powell_scalar_slice_pos_candidate ha
    by_cases hxneg : x ≤ -1
    · have hvalx : powell_scalar_slice a x = -a * x + (x + 1) ^ 2 :=
        powell_scalar_slice_of_le_neg_one (a := a) hxneg
      have hlin : 0 ≤ a * (1 - x) := by
        have hx1 : 0 ≤ 1 - x := by linarith
        exact mul_nonneg ha.le hx1
      have hapos : 0 < a ^ 2 / 4 := by
        nlinarith
      rw [hvalx, hvalc] at heq
      nlinarith [sq_nonneg (x + 1), hlin, hapos]
    · by_cases hxone : x ≤ 1
      · have hmid : x ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor <;> linarith
        have hvalx : powell_scalar_slice a x = -a * x :=
          powell_scalar_slice_of_mem_Icc (a := a) hmid
        have hlin : 0 ≤ a * (1 - x) := by
          have hx1 : 0 ≤ 1 - x := by linarith
          exact mul_nonneg ha.le hx1
        have hapos : 0 < a ^ 2 / 4 := by
          nlinarith
        rw [hvalx, hvalc] at heq
        nlinarith [hlin, hapos]
      · have hxge : 1 ≤ x := by linarith
        have hvalx : powell_scalar_slice a x = -a * x + (x - 1) ^ 2 :=
          powell_scalar_slice_of_one_le (a := a) hxge
        rw [hvalx, hvalc] at heq
        have hsquare : (x - (1 + a / 2)) ^ 2 = 0 := by
          nlinarith
        nlinarith [sq_nonneg (x - (1 + a / 2)), hsquare]
  · intro hx
    -- The reverse implication is the explicit minimizer statement already proved.
    simpa [hx] using powell_scalar_slice_pos_isMinOn ha

/-- Helper for Definition 14.3: for negative `a`, the point `-1 + a / 2` minimizes the scalar
slice globally. -/
lemma powell_scalar_slice_neg_isMinOn {a : ℝ} (ha : a < 0) :
    IsMinOn (fun t ↦ ((powell_scalar_slice a t : ℝ) : EReal)) Set.univ (-1 + a / 2) := by
  -- Split the competitor `x` into the same three regions, now centered at the left-hand
  -- completed-square minimizer.
  rw [isMinOn_univ_iff]
  intro x
  have hvalc : powell_scalar_slice a (-1 + a / 2) = a - a ^ 2 / 4 :=
    powell_scalar_slice_neg_candidate ha
  by_cases hxneg : x ≤ -1
  · have hvalx : powell_scalar_slice a x = -a * x + (x + 1) ^ 2 :=
      powell_scalar_slice_of_le_neg_one (a := a) hxneg
    have hcomp : a - a ^ 2 / 4 ≤ -a * x + (x + 1) ^ 2 := by
      nlinarith [sq_nonneg (x - (-1 + a / 2))]
    have hcompE :
        (((a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x + (x + 1) ^ 2 : ℝ)) : EReal) := by
      exact_mod_cast hcomp
    simpa [hvalc, hvalx] using hcompE
  · by_cases hxone : x ≤ 1
    · have hmid : x ∈ Set.Icc (-1 : ℝ) 1 := by
        constructor <;> linarith
      have hvalx : powell_scalar_slice a x = -a * x :=
        powell_scalar_slice_of_mem_Icc (a := a) hmid
      have hlin : 0 ≤ (-a) * (x + 1) := by
        have hx1 : 0 ≤ x + 1 := by linarith
        exact mul_nonneg (by linarith : 0 ≤ -a) hx1
      have hcomp : a - a ^ 2 / 4 ≤ -a * x := by
        nlinarith [hlin]
      have hcompE : (((a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x : ℝ)) : EReal) := by
        exact_mod_cast hcomp
      simpa [hvalc, hvalx] using hcompE
    · have hxge : 1 ≤ x := by linarith
      have hvalx : powell_scalar_slice a x = -a * x + (x - 1) ^ 2 :=
        powell_scalar_slice_of_one_le (a := a) hxge
      have hlin : 0 ≤ (-a) * (x + 1) := by
        have hx1 : 0 ≤ x + 1 := by linarith
        exact mul_nonneg (by linarith : 0 ≤ -a) hx1
      have hcomp : a - a ^ 2 / 4 ≤ -a * x + (x - 1) ^ 2 := by
        nlinarith [sq_nonneg (x - 1), hlin]
      have hcompE :
          (((a - a ^ 2 / 4 : ℝ)) : EReal) ≤ (((-a * x + (x - 1) ^ 2 : ℝ)) : EReal) := by
        exact_mod_cast hcomp
      simpa [hvalc, hvalx] using hcompE

/-- Helper for Definition 14.3: for negative `a`, the scalar slice has the unique minimizer
`-1 + a / 2`. -/
lemma powell_scalar_slice_isMinOn_neg_iff {a x : ℝ} (ha : a < 0) :
    IsMinOn (fun t ↦ ((powell_scalar_slice a t : ℝ) : EReal)) Set.univ x ↔
      x = -1 + a / 2 := by
  constructor
  · intro hx
    -- Compare a putative minimizer with the known left-hand minimizer and exclude the other
    -- regions by strict positivity of the corresponding gap.
    have hc := powell_scalar_slice_neg_isMinOn ha
    rw [isMinOn_univ_iff] at hx hc
    have hxc : ((powell_scalar_slice a x : ℝ) : EReal) ≤
        ((powell_scalar_slice a (-1 + a / 2) : ℝ) : EReal) := hx (-1 + a / 2)
    have hcx : ((powell_scalar_slice a (-1 + a / 2) : ℝ) : EReal) ≤
        ((powell_scalar_slice a x : ℝ) : EReal) := hc x
    have hxc' : powell_scalar_slice a x ≤ powell_scalar_slice a (-1 + a / 2) := by
      exact_mod_cast hxc
    have hcx' : powell_scalar_slice a (-1 + a / 2) ≤ powell_scalar_slice a x := by
      exact_mod_cast hcx
    have heq : powell_scalar_slice a x = powell_scalar_slice a (-1 + a / 2) :=
      le_antisymm hxc' hcx'
    have hvalc : powell_scalar_slice a (-1 + a / 2) = a - a ^ 2 / 4 :=
      powell_scalar_slice_neg_candidate ha
    by_cases hxneg : x ≤ -1
    · have hvalx : powell_scalar_slice a x = -a * x + (x + 1) ^ 2 :=
        powell_scalar_slice_of_le_neg_one (a := a) hxneg
      rw [hvalx, hvalc] at heq
      have hsquare : (x - (-1 + a / 2)) ^ 2 = 0 := by
        nlinarith
      nlinarith [sq_nonneg (x - (-1 + a / 2)), hsquare]
    · by_cases hxone : x ≤ 1
      · have hmid : x ∈ Set.Icc (-1 : ℝ) 1 := by
          constructor <;> linarith
        have hvalx : powell_scalar_slice a x = -a * x :=
          powell_scalar_slice_of_mem_Icc (a := a) hmid
        have hlin : 0 ≤ (-a) * (x + 1) := by
          have hx1 : 0 ≤ x + 1 := by linarith
          exact mul_nonneg (by linarith : 0 ≤ -a) hx1
        have hapos : 0 < a ^ 2 / 4 := by
          nlinarith
        rw [hvalx, hvalc] at heq
        nlinarith [hlin, hapos]
      · have hxge : 1 ≤ x := by linarith
        have hvalx : powell_scalar_slice a x = -a * x + (x - 1) ^ 2 :=
          powell_scalar_slice_of_one_le (a := a) hxge
        have hlin : 0 ≤ (-a) * (x + 1) := by
          have hx1 : 0 ≤ x + 1 := by linarith
          exact mul_nonneg (by linarith : 0 ≤ -a) hx1
        have hapos : 0 < a ^ 2 / 4 := by
          nlinarith
        rw [hvalx, hvalc] at heq
        nlinarith [sq_nonneg (x - 1), hlin, hapos]
  · intro hx
    -- The reverse implication is the explicit minimizer statement already proved.
    simpa [hx] using powell_scalar_slice_neg_isMinOn ha

/-- Helper for Definition 14.3: the scalar Powell slice has the textbook argmin description. -/
theorem powell_scalar_slice_argmin_eq (a : ℝ) :
    {x : ℝ | IsMinOn (fun t ↦ ((powell_scalar_slice a t : ℝ) : EReal)) Set.univ x} =
      if a = 0 then Set.Icc (-1 : ℝ) 1 else {a.sign * (1 + |a| / 2)} := by
  ext x
  -- Split according to the sign of the linear coefficient and plug in the specialized
  -- one-dimensional minimizer characterization.
  by_cases ha : a = 0
  · simp [ha, powell_scalar_slice_isMinOn_zero_iff]
  · rcases lt_or_gt_of_ne ha with hneg | hpos
    · have hsign : a.sign * (1 + |a| / 2) = -1 + a / 2 := by
        rw [Real.sign_of_neg hneg, abs_of_neg hneg]
        ring
      simp [ha, hsign, powell_scalar_slice_isMinOn_neg_iff hneg]
    · have hsign : a.sign * (1 + |a| / 2) = 1 + a / 2 := by
        rw [Real.sign_of_pos hpos, abs_of_pos hpos]
        ring
      simp [ha, hsign, powell_scalar_slice_isMinOn_pos_iff hpos]

-- Proof sketch: analyze the one-variable function `x ↦ φ(x, y, z)` piecewise on
-- `(-∞, -1]`, `[-1, 1]`, and `[1, ∞)`, then compare the resulting stationary points to show that
-- the minimizer set is the stated singleton when `y + z ≠ 0` and the full interval `[-1, 1]`
-- when `y + z = 0`.
/-- Fixing `y` and `z`, the Chapter 14 owner argmin set for the first-coordinate slice of
Powell's example is the singleton
`{sign (y + z) * (1 + |y + z| / 2)}` when `y + z ≠ 0`, and the interval `[-1, 1]` when
`y + z = 0`. -/
theorem powell_example_x_argmin_eq (y z : ℝ) :
    alternating_minimization_argmin powell_example ![0, y, z] 0 =
      if y + z = 0 then Set.Icc (-1 : ℝ) 1 else {(y + z).sign * (1 + |y + z| / 2)} := by
  ext t
  -- Rewrite the block-argmin condition as the scalar slice plus a constant term.
  rw [mem_alternating_minimization_argmin_update_iff]
  have hslice :
      (fun s ↦ powell_example (Function.update ![0, y, z] 0 s)) =
        fun s ↦
          ((powell_scalar_slice (y + z) s +
            (-y * z + (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 + (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2) : ℝ) :
            EReal) := by
    funext s
    simpa using powell_example_update_zero_apply s y z
  rw [hslice]
  rw [isMinOn_univ_ereal_add_const_iff
    (f := fun s ↦ powell_scalar_slice (y + z) s)
    (c := -y * z + (y - 1)⁺ ^ 2 + (-y - 1)⁺ ^ 2 + (z - 1)⁺ ^ 2 + (-z - 1)⁺ ^ 2)]
  -- The remaining minimizer classification is exactly the scalar theorem.
  simpa using congrArg (fun s : Set ℝ => t ∈ s) (powell_scalar_slice_argmin_eq (y + z))

-- Proof sketch: apply the same piecewise one-dimensional minimization argument as for
-- `powell_example_x_argmin_eq`, now to `y ↦ φ(x, y, z)`, with the linear coefficient determined by
-- `x + z`.
/-- Fixing `x` and `z`, the Chapter 14 owner argmin set for the second-coordinate slice of
Powell's example is the singleton
`{sign (x + z) * (1 + |x + z| / 2)}` when `x + z ≠ 0`, and the interval `[-1, 1]` when
`x + z = 0`. -/
theorem powell_example_y_argmin_eq (x z : ℝ) :
    alternating_minimization_argmin powell_example ![x, 0, z] 1 =
      if x + z = 0 then Set.Icc (-1 : ℝ) 1 else {(x + z).sign * (1 + |x + z| / 2)} := by
  ext t
  -- Route correction: transport the `y`-slice to the already solved `x`-slice by cyclic
  -- symmetry instead of repeating the one-dimensional analysis.
  rw [mem_alternating_minimization_argmin_update_iff]
  have hcyc :
      (fun u ↦ powell_example (Function.update ![x, 0, z] 1 u)) =
        fun u ↦ powell_example (Function.update ![0, z, x] 0 u) := by
    funext u
    -- The updated vectors are `[x, u, z]` and `[u, z, x]`, which are related by the cyclic
    -- symmetry of Powell's objective.
    calc
      powell_example (Function.update ![x, 0, z] 1 u)
          = (φ x u z : EReal) := by
              simp [powell_example, Function.update]
      _ = (φ u z x : EReal) := by
            rw [powell_example_objective_cyclic]
      _ = powell_example (Function.update ![0, z, x] 0 u) := by
            simp [powell_example, Function.update]
  rw [hcyc]
  calc
    IsMinOn (fun u ↦ powell_example (Function.update ![0, z, x] 0 u)) Set.univ t
        ↔ t ∈ alternating_minimization_argmin powell_example ![0, z, x] 0 := by
            symm
            simpa using
              (mem_alternating_minimization_argmin_update_iff
                (F := powell_example) (xBar := ![0, z, x]) (i := 0) (y := t))
    _ ↔ t ∈ if x + z = 0 then Set.Icc (-1 : ℝ) 1 else {(x + z).sign * (1 + |x + z| / 2)} := by
          simpa [add_comm] using congrArg (fun s : Set ℝ => t ∈ s) (powell_example_x_argmin_eq z x)

-- Proof sketch: apply the same piecewise one-dimensional minimization argument as for the `x`
-- and `y` sections, now to `z ↦ φ(x, y, z)`, with linear coefficient `x + y`.
/-- Fixing `x` and `y`, the Chapter 14 owner argmin set for the third-coordinate slice of
Powell's example is the singleton
`{sign (x + y) * (1 + |x + y| / 2)}` when `x + y ≠ 0`, and the interval `[-1, 1]` when
`x + y = 0`. -/
theorem powell_example_z_argmin_eq (x y : ℝ) :
    alternating_minimization_argmin powell_example ![x, y, 0] 2 =
      if x + y = 0 then Set.Icc (-1 : ℝ) 1 else {(x + y).sign * (1 + |x + y| / 2)} := by
  ext t
  -- Route correction: transport the `z`-slice to the `x`-slice by two cyclic permutations.
  rw [mem_alternating_minimization_argmin_update_iff]
  have hcyc :
      (fun u ↦ powell_example (Function.update ![x, y, 0] 2 u)) =
        fun u ↦ powell_example (Function.update ![0, x, y] 0 u) := by
    funext u
    -- The updated vectors are `[x, y, u]` and `[u, x, y]`, connected by two cyclic rewrites.
    calc
      powell_example (Function.update ![x, y, 0] 2 u)
          = (φ x y u : EReal) := by
              simp [powell_example, Function.update]
      _ = (φ y u x : EReal) := by
            rw [powell_example_objective_cyclic]
      _ = (φ u x y : EReal) := by
            rw [powell_example_objective_cyclic]
      _ = powell_example (Function.update ![0, x, y] 0 u) := by
            simp [powell_example, Function.update]
  rw [hcyc]
  calc
    IsMinOn (fun u ↦ powell_example (Function.update ![0, x, y] 0 u)) Set.univ t
        ↔ t ∈ alternating_minimization_argmin powell_example ![0, x, y] 0 := by
            symm
            simpa using
              (mem_alternating_minimization_argmin_update_iff
                (F := powell_example) (xBar := ![0, x, y]) (i := 0) (y := t))
    _ ↔ t ∈ if x + y = 0 then Set.Icc (-1 : ℝ) 1 else {(x + y).sign * (1 + |x + y| / 2)} := by
          simpa [add_comm] using congrArg (fun s : Set ℝ => t ∈ s) (powell_example_x_argmin_eq x y)

end
