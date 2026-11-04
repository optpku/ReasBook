/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_definition_6_2_1_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_1.ch6_sec6_3_1_definition_6_3_1_extra_1

section Theorem622

variable {q : ℕ} {f : Fin q → ℝ} {π : (Fin q → ℝ) → ℝ}

local notation "Rq" => Fin q → ℝ
local notation "IntAssignment" => Rq →₀ ℤ

open scoped IntegerVectorNotation

/-- Helper for Theorem 6.22: resetting only the value at the origin to zero preserves validity. -/
lemma pure_integer_valid_function_reset_zero
    (hπ : pure_integer_valid_function f π) :
    pure_integer_valid_function f (fun r ↦ if r = 0 then 0 else π r) := by
  classical
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Only the coefficient at `0` changes, and it is reset to a nonnegative value.
    intro r
    by_cases hr : r = 0
    · simp [hr]
    · simpa [hr] using hπ.nonneg r
  · intro x hx
    have hx_nonneg : ∀ r, 0 ≤ x r := (mem_pure_integer_feasible_set_iff.mp hx).1
    have hx_lattice : pure_integer_balance f x ∈ ℤ^q := (mem_pure_integer_feasible_set_iff.mp hx).2
    have herase_nonneg : ∀ r, 0 ≤ (x.erase 0) r := by
      intro r
      by_cases hr : r = 0
      · simp [hr]
      · simpa [Finsupp.erase_ne hr] using hx_nonneg r
    have herase_balance :
        pure_integer_balance f (x.erase 0) = pure_integer_balance f x := by
      -- Erasing the origin leaves the balance unchanged because the origin contributes zero.
      ext i
      rw [pure_integer_balance_apply, pure_integer_balance_apply]
      have hsum :
          (x.erase 0).sum (fun r n ↦ (n : ℝ) * r i) =
            x.sum (fun r n ↦ (n : ℝ) * r i) := by
        rw [← Finsupp.add_sum_erase' x 0 (fun r n ↦ (n : ℝ) * r i) (fun r ↦ by simp)]
        simp
      rw [hsum]
    have herase_feasible : x.erase 0 ∈ pure_integer_feasible_set f := by
      rw [mem_pure_integer_feasible_set_iff]
      exact ⟨herase_nonneg, by simpa [herase_balance] using hx_lattice⟩
    have herase_sum :
        (x.erase 0).sum (fun r n ↦ (n : ℝ) * (if r = 0 then 0 else π r)) =
          (x.erase 0).sum (fun r n ↦ (n : ℝ) * π r) :=
      intAssignment_sum_eq_of_eq_on_support (x := x.erase 0)
        (ρ := fun r ↦ if r = 0 then 0 else π r) (π := π) <| by
          intro r hr
          have hr0 : r ≠ 0 := by
            intro hr0
            subst hr0
            simp at hr
          simp [hr0]
    have hsum_eq :
        x.sum (fun r n ↦ (n : ℝ) * (if r = 0 then 0 else π r)) =
          (x.erase 0).sum (fun r n ↦ (n : ℝ) * π r) := by
      calc
        x.sum (fun r n ↦ (n : ℝ) * (if r = 0 then 0 else π r)) =
            (x.erase 0).sum (fun r n ↦ (n : ℝ) * (if r = 0 then 0 else π r)) := by
              rw [← Finsupp.add_sum_erase' x 0
                (fun r n ↦ (n : ℝ) * (if r = 0 then 0 else π r)) (fun r ↦ by simp)]
              simp
        _ = (x.erase 0).sum (fun r n ↦ (n : ℝ) * π r) := herase_sum
    rw [hsum_eq]
    exact pure_integer_valid_function_one_le_sum hπ herase_feasible

/-- A consequence of Theorem 6.22 (Gomory and Johnson [179]): every minimal valid function for
`G_f` vanishes at the origin. -/
theorem pure_integer_minimal_valid_function_zero_eq_zero
    (hπ : pure_integer_minimal_valid_function f π) :
    π 0 = 0 := by
  have hπvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  have hreset := pure_integer_valid_function_reset_zero (f := f) (π := π) hπvalid
  have hle : ∀ r, (if r = 0 then 0 else π r) ≤ π r := by
    intro r
    by_cases hr : r = 0
    · simp [hr, hπ.nonneg 0]
    · simp [hr]
  -- Minimality forces the reset-at-zero perturbation to coincide with `π`.
  have heq := pure_integer_minimal_valid_function_eq_of_le hπ hreset hle
  have hzero := congrArg (fun ψ => ψ 0) heq
  simpa using hzero.symm

/-- Helper for Theorem 6.22: subadditivity controls the value on a natural multiple of a vector. -/
lemma subadditive_le_nat_smul
    (h_zero : π 0 = 0) (h_subadditive : π.Subadditive) (r : Rq) :
    ∀ n : ℕ, π ((n : ℝ) • r) ≤ (n : ℝ) * π r
  | 0 => by simp [h_zero]
  | n + 1 => by
      -- Peel off one copy of `r` and apply subadditivity before using the induction hypothesis.
      have hstep :
          π (((n + 1 : ℕ) : ℝ) • r) ≤ π ((n : ℝ) • r) + π r := by
        simpa [Nat.succ_eq_add_one, add_smul] using h_subadditive ((n : ℝ) • r) r
      have hih := subadditive_le_nat_smul h_zero h_subadditive r n
      calc
        π (((n + 1 : ℕ) : ℝ) • r) ≤ π ((n : ℝ) • r) + π r := hstep
        _ ≤ (n : ℝ) * π r + π r := by gcongr
        _ = ((n + 1 : ℕ) : ℝ) * π r := by
          norm_num [Nat.cast_add]
          ring

/-- Helper for Theorem 6.22: subadditivity controls the value on a nonnegative integer multiple
of a vector. -/
lemma subadditive_le_int_smul
    (h_zero : π 0 = 0) (h_subadditive : π.Subadditive) (r : Rq) {n : ℤ} (hn : 0 ≤ n) :
    π ((n : ℝ) • r) ≤ (n : ℝ) * π r := by
  have hn_nat : ((Int.toNat n : ℕ) : ℤ) = n := Int.toNat_of_nonneg hn
  have hn_real : ((Int.toNat n : ℕ) : ℝ) = (n : ℝ) := by
    exact_mod_cast hn_nat
  -- Convert the nonnegative integer coefficient to the natural-number case.
  simpa [hn_real] using
    subadditive_le_nat_smul (π := π) h_zero h_subadditive r (Int.toNat n)

/-- Helper for Theorem 6.22: a subadditive function is bounded above by the cut sum of any
nonnegative finitely supported integer combination. -/
lemma subadditive_le_pure_integer_finsupp_sum
    (h_zero : π 0 = 0) (h_subadditive : π.Subadditive)
    {x : IntAssignment} (hx_nonneg : ∀ r, 0 ≤ x r) :
    π (x.sum (fun r n ↦ (n : ℝ) • r)) ≤ x.sum (fun r n ↦ (n : ℝ) * π r) := by
  classical
  revert hx_nonneg
  induction x using Finsupp.induction with
  | zero =>
      intro hx_nonneg
      simp [h_zero]
  | single_add r n x hr hn ih =>
      intro hx_nonneg
      have hx_r : x r = 0 := by
        simpa [Finsupp.mem_support_iff] using hr
      have hn_nonneg : 0 ≤ n := by
        simpa [hx_r] using hx_nonneg r
      have hx_nonneg_tail : ∀ s, 0 ≤ x s := by
        intro s
        by_cases hs : s = r
        · subst hs
          simp [hx_r]
        · simpa [Finsupp.single_eq_of_ne hs] using hx_nonneg s
      have htail :=
        ih hx_nonneg_tail
      have hsum_vec :
          (Finsupp.single r n + x).sum (fun s m ↦ (m : ℝ) • s) =
            (n : ℝ) • r + x.sum (fun s m ↦ (m : ℝ) • s) := by
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro a b₁ b₂
          simp [Int.cast_add, add_smul]
      have hsum_π :
          (Finsupp.single r n + x).sum (fun s m ↦ (m : ℝ) * π s) =
            (n : ℝ) * π r + x.sum (fun s m ↦ (m : ℝ) * π s) := by
        rw [Finsupp.sum_add_index]
        · simp
        · simp
        · intro a b₁ b₂
          simp [Int.cast_add, add_mul]
      -- Split off the new singleton term and bound each side with the one-point and tail estimates.
      calc
        π ((Finsupp.single r n + x).sum (fun s m ↦ (m : ℝ) • s)) =
            π ((n : ℝ) • r + x.sum (fun s m ↦ (m : ℝ) • s)) := by
              rw [hsum_vec]
        _ ≤ π ((n : ℝ) • r) + π (x.sum (fun s m ↦ (m : ℝ) • s)) :=
          h_subadditive _ _
        _ ≤ (n : ℝ) * π r + x.sum (fun s m ↦ (m : ℝ) * π s) :=
          add_le_add
            (subadditive_le_int_smul (π := π) h_zero h_subadditive r hn_nonneg)
            htail
        _ = (Finsupp.single r n + x).sum (fun s m ↦ (m : ℝ) * π s) := by
          rw [hsum_π]

/-- Helper for Theorem 6.22: moving `a` units of mass from `r` to `t` changes the weighted
coefficient sum by `(a : ℝ) * (ρ t - ρ r)`. -/
lemma pureIntegerTransferWeightedSum
    {ρ : Rq → ℝ} {x : IntAssignment} {r t : Rq} {a : ℤ} :
    let y := x + Finsupp.single t a - Finsupp.single r a
    y.sum (fun s n ↦ (n : ℝ) * ρ s) =
      x.sum (fun s n ↦ (n : ℝ) * ρ s) + (a : ℝ) * (ρ t - ρ r) := by
  -- Normalize the moved assignment by summing the added and removed singleton terms explicitly.
  dsimp
  rw [Finsupp.sum_sub_index]
  · rw [Finsupp.sum_add_index]
    · simp
      ring_nf
    · simp
    · intro s b₁ b₂
      simp [Int.cast_add, add_mul]
  · intro s b₁ b₂
    simp
    ring_nf

/-- Helper for Theorem 6.22: moving `a` units of mass from `r` to `t` changes the balance by the
displacement vector `(a : ℝ) • (t - r)`. -/
lemma pureIntegerTransferBalance
    {x : IntAssignment} {r t : Rq} {a : ℤ} :
    let y := x + Finsupp.single t a - Finsupp.single r a
    pure_integer_balance f y =
      pure_integer_balance f x + fun i ↦ (a : ℝ) * (t i - r i) := by
  -- Evaluate the balance coordinatewise and reuse the generic weighted-sum transfer formula.
  ext i
  have hsum :=
    pureIntegerTransferWeightedSum (ρ := fun s : Rq ↦ s i) (x := x) (r := r) (t := t) (a := a)
  calc
    pure_integer_balance f (x + Finsupp.single t a - Finsupp.single r a) i =
        f i + ((x + Finsupp.single t a - Finsupp.single r a).sum
          (fun s n ↦ (n : ℝ) * s i)) := by
          rw [pure_integer_balance_apply]
    _ = f i + (x.sum (fun s n ↦ (n : ℝ) * s i) + (a : ℝ) * (t i - r i)) := by
          exact congrArg (fun z : ℝ ↦ f i + z) hsum
    _ = (pure_integer_balance f x + fun i ↦ (a : ℝ) * (t i - r i)) i := by
          simp [pure_integer_balance_apply, Pi.add_apply, add_assoc]

/-- Helper for Theorem 6.22: adding an integer vector to a point of `ℤ^q`
keeps the result in `ℤ^q`. -/
lemma pureIntegerTransferLatticeMem
    {v : Rq} {a : ℤ} {w : Fin q → ℤ}
    (hv : v ∈ ℤ^q) :
    (v + fun i ↦ ((a * w i : ℤ) : ℝ)) ∈ ℤ^q := by
  rcases (mem_integerVectors_iff.mp hv) with ⟨z, hz⟩
  refine (mem_integerVectors_iff).2 ?_
  refine ⟨fun i ↦ z i + a * w i, ?_⟩
  funext i
  -- Read the integer-lattice witness coordinatewise and add the new integer displacement.
  have hi := congrArg (fun u : Rq ↦ u i) hz
  simp [Pi.add_apply, hi, Int.cast_add, Int.cast_mul]

/-- Helper for Theorem 6.22: splitting `a` units of mass from `r₁ + r₂` into `r₁` and `r₂`
changes the weighted coefficient sum by `(a : ℝ) * (ρ r₁ + ρ r₂ - ρ (r₁ + r₂))`. -/
lemma pureIntegerSplitWeightedSum
    {ρ : Rq → ℝ} {x : IntAssignment} {r₁ r₂ : Rq} {a : ℤ} :
    let y := x + Finsupp.single r₁ a + Finsupp.single r₂ a - Finsupp.single (r₁ + r₂) a
    y.sum (fun s n ↦ (n : ℝ) * ρ s) =
      x.sum (fun s n ↦ (n : ℝ) * ρ s) + (a : ℝ) * (ρ r₁ + ρ r₂ - ρ (r₁ + r₂)) := by
  -- Normalize the split update by exposing the two added singleton terms and the removed target.
  dsimp
  rw [Finsupp.sum_sub_index]
  · rw [Finsupp.sum_add_index]
    · rw [Finsupp.sum_add_index]
      · simp
        ring_nf
      · simp
      · intro s b₁ b₂
        simp [Int.cast_add, add_mul]
    · simp
    · intro s b₁ b₂
      simp [Int.cast_add, add_mul]
  · intro s b₁ b₂
    simp
    ring_nf

/-- Helper for Theorem 6.22: splitting `a` units of mass from `r₁ + r₂` into `r₁` and `r₂`
preserves the balance. -/
lemma pureIntegerSplitBalance
    {x : IntAssignment} {r₁ r₂ : Rq} {a : ℤ} :
    let y := x + Finsupp.single r₁ a + Finsupp.single r₂ a - Finsupp.single (r₁ + r₂) a
    pure_integer_balance f y = pure_integer_balance f x := by
  -- After evaluating each coordinate, the split displacement cancels because `r₁ + r₂`
  -- is exactly the sum of the two target vectors.
  ext i
  have hsum :=
    pureIntegerSplitWeightedSum (ρ := fun s : Rq ↦ s i) (x := x) (r₁ := r₁) (r₂ := r₂) (a := a)
  calc
    pure_integer_balance f (x + Finsupp.single r₁ a + Finsupp.single r₂ a -
        Finsupp.single (r₁ + r₂) a) i =
        f i + ((x + Finsupp.single r₁ a + Finsupp.single r₂ a -
          Finsupp.single (r₁ + r₂) a).sum (fun s n ↦ (n : ℝ) * s i)) := by
          rw [pure_integer_balance_apply]
    _ = f i + (x.sum (fun s n ↦ (n : ℝ) * s i) +
          (a : ℝ) * (r₁ i + r₂ i - (r₁ + r₂) i)) := by
          exact congrArg (fun z : ℝ ↦ f i + z) hsum
    _ = pure_integer_balance f x i := by
          have hcoord : (r₁ + r₂) i = r₁ i + r₂ i := by rfl
          rw [pure_integer_balance_apply]
          rw [hcoord]
          ring_nf

/-- Helper for Theorem 6.22: lowering the value at `r₁ + r₂` to `π r₁ + π r₂` preserves
validity when neither summand is the origin. -/
lemma pure_integer_valid_function_lower_at_sum
    (hπ : pure_integer_valid_function f π)
    {r₁ r₂ : Rq} (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0) :
    pure_integer_valid_function f
      (fun r ↦ if r = r₁ + r₂ then π r₁ + π r₂ else π r) := by
  classical
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Only the coefficient at `r₁ + r₂` changes, and it is replaced by a nonnegative sum.
    intro r
    by_cases hr : r = r₁ + r₂
    · simp [hr, add_nonneg (hπ.nonneg r₁) (hπ.nonneg r₂)]
    · simp [hr, hπ.nonneg r]
  · intro x hx
    let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then π r₁ + π r₂ else π r
    let a : ℤ := x (r₁ + r₂)
    let y : IntAssignment :=
      x + Finsupp.single r₁ a + Finsupp.single r₂ a - Finsupp.single (r₁ + r₂) a
    have hx_nonneg : ∀ r, 0 ≤ x r := (mem_pure_integer_feasible_set_iff.mp hx).1
    have hx_lattice : pure_integer_balance f x ∈ ℤ^q := (mem_pure_integer_feasible_set_iff.mp hx).2
    have ha_nonneg : 0 ≤ a := by
      simpa [a] using hx_nonneg (r₁ + r₂)
    have hsum_ne_left : r₁ + r₂ ≠ r₁ := by
      intro h
      apply hr₂
      ext i
      have hi := congrArg (fun v : Rq ↦ v i) h
      have hi' : r₁ i + r₂ i = r₁ i := by simpa using hi
      have hz : r₂ i = 0 := by linarith
      simpa using hz
    have hsum_ne_right : r₁ + r₂ ≠ r₂ := by
      intro h
      apply hr₁
      ext i
      have hi := congrArg (fun v : Rq ↦ v i) h
      have hi' : r₁ i + r₂ i = r₂ i := by simpa using hi
      have hz : r₁ i = 0 := by linarith
      simpa using hz
    have hy_nonneg : ∀ s, 0 ≤ y s := by
      intro s
      have hy_apply :
          y s = x s + (if r₁ = s then a else 0) + (if r₂ = s then a else 0) -
            (if r₁ + r₂ = s then a else 0) := by
        simp [y, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply,
          add_left_comm, add_comm, eq_comm]
      by_cases hs_sum : s = r₁ + r₂
      · -- At the split source, the removed mass is exactly the old coefficient.
        have hs₁ : r₁ ≠ s := by simpa [hs_sum] using Ne.symm hsum_ne_left
        have hs₂ : r₂ ≠ s := by simpa [hs_sum] using Ne.symm hsum_ne_right
        have hy_zero : y s = 0 := by
          rw [hy_apply]
          simp [a, hs_sum, hr₁, hr₂]
        rw [hy_zero]
      · by_cases hs₁ : s = r₁
        · -- At `r₁`, the split only adds the transferred mass.
          by_cases h12 : r₁ = r₂
          · have hs₂ : s = r₂ := by simpa [h12] using hs₁
            have hy_val : y s = x s + a + a := by
              rw [hy_apply]
              simp [hs₁, h12, hr₂, add_left_comm, add_comm]
            rw [hy_val]
            exact add_nonneg (add_nonneg (hx_nonneg s) ha_nonneg) ha_nonneg
          · have hy_val : y s = x s + a := by
              have hs₂ : r₂ ≠ s := by simpa [hs₁] using Ne.symm h12
              have h21 : r₂ ≠ r₁ := by
                intro h
                exact h12 h.symm
              rw [hy_apply]
              simp [hs₁, hsum_ne_left, h21, add_comm]
            rw [hy_val]
            exact add_nonneg (hx_nonneg s) ha_nonneg
        · by_cases hs₂ : s = r₂
          · -- At `r₂`, the split only adds the transferred mass.
            have hy_val : y s = x s + a := by
              have h12 : r₁ ≠ r₂ := by
                intro h
                apply hs₁
                simpa [h] using hs₂
              rw [hy_apply]
              simp [hs₂, hsum_ne_right, h12, add_comm]
            rw [hy_val]
            exact add_nonneg (hx_nonneg s) ha_nonneg
          · -- Away from the three special indices, the assignment is unchanged.
            have hy_val : y s = x s := by
              have hs_sum' : r₁ + r₂ ≠ s := by
                intro h
                exact hs_sum h.symm
              have hr1s : r₁ ≠ s := by
                intro h
                exact hs₁ h.symm
              have hr2s : r₂ ≠ s := by
                intro h
                exact hs₂ h.symm
              rw [hy_apply]
              simp [hr1s, hr2s, hs_sum']
            rw [hy_val]
            exact hx_nonneg s
    have hy_balance : pure_integer_balance f y = pure_integer_balance f x := by
      -- Route correction: consume the split balance bridge lemma instead of re-normalizing
      -- the moved assignment in place.
      simpa [y, a] using
        pureIntegerSplitBalance (f := f) (x := x) (r₁ := r₁) (r₂ := r₂) (a := a)
    have hy_feasible : y ∈ pure_integer_feasible_set f := by
      rw [mem_pure_integer_feasible_set_iff]
      exact ⟨hy_nonneg, by simpa [hy_balance] using hx_lattice⟩
    have hsum_support :
        x.sum (fun s n ↦ (n : ℝ) * ρ s) =
          x.sum (fun s n ↦ (n : ℝ) * π s) + (a : ℝ) * (π r₁ + π r₂ - π (r₁ + r₂)) := by
      -- Isolate the coefficient at `r₁ + r₂` before comparing `ρ` and `π`.
      rw [← Finsupp.add_sum_erase' x (r₁ + r₂) (fun s n ↦ (n : ℝ) * ρ s) (fun s ↦ by simp)]
      rw [← Finsupp.add_sum_erase' x (r₁ + r₂) (fun s n ↦ (n : ℝ) * π s) (fun s ↦ by simp)]
      have herase_eq :
          (x.erase (r₁ + r₂)).sum (fun s n ↦ (n : ℝ) * ρ s) =
            (x.erase (r₁ + r₂)).sum (fun s n ↦ (n : ℝ) * π s) :=
        intAssignment_sum_eq_of_eq_on_support (x := x.erase (r₁ + r₂))
          (ρ := ρ) (π := π) <| by
            intro s hs
            have hs_ne : s ≠ r₁ + r₂ := by
              intro hs_eq
              subst hs_eq
              simp at hs
            simp [ρ, hs_ne]
      rw [herase_eq]
      simp [ρ, a]
      ring
    have hy_sum :
        y.sum (fun s n ↦ (n : ℝ) * π s) =
          x.sum (fun s n ↦ (n : ℝ) * π s) + (a : ℝ) * (π r₁ + π r₂ - π (r₁ + r₂)) := by
      -- The split weighted-sum bridge puts the moved assignment into the same normal form.
      simpa [y, a] using
        pureIntegerSplitWeightedSum (ρ := π) (x := x) (r₁ := r₁) (r₂ := r₂) (a := a)
    calc
      1 ≤ y.sum (fun s n ↦ (n : ℝ) * π s) :=
        pure_integer_valid_function_one_le_sum hπ hy_feasible
      _ = x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
        rw [hy_sum, hsum_support]

/-- Another consequence of Theorem 6.22 (Gomory and Johnson [179]): every minimal valid function
for `G_f` is subadditive. -/
theorem pure_integer_minimal_valid_function_subadditive
    (hπ : pure_integer_minimal_valid_function f π) :
    π.Subadditive := by
  intro r₁ r₂
  by_cases hr₁ : r₁ = 0
  · -- When `r₁ = 0`, the claimed inequality reduces to `π 0 = 0`.
    simp [hr₁, pure_integer_minimal_valid_function_zero_eq_zero hπ]
  by_cases hr₂ : r₂ = 0
  · -- When `r₂ = 0`, the claimed inequality reduces to `π 0 = 0`.
    simp [hr₂, pure_integer_minimal_valid_function_zero_eq_zero hπ]
  by_cases hlt : π (r₁ + r₂) > π r₁ + π r₂
  · let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then π r₁ + π r₂ else π r
    have hπvalid : pure_integer_valid_function f π :=
      { nonneg := hπ.nonneg
        one_le_sum := hπ.one_le_sum }
    have hρvalid :
        pure_integer_valid_function f ρ :=
      pure_integer_valid_function_lower_at_sum (f := f) (π := π) hπvalid hr₁ hr₂
    have hle : ∀ r, ρ r ≤ π r := by
      intro r
      by_cases hr : r = r₁ + r₂
      · simp [ρ, hr, le_of_lt hlt]
      · simp [ρ, hr]
    -- Minimality forbids lowering the value at `r₁ + r₂` below `π (r₁ + r₂)`.
    have heq := pure_integer_minimal_valid_function_eq_of_le hπ hρvalid hle
    have hpoint := congrArg (fun ψ => ψ (r₁ + r₂)) heq
    have hcontr : π r₁ + π r₂ = π (r₁ + r₂) := by
      simpa [ρ] using hpoint
    linarith
  · exact le_of_not_gt hlt

/-- Helper for Theorem 6.22: replacing the value at `r` by its value at an integer translate
preserves validity. -/
lemma pure_integer_valid_function_lower_at_integer_translate
    (hπ : pure_integer_valid_function f π)
    (r : Rq) (w : Fin q → ℤ) :
    pure_integer_valid_function f
      (fun s ↦ if s = r then π (r + fun i ↦ (w i : ℝ)) else π s) := by
  classical
  let ρ : Rq → ℝ := fun s ↦ if s = r then π (r + fun i ↦ (w i : ℝ)) else π s
  refine
    { nonneg := ?_
      one_le_sum := ?_ }
  · -- Only the value at `r` changes, and it is replaced by another nonnegative value of `π`.
    intro s
    by_cases hs : s = r
    · simp [hs, hπ.nonneg]
    · simp [hs, hπ.nonneg]
  · intro x hx
    have hx_nonneg : ∀ s, 0 ≤ x s := (mem_pure_integer_feasible_set_iff.mp hx).1
    have hx_lattice : pure_integer_balance f x ∈ ℤ^q := (mem_pure_integer_feasible_set_iff.mp hx).2
    by_cases hw0 : w = 0
    · -- When the translation vector is zero, the perturbed coefficient function is just `π`.
      have hsum_eq :
          x.sum (fun s n ↦ (n : ℝ) * ρ s) =
            x.sum (fun s n ↦ (n : ℝ) * π s) :=
        intAssignment_sum_eq_of_eq_on_support (x := x) (ρ := ρ) (π := π) <| by
          intro s hs
          by_cases hs_eq : s = r
          · subst hs_eq
            dsimp [ρ]
            rw [show s + (fun i ↦ (w i : ℝ)) = s by
              ext i
              simp [hw0]]
            simp
          · simp [ρ, hs_eq]
      rw [hsum_eq]
      exact pure_integer_valid_function_one_le_sum hπ hx
    · by_cases hxr0 : x r = 0
      · -- If `x r = 0`, the changed coefficient lies outside the support of `x`.
        have hr_not_mem : r ∉ x.support := by
          simpa [Finsupp.mem_support_iff] using hxr0
        have hsum_eq :
            x.sum (fun s n ↦ (n : ℝ) * ρ s) =
              x.sum (fun s n ↦ (n : ℝ) * π s) :=
          intAssignment_sum_eq_of_eq_on_support (x := x) (ρ := ρ) (π := π) <| by
            intro s hs
            by_cases hs_eq : s = r
            · exact False.elim <| hr_not_mem (hs_eq ▸ hs)
            · simp [ρ, hs_eq]
        rw [hsum_eq]
        exact pure_integer_valid_function_one_le_sum hπ hx
      · let t : Rq := r + fun i ↦ (w i : ℝ)
        let a : ℤ := x r
        let y : IntAssignment := x + Finsupp.single t a - Finsupp.single r a
        have ha_nonneg : 0 ≤ a := by
          simpa [a] using hx_nonneg r
        have ht_ne : t ≠ r := by
          intro ht_eq
          apply hw0
          funext i
          have hi := congrArg (fun u : Rq ↦ u i) ht_eq
          have hi_eq : r i + (w i : ℝ) = r i := by
            simpa [t] using hi
          have hi_zero : (w i : ℝ) = 0 := by
            linarith
          exact_mod_cast hi_zero
        have hy_nonneg : ∀ s, 0 ≤ y s := by
          intro s
          by_cases hs_r : s = r
          · -- At the source point, all moved mass is removed.
            have hy_zero : y s = 0 := by
              simp [y, a, t, hs_r, ht_ne, Finsupp.add_apply, Finsupp.sub_apply]
            rw [hy_zero]
          · by_cases hs_t : s = t
            · -- At the translated point, the moved mass is added to the old coefficient.
              have hr_ne_t : r ≠ t := by
                intro hr_eq
                exact ht_ne hr_eq.symm
              have hy_val : y s = x s + a := by
                simp [y, a, t, hs_t, hr_ne_t, Finsupp.add_apply, Finsupp.sub_apply,
                  add_comm]
              rw [hy_val]
              exact add_nonneg (hx_nonneg s) ha_nonneg
            · -- Away from the source and target, the assignment is unchanged.
              have hy_val : y s = x s := by
                simp [y, a, t, hs_r, hs_t, Finsupp.add_apply, Finsupp.sub_apply]
              rw [hy_val]
              exact hx_nonneg s
        have hy_balance :
            pure_integer_balance f y =
              pure_integer_balance f x + fun i ↦ ((a * w i : ℤ) : ℝ) := by
          -- Route correction: use the transfer balance bridge once, then rewrite the displacement
          -- as the corresponding integer vector.
          ext i
          have hi :=
            congrArg (fun u : Rq ↦ u i) <|
              (pureIntegerTransferBalance (f := f) (x := x) (r := r) (t := t) (a := a))
          simpa [y, a, t, Int.cast_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
            using hi
        have hy_feasible : y ∈ pure_integer_feasible_set f := by
          rw [mem_pure_integer_feasible_set_iff]
          refine ⟨hy_nonneg, ?_⟩
          rw [hy_balance]
          exact pureIntegerTransferLatticeMem (v := pure_integer_balance f x) (a := a)
            (w := w) hx_lattice
        have hsum_support :
            x.sum (fun s n ↦ (n : ℝ) * ρ s) =
              x.sum (fun s n ↦ (n : ℝ) * π s) + (a : ℝ) * (π t - π r) := by
          -- Isolate the source coefficient before comparing `ρ` with `π`.
          rw [← Finsupp.add_sum_erase' x r (fun s n ↦ (n : ℝ) * ρ s) (fun s ↦ by simp)]
          rw [← Finsupp.add_sum_erase' x r (fun s n ↦ (n : ℝ) * π s) (fun s ↦ by simp)]
          have herase_eq :
              (x.erase r).sum (fun s n ↦ (n : ℝ) * ρ s) =
                (x.erase r).sum (fun s n ↦ (n : ℝ) * π s) :=
            intAssignment_sum_eq_of_eq_on_support (x := x.erase r) (ρ := ρ) (π := π) <| by
              intro s hs
              have hs_ne : s ≠ r := by
                intro hs_eq
                subst hs_eq
                simp at hs
              simp [ρ, hs_ne]
          rw [herase_eq]
          simp [ρ, a]
          ring
        have hy_sum :
            y.sum (fun s n ↦ (n : ℝ) * π s) =
              x.sum (fun s n ↦ (n : ℝ) * π s) + (a : ℝ) * (π t - π r) := by
          -- The moved assignment produces the same correction term on the ordinary `π`-sum.
          simpa [y, a, t] using
            pureIntegerTransferWeightedSum (ρ := π) (x := x) (r := r) (t := t) (a := a)
        calc
          1 ≤ y.sum (fun s n ↦ (n : ℝ) * π s) :=
            pure_integer_valid_function_one_le_sum hπ hy_feasible
          _ = x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
            rw [hy_sum, hsum_support]

/-- Helper for Theorem 6.22: after moving one unit of mass from `r` to the origin, the
remaining tail still bounds `π (-f-r)` from below. -/
lemma pureIntegerSymmetryTailLowerBound
    (h_zero : π 0 = 0) (h_subadditive : π.Subadditive) (h_periodic : integer_periodic_on_rn π)
    {x : IntAssignment} (hx : x ∈ pure_integer_feasible_set f) {r : Rq} (hr : 1 ≤ x r) :
    let y := x + Finsupp.single 0 1 - Finsupp.single r 1
    π (-f - r) ≤ y.sum (fun s n ↦ (n : ℝ) * π s) := by
  let y : IntAssignment := x + Finsupp.single 0 1 - Finsupp.single r 1
  have hx_nonneg : ∀ s, 0 ≤ x s := (mem_pure_integer_feasible_set_iff.mp hx).1
  have hx_lattice : pure_integer_balance f x ∈ ℤ^q := (mem_pure_integer_feasible_set_iff.mp hx).2
  have hy_nonneg : ∀ s, 0 ≤ y s := by
    intro s
    by_cases hs_r : s = r
    · -- At `r`, one unit is removed and the hypothesis `1 ≤ x r` keeps the coefficient nonnegative.
      by_cases hr0 : r = 0
      · have hy_val : y s = x s := by
          simp [y, hs_r, hr0]
        rw [hy_val]
        exact hx_nonneg s
      · have hy_val : y s = x s - 1 := by
          simp [y, hs_r, hr0, Finsupp.add_apply, Finsupp.sub_apply]
        rw [hy_val]
        have hs_ge_one : (1 : ℤ) ≤ x s := by
          simpa [hs_r] using hr
        linarith
    · by_cases hs0 : s = 0
      · -- At the origin, the moved unit only increases the coefficient.
        have hr0 : r ≠ 0 := by
          intro hr0
          apply hs_r
          simp [hs0, hr0]
        have hy_val : y s = x s + 1 := by
          simp [y, hs0, hr0, Finsupp.add_apply, Finsupp.sub_apply]
        rw [hy_val]
        linarith [hx_nonneg s]
      · -- Away from `r` and `0`, the assignment is unchanged.
        have hy_val : y s = x s := by
          simp [y, hs_r, hs0, Finsupp.add_apply, Finsupp.sub_apply]
        rw [hy_val]
        exact hx_nonneg s
  rcases (mem_integerVectors_iff.mp hx_lattice) with ⟨z, hz⟩
  have hsum_vec :
      y.sum (fun s n ↦ (n : ℝ) • s) = -f - r + fun i ↦ (z i : ℝ) := by
    -- Rewrite the moved weighted vector sum from the lattice witness of `x`.
    ext i
    have hx_coord : x.sum (fun s n ↦ (n : ℝ) * s i) = -f i + (z i : ℝ) := by
      have hi : f i + x.sum (fun s n ↦ (n : ℝ) * s i) = (z i : ℝ) := by
        simpa [pure_integer_balance_apply] using congrArg (fun u : Rq ↦ u i) hz
      have hi' : x.sum (fun s n ↦ (n : ℝ) * s i) + f i = (z i : ℝ) := by
        simpa [add_comm] using hi
      calc
        x.sum (fun s n ↦ (n : ℝ) * s i) = (z i : ℝ) - f i := eq_sub_of_add_eq hi'
        _ = -f i + (z i : ℝ) := by ring
    have hy_coord :
        y.sum (fun s n ↦ (n : ℝ) * s i) = x.sum (fun s n ↦ (n : ℝ) * s i) - r i := by
      simpa [y, sub_eq_add_neg] using
        (pureIntegerTransferWeightedSum (ρ := fun s : Rq ↦ s i) (x := x) (r := r) (t := 0)
          (a := (1 : ℤ)))
    calc
      (y.sum (fun s n ↦ (n : ℝ) • s)) i = y.sum (fun s n ↦ (n : ℝ) * s i) := by
        rw [Finsupp.sum_apply']
        simp [Pi.smul_apply, smul_eq_mul]
      _ = x.sum (fun s n ↦ (n : ℝ) * s i) - r i := hy_coord
      _ = (-f i + (z i : ℝ)) - r i := by rw [hx_coord]
      _ = (-f - r + fun j ↦ (z j : ℝ)) i := by
        simp [Pi.add_apply, Pi.neg_apply]
        ring
  -- Compare `π` on the moved weighted sum with the subadditive upper bound on that sum.
  calc
    π (-f - r) = π ((-f - r) + fun i ↦ (z i : ℝ)) := h_periodic (-f - r) z
    _ = π (y.sum (fun s n ↦ (n : ℝ) • s)) := by rw [hsum_vec]
    _ ≤ y.sum (fun s n ↦ (n : ℝ) * π s) :=
      subadditive_le_pure_integer_finsupp_sum (π := π) h_zero h_subadditive hy_nonneg

/-- Another consequence of Theorem 6.22 (Gomory and Johnson [179]): every minimal valid function
for `G_f` is periodic modulo the integer lattice. -/
theorem pure_integer_minimal_valid_function_periodic
    (hπ : pure_integer_minimal_valid_function f π) :
    integer_periodic_on_rn π := by
  have hπvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  have htranslate_le :
      ∀ (r : Rq) (w : Fin q → ℤ), π r ≤ π (r + fun i ↦ (w i : ℝ)) := by
    intro r w
    by_contra hlt
    let ρ : Rq → ℝ := fun s ↦ if s = r then π (r + fun i ↦ (w i : ℝ)) else π s
    have hρvalid :
        pure_integer_valid_function f ρ :=
      pure_integer_valid_function_lower_at_integer_translate (f := f) (π := π) hπvalid r w
    have hle : ∀ s, ρ s ≤ π s := by
      intro s
      by_cases hs : s = r
      · exact by
          have hstrict : π (r + fun i ↦ (w i : ℝ)) < π r := lt_of_not_ge hlt
          simpa [ρ, hs] using le_of_lt hstrict
      · simp [ρ, hs]
    -- Minimality forbids lowering the value at `r` below the value at an integer translate.
    have heq := pure_integer_minimal_valid_function_eq_of_le hπ hρvalid hle
    have hpoint := congrArg (fun ψ => ψ r) heq
    have hr_eq : π (r + fun i ↦ (w i : ℝ)) = π r := by
      simpa [ρ] using hpoint
    exact (lt_of_not_ge hlt).ne hr_eq
  intro r w
  refine le_antisymm (htranslate_le r w) ?_
  -- Apply the same lowering argument to the translate by `-w` to recover the reverse inequality.
  have hback := htranslate_le (r + fun i ↦ (w i : ℝ)) (fun i ↦ -w i)
  convert hback using 2
  ext i
  simp [add_assoc]

/-- Theorem 6.22 (4) (Gomory and Johnson [179]). Every minimal valid function for `G_f`
satisfies the symmetry condition. -/
theorem pure_integer_minimal_valid_function_symmetry
    (hπ : pure_integer_minimal_valid_function f π) :
    satisfies_symmetry_condition f π := by
  intro r
  have hπvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  have h_zero : π 0 = 0 := pure_integer_minimal_valid_function_zero_eq_zero hπ
  have h_subadditive : π.Subadditive := pure_integer_minimal_valid_function_subadditive hπ
  have h_periodic : integer_periodic_on_rn π := pure_integer_minimal_valid_function_periodic hπ
  have h_lower : 1 ≤ π r + π (-f - r) :=
    pure_integer_valid_function_symmetry_lower_bound hπvalid r
  have h_upper : π r + π (-f - r) ≤ 1 := by
    by_contra hgt
    let σ : ℝ := π r + π (-f - r)
    have hσ_gt : 1 < σ := by
      simpa [σ] using lt_of_not_ge hgt
    have hσ_pos : 0 < σ := lt_trans zero_lt_one hσ_gt
    have h_other_le : π (-f - r) ≤ 1 :=
      pure_integer_minimal_valid_function_le_one hπ (-f - r)
    have hπr_pos : 0 < π r := by
      linarith
    let ρ : Rq → ℝ := fun s ↦ if s = r then π r / σ else π s
    have hρvalid : pure_integer_valid_function f ρ := by
      refine
        { nonneg := ?_
          one_le_sum := ?_ }
      · -- Only the value at `r` changes, and the scaled value stays nonnegative.
        intro s
        by_cases hs : s = r
        · simp [ρ, hs, div_nonneg (hπ.nonneg r) (le_of_lt hσ_pos)]
        · simp [ρ, hs, hπ.nonneg]
      · intro x hx
        have hx_nonneg : ∀ s, 0 ≤ x s := (mem_pure_integer_feasible_set_iff.mp hx).1
        have hρ_nonneg : ∀ s, 0 ≤ ρ s := by
          intro s
          by_cases hs : s = r
          · simp [ρ, hs, div_nonneg (hπ.nonneg r) (le_of_lt hσ_pos)]
          · simp [ρ, hs, hπ.nonneg]
        by_cases hxr0 : x r = 0
        · -- If `x r = 0`, the scaled coefficient is outside the support of `x`.
          have hr_not_mem : r ∉ x.support := by
            simpa [Finsupp.mem_support_iff] using hxr0
          have hsum_eq :
              x.sum (fun s n ↦ (n : ℝ) * ρ s) =
                x.sum (fun s n ↦ (n : ℝ) * π s) :=
            intAssignment_sum_eq_of_eq_on_support (x := x) (ρ := ρ) (π := π) <| by
              intro s hs
              by_cases hs_eq : s = r
              · exact False.elim <| hr_not_mem (hs_eq ▸ hs)
              · simp [ρ, hs_eq]
          rw [hsum_eq]
          exact pure_integer_valid_function_one_le_sum hπvalid hx
        · have hr_mem : r ∈ x.support := by
            simpa [Finsupp.mem_support_iff] using hxr0
          have hxr_pos : 0 < x r := lt_of_le_of_ne (hx_nonneg r) (Ne.symm hxr0)
          have hxr_ge_one : (1 : ℤ) ≤ x r := by
            simpa using Int.add_one_le_iff.mpr hxr_pos
          have hxr_ge_one_real : (1 : ℝ) ≤ (x r : ℝ) := by
            exact_mod_cast hxr_ge_one
          by_cases hlarge : σ / π r ≤ (x r : ℝ)
          · -- If the contribution at `r` alone is at least `1`, it already proves validity.
            have hterm : 1 ≤ (x r : ℝ) * ρ r := by
              have hfrac_pos : 0 < π r / σ := by
                exact div_pos hπr_pos hσ_pos
              have hmul :
                  (σ / π r) * (π r / σ) ≤ (x r : ℝ) * (π r / σ) := by
                exact mul_le_mul_of_nonneg_right hlarge (le_of_lt hfrac_pos)
              have hone : (σ / π r) * (π r / σ) = 1 := by
                field_simp [hπr_pos.ne', hσ_pos.ne']
              simpa [ρ, hone] using hmul
            exact one_le_intAssignment_sum_of_one_le_term
              (x := x) (ρ := ρ) (r := r) hx_nonneg hρ_nonneg hr_mem hterm
          · -- In the middle branch, peel off one copy of `r` and use the tail lower bound.
            let y : IntAssignment := x + Finsupp.single 0 1 - Finsupp.single r 1
            have hmid : (x r : ℝ) < σ / π r := lt_of_not_ge hlarge
            have hy_tail :
                π (-f - r) ≤ y.sum (fun s n ↦ (n : ℝ) * π s) :=
              pureIntegerSymmetryTailLowerBound (f := f) (π := π) h_zero h_subadditive
                h_periodic hx hxr_ge_one
            have hy_sum :
                y.sum (fun s n ↦ (n : ℝ) * π s) =
                  x.sum (fun s n ↦ (n : ℝ) * π s) - π r := by
              -- Route correction: normalize the one-point move through the transfer bridge and
              -- use `π 0 = 0` to erase the contribution added at the origin.
              simpa [y, h_zero, sub_eq_add_neg] using
                (pureIntegerTransferWeightedSum (ρ := π) (x := x) (r := r) (t := 0)
                  (a := (1 : ℤ)))
            have hρ_sum :
                x.sum (fun s n ↦ (n : ℝ) * ρ s) =
                  x.sum (fun s n ↦ (n : ℝ) * π s) + (x r : ℝ) * (π r / σ - π r) := by
              -- Isolate the source coefficient before comparing `ρ` and `π`.
              rw [← Finsupp.add_sum_erase' x r (fun s n ↦ (n : ℝ) * ρ s) (fun s ↦ by simp)]
              rw [← Finsupp.add_sum_erase' x r (fun s n ↦ (n : ℝ) * π s) (fun s ↦ by simp)]
              have herase_eq :
                  (x.erase r).sum (fun s n ↦ (n : ℝ) * ρ s) =
                    (x.erase r).sum (fun s n ↦ (n : ℝ) * π s) :=
                intAssignment_sum_eq_of_eq_on_support (x := x.erase r) (ρ := ρ) (π := π) <| by
                  intro s hs
                  have hs_ne : s ≠ r := by
                    intro hs_eq
                    subst hs_eq
                    simp at hs
                  simp [ρ, hs_ne]
              rw [herase_eq]
              simp [ρ]
              ring
            have hxπ_lt_sigma : (x r : ℝ) * π r < σ := by
              have := (mul_lt_mul_of_pos_right hmid hπr_pos)
              simpa [div_eq_mul_inv, hπr_pos.ne'] using this
            have hscale_lt : ((σ - 1) / σ) * ((x r : ℝ) * π r) < σ - 1 := by
              have hfrac_pos : 0 < (σ - 1) / σ := by
                positivity
              have hmul :=
                mul_lt_mul_of_pos_left hxπ_lt_sigma hfrac_pos
              have hscale_eq : ((σ - 1) / σ) * σ = σ - 1 := by
                field_simp [hσ_pos.ne']
              linarith
            have hstrict_sum : 1 < x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
              calc
                1 = σ - (σ - 1) := by ring
                _ < σ - ((σ - 1) / σ) * ((x r : ℝ) * π r) := by linarith
                _ = π (-f - r) + π r - ((σ - 1) / σ) * ((x r : ℝ) * π r) := by
                      simp [σ, add_comm]
                _ ≤ y.sum (fun s n ↦ (n : ℝ) * π s) + π r -
                      ((σ - 1) / σ) * ((x r : ℝ) * π r) := by
                        gcongr
                _ = x.sum (fun s n ↦ (n : ℝ) * π s) -
                      ((σ - 1) / σ) * ((x r : ℝ) * π r) := by
                        rw [hy_sum]
                        ring
                _ = x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
                        rw [hρ_sum]
                        field_simp [hσ_pos.ne']
                        ring
            exact le_of_lt hstrict_sum
    have hρ_le : ∀ s, ρ s ≤ π s := by
      intro s
      by_cases hs : s = r
      · have hscaled_lt : π r / σ < π r := by
          refine (div_lt_iff₀ hσ_pos).2 ?_
          nlinarith
        simpa [ρ, hs] using le_of_lt hscaled_lt
      · simp [ρ, hs]
    -- Minimality forbids lowering `π r` below the scaled value `π r / σ`.
    have hEq := pure_integer_minimal_valid_function_eq_of_le hπ hρvalid hρ_le
    have hpoint : ρ r = π r := by
      simpa using congrArg (fun ψ ↦ ψ r) hEq
    have hscaled_lt : ρ r < π r := by
      have hlt : π r / σ < π r := by
        refine (div_lt_iff₀ hσ_pos).2 ?_
        nlinarith
      simpa [ρ] using hlt
    exact hscaled_lt.ne hpoint
  exact le_antisymm h_upper h_lower

/-- The converse direction of Theorem 6.22 (Gomory and Johnson [179]): a nonnegative-valued
function `π : ℝ^q → ℝ` that satisfies `π 0 = 0`, subadditivity, integer periodicity, and the
symmetry condition is a minimal valid function for `G_f`. -/
theorem pure_integer_minimal_valid_function_of_zero_subadditive_periodic_symmetry
    (h_nonneg : ∀ r, 0 ≤ π r) (h_zero : π 0 = 0) (h_subadditive : π.Subadditive)
    (h_periodic : integer_periodic_on_rn π)
    (h_symmetry : satisfies_symmetry_condition f π) :
    pure_integer_minimal_valid_function f π := by
  refine
    { nonneg := h_nonneg
      one_le_sum := ?_
      eq_of_le := ?_ }
  · intro x hx
    have hx_nonneg : ∀ r, 0 ≤ x r := (mem_pure_integer_feasible_set_iff.mp hx).1
    have hx_lattice : pure_integer_balance f x ∈ ℤ^q := (mem_pure_integer_feasible_set_iff.mp hx).2
    rcases (mem_integerVectors_iff.mp hx_lattice) with ⟨z, hz⟩
    have h_neg_f : π (-f) = 1 := by
      -- Evaluate symmetry at the origin and use the prescribed normalization `π 0 = 0`.
      simpa [h_zero] using h_symmetry 0
    have hsum_vec :
        x.sum (fun r n ↦ (n : ℝ) • r) = -f + fun i ↦ (z i : ℝ) := by
      -- Rewriting the lattice-valued balance isolates the weighted sum as `-f + z`.
      ext i
      rw [Finsupp.sum_apply', Pi.add_apply, Pi.neg_apply]
      have hi : f i + x.sum (fun r n ↦ (n : ℝ) * r i) = (z i : ℝ) := by
        simpa [pure_integer_balance_apply] using congrArg (fun v : Rq ↦ v i) hz
      have hi' : x.sum (fun r n ↦ (n : ℝ) * r i) + f i = (z i : ℝ) := by
        simpa [add_comm] using hi
      calc
        x.sum (fun r n ↦ (n : ℝ) * r i) = (z i : ℝ) - f i := eq_sub_of_add_eq hi'
        _ = -f i + (z i : ℝ) := by ring
    calc
      1 = π (-f) := h_neg_f.symm
      _ = π (-f + fun i ↦ (z i : ℝ)) := h_periodic (-f) z
      _ = π (x.sum (fun r n ↦ (n : ℝ) • r)) := by rw [hsum_vec]
      _ ≤ x.sum (fun r n ↦ (n : ℝ) * π r) :=
        subadditive_le_pure_integer_finsupp_sum (π := π) h_zero h_subadditive hx_nonneg
  · intro π' hπ' hle
    funext r
    apply le_antisymm (hle r)
    have hlower' : 1 ≤ π' r + π' (-f - r) :=
      pure_integer_valid_function_symmetry_lower_bound hπ' r
    have hsym : π r + π (-f - r) = 1 := h_symmetry r
    have hother_le : π' (-f - r) ≤ π (-f - r) := hle (-f - r)
    -- The lower bound for `π'` and the symmetry equation for `π` force equality pointwise.
    linarith

end Theorem622
