/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs

section Chap01
section Section01

universe u

/-- Definition 1.1.1: An ordered set is a set `S` with a relation `<` such that
(i) (trichotomy) for all `x y ∈ S`, exactly one of `x < y`, `x = y`, or `y < x`
holds, and (ii) (transitivity) if `x < y` and `y < z` then `x < z`. We write
`x ≤ y` if `x < y` or `x = y`, and define `>`, `≥` analogously. -/
structure OrderedSet (α : Type u) where
  lt : α → α → Prop
  trichotomous : ∀ x y, lt x y ∨ x = y ∨ lt y x
  irrefl : ∀ x, ¬ lt x x
  trans : ∀ {x y z}, lt x y → lt y z → lt x z

namespace OrderedSet

variable {α : Type u} (S : OrderedSet α)

/-- The weak order associated to an ordered set. -/
def le (x y : α) : Prop :=
  S.lt x y ∨ x = y

/-- The axioms of an ordered set give a strict total order in mathlib's sense. -/
theorem toStrictTotalOrder : IsStrictTotalOrder α S.lt := by
  refine { trichotomous := ?_, irrefl := S.irrefl, trans := ?_ }
  · intro a b hab hba
    rcases S.trichotomous a b with h | h | h
    · exact (hab h).elim
    · exact h
    · exact (hba h).elim
  intro a b c h1 h2
  exact S.trans h1 h2

/-- A strict total order in mathlib yields the ordered-set structure described
in Definition 1.1.1. -/
def ofStrictTotalOrder {lt : α → α → Prop}
    (h : IsStrictTotalOrder α lt) : OrderedSet α := by
  refine { lt := lt, trichotomous := ?_, irrefl := ?_, trans := ?_ }
  · intro a b
    by_cases hab : lt a b
    · exact Or.inl hab
    by_cases hba : lt b a
    · exact Or.inr (Or.inr hba)
    · exact Or.inr (Or.inl (h.trichotomous a b hab hba))
  · exact h.irrefl
  · intro x y z hxy hyz
    exact h.trans x y z hxy hyz

end OrderedSet

/-! Definition 1.1.2: For a subset `E` of an ordered set `S`, (i) `E` is
bounded above if there is `b` with `x ≤ b` for all `x ∈ E`, and such a `b` is an
upper bound; (ii) `E` is bounded below if there is `b` with `x ≥ b` for all
`x ∈ E`, and such a `b` is a lower bound; (iii) an upper bound `b₀` is a least
upper bound (supremum) if `b₀ ≤ b` for all upper bounds `b`, written
`sup E = b₀`; (iv) a lower bound `b₀` is a greatest lower bound (infimum) if
`b ≤ b₀` for all lower bounds `b`, written `inf E = b₀`. A set bounded above and
below is called bounded. -/
namespace OrderedSet

variable {α : Type u} (S : OrderedSet α) (E : Set α)

/-- An element bounding every member of `E` above. -/
def IsUpperBound (b : α) : Prop :=
  ∀ ⦃x⦄, x ∈ E → S.le x b

/-- An element bounding every member of `E` below. -/
def IsLowerBound (b : α) : Prop :=
  ∀ ⦃x⦄, x ∈ E → S.le b x

/-- Existence of an upper bound for `E`. -/
def BoundedAbove : Prop :=
  ∃ b, IsUpperBound (S := S) (E := E) b

/-- Existence of a lower bound for `E`. -/
def BoundedBelow : Prop :=
  ∃ b, IsLowerBound (S := S) (E := E) b

/-- An upper bound that is minimal among all upper bounds. -/
def IsLeastUpperBound (b₀ : α) : Prop :=
  IsUpperBound (S := S) (E := E) b₀ ∧
    ∀ b, IsUpperBound (S := S) (E := E) b → S.le b₀ b

/-- A lower bound that is maximal among all lower bounds. -/
def IsGreatestLowerBound (b₀ : α) : Prop :=
  IsLowerBound (S := S) (E := E) b₀ ∧
    ∀ b, IsLowerBound (S := S) (E := E) b → S.le b b₀

/-- A set that is both bounded above and bounded below. -/
def Bounded : Prop :=
  BoundedAbove (S := S) (E := E) ∧ BoundedBelow (S := S) (E := E)

noncomputable def supremum (h : ∃ b₀, IsLeastUpperBound (S := S) (E := E) b₀) :
    α :=
  Classical.choose h

noncomputable def infimum (h : ∃ b₀, IsGreatestLowerBound (S := S) (E := E) b₀) :
    α :=
  Classical.choose h

lemma supremum_spec (h : ∃ b₀, IsLeastUpperBound (S := S) (E := E) b₀) :
    IsLeastUpperBound (S := S) (E := E) (supremum (S := S) (E := E) h) := by
  classical
  simpa [supremum] using Classical.choose_spec h

lemma infimum_spec (h : ∃ b₀, IsGreatestLowerBound (S := S) (E := E) b₀) :
    IsGreatestLowerBound (S := S) (E := E) (infimum (S := S) (E := E) h) := by
  classical
  simpa [infimum] using Classical.choose_spec h

/-- Definition 1.1.3: An ordered set has the least-upper-bound property if
every nonempty subset that is bounded above has a least upper bound (supremum)
in the set. -/
def LeastUpperBoundProperty : Prop :=
  ∀ {E : Set α}, E.Nonempty →
    BoundedAbove (S := S) (E := E) →
    ∃ b₀, IsLeastUpperBound (S := S) (E := E) b₀

section ComparisonWithMathlib

variable [Preorder α]

lemma boundedAbove_iff_bddAbove (hle : ∀ x y, S.le x y ↔ x ≤ y) :
    BoundedAbove (S := S) (E := E) ↔ BddAbove E := by
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x hx
    exact (hle x b).1 (hb hx)
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x hx
    exact (hle x b).2 (hb hx)

lemma boundedBelow_iff_bddBelow (hle : ∀ x y, S.le x y ↔ x ≤ y) :
    BoundedBelow (S := S) (E := E) ↔ BddBelow E := by
  constructor
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x hx
    exact (hle b x).1 (hb hx)
  · intro h
    rcases h with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro x hx
    exact (hle b x).2 (hb hx)

lemma leastUpperBound_iff_isLUB {b₀ : α} (hle : ∀ x y, S.le x y ↔ x ≤ y) :
    IsLeastUpperBound (S := S) (E := E) b₀ ↔ IsLUB E b₀ := by
  constructor
  · intro h
    rcases h with ⟨hUpper, hLeast⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hle x b₀).1 (hUpper hx)
    · intro b hb
      have hb' : IsUpperBound (S := S) (E := E) b := by
        intro x hx
        exact (hle x b).2 (hb hx)
      exact (hle b₀ b).1 (hLeast b hb')
  · intro h
    rcases h with ⟨hUpper, hLeast⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hle x b₀).2 (hUpper hx)
    · intro b hb
      have hb' : b ∈ upperBounds E := by
        intro x hx
        exact (hle x b).1 (hb hx)
      exact (hle b₀ b).2 (hLeast hb')

lemma greatestLowerBound_iff_isGLB {b₀ : α} (hle : ∀ x y, S.le x y ↔ x ≤ y) :
    IsGreatestLowerBound (S := S) (E := E) b₀ ↔ IsGLB E b₀ := by
  constructor
  · intro h
    rcases h with ⟨hLower, hGreatest⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hle b₀ x).1 (hLower hx)
    · intro b hb
      have hb' : IsLowerBound (S := S) (E := E) b := by
        intro x hx
        exact (hle b x).2 (hb hx)
      exact (hle b b₀).1 (hGreatest b hb')
  · intro h
    rcases h with ⟨hLower, hGreatest⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hle b₀ x).2 (hLower hx)
    · intro b hb
      have hb' : b ∈ lowerBounds E := by
        intro x hx
        exact (hle b x).1 (hb hx)
      exact (hle b b₀).2 (hGreatest hb')

lemma leastUpperBoundProperty_iff (hle : ∀ x y, S.le x y ↔ x ≤ y) :
    LeastUpperBoundProperty (S := S) ↔
      ∀ {E : Set α}, E.Nonempty → BddAbove E → ∃ b₀, IsLUB E b₀ := by
  constructor
  · intro h E hE hB
    have hB' : BoundedAbove (S := S) (E := E) :=
      (boundedAbove_iff_bddAbove (S := S) (E := E) (hle := hle)).2 hB
    obtain ⟨b₀, hb₀⟩ := h hE hB'
    exact ⟨b₀, (leastUpperBound_iff_isLUB (S := S) (E := E) (hle := hle)).1 hb₀⟩
  · intro h E hE hB
    have hB' : BddAbove E :=
      (boundedAbove_iff_bddAbove (S := S) (E := E) (hle := hle)).1 hB
    obtain ⟨b₀, hb₀⟩ := h hE hB'
    exact ⟨b₀, (leastUpperBound_iff_isLUB (S := S) (E := E) (hle := hle)).2 hb₀⟩

end ComparisonWithMathlib

end OrderedSet

/-- Example 1.1.4: The subset `{x : ℚ | x^2 < 2}` has no supremum in `ℚ`, so
`ℚ` does not have the least-upper-bound property.  Equivalently, there is no
rational square root of `2`. -/
theorem rat_sq_lt_two_has_no_sup :
    ¬ ∃ q : ℚ, IsLUB {x : ℚ | x * x < (2 : ℚ)} q := by
  classical
  intro h
  rcases h with ⟨q, hq⟩
  let S : Set ℚ := {x : ℚ | x * x < (2 : ℚ)}
  have h_upper : ∀ ⦃x : ℚ⦄, x ∈ S → x ≤ q := by
    intro x hx
    exact hq.1 hx
  have h_least : ∀ ⦃b : ℚ⦄, b ∈ upperBounds S → q ≤ b := by
    intro b hb
    exact hq.2 hb
  have h_one_mem : (1 : ℚ) ∈ S := by
    change (1 : ℚ) * 1 < 2
    norm_num
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one (h_upper h_one_mem)
  have hmem_lt_sqrt :
      ∀ {x : ℚ}, x ∈ S → (x : ℝ) < Real.sqrt 2 := by
    intro x hx
    have hx' : (x : ℝ) ^ 2 < (2 : ℝ) := by
      have hx'' : (x : ℝ) * (x : ℝ) < (2 : ℝ) := by exact_mod_cast hx
      simpa [pow_two] using hx''
    have hx_sq : (x : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
      simpa [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))] using hx'
    have h_abs : |(x : ℝ)| < Real.sqrt 2 := by
      have h_abs' := (sq_lt_sq.mp hx_sq)
      have h_abs_sqrt : |Real.sqrt 2| = Real.sqrt 2 :=
        abs_of_nonneg (Real.sqrt_nonneg _)
      simpa [h_abs_sqrt] using h_abs'
    exact (abs_lt.mp h_abs).2
  by_cases hlt : (q : ℝ) < Real.sqrt 2
  · obtain ⟨r, hqr, hrlt⟩ := exists_rat_btwn hlt
    have hr_pos : 0 < (r : ℝ) := lt_trans (by exact_mod_cast hq_pos) hqr
    have hr_sq : (r : ℝ) ^ 2 < (2 : ℝ) := by
      have hr_sq' : (r : ℝ) ^ 2 < (Real.sqrt 2) ^ 2 := by
        have hr_abs : |(r : ℝ)| < |Real.sqrt 2| := by
          have hr_abs_r : |(r : ℝ)| = (r : ℝ) := abs_of_nonneg (le_of_lt hr_pos)
          have hs_abs : |Real.sqrt 2| = Real.sqrt 2 :=
            abs_of_nonneg (Real.sqrt_nonneg _)
          simpa [hr_abs_r, hs_abs] using hrlt
        exact (sq_lt_sq.mpr hr_abs)
      have hsqrt_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        have : 0 ≤ (2 : ℝ) := by norm_num
        simp
      simpa [hsqrt_sq] using hr_sq'
    have hr_mem : r ∈ S := by
      have hr_mul : (r : ℝ) * (r : ℝ) < (2 : ℝ) := by simpa [pow_two] using hr_sq
      have hr_rat : r * r < (2 : ℚ) := by exact_mod_cast hr_mul
      simpa [S] using hr_rat
    have hr_le_q : r ≤ q := h_upper hr_mem
    have hqr' : q < r := by exact_mod_cast hqr
    exact (not_lt_of_ge hr_le_q) hqr'
  · have hge : Real.sqrt 2 ≤ (q : ℝ) := le_of_not_gt hlt
    rcases lt_or_eq_of_le hge with hgt | hEq
    · obtain ⟨r, hr_gt, hr_lt_q⟩ := exists_rat_btwn hgt
      have hr_upper : r ∈ upperBounds S := by
        intro x hx
        have hx_lt : (x : ℝ) < r := lt_trans (hmem_lt_sqrt hx) hr_gt
        exact le_of_lt (by exact_mod_cast hx_lt)
      have hq_le_r : q ≤ r := h_least hr_upper
      have hr_lt_q' : r < q := by exact_mod_cast hr_lt_q
      exact (not_lt_of_ge hq_le_r) hr_lt_q'
    · exact (irrational_sqrt_two.ne_rat q) (by simp [hEq.symm])

/-- No rational number has square equal to `2`. -/
theorem rational_sq_eq_two_absurd : ¬ ∃ x : ℚ, x * x = (2 : ℚ) := by
  intro h
  rcases h with ⟨q, hq⟩
  have hsq_real : (q : ℝ) * (q : ℝ) = (2 : ℝ) := by exact_mod_cast hq
  have hsq_abs : Real.sqrt 2 = |(q : ℝ)| := by
    have hsq_pow : (q : ℝ) ^ 2 = (2 : ℝ) := by simpa [pow_two] using hsq_real
    have hsq_rt : Real.sqrt 2 = Real.sqrt ((q : ℝ) ^ 2) := by simp [hsq_pow]
    simpa [Real.sqrt_sq_eq_abs] using hsq_rt
  exact (irrational_sqrt_two.ne_rat (|q|)) (by simpa [Rat.cast_abs] using hsq_abs)

section FieldAxiomsSection

variable (F : Type u) [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]

/-- Definition 1.1.5: A field is a set `F` with addition and multiplication such
that (A1) if `x,y ∈ F` then `x + y ∈ F`; (A2) addition is commutative; (A3)
addition is associative; (A4) there is `0 ∈ F` with `0 + x = x`; (A5) every
`x` has an additive inverse `-x` with `x + (-x) = 0`; (M1) if `x,y ∈ F` then
`x * y ∈ F`; (M2) multiplication is commutative; (M3) multiplication is
associative; (M4) there is `1 ∈ F` with `1 * x = x` and `1 ≠ 0`; (M5) every
`x ≠ 0` has a multiplicative inverse `x⁻¹` with `x * x⁻¹ = 1`; and (D)
distributivity `x * (y + z) = x * y + x * z` holds. -/
structure FieldAxioms (F : Type u) [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F] :
    Prop where
  add_comm : ∀ x y : F, x + y = y + x
  add_assoc : ∀ x y z : F, (x + y) + z = x + (y + z)
  zero_add : ∀ x : F, 0 + x = x
  add_left_neg : ∀ x : F, x + (-x) = 0
  mul_comm : ∀ x y : F, x * y = y * x
  mul_assoc : ∀ x y z : F, (x * y) * z = x * (y * z)
  one_mul : ∀ x : F, (1 : F) * x = x
  mul_inv_cancel : ∀ {x : F}, x ≠ 0 → x * x⁻¹ = (1 : F)
  distrib : ∀ x y z : F, x * (y + z) = x * y + x * z
  one_ne_zero : (1 : F) ≠ (0 : F)

variable (F : Type u)

/-- Mathlib's `Field` structure satisfies the axioms in Definition 1.1.5. -/
lemma field_axioms_of_field [Field F] : FieldAxioms (F := F) := by
  refine ⟨?add_comm, ?add_assoc, ?zero_add, ?add_left_neg, ?mul_comm, ?mul_assoc,
      ?one_mul, ?mul_inv_cancel, ?distrib, ?one_ne_zero⟩
  · intro x y; exact add_comm x y
  · intro x y z; exact add_assoc x y z
  · intro x; exact zero_add x
  · intro x; simp
  · intro x y; exact mul_comm x y
  · intro x y z; exact mul_assoc x y z
  · intro x; exact one_mul x
  · intro x hx; simpa using (mul_inv_cancel₀ (a := x) hx)
  · intro x y z; simpa using (mul_add x y z)
  · exact one_ne_zero

/-- From the field axioms we can derive the right identity for addition. -/
lemma FieldAxioms.add_zero [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) (x : F) : x + 0 = x := by
  have := h.zero_add x
  simpa [h.add_comm x 0] using this

/-- From the field axioms we can derive right multiplication by `1`. -/
lemma FieldAxioms.mul_one [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) (x : F) : x * (1 : F) = x := by
  have := h.one_mul x
  simpa [h.mul_comm x 1] using this

/-- From the field axioms we obtain right distributivity. -/
lemma FieldAxioms.right_distrib [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) (x y z : F) :
    (x + y) * z = x * z + y * z := by
  calc
    (x + y) * z = z * (x + y) := by simp [h.mul_comm]
    _ = z * x + z * y := h.distrib _ _ _
    _ = x * z + y * z := by
      simp [h.mul_comm]

/-- From the field axioms we can show that `x * 0 = 0`. -/
lemma FieldAxioms.mul_zero [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) (x : F) : x * (0 : F) = 0 := by
  have hzero : x * 0 + -(x * 0) = x * 0 + x * 0 + -(x * 0) := by
    have hx0 : x * 0 = x * 0 + x * 0 := by
      have := h.distrib x 0 0
      simpa [h.zero_add] using this
    simpa using congrArg (fun t => t + -(x * 0)) hx0
  have hleft : x * 0 + -(x * 0) = 0 := by simpa using h.add_left_neg (x * 0)
  have hright : x * 0 + x * 0 + -(x * 0) = x * 0 := by
    calc
      x * 0 + x * 0 + -(x * 0) = x * 0 + (x * 0 + -(x * 0)) := by
        simpa using h.add_assoc (x * 0) (x * 0) (-(x * 0))
      _ = x * 0 + 0 := by simp [h.add_left_neg]
      _ = x * 0 := by simp [h.add_zero]
  have : 0 = x * 0 := by
    calc
      0 = x * 0 + x * 0 + -(x * 0) := by
        calc
          0 = x * 0 + -(x * 0) := by simpa [eq_comm] using hleft
          _ = x * 0 + x * 0 + -(x * 0) := hzero
      _ = x * 0 := hright
  simpa [eq_comm] using this

/-- From the field axioms we can show that `0 * x = 0`. -/
lemma FieldAxioms.zero_mul [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) (x : F) : (0 : F) * x = 0 := by
  calc
    (0 : F) * x = x * 0 := h.mul_comm _ _
    _ = 0 := FieldAxioms.mul_zero (F := F) (h := h) x

/-- Construct a mathlib `Field` structure from the axioms in Definition 1.1.5. -/
noncomputable def field_structure_from_axioms [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) : Field F := by
  classical
  -- First, build the commutative-ring structure from the axioms.
  let h_neg_add_cancel : ∀ a : F, -a + a = (0 : F) := by
    intro a
    calc
      (-a) + a = a + (-a) := by simpa using (h.add_comm (-a) a)
      _ = 0 := h.add_left_neg a
  letI commRing : CommRing F :=
    CommRing.ofMinimalAxioms (R := F) (add_assoc := h.add_assoc) (zero_add := h.zero_add)
      (neg_add_cancel := h_neg_add_cancel) (mul_assoc := h.mul_assoc) (mul_comm := h.mul_comm)
      (one_mul := h.one_mul) (left_distrib := h.distrib)
  -- Nontriviality follows from `1 ≠ 0`.
  haveI : Nontrivial F := ⟨⟨1, 0, h.one_ne_zero⟩⟩
  -- Every element is either a unit or zero, thanks to the given inverse axiom.
  have h_units : ∀ a : F, IsUnit a ∨ a = 0 := by
    intro a
    by_cases ha : a = 0
    · right; exact ha
    · left
      refine ⟨⟨a, a⁻¹, ?h₁, ?h₂⟩, rfl⟩
      · exact h.mul_inv_cancel ha
      · calc
          a⁻¹ * a = a * a⁻¹ := h.mul_comm _ _
          _ = 1 := h.mul_inv_cancel ha
  -- Turn this into a field structure.
  exact Field.ofIsUnitOrEqZero (R := F) h_units

/-- The axioms in Definition 1.1.5 recover the existence of a mathlib `Field`
structure. -/
lemma field_of_field_axioms [Add F] [Mul F] [Zero F] [One F] [Neg F] [Inv F]
    (h : FieldAxioms (F := F)) : Nonempty (Field F) := by
  exact ⟨field_structure_from_axioms (F := F) h⟩

/-- The book's axioms for a field are equivalent to the existence of a mathlib
`Field` structure using the same operations. -/
theorem field_iff_field_axioms :
    (∃ inst : Field F, (by let _ : Field F := inst; exact FieldAxioms (F := F))) ↔
      Nonempty (Field F) := by
  classical
  constructor
  · rintro ⟨inst, _⟩
    exact ⟨inst⟩
  · intro h
    rcases h with ⟨hField⟩
    refine ⟨hField, ?_⟩
    let _ : Field F := hField
    exact field_axioms_of_field (F := F)

/-- Example 1.1.6: The rationals `ℚ` form a field, while the integers `ℤ`
fail axiom (M5) because `2` has no multiplicative inverse; this is the only
field axiom that does not hold for `ℤ`. -/
theorem rationals_field : Nonempty (Field ℚ) := by
  exact ⟨inferInstance⟩

/-- The multiplicative inverse required by (M5) for `2 : ℤ` does not exist. -/
theorem two_mul_eq_one_int_absurd : ¬ ∃ x : ℤ, (2 : ℤ) * x = 1 := by
  intro h
  rcases h with ⟨x, hx⟩
  have hdiv : (2 : ℤ) ∣ (1 : ℤ) := ⟨x, hx.symm⟩
  have : False := by
    norm_num at hdiv
  exact this

/-- The usual ring structure on the integers does not extend to a field
structure. -/
theorem integers_not_field : ¬ IsField ℤ := by
  exact Int.not_isField

end FieldAxiomsSection

/-- Definition 1.1.7: An ordered field is a field equipped with a strict total
order such that (i) `x < y` implies `x + z < y + z` for all `x y z`, and
(ii) `0 < x` and `0 < y` imply `0 < x * y`. Elements with `0 < x` are positive,
those with `x < 0` are negative, `0 < x ∨ x = 0` are nonnegative, and
`x < 0 ∨ x = 0` are nonpositive. -/
structure OrderedFieldAxioms (F : Type u) [Field F] [LT F] : Prop where
  order : IsStrictTotalOrder F (· < ·)
  add_lt_add : ∀ {x y z : F}, x < y → x + z < y + z
  mul_pos : ∀ {x y : F}, 0 < x → 0 < y → 0 < x * y

section OrderedFieldTerminology

variable (F : Type u) [Field F] [LT F]

/-- An element is positive if it is greater than zero. -/
def isPositive (x : F) : Prop :=
  0 < x

/-- An element is negative if it is less than zero. -/
def isNegative (x : F) : Prop :=
  x < 0

/-- An element is nonnegative if it is positive or zero. -/
def isNonnegative (x : F) : Prop :=
  0 < x ∨ x = 0

/-- An element is nonpositive if it is negative or zero. -/
def isNonpositive (x : F) : Prop :=
  x < 0 ∨ x = 0

end OrderedFieldTerminology

variable (F : Type u)

/-- Mathlib's ordered ring structure (`Field` together with a linear order and
compatibility axioms) satisfies the ordered-field axioms in Definition 1.1.7. -/
lemma orderedFieldAxioms_of_isStrictOrderedRing [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] : OrderedFieldAxioms (F := F) := by
  refine ⟨?order, ?add_lt_add, ?mul_pos⟩
  · infer_instance
  · intro x y z hxy
    simpa [add_comm] using add_lt_add_right hxy z
  · intro x y hx hy
    exact mul_pos hx hy

/-- The book's ordered-field axioms are equivalent to the existence of a mathlib
structure using the same operations. -/
theorem orderedField_iff_isStrictOrderedRing [Field F] [LinearOrder F] :
    OrderedFieldAxioms (F := F) ↔ IsStrictOrderedRing F := by
  constructor
  · intro h
    have add_le_add_left : ∀ a b : F, a ≤ b → ∀ c, a + c ≤ b + c := by
      intro a b hab c
      rcases lt_or_eq_of_le hab with hlt | hEq
      · exact (h.add_lt_add (z := c) hlt).le
      · simp [hEq]
    letI : IsOrderedAddMonoid F :=
      { add_le_add_left := add_le_add_left
        add_le_add_right := by
          intro a b hab c
          simpa [add_comm] using (add_le_add_left a b hab c) }
    have hzero_lt_one : (0 : F) < 1 := by
      rcases lt_trichotomy (0 : F) (1 : F) with hlt | hEq | hgt
      · exact hlt
      · exact (False.elim (one_ne_zero hEq.symm))
      · have hneg : (0 : F) < (-1 : F) := by
          have h' := h.add_lt_add (x := 1) (y := 0) (z := -1) hgt
          simpa using h'
        have hpos : (0 : F) < (-1 : F) * (-1 : F) := h.mul_pos hneg hneg
        simpa using hpos
    letI : ZeroLEOneClass F := ⟨hzero_lt_one.le⟩
    refine IsStrictOrderedRing.of_mul_pos (R := F) (mul_pos := ?_)
    intro a b ha hb
    exact h.mul_pos ha hb
  · intro h
    exact orderedFieldAxioms_of_isStrictOrderedRing (F := F)

section OrderedFieldInequalities

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {x y z w : F}

/-- Proposition 1.1.8: Let `F` be an ordered field and `x y z w ∈ F`.
(i) If `x > 0`, then `-x < 0` (and conversely).
(ii) If `x > 0` and `y < z`, then `x * y < x * z`.
(iii) If `x < 0` and `y < z`, then `x * y > x * z`.
(iv) If `x ≠ 0`, then `x^2 > 0`.
(v) If `0 < x < y`, then `0 < 1 / y < 1 / x`.
(vi) If `0 < x < y`, then `x^2 < y^2`.
(vii) If `x ≤ y` and `z ≤ w`, then `x + z ≤ y + w`. -/
theorem orderedField_neg_of_pos_iff : x > 0 ↔ -x < 0 := by
  -- `0 < x` is equivalent to `-x < 0` via the positivity of a double negation
  simp

theorem orderedField_mul_lt_mul_left_of_pos (hx : 0 < x) (hyz : y < z) :
    x * y < x * z := by
  exact mul_lt_mul_of_pos_left hyz hx

theorem orderedField_mul_gt_mul_left_of_neg (hx : x < 0) (hyz : y < z) :
    x * y > x * z := by
  exact mul_lt_mul_of_neg_left hyz hx

theorem orderedField_sq_pos_of_ne_zero (hx : x ≠ 0) : x ^ 2 > 0 := by
  simpa using (sq_pos_of_ne_zero hx)

theorem orderedField_inv_bounds_of_lt (hx : 0 < x) (hxy : x < y) :
    0 < (1 / y) ∧ 1 / y < 1 / x := by
  have hy : 0 < y := lt_trans hx hxy
  have hinv_y : 0 < (1 / y) := by
    simpa [one_div] using inv_pos.mpr hy
  have hinv_lt : 1 / y < 1 / x := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hx hxy)
  exact ⟨hinv_y, hinv_lt⟩

theorem orderedField_sq_lt_sq_of_pos_of_lt (hx : 0 < x) (hxy : x < y) :
    x ^ 2 < y ^ 2 := by
  have hy : 0 < y := lt_trans hx hxy
  have h₁ : x * x < x * y := mul_lt_mul_of_pos_left hxy hx
  have h₂ : x * y < y * y := mul_lt_mul_of_pos_right hxy hy
  have hxy' : x * x < y * y := lt_trans h₁ h₂
  simpa [pow_two] using hxy'

theorem orderedField_add_le_add (hxy : x ≤ y) (hzw : z ≤ w) :
    x + z ≤ y + w := by
  exact add_le_add hxy hzw

end OrderedFieldInequalities

/-- Proposition 1.1.9: In an ordered field, if `x * y > 0` then either both
`x` and `y` are positive or both are negative. -/
theorem pos_mul_same_sign {F : Type u} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {x y : F}
    (h : x * y > 0) :
    (0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0) := by
  -- Directly unpack the characterization of a positive product.
  simpa using (mul_pos_iff.mp h)

/-- Example 1.1.10: The complex numbers `ℂ = {x + iy | x y ∈ ℝ}` satisfy
`I^2 = -1` and form a field.  No ordering of `ℂ` can make it an ordered field:
in every ordered field, `-1 < 0` and squares of nonzero elements are positive,
but `(I : ℂ)^2 = -1`. -/
theorem complex_field : Nonempty (Field ℂ) := by
  exact ⟨inferInstance⟩

lemma complex_I_square_pos [LinearOrder ℂ] [IsStrictOrderedRing ℂ] :
    (0 : ℂ) < (Complex.I : ℂ) ^ 2 := by
  simpa using
    (orderedField_sq_pos_of_ne_zero (x := (Complex.I : ℂ)) Complex.I_ne_zero)

/-- There is no way to equip `ℂ` with a linear order making it an ordered
field. -/
theorem complex_not_linearOrderedField :
    ¬ ∃ _ : LinearOrder ℂ, IsStrictOrderedRing ℂ := by
  intro h
  rcases h with ⟨hlin, hstrict⟩
  -- Use the order from the hypothesis in the rest of the argument.
  let _ : LinearOrder ℂ := hlin
  let _ : IsStrictOrderedRing ℂ := hstrict
  -- In any ordered field, the square of a nonzero element is positive.
  have hpos : (0 : ℂ) < (-1) := by
    have hIpos : (0 : ℂ) < (Complex.I : ℂ) ^ 2 := complex_I_square_pos
    simpa [Complex.I_sq] using hIpos
  -- But `-1` is negative because `1` is positive.
  have hneg : (-1 : ℂ) < 0 :=
    (orderedField_neg_of_pos_iff (x := (1 : ℂ))).1 (show (0 : ℂ) < 1 from zero_lt_one)
  exact (lt_asymm hneg hpos).elim

/-- Proposition 1.1.11: In an ordered field with the least-upper-bound
property, every nonempty subset that is bounded below has an infimum. -/
theorem infimum_exists_of_bddBelow {F : Type u} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F]
    (lub : ∀ {E : Set F}, E.Nonempty → BddAbove E → ∃ b₀, IsLUB E b₀)
    {A : Set F} (hA : A.Nonempty) (hB : BddBelow A) :
    ∃ infA, IsGLB A infA := by
  classical
  rcases hA with ⟨a₀, ha₀⟩
  let B : Set F := (fun x : F => -x) '' A
  have hB_nonempty : B.Nonempty := ⟨-a₀, ⟨a₀, ha₀, rfl⟩⟩
  rcases hB with ⟨b₀, hb₀⟩
  have hB_bddAbove : BddAbove B := by
    refine ⟨-b₀, ?_⟩
    intro y hy
    rcases hy with ⟨x, hxA, rfl⟩
    have hb_le : b₀ ≤ x := hb₀ hxA
    have hneg : -x ≤ -b₀ := neg_le_neg hb_le
    simpa using hneg
  obtain ⟨c, hc⟩ := lub (E := B) hB_nonempty hB_bddAbove
  refine ⟨-c, ?_⟩
  constructor
  · intro x hxA
    have hxB : -x ∈ B := ⟨x, hxA, rfl⟩
    have hxc : -x ≤ c := hc.1 hxB
    have hneg : -c ≤ x := by
      have := neg_le_neg hxc
      simpa [neg_neg] using this
    exact hneg
  · intro b hbLower
    have hb_upper : -b ∈ upperBounds B := by
      intro y hy
      rcases hy with ⟨x, hxA, rfl⟩
      have hbx : b ≤ x := hbLower hxA
      have hneg : -x ≤ -b := neg_le_neg hbx
      simpa using hneg
    have hcle : c ≤ -b := hc.2 hb_upper
    have hneg : b ≤ -c := by
      have := neg_le_neg hcle
      simpa [neg_neg] using this
    exact hneg

end Section01
end Chap01
