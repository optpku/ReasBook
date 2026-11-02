import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Basic

-- Declarations for this item will be appended below by the statement pipeline.
-- `lean_leansearch` is unavailable in this session, so this file uses direct mathlib primitives.

section Definition631Extra1

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "IntAssignment" => Rq →₀ ℤ

open scoped IntegerVectorNotation

/-- The shifted weighted vector sum associated to a finitely supported integer family. -/
def pure_integer_balance (f : Rq) (x : IntAssignment) : Rq :=
  f + x.sum (fun r n ↦ (n : ℝ) • r)

/-- `pure_integer_balance f x` is the coordinatewise sum `f_i + ∑_r x_r r_i`. -/
@[simp] theorem pure_integer_balance_apply (f : Rq) (x : IntAssignment) (i : Fin q) :
    pure_integer_balance f x i = f i + x.sum (fun r n ↦ (n : ℝ) * r i) := by
  rw [pure_integer_balance, Pi.add_apply, Finsupp.sum_apply']
  simp [Pi.smul_apply, smul_eq_mul]

/-- A finitely supported family is feasible for the pure integer infinite relaxation when it is
coordinatewise nonnegative and its shifted weighted sum lies in the integer lattice. -/
class pure_integer_feasible_point (f : Rq) (x : IntAssignment) : Prop where
  /-- A feasible family is coordinatewise nonnegative. -/
  nonneg : ∀ r, 0 ≤ x r
  /-- The shifted weighted sum belongs to the integer lattice. -/
  lattice_mem : pure_integer_balance f x ∈ ℤ^q

namespace pure_integer_feasible_point

/-- A feasible point has lattice-valued shifted balance in the canonical vector form. -/
theorem balance_mem_integerVectors {f : Rq} {x : IntAssignment}
    (hx : pure_integer_feasible_point f x) :
    pure_integer_balance f x ∈ ℤ^q :=
  hx.lattice_mem

end pure_integer_feasible_point

/-- Helper for this entry: the pure integer infinite relaxation `G_f` consists of the
finitely supported families `x : (ℝ^q) →₀ ℤ` with `x_r ≥ 0` for all `r` and
`f + ∑ r, x_r r ∈ ℤ^q`. -/
def pure_integer_feasible_set (f : Rq) : Set IntAssignment :=
  pure_integer_feasible_point f

/-- Unfolding lemma for membership in `pure_integer_feasible_set`. -/
theorem mem_pure_integer_feasible_set_iff {f : Rq} {x : IntAssignment} :
    x ∈ pure_integer_feasible_set f ↔
      (∀ r, 0 ≤ x r) ∧
        pure_integer_balance f x ∈ ℤ^q := by
  constructor
  · intro hx
    exact ⟨hx.nonneg, hx.lattice_mem⟩
  · rintro ⟨h_nonneg, h_lattice⟩
    exact ⟨h_nonneg, h_lattice⟩

/-- Helper for this entry: the family supported at `-f` with value `1` is a feasible
solution of the pure integer infinite relaxation. -/
theorem single_neg_f_mem_pure_integer_feasible_set (f : Rq) :
    Finsupp.single (-f) (1 : ℤ) ∈ pure_integer_feasible_set f := by
  rw [mem_pure_integer_feasible_set_iff]
  constructor
  · -- The singleton assignment is coordinatewise nonnegative.
    intro s
    by_cases hs : s = -f
    · simp [hs]
    · simp [hs]
  · -- The singleton contribution cancels the shift `f`, so the balance is the zero vector.
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨0, ?_⟩
    funext i
    simp [pure_integer_balance]

/-- Helper for this entry:
the family supported at `r` and `-f-r`, each with value `1`,
is a feasible solution of the pure integer infinite relaxation. -/
theorem pair_mem_pure_integer_feasible_set (f r : Rq) :
    Finsupp.single r (1 : ℤ) + Finsupp.single (-f - r) (1 : ℤ) ∈ pure_integer_feasible_set f :=
  by
  rw [mem_pure_integer_feasible_set_iff]
  constructor
  · -- Each coordinate is a sum of two nonnegative singleton coefficients.
    intro s
    have hleft : 0 ≤ Finsupp.single r (1 : ℤ) s := by
      by_cases hs : s = r
      · simp [hs]
      · simp [hs]
    have hright : 0 ≤ Finsupp.single (-f - r) (1 : ℤ) s := by
      by_cases hs : s = -f - r
      · simp [hs]
      · simp [hs]
    simpa using add_nonneg hleft hright
  · -- The two chosen support points sum to `-f`, so the shifted balance is again zero.
    refine (mem_integerVectors_iff).2 ?_
    refine ⟨0, ?_⟩
    funext i
    rw [pure_integer_balance_apply, Finsupp.sum_add_index]
    · simp
    · simp
    · intro a ha b₁ b₂
      simp [Int.cast_add, add_mul]

/-- Helper for this entry: a function `π : ℝ^q → ℝ` is valid for `G_f` if `π ≥ 0`
pointwise and the inequality `∑ r, π r * x_r ≥ 1` holds for every feasible `x ∈ G_f`. -/
class pure_integer_valid_function (f : Rq) (π : Rq → ℝ) : Prop where
  /-- A valid function is pointwise nonnegative. -/
  nonneg : ∀ r, 0 ≤ π r
  /-- A valid function satisfies the defining inequality on every feasible point. -/
  one_le_sum : ∀ ⦃x : IntAssignment⦄, x ∈ pure_integer_feasible_set f →
    1 ≤ x.sum (fun r n ↦ (n : ℝ) * π r)

/-- A valid function satisfies the defining inequality on every feasible point. -/
theorem pure_integer_valid_function_one_le_sum {f : Rq}
    {π : Rq → ℝ} (hπ : pure_integer_valid_function f π)
    {x : IntAssignment} (hx : x ∈ pure_integer_feasible_set f) :
    1 ≤ x.sum (fun r n ↦ (n : ℝ) * π r) :=
  hπ.one_le_sum hx

/-- Helper for this entry:
a valid function is minimal if every valid function below it
pointwise is equal to it. -/
class pure_integer_minimal_valid_function (f : Rq) (π : Rq → ℝ)
    : Prop extends pure_integer_valid_function f π where
  /-- Pointwise domination by another valid function forces equality. -/
  eq_of_le : ∀ ⦃π' : Rq → ℝ⦄, pure_integer_valid_function f π' →
    (∀ r, π' r ≤ π r) → π' = π

/-- A minimal valid function is valid. -/
instance pure_integer_minimal_valid_function_to_valid_function {f : Rq}
    {π : Rq → ℝ} [hπ : pure_integer_minimal_valid_function f π] :
    pure_integer_valid_function f π :=
  { nonneg := hπ.nonneg
    one_le_sum := hπ.one_le_sum }

/-- A minimal valid function is determined among valid functions by pointwise domination. -/
theorem pure_integer_minimal_valid_function_eq_of_le {f : Rq}
    {π π' : Rq → ℝ} (hπ : pure_integer_minimal_valid_function f π)
    (hπ' : pure_integer_valid_function f π') (hle : ∀ r, π' r ≤ π r) :
    π' = π :=
  hπ.eq_of_le hπ' hle

/-- Helper for Definition 6.3.1-extra-1: if two coefficient functions agree on
`x.support`, then they give the same weighted sum against `x`. -/
lemma intAssignment_sum_eq_of_eq_on_support {x : IntAssignment} {ρ π : Rq → ℝ}
    (h_eq : ∀ s ∈ x.support, ρ s = π s) :
    x.sum (fun s n ↦ (n : ℝ) * ρ s) = x.sum (fun s n ↦ (n : ℝ) * π s) := by
  rw [Finsupp.sum, Finsupp.sum]
  exact Finset.sum_congr rfl (fun s hs ↦ by rw [h_eq s hs])

/-- Helper for Definition 6.3.1-extra-1: a nonnegative weighted sum is at least `1`
once one support term is already at least `1`. -/
lemma one_le_intAssignment_sum_of_one_le_term {x : IntAssignment} {ρ : Rq → ℝ} {r : Rq}
    (hx_nonneg : ∀ s, 0 ≤ x s) (hρ_nonneg : ∀ s, 0 ≤ ρ s) (hr_mem : r ∈ x.support)
    (hterm : 1 ≤ (x r : ℝ) * ρ r) :
    1 ≤ x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
  have hsum_nonneg : ∀ s ∈ x.support, 0 ≤ (x s : ℝ) * ρ s := by
    intro s hs
    exact mul_nonneg (by exact_mod_cast hx_nonneg s) (hρ_nonneg s)
  calc
    1 ≤ (x r : ℝ) * ρ r := hterm
    _ ≤ x.sum (fun s n ↦ (n : ℝ) * ρ s) := by
      rw [Finsupp.sum]
      exact Finset.single_le_sum hsum_nonneg hr_mem

/-- Helper for this entry: lowering one coefficient to `min (π r) 1` preserves
validity for the pure integer infinite relaxation. -/
lemma pure_integer_valid_function_lower_at_one {f : Rq}
    {π : Rq → ℝ} (hπ : pure_integer_valid_function f π) (r : Rq) :
    pure_integer_valid_function f (fun s ↦ if s = r then min (π r) 1 else π s) := by
  classical
  let ρ : Rq → ℝ := fun s ↦ if s = r then min (π r) 1 else π s
  refine { nonneg := ?_, one_le_sum := ?_ }
  · -- Only the value at `r` changes, and it stays between `0` and `1`.
    intro s
    by_cases hs : s = r
    · simpa [ρ, hs] using le_min (hπ.nonneg r) zero_le_one
    · simpa [ρ, hs] using hπ.nonneg s
  · intro x hx
    have hx_nonneg : ∀ s, 0 ≤ x s := (mem_pure_integer_feasible_set_iff.mp hx).1
    have hρ_nonneg : ∀ s, 0 ≤ ρ s := by
      intro s
      by_cases hs : s = r
      · simpa [ρ, hs] using le_min (hπ.nonneg r) zero_le_one
      · simpa [ρ, hs] using hπ.nonneg s
    by_cases hle : π r ≤ 1
    · -- If `π r ≤ 1`, the lowered function agrees with `π` everywhere.
      have hsum_eq :
          x.sum (fun s n ↦ (n : ℝ) * ρ s) =
            x.sum (fun s n ↦ (n : ℝ) * π s) :=
        intAssignment_sum_eq_of_eq_on_support (x := x) (ρ := ρ) (π := π) <| by
          intro s hs
          by_cases hs_eq : s = r
          · simp [ρ, hs_eq, hle]
          · simp [ρ, hs_eq]
      have hsum_eq' :
          x.sum (fun s n ↦ (n : ℝ) * (if s = r then min (π r) 1 else π s)) =
            x.sum (fun s n ↦ (n : ℝ) * π s) := by
        simpa [ρ] using hsum_eq
      rw [hsum_eq']
      exact pure_integer_valid_function_one_le_sum hπ hx
    · -- Otherwise the changed value is exactly `1`.
      have hlt : 1 < π r := lt_of_not_ge hle
      by_cases hxr : x r = 0
      · -- If `x r = 0`, the modified coefficient is outside the support of `x`.
        have hr_not_mem : r ∉ x.support := by
          simpa [Finsupp.mem_support_iff] using hxr
        have hsum_eq :
            x.sum (fun s n ↦ (n : ℝ) * ρ s) =
              x.sum (fun s n ↦ (n : ℝ) * π s) :=
          intAssignment_sum_eq_of_eq_on_support (x := x) (ρ := ρ) (π := π) <| by
            intro s hs
            by_cases hs_eq : s = r
            · exact False.elim <| hr_not_mem (hs_eq ▸ hs)
            · simp [ρ, hs_eq]
        have hsum_eq' :
            x.sum (fun s n ↦ (n : ℝ) * (if s = r then min (π r) 1 else π s)) =
              x.sum (fun s n ↦ (n : ℝ) * π s) := by
          simpa [ρ] using hsum_eq
        rw [hsum_eq']
        exact pure_integer_valid_function_one_le_sum hπ hx
      · -- If `x r ≠ 0`, then `x r ≥ 1`, so the contribution at `r` already gives the bound.
        have hr_mem : r ∈ x.support := by
          simpa [Finsupp.mem_support_iff] using hxr
        have hxr_pos : 0 < x r := lt_of_le_of_ne (hx_nonneg r) (Ne.symm hxr)
        have hxr_ge_one : (1 : ℤ) ≤ x r := by
          simpa using Int.add_one_le_iff.mpr hxr_pos
        have hxr_ge_one_real : (1 : ℝ) ≤ (x r : ℝ) := by
          exact_mod_cast hxr_ge_one
        have hρr : ρ r = 1 := by
          simp [ρ, min_eq_right (le_of_lt hlt)]
        have hterm : 1 ≤ (x r : ℝ) * ρ r := by
          simpa [hρr] using hxr_ge_one_real
        exact one_le_intAssignment_sum_of_one_le_term
          (x := x) (ρ := ρ) (r := r) hx_nonneg hρ_nonneg hr_mem hterm

/-- Definition 6.3.1-extra-1: every minimal valid function satisfies `π r ≤ 1`. -/
theorem pure_integer_minimal_valid_function_le_one {f : Rq}
    {π : Rq → ℝ} (hπ : pure_integer_minimal_valid_function f π) (r : Rq) :
    π r ≤ 1 := by
  -- Compare `π` with the valid function obtained by lowering only the value at `r`.
  have hvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  have hρ :
      pure_integer_valid_function f (fun s ↦ if s = r then min (π r) 1 else π s) :=
    pure_integer_valid_function_lower_at_one hvalid r
  have hρ_le : ∀ s, (if s = r then min (π r) 1 else π s) ≤ π s := by
    intro s
    by_cases hs : s = r
    · rw [if_pos hs, hs]
      exact min_le_left _ _
    · rw [if_neg hs]
  have hEq :
      (fun s ↦ if s = r then min (π r) 1 else π s) = π :=
    pure_integer_minimal_valid_function_eq_of_le hπ hρ hρ_le
  -- Reading off the equality at `r` gives `π r = min (π r) 1`, hence `π r ≤ 1`.
  calc
    π r = min (π r) 1 := by
      simpa using congrArg (fun ψ ↦ ψ r) hEq.symm
    _ ≤ 1 := min_le_right _ _

/-- Helper for this entry: every minimal valid function satisfies `π (-f) = 1`. -/
theorem pure_integer_minimal_valid_function_neg_f_eq_one {f : Rq}
    {π : Rq → ℝ} (hπ : pure_integer_minimal_valid_function f π) :
    π (-f) = 1 := by
  have hvalid : pure_integer_valid_function f π :=
    { nonneg := hπ.nonneg
      one_le_sum := hπ.one_le_sum }
  -- Evaluating validity on the singleton feasible point gives the lower bound at `-f`.
  have hone_le : 1 ≤ π (-f) := by
    have hsum :
        (Finsupp.single (-f) (1 : ℤ)).sum (fun r n ↦ (n : ℝ) * π r) = π (-f) := by
      simp
    rw [← hsum]
    exact pure_integer_valid_function_one_le_sum hvalid
      (single_neg_f_mem_pure_integer_feasible_set f)
  have hle_one : π (-f) ≤ 1 := pure_integer_minimal_valid_function_le_one hπ (-f)
  exact le_antisymm hle_one hone_le

/-- Helper for this entry: every valid function satisfies the lower-bound half of the
symmetry relation `π r + π (-f-r) ≥ 1`. -/
theorem pure_integer_valid_function_symmetry_lower_bound {f : Rq}
    {π : Rq → ℝ} (hπ : pure_integer_valid_function f π) (r : Rq) :
    1 ≤ π r + π (-f - r) := by
  -- Apply validity to the two-point feasible assignment described in the source text.
  have hsum :
      (Finsupp.single r (1 : ℤ) + Finsupp.single (-f - r) (1 : ℤ)).sum
          (fun s n ↦ (n : ℝ) * π s) =
        π r + π (-f - r) := by
    rw [Finsupp.sum_add_index]
    · simp
    · simp
    · intro a ha b₁ b₂
      simp [Int.cast_add, add_mul]
  rw [← hsum]
  exact pure_integer_valid_function_one_le_sum hπ
    (pair_mem_pure_integer_feasible_set f r)

/-- Helper for this entry: `π` satisfies the symmetry condition when
`π r + π (-f-r) = 1` for every `r ∈ ℝ^q`. -/
def satisfies_symmetry_condition (f : Rq) (π : Rq → ℝ) : Prop :=
  ∀ r, π r + π (-f - r) = 1

/-- Unfolding lemma for `satisfies_symmetry_condition`. -/
theorem satisfies_symmetry_condition_iff {f : Rq} {π : Rq → ℝ} :
    satisfies_symmetry_condition f π ↔ ∀ r, π r + π (-f - r) = 1 :=
  Iff.rfl

/-- Helper for this entry: `π` is periodic when it is invariant under translation by
integer vectors. -/
def integer_periodic_on_rn (π : Rq → ℝ) : Prop :=
  ∀ (r : Rq) (w : Fin q → ℤ), π r = π (r + fun i ↦ (w i : ℝ))

/-- Unfolding lemma for `integer_periodic_on_rn`. -/
theorem integer_periodic_on_rn_iff {π : Rq → ℝ} :
    integer_periodic_on_rn π ↔
      ∀ (r : Rq) (w : Fin q → ℤ), π r = π (r + fun i ↦ (w i : ℝ)) :=
  Iff.rfl

end Definition631Extra1
