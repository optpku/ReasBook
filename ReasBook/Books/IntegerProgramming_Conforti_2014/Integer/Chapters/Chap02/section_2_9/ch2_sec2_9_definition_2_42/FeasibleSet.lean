module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_1.ch1_sec1_1_definition_1_2.FeasibleRegion

@[expose] public section

namespace Mixing

open scoped IntegerVectorNotation

variable {n : ℕ}

/-- The source tuple bridge sending a purchase vector `x` and production amount `y` to the
canonical mixed point `(x, fun _ ↦ y)` in `MixedRealPoint n 1`. -/
def point (x : Fin n → ℝ) (y : ℝ) : MixedRealPoint n 1 :=
  (x, fun _ ↦ y)

/-- Helper for Definition 2.42: the purchase block of `point x y` is exactly `x`. -/
theorem point_fst
    {x : Fin n → ℝ} {y : ℝ} :
    (point x y).1 = x := by
  -- The tuple bridge stores the purchase coordinates in the first component.
  rfl

/-- Helper for Definition 2.42: every continuous coordinate of `point x y` is the production
amount `y`. -/
theorem point_snd
    {x : Fin n → ℝ} {y : ℝ} (j : Fin 1) :
    (point x y).2 j = y := by
  -- The tuple bridge uses the constant one-coordinate production block.
  fin_cases j
  rfl

/-- Definition 2.42. The mixing set for the make-or-buy problem with demand vector `b` is the
Chapter 1 MILP feasible-set owner specialized to one production variable and the covering
inequalities `b i ≤ y + x i` for every `i`. -/
def feasibleSet (b : Fin n → ℝ) : Set (MixedRealPoint n 1) :=
  milp_feasible_set
    (fun i j ↦ if j = i then (-1 : ℝ) else 0)
    (fun _ _ ↦ (-1 : ℝ))
    (fun i ↦ -b i)

end Mixing

namespace MixingNotation

scoped notation:max "MIX[" b "]" => Mixing.feasibleSet b

end MixingNotation

namespace Mixing

open scoped IntegerVectorNotation
open scoped MixingNotation

/-- Membership in `MIX[b]` is exactly nonnegativity of the production scalar, nonnegativity and
integrality of the purchase block, and the covering inequalities `b i ≤ y + x i`. -/
theorem mem_feasibleSet_iff
    {b : Fin n → ℝ} {xy : MixedRealPoint n 1} :
    xy ∈ MIX[b] ↔
      0 ≤ xy.2 0 ∧
        0 ≤ xy.1 ∧
        xy.1 ∈ ℤ^n ∧
        ∀ i : Fin n, b i ≤ xy.2 0 + xy.1 i := by
  rw [feasibleSet, mem_milp_feasible_set_iff_mem_mixed_integer_lattice]
  constructor
  · rintro ⟨hineq, hx_nonneg, hy_nonneg, hxy_lattice⟩
    have hx_integral : xy.1 ∈ ℤ^n := by
      exact mem_integerVectors_iff.mpr <| mem_mixed_integer_lattice_exists_iff.mp hxy_lattice
    refine ⟨hy_nonneg 0, hx_nonneg, hx_integral, ?_⟩
    intro i
    have hi := hineq i
    simpa [Matrix.mulVec, dotProduct] using hi
  · rintro ⟨hy_nonneg, hx_nonneg, hx_integral, hcover⟩
    refine ⟨?_, hx_nonneg, ?_, ?_⟩
    · intro i
      have hi := hcover i
      simpa [Matrix.mulVec, dotProduct] using hi
    · intro j
      fin_cases j
      simpa using hy_nonneg
    · exact mem_mixed_integer_lattice_exists_iff.mpr <| mem_integerVectors_iff.mp hx_integral

/-- `MIX[b]` is the Chapter 1 MILP feasible-set owner specialized to one continuous production
variable and the row inequalities `-x_i - y ≤ -b_i`. -/
theorem feasibleSet_eq_milp_feasible_set
    (b : Fin n → ℝ) :
    MIX[b] =
      milp_feasible_set
        (fun i j ↦ if j = i then (-1 : ℝ) else 0)
        (fun _ _ ↦ (-1 : ℝ))
        (fun i ↦ -b i) :=
  rfl

/-- Membership of the source-form point `point x y` in `MIX[b]` is exactly the textbook
condition `y ∈ ℝ_+`, `x ∈ ℤ_+^n`, and `b i ≤ y + x i` for all `i`. -/
theorem point_mem_feasibleSet_iff
    {b : Fin n → ℝ} {x : Fin n → ℝ} {y : ℝ} :
    point x y ∈ MIX[b] ↔
      0 ≤ y ∧
        0 ≤ x ∧
        x ∈ ℤ^n ∧
        ∀ i : Fin n, b i ≤ y + x i := by
  -- Rewrite the mixed-point membership criterion through the source tuple bridge.
  simpa [point_fst, point_snd] using
    (mem_feasibleSet_iff : point x y ∈ MIX[b] ↔
      0 ≤ (point x y).2 0 ∧
        0 ≤ (point x y).1 ∧
        (point x y).1 ∈ ℤ^n ∧
        ∀ i : Fin n, b i ≤ (point x y).2 0 + (point x y).1 i)

end Mixing

end
