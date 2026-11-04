/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Bounds.Basic

@[expose] public section

namespace PureIntegerSlope

/-- The ambient real polyhedron
`P = {(x₁, x₂) ∈ ℝ² | -a₁ x₁ + a₂ x₂ ≤ 0, x₁ ≤ u, x₂ ≥ 0}`. -/
def polyhedron (a₁ a₂ u : ℤ) : Set (ℝ × ℝ) :=
  {p | -(a₁ : ℝ) * p.1 + (a₂ : ℝ) * p.2 ≤ 0 ∧ p.1 ≤ (u : ℝ) ∧ 0 ≤ p.2}

/-- Membership in `polyhedron a₁ a₂ u` means that the defining inequality,
the upper bound `x₁ ≤ u`, and the nonnegativity condition `x₂ ≥ 0` all hold. -/
theorem mem_polyhedron_iff
    {a₁ a₂ u : ℤ} {p : ℝ × ℝ} :
    p ∈ polyhedron a₁ a₂ u ↔
      -(a₁ : ℝ) * p.1 + (a₂ : ℝ) * p.2 ≤ 0 ∧
        p.1 ≤ (u : ℝ) ∧
        0 ≤ p.2 := by
  -- Membership is definitionally the conjunction of the three inequalities.
  rfl

/-- The discrete lattice set `S = P ∩ ℤ²`, represented on the integer carrier `ℤ × ℤ`. -/
def latticeSet (a₁ a₂ u : ℤ) : Set (ℤ × ℤ) :=
  {p | -a₁ * p.1 + a₂ * p.2 ≤ 0 ∧ p.1 ≤ u ∧ 0 ≤ p.2}

/-- Membership in `latticeSet a₁ a₂ u` is exactly the integer-coordinate version of the defining
inequalities for `P`. -/
theorem mem_latticeSet_iff
    {a₁ a₂ u : ℤ} {p : ℤ × ℤ} :
    p ∈ latticeSet a₁ a₂ u ↔
      -a₁ * p.1 + a₂ * p.2 ≤ 0 ∧
        p.1 ≤ u ∧
        0 ≤ p.2 := by
  -- Membership is definitionally the integer version of the three inequalities.
  rfl

/-- The ambient real realization of `S = P ∩ ℤ²`. -/
def realLatticeSet (a₁ a₂ u : ℤ) : Set (ℝ × ℝ) :=
  polyhedron a₁ a₂ u ∩
    {p | p.1 ∈ Set.range (Int.cast : ℤ → ℝ)} ∩
      {p | p.2 ∈ Set.range (Int.cast : ℤ → ℝ)}

/-- Membership in `realLatticeSet a₁ a₂ u` means that the point lies in `polyhedron a₁ a₂ u`
and that both coordinates are integers. -/
theorem mem_realLatticeSet_iff
    {a₁ a₂ u : ℤ} {p : ℝ × ℝ} :
    p ∈ realLatticeSet a₁ a₂ u ↔
      p ∈ polyhedron a₁ a₂ u ∧
        p.1 ∈ Set.range (Int.cast : ℤ → ℝ) ∧
        p.2 ∈ Set.range (Int.cast : ℤ → ℝ) := by
  -- Reassociate the intersections defining the real lattice set.
  simp only [realLatticeSet, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]

/-- The ambient real lattice set is the coordinatewise real image of the discrete integer carrier
`latticeSet a₁ a₂ u`. -/
theorem realLatticeSet_eq_image_latticeSet
    (a₁ a₂ u : ℤ) :
    realLatticeSet a₁ a₂ u =
      (fun x : ℤ × ℤ ↦ ((x.1 : ℝ), (x.2 : ℝ))) '' latticeSet a₁ a₂ u := by
  -- Integer-coordinate witnesses identify the two presentations pointwise.
  ext p
  constructor
  · intro hp
    rw [mem_realLatticeSet_iff] at hp
    obtain ⟨hpP, ⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩ := hp
    refine ⟨(x₁, x₂), ?_, ?_⟩
    · rw [mem_latticeSet_iff]
      rw [mem_polyhedron_iff] at hpP
      rw [← hx₁, ← hx₂] at hpP
      exact_mod_cast hpP
    · exact Prod.ext hx₁ hx₂
  · rintro ⟨x, hx, rfl⟩
    rw [mem_latticeSet_iff] at hx
    rw [mem_realLatticeSet_iff, mem_polyhedron_iff]
    simp only [Set.mem_range]
    refine ⟨?_, ⟨x.1, rfl⟩, ⟨x.2, rfl⟩⟩
    exact_mod_cast hx

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
the origin belongs to the real lattice set whenever the first-coordinate bound is nonnegative. -/
lemma zero_mem_realLatticeSet
    {a₁ a₂ u : ℤ} (hu : 0 ≤ u) :
    (0 : ℝ × ℝ) ∈ realLatticeSet a₁ a₂ u := by
  -- Realize the origin as the coordinatewise real image of the integer origin.
  rw [realLatticeSet_eq_image_latticeSet]
  refine ⟨(0, 0), ?_, ?_⟩
  · rw [mem_latticeSet_iff]
    simp only [mul_zero, zero_add, le_refl, true_and]
    exact ⟨hu, trivial⟩
  · norm_num

/-- The slope `x₂ / x₁` attached to an integer point, viewed in `ℝ`. -/
noncomputable def slope (x : ℤ × ℤ) : ℝ :=
  (x.2 : ℝ) / (x.1 : ℝ)

/-- Unfolding equation for `slope`. -/
theorem slope_def
    (x : ℤ × ℤ) :
    slope x = (x.2 : ℝ) / (x.1 : ℝ) := by
  -- Unfold the slope definition.
  rfl

/-- The lattice points of `S` with positive first coordinate, i.e. the domain of the source
maximization problem. -/
def admissiblePoints (a₁ a₂ u : ℤ) : Set (ℤ × ℤ) :=
  {x | x ∈ latticeSet a₁ a₂ u ∧ 0 < x.1}

/-- Membership in `admissiblePoints a₁ a₂ u` means that the integer point lies in
`latticeSet a₁ a₂ u` and has positive first coordinate. -/
theorem mem_admissiblePoints_iff
    {a₁ a₂ u : ℤ} {x : ℤ × ℤ} :
    x ∈ admissiblePoints a₁ a₂ u ↔
      x ∈ latticeSet a₁ a₂ u ∧
        0 < x.1 := by
  -- Membership is definitionally lattice membership plus positivity.
  rfl

/-- The set of objective values `x₂ / x₁` attained on the admissible lattice points. -/
noncomputable def objectiveValues (a₁ a₂ u : ℤ) : Set ℝ :=
  slope '' admissiblePoints a₁ a₂ u

/-- Membership in `objectiveValues a₁ a₂ u` means that the value is realized by some admissible
lattice point. -/
theorem mem_objectiveValues_iff
    {a₁ a₂ u : ℤ} {z : ℝ} :
    z ∈ objectiveValues a₁ a₂ u ↔
      ∃ x ∈ admissiblePoints a₁ a₂ u, slope x = z := by
  -- Expand image membership and orient its equality toward `z`.
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

/-- A lattice point is optimal when it is admissible and its slope is the greatest element of the
attained objective-value set. -/
noncomputable def isOptimalPoint (a₁ a₂ u : ℤ) (x : ℤ × ℤ) : Prop :=
  x ∈ admissiblePoints a₁ a₂ u ∧
    IsGreatest (objectiveValues a₁ a₂ u) (slope x)

/-- The optimality predicate unfolds to admissibility together with `IsGreatest` for the slope
value `x₂ / x₁`. -/
theorem isOptimalPoint_iff
    {a₁ a₂ u : ℤ} {x : ℤ × ℤ} :
    isOptimalPoint a₁ a₂ u x ↔
      x ∈ admissiblePoints a₁ a₂ u ∧
        IsGreatest (objectiveValues a₁ a₂ u) (slope x) := by
  -- Unfold the optimal-point predicate.
  rfl

/-- A `PureIntegerSlope.Problem` records positive integers `a₁`, `a₂`, `u`,
the chosen optimal lattice point `xStar`, and the reducedness hypothesis on `xStar.2 / xStar.1`.
-/
structure Problem where
  a₁ : ℤ
  a₂ : ℤ
  u : ℤ
  ha₁_pos : 0 < a₁
  ha₂_pos : 0 < a₂
  hu_pos : 0 < u
  xStar : ℤ × ℤ
  hxStar_opt : isOptimalPoint a₁ a₂ u xStar
  hxStar_reduced : Nat.Coprime xStar.2.natAbs xStar.1.natAbs

namespace Problem

/-- The distinguished point `xStar` in a `PureIntegerSlope.Problem` is optimal for the associated
slope-maximization problem. -/
theorem xStar_isOptimalPoint
    (E : Problem) :
    isOptimalPoint E.a₁ E.a₂ E.u E.xStar := by
  -- Project the optimality certificate stored in the problem data.
  exact E.hxStar_opt

/-- The point `E.xStar` is the distinguished reduced lattice point determining the
positive-slope boundary ray in the Definition 1.33 setup. -/
theorem xStar_isDistinguishedBoundaryLatticePoint
    (E : Problem) :
    isOptimalPoint E.a₁ E.a₂ E.u E.xStar ∧
      Nat.Coprime E.xStar.2.natAbs E.xStar.1.natAbs := by
  -- Combine the two certificates stored in the problem data.
  exact ⟨E.hxStar_opt, E.hxStar_reduced⟩

/-- The integer `k = ⌊u / x₁*⌋` attached to `E`. -/
noncomputable def k (E : Problem) : ℤ :=
  Int.floor ((E.u : ℝ) / (E.xStar.1 : ℝ))

/-- Unfolding equation for `E.k`. -/
theorem k_def
    (E : Problem) :
    E.k = Int.floor ((E.u : ℝ) / (E.xStar.1 : ℝ)) := by
  -- Unfold the definition of the terminal integer multiplier.
  rfl

/-- The lattice point `k x*` on the ray through the distinguished optimal point. -/
noncomputable def boundaryLatticePoint (E : Problem) : ℤ × ℤ :=
  (E.k * E.xStar.1, E.k * E.xStar.2)

/-- Unfolding equation for `E.boundaryLatticePoint`. -/
theorem boundaryLatticePoint_def
    (E : Problem) :
    E.boundaryLatticePoint = (E.k * E.xStar.1, E.k * E.xStar.2) := by
  -- Unfold the integer endpoint on the distinguished ray.
  rfl

/-- The distinguished endpoint of the positive-slope boundary segment of
`convexHull ℝ (PureIntegerSlope.realLatticeSet E.a₁ E.a₂ E.u)`, realized as the real lift of
`E.boundaryLatticePoint`. -/
noncomputable def boundaryPoint (E : Problem) : ℝ × ℝ :=
  ((E.boundaryLatticePoint.1 : ℝ), (E.boundaryLatticePoint.2 : ℝ))

/-- Unfolding equation for `E.boundaryPoint`. -/
theorem boundaryPoint_def
    (E : Problem) :
    E.boundaryPoint =
      ((E.boundaryLatticePoint.1 : ℝ), (E.boundaryLatticePoint.2 : ℝ)) := by
  -- Unfold the real lift of the integer endpoint.
  rfl

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
every feasible lattice point has nonnegative coordinates and cross-product slope at most that of
the distinguished optimal point. -/
lemma latticePoint_crossMul_le
    (E : Problem) {x : ℤ × ℤ}
    (hx : x ∈ latticeSet E.a₁ E.a₂ E.u) :
    0 ≤ x.1 ∧ 0 ≤ x.2 ∧
      x.2 * E.xStar.1 ≤ x.1 * E.xStar.2 := by
  -- Feasibility and positivity of the coefficients first force both coordinates nonnegative.
  rw [mem_latticeSet_iff] at hx
  have hx₁_nonneg : 0 ≤ x.1 := by
    nlinarith [E.ha₁_pos, E.ha₂_pos]
  refine ⟨hx₁_nonneg, hx.2.2, ?_⟩
  obtain ⟨hxStar_adm, hxStar_greatest⟩ := isOptimalPoint_iff.mp E.hxStar_opt
  have hxStar₁_pos : 0 < E.xStar.1 := (mem_admissiblePoints_iff.mp hxStar_adm).2
  by_cases hx₁_zero : x.1 = 0
  · -- On the vertical axis feasibility forces the lattice point to be the origin.
    have hx₂_product_nonpos : E.a₂ * x.2 ≤ 0 := by
      simpa only [hx₁_zero, mul_zero, neg_zero, zero_add] using hx.1
    have hx₂_product_zero : E.a₂ * x.2 = 0 :=
      le_antisymm hx₂_product_nonpos (mul_nonneg E.ha₂_pos.le hx.2.2)
    have hx₂_zero : x.2 = 0 := by
      exact (mul_eq_zero.mp hx₂_product_zero).resolve_left (ne_of_gt E.ha₂_pos)
    simp only [hx₁_zero, hx₂_zero, zero_mul, le_refl]
  · -- Otherwise optimality compares the two slopes, and positive denominators clear safely.
    have hx₁_pos : 0 < x.1 := lt_of_le_of_ne hx₁_nonneg (Ne.symm hx₁_zero)
    have hx_adm : x ∈ admissiblePoints E.a₁ E.a₂ E.u :=
      mem_admissiblePoints_iff.mpr ⟨mem_latticeSet_iff.mpr hx, hx₁_pos⟩
    have hx_value : slope x ∈ objectiveValues E.a₁ E.a₂ E.u :=
      mem_objectiveValues_iff.mpr ⟨x, hx_adm, rfl⟩
    have hslope : slope x ≤ slope E.xStar := hxStar_greatest.2 hx_value
    rw [slope_def, slope_def, div_le_div_iff₀] at hslope
    · have hcross : x.2 * E.xStar.1 ≤ E.xStar.2 * x.1 := by
        exact_mod_cast hslope
      simpa only [mul_comm] using hcross
    · exact_mod_cast hx₁_pos
    · exact_mod_cast hxStar₁_pos

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
an integer point collinear with a primitive integer direction has first coordinate divisible by
the direction's first coordinate. -/
lemma first_dvd_of_coprime_crossMul_eq
    {a b x y : ℤ}
    (hcop : Nat.Coprime b.natAbs a.natAbs)
    (hcross : y * a = x * b) :
    a ∣ x := by
  -- Taking absolute values turns collinearity into a natural-number divisibility statement.
  have habs : y.natAbs * a.natAbs = x.natAbs * b.natAbs := by
    rw [← Int.natAbs_mul, hcross, Int.natAbs_mul]
  have hdiv_mul : a.natAbs ∣ x.natAbs * b.natAbs := by
    rw [← habs]
    exact dvd_mul_left _ _
  have hdiv : a.natAbs ∣ x.natAbs :=
    hcop.symm.dvd_mul_right.mp hdiv_mul
  -- Divisibility is unchanged by replacing integers with their absolute values.
  rwa [Int.natAbs_dvd_natAbs] at hdiv

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
the distinguished optimal point has positive first coordinate, nonnegative second coordinate, and
lies below the first-coordinate bound. -/
lemma xStar_coordinate_bounds (E : Problem) :
    0 < E.xStar.1 ∧ 0 ≤ E.xStar.2 ∧ E.xStar.1 ≤ E.u := by
  -- Optimality includes admissibility, whose lattice constraints give all three bounds.
  have hxStar_adm := (isOptimalPoint_iff.mp E.hxStar_opt).1
  obtain ⟨hxStar_lattice, hxStar₁_pos⟩ := mem_admissiblePoints_iff.mp hxStar_adm
  have hxStar_constraints := mem_latticeSet_iff.mp hxStar_lattice
  exact ⟨hxStar₁_pos, hxStar_constraints.2.2, hxStar_constraints.2.1⟩

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
the terminal ray multiplier is at least one and its first coordinate does not exceed `E.u`. -/
lemma terminalMultiplier_bounds (E : Problem) :
    1 ≤ E.k ∧ E.k * E.xStar.1 ≤ E.u := by
  have hxStar_bounds := xStar_coordinate_bounds E
  have hxStar₁_pos_real : (0 : ℝ) < (E.xStar.1 : ℝ) := by
    exact_mod_cast hxStar_bounds.1
  -- The feasible distinguished point shows that the quotient defining `k` is at least one.
  have hone_le_div : (1 : ℝ) ≤ (E.u : ℝ) / (E.xStar.1 : ℝ) := by
    rw [le_div_iff₀ hxStar₁_pos_real]
    have hxStar₁_le_real : (E.xStar.1 : ℝ) ≤ (E.u : ℝ) := by
      exact_mod_cast hxStar_bounds.2.2
    simpa only [one_mul] using hxStar₁_le_real
  have hone_le_k : (1 : ℤ) ≤ E.k := by
    rw [k_def, Int.le_floor]
    simpa only [Int.cast_one] using hone_le_div
  refine ⟨hone_le_k, ?_⟩
  -- The defining floor inequality gives the complementary upper bound after clearing positivity.
  have hk_le_div : (E.k : ℝ) ≤ (E.u : ℝ) / (E.xStar.1 : ℝ) := by
    rw [k_def]
    exact Int.floor_le _
  have hk_mul_le_real :
      (E.k : ℝ) * (E.xStar.1 : ℝ) ≤ (E.u : ℝ) := by
    rwa [le_div_iff₀ hxStar₁_pos_real] at hk_le_div
  exact_mod_cast hk_mul_le_real

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
the terminal primitive-ray point is itself a feasible real lattice point. -/
lemma boundaryPoint_mem_realLatticeSet (E : Problem) :
    E.boundaryPoint ∈ realLatticeSet E.a₁ E.a₂ E.u := by
  have hxStar_adm := (isOptimalPoint_iff.mp E.hxStar_opt).1
  have hxStar_lattice := (mem_admissiblePoints_iff.mp hxStar_adm).1
  have hxStar_constraints := mem_latticeSet_iff.mp hxStar_lattice
  have hxStar_bounds := xStar_coordinate_bounds E
  have hk_bounds := terminalMultiplier_bounds E
  have hzero_le_one : (0 : ℤ) ≤ 1 := by
    norm_num
  have hk_nonneg : 0 ≤ E.k := le_trans hzero_le_one hk_bounds.1
  -- It suffices to verify the three integral constraints for the scaled endpoint.
  rw [realLatticeSet_eq_image_latticeSet]
  refine ⟨E.boundaryLatticePoint, ?_, ?_⟩
  · rw [mem_latticeSet_iff, boundaryLatticePoint_def]
    refine ⟨?_, hk_bounds.2, mul_nonneg hk_nonneg hxStar_bounds.2.1⟩
    -- Scaling preserves the defining slope inequality because the multiplier is nonnegative.
    calc
      -E.a₁ * (E.k * E.xStar.1) + E.a₂ * (E.k * E.xStar.2) =
          E.k * (-E.a₁ * E.xStar.1 + E.a₂ * E.xStar.2) := by ring
      _ ≤ E.k * 0 := mul_le_mul_of_nonneg_left hxStar_constraints.1 hk_nonneg
      _ = 0 := mul_zero E.k
  · exact (boundaryPoint_def E).symm

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
every feasible lattice point satisfies the integral support cut exposing the terminal primitive-ray
point. -/
lemma latticePoint_boundaryCut_le
    (E : Problem) {x : ℤ × ℤ}
    (hx : x ∈ latticeSet E.a₁ E.a₂ E.u) :
    x.1 + E.u * (x.2 * E.xStar.1 - x.1 * E.xStar.2) ≤
      E.k * E.xStar.1 := by
  have hx_bounds := latticePoint_crossMul_le E hx
  have hx_constraints := mem_latticeSet_iff.mp hx
  have hxStar_bounds := xStar_coordinate_bounds E
  have hk_bounds := terminalMultiplier_bounds E
  have hzero_le_one : (0 : ℤ) ≤ 1 := by
    norm_num
  by_cases hcross : x.2 * E.xStar.1 = x.1 * E.xStar.2
  · -- On the exposed ray, primitivity makes the first coordinate an integral multiple of `xStar.1`.
    have hdiv : E.xStar.1 ∣ x.1 :=
      first_dvd_of_coprime_crossMul_eq E.hxStar_reduced hcross
    obtain ⟨m, hm⟩ := hdiv
    have hxStar₁_pos_real : (0 : ℝ) < (E.xStar.1 : ℝ) := by
      exact_mod_cast hxStar_bounds.1
    have hm_le_div : (m : ℝ) ≤ (E.u : ℝ) / (E.xStar.1 : ℝ) := by
      rw [le_div_iff₀ hxStar₁_pos_real]
      rw [← Int.cast_mul, mul_comm m E.xStar.1, ← hm]
      exact_mod_cast hx_constraints.2.1
    have hm_le_k : m ≤ E.k := by
      rw [k_def, Int.le_floor]
      exact hm_le_div
    have hx₁_le : x.1 ≤ E.k * E.xStar.1 := by
      rw [hm, mul_comm E.xStar.1 m]
      exact mul_le_mul_of_nonneg_right hm_le_k hxStar_bounds.1.le
    simpa only [hcross, sub_self, mul_zero, add_zero] using hx₁_le
  · -- Off the ray, the integral slope defect is at most `-1`, so the cut's left side is
    -- nonpositive.
    have hdefect : x.2 * E.xStar.1 - x.1 * E.xStar.2 ≤ -1 := by
      omega
    calc
      x.1 + E.u * (x.2 * E.xStar.1 - x.1 * E.xStar.2)
          ≤ E.u + E.u * (-1) :=
            add_le_add hx_constraints.2.1
              (mul_le_mul_of_nonneg_left hdefect E.hu_pos.le)
      _ = 0 := by ring
      _ ≤ E.k * E.xStar.1 :=
        mul_nonneg (le_trans hzero_le_one hk_bounds.1) hxStar_bounds.1.le

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
the integral support cut remains valid on the real convex hull of the lattice set. -/
lemma boundaryCut_le_on_convexHull
    (E : Problem) {p : ℝ × ℝ}
    (hp : p ∈ convexHull ℝ (realLatticeSet E.a₁ E.a₂ E.u)) :
    p.1 + (E.u : ℝ) *
        (p.2 * (E.xStar.1 : ℝ) - p.1 * (E.xStar.2 : ℝ)) ≤
      (E.k : ℝ) * (E.xStar.1 : ℝ) := by
  -- First transport the integer cut to every generator of the real lattice set.
  have hgenerators :
      realLatticeSet E.a₁ E.a₂ E.u ⊆
        {q : ℝ × ℝ |
          q.1 + (E.u : ℝ) *
              (q.2 * (E.xStar.1 : ℝ) - q.1 * (E.xStar.2 : ℝ)) ≤
            (E.k : ℝ) * (E.xStar.1 : ℝ)} := by
    intro q hq
    rw [realLatticeSet_eq_image_latticeSet] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hcut := latticePoint_boundaryCut_le E hx
    simp only [Set.mem_setOf_eq]
    exact_mod_cast hcut
  have hconvex :
      Convex ℝ
        {q : ℝ × ℝ |
          q.1 + (E.u : ℝ) *
              (q.2 * (E.xStar.1 : ℝ) - q.1 * (E.xStar.2 : ℝ)) ≤
            (E.k : ℝ) * (E.xStar.1 : ℝ)} := by
    -- The cut defines a halfspace because its left side is linear in the point.
    intro q hq r hr a b ha hb hab
    simp only [Set.mem_setOf_eq] at hq hr ⊢
    have haq := mul_le_mul_of_nonneg_left hq ha
    have hbr := mul_le_mul_of_nonneg_left hr hb
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    calc
      a * q.1 + b * r.1 + (E.u : ℝ) *
          ((a * q.2 + b * r.2) * (E.xStar.1 : ℝ) -
            (a * q.1 + b * r.1) * (E.xStar.2 : ℝ)) =
          a * (q.1 + (E.u : ℝ) *
            (q.2 * (E.xStar.1 : ℝ) - q.1 * (E.xStar.2 : ℝ))) +
          b * (r.1 + (E.u : ℝ) *
            (r.2 * (E.xStar.1 : ℝ) - r.1 * (E.xStar.2 : ℝ))) := by ring
      _ ≤ a * ((E.k : ℝ) * (E.xStar.1 : ℝ)) +
          b * ((E.k : ℝ) * (E.xStar.1 : ℝ)) := add_le_add haq hbr
      _ = (E.k : ℝ) * (E.xStar.1 : ℝ) := by
        rw [← add_mul, hab, one_mul]
  exact convexHull_min hgenerators hconvex hp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
membership in the segment from zero to the terminal primitive-ray point is characterized by
coordinate signs, collinearity, and the terminal first-coordinate bound. -/
lemma mem_segment_zero_boundaryPoint_iff
    (E : Problem) {p : ℝ × ℝ} :
    p ∈ segment ℝ (0 : ℝ × ℝ) E.boundaryPoint ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧
        p.2 * (E.xStar.1 : ℝ) = p.1 * (E.xStar.2 : ℝ) ∧
        p.1 ≤ (E.k : ℝ) * (E.xStar.1 : ℝ) := by
  have hxStar_bounds := xStar_coordinate_bounds E
  have hk_bounds := terminalMultiplier_bounds E
  have hxStar₁_pos_real : (0 : ℝ) < (E.xStar.1 : ℝ) := by
    exact_mod_cast hxStar_bounds.1
  have hxStar₂_nonneg_real : (0 : ℝ) ≤ (E.xStar.2 : ℝ) := by
    exact_mod_cast hxStar_bounds.2.1
  have hzero_lt_one : (0 : ℤ) < 1 := by
    norm_num
  have hk_pos : 0 < E.k := lt_of_lt_of_le hzero_lt_one hk_bounds.1
  have hk_pos_real : (0 : ℝ) < (E.k : ℝ) := by
    exact_mod_cast hk_pos
  have hfirst_pos :
      (0 : ℝ) < (E.k : ℝ) * (E.xStar.1 : ℝ) :=
    mul_pos hk_pos_real hxStar₁_pos_real
  have hsecond_nonneg :
      (0 : ℝ) ≤ (E.k : ℝ) * (E.xStar.2 : ℝ) :=
    mul_nonneg hk_pos_real.le hxStar₂_nonneg_real
  have hboundary :
      E.boundaryPoint =
        ((E.k : ℝ) * (E.xStar.1 : ℝ),
          (E.k : ℝ) * (E.xStar.2 : ℝ)) := by
    rw [boundaryPoint_def, boundaryLatticePoint_def]
    simp only [Int.cast_mul]
  rw [segment_eq_image]
  constructor
  · rintro ⟨θ, ⟨hθ_nonneg, hθ_le⟩, hp⟩
    -- Project the segment parametrization to its two coordinates.
    rw [hboundary] at hp
    simp only [smul_zero, zero_add, Prod.smul_mk, smul_eq_mul] at hp
    have hp₁ := congrArg Prod.fst hp
    have hp₂ := congrArg Prod.snd hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hp₁]
      exact mul_nonneg hθ_nonneg hfirst_pos.le
    · rw [← hp₂]
      exact mul_nonneg hθ_nonneg hsecond_nonneg
    · rw [← hp₁, ← hp₂]
      ring
    · rw [← hp₁]
      exact mul_le_of_le_one_left hfirst_pos.le hθ_le
  · rintro ⟨hp₁_nonneg, hp₂_nonneg, hcross, hp₁_le⟩
    -- Recover the unique segment parameter from the positive first endpoint coordinate.
    have hfirst_ne : (E.k : ℝ) * (E.xStar.1 : ℝ) ≠ 0 := ne_of_gt hfirst_pos
    have hk_ne : (E.k : ℝ) ≠ 0 := ne_of_gt hk_pos_real
    have hxStar₁_ne : (E.xStar.1 : ℝ) ≠ 0 := ne_of_gt hxStar₁_pos_real
    refine ⟨p.1 / ((E.k : ℝ) * (E.xStar.1 : ℝ)), ?_, ?_⟩
    · exact ⟨div_nonneg hp₁_nonneg hfirst_pos.le,
        (div_le_one hfirst_pos).mpr hp₁_le⟩
    · rw [hboundary]
      simp only [smul_zero, zero_add, Prod.smul_mk, smul_eq_mul]
      apply Prod.ext
      · exact div_mul_cancel₀ p.1 hfirst_ne
      · field_simp [hk_ne, hxStar₁_ne]
        nlinarith [hcross]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_4/ch1_sec1_4_2_definition_1_33/Problem.lean:
The distinguished boundary point `E.boundaryPoint` is the endpoint of the positive-slope boundary
segment of `convexHull ℝ (PureIntegerSlope.realLatticeSet E.a₁ E.a₂ E.u)` emanating from the origin.
-/
theorem boundaryPoint_isPositiveSlopeBoundaryEndpoint
    (E : Problem) :
    segment ℝ (0 : ℝ × ℝ) E.boundaryPoint =
      convexHull ℝ (PureIntegerSlope.realLatticeSet E.a₁ E.a₂ E.u) ∩
        {p : ℝ × ℝ |
          0 ≤ p.1 ∧
            0 ≤ p.2 ∧
            p.2 * (E.xStar.1 : ℝ) = p.1 * (E.xStar.2 : ℝ)} := by
  -- The origin lemma supplies the first endpoint needed for convexity of the hull.
  have hzero_mem : (0 : ℝ × ℝ) ∈ realLatticeSet E.a₁ E.a₂ E.u :=
    zero_mem_realLatticeSet E.hu_pos.le
  ext p
  constructor
  · intro hp
    -- Segment membership supplies the ray equations, while convexity supplies hull membership.
    have hp_ray := mem_segment_zero_boundaryPoint_iff E |>.mp hp
    have hp_hull := segment_subset_convexHull hzero_mem
      (boundaryPoint_mem_realLatticeSet E) hp
    exact ⟨hp_hull, hp_ray.1, hp_ray.2.1, hp_ray.2.2.1⟩
  · rintro ⟨hp_hull, hp₁_nonneg, hp₂_nonneg, hcross⟩
    -- On the ray the support defect vanishes, so the global cut is exactly the endpoint bound.
    have hcut := boundaryCut_le_on_convexHull E hp_hull
    have hp₁_le : p.1 ≤ (E.k : ℝ) * (E.xStar.1 : ℝ) := by
      simpa only [hcross, sub_self, mul_zero, add_zero] using hcut
    exact mem_segment_zero_boundaryPoint_iff E |>.mpr
      ⟨hp₁_nonneg, hp₂_nonneg, hcross, hp₁_le⟩

#print axioms boundaryPoint_isPositiveSlopeBoundaryEndpoint

/-- The positive-slope endpoint at first coordinate `u` on the ray through `E.xStar`. -/
noncomputable def positiveSlopeEndpoint (E : Problem) : ℝ × ℝ :=
  ((E.u : ℝ), (E.u : ℝ) * (E.xStar.2 : ℝ) / (E.xStar.1 : ℝ))

/-- Unfolding equation for `E.positiveSlopeEndpoint`. -/
theorem positiveSlopeEndpoint_def
    (E : Problem) :
    E.positiveSlopeEndpoint =
      ((E.u : ℝ), (E.u : ℝ) * (E.xStar.2 : ℝ) / (E.xStar.1 : ℝ)) := by
  -- Unfold the endpoint at first coordinate `u`.
  rfl

end Problem

end PureIntegerSlope

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_e48d3b8f691f06ce0613"
#print axioms _root_.PureIntegerSlope.Problem.boundaryPoint_isPositiveSlopeBoundaryEndpoint
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_e48d3b8f691f06ce0613"
