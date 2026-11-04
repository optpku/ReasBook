/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_1.ch6_sec6_2_1_theorem_6_16
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_definition_6_3_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_28
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_3.ch6_sec6_3_3_theorem_6_34
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_5.ch6_sec6_5_exercise_6_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Matrix

namespace NonnegativeInfiniteModel

variable {q : ℕ}

/-- The feasible assignments are the finitely supported nonnegative families whose shifted
balance with `f` lies in `ℤ_+^q`. -/
def feasibleSet (f : Fin q → ℝ) : Set ((Fin q → ℝ) →₀ NNReal) :=
  {y | continuous_infinite_balance f y ∈ nonnegativeIntegerVectors q}

/-- Membership in `feasibleSet f` is exactly the `ℤ_+^q` balance condition. -/
theorem mem_feasibleSet_iff {f : Fin q → ℝ} {y : (Fin q → ℝ) →₀ NNReal} :
    y ∈ feasibleSet f ↔
      continuous_infinite_balance f y ∈ nonnegativeIntegerVectors q := by
  -- This is the defining set-membership condition.
  rfl

/-- A function is valid for the nonnegative infinite model when its cut inequality holds for
every feasible finitely supported assignment. -/
def validFor (f : Fin q → ℝ) (ψ : (Fin q → ℝ) → ℝ) : Prop :=
  ∀ {y : (Fin q → ℝ) →₀ NNReal},
    y ∈ feasibleSet f → 1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ))

/-- A valid function gives its defining cut inequality on every feasible assignment. -/
theorem validFor_one_le
    {f : Fin q → ℝ} {ψ : (Fin q → ℝ) → ℝ} {y : (Fin q → ℝ) →₀ NNReal}
    (hψ : validFor f ψ) (hy : y ∈ feasibleSet f) :
    1 ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
  -- Apply the defining validity predicate at the given feasible assignment.
  exact hψ hy

/-- The shifted unit sublevel set `B_ψ = {x | ψ (x - f) ≤ 1}`. -/
def levelSet (f : Fin q → ℝ) (ψ : (Fin q → ℝ) → ℝ) : Set (Fin q → ℝ) :=
  {x | x - f ∈ sublinear_unit_sublevel_set ψ}

/-- Membership in `levelSet f ψ` is exactly the inequality `ψ (x - f) ≤ 1`. -/
theorem mem_levelSet_iff
    {f : Fin q → ℝ} {ψ : (Fin q → ℝ) → ℝ} {x : Fin q → ℝ} :
    x ∈ levelSet f ψ ↔ ψ (x - f) ≤ 1 := by
  -- Unfold the translated set once and reuse the unit-sublevel membership API.
  rw [levelSet, mem_sublinear_unit_sublevel_set]

/-- The shifted unit sublevel set of a sublinear function is convex. -/
theorem levelSetConvex {f : Fin q → ℝ} {ψ : (Fin q → ℝ) → ℝ}
    (hψ : Function.Sublinear ψ) :
    Convex ℝ (levelSet f ψ) := by
  -- Translate convexity of the unit sublevel set through the shift by `f`.
  intro x hx y hy a b ha hb hab
  have hx' : x - f ∈ sublinear_unit_sublevel_set ψ := by
    simpa [levelSet] using hx
  have hy' : y - f ∈ sublinear_unit_sublevel_set ψ := by
    simpa [levelSet] using hy
  have hxy :
      a • (x - f) + b • (y - f) ∈ sublinear_unit_sublevel_set ψ :=
    convex_sublinear_unit_sublevel_set hψ hx' hy' ha hb hab
  have htranslate :
      a • (x - f) + b • (y - f) = (a • x + b • y) - f := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    calc
      a * (x i - f i) + b * (y i - f i) =
          a * x i + b * y i - (a + b) * f i := by ring
      _ = a * x i + b * y i - f i := by rw [hab, one_mul]
  simpa [levelSet] using htranslate ▸ hxy

/-- Every nonnegative-integer feasible assignment is feasible for the chapter's continuous
infinite relaxation with balance in `ℤ^q`. -/
theorem feasibleSet_subset_continuous {f : Fin q → ℝ} :
    feasibleSet f ⊆ continuous_infinite_relaxation_feasible_set f := by
  intro y hy
  -- Forget only the nonnegativity half of the `ℤ_+^q` balance condition.
  rw [mem_continuous_infinite_relaxation_feasible_set_iff]
  exact nonnegativeIntegerVectors_subset_integerVectors ((mem_feasibleSet_iff).1 hy)

/-- Helper for Exercise 6.19:
interior points of `levelSet f ψ` are exactly the strict translated sublevel points. -/
theorem mem_interior_levelSet_iff
    {f : Fin q → ℝ} {ψ : (Fin q → ℝ) → ℝ}
    (hψ : Function.Sublinear ψ) {x : Fin q → ℝ} :
    x ∈ interior (levelSet f ψ) ↔ ψ (x - f) < 1 := by
  let K : Set (Fin q → ℝ) := sublinear_unit_sublevel_set ψ
  have htranslate :
      x ∈ interior (levelSet f ψ) ↔ x - f ∈ interior K := by
    -- Translation by `-f` identifies `levelSet f ψ` with the unit sublevel set of `ψ`.
    simpa [K, levelSet, sub_eq_add_neg, add_comm] using
      (memInterior_setOf_add_mem_iff K (-f) x)
  constructor
  · intro hx
    have hxK : x - f ∈ interior K := htranslate.mp hx
    have hxle : ψ (x - f) ≤ 1 := by
      exact (mem_sublinear_unit_sublevel_set (g := ψ) (r := x - f)).1 (interior_subset hxK)
    -- If the boundary value were `1`, a slight homothety from the origin would stay inside `K`,
    -- contradicting positive homogeneity.
    by_contra hnotlt
    have hxeq : ψ (x - f) = 1 := le_antisymm hxle (le_of_not_gt hnotlt)
    have hhom :
        ∀ᶠ δ in nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ)),
          AffineMap.homothety (0 : Fin q → ℝ) δ (x - f) ∈ K := by
      exact
        (eventually_homothety_mem_of_mem_interior ℝ (0 : Fin q → ℝ) hxK).filter_mono
          nhdsWithin_le_nhds
    rcases (hhom.and self_mem_nhdsWithin).exists with ⟨δ, hδK, hδgt⟩
    have hδgt' : 1 < δ := by
      simpa using hδgt
    have hδpos : 0 < δ := zero_lt_one.trans hδgt'
    have hδeq :
        AffineMap.homothety (0 : Fin q → ℝ) δ (x - f) = δ • (x - f) := by
      ext i
      simp [AffineMap.homothety_eq_lineMap, AffineMap.lineMap_apply]
    have hδle : ψ (δ • (x - f)) ≤ 1 := by
      rw [← hδeq]
      exact (mem_sublinear_unit_sublevel_set (g := ψ) (r := _)).1 hδK
    have hδψ : ψ (δ • (x - f)) = δ * ψ (x - f) :=
      hψ.positivelyHomogeneous _ _ hδpos
    have : δ * ψ (x - f) ≤ 1 := by
      simpa [hδψ] using hδle
    linarith
  · intro hx
    have hcont : Continuous fun y : Fin q → ℝ ↦ ψ (y - f) := by
      exact hψ.continuous.comp (continuous_id.sub continuous_const)
    -- A strict continuous sublevel set is open and sits inside the closed sublevel set.
    have hx' :
        x ∈ interior {y : Fin q → ℝ | ψ (y - f) ≤ 1} := by
      exact (lt_subset_interior_le hcont continuous_const) (by simpa using hx)
    simpa [levelSet, sublinear_unit_sublevel_set] using hx'

/-- Exercise 6.19 (1). If `ψ : ℝ^q → ℝ` is sublinear and
`B_ψ = {x ∈ ℝ^q | ψ (x - f) ≤ 1}` is `ℤ_+^q`-free, then `ψ` is valid for the
nonnegative infinite model with right-hand side `f`. -/
theorem validOfSublinear
    (f : Fin q → ℝ) (ψ : (Fin q → ℝ) → ℝ)
    (hψ : Function.Sublinear ψ)
    (hfree : is_nonnegative_integer_free (levelSet f ψ)) :
    validFor f ψ := by
  intro y hy
  -- Route correction: prove validity directly from sublinearity and freeness, without gauges.
  by_contra hcut
  let z : Fin q → ℝ := continuous_infinite_balance f y
  have hz_nonnegative : z ∈ nonnegativeIntegerVectors q := (mem_feasibleSet_iff).1 hy
  have hz_shift :
      z - f = y.sum (fun r a ↦ (a : ℝ) • r) := by
    -- Subtracting the right-hand side removes the translation term from the balance.
    ext i
    simp [z, continuous_infinite_balance, add_assoc]
  have hz_le :
      ψ (z - f) ≤ y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
    rw [hz_shift]
    exact sublinear_le_continuous_finsupp_sum hψ y
  have hz_lt : ψ (z - f) < 1 := by
    exact lt_of_le_of_lt hz_le (lt_of_not_ge hcut)
  have hz_interior : z ∈ interior (levelSet f ψ) :=
    (mem_interior_levelSet_iff hψ).2 hz_lt
  exact (is_nonnegative_integer_free.not_mem_interior hfree hz_nonnegative) hz_interior

namespace MaxFourCut

/-- The right-hand side `f = (1/4, 1/2)` from the concrete two-dimensional model. -/
noncomputable def f : Fin 2 → ℝ :=
  ![(1 / 4 : ℝ), (1 / 2 : ℝ)]

/-- The concrete right-hand side agrees with its displayed coordinate vector. -/
theorem f_eq :
    f = ![(1 / 4 : ℝ), (1 / 2 : ℝ)] := by
  -- This is the displayed definition.
  rfl

/-- The maximum of the two linear forms in the concrete two-dimensional model. -/
def psi : (Fin 2 → ℝ) → ℝ :=
  fun r ↦ max ((4 : ℝ) * r 0 + (4 : ℝ) * r 1) ((4 : ℝ) * r 0 - (4 : ℝ) * r 1)

/-- The value of `psi` is the displayed maximum of two linear forms. -/
theorem psi_apply (r : Fin 2 → ℝ) :
    psi r = max ((4 : ℝ) * r 0 + (4 : ℝ) * r 1)
      ((4 : ℝ) * r 0 - (4 : ℝ) * r 1) := by
  -- This is the unfolded maximum formula.
  rfl

/-- The shifted unit sublevel set for the concrete right-hand side and function. -/
def levelSet : Set (Fin 2 → ℝ) :=
  NonnegativeInfiniteModel.levelSet f psi

/-- The concrete shifted level set is the intersection of the two displayed halfspaces. -/
theorem levelSet_eq :
    levelSet = {x | x 0 + x 1 ≤ 1 ∧ x 0 ≤ x 1} := by
  ext x
  constructor
  · intro hx
    have hx' : psi (x - f) ≤ 1 := (NonnegativeInfiniteModel.mem_levelSet_iff).1 hx
    rw [psi_apply, max_le_iff] at hx'
    constructor
    · -- The first branch encodes the sum inequality.
      have hsum := hx'.1
      simp [f, Pi.sub_apply] at hsum
      linarith
    · -- The second branch encodes the ordering inequality.
      have hdiff := hx'.2
      simp [f, Pi.sub_apply] at hdiff
      linarith
  · rintro ⟨hxsum, hxorder⟩
    -- Reassemble the two explicit inequalities into the max-form inequality.
    rw [NonnegativeInfiniteModel.mem_levelSet_iff, psi_apply, max_le_iff]
    constructor
    · simp [f, Pi.sub_apply]
      linarith
    · simp [f, Pi.sub_apply]
      linarith

/-- The concrete maximum of linear forms is sublinear. -/
instance instSublinear : Function.Sublinear psi := by
  refine ⟨?_, ?_⟩
  · intro r s
    -- Bound each branch of the maximum separately at `r + s`.
    rw [psi_apply, psi_apply, psi_apply]
    refine max_le ?_ ?_
    · calc
        (4 : ℝ) * (r + s) 0 + (4 : ℝ) * (r + s) 1 =
            ((4 : ℝ) * r 0 + (4 : ℝ) * r 1) +
              ((4 : ℝ) * s 0 + (4 : ℝ) * s 1) := by
                ring
        _ ≤ psi r + psi s := add_le_add (le_max_left _ _) (le_max_left _ _)
    · calc
        (4 : ℝ) * (r + s) 0 - (4 : ℝ) * (r + s) 1 =
            ((4 : ℝ) * r 0 - (4 : ℝ) * r 1) +
              ((4 : ℝ) * s 0 - (4 : ℝ) * s 1) := by
                ring
        _ ≤ psi r + psi s := add_le_add (le_max_right _ _) (le_max_right _ _)
  · intro r c hc
    -- Positive homogeneity follows by pulling the nonnegative scalar through the maximum.
    rw [psi_apply, psi_apply]
    have hsum :
        (4 : ℝ) * (c • r) 0 + (4 : ℝ) * (c • r) 1 =
          c * ((4 : ℝ) * r 0 + (4 : ℝ) * r 1) := by
      simp [Pi.smul_apply]
      ring
    have hdiff :
        (4 : ℝ) * (c • r) 0 - (4 : ℝ) * (c • r) 1 =
          c * ((4 : ℝ) * r 0 - (4 : ℝ) * r 1) := by
      simp [Pi.smul_apply]
      ring
    rw [hsum, hdiff, ← mul_max_of_nonneg _ _ hc.le]

/-- The concrete shifted level set is `ℤ_+^2`-free. -/
theorem levelSetFree :
    is_nonnegative_integer_free levelSet := by
  rw [is_nonnegative_integer_free_iff]
  intro z hz
  have hz_strict :
      psi ((Nat.cast ∘ z : Fin 2 → ℝ) - f) < 1 :=
    (mem_interior_levelSet_iff (f := f) (ψ := psi) instSublinear).1 hz
  rw [psi_apply] at hz_strict
  have hsum :
      (4 : ℝ) * (((Nat.cast ∘ z : Fin 2 → ℝ) - f) 0) +
          (4 : ℝ) * (((Nat.cast ∘ z : Fin 2 → ℝ) - f) 1) < 1 := by
    exact lt_of_le_of_lt (le_max_left _ _) hz_strict
  have hdiff :
      (4 : ℝ) * (((Nat.cast ∘ z : Fin 2 → ℝ) - f) 0) -
          (4 : ℝ) * (((Nat.cast ∘ z : Fin 2 → ℝ) - f) 1) < 1 := by
    exact lt_of_le_of_lt (le_max_right _ _) hz_strict
  have hz0_nonneg : 0 ≤ (z 0 : ℝ) := Nat.cast_nonneg (z 0)
  have hz1_nonneg : 0 ≤ (z 1 : ℝ) := Nat.cast_nonneg (z 1)
  -- The two strict branch inequalities have no nonnegative integer solution.
  simp [f, Pi.sub_apply, Function.comp_apply] at hsum hdiff
  nlinarith

/-- Exercise 6.19 (2). For `q = 2`, `f = (1/4, 1/2)`, and
`ψ(r) = max {4 r₁ + 4 r₂, 4 r₁ - 4 r₂}`, the function `ψ` is valid for the
nonnegative infinite model with balance in `ℤ_+^2`. -/
theorem valid :
    NonnegativeInfiniteModel.validFor f psi := by
  -- Route correction: finish from the abstract sublinear/free-set theorem proved above.
  exact NonnegativeInfiniteModel.validOfSublinear f psi instSublinear levelSetFree

end MaxFourCut

end NonnegativeInfiniteModel
