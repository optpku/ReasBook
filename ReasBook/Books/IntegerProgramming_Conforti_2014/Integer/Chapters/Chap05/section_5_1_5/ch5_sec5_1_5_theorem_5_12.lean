/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_1.ch5_sec5_1_1_theorem_5_5

open scoped Matrix
open scoped SplitHullNotation

-- Domain-style sampling for this refine pass:
-- * source-facing owners kept here: `is_mixed_integer_rounding_inequality`,
--   `mixed_integer_rounding_closure`
-- * core/canonical split owners reused from Chapter 5.1:
--   `Split`, `split_hull`, `splitClosure`, `polyhedron_le_set`
-- * bridge/view kept here: `mixed_split_closure`; on matrix polyhedra it is
--   identified with the Chapter 5 matrix owner `splitClosure`

section Theorem512

variable {m n : ℕ}

/-- An inequality `a x ≤ δ` is a mixed integer rounding inequality for `P` relative to the
integer-coordinate set `I` if it comes from the variable-aggregation MIR construction. -/
def is_mixed_integer_rounding_inequality
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (a : Fin n → ℝ)
    (δ : ℝ) : Prop :=
  ∃ π : Fin n → ℤ, ∃ c : Fin n → ℝ, ∃ γ β : ℝ,
    (∀ j : Fin n, j ∉ I → π j = 0) ∧
    (∀ x : Fin n → ℝ, x ∈ P →
      (fun i : Fin n ↦ (π i : ℝ)) ⬝ᵥ x - (γ - c ⬝ᵥ x) ≤ β) ∧
    (∀ x : Fin n → ℝ, x ∈ P → c ⬝ᵥ x ≤ γ) ∧
    a = (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ∧
    δ = (⌊β⌋ : ℝ) + γ / (1 - Int.fract β)

/-- The mixed integer rounding closure `P^MIR[I]` of `P` is the set of points of `P`
satisfying every mixed integer rounding inequality supported on `I`. -/
def mixed_integer_rounding_closure
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ {x : Fin n → ℝ |
    ∀ a : Fin n → ℝ, ∀ δ : ℝ,
      is_mixed_integer_rounding_inequality I P a δ → a ⬝ᵥ x ≤ δ}

/-- The mixed split closure `P^split[I]` of `P` is the intersection of the Chapter 5 split hulls
`P^(π, π₀)` over all splits supported on `I`. This is a `bridge/view` construction
built directly from the existing owners `Split` and `split_hull`. -/
def mixed_split_closure
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  P ∩ ⋂ s : Split I.toFinite.toFinset, P^(s, s.π0)

namespace IndexedMixedClosureNotation

/-- Textbook notation for the mixed integer rounding closure relative to the integer-coordinate
set `I`. -/
scoped notation:max P "^MIR[" I "]" => mixed_integer_rounding_closure I P

/-- Textbook notation for the mixed split closure relative to the integer-coordinate set `I`. -/
scoped notation:max P "^split[" I "]" => mixed_split_closure I P

end IndexedMixedClosureNotation

open scoped IndexedMixedClosureNotation

/-- Membership in `P^MIR[I]` means belonging to `P` and satisfying every mixed integer rounding
inequality for `P` relative to `I`. -/
@[simp] theorem mem_mixed_integer_rounding_closure_iff
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ P^MIR[I] ↔
      x ∈ P ∧
        ∀ a : Fin n → ℝ, ∀ δ : ℝ,
          is_mixed_integer_rounding_inequality I P a δ → a ⬝ᵥ x ≤ δ :=
  Iff.rfl

/-- Membership in `P^split[I]` means belonging to every split hull `P^(π, π₀)`
whose integral split data is supported on `I`. -/
@[simp] theorem mem_mixed_split_closure_iff
    (I : Set (Fin n))
    (P : Set (Fin n → ℝ))
    (x : Fin n → ℝ) :
    x ∈ P^split[I] ↔
      x ∈ P ∧ ∀ s : Split I.toFinite.toFinset, x ∈ P^(s, s.π0) := by
  simp [mixed_split_closure]

/-- Helper for Theorem 5.12: evaluating the MIR coefficient vector on a point separates into the
integral split term and the scaled correction term. -/
lemma mirWitnessDot_eq
    (π : Fin n → ℤ)
    (c x : Fin n → ℝ)
    (β : ℝ) :
    (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ⬝ᵥ x =
      split_dot π x + c ⬝ᵥ x / (1 - Int.fract β) := by
  -- Rewrite the coefficient vector as a sum of the split row and a scalar multiple.
  have hdecomp :
      (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) =
        (fun i : Fin n ↦ (π i : ℝ)) + (1 / (1 - Int.fract β)) • c := by
    ext i
    simp [div_eq_mul_inv, mul_comm]
  rw [hdecomp, add_dotProduct, smul_dotProduct, split_dot]
  ring

/-- Helper for Theorem 5.12: the MIR inequality is valid on the lower split branch
`split_branch_lower P π ⌊β⌋`. -/
lemma mirInequalityValidOnLowerBranch
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {c : Fin n → ℝ}
    {γ β : ℝ}
    {y : Fin n → ℝ}
    (hc : ∀ z : Fin n → ℝ, z ∈ P → c ⬝ᵥ z ≤ γ)
    (hy : y ∈ split_branch_lower P π (⌊β⌋)) :
    (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ⬝ᵥ y ≤
      (⌊β⌋ : ℝ) + γ / (1 - Int.fract β) := by
  rcases (mem_split_branch_lower_iff.mp hy) with ⟨hyP, hyLower⟩
  have hden_pos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  have hscaled :
      (1 - Int.fract β) * split_dot π y + c ⬝ᵥ y ≤
        (1 - Int.fract β) * (⌊β⌋ : ℝ) + γ := by
    have hbranch :
        (1 - Int.fract β) * split_dot π y ≤
          (1 - Int.fract β) * (⌊β⌋ : ℝ) := by
      exact mul_le_mul_of_nonneg_left hyLower hden_pos.le
    have hcorr : c ⬝ᵥ y ≤ γ := hc y hyP
    -- The lower-branch bound supplies the split term, and `c y ≤ γ` supplies the correction term.
    nlinarith
  -- Rewrite the MIR left-hand side into a single denominator and divide by the positive factor.
  rw [mirWitnessDot_eq]
  calc
    split_dot π y + c ⬝ᵥ y / (1 - Int.fract β) =
        ((1 - Int.fract β) * split_dot π y + c ⬝ᵥ y) / (1 - Int.fract β) := by
          field_simp [hden_pos.ne']
    _ ≤ ((1 - Int.fract β) * (⌊β⌋ : ℝ) + γ) / (1 - Int.fract β) := by
          exact div_le_div_of_nonneg_right hscaled hden_pos.le
    _ = (⌊β⌋ : ℝ) + γ / (1 - Int.fract β) := by
          field_simp [hden_pos.ne']

/-- Helper for Theorem 5.12: the MIR inequality is valid on the upper split branch
`split_branch_upper P π ⌊β⌋`. -/
lemma mirInequalityValidOnUpperBranch
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {c : Fin n → ℝ}
    {γ β : ℝ}
    {y : Fin n → ℝ}
    (hvalid : ∀ z : Fin n → ℝ, z ∈ P →
      split_dot π z - (γ - c ⬝ᵥ z) ≤ β)
    (hy : y ∈ split_branch_upper P π (⌊β⌋)) :
    (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ⬝ᵥ y ≤
      (⌊β⌋ : ℝ) + γ / (1 - Int.fract β) := by
  rcases (mem_split_branch_upper_iff.mp hy) with ⟨hyP, hyUpper⟩
  have hfract_nonneg : 0 ≤ Int.fract β := Int.fract_nonneg β
  have hden_pos : 0 < 1 - Int.fract β := by
    linarith [Int.fract_lt_one β]
  have hbase :
      split_dot π y + c ⬝ᵥ y ≤ (⌊β⌋ : ℝ) + Int.fract β + γ := by
    have hvalid' := hvalid y hyP
    rw [← Int.floor_add_fract β] at hvalid'
    -- Put the source MIR inequality into the `⌊β⌋ + fract β` normal form.
    linarith
  have hfract_gap :
      Int.fract β ≤ Int.fract β * (split_dot π y - (⌊β⌋ : ℝ)) := by
    have hupper_gap : 1 ≤ split_dot π y - (⌊β⌋ : ℝ) := by
      linarith
    simpa using mul_le_mul_of_nonneg_left hupper_gap hfract_nonneg
  have hscaled :
      (1 - Int.fract β) * split_dot π y + c ⬝ᵥ y ≤
        (1 - Int.fract β) * (⌊β⌋ : ℝ) + γ := by
    -- On the upper branch, the extra fractional part is absorbed by the gap `split_dot π y - ⌊β⌋`.
    nlinarith
  -- Rewrite the MIR left-hand side into a single denominator and divide by the positive factor.
  rw [mirWitnessDot_eq]
  calc
    split_dot π y + c ⬝ᵥ y / (1 - Int.fract β) =
        ((1 - Int.fract β) * split_dot π y + c ⬝ᵥ y) / (1 - Int.fract β) := by
          field_simp [hden_pos.ne']
    _ ≤ ((1 - Int.fract β) * (⌊β⌋ : ℝ) + γ) / (1 - Int.fract β) := by
          exact div_le_div_of_nonneg_right hscaled hden_pos.le
    _ = (⌊β⌋ : ℝ) + γ / (1 - Int.fract β) := by
          field_simp [hden_pos.ne']

/-- Helper for Theorem 5.12: any MIR witness is valid on the split hull cut out by its supported
split row and floor right-hand side. -/
lemma mirInequalityValidOnSplitHull
    {P : Set (Fin n → ℝ)}
    {π : Fin n → ℤ}
    {c : Fin n → ℝ}
    {γ β : ℝ}
    {x : Fin n → ℝ}
    (hvalid : ∀ y : Fin n → ℝ, y ∈ P →
      split_dot π y - (γ - c ⬝ᵥ y) ≤ β)
    (hc : ∀ y : Fin n → ℝ, y ∈ P → c ⬝ᵥ y ≤ γ)
    (hx : x ∈ P^(π, ⌊β⌋)) :
    (fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)) ⬝ᵥ x ≤
      (⌊β⌋ : ℝ) + γ / (1 - Int.fract β) := by
  let α : Fin n → ℝ := fun i : Fin n ↦ (π i : ℝ) + c i / (1 - Int.fract β)
  let δ : ℝ := (⌊β⌋ : ℝ) + γ / (1 - Int.fract β)
  have hvalid_union :
      is_valid_inequality
        (split_branch_lower P π (⌊β⌋) ∪ split_branch_upper P π (⌊β⌋))
        α δ := by
    rw [is_valid_inequality_iff]
    intro y hy
    rcases hy with hy | hy
    · exact mirInequalityValidOnLowerBranch hc hy
    · exact mirInequalityValidOnUpperBranch hvalid hy
  have hvalid_hull : is_valid_inequality (P^(π, ⌊β⌋)) α δ := by
    -- Route correction: validate the MIR halfspace on each branch first, then lift once to
    -- the convex hull rather than normalizing the whole hull proof in place.
    simpa [α, δ, split_hull] using
      (is_valid_inequality_convexHull_iff
        (S := split_branch_lower P π (⌊β⌋) ∪ split_branch_upper P π (⌊β⌋))
        (α := α) (β := δ)).2 hvalid_union
  exact hvalid_hull hx

/-- Helper for Theorem 5.12: every basic split cut from Theorem 5.5 can be packaged as an MIR
inequality with the same supported split row. -/
lemma basicSplitCutIsMir
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n))
    (s : Split I.toFinite.toFinset)
    (u : Fin m → ℝ)
    (huBasic : u ∈ basic_row_multiplier_set A s)
    (_hub_left : (s.π0 : ℝ) < u ⬝ᵥ b)
    (_hub_right : u ⬝ᵥ b < (s.π0 : ℝ) + 1) :
    is_mixed_integer_rounding_inequality I (polyhedron_le_set A b)
      (fun i : Fin n ↦
        (s i : ℝ) + ((row_multiplier_neg u) ᵥ* A) i / (1 - Int.fract (u ⬝ᵥ b)))
      ((⌊u ⬝ᵥ b⌋ : ℝ) + (row_multiplier_neg u ⬝ᵥ b) / (1 - Int.fract (u ⬝ᵥ b))) := by
  rcases (mem_basic_row_multiplier_set_iff A s u).mp huBasic with ⟨huπ, _⟩
  refine ⟨s, (row_multiplier_neg u) ᵥ* A, row_multiplier_neg u ⬝ᵥ b, u ⬝ᵥ b, ?_, ?_, ?_, rfl, rfl⟩
  · intro j hj
    have hj' : j ∉ I.toFinite.toFinset := by
      simpa using hj
    exact s.coeff_eq_zero_of_not_mem hj'
  · intro x hxP
    have hsplit :
        split_dot s x = u ⬝ᵥ (A *ᵥ x) := by
      rw [split_dot, ← huπ, Matrix.dotProduct_mulVec]
    have hnegAx :
        ((row_multiplier_neg u) ᵥ* A) ⬝ᵥ x =
          row_multiplier_neg u ⬝ᵥ (A *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    have hpos_nonneg : 0 ≤ row_multiplier_pos u := by
      intro i
      simp [row_multiplier_pos]
    have hpos_le :
        row_multiplier_pos u ⬝ᵥ (A *ᵥ x) ≤ row_multiplier_pos u ⬝ᵥ b := by
      exact dotProduct_le_dotProduct_of_nonneg_left hxP hpos_nonneg
    have hbeta :
        row_multiplier_pos u ⬝ᵥ b - row_multiplier_neg u ⬝ᵥ b = u ⬝ᵥ b := by
      calc
        row_multiplier_pos u ⬝ᵥ b - row_multiplier_neg u ⬝ᵥ b =
            (row_multiplier_pos u - row_multiplier_neg u) ⬝ᵥ b := by
              rw [sub_dotProduct]
        _ = u ⬝ᵥ b := by
              rw [row_multiplier_pos_sub_neg_eq]
    have hdecomp :
        u ⬝ᵥ (A *ᵥ x) =
          row_multiplier_pos u ⬝ᵥ (A *ᵥ x) -
            row_multiplier_neg u ⬝ᵥ (A *ᵥ x) := by
      calc
        u ⬝ᵥ (A *ᵥ x) = (row_multiplier_pos u - row_multiplier_neg u) ⬝ᵥ (A *ᵥ x) := by
          rw [row_multiplier_pos_sub_neg_eq]
        _ = row_multiplier_pos u ⬝ᵥ (A *ᵥ x) -
              row_multiplier_neg u ⬝ᵥ (A *ᵥ x) := by
          rw [sub_dotProduct]
    -- Rewrite the MIR witness inequality into the positive-part row bound on `A x`.
    calc
      split_dot s x - (row_multiplier_neg u ⬝ᵥ b - ((row_multiplier_neg u) ᵥ* A) ⬝ᵥ x)
          = row_multiplier_pos u ⬝ᵥ (A *ᵥ x) - row_multiplier_neg u ⬝ᵥ b := by
              rw [hsplit, hnegAx, hdecomp]
              ring
      _ ≤ row_multiplier_pos u ⬝ᵥ b - row_multiplier_neg u ⬝ᵥ b := by
            exact sub_le_sub_right hpos_le _
      _ = u ⬝ᵥ b := hbeta
  · intro x hxP
    have hneg_nonneg : 0 ≤ row_multiplier_neg u := by
      intro i
      simp [row_multiplier_neg]
    have hneg_le :
        row_multiplier_neg u ⬝ᵥ (A *ᵥ x) ≤ row_multiplier_neg u ⬝ᵥ b := by
      exact dotProduct_le_dotProduct_of_nonneg_left hxP hneg_nonneg
    -- The correction row is nonnegative, so feasibility of `A x ≤ b` bounds it by `γ`.
    simpa [Matrix.dotProduct_mulVec] using hneg_le

/-- On the matrix polyhedron `polyhedron_le_set A b`, the source-facing set-level mixed split
closure agrees with the canonical Chapter 5 split-closure owner
`splitClosure A b I.toFinite.toFinset`. -/
theorem mixed_split_closure_polyhedron_le_set_eq_splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^split[I] =
      splitClosure A b I.toFinite.toFinset := by
  -- Route correction: the source-facing wrapper must retain ambient polyhedron membership.
  ext x
  simp [mixed_split_closure, splitClosure, split_polyhedron]

/-- Membership in the source-facing mixed split closure of `polyhedron_le_set A b` is
equivalently membership in the canonical Chapter 5 split closure. -/
theorem mem_mixed_split_closure_polyhedron_le_set_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n))
    (x : Fin n → ℝ) :
    x ∈ (polyhedron_le_set A b)^split[I] ↔
      x ∈ splitClosure A b I.toFinite.toFinset := by
  simp [mixed_split_closure_polyhedron_le_set_eq_splitClosure A b I]

/-- Helper for Theorem 5.12: a point in the split closure satisfies every MIR inequality by
checking the zero-split case directly and the supported nonzero case on the corresponding split
hull. -/
lemma splitClosure_subset_mixedIntegerRoundingClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    splitClosure A b I.toFinite.toFinset ⊆ (polyhedron_le_set A b)^MIR[I] := by
  intro x hx
  rcases (mem_splitClosure_iff A b I.toFinite.toFinset x).mp hx with ⟨hxP, hxSplit⟩
  refine (mem_mixed_integer_rounding_closure_iff I (polyhedron_le_set A b) x).2 ?_
  refine ⟨hxP, ?_⟩
  intro a δ hMir
  rcases hMir with ⟨π, c, γ, β, hsupport, hvalid, hc, ha, hδ⟩
  by_cases hπ : π = 0
  · -- Route correction: the zero split is handled directly on the ambient polyhedron.
    subst hπ
    rw [ha, hδ]
    by_cases hfloor : 0 ≤ Int.floor β
    · have hxLower :
          x ∈ split_branch_lower (polyhedron_le_set A b) 0 (⌊β⌋) := by
        refine (mem_split_branch_lower_iff).2 ⟨hxP, ?_⟩
        simpa [split_dot] using hfloor
      exact mirInequalityValidOnLowerBranch hc hxLower
    · have hupper_int : Int.floor β + 1 ≤ 0 := by
        exact Int.add_one_le_iff.mpr (lt_of_not_ge hfloor)
      have hxUpper :
          x ∈ split_branch_upper (polyhedron_le_set A b) 0 (⌊β⌋) := by
        refine (mem_split_branch_upper_iff).2 ⟨hxP, ?_⟩
        have hupper_real : (⌊β⌋ : ℝ) + 1 ≤ (0 : ℝ) := by
          exact_mod_cast hupper_int
        simpa [split_dot] using hupper_real
      exact mirInequalityValidOnUpperBranch hvalid hxUpper
  · let s : Split I.toFinite.toFinset := {
        π := π
        π0 := Int.floor β
        nonzero := hπ
        zero_on_continuous := by
          intro j hj
          exact hsupport j (by simpa using hj) }
    have hxHull : x ∈ (polyhedron_le_set A b)^(s, s.π0) := by
      simpa [split_polyhedron] using hxSplit s
    -- The supported nonzero case is exactly the split-hull validity bridge.
    rw [ha, hδ]
    exact mirInequalityValidOnSplitHull hvalid hc hxHull

/-- Helper for Theorem 5.12: a packaged MIR bound implies the weighted slack inequality behind
`split_cut_value`. -/
lemma weightedSlackBound_ofMirBound
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n))
    (s : Split I.toFinite.toFinset)
    (u : Fin m → ℝ)
    (huBasic : u ∈ basic_row_multiplier_set A s)
    (hub_left : (s.π0 : ℝ) < u ⬝ᵥ b)
    (hub_right : u ⬝ᵥ b < (s.π0 : ℝ) + 1)
    {x : Fin n → ℝ}
    (_hxP : x ∈ polyhedron_le_set A b)
    (hMir :
      (fun i : Fin n ↦
        (s i : ℝ) + ((row_multiplier_neg u) ᵥ* A) i / (1 - Int.fract (u ⬝ᵥ b))) ⬝ᵥ x ≤
        (⌊u ⬝ᵥ b⌋ : ℝ) + (row_multiplier_neg u ⬝ᵥ b) / (1 - Int.fract (u ⬝ᵥ b))) :
    Int.fract (u ⬝ᵥ b) * (1 - Int.fract (u ⬝ᵥ b)) ≤
      (1 - Int.fract (u ⬝ᵥ b)) * (row_multiplier_pos u ⬝ᵥ (b - A *ᵥ x)) +
        Int.fract (u ⬝ᵥ b) * (row_multiplier_neg u ⬝ᵥ (b - A *ᵥ x)) := by
  rcases (mem_basic_row_multiplier_set_iff A s u).mp huBasic with ⟨huπ, _⟩
  let f : ℝ := Int.fract (u ⬝ᵥ b)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ (b - A *ᵥ x)
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ (b - A *ᵥ x)
  have hfloor : Int.floor (u ⬝ᵥ b) = s.π0 := by
    refine Int.floor_eq_iff.mpr ?_
    constructor <;> linarith
  have hf_lt_one : f < 1 := by
    dsimp [f]
    exact Int.fract_lt_one _
  have hOneSubPos : 0 < 1 - f := by
    linarith
  have hub_decomp : u ⬝ᵥ b = (s.π0 : ℝ) + f := by
    calc
      u ⬝ᵥ b = (⌊u ⬝ᵥ b⌋ : ℝ) + Int.fract (u ⬝ᵥ b) := by
        exact (Int.floor_add_fract (u ⬝ᵥ b)).symm
      _ = (s.π0 : ℝ) + Int.fract (u ⬝ᵥ b) := by
        rw [hfloor]
      _ = (s.π0 : ℝ) + f := by
        rfl
  have hMir' :
      split_dot s x + row_multiplier_neg u ⬝ᵥ (A *ᵥ x) / (1 - f) ≤
        (s.π0 : ℝ) + row_multiplier_neg u ⬝ᵥ b / (1 - f) := by
    have hnegAx :
        ((row_multiplier_neg u) ᵥ* A) ⬝ᵥ x =
          row_multiplier_neg u ⬝ᵥ (A *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    dsimp [f] at hMir ⊢
    rw [mirWitnessDot_eq, hnegAx] at hMir
    simpa [hfloor] using hMir
  have hnegSlack :
      row_multiplier_neg u ⬝ᵥ b =
        s2 + row_multiplier_neg u ⬝ᵥ (A *ᵥ x) := by
    dsimp [s2]
    rw [dotProduct_sub]
    ring
  have hbranch :
      split_dot s x - (s.π0 : ℝ) ≤ s2 / (1 - f) := by
    have hMir'' :
        split_dot s x + row_multiplier_neg u ⬝ᵥ (A *ᵥ x) / (1 - f) ≤
          (s.π0 : ℝ) + s2 / (1 - f) +
            row_multiplier_neg u ⬝ᵥ (A *ᵥ x) / (1 - f) := by
      rw [hnegSlack, add_div] at hMir'
      simpa [add_assoc, add_left_comm, add_comm] using hMir'
    -- Move the shared correction term to the other side so only the slack numerator remains.
    linarith
  have hscaled :
      (split_dot s x - (s.π0 : ℝ)) * (1 - f) ≤ s2 := by
    exact (le_div_iff₀ hOneSubPos).mp hbranch
  have hgap_eq : s1 - s2 = u ⬝ᵥ b - split_dot s x := by
    simpa [s1, s2] using splitCutRowSlackGap_eq_rhsGap A b u s huπ x
  have hsplit_eq : split_dot s x - (s.π0 : ℝ) = f - s1 + s2 := by
    linarith [hgap_eq, hub_decomp]
  have hweighted : f * (1 - f) ≤ (1 - f) * s1 + f * s2 := by
    rw [hsplit_eq] at hscaled
    -- Expanding the scaled branch inequality produces the weighted slack numerator inequality.
    nlinarith
  simpa [f, s1, s2] using hweighted

/-- Helper for Theorem 5.12: the MIR bound attached to a basic split cut is exactly strong enough
to imply the Chapter 5 split-cut inequality `1 ≤ split_cut_value`. -/
lemma splitCutValueGeOneOfMirBound
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n))
    (s : Split I.toFinite.toFinset)
    (u : Fin m → ℝ)
    (huBasic : u ∈ basic_row_multiplier_set A s)
    (hub_left : (s.π0 : ℝ) < u ⬝ᵥ b)
    (hub_right : u ⬝ᵥ b < (s.π0 : ℝ) + 1)
    {x : Fin n → ℝ}
    (hxP : x ∈ polyhedron_le_set A b)
    (hMir :
      (fun i : Fin n ↦
        (s i : ℝ) + ((row_multiplier_neg u) ᵥ* A) i / (1 - Int.fract (u ⬝ᵥ b))) ⬝ᵥ x ≤
        (⌊u ⬝ᵥ b⌋ : ℝ) + (row_multiplier_neg u ⬝ᵥ b) / (1 - Int.fract (u ⬝ᵥ b))) :
    1 ≤ split_cut_value A b u s.π0 x := by
  let f : ℝ := Int.fract (u ⬝ᵥ b)
  let s1 : ℝ := row_multiplier_pos u ⬝ᵥ (b - A *ᵥ x)
  let s2 : ℝ := row_multiplier_neg u ⬝ᵥ (b - A *ᵥ x)
  have hweighted :=
    weightedSlackBound_ofMirBound A b I s u huBasic hub_left hub_right hxP hMir
  have hfloor : Int.floor (u ⬝ᵥ b) = s.π0 := by
    refine Int.floor_eq_iff.mpr ?_
    constructor <;> linarith
  have hub_decomp : u ⬝ᵥ b = (s.π0 : ℝ) + f := by
    calc
      u ⬝ᵥ b = (⌊u ⬝ᵥ b⌋ : ℝ) + Int.fract (u ⬝ᵥ b) := by
        exact (Int.floor_add_fract (u ⬝ᵥ b)).symm
      _ = (s.π0 : ℝ) + Int.fract (u ⬝ᵥ b) := by
        rw [hfloor]
      _ = (s.π0 : ℝ) + f := by
        rfl
  have hf_pos : 0 < f := by
    linarith [hub_decomp]
  have hOneSubPos : 0 < 1 - f := by
    linarith [hub_decomp]
  have hcut :
      split_cut_value A b u s.π0 x = s1 / f + s2 / (1 - f) := by
    have hden1 : u ⬝ᵥ b - (s.π0 : ℝ) = f := by
      linarith [hub_decomp]
    have hden2 : (s.π0 : ℝ) + 1 - u ⬝ᵥ b = 1 - f := by
      linarith [hub_decomp]
    -- Route correction: rewrite the Chapter 5 cut only after the numerator inequality is in hand.
    simpa [s1, s2] using (show split_cut_value A b u s.π0 x = s1 / f + s2 / (1 - f) by
      rw [split_cut_value, hden1, hden2])
  have hrepr :
      s1 / f + s2 / (1 - f) = ((1 - f) * s1 + f * s2) / (f * (1 - f)) := by
    field_simp [hf_pos.ne', hOneSubPos.ne']
  rw [hcut, hrepr]
  exact (le_div_iff₀ (mul_pos hf_pos hOneSubPos)).2 (by simpa [f, s1, s2] using hweighted)

/-- Helper for Theorem 5.12: every MIR-closed point satisfies every basic split cut from
Theorem 5.5, hence lies in the canonical split closure. -/
lemma mirClosureSubsetSplitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^MIR[I] ⊆ splitClosure A b I.toFinite.toFinset := by
  intro x hx
  rcases (mem_mixed_integer_rounding_closure_iff I (polyhedron_le_set A b) x).mp hx with
    ⟨hxP, hxMir⟩
  refine (mem_splitClosure_iff A b I.toFinite.toFinset x).2 ⟨hxP, ?_⟩
  intro s
  rw [split_polyhedron_eq_basic_split_cut_system A b s]
  refine (mem_basic_split_cut_system_iff A b s s.π0 x).2 ⟨hxP, ?_⟩
  intro u huBasic hub_left hub_right
  have hMirBound :
      (fun i : Fin n ↦
        (s i : ℝ) + ((row_multiplier_neg u) ᵥ* A) i / (1 - Int.fract (u ⬝ᵥ b))) ⬝ᵥ x ≤
        (⌊u ⬝ᵥ b⌋ : ℝ) + (row_multiplier_neg u ⬝ᵥ b) / (1 - Int.fract (u ⬝ᵥ b)) :=
    hxMir _ _ (basicSplitCutIsMir A b I s u huBasic hub_left hub_right)
  -- Feed the packaged MIR witness through the arithmetic bridge to recover the split cut.
  exact splitCutValueGeOneOfMirBound A b I s u huBasic hub_left hub_right hxP hMirBound

/-- Theorem 5.12. For the polyhedron `P = {x ∈ ℝ^n | A x ≤ b}`, the mixed integer rounding
closure `(P)^MIR[I]` equals the canonical Chapter 5 split closure relative to the same
integer-coordinate set `I`. -/
theorem mixed_integer_rounding_closure_eq_splitClosure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^MIR[I] =
      splitClosure A b I.toFinite.toFinset := by
  -- Theorem 5.12 is exactly the pair of closure containments proved above.
  exact Set.Subset.antisymm
    (mirClosureSubsetSplitClosure A b I)
    (splitClosure_subset_mixedIntegerRoundingClosure A b I)

/-- Theorem 5.12 in the source-facing closure notation `P^MIR[I] = P^split[I]`. -/
theorem mixed_integer_rounding_closure_eq_mixed_split_closure
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (I : Set (Fin n)) :
    (polyhedron_le_set A b)^MIR[I] =
      (polyhedron_le_set A b)^split[I] := by
  simpa [mixed_split_closure_polyhedron_le_set_eq_splitClosure A b I] using
    mixed_integer_rounding_closure_eq_splitClosure A b I

end Theorem512
