/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_theorem_3_40

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain/style note: keep the exercise-specific polyhedron and generators as source-facing data,
-- and reuse the Chapter 3 owner layer `recessionCone`/`is_pointed` together with
-- `IsExtremeRayOfPolyhedron` for the derived pointedness and extreme-ray API.

open scoped BigOperators

/-- The polyhedron from Exercise 3.29, written in coordinates `(x₀, …, xₙ)`. -/
def exercise_3_29_polyhedron {n : ℕ} (b : Fin n → ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | 0 ≤ x 0 ∧ ∀ t : Fin n, b t ≤ x 0 + x (Fin.succ t)}

/-- Membership in the polyhedron from Exercise 3.29 is exactly the coordinate inequality system
`x₀ ≥ 0` and `x₀ + x_t ≥ b_t` for `t = 1, …, n`. -/
theorem mem_exercise_3_29_polyhedron_iff {n : ℕ} {b : Fin n → ℝ} {x : Fin (n + 1) → ℝ} :
    x ∈ exercise_3_29_polyhedron b ↔ 0 ≤ x 0 ∧ ∀ t : Fin n, b t ≤ x 0 + x (Fin.succ t) := Iff.rfl

/-- The distinguished generators `r⁰, …, rⁿ` from Exercise 3.29. -/
def exercise_3_29_ray {n : ℕ} (s : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun i ↦ if s = 0 then if i = 0 then 1 else -1 else if i = s then 1 else 0

/-- Coordinate formula for the distinguished generators from Exercise 3.29. -/
theorem exercise_3_29_ray_apply {n : ℕ} (s i : Fin (n + 1)) :
    exercise_3_29_ray s i = if s = 0 then if i = 0 then 1 else -1 else if i = s then 1 else 0 :=
  rfl

/-- Each distinguished generator from Exercise 3.29 is nonzero. -/
theorem exercise_3_29_ray_ne_zero {n : ℕ} (s : Fin (n + 1)) :
    exercise_3_29_ray s ≠ 0 := by
  intro hs
  have hs_eval : exercise_3_29_ray s s = 1 := by
    by_cases h0 : s = 0
    · simp [exercise_3_29_ray, h0]
    · simp [exercise_3_29_ray, h0]
  have hs_zero : exercise_3_29_ray s s = 0 := congrFun hs s
  have h10 : (1 : ℝ) = 0 := hs_eval.symm.trans hs_zero
  exact one_ne_zero h10

/-- Helper for Exercise 3.29: the base point `(0, b₁, …, bₙ)` is feasible for the exercise
polyhedron. -/
lemma exercise_3_29_basepoint_mem {n : ℕ} (b : Fin n → ℝ) :
    Fin.cases 0 b ∈ exercise_3_29_polyhedron b := by
  -- The base point saturates every defining inequality.
  rw [mem_exercise_3_29_polyhedron_iff]
  constructor
  · simp
  · intro t
    simp

/-- Helper for Exercise 3.29: a direction is in the recession cone exactly when it preserves the
coordinate inequalities `x₀ ≥ 0` and `x₀ + x_t ≥ b_t` under translation. -/
lemma exercise_3_29_mem_recessionCone_iff {n : ℕ} {b : Fin n → ℝ} {r : Fin (n + 1) → ℝ} :
    r ∈ recessionCone (exercise_3_29_polyhedron b) ↔
      0 ≤ r 0 ∧ ∀ t : Fin n, 0 ≤ r 0 + r (Fin.succ t) := by
  constructor
  · intro hr
    rw [mem_recessionCone_iff] at hr
    -- Evaluate the recession-direction condition at the feasible base point.
    have hbase := hr (exercise_3_29_basepoint_mem b) 1 zero_le_one
    rw [mem_exercise_3_29_polyhedron_iff] at hbase
    constructor
    · simpa using hbase.1
    · intro t
      have ht : b t ≤ b t + (r 0 + r (Fin.succ t)) := by
        simpa [exercise_3_29_basepoint_mem, add_assoc, add_left_comm, add_comm] using hbase.2 t
      linarith
  · rintro ⟨hr0, hrineq⟩
    rw [mem_recessionCone_iff]
    intro x hx a ha
    rw [mem_exercise_3_29_polyhedron_iff] at hx ⊢
    constructor
    · -- The zeroth coordinate stays nonnegative after moving in a recession direction.
      simpa [Pi.add_apply, Pi.smul_apply, mul_comm] using add_nonneg hx.1 (mul_nonneg ha hr0)
    · intro t
      -- Each mixed inequality gains the nonnegative increment `a * (r₀ + r_t)`.
      have hdir : 0 ≤ a * r 0 + a * r (Fin.succ t) := by
        simpa [mul_add] using mul_nonneg ha (hrineq t)
      have ht : b t ≤ x 0 + x (Fin.succ t) + (a * r 0 + a * r (Fin.succ t)) := by
        linarith [hx.2 t, hdir]
      simpa [Pi.add_apply, Pi.smul_apply, add_assoc, add_left_comm, add_comm, mul_comm,
        mul_left_comm, mul_assoc] using ht

/-- Helper for Exercise 3.29: every distinguished generator is a recession direction of the
exercise polyhedron. -/
lemma exercise_3_29_ray_mem_recessionCone {n : ℕ} (b : Fin n → ℝ) (s : Fin (n + 1)) :
    exercise_3_29_ray s ∈ recessionCone (exercise_3_29_polyhedron b) := by
  rw [exercise_3_29_mem_recessionCone_iff]
  by_cases h0 : s = 0
  · constructor
    · simp [exercise_3_29_ray, h0]
    · intro t
      simp [exercise_3_29_ray, h0]
  · constructor
    · have h0' : ¬ (0 : Fin (n + 1)) = s := by
        simpa [eq_comm] using h0
      simp [exercise_3_29_ray, h0, h0']
    · intro t
      have h0' : ¬ (0 : Fin (n + 1)) = s := by
        simpa [eq_comm] using h0
      by_cases ht : Fin.succ t = s
      · simp [exercise_3_29_ray, h0, h0', ht]
      · simp [exercise_3_29_ray, h0, h0', ht]

/-- Helper for Exercise 3.29: the recession directions of the exercise polyhedron are the carrier
of a canonical convex cone. -/
lemma exercise_3_29_recessionCone_as_convexCone {n : ℕ} (b : Fin n → ℝ) :
    ∃ K : ConvexCone ℝ (Fin (n + 1) → ℝ),
      (K : Set (Fin (n + 1) → ℝ)) = recessionCone (exercise_3_29_polyhedron b) := by
  -- The recession cone already comes with the canonical pointed-cone structure from Definition
  -- 3.6-extra-1, so we only expose its underlying convex-cone carrier here.
  refine ⟨(recessionPointedCone ℝ (exercise_3_29_polyhedron b) : ConvexCone ℝ
    (Fin (n + 1) → ℝ)), rfl⟩

/-- Helper for Exercise 3.29: the recession directions of the exercise polyhedron are the carrier
of a canonical pointed cone. -/
lemma exercise_3_29_recessionCone_as_pointedCone {n : ℕ} (b : Fin n → ℝ) :
    ∃ K : PointedCone ℝ (Fin (n + 1) → ℝ),
      (K : Set (Fin (n + 1) → ℝ)) = recessionCone (exercise_3_29_polyhedron b) := by
  exact ⟨recessionPointedCone ℝ (exercise_3_29_polyhedron b), rfl⟩

/-- Helper for Exercise 3.29: an extreme-ray generator belongs to the ambient cone whose edge it
spans. -/
lemma exercise_3_29_extreme_ray_mem {n : ℕ} {C : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hr : IsExtremeRayOfCone C r) :
    r ∈ C := by
  -- Evaluate the extreme-subset condition at the generator itself.
  have hr_edge :
      IsEdgeOf C (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) :=
    (isExtremeRayOfCone_iff).1 hr
  have hr_hull : r ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    exact PointedCone.subset_hull (by simp)
  exact hr_edge.isExtreme.1 hr_hull

/-- Helper for Exercise 3.29: a vector with `r₀ > 0` and all mixed recession coefficients zero lies
on the distinguished ray `r⁰`. -/
lemma exercise_3_29_eq_smul_ray_zero_of_eq_zero
    {n : ℕ} {r : Fin (n + 1) → ℝ}
    (h : ∀ t : Fin n, r 0 + r (Fin.succ t) = 0) :
    r = r 0 • exercise_3_29_ray (0 : Fin (n + 1)) := by
  -- Coordinatewise, the vanishing mixed coefficients force every tail coordinate to be `-r₀`.
  ext i
  refine Fin.cases ?_ ?_ i
  · simp [exercise_3_29_ray]
  · intro t
    have ht : r (Fin.succ t) = -r 0 := by
      linarith [h t]
    simp [exercise_3_29_ray, ht]

/-- Helper for Exercise 3.29: if only one tail coordinate is positive and all other tail
coordinates vanish, then the vector lies on the corresponding distinguished coordinate ray. -/
lemma exercise_3_29_eq_smul_ray_succ_of_unique_support
    {n : ℕ} {r : Fin (n + 1) → ℝ} {t0 : Fin n}
    (h0 : r 0 = 0)
    (huniq : ∀ t : Fin n, t ≠ t0 → r (Fin.succ t) = 0) :
    r = r (Fin.succ t0) • exercise_3_29_ray (Fin.succ t0) := by
  -- The coordinate-ray case is the `r₀ = 0` specialization of the recession-coordinate system.
  ext i
  refine Fin.cases ?_ ?_ i
  · have hs : ¬ (Fin.succ t0 : Fin (n + 1)) = 0 := by
      simp
    have hs' : ¬ (0 : Fin (n + 1)) = Fin.succ t0 := by
      simpa [eq_comm] using hs
    simp [exercise_3_29_ray, h0, hs, hs']
  · intro t
    by_cases ht : t = t0
    · subst ht
      simp [exercise_3_29_ray]
    · simp [exercise_3_29_ray, ht, huniq t ht]

/-- Helper for Exercise 3.29: membership in the singleton pointed-cone hull is exactly being a
nonnegative scalar multiple of the generator. -/
lemma exercise_3_29_mem_singleton_pointedCone_hull_iff
    {n : ℕ} {r x : Fin n → ℝ} :
    x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
      ∃ μ : ℝ, 0 ≤ μ ∧ x = μ • r := by
  have hmem :
      x ∈ (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) ↔
        ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℝ, (∀ j, rays j ∈ ({r} : Set (Fin n → ℝ))) ∧
          ∃ coeff : Fin q → ℝ, (∀ j, 0 ≤ coeff j) ∧ x = ∑ j, coeff j • rays j := by
    simpa using (mem_hull_iff (X := ({r} : Set (Fin n → ℝ))) (v := x))
  rw [hmem]
  constructor
  · rintro ⟨q, rays, hrays, coeff, hcoeff, hsum⟩
    -- Collapse the finite conic combination because every source vector is the same singleton
    -- generator.
    refine ⟨∑ j, coeff j, Finset.sum_nonneg fun j _ ↦ hcoeff j, ?_⟩
    calc
      x = ∑ j, coeff j • rays j := hsum
      _ = ∑ j, coeff j • r := by
            apply Finset.sum_congr rfl
            intro j hj
            have hrj : rays j = r := Set.mem_singleton_iff.mp (hrays j)
            simp [hrj]
      _ = (∑ j, coeff j) • r := by
            rw [Finset.sum_smul]
  · rintro ⟨μ, hμ, rfl⟩
    -- A single nonnegative coefficient gives the canonical witness in the singleton hull.
    refine ⟨1, fun _ ↦ r, ?_, fun _ ↦ μ, ?_, ?_⟩
    · intro j
      simp
    · intro j
      exact hμ
    · simp

/-- Helper for Exercise 3.29: perturbing by `r⁰` shifts only the head coordinate. -/
lemma exercise_3_29_ray_zero_head_coordinate_effect
    {n : ℕ} (x : Fin (n + 1) → ℝ) (ε : ℝ) :
    (x + ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 + ε ∧
      (x - ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 - ε := by
  -- The head coordinate of `r⁰` is `1`, so addition and subtraction only change `x₀`.
  constructor
  · simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray]
  · simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray]

/-- Helper for Exercise 3.29: perturbing by `r⁰` leaves every mixed sum `x₀ + x_t` unchanged. -/
lemma exercise_3_29_ray_zero_mixed_coordinate_effect
    {n : ℕ} (x : Fin (n + 1) → ℝ) (ε : ℝ) (t : Fin n) :
    (x + ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
        (x + ε • exercise_3_29_ray (0 : Fin (n + 1))) (Fin.succ t) =
      x 0 + x (Fin.succ t) ∧
      (x - ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
          (x - ε • exercise_3_29_ray (0 : Fin (n + 1))) (Fin.succ t) =
        x 0 + x (Fin.succ t) := by
  -- The `+ε` and `-ε` contributions cancel because `r⁰_t = -1` for every successor coordinate.
  constructor
  · calc
      (x + ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
          (x + ε • exercise_3_29_ray (0 : Fin (n + 1))) (Fin.succ t)
        = (x 0 + ε) + (x (Fin.succ t) + ε * (-1 : ℝ)) := by
            simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray]
      _ = x 0 + x (Fin.succ t) := by
            ring
  · calc
      (x - ε • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
          (x - ε • exercise_3_29_ray (0 : Fin (n + 1))) (Fin.succ t)
        = (x 0 - ε) + (x (Fin.succ t) - ε * (-1 : ℝ)) := by
            simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray]
      _ = x 0 + x (Fin.succ t) := by
            ring

/-- Helper for Exercise 3.29: perturbing by `rᵗ` leaves the head coordinate fixed. -/
lemma exercise_3_29_ray_succ_head_coordinate_effect
    {n : ℕ} (x : Fin (n + 1) → ℝ) (ε : ℝ) (t0 : Fin n) :
    (x + ε • exercise_3_29_ray (Fin.succ t0)) 0 = x 0 ∧
      (x - ε • exercise_3_29_ray (Fin.succ t0)) 0 = x 0 := by
  -- Every successor ray has head coordinate `0`.
  have hsucc_ne_zero : ¬ (Fin.succ t0 : Fin (n + 1)) = 0 := by
    simp
  have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ t0 := by
    simpa [eq_comm] using hsucc_ne_zero
  constructor
  · simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]
  · simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]

/-- Helper for Exercise 3.29: perturbing by the support ray `rᵗ` changes exactly the mixed sum
attached to the same support index. -/
lemma exercise_3_29_ray_succ_support_coordinate_effect
    {n : ℕ} (x : Fin (n + 1) → ℝ) (ε : ℝ) (t0 : Fin n) :
    (x + ε • exercise_3_29_ray (Fin.succ t0)) 0 +
        (x + ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t0) =
      x 0 + x (Fin.succ t0) + ε ∧
      (x - ε • exercise_3_29_ray (Fin.succ t0)) 0 +
          (x - ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t0) =
        x 0 + x (Fin.succ t0) - ε := by
  -- Only the support coordinate of `rᵗ` contributes, and it contributes `1`.
  have hsucc_ne_zero : ¬ (Fin.succ t0 : Fin (n + 1)) = 0 := by
    simp
  have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ t0 := by
    simpa [eq_comm] using hsucc_ne_zero
  constructor
  · calc
      (x + ε • exercise_3_29_ray (Fin.succ t0)) 0 +
          (x + ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t0)
        = x 0 + (x (Fin.succ t0) + ε) := by
            simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]
      _ = x 0 + x (Fin.succ t0) + ε := by
            ring
  · calc
      (x - ε • exercise_3_29_ray (Fin.succ t0)) 0 +
          (x - ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t0)
        = x 0 + (x (Fin.succ t0) - ε) := by
            simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]
      _ = x 0 + x (Fin.succ t0) - ε := by
            ring

/-- Helper for Exercise 3.29: perturbing by a support ray leaves every off-support mixed sum
unchanged. -/
lemma exercise_3_29_ray_succ_offsupport_coordinate_effect
    {n : ℕ} (x : Fin (n + 1) → ℝ) (ε : ℝ) {t0 t : Fin n}
    (ht : t ≠ t0) :
    (x + ε • exercise_3_29_ray (Fin.succ t0)) 0 +
        (x + ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t) =
      x 0 + x (Fin.succ t) ∧
      (x - ε • exercise_3_29_ray (Fin.succ t0)) 0 +
          (x - ε • exercise_3_29_ray (Fin.succ t0)) (Fin.succ t) =
        x 0 + x (Fin.succ t) := by
  -- Off the support index, the successor ray vanishes identically.
  have hsucc_ne_zero : ¬ (Fin.succ t0 : Fin (n + 1)) = 0 := by
    simp
  have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ t0 := by
    simpa [eq_comm] using hsucc_ne_zero
  constructor
  · simp [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, ht, hsucc_ne_zero, hzero_ne_succ]
  · simp [Pi.sub_apply, Pi.smul_apply, exercise_3_29_ray, ht, hsucc_ne_zero, hzero_ne_succ]

/-- Helper for Exercise 3.29: a positive weighted sum of two nonnegative reals can vanish only if
both summands vanish. -/
lemma positive_weighted_sum_eq_zero_of_nonneg
    {μ₁ μ₂ a b : ℝ} (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsum : μ₁ * a + μ₂ * b = 0) :
    a = 0 ∧ b = 0 := by
  -- Each summand is nonnegative, so equality to zero forces both summands to be zero.
  have hμ₁a_nonneg : 0 ≤ μ₁ * a := mul_nonneg (le_of_lt hμ₁) ha
  have hμ₂b_nonneg : 0 ≤ μ₂ * b := mul_nonneg (le_of_lt hμ₂) hb
  have hμ₁a_zero : μ₁ * a = 0 := by
    linarith
  have hμ₂b_zero : μ₂ * b = 0 := by
    linarith
  constructor
  · exact (mul_eq_zero.mp hμ₁a_zero).resolve_left hμ₁.ne'
  · exact (mul_eq_zero.mp hμ₂b_zero).resolve_left hμ₂.ne'

/-- Helper for Exercise 3.29: moving in the distinguished ray `r⁰` preserves feasibility as long
as the zeroth coordinate stays nonnegative. -/
lemma exercise_3_29_perturb_zero_mem_polyhedron
    {n : ℕ} {b : Fin n → ℝ} {x : Fin (n + 1) → ℝ}
    (hx : x ∈ exercise_3_29_polyhedron b) {ε : ℝ}
    (hε : 0 ≤ ε) (hεx : ε ≤ x 0) :
    x + ε • exercise_3_29_ray (0 : Fin (n + 1)) ∈ exercise_3_29_polyhedron b ∧
      x - ε • exercise_3_29_ray (0 : Fin (n + 1)) ∈ exercise_3_29_polyhedron b := by
  -- Rewriting by the `r⁰` coordinate formulas reduces feasibility to the original inequalities and
  -- the backward head-coordinate bound `ε ≤ x₀`.
  rcases (mem_exercise_3_29_polyhedron_iff.mp hx) with ⟨hx0, hxineq⟩
  constructor
  · rw [mem_exercise_3_29_polyhedron_iff]
    constructor
    · rcases exercise_3_29_ray_zero_head_coordinate_effect x ε with ⟨hhead, _⟩
      rw [hhead]
      linarith
    · intro t
      rcases exercise_3_29_ray_zero_mixed_coordinate_effect x ε t with ⟨hmixed, _⟩
      rw [hmixed]
      exact hxineq t
  · rw [mem_exercise_3_29_polyhedron_iff]
    constructor
    · rcases exercise_3_29_ray_zero_head_coordinate_effect x ε with ⟨_, hhead⟩
      rw [hhead]
      linarith
    · intro t
      rcases exercise_3_29_ray_zero_mixed_coordinate_effect x ε t with ⟨_, hmixed⟩
      rw [hmixed]
      exact hxineq t

/-- Helper for Exercise 3.29: moving in a coordinate ray `rᵗ` preserves feasibility as long as the
corresponding slack `x₀ + x_t - b_t` stays nonnegative. -/
lemma exercise_3_29_perturb_succ_mem_polyhedron
    {n : ℕ} {b : Fin n → ℝ} {x : Fin (n + 1) → ℝ} (t0 : Fin n)
    (hx : x ∈ exercise_3_29_polyhedron b) {ε : ℝ}
    (hε : 0 ≤ ε) (hεx : ε ≤ x 0 + x (Fin.succ t0) - b t0) :
    x + ε • exercise_3_29_ray (Fin.succ t0) ∈ exercise_3_29_polyhedron b ∧
      x - ε • exercise_3_29_ray (Fin.succ t0) ∈ exercise_3_29_polyhedron b := by
  -- Rewriting by the `rᵗ` support/off-support formulas isolates the unique mixed inequality that
  -- changes under the perturbation.
  rcases (mem_exercise_3_29_polyhedron_iff.mp hx) with ⟨hx0, hxineq⟩
  constructor
  · rw [mem_exercise_3_29_polyhedron_iff]
    constructor
    · rcases exercise_3_29_ray_succ_head_coordinate_effect x ε t0 with ⟨hhead, _⟩
      simpa [hhead] using hx0
    · intro t
      by_cases ht : t = t0
      · subst ht
        rcases exercise_3_29_ray_succ_support_coordinate_effect x ε t with ⟨hmixed, _⟩
        rw [hmixed]
        linarith [hxineq t, hε]
      · rcases exercise_3_29_ray_succ_offsupport_coordinate_effect x ε ht with ⟨hmixed, _⟩
        rw [hmixed]
        exact hxineq t
  · rw [mem_exercise_3_29_polyhedron_iff]
    constructor
    · rcases exercise_3_29_ray_succ_head_coordinate_effect x ε t0 with ⟨_, hhead⟩
      simpa [hhead] using hx0
    · intro t
      by_cases ht : t = t0
      · subst ht
        rcases exercise_3_29_ray_succ_support_coordinate_effect x ε t with ⟨_, hmixed⟩
        rw [hmixed]
        linarith [hxineq t, hεx]
      · rcases exercise_3_29_ray_succ_offsupport_coordinate_effect x ε ht with ⟨_, hmixed⟩
        rw [hmixed]
        exact hxineq t

/-- Helper for Exercise 3.29: any nonnegative combination of the coordinate rays `r¹, …, rⁿ`
belongs to the recession cone. -/
lemma exercise_3_29_sum_succ_rays_mem_recessionCone
    {n : ℕ} (b : Fin n → ℝ) (coeff : Fin n → ℝ)
    (hcoeff : ∀ t : Fin n, 0 ≤ coeff t) :
    (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) ∈
      recessionCone (exercise_3_29_polyhedron b) := by
  -- The recession cone is a pointed cone, so finite sums of nonnegative scalar multiples of known
  -- recession directions remain inside it.
  change (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) ∈
    recessionPointedCone ℝ (exercise_3_29_polyhedron b)
  exact Submodule.sum_mem _ fun t _ ↦
    PointedCone.smul_mem _ (hcoeff t) (exercise_3_29_ray_mem_recessionCone b (Fin.succ t))

/-- Helper for Exercise 3.29: every finite sum of successor rays has head coordinate `0`. -/
lemma exercise_3_29_sum_succ_rays_head_coordinate
    {n : ℕ} (coeff : Fin n → ℝ) :
    (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) 0 = 0 := by
  -- Only the distinguished head-positive ray `r⁰` contributes at coordinate `0`.
  calc
    (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) 0
      = ∑ t : Fin n, (coeff t • exercise_3_29_ray (Fin.succ t)) 0 := by
          simp
    _ = ∑ t : Fin n, 0 := by
          apply Finset.sum_congr rfl
          intro t ht
          have hsucc_ne_zero : ¬ (Fin.succ t : Fin (n + 1)) = 0 := by
            simp
          have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ t := by
            simpa [eq_comm] using hsucc_ne_zero
          simp [Pi.smul_apply, exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]
    _ = 0 := by
          simp

/-- Helper for Exercise 3.29: a finite sum of successor rays reads off the coefficient at the
matching successor coordinate. -/
lemma exercise_3_29_sum_succ_rays_succ_coordinate
    {n : ℕ} (coeff : Fin n → ℝ) (t0 : Fin n) :
    (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) (Fin.succ t0) = coeff t0 := by
  -- Only the matching successor ray survives at coordinate `Fin.succ t0`.
  calc
    (∑ t : Fin n, coeff t • exercise_3_29_ray (Fin.succ t)) (Fin.succ t0)
      = ∑ t : Fin n, (coeff t • exercise_3_29_ray (Fin.succ t)) (Fin.succ t0) := by
          simp
    _ = ∑ t : Fin n, coeff t * (if t = t0 then 1 else 0 : ℝ) := by
          apply Finset.sum_congr rfl
          intro t ht
          by_cases htt : t = t0
          · simp [Pi.smul_apply, exercise_3_29_ray, htt, eq_comm]
          · have ht0t : t0 ≠ t := by
              simpa [eq_comm] using htt
            simp [Pi.smul_apply, exercise_3_29_ray, htt, ht0t]
    _ = coeff t0 := by
          rw [Finset.sum_eq_single t0]
          · simp
          · intro t _ ht
            simp [ht]
          · simp

/-- Helper for Exercise 3.29: deleting one support coefficient from a successor-ray sum makes the
matching coordinate vanish while leaving all other successor coordinates unchanged. -/
lemma exercise_3_29_sum_succ_rays_deleted_support_coordinate
    {n : ℕ} (coeff : Fin n → ℝ) (t1 t0 : Fin n) :
    (∑ t : Fin n, (if t = t1 then 0 else coeff t) • exercise_3_29_ray (Fin.succ t))
        (Fin.succ t0) =
      if t0 = t1 then 0 else coeff t0 := by
  -- Route correction: isolate the deleted-support `if`-normalization once, then reuse the clean
  -- coordinate formula downstream.
  simpa using exercise_3_29_sum_succ_rays_succ_coordinate
    (coeff := fun t : Fin n ↦ if t = t1 then 0 else coeff t) t0

/-- Helper for Exercise 3.29: every vector admits the canonical decomposition into the distinguished
rays with coefficients `r₀` and `r₀ + r_t`. -/
lemma exercise_3_29_recession_direction_eq_ray_combination
    {n : ℕ} {r : Fin (n + 1) → ℝ} :
    r = r 0 • exercise_3_29_ray (0 : Fin (n + 1)) +
      ∑ t : Fin n, (r 0 + r (Fin.succ t)) • exercise_3_29_ray (Fin.succ t) := by
  -- Route correction: instead of repeatedly unfolding the ray definition inside later
  -- classification proofs, normalize the canonical simplicial decomposition once here.
  ext i
  refine Fin.cases ?_ ?_ i
  · -- At the head coordinate, only the `r⁰` term contributes.
    symm
    calc
      (r 0 • exercise_3_29_ray (0 : Fin (n + 1)) +
          ∑ u : Fin n, (r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u)) 0
        = (r 0 • exercise_3_29_ray (0 : Fin (n + 1))) 0 +
            (∑ u : Fin n, (r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u)) 0 := by
              simp [Pi.add_apply]
      _ = r 0 + (∑ u : Fin n, (r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u)) 0 := by
              simp [Pi.smul_apply, exercise_3_29_ray]
      _ = r 0 + ∑ u : Fin n, ((r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u)) 0 := by
              simp
      _ = r 0 + ∑ u : Fin n, 0 := by
              apply congrArg (fun z => r 0 + z)
              apply Finset.sum_congr rfl
              intro u hu
              have hu_zero : exercise_3_29_ray (Fin.succ u) 0 = 0 := by
                have hsucc_ne_zero : ¬ (Fin.succ u : Fin (n + 1)) = 0 := by
                  simp
                have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ u := by
                  simpa [eq_comm] using hsucc_ne_zero
                simp [exercise_3_29_ray, hsucc_ne_zero, hzero_ne_succ]
              simp [Pi.smul_apply, hu_zero]
      _ = r 0 := by
              simp
  · intro t
    -- At the successor coordinate, the `r⁰` term contributes `-r₀` and the matching successor ray
    -- contributes `r₀ + r_t`.
    symm
    calc
      (r 0 • exercise_3_29_ray (0 : Fin (n + 1)) +
          ∑ u : Fin n, (r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u))
          (Fin.succ t)
        = (r 0 • exercise_3_29_ray (0 : Fin (n + 1))) (Fin.succ t) +
            (∑ u : Fin n, (r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u))
              (Fin.succ t) := by
              simp [Pi.add_apply]
      _ = r 0 * (-1 : ℝ) +
            ∑ u : Fin n, ((r 0 + r (Fin.succ u)) • exercise_3_29_ray (Fin.succ u))
              (Fin.succ t) := by
              simp [Pi.smul_apply, exercise_3_29_ray]
      _ = -r 0 +
            ∑ u : Fin n, (r 0 + r (Fin.succ u)) *
              exercise_3_29_ray (Fin.succ u) (Fin.succ t) := by
              simp [Pi.smul_apply]
      _ = -r 0 +
            ∑ u : Fin n, (r 0 + r (Fin.succ u)) * (if u = t then 1 else 0) := by
              apply congrArg (fun z => -r 0 + z)
              apply Finset.sum_congr rfl
              intro u hu
              by_cases hut : u = t
              · simp [exercise_3_29_ray, hut, eq_comm]
              · have htu : t ≠ u := by
                  simpa [eq_comm] using hut
                simp [exercise_3_29_ray, hut, htu]
      _ = -r 0 + (r 0 + r (Fin.succ t)) := by
              rw [Finset.sum_eq_single t]
              · simp
              · intro u _ hu
                simp [hu]
              · simp
      _ = r (Fin.succ t) := by
              ring

/-- Helper for Exercise 3.29: every point is the midpoint of its symmetric perturbation pair. -/
lemma exercise_3_29_mem_openSegment_of_symmetric_perturbation
    {n : ℕ} (x d : Fin n → ℝ) :
    x ∈ openSegment ℝ (x + d) (x - d) := by
  -- The midpoint parameter `1 / 2` recovers the original point from the symmetric endpoints.
  rw [openSegment_eq_image_lineMap]
  refine ⟨(1 / 2 : ℝ), by constructor <;> norm_num, ?_⟩
  ext i
  simp [AffineMap.lineMap_apply_module, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- Helper for Exercise 3.29: if every mixed coefficient vanishes, then the recession direction is
on the distinguished ray `r⁰`. -/
lemma exercise_3_29_sameRay_ray_zero_of_mixed_eq_zero
    {n : ℕ} {b : Fin n → ℝ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ recessionCone (exercise_3_29_polyhedron b)) (hr_ne : r ≠ 0)
    (hmix : ∀ t : Fin n, r 0 + r (Fin.succ t) = 0) :
    SameRay ℝ r (exercise_3_29_ray (0 : Fin (n + 1))) := by
  -- The mixed equalities identify `r` with a positive multiple of `r⁰`.
  have hr_eq : r = r 0 • exercise_3_29_ray (0 : Fin (n + 1)) :=
    exercise_3_29_eq_smul_ray_zero_of_eq_zero hmix
  have hr0_nonneg : 0 ≤ r 0 := (exercise_3_29_mem_recessionCone_iff.mp hr).1
  have hr0_ne : r 0 ≠ 0 := by
    intro hr0_zero
    have : r = 0 := by
      rw [hr_eq, hr0_zero]
      simp
    exact hr_ne this
  have hr0_pos : 0 < r 0 := lt_of_le_of_ne hr0_nonneg hr0_ne.symm
  rw [hr_eq]
  exact SameRay.sameRay_pos_smul_left
    (exercise_3_29_ray (0 : Fin (n + 1))) hr0_pos

/-- Helper for Exercise 3.29: if `r₀ = 0` and only one tail coordinate can be nonzero, then the
direction is on the corresponding coordinate ray. -/
lemma exercise_3_29_sameRay_ray_succ_of_head_zero_unique_support
    {n : ℕ} {b : Fin n → ℝ} {r : Fin (n + 1) → ℝ} {t0 : Fin n}
    (hr : r ∈ recessionCone (exercise_3_29_polyhedron b)) (hr_ne : r ≠ 0)
    (h0 : r 0 = 0)
    (huniq : ∀ t : Fin n, t ≠ t0 → r (Fin.succ t) = 0) :
    SameRay ℝ r (exercise_3_29_ray (Fin.succ t0)) := by
  -- The unique-support pattern identifies `r` with a positive multiple of the chosen coordinate
  -- ray.
  have hr_eq : r = r (Fin.succ t0) • exercise_3_29_ray (Fin.succ t0) :=
    exercise_3_29_eq_smul_ray_succ_of_unique_support h0 huniq
  have hr_tail_nonneg : 0 ≤ r (Fin.succ t0) := by
    simpa [h0] using (exercise_3_29_mem_recessionCone_iff.mp hr).2 t0
  have hr_tail_ne : r (Fin.succ t0) ≠ 0 := by
    intro htail_zero
    have : r = 0 := by
      rw [hr_eq, htail_zero]
      simp
    exact hr_ne this
  have hr_tail_pos : 0 < r (Fin.succ t0) := lt_of_le_of_ne hr_tail_nonneg hr_tail_ne.symm
  rw [hr_eq]
  exact SameRay.sameRay_pos_smul_left
    (exercise_3_29_ray (Fin.succ t0)) hr_tail_pos

/-- Helper for Exercise 3.29: a nonzero vector with vanishing head coordinate cannot lie on the
distinguished head-positive ray `r⁰`. -/
lemma exercise_3_29_ray_zero_not_sameRay_of_head_zero
    {n : ℕ} {q : Fin (n + 1) → ℝ}
    (hq_ne : q ≠ 0) (hq0 : q 0 = 0) :
    ¬ SameRay ℝ (exercise_3_29_ray (0 : Fin (n + 1))) q := by
  -- The head coordinate of `r⁰` is `1`, while every multiple of `q` still has head coordinate `0`.
  intro hsame
  rcases hsame.exists_nonneg_right hq_ne with ⟨a, ha, hray_eq⟩
  have hcoord := congrArg (fun p => p 0) hray_eq
  have : (1 : ℝ) = 0 := by
    simpa [exercise_3_29_ray, hq0, Pi.smul_apply] using hcoord
  exact one_ne_zero this

/-- Helper for Exercise 3.29: a vector that vanishes on the support of `rᵗ¹` but is positive at a
different support coordinate cannot lie on the same ray as `rᵗ¹`. -/
lemma exercise_3_29_ray_succ_not_sameRay_of_support_gap
    {n : ℕ} {t1 t2 : Fin n} (ht : t1 ≠ t2) {q : Fin (n + 1) → ℝ}
    (hq_gap : q (Fin.succ t1) = 0) (hq_pos : 0 < q (Fin.succ t2)) :
    ¬ SameRay ℝ (exercise_3_29_ray (Fin.succ t1)) q := by
  -- The support coordinate of `rᵗ¹` equals `1`, so a same-ray vector cannot vanish there.
  intro hsame
  have hq_ne : q ≠ 0 := by
    intro hq_zero
    have : (0 : ℝ) < 0 := by
      simpa [hq_zero] using hq_pos
    linarith
  rcases hsame.exists_nonneg_right hq_ne with ⟨a, ha, hray_eq⟩
  have hcoord := congrArg (fun p => p (Fin.succ t1)) hray_eq
  have : (1 : ℝ) = 0 := by
    simpa [exercise_3_29_ray, hq_gap, Pi.smul_apply] using hcoord
  exact one_ne_zero this

/-- Helper for Exercise 3.29: if both the head coefficient and one successor coefficient are
positive, then the recession direction splits as a proper conic combination of two distinct rays. -/
lemma exercise_3_29_proper_conic_combination_of_positive_head_and_tail
    {n : ℕ} {b : Fin n → ℝ} {r : Fin (n + 1) → ℝ} {t0 : Fin n}
    (hr : r ∈ recessionCone (exercise_3_29_polyhedron b))
    (hhead : 0 < r 0) (ht0 : 0 < r 0 + r (Fin.succ t0)) :
    ProperConicCombinationOfDistinctConeRays
      (recessionCone (exercise_3_29_polyhedron b)) r := by
  let q : Fin (n + 1) → ℝ :=
    ∑ t : Fin n, (r 0 + r (Fin.succ t)) • exercise_3_29_ray (Fin.succ t)
  have hr_props := exercise_3_29_mem_recessionCone_iff.mp hr
  have hq_mem : q ∈ recessionCone (exercise_3_29_polyhedron b) := by
    -- The tail part of the canonical decomposition is a nonnegative conic combination of
    -- successor rays.
    simpa [q] using exercise_3_29_sum_succ_rays_mem_recessionCone b
      (fun t : Fin n ↦ r 0 + r (Fin.succ t)) hr_props.2
  have hq0 : q 0 = 0 := by
    -- The canonical tail part has no head contribution.
    simpa [q] using exercise_3_29_sum_succ_rays_head_coordinate
      (coeff := fun t : Fin n ↦ r 0 + r (Fin.succ t))
  have hq_t0 : q (Fin.succ t0) = r 0 + r (Fin.succ t0) := by
    -- At the chosen support coordinate, the tail part reads off exactly the positive coefficient.
    simpa [q] using exercise_3_29_sum_succ_rays_succ_coordinate
      (coeff := fun t : Fin n ↦ r 0 + r (Fin.succ t)) t0
  have hq_ne : q ≠ 0 := by
    -- A positive support coordinate prevents the tail part from vanishing.
    intro hq_zero
    have hq_pos : 0 < q (Fin.succ t0) := by
      simpa [hq_t0] using ht0
    have : (0 : ℝ) < 0 := by
      simpa [hq_zero] using hq_pos
    linarith
  refine ⟨exercise_3_29_ray (0 : Fin (n + 1)), q,
    exercise_3_29_ray_mem_recessionCone b 0, hq_mem,
    exercise_3_29_ray_ne_zero 0, hq_ne,
    exercise_3_29_ray_zero_not_sameRay_of_head_zero hq_ne hq0,
    r 0, 1, hhead, zero_lt_one, ?_⟩
  -- The canonical simplicial decomposition supplies the conic-combination equality.
  simpa [q] using exercise_3_29_recession_direction_eq_ray_combination (r := r)

/-- Helper for Exercise 3.29: if two different successor coefficients are positive while the head
coefficient vanishes, then the recession direction splits as a proper conic combination of two
distinct coordinate rays. -/
lemma exercise_3_29_proper_conic_combination_of_two_positive_tail_coefficients
    {n : ℕ} {b : Fin n → ℝ} {r : Fin (n + 1) → ℝ} {t1 t2 : Fin n}
    (hr : r ∈ recessionCone (exercise_3_29_polyhedron b))
    (h0 : r 0 = 0) (ht : t1 ≠ t2)
    (ht1_pos : 0 < r (Fin.succ t1)) (ht2_pos : 0 < r (Fin.succ t2)) :
    ProperConicCombinationOfDistinctConeRays
      (recessionCone (exercise_3_29_polyhedron b)) r := by
  let q : Fin (n + 1) → ℝ :=
    ∑ t : Fin n, (if t = t1 then 0 else r (Fin.succ t)) • exercise_3_29_ray (Fin.succ t)
  have hr_props := exercise_3_29_mem_recessionCone_iff.mp hr
  have hcoeff_nonneg : ∀ t : Fin n, 0 ≤ if t = t1 then 0 else r (Fin.succ t) := by
    intro t
    by_cases htt : t = t1
    · simp [htt]
    · simpa [htt, h0] using hr_props.2 t
  have hq_mem : q ∈ recessionCone (exercise_3_29_polyhedron b) := by
    -- Deleting one nonnegative coefficient keeps the conic combination inside the recession cone.
    simpa [q] using exercise_3_29_sum_succ_rays_mem_recessionCone b
      (fun t : Fin n ↦ if t = t1 then 0 else r (Fin.succ t)) hcoeff_nonneg
  have hq0 : q 0 = 0 := by
    -- Successor-ray combinations always have zero head coordinate.
    simpa [q] using exercise_3_29_sum_succ_rays_head_coordinate
      (coeff := fun t : Fin n ↦ if t = t1 then 0 else r (Fin.succ t))
  have hq_t1 : q (Fin.succ t1) = 0 := by
    -- The deleted support coordinate vanishes by construction.
    simpa [q] using exercise_3_29_sum_succ_rays_deleted_support_coordinate
      (coeff := fun t : Fin n ↦ r (Fin.succ t)) t1 t1
  have ht21 : t2 ≠ t1 := by
    simpa [eq_comm] using ht
  have hq_t2 : q (Fin.succ t2) = r (Fin.succ t2) := by
    -- Every off-support successor coordinate keeps its original coefficient.
    simpa [q, ht21] using exercise_3_29_sum_succ_rays_deleted_support_coordinate
      (coeff := fun t : Fin n ↦ r (Fin.succ t)) t1 t2
  have hq_ne : q ≠ 0 := by
    -- The second positive tail coordinate survives in the deleted-support sum.
    intro hq_zero
    have hq_pos : 0 < q (Fin.succ t2) := by
      simpa [hq_t2] using ht2_pos
    have : (0 : ℝ) < 0 := by
      simpa [hq_zero] using hq_pos
    linarith
  refine ⟨exercise_3_29_ray (Fin.succ t1), q,
    exercise_3_29_ray_mem_recessionCone b (Fin.succ t1), hq_mem,
    exercise_3_29_ray_ne_zero (Fin.succ t1), hq_ne,
    exercise_3_29_ray_succ_not_sameRay_of_support_gap ht hq_t1 (by simpa [hq_t2] using ht2_pos),
    r (Fin.succ t1), 1, ht1_pos, zero_lt_one, ?_⟩
  -- The deleted-support decomposition reconstructs `r` coordinatewise.
  change r = r (Fin.succ t1) • exercise_3_29_ray (Fin.succ t1) + 1 • q
  ext i
  refine Fin.cases ?_ ?_ i
  · have hsucc_ne_zero : ¬ (Fin.succ t1 : Fin (n + 1)) = 0 := by
      simp
    have hzero_ne_succ : ¬ (0 : Fin (n + 1)) = Fin.succ t1 := by
      simpa [eq_comm] using hsucc_ne_zero
    simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, h0, hq0, hsucc_ne_zero, hzero_ne_succ]
  · intro t
    by_cases htt : t = t1
    · subst t
      simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hq_t1]
    · have hq_t : q (Fin.succ t) = r (Fin.succ t) := by
          simpa [q, htt] using exercise_3_29_sum_succ_rays_deleted_support_coordinate
            (coeff := fun u : Fin n ↦ r (Fin.succ u)) t1 t
      have htt' : t1 ≠ t := by
        exact fun h => htt h.symm
      simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, hq_t, htt, htt']

/-- Helper for Exercise 3.29: extreme-rayhood is invariant under replacing a nonzero generator by
another nonzero vector on the same ray. -/
lemma isExtremeRayOfPolyhedron_of_sameRay
    {n : ℕ} {P : Set (Fin n → ℝ)} {u v : Fin n → ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : SameRay ℝ u v)
    (hv_extreme : IsExtremeRayOfPolyhedron P v) :
    IsExtremeRayOfPolyhedron P u := by
  rw [isExtremeRayOfPolyhedron_iff, isExtremeRayOfCone_iff] at hv_extreme ⊢
  -- It is enough to identify the singleton pointed-cone hulls of two nonzero same-ray generators.
  have hhull :
      (PointedCone.hull ℝ ({u} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        (PointedCone.hull ℝ ({v} : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      rcases exercise_3_29_mem_singleton_pointedCone_hull_iff.mp hx with ⟨a, ha, rfl⟩
      rcases huv.exists_nonneg_right hv with ⟨b, hb, hu_eq⟩
      exact exercise_3_29_mem_singleton_pointedCone_hull_iff.mpr
        ⟨a * b, mul_nonneg ha hb, by rw [hu_eq, smul_smul]⟩
    · intro hx
      rcases exercise_3_29_mem_singleton_pointedCone_hull_iff.mp hx with ⟨a, ha, rfl⟩
      rcases huv.symm.exists_nonneg_right hu with ⟨b, hb, hv_eq⟩
      exact exercise_3_29_mem_singleton_pointedCone_hull_iff.mpr
        ⟨a * b, mul_nonneg ha hb, by rw [hv_eq, smul_smul]⟩
  simpa [hhull] using hv_extreme

/-- Helper for Exercise 3.29: the only extreme point of the exercise polyhedron is the base point
`(0, b₁, …, bₙ)`. -/
lemma exercise_3_29_extreme_point_iff_eq_basepoint {n : ℕ} (b : Fin n → ℝ)
    {x : Fin (n + 1) → ℝ} :
    x ∈ (exercise_3_29_polyhedron b).extremePoints ℝ ↔ x = Fin.cases 0 b := by
  constructor
  · intro hx
    rcases (mem_extremePoints_iff_left.mp hx) with ⟨hxP, hx_extreme⟩
    have hx_mem := mem_exercise_3_29_polyhedron_iff.mp hxP
    have hx0 : x 0 = 0 := by
      -- If `x₀ > 0`, the symmetric perturbation along `r⁰` keeps feasibility and contradicts
      -- extremality.
      by_contra hx0_ne
      have hx0_pos : 0 < x 0 := lt_of_le_of_ne hx_mem.1 (by simpa [eq_comm] using hx0_ne)
      rcases exercise_3_29_perturb_zero_mem_polyhedron hxP (le_of_lt hx0_pos) le_rfl with
        ⟨hyP, hzP⟩
      have hy_eq :
          x + x 0 • exercise_3_29_ray (0 : Fin (n + 1)) = x :=
        hx_extreme _ hyP _ hzP
          (exercise_3_29_mem_openSegment_of_symmetric_perturbation x
            (x 0 • exercise_3_29_ray (0 : Fin (n + 1))))
      have hhead : (x + x 0 • exercise_3_29_ray (0 : Fin (n + 1))) 0 = x 0 := by
        simpa using congrArg (fun p => p 0) hy_eq
      rcases exercise_3_29_ray_zero_head_coordinate_effect x (x 0) with ⟨hplus, _⟩
      rw [hplus] at hhead
      linarith
    have hmix : ∀ t : Fin n, x 0 + x (Fin.succ t) = b t := by
      intro t
      -- If one mixed inequality is slack, the symmetric perturbation along the matching
      -- coordinate ray keeps feasibility and again contradicts extremality.
      by_contra hmix_ne
      have hineq_t : b t ≤ x 0 + x (Fin.succ t) := hx_mem.2 t
      have hslack_pos : 0 < x 0 + x (Fin.succ t) - b t := by
        have hlt : b t < x 0 + x (Fin.succ t) := by
          exact lt_of_le_of_ne hineq_t (by simpa [eq_comm] using hmix_ne)
        linarith
      rcases exercise_3_29_perturb_succ_mem_polyhedron t hxP (le_of_lt hslack_pos) le_rfl with
        ⟨hyP, hzP⟩
      have hy_eq :
          x + (x 0 + x (Fin.succ t) - b t) • exercise_3_29_ray (Fin.succ t) = x :=
        hx_extreme _ hyP _ hzP
          (exercise_3_29_mem_openSegment_of_symmetric_perturbation x
            ((x 0 + x (Fin.succ t) - b t) • exercise_3_29_ray (Fin.succ t)))
      have hsupp :
          (x + (x 0 + x (Fin.succ t) - b t) • exercise_3_29_ray (Fin.succ t)) 0 +
              (x + (x 0 + x (Fin.succ t) - b t) • exercise_3_29_ray (Fin.succ t))
                (Fin.succ t) =
            x 0 + x (Fin.succ t) := by
        simpa using congrArg (fun p => p 0 + p (Fin.succ t)) hy_eq
      rcases exercise_3_29_ray_succ_support_coordinate_effect x
        (x 0 + x (Fin.succ t) - b t) t with ⟨hplus, _⟩
      rw [hplus] at hsupp
      linarith
    ext i
    refine Fin.cases ?_ ?_ i
    · simpa using hx0
    · intro t
      have htail : x (Fin.succ t) = b t := by
        linarith [hmix t, hx0]
      simpa using htail
  · rintro rfl
    rw [mem_extremePoints_iff_left]
    constructor
    · exact exercise_3_29_basepoint_mem b
    · intro y hy z hz hseg
      rcases mem_exercise_3_29_polyhedron_iff.mp hy with ⟨hy0_nonneg, hyineq⟩
      rcases mem_exercise_3_29_polyhedron_iff.mp hz with ⟨hz0_nonneg, hzineq⟩
      rw [openSegment_eq_image_lineMap] at hseg
      rcases hseg with ⟨a, ha, hline⟩
      have h_one_sub_a : 0 < 1 - a := by
        exact sub_pos.mpr ha.2
      have hhead_zero : (1 - a) * y 0 + a * z 0 = 0 := by
        -- The base point has head coordinate `0`, so the head convex combination must vanish.
        have hcoord := congrArg (fun p => p 0) hline
        simpa [AffineMap.lineMap_apply_module] using hcoord
      have hhead_vanish := positive_weighted_sum_eq_zero_of_nonneg
        h_one_sub_a ha.1 hy0_nonneg hz0_nonneg hhead_zero
      have hy0 : y 0 = 0 := hhead_vanish.1
      have hytail : ∀ t : Fin n, y (Fin.succ t) = b t := by
        intro t
        have hy_slack_nonneg : 0 ≤ y 0 + y (Fin.succ t) - b t := by
          linarith [hyineq t]
        have hz_slack_nonneg : 0 ≤ z 0 + z (Fin.succ t) - b t := by
          linarith [hzineq t]
        have hmix_eq : (1 - a) * (y 0 + y (Fin.succ t)) +
            a * (z 0 + z (Fin.succ t)) = b t := by
          -- The base-point equality on coordinate `t` is the convex combination of the two mixed
          -- sums.
          have hcoord := congrArg (fun p => p 0 + p (Fin.succ t)) hline
          simpa [AffineMap.lineMap_apply_module, Fin.cases, add_assoc, add_left_comm, add_comm,
            left_distrib, right_distrib, sub_eq_add_neg] using hcoord
        have hslack_zero :
            (1 - a) * (y 0 + y (Fin.succ t) - b t) +
              a * (z 0 + z (Fin.succ t) - b t) = 0 := by
          linarith
        have hy_slack_zero := (positive_weighted_sum_eq_zero_of_nonneg
          h_one_sub_a ha.1 hy_slack_nonneg hz_slack_nonneg hslack_zero).1
        linarith
      ext i
      refine Fin.cases ?_ ?_ i
      · simpa using hy0
      · intro t
        simpa using hytail t

/-- Helper for Exercise 3.29: each distinguished generator spans an extreme ray of the exercise
polyhedron. -/
lemma exercise_3_29_ray_isExtremeRay {n : ℕ} (b : Fin n → ℝ) (s : Fin (n + 1)) :
    IsExtremeRayOfPolyhedron (exercise_3_29_polyhedron b) (exercise_3_29_ray s) := by
  rw [isExtremeRayOfPolyhedron_iff]
  have hcone := exercise_3_29_recessionCone_as_pointedCone b
  refine (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
    hcone (exercise_3_29_ray_mem_recessionCone b s) (exercise_3_29_ray_ne_zero s)).2 ?_
  intro hproper
  rcases hproper with
    ⟨u, v, hu_mem, hv_mem, hu_ne, hv_ne, huv_distinct,
      μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
  have hu_props := exercise_3_29_mem_recessionCone_iff.mp hu_mem
  have hv_props := exercise_3_29_mem_recessionCone_iff.mp hv_mem
  obtain rfl | ⟨t0, rfl⟩ := s.eq_zero_or_eq_succ
  · -- Route correction: use mixed-coordinate evaluation first, then invoke the same-ray normal
    -- form for the head-positive generator `r⁰`.
    have hu_same : SameRay ℝ u (exercise_3_29_ray (0 : Fin (n + 1))) := by
      apply exercise_3_29_sameRay_ray_zero_of_mixed_eq_zero hu_mem hu_ne
      intro t
      have hcoord := congrArg (fun p => p 0 + p (Fin.succ t)) hdecomp
      have hsum : μ₁ * (u 0 + u (Fin.succ t)) + μ₂ * (v 0 + v (Fin.succ t)) = 0 := by
        have hsum' : μ₁ * u 0 + μ₂ * v 0 + (μ₁ * u (Fin.succ t) + μ₂ * v (Fin.succ t)) = 0 := by
          simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray] using hcoord.symm
        linarith
      exact (positive_weighted_sum_eq_zero_of_nonneg hμ₁ hμ₂
        (hu_props.2 t) (hv_props.2 t) hsum).1
    have hv_same : SameRay ℝ v (exercise_3_29_ray (0 : Fin (n + 1))) := by
      apply exercise_3_29_sameRay_ray_zero_of_mixed_eq_zero hv_mem hv_ne
      intro t
      have hcoord := congrArg (fun p => p 0 + p (Fin.succ t)) hdecomp
      have hsum : μ₁ * (u 0 + u (Fin.succ t)) + μ₂ * (v 0 + v (Fin.succ t)) = 0 := by
        have hsum' : μ₁ * u 0 + μ₂ * v 0 + (μ₁ * u (Fin.succ t) + μ₂ * v (Fin.succ t)) = 0 := by
          simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray] using hcoord.symm
        linarith
      exact (positive_weighted_sum_eq_zero_of_nonneg hμ₁ hμ₂
        (hu_props.2 t) (hv_props.2 t) hsum).2
    have huv_same : SameRay ℝ u v :=
      SameRay.trans hu_same hv_same.symm
        (fun hzero_mid ↦ False.elim (exercise_3_29_ray_ne_zero (0 : Fin (n + 1)) hzero_mid))
    exact huv_distinct huv_same
  · -- Evaluate the head coordinate first, then kill every off-support successor coordinate.
    have huv_head := congrArg (fun p => p 0) hdecomp
    have hsum_head : μ₁ * u 0 + μ₂ * v 0 = 0 := by
      simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray] using huv_head.symm
    have hhead_zero := positive_weighted_sum_eq_zero_of_nonneg hμ₁ hμ₂
      hu_props.1 hv_props.1 hsum_head
    have hu0 : u 0 = 0 := hhead_zero.1
    have hv0 : v 0 = 0 := hhead_zero.2
    have hu_same : SameRay ℝ u (exercise_3_29_ray (Fin.succ t0)) := by
      apply exercise_3_29_sameRay_ray_succ_of_head_zero_unique_support hu_mem hu_ne hu0
      intro t ht
      have hcoord := congrArg (fun p => p (Fin.succ t)) hdecomp
      have ht' : t0 ≠ t := by
        exact fun h => ht h.symm
      have hsum : μ₁ * u (Fin.succ t) + μ₂ * v (Fin.succ t) = 0 := by
        simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, ht, ht'] using hcoord.symm
      have hu_tail_nonneg : 0 ≤ u (Fin.succ t) := by
        simpa [hu0] using hu_props.2 t
      have hv_tail_nonneg : 0 ≤ v (Fin.succ t) := by
        simpa [hv0] using hv_props.2 t
      exact (positive_weighted_sum_eq_zero_of_nonneg hμ₁ hμ₂
        hu_tail_nonneg hv_tail_nonneg hsum).1
    have hv_same : SameRay ℝ v (exercise_3_29_ray (Fin.succ t0)) := by
      apply exercise_3_29_sameRay_ray_succ_of_head_zero_unique_support hv_mem hv_ne hv0
      intro t ht
      have hcoord := congrArg (fun p => p (Fin.succ t)) hdecomp
      have ht' : t0 ≠ t := by
        exact fun h => ht h.symm
      have hsum : μ₁ * u (Fin.succ t) + μ₂ * v (Fin.succ t) = 0 := by
        simpa [Pi.add_apply, Pi.smul_apply, exercise_3_29_ray, ht, ht'] using hcoord.symm
      have hu_tail_nonneg : 0 ≤ u (Fin.succ t) := by
        simpa [hu0] using hu_props.2 t
      have hv_tail_nonneg : 0 ≤ v (Fin.succ t) := by
        simpa [hv0] using hv_props.2 t
      exact (positive_weighted_sum_eq_zero_of_nonneg hμ₁ hμ₂
        hu_tail_nonneg hv_tail_nonneg hsum).2
    have huv_same : SameRay ℝ u v :=
      SameRay.trans hu_same hv_same.symm
        (fun hzero_mid ↦ False.elim (exercise_3_29_ray_ne_zero (Fin.succ t0) hzero_mid))
    exact huv_distinct huv_same

/-- Helper for Exercise 3.29: every nonzero extreme ray of the exercise polyhedron is generated by
one of the distinguished vectors `r⁰, …, rⁿ`. -/
lemma exercise_3_29_sameRay_of_extreme_ray {n : ℕ} (b : Fin n → ℝ)
    {r : Fin (n + 1) → ℝ} (hr0 : r ≠ 0)
    (hr : IsExtremeRayOfPolyhedron (exercise_3_29_polyhedron b) r) :
    ∃ s : Fin (n + 1), SameRay ℝ r (exercise_3_29_ray s) := by
  classical
  rw [isExtremeRayOfPolyhedron_iff] at hr
  have hr_mem : r ∈ recessionCone (exercise_3_29_polyhedron b) :=
    exercise_3_29_extreme_ray_mem hr
  have hr_props := exercise_3_29_mem_recessionCone_iff.mp hr_mem
  have hnotproper :
      ¬ ProperConicCombinationOfDistinctConeRays
        (recessionCone (exercise_3_29_polyhedron b)) r :=
    -- Route correction: the Chapter 3 owner now first asks for the ambient convex-cone witness for
    -- the recession cone before the membership and nonzero premises.
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      (exercise_3_29_recessionCone_as_pointedCone b) hr_mem hr0).1 hr
  by_cases h0 : r 0 = 0
  · have htail_exists : ∃ t : Fin n, r (Fin.succ t) ≠ 0 := by
      by_contra htail_missing
      have hr_zero : r = 0 := by
        ext i
        refine Fin.cases h0 ?_ i
        intro t
        by_contra ht
        exact htail_missing ⟨t, ht⟩
      exact hr0 hr_zero
    rcases htail_exists with ⟨t1, ht1_ne⟩
    have ht1_nonneg : 0 ≤ r (Fin.succ t1) := by
      simpa [h0] using hr_props.2 t1
    have ht1_pos : 0 < r (Fin.succ t1) := by
      exact lt_of_le_of_ne ht1_nonneg (by simpa [eq_comm] using ht1_ne)
    have huniq : ∀ t : Fin n, t ≠ t1 → r (Fin.succ t) = 0 := by
      intro t ht
      by_contra ht_ne
      have ht_nonneg : 0 ≤ r (Fin.succ t) := by
        simpa [h0] using hr_props.2 t
      have ht_pos : 0 < r (Fin.succ t) := by
        exact lt_of_le_of_ne ht_nonneg (by simpa [eq_comm] using ht_ne)
      exact hnotproper <|
        exercise_3_29_proper_conic_combination_of_two_positive_tail_coefficients
          hr_mem h0 (by simpa [eq_comm] using ht) ht1_pos ht_pos
    exact ⟨Fin.succ t1, exercise_3_29_sameRay_ray_succ_of_head_zero_unique_support
      hr_mem hr0 h0 huniq⟩
  · have hr_head_pos : 0 < r 0 := by
      exact lt_of_le_of_ne hr_props.1 (by simpa [eq_comm] using h0)
    by_cases hmix : ∀ t : Fin n, r 0 + r (Fin.succ t) = 0
    · exact ⟨0, exercise_3_29_sameRay_ray_zero_of_mixed_eq_zero hr_mem hr0 hmix⟩
    · have hmix_exists : ∃ t : Fin n, r 0 + r (Fin.succ t) ≠ 0 := by
        exact not_forall.mp hmix
      rcases hmix_exists with ⟨t0, ht0_ne⟩
      have ht0_nonneg : 0 ≤ r 0 + r (Fin.succ t0) := hr_props.2 t0
      have ht0_pos : 0 < r 0 + r (Fin.succ t0) := lt_of_le_of_ne ht0_nonneg ht0_ne.symm
      exact False.elim <| hnotproper <|
        exercise_3_29_proper_conic_combination_of_positive_head_and_tail
          hr_mem hr_head_pos ht0_pos

/-- Exercise 3.29 (1). The polyhedron
`{(x₀, …, xₙ) ∈ ℝ^(n+1) | x₀ + x_t ≥ b_t for t = 1, …, n, x₀ ≥ 0}` has pointed recession cone. -/
theorem exercise_3_29_pointed {n : ℕ} (b : Fin n → ℝ) :
    is_pointed (recessionCone (exercise_3_29_polyhedron b)) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro d hd
  rw [mem_linealitySpace_iff] at hd
  -- A lineality direction of the recession cone yields both `d` and `-d` as recession directions
  -- of the original polyhedron.
  have hd_pos : d ∈ recessionCone (exercise_3_29_polyhedron b) := by
    simpa using hd (zero_mem_recessionCone :
      (0 : Fin (n + 1) → ℝ) ∈ recessionCone (exercise_3_29_polyhedron b)) 1
  have hd_neg : -d ∈ recessionCone (exercise_3_29_polyhedron b) := by
    simpa using hd (zero_mem_recessionCone :
      (0 : Fin (n + 1) → ℝ) ∈ recessionCone (exercise_3_29_polyhedron b)) (-1)
  rw [exercise_3_29_mem_recessionCone_iff] at hd_pos hd_neg
  ext i
  refine Fin.cases ?_ ?_ i
  · have h0_le : d 0 ≤ 0 := by
      simpa using hd_neg.1
    exact le_antisymm h0_le hd_pos.1
  · intro t
    have h0 : d 0 = 0 := by
      have h0_le : d 0 ≤ 0 := by
        simpa using hd_neg.1
      exact le_antisymm h0_le hd_pos.1
    have hpos : 0 ≤ d (Fin.succ t) := by
      simpa [h0] using hd_pos.2 t
    have hneg : 0 ≤ -d (Fin.succ t) := by
      simpa [h0] using hd_neg.2 t
    have hle : d (Fin.succ t) ≤ 0 := by
      linarith
    exact le_antisymm hle hpos

/-- Exercise 3.29 (2). The unique vertex of the polyhedron from Exercise 3.29 is
`(0, b₁, …, bₙ)`, represented as `Fin.cases 0 b`. -/
theorem exercise_3_29_extremePoints_eq_singleton {n : ℕ} (b : Fin n → ℝ) :
    (exercise_3_29_polyhedron b).extremePoints ℝ = {Fin.cases 0 b} := by
  -- The helper lemma already characterizes the unique extreme point coordinatewise.
  ext x
  simp [exercise_3_29_extreme_point_iff_eq_basepoint]

/-- Exercise 3.29 (3). A nonzero vector generates an extreme ray of the polyhedron from
Exercise 3.29 exactly when it lies on the same ray as one of the distinguished generators
`r⁰, …, rⁿ`. -/
theorem exercise_3_29_extreme_ray_iff {n : ℕ} (b : Fin n → ℝ) {r : Fin (n + 1) → ℝ}
    (hr : r ≠ 0) :
    IsExtremeRayOfPolyhedron (exercise_3_29_polyhedron b) r ↔
      ∃ s : Fin (n + 1), SameRay ℝ r (exercise_3_29_ray s) := by
  constructor
  · exact exercise_3_29_sameRay_of_extreme_ray b hr
  · rintro ⟨s, hsame⟩
    exact isExtremeRayOfPolyhedron_of_sameRay
      hr (exercise_3_29_ray_ne_zero s) hsame
      (exercise_3_29_ray_isExtremeRay b s)
