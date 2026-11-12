/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_theorem_4_42

open scoped BigOperators Matrix Pointwise

-- Domain-style sampling for this refine pass:
-- * source-facing owners kept here: `split_polyhedron_left`, `split_polyhedron_right`,
--   `split_lifted_polyhedron`, `split_x_projection`
-- * core/canonical owners reused here: `is_polyhedron`, `polyhedron_le_set`
-- * nearby Chapter 4.9 owner pattern inspected: `balas_lifted_polyhedron`, `balas_x_projection`
-- This file keeps the split-specific source-facing objects, but no longer shadows the Chapter 3
-- polyhedron owner.

section Lemma445

variable {m n : ℕ}

/-- The left split polyhedron `P₁ = {x | A x ≤ b, c x ≤ d₁}`. -/
def split_polyhedron_left
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 : ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩ {x : Fin n → ℝ | c ⬝ᵥ x ≤ d1}

/-- Membership in `split_polyhedron_left A b c d1` is the conjunction
`A x ≤ b` and `c x ≤ d₁`. -/
theorem mem_split_polyhedron_left_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 : ℝ)
    (x : Fin n → ℝ) :
    x ∈ split_polyhedron_left A b c d1 ↔ A *ᵥ x ≤ b ∧ c ⬝ᵥ x ≤ d1 := by
  rfl

/-- The right split polyhedron `P₂ = {x | A x ≤ b, c x ≥ d₂}`. -/
def split_polyhedron_right
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d2 : ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩ {x : Fin n → ℝ | d2 ≤ c ⬝ᵥ x}

/-- Membership in `split_polyhedron_right A b c d2` is the conjunction
`A x ≤ b` and `c x ≥ d₂`. -/
theorem mem_split_polyhedron_right_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d2 : ℝ)
    (x : Fin n → ℝ) :
    x ∈ split_polyhedron_right A b c d2 ↔ A *ᵥ x ≤ b ∧ d2 ≤ c ⬝ᵥ x := by
  rfl

/-- The lifted polyhedron `Q` from Lemma 4.45, with variables `(x, x¹, x², λ)`. -/
def split_lifted_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) : Set ((Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) × ℝ) :=
  {(x, x1, x2, lam) |
    A *ᵥ x1 ≤ lam • b ∧
      c ⬝ᵥ x1 ≤ lam * d1 ∧
      A *ᵥ x2 ≤ (1 - lam) • b ∧
      (1 - lam) * d2 ≤ c ⬝ᵥ x2 ∧
      x1 + x2 = x ∧
      0 ≤ lam ∧
      lam ≤ 1}

/-- Membership in `split_lifted_polyhedron A b c d1 d2` is exactly the system
`A x¹ ≤ λ b`, `c x¹ ≤ λ d₁`, `A x² ≤ (1 - λ) b`, `c x² ≥ (1 - λ) d₂`,
`x¹ + x² = x`, and `0 ≤ λ ≤ 1`. -/
theorem mem_split_lifted_polyhedron_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    (x x1 x2 : Fin n → ℝ)
    (lam : ℝ) :
    (x, x1, x2, lam) ∈ split_lifted_polyhedron A b c d1 d2 ↔
      A *ᵥ x1 ≤ lam • b ∧
        c ⬝ᵥ x1 ≤ lam * d1 ∧
        A *ᵥ x2 ≤ (1 - lam) • b ∧
        (1 - lam) * d2 ≤ c ⬝ᵥ x2 ∧
        x1 + x2 = x ∧
        0 ≤ lam ∧
        lam ≤ 1 := by
  rfl

/-- The projection of `split_lifted_polyhedron A b c d1 d2` onto the `x`-variables. -/
def split_x_projection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) : Set (Fin n → ℝ) :=
  Prod.fst '' split_lifted_polyhedron A b c d1 d2

/-- Membership in `split_x_projection A b c d1 d2` means that `x` has compatible auxiliary
variables `x¹`, `x²`, and `λ` satisfying the lifted split system. -/
theorem mem_split_x_projection_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    (x : Fin n → ℝ) :
    x ∈ split_x_projection A b c d1 d2 ↔
      ∃ x1 x2 : Fin n → ℝ, ∃ lam : ℝ,
        A *ᵥ x1 ≤ lam • b ∧
          c ⬝ᵥ x1 ≤ lam * d1 ∧
          A *ᵥ x2 ≤ (1 - lam) • b ∧
          (1 - lam) * d2 ≤ c ⬝ᵥ x2 ∧
          x1 + x2 = x ∧
          0 ≤ lam ∧
          lam ≤ 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2.1, y.2.2.1, y.2.2.2,
      (mem_split_lifted_polyhedron_iff A b c d1 d2 y.1 y.2.1 y.2.2.1 y.2.2.2).1 hy⟩
  · rintro ⟨x1, x2, lam, hLifted⟩
    exact ⟨(x, x1, x2, lam),
      (mem_split_lifted_polyhedron_iff A b c d1 d2 x x1 x2 lam).2 hLifted, rfl⟩

/-- Helper for Lemma 4.45: convex combinations of lifted split witnesses remain feasible in the
split projection. -/
lemma convexSplitXProjection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) :
    Convex ℝ (split_x_projection A b c d1 d2) := by
  intro x hx y hy a s ha hs has
  rw [mem_split_x_projection_iff] at hx hy ⊢
  rcases hx with ⟨x1, x2, lam, hAx1, hcx1, hAx2, hcx2, hsumx, hlam_nonneg, hlam_le⟩
  rcases hy with ⟨y1, y2, mu, hAy1, hcy1, hAy2, hcy2, hsumy, hmu_nonneg, hmu_le⟩
  refine ⟨a • x1 + s • y1, a • x2 + s • y2, a * lam + s * mu, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    -- Each block row inequality is preserved under the same convex combination of witnesses.
    have hxrow : (A *ᵥ x1) i ≤ lam * b i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hAx1 i
    have hyrow : (A *ᵥ y1) i ≤ mu * b i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hAy1 i
    have hax : a * (A *ᵥ x1) i ≤ a * (lam * b i) := mul_le_mul_of_nonneg_left hxrow ha
    have hsy : s * (A *ᵥ y1) i ≤ s * (mu * b i) := mul_le_mul_of_nonneg_left hyrow hs
    have hsum := add_le_add hax hsy
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
      left_distrib, right_distrib, mul_add, add_mul, mul_assoc] using hsum
  · -- The split inequality with `c` is likewise stable under convex combinations.
    have hxrow : c ⬝ᵥ x1 ≤ lam * d1 := hcx1
    have hyrow : c ⬝ᵥ y1 ≤ mu * d1 := hcy1
    have hax : a * (c ⬝ᵥ x1) ≤ a * (lam * d1) := mul_le_mul_of_nonneg_left hxrow ha
    have hsy : s * (c ⬝ᵥ y1) ≤ s * (mu * d1) := mul_le_mul_of_nonneg_left hyrow hs
    have hsum := add_le_add hax hsy
    simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, left_distrib, right_distrib,
      mul_add, add_mul, mul_assoc] using hsum
  · intro i
    have hxrow : (A *ᵥ x2) i ≤ (1 - lam) * b i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hAx2 i
    have hyrow : (A *ᵥ y2) i ≤ (1 - mu) * b i := by
      simpa [Pi.smul_apply, smul_eq_mul] using hAy2 i
    have hax : a * (A *ᵥ x2) i ≤ a * ((1 - lam) * b i) := mul_le_mul_of_nonneg_left hxrow ha
    have hsy : s * (A *ᵥ y2) i ≤ s * ((1 - mu) * b i) := mul_le_mul_of_nonneg_left hyrow hs
    have hsum := add_le_add hax hsy
    have hcoeff :
        (a * ((1 - lam) * b i) + s * ((1 - mu) * b i)) =
          (1 - (a * lam + s * mu)) * b i := by
      calc
        a * ((1 - lam) * b i) + s * ((1 - mu) * b i)
            = (a * (1 - lam) + s * (1 - mu)) * b i := by ring
        _ = (a + s - (a * lam + s * mu)) * b i := by ring
        _ = (1 - (a * lam + s * mu)) * b i := by rw [has]
    calc
      (A *ᵥ (a • x2 + s • y2)) i
          = a * (A *ᵥ x2) i + s * (A *ᵥ y2) i := by
              simp [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      _ ≤ a * ((1 - lam) * b i) + s * ((1 - mu) * b i) := hsum
      _ = (1 - (a * lam + s * mu)) * b i := hcoeff
  · -- The lower split inequality is preserved after rewriting the new left side.
    have hxrow : (1 - lam) * d2 ≤ c ⬝ᵥ x2 := hcx2
    have hyrow : (1 - mu) * d2 ≤ c ⬝ᵥ y2 := hcy2
    have hax : a * ((1 - lam) * d2) ≤ a * (c ⬝ᵥ x2) := mul_le_mul_of_nonneg_left hxrow ha
    have hsy : s * ((1 - mu) * d2) ≤ s * (c ⬝ᵥ y2) := mul_le_mul_of_nonneg_left hyrow hs
    have hsum := add_le_add hax hsy
    have hcoeff :
        a * ((1 - lam) * d2) + s * ((1 - mu) * d2) =
          (1 - (a * lam + s * mu)) * d2 := by
      calc
        a * ((1 - lam) * d2) + s * ((1 - mu) * d2)
            = (a * (1 - lam) + s * (1 - mu)) * d2 := by ring
        _ = (a + s - (a * lam + s * mu)) * d2 := by ring
        _ = (1 - (a * lam + s * mu)) * d2 := by rw [has]
    calc
      (1 - (a * lam + s * mu)) * d2 = a * ((1 - lam) * d2) + s * ((1 - mu) * d2) := hcoeff.symm
      _ ≤ a * (c ⬝ᵥ x2) + s * (c ⬝ᵥ y2) := hsum
      _ = c ⬝ᵥ (a • x2 + s • y2) := by
            simp [dotProduct_add, dotProduct_smul, smul_eq_mul]
  · -- The visible point equation is preserved componentwise.
    calc
      a • x1 + s • y1 + (a • x2 + s • y2)
          = a • (x1 + x2) + s • (y1 + y2) := by
              ext i
              simp [Pi.smul_apply]
              ring
      _ = a • x + s • y := by rw [hsumx, hsumy]
  · exact add_nonneg (mul_nonneg ha hlam_nonneg) (mul_nonneg hs hmu_nonneg)
  · have hlam_scaled : a * lam ≤ a := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hlam_le ha
    have hmu_scaled : s * mu ≤ s := by
      simpa [mul_one] using mul_le_mul_of_nonneg_left hmu_le hs
    linarith

/-- Helper for Lemma 4.45: if `0 < λ < 1`, rescaling the lifted split witness produces one point
of `P₁`, one point of `P₂`, and the original convex decomposition of `x`. -/
lemma scaledWitnessMemSplitSidesOfInnerLambda
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    {x x1 x2 : Fin n → ℝ}
    {lam : ℝ}
    (hLifted : (x, x1, x2, lam) ∈ split_lifted_polyhedron A b c d1 d2)
    (hlam : 0 < lam)
    (hlam_lt : lam < 1) :
    lam⁻¹ • x1 ∈ split_polyhedron_left A b c d1 ∧
      (1 - lam)⁻¹ • x2 ∈ split_polyhedron_right A b c d2 ∧
      x = lam • (lam⁻¹ • x1) + (1 - lam) • ((1 - lam)⁻¹ • x2) := by
  rcases (mem_split_lifted_polyhedron_iff A b c d1 d2 x x1 x2 lam).1 hLifted with
    ⟨hAx1, hcx1, hAx2, hcx2, hsum, -, -⟩
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hone : 0 < 1 - lam := by linarith
  have hone_ne : 1 - lam ≠ 0 := ne_of_gt hone
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_split_polyhedron_left_iff]
    refine ⟨?_, ?_⟩
    · change A *ᵥ (lam⁻¹ • x1) ≤ b
      intro i
      have hrow : (A *ᵥ x1) i ≤ lam * b i := by
        simpa [Pi.smul_apply, smul_eq_mul] using hAx1 i
      have hdiv : (A *ᵥ x1) i / lam ≤ b i := by
        exact (div_le_iff₀ hlam).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hrow)
      simpa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hdiv
    · have hdiv : (c ⬝ᵥ x1) / lam ≤ d1 := by
        exact (div_le_iff₀ hlam).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcx1)
      simpa [dotProduct_smul, smul_eq_mul, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hdiv
  · rw [mem_split_polyhedron_right_iff]
    refine ⟨?_, ?_⟩
    · change A *ᵥ ((1 - lam)⁻¹ • x2) ≤ b
      intro i
      have hrow : (A *ᵥ x2) i ≤ (1 - lam) * b i := by
        simpa [Pi.smul_apply, smul_eq_mul] using hAx2 i
      have hdiv : (A *ᵥ x2) i / (1 - lam) ≤ b i := by
        exact (div_le_iff₀ hone).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hrow)
      simpa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hdiv
    · have hdiv : d2 ≤ (c ⬝ᵥ x2) / (1 - lam) := by
        refine (le_div_iff₀ hone).2 ?_
        simpa [mul_assoc, mul_left_comm, mul_comm] using hcx2
      simpa [dotProduct_smul, smul_eq_mul, div_eq_mul_inv,
        mul_assoc, mul_left_comm, mul_comm] using hdiv
  · -- Normalize the two scaled parts back to the original visible point.
    calc
      x = x1 + x2 := by simpa using hsum.symm
      _ = lam • (lam⁻¹ • x1) + (1 - lam) • ((1 - lam)⁻¹ • x2) := by
            rw [smul_smul, smul_smul, mul_inv_cancel₀ hlam_ne, mul_inv_cancel₀ hone_ne,
              one_smul, one_smul]

/-- Helper for Lemma 4.45: for any `t > 0`, the point `x + r` lies on the segment joining
`x` and `x + t • r` with coefficient `t⁻¹`. -/
lemma addPoint_eq_invSmul_farPoint
    {x r : Fin n → ℝ}
    {t : ℝ}
    (ht : 0 < t) :
    t⁻¹ • (x + t • r) + (1 - t⁻¹) • x = x + r := by
  have hsum : t⁻¹ + (1 - t⁻¹) = 1 := by ring
  calc
    t⁻¹ • (x + t • r) + (1 - t⁻¹) • x
        = (t⁻¹ • x + t⁻¹ • (t • r)) + (1 - t⁻¹) • x := by
            rw [smul_add]
    _ = (t⁻¹ • x + r) + (1 - t⁻¹) • x := by
          rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    _ = (t⁻¹ • x + (1 - t⁻¹) • x) + r := by
          abel
    _ = (t⁻¹ + (1 - t⁻¹)) • x + r := by
          rw [← add_smul]
    _ = x + r := by
          rw [hsum, one_smul]

/-- Helper for Lemma 4.45: starting from a point of `P₂`, adding a homogeneous left-direction
still lands in `conv (P₁ ∪ P₂)`. -/
lemma rightPointAddLeftDirectionMemConvexHullSplitUnion
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    {xbar r : Fin n → ℝ}
    (hxbar : xbar ∈ split_polyhedron_right A b c d2)
    (hrA : A *ᵥ r ≤ 0)
    (hrc : c ⬝ᵥ r ≤ 0) :
    xbar + r ∈ convexHull ℝ (split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2) := by
  let U := split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2
  rw [mem_split_polyhedron_right_iff] at hxbar
  by_cases hzero : c ⬝ᵥ r = 0
  · -- If the split value stays fixed, the translated point remains in `P₂`.
    have hxright : xbar + r ∈ split_polyhedron_right A b c d2 := by
      rw [mem_split_polyhedron_right_iff]
      refine ⟨?_, ?_⟩
      · intro i
        simpa [Matrix.mulVec_add] using add_le_add (hxbar.1 i) (hrA i)
      · simpa [dotProduct_add, hzero] using hxbar.2
    exact subset_convexHull ℝ U (Or.inr hxright)
  · -- Route correction: when `c ⬝ᵥ r < 0`, move far enough along the ray to reach `P₁`
    -- and place `xbar + r` on the segment joining that point to `xbar`.
    have hneg : c ⬝ᵥ r < 0 := lt_of_le_of_ne hrc hzero
    let t : ℝ := max 1 ((c ⬝ᵥ xbar - d1) / (-(c ⬝ᵥ r)))
    have ht_ge_one : 1 ≤ t := le_max_left _ _
    have ht_nonneg : 0 ≤ t := le_trans (by norm_num) ht_ge_one
    have hden : 0 < -(c ⬝ᵥ r) := by linarith
    have ht_bound : (c ⬝ᵥ xbar - d1) / (-(c ⬝ᵥ r)) ≤ t := le_max_right _ _
    have hxleft : xbar + t • r ∈ split_polyhedron_left A b c d1 := by
      rw [mem_split_polyhedron_left_iff]
      refine ⟨?_, ?_⟩
      · intro i
        have hrscaled : (A *ᵥ (t • r)) i ≤ 0 := by
          have : t * (A *ᵥ r) i ≤ t * 0 := mul_le_mul_of_nonneg_left (hrA i) ht_nonneg
          simpa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm] using this
        simpa [Matrix.mulVec_add] using add_le_add (hxbar.1 i) hrscaled
      · have hbound' : c ⬝ᵥ xbar - d1 ≤ t * (-(c ⬝ᵥ r)) := by
          exact (div_le_iff₀ hden).1 ht_bound
        have hdot : c ⬝ᵥ (xbar + t • r) ≤ d1 := by
          have : c ⬝ᵥ xbar + t * (c ⬝ᵥ r) ≤ d1 := by
            linarith
          simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm] using this
        exact hdot
    have hxbarHull : xbar ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inr hxbar)
    have hxleftHull : xbar + t • r ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inl hxleft)
    have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) ht_ge_one
    have hcoeff₁ : 0 ≤ t⁻¹ := inv_nonneg.mpr ht_nonneg
    have hcoeff₂ : 0 ≤ 1 - t⁻¹ := by
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ ht_ge_one)
    have hcoeff_sum : t⁻¹ + (1 - t⁻¹) = 1 := by ring
    have hcomb : t⁻¹ • (xbar + t • r) + (1 - t⁻¹) • xbar = xbar + r :=
      addPoint_eq_invSmul_farPoint ht_pos
    have hconv : Convex ℝ (convexHull ℝ U) := convex_convexHull ℝ U
    have hmem :
        t⁻¹ • (xbar + t • r) + (1 - t⁻¹) • xbar ∈ convexHull ℝ U := by
      exact (convex_iff_add_mem.mp hconv) hxleftHull hxbarHull hcoeff₁ hcoeff₂ hcoeff_sum
    exact hcomb ▸ hmem

/-- Helper for Lemma 4.45: starting from a point of `P₁`, adding a homogeneous right-direction
still lands in `conv (P₁ ∪ P₂)`. -/
lemma leftPointAddRightDirectionMemConvexHullSplitUnion
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    {xbar r : Fin n → ℝ}
    (hxbar : xbar ∈ split_polyhedron_left A b c d1)
    (hrA : A *ᵥ r ≤ 0)
    (hrc : 0 ≤ c ⬝ᵥ r) :
    xbar + r ∈ convexHull ℝ (split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2) := by
  let U := split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2
  rw [mem_split_polyhedron_left_iff] at hxbar
  by_cases hzero : c ⬝ᵥ r = 0
  · -- If the split value stays fixed, the translated point remains in `P₁`.
    have hxleft : xbar + r ∈ split_polyhedron_left A b c d1 := by
      rw [mem_split_polyhedron_left_iff]
      refine ⟨?_, ?_⟩
      · intro i
        simpa [Matrix.mulVec_add] using add_le_add (hxbar.1 i) (hrA i)
      · simpa [dotProduct_add, hzero] using hxbar.2
    exact subset_convexHull ℝ U (Or.inl hxleft)
  · -- Route correction: when `c ⬝ᵥ r > 0`, move far enough along the ray to reach `P₂`
    -- and place `xbar + r` on the segment joining that point to `xbar`.
    have hpos : 0 < c ⬝ᵥ r := lt_of_le_of_ne hrc (Ne.symm hzero)
    let t : ℝ := max 1 ((d2 - c ⬝ᵥ xbar) / (c ⬝ᵥ r))
    have ht_ge_one : 1 ≤ t := le_max_left _ _
    have ht_nonneg : 0 ≤ t := le_trans (by norm_num) ht_ge_one
    have ht_bound : (d2 - c ⬝ᵥ xbar) / (c ⬝ᵥ r) ≤ t := le_max_right _ _
    have hxright : xbar + t • r ∈ split_polyhedron_right A b c d2 := by
      rw [mem_split_polyhedron_right_iff]
      refine ⟨?_, ?_⟩
      · intro i
        have hrscaled : (A *ᵥ (t • r)) i ≤ 0 := by
          have : t * (A *ᵥ r) i ≤ t * 0 := mul_le_mul_of_nonneg_left (hrA i) ht_nonneg
          simpa [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm] using this
        simpa [Matrix.mulVec_add] using add_le_add (hxbar.1 i) hrscaled
      · have hbound' : d2 - c ⬝ᵥ xbar ≤ t * (c ⬝ᵥ r) := by
          exact (div_le_iff₀ hpos).1 ht_bound
        have hdot : d2 ≤ c ⬝ᵥ (xbar + t • r) := by
          have : d2 ≤ c ⬝ᵥ xbar + t * (c ⬝ᵥ r) := by
            linarith
          simpa [dotProduct_add, dotProduct_smul, smul_eq_mul, mul_assoc, mul_left_comm,
            mul_comm] using this
        exact hdot
    have hxbarHull : xbar ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inl hxbar)
    have hxrightHull : xbar + t • r ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inr hxright)
    have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num) ht_ge_one
    have hcoeff₁ : 0 ≤ t⁻¹ := inv_nonneg.mpr ht_nonneg
    have hcoeff₂ : 0 ≤ 1 - t⁻¹ := by
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ ht_ge_one)
    have hcoeff_sum : t⁻¹ + (1 - t⁻¹) = 1 := by ring
    have hcomb : t⁻¹ • (xbar + t • r) + (1 - t⁻¹) • xbar = xbar + r :=
      addPoint_eq_invSmul_farPoint ht_pos
    have hconv : Convex ℝ (convexHull ℝ U) := convex_convexHull ℝ U
    have hmem :
        t⁻¹ • (xbar + t • r) + (1 - t⁻¹) • xbar ∈ convexHull ℝ U := by
      exact (convex_iff_add_mem.mp hconv) hxrightHull hxbarHull hcoeff₁ hcoeff₂ hcoeff_sum
    exact hcomb ▸ hmem

/-- Lemma 4.45 (1). Let `P₁ = {x | A x ≤ b, c x ≤ d₁}` and `P₂ = {x | A x ≤ b, d₂ ≤ c x}`.
Then `conv (P₁ ∪ P₂)` is the projection onto the space of `x` variables of the polyhedron
`split_lifted_polyhedron A b c d1 d2`. -/
theorem convexHull_split_polyhedra_eq_split_x_projection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) :
    convexHull ℝ (split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2) =
      split_x_projection A b c d1 d2 := by
  let U := split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2
  apply Set.Subset.antisymm
  · -- First include each split polyhedron into the projection by an explicit lifted witness.
    refine convexHull_min ?_ (convexSplitXProjection A b c d1 d2)
    intro x hx
    rcases hx with hx | hx
    · rw [mem_split_x_projection_iff]
      rw [mem_split_polyhedron_left_iff] at hx
      refine ⟨x, 0, 1, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, by simp, by norm_num, by norm_num⟩
      · simpa using hx.1
      · simpa using hx.2
      · simp
      · simp
    · rw [mem_split_x_projection_iff]
      rw [mem_split_polyhedron_right_iff] at hx
      refine ⟨0, x, 0, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, by simp, by norm_num, by norm_num⟩
      · simp
      · simp
      · simpa using hx.1
      · simpa using hx.2
  · -- Analyze the split multiplier `λ` to recover either a genuine convex combination or an
    -- endpoint segment argument.
    intro x hx
    rw [mem_split_x_projection_iff] at hx
    rcases hx with ⟨x1, x2, lam, hAx1, hcx1, hAx2, hcx2, hsum, hlam_nonneg, hlam_le⟩
    have hLifted : (x, x1, x2, lam) ∈ split_lifted_polyhedron A b c d1 d2 := by
      exact (mem_split_lifted_polyhedron_iff A b c d1 d2 x x1 x2 lam).2
        ⟨hAx1, hcx1, hAx2, hcx2, hsum, hlam_nonneg, hlam_le⟩
    by_cases hlam_zero : lam = 0
    · have hx2right : x2 ∈ split_polyhedron_right A b c d2 := by
        rw [mem_split_polyhedron_right_iff]
        refine ⟨?_, ?_⟩
        · simpa [hlam_zero] using hAx2
        · simpa [hlam_zero] using hcx2
      have hxsum' : x2 + x1 = x := by simpa [add_comm] using hsum
      have hmem :=
        rightPointAddLeftDirectionMemConvexHullSplitUnion A b c d1 d2 hx2right
          (by simpa [hlam_zero] using hAx1)
          (by simpa [hlam_zero] using hcx1)
      simpa [hxsum'] using hmem
    · by_cases hlam_one : lam = 1
      · have hx1left : x1 ∈ split_polyhedron_left A b c d1 := by
          rw [mem_split_polyhedron_left_iff]
          refine ⟨?_, ?_⟩
          · simpa [hlam_one] using hAx1
          · simpa [hlam_one] using hcx1
        have hxsum' : x1 + x2 = x := hsum
        have hmem :=
          leftPointAddRightDirectionMemConvexHullSplitUnion A b c d1 d2 hx1left
            (by simpa [hlam_one] using hAx2)
            (by simpa [hlam_one] using hcx2)
        simpa [hxsum'] using hmem
      · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam_nonneg (Ne.symm hlam_zero)
        have hlam_lt : lam < 1 := lt_of_le_of_ne hlam_le hlam_one
        rcases scaledWitnessMemSplitSidesOfInnerLambda A b c d1 d2 hLifted hlam_pos hlam_lt with
          ⟨hx1left, hx2right, hdecomp⟩
        have hx1Hull : lam⁻¹ • x1 ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inl hx1left)
        have hx2Hull : (1 - lam)⁻¹ • x2 ∈ convexHull ℝ U := subset_convexHull ℝ U (Or.inr hx2right)
        have hone_nonneg : 0 ≤ 1 - lam := sub_nonneg.mpr hlam_le
        have hconv : Convex ℝ (convexHull ℝ U) := convex_convexHull ℝ U
        have hmem :
            lam • (lam⁻¹ • x1) + (1 - lam) • ((1 - lam)⁻¹ • x2) ∈ convexHull ℝ U := by
          exact (convex_iff_add_mem.mp hconv) hx1Hull hx2Hull hlam_nonneg hone_nonneg (by ring)
        simpa [hdecomp] using hmem

/-- Helper for Lemma 4.45: the left split polyhedron is the matrix polyhedron obtained by adding
the row `c` with right-hand side `d₁`. -/
private def splitLeftMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Matrix (Fin (m + 1)) (Fin n) ℝ :=
  Fin.snoc A c

/-- Helper for Lemma 4.45: the right-hand side for the left split matrix system. -/
private def splitLeftRhs
    (b : Fin m → ℝ)
    (d1 : ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc b d1

/-- Helper for Lemma 4.45: the right split polyhedron is the matrix polyhedron obtained by adding
the row `-c` with right-hand side `-d₂`. -/
private def splitRightMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Matrix (Fin (m + 1)) (Fin n) ℝ :=
  Fin.snoc A (-c)

/-- Helper for Lemma 4.45: the right-hand side for the right split matrix system. -/
private def splitRightRhs
    (b : Fin m → ℝ)
    (d2 : ℝ) : Fin (m + 1) → ℝ :=
  Fin.snoc b (-d2)

/-- Helper for Lemma 4.45: the left split polyhedron is exactly one matrix-inequality system. -/
private theorem split_polyhedron_left_eq_polyhedron_le_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 : ℝ) :
    split_polyhedron_left A b c d1 =
      polyhedron_le_set (splitLeftMatrix A c) (splitLeftRhs b d1) := by
  ext x
  constructor
  · intro hx
    rw [mem_split_polyhedron_left_iff] at hx
    intro i
    cases i using Fin.lastCases with
    | last =>
        simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx.2
    | cast i =>
        simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx.1 i
  · intro hx
    rw [mem_split_polyhedron_left_iff]
    refine ⟨?_, ?_⟩
    · intro i
      simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx (Fin.castSucc i)
    · simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx (Fin.last m)

/-- Helper for Lemma 4.45: the right split polyhedron is exactly one matrix-inequality system. -/
private theorem split_polyhedron_right_eq_polyhedron_le_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d2 : ℝ) :
    split_polyhedron_right A b c d2 =
      polyhedron_le_set (splitRightMatrix A c) (splitRightRhs b d2) := by
  ext x
  constructor
  · intro hx
    rw [mem_split_polyhedron_right_iff] at hx
    intro i
    cases i using Fin.lastCases with
    | last =>
        have hlast : (-c) ⬝ᵥ x ≤ -d2 := by
          simpa [dotProduct_neg] using neg_le_neg hx.2
        simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hlast
    | cast i =>
        simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx.1 i
  · intro hx
    rw [mem_split_polyhedron_right_iff]
    refine ⟨?_, ?_⟩
    · intro i
      simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
        Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx (Fin.castSucc i)
    · have hlast : (-c) ⬝ᵥ x ≤ -d2 := by
        simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc] using hx (Fin.last m)
      have hxright : d2 ≤ c ⬝ᵥ x := by
        simpa [dotProduct_neg] using neg_le_neg hlast
      exact hxright

/-- Helper for Lemma 4.45: both split sides fit the two-block Balas template with a common row
count `m + 1`. -/
private def splitBalasRowCount
    (_ : Fin 2) : ℕ :=
  m + 1

/-- Helper for Lemma 4.45: the two Balas input matrices for the split system. -/
private def splitBalasMatrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    ∀ i : Fin 2, Matrix (Fin (splitBalasRowCount (m := m) i)) (Fin n) ℝ :=
  fun i ↦ Fin.cases (splitLeftMatrix A c) (fun _ ↦ splitRightMatrix A c) i

/-- Helper for Lemma 4.45: the two Balas input right-hand sides for the split system. -/
private def splitBalasRhs
    (b : Fin m → ℝ)
    (d1 d2 : ℝ) :
    ∀ i : Fin 2, Fin (splitBalasRowCount (m := m) i) → ℝ :=
  fun i ↦ Fin.cases (splitLeftRhs b d1) (fun _ ↦ splitRightRhs b d2) i

/-- Helper for Lemma 4.45: the split projection is exactly the Balas `x`-projection for the
two matrix polyhedra `P₁` and `P₂`. -/
private theorem splitBalasXProjection_eq_splitXProjection
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) :
    balas_x_projection (splitBalasRowCount (m := m))
        (splitBalasMatrix A c) (splitBalasRhs b d1 d2) =
      split_x_projection A b c d1 d2 := by
  ext x
  constructor
  · intro hx
    rw [mem_balas_x_projection_iff] at hx
    rw [mem_split_x_projection_iff]
    rcases hx with ⟨xParts, δ, hLifted⟩
    rcases (mem_balas_lifted_polyhedron_iff
      (splitBalasRowCount (m := m)) (splitBalasMatrix A c) (splitBalasRhs b d1 d2) x xParts δ).1
        hLifted with ⟨hineq, hsumX, hsumδ, hδnonneg⟩
    have hδsum : δ 0 + δ 1 = 1 := by
      simpa [Fin.sum_univ_two] using hsumδ
    have hδ1 : δ 1 = 1 - δ 0 := by
      linarith
    have hsumParts : xParts 0 + xParts 1 = x := by
      simpa [Fin.sum_univ_two] using hsumX
    have hlam_le : δ 0 ≤ 1 := by
      linarith [hδnonneg 1, hδsum]
    have hAx1 : A *ᵥ xParts 0 ≤ δ 0 • b := by
      intro i
      have hcast :
          (splitLeftMatrix A c *ᵥ xParts 0) (Fin.castSucc i) ≤
            (δ 0 • splitLeftRhs b d1) (Fin.castSucc i) := by
        simpa [splitBalasMatrix, splitBalasRhs] using (hineq 0) (Fin.castSucc i)
      simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul] using hcast
    have hcx1 : c ⬝ᵥ xParts 0 ≤ δ 0 * d1 := by
      have hlast :
          (splitLeftMatrix A c *ᵥ xParts 0) (Fin.last m) ≤
            (δ 0 • splitLeftRhs b d1) (Fin.last m) := by
        simpa [splitBalasMatrix, splitBalasRhs] using (hineq 0) (Fin.last m)
      simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_last, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul] using hlast
    have hAx2δ : A *ᵥ xParts 1 ≤ δ 1 • b := by
      intro i
      have hcast :
          (splitRightMatrix A c *ᵥ xParts 1) (Fin.castSucc i) ≤
            (δ 1 • splitRightRhs b d2) (Fin.castSucc i) := by
        simpa [splitBalasMatrix, splitBalasRhs] using (hineq 1) (Fin.castSucc i)
      simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul] using hcast
    have hcx2δ : δ 1 * d2 ≤ c ⬝ᵥ xParts 1 := by
      have hlast :
          (splitRightMatrix A c *ᵥ xParts 1) (Fin.last m) ≤
            (δ 1 • splitRightRhs b d2) (Fin.last m) := by
        simpa [splitBalasMatrix, splitBalasRhs] using (hineq 1) (Fin.last m)
      have hneg :
          -(c ⬝ᵥ xParts 1) ≤ δ 1 * (-d2) := by
        simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
          Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
          dotProduct_neg] using hlast
      linarith
    -- Route correction: specialize the generic Balas witness to `k = 2` with `λ = δ 0`.
    refine ⟨xParts 0, xParts 1, δ 0, hAx1, hcx1, ?_, ?_, hsumParts, hδnonneg 0, hlam_le⟩
    · simpa [hδ1] using hAx2δ
    · simpa [hδ1] using hcx2δ
  · intro hx
    rw [mem_split_x_projection_iff] at hx
    rw [mem_balas_x_projection_iff]
    rcases hx with ⟨x1, x2, lam, hAx1, hcx1, hAx2, hcx2, hsum, hlam_nonneg, hlam_le⟩
    refine ⟨![x1, x2], ![lam, 1 - lam], ?_⟩
    rw [mem_balas_lifted_polyhedron_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i
      · intro j
        cases j using Fin.lastCases with
        | last =>
            change (splitLeftMatrix A c *ᵥ x1) (Fin.last m) ≤
              (lam • splitLeftRhs b d1) (Fin.last m)
            simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
              Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Pi.smul_apply,
              smul_eq_mul] using hcx1
        | cast j =>
            change (splitLeftMatrix A c *ᵥ x1) (Fin.castSucc j) ≤
              (lam • splitLeftRhs b d1) (Fin.castSucc j)
            simpa [splitLeftMatrix, splitLeftRhs, Matrix.mulVec, dotProduct,
              Fin.sum_univ_castSucc, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul] using hAx1 j
      · intro j
        cases j using Fin.lastCases with
        | last =>
            change (splitRightMatrix A c *ᵥ x2) (Fin.last m) ≤
              ((1 - lam) • splitRightRhs b d2) (Fin.last m)
            simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
              Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Pi.smul_apply,
              smul_eq_mul, dotProduct_neg] using (neg_le_neg hcx2)
        | cast j =>
            change (splitRightMatrix A c *ᵥ x2) (Fin.castSucc j) ≤
              ((1 - lam) • splitRightRhs b d2) (Fin.castSucc j)
            simpa [splitRightMatrix, splitRightRhs, Matrix.mulVec, dotProduct,
              Fin.sum_univ_castSucc, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul] using hAx2 j
    · simp [Fin.sum_univ_two, hsum]
    · simp [Fin.sum_univ_two]
    · intro i
      fin_cases i <;> simp [hlam_nonneg, hlam_le]

/-- Helper for Lemma 4.45: each homogeneous split Balas block has a finite ray family. -/
private lemma existsSplitBalasRayFamily
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    ∃ R : Fin 2 → Finset (Fin n → ℝ),
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  classical
  have hgen :
      ∀ i : Fin 2,
        ∃ q : ℕ, ∃ M : Matrix (Fin n) (Fin q) ℝ,
          polyhedron_le_set (splitBalasMatrix A c i) 0 = (matrix_cone M : Set (Fin n → ℝ)) := by
    intro i
    have hPolyhedral :
        is_polyhedral_cone (polyhedron_le_set (splitBalasMatrix A c i) 0) := by
      refine (is_polyhedral_cone_iff).2 ?_
      exact ⟨splitBalasRowCount (m := m) i, splitBalasMatrix A c i, rfl⟩
    exact Theorem442Local.exists_matrixCone_eq_of_isPolyhedralCone hPolyhedral
  choose q M hM using hgen
  let R : Fin 2 → Finset (Fin n → ℝ) :=
    fun i ↦ Finset.univ.image (fun j : Fin (q i) ↦ fun l : Fin n ↦ M i l j)
  refine ⟨R, ?_⟩
  intro i
  -- Convert the matrix-cone presentation into a pointed-cone hull of a finite set of columns.
  calc
    polyhedron_le_set (splitBalasMatrix A c i) 0 = (matrix_cone (M i) : Set (Fin n → ℝ)) := hM i
    _ = finitely_generated_cone (fun j : Fin (q i) ↦ fun l : Fin n ↦ M i l j) := by
          symm
          exact finitely_generated_cone_eq_matrix_cone (fun j : Fin (q i) ↦ fun l : Fin n ↦ M i l j)
    _ = (PointedCone.hull ℝ
          (Set.range (fun j : Fin (q i) ↦ fun l : Fin n ↦ M i l j)) : Set (Fin n → ℝ)) := by
          rw [finitely_generated_cone_eq_pointedConeHull_range]
    _ = (PointedCone.hull ℝ
          ((Finset.univ.image (fun j : Fin (q i) ↦ fun l : Fin n ↦ M i l j)) :
            Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
          rw [range_eq_image_univ]
    _ = (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
          rfl

/-- Helper for Lemma 4.45: each nonempty split Balas block admits a finite vertex family
compatible with the chosen finite ray family, and empty branches use `∅`. -/
private lemma existsSplitBalasVertexFamily
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    (R : Fin 2 → Finset (Fin n → ℝ))
    (hR :
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) :
    ∃ V : Fin 2 → Finset (Fin n → ℝ),
      (∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) ≠ ∅ →
          polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) =
            convexHull ℝ (V i : Set (Fin n → ℝ)) +
              (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ))) ∧
      (∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) = ∅ →
          V i = ∅) := by
  classical
  let V : Fin 2 → Finset (Fin n → ℝ) := fun i ↦
    if hPi : polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) ≠ ∅ then
      Classical.choose
        (matrixPolyhedron_eq_convexHull_add_givenRayHull_of_nonempty
          (splitBalasRowCount (m := m)) (splitBalasMatrix A c) (splitBalasRhs b d1 d2) R hR
          (Set.nonempty_iff_ne_empty.mpr hPi))
    else ∅
  refine ⟨V, ?_, ?_⟩
  · intro i hPi
    -- On a nonempty branch, unfold the chosen witness exactly once.
    simpa [V, hPi] using
      Classical.choose_spec
        (matrixPolyhedron_eq_convexHull_add_givenRayHull_of_nonempty
          (splitBalasRowCount (m := m)) (splitBalasMatrix A c) (splitBalasRhs b d1 d2) R hR
          (Set.nonempty_iff_ne_empty.mpr hPi))
  · intro i hEmpty
    -- Empty branches contribute no vertices to the Balas nonempty family.
    simp [V, hEmpty]

/-- Helper for Lemma 4.45: finite split Balas vertex families agree with their explicit finite
owners, and the Balas ray family is just the finite biunion of the chosen local rays. -/
private lemma balasFamilies_eq_biUnionOwners
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    (R V : Fin 2 → Finset (Fin n → ℝ))
    (hVempty :
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) = ∅ →
          V i = ∅) :
    balas_nonempty_family (splitBalasRowCount (m := m)) (splitBalasMatrix A c)
        (splitBalasRhs b d1 d2) V =
      (Finset.univ.biUnion V : Set (Fin n → ℝ)) ∧
    balas_ray_family R = (Finset.univ.biUnion R : Set (Fin n → ℝ)) := by
  constructor
  · -- Route correction: normalize the guarded Balas vertex owner to the explicit finite biunion.
    ext x
    constructor
    · intro hx
      rcases (mem_balas_nonempty_family_iff (splitBalasRowCount (m := m))
        (splitBalasMatrix A c) (splitBalasRhs b d1 d2) V x).1 hx with ⟨i, -, hxi⟩
      exact Finset.mem_biUnion.2 ⟨i, by simp, hxi⟩
    · intro hx
      rcases Finset.mem_biUnion.1 hx with ⟨i, -, hxi⟩
      have hnonempty :
          polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) ≠ ∅ := by
        intro hEmpty
        have hVi_empty : V i = ∅ := hVempty i hEmpty
        simp [hVi_empty] at hxi
      exact (mem_balas_nonempty_family_iff (splitBalasRowCount (m := m))
        (splitBalasMatrix A c) (splitBalasRhs b d1 d2) V x).2 ⟨i, hnonempty, hxi⟩
  · -- The global Balas ray owner is already an unguarded finite biunion.
    ext x
    constructor
    · rintro ⟨i, hxi⟩
      exact Finset.mem_biUnion.2 ⟨i, by simp, hxi⟩
    · intro hx
      rcases Finset.mem_biUnion.1 hx with ⟨i, -, hxi⟩
      exact ⟨i, hxi⟩

/-- Helper for Lemma 4.45: the split projection is polyhedral via the finite Balas normal form. -/
private theorem splitXProjection_eq_vertexHull_add_commonCone
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ)
    (R V : Fin 2 → Finset (Fin n → ℝ))
    (hR :
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) 0 =
          (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hV :
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) ≠ ∅ →
          polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) =
            convexHull ℝ (V i : Set (Fin n → ℝ)) +
              (PointedCone.hull ℝ (R i : Set (Fin n → ℝ)) : Set (Fin n → ℝ)))
    (hVempty :
      ∀ i : Fin 2,
        polyhedron_le_set (splitBalasMatrix A c i) (splitBalasRhs b d1 d2 i) = ∅ →
          V i = ∅) :
    let S : Finset (Fin n → ℝ) := Finset.univ.biUnion V
    let T : Finset (Fin n → ℝ) := Finset.univ.biUnion R
    split_x_projection A b c d1 d2 =
      convexHull ℝ (S : Set (Fin n → ℝ)) +
        (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
  classical
  rcases balasFamilies_eq_biUnionOwners A b c d1 d2 R V hVempty with ⟨hVeq, hReq⟩
  let S : Finset (Fin n → ℝ) := Finset.univ.biUnion V
  let T : Finset (Fin n → ℝ) := Finset.univ.biUnion R
  -- Normalize the split projection to one explicit finite hull-plus-cone presentation.
  calc
    split_x_projection A b c d1 d2 =
        balas_x_projection (splitBalasRowCount (m := m)) (splitBalasMatrix A c)
          (splitBalasRhs b d1 d2) := by
            symm
            exact splitBalasXProjection_eq_splitXProjection A b c d1 d2
    _ =
        balas_union_polyhedron (splitBalasRowCount (m := m)) (splitBalasMatrix A c)
          (splitBalasRhs b d1 d2) V R := by
            symm
            exact balas_union_polyhedron_eq_x_projection (splitBalasRowCount (m := m))
              (splitBalasMatrix A c) (splitBalasRhs b d1 d2) V R hR hV
    _ =
        convexHull ℝ (balas_nonempty_family (splitBalasRowCount (m := m))
          (splitBalasMatrix A c) (splitBalasRhs b d1 d2) V) +
          (PointedCone.hull ℝ (balas_ray_family R) : Set (Fin n → ℝ)) := by
            rfl
    _ = convexHull ℝ (S : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
            simp [S, T, hVeq, hReq]

/-- Helper for Lemma 4.45: the pointed-cone hull of a finite set is a finitely generated cone. -/
private theorem pointedConeHull_finset_eq_finitelyGeneratedCone
    {n : ℕ}
    (T : Finset (Fin n → ℝ)) :
    ∃ q : ℕ, ∃ rays : Fin q → Fin n → ℝ,
      (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) =
        finitely_generated_cone rays := by
  let e : Fin T.card ≃ ↥T := (Finset.equivFin T).symm
  let rays : Fin T.card → Fin n → ℝ := fun i ↦ (e i).1
  have hrays_range : Set.range rays = (T : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp [rays]⟩
  refine ⟨T.card, rays, ?_⟩
  calc
    (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ))
        = (PointedCone.hull ℝ (Set.range rays) : Set (Fin n → ℝ)) := by
            rw [hrays_range]
    _ = finitely_generated_cone rays := by
          symm
          exact finitely_generated_cone_eq_pointedConeHull_range rays

/-- Helper for Lemma 4.45: the split projection is polyhedral via the finite Balas normal form. -/
private theorem splitXProjection_isPolyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) :
    is_polyhedron (split_x_projection A b c d1 d2) := by
  classical
  rcases existsSplitBalasRayFamily A c with ⟨R, hR⟩
  rcases existsSplitBalasVertexFamily A b c d1 d2 R hR with ⟨V, hV, hVempty⟩
  let S : Finset (Fin n → ℝ) := Finset.univ.biUnion V
  let T : Finset (Fin n → ℝ) := Finset.univ.biUnion R
  have htarget :
      split_x_projection A b c d1 d2 =
        convexHull ℝ (S : Set (Fin n → ℝ)) +
          (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := by
    -- Keep the split projection in the native finite-owner spelling from Balas.
    simpa [S, T] using
      splitXProjection_eq_vertexHull_add_commonCone A b c d1 d2 R V hR hV hVempty
  have hS_polytope : (convexHull ℝ (S : Set (Fin n → ℝ))).IsPolytope ℝ := by
    exact ⟨(S : Set (Fin n → ℝ)), S.finite_toSet, rfl⟩
  rcases pointedConeHull_finset_eq_finitelyGeneratedCone T with ⟨q, rays, hT_eq⟩
  -- The Balas normal form is already a polytope plus a finitely generated cone.
  refine (is_polyhedron_iff_eq_polytope_add_finitely_generated_cone).2 ?_
  refine ⟨convexHull ℝ (S : Set (Fin n → ℝ)), hS_polytope, q, rays, ?_⟩
  calc
    split_x_projection A b c d1 d2
        = convexHull ℝ (S : Set (Fin n → ℝ)) +
            (PointedCone.hull ℝ (T : Set (Fin n → ℝ)) : Set (Fin n → ℝ)) := htarget
    _ = convexHull ℝ (S : Set (Fin n → ℝ)) + finitely_generated_cone rays := by rw [hT_eq]

/-- Lemma 4.45 (2). Let `P₁ = {x | A x ≤ b, c x ≤ d₁}` and `P₂ = {x | A x ≤ b, d₂ ≤ c x}`.
Then `conv (P₁ ∪ P₂)` is a polyhedron. -/
theorem convexHull_split_polyhedra_is_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (d1 d2 : ℝ) :
    is_polyhedron
      (convexHull ℝ (split_polyhedron_left A b c d1 ∪ split_polyhedron_right A b c d2)) := by
  -- Route correction: close polyhedrality on the Balas side, then rewrite back through part (1).
  simpa [convexHull_split_polyhedra_eq_split_x_projection A b c d1 d2] using
    splitXProjection_isPolyhedron A b c d1 d2

end Lemma445
