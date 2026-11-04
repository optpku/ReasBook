/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib.Analysis.Convex.Body
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_theorem_7_26

open scoped BigOperators Matrix

section Theorem727

variable {n : ℕ}

/-- A circumscribed convex set `(K; n, R)` consists of a convex body in `ℝ^n` together with the
chosen rational outer-radius bound `R` appearing in the source model. -/
structure CircumscribedConvexSet (n : ℕ) where
  body : ConvexBody (Fin n → ℝ)
  radius : ℚ
  body_subset_closedBall {x : Fin n → ℝ} (hx : x ∈ body) :
    x ∈ Metric.closedBall (0 : Fin n → ℝ) (radius : ℝ)

instance : Coe (CircumscribedConvexSet n) (ConvexBody (Fin n → ℝ)) where
  coe K := K.body

instance : Membership (Fin n → ℝ) (CircumscribedConvexSet n) where
  mem K x := x ∈ K.body

namespace CircumscribedConvexSet

@[simp] theorem mem_body_iff {K : CircumscribedConvexSet n} {x : Fin n → ℝ} :
    x ∈ K ↔ x ∈ K.body := by
  rfl

/-- The encoding size of a circumscribed convex set records only the explicit dimension and chosen
outer radius from `(K; n, R)`. -/
def encodingSize (K : CircumscribedConvexSet n) : ℕ :=
  n + EncodingSize.rational K.radius

/-- The enclosing closed-ball condition already forces the chosen outer radius to be nonnegative. -/
theorem radius_nonneg (K : CircumscribedConvexSet n) : 0 ≤ K.radius := by
  obtain ⟨x, hx⟩ := K.body.nonempty
  have hr : (0 : ℝ) ≤ (K.radius : ℝ) := by
    exact le_trans dist_nonneg (show dist x 0 ≤ (K.radius : ℝ) from K.body_subset_closedBall hx)
  exact_mod_cast hr

/-- Every point of a circumscribed convex set lies in the chosen enclosing closed ball. -/
theorem mem_closedBall_of_mem
    {K : CircumscribedConvexSet n}
    {x : Fin n → ℝ}
    (hx : x ∈ K) :
    x ∈ Metric.closedBall (0 : Fin n → ℝ) (K.radius : ℝ) :=
  K.body_subset_closedBall hx

end CircumscribedConvexSet

/-- A weak optimization query consists of a rational objective vector and a positive rational
tolerance. -/
structure WeakOptimizationQuery (n : ℕ) where
  objective : Fin n → ℚ
  epsilon : ℚ
  epsilon_pos : 0 < epsilon

namespace WeakOptimizationQuery

/-- The encoding size of a weak optimization query is the size of the rational objective vector
and the tolerance. -/
def encodingSize (query : WeakOptimizationQuery n) : ℕ :=
  EncodingSize.rationalVector query.objective +
    EncodingSize.rational query.epsilon

end WeakOptimizationQuery

/-- The encoding size of a weak optimization instance is the size of `(K; n, R)` together with the
optimization query. -/
def CircumscribedConvexSet.weakOptimizationEncodingSize
    (K : CircumscribedConvexSet n)
    (query : WeakOptimizationQuery n) : ℕ :=
  K.encodingSize + query.encodingSize

/-- A weak optimization solution is a rational point in `S(K, ε)` whose objective value is within
`ε` of the optimum over the convex body `K`. -/
structure WeakOptimizationSolution
    (K : ConvexBody (Fin n → ℝ)) (c : Fin n → ℚ) (ε : ℚ) where
  point : Fin n → ℚ
  point_mem :
    (fun i ↦ (point i : ℝ)) ∈ Metric.cthickening (ε : ℝ) K
  near_optimal {x : Fin n → ℝ} (hx : x ∈ K) :
    (fun i ↦ (c i : ℝ)) ⬝ᵥ x ≤
      (fun i ↦ (c i : ℝ)) ⬝ᵥ (fun i ↦ (point i : ℝ)) + (ε : ℝ)

/-- An oracle-polynomial-time weak optimization solver for `K` returns a weak optimization
solution for each query, together with a polynomial runtime bound in the full input encoding
size. -/
abbrev WeakOptimizationSolver (K : CircumscribedConvexSet n) :=
  PolynomialTimeQuerySolver
    (WeakOptimizationQuery n)
    (fun query ↦ WeakOptimizationSolution K query.objective query.epsilon)
    K.weakOptimizationEncodingSize

/-- A weak separation query consists of a rational query point and a positive rational tolerance.
-/
structure WeakSeparationQuery (n : ℕ) where
  point : Fin n → ℚ
  delta : ℚ
  delta_pos : 0 < delta

namespace WeakSeparationQuery

/-- The encoding size of a weak separation query is the size of the rational query point and the
tolerance. -/
def encodingSize (query : WeakSeparationQuery n) : ℕ :=
  EncodingSize.rationalVector query.point +
    EncodingSize.rational query.delta

end WeakSeparationQuery

/-- The encoding size of a weak separation instance is the size of `(K; n, R)` together with the
separation query. -/
def CircumscribedConvexSet.weakSeparationEncodingSize
    (K : CircumscribedConvexSet n)
    (query : WeakSeparationQuery n) : ℕ :=
  K.encodingSize + query.encodingSize

/-- A separating certificate for the weak separation problem is a rational linear inequality with
an explicit coordinatewise `L∞`-style normalization on the rational normal vector that separates
the convex body `K` from the query point up to the tolerance `δ`. The source only asks for a
rational separator `c`; the coordinatewise bound and saturation below are the formal scale-fixing
used here to block the vacuous rescaling ambiguity without imposing an unjustified Euclidean-unit
normalization. -/
structure WeakSeparationCertificate
    (K : ConvexBody (Fin n → ℝ)) (y : Fin n → ℚ) (δ : ℚ) where
  normal : Fin n → ℚ
  normal_abs_le_one (i : Fin n) : |normal i| ≤ 1
  normal_abs_eq_one : ∃ i : Fin n, |normal i| = 1
  separates {x : Fin n → ℝ} (hx : x ∈ K) :
    (fun i ↦ (normal i : ℝ)) ⬝ᵥ x ≤
      (fun i ↦ (normal i : ℝ)) ⬝ᵥ (fun i ↦ (y i : ℝ)) + (δ : ℝ)

namespace WeakSeparationCertificate

theorem normal_ne_zero
    {K : ConvexBody (Fin n → ℝ)} {y : Fin n → ℚ} {δ : ℚ}
    (certificate : WeakSeparationCertificate K y δ) :
    certificate.normal ≠ 0 := by
  intro hzero
  rcases certificate.normal_abs_eq_one with ⟨i, hi⟩
  have hfalse : (0 : ℚ) = 1 := by
    simpa [hzero] using hi
  norm_num at hfalse

end WeakSeparationCertificate

/-- A weak separation answer either certifies that the rational query point lies in `S(K, δ)` or
returns a rational separating certificate. -/
inductive WeakSeparationAnswer
    (K : ConvexBody (Fin n → ℝ)) (y : Fin n → ℚ) (δ : ℚ) where
  | near :
      (fun i ↦ (y i : ℝ)) ∈ Metric.cthickening (δ : ℝ) K →
        WeakSeparationAnswer K y δ
  | separated :
      WeakSeparationCertificate K y δ →
        WeakSeparationAnswer K y δ

/-- An oracle-polynomial-time weak separation solver for `K` answers each separation query,
together with a polynomial runtime bound in the full input encoding size. -/
abbrev WeakSeparationSolver (K : CircumscribedConvexSet n) :=
  PolynomialTimeQuerySolver
    (WeakSeparationQuery n)
    (fun query ↦ WeakSeparationAnswer K query.point query.delta)
    K.weakSeparationEncodingSize

end Theorem727
