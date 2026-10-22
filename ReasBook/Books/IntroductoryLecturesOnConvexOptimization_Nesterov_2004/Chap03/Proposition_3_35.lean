/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators EuclideanOrthant

local notation "E" N => EuclideanSpace ℝ (Fin (N + 1))

/-
Primary domain: finite-dimensional Euclidean stepsize optimization on the strict orthant.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the chapter owner for the
  coordinatewise orthant domain in `EuclideanSpace ℝ (Fin m)`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`, the corresponding coordinatewise membership bridge
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the dimension-based strict orthant owner and membership bridge
- `orthantLogarithmicBarrierDomain` and `mem_orthantLogarithmicBarrierDomain_iff` in
  `Chap07/Definition_7_76`, a later strict-orthant owner with the same coordinatewise positivity
  surface

Best owner abstraction:
- `source-facing`: the scalar functional `deltaN` from Proposition 3.35 and its constant stepsize
  minimizer
- `core/canonical`: the strict orthant owner `EuclideanSpace.positiveOrthant`
- `bridge/view`: the coordinatewise membership and evaluation lemmas

Primitive data:
- the horizon `N`
- the radius `R`
- the stepsize vector `h : E N`

Derived API:
- coordinatewise positivity of the orthant domain
- the defining quotient formula for `deltaN`
- the constant-choice vector and its coordinate formula
- the minimization statement on the strict orthant
-/

/-- The function `Δ_N(h₀, …, h_N) = (R² + ∑ hᵢ²) / (2 ∑ hᵢ)` from Proposition 3.35. -/
def deltaN (N : ℕ) (R : ℝ) (h : E N) : ℝ :=
  (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
    (2 * ∑ i : Fin (N + 1), h i)

namespace DeltaN

/- Source-facing Lean notation for the textbook finite-horizon stepsize scalar `Δ_N(h₀, …, h_N)`,
with the ambient radius parameter displayed as `Δ[N; R] h`. -/
scoped notation:max "Δ[" N:arg "; " R:arg "]" => deltaN N R

end DeltaN

open scoped DeltaN

/-- Evaluating `deltaN` gives the defining quotient
`(R² + ∑ hᵢ²) / (2 ∑ hᵢ)`. -/
@[simp] theorem deltaN_apply (N : ℕ) (R : ℝ) (h : E N) :
    Δ[N; R] h =
      (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
        (2 * ∑ i : Fin (N + 1), h i) :=
  rfl

/-- The constant point with every coordinate equal to `R / √(N + 1)`. -/
def deltaNConstantChoice (N : ℕ) (R : ℝ) : E N :=
  (EuclideanSpace.equiv (Fin (N + 1)) ℝ).symm
    (Function.const _ (R / Real.sqrt (N + 1 : ℝ)))

/-- Every coordinate of `deltaNConstantChoice N R` is `R / √(N + 1)`. -/
@[simp] theorem deltaNConstantChoice_apply (N : ℕ) (R : ℝ) (i : Fin (N + 1)) :
    deltaNConstantChoice N R i = R / Real.sqrt (N + 1 : ℝ) := by
  simp [deltaNConstantChoice]

/-- Evaluating `deltaN` at the canonical constant choice gives `R / √(N + 1)`. -/
@[simp] theorem deltaN_constantChoice (N : ℕ) (R : ℝ) :
    Δ[N; R] (deltaNConstantChoice N R) = R / Real.sqrt (N + 1 : ℝ) := by
  have hs : Real.sqrt (N + 1 : ℝ) ≠ 0 := by
    positivity
  have hsq : Real.sqrt (N + 1 : ℝ) ^ (2 : ℕ) = N + 1 := by
    rw [Real.sq_sqrt]
    positivity
  simp [deltaN, Finset.sum_const, pow_two]
  field_simp [hs]
  rw [hsq]
  ring_nf

/-- The constant choice belongs to the positive orthant whenever `R > 0`. -/
-- Proof sketch: use `deltaNConstantChoice_apply` to identify each coordinate with
-- `R / √(N + 1)`, and note that `√(N + 1)` is positive.
theorem deltaNConstantChoice_mem_positiveOrthant (N : ℕ) {R : ℝ} (hR : 0 < R) :
    deltaNConstantChoice N R ∈ ℝ₊₊^(N + 1) := by
  rw [EuclideanSpace.mem_positiveOrthant_iff]
  intro i
  simpa only [deltaNConstantChoice_apply] using
    div_pos hR <| Real.sqrt_pos.2 <| by positivity

/-- Helper for Proposition 3.35: a vector in the positive orthant has strictly positive coordinate
sum. -/
-- Proof sketch: every coordinate is positive, so the whole finite sum dominates the `0`th
-- coordinate and is therefore positive.
private theorem positiveOrthant_sum_pos {N : ℕ} {h : E N}
    (hh : h ∈ ℝ₊₊^(N + 1)) :
    0 < ∑ i : Fin (N + 1), h i := by
  rw [EuclideanSpace.mem_positiveOrthant_iff] at hh
  -- A positive summand gives a positive lower bound for the full sum.
  have hle : h 0 ≤ ∑ i : Fin (N + 1), h i := by
    exact Finset.single_le_sum (fun i _ ↦ le_of_lt (hh i)) (Finset.mem_univ 0)
  exact lt_of_lt_of_le (hh 0) hle

/-- Helper for Proposition 3.35: Cauchy--Schwarz lower-bounds the sum of squares by the square of
the sum divided by the dimension. -/
-- Proof sketch: apply `sq_sum_le_card_mul_sum_sq` on `Finset.univ` and divide by the positive
-- scalar `(N + 1 : ℝ)`.
private theorem sum_sq_lower_bound_by_sq_sum (N : ℕ) (h : E N) :
    ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ) ≤
      ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hcs :
      (∑ i : Fin (N + 1), h i) ^ (2 : ℕ) ≤
        (N + 1 : ℝ) * ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
    simpa using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin (N + 1) ↦ h i))
  exact (div_le_iff₀ hdim).2 <| by
    simpa [mul_comm] using hcs

/-- Helper for Proposition 3.35: the Cauchy--Schwarz estimate yields the scalar relaxation that
depends only on `S = ∑ i, h i`. -/
-- Proof sketch: rewrite `Δ[N; R] h` by definition, replace `∑ hᵢ²` by the lower bound
-- `S² / (N + 1)`, and compare the two quotients over the positive denominator `2 * S`.
private theorem deltaN_lower_bound_by_scalar_relaxation (N : ℕ) {R : ℝ} {h : E N}
    (hh : h ∈ ℝ₊₊^(N + 1)) :
    R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
      (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) ≤
        Δ[N; R] h := by
  have hsum_pos : 0 < ∑ i : Fin (N + 1), h i := positiveOrthant_sum_pos hh
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hnumer :
      R ^ (2 : ℕ) + ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ) ≤
        R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ) := by
    exact add_le_add le_rfl (sum_sq_lower_bound_by_sq_sum N h)
  have hrewrite :
      R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
        (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) =
          (R ^ (2 : ℕ) + ((∑ i : Fin (N + 1), h i) ^ (2 : ℕ)) / (N + 1 : ℝ)) /
            (2 * ∑ i : Fin (N + 1), h i) := by
    field_simp [hsum_pos.ne', hdim.ne']
  -- After rewriting both terms over the same denominator, only numerator monotonicity remains.
  rw [hrewrite, deltaN_apply]
  exact (div_le_div_iff_of_pos_right
    (show 0 < 2 * ∑ i : Fin (N + 1), h i by positivity)).2 hnumer

/-- Helper for Proposition 3.35: the scalar relaxation is minimized at
`S = R * √(N + 1)`, with minimum value `R / √(N + 1)`. -/
-- Proof sketch: rewrite the right-hand side as a single quotient and clear the positive
-- denominator `2 * S`; the remaining estimate is the AM-GM / square-completion inequality
-- `2ab ≤ a² + b²` with `a = R` and `b = S / √(N + 1)`.
private theorem stepsize_scalar_lower_bound (N : ℕ) {R S : ℝ} (hS : 0 < S) :
    R / Real.sqrt (N + 1 : ℝ) ≤ R ^ (2 : ℕ) / (2 * S) + S / (2 * (N + 1 : ℝ)) := by
  have hdim : 0 < (N + 1 : ℝ) := by
    positivity
  have hsqrt : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.2 hdim
  have hsqrt_sq : Real.sqrt (N + 1 : ℝ) ^ (2 : ℕ) = N + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hrewrite :
      R ^ (2 : ℕ) / (2 * S) + S / (2 * (N + 1 : ℝ)) =
        (R ^ (2 : ℕ) + S ^ (2 : ℕ) / (N + 1 : ℝ)) / (2 * S) := by
    field_simp [hS.ne', hdim.ne']
  rw [hrewrite]
  apply (le_div_iff₀ (show 0 < 2 * S by positivity)).2
  have hamgm :
      2 * R * (S / Real.sqrt (N + 1 : ℝ)) ≤
        R ^ (2 : ℕ) + (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (two_mul_le_add_sq R (S / Real.sqrt (N + 1 : ℝ)))
  have hmul :
      (R / Real.sqrt (N + 1 : ℝ)) * (2 * S) =
        2 * R * (S / Real.sqrt (N + 1 : ℝ)) := by
    field_simp [hsqrt.ne']
  have hsquare :
      (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) = S ^ (2 : ℕ) / (N + 1 : ℝ) := by
    rw [div_pow, hsqrt_sq]
  -- This is the scalar one-variable minimum after clearing denominators.
  calc
    (R / Real.sqrt (N + 1 : ℝ)) * (2 * S)
      = 2 * R * (S / Real.sqrt (N + 1 : ℝ)) := hmul
    _ ≤ R ^ (2 : ℕ) + (S / Real.sqrt (N + 1 : ℝ)) ^ (2 : ℕ) := hamgm
    _ = R ^ (2 : ℕ) + S ^ (2 : ℕ) / (N + 1 : ℝ) := by rw [hsquare]

/-- Proposition 3.35: for `R > 0`, the function `Δ_N` attains its minimum on the
positive orthant at the constant choice `h_i = R / √(N + 1)`. The closed-form value is recorded
separately by `deltaN_constantChoice`. -/
-- Proof sketch: write `S = ∑ i, h i` and `Q = ∑ i, h i^2`; Cauchy--Schwarz gives
-- `Q ≥ S^2 / (N + 1)`, so `Δ[N; R] h` is bounded below by
-- `R^2 / (2 S) + S / (2 (N + 1))`. Minimize this one-variable expression at
-- `S = R * √(N + 1)`, and check that equality holds exactly for the constant choice.
theorem deltaN_constantChoice_minimizes_positiveOrthant
    (N : ℕ) {R : ℝ} (hR : 0 < R) :
    IsMinOn (Δ[N; R]) (ℝ₊₊^(N + 1)) (deltaNConstantChoice N R) := by
  -- The positivity assumption records that the constant candidate actually lies in the domain.
  have : deltaNConstantChoice N R ∈ ℝ₊₊^(N + 1) :=
    deltaNConstantChoice_mem_positiveOrthant N hR
  rw [isMinOn_iff]
  intro h hh
  have hsum_pos : 0 < ∑ i : Fin (N + 1), h i := positiveOrthant_sum_pos hh
  -- Compare `Δ[N; R] h` with the scalar relaxation and then with the constant-choice value.
  calc
    Δ[N; R] (deltaNConstantChoice N R)
      = R / Real.sqrt (N + 1 : ℝ) := deltaN_constantChoice N R
    _ ≤ R ^ (2 : ℕ) / (2 * ∑ i : Fin (N + 1), h i) +
        (∑ i : Fin (N + 1), h i) / (2 * (N + 1 : ℝ)) :=
      stepsize_scalar_lower_bound N hsum_pos
    _ ≤ Δ[N; R] h := deltaN_lower_bound_by_scalar_relaxation N hh
