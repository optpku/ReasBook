/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped BigOperators ENNReal

noncomputable section

namespace ProbabilityTheory

/- Domain-style sampling for Exercise 19.5.1:
- `source-facing`: the star-triangle transformation for a three-legged star with branch
  conductances `c`.
- `core/canonical`: finite conductance families together with the quadratic Dirichlet energy used
  in Chapter 19.
- `bridge/view`: the star and triangle boundary energies below are source-facing views obtained by
  evaluating that energy on the corresponding conductance families. -/

/-- Helper for Exercise 19.5.1: the finite Dirichlet energy of a conductance network. -/
private def finiteDirichletEnergy {E : Type*} [Fintype E] (C : E → E → ℝ≥0∞) (u : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : E, ∑ y : E, (C x y).toReal * (u x - u y) ^ (2 : ℕ)

/-- The total conductance of the three star edges. -/
def starTriangleTotalConductance (c : Fin 3 → NNReal) : NNReal :=
  ∑ i : Fin 3, c i

/-- The conductance-weighted center value used in the star-triangle transformation. When
`0 < starTriangleTotalConductance c`, this is the unique harmonic potential at the center; when
the total conductance vanishes, the defining weighted sum is `0`, so this value is `0`. -/
def starTriangleCenterPotential (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) : ℝ :=
  (∑ i : Fin 3, (c i : ℝ) * v i) / starTriangleTotalConductance c

/-- The conductance family on the boundary triangle equivalent to the star with branch
conductances `c`. -/
def starTriangleEquivalentConductance (c : Fin 3 → NNReal) : Fin 3 → Fin 3 → ℝ≥0∞ :=
  fun i j ↦
    if i = j then 0
    else ((c i * c j / starTriangleTotalConductance c : NNReal) : ℝ≥0∞)

-- Proof sketch: unfold `starTriangleEquivalentConductance`; when `i ≠ j` the off-diagonal branch
-- of the `if` reduces to the quotient formula `c i * c j / ∑ k, c k`.
/-- Off the diagonal, the triangle edge conductance is `c i * c j / (∑ k, c k)`. -/
theorem starTriangleEquivalentConductance_apply_of_ne
    (c : Fin 3 → NNReal) {i j : Fin 3} (hij : i ≠ j) :
    starTriangleEquivalentConductance c i j =
      c i * c j / starTriangleTotalConductance c := by
  by_cases hS : starTriangleTotalConductance c = 0
  · -- In the degenerate zero-total case, every branch conductance vanishes, so both sides are `0`.
    have hsum : ∑ k ∈ (Finset.univ : Finset (Fin 3)), c k = 0 := by
      simpa [starTriangleTotalConductance] using hS
    have hci :
        c i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ show 0 ≤ c k from by exact zero_le _)).1 hsum i
        (by simp)
    have hcj :
        c j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ ↦ show 0 ≤ c k from by exact zero_le _)).1 hsum j
        (by simp)
    simp [starTriangleEquivalentConductance, hij, hS, hci, hcj]
  · -- Away from the degenerate case, `NNReal` and `ENNReal` division agree after coercion.
    simp [starTriangleEquivalentConductance, hij, hS, ENNReal.coe_div]

private inductive StarTriangleVertex
  | center
  | boundary (i : Fin 3)
  deriving DecidableEq, Fintype

private def starConductance (c : Fin 3 → NNReal) : StarTriangleVertex → StarTriangleVertex → ℝ≥0∞
  | .center, .boundary i => c i
  | .boundary i, .center => c i
  | _, _ => 0

private def starPotential (u : ℝ) (v : Fin 3 → ℝ) : StarTriangleVertex → ℝ
  | .center => u
  | .boundary i => v i

/-- Helper for Exercise 19.5.1: `StarTriangleVertex` is the center together with the three
boundary labels. -/
private def starTriangleVertexEquiv : StarTriangleVertex ≃ Option (Fin 3) where
  toFun
    | .center => none
    | .boundary i => some i
  invFun
    | none => .center
    | some i => .boundary i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

/-- Helper for Exercise 19.5.1: summing over the star vertices splits into the center term and the
three boundary terms. -/
private theorem sum_starTriangleVertex {α : Type*} [AddCommMonoid α]
    (f : StarTriangleVertex → α) :
    (∑ x : StarTriangleVertex, f x) = f .center + ∑ i : Fin 3, f (.boundary i) := by
  -- Transport the finite sum to `Option (Fin 3)` so the center and boundary contributions
  -- separate cleanly.
  have hsum :
      ∑ x : StarTriangleVertex, f x =
        ∑ o : Option (Fin 3), f (starTriangleVertexEquiv.symm o) := by
    refine
      Fintype.sum_equiv starTriangleVertexEquiv
        (fun x : StarTriangleVertex ↦ f x)
        (fun o : Option (Fin 3) ↦ f (starTriangleVertexEquiv.symm o)) ?_
    intro x
    simpa using congrArg f (starTriangleVertexEquiv.left_inv x)
  calc
    ∑ x : StarTriangleVertex, f x
        = ∑ o : Option (Fin 3), f (starTriangleVertexEquiv.symm o) := hsum
    _ = f (starTriangleVertexEquiv.symm none) +
          ∑ i : Fin 3, f (starTriangleVertexEquiv.symm (some i)) := by
            rw [Fintype.sum_option]
    _ = f .center + ∑ i : Fin 3, f (.boundary i) := by
          simp [starTriangleVertexEquiv]

/-- The Dirichlet energy of the star network with center potential `u` and boundary potential
`v`. -/
def starNetworkBoundaryEnergy (c : Fin 3 → NNReal) (u : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  finiteDirichletEnergy (starConductance c) (starPotential u v)

/-- The Dirichlet energy of the triangle obtained from the star by the star-triangle
transformation. -/
def triangleNetworkBoundaryEnergy (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) : ℝ :=
  finiteDirichletEnergy (starTriangleEquivalentConductance c) v

/-- Helper for Exercise 19.5.1: the unordered-pair normal form of the triangle energy. -/
private def starTrianglePairwiseEnergy (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) : ℝ :=
  ((c 0 * c 1 / starTriangleTotalConductance c : NNReal) : ℝ) * (v 0 - v 1) ^ (2 : ℕ) +
    ((c 0 * c 2 / starTriangleTotalConductance c : NNReal) : ℝ) * (v 0 - v 2) ^ (2 : ℕ) +
      ((c 1 * c 2 / starTriangleTotalConductance c : NNReal) : ℝ) * (v 1 - v 2) ^ (2 : ℕ)

/-- Helper for Exercise 19.5.1: the center row of the star energy is exactly the weighted sum of
the three boundary edge terms. -/
private theorem starEnergyRow_center
    (c : Fin 3 → NNReal) (u : ℝ) (v : Fin 3 → ℝ) :
    ∑ y : StarTriangleVertex,
      (starConductance c .center y).toReal *
        (starPotential u v .center - starPotential u v y) ^ (2 : ℕ) =
      ∑ i : Fin 3, (c i : ℝ) * (u - v i) ^ (2 : ℕ) := by
  -- The center-to-center term vanishes, and the three boundary terms are exactly the star edges.
  rw [sum_starTriangleVertex]
  simp [starConductance, starPotential]

/-- Helper for Exercise 19.5.1: each boundary row of the star energy contains only the edge back
to the center. -/
private theorem starEnergyRow_boundary
    (c : Fin 3 → NNReal) (u : ℝ) (v : Fin 3 → ℝ) (i : Fin 3) :
    ∑ y : StarTriangleVertex,
      (starConductance c (.boundary i) y).toReal *
        (starPotential u v (.boundary i) - starPotential u v y) ^ (2 : ℕ) =
      (c i : ℝ) * (u - v i) ^ (2 : ℕ) := by
  -- Only the boundary-to-center term survives, and squaring removes the sign change.
  by_cases hci : c i = 0
  · rw [sum_starTriangleVertex]
    simp [starConductance, starPotential, hci]
  · rw [sum_starTriangleVertex]
    simp [starConductance, starPotential, hci]
    ring_nf

/-- Helper for Exercise 19.5.1: the star boundary energy is the weighted sum of the three squared
boundary differences from the center. -/
private theorem starNetworkBoundaryEnergy_eq_weightedSum
    (c : Fin 3 → NNReal) (u : ℝ) (v : Fin 3 → ℝ) :
    starNetworkBoundaryEnergy c u v =
      ∑ i : Fin 3, (c i : ℝ) * (u - v i) ^ (2 : ℕ) := by
  -- Expand the Dirichlet energy and split the outer sum into the center row and the three
  -- boundary rows.
  rw [starNetworkBoundaryEnergy, finiteDirichletEnergy, sum_starTriangleVertex]
  rw [starEnergyRow_center]
  simp_rw [starEnergyRow_boundary]
  ring

/-- Helper for Exercise 19.5.1: the triangle boundary energy is the sum of its three unordered
edge contributions. -/
private theorem triangleNetworkBoundaryEnergy_eq_pairwise
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) :
    triangleNetworkBoundaryEnergy c v = starTrianglePairwiseEnergy c v := by
  -- Expand the ordered double sum over `Fin 3` and discard the diagonal zero-conductance terms.
  rw [triangleNetworkBoundaryEnergy, finiteDirichletEnergy, starTrianglePairwiseEnergy]
  repeat' rw [Fin.sum_univ_three]
  simp [starTriangleEquivalentConductance, pow_two]
  ring_nf

/-- Helper for Exercise 19.5.1: if the total conductance vanishes, then every branch conductance
vanishes. -/
private theorem starTriangleConductance_eq_zero_of_total_eq_zero
    (c : Fin 3 → NNReal) (hS : starTriangleTotalConductance c = 0) (i : Fin 3) :
    c i = 0 := by
  -- A sum of nonnegative `NNReal` terms can vanish only if each term is zero.
  have hsum : ∑ j ∈ (Finset.univ : Finset (Fin 3)), c j = 0 := by
    simpa [starTriangleTotalConductance] using hS
  exact
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ show 0 ≤ c j from by exact zero_le _)).1 hsum i
      (by simp)

/-- Helper for Exercise 19.5.1: the weighted center value is the explicit three-point weighted
average. -/
private theorem starTriangleCenterPotential_eq_coordinates
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) :
    starTriangleCenterPotential c v =
      ((c 0 : ℝ) * v 0 + (c 1 : ℝ) * v 1 + (c 2 : ℝ) * v 2) /
        ((c 0 : ℝ) + (c 1 : ℝ) + (c 2 : ℝ)) := by
  -- Expand the numerator and denominator sums over the three boundary vertices.
  rw [starTriangleCenterPotential, starTriangleTotalConductance, NNReal.coe_sum]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]

/-- Helper for Exercise 19.5.1: the pairwise triangle energy is the explicit three-edge quadratic
form in the boundary values. -/
private theorem starTrianglePairwiseEnergy_eq_coordinates
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) :
    starTrianglePairwiseEnergy c v =
      ((c 0 : ℝ) * (c 1 : ℝ) / ((c 0 : ℝ) + (c 1 : ℝ) + (c 2 : ℝ))) *
          (v 0 - v 1) ^ (2 : ℕ) +
        ((c 0 : ℝ) * (c 2 : ℝ) / ((c 0 : ℝ) + (c 1 : ℝ) + (c 2 : ℝ))) *
          (v 0 - v 2) ^ (2 : ℕ) +
          ((c 1 : ℝ) * (c 2 : ℝ) / ((c 0 : ℝ) + (c 1 : ℝ) + (c 2 : ℝ))) *
            (v 1 - v 2) ^ (2 : ℕ) := by
  -- Convert the `NNReal` coefficients and the total conductance into their explicit real forms.
  simp [starTrianglePairwiseEnergy, starTriangleTotalConductance, Fin.sum_univ_three,
    NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div]

/-- Helper for Exercise 19.5.1: the weighted variance around the weighted average is the centered
second-moment formula for three coordinates. -/
private theorem weightedVarianceCoordinates_eq_centeredSquares
    (a b d x y z : ℝ) (hS : a + b + d ≠ 0) :
    a * (((a * x + b * y + d * z) / (a + b + d) - x) ^ (2 : ℕ)) +
        b * (((a * x + b * y + d * z) / (a + b + d) - y) ^ (2 : ℕ)) +
          d * (((a * x + b * y + d * z) / (a + b + d) - z) ^ (2 : ℕ)) =
      (a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) + d * z ^ (2 : ℕ)) -
        (a * x + b * y + d * z) ^ (2 : ℕ) / (a + b + d) := by
  -- Clear the common denominator and reduce the goal to a polynomial identity.
  field_simp [pow_two, hS]
  ring

/-- Helper for Exercise 19.5.1: the pairwise quadratic form is the same centered second-moment
expression. -/
private theorem pairwiseCoordinates_eq_centeredSquares
    (a b d x y z : ℝ) (hS : a + b + d ≠ 0) :
      (a * b / (a + b + d)) * (x - y) ^ (2 : ℕ) +
        (a * d / (a + b + d)) * (x - z) ^ (2 : ℕ) +
          (b * d / (a + b + d)) * (y - z) ^ (2 : ℕ) =
      (a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) + d * z ^ (2 : ℕ)) -
        (a * x + b * y + d * z) ^ (2 : ℕ) / (a + b + d) := by
  -- Clear the common denominator and reduce the goal to a polynomial identity.
  field_simp [pow_two, hS]
  ring

/-- Helper for Exercise 19.5.1: the weighted variance identity for three real coordinates equals
the corresponding pairwise quadratic form. -/
private theorem weightedVarianceCoordinates_eq_pairwise
    (a b d x y z : ℝ) (hS : a + b + d ≠ 0) :
    a * (((a * x + b * y + d * z) / (a + b + d) - x) ^ (2 : ℕ)) +
        b * (((a * x + b * y + d * z) / (a + b + d) - y) ^ (2 : ℕ)) +
          d * (((a * x + b * y + d * z) / (a + b + d) - z) ^ (2 : ℕ)) =
      (a * b / (a + b + d)) * (x - y) ^ (2 : ℕ) +
        (a * d / (a + b + d)) * (x - z) ^ (2 : ℕ) +
          (b * d / (a + b + d)) * (y - z) ^ (2 : ℕ) := by
  -- Compare the two normal forms through the shared centered second-moment expression.
  calc
    a * (((a * x + b * y + d * z) / (a + b + d) - x) ^ (2 : ℕ)) +
        b * (((a * x + b * y + d * z) / (a + b + d) - y) ^ (2 : ℕ)) +
          d * (((a * x + b * y + d * z) / (a + b + d) - z) ^ (2 : ℕ))
        =
          (a * x ^ (2 : ℕ) + b * y ^ (2 : ℕ) + d * z ^ (2 : ℕ)) -
            (a * x + b * y + d * z) ^ (2 : ℕ) / (a + b + d) := by
              exact weightedVarianceCoordinates_eq_centeredSquares a b d x y z hS
    _ =
          (a * b / (a + b + d)) * (x - y) ^ (2 : ℕ) +
            (a * d / (a + b + d)) * (x - z) ^ (2 : ℕ) +
              (b * d / (a + b + d)) * (y - z) ^ (2 : ℕ) := by
                exact (pairwiseCoordinates_eq_centeredSquares a b d x y z hS).symm

/-- Helper for Exercise 19.5.1: at nonzero total conductance, the weighted variance at the
harmonic center equals the pairwise triangle quadratic form. -/
private theorem weightedVariance_fin3_eq_pairwise
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) (hS : starTriangleTotalConductance c ≠ 0) :
    (∑ i : Fin 3, (c i : ℝ) * (starTriangleCenterPotential c v - v i) ^ (2 : ℕ)) =
      starTrianglePairwiseEnergy c v := by
  have hSreal : (c 0 : ℝ) + (c 1 : ℝ) + (c 2 : ℝ) ≠ 0 := by
    -- The explicit real denominator vanishes exactly when the total `NNReal` conductance does.
    intro hzero
    apply hS
    apply NNReal.coe_injective
    simpa [starTriangleTotalConductance, Fin.sum_univ_three, NNReal.coe_add] using hzero
  -- Rewrite both network energies to their explicit three-coordinate forms.
  rw [Fin.sum_univ_three, starTriangleCenterPotential_eq_coordinates,
    starTrianglePairwiseEnergy_eq_coordinates]
  -- The explicit coordinate identity is exactly the weighted-variance to pairwise bridge.
  simpa using
    (weightedVarianceCoordinates_eq_pairwise
      (a := (c 0 : ℝ)) (b := (c 1 : ℝ)) (d := (c 2 : ℝ))
      (x := v 0) (y := v 1) (z := v 2) hSreal)

-- Proof sketch: if `starTriangleTotalConductance c = 0`, then every branch conductance vanishes,
-- so both Dirichlet energies are `0`. Otherwise substitute the weighted center value
-- `starTriangleCenterPotential c v = (∑ i, c i * v i) / (∑ i, c i)` into the star energy,
-- expand the square, and simplify the resulting quadratic form. The coefficients match the
-- triangle energy defined by the equivalent conductance family
-- `starTriangleEquivalentConductance c`.
/-- Exercise 19.5.1: the star-triangle transformation is valid. For three boundary vertices with
star branch conductances `c`, eliminating the center vertex by the conductance-weighted center
value `starTriangleCenterPotential c v` produces the same boundary Dirichlet energy as the
triangle with edge conductances `c i * c j / (∑ k, c k)`. For positive total conductance this
center value is the harmonic one, while in the degenerate zero-conductance case both energies
vanish. -/
theorem star_triangle_transformation
    (c : Fin 3 → NNReal) (v : Fin 3 → ℝ) :
    starNetworkBoundaryEnergy c (starTriangleCenterPotential c v) v =
      triangleNetworkBoundaryEnergy c v := by
  by_cases hS0 : starTriangleTotalConductance c = 0
  · -- If every branch conductance vanishes, both boundary energies collapse to zero.
    have hc0 : c 0 = 0 := starTriangleConductance_eq_zero_of_total_eq_zero c hS0 0
    have hc1 : c 1 = 0 := starTriangleConductance_eq_zero_of_total_eq_zero c hS0 1
    have hc2 : c 2 = 0 := starTriangleConductance_eq_zero_of_total_eq_zero c hS0 2
    rw [starNetworkBoundaryEnergy_eq_weightedSum, triangleNetworkBoundaryEnergy_eq_pairwise]
    rw [Fin.sum_univ_three]
    simp [starTrianglePairwiseEnergy, starTriangleTotalConductance, hc0, hc1, hc2]
  · -- For nonzero total conductance, both sides normalize to the same quadratic form.
    rw [starNetworkBoundaryEnergy_eq_weightedSum, triangleNetworkBoundaryEnergy_eq_pairwise]
    exact weightedVariance_fin3_eq_pairwise c v hS0

end ProbabilityTheory
