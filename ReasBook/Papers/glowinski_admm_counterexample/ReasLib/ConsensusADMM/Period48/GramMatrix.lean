/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.IntegerMatrix
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace ConsensusADMM
namespace Period48

noncomputable section

/-- The multiplier value `γ₀ = 1887 / 1000` of the period-48 configuration. -/
def gammaZero : ℝ :=
  (1887 : ℝ) / 1000

/-- The multiplier `γ₀` equals the rational `1887 / 1000`. -/
theorem gammaZero_eq : gammaZero = (1887 : ℝ) / 1000 :=
  -- Definitional: the right-hand side is the defining body of `gammaZero`.
  rfl

/-- The alternating-component scale `σ = 6887062879763 / 6697811464000`. -/
def sigma : ℝ :=
  (6887062879763 : ℝ) / 6697811464000

/-- The scale `σ` equals the rational `6887062879763 / 6697811464000`. -/
theorem sigma_eq : sigma = (6887062879763 : ℝ) / 6697811464000 :=
  -- Definitional: the right-hand side is the defining body of `sigma`.
  rfl

/-- The period-48 alternating vector with coordinates `vᵢ = (-1) ^ i.val`. -/
def alternating (i : Fin 48) : ℝ :=
  (-1 : ℝ) ^ i.val

/-- Pointwise evaluation of the alternating period-48 vector. -/
theorem alternating_apply (i : Fin 48) : alternating i = (-1 : ℝ) ^ i.val :=
  -- Definitional: the right-hand side is the defining body of `alternating`.
  rfl

/-- Every coordinate of the alternating vector is a unit: `vᵢ * vᵢ = 1`. -/
lemma alternating_mul_self (i : Fin 48) : alternating i * alternating i = 1 := by
  -- Combine the two factors into a single power with an even exponent.
  simp only [alternating]
  rw [← pow_add]
  exact (Even.add_self i.val).neg_one_pow

/-- The alternating vector obeys the one-step relation `vᵢ₋₁ = -vᵢ`. -/
lemma alternating_sub_one_eq_neg (i : Fin 48) : alternating (i - 1) = -alternating i := by
  -- Consecutive phases have exponents of opposite parity, so their product is `-1`.
  have hodd : Odd ((i - 1).val + i.val) := by
    rw [Nat.odd_iff]
    fin_cases i <;> decide
  have hsum : alternating (i - 1) * alternating i = -1 := by
    simp only [alternating]
    rw [← pow_add]
    exact hodd.neg_one_pow
  rw [← mul_one (alternating (i - 1)), ← alternating_mul_self i, ← mul_assoc, hsum,
    neg_one_mul]

/-- A cyclic displacement in `Fin 48` has the same parity as the sum of the two phases. -/
lemma val_sub_mod_two (i j : Fin 48) : (j - i).val % 2 = (i.val + j.val) % 2 := by
  -- Descend from the cyclic remainder modulo `48` to the remainder modulo `2`.
  rw [Fin.val_sub, Nat.mod_mod_of_dvd _ (show 2 ∣ 48 by norm_num)]
  have hi : i.val < 48 := i.isLt
  have hj : j.val < 48 := j.isLt
  omega

/-- The alternating vector flips sign at odd cyclic displacement. -/
lemma alternating_eq_neg_of_odd_sub {i j : Fin 48} (h : Odd ((j - i).val)) :
    alternating j = -alternating i := by
  -- Transport the oddness hypothesis to the sum of the two phases.
  have hodd : Odd (i.val + j.val) := by
    rw [Nat.odd_iff] at h ⊢
    rw [← val_sub_mod_two i j]
    exact h
  have hsum : alternating j * alternating i = -1 := by
    simp only [alternating]
    rw [← pow_add, Nat.add_comm j.val i.val]
    exact hodd.neg_one_pow
  rw [← mul_one (alternating j), ← alternating_mul_self i, ← mul_assoc, hsum, neg_one_mul]

/-- The alternating vector is invariant at even cyclic displacement. -/
lemma alternating_eq_of_even_sub {i j : Fin 48} (h : Even ((j - i).val)) :
    alternating j = alternating i := by
  -- Transport the evenness hypothesis to the sum of the two phases.
  have heven : Even (i.val + j.val) := by
    rw [Nat.even_iff] at h ⊢
    rw [← val_sub_mod_two i j]
    exact h
  have hsum : alternating j * alternating i = 1 := by
    simp only [alternating]
    rw [← pow_add, Nat.add_comm j.val i.val]
    exact heven.neg_one_pow
  rw [← mul_one (alternating j), ← alternating_mul_self i, ← mul_assoc, hsum, one_mul]

/-- Every coordinate of the alternating vector equals `1` or `-1`. -/
lemma alternating_eq_one_or_eq_neg_one (i : Fin 48) : alternating i = 1 ∨ alternating i = -1 := by
  simpa only [alternating] using neg_one_pow_eq_or ℝ i.val

/-- The two-block vector `h = (-σ v, γ₀ v)`. -/
def perturbationVector (a : Fin 2 × Fin 48) : ℝ :=
  if a.1 = 0 then -sigma * alternating a.2 else gammaZero * alternating a.2

/-- Pointwise evaluation of the two blocks of `h`. -/
theorem perturbationVector_apply (b : Fin 2) (i : Fin 48) :
    perturbationVector (b, i) =
      if b = 0 then -sigma * alternating i else gammaZero * alternating i :=
  -- Definitional: the first block is read off by the projection `(b, i).1`.
  rfl

/-- The Gram matrix `H = 2K - I₉₆ + 3hhᵀ` in two-block coordinates, where `K`
is the period-48 integer block-circulant matrix. -/
def gramMatrix : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ :=
  fun a b ↦
    2 * (integerMatrix a b : ℝ) - (if a = b then 1 else 0) +
      3 * perturbationVector a * perturbationVector b

/-- Entrywise formula for the period-48 Gram matrix. -/
theorem gramMatrix_apply (a b : Fin 2 × Fin 48) :
    gramMatrix a b =
      2 * (integerMatrix a b : ℝ) - (if a = b then 1 else 0) +
        3 * perturbationVector a * perturbationVector b :=
  -- Definitional: the right-hand side is the defining body of `gramMatrix`.
  rfl

/-- The period-48 Gram matrix is symmetric. -/
theorem gramMatrix_isSymm : gramMatrix.IsSymm := by
  -- Reduce to the entrywise identity `H b a = H a b`.
  refine Matrix.IsSymm.ext fun a b => ?_
  by_cases hab : a = b
  · rw [hab]
  · -- Off the diagonal the integer block is symmetric and the rank-one term commutes.
    have hba : ¬ b = a := fun h => hab h.symm
    have hcomm : integerMatrix b a = integerMatrix a b :=
      Matrix.IsSymm.apply integerMatrix_transpose a b
    simp only [gramMatrix, if_neg hab, if_neg hba, hcomm]
    ring

/-- The alternating auxiliary `ηᵢ = -σ vᵢ`. -/
def alternatingEta (i : Fin 48) : ℝ :=
  -sigma * alternating i

/-- The auxiliary `ηᵢ` in terms of `σ` and the alternating vector. -/
theorem alternatingEta_apply (i : Fin 48) :
    alternatingEta i = -sigma * alternating i :=
  -- Definitional: the right-hand side is the defining body of `alternatingEta`.
  rfl

/-- The first difference `ρᵢ = vᵢ - vᵢ₋₁` of the alternating vector. -/
def alternatingResidual (i : Fin 48) : ℝ :=
  alternating i - alternating (i - 1)

/-- The first difference `ρᵢ` in terms of the alternating vector. -/
theorem alternatingResidual_apply (i : Fin 48) :
    alternatingResidual i = alternating i - alternating (i - 1) :=
  -- Definitional: the right-hand side is the defining body of `alternatingResidual`.
  rfl

/-- The combined alternating vertex `ξᵢ = ηᵢ + ρᵢ`. -/
def alternatingVertex (i : Fin 48) : ℝ :=
  alternatingEta i + alternatingResidual i

/-- The alternating vertex `ξᵢ` in terms of `η` and `ρ`. -/
theorem alternatingVertex_apply (i : Fin 48) :
    alternatingVertex i = alternatingEta i + alternatingResidual i :=
  -- Definitional: the right-hand side is the defining body of `alternatingVertex`.
  rfl

/-- The first-block support normal `aᵢ(γ) = ηᵢ₋₁ - γ * vᵢ₋₁ - ξᵢ`. -/
def alternatingFirstNormal (gamma : ℝ) (i : Fin 48) : ℝ :=
  alternatingEta (i - 1) - gamma * alternating (i - 1) - alternatingVertex i

/-- The first-block support normal `aᵢ(γ)` in terms of `η`, the alternating
vector, and the vertex `ξ`. -/
theorem alternatingFirstNormal_apply (gamma : ℝ) (i : Fin 48) :
    alternatingFirstNormal gamma i =
      alternatingEta (i - 1) - gamma * alternating (i - 1) - alternatingVertex i :=
  -- Definitional: the right-hand side is the defining body of `alternatingFirstNormal`.
  rfl

/-- The second-block support normal `cᵢ(γ) = γ * vᵢ₋₁ + ρᵢ`. -/
def alternatingSecondNormal (gamma : ℝ) (i : Fin 48) : ℝ :=
  gamma * alternating (i - 1) + alternatingResidual i

/-- The second-block support normal `cᵢ(γ)` in terms of the alternating vector
and the residual `ρ`. -/
theorem alternatingSecondNormal_apply (gamma : ℝ) (i : Fin 48) :
    alternatingSecondNormal gamma i =
      gamma * alternating (i - 1) + alternatingResidual i :=
  -- Definitional: the right-hand side is the defining body of `alternatingSecondNormal`.
  rfl

/-- The pair of first- and second-block support contributions of the alternating
component at phases `i` and `j`. -/
def alternatingSupport (gamma : ℝ) (i j : Fin 48) : ℝ × ℝ :=
  (alternatingFirstNormal gamma i *
      (alternatingVertex i - alternatingVertex j),
    alternatingSecondNormal gamma i * (alternatingEta i - alternatingEta j))

/-- At odd cyclic displacement the alternating component contributes the pair
`(2 * (2 - sigma) * (gamma + 2 * sigma - 2), 2 * sigma * (gamma - 2))` to the two
block supports. -/
theorem alternatingSupport_odd (gamma : ℝ) (i j : Fin 48)
    (odd : Odd ((j - i).val)) :
    alternatingSupport gamma i j =
      (2 * (2 - sigma) * (gamma + 2 * sigma - 2), 2 * sigma * (gamma - 2)) := by
  -- Unfold the support pair and normalize every occurrence of `vᵢ` and `vᵢ₋₁`.
  have hji : alternating j = -alternating i := alternating_eq_neg_of_odd_sub odd
  simp only [alternatingSupport, alternatingFirstNormal, alternatingSecondNormal,
    alternatingVertex, alternatingEta, alternatingResidual,
    alternating_sub_one_eq_neg i, alternating_sub_one_eq_neg j, hji]
  -- The remaining expression is a polynomial in `vᵢ`, and `vᵢ = ±1`.
  rcases alternating_eq_one_or_eq_neg_one i with h | h <;> rw [h] <;> ext <;> ring_nf

/-- At even cyclic displacement the alternating component contributes zero to
both non-origin supports. -/
theorem alternatingSupport_even (gamma : ℝ) (i j : Fin 48)
    (even : Even ((j - i).val)) :
    alternatingSupport gamma i j = (0, 0) := by
  -- Unfold the support pair; at even displacement both vertex and multiplier agree.
  have hji : alternating j = alternating i := alternating_eq_of_even_sub even
  simp only [alternatingSupport, alternatingFirstNormal, alternatingSecondNormal,
    alternatingVertex, alternatingEta, alternatingResidual,
    alternating_sub_one_eq_neg i, alternating_sub_one_eq_neg j, hji]
  ext <;> ring_nf

/-- The pair of alternating-component support contributions at phase `i`,
measured against the origin. -/
def alternatingOriginSupport (gamma : ℝ) (i : Fin 48) : ℝ × ℝ :=
  (alternatingFirstNormal gamma i * alternatingVertex i,
    alternatingSecondNormal gamma i * alternatingEta i)

/-- The origin contributions are half the two odd-displacement contributions. -/
theorem alternatingOriginSupport_eq (gamma : ℝ) (i : Fin 48) :
    alternatingOriginSupport gamma i =
      ((2 - sigma) * (gamma + 2 * sigma - 2), sigma * (gamma - 2)) := by
  -- Unfold the origin pair and normalize `vᵢ₋₁ = -vᵢ`.
  simp only [alternatingOriginSupport, alternatingFirstNormal, alternatingSecondNormal,
    alternatingVertex, alternatingEta, alternatingResidual, alternating_sub_one_eq_neg i]
  -- The remaining expression is a polynomial in `vᵢ`, and `vᵢ = ±1`.
  rcases alternating_eq_one_or_eq_neg_one i with h | h <;> rw [h] <;> ext <;> ring_nf

end

end Period48
end ConsensusADMM
