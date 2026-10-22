/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.GramMatrix
public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Threshold
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace ConsensusADMM
namespace Period48
namespace Coefficient

noncomputable section

/-- The first-block coefficient basis vector `ηᵢ`: the standard basis vector of
`(Fin 2 × Fin 48) → ℝ` supported on the first block at phase `i`. -/
def eta (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  fun p ↦ if p.1 = 0 ∧ (p.2 : ZMod 48) = i then 1 else 0

/-- The second-block coefficient basis vector `νᵢ`: the standard basis vector of
`(Fin 2 × Fin 48) → ℝ` supported on the second block at phase `i`. -/
def nu (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  fun p ↦ if p.1 = 1 ∧ (p.2 : ZMod 48) = i then 1 else 0

/-- The scaled second-block coefficient vector `wᵢ = νᵢ / γ₀`. -/
def w (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  gammaZero⁻¹ • nu i

/-- The coefficient residual `ρᵢ = wᵢ - wᵢ₋₁`. -/
def rho (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  w i - w (i - 1)

/-- The first-block vertex coefficient `ξᵢ = ηᵢ + ρᵢ`. -/
def xi (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  eta i + rho i

/-- The affine first normal `aᵢ(γ) = ηᵢ₋₁ - γ wᵢ₋₁ - ξᵢ`, affine in the
multiplier factor `γ`. -/
def firstNormal (γ : ℝ) (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  eta (i - 1) - γ • w (i - 1) - xi i

/-- The affine second normal `cᵢ(γ) = γ wᵢ₋₁ + ρᵢ`, affine in the multiplier
factor `γ`. -/
def secondNormal (γ : ℝ) (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  γ • w (i - 1) + rho i

/-- The vertex family of block `b`: `ξᵢ` in the first block and `ηᵢ` in the
second block. -/
def vertex (b : Fin 2) (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  if b = 0 then xi i else eta i

/-- The normal family of block `b`: `aᵢ(γ)` in the first block and `cᵢ(γ)` in the
second block. -/
def normal (b : Fin 2) (γ : ℝ) (i : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  if b = 0 then firstNormal γ i else secondNormal γ i

/-- The vector tested against the normal of block `b` at phase `i`: the vertex
`vertex b i` at displacement `0`, and the phase difference towards `i + d`
otherwise. -/
def testVector (b : Fin 2) (i d : ZMod 48) : (Fin 2 × Fin 48) → ℝ :=
  if d = 0 then vertex b i else vertex b i - vertex b (i + d)

/-- The support test of block `b` at phase `i` and displacement `d`: the Gram
pairing `zᵀ H w` of the block normal with the tested vector. -/
def support (b : Fin 2) (γ : ℝ) (i d : ZMod 48) : ℝ :=
  dotProduct (normal b γ i) (gramMatrix.mulVec (testVector b i d))

/-- The value at the critical factor `γ̂` of the phase-zero support expression of
block `b` and displacement `d`. -/
def supportAtCritical (b : Fin 2) (d : ZMod 48) : ℝ :=
  support b criticalFactor 0 d

/-- The slope of the phase-zero support expression of block `b` and displacement
`d`, recorded as its secant over `[γ̂, γ̂ + 1]`. -/
def supportSlope (b : Fin 2) (d : ZMod 48) : ℝ :=
  support b (criticalFactor + 1) 0 d - support b criticalFactor 0 d

/-! ## Bilinear-form helpers for the coefficient pairing -/

/-- The coefficient coordinate pairing block `a` with phase `i`. -/
def blockCoord (a : Fin 2) (i : ZMod 48) : Fin 2 × Fin 48 :=
  (a, i)

/-- The first-block coefficient basis vector `ηᵢ` is the standard basis vector
supported at the coordinate `(0, i)`. -/
lemma eta_eq_single (i : ZMod 48) : eta i = Pi.single (blockCoord 0 i) (1 : ℝ) := by
  funext p
  rw [eta, Pi.single_apply]
  by_cases h : p = blockCoord 0 i
  · have hc : p.1 = 0 ∧ (p.2 : ZMod 48) = i := by
      rw [h]
      exact ⟨rfl, rfl⟩
    rw [if_pos hc, if_pos h]
  · have hc : ¬ (p.1 = 0 ∧ (p.2 : ZMod 48) = i) := fun hcc ↦ h (Prod.ext hcc.1 hcc.2)
    rw [if_neg hc, if_neg h]

/-- The second-block coefficient basis vector `νᵢ` is the standard basis vector
supported at the coordinate `(1, i)`. -/
lemma nu_eq_single (i : ZMod 48) : nu i = Pi.single (blockCoord 1 i) (1 : ℝ) := by
  funext p
  rw [nu, Pi.single_apply]
  by_cases h : p = blockCoord 1 i
  · have hc : p.1 = 1 ∧ (p.2 : ZMod 48) = i := by
      rw [h]
      exact ⟨rfl, rfl⟩
    rw [if_pos hc, if_pos h]
  · have hc : ¬ (p.1 = 1 ∧ (p.2 : ZMod 48) = i) := fun hcc ↦ h (Prod.ext hcc.1 hcc.2)
    rw [if_neg hc, if_neg h]

/-- The coefficient pairing of a standard basis vector with an arbitrary vector
reads off the corresponding coordinate. -/
lemma dotProduct_single_one (c : Fin 2 × Fin 48) (f : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (Pi.single c (1 : ℝ)) f = f c := by
  simp only [dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The coefficient pairing is additive in its left argument. -/
lemma dotProduct_add_left (f g h : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (f + g) h = dotProduct f h + dotProduct g h := by
  simp only [dotProduct, Pi.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

/-- The coefficient pairing is additive in its right argument. -/
lemma dotProduct_add_right (f g h : (Fin 2 × Fin 48) → ℝ) :
    dotProduct f (g + h) = dotProduct f g + dotProduct f h := by
  simp only [dotProduct, Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- The coefficient pairing is subtractive in its left argument. -/
lemma dotProduct_sub_left (f g h : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (f - g) h = dotProduct f h - dotProduct g h := by
  simp only [dotProduct, Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- The coefficient pairing is homogeneous in its left argument. -/
lemma dotProduct_smul_left (a : ℝ) (f g : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (a • f) g = a * dotProduct f g := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [Finset.mul_sum]

/-- The coefficient pairing is homogeneous in its right argument. -/
lemma dotProduct_smul_right (a : ℝ) (f g : (Fin 2 × Fin 48) → ℝ) :
    dotProduct f (a • g) = a * dotProduct f g := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rw [Finset.mul_sum]

/-- The tested vector at zero displacement is the base vertex. -/
lemma testVector_eq_origin (b : Fin 2) (i : ZMod 48) : testVector b i 0 = vertex b i := by
  rw [testVector, if_pos rfl]

/-- The tested vector at a nonzero displacement is the difference of two vertices. -/
lemma testVector_eq_diff (b : Fin 2) (i d : ZMod 48) (hd : d ≠ 0) :
    testVector b i d = vertex b i - vertex b (i + d) := by
  rw [testVector, if_neg hd]

/-- The first block test vertex is the coefficient vertex `ξ`. -/
lemma vertex_zero (i : ZMod 48) : vertex 0 i = xi i := by
  rw [vertex, if_pos rfl]

/-- The second block test vertex is the coefficient basis vector `η`. -/
lemma vertex_one (i : ZMod 48) : vertex 1 i = eta i := by
  rw [vertex, if_neg (by decide)]

/-- The first block normal is the affine family `aᵢ`. -/
lemma normal_zero (γ : ℝ) (i : ZMod 48) : normal 0 γ i = firstNormal γ i := by
  rw [normal, if_pos rfl]

/-- The second block normal is the affine family `cᵢ`. -/
lemma normal_one (γ : ℝ) (i : ZMod 48) : normal 1 γ i = secondNormal γ i := by
  rw [normal, if_neg (by decide)]

/-- The first-block normal depends affinely on the multiplier factor `γ`. -/
lemma firstNormal_eq_affine (γ : ℝ) (i : ZMod 48) :
    firstNormal γ i = firstNormal 0 i + γ • (firstNormal 1 i - firstNormal 0 i) := by
  ext p
  simp only [firstNormal, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The second-block normal depends affinely on the multiplier factor `γ`. -/
lemma secondNormal_eq_affine (γ : ℝ) (i : ZMod 48) :
    secondNormal γ i = secondNormal 0 i + γ • (secondNormal 1 i - secondNormal 0 i) := by
  ext p
  simp only [secondNormal, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every block normal depends affinely on the multiplier factor `γ`. -/
lemma normal_eq_affine (b : Fin 2) (γ : ℝ) (i : ZMod 48) :
    normal b γ i = normal b 0 i + γ • (normal b 1 i - normal b 0 i) := by
  by_cases hb : b = 0
  · subst hb
    simpa only [normal_zero] using firstNormal_eq_affine γ i
  · have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    simpa only [normal_one] using secondNormal_eq_affine γ i


/-! ## Cyclic phase-shift invariance of the coefficient pairing -/

/-- The phase coordinate `k : Fin 48`, viewed as a cyclic phase in `ZMod 48`. -/
def toPhase (k : Fin 48) : ZMod 48 := k

/-- The cyclic shift of the two-block coefficient coordinates that moves the
phase `k` to `k + m`. -/
def phaseShift (m : ZMod 48) : (Fin 2 × Fin 48) ≃ (Fin 2 × Fin 48) :=
  Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.addRight (G := Fin 48) m)

/-- The phase shift preserves the block coordinate. -/
lemma phaseShift_fst (m : ZMod 48) (a : Fin 2) (k : Fin 48) :
    (phaseShift m (a, k)).1 = a := rfl

/-- The phase shift acts on a coordinate pair by adding `m` to the phase. -/
lemma phaseShift_pair (m : ZMod 48) (a : Fin 2) (k : Fin 48) :
    phaseShift m (a, k) = (a, Equiv.addRight (G := Fin 48) m k) := rfl

/-- The phase of a shifted coordinate is the sum of the phases in `ZMod 48`. -/
lemma toPhase_addRight (m : ZMod 48) (k : Fin 48) :
    toPhase (Equiv.addRight (G := Fin 48) m k) = toPhase k + m := rfl

/-- The phase coordinate of a shifted pair is shifted by `m`. -/
lemma phaseShift_snd (m : ZMod 48) (a : Fin 2) (k : Fin 48) :
    toPhase (phaseShift m (a, k)).2 = toPhase k + m := rfl

/-- Pointwise evaluation of the first-block basis vector on a coordinate pair. -/
lemma eta_apply_pair (i : ZMod 48) (a : Fin 2) (k : Fin 48) :
    eta i (a, k) = (if a = 0 ∧ toPhase k = i then (1 : ℝ) else 0) := rfl

/-- The first-block basis vector is carried by the phase shift to the vector at
the shifted phase. -/
lemma eta_phaseShift (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    eta i (phaseShift m p) = eta (i - m) p := by
  obtain ⟨a, k⟩ := p
  rw [show eta i (phaseShift m (a, k)) =
      (if a = 0 ∧ toPhase (phaseShift m (a, k)).2 = i then (1 : ℝ) else 0) from rfl,
    phaseShift_snd, eta_apply_pair]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_sub_iff_add_eq.mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_sub_iff_add_eq.mp h2⟩

/-- Pointwise evaluation of the second-block basis vector on a coordinate pair. -/
lemma nu_apply_pair (i : ZMod 48) (a : Fin 2) (k : Fin 48) :
    nu i (a, k) = (if a = 1 ∧ toPhase k = i then (1 : ℝ) else 0) := rfl

/-- The second-block basis vector is carried by the phase shift to the vector at
the shifted phase. -/
lemma nu_phaseShift (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    nu i (phaseShift m p) = nu (i - m) p := by
  obtain ⟨a, k⟩ := p
  rw [show nu i (phaseShift m (a, k)) =
      (if a = 1 ∧ toPhase (phaseShift m (a, k)).2 = i then (1 : ℝ) else 0) from rfl,
    phaseShift_snd, nu_apply_pair]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_sub_iff_add_eq.mpr h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, eq_sub_iff_add_eq.mp h2⟩

/-- The scaled second-block vector transforms contravariantly under the phase shift. -/
lemma w_phaseShift (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    w i (phaseShift m p) = w (i - m) p := by
  simp only [w, Pi.smul_apply, nu_phaseShift]

/-- The coefficient residual transforms contravariantly under the phase shift. -/
lemma rho_phaseShift (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    rho i (phaseShift m p) = rho (i - m) p := by
  have h : i - 1 - m = i - m - 1 := by abel
  simp only [rho, Pi.sub_apply, w_phaseShift, h]

/-- The first-block vertex coefficient transforms contravariantly under the phase shift. -/
lemma xi_phaseShift (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    xi i (phaseShift m p) = xi (i - m) p := by
  simp only [xi, Pi.add_apply, eta_phaseShift, rho_phaseShift]

/-- The first-block normal transforms contravariantly under the phase shift. -/
lemma firstNormal_phaseShift (γ : ℝ) (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    firstNormal γ i (phaseShift m p) = firstNormal γ (i - m) p := by
  have h : i - 1 - m = i - m - 1 := by abel
  simp only [firstNormal, Pi.sub_apply, Pi.smul_apply, eta_phaseShift, w_phaseShift, h,
    xi_phaseShift]

/-- The second-block normal transforms contravariantly under the phase shift. -/
lemma secondNormal_phaseShift (γ : ℝ) (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    secondNormal γ i (phaseShift m p) = secondNormal γ (i - m) p := by
  have h : i - 1 - m = i - m - 1 := by abel
  simp only [secondNormal, Pi.add_apply, Pi.smul_apply, w_phaseShift, h, rho_phaseShift]

/-- The block vertex family transforms contravariantly under the phase shift. -/
lemma vertex_phaseShift (b : Fin 2) (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    vertex b i (phaseShift m p) = vertex b (i - m) p := by
  by_cases hb : b = 0
  · subst hb
    simpa only [vertex_zero] using xi_phaseShift i m p
  · have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    simpa only [vertex_one] using eta_phaseShift i m p

/-- The block normal family transforms contravariantly under the phase shift. -/
lemma normal_phaseShift (b : Fin 2) (γ : ℝ) (i m : ZMod 48) (p : Fin 2 × Fin 48) :
    normal b γ i (phaseShift m p) = normal b γ (i - m) p := by
  by_cases hb : b = 0
  · subst hb
    simpa only [normal_zero] using firstNormal_phaseShift γ i m p
  · have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    simpa only [normal_one] using secondNormal_phaseShift γ i m p

/-- The tested vector transforms contravariantly under the phase shift. -/
lemma testVector_phaseShift (b : Fin 2) (i d m : ZMod 48) (p : Fin 2 × Fin 48) :
    testVector b i d (phaseShift m p) = testVector b (i - m) d p := by
  have hid : (i + d) - m = (i - m) + d := by abel
  by_cases hd : d = 0
  · rw [testVector, if_pos hd, testVector, if_pos hd]
    exact vertex_phaseShift b i m p
  · rw [testVector, if_neg hd, testVector, if_neg hd]
    simp only [Pi.sub_apply, vertex_phaseShift, hid]

/-- The sign of the alternating vector after a phase shift by `m`. -/
def altSign (m : ZMod 48) : ℝ := (-1 : ℝ) ^ m.val

/-- The alternating vector is the sign `altSign` of its phase. -/
lemma alternating_eq_altSign (k : Fin 48) : alternating k = altSign (toPhase k) := rfl

/-- The shift sign is its own inverse: `altSign m * altSign m = 1`. -/
lemma altSign_mul_self (m : ZMod 48) : altSign m * altSign m = 1 := by
  rw [show altSign m = alternating (toPhase m) from rfl]
  exact alternating_mul_self (toPhase m)

/-- The shift sign is multiplicative in the shift: shifting twice multiplies the
signs. -/
lemma altSign_add (i m : ZMod 48) : altSign (i + m) = altSign m * altSign i := by
  have h2 : (i + m).val % 2 = (i.val + m.val) % 2 := by
    rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 48)]
  have heven : Even (i + m).val ↔ Even (i.val + m.val) := by
    rw [Nat.even_iff, Nat.even_iff, h2]
  have h : (-1 : ℝ) ^ (i + m).val = (-1 : ℝ) ^ (i.val + m.val) :=
    neg_one_pow_congr heven
  simp only [altSign]
  rw [h, pow_add, mul_comm]

/-- A phase-shifted alternating coordinate is the shift sign times the original one. -/
lemma alternating_addRight (m : ZMod 48) (k : Fin 48) :
    alternating (Equiv.addRight (G := Fin 48) m k) = altSign m * alternating k := by
  rw [show alternating (Equiv.addRight (G := Fin 48) m k) =
      altSign (toPhase (Equiv.addRight (G := Fin 48) m k)) from rfl, toPhase_addRight,
    altSign_add]
  simp only [alternating_eq_altSign]

/-- Pointwise evaluation of the perturbation vector on a coordinate pair. -/
lemma perturbationVector_apply_mul (a : Fin 2) (i : Fin 48) :
    perturbationVector (a, i) = (if a = 0 then -sigma else gammaZero) * alternating i := by
  rw [perturbationVector_apply]
  by_cases h : a = 0 <;> simp [h]

/-- The perturbation vector is multiplied by the shift sign under the phase shift. -/
lemma perturbationVector_phaseShift (a : Fin 2) (i : Fin 48) (m : ZMod 48) :
    perturbationVector (phaseShift m (a, i)) = altSign m * perturbationVector (a, i) := by
  rw [phaseShift_pair,
    perturbationVector_apply_mul a (Equiv.addRight (G := Fin 48) m i),
    perturbationVector_apply_mul a i, alternating_addRight]
  by_cases h : a = 0 <;> simp [h] <;> ring

/-- The rank-one perturbation term of the Gram matrix is invariant under the
phase shift. -/
lemma perturbationVector_phaseShift_mul (a b : Fin 2) (i j : Fin 48) (m : ZMod 48) :
    perturbationVector (phaseShift m (a, i)) * perturbationVector (phaseShift m (b, j)) =
      perturbationVector (a, i) * perturbationVector (b, j) := by
  rw [perturbationVector_phaseShift, perturbationVector_phaseShift,
    mul_mul_mul_comm, altSign_mul_self m, one_mul]

/-- Twice-shifted phases differ by the same cyclic displacement. -/
lemma addRight_sub_addRight (k l : Fin 48) (m : ZMod 48) :
    Equiv.addRight (G := Fin 48) m l - Equiv.addRight (G := Fin 48) m k = l - k := by
  have h : toPhase (Equiv.addRight (G := Fin 48) m l) -
      toPhase (Equiv.addRight (G := Fin 48) m k) = toPhase l - toPhase k := by
    rw [toPhase_addRight, toPhase_addRight]
    abel
  exact h

/-- The integer part of the Gram matrix is invariant under the phase shift. -/
lemma integerMatrix_phaseShift (a b : Fin 2) (i j : Fin 48) (m : ZMod 48) :
    integerMatrix (phaseShift m (a, i)) (phaseShift m (b, j)) = integerMatrix (a, i) (b, j) := by
  simp only [phaseShift_pair, integerMatrix_apply, circulant_apply, addRight_sub_addRight]

/-- The period-48 Gram matrix is invariant under the phase shift. -/
lemma gramMatrix_phaseShift (m : ZMod 48) (x y : Fin 2 × Fin 48) :
    gramMatrix (phaseShift m x) (phaseShift m y) = gramMatrix x y := by
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  have hiff : (phaseShift m (a, i) = phaseShift m (b, j)) ↔ ((a, i) = (b, j)) :=
    (phaseShift m).apply_eq_iff_eq
  simp only [gramMatrix, hiff, integerMatrix_phaseShift, mul_assoc,
    perturbationVector_phaseShift_mul]

/-- A support is the Gram pairing `zᵀ H w` of the block normal and the tested
vector. -/
theorem support_def (b : Fin 2) (γ : ℝ) (i d : ZMod 48) :
    support b γ i d =
      dotProduct (normal b γ i) (gramMatrix.mulVec (testVector b i d)) :=
  -- Definitional: the right-hand side is the defining body of `support`.
  rfl

/-- Supports are cyclically invariant in the phase, so the phase-zero
expressions determine all of them. -/
theorem supportCyclic (b : Fin 2) (γ : ℝ) (i d : ZMod 48) :
    support b γ i d = support b γ 0 d := by
  -- The shifted Gram matrix is unchanged, so only the normal and the tested vector move.
  have hmv : ∀ x : Fin 2 × Fin 48,
      (gramMatrix.mulVec (testVector b i d)) (phaseShift i x) =
        (gramMatrix.mulVec (testVector b 0 d)) x := by
    intro x
    rw [Matrix.mulVec_apply, Matrix.mulVec_apply]
    simp only [Matrix.row, dotProduct]
    rw [← Equiv.sum_comp (phaseShift i)]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [gramMatrix_phaseShift, testVector_phaseShift, sub_self]
  -- Reindex the pairing along the phase shift, then evaluate pointwise.
  rw [support_def, support_def]
  rw [show dotProduct (normal b γ i) (gramMatrix.mulVec (testVector b i d))
      = ∑ x, normal b γ i x * (gramMatrix.mulVec (testVector b i d)) x from rfl,
    ← Equiv.sum_comp (phaseShift i)]
  rw [show dotProduct (normal b γ 0) (gramMatrix.mulVec (testVector b 0 d))
      = ∑ x, normal b γ 0 x * (gramMatrix.mulVec (testVector b 0 d)) x from rfl]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [normal_phaseShift, sub_self, hmv]

/-- There are `96` phase-zero support expressions: `2` blocks times `48`
displacements. -/
theorem phaseZeroTest_card : Fintype.card (Fin 2 × ZMod 48) = 96 := by
  -- Count the two blocks and the 48 phases separately.
  rw [Fintype.card_prod, Fintype.card_fin, ZMod.card]

/-- The `96` phase-zero expressions give all `4608` block-phase-displacement
supports. -/
theorem supportTest_card : Fintype.card (Fin 2 × ZMod 48 × ZMod 48) = 4608 := by
  -- Count the block, the phase, and the displacement separately.
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, ZMod.card]

/-- At a fixed phase and displacement the support is affine in the multiplier
factor `γ`, with slope the difference of its values at `1` and `0`. -/
lemma support_affine_phase (b : Fin 2) (γ : ℝ) (i d : ZMod 48) :
    support b γ i d = support b 0 i d + γ * (support b 1 i d - support b 0 i d) := by
  -- Split the normal into its `γ = 0` part and `γ` times its slope, then use bilinearity.
  rw [support_def, support_def, support_def, normal_eq_affine, dotProduct_add_left,
    dotProduct_smul_left, dotProduct_sub_left]

/-- Every support is affine in the multiplier factor `γ`, determined by its value
at the critical factor `γ̂` and its slope there. -/
theorem support_affine (b : Fin 2) (γ : ℝ) (i d : ZMod 48) :
    support b γ i d =
      supportAtCritical b d + (γ - criticalFactor) * supportSlope b d := by
  -- Evaluate the affine dependence at `γ̂` and at `γ̂ + 1`.
  have hcrit : support b criticalFactor 0 d =
      support b 0 0 d + criticalFactor * (support b 1 0 d - support b 0 0 d) :=
    support_affine_phase b criticalFactor 0 d
  have hslope : supportSlope b d = support b 1 0 d - support b 0 0 d := by
    rw [supportSlope, support_affine_phase b (criticalFactor + 1) 0 d, hcrit]
    ring
  rw [supportCyclic, support_affine_phase, supportAtCritical, hcrit, hslope]
  ring

/-! ## Entrywise evaluations of the Gram matrix and of the coefficient pairing -/

/-- Two block coordinates with the same block are equal exactly when their phases
agree. -/
lemma blockCoord_eq_iff (a : Fin 2) (i j : ZMod 48) :
    (blockCoord a i = blockCoord a j) ↔ (i = j) :=
  ⟨fun h ↦ (Prod.mk.inj h).2, fun h ↦ by rw [h]⟩

/-- The indicator that two same-block coordinates agree only sees the phases. -/
lemma blockCoord_ite (a : Fin 2) (i j : ZMod 48) (x y : ℝ) :
    (if blockCoord a i = blockCoord a j then x else y) = (if i = j then x else y) := by
  by_cases h : i = j
  · rw [if_pos ((blockCoord_eq_iff a i j).mpr h), if_pos h]
  · rw [if_neg (fun hh ↦ h ((blockCoord_eq_iff a i j).mp hh)), if_neg h]

/-- The cyclic predecessor of the phase `0` is the phase `-1`. -/
lemma zero_sub_one_zmod : (0 : ZMod 48) - 1 = -1 := by
  rw [sub_eq_add_neg, zero_add]

/-- The unscaled integer matrix has the row `p` from the first block to the first
block. -/
lemma integerMatrix_block_zero_zero (i j : ZMod 48) :
    integerMatrix (blockCoord 0 i) (blockCoord 0 j) = p (j - i) :=
  -- Definitional: the four block cases are the four branches of `integerMatrix`.
  rfl

/-- The unscaled integer matrix has the row `c` from the first block to the second
block. -/
lemma integerMatrix_block_zero_one (i j : ZMod 48) :
    integerMatrix (blockCoord 0 i) (blockCoord 1 j) = c (j - i) :=
  rfl

/-- The unscaled integer matrix has the row `c` from the second block to the first
block. -/
lemma integerMatrix_block_one_zero (i j : ZMod 48) :
    integerMatrix (blockCoord 1 i) (blockCoord 0 j) = c (i - j) :=
  rfl

/-- The unscaled integer matrix has the row `q` from the second block to the second
block. -/
lemma integerMatrix_block_one_one (i j : ZMod 48) :
    integerMatrix (blockCoord 1 i) (blockCoord 1 j) = q (j - i) :=
  rfl

/-- Entrywise evaluation of the Gram matrix in the first block at the first block. -/
lemma gramMatrix_block_zero_zero (i j : ZMod 48) :
    gramMatrix (blockCoord 0 i) (blockCoord 0 j) =
      2 * (p (j - i) : ℝ) - (if i = j then (1 : ℝ) else 0) +
        3 * sigma * sigma * alternating i * alternating j := by
  rw [gramMatrix_apply, blockCoord_ite, integerMatrix_block_zero_zero]
  simp only [perturbationVector, blockCoord, ↓reduceIte]
  by_cases h : i = j
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

/-- Entrywise evaluation of the Gram matrix from the first block to the second
block; the two blocks have different indices, so no diagonal correction occurs. -/
lemma gramMatrix_block_zero_one (i j : ZMod 48) :
    gramMatrix (blockCoord 0 i) (blockCoord 1 j) =
      2 * (c (j - i) : ℝ) - 3 * sigma * gammaZero * alternating i * alternating j := by
  rw [gramMatrix_apply, integerMatrix_block_zero_one]
  have hne : ¬ (blockCoord 0 i = blockCoord 1 j) := by
    intro h
    exact absurd (Prod.mk.inj h).1 (by decide)
  rw [if_neg hne]
  simp only [perturbationVector, blockCoord, if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
    ↓reduceIte]
  ring

/-- Entrywise evaluation of the Gram matrix from the second block to the first
block; the two blocks have different indices, so no diagonal correction occurs. -/
lemma gramMatrix_block_one_zero (i j : ZMod 48) :
    gramMatrix (blockCoord 1 i) (blockCoord 0 j) =
      2 * (c (i - j) : ℝ) - 3 * gammaZero * sigma * alternating i * alternating j := by
  rw [gramMatrix_apply, integerMatrix_block_one_zero]
  have hne : ¬ (blockCoord 1 i = blockCoord 0 j) := by
    intro h
    exact absurd (Prod.mk.inj h).1 (by decide)
  rw [if_neg hne]
  simp only [perturbationVector, blockCoord, if_neg (by decide : ¬ ((1 : Fin 2) = 0)),
    ↓reduceIte]
  ring

/-- Entrywise evaluation of the Gram matrix in the second block at the second
block. -/
lemma gramMatrix_block_one_one (i j : ZMod 48) :
    gramMatrix (blockCoord 1 i) (blockCoord 1 j) =
      2 * (q (j - i) : ℝ) - (if i = j then (1 : ℝ) else 0) +
        3 * gammaZero * gammaZero * alternating i * alternating j := by
  rw [gramMatrix_apply, blockCoord_ite, integerMatrix_block_one_one]
  simp only [perturbationVector, blockCoord, if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  by_cases h : i = j
  · rw [if_pos h]; ring
  · rw [if_neg h]; ring

/-! ### Row evaluations of the Gram matrix -/

/-- Applying the Gram matrix to a first-block basis vector reads off the
corresponding entry. -/
lemma mulVec_eta_coord (cc : Fin 2 × Fin 48) (i : ZMod 48) :
    (gramMatrix.mulVec (eta i)) cc = gramMatrix cc (blockCoord 0 i) := by
  rw [eta_eq_single, Matrix.mulVec_single_one]
  -- The single-column vector is read off at `cc` itself.
  rfl

/-- Applying the Gram matrix to a second-block basis vector reads off the
corresponding entry. -/
lemma mulVec_nu_coord (cc : Fin 2 × Fin 48) (i : ZMod 48) :
    (gramMatrix.mulVec (nu i)) cc = gramMatrix cc (blockCoord 1 i) := by
  rw [nu_eq_single, Matrix.mulVec_single_one]
  rfl

/-- Applying the Gram matrix to the scaled basis vector `wᵢ` reads off the
corresponding entry, scaled by `γ₀⁻¹`. -/
lemma mulVec_w_coord (cc : Fin 2 × Fin 48) (i : ZMod 48) :
    (gramMatrix.mulVec (w i)) cc = gammaZero⁻¹ * gramMatrix cc (blockCoord 1 i) := by
  rw [w, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mulVec_nu_coord]

/-- Applying the Gram matrix to the first-block vertex `ξᵢ` reads off the three
entries attached to `ηᵢ`, `νᵢ`, and `νᵢ₋₁`. -/
lemma mulVec_xi_coord (cc : Fin 2 × Fin 48) (i : ZMod 48) :
    (gramMatrix.mulVec (xi i)) cc =
      gramMatrix cc (blockCoord 0 i) +
        gammaZero⁻¹ * (gramMatrix cc (blockCoord 1 i) - gramMatrix cc (blockCoord 1 (i - 1))) := by
  rw [xi, rho, Matrix.mulVec_add, Matrix.mulVec_sub]
  simp only [Pi.add_apply, Pi.sub_apply, mulVec_eta_coord, mulVec_w_coord]
  ring

/-! ### Pairings with the coefficient vertices and normals -/

/-- The coefficient pairing is negated in its left argument. -/
lemma dotProduct_neg_left (f g : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (-f) g = -dotProduct f g := by
  rw [← neg_one_smul ℝ f, dotProduct_smul_left]
  ring

/-- Pairing with the first-block basis vector `ηᵢ` reads off its coordinate. -/
lemma dotProduct_eta (i : ZMod 48) (y : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (eta i) y = y (blockCoord 0 i) := by
  rw [eta_eq_single, dotProduct_single_one]

/-- Pairing with the scaled second-block basis vector `wᵢ` reads off its
coordinate scaled by `γ₀⁻¹`. -/
lemma dotProduct_w (i : ZMod 48) (y : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (w i) y = gammaZero⁻¹ * y (blockCoord 1 i) := by
  rw [w, dotProduct_smul_left, nu_eq_single, dotProduct_single_one]

/-- Pairing with the first-block vertex `ξᵢ` reads off its three coordinates. -/
lemma dotProduct_xi (i : ZMod 48) (y : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (xi i) y =
      y (blockCoord 0 i) + gammaZero⁻¹ * (y (blockCoord 1 i) - y (blockCoord 1 (i - 1))) := by
  rw [xi, rho, dotProduct_add_left, dotProduct_sub_left, dotProduct_eta, dotProduct_w,
    dotProduct_w]
  ring

/-- Pairing with the first-block normal `aᵢ(γ)` reads off its three coordinates. -/
lemma dotProduct_firstNormal (γ : ℝ) (i : ZMod 48) (y : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (firstNormal γ i) y =
      y (blockCoord 0 (i - 1)) - γ * gammaZero⁻¹ * y (blockCoord 1 (i - 1)) -
        (y (blockCoord 0 i) + gammaZero⁻¹ * (y (blockCoord 1 i) - y (blockCoord 1 (i - 1)))) := by
  rw [firstNormal, dotProduct_sub_left, dotProduct_sub_left, dotProduct_eta,
    dotProduct_smul_left, dotProduct_w, dotProduct_xi]
  ring

/-- Pairing with the second-block normal `cᵢ(γ)` reads off its two coordinates. -/
lemma dotProduct_secondNormal (γ : ℝ) (i : ZMod 48) (y : (Fin 2 × Fin 48) → ℝ) :
    dotProduct (secondNormal γ i) y =
      γ * gammaZero⁻¹ * y (blockCoord 1 (i - 1)) + gammaZero⁻¹ * y (blockCoord 1 i) -
        gammaZero⁻¹ * y (blockCoord 1 (i - 1)) := by
  rw [secondNormal, rho, dotProduct_add_left, dotProduct_sub_left, dotProduct_smul_left]
  simp only [dotProduct_w]
  ring

/-! ### Alternating-vector evaluations -/

/-- The alternating vector is the cast of the integer sign `(-1) ^ i.val`. -/
lemma alternating_eq_intCast (i : ZMod 48) : alternating i = (((-1 : ℤ) ^ i.val : ℤ) : ℝ) := by
  unfold alternating
  push_cast
  congr 1

/-- The value of the phase index `-1` in `Fin 48`. -/
lemma val_negOne_zmod : ((-1 : ZMod 48)).val = 47 := by decide

/-- The alternating vector at the phase `-1`. -/
lemma alternating_negOne : alternating (-1 : ZMod 48) = -1 := by
  rw [alternating_eq_intCast, val_negOne_zmod]
  norm_num

/-- The alternating vector at the phase `0`. -/
lemma alternating_zero : alternating (0 : ZMod 48) = 1 := by
  rw [alternating_eq_intCast]
  norm_num

/-! ### Normals of the phase-zero support family -/

/-- Over one unit of the multiplier factor the first-block normal at phase zero
decreases by `w(-1)`. -/
lemma firstNormal_slope_zero :
    firstNormal (criticalFactor + 1) 0 - firstNormal criticalFactor 0 = -w (-1 : ZMod 48) := by
  funext p
  simp only [firstNormal, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul,
    zero_sub_one_zmod]
  ring

/-- Over one unit of the multiplier factor the second-block normal at phase zero
increases by `w(-1)`. -/
lemma secondNormal_slope_zero :
    secondNormal (criticalFactor + 1) 0 - secondNormal criticalFactor 0 = w (-1 : ZMod 48) := by
  funext p
  simp only [secondNormal, rho, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    zero_sub_one_zmod]
  ring

/-! ### Phase-zero support reductions -/

/-- The phase-zero first-block slope at displacement zero is the scaled first
coordinate of the Gram vector of `ξ₀`. -/
lemma supportSlope_zero_zero :
    supportSlope 0 0 = -gammaZero⁻¹ * ((gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1))) := by
  rw [supportSlope, support_def, support_def, normal_zero, normal_zero, ← dotProduct_sub_left,
    firstNormal_slope_zero, testVector_eq_origin, vertex_zero, dotProduct_neg_left, dotProduct_w]
  ring

/-- The phase-zero first-block slope at a nonzero displacement is the scaled drop
of the first coordinate of the Gram vector of `ξ` between phases `0` and `d`. -/
lemma supportSlope_zero_of_ne (d : ZMod 48) (hd : d ≠ 0) :
    supportSlope 0 d = -gammaZero⁻¹ *
      ((gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1)) -
        (gramMatrix.mulVec (xi d)) (blockCoord 1 (-1))) := by
  rw [supportSlope, support_def, support_def, normal_zero, normal_zero, ← dotProduct_sub_left,
    firstNormal_slope_zero, testVector_eq_diff 0 0 d hd, zero_add, dotProduct_neg_left,
    dotProduct_w, Matrix.mulVec_sub]
  simp only [Pi.sub_apply, vertex_zero]
  ring

/-- The phase-zero second-block slope at displacement zero is the scaled entry of
the Gram matrix from `(1, -1)` to `(0, 0)`. -/
lemma supportSlope_one_zero :
    supportSlope 1 0 = gammaZero⁻¹ * gramMatrix (blockCoord 1 (-1)) (blockCoord 0 0) := by
  rw [supportSlope, support_def, support_def, normal_one, normal_one, ← dotProduct_sub_left,
    secondNormal_slope_zero, testVector_eq_origin, vertex_one, dotProduct_w, mulVec_eta_coord]

/-- The phase-zero second-block slope at a nonzero displacement is the scaled drop
of the Gram entry from `(1, -1)` to `(0, ·)` between phases `0` and `d`. -/
lemma supportSlope_one_of_ne (d : ZMod 48) (hd : d ≠ 0) :
    supportSlope 1 d = gammaZero⁻¹ *
      (gramMatrix (blockCoord 1 (-1)) (blockCoord 0 0) -
        gramMatrix (blockCoord 1 (-1)) (blockCoord 0 d)) := by
  rw [supportSlope, support_def, support_def, normal_one, normal_one, ← dotProduct_sub_left,
    secondNormal_slope_zero, testVector_eq_diff 1 0 d hd, zero_add, dotProduct_w,
    Matrix.mulVec_sub]
  simp only [Pi.sub_apply, vertex_one, mulVec_eta_coord]

/-- The phase-zero first-block support at the critical factor and displacement
zero is the first-coordinate functional of the Gram vector of `ξ₀`. -/
lemma supportAtCritical_zero_zero :
    supportAtCritical 0 0 = (gramMatrix.mulVec (xi 0)) (blockCoord 0 (-1)) -
      criticalFactor * gammaZero⁻¹ * (gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1)) -
      ((gramMatrix.mulVec (xi 0)) (blockCoord 0 0) +
        gammaZero⁻¹ * ((gramMatrix.mulVec (xi 0)) (blockCoord 1 0) -
          (gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1)))) := by
  rw [supportAtCritical, support_def, normal_zero, testVector_eq_origin, vertex_zero,
    dotProduct_firstNormal, zero_sub_one_zmod]

/-- The phase-zero first-block support at the critical factor and a nonzero
displacement is the first-coordinate functional of the drop of the Gram vector of
`ξ` between phases `0` and `d`. -/
lemma supportAtCritical_zero_of_ne (d : ZMod 48) (hd : d ≠ 0) :
    supportAtCritical 0 d =
      ((gramMatrix.mulVec (xi 0)) (blockCoord 0 (-1)) -
          (gramMatrix.mulVec (xi d)) (blockCoord 0 (-1))) -
        criticalFactor * gammaZero⁻¹ *
          ((gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1)) -
            (gramMatrix.mulVec (xi d)) (blockCoord 1 (-1))) -
        (((gramMatrix.mulVec (xi 0)) (blockCoord 0 0) -
            (gramMatrix.mulVec (xi d)) (blockCoord 0 0)) +
          gammaZero⁻¹ *
            (((gramMatrix.mulVec (xi 0)) (blockCoord 1 0) -
                (gramMatrix.mulVec (xi d)) (blockCoord 1 0)) -
              ((gramMatrix.mulVec (xi 0)) (blockCoord 1 (-1)) -
                (gramMatrix.mulVec (xi d)) (blockCoord 1 (-1))))) := by
  rw [supportAtCritical, support_def, normal_zero, testVector_eq_diff 0 0 d hd, zero_add,
    dotProduct_firstNormal, zero_sub_one_zmod, Matrix.mulVec_sub]
  simp only [Pi.sub_apply, vertex_zero]

/-- The phase-zero second-block support at the critical factor and displacement
zero is the second-coordinate functional of the Gram vector of `η₀`. -/
lemma supportAtCritical_one_zero :
    supportAtCritical 1 0 = gammaZero⁻¹ *
      ((criticalFactor - 1) * gramMatrix (blockCoord 1 (-1)) (blockCoord 0 0) +
        gramMatrix (blockCoord 1 0) (blockCoord 0 0)) := by
  rw [supportAtCritical, support_def, normal_one, testVector_eq_origin, vertex_one,
    dotProduct_secondNormal, zero_sub_one_zmod, mulVec_eta_coord, mulVec_eta_coord]
  ring

/-- The phase-zero second-block support at the critical factor and a nonzero
displacement is the second-coordinate functional of the drop of the Gram vector of
`η` between phases `0` and `d`. -/
lemma supportAtCritical_one_of_ne (d : ZMod 48) (hd : d ≠ 0) :
    supportAtCritical 1 d = gammaZero⁻¹ *
      ((criticalFactor - 1) * (gramMatrix (blockCoord 1 (-1)) (blockCoord 0 0) -
          gramMatrix (blockCoord 1 (-1)) (blockCoord 0 d)) +
        (gramMatrix (blockCoord 1 0) (blockCoord 0 0) -
          gramMatrix (blockCoord 1 0) (blockCoord 0 d))) := by
  rw [supportAtCritical, support_def, normal_one, testVector_eq_diff 1 0 d hd, zero_add,
    dotProduct_secondNormal, zero_sub_one_zmod, Matrix.mulVec_sub]
  simp only [Pi.sub_apply, vertex_one, mulVec_eta_coord]
  ring

/-! ### Integer certificates for the phase-zero support quantities -/

/-- The integer sign `(-1) ^ i.val` attached to a phase. -/
def altInt (i : ZMod 48) : ℤ := (-1 : ℤ) ^ i.val

/-- The alternating vector is the real cast of the integer sign `altInt`. -/
lemma alternating_eq_altInt (i : ZMod 48) : alternating i = (altInt i : ℝ) := by
  -- Unfold the integer sign and read off the defining cast.
  rw [altInt]
  exact alternating_eq_intCast i

/-- The integer sign flips at the predecessor phase. -/
lemma altInt_sub_one (i : ZMod 48) : altInt (i - 1) = -altInt i := by
  -- Enumerate the 48 phases; each case is an explicit integer identity.
  fin_cases i <;> decide

/-- The alternating vector flips sign at the predecessor phase, in the cyclic
phase spelling. -/
lemma alternating_sub_one_phase (i : ZMod 48) : alternating (i - 1 : ZMod 48) = -alternating i := by
  -- Route correction: the unrestricted spelling `i - 1` asks Lean for a subtraction
  -- of `Fin 48` from `ZMod 48`, so the index is pinned to `ZMod 48` here.  The relation
  -- itself is the `Fin 48`-spelled one already proved for the alternating vector.
  exact alternating_sub_one_eq_neg i

/-- The integer sign at the phase `0` is `1`. -/
lemma altInt_zero : altInt (0 : ZMod 48) = 1 := by decide

/-- The integer sign at the phase `-1` is `-1`. -/
lemma altInt_negOne : altInt (-1 : ZMod 48) = -1 := by decide

/-! ### Row entries of the Gram vector of `ξ` -/

/-- The `(0, -1)` coordinate of the Gram vector of `ξᵢ`, expanded in the integer
rows `p`, `c` and the rank-one perturbation `σσ`. -/
lemma mulVec_xi_block_zero_negOne (i : ZMod 48) :
    (gramMatrix.mulVec (xi i)) (blockCoord 0 (-1)) =
      2 * (p (i + 1 : ZMod 48) : ℝ) - (if (-1 : ZMod 48) = i then 1 else 0) -
        3 * sigma * sigma * alternating i +
        gammaZero⁻¹ *
          (2 * (c (i + 1 : ZMod 48) : ℝ) + 3 * sigma * gammaZero * alternating i -
            (2 * (c i : ℝ) - 3 * sigma * gammaZero * alternating i)) := by
  -- Expand the `ξ` row through `η`, `ν`, and `ν₋₁`, then evaluate the three Gram entries.
  rw [mulVec_xi_coord, gramMatrix_block_zero_zero, gramMatrix_block_zero_one,
    gramMatrix_block_zero_one, alternating_negOne, alternating_sub_one_phase i]
  simp only [sub_neg_eq_add, sub_add_cancel]
  ring

/-- The `(0, 0)` coordinate of the Gram vector of `ξᵢ`, expanded in the integer
rows `p`, `c` and the rank-one perturbation. -/
lemma mulVec_xi_block_zero_zero (i : ZMod 48) :
    (gramMatrix.mulVec (xi i)) (blockCoord 0 0) =
      2 * (p i : ℝ) - (if (0 : ZMod 48) = i then 1 else 0) +
        3 * sigma * sigma * alternating i +
        gammaZero⁻¹ *
          (2 * (c i : ℝ) - 3 * sigma * gammaZero * alternating i -
            (2 * (c (i - 1 : ZMod 48) : ℝ) + 3 * sigma * gammaZero * alternating i)) := by
  -- Expand the `ξ` row and clear the cyclic indices `i - 0` and `i - 1 - 0`.
  rw [mulVec_xi_coord, gramMatrix_block_zero_zero, gramMatrix_block_zero_one,
    gramMatrix_block_zero_one, alternating_zero, alternating_sub_one_phase i]
  simp only [sub_zero]
  ring

/-- The `(1, -1)` coordinate of the Gram vector of `ξᵢ`, expanded in the integer
rows `q`, `c` and the rank-one perturbation. -/
lemma mulVec_xi_block_one_negOne (i : ZMod 48) :
    (gramMatrix.mulVec (xi i)) (blockCoord 1 (-1)) =
      2 * (c ((-1 : ZMod 48) - i) : ℝ) + 3 * gammaZero * sigma * alternating i +
        gammaZero⁻¹ *
          (2 * (q (i + 1 : ZMod 48) : ℝ) - (if (-1 : ZMod 48) = i then 1 else 0) -
              3 * gammaZero * gammaZero * alternating i -
            (2 * (q i : ℝ) -
              (if (-1 : ZMod 48) = (i - 1 : ZMod 48) then 1 else 0) +
                3 * gammaZero * gammaZero * alternating i)) := by
  -- Expand the `ξ` row and evaluate the `(1, -1)`, `(1, i)`, `(1, i-1)` entries.
  rw [mulVec_xi_coord, gramMatrix_block_one_zero, gramMatrix_block_one_one,
    gramMatrix_block_one_one, alternating_negOne, alternating_sub_one_phase i]
  simp only [sub_neg_eq_add, sub_add_cancel]
  ring

/-- The `(1, 0)` coordinate of the Gram vector of `ξᵢ`, expanded in the integer
rows `q`, `c` and the rank-one perturbation. -/
lemma mulVec_xi_block_one_zero (i : ZMod 48) :
    (gramMatrix.mulVec (xi i)) (blockCoord 1 0) =
      2 * (c (-i) : ℝ) - 3 * gammaZero * sigma * alternating i +
        gammaZero⁻¹ *
          (2 * (q i : ℝ) - (if (0 : ZMod 48) = i then 1 else 0) +
              3 * gammaZero * gammaZero * alternating i -
            (2 * (q (i - 1 : ZMod 48) : ℝ) -
              (if (0 : ZMod 48) = (i - 1 : ZMod 48) then 1 else 0) -
                3 * gammaZero * gammaZero * alternating i)) := by
  -- Expand the `ξ` row and evaluate the `(1, 0)`, `(1, i)`, `(1, i-1)` entries.
  rw [mulVec_xi_coord, gramMatrix_block_one_zero, gramMatrix_block_one_one,
    gramMatrix_block_one_one, alternating_zero, alternating_sub_one_phase i]
  simp only [sub_zero, zero_sub]
  ring

/-! ### Integral certificates of the phase-zero support values and slopes -/

/-- The integral certificate attached to phase `i` for the phase-zero first-block
support slope: the difference of the certificates at phases `0` and `d` is
`23849359428855816000` times `supportSlope 0 d`. -/
def firstSlopeAtom (i : ZMod 48) : ℤ :=
  -25277540465136000000 * c ((-1 : ZMod 48) - i) +
    69526436563202442759 * altInt i +
    13395622928000000000 * q i -
    13395622928000000000 * q (i + 1 : ZMod 48) +
    6697811464000000000 * (if (-1 : ZMod 48) = i then 1 else 0) -
    6697811464000000000 * (if (-1 : ZMod 48) = (i - 1 : ZMod 48) then 1 else 0)

/-- The integral certificate of the phase-zero first-block support slope at
displacement `d`, obtained as the drop of `firstSlopeAtom` between phases `0`
and `d` (with the phase-zero certificate alone at `d = 0`). -/
def firstSlopeNum (d : ZMod 48) : ℤ :=
  if d = 0 then firstSlopeAtom 0 else firstSlopeAtom 0 - firstSlopeAtom d

/-- The integral certificate of the phase-zero second-block support slope at
displacement `d`, obtained as the drop of `q` at the phase shift `-1` together
with the alternating-sign correction `1 - (-1) ^ d.val`. -/
def secondSlopeNum (d : ZMod 48) : ℤ :=
  if d = 0 then
    2 * 1000 * 6697811464000 * c ((-1 : ZMod 48) : Fin 48) + 3 * 6887062879763 * 1887
  else
    2 * 1000 * 6697811464000 * (c ((-1 : ZMod 48) : Fin 48) - c ((-1 : ZMod 48) - d)) +
      3 * 6887062879763 * 1887 * (1 - (-1 : ℤ) ^ d.val)

/-- The integral certificate attached to phase `i` for the phase-zero first-block
support at the critical multiplier factor. -/
def firstValueAtom (i : ZMod 48) : ℤ :=
  1837883820883040509945990153214072000000 * (if (0 : ZMod 48) = i then 1 else 0) -
    402976739423338588283245688000000000000 *
      (if (0 : ZMod 48) = (i - 1 : ZMod 48) then 1 else 0) -
    1077484118980673623216960631648072000000 * (if (-1 : ZMod 48) = i then 1 else 0) -
    357422962479028298445783833566000000000 *
      (if (-1 : ZMod 48) = (i - 1 : ZMod 48) then 1 else 0) +
    8129699184921088267193630139496236432573 * altInt i -
    1348914260395852798334388187878084000000 * c ((-1 : ZMod 48) - i) -
    1520834214583679832180969226512000000000 * c (-i) -
    3041668429167359664361938453024000000000 * c i +
    1520834214583679832180969226512000000000 * c (i + 1 : ZMod 48) +
    1520834214583679832180969226512000000000 * c (i - 1 : ZMod 48) -
    2869814162919403843325488930428144000000 * p i +
    2869814162919403843325488930428144000000 * p (i + 1 : ZMod 48) -
    91107553888620579674923708868000000000 * q i -
    714845924958056596891567667132000000000 * q (i + 1 : ZMod 48) +
    805953478846677176566491376000000000000 * q (i - 1 : ZMod 48)

/-- The integral certificate of the phase-zero first-block support at the critical
multiplier factor, at displacement `d`. -/
def firstValueNum (d : ZMod 48) : ℤ :=
  if d = 0 then firstValueAtom 0 else firstValueAtom 0 - firstValueAtom d

/-- The integral certificate attached to phase `i` for the phase-zero second-block
support at the critical multiplier factor. -/
def secondValueAtom (i : ZMod 48) : ℤ :=
  3850587831818621888000000000 * c (-i) +
    3415305092060114623216000000 * c ((-1 : ZMod 48) - i) -
    1266880744721117263419972279 * altInt i

/-- The integral certificate of the phase-zero second-block support at the critical
multiplier factor, at displacement `d`. -/
def secondValueNum (d : ZMod 48) : ℤ :=
  if d = 0 then secondValueAtom 0 else secondValueAtom 0 - secondValueAtom d

/-! ### Certificates of the phase-zero support quantities -/

/-- `23849359428855816000` times the phase-zero first-block support slope is the
drop of the integral certificate between phases `0` and `d`. -/
lemma supportSlope_zero_num (d : ZMod 48) :
    (23849359428855816000 : ℝ) * supportSlope 0 d = (firstSlopeNum d : ℝ) := by
  by_cases hd : d = 0
  · -- At zero displacement only the phase-zero certificate contributes.
    subst hd
    rw [firstSlopeNum, if_pos rfl, supportSlope_zero_zero, mulVec_xi_block_one_negOne,
      firstSlopeAtom, gammaZero_eq, sigma_eq, alternating_eq_altInt (0 : ZMod 48)]
    rw [altInt_zero]
    push_cast
    ring
  · -- At nonzero displacement the slope is the drop of the phase-`d` certificate.
    rw [firstSlopeNum, if_neg hd, supportSlope_zero_of_ne d hd]
    -- `rw` fixes a single instantiation of a definition and would therefore unfold only
    -- the phase-`0` copy of the atom; `simp only` unfolds every occurrence.
    simp only [firstSlopeAtom]
    -- Expanding the two Gram vectors of `xi` one phase at a time keeps the goal well typed.
    simp only [mulVec_xi_block_one_negOne]
    -- Evaluate the constant guards, the Gram-introduced `sigma`, and the sign vector.
    simp only [gammaZero_eq, sigma_eq, alternating_eq_altInt, altInt_zero, zero_add, sub_zero]
    push_cast
    ring

/-- `1887 * 6697811464000` times the phase-zero second-block support slope is the
drop of the integral certificate between phases `0` and `d`. -/
lemma supportSlope_one_num (d : ZMod 48) :
    (1887 * 6697811464000 : ℝ) * supportSlope 1 d = (secondSlopeNum d : ℝ) := by
  by_cases hd : d = 0
  · subst hd
    rw [secondSlopeNum, if_pos rfl, supportSlope_one_zero, gramMatrix_block_one_zero,
      alternating_negOne, alternating_zero, sub_zero, gammaZero_eq, sigma_eq]
    push_cast
    ring
  · rw [secondSlopeNum, if_neg hd, supportSlope_one_of_ne d hd, gramMatrix_block_one_zero,
      gramMatrix_block_one_zero, alternating_eq_intCast d, alternating_negOne, alternating_zero,
      sub_zero, gammaZero_eq, sigma_eq]
    push_cast
    ring

/-- `1434907081459701921662744465214072000000` times the phase-zero first-block
support at the critical factor is the drop of its integral certificate between
phases `0` and `d`. -/
lemma supportAtCritical_zero_num (d : ZMod 48) :
    (1434907081459701921662744465214072000000 : ℝ) * supportAtCritical 0 d =
      (firstValueNum d : ℝ) := by
  by_cases hd : d = 0
  · -- At zero displacement only the phase-zero certificate contributes.
    subst hd
    rw [firstValueNum, if_pos rfl, supportAtCritical_zero_zero, mulVec_xi_block_zero_negOne,
      mulVec_xi_block_one_negOne, mulVec_xi_block_zero_zero, mulVec_xi_block_one_zero,
      firstValueAtom, criticalFactor_eq, gammaZero_eq, sigma_eq,
      alternating_eq_altInt (0 : ZMod 48)]
    rw [altInt_zero]
    push_cast
    ring
  · -- At nonzero displacement the value is the drop of the phase-`d` certificate.
    rw [firstValueNum, if_neg hd, supportAtCritical_zero_of_ne d hd]
    -- `rw` would fix one instantiation of the atom and unfold only its phase-`0` copy.
    simp only [firstValueAtom]
    -- Expanding the four Gram vectors of `xi` one entry at a time keeps the goal well typed.
    simp only [mulVec_xi_block_zero_negOne, mulVec_xi_block_one_negOne, mulVec_xi_block_zero_zero,
      mulVec_xi_block_one_zero]
    -- Evaluate the constant guards, the Gram-introduced `sigma`, and the sign vector.
    simp only [criticalFactor_eq, gammaZero_eq, sigma_eq, alternating_eq_altInt, altInt_zero,
      zero_add, sub_zero]
    push_cast
    ring

/-- `3633029619320869751328000000` times the phase-zero second-block support at the
critical factor is the drop of its integral certificate between phases `0` and `d`. -/
lemma supportAtCritical_one_num (d : ZMod 48) :
    (3633029619320869751328000000 : ℝ) * supportAtCritical 1 d =
      (secondValueNum d : ℝ) := by
  by_cases hd : d = 0
  · subst hd
    rw [secondValueNum, if_pos rfl, supportAtCritical_one_zero]
    -- Evaluate the two Gram entries only after `supportAtCritical_one_zero` produced them,
    -- and replace `sigma` only afterwards, since the entries introduce it.
    simp only [secondValueAtom, gramMatrix_block_one_zero]
    simp only [criticalFactor_eq, gammaZero_eq, sigma_eq, alternating_negOne, alternating_zero,
      altInt_zero, sub_zero, neg_zero]
    push_cast
    ring
  · rw [secondValueNum, if_neg hd, supportAtCritical_one_of_ne d hd]
    -- `rw` fixes one instantiation of the atom, so `simp only` is used to unfold it.
    simp only [secondValueAtom]
    -- Expanding the four Gram entries together keeps both sides in the same normal form.
    simp only [gramMatrix_block_one_zero]
    -- Evaluate the constant guards, the Gram-introduced `sigma`, and the sign vector.
    simp only [criticalFactor_eq, gammaZero_eq, sigma_eq, alternating_eq_altInt, altInt_negOne,
      altInt_zero, sub_zero, neg_zero, zero_sub]
    push_cast
    ring

/-! ### The four numerical support bounds -/

/-- Every first-block support slope exceeds `30000`. -/
theorem firstSlopeBound (d : ZMod 48) : (30000 : ℝ) < supportSlope 0 d := by
  -- Certify the bound on the integral certificate, then divide by its scale.
  have hb : 30000 * (23849359428855816000 : ℤ) < firstSlopeNum d := by
    fin_cases d <;> decide
  have hb' : (30000 : ℝ) * (23849359428855816000 : ℝ) < (firstSlopeNum d : ℝ) := by
    exact_mod_cast hb
  have hK : (0 : ℝ) < 23849359428855816000 := by norm_num
  have hgoal : (23849359428855816000 : ℝ) * 30000 <
      (23849359428855816000 : ℝ) * supportSlope 0 d := by
    rw [mul_comm (23849359428855816000 : ℝ) 30000, supportSlope_zero_num d]
    exact hb'
  exact lt_of_mul_lt_mul_left hgoal (le_of_lt hK)

/-- Every second-block support slope exceeds `20000`. -/
theorem secondSlopeBound (d : ZMod 48) : (20000 : ℝ) < supportSlope 1 d := by
  have hb : 20000 * (1887 * 6697811464000) < secondSlopeNum d := by
    fin_cases d <;> decide
  have hb' : (20000 : ℝ) * (1887 * 6697811464000) < (secondSlopeNum d : ℝ) := by
    exact_mod_cast hb
  have hK : (0 : ℝ) < 1887 * 6697811464000 := by norm_num
  have hgoal : (1887 * 6697811464000 : ℝ) * 20000 <
      (1887 * 6697811464000 : ℝ) * supportSlope 1 d := by
    rw [mul_comm (1887 * 6697811464000 : ℝ) 20000, supportSlope_one_num d]
    exact hb'
  exact lt_of_mul_lt_mul_left hgoal (le_of_lt hK)

/-- Apart from the displacement `-10`, every first-block support at the critical
factor exceeds `1 / 10`. -/
theorem firstValueBound (d : ZMod 48) (h : d ≠ (-10 : ZMod 48)) :
    (1 : ℝ) / 10 < supportAtCritical 0 d := by
  -- Certify the bound on the integral certificate; the single excluded
  -- displacement is the one where the certificate vanishes.
  have hb : (1434907081459701921662744465214072000000 : ℤ) < 10 * firstValueNum d := by
    -- `decide` cannot see the hypothesis `h` while enumerating the displacements, and the
    -- certificate vanishes at the excluded one.  So the excluded displacement is absorbed
    -- by a slack term that vanishes elsewhere and is positive there; `h` removes it again.
    have hcert : (1434907081459701921662744465214072000000 : ℤ) <
        10 * firstValueNum d +
          (if d = (-10 : ZMod 48) then 1434907081459701921662744465214072000001 else 0) := by
      fin_cases d <;> decide
    simpa only [if_neg h, add_zero] using hcert
  have hb' : (1434907081459701921662744465214072000000 : ℝ) < 10 * (firstValueNum d : ℝ) := by
    exact_mod_cast hb
  have hK : (0 : ℝ) < 1434907081459701921662744465214072000000 := by norm_num
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 10)]
  have hstep : (1434907081459701921662744465214072000000 : ℝ) * (1 : ℝ) <
      (1434907081459701921662744465214072000000 : ℝ) * (supportAtCritical 0 d * 10) := by
    have hprod : (1434907081459701921662744465214072000000 : ℝ) *
        (supportAtCritical 0 d * 10) = 10 * (firstValueNum d : ℝ) := by
      rw [← mul_assoc, supportAtCritical_zero_num d]
      ring
    rw [hprod, mul_one]
    exact hb'
  exact lt_of_mul_lt_mul_left hstep (le_of_lt hK)

/-- Every second-block support at the critical factor exceeds `2`. -/
theorem secondValueBound (d : ZMod 48) : (2 : ℝ) < supportAtCritical 1 d := by
  have hb : 2 * (3633029619320869751328000000 : ℤ) < secondValueNum d := by
    fin_cases d <;> decide
  have hb' : (2 : ℝ) * (3633029619320869751328000000 : ℝ) < (secondValueNum d : ℝ) := by
    exact_mod_cast hb
  have hK : (0 : ℝ) < 3633029619320869751328000000 := by norm_num
  have hgoal : (3633029619320869751328000000 : ℝ) * 2 <
      (3633029619320869751328000000 : ℝ) * supportAtCritical 1 d := by
    rw [mul_comm (3633029619320869751328000000 : ℝ) 2, supportAtCritical_one_num d]
    exact hb'
  exact lt_of_mul_lt_mul_left hgoal (le_of_lt hK)

/-! ### The exceptional displacement -/

/-- The first-block critical value at the exceptional displacement `-10` vanishes. -/
lemma supportAtCritical_zero_active : supportAtCritical 0 (-10 : ZMod 48) = 0 := by
  -- The integral certificate at this displacement is zero, and its scale is nonzero.
  have h := supportAtCritical_zero_num (-10 : ZMod 48)
  have hz : firstValueNum (-10 : ZMod 48) = 0 := by decide
  have h0 : (firstValueNum (-10 : ZMod 48) : ℝ) = 0 := by
    rw [hz]
    norm_num
  rw [h0] at h
  have hK : (1434907081459701921662744465214072000000 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left hK

/-- The first-block slope at the exceptional displacement `-10`. -/
lemma supportSlope_zero_active :
    supportSlope 0 (-10 : ZMod 48) = 287451196000 / 1186923 := by
  -- Read the slope off the integral certificate, which is the scaled value.
  have h := supportSlope_zero_num (-10 : ZMod 48)
  have hnum : firstSlopeNum (-10 : ZMod 48) = 5775881747727932832000000 := by decide
  have hcast : ((5775881747727932832000000 : ℤ) : ℝ) =
      (23849359428855816000 : ℝ) * (287451196000 / 1186923 : ℝ) := by
    push_cast
    norm_num
  rw [hnum, hcast] at h
  have hK : (23849359428855816000 : ℝ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ hK h

/-- The first-block support of displacement `-10` is the single exceptional
expression, equal to `(287451196000 / 1186923) (γ - γ̂)`. -/
theorem activeSupport (γ : ℝ) (i : ZMod 48) :
    support 0 γ i (-10 : ZMod 48) =
      (287451196000 / 1186923 : ℝ) * (γ - criticalFactor) := by
  -- Rotate the phase to `0`, apply the affine form, and insert the two evaluations.
  rw [supportCyclic 0 γ i (-10 : ZMod 48), support_affine 0 γ 0 (-10 : ZMod 48),
    supportAtCritical_zero_active, supportSlope_zero_active]
  ring

/-- Throughout the critical half-line `γ ≥ γ̂`, every origin test and every
nonself test of both blocks is nonnegative. -/
theorem allSupportsNonneg (γ : ℝ) (h : criticalFactor ≤ γ) :
    ∀ b : Fin 2, ∀ i d : ZMod 48, 0 ≤ support b γ i d := by
  -- On the critical half-line each support is a nonnegative endpoint plus a
  -- nonnegative multiple of a strictly positive slope.
  have hγ : 0 ≤ γ - criticalFactor := sub_nonneg.mpr h
  intro b i d
  have hslope0 : 0 < supportSlope 0 d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 30000) (le_of_lt (firstSlopeBound d))
  have hslope1 : 0 < supportSlope 1 d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 20000) (le_of_lt (secondSlopeBound d))
  have hvalue1 : 0 < supportAtCritical 1 d :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_of_lt (secondValueBound d))
  rw [support_affine]
  -- Split the block explicitly: `fin_cases` would leave the literal `b` in a
  -- spelling that blocks the rewrites below.
  by_cases hb : b = 0
  · subst hb
    by_cases hd : d = (-10 : ZMod 48)
    · subst hd
      rw [supportAtCritical_zero_active, zero_add]
      exact mul_nonneg hγ (le_of_lt hslope0)
    · have hvalue0 : 0 < supportAtCritical 0 d :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 10) (le_of_lt (firstValueBound d hd))
      exact add_nonneg (le_of_lt hvalue0) (mul_nonneg hγ (le_of_lt hslope0))
  · have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    exact add_nonneg (le_of_lt hvalue1) (mul_nonneg hγ (le_of_lt hslope1))

/-- Nonnegativity of the whole support family of a block is equivalent to
nonnegativity of the Gram pairings of its normals against each block vertex and
against every difference of two distinct block vertices. -/
theorem support_nonneg_iff_pairing (γ : ℝ) (b : Fin 2) :
    (∀ i d, 0 ≤ support b γ i d) ↔
      (∀ i, 0 ≤ dotProduct (normal b γ i) (gramMatrix.mulVec (vertex b i))) ∧
        ∀ i j, j ≠ i →
          0 ≤ dotProduct (normal b γ i)
            (gramMatrix.mulVec (vertex b i - vertex b j)) := by
  -- The family of tested vectors splits into the origin tests and the pairwise tests.
  constructor
  · rintro h
    refine ⟨fun i ↦ ?_, fun i j hj ↦ ?_⟩
    · simpa only [support_def, testVector_eq_origin] using h i 0
    · have hji : (j - i) ≠ 0 := sub_ne_zero.mpr hj
      have hcancel : i + (j - i) = j := by rw [add_comm, sub_add_cancel]
      simpa only [support_def, testVector_eq_diff b i (j - i) hji, hcancel] using h i (j - i)
  · rintro ⟨h0, h1⟩ i d
    rcases eq_or_ne d 0 with rfl | hd
    · simpa only [support_def, testVector_eq_origin] using h0 i
    · have hne : i + d ≠ i := fun h ↦ hd (add_left_cancel (by rw [h, add_zero]))
      simpa only [support_def, testVector_eq_diff b i d hd] using h1 i (i + d) hne

/-- For any Gram factor `S` with `Sᵀ * S = H`, a coefficient support equals the
inner product of the realized normal and the realized tested vector. -/
theorem support_eq_inner
    (S : Matrix (Fin 2 × Fin 48) (Fin 2 × Fin 48) ℝ)
    (factor : S.transpose * S = gramMatrix) (b : Fin 2) (γ : ℝ) (i d : ZMod 48) :
    support b γ i d =
      dotProduct (S.mulVec (normal b γ i)) (S.mulVec (testVector b i d)) := by
  -- Replace the Gram matrix by its factorisation and reassociate the two `mulVec`s.
  rw [support_def, ← factor]
  rw [← Matrix.mulVec_mulVec]
  -- Move the transposed factor across the pairing using the transpose rule.
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

end

end Coefficient
end Period48
end ConsensusADMM
