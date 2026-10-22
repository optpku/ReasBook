/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.RectangularStochastic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Notation_4_5.DiscreteEM
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

public section

open scoped BigOperators

namespace NonnegativeEM

/-- The total mass of the finite joint law `fun (j, i) ↦ ENNReal.ofReal (K i j * f j)` is `1`
under the source normalization hypotheses. -/
theorem jointMass_sum_eq_one {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ)
    (hK : K.IsColStochasticRect) (hf : f ∈ stdSimplex ℝ (Fin n)) :
    ∑ p : Fin n × Fin m, ENNReal.ofReal (K p.2 p.1 * f p.1) = 1 := by
  calc
    ∑ p : Fin n × Fin m, ENNReal.ofReal (K p.2 p.1 * f p.1) =
        ENNReal.ofReal (∑ p : Fin n × Fin m, K p.2 p.1 * f p.1) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun p : Fin n × Fin m ↦ K p.2 p.1 * f p.1)
        (fun p _ ↦ mul_nonneg (hK.nonneg p.2 p.1) (hf.1 p.1))
    _ = ENNReal.ofReal (∑ j, (∑ i, K i j) * f j) := by
      congr 1
      rw [← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa using (show ∑ y, K y j * f j = (∑ i, K i j) * f j by
        rw [← Finset.sum_mul])
    _ = ENNReal.ofReal (∑ j, f j) := by
      congr 1
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [hK.sum_col_eq_one j, one_mul]
    _ = 1 := by
      rw [hf.2, ENNReal.ofReal_one]

/-- The joint distribution from equation `(4.60)` with mass `K i j * f j`. -/
def jointPmf {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ)
    (hK : K.IsColStochasticRect) (hf : f ∈ stdSimplex ℝ (Fin n)) : PMF (Fin n × Fin m) :=
  PMF.ofFintype (fun p ↦ ENNReal.ofReal (K p.2 p.1 * f p.1)) (jointMass_sum_eq_one K f hK hf)

/-- The value of `jointPmf` at `(j, i)` is `ENNReal.ofReal (K i j * f j)`. -/
theorem jointPmf_apply {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ)
    (hK : K.IsColStochasticRect) (hf : f ∈ stdSimplex ℝ (Fin n)) (j : Fin n) (i : Fin m) :
    jointPmf K f hK hf (j, i) = ENNReal.ofReal (K i j * f j) := by
  rfl

/-- The observed marginal of `jointPmf` is the matrix-vector product `Matrix.mulVec K f`. -/
theorem observedMarginal_eq_mulVec {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ)
    (hK : K.IsColStochasticRect) (hf : f ∈ stdSimplex ℝ (Fin n)) (i : Fin m) :
    PMF.map Prod.snd (jointPmf K f hK hf) i =
      ENNReal.ofReal (Matrix.mulVec K f i) := by
  calc
    PMF.map Prod.snd (jointPmf K f hK hf) i =
        ∑ j, jointPmf K f hK hf (j, i) := by
      rw [PMF.map_apply, tsum_fintype, ← Finset.univ_product_univ, Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [jointPmf_apply]
    _ = ∑ j, ENNReal.ofReal (K i j * f j) := by
      simp [jointPmf_apply]
    _ = ENNReal.ofReal (∑ j, K i j * f j) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun j : Fin n ↦ K i j * f j)
        (fun j _ ↦ mul_nonneg (hK.nonneg i j) (hf.1 j))
    _ = ENNReal.ofReal (Matrix.mulVec K f i) := by
      simp [Matrix.mulVec, dotProduct]

/-- The model-specific joint law as a canonical `DiscreteEM` family over the parameter simplex
`stdSimplex ℝ (Fin n)`. -/
def jointFamily {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect) :
    stdSimplex ℝ (Fin n) → PMF (Fin n × Fin m)
  | ⟨f, hf⟩ => jointPmf K f hK hf

/-- `jointFamily` specializes to `jointPmf` at a concrete probability vector. -/
theorem jointFamily_apply {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ)
    (hK : K.IsColStochasticRect) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n)) :
    jointFamily K hK ⟨f, hf⟩ = jointPmf K f hK hf := by
  rfl

/-- Specializing `DiscreteEM.observedPmf` to `jointFamily` recovers `Matrix.mulVec K f`. -/
theorem observedPmf_eq_mulVec {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ)
    (hK : K.IsColStochasticRect) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n)) (i : Fin m) :
    DiscreteEM.observedPmf (jointFamily K hK) ⟨f, hf⟩ i =
      ENNReal.ofReal (Matrix.mulVec K f i) := by
  calc
    DiscreteEM.observedPmf (jointFamily K hK) ⟨f, hf⟩ i =
        ∑ j, jointFamily K hK ⟨f, hf⟩ (j, i) := by
      simpa using
        (DiscreteEM.observedPmf_apply_eq_sum (joint := jointFamily K hK) ⟨f, hf⟩ i)
    _ = ∑ j, jointPmf K f hK hf (j, i) := by
      simp [jointFamily_apply]
    _ = ∑ j, ENNReal.ofReal (K i j * f j) := by
      simp [jointPmf_apply]
    _ = ENNReal.ofReal (∑ j, K i j * f j) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun j : Fin n ↦ K i j * f j)
        (fun j _ ↦ mul_nonneg (hK.nonneg i j) (hf.1 j))
    _ = ENNReal.ofReal (Matrix.mulVec K f i) := by
      simp [Matrix.mulVec, dotProduct]

/-- Positive model output gives the nonvanishing hypothesis needed by
`DiscreteEM.posteriorPmf`. -/
theorem observedPmf_ne_zero_of_mulVec_pos {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ)
    (hK : K.IsColStochasticRect) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n)) (i : Fin m)
    (hi : 0 < Matrix.mulVec K f i) :
    DiscreteEM.observedPmf (jointFamily K hK) ⟨f, hf⟩ i ≠ 0 := by
  rw [observedPmf_eq_mulVec K hK f hf i]
  exact ENNReal.ofReal_ne_zero_iff.2 hi

end NonnegativeEM
