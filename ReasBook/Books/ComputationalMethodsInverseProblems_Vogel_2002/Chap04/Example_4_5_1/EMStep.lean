/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.JointModel
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public section

namespace NonnegativeEM

open scoped BigOperators

/-- The conditional weight `P{X = j | Y = i}` attached to the current iterate `fCurrent`,
specialized from the canonical `DiscreteEM.posteriorPmf`. -/
noncomputable def posteriorWeight
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i)
    (i : Fin m) (j : Fin n) : ℝ :=
  (DiscreteEM.posteriorPmf (jointFamily K hK) ⟨fCurrent, hfCurrent⟩ i
      (observedPmf_ne_zero_of_mulVec_pos K hK fCurrent hfCurrent i (hobsPos i)) j).toReal

/-- `posteriorWeight` is the real-valued point mass of the specialized posterior PMF. -/
theorem posteriorWeight_eq_posteriorPmf
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i) (i : Fin m) (j : Fin n) :
    posteriorWeight K hK fCurrent hfCurrent hobsPos i j =
      (DiscreteEM.posteriorPmf (jointFamily K hK) ⟨fCurrent, hfCurrent⟩ i
        (observedPmf_ne_zero_of_mulVec_pos K hK fCurrent hfCurrent i (hobsPos i)) j).toReal := by
  rfl

/-- The conditional weight is the quotient `K i j * fCurrent j / ∑ l, K i l * fCurrent l`. -/
theorem posteriorWeight_eq
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i)
    (i : Fin m) (j : Fin n) :
    posteriorWeight K hK fCurrent hfCurrent hobsPos i j =
      K i j * fCurrent j / ∑ l, K i l * fCurrent l := by
  rw [posteriorWeight_eq_posteriorPmf, DiscreteEM.posteriorPmf_apply, jointFamily_apply,
    jointPmf_apply, observedPmf_eq_mulVec]
  have hJointNonneg : 0 ≤ K i j * fCurrent j :=
    mul_nonneg (hK.nonneg i j) (hfCurrent.1 j)
  have hObservedNonneg : 0 ≤ Matrix.mulVec K fCurrent i :=
    le_of_lt (hobsPos i)
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hJointNonneg, ENNReal.toReal_ofReal hObservedNonneg]
  simp [Matrix.mulVec, dotProduct]

/-- The EM update associated to equation `(4.66)`. The source positivity conditions are kept in
theorems about this update, not in the definition itself. -/
noncomputable def emUpdate
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ) (fCurrent : Fin n → ℝ) :
    Fin n → ℝ :=
  fun j ↦ fCurrent j * ∑ i, K i j * (g i / Matrix.mulVec K fCurrent i)

/-- The M-step update is the displayed coordinate formula from equation `(4.66)`. -/
theorem emUpdate_apply
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ) (fCurrent : Fin n → ℝ)
    (j : Fin n) :
    emUpdate K g fCurrent j =
      fCurrent j * ∑ i, K i j * (g i / ∑ l, K i l * fCurrent l) := by
  simp [emUpdate, Matrix.mulVec, dotProduct]

/-- The model-specific E-step objective, expressed as a weighted sum of the canonical
`DiscreteEM.qFunction` values for the joint family `jointFamily K hK`. -/
noncomputable def qFunction
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (g : Fin m → ℝ) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n))
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i) : ℝ :=
  (r : ℝ) * ∑ i, g i *
    DiscreteEM.qFunction (jointFamily K hK) ⟨f, hf⟩ ⟨fCurrent, hfCurrent⟩ i
      (observedPmf_ne_zero_of_mulVec_pos K hK fCurrent hfCurrent i (hobsPos i))

/-- `qFunction` is the weighted sum of the specialized canonical discrete-EM auxiliary
functionals. -/
theorem qFunction_eq_discreteQFunction_sum
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (g : Fin m → ℝ) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n))
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i) :
    qFunction r K hK g f hf fCurrent hfCurrent hobsPos =
      (r : ℝ) * ∑ i, g i *
        DiscreteEM.qFunction (jointFamily K hK) ⟨f, hf⟩ ⟨fCurrent, hfCurrent⟩ i
          (observedPmf_ne_zero_of_mulVec_pos K hK fCurrent hfCurrent i (hobsPos i)) := by
  simp [qFunction]

/-- Under the source positivity hypotheses and the nonnegativity of `g`, the specialized
`qFunction` recovers the displayed weighted-posterior formula from equation `(4.65)`. -/
theorem qFunction_eq_weightedPosteriorSum
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (hK : K.IsColStochasticRect)
    (g : Fin m → ℝ) (f : Fin n → ℝ) (hf : f ∈ stdSimplex ℝ (Fin n))
    (fCurrent : Fin n → ℝ) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i)
    (hgNonneg : ∀ i, 0 ≤ g i)
    (hlog : ∀ i j, 0 < g i → 0 < posteriorWeight K hK fCurrent hfCurrent hobsPos i j →
      0 < K i j ∧ 0 < f j) :
    qFunction r K hK g f hf fCurrent hfCurrent hobsPos =
      ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
          posteriorWeight K hK fCurrent hfCurrent hobsPos i j := by
  calc
    qFunction r K hK g f hf fCurrent hfCurrent hobsPos =
        (r : ℝ) * ∑ i, g i * ∑ j,
          posteriorWeight K hK fCurrent hfCurrent hobsPos i j *
            Real.log (K i j * f j) := by
      rw [qFunction_eq_discreteQFunction_sum]
      refine congrArg ((r : ℝ) * ·) ?_
      refine Finset.sum_congr rfl ?_
      intro i hi
      congr 1
      rw [DiscreteEM.qFunction_def]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [DiscreteEM.completeLogLikelihood_def,
        ← posteriorWeight_eq_posteriorPmf K hK fCurrent hfCurrent hobsPos i j,
        jointFamily_apply, jointPmf_apply]
      have hMassNonneg : 0 ≤ K i j * f j :=
        mul_nonneg (hK.nonneg i j) (hf.1 j)
      rw [ENNReal.toReal_ofReal hMassNonneg]
    _ = ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
            posteriorWeight K hK fCurrent hfCurrent hobsPos i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hgiZero : g i = 0
      · simp [hgiZero]
      · by_cases hpostZero :
          posteriorWeight K hK fCurrent hfCurrent hobsPos i j = 0
        · simp [hpostZero]
        · have hgiPos : 0 < g i :=
            lt_of_le_of_ne (hgNonneg i) (Ne.symm hgiZero)
          have hpostNonneg :
              0 ≤ posteriorWeight K hK fCurrent hfCurrent hobsPos i j := by
            rw [posteriorWeight_eq_posteriorPmf]
            exact ENNReal.toReal_nonneg
          have hpostPos :
              0 < posteriorWeight K hK fCurrent hfCurrent hobsPos i j :=
            lt_of_le_of_ne hpostNonneg (Ne.symm hpostZero)
          obtain ⟨hKPos, hfPos⟩ := hlog i j hgiPos hpostPos
          rw [Real.log_mul hKPos.ne' hfPos.ne']
          ring

end NonnegativeEM
