/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.EMStep
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Prop_4_37
public import Mathlib.Order.Filter.Extr

public section

namespace NonnegativeEM

open scoped BigOperators

/-- Companion API for the inequality-constraint clause of `Exercise 4.21`: if the current iterate
is a probability vector in the Chapter 4 nonnegative-EM setup and the current model output is
nonvanishing on the support of the observed probability vector `g`, then the update from equation
`(4.66)` remains a probability vector, so the inequality constraint `(4.51)` is preserved together
with the normalization constraint `(4.52)`; the stronger positivity assumptions needed for
`qFunction` do not enter this constraint-preservation statement. -/
theorem emUpdate_isProbabilityVector
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ) (fCurrent : Fin n → ℝ)
    (hK : K.IsColStochasticRect) (hg : g ∈ stdSimplex ℝ (Fin m))
    (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hmodelSupport : ∀ i, 0 < g i → 0 < Matrix.mulVec K fCurrent i) :
    emUpdate K g fCurrent ∈ stdSimplex ℝ (Fin n) := by
  have hmodelSimplex : Matrix.mulVec K fCurrent ∈ stdSimplex ℝ (Fin m) :=
    Matrix.IsColStochasticRect.mulVec_mem_stdSimplex hK hfCurrent
  refine ⟨?_, ?_⟩
  · intro j
    -- Each update coordinate is a product of two nonnegative factors.
    rw [show emUpdate K g fCurrent j =
      fCurrent j * ∑ i, K i j * (g i / Matrix.mulVec K fCurrent i) by
      simpa [Matrix.mulVec, dotProduct] using emUpdate_apply K g fCurrent j]
    refine mul_nonneg (hfCurrent.1 j) ?_
    refine Finset.sum_nonneg ?_
    intro i hi
    refine mul_nonneg (hK.nonneg i j) ?_
    exact div_nonneg (hg.1 i) (hmodelSimplex.1 i)
  · -- Commute the finite sums and collapse each row contribution back to `g i`.
    calc
      ∑ j, emUpdate K g fCurrent j
          = ∑ j, fCurrent j * ∑ i, K i j * (g i / Matrix.mulVec K fCurrent i) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simpa [Matrix.mulVec, dotProduct] using emUpdate_apply K g fCurrent j
      _ = ∑ j, ∑ i, fCurrent j * (K i j * (g i / Matrix.mulVec K fCurrent i)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, fCurrent j * (K i j * (g i / Matrix.mulVec K fCurrent i)) := by
              rw [Finset.sum_comm]
      _ = ∑ i, (g i / Matrix.mulVec K fCurrent i) * ∑ j, K i j * fCurrent j := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              calc
                ∑ j, fCurrent j * (K i j * (g i / Matrix.mulVec K fCurrent i))
                    = ∑ j, (g i / Matrix.mulVec K fCurrent i) * (K i j * fCurrent j) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        ring
                _ = (g i / Matrix.mulVec K fCurrent i) * ∑ j, K i j * fCurrent j := by
                        rw [Finset.mul_sum]
      _ = ∑ i, (g i / Matrix.mulVec K fCurrent i) * Matrix.mulVec K fCurrent i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [Matrix.mulVec, dotProduct]
      _ = ∑ i, g i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hgi : g i = 0
              · simp [hgi]
              · have hgi_pos : 0 < g i := lt_of_le_of_ne (hg.1 i) (by simpa [eq_comm] using hgi)
                have hden_pos : 0 < Matrix.mulVec K fCurrent i := hmodelSupport i hgi_pos
                rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hden_pos.ne', mul_one]
      _ = 1 := hg.2

/-- Helper for Exercise 4.21: the `j`-th EM update coordinate is the weighted posterior
quotient sum attached to the current iterate. -/
lemma emUpdate_eq_weightedPosteriorQuotientSum
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ) (fCurrent : Fin n → ℝ)
    (j : Fin n) :
    emUpdate K g fCurrent j =
      ∑ i, g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
  -- Expand the update and commute the scalar factors into the coefficient form used below.
  calc
    emUpdate K g fCurrent j
        = fCurrent j * ∑ i, K i j * (g i / Matrix.mulVec K fCurrent i) := by
            simpa [Matrix.mulVec, dotProduct] using emUpdate_apply K g fCurrent j
    _ = ∑ i, fCurrent j * (K i j * (g i / Matrix.mulVec K fCurrent i)) := by
            rw [Finset.mul_sum]
    _ = ∑ i, g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [div_eq_mul_inv, div_eq_mul_inv]
            ring

/-- Helper for Exercise 4.21: positivity of an EM update coordinate forces positivity of the
candidate coordinate through the source support hypothesis. -/
lemma candidatePos_of_emUpdatePos
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (fCurrent : Fin n → ℝ) (f : Fin n → ℝ) (hK : K.IsColStochasticRect)
    (hg : g ∈ stdSimplex ℝ (Fin m)) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hlogCandidate : ∀ i j, 0 < g i →
      0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i → 0 < f j)
    {j : Fin n} :
    0 < emUpdate K g fCurrent j → 0 < f j := by
  intro huj
  have hmodelSimplex : Matrix.mulVec K fCurrent ∈ stdSimplex ℝ (Fin m) :=
    Matrix.IsColStochasticRect.mulVec_mem_stdSimplex hK hfCurrent
  have hsum_pos :
      0 < ∑ i, g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    simpa [emUpdate_eq_weightedPosteriorQuotientSum K g fCurrent j] using huj
  have hsummand_nonneg :
      ∀ i, 0 ≤ g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    intro i
    refine mul_nonneg (hg.1 i) ?_
    exact div_nonneg (mul_nonneg (hK.nonneg i j) (hfCurrent.1 j)) (hmodelSimplex.1 i)
  obtain ⟨i, hi_mem, hsummand_ne⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero
      (s := Finset.univ)
      (f := fun i ↦ g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i))
      (by exact ne_of_gt hsum_pos)
  have hsummand_pos :
      0 < g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) :=
    lt_of_le_of_ne (hsummand_nonneg i) (by simpa [eq_comm] using hsummand_ne)
  have hquot_nonneg : 0 ≤ K i j * fCurrent j / Matrix.mulVec K fCurrent i :=
    div_nonneg (mul_nonneg (hK.nonneg i j) (hfCurrent.1 j)) (hmodelSimplex.1 i)
  have hgi_ne : g i ≠ 0 := by
    intro hzero
    exact hsummand_ne (by simp [hzero])
  have hgi_pos : 0 < g i := lt_of_le_of_ne (hg.1 i) (by simpa [eq_comm] using hgi_ne)
  have hquot_ne : K i j * fCurrent j / Matrix.mulVec K fCurrent i ≠ 0 := by
    intro hzero
    exact hsummand_ne (by simp [hzero])
  have hquot_pos : 0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i :=
    lt_of_le_of_ne hquot_nonneg (by simpa [eq_comm] using hquot_ne)
  -- Feed the positive posterior witness back into the candidate positivity hypothesis.
  exact hlogCandidate i j hgi_pos hquot_pos

/-- Helper for Exercise 4.21: among simplex vectors, the weighted log functional is maximized at
its own weight vector. -/
lemma weightedLog_le_self_of_stdSimplex
    {n : ℕ} (u v : Fin n → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin n)) (hv : v ∈ stdSimplex ℝ (Fin n))
    (hpos : ∀ j, 0 < u j → 0 < v j) :
    ∑ j, u j * Real.log (v j) ≤ ∑ j, u j * Real.log (u j) := by
  have hterm :
      ∀ j, u j * (Real.log (u j) - Real.log (v j)) ≥ u j - v j := by
    intro j
    -- Apply the scalar log-gap bound pointwise to the two simplex coordinates.
    refine DiscreteEM.weightedLogDiff_ge_massDiff (a := u j) (b := v j)
      (hu.1 j) (hv.1 j) ?_
    exact fun huj ↦ hpos j huj
  have hsum_nonneg : 0 ≤ ∑ j, u j * (Real.log (u j) - Real.log (v j)) := by
    have hsum_lower :
        ∑ j, (u j - v j) ≤ ∑ j, u j * (Real.log (u j) - Real.log (v j)) := by
      -- Sum the pointwise lower bounds over the simplex coordinates.
      exact Finset.sum_le_sum fun j hj ↦ hterm j
    have hsum_zero : ∑ j, (u j - v j) = 0 := by
      -- Both vectors have total mass `1`, so the mass-difference sum vanishes.
      calc
        ∑ j, (u j - v j) = (∑ j, u j) - ∑ j, v j := by
          rw [Finset.sum_sub_distrib]
        _ = 0 := by simp [hu.2, hv.2]
    simpa [hsum_zero] using hsum_lower
  have hgap :
      0 ≤ (∑ j, u j * Real.log (u j)) - ∑ j, u j * Real.log (v j) := by
    -- Expand the summed log gap into the difference of the two weighted log sums.
    calc
      0 ≤ ∑ j, u j * (Real.log (u j) - Real.log (v j)) := hsum_nonneg
      _ = (∑ j, u j * Real.log (u j)) - ∑ j, u j * Real.log (v j) := by
            calc
              ∑ j, u j * (Real.log (u j) - Real.log (v j))
                  = ∑ j, (u j * Real.log (u j) - u j * Real.log (v j)) := by
                      refine Finset.sum_congr rfl ?_
                      intro j hj
                      rw [mul_sub]
              _ = (∑ j, u j * Real.log (u j)) - ∑ j, u j * Real.log (v j) := by
                      rw [Finset.sum_sub_distrib]
  exact sub_nonneg.mp hgap

/-- Helper for Exercise 4.21: the displayed objective is an `x`-independent log-`K` term plus the
weighted log functional with weights `emUpdate K g fCurrent`. -/
lemma exerciseObjective_eq_const_add_weightedLog
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (fCurrent x : Fin n → ℝ) :
    ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (x j)) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i) =
      (∑ i, ∑ j,
        (r : ℝ) * g i * Real.log (K i j) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i)) +
      (r : ℝ) * ∑ j, emUpdate K g fCurrent j * Real.log (x j) := by
  let w : Fin m → Fin n → ℝ :=
    fun i j ↦ K i j * fCurrent j / Matrix.mulVec K fCurrent i
  -- Separate the `log K` contribution from the `log x` contribution.
  calc
    ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (x j)) * w i j
        =
      ∑ i, ∑ j,
        ((r : ℝ) * g i * Real.log (K i j) * w i j +
          (r : ℝ) * g i * Real.log (x j) * w i j) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [w]
            ring
    _ =
      (∑ i, ∑ j, (r : ℝ) * g i * Real.log (K i j) * w i j) +
        ∑ i, ∑ j, (r : ℝ) * g i * Real.log (x j) * w i j := by
          simp_rw [Finset.sum_add_distrib]
    _ =
      (∑ i, ∑ j, (r : ℝ) * g i * Real.log (K i j) * w i j) +
        (r : ℝ) * ∑ j, emUpdate K g fCurrent j * Real.log (x j) := by
          congr 1
          calc
            ∑ i, ∑ j, (r : ℝ) * g i * Real.log (x j) * w i j
                = ∑ j, ∑ i, (r : ℝ) * g i * Real.log (x j) * w i j := by
                    rw [Finset.sum_comm]
            _ = ∑ j, ((r : ℝ) * ∑ i, g i * w i j) * Real.log (x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    calc
                      ∑ i, (r : ℝ) * g i * Real.log (x j) * w i j
                          = ∑ i, ((r : ℝ) * (g i * w i j)) * Real.log (x j) := by
                              refine Finset.sum_congr rfl ?_
                              intro i hi
                              ring
                      _ = (∑ i, (r : ℝ) * (g i * w i j)) * Real.log (x j) := by
                              rw [Finset.sum_mul]
                      _ = ((r : ℝ) * ∑ i, g i * w i j) * Real.log (x j) := by
                              rw [Finset.mul_sum]
            _ = ∑ j, ((r : ℝ) * emUpdate K g fCurrent j) * Real.log (x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    rw [emUpdate_eq_weightedPosteriorQuotientSum]
            _ = (r : ℝ) * ∑ j, emUpdate K g fCurrent j * Real.log (x j) := by
                    calc
                      ∑ j, (r : ℝ) * emUpdate K g fCurrent j * Real.log (x j)
                          = ∑ j, (r : ℝ) * (emUpdate K g fCurrent j * Real.log (x j)) := by
                              refine Finset.sum_congr rfl ?_
                              intro j hj
                              ring
                      _ = (r : ℝ) * ∑ j, emUpdate K g fCurrent j * Real.log (x j) := by
                              rw [Finset.mul_sum]
    _ =
      (∑ i, ∑ j,
        (r : ℝ) * g i * Real.log (K i j) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i)) +
      (r : ℝ) * ∑ j, emUpdate K g fCurrent j * Real.log (x j) := by
          simp [w]

/-- Exercise 4.21. In the Chapter 4 nonnegative-EM setup, equation `(4.66)`
maximizes the displayed objective from `(4.65)` over admissible candidates: the normalization
constraint `(4.52)` is kept explicit, and the nonnegativity side condition from `(4.51)` is
required on the candidate so the comparison ranges over probability vectors rather than arbitrary
signed vectors.
The support-level nonvanishing hypothesis needed to interpret the posterior quotient is assumed
only on the support of `g`; positivity of `K i j` on positive posterior support is derived from
the stochastic/simplex setup, while the candidate-side log positivity for `f` is assumed exactly
where it is needed. The update-side verification of `(4.51)` and `(4.52)` is supplied by
`emUpdate_isProbabilityVector`. -/
theorem exercise_4_21
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (fCurrent : Fin n → ℝ) (f : Fin n → ℝ) (hK : K.IsColStochasticRect)
    (hg : g ∈ stdSimplex ℝ (Fin m)) (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hmodelSupport : ∀ i, 0 < g i → 0 < Matrix.mulVec K fCurrent i)
    (hEq : ∑ j, f j = 1)
    (hfNonneg : ∀ j, 0 ≤ f j)
    (hlogCandidate : ∀ i j, 0 < g i →
      0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i → 0 < f j) :
    ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i) ≤
      ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
  let u : Fin n → ℝ := emUpdate K g fCurrent
  let base : ℝ :=
    ∑ i, ∑ j,
      (r : ℝ) * g i * Real.log (K i j) *
        (K i j * fCurrent j / Matrix.mulVec K fCurrent i)
  have hu : u ∈ stdSimplex ℝ (Fin n) :=
    emUpdate_isProbabilityVector K g fCurrent hK hg hfCurrent hmodelSupport
  have hf : f ∈ stdSimplex ℝ (Fin n) := ⟨hfNonneg, hEq⟩
  have hcandidate_pos : ∀ j, 0 < u j → 0 < f j := by
    intro j huj
    -- Positive update support produces the candidate positivity required by the entropy bound.
    simpa [u] using
      candidatePos_of_emUpdatePos K g fCurrent f hK hg hfCurrent
        hlogCandidate (j := j) huj
  have hweightedLog :
      ∑ j, u j * Real.log (f j) ≤ ∑ j, u j * Real.log (u j) :=
    weightedLog_le_self_of_stdSimplex u f hu hf hcandidate_pos
  have hr_nonneg : 0 ≤ (r : ℝ) := by
    exact_mod_cast Nat.zero_le r
  have hscaled :
      (r : ℝ) * ∑ j, u j * Real.log (f j) ≤
        (r : ℝ) * ∑ j, u j * Real.log (u j) :=
    mul_le_mul_of_nonneg_left hweightedLog hr_nonneg
  -- Route correction: keep the proof on the raw displayed sum and normalize it to the weighted
  -- log functional, rather than forcing the stronger `qFunction` owner hypotheses here.
  calc
    ∑ i, ∑ j,
        (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
          (K i j * fCurrent j / Matrix.mulVec K fCurrent i)
        = base + (r : ℝ) * ∑ j, u j * Real.log (f j) := by
            simpa [u, base] using
              exerciseObjective_eq_const_add_weightedLog r K g fCurrent f
    _ ≤ base + (r : ℝ) * ∑ j, u j * Real.log (u j) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hscaled base
    _ = ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
            simpa [u, base] using
              (exerciseObjective_eq_const_add_weightedLog r K g fCurrent u).symm

/-- Companion `IsMaxOn` form of `Exercise 4.21` for the canonical owner
`NonnegativeEM.qFunction`: on the simplex subset where every coordinate carrying positive
reference posterior mass stays positive for the candidate, equation `(4.66)` maximizes the
M-step objective. -/
theorem emUpdate_isMaxOn_qFunction
    {m n : ℕ} (r : ℕ) (K : Matrix (Fin m) (Fin n) ℝ) (g : Fin m → ℝ)
    (fCurrent : Fin n → ℝ) (hK : K.IsColStochasticRect) (hg : g ∈ stdSimplex ℝ (Fin m))
    (hfCurrent : fCurrent ∈ stdSimplex ℝ (Fin n))
    (hobsPos : ∀ i, 0 < Matrix.mulVec K fCurrent i) :
    IsMaxOn
      (fun f : stdSimplex ℝ (Fin n) ↦
        qFunction r K hK g f f.2 fCurrent hfCurrent hobsPos)
      {f | ∀ i j, 0 < g i →
        0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i → 0 < f j}
      ⟨emUpdate K g fCurrent,
        emUpdate_isProbabilityVector K g fCurrent hK hg hfCurrent
          (fun i _ ↦ hobsPos i)⟩ := by
  rw [isMaxOn_iff]
  intro f hfSupport
  have hu :
      emUpdate K g fCurrent ∈ stdSimplex ℝ (Fin n) :=
    emUpdate_isProbabilityVector K g fCurrent hK hg hfCurrent (fun i _ ↦ hobsPos i)
  let uMax : stdSimplex ℝ (Fin n) := ⟨emUpdate K g fCurrent, hu⟩
  have hcandidateLog :
      ∀ i j, 0 < g i →
        0 < posteriorWeight K hK fCurrent hfCurrent hobsPos i j →
          0 < K i j ∧ 0 < f j := by
    intro i j hgi hpost
    have hquot :
        0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i := by
      simpa [posteriorWeight_eq K hK fCurrent hfCurrent hobsPos i j, Matrix.mulVec, dotProduct]
        using hpost
    have hprodPos : 0 < K i j * fCurrent j :=
      (div_pos_iff_of_pos_right (hobsPos i)).mp hquot
    -- Positive posterior weight forces a positive kernel coefficient on that support.
    have hKPos : 0 < K i j :=
      pos_of_mul_pos_left hprodPos (hfCurrent.1 j)
    exact ⟨hKPos, hfSupport i j hgi hquot⟩
  have hemUpdateLog :
      ∀ i j, 0 < g i →
        0 < posteriorWeight K hK fCurrent hfCurrent hobsPos i j →
          0 < K i j ∧ 0 < emUpdate K g fCurrent j := by
    intro i j hgi hpost
    have hquot :
        0 < K i j * fCurrent j / Matrix.mulVec K fCurrent i := by
      simpa [posteriorWeight_eq K hK fCurrent hfCurrent hobsPos i j, Matrix.mulVec, dotProduct]
        using hpost
    have hprodPos : 0 < K i j * fCurrent j :=
      (div_pos_iff_of_pos_right (hobsPos i)).mp hquot
    have hKPos : 0 < K i j :=
      pos_of_mul_pos_left hprodPos (hfCurrent.1 j)
    have hsummandPos :
        0 < g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) :=
      mul_pos hgi hquot
    have hsummandNonneg :
        ∀ i', 0 ≤ g i' * (K i' j * fCurrent j / Matrix.mulVec K fCurrent i') := by
      intro i'
      refine mul_nonneg (hg.1 i') ?_
      exact div_nonneg (mul_nonneg (hK.nonneg i' j) (hfCurrent.1 j)) (le_of_lt (hobsPos i'))
    have hsumPos :
        0 < ∑ i', g i' * (K i' j * fCurrent j / Matrix.mulVec K fCurrent i') := by
      have hsingleLe :
          g i * (K i j * fCurrent j / Matrix.mulVec K fCurrent i) ≤
            ∑ i', g i' * (K i' j * fCurrent j / Matrix.mulVec K fCurrent i') := by
        simpa using
          (Finset.single_le_sum
            (s := Finset.univ)
            (f := fun i' ↦ g i' * (K i' j * fCurrent j / Matrix.mulVec K fCurrent i'))
            (fun i' _ ↦ hsummandNonneg i')
            (Finset.mem_univ i))
      exact lt_of_lt_of_le hsummandPos hsingleLe
    -- The positive posterior-support witness contributes a positive term to the update sum.
    have hUpdatePos : 0 < emUpdate K g fCurrent j := by
      simpa [emUpdate_eq_weightedPosteriorQuotientSum K g fCurrent j] using hsumPos
    exact ⟨hKPos, hUpdatePos⟩
  have hmain :
      ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) ≤
        ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    exact exercise_4_21 r K g fCurrent f hK hg hfCurrent
      (fun i _ ↦ hobsPos i) f.2.2 f.2.1 hfSupport
  have hleft :
      qFunction r K hK g f f.2 fCurrent hfCurrent hobsPos =
        ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    simpa [posteriorWeight_eq K hK fCurrent hfCurrent hobsPos, Matrix.mulVec, dotProduct] using
      qFunction_eq_weightedPosteriorSum r K hK g f f.2 fCurrent hfCurrent hobsPos hcandidateLog
  have hright :
      qFunction r K hK g uMax uMax.2 fCurrent hfCurrent hobsPos =
        ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (uMax j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    simpa [posteriorWeight_eq K hK fCurrent hfCurrent hobsPos, Matrix.mulVec, dotProduct]
      using
      qFunction_eq_weightedPosteriorSum r K hK g uMax uMax.2
        fCurrent hfCurrent hobsPos hemUpdateLog
  have hrightRaw :
      qFunction r K hK g uMax uMax.2 fCurrent hfCurrent hobsPos =
        ∑ i, ∑ j,
          (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
            (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
    calc
      qFunction r K hK g uMax uMax.2 fCurrent hfCurrent hobsPos
          = ∑ i, ∑ j,
              (r : ℝ) * g i * (Real.log (K i j) + Real.log (uMax j)) *
                (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := hright
      _ = ∑ i, ∑ j,
            (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
              (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            have huMax_apply : uMax j = emUpdate K g fCurrent j := by
              rfl
            rw [huMax_apply]
  have hgoal :
      qFunction r K hK g f f.2 fCurrent hfCurrent hobsPos ≤
        qFunction r K hK g uMax uMax.2 fCurrent hfCurrent hobsPos := by
    calc
      qFunction r K hK g f f.2 fCurrent hfCurrent hobsPos
          = ∑ i, ∑ j,
              (r : ℝ) * g i * (Real.log (K i j) + Real.log (f j)) *
                (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := hleft
      _ ≤ ∑ i, ∑ j,
            (r : ℝ) * g i * (Real.log (K i j) + Real.log (emUpdate K g fCurrent j)) *
              (K i j * fCurrent j / Matrix.mulVec K fCurrent i) := hmain
      _ = qFunction r K hK g uMax uMax.2 fCurrent hfCurrent hobsPos :=
            hrightRaw.symm
  simpa [uMax, hu] using hgoal

end NonnegativeEM
