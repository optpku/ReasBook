/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-- The finite gambler's ruin transition matrix on `{0, ..., N}` with gain probability `r`,
written in the chapter's canonical `ℝ≥0∞` codomain for discrete Markov chains. -/
def gamblerRuinTransitionMatrix (N : ℕ) (r : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ≥0∞ :=
  fun i j ↦
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = Fin.last N then
      if j = Fin.last N then 1 else 0
    else if j.1 = i.1 + 1 then
      ENNReal.ofReal r
    else if i.1 = j.1 + 1 then
      ENNReal.ofReal (1 - r)
    else
      0

/-- The one-step kernel associated with the gambler's ruin transition matrix. -/
abbrev gamblerRuinKernel (N : ℕ) (r : ℝ) :
    Kernel (Fin (N + 1)) (Fin (N + 1)) :=
  discreteMatrixKernel (gamblerRuinTransitionMatrix N r)

/-- The same transition matrix regarded as a real matrix for characteristic-polynomial and
spectral computations. -/
def gamblerRuinTransitionMatrixReal (N : ℕ) (r : ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun i j ↦
    if i = 0 then
      if j = 0 then 1 else 0
    else if i = Fin.last N then
      if j = Fin.last N then 1 else 0
    else if j.1 = i.1 + 1 then
      r
    else if i.1 = j.1 + 1 then
      1 - r
    else
      0

-- Proof sketch: for `0 ≤ r ≤ 1`, the off-diagonal masses `r` and `1 - r` are nonnegative, so
-- taking `toReal` entrywise on the canonical `ℝ≥0∞` transition matrix recovers the usual real
-- transition matrix used in the linear-algebra calculations.
/-- In the probabilistic regime `0 ≤ r ≤ 1`, the real bridge is obtained by taking `toReal`
entrywise on the canonical gambler's ruin transition matrix. -/
theorem gamblerRuinTransitionMatrixReal_eq_toReal
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    gamblerRuinTransitionMatrixReal N r = fun i j ↦ (gamblerRuinTransitionMatrix N r i j).toReal :=
  by
    -- Proof comment: compare the two matrices entrywise and follow the same boundary/interior
    -- case split used in their definitions.
    ext i j
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hj0 : j = 0
      · subst hj0
        simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix]
      · simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hj0]
    · by_cases hiN : i = Fin.last N
      · subst hiN
        have hNpos : N ≠ 0 := by
          intro hN0
          apply hi0
          subst hN0
          rfl
        by_cases hjN : j = Fin.last N
        · subst hjN
          simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hNpos]
        · simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hi0, hjN]
      · by_cases hright : j.1 = i.1 + 1
        · -- Proof comment: on the right-neighbor entry, `toReal (ofReal r) = r`.
          simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hi0, hiN, hright,
            ENNReal.toReal_ofReal, hr0]
        · by_cases hleft : i.1 = j.1 + 1
          · -- Proof comment: on the left-neighbor entry, `toReal (ofReal (1 - r)) = 1 - r`.
            have hright' : ¬j.1 = j.1 + 1 + 1 := by
              omega
            simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hi0, hiN, hleft,
              hright', ENNReal.toReal_ofReal, sub_nonneg.mpr hr1]
          · simp [gamblerRuinTransitionMatrixReal, gamblerRuinTransitionMatrix, hi0, hiN, hright,
              hleft]

-- Proof sketch: the boundary rows are Dirac masses at `0` and `N`, and each interior row has
-- exactly the two nonzero entries `r` and `1 - r`, which add up to `1`.
/-- The gambler's ruin transition matrix is stochastic whenever `0 ≤ r ≤ 1`. -/
theorem gamblerRuinTransitionMatrix_isStochastic
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsStochasticMatrix (gamblerRuinTransitionMatrix N r) := by
  intro i
  classical
  by_cases hi0 : i = 0
  · subst hi0
    -- Proof comment: the row at the absorbing state `0` is a Dirac mass at `0`.
    have hsupport :
        ∀ j ∉ ({0} : Finset (Fin (N + 1))), gamblerRuinTransitionMatrix N r 0 j = 0 := by
      intro j hj
      have hj0 : j ≠ 0 := by
        intro h
        exact hj (by simp [h])
      simp [gamblerRuinTransitionMatrix, hj0]
    rw [tsum_eq_sum hsupport]
    simp [gamblerRuinTransitionMatrix]
  · by_cases hiN : i = Fin.last N
    · subst hiN
      have hNpos : N ≠ 0 := by
        intro hN0
        apply hi0
        subst hN0
        rfl
      -- Proof comment: the row at the absorbing state `N` is a Dirac mass at `N`.
      have hsupport :
          ∀ j ∉ ({Fin.last N} : Finset (Fin (N + 1))),
            gamblerRuinTransitionMatrix N r (Fin.last N) j = 0 := by
        intro j hj
        have hjN : j ≠ Fin.last N := by
          intro h
          exact hj (by simp [h])
        simp [gamblerRuinTransitionMatrix, hjN, hNpos]
      rw [tsum_eq_sum hsupport]
      simp [gamblerRuinTransitionMatrix, hNpos]
    · have hi0_nat : i.1 ≠ 0 := by
        intro h
        apply hi0
        exact Fin.ext h
      have hi_lt_N : i.1 < N := by
        by_contra h
        have hi_ge_N : N ≤ i.1 := Nat.not_lt.mp h
        have hi_eq_last : i.1 = N := by omega
        apply hiN
        exact Fin.ext hi_eq_last
      have hpred_lt : i.1 - 1 < N + 1 := by
        omega
      have hsucc_lt : i.1 + 1 < N + 1 := by
        omega
      let jPrev : Fin (N + 1) := ⟨i.1 - 1, hpred_lt⟩
      let jNext : Fin (N + 1) := ⟨i.1 + 1, hsucc_lt⟩
      have hjPrev_step : i.1 = jPrev.1 + 1 := by
        dsimp [jPrev]
        omega
      have hjNext_step : jNext.1 = i.1 + 1 := by
        dsimp [jNext]
      have hpair : jPrev ≠ jNext := by
        intro h
        have hvals : jPrev.1 = jNext.1 := congrArg Fin.val h
        dsimp [jPrev, jNext] at hvals
        omega
      have hsupport :
          ∀ j ∉ ({jPrev, jNext} : Finset (Fin (N + 1))),
            gamblerRuinTransitionMatrix N r i j = 0 := by
        intro j hj
        have hjPrev : j ≠ jPrev := by
          intro h
          exact hj (by simp [h])
        have hjNext : j ≠ jNext := by
          intro h
          exact hj (by simp [h])
        have hright : j.1 ≠ i.1 + 1 := by
          intro h
          apply hjNext
          exact Fin.ext <| by
            dsimp [jNext]
            exact h
        have hleft : i.1 ≠ j.1 + 1 := by
          intro h
          apply hjPrev
          exact Fin.ext <| by
            dsimp [jPrev]
            omega
        simp [gamblerRuinTransitionMatrix, hi0, hiN, hright, hleft]
      rw [tsum_eq_sum hsupport]
      -- Proof comment: an interior row is supported on the two neighbors `i - 1` and `i + 1`.
      have hprev_far : ¬jPrev.1 = jPrev.1 + 1 + 1 := by
        dsimp [jPrev]
        omega
      have hprev :
          gamblerRuinTransitionMatrix N r i jPrev = ENNReal.ofReal (1 - r) := by
        simp [gamblerRuinTransitionMatrix, hi0, hiN, hjPrev_step, hprev_far]
      have hnext :
          gamblerRuinTransitionMatrix N r i jNext = ENNReal.ofReal r := by
        simp [gamblerRuinTransitionMatrix, hi0, hiN, hjNext_step]
      have hadd :
          ENNReal.ofReal r + ENNReal.ofReal (1 - r) = ENNReal.ofReal 1 := by
        rw [← ENNReal.ofReal_add hr0 (sub_nonneg.mpr hr1)]
        congr 1
        ring
      rw [Finset.sum_pair hpair, hprev, hnext]
      simpa [add_comm] using hadd

/-- The gambler's ruin kernel is a Markov kernel whenever `0 ≤ r ≤ 1`. -/
theorem gamblerRuinKernel_isMarkovKernel
    (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsMarkovKernel (gamblerRuinKernel N r) :=
  discreteMatrixKernel_isMarkovKernel _ (gamblerRuinTransitionMatrix_isStochastic N hr0 hr1)

/-- The step standard deviation `σ = sqrt (4 r (1 - r))`
appearing in the explicit spectrum. -/
def gamblerRuinSigma (r : ℝ) : ℝ :=
  Real.sqrt (4 * r * (1 - r))

/-- The nontrivial eigenvalues of the gambler's ruin transition matrix. -/
def gamblerRuinNontrivialEigenvalue (N : ℕ) (r : ℝ) : Fin (N - 1) → ℝ :=
  fun n ↦ gamblerRuinSigma r * Real.cos ((((n : ℕ) : ℝ) + 1) * Real.pi / N)

/-- The explicit decay rate `σ cos (π / N)` coming from the largest nontrivial eigenvalue. -/
def gamblerRuinDecayRate (N : ℕ) (r : ℝ) : ℝ :=
  gamblerRuinSigma r * Real.cos (Real.pi / (N : ℝ))

/-- Helper for Example 18.20: the variance scale `σ` vanishes at the degenerate endpoint
probabilities `r = 0` and `r = 1`. -/
lemma gamblerRuinSigma_eq_zero_of_eq_zero_or_one {r : ℝ} (hr : r = 0 ∨ r = 1) :
    gamblerRuinSigma r = 0 := by
  -- Proof comment: at both endpoints the radicand `4 * r * (1 - r)` is zero.
  rcases hr with rfl | rfl <;> simp [gamblerRuinSigma]

/-- Helper for Example 18.20: at the degenerate endpoint probabilities, every nontrivial mode
collapses to the zero eigenvalue. -/
lemma gamblerRuinNontrivialEigenvalue_eq_zero_of_eq_zero_or_one
    (N : ℕ) {r : ℝ} (hr : r = 0 ∨ r = 1) (n : Fin (N - 1)) :
    gamblerRuinNontrivialEigenvalue N r n = 0 := by
  -- Proof comment: the cosine factor stays bounded, so the vanishing prefactor `σ` kills it.
  simp [gamblerRuinNontrivialEigenvalue, gamblerRuinSigma_eq_zero_of_eq_zero_or_one hr]

/-- Helper for Example 18.20: the `Fin (N - 1)` indexing in `gamblerRuinNontrivialEigenvalue`
matches the interval indexing `k = 1, ..., N - 1` used by the Chebyshev root factorization. -/
lemma gamblerRuinNontrivialEigenvalue_range_iff
    (N : ℕ) (hN : 2 ≤ N) {r x : ℝ} :
    (∃ n : Fin (N - 1), x = gamblerRuinNontrivialEigenvalue N r n) ↔
      ∃ k ∈ Finset.Icc 1 (N - 1),
        x = gamblerRuinSigma r * Real.cos (Real.pi * k / N) := by
  let _ := hN
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨(n : ℕ) + 1, ?_, ?_⟩
    · -- Proof comment: `n : Fin (N - 1)` corresponds to `k = n + 1` in the interval indexing.
      simp [Finset.mem_Icc]
    · -- Proof comment: after reindexing, the phase is the same angle written in the textbook form.
      simp [gamblerRuinNontrivialEigenvalue, mul_comm]
  · rintro ⟨k, hk, hxk⟩
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ N - 1 := (Finset.mem_Icc.mp hk).2
    let n : Fin (N - 1) := ⟨k - 1, by omega⟩
    have hn : (n : ℕ) + 1 = k := by
      dsimp [n]
      omega
    refine ⟨n, ?_⟩
    -- Proof comment: the inverse reindexing `n = k - 1` recovers the original mode formula.
    calc
      x = gamblerRuinSigma r * Real.cos (Real.pi * k / N) := hxk
      _ = gamblerRuinSigma r * Real.cos (Real.pi * ((((n : ℕ) : ℝ) + 1)) / N) := by
        have hnReal : (((n : ℕ) : ℝ) + 1) = k := by
          exact_mod_cast hn
        rw [← hnReal]
      _ = gamblerRuinSigma r * Real.cos ((((n : ℕ) : ℝ) + 1) * Real.pi / N) := by
        congr 1
        rw [mul_comm]
      _ = gamblerRuinNontrivialEigenvalue N r n := by
        rw [gamblerRuinNontrivialEigenvalue]

/-- Helper for Example 18.20: the diagonal contribution to the endpoint characteristic polynomial
is exactly the two absorbing factors `(X - 1)` and the `N - 1` interior factors `X`. -/
lemma gamblerRuinTransitionMatrixReal_diagonalProduct
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} :
    ∏ i : Fin (N + 1), (Polynomial.X - Polynomial.C (gamblerRuinTransitionMatrixReal N r i i)) =
      (Polynomial.X - 1) ^ 2 * Polynomial.X ^ (N - 1) := by
  have hN1 : 1 ≤ N := by
    omega
  have hpred : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  let f : ℕ → Polynomial ℝ := fun i ↦
    if h : i < N + 1 then
      Polynomial.X - Polynomial.C (gamblerRuinTransitionMatrixReal N r ⟨i, h⟩ ⟨i, h⟩)
    else
      1
  -- Proof comment: split the full diagonal product into the first boundary index, the `N - 1`
  -- interior indices, and the final boundary index.
  rw [Finset.prod_fin_eq_prod_range]
  have hsplit :
      (∏ i ∈ Finset.range (N + 1), f i) =
        ((∏ i ∈ Finset.range (N - 1), f (i + 1)) * f 0) * f N := by
    calc
      (∏ i ∈ Finset.range (N + 1), f i) = (∏ i ∈ Finset.range N, f i) * f N := by
        rw [Finset.prod_range_succ]
      _ = ((∏ i ∈ Finset.range (N - 1), f (i + 1)) * f 0) * f N := by
        rw [show (∏ i ∈ Finset.range N, f i) = (∏ i ∈ Finset.range (N - 1), f (i + 1)) * f 0 by
          simpa [f, hpred] using (Finset.prod_range_succ' f (N - 1))]
  rw [hsplit]
  have hInterior :
      (∏ k ∈ Finset.range (N - 1), f (k + 1)) =
        Polynomial.X ^ (N - 1) := by
    calc
      (∏ k ∈ Finset.range (N - 1), f (k + 1))
          = ∏ k ∈ Finset.range (N - 1), (Polynomial.X : Polynomial ℝ) := by
              refine Finset.prod_congr rfl ?_
              intro k hk
              have hkRange : k < N - 1 := Finset.mem_range.mp hk
              have hklt : k + 1 < N + 1 := by
                omega
              have hi0 : (⟨k + 1, hklt⟩ : Fin (N + 1)) ≠ 0 := by
                simp
              have hiN : (⟨k + 1, hklt⟩ : Fin (N + 1)) ≠ Fin.last N := by
                intro h
                have hval := congrArg Fin.val h
                simp at hval
                omega
              have hdiag :
                  gamblerRuinTransitionMatrixReal N r ⟨k + 1, hklt⟩ ⟨k + 1, hklt⟩ = 0 := by
                simp [gamblerRuinTransitionMatrixReal, hi0, hiN]
              have hf :
                  f (k + 1) =
                    Polynomial.X -
                      Polynomial.C
                        (gamblerRuinTransitionMatrixReal N r ⟨k + 1, hklt⟩ ⟨k + 1, hklt⟩) := by
                have hkN : k < N := by
                  omega
                simp [f, hkN]
              rw [hf, hdiag]
              simp
      _ = Polynomial.X ^ (N - 1) := by
            rw [Finset.prod_const]
            simp
  -- Proof comment: the absorbing boundary states contribute the two `(X - 1)` factors.
  have hFirst : f 0 = Polynomial.X - 1 := by
    simp [f, gamblerRuinTransitionMatrixReal]
  have hLast : f N = Polynomial.X - 1 := by
    have hN0 : N ≠ 0 := by
      omega
    have hlast : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) = Fin.last N := by
      ext
      simp
    simp [f, gamblerRuinTransitionMatrixReal, hN0, hlast]
  rw [hInterior, hFirst, hLast]
  simp [pow_two, mul_comm, mul_left_comm]

/-- Helper for Example 18.20: at the endpoint probabilities `r = 0` or `r = 1`, the transition
matrix has characteristic polynomial `(X - 1)^2 * X^(N - 1)`. -/
lemma gamblerRuinTransitionMatrixReal_charpoly_eq_endpoint
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr : r = 0 ∨ r = 1) :
    (gamblerRuinTransitionMatrixReal N r).charpoly =
      (Polynomial.X - 1) ^ 2 * Polynomial.X ^ (N - 1) := by
  rcases hr with rfl | rfl
  · -- Route correction: for `r = 0`, transpose the lower-triangular matrix so the upper-triangular
    -- characteristic-polynomial formula applies without rebuilding a second determinant argument.
    have htri :
        Matrix.BlockTriangular (Matrix.transpose (gamblerRuinTransitionMatrixReal N 0)) id := by
      intro i j hij
      by_cases hj0 : j = 0
      · subst hj0
        have hi0 : i ≠ 0 := by
          exact ne_of_gt hij
        simp [Matrix.transpose, gamblerRuinTransitionMatrixReal, hi0]
      · have hjN : j ≠ Fin.last N := by
          intro h
          have : i ≤ j := by
            simpa [h] using (Fin.le_last i)
          exact (not_lt_of_ge this) hij
        have hijVal : j.1 < i.1 := hij
        have hstep : ¬j.1 = i.1 + 1 := by
          omega
        simp [Matrix.transpose, gamblerRuinTransitionMatrixReal, hj0, hjN, hstep]
    calc
      (gamblerRuinTransitionMatrixReal N 0).charpoly
          = (Matrix.transpose (gamblerRuinTransitionMatrixReal N 0)).charpoly := by
              symm
              exact Matrix.charpoly_transpose (gamblerRuinTransitionMatrixReal N 0)
      _ = ∏ i : Fin (N + 1),
            (Polynomial.X -
              Polynomial.C ((Matrix.transpose (gamblerRuinTransitionMatrixReal N 0)) i i)) := by
            exact Matrix.charpoly_of_upperTriangular _ htri
      _ = (Polynomial.X - 1) ^ 2 * Polynomial.X ^ (N - 1) := by
            simpa [Matrix.transpose_apply] using
              (gamblerRuinTransitionMatrixReal_diagonalProduct N hN (r := (0 : ℝ)))
  · -- Proof comment: when `r = 1`, the only off-diagonal entries lie on the superdiagonal, so the
    -- matrix is already upper triangular.
    have htri : (gamblerRuinTransitionMatrixReal N 1).BlockTriangular id := by
      intro i j hij
      have hi0 : i ≠ 0 := by
        intro h
        subst h
        exact (not_lt_of_ge (Fin.zero_le j)) hij
      by_cases hiN : i = Fin.last N
      · have hjN : j ≠ Fin.last N := by
          intro h
          simp [h, hiN] at hij
        have hN0 : N ≠ 0 := by
          omega
        simp [gamblerRuinTransitionMatrixReal, hiN, hjN, hN0]
      · have hijVal : j.1 < i.1 := hij
        have hstep : ¬j.1 = i.1 + 1 := by
          omega
        simp [gamblerRuinTransitionMatrixReal, hi0, hiN, hstep]
    calc
      (gamblerRuinTransitionMatrixReal N 1).charpoly
          = ∏ i : Fin (N + 1),
              (Polynomial.X - Polynomial.C (gamblerRuinTransitionMatrixReal N 1 i i)) := by
                exact Matrix.charpoly_of_upperTriangular _ htri
      _ = (Polynomial.X - 1) ^ 2 * Polynomial.X ^ (N - 1) := by
            simpa using gamblerRuinTransitionMatrixReal_diagonalProduct N hN (r := (1 : ℝ))

/-- Helper for Example 18.20: in the degenerate endpoint cases `r = 0` or `r = 1`, the only
characteristic-polynomial roots are the absorbing root `1` and the collapsed nontrivial root `0`. -/
lemma gamblerRuinCharpoly_isRoot_iff_endpoint
    (N : ℕ) (hN : 2 ≤ N) {r x : ℝ} (hr : r = 0 ∨ r = 1) :
    Polynomial.IsRoot (gamblerRuinTransitionMatrixReal N r).charpoly x ↔
      x = 1 ∨ ∃ k ∈ Finset.Icc 1 (N - 1),
        x = gamblerRuinSigma r * Real.cos (Real.pi * k / N) := by
  have hchar := gamblerRuinTransitionMatrixReal_charpoly_eq_endpoint N hN hr
  have hNsub : N - 1 ≠ 0 := by
    omega
  have hroot :
      Polynomial.IsRoot (((Polynomial.X - 1) ^ 2 * Polynomial.X ^ (N - 1) : Polynomial ℝ)) x ↔
        x = 1 ∨ x = 0 := by
    -- Proof comment: after evaluating the explicit endpoint polynomial, only the factors
    -- `x - 1` and `x` can vanish.
    simp [Polynomial.IsRoot, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, pow_two, hNsub, mul_eq_zero, sub_eq_zero]
  have hσzero : gamblerRuinSigma r = 0 := gamblerRuinSigma_eq_zero_of_eq_zero_or_one hr
  have hOneMem : 1 ∈ Finset.Icc 1 (N - 1) := by
    simp [Finset.mem_Icc]
    omega
  rw [hchar, hroot]
  constructor
  · intro hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ⟨1, hOneMem, ?_⟩
      simp [hσzero]
  · intro hx
    rcases hx with rfl | ⟨k, hk, hxk⟩
    · exact Or.inl rfl
    · right
      simpa [hσzero] using hxk

/-- Helper for Example 18.20: the interior tridiagonal determinant satisfies the scalar recursion
from the textbook characteristic-polynomial computation. -/
def gamblerRuinCharacteristicValue (r x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | n + 2 =>
      x * gamblerRuinCharacteristicValue r x (n + 1) -
        r * (1 - r) * gamblerRuinCharacteristicValue r x n

/-- Helper for Example 18.20: in the strict interior regime `0 < r < 1`, the variance scale
`σ` squares to `4 r (1 - r)`. -/
lemma gamblerRuinSigma_sq_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    gamblerRuinSigma r ^ (2 : ℕ) = 4 * r * (1 - r) := by
  -- Proof comment: the radicand is nonnegative, so `sq_sqrt` identifies `σ²` with it.
  have hradicand : 0 ≤ 4 * r * (1 - r) := by
    nlinarith
  rw [gamblerRuinSigma]
  exact Real.sq_sqrt hradicand

/-- Helper for Example 18.20: the strict interior regime `0 < r < 1` forces `σ ≠ 0`. -/
lemma gamblerRuinSigma_ne_zero_of_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    gamblerRuinSigma r ≠ 0 := by
  -- Proof comment: a positive radicand gives a nonzero square root.
  have hradicand : 0 < 4 * r * (1 - r) := by
    nlinarith
  rw [gamblerRuinSigma]
  exact Real.sqrt_ne_zero'.2 hradicand

/-- Helper for Example 18.20: the scalar recurrence from the interior determinant is solved by the
Chebyshev polynomial `U_n` after the normalization `x / σ`. -/
lemma gamblerRuinCharacteristicValue_eq_chebyshevEval {r x : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    gamblerRuinCharacteristicValue r x n =
      (gamblerRuinSigma r / 2) ^ n *
        (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval (x / gamblerRuinSigma r) := by
  have hσne : gamblerRuinSigma r ≠ 0 := gamblerRuinSigma_ne_zero_of_pos hr0 hr1
  have hσsq : gamblerRuinSigma r ^ (2 : ℕ) = 4 * r * (1 - r) :=
    gamblerRuinSigma_sq_of_pos hr0 hr1
  -- Proof comment: match the characteristic-value recursion with the standard recursion of
  -- `Chebyshev.U` after normalizing by the nonzero scale `σ`.
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [gamblerRuinCharacteristicValue, Polynomial.Chebyshev.U_zero]
  | one =>
      simp [gamblerRuinCharacteristicValue, Polynomial.Chebyshev.U_one]
      field_simp [hσne]
  | more n ih1 ih2 =>
      have hrMul : r * (1 - r) = gamblerRuinSigma r ^ (2 : ℕ) / 4 := by
        linarith [hσsq]
      simp [gamblerRuinCharacteristicValue, ih1, ih2, Polynomial.Chebyshev.U_add_two]
      field_simp [hσne]
      rw [hrMul]
      ring

/-- Helper for Example 18.20: reindexing `k = j + 1` turns the range product into the interval
product `∏_{k = 1}^n`. -/
lemma prod_range_succ_eq_prod_Icc {α : Type*} [CommMonoid α] (n : ℕ) (f : ℕ → α) :
    Finset.prod (Finset.range n) (fun k ↦ f (k + 1)) = ∏ k ∈ Finset.Icc 1 n, f k := by
  classical
  -- Proof comment: the bijection `k ↦ k + 1` carries `range n` onto `Icc 1 n`.
  refine Finset.prod_nbij (fun k ↦ k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    exact Finset.mem_Icc.mpr
      ⟨Nat.succ_le_succ (Nat.zero_le k), Nat.succ_le_of_lt (Finset.mem_range.mp hk)⟩
  · intro a ha b hb hab
    exact Nat.succ.inj hab
  · intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk2 : k ≤ n := (Finset.mem_Icc.mp hk).2
    refine ⟨k - 1, Finset.mem_range.mpr (by omega), ?_⟩
    simpa [Nat.add_comm] using Nat.sub_add_cancel hk1
  · intro a ha
    rfl

/-- Helper for Example 18.20: the Chebyshev polynomial `U_n` factors over its real roots in the
interval-product form appearing in the textbook formula. -/
lemma chebyshevUEval_eq_rootProduct (n : ℕ) (y : ℝ) :
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
      ((2 : ℝ) ^ n * (∏ k ∈ Finset.Icc 1 n, (y - Real.cos (Real.pi * k / (n + 1))))) := by
  have hroots : Multiset.card (Polynomial.Chebyshev.U ℝ n).roots =
      (Polynomial.Chebyshev.U ℝ n).natDegree := by
    rw [Polynomial.Chebyshev.roots_U_real, Polynomial.Chebyshev.natDegree_U_natCast]
    simpa using Finset.card_image_of_injOn
      ((Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n))
  have hprod :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := Polynomial.Chebyshev.U ℝ n) hroots
  have hEval := congrArg (fun p : Polynomial ℝ ↦ p.eval y) hprod
  have hinj :
      Set.InjOn (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))) (Finset.range n) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n))
  have hRangeImage :
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod ((Finset.range n).image (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))))
            (fun z ↦ y - z)) := by
    -- Proof comment: evaluate the standard factorization theorem at `y`.
    simpa [Polynomial.Chebyshev.roots_U_real, Polynomial.Chebyshev.leadingCoeff_U_natCast,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod, Polynomial.eval_sub,
      Polynomial.eval_X, mul_comm, mul_left_comm, mul_assoc] using hEval.symm
  have hRange :
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := by
    calc
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
          ((2 : ℝ) ^ n *
            Finset.prod
              ((Finset.range n).image (fun k : ℕ ↦ Real.cos (Real.pi * (k + 1) / (n + 1))))
              (fun z ↦ y - z)) := hRangeImage
      _ =
          ((2 : ℝ) ^ n *
            Finset.prod (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := by
        congr 1
        exact Finset.prod_image hinj
  -- Proof comment: rewrite the range product as the textbook interval product.
  calc
    (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval y =
        ((2 : ℝ) ^ n *
          Finset.prod
            (Finset.range n) (fun k ↦ y - Real.cos (Real.pi * (k + 1) / (n + 1)))) := hRange
    _ =
        ((2 : ℝ) ^ n *
          ∏ k ∈ Finset.Icc 1 n, (y - Real.cos (Real.pi * k / (n + 1)))) := by
      congr 1
      simpa using prod_range_succ_eq_prod_Icc n
        (fun k ↦ y - Real.cos (Real.pi * k / (n + 1)))

/-- Helper for Example 18.20: after scaling the Chebyshev roots by `σ`, the global constants
collapse to the product `∏ (σ cos(π k / (n + 1)) - x)`. -/
lemma scaledChebyshevRootProduct_eq_gamblerRuinProduct {σ x : ℝ} {n : ℕ} (hσne : σ ≠ 0) :
    (σ / 2) ^ n * (2 : ℝ) ^ n *
        ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1))) =
      (-1 : ℝ) ^ n * ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x) := by
  have hprod :
      ∏ k ∈ Finset.Icc 1 n, (x / σ - Real.cos (Real.pi * k / (n + 1))) =
        ∏ k ∈ Finset.Icc 1 n, ((-1 / σ) * (σ * Real.cos (Real.pi * k / (n + 1)) - x)) := by
    -- Proof comment: normalize each factor with one field computation.
    refine Finset.prod_congr rfl ?_
    intro k hk
    field_simp [hσne]
    ring
  have hscalar : (σ / 2) ^ n * (2 : ℝ) ^ n * (-1 / σ) ^ n = (-1 : ℝ) ^ n := by
    have hbase : (σ / 2) * 2 * (-1 / σ) = -1 := by
      field_simp [hσne]
    repeat rw [← mul_pow]
    rw [hbase]
  rw [hprod, Finset.prod_mul_distrib, Finset.prod_const]
  have hcard : (Finset.Icc 1 n).card = n := by
    simp
  rw [hcard]
  calc
    (σ / 2) ^ n * (2 : ℝ) ^ n *
        (((-1 / σ) ^ n) * ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x)) =
      (((σ / 2) ^ n * (2 : ℝ) ^ n * (-1 / σ) ^ n) *
        ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x)) := by
      ring
    _ = (-1 : ℝ) ^ n * ∏ k ∈ Finset.Icc 1 n, (σ * Real.cos (Real.pi * k / (n + 1)) - x) := by
      rw [hscalar]

/-- Helper for Example 18.20: after removing the two absorbing boundary states from `x I - P`,
the remaining block is the textbook tridiagonal matrix with diagonal `x`, superdiagonal `-r`,
and subdiagonal `-(1 - r)`. -/
def gamblerRuinInteriorMatrix (m : ℕ) (r x : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j ↦
    if i = j then
      x
    else if j.1 = i.1 + 1 then
      -r
    else if i.1 = j.1 + 1 then
      -(1 - r)
    else
      0

/-- Helper for Example 18.20: deleting the first row and first column of the interior tridiagonal
matrix preserves the same tridiagonal shape one size smaller. -/
lemma gamblerRuinInteriorMatrix_submatrix_succ_succ
    (n : ℕ) (r x : ℝ) :
    (gamblerRuinInteriorMatrix (n + 2) r x).submatrix Fin.succ Fin.succ =
      gamblerRuinInteriorMatrix (n + 1) r x := by
  -- Proof comment: shifting both indices by one preserves equality and nearest-neighbor relations.
  ext i j
  simp [gamblerRuinInteriorMatrix]

/-- Helper for Example 18.20: the off-diagonal minor from the first row expansion has a sparse
first column whose only surviving entry is `-(1 - r)`. -/
lemma gamblerRuinInteriorStepMinor_det_eq
    (n : ℕ) (r x : ℝ) :
    ((gamblerRuinInteriorMatrix (n + 2) r x).submatrix Fin.succ (Fin.succ 0).succAbove).det =
      -(1 - r) * (gamblerRuinInteriorMatrix n r x).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    (gamblerRuinInteriorMatrix (n + 2) r x).submatrix Fin.succ (Fin.succ 0).succAbove
  have hsub :
      B.submatrix Fin.succ Fin.succ = gamblerRuinInteriorMatrix n r x := by
    -- Proof comment: removing the top row and left column of the sparse minor leaves the same
    -- tridiagonal matrix on the indices `2, ..., n + 1`.
    ext i j
    simp [B, gamblerRuinInteriorMatrix]
  have hminor :
      ((gamblerRuinInteriorMatrix (n + 2) r x).submatrix (Fin.succ ∘ Fin.succ)
        ((Fin.succ 0).succAbove ∘ Fin.succ)).det =
        (gamblerRuinInteriorMatrix n r x).det := by
    simpa [B] using congrArg Matrix.det hsub
  have htail :
      (∑ i : Fin n,
          (-1 : ℝ) ^ (i.succ : ℕ) * B i.succ 0 *
            (B.submatrix i.succ.succAbove Fin.succ).det) = (0 : ℝ) := by
    classical
    show Finset.sum Finset.univ
        (fun i : Fin n ↦
          (-1 : ℝ) ^ (i.succ : ℕ) * B i.succ 0 *
            (B.submatrix i.succ.succAbove Fin.succ).det) = 0
    refine Finset.sum_eq_zero ?_
    intro i hi
    rw [show B i.succ 0 = 0 by simp [B, gamblerRuinInteriorMatrix]]
    simp
  -- Proof comment: expand the first column; only the top entry `-(1 - r)` survives.
  rw [Matrix.det_succ_column_zero B, Fin.sum_univ_succ, htail]
  rw [show (B.submatrix (Fin.succAbove 0) Fin.succ).det = (gamblerRuinInteriorMatrix n r x).det by
    simpa using hminor]
  simp [B, gamblerRuinInteriorMatrix]

/-- Helper for Example 18.20: the tridiagonal determinant obeys the same two-step recursion as the
scalar characteristic-value sequence from the textbook. -/
lemma gamblerRuinInteriorMatrix_det_eq_characteristicValue
    (m : ℕ) (r x : ℝ) :
    (gamblerRuinInteriorMatrix m r x).det = gamblerRuinCharacteristicValue r x m := by
  induction m using Nat.twoStepInduction with
  | zero =>
      -- Proof comment: the `0 × 0` determinant is the initial value of the scalar recursion.
      simp [gamblerRuinCharacteristicValue]
  | one =>
      -- Proof comment: the `1 × 1` tridiagonal block contains only the diagonal entry `x`.
      rw [Matrix.det_fin_one]
      simp [gamblerRuinCharacteristicValue, gamblerRuinInteriorMatrix]
  | more n ih₁ ih₂ =>
      let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ := gamblerRuinInteriorMatrix (n + 2) r x
      have hdiagMatrix :
          A.submatrix Fin.succ (Fin.succAbove 0) = gamblerRuinInteriorMatrix (n + 1) r x := by
        simpa [A] using gamblerRuinInteriorMatrix_submatrix_succ_succ n r x
      have hdiag :
          (A.submatrix Fin.succ (Fin.succAbove 0)).det =
            gamblerRuinCharacteristicValue r x (n + 1) := by
        rw [hdiagMatrix]
        exact ih₂
      have htail :
          (∑ i : Fin n,
              (-1 : ℝ) ^ (i.succ.succ : ℕ) *
                A 0 i.succ.succ *
                (A.submatrix Fin.succ i.succ.succ.succAbove).det) = (0 : ℝ) := by
        classical
        show Finset.sum Finset.univ
            (fun i : Fin n ↦
              (-1 : ℝ) ^ (i.succ.succ : ℕ) *
                A 0 i.succ.succ *
                (A.submatrix Fin.succ i.succ.succ.succAbove).det) = 0
        refine Finset.sum_eq_zero ?_
        intro i hi
        rw [show A 0 i.succ.succ = 0 by
          have hneq : (0 : Fin (n + 2)) ≠ i.succ.succ := by
            simpa using (Fin.succ_ne_zero i.succ).symm
          simp [A, gamblerRuinInteriorMatrix, hneq]]
        simp
      -- Proof comment: the first-row Laplace expansion has only the diagonal and superdiagonal
      -- contributions, matching the textbook two-step recursion.
      rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ, hdiag, htail]
      rw [show ((gamblerRuinInteriorMatrix (n + 2) r x).submatrix Fin.succ
          (Fin.succ 0).succAbove).det =
          -(1 - r) * gamblerRuinCharacteristicValue r x n by
        simpa [ih₁] using gamblerRuinInteriorStepMinor_det_eq n r x]
      simp [gamblerRuinCharacteristicValue, gamblerRuinInteriorMatrix]
      ring

/-- Helper for Example 18.20: after removing the two absorbing boundary rows and columns from
`x I - P`, the remaining principal block is exactly the interior tridiagonal matrix. -/
lemma gamblerRuinBoundaryMinor_submatrix_castSucc_eq_interior
    (n : ℕ) (r x : ℝ) :
    (((Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r).submatrix
        Fin.succ Fin.succ).submatrix Fin.castSucc Fin.castSucc) =
      gamblerRuinInteriorMatrix (n + 1) r x := by
  -- Proof comment: after shifting once past `0` and once past `N`, the remaining indices are the
  -- interior states `1, ..., N - 1`, so the diagonal and nearest-neighbor tests match verbatim.
  ext i j
  let i' : Fin (n + 3) := (Fin.castSucc i).succ
  let j' : Fin (n + 3) := (Fin.castSucc j).succ
  have hi0 : i' ≠ 0 := by
    dsimp [i']
    exact Fin.succ_ne_zero (Fin.castSucc i)
  have hj0 : j' ≠ 0 := by
    dsimp [j']
    exact Fin.succ_ne_zero (Fin.castSucc j)
  have hiLast : i' ≠ Fin.last (n + 2) := by
    dsimp [i']
    exact (Fin.succ_ne_last_iff _).2 (Fin.castSucc_ne_last i)
  have hjLast : j' ≠ Fin.last (n + 2) := by
    dsimp [j']
    exact (Fin.succ_ne_last_iff _).2 (Fin.castSucc_ne_last j)
  have hdiag : i' = j' ↔ i = j := by
    constructor
    · intro h
      apply Fin.ext
      have hval := congrArg Fin.val h
      dsimp [i', j'] at hval
      omega
    · intro h
      cases h
      rfl
  have hright :
      j'.1 = i'.1 + 1 ↔ j.1 = i.1 + 1 := by
    dsimp [i', j']
    omega
  have hleft :
      i'.1 = j'.1 + 1 ↔ i.1 = j.1 + 1 := by
    dsimp [i', j']
    omega
  by_cases hij : i = j
  · subst hij
    have hstep : ¬i.1 = i.1 + 1 := by
      omega
    simp [gamblerRuinInteriorMatrix, Matrix.submatrix_apply, gamblerRuinTransitionMatrixReal,
      i', hi0, hiLast]
  · have hneq : i' ≠ j' := by
      intro h
      exact hij (hdiag.mp h)
    by_cases hright0 : j.1 = i.1 + 1
    · have hleft0 : ¬i.1 = j.1 + 1 := by
        omega
      simp [gamblerRuinInteriorMatrix, Matrix.submatrix_apply, gamblerRuinTransitionMatrixReal,
        i', j', hi0, hiLast, hij, hneq, hright0]
    · by_cases hleft0 : i.1 = j.1 + 1
      · have hsub : -(1 - r) = r - 1 := by
          ring
        have hfar : ¬j.1 = j.1 + 1 + 1 := by
          omega
        simp [gamblerRuinInteriorMatrix, Matrix.submatrix_apply, gamblerRuinTransitionMatrixReal,
          i', j', hi0, hiLast, hij, hneq, hleft0, hsub, hfar]
      · simp [gamblerRuinInteriorMatrix, Matrix.submatrix_apply, gamblerRuinTransitionMatrixReal,
          i', j', hi0, hiLast, hij, hneq, hright0, hleft0]

/-- Helper for Example 18.20: once the first absorbing row and column are removed, the remaining
matrix still has a sparse boundary row contributing the second factor `x - 1`. -/
lemma gamblerRuinBoundaryMinor_det_eq_linear_mul_interiorDet
    (n : ℕ) (r x : ℝ) :
    ((Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r).submatrix
      Fin.succ Fin.succ).det =
      (x - 1) * (gamblerRuinInteriorMatrix (n + 1) r x).det := by
  let A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ :=
    (Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r).submatrix
      Fin.succ Fin.succ
  have htail :
      (∑ j : Fin (n + 1),
          (-1 : ℝ) ^ ((Fin.last (n + 1) : ℕ) + (Fin.castSucc j : ℕ)) *
            A (Fin.last (n + 1)) (Fin.castSucc j) *
            (A.submatrix (Fin.last (n + 1)).succAbove (Fin.castSucc j).succAbove).det) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [show A (Fin.last (n + 1)) (Fin.castSucc j) = 0 by
      have hjLast : ((Fin.castSucc j).succ : Fin (n + 3)) ≠ Fin.last (n + 2) := by
        exact (Fin.succ_ne_last_iff _).2 (Fin.castSucc_ne_last j)
      have hjLast' : Fin.last (n + 2) ≠ ((Fin.castSucc j).succ : Fin (n + 3)) := by
        exact fun h ↦ hjLast h.symm
      simp [A, Matrix.diagonal, gamblerRuinTransitionMatrixReal, hjLast, hjLast']]
    simp
  have hminor :
      (A.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det =
        (gamblerRuinInteriorMatrix (n + 1) r x).det := by
    simpa [A] using
      congrArg Matrix.det (gamblerRuinBoundaryMinor_submatrix_castSucc_eq_interior n r x)
  have hsign :
      (-1 : ℝ) ^ ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 1 := by
    rw [show ((Fin.last (n + 1) : ℕ) + (Fin.last (n + 1) : ℕ)) = 2 * (n + 1) by
      simp [Fin.val_last, two_mul]]
    simp
  -- Proof comment: expand along the absorbing last row; all non-last entries vanish, and the
  -- remaining minor is exactly the interior block identified above.
  rw [Matrix.det_succ_row A (Fin.last (n + 1)), Fin.sum_univ_castSucc, htail, hsign, hminor]
  rw [show A (Fin.last (n + 1)) (Fin.last (n + 1)) = x - 1 by
    simp [A, gamblerRuinTransitionMatrixReal]]
  simp

/-- Helper for Example 18.20: the determinant of `x I - P` factors into the two absorbing boundary
terms `(x - 1)^2` and the interior tridiagonal determinant. -/
lemma gamblerRuinEvalDet_eq_boundarySquare_mul_interiorDet
    (n : ℕ) (r x : ℝ) :
    (Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r).det =
      (x - 1) ^ (2 : ℕ) * (gamblerRuinInteriorMatrix (n + 1) r x).det := by
  let A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℝ :=
    Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r
  have htail :
      (∑ j : Fin (n + 2),
          (-1 : ℝ) ^ (j.succ : ℕ) * A 0 j.succ *
            (A.submatrix Fin.succ j.succ.succAbove).det) = 0 := by
    classical
    refine Finset.sum_eq_zero ?_
    intro j hj
    rw [show A 0 j.succ = 0 by
      have hj0 : (0 : Fin (n + 3)) ≠ j.succ := by
        exact fun h ↦ Fin.succ_ne_zero j h.symm
      simp [A, Matrix.diagonal, gamblerRuinTransitionMatrixReal, hj0]]
    simp
  -- Proof comment: expand the first row; only the absorbing `(0, 0)` entry survives, and its
  -- minor is the one-boundary determinant already computed.
  rw [Matrix.det_succ_row_zero A, Fin.sum_univ_succ, htail]
  rw [show A 0 0 = x - 1 by simp [A, gamblerRuinTransitionMatrixReal]]
  rw [show (A.submatrix Fin.succ (Fin.succAbove 0)).det =
      ((Matrix.scalar (Fin (n + 3)) x - gamblerRuinTransitionMatrixReal (n + 2) r).submatrix
        Fin.succ Fin.succ).det by
    simp [A]]
  rw [gamblerRuinBoundaryMinor_det_eq_linear_mul_interiorDet]
  norm_num
  ring

/-- Helper for Example 18.20: in the normal form `N = n + 2`, the characteristic polynomial
evaluated at `x` is the absorbing square factor times the scalar recurrence value. -/
lemma
    gamblerRuinCharpolyEval_eq_boundarySquare_mul_characteristicValue
    (n : ℕ) {r x : ℝ} :
    (gamblerRuinTransitionMatrixReal (n + 2) r).charpoly.eval x =
      (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x (n + 1) := by
  -- Proof comment: evaluate the characteristic polynomial as `det (x I - P)`, then substitute
  -- the boundary factorization and the interior determinant recursion.
  rw [Matrix.eval_charpoly, gamblerRuinEvalDet_eq_boundarySquare_mul_interiorDet,
    gamblerRuinInteriorMatrix_det_eq_characteristicValue]
  have hsq : (x - 1) ^ (2 : ℕ) = (1 - x) ^ (2 : ℕ) := by
    ring
  rw [hsq]

/-- Helper for Example 18.20: in the strict interior regime `0 < r < 1`, the characteristic
polynomial roots are exactly the absorbing root `1` together with the cosine roots. -/
lemma gamblerRuinCharpoly_isRoot_iff_interiorEval
    (N : ℕ) (hN : 2 ≤ N) {r x : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Polynomial.IsRoot (gamblerRuinTransitionMatrixReal N r).charpoly x ↔
      x = 1 ∨ ∃ k ∈ Finset.Icc 1 (N - 1),
        x = gamblerRuinSigma r * Real.cos (Real.pi * k / N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := by
    refine ⟨N - 2, ?_⟩
    omega
  have hσne : gamblerRuinSigma r ≠ 0 := gamblerRuinSigma_ne_zero_of_pos hr0 hr1
  have hroot :
      Polynomial.IsRoot (gamblerRuinTransitionMatrixReal (n + 2) r).charpoly x ↔
        (1 - x) ^ (2 : ℕ) *
          (((-1 : ℝ) ^ (n + 1)) *
            ∏ k ∈ Finset.Icc 1 (n + 1),
              (gamblerRuinSigma r * Real.cos (Real.pi * k / (n + 2)) - x)) = 0 := by
    -- Proof comment: rewrite `charpoly.eval x` through the determinant factorization and then
    -- substitute the Chebyshev root product for the interior recurrence term.
    have hcharpolyEval :
        (gamblerRuinTransitionMatrixReal (n + 2) r).charpoly.eval x =
          (1 - x) ^ (2 : ℕ) * gamblerRuinCharacteristicValue r x (n + 1) :=
      gamblerRuinCharpolyEval_eq_boundarySquare_mul_characteristicValue
        (n := n) (r := r) (x := x)
    rw [Polynomial.IsRoot, hcharpolyEval]
    rw [gamblerRuinCharacteristicValue_eq_chebyshevEval hr0 hr1, chebyshevUEval_eq_rootProduct]
    have hfactor :
        (1 - x) ^ (2 : ℕ) *
            ((gamblerRuinSigma r / 2) ^ (n + 1) *
              ((2 : ℝ) ^ (n + 1) *
                ∏ k ∈ Finset.Icc 1 (n + 1),
                  (x / gamblerRuinSigma r -
                    Real.cos (Real.pi * k / ((((n + 1 : ℕ) : ℝ) + 1)))))) =
          (1 - x) ^ (2 : ℕ) *
            ((gamblerRuinSigma r / 2) ^ (n + 1) * (2 : ℝ) ^ (n + 1) *
              ∏ k ∈ Finset.Icc 1 (n + 1),
                (x / gamblerRuinSigma r -
                  Real.cos (Real.pi * k / ((((n + 1 : ℕ) : ℝ) + 1))))) := by
      ring
    have hden : ((n : ℝ) + (1 + 1)) = (n : ℝ) + 2 := by
      ring
    rw [hfactor]
    rw [scaledChebyshevRootProduct_eq_gamblerRuinProduct (x := x) (n := n + 1) hσne]
    constructor <;> intro h <;>
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm, hden] using h
  constructor
  · intro hx
    have hx' := hroot.mp hx
    rcases mul_eq_zero.mp hx' with hboundary | hinner
    · left
      have hx1 : 1 - x = 0 := by
        simpa [pow_two] using sq_eq_zero_iff.mp hboundary
      linarith
    · right
      have hprod :
          ∏ k ∈ Finset.Icc 1 (n + 1),
            (gamblerRuinSigma r * Real.cos (Real.pi * k / (n + 2)) - x) = 0 := by
        exact (mul_eq_zero.mp hinner).resolve_left (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))
      rcases Finset.prod_eq_zero_iff.mp hprod with ⟨k, hk, hkzero⟩
      refine ⟨k, hk, ?_⟩
      have hkzero' :
          gamblerRuinSigma r * Real.cos (Real.pi * k / (((n + 2 : ℕ) : ℝ))) = x := by
        simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
          sub_eq_zero.mp hkzero
      exact hkzero'.symm
  · intro hx
    apply hroot.mpr
    rcases hx with rfl | ⟨k, hk, rfl⟩
    · simp
    · have hprod :
        ∏ l ∈ Finset.Icc 1 (n + 1),
          (gamblerRuinSigma r * Real.cos (Real.pi * l / (n + 2)) -
            gamblerRuinSigma r * Real.cos (Real.pi * k / (n + 2))) = 0 := by
        exact Finset.prod_eq_zero_iff.mpr ⟨k, hk, by ring⟩
      simp [hprod]

/-- Helper for Example 18.20: the characteristic polynomial roots are exactly the absorbing root
`1` together with the cosine roots `σ cos (π k / N)` for `k = 1, ..., N - 1`. -/
lemma gamblerRuinCharpoly_isRoot_iff
    (N : ℕ) (hN : 2 ≤ N) {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Polynomial.IsRoot (gamblerRuinTransitionMatrixReal N r).charpoly x ↔
      x = 1 ∨ ∃ k ∈ Finset.Icc 1 (N - 1),
        x = gamblerRuinSigma r * Real.cos (Real.pi * k / N) := by
  -- Route correction: the main theorem is now reduced to this polynomial root description.
  by_cases hrEndpoint : r = 0 ∨ r = 1
  · -- Proof comment: the degenerate endpoint chains are triangular, so their roots are already
    -- handled by the dedicated endpoint lemma.
    exact gamblerRuinCharpoly_isRoot_iff_endpoint N hN hrEndpoint
  have hr0' : 0 < r := by
    have hrne0 : 0 ≠ r := by
      intro h
      exact hrEndpoint (Or.inl h.symm)
    exact lt_of_le_of_ne hr0 hrne0
  have hr1' : r < 1 := by
    have hrne1 : r ≠ 1 := by
      intro h
      exact hrEndpoint (Or.inr h)
    exact lt_of_le_of_ne hr1 hrne1
  -- Proof comment: in the strict branch, the determinant bridge identifies the characteristic
  -- polynomial with the tridiagonal scalar recurrence solved above by Chebyshev polynomials.
  exact gamblerRuinCharpoly_isRoot_iff_interiorEval N hN hr0' hr1'

-- Proof sketch: conjugate the tridiagonal interior block of
-- `gamblerRuinTransitionMatrixReal N r` to a symmetric Toeplitz matrix with off-diagonal entries
-- `sqrt (r * (1 - r))`; its eigenvectors are the sine modes on `Fin (N - 1)`, which yield the
-- eigenvalues `σ cos (kπ / N)`, and the two absorbing boundary states contribute the eigenvalue
-- `1`.
/-- Example 18.20: the spectrum of the real gambler's ruin transition matrix on `{0, ..., N}`
consists of the absorbing eigenvalue `1` together with the values `σ cos (kπ / N)` for
`k = 1, ..., N - 1`. -/
theorem gamblerRuin_spectrum_eq
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    spectrum ℝ (gamblerRuinTransitionMatrixReal N r) =
      {1} ∪ Set.range (gamblerRuinNontrivialEigenvalue N r) := by
  -- Proof comment: transport spectrum membership to characteristic-polynomial roots and then
  -- rewrite the cosine indexing into the `Fin (N - 1)` parametrization from the theorem statement.
  ext x
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
  rw [gamblerRuinCharpoly_isRoot_iff N hN hr0 hr1]
  constructor
  · intro hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · rcases (gamblerRuinNontrivialEigenvalue_range_iff N hN).2 hx with ⟨n, hn⟩
      exact Or.inr ⟨n, hn.symm⟩
  · intro hx
    rcases hx with rfl | ⟨n, hn⟩
    · exact Or.inl rfl
    · exact Or.inr <| (gamblerRuinNontrivialEigenvalue_range_iff N hN).1 ⟨n, hn.symm⟩

/-- Helper for Example 18.20: each explicit cosine mode is bounded by the decay rate
`σ cos (π / N)`. -/
lemma gamblerRuinMode_abs_le_decayRate
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ}
    (n : Fin (N - 1)) :
    |gamblerRuinNontrivialEigenvalue N r n| ≤ gamblerRuinDecayRate N r := by
  let θ : ℝ := (((n : ℕ) : ℝ) + 1) * Real.pi / (N : ℝ)
  have hNreal : (2 : ℝ) ≤ N := by
    exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by
    linarith
  have hpiDiv_nonneg : 0 ≤ Real.pi / (N : ℝ) := by
    exact div_nonneg Real.pi_pos.le hNpos.le
  have hsigma_nonneg : 0 ≤ gamblerRuinSigma r := by
    simp [gamblerRuinSigma]
  have hθ_lower : Real.pi / (N : ℝ) ≤ θ := by
    have hn_nonneg : (0 : ℝ) ≤ (n : ℕ) := by
      exact_mod_cast Nat.zero_le (n : ℕ)
    have hmul : Real.pi ≤ (((n : ℕ) : ℝ) + 1) * Real.pi := by
      nlinarith [Real.pi_pos, hn_nonneg]
    simpa [θ, mul_comm, mul_left_comm, mul_assoc] using
      (div_le_div_iff_of_pos_right hNpos).2 hmul
  have hθ_upper : θ ≤ Real.pi - Real.pi / (N : ℝ) := by
    have hn_upper_nat : (n : ℕ) + 1 ≤ N - 1 := Nat.succ_le_of_lt n.2
    have hN_ge_one : 1 ≤ N := by
      linarith
    have hn_upper : (((n : ℕ) : ℝ) + 1) ≤ ((N - 1 : ℕ) : ℝ) := by
      have hn_upper_cast : (((n : ℕ) + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hn_upper_nat
      simpa [Nat.cast_add] using hn_upper_cast
    have hmul : ((((n : ℕ) : ℝ) + 1) * Real.pi) ≤ ((N - 1 : ℕ) : ℝ) * Real.pi := by
      nlinarith [Real.pi_pos, hn_upper]
    have hdiv :
        θ ≤ (((N - 1 : ℕ) : ℝ) * Real.pi / (N : ℝ)) := by
      simpa [θ, mul_comm, mul_left_comm, mul_assoc] using
        (div_le_div_iff_of_pos_right hNpos).2 hmul
    have hrewrite :
        (((N - 1 : ℕ) : ℝ) * Real.pi / (N : ℝ)) = Real.pi - Real.pi / (N : ℝ) := by
      rw [Nat.cast_sub hN_ge_one]
      norm_num
      have hNne : (N : ℝ) ≠ 0 := by
        positivity
      field_simp [hNne]
    simpa [hrewrite] using hdiv
  have hθ_nonneg : 0 ≤ θ := by
    linarith [hθ_lower, Real.pi_pos]
  have hθ_le_pi : θ ≤ Real.pi := by
    linarith [hθ_upper, hpiDiv_nonneg]
  have habsCos : |Real.cos θ| ≤ Real.cos (Real.pi / (N : ℝ)) := by
    by_cases hhalf : θ ≤ Real.pi / 2
    · -- Proof comment: on `[0, π / 2]`, `cos` is nonnegative and decreases with the angle.
      have hcos_nonneg : 0 ≤ Real.cos θ := by
        refine Real.cos_nonneg_of_mem_Icc ?_
        constructor <;> linarith
      rw [abs_of_nonneg hcos_nonneg]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hpiDiv_nonneg hθ_le_pi hθ_lower
    · have hhalf' : Real.pi / 2 ≤ θ := by
        linarith
      have hmirror_nonneg : 0 ≤ Real.pi - θ := by
        linarith
      have hmirror_le_pi : Real.pi - θ ≤ Real.pi := by
        linarith
      have hmirror_lower : Real.pi / (N : ℝ) ≤ Real.pi - θ := by
        linarith [hθ_upper]
      have hcos_nonpos : Real.cos θ ≤ 0 := by
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hhalf' (by linarith [hθ_le_pi])
      -- Proof comment: on `[π / 2, π]`, reflect across `π / 2` using
      -- `cos (π - θ) = -cos θ`.
      rw [abs_of_nonpos hcos_nonpos, ← Real.cos_pi_sub θ]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hpiDiv_nonneg hmirror_le_pi hmirror_lower
  -- Proof comment: once the cosine mode is bounded, multiply by the nonnegative prefactor `σ`.
  calc
    |gamblerRuinNontrivialEigenvalue N r n|
        = |gamblerRuinSigma r * Real.cos θ| := by
            simp [gamblerRuinNontrivialEigenvalue, θ]
    _ = gamblerRuinSigma r * |Real.cos θ| := by
          rw [abs_mul, abs_of_nonneg hsigma_nonneg]
    _ ≤ gamblerRuinSigma r * Real.cos (Real.pi / (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left habsCos hsigma_nonneg
    _ = gamblerRuinDecayRate N r := by
          simp [gamblerRuinDecayRate]

-- Proof sketch: combine `gamblerRuin_spectrum_eq` with the monotonicity of `cos` on `[0, π]`; the
-- nontrivial eigenvalues are `σ cos (kπ / N)` with `1 ≤ k ≤ N - 1`, so the largest modulus among
-- them is attained at `k = 1` and equals `σ cos (π / N)`.
/-- Every non-absorbing spectral value of the gambler's ruin chain is bounded in modulus by the
explicit rate `σ cos (π / N)`. -/
theorem gamblerRuin_nontrivial_spectral_bound
    (N : ℕ) (hN : 2 ≤ N) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {x : ℝ}
    (hx : x ∈ spectrum ℝ (gamblerRuinTransitionMatrixReal N r)) (hx1 : x ≠ 1) :
    |x| ≤ gamblerRuinDecayRate N r := by
  -- Proof comment: the explicit spectrum theorem reduces every non-absorbing spectral value to one
  -- of the cosine modes.
  have hx' : x = 1 ∨ ∃ n : Fin (N - 1), x = gamblerRuinNontrivialEigenvalue N r n := by
    rw [gamblerRuin_spectrum_eq N hN hr0 hr1] at hx
    rcases hx with hx | hx
    · exact Or.inl (by simpa [Set.mem_singleton_iff] using hx)
    · rcases hx with ⟨n, hn⟩
      exact Or.inr ⟨n, hn.symm⟩
  rcases hx' with rfl | ⟨n, rfl⟩
  · exact (hx1 rfl).elim
  · -- Proof comment: the remaining branch is the standalone mode estimate above.
    exact gamblerRuinMode_abs_le_decayRate N hN n
