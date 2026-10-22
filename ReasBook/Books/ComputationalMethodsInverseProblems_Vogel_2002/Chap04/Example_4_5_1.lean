/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.EMStep
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5_1.JointModel

public section

namespace NonnegativeEM

open scoped BigOperators

/- Example 4.5-extra-2 (1): under the normalized nonnegative setup for `K` and `f`, the model
output `Matrix.mulVec K f` is again a probability vector. -/
#check Matrix.IsColStochasticRect.mulVec_mem_stdSimplex

/- Example 4.5-extra-2 (2): the joint law of `(X, Y)` has mass `K i j * f j` at `(j, i)`. -/
#check jointPmf_apply

/- Example 4.5-extra-2 (3): the marginal law of `Y` is the model vector `Matrix.mulVec K f`. -/
#check observedMarginal_eq_mulVec

/- The canonical `DiscreteEM` parameter family for this nonnegative rectangular model is
`jointFamily`. -/
#check jointFamily

/- The conditional weight `P{X = j | Y = i}` attached to the current iterate `fCurrent` is the
specialized real-valued point mass of `DiscreteEM.posteriorPmf`. -/
#check posteriorWeight

/- The specialized `qFunction` is the weighted sum of the canonical `DiscreteEM.qFunction`
values for the model family `jointFamily`. -/
#check qFunction

/- The EM update associated to equation `(4.66)`. -/
#check emUpdate

/-- Helper for Example 4.5-extra-2: rational coordinates of a simplex point can be lifted to
nonnegative rational coordinates with the same real values. -/
lemma existsNonnegativeRatCoordinates
    {m : ℕ} (g : Fin m → ℝ) (hg : g ∈ stdSimplex ℝ (Fin m))
    (hRat : ∀ i, ∃ q : ℚ, g i = q) :
    ∃ q : Fin m → ℚ≥0, ∀ i, (q i : ℝ) = g i := by
  -- Extract rational representatives and use simplex nonnegativity to promote them to `ℚ≥0`.
  choose qRat hqRat using hRat
  let q : Fin m → ℚ≥0 := fun i ↦
    ⟨qRat i, by
      have hgi : 0 ≤ g i := (mem_Icc_of_mem_stdSimplex hg i).1
      have hqi : 0 ≤ (qRat i : ℝ) := by
        simpa [hqRat i] using hgi
      exact Rat.cast_nonneg.mp hqi⟩
  refine ⟨q, ?_⟩
  intro i
  -- The lift does not change the corresponding real coordinate.
  simpa [q] using (hqRat i).symm

/-- Helper for Example 4.5-extra-2: finitely many nonnegative rational coordinates admit a common
positive denominator whose scaled coordinates are natural numbers. -/
lemma commonDenominatorCounts
    {m : ℕ} (q : Fin m → ℚ≥0) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : Fin m → ℕ, ∀ i, (N i : ℝ) = (r : ℝ) * (q i : ℝ) := by
  let r : ℕ := ∏ i, (q i).den
  let N : Fin m → ℕ := fun i ↦ (q i).num * ∏ j ∈ Finset.univ.erase i, (q j).den
  refine ⟨r, ?_, N, ?_⟩
  · -- Every denominator is positive, so the full product is positive.
    dsimp [r]
    exact Finset.prod_pos fun i _ ↦ NNRat.den_pos (q i)
  · intro i
    -- Split off the `i`-th denominator from the common product and use `q * q.den = q.num`.
    have hsplit :
        (∏ j ∈ Finset.univ.erase i, (q j).den) * (q i).den = r := by
      simpa [r] using
        (Finset.prod_erase_mul
          (Finset.univ)
          (fun j : Fin m ↦ (q j).den)
          (by simp : i ∈ Finset.univ))
    have hmul : ((q i).num : ℝ) = (q i : ℝ) * (q i).den := by
      exact_mod_cast (NNRat.mul_den_eq_num (q i)).symm
    calc
      (N i : ℝ) = ((q i).num : ℝ) * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℝ) := by
        simp [N, Nat.cast_mul, Nat.cast_prod]
      _ = ((q i : ℝ) * (q i).den) * ∏ j ∈ Finset.univ.erase i, ((q j).den : ℝ) := by
        rw [hmul]
      _ = (q i : ℝ) * ((∏ j ∈ Finset.univ.erase i, ((q j).den : ℝ)) * (q i).den) := by
        ring
      _ = (q i : ℝ) * (r : ℝ) := by
        have hsplitReal :
            (∏ j ∈ Finset.univ.erase i, ((q j).den : ℝ)) * (q i).den = (r : ℝ) := by
          exact_mod_cast hsplit
        rw [hsplitReal]
      _ = (r : ℝ) * (q i : ℝ) := by ring

/-- Helper for Example 4.5-extra-2: regrouping a finite sum by the fibers of the observed-value
map `y`. -/
lemma sumOverObservedValues_eq_sumCardMul
    {m r : ℕ} (φ : Fin m → ℝ) (y : Fin r → Fin m) :
    ∑ k, φ (y k) = ∑ i, ((Finset.univ.filter fun k : Fin r ↦ y k = i).card : ℝ) * φ i := by
  -- First rewrite the sum as a sum over observed-value fibers.
  calc
    ∑ k, φ (y k) = ∑ i, ∑ k ∈ Finset.univ with y k = i, φ i := by
      simpa using
        (Finset.sum_fiberwise'
          (s := (Finset.univ : Finset (Fin r)))
          (g := y)
          (f := φ)).symm
    _ = ∑ i, ((Finset.univ.filter fun k : Fin r ↦ y k = i).card : ℝ) * φ i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Helper for Example 4.5-extra-2: the hidden-state fibers over a fixed observed value partition
that observed fiber. -/
lemma pairCountFiberSum_eq_observedCard
    {m n r : ℕ} (x : Fin r → Fin n) (y : Fin r → Fin m) (i : Fin m) :
    ∑ j, (Finset.univ.filter fun k : Fin r ↦ y k = i ∧ x k = j).card =
      (Finset.univ.filter fun k : Fin r ↦ y k = i).card := by
  -- Count the fixed observed fiber by summing the cardinalities of its hidden-state fibers.
  symm
  simpa [Finset.filter_filter, and_assoc, and_left_comm, and_comm] using
    (Finset.card_eq_sum_card_fiberwise
      (f := x)
      (s := Finset.univ.filter fun k : Fin r ↦ y k = i)
      (t := (Finset.univ : Finset (Fin n)))
      (fun k hk ↦ by simp))

/-- Example 4.5-extra-2 (4): if the observed vector `g` has rational coordinates, then there is a
positive sample size `r` whose expected counts `r * g i` are all integers. -/
theorem existsIntegerObservedCounts
    {m : ℕ} (g : Fin m → ℝ) (hg : g ∈ stdSimplex ℝ (Fin m))
    (hRat : ∀ i, ∃ q : ℚ, g i = q) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : Fin m → ℕ, ∀ i, (N i : ℝ) = (r : ℝ) * g i := by
  -- Lift the rational coordinates to `ℚ≥0` and then clear their common denominator.
  obtain ⟨q, hq⟩ := existsNonnegativeRatCoordinates g hg hRat
  obtain ⟨r, hrPos, N, hN⟩ := commonDenominatorCounts q
  refine ⟨r, hrPos, N, ?_⟩
  intro i
  -- Transport the common-denominator identity back from the lifted coordinates to `g`.
  calc
    (N i : ℝ) = (r : ℝ) * (q i : ℝ) := hN i
    _ = (r : ℝ) * g i := by rw [hq i]

/-- Example 4.5-extra-2 (5): for a realization `y` whose counts agree with `N i = r * g i`, the
observed-data log-likelihood is `r * ∑ i, g i * log ((Matrix.mulVec K f) i)`. -/
theorem observedLogLikelihood_eq_weightedLogModel
    {m n r : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (f : Fin n → ℝ) (g : Fin m → ℝ)
    (y : Fin r → Fin m) (N : Fin m → ℕ) (hN : ∀ i, (N i : ℝ) = (r : ℝ) * g i)
    (hy : ∀ i, (Finset.univ.filter fun k : Fin r ↦ y k = i).card = N i) :
    ∑ k, Real.log (Matrix.mulVec K f (y k)) =
      (r : ℝ) * ∑ i, g i * Real.log (Matrix.mulVec K f i) := by
  let φ : Fin m → ℝ := fun i ↦ Real.log (Matrix.mulVec K f i)
  -- Regroup the repeated log terms by observed value and then substitute the count formulas.
  calc
    ∑ k, Real.log (Matrix.mulVec K f (y k)) =
        ∑ i, ((Finset.univ.filter fun k : Fin r ↦ y k = i).card : ℝ) * φ i := by
      simpa [φ] using sumOverObservedValues_eq_sumCardMul φ y
    _ = ∑ i, (N i : ℝ) * φ i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hy i]
    _ = ∑ i, ((r : ℝ) * g i) * φ i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [hN i]
    _ = ∑ i, (r : ℝ) * (g i * φ i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    _ = (r : ℝ) * ∑ i, g i * φ i := by
      rw [Finset.mul_sum]
    _ = (r : ℝ) * ∑ i, g i * Real.log (Matrix.mulVec K f i) := by
      simp [φ]

/-- Example 4.5-extra-2 (6): the pair counts `N i j` for a realization `(x, y)` sum to the
observed counts `N i`; the scaled form `r * g i` is recorded by
`pairCounts_sum_eq_scaledObservedCounts`. -/
theorem pairCounts_sum_eq_observedCounts
    {m n r : ℕ} (x : Fin r → Fin n) (y : Fin r → Fin m)
    (N : Fin m → ℕ) (Nxy : Fin m → Fin n → ℕ)
    (hy : ∀ i, (Finset.univ.filter fun k : Fin r ↦ y k = i).card = N i)
    (hxy : ∀ i j, (Finset.univ.filter fun k : Fin r ↦ y k = i ∧ x k = j).card = Nxy i j) :
    ∀ i, ∑ j, Nxy i j = N i := by
  intro i
  -- Sum the pair counts over the hidden value and rewrite them back to observed counts.
  calc
    ∑ j, Nxy i j =
        ∑ j, (Finset.univ.filter fun k : Fin r ↦ y k = i ∧ x k = j).card := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← hxy i j]
    _ = (Finset.univ.filter fun k : Fin r ↦ y k = i).card :=
      pairCountFiberSum_eq_observedCard x y i
    _ = N i := hy i

/-- Combining `pairCounts_sum_eq_observedCounts` with the displayed identities
`N i = r * g i` gives the scaled-count form after coercion to `ℝ`. -/
theorem pairCounts_sum_eq_scaledObservedCounts
    {m n r : ℕ} (g : Fin m → ℝ) (x : Fin r → Fin n) (y : Fin r → Fin m)
    (N : Fin m → ℕ) (Nxy : Fin m → Fin n → ℕ) (hN : ∀ i, (N i : ℝ) = (r : ℝ) * g i)
    (hy : ∀ i, (Finset.univ.filter fun k : Fin r ↦ y k = i).card = N i)
    (hxy : ∀ i j, (Finset.univ.filter fun k : Fin r ↦ y k = i ∧ x k = j).card = Nxy i j) :
    ∀ i, ((∑ j, Nxy i j : ℕ) : ℝ) = (r : ℝ) * g i := by
  intro i
  exact Eq.trans
    (congrArg (fun t : ℕ ↦ (t : ℝ)) (pairCounts_sum_eq_observedCounts x y N Nxy hy hxy i))
    (hN i)

/- Example 4.5-extra-2 (7): the conditional law of `X` given `Y = i` at the current iterate
`fCurrent` is `K i j * fCurrent j / ∑ l, K i l * fCurrent l`. -/
#check posteriorWeight_eq

/- Example 4.5-extra-2 (8): under the positivity assumptions needed to split the complete-data
log-likelihood, the specialized `qFunction` is the weighted sum
`∑ i ∑ j r * g i * (log (K i j) + log (f j)) * posteriorWeight ... i j`. -/
#check qFunction_eq_weightedPosteriorSum

/- Example 4.5-extra-2 (9): the M-step updates the current iterate by
`fCurrent j * ∑ i, K i j * (g i / ∑ l, K i l * fCurrent l)`. -/
#check emUpdate_apply

end NonnegativeEM
