/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Topology

/-- The `n`th Galton--Watson extinction approximation, obtained by iterating the offspring
probability generating function from `0`. -/
noncomputable abbrev galtonWatsonExtinctionApproximation (p : PMF ℕ) (n : ℕ) : ℝ :=
  Nat.iterate (probabilityGeneratingFunctionReal p) n 0

-- Proof sketch: unfold the zeroth iterate of a function.
/-- The zeroth extinction approximation is `0`. -/
theorem galtonWatsonExtinctionApproximation_zero (p : PMF ℕ) :
    galtonWatsonExtinctionApproximation p 0 = 0 := by
  -- Unfold the zeroth iterate.
  rfl

-- Proof sketch: use the defining recursion of `Nat.iterate` to rewrite the `(n + 1)`st iterate as
-- one further application of the probability generating function to the `n`th iterate.
/-- The extinction approximations satisfy the Galton--Watson recursion `q_(n+1) = ψ(q_n)`. -/
theorem galtonWatsonExtinctionApproximation_succ (p : PMF ℕ) (n : ℕ) :
    galtonWatsonExtinctionApproximation p (n + 1) =
      probabilityGeneratingFunctionReal p (galtonWatsonExtinctionApproximation p n) := by
  -- Rewrite the successor iterate using the recursion for `Nat.iterate`.
  rw [galtonWatsonExtinctionApproximation, Function.iterate_succ_apply']

/-- The Galton--Watson extinction probability, defined as the supremum of the extinction
approximations. -/
noncomputable abbrev galtonWatsonExtinctionProbability (p : PMF ℕ) : ℝ :=
  sSup (Set.range (galtonWatsonExtinctionApproximation p))

-- Proof sketch: this is immediate from the definition of
-- `galtonWatsonExtinctionProbability`.
/-- The extinction probability is the supremum of the iterated extinction approximations. -/
theorem galtonWatsonExtinctionProbability_def (p : PMF ℕ) :
    galtonWatsonExtinctionProbability p =
      sSup (Set.range (galtonWatsonExtinctionApproximation p)) := by
  -- This is just the defining abbreviation.
  rfl

/-- The fixed points of the offspring probability generating function inside the unit interval. -/
noncomputable abbrev galtonWatsonFixedPoints (p : PMF ℕ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩ Function.fixedPoints (probabilityGeneratingFunctionReal p)

-- Proof sketch: unfold `galtonWatsonFixedPoints` and `Function.fixedPoints`; membership is exactly
-- the conjunction of belonging to `[0,1]` and satisfying `ψ(r) = r`.
/-- A point belongs to `galtonWatsonFixedPoints p` exactly when it lies in `[0,1]` and is a fixed
point of the offspring probability generating function. -/
theorem mem_galtonWatsonFixedPoints_iff (p : PMF ℕ) (r : ℝ) :
    r ∈ galtonWatsonFixedPoints p ↔
      r ∈ Set.Icc (0 : ℝ) 1 ∧ probabilityGeneratingFunctionReal p r = r := by
  -- Unfold the intersection with the fixed-point set.
  simp [galtonWatsonFixedPoints, Function.fixedPoints, Function.IsFixedPt]

/-- The expected offspring number of the Galton--Watson law `p`, written as the extended real
series `∑ k p_k`. -/
noncomputable abbrev galtonWatsonOffspringMean (p : PMF ℕ) : ENNReal :=
  ∑' k : ℕ, (k : ENNReal) * p k

-- Proof sketch: unfold `galtonWatsonOffspringMean`.
/-- The offspring mean is the `ENNReal` series `∑' k, k * p k`. -/
theorem galtonWatsonOffspringMean_eq_tsum (p : PMF ℕ) :
    galtonWatsonOffspringMean p = ∑' k : ℕ, (k : ENNReal) * p k := by
  -- This is just the defining abbreviation.
  rfl

/-- The left derivative limit of the offspring probability generating function exists and is
strictly larger than `1`. -/
def probabilityGeneratingFunctionDerivativeLeftLimitGtOne (p : PMF ℕ) : Prop :=
  ∃ l : ENNReal,
    Filter.Tendsto
      (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
      (𝓝[<] (1 : ℝ)) (𝓝 l) ∧ 1 < l

-- Proof sketch: unfold
-- `probabilityGeneratingFunctionDerivativeLeftLimitGtOne`.
/-- The derivative-left-limit condition is the existence of a left limit for `ψ'` at `1` that is
strictly greater than `1`. -/
theorem probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff (p : PMF ℕ) :
    probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
      ∃ l : ENNReal,
        Filter.Tendsto
          (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
          (𝓝[<] (1 : ℝ)) (𝓝 l) ∧ 1 < l := by
  -- The proposition was introduced with exactly this existential form.
  rfl

/-- Helper for Theorem 3.11: the real offspring probability generating function is monotone on the
unit interval. -/
theorem probabilityGeneratingFunctionReal_monotoneOn_unitInterval (p : PMF ℕ) :
    MonotoneOn (probabilityGeneratingFunctionReal p) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hCoeffSummable : Summable (fun n : ℕ ↦ (p n).toReal) := by
    simpa using ENNReal.summable_toReal p.tsum_coe_ne_top
  have hxSummable : Summable (fun n : ℕ ↦ (p n).toReal * x ^ n) := by
    -- The pgf series is dominated termwise by the coefficient series on `[0,1]`.
    refine Summable.of_nonneg_of_le (f := fun n : ℕ ↦ (p n).toReal) (fun n ↦ ?_)
      (fun n ↦ ?_) hCoeffSummable
    · exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hx.1 _)
    · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hx.1 hx.2)
  have hySummable : Summable (fun n : ℕ ↦ (p n).toReal * y ^ n) := by
    -- The same domination argument works at the larger point `y`.
    refine Summable.of_nonneg_of_le (f := fun n : ℕ ↦ (p n).toReal) (fun n ↦ ?_)
      (fun n ↦ ?_) hCoeffSummable
    · exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hy.1 _)
    · exact mul_le_of_le_one_right ENNReal.toReal_nonneg (pow_le_one₀ hy.1 hy.2)
  -- Compare the pgf values termwise.
  rw [probabilityGeneratingFunctionReal_apply, probabilityGeneratingFunctionReal_apply]
  exact hxSummable.tsum_le_tsum
    (fun n ↦
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx.1 hxy n) ENNReal.toReal_nonneg)
    hySummable

/-- Helper for Theorem 3.11: every extinction iterate stays in the unit interval. -/
theorem galtonWatsonExtinctionApproximation_mem_unitInterval (p : PMF ℕ) (n : ℕ) :
    galtonWatsonExtinctionApproximation p n ∈ Set.Icc (0 : ℝ) 1 := by
  induction n with
  | zero =>
      -- The iteration starts from `0`.
      simp [galtonWatsonExtinctionApproximation_zero p]
  | succ n ih =>
      -- Applying the pgf preserves the unit interval.
      rw [galtonWatsonExtinctionApproximation_succ]
      exact probabilityGeneratingFunctionReal_mem_unitInterval p
        ⟨galtonWatsonExtinctionApproximation p n, ih⟩

/-- Helper for Theorem 3.11: the Galton--Watson extinction approximations form an increasing
sequence. -/
theorem galtonWatsonExtinctionApproximation_le_succ (p : PMF ℕ) (n : ℕ) :
    galtonWatsonExtinctionApproximation p n ≤ galtonWatsonExtinctionApproximation p (n + 1) := by
  induction n with
  | zero =>
      -- The first iterate is nonnegative because the pgf is nonnegative on `[0,1]`.
      rw [galtonWatsonExtinctionApproximation_zero, galtonWatsonExtinctionApproximation_succ]
      exact probabilityGeneratingFunctionReal_nonneg p ⟨0, by simp, by simp⟩
  | succ n ih =>
      -- Monotonicity of the pgf propagates the stepwise inequality.
      rw [galtonWatsonExtinctionApproximation_succ, galtonWatsonExtinctionApproximation_succ]
      exact probabilityGeneratingFunctionReal_monotoneOn_unitInterval p
        (galtonWatsonExtinctionApproximation_mem_unitInterval p n)
        (galtonWatsonExtinctionApproximation_mem_unitInterval p (n + 1))
        ih

/-- Helper for Theorem 3.11: the extinction approximations are monotone increasing in the iterate
index. -/
theorem galtonWatsonExtinctionApproximation_monotone (p : PMF ℕ) :
    Monotone (galtonWatsonExtinctionApproximation p) := by
  -- Upgrade the stepwise inequality to monotonicity on `ℕ`.
  exact monotone_nat_of_le_succ (galtonWatsonExtinctionApproximation_le_succ p)

/-- Helper for Theorem 3.11: the extinction probability itself still lies in `[0,1]`. -/
theorem galtonWatsonExtinctionProbability_mem_unitInterval (p : PMF ℕ) :
    galtonWatsonExtinctionProbability p ∈ Set.Icc (0 : ℝ) 1 := by
  have hBdd : BddAbove (Set.range (galtonWatsonExtinctionApproximation p)) := by
    -- Every iterate is bounded above by `1`.
    refine ⟨1, ?_⟩
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact (galtonWatsonExtinctionApproximation_mem_unitInterval p n).2
  rw [galtonWatsonExtinctionProbability_def]
  refine ⟨?_, ?_⟩
  · -- The initial iterate `0` witnesses the lower bound.
    exact le_csSup hBdd (Set.mem_range_self 0)
  · -- The upper bound comes from the unit-interval bounds on the whole range.
    refine csSup_le (Set.range_nonempty _) ?_
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact (galtonWatsonExtinctionApproximation_mem_unitInterval p n).2

/-- Helper for Theorem 3.11: every fixed point in `[0,1]` dominates every extinction iterate. -/
theorem galtonWatsonExtinctionApproximation_le_of_mem_fixedPoints
    (p : PMF ℕ) {r : ℝ} (hr : r ∈ galtonWatsonFixedPoints p) :
    ∀ n : ℕ, galtonWatsonExtinctionApproximation p n ≤ r := by
  rcases (mem_galtonWatsonFixedPoints_iff p r).1 hr with ⟨hrIcc, hrFix⟩
  intro n
  induction n with
  | zero =>
      -- The iteration starts at `0`, which is below every point in `[0,1]`.
      simpa [galtonWatsonExtinctionApproximation_zero p] using hrIcc.1
  | succ n ih =>
      -- Apply monotonicity of the pgf and use that `r` is fixed.
      rw [galtonWatsonExtinctionApproximation_succ]
      simpa [hrFix] using
        probabilityGeneratingFunctionReal_monotoneOn_unitInterval p
          (galtonWatsonExtinctionApproximation_mem_unitInterval p n) hrIcc ih

/-- Helper for Theorem 3.11: the extinction probability is the least fixed point of the pgf on
`[0,1]`. -/
theorem galtonWatsonExtinctionProbability_isLeastFixedPoint (p : PMF ℕ) :
    galtonWatsonExtinctionProbability p ∈ galtonWatsonFixedPoints p ∧
      ∀ {r : ℝ}, r ∈ galtonWatsonFixedPoints p → galtonWatsonExtinctionProbability p ≤ r := by
  have hMono := galtonWatsonExtinctionApproximation_monotone p
  have hBounds : ∀ n : ℕ, galtonWatsonExtinctionApproximation p n ∈ Set.Icc (0 : ℝ) 1 :=
    galtonWatsonExtinctionApproximation_mem_unitInterval p
  have hBddIci : BddAbove ((galtonWatsonExtinctionApproximation p) '' Set.Ici 0) := by
    -- The iterate sequence stays below `1`, so its tail from `0` is bounded above.
    refine ⟨1, ?_⟩
    intro x hx
    rcases hx with ⟨n, -, rfl⟩
    exact (hBounds n).2
  have hRangeEq :
      (galtonWatsonExtinctionApproximation p) '' Set.Ici 0 =
        Set.range (galtonWatsonExtinctionApproximation p) := by
    -- On `ℕ`, the tail `Set.Ici 0` is the whole range of iterates.
    ext x
    constructor
    · intro hx
      rcases hx with ⟨n, -, rfl⟩
      exact Set.mem_range_self n
    · intro hx
      rcases hx with ⟨n, rfl⟩
      exact ⟨n, Nat.zero_le n, rfl⟩
  have hTendsto :
      Filter.Tendsto (galtonWatsonExtinctionApproximation p) Filter.atTop
        (𝓝 (galtonWatsonExtinctionProbability p)) := by
    -- Monotone convergence identifies the iterate limit with the supremum defining `q`.
    rw [galtonWatsonExtinctionProbability_def, ← hRangeEq]
    refine Real.tendsto_atTop_csSup_of_monotoneOn_bddAbove_nat_Ici ?_ hBddIci
    intro m hm n hn hmn
    exact hMono hmn
  have hqIcc : galtonWatsonExtinctionProbability p ∈ Set.Icc (0 : ℝ) 1 :=
    galtonWatsonExtinctionProbability_mem_unitInterval p
  have hTendstoWithin :
      Filter.Tendsto (galtonWatsonExtinctionApproximation p) Filter.atTop
        (𝓝[Set.Icc (0 : ℝ) 1] (galtonWatsonExtinctionProbability p)) := by
    -- The convergent iterate sequence eventually stays in the interval because every term does.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      (galtonWatsonExtinctionApproximation p) hTendsto ?_
    exact Filter.Eventually.of_forall hBounds
  have hContWithin :
      ContinuousWithinAt (probabilityGeneratingFunctionReal p) (Set.Icc (0 : ℝ) 1)
        (galtonWatsonExtinctionProbability p) :=
    probabilityGeneratingFunctionReal_continuousOn_unitInterval p _ hqIcc
  have hMapTendsto :
      Filter.Tendsto
        (fun n ↦
          probabilityGeneratingFunctionReal p (galtonWatsonExtinctionApproximation p n))
        Filter.atTop (𝓝 (probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p))) := by
    -- Continuity on `[0,1]` lets us pass the iterate limit through one more application of `ψ`.
    exact hContWithin.tendsto.comp hTendstoWithin
  have hSuccTendsto :
      Filter.Tendsto (fun n ↦ galtonWatsonExtinctionApproximation p (n + 1)) Filter.atTop
        (𝓝 (galtonWatsonExtinctionProbability p)) := by
    -- Shifting a convergent sequence by one index preserves its limit.
    exact (Filter.tendsto_add_atTop_iff_nat 1).2 hTendsto
  have hFix :
      probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p) =
        galtonWatsonExtinctionProbability p := by
    -- Compare the two descriptions of the successor sequence limit.
    refine tendsto_nhds_unique ?_ hSuccTendsto
    simpa [galtonWatsonExtinctionApproximation_succ] using hMapTendsto
  refine ⟨?_, ?_⟩
  · -- The limit point `q` is a fixed point inside `[0,1]`.
    exact (mem_galtonWatsonFixedPoints_iff p (galtonWatsonExtinctionProbability p)).2
      ⟨hqIcc, hFix⟩
  · intro r hr
    -- Any fixed point dominates every iterate, hence also their supremum.
    rw [galtonWatsonExtinctionProbability_def]
    refine csSup_le ?_ ?_
    · exact Set.range_nonempty _
    · intro x hx
      rcases hx with ⟨n, rfl⟩
      exact galtonWatsonExtinctionApproximation_le_of_mem_fixedPoints p hr n

/-- Helper for Theorem 3.11: the left derivative condition at `1` is equivalent to the offspring
mean being strictly larger than `1`. -/
theorem probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff_offspringMean_gt_one
    (p : PMF ℕ) :
    probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔ 1 < galtonWatsonOffspringMean p := by
  constructor
  · intro h
    rcases h with ⟨l, hl, hlt⟩
    have hMean :
        Filter.Tendsto
          (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
          (𝓝[<] (1 : ℝ)) (𝓝 (galtonWatsonOffspringMean p)) := by
      -- Specialize Theorem 3.2 to the first derivative and rewrite the factorial moment.
      simpa [galtonWatsonOffspringMean, iteratedDeriv_one, Nat.descFactorial_one, mul_comm] using
        probabilityGeneratingFunctionReal_iteratedDeriv_tendsto_left_one p 1
    have hlEq : l = galtonWatsonOffspringMean p := tendsto_nhds_unique hl hMean
    simpa [hlEq] using hlt
  · intro hMean
    -- Use the known first-derivative limit with the offspring mean as witness.
    refine ⟨galtonWatsonOffspringMean p, ?_, hMean⟩
    simpa [galtonWatsonOffspringMean, iteratedDeriv_one, Nat.descFactorial_one, mul_comm] using
      probabilityGeneratingFunctionReal_iteratedDeriv_tendsto_left_one p 1

/-- Helper for Theorem 3.11: if all offspring mass above `1` vanishes, then the real pgf is the
affine map `z ↦ p 0 + p 1 * z`. -/
theorem probabilityGeneratingFunctionReal_eq_p0_add_p1_mul_of_no_mass_ge_two
    (p : PMF ℕ) (hlin : ∀ k : ℕ, 2 ≤ k → p k = 0) (z : ℝ) :
    probabilityGeneratingFunctionReal p z = (p 0).toReal + (p 1).toReal * z := by
  let f : ℕ → ℝ := fun n ↦ (p n).toReal * z ^ n
  have htail : Summable (fun n : ℕ ↦ f (n + 2)) := by
    -- Past degree `1`, every coefficient vanishes identically.
    simp [f, hlin, Nat.le_add_left 2]
  have hsum : Summable f := (summable_nat_add_iff 2).1 htail
  have hsplit := Summable.sum_add_tsum_nat_add 2 hsum
  have htailZero : ∑' n : ℕ, f (n + 2) = 0 := by
    -- The tail sum collapses because each tail term is already zero.
    simp [f, hlin, Nat.le_add_left 2]
  -- Split the series after the first two terms and discard the zero tail.
  rw [probabilityGeneratingFunctionReal_apply]
  calc
    ∑' n : ℕ, f n = ∑ n ∈ Finset.range 2, f n + ∑' n : ℕ, f (n + 2) := by
      symm
      exact hsplit
    _ = ∑ n ∈ Finset.range 2, f n := by rw [htailZero, add_zero]
    _ = (p 0).toReal + (p 1).toReal * z := by
      simp [f, Finset.sum_range_succ]

/-- Helper for Theorem 3.11: the second derivative of the real pgf is strictly positive on
`(0,1)` as soon as some offspring mass sits at degree at least `2`. -/
theorem probabilityGeneratingFunctionReal_deriv2_pos_on_unitIntervalInterior_of_exists_mass_ge_two
    (p : PMF ℕ) (hmass : ∃ k : ℕ, 2 ≤ k ∧ p k ≠ 0) {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < (deriv^[2] (probabilityGeneratingFunctionReal p)) x := by
  rcases hmass with ⟨k, hk2, hkNe⟩
  let m : ℕ := k - 2
  have hm : m + 2 = k := by
    dsimp [m]
    exact Nat.sub_add_cancel hk2
  have hkNe' : p (m + 2) ≠ 0 := by
    simpa [hm] using hkNe
  have hseries :
      ENNReal.ofReal ((deriv^[2] (probabilityGeneratingFunctionReal p)) x) =
        ∑' n : ℕ,
          p (n + 2) * (Nat.descFactorial (n + 2) 2 : ENNReal) * ENNReal.ofReal (x ^ n) := by
    -- Rewrite the second derivative through the shifted derivative series from Theorem 3.2.
    simpa [iteratedDeriv_eq_iterate] using
      probabilityGeneratingFunctionReal_iteratedDeriv_eq_series_ennreal p 2 hx
  have hdescNatPos : 0 < Nat.descFactorial (m + 2) 2 := by
    -- At degree at least `2`, the descending factorial factor is strictly positive.
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
    exact Nat.mul_pos (by omega) (by omega)
  have htermPos :
      0 <
        p (m + 2) * (Nat.descFactorial (m + 2) 2 : ENNReal) * ENNReal.ofReal (x ^ m) := by
    have hpPos : 0 < p (m + 2) := bot_lt_iff_ne_bot.mpr hkNe'
    have hdescPos : 0 < (Nat.descFactorial (m + 2) 2 : ENNReal) := by
      exact_mod_cast hdescNatPos
    have hpowPos : 0 < ENNReal.ofReal (x ^ m) := by
      exact ENNReal.ofReal_pos.mpr (pow_pos hx.1 _)
    -- The witness term indexed by `m = k - 2` is strictly positive.
    have hmulPos : 0 < p (m + 2) * (Nat.descFactorial (m + 2) 2 : ENNReal) :=
      ENNReal.mul_pos hpPos.ne' hdescPos.ne'
    exact ENNReal.mul_pos hmulPos.ne' hpowPos.ne'
  have htermLe :
      p (m + 2) * (Nat.descFactorial (m + 2) 2 : ENNReal) * ENNReal.ofReal (x ^ m) ≤
        ENNReal.ofReal ((deriv^[2] (probabilityGeneratingFunctionReal p)) x) := by
    -- A single nonnegative summand is bounded above by the full `ENNReal` series.
    rw [hseries]
    exact ENNReal.le_tsum m
  have hpos :
      0 < ENNReal.ofReal ((deriv^[2] (probabilityGeneratingFunctionReal p)) x) :=
    lt_of_lt_of_le htermPos htermLe
  exact ENNReal.ofReal_pos.mp hpos

/-- Helper for Theorem 3.11: if there is offspring mass at some degree at least `2`, then the real
pgf is strictly convex on the whole unit interval. -/
theorem probabilityGeneratingFunctionReal_strictConvexOn_unitInterval_of_exists_mass_ge_two
    (p : PMF ℕ) (hmass : ∃ k : ℕ, 2 ≤ k ∧ p k ≠ 0) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (probabilityGeneratingFunctionReal p) := by
  -- Strict positivity of the second derivative upgrades continuity to strict convexity.
  refine strictConvexOn_of_deriv2_pos (convex_Icc (0 : ℝ) 1)
    (probabilityGeneratingFunctionReal_continuousOn_unitInterval p) ?_
  intro x hx
  have hxIoo : x ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa using hx
  exact
    probabilityGeneratingFunctionReal_deriv2_pos_on_unitIntervalInterior_of_exists_mass_ge_two
      p hmass hxIoo

/-- Helper for Theorem 3.11: `1` is always a fixed point of the real offspring pgf on `[0,1]`. -/
theorem one_mem_galtonWatsonFixedPoints (p : PMF ℕ) : (1 : ℝ) ∈ galtonWatsonFixedPoints p := by
  -- The pgf fixes `1` because the PMF coefficients sum to `1`.
  refine (mem_galtonWatsonFixedPoints_iff p 1).2 ?_
  constructor
  · simp
  · rw [probabilityGeneratingFunctionReal_apply]
    have hp_tsum : ∑' n : ℕ, (p n).toReal = 1 := by
      rw [← ENNReal.toReal_one, ← p.tsum_coe, ENNReal.tsum_toReal_eq]
      intro n
      exact p.apply_ne_top n
    simpa using hp_tsum

/-- Helper for Theorem 3.11: in the affine branch with no offspring mass above `1`, every fixed
point in `[0,1]` must be `1`. -/
theorem galtonWatson_fixedPoint_eq_one_of_no_mass_ge_two
    (p : PMF ℕ) (hp1 : p 1 ≠ 1) (hlin : ∀ k : ℕ, 2 ≤ k → p k = 0) {r : ℝ}
    (hr : r ∈ galtonWatsonFixedPoints p) : r = 1 := by
  rcases (mem_galtonWatsonFixedPoints_iff p r).1 hr with ⟨hrIcc, hrFix⟩
  have hLinearAtR := probabilityGeneratingFunctionReal_eq_p0_add_p1_mul_of_no_mass_ge_two p hlin r
  have hLinearAtOne :=
    probabilityGeneratingFunctionReal_eq_p0_add_p1_mul_of_no_mass_ge_two p hlin 1
  have hpsiOne :
      probabilityGeneratingFunctionReal p 1 = 1 :=
    (mem_galtonWatsonFixedPoints_iff p 1).1 (one_mem_galtonWatsonFixedPoints p) |>.2
  have hp01 : (p 0).toReal + (p 1).toReal = 1 := by
    -- In the affine branch, evaluating the pgf at `1` leaves only the masses at `0` and `1`.
    calc
      (p 0).toReal + (p 1).toReal = (p 0).toReal + (p 1).toReal * 1 := by ring
      _ = probabilityGeneratingFunctionReal p 1 := by simpa using hLinearAtOne.symm
      _ = 1 := hpsiOne
  have hp1LeENN : p 1 ≤ 1 := by
    simpa [p.tsum_coe] using (ENNReal.le_tsum (f := fun n : ℕ ↦ p n) 1)
  have hp1Le : (p 1).toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (p.apply_ne_top 1) ENNReal.one_ne_top).2 hp1LeENN
  have hp1NeReal : (p 1).toReal ≠ 1 := by
    intro hp1Eq
    apply hp1
    exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top 1) ENNReal.one_ne_top).mp hp1Eq
  have hp1Lt : (p 1).toReal < 1 := lt_of_le_of_ne hp1Le hp1NeReal
  have hFactor : (1 - (p 1).toReal) * (1 - r) = 0 := by
    -- Rewrite the fixed-point equation into the affine factorization.
    nlinarith [hrFix, hLinearAtR, hp01]
  have hOneSubPos : 0 < 1 - (p 1).toReal := by
    linarith
  have hOneSubR : 1 - r = 0 := by
    -- The nonzero affine factor forces the remaining factor to vanish.
    nlinarith [hFactor, hOneSubPos, hrIcc.2]
  linarith

/-- Helper for Theorem 3.11: every secant slope from `x < 1` to `1` is bounded above by the
offspring mean. -/
theorem probabilityGeneratingFunctionReal_secantSlope_le_offspringMean
    (p : PMF ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hx1 : x < 1) :
    ENNReal.ofReal ((1 - probabilityGeneratingFunctionReal p x) / (1 - x)) ≤
      galtonWatsonOffspringMean p := by
  have hContDiff := probabilityGeneratingFunctionReal_contDiffOn_unitIntervalInterior p
  have hCont :
      ContinuousOn (probabilityGeneratingFunctionReal p) (Set.Icc x 1) := by
    -- Restrict continuity on `[0,1]` to the shorter interval `[x,1]`.
    refine (probabilityGeneratingFunctionReal_continuousOn_unitInterval p).mono ?_
    intro z hz
    exact ⟨le_trans hx.1 hz.1, hz.2⟩
  have hDiff :
      DifferentiableOn ℝ (probabilityGeneratingFunctionReal p) (Set.Ioo x 1) := by
    intro z hz
    -- Interior differentiability comes from the `C^∞` regularity on `(0,1)`.
    have hzIoo : z ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 hz.1, hz.2⟩
    have hzDiff :
        DifferentiableAt ℝ (probabilityGeneratingFunctionReal p) z := by
      exact (hContDiff.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hzIoo)).differentiableAt (by simp)
    exact hzDiff.differentiableWithinAt
  rcases exists_deriv_eq_slope' (probabilityGeneratingFunctionReal p) hx1 hCont hDiff with
    ⟨c, hc, hcSlope⟩
  have hDerivLe :
      ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) c) ≤
        galtonWatsonOffspringMean p := by
    -- Compare the derivative at the MVT point with the factorial-moment bound from Theorem 3.2.
    have hcIoo : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 hc.1, hc.2⟩
    simpa [galtonWatsonOffspringMean_eq_tsum, iteratedDeriv_eq_iterate, mul_comm] using
      probabilityGeneratingFunctionReal_iteratedDeriv_le_factorialMoment_tsum p 1 hcIoo
  have hpsiOne :
      probabilityGeneratingFunctionReal p 1 = 1 :=
    (mem_galtonWatsonFixedPoints_iff p 1).1 (one_mem_galtonWatsonFixedPoints p) |>.2
  -- Rewrite the MVT slope as the secant expression ending at the fixed point `1`.
  simpa [hcSlope, slope_def_field, hpsiOne] using hDerivLe

-- Proof sketch: use strict convexity of the offspring generating function under `p 1 ≠ 1`,
-- identify `q` as the minimal fixed point obtained from the Galton--Watson extinction
-- approximations, and then show that the only fixed points in `[0,1]` are `q` and `1`.
/-- The fixed points of the Galton--Watson offspring generating function in `[0,1]` are exactly the
extinction probability and `1`. -/
theorem galtonWatson_fixedPoints_eq_extinctionProbability_or_one (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    galtonWatsonFixedPoints p = ({galtonWatsonExtinctionProbability p, (1 : ℝ)} : Set ℝ) := by
  -- Route correction: the right first step is the least-fixed-point theorem, not blanket
  -- strict convexity from `hp1`.
  have hLeast := galtonWatsonExtinctionProbability_isLeastFixedPoint p
  have hOne : (1 : ℝ) ∈ galtonWatsonFixedPoints p := one_mem_galtonWatsonFixedPoints p
  ext r
  constructor
  · intro hr
    rcases (mem_galtonWatsonFixedPoints_iff p r).1 hr with ⟨hrIcc, hrFix⟩
    by_cases hmass : ∃ k : ℕ, 2 ≤ k ∧ p k ≠ 0
    · have hStrict :
          StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (probabilityGeneratingFunctionReal p) :=
        probabilityGeneratingFunctionReal_strictConvexOn_unitInterval_of_exists_mass_ge_two p hmass
      by_cases hrq : r = galtonWatsonExtinctionProbability p
      · simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inl hrq
      · by_cases hr1 : r = 1
        · simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using Or.inr hr1
        · have hqLeR : galtonWatsonExtinctionProbability p ≤ r := hLeast.2 hr
          have hqLtR : galtonWatsonExtinctionProbability p < r := by
            exact lt_of_le_of_ne hqLeR (by simpa [eq_comm] using hrq)
          have hrLtOne : r < 1 := lt_of_le_of_ne hrIcc.2 hr1
          have hqIcc :
              galtonWatsonExtinctionProbability p ∈ Set.Icc (0 : ℝ) 1 := hLeast.1.1
          let a : ℝ := (1 - r) / (1 - galtonWatsonExtinctionProbability p)
          let b : ℝ := (r - galtonWatsonExtinctionProbability p) /
            (1 - galtonWatsonExtinctionProbability p)
          have hDenPos : 0 < 1 - galtonWatsonExtinctionProbability p := by
            linarith
          have haPos : 0 < a := by
            dsimp [a]
            have hNumPos : 0 < 1 - r := by
              linarith
            exact div_pos hNumPos hDenPos
          have hbPos : 0 < b := by
            dsimp [b]
            exact div_pos (sub_pos.mpr hqLtR) hDenPos
          have hab : a + b = 1 := by
            -- These are exactly the barycentric coordinates of `r` between `q` and `1`.
            dsimp [a, b]
            field_simp [hDenPos.ne']
            ring
          have hrCombo :
              a * galtonWatsonExtinctionProbability p + b * (1 : ℝ) = r := by
            -- The chosen coefficients interpolate from `q` to `r`.
            dsimp [a, b]
            field_simp [hDenPos.ne']
            ring
          have hrCombo' :
              a * galtonWatsonExtinctionProbability p + b = r := by
            simpa using hrCombo
          have hStrictAtR :
              probabilityGeneratingFunctionReal p r <
                a * probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p) +
                  b * probabilityGeneratingFunctionReal p 1 := by
            -- Strict convexity rules out a third fixed point strictly between `q` and `1`.
            have :=
              hStrict.2 (x := galtonWatsonExtinctionProbability p) hqIcc (y := (1 : ℝ))
                (by simp) (by linarith) haPos hbPos hab
            simpa [smul_eq_mul, hrCombo'] using this
          have hqFix :
              probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p) =
                galtonWatsonExtinctionProbability p := hLeast.1.2
          have hOneFix : probabilityGeneratingFunctionReal p 1 = 1 :=
            (mem_galtonWatsonFixedPoints_iff p 1).1 hOne |>.2
          have : r < r := by
            nlinarith [hStrictAtR, hqFix, hOneFix, hrFix, hrCombo]
          exact (lt_irrefl _ this).elim
    · push Not at hmass
      have hrEqOne :
          r = 1 := galtonWatson_fixedPoint_eq_one_of_no_mass_ge_two p hp1 hmass hr
      have hqEqOne :
          galtonWatsonExtinctionProbability p = 1 :=
        galtonWatson_fixedPoint_eq_one_of_no_mass_ge_two p hp1 hmass hLeast.1
      simpa [hrEqOne, hqEqOne, Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro hr
    -- The two advertised points are indeed fixed points in `[0,1]`.
    rcases hr with rfl | rfl
    · exact hLeast.1
    · exact hOne

-- Proof sketch: combine the strict-convexity fixed-point picture near `1` with the existence and
-- identification of the left limit of `ψ'` at `1`, then rewrite that limit as the offspring mean
-- using the first-derivative case of the pgf derivative formula.
/-- The extinction probability is strictly less than `1` exactly when the left limit of `ψ'` at
`1` is greater than `1`, equivalently when the offspring mean exceeds `1`. -/
theorem galtonWatson_extinctionProbability_lt_one_iff_derivativeLeftLimit_gt_one_iff_offspringMean_gt_one
    (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    ((galtonWatsonExtinctionProbability p < 1 ↔
        probabilityGeneratingFunctionDerivativeLeftLimitGtOne p) ∧
      (probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
        1 < galtonWatsonOffspringMean p)) := by
  -- Route correction: repair the malformed nested `↔` into the two textbook equivalences.
  have hMean :
      probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
        1 < galtonWatsonOffspringMean p :=
    probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff_offspringMean_gt_one p
  have hExt :
      galtonWatsonExtinctionProbability p < 1 ↔
        probabilityGeneratingFunctionDerivativeLeftLimitGtOne p := by
    have hFixed := galtonWatson_fixedPoints_eq_extinctionProbability_or_one p hp1
    constructor
    · intro hqLtOne
      by_cases hmass : ∃ k : ℕ, 2 ≤ k ∧ p k ≠ 0
      · have hStrict :
            StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (probabilityGeneratingFunctionReal p) :=
          probabilityGeneratingFunctionReal_strictConvexOn_unitInterval_of_exists_mass_ge_two p hmass
        have hqIcc :
            galtonWatsonExtinctionProbability p ∈ Set.Icc (0 : ℝ) 1 :=
          galtonWatsonExtinctionProbability_mem_unitInterval p
        let x : ℝ := (galtonWatsonExtinctionProbability p + 1) / 2
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := by
          dsimp [x]
          constructor
          · nlinarith [hqIcc.1]
          · nlinarith [hqIcc.2]
        have hxLtOne : x < 1 := by
          dsimp [x]
          nlinarith
        have hMid :
            probabilityGeneratingFunctionReal p
                ((1 / 2 : ℝ) * galtonWatsonExtinctionProbability p + (1 / 2 : ℝ) * 1) <
              (1 / 2 : ℝ) *
                  probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p) +
                (1 / 2 : ℝ) * probabilityGeneratingFunctionReal p 1 := by
          -- Evaluate strict convexity at the midpoint between `q` and `1`.
          exact hStrict.2 hqIcc (by simp) (by linarith) (by norm_num) (by norm_num) (by norm_num)
        have hqFix :
            probabilityGeneratingFunctionReal p (galtonWatsonExtinctionProbability p) =
              galtonWatsonExtinctionProbability p :=
          (galtonWatsonExtinctionProbability_isLeastFixedPoint p).1.2
        have hOneFix : probabilityGeneratingFunctionReal p 1 = 1 :=
          (mem_galtonWatsonFixedPoints_iff p 1).1 (one_mem_galtonWatsonFixedPoints p) |>.2
        have hψxLt : probabilityGeneratingFunctionReal p x < x := by
          -- The midpoint lies strictly below the chord through the two fixed endpoints.
          have hxMid :
              ((1 / 2 : ℝ) * galtonWatsonExtinctionProbability p + (1 / 2 : ℝ) * 1) = x := by
            dsimp [x]
            ring
          rw [hxMid, hqFix, hOneFix, hxMid] at hMid
          exact hMid
        have hSecantGt : 1 < (1 - probabilityGeneratingFunctionReal p x) / (1 - x) := by
          have hDenPos : 0 < 1 - x := by
            dsimp [x]
            linarith
          exact (one_lt_div hDenPos).2 (by linarith [hψxLt])
        have hSecantLe :
            ENNReal.ofReal ((1 - probabilityGeneratingFunctionReal p x) / (1 - x)) ≤
              galtonWatsonOffspringMean p :=
          probabilityGeneratingFunctionReal_secantSlope_le_offspringMean p hxIcc hxLtOne
        have hMeanGt : 1 < galtonWatsonOffspringMean p := by
          -- A secant slope above `1` forces the offspring mean above `1`.
          exact
            lt_of_lt_of_le
              ((ENNReal.one_lt_ofReal).2 hSecantGt)
              hSecantLe
        exact hMean.mpr hMeanGt
      · push Not at hmass
        have hqEqOne :
            galtonWatsonExtinctionProbability p = 1 :=
          galtonWatson_fixedPoint_eq_one_of_no_mass_ge_two p hp1 hmass
            (galtonWatsonExtinctionProbability_isLeastFixedPoint p).1
        exact (lt_irrefl _ (hqEqOne ▸ hqLtOne)).elim
    · intro hDeriv
      by_cases hmass : ∃ k : ℕ, 2 ≤ k ∧ p k ≠ 0
      · have hStrict :
            StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) (probabilityGeneratingFunctionReal p) :=
          probabilityGeneratingFunctionReal_strictConvexOn_unitInterval_of_exists_mass_ge_two p hmass
        have hConvex := hStrict.convexOn
        have hContDiff := probabilityGeneratingFunctionReal_contDiffOn_unitIntervalInterior p
        rcases (probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff p).1 hDeriv with
          ⟨l, hl, hlGt⟩
        have hDerivEvent :
            ∀ᶠ z in 𝓝[<] (1 : ℝ),
              1 < ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z) := by
          exact (tendsto_order.1 hl).1 1 hlGt
        have hIooEvent : ∀ᶠ z in 𝓝[<] (1 : ℝ), z ∈ Set.Ioo (0 : ℝ) 1 := by
          have hmem :
              Set.Ioi (0 : ℝ) ∩ Set.Iio (1 : ℝ) ∈ 𝓝[<] (1 : ℝ) := by
            rw [nhdsWithin, Filter.mem_inf_iff]
            exact ⟨Set.Ioi (0 : ℝ), Ioi_mem_nhds zero_lt_one, Set.Iio (1 : ℝ), by simp, rfl⟩
          refine Filter.mem_of_superset hmem ?_
          intro z hz
          exact ⟨hz.1, hz.2⟩
        rcases Filter.Eventually.exists (hIooEvent.and hDerivEvent) with ⟨x, hxIoo, hxDeriv⟩
        have hxDiff :
            DifferentiableAt ℝ (probabilityGeneratingFunctionReal p) x :=
          (hContDiff.contDiffAt (IsOpen.mem_nhds isOpen_Ioo hxIoo)).differentiableAt (by simp)
        have hxDerivWithin :
            derivWithin (probabilityGeneratingFunctionReal p) (Set.Ioi x) x =
              deriv (probabilityGeneratingFunctionReal p) x := by
          exact hxDiff.derivWithin (uniqueDiffWithinAt_Ioi x)
        have hSlopeGe :
            deriv (probabilityGeneratingFunctionReal p) x ≤
              slope (probabilityGeneratingFunctionReal p) x 1 := by
          -- Convexity forces the secant slope to dominate the derivative at an interior point.
          simpa [hxDerivWithin] using
            hConvex.rightDeriv_le_slope_of_mem_interior
              (by simpa using hxIoo) (by simp) hxIoo.2
        have hxDerivGt : 1 < deriv (probabilityGeneratingFunctionReal p) x :=
          ENNReal.one_lt_ofReal.mp hxDeriv
        have hpsiOne :
            probabilityGeneratingFunctionReal p 1 = 1 :=
          (mem_galtonWatsonFixedPoints_iff p 1).1 (one_mem_galtonWatsonFixedPoints p) |>.2
        have hψxLt : probabilityGeneratingFunctionReal p x < x := by
          have hSlopeGt :
              1 < slope (probabilityGeneratingFunctionReal p) x 1 :=
            lt_of_lt_of_le hxDerivGt hSlopeGe
          rw [slope_def_field, hpsiOne] at hSlopeGt
          have hDenPos : 0 < 1 - x := by
            nlinarith [hxIoo.2]
          -- A secant slope above `1` means the graph lies below the diagonal at `x`.
          have hNumGt : 1 - x < 1 - probabilityGeneratingFunctionReal p x :=
            (one_lt_div hDenPos).1 hSlopeGt
          linarith
        let g : ℝ → ℝ := fun z ↦ probabilityGeneratingFunctionReal p z - z
        have hgCont : ContinuousOn g (Set.Icc (0 : ℝ) x) := by
          -- The comparison function `g = ψ - id` is continuous on `[0,x]`.
          refine
            ((probabilityGeneratingFunctionReal_continuousOn_unitInterval p).mono ?_).sub
              continuousOn_id
          intro z hz
          exact ⟨hz.1, le_trans hz.2 hxIoo.2.le⟩
        have hg0Nonneg : 0 ≤ g 0 := by
          -- At the origin, `g` is just the nonnegative value `ψ(0)`.
          dsimp [g]
          simpa using probabilityGeneratingFunctionReal_nonneg p ⟨0, by simp, by simp⟩
        have hgxNeg : g x < 0 := by
          -- At the chosen interior point, the graph already lies below the diagonal.
          dsimp [g]
          linarith
        have hZeroMem : (0 : ℝ) ∈ Set.Icc (g x) (g 0) := by
          constructor <;> linarith
        have hRoot : (0 : ℝ) ∈ g '' Set.Icc (0 : ℝ) x := by
          exact intermediate_value_Icc' hxIoo.1.le hgCont hZeroMem
        rcases hRoot with ⟨r, hrIcc, hrZero⟩
        have hrFix : probabilityGeneratingFunctionReal p r = r := by
          -- The IVT gives a genuine fixed point of `ψ` in `[0,x]`.
          dsimp [g] at hrZero
          linarith
        have hrMem : r ∈ galtonWatsonFixedPoints p := by
          refine (mem_galtonWatsonFixedPoints_iff p r).2 ?_
          refine ⟨⟨hrIcc.1, le_trans hrIcc.2 hxIoo.2.le⟩, hrFix⟩
        have hrClassified :
            r = galtonWatsonExtinctionProbability p ∨ r = 1 := by
          simpa [hFixed, Set.mem_insert_iff, Set.mem_singleton_iff] using hrMem
        rcases hrClassified with rfl | hrOne
        · exact lt_of_le_of_lt hrIcc.2 hxIoo.2
        · exfalso
          have : (1 : ℝ) ≤ x := by
            simpa [hrOne] using hrIcc.2
          have hxNot : ¬ (1 : ℝ) ≤ x := by
            linarith [hxIoo.2]
          exact hxNot this
      · push Not at hmass
        rcases (probabilityGeneratingFunctionDerivativeLeftLimitGtOne_iff p).1 hDeriv with
          ⟨l, hl, hlGt⟩
        have hfun :
            probabilityGeneratingFunctionReal p =
              fun z : ℝ ↦ (p 0).toReal + (p 1).toReal * z := by
          funext z
          rw [probabilityGeneratingFunctionReal_eq_p0_add_p1_mul_of_no_mass_ge_two p hmass z]
        have hConst :
            ∀ z : ℝ, deriv (probabilityGeneratingFunctionReal p) z = (p 1).toReal := by
          intro z
          -- In the affine branch, the derivative is the constant coefficient `p 1`.
          calc
            deriv (probabilityGeneratingFunctionReal p) z =
                deriv (fun z : ℝ ↦ (p 0).toReal + (p 1).toReal * z) z := by
                  rw [hfun]
            _ = deriv (fun z : ℝ ↦ (p 1).toReal * z) z := by simp
            _ = (p 1).toReal := by
              simpa using deriv_const_mul (p 1).toReal (x := z) differentiableAt_id
        have hConstTendsto :
            Filter.Tendsto
              (fun z : ℝ ↦ ENNReal.ofReal (deriv (probabilityGeneratingFunctionReal p) z))
              (𝓝[<] (1 : ℝ)) (𝓝 (ENNReal.ofReal ((p 1).toReal))) := by
          simpa [hConst] using
            (tendsto_const_nhds :
              Filter.Tendsto
                (fun _ : ℝ ↦ ENNReal.ofReal ((p 1).toReal))
                (𝓝[<] (1 : ℝ)) (𝓝 (ENNReal.ofReal ((p 1).toReal))))
        have hlEq : l = ENNReal.ofReal ((p 1).toReal) := tendsto_nhds_unique hl hConstTendsto
        have hp1LeENN : p 1 ≤ 1 := by
          simpa [p.tsum_coe] using (ENNReal.le_tsum (f := fun n : ℕ ↦ p n) 1)
        have hp1Le : (p 1).toReal ≤ 1 := by
          exact (ENNReal.toReal_le_toReal (p.apply_ne_top 1) ENNReal.one_ne_top).2 hp1LeENN
        have : ¬ 1 < l := by
          simpa [hlEq] using (not_lt_of_ge hp1Le)
        exact (this hlGt).elim
  exact ⟨hExt, hMean⟩

-- Proof sketch: combine the atomic fixed-point statement with the two supercriticality
-- equivalences.
/-- Theorem 3.11: If `p 1 ≠ 1`, then the fixed points of the offspring generating function on
`[0,1]` are exactly the extinction probability `q` and `1`, and the conditions `q < 1`,
`lim_{z \uparrow 1} ψ'(z) > 1`, and `∑ k, k p_k > 1` are equivalent. -/
theorem galtonWatson_extinctionProbability_fixedPoints_and_supercriticality
    (p : PMF ℕ) (hp1 : p 1 ≠ 1) :
    galtonWatsonFixedPoints p = ({galtonWatsonExtinctionProbability p, (1 : ℝ)} : Set ℝ) ∧
      (galtonWatsonExtinctionProbability p < 1 ↔
        probabilityGeneratingFunctionDerivativeLeftLimitGtOne p) ∧
      (probabilityGeneratingFunctionDerivativeLeftLimitGtOne p ↔
        1 < galtonWatsonOffspringMean p) := by
  -- Assemble the fixed-point classification with the repaired supercriticality equivalences.
  have hFixed := galtonWatson_fixedPoints_eq_extinctionProbability_or_one p hp1
  have hSuper :=
    galtonWatson_extinctionProbability_lt_one_iff_derivativeLeftLimit_gt_one_iff_offspringMean_gt_one
      p hp1
  exact ⟨hFixed, hSuper.1, hSuper.2⟩
