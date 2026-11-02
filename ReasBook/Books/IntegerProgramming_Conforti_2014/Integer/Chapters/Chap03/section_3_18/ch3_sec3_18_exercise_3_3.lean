import Mathlib

open scoped BigOperators
open scoped Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the statement
-- below uses a direct `Fin`-indexed formulation for the fractional knapsack LP and its greedy
-- optimal solution.

section FeasibleSet

variable {𝕜 : Type*} [AddCommMonoid 𝕜] [Mul 𝕜] [One 𝕜] [LE 𝕜]

/-- The feasible set of the fractional knapsack problem with weights `a` and capacity `b`. -/
def fractionalKnapsackSet {n : ℕ} (a : Fin n → 𝕜) (b : 𝕜) : Set (Fin n → 𝕜) :=
  {x | a ⬝ᵥ x ≤ b ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1}

/-- Membership in the fractional knapsack set means satisfying the capacity inequality and the
coordinate bounds `0 ≤ x_j ≤ 1`. -/
theorem mem_fractionalKnapsackSet_iff
    {n : ℕ} (a : Fin n → 𝕜) (b : 𝕜) (x : Fin n → 𝕜) :
    x ∈ fractionalKnapsackSet a b ↔ a ⬝ᵥ x ≤ b ∧ ∀ j, 0 ≤ x j ∧ x j ≤ 1 := by
  rfl

end FeasibleSet

section PrefixSum

variable {𝕜 : Type*} [AddCommMonoid 𝕜]

/-- The sum of the first `k` entries of a `Fin n`-indexed vector, where `k : Fin (n + 1)` is
viewed as a count. Applied to the weight vector, this is the prefix weight. -/
def fractionalKnapsackPrefixSum {n : ℕ} (a : Fin n → 𝕜) (m : Fin (n + 1)) : 𝕜 :=
  Finset.sum (Finset.range m.1) fun i ↦ if hi : i < n then a ⟨i, hi⟩ else 0

/-- Helper for Exercise 3.3: extending a prefix by one item adds exactly that item's weight. -/
lemma fractionalKnapsackPrefixSum_succ
    {n : ℕ} (a : Fin n → 𝕜) (h : Fin n) :
    fractionalKnapsackPrefixSum a h.succ =
      fractionalKnapsackPrefixSum a h.castSucc + a h := by
  simp [fractionalKnapsackPrefixSum, Finset.sum_range_succ, h.is_lt]

end PrefixSum

section GreedyData

variable {𝕜 : Type*} [Field 𝕜]

/-- The greedy fractional knapsack vector with zero-based breakpoint `h`: all items before `h`
are taken completely, item `h` is taken fractionally, and all later items are omitted. -/
noncomputable def fractionalKnapsackGreedySolution {n : ℕ} (a : Fin n → 𝕜) (b : 𝕜)
    (h : Fin n) : Fin n → 𝕜 :=
  fun i ↦
    if i < h then 1
    else if i = h then
      (b - fractionalKnapsackPrefixSum a h.castSucc) / a h
    else 0

/-- Helper for Exercise 3.3: summing any coefficient vector against the greedy solution leaves the
full prefix and the breakpoint contribution. -/
lemma dotProduct_fractionalKnapsackGreedySolution
    {n : ℕ} (d a : Fin n → 𝕜) (b : 𝕜) (h : Fin n) :
    d ⬝ᵥ fractionalKnapsackGreedySolution a b h =
      fractionalKnapsackPrefixSum d h.castSucc +
        d h * ((b - fractionalKnapsackPrefixSum a h.castSucc) / a h) := by
  let term : ℕ → 𝕜 := fun k ↦
    if hk : k < n then
      d ⟨k, hk⟩ * fractionalKnapsackGreedySolution a b h ⟨k, hk⟩
    else 0
  -- Rewrite the finite sum as a `range` sum and isolate the prefix, breakpoint, and tail parts.
  rw [dotProduct, Finset.sum_fin_eq_sum_range, fractionalKnapsackPrefixSum]
  calc
    Finset.sum (Finset.range n) term
        = Finset.sum (Finset.range h.1.succ) term + Finset.sum (Finset.Ico h.1.succ n) term := by
          symm
          exact Finset.sum_range_add_sum_Ico term (Nat.succ_le_of_lt h.is_lt)
    _ = Finset.sum (Finset.range h.1) term + term h.1 +
          Finset.sum (Finset.Ico h.1.succ n) term := by
          rw [Finset.sum_range_succ]
  have hprefix :
      Finset.sum (Finset.range h.1) term = fractionalKnapsackPrefixSum d h.castSucc := by
    rw [fractionalKnapsackPrefixSum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk_lt : k < h.1 := Finset.mem_range.mp hk
    have hkn : k < n := Nat.lt_trans hk_lt h.is_lt
    have hlt : (⟨k, hkn⟩ : Fin n) < h := by
      simpa using hk_lt
    simp [term, hkn, fractionalKnapsackGreedySolution, hlt]
  rw [hprefix]
  have hbreak : term h.1 = d h * ((b - fractionalKnapsackPrefixSum a h.castSucc) / a h) := by
    have hnotlt : ¬ (h < h) := by exact lt_irrefl h
    simp [term, h.is_lt, fractionalKnapsackGreedySolution]
  rw [hbreak]
  have htail : Finset.sum (Finset.Ico h.1.succ n) term = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk_lo : h.1 + 1 ≤ k := by exact Finset.mem_Ico.mp hk |>.1
    have hk_hi : k < n := by exact Finset.mem_Ico.mp hk |>.2
    have hnotlt : ¬ ((⟨k, hk_hi⟩ : Fin n) < h) := by
      intro hlt
      have hlt' : k < h.1 := by simpa using hlt
      exact Nat.not_lt_of_ge (Nat.le_trans (Nat.le_succ h.1) hk_lo) hlt'
    have hne : (⟨k, hk_hi⟩ : Fin n) ≠ h := by
      intro hEq
      have hk_eq : k = h.1 := by simpa using congrArg Fin.val hEq
      exact Nat.not_succ_le_self h.1 (hk_eq ▸ hk_lo)
    simp [hk_hi, fractionalKnapsackGreedySolution, hnotlt, hne]
  rw [htail, add_zero]
  simp [fractionalKnapsackPrefixSum]

end GreedyData

section Greedy

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Helper for Exercise 3.3: the greedy breakpoint fraction lies in the unit interval and packs
the knapsack to capacity. -/
lemma fractionalKnapsackGreedySolution_mem_set
    {n : ℕ} {a : Fin n → 𝕜} {b : 𝕜} (h : Fin n)
    (ha_pos : ∀ j, 0 < a j)
    (hprefix_le : fractionalKnapsackPrefixSum a h.castSucc ≤ b)
    (hprefix_lt_next : b < fractionalKnapsackPrefixSum a h.succ) :
    fractionalKnapsackGreedySolution a b h ∈ fractionalKnapsackSet a b := by
  have hprefix_lt :
      b - fractionalKnapsackPrefixSum a h.castSucc < a h := by
    rw [fractionalKnapsackPrefixSum_succ] at hprefix_lt_next
    linarith
  have hfrac_nonneg :
      0 ≤ (b - fractionalKnapsackPrefixSum a h.castSucc) / a h := by
    apply div_nonneg
    · exact sub_nonneg.mpr hprefix_le
    · exact le_of_lt (ha_pos h)
  have hfrac_lt_one :
      (b - fractionalKnapsackPrefixSum a h.castSucc) / a h < 1 := by
    exact (div_lt_iff₀ (ha_pos h)).2 <| by simpa using hprefix_lt
  have ha_ne : a h ≠ 0 := ne_of_gt (ha_pos h)
  have hweight_eq : a ⬝ᵥ fractionalKnapsackGreedySolution a b h = b := by
    -- The generic greedy-sum identity becomes an exact capacity equation for the weights.
    rw [dotProduct_fractionalKnapsackGreedySolution a a b h]
    field_simp [ha_ne]
    ring
  refine ⟨?_, ?_⟩
  · -- Compute the total packed weight exactly and simplify it to the capacity `b`.
    exact le_of_eq hweight_eq
  · -- Check coordinate bounds by splitting before, at, and after the breakpoint.
    intro j
    by_cases hj_lt : j < h
    · have hj_ne : j ≠ h := ne_of_lt hj_lt
      simp [fractionalKnapsackGreedySolution, hj_lt]
    · by_cases hj_eq : j = h
      · subst hj_eq
        constructor
        · simpa [fractionalKnapsackGreedySolution] using hfrac_nonneg
        · simpa [fractionalKnapsackGreedySolution] using le_of_lt hfrac_lt_one
      · simp [fractionalKnapsackGreedySolution, hj_lt, hj_eq]

/-- Helper for Exercise 3.3: items before the breakpoint dominate the breakpoint ratio. -/
lemma breakpoint_ratio_mul_le
    {n : ℕ} {a c : Fin n → 𝕜} (h : Fin n)
    (ha_pos : ∀ j, 0 < a j)
    (hratio : Antitone fun j : Fin n ↦ c j / a j)
    {i : Fin n} (hi : i < h) :
    (c h / a h) * a i ≤ c i := by
  have hratio_hi : c h / a h ≤ c i / a i := by
    exact hratio (le_of_lt hi)
  exact (le_div_iff₀ (ha_pos i)).mp <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hratio_hi

/-- Helper for Exercise 3.3: items at or after the breakpoint are bounded by the breakpoint
ratio. -/
lemma le_breakpoint_ratio_mul
    {n : ℕ} {a c : Fin n → 𝕜} (h : Fin n)
    (ha_pos : ∀ j, 0 < a j)
    (hratio : Antitone fun j : Fin n ↦ c j / a j)
    {i : Fin n} (hi : h ≤ i) :
    c i ≤ (c h / a h) * a i := by
  have hratio_hi : c i / a i ≤ c h / a h := by
    exact hratio hi
  exact (div_le_iff₀ (ha_pos i)).mp <| by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hratio_hi

/-- Helper for Exercise 3.3: the breakpoint ratio and upper-bound slacks give a dual upper bound
for every feasible fractional knapsack solution. -/
lemma fractionalKnapsack_dotProduct_le_threshold_dual_value
    {n : ℕ} {a c : Fin n → 𝕜} {b : 𝕜} (h : Fin n)
    (ha_pos : ∀ j, 0 < a j)
    (hc_nonneg : ∀ j, 0 ≤ c j)
    (hratio : Antitone fun j : Fin n ↦ c j / a j)
    {y : Fin n → 𝕜} (hy : y ∈ fractionalKnapsackSet a b) :
    c ⬝ᵥ y ≤
      (c h / a h) * b + ∑ i, if i < h then c i - (c h / a h) * a i else 0 := by
  let lam : 𝕜 := c h / a h
  let s : Fin n → 𝕜 := fun i ↦ if i < h then c i - lam * a i else 0
  have hlam_nonneg : 0 ≤ lam := by
    exact div_nonneg (hc_nonneg h) (le_of_lt (ha_pos h))
  have hs_nonneg : ∀ i, 0 ≤ s i := by
    intro i
    by_cases hi : i < h
    · have hbound : lam * a i ≤ c i := by
        simpa [lam] using breakpoint_ratio_mul_le h ha_pos hratio hi
      simpa [s, hi] using sub_nonneg.mpr hbound
    · simp [s, hi]
  have hpointwise : ∀ i, c i * y i ≤ lam * (a i * y i) + s i := by
    intro i
    rcases hy.2 i with ⟨hy_nonneg, hy_le_one⟩
    by_cases hi : i < h
    · have hs_eq : c i = lam * a i + s i := by
        simp [s, hi, lam, sub_eq_add_neg]
      have hsy : s i * y i ≤ s i := by
        simpa using (mul_le_mul_of_nonneg_left hy_le_one (hs_nonneg i))
      calc
        c i * y i = (lam * a i + s i) * y i := by rw [hs_eq]
        _ = lam * (a i * y i) + s i * y i := by ring
        _ ≤ lam * (a i * y i) + s i := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hsy (lam * (a i * y i))
    · have hci : c i ≤ lam * a i := by
        exact le_breakpoint_ratio_mul h ha_pos hratio (le_of_not_gt hi)
      have hs_eq : s i = 0 := by simp [s, hi]
      calc
        c i * y i ≤ (lam * a i) * y i := by
          exact mul_le_mul_of_nonneg_right hci hy_nonneg
        _ = lam * (a i * y i) := by ring
        _ ≤ lam * (a i * y i) + s i := by
          rw [hs_eq]
          linarith
  calc
    c ⬝ᵥ y = ∑ i, c i * y i := rfl
    _ ≤ ∑ i, (lam * (a i * y i) + s i) := by
      exact Finset.sum_le_sum fun i _ ↦ hpointwise i
    _ = (∑ i, lam * (a i * y i)) + ∑ i, s i := by
      rw [Finset.sum_add_distrib]
    _ = lam * (∑ i, a i * y i) + ∑ i, s i := by
      rw [← Finset.mul_sum]
    _ ≤ lam * b + ∑ i, s i := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (mul_le_mul_of_nonneg_left hy.1 hlam_nonneg) (∑ i, s i)
    _ = (c h / a h) * b + ∑ i, if i < h then c i - (c h / a h) * a i else 0 := by
      simp [lam, s]

omit [IsStrictOrderedRing 𝕜] in
/-- Helper for Exercise 3.3: the greedy vector attains the threshold dual value exactly. -/
lemma fractionalKnapsackGreedy_dotProduct_eq_threshold_dual_value
    {n : ℕ} {a c : Fin n → 𝕜} {b : 𝕜} (h : Fin n)
    (ha_pos : ∀ j, 0 < a j) :
    c ⬝ᵥ fractionalKnapsackGreedySolution a b h =
      (c h / a h) * b + ∑ i, if i < h then c i - (c h / a h) * a i else 0 := by
  let lam : 𝕜 := c h / a h
  let x : Fin n → 𝕜 := fractionalKnapsackGreedySolution a b h
  have ha_ne : a h ≠ 0 := ne_of_gt (ha_pos h)
  have hx_weight : a ⬝ᵥ x = b := by
    -- Reuse the exact weighted-sum computation from the greedy support pattern.
    rw [show x = fractionalKnapsackGreedySolution a b h by rfl]
    rw [dotProduct_fractionalKnapsackGreedySolution a a b h]
    field_simp [ha_ne]
    ring
  have hpointwise :
      ∀ i, c i * x i = lam * (a i * x i) + (if i < h then c i - lam * a i else 0) := by
    intro i
    by_cases hi : i < h
    · simp [x, fractionalKnapsackGreedySolution, hi, lam]
    · by_cases hieq : i = h
      · have hnotlt : ¬ i < h := by simp [hieq]
        simp [x, fractionalKnapsackGreedySolution, hieq, lam]
        field_simp [ha_ne]
      · simp [x, fractionalKnapsackGreedySolution, hi, hieq, lam]
  -- The greedy vector has the exact same value as the certificate bound from the dual step.
  calc
    c ⬝ᵥ x = ∑ i, c i * x i := rfl
    _ = ∑ i, (lam * (a i * x i) + (if i < h then c i - lam * a i else 0)) := by
      exact Finset.sum_congr rfl fun i _ ↦ hpointwise i
    _ = (∑ i, lam * (a i * x i)) + ∑ i, if i < h then c i - lam * a i else 0 := by
      rw [Finset.sum_add_distrib]
    _ = lam * (∑ i, a i * x i) + ∑ i, if i < h then c i - lam * a i else 0 := by
      rw [← Finset.mul_sum]
    _ = lam * (a ⬝ᵥ x) + ∑ i, if i < h then c i - lam * a i else 0 := by
      rfl
    _ = lam * b + ∑ i, if i < h then c i - lam * a i else 0 := by
      rw [hx_weight]
    _ = (c h / a h) * b + ∑ i, if i < h then c i - (c h / a h) * a i else 0 := by
      simp [lam]

/-- Exercise 3.3. If the profit-to-weight ratios are arranged in nonincreasing order and `h` is
the zero-based index of the first item that is not packed completely, then the standard greedy
fractional knapsack vector is an optimal solution of the fractional knapsack problem. -/
theorem fractionalKnapsackGreedySolution_optimal
    {n : ℕ} (a c : Fin n → 𝕜) (b : 𝕜) (h : Fin n)
    (ha_pos : ∀ j, 0 < a j)
    (hc_nonneg : ∀ j, 0 ≤ c j)
    (hratio : Antitone fun j : Fin n ↦ c j / a j)
    (hprefix_le : fractionalKnapsackPrefixSum a h.castSucc ≤ b)
    (hprefix_lt_next : b < fractionalKnapsackPrefixSum a h.succ) :
    fractionalKnapsackGreedySolution a b h ∈ fractionalKnapsackSet a b ∧
      ∀ y ∈ fractionalKnapsackSet a b,
        c ⬝ᵥ y ≤ c ⬝ᵥ fractionalKnapsackGreedySolution a b h := by
  refine ⟨?_, ?_⟩
  · -- First certify that the greedy breakpoint vector is feasible.
    exact fractionalKnapsackGreedySolution_mem_set h ha_pos hprefix_le hprefix_lt_next
  · intro y hy
    -- Then compare any feasible point to the dual threshold value attained by the greedy point.
    calc
      c ⬝ᵥ y ≤
          (c h / a h) * b + ∑ i, if i < h then c i - (c h / a h) * a i else 0 := by
        exact fractionalKnapsack_dotProduct_le_threshold_dual_value h ha_pos hc_nonneg hratio hy
      _ = c ⬝ᵥ fractionalKnapsackGreedySolution a b h := by
        symm
        exact fractionalKnapsackGreedy_dotProduct_eq_threshold_dual_value h ha_pos

end Greedy
