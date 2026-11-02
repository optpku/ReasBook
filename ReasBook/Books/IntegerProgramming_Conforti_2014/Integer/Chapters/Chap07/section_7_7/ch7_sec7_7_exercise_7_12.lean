import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_2.ch7_sec7_2_2_theorem_7_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain sampling for this exercise:
- primary domain: sequence-independent lifting functions for minimal covers, with the goal of
  proving superadditivity on `[0, b]`
- inspected upstream declarations:
  * `SequenceIndependentLifting.is_superadditive_on_Icc` from Theorem 7.7, the
    `core/canonical` owner for superadditivity on `[0, b]`
  * `theorem_7_4_mu` from Theorem 7.4 and `theorem_7_16_cover_sum` from Theorem 7.16, the
    chapter-level owners for ordered-cover partial sums in more specialized ambient models
  * `flow_cover_excess` from Theorem 7.9, the chapter-level owner for the excess parameter in the
    finite flow-cover setting

This file stays `source-facing`: the ordered sequence `a`, its partial sums `μ`, the excess
`λ = μ_t - b`, the auxiliary quantities `ρ_h`, the intervals `F_h` and `S_h`, and the resulting
piecewise lifting function `g` are the mathematical objects named in Exercise 7.12 itself.
Only the superadditivity predicate is reused directly from the upstream canonical owner. The
implementation helper used to assemble `g` is kept internal because it is derived API rather than
source-level data. -/

open SequenceIndependentLifting

/-- The partial sums `μ_h = a₀ + ⋯ + a_{h-1}` of the ordered cover weights used in
Exercise 7.12. -/
def exercise_7_12_mu
    (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | h + 1 => exercise_7_12_mu a h + a h

/-- The initial partial sum in Exercise 7.12 is `μ₀ = 0`. -/
@[simp] theorem exercise_7_12_mu_zero
    (a : ℕ → ℝ) :
    exercise_7_12_mu a 0 = 0 :=
  rfl

/-- The partial sums in Exercise 7.12 satisfy the recursive relation
`μ_{h+1} = μ_h + a_h`. -/
@[simp] theorem exercise_7_12_mu_succ
    (a : ℕ → ℝ)
    (h : ℕ) :
    exercise_7_12_mu a (h + 1) = exercise_7_12_mu a h + a h :=
  rfl

/-- The recursive owner `exercise_7_12_mu` agrees with the explicit sum
`μ_h = a₀ + ⋯ + a_{h-1}`. -/
theorem exercise_7_12_mu_eq_sum
    (a : ℕ → ℝ)
    (h : ℕ) :
    exercise_7_12_mu a h = (Finset.range h).sum fun i ↦ a i := by
  induction h with
  | zero =>
      simp
  | succ h ih =>
      rw [exercise_7_12_mu_succ, Finset.sum_range_succ, ih]

/-- The cover excess `λ = μ_t - b` used in Exercise 7.12. -/
def exercise_7_12_cover_excess
    (a : ℕ → ℝ)
    (t : ℕ)
    (b : ℝ) : ℝ :=
  exercise_7_12_mu a t - b

/-- Expanding `exercise_7_12_cover_excess a t b` recovers the source formula `λ = μ_t - b`. -/
theorem exercise_7_12_cover_excess_eq
    (a : ℕ → ℝ)
    (t : ℕ)
    (b : ℝ) :
    exercise_7_12_cover_excess a t b = exercise_7_12_mu a t - b :=
  rfl

/-- The excess quantities `ρ_h = max (0, a_h - (a₀ - λ))` used in the GNS auxiliary lifting
function `(7.12)`. -/
def exercise_7_12_rho
    (a : ℕ → ℝ)
    (lam : ℝ) : ℕ → ℝ :=
  fun h ↦ max 0 (a h - (a 0 - lam))

/-- Evaluating `exercise_7_12_rho a λ` at `h` recovers the source formula
`ρ_h = max (0, a_h - (a₀ - λ))`. -/
@[simp] theorem exercise_7_12_rho_apply
    (a : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) :
    exercise_7_12_rho a lam h = max 0 (a h - (a 0 - lam)) :=
  rfl

/-- The interval `F_h = (μ_h - λ + ρ_h, μ_{h+1} - λ]` appearing in the piecewise definition of
the auxiliary lifting function `g` from `(7.12)`. -/
def exercise_7_12_F
    (μ ρ : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) : Set ℝ :=
  Set.Ioc (μ h - lam + ρ h) (μ (h + 1) - lam)

/-- Membership in `exercise_7_12_F μ ρ λ h` means lying in the interval
`(μ_h - λ + ρ_h, μ_{h+1} - λ]`. -/
theorem mem_exercise_7_12_F_iff
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ} :
    z ∈ exercise_7_12_F μ ρ lam h ↔ μ h - lam + ρ h < z ∧ z ≤ μ (h + 1) - lam := Iff.rfl

/-- The interval `S_h = (μ_h - λ, μ_h - λ + ρ_h]` appearing in the piecewise definition of the
auxiliary lifting function `g` from `(7.12)`. -/
def exercise_7_12_S
    (μ ρ : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) : Set ℝ :=
  Set.Ioc (μ h - lam) (μ h - lam + ρ h)

/-- Membership in `exercise_7_12_S μ ρ λ h` means lying in the interval
`(μ_h - λ, μ_h - λ + ρ_h]`. -/
theorem mem_exercise_7_12_S_iff
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ} :
    z ∈ exercise_7_12_S μ ρ lam h ↔ μ h - lam < z ∧ z ≤ μ h - lam + ρ h := Iff.rfl

/-- The pointwise value contributed by the `h`-th piece of the auxiliary lifting function
`g` from `(7.12)`. -/
private noncomputable def pieceValue
    (μ ρ : ℕ → ℝ)
    (lam z : ℝ)
    (h : ℕ) : ℝ :=
  let _ := Classical.propDecidable
  if z ∈ exercise_7_12_F μ ρ lam h then
    (h : ℝ)
  else if 1 ≤ h ∧ z ∈ exercise_7_12_S μ ρ lam h then
    (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1
  else
    0

/-- The canonical auxiliary lifting function `g` from `(7.12)`, formed by taking the maximum
piece value among the first `t` stages and fixing the value `0` at the origin. -/
noncomputable def exercise_7_12_g
    (t : ℕ)
    (μ ρ : ℕ → ℝ)
    (lam : ℝ) : ℝ → ℝ :=
  let _ := Classical.propDecidable
  fun z ↦
    if z = 0 then
      0
    else
      sSup ({0} ∪ {r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h})

/-- At the origin, the auxiliary lifting function `(7.12)` vanishes. -/
theorem exercise_7_12_g_zero
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam : ℝ} :
    exercise_7_12_g t μ ρ lam 0 = 0 := by
  classical
  simp [exercise_7_12_g]

private theorem exercise_7_12_g_pieceSet_bddAbove
    (t : ℕ)
    (μ ρ : ℕ → ℝ)
    (lam z : ℝ) :
    BddAbove ({0} ∪ {r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h}) := by
  have hfinite :
      ({r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h} : Set ℝ).Finite := by
    refine ((Finset.finite_toSet (Finset.range t)).image (pieceValue μ ρ lam z)).subset ?_
    rintro r ⟨h, hh, rfl⟩
    exact ⟨h, by simpa using hh, rfl⟩
  have hzero : ({0} : Set ℝ).Finite := by simp
  exact hzero.bddAbove.union hfinite.bddAbove

/-- Helper for Exercise 7.12: the auxiliary lifting function `(7.12)` is everywhere nonnegative
because the defining supremum always contains the candidate value `0`. -/
theorem exercise_7_12_g_nonneg
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ} :
    0 ≤ exercise_7_12_g t μ ρ lam z := by
  classical
  by_cases hz0 : z = 0
  · -- At the origin the lifting function is exactly `0`.
    simpa [hz0, exercise_7_12_g_zero]
  · -- Away from the origin, the supremum is taken over a set containing the value `0`.
    have hmem :
        (0 : ℝ) ∈
          ({0} ∪ {r | ∃ h ∈ Finset.range t, r = pieceValue μ ρ lam z h}) :=
      Or.inl rfl
    simpa [exercise_7_12_g, hz0] using
      (le_csSup (exercise_7_12_g_pieceSet_bddAbove t μ ρ lam z) hmem)

/-- Membership in `F_h` with `h < t` contributes the stage value `h` to the supremum defining
the auxiliary lifting function `(7.12)`. -/
theorem exercise_7_12_le_g_of_mem_F
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (hh : h < t)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_F μ ρ lam h) :
    (h : ℝ) ≤ exercise_7_12_g t μ ρ lam z := by
  classical
  have hmem :
      (h : ℝ) ∈
        ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) := by
    right
    refine ⟨h, by simpa using hh, ?_⟩
    simp [pieceValue, hz]
  simpa [exercise_7_12_g, hz0] using
    (le_csSup_of_le (exercise_7_12_g_pieceSet_bddAbove t μ ρ lam z) hmem le_rfl)

/-- Membership in `S_h` with `1 ≤ h < t` contributes the source affine interpolation value to the
supremum defining the auxiliary lifting function `(7.12)`. -/
theorem exercise_7_12_le_g_of_mem_S
    {t : ℕ}
    {μ ρ : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (h1 : 1 ≤ h)
    (hh : h < t)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_S μ ρ lam h) :
    (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 ≤ exercise_7_12_g t μ ρ lam z := by
  classical
  have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam h := by
    intro hzF
    exact not_lt_of_ge hz.2 hzF.1
  have hmem :
      (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 ∈
        ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) := by
    right
    refine ⟨h, by simpa using hh, ?_⟩
    simp [pieceValue, hz_not_mem_F, h1, hz]
  simpa [exercise_7_12_g, hz0] using
    (le_csSup_of_le (exercise_7_12_g_pieceSet_bddAbove t μ ρ lam z) hmem le_rfl)

/-- Helper for Exercise 7.12: the partial sums `exercise_7_12_mu a` are monotone on the prefix
`{0, …, t}` when the ordered cover weights are nonnegative. -/
theorem exercise_7_12_mu_le_of_le
    {t : ℕ}
    {a : ℕ → ℝ}
    (ha_nonneg : ∀ ⦃h : ℕ⦄, h < t → 0 ≤ a h)
    {i j : ℕ}
    (hij : i ≤ j)
    (hj : j ≤ t) :
    exercise_7_12_mu a i ≤ exercise_7_12_mu a j := by
  -- Rewrite the partial sums as range sums and compare them by the inclusion `range i ⊆ range j`.
  rw [exercise_7_12_mu_eq_sum, exercise_7_12_mu_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro n hn
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hij)
  · intro n hn _
    exact ha_nonneg (lt_of_lt_of_le (Finset.mem_range.mp hn) hj)

/-- Helper for Exercise 7.12: every `ρ_h` is nonnegative. -/
theorem exercise_7_12_rho_nonneg
    (a : ℕ → ℝ)
    (lam : ℝ)
    (h : ℕ) :
    0 ≤ exercise_7_12_rho a lam h := by
  simp [exercise_7_12_rho]

/-- Helper for Exercise 7.12: the sequence `ρ_h` is antitone along the ordered cover. -/
theorem exercise_7_12_rho_antitone
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {i j : ℕ}
    (hij : i ≤ j)
    (hj : j < t) :
    exercise_7_12_rho a lam j ≤ exercise_7_12_rho a lam i := by
  -- The arguments of the `max` inherit the descending order of the cover weights.
  have harg : a j - (a 0 - lam) ≤ a i - (a 0 - lam) := by
    linarith [ha_desc hij hj]
  show max 0 (a j - (a 0 - lam)) ≤ max 0 (a i - (a 0 - lam))
  exact max_le_max le_rfl harg

/-- Helper for Exercise 7.12: on a constant piece `F_h`, the auxiliary lifting function is
exactly the stage value `h`. -/
theorem exercise_7_12_g_eq_of_mem_F
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (hlam_le_a0 : lam ≤ a 0)
    (hh : h < t)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_F (exercise_7_12_mu a) (exercise_7_12_rho a lam) lam h) :
    exercise_7_12_g t (exercise_7_12_mu a) (exercise_7_12_rho a lam) lam z = (h : ℝ) := by
  classical
  let μ := exercise_7_12_mu a
  let ρ := exercise_7_12_rho a lam
  have hμsucc : ∀ k : ℕ, μ (k + 1) = μ k + a k := by
    intro k
    simpa [μ] using exercise_7_12_mu_succ a k
  have hρ_nonneg : ∀ k : ℕ, 0 ≤ ρ k := by
    intro k
    simpa [ρ] using exercise_7_12_rho_nonneg a lam k
  have hz_left : μ h - lam < z := by
    have : μ h - lam + ρ h < z := hz.1
    linarith [hρ_nonneg h]
  have hz_le_stage : z ≤ μ (h + 1) - lam := hz.2
  have hlower :
      (h : ℝ) ≤ exercise_7_12_g t μ ρ lam z :=
    exercise_7_12_le_g_of_mem_F hh hz0 hz
  refine le_antisymm ?_ hlower
  -- Compare the supremum defining `g` against the unique active stage `h`.
  have hsSup_le :
      sSup ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) ≤ h := by
    refine csSup_le ?_ ?_
    exact ⟨0, Or.inl rfl⟩
    intro r hr
    rcases hr with rfl | hr
    · exact Nat.cast_nonneg h
    · rcases hr with ⟨k, hkMem, rfl⟩
      have hk : k < t := by
        simpa using hkMem
      by_cases hkh : k = h
      · subst k
        simpa [μ, ρ, pieceValue, hz]
      · by_cases hlt : k < h
        · have hk_stage : μ (k + 1) ≤ μ h :=
            exercise_7_12_mu_le_of_le ha_nonneg (Nat.succ_le_of_lt hlt) (Nat.le_of_lt hh)
          have hρk_le_ak : ρ k ≤ a k := by
            by_cases hk_nonneg : 0 ≤ a k - (a 0 - lam)
            · have hbase : 0 ≤ a 0 - lam := sub_nonneg.mpr hlam_le_a0
              simp [ρ, hk_nonneg]
              linarith
            · have hk_lt0 : a k - (a 0 - lam) < 0 := lt_of_not_ge hk_nonneg
              have hak_nonneg : 0 ≤ a k := ha_nonneg hk
              simp [ρ, exercise_7_12_rho, hk_lt0.le]
              exact hak_nonneg
          have hz_not_mem_S : z ∉ exercise_7_12_S μ ρ lam k := by
            intro hzS
            have hz_upper : z ≤ μ (k + 1) - lam := by
              have : μ k - lam + ρ k ≤ μ (k + 1) - lam := by
                rw [hμsucc k]
                linarith
              exact le_trans hzS.2 this
            have : z ≤ μ h - lam := by
              linarith
            linarith
          have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam k := by
            intro hzF
            have : z ≤ μ h - lam := by
              have : μ (k + 1) - lam ≤ μ h - lam := by
                linarith
              exact le_trans hzF.2 this
            linarith
          simpa [pieceValue, hz_not_mem_F, hz_not_mem_S] using
            (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
        · have hgt : h < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (by
            intro hEq
            apply hkh
            exact hEq.symm)
          have hk_stage : μ (h + 1) ≤ μ k :=
            exercise_7_12_mu_le_of_le ha_nonneg (Nat.succ_le_of_lt hgt) (Nat.le_of_lt hk)
          have hz_stage : z ≤ μ k - lam := by
            linarith [hz_le_stage, hk_stage]
          have hz_not_mem_S : z ∉ exercise_7_12_S μ ρ lam k := by
            intro hzS
            exact not_lt_of_ge hz_stage hzS.1
          have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam k := by
            intro hzF
            have hz_lower : μ k - lam < z := by
              have hρk_nonneg : 0 ≤ ρ k := hρ_nonneg k
              linarith [hzF.1]
            exact not_lt_of_ge hz_stage hz_lower
          simpa [pieceValue, hz_not_mem_F, hz_not_mem_S] using
            (Nat.cast_nonneg h : (0 : ℝ) ≤ h)
  simpa [exercise_7_12_g, hz0] using hsSup_le

/-- Helper for Exercise 7.12: on an affine piece `S_h`, the auxiliary lifting function is the
source interpolation formula. -/
theorem exercise_7_12_g_eq_of_mem_S
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam z : ℝ}
    {h : ℕ}
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hlam_le_a0 : lam ≤ a 0)
    (h1 : 1 ≤ h)
    (hh : h < t)
    (hrho1_pos : 0 < exercise_7_12_rho a lam 1)
    (hz0 : z ≠ 0)
    (hz : z ∈ exercise_7_12_S (exercise_7_12_mu a) (exercise_7_12_rho a lam) lam h) :
    exercise_7_12_g t (exercise_7_12_mu a) (exercise_7_12_rho a lam) lam z =
      (h : ℝ) -
        (exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h - z) /
          exercise_7_12_rho a lam 1 := by
  classical
  let μ := exercise_7_12_mu a
  let ρ := exercise_7_12_rho a lam
  have hμsucc : ∀ k : ℕ, μ (k + 1) = μ k + a k := by
    intro k
    simpa [μ] using exercise_7_12_mu_succ a k
  have hρ_nonneg : ∀ k : ℕ, 0 ≤ ρ k := by
    intro k
    simpa [ρ] using exercise_7_12_rho_nonneg a lam k
  have hρ_le_weight : ∀ ⦃k : ℕ⦄, k < t → ρ k ≤ a k := by
    intro k hk
    by_cases hk_nonneg : 0 ≤ a k - (a 0 - lam)
    · have hbase : 0 ≤ a 0 - lam := sub_nonneg.mpr hlam_le_a0
      simp [ρ, hk_nonneg]
      linarith
    · have hk_lt0 : a k - (a 0 - lam) < 0 := lt_of_not_ge hk_nonneg
      have hak_nonneg : 0 ≤ a k := ha_nonneg hk
      simp [ρ, exercise_7_12_rho, hk_lt0.le]
      exact hak_nonneg
  have hρh_le : ρ h ≤ ρ 1 := by
    simpa [ρ] using exercise_7_12_rho_antitone ha_desc h1 hh
  have hz_not_mem_F_h : z ∉ exercise_7_12_F μ ρ lam h := by
    intro hzF
    exact not_lt_of_ge hz.2 hzF.1
  have htarget_nonneg :
      0 ≤ (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 := by
    have hnum_nonneg : 0 ≤ μ h - lam + ρ h - z := by
      linarith [hz.2]
    have hnum_le : μ h - lam + ρ h - z ≤ ρ 1 := by
      have : μ h - lam + ρ h - z ≤ ρ h := by
        linarith [hz.1]
      linarith
    have hfrac_le : (μ h - lam + ρ h - z) / ρ 1 ≤ 1 := by
      have hnum_le' : μ h - lam + ρ h - z ≤ 1 * ρ 1 := by
        simpa using hnum_le
      simpa using (div_le_iff₀ hrho1_pos).2 hnum_le'
    have hreal : (1 : ℝ) ≤ h := by
      exact_mod_cast h1
    linarith
  have hlower :
      (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 ≤
        exercise_7_12_g t μ ρ lam z :=
    exercise_7_12_le_g_of_mem_S h1 hh hz0 hz
  refine le_antisymm ?_ hlower
  -- Every other stage contributes `0`, so the active affine piece controls the supremum.
  have hsSup_le :
      sSup ({0} ∪ {r | ∃ k ∈ Finset.range t, r = pieceValue μ ρ lam z k}) ≤
        (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 := by
    refine csSup_le ?_ ?_
    exact ⟨0, Or.inl rfl⟩
    intro r hr
    rcases hr with rfl | hr
    · exact htarget_nonneg
    · rcases hr with ⟨k, hkMem, rfl⟩
      have hk : k < t := by
        simpa using hkMem
      by_cases hkh : k = h
      · subst k
        simpa [μ, ρ, pieceValue, hz_not_mem_F_h, h1, hz]
      · by_cases hlt : k < h
        · have hk_stage : μ (k + 1) ≤ μ h :=
            exercise_7_12_mu_le_of_le ha_nonneg (Nat.succ_le_of_lt hlt) (Nat.le_of_lt hh)
          have hρk_le_ak : ρ k ≤ a k := by
            by_cases hk_nonneg : 0 ≤ a k - (a 0 - lam)
            · have hbase : 0 ≤ a 0 - lam := sub_nonneg.mpr hlam_le_a0
              simp [ρ, hk_nonneg]
              linarith
            · have hk_lt0 : a k - (a 0 - lam) < 0 := lt_of_not_ge hk_nonneg
              have hak_nonneg : 0 ≤ a k := ha_nonneg hk
              simp [ρ, exercise_7_12_rho, hk_lt0.le]
              exact hak_nonneg
          have hz_not_mem_S : z ∉ exercise_7_12_S μ ρ lam k := by
            intro hzS
            have hz_upper : z ≤ μ (k + 1) - lam := by
              have : μ k - lam + ρ k ≤ μ (k + 1) - lam := by
                rw [hμsucc k]
                linarith
              exact le_trans hzS.2 this
            have : z ≤ μ h - lam := by
              linarith
            linarith [hz.1]
          have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam k := by
            intro hzF
            have : z ≤ μ h - lam := by
              have : μ (k + 1) - lam ≤ μ h - lam := by
                linarith
              exact le_trans hzF.2 this
            linarith [hz.1]
          have hk_le_target : (0 : ℝ) ≤ (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 :=
            htarget_nonneg
          simpa [pieceValue, hz_not_mem_F, hz_not_mem_S] using hk_le_target
        · have hgt : h < k := lt_of_le_of_ne (Nat.le_of_not_gt hlt) (by
            intro hEq
            apply hkh
            exact hEq.symm)
          have hk_stage : μ (h + 1) ≤ μ k :=
            exercise_7_12_mu_le_of_le ha_nonneg (Nat.succ_le_of_lt hgt) (Nat.le_of_lt hk)
          have hz_stage : z ≤ μ k - lam := by
            have hz_stage_succ : z ≤ μ (h + 1) - lam := by
              rw [hμsucc h]
              linarith [hz.2, hρ_le_weight hh]
            linarith [hz_stage_succ, hk_stage]
          have hz_not_mem_S : z ∉ exercise_7_12_S μ ρ lam k := by
            intro hzS
            exact not_lt_of_ge hz_stage hzS.1
          have hz_not_mem_F : z ∉ exercise_7_12_F μ ρ lam k := by
            intro hzF
            have hz_lower : μ k - lam < z := by
              have hρk_nonneg : 0 ≤ ρ k := hρ_nonneg k
              have hk_lower : μ k - lam ≤ μ k - lam + ρ k := by
                linarith
              exact lt_of_le_of_lt hk_lower hzF.1
            exact not_lt_of_ge hz_stage hz_lower
          have hk_le_target : (0 : ℝ) ≤ (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 :=
            htarget_nonneg
          simpa [pieceValue, hz_not_mem_F, hz_not_mem_S] using hk_le_target
  simpa [exercise_7_12_g, hz0] using hsSup_le

/-- Helper for Exercise 7.12: every tail block of the ordered cover is bounded by the initial
shifted block of the same length. -/
theorem exercise_7_12_mu_tail_le_shifted
    {t : ℕ}
    {a : ℕ → ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k) - exercise_7_12_mu a h ≤
      exercise_7_12_mu a (k + 1) - a 0 := by
  -- Induct on the tail length and compare the newly added ordered weights.
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hhk : h + k < t := by omega
      have hdesc : a (h + k) ≤ a (k + 1) := by
        exact ha_desc (by omega) hhk
      -- Peel off the last summand on both partial sums and reuse the induction hypothesis.
      have hsucc : h + (k + 1) = h + k + 1 := by omega
      have ih' := ih (by omega)
      rw [hsucc, exercise_7_12_mu_succ a (h + k), exercise_7_12_mu_succ a (k + 1)]
      linarith

/-- Helper for Exercise 7.12: the start of stage `h + k` is controlled by the start of stage `h`
and the cutpoint of stage `k`. -/
theorem exercise_7_12_stageStart_add_le
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k) - lam ≤
      (exercise_7_12_mu a h - lam) +
        (exercise_7_12_mu a k - lam + exercise_7_12_rho a lam k) := by
  have htail : exercise_7_12_mu a (h + k) - exercise_7_12_mu a h ≤
      exercise_7_12_mu a (k + 1) - a 0 :=
    exercise_7_12_mu_tail_le_shifted ha_desc h1 hkt
  have hρ_lower : a k - (a 0 - lam) ≤ exercise_7_12_rho a lam k := by
    simpa [exercise_7_12_rho] using
      (le_max_right (0 : ℝ) (a k - (a 0 - lam)))
  -- Rewrite the shifted block and absorb the `a k - (a₀ - λ)` term into `ρ k`.
  rw [exercise_7_12_mu_succ a k] at htail
  linarith

/-- Helper for Exercise 7.12: the symmetric start bound is obtained by swapping the two stage
indices. -/
theorem exercise_7_12_stageStart_add_le_symm
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k) - lam ≤
      (exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) +
        (exercise_7_12_mu a k - lam) := by
  -- Reuse the left-handed bound after swapping the roles of `h` and `k`.
  simpa [Nat.add_comm, add_comm, add_left_comm, add_assoc] using
    (exercise_7_12_stageStart_add_le (t := t) (a := a) (lam := lam) ha_desc k1 h1
      (by simpa [Nat.add_comm] using hkt))

/-- Helper for Exercise 7.12: the cutpoint of stage `h + k` is bounded by the sum of the
cutpoints of stages `h` and `k`. -/
theorem exercise_7_12_stageCutpoint_add_le
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k < t) :
    exercise_7_12_mu a (h + k) - lam + exercise_7_12_rho a lam (h + k) ≤
      (exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) +
        (exercise_7_12_mu a k - lam + exercise_7_12_rho a lam k) := by
  have hstart :
      exercise_7_12_mu a (h + k) - lam ≤
        (exercise_7_12_mu a h - lam) +
          (exercise_7_12_mu a k - lam + exercise_7_12_rho a lam k) :=
    exercise_7_12_stageStart_add_le (t := t) (a := a) (lam := lam) ha_desc h1 k1 hkt.le
  have hρ_tail :
      exercise_7_12_rho a lam (h + k) ≤ exercise_7_12_rho a lam h := by
    simpa using
      (exercise_7_12_rho_antitone (t := t) (a := a) (lam := lam) ha_desc (by omega) hkt)
  -- Add the antitone `ρ` estimate to the start inequality.
  linarith

/-- Helper for Exercise 7.12: every point in `(0, b]` lies either in `F₀` or in one of the
positive-stage pieces `S_h` or `F_h`. -/
theorem exercise_7_12_mem_piece_of_Ioc
    {t : ℕ}
    {a : ℕ → ℝ}
    {b z : ℝ}
    (ht0 : 0 < t)
    (hcover_sum : b < exercise_7_12_mu a t)
    (hz0 : 0 < z)
    (hzb : z ≤ b) :
    let μ := exercise_7_12_mu a
    let lam := exercise_7_12_cover_excess a t b
    let ρ := exercise_7_12_rho a lam
    z ∈ exercise_7_12_F μ ρ lam 0 ∨
      ∃ h, 1 ≤ h ∧ h < t ∧
        (z ∈ exercise_7_12_S μ ρ lam h ∨ z ∈ exercise_7_12_F μ ρ lam h) := by
  dsimp
  let μ := exercise_7_12_mu a
  let lam := exercise_7_12_cover_excess a t b
  let ρ := exercise_7_12_rho a lam
  have hlam_pos : 0 < lam := by
    have : 0 < exercise_7_12_cover_excess a t b := by
      dsimp [exercise_7_12_cover_excess]
      linarith
    simpa [lam] using this
  have hμt : μ t - lam = b := by
    have : exercise_7_12_mu a t - exercise_7_12_cover_excess a t b = b := by
      dsimp [exercise_7_12_cover_excess]
      ring
    simpa [μ, lam] using this
  have ht1 : t - 1 + 1 = t := by omega
  have hzt : z ≤ μ t - lam := by
    rw [hμt]
    exact hzb
  have hexists : ∃ j : ℕ, z ≤ μ (j + 1) - lam := by
    refine ⟨t - 1, ?_⟩
    simpa [ht1] using hzt
  let j : ℕ := Nat.find hexists
  have hzj : z ≤ μ (j + 1) - lam := Nat.find_spec hexists
  have hj_le : j ≤ t - 1 := by
    exact Nat.find_min' hexists (by simpa [ht1] using hzt)
  have hjt : j < t := by
    omega
  by_cases hj0 : j = 0
  · have hz_upper : z ≤ μ (0 + 1) - lam := by
      simpa [j, hj0] using hzj
    subst j
    left
    have hρ0 : ρ 0 = lam := by
      simp [ρ, exercise_7_12_rho, hlam_pos.le]
    -- The first piece starts at `0` because `ρ₀ = λ`.
    have hz_lower : μ 0 - lam + ρ 0 < z := by
      simpa [μ, hρ0] using hz0
    have hz_upper' : z ≤ μ 1 - lam := by
      simpa [μ] using hz_upper
    exact ⟨hz_lower, hz_upper'⟩
  · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
    have hnot_prev : ¬ z ≤ μ j - lam := by
      intro hzprev
      have hfind_le : j ≤ j - 1 := by
        have : Nat.find hexists ≤ j - 1 := by
          apply Nat.find_min'
          simpa [j, Nat.sub_add_cancel hj1] using hzprev
        simpa [j] using this
      omega
    have hz_left : μ j - lam < z := by
      linarith
    by_cases hq : z ≤ μ j - lam + ρ j
    · -- If `z` stays before the stage cutpoint, it lies in `S_j`.
      right
      refine ⟨j, hj1, hjt, Or.inl ?_⟩
      exact ⟨hz_left, hq⟩
    · -- Otherwise `z` lies between the cutpoint and the next stage start, hence in `F_j`.
      right
      refine ⟨j, hj1, hjt, Or.inr ?_⟩
      exact ⟨by linarith, hzj⟩

/-- Helper for Exercise 7.12: each cutpoint correction `ρ_h` stays below the corresponding cover
weight `a_h` when the excess satisfies `λ ≤ a₀`. -/
theorem exercise_7_12_rho_le_weight
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_nonneg : ∀ ⦃h : ℕ⦄, h < t → 0 ≤ a h)
    (hlam_le_a0 : lam ≤ a 0)
    {h : ℕ}
    (hh : h < t) :
    exercise_7_12_rho a lam h ≤ a h := by
  -- Split on whether the defining `max` for `ρ_h` is active.
  by_cases harg : 0 ≤ a h - (a 0 - lam)
  · have hbase : 0 ≤ a 0 - lam := sub_nonneg.mpr hlam_le_a0
    simp [exercise_7_12_rho, harg]
    linarith
  · have hlt : a h - (a 0 - lam) < 0 := lt_of_not_ge harg
    have hah_nonneg : 0 ≤ a h := ha_nonneg hh
    simp [exercise_7_12_rho, hlt.le]
    exact hah_nonneg

/-- Helper for Exercise 7.12: moving the positive-part correction from a larger weight to a
smaller weight can only increase the corrected sum. -/
theorem exercise_7_12_shiftedMax_exchange
    {x y θ : ℝ}
    (hyx : y ≤ x) :
    y + max 0 (x - θ) ≤ x + max 0 (y - θ) := by
  -- Compare the two positive parts by splitting on whether the shifted weights cross the cutoff.
  have hshift : y - θ ≤ x - θ := by
    linarith
  by_cases hy : 0 ≤ y - θ
  · have hx : 0 ≤ x - θ := le_trans hy hshift
    rw [max_eq_right hx, max_eq_right hy]
    linarith
  · have hy' : y - θ ≤ 0 := le_of_not_ge hy
    by_cases hx : 0 ≤ x - θ
    · rw [max_eq_right hx, max_eq_left hy']
      linarith
    · have hx' : x - θ ≤ 0 := le_of_not_ge hx
      rw [max_eq_left hx', max_eq_left hy']
      linarith

/-- Helper for Exercise 7.12: advancing one stage lowers the raw weight enough to compensate for
the change in the cutpoint correction. -/
theorem exercise_7_12_succWeight_add_rho_le_weight_add_succRho
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {k : ℕ}
    (hk : k + 1 < t) :
    a (k + 1) + exercise_7_12_rho a lam k ≤
      a k + exercise_7_12_rho a lam (k + 1) := by
  -- Apply the generic exchange inequality to the ordered neighboring weights.
  have hdesc : a (k + 1) ≤ a k := ha_desc (Nat.le_succ k) hk
  simpa [exercise_7_12_rho] using
    (exercise_7_12_shiftedMax_exchange (x := a k) (y := a (k + 1)) (θ := a 0 - lam) hdesc)

/-- Helper for Exercise 7.12: moving the distinguished correction `ρ₁` from the first positive
weight to a later ordered weight keeps the corrected sum below the stage-`h` correction. -/
theorem exercise_7_12_weight_add_rho1_le_weight1_add_rho
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h : ℕ}
    (h1 : 1 ≤ h)
    (hh : h < t) :
    a h + exercise_7_12_rho a lam 1 ≤ a 1 + exercise_7_12_rho a lam h := by
  -- Compare the ordered weights `a₁` and `a_h` in the generic exchange inequality.
  have hdesc : a h ≤ a 1 := ha_desc h1 hh
  simpa [exercise_7_12_rho] using
    (exercise_7_12_shiftedMax_exchange (x := a 1) (y := a h) (θ := a 0 - lam) hdesc)

/-- Helper for Exercise 7.12: every positive-stage tail keeps a full `ρ₁` of slack when it is
compared with the shifted initial prefix of the same length. -/
theorem exercise_7_12_tail_add_rho1_le_shiftedPrefix
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k) - exercise_7_12_mu a h + exercise_7_12_rho a lam 1 ≤
      exercise_7_12_mu a (k + 1) - a 0 + exercise_7_12_rho a lam h := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le k1
  induction m with
  | zero =>
      -- The one-step tail is exactly the exchanged weight inequality.
      simpa [exercise_7_12_mu_succ, add_comm, add_left_comm, add_assoc] using
        (exercise_7_12_weight_add_rho1_le_weight1_add_rho
          (t := t) (a := a) (lam := lam) ha_desc h1 (by simpa using hkt))
  | succ m ih =>
      have hm_lt : h + (m + 1) < t := by
        omega
      have hdesc : a (h + (m + 1)) ≤ a (m + 2) := by
        exact ha_desc (by omega) hm_lt
      have ih' :
          exercise_7_12_mu a (h + (m + 1)) - exercise_7_12_mu a h +
              exercise_7_12_rho a lam 1 ≤
            exercise_7_12_mu a (m + 2) - a 0 + exercise_7_12_rho a lam h :=
        by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (by omega) (by omega)
      -- Peel off the last summand on both sides and compare the newly added weights.
      have hleft :
          exercise_7_12_mu a (h + (1 + (m + 1))) - exercise_7_12_mu a h +
              exercise_7_12_rho a lam 1 =
            (exercise_7_12_mu a (h + (m + 1)) - exercise_7_12_mu a h +
                exercise_7_12_rho a lam 1) +
              a (h + (m + 1)) := by
        rw [show h + (1 + (m + 1)) = (h + (m + 1)) + 1 by omega,
          exercise_7_12_mu_succ a (h + (m + 1))]
        ring
      have hright :
          exercise_7_12_mu a (1 + (m + 1) + 1) - a 0 + exercise_7_12_rho a lam h =
            (exercise_7_12_mu a (m + 2) - a 0 + exercise_7_12_rho a lam h) +
              a (m + 2) := by
        rw [show 1 + (m + 1) + 1 = (m + 2) + 1 by omega, exercise_7_12_mu_succ a (m + 2)]
        ring
      linarith

/-- Helper for Exercise 7.12: the start of the fallback stage `h + k - 1` lies to the left of
the sum of the starts of stages `h` and `k`. -/
theorem exercise_7_12_prevStageStart_add_le
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hlam_le_a0 : lam ≤ a 0)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k - 1) - lam ≤
      (exercise_7_12_mu a h - lam) + (exercise_7_12_mu a k - lam) := by
  -- Compare the shifted tail of length `k - 1` with the initial block of the same length.
  have htail :
      exercise_7_12_mu a (h + k - 1) - exercise_7_12_mu a h ≤
        exercise_7_12_mu a k - a 0 := by
    have hadd : h + (k - 1) = h + k - 1 := by
      omega
    have hkcancel : k - 1 + 1 = k := by
      omega
    simpa [hadd, hkcancel] using
      (exercise_7_12_mu_tail_le_shifted (t := t) (a := a) (h := h) (k := k - 1) ha_desc h1
        (by omega))
  linarith

/-- Helper for Exercise 7.12: adding a full `ρ₁` of slack still keeps the stage start `h + k`
below the sum of the two stage cutpoints. -/
theorem exercise_7_12_stageStart_add_rho1_le
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hkt : h + k ≤ t) :
    exercise_7_12_mu a (h + k) - lam + exercise_7_12_rho a lam 1 ≤
      (exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) +
        (exercise_7_12_mu a k - lam + exercise_7_12_rho a lam k) := by
  have htail :
      exercise_7_12_mu a (h + k) - exercise_7_12_mu a h + exercise_7_12_rho a lam 1 ≤
        exercise_7_12_mu a (k + 1) - a 0 + exercise_7_12_rho a lam h :=
    exercise_7_12_tail_add_rho1_le_shiftedPrefix
      (t := t) (a := a) (lam := lam) ha_desc h1 k1 hkt
  have hρ_lower : a k - (a 0 - lam) ≤ exercise_7_12_rho a lam k := by
    -- The stage-`k` correction dominates the raw shifted weight by definition.
    simpa [exercise_7_12_rho] using
      (le_max_right (0 : ℝ) (a k - (a 0 - lam)))
  -- Rewrite the shifted prefix endpoint and absorb the remaining scalar term into `ρ_k`.
  rw [exercise_7_12_mu_succ a k] at htail
  linarith

/-- Helper for Exercise 7.12: if a point lies past stage `s` but still before the next endpoint of
stage `h`, then the monotonicity of the partial sums forces `s ≤ h`. -/
theorem exercise_7_12_stageIndex_le_of_stageBounds
    {t : ℕ}
    {a : ℕ → ℝ}
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    {s h : ℕ}
    (hs : s < t)
    (hh : h < t)
    {lam z : ℝ}
    (hs_lower : exercise_7_12_mu a s - lam < z)
    (hh_upper : z ≤ exercise_7_12_mu a (h + 1) - lam) :
    s ≤ h := by
  -- A later stage endpoint cannot lie to the left of an earlier stage start.
  by_contra hsh
  have hhs : h < s := lt_of_not_ge hsh
  have hμ : exercise_7_12_mu a (h + 1) ≤ exercise_7_12_mu a s :=
    exercise_7_12_mu_le_of_le ha_nonneg (Nat.succ_le_of_lt hhs) hs.le
  have hz_le : z ≤ exercise_7_12_mu a s - lam := by
    linarith
  exact not_lt_of_ge hz_le hs_lower

/-- Helper for Exercise 7.12: once the evaluation point has reached the actual stage `h`, every
earlier positive-stage support line lies below the stage-`h` support line. -/
theorem exercise_7_12_supportLine_le_of_stage_le
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hrho1_pos : 0 < exercise_7_12_rho a lam 1)
    {s h : ℕ}
    (hs1 : 1 ≤ s)
    (hsh : s ≤ h)
    (hh : h < t)
    {z : ℝ}
    (hh_lower : exercise_7_12_mu a h - lam < z) :
    (s : ℝ) -
        max 0
            ((exercise_7_12_mu a s - lam + exercise_7_12_rho a lam s) - z) /
          exercise_7_12_rho a lam 1 ≤
      (h : ℝ) -
        max 0
            ((exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z) /
          exercise_7_12_rho a lam 1 := by
  rcases Nat.eq_or_lt_of_le hsh with rfl | hlt
  · -- When the requested stage is the actual stage, the support lines coincide.
    exact le_rfl
  · -- Otherwise the later-stage support line still stays above the earlier stage index.
    have h1 : 1 ≤ h := le_trans hs1 hsh
    have hleft_div_nonneg :
        0 ≤
          max 0
              ((exercise_7_12_mu a s - lam + exercise_7_12_rho a lam s) - z) /
            exercise_7_12_rho a lam 1 := by
      exact div_nonneg (le_max_left _ _) hrho1_pos.le
    have hleft_le :
        (s : ℝ) -
            max 0
                ((exercise_7_12_mu a s - lam + exercise_7_12_rho a lam s) - z) /
              exercise_7_12_rho a lam 1 ≤
          s := by
      linarith
    have hrhoh_le :
        exercise_7_12_rho a lam h ≤ exercise_7_12_rho a lam 1 := by
      exact exercise_7_12_rho_antitone (t := t) (a := a) (lam := lam) ha_desc h1 hh
    have hraw_le_rhoh :
        (exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z ≤
          exercise_7_12_rho a lam h := by
      linarith
    have hmax_le_rho1 :
        max 0
            ((exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z) ≤
          exercise_7_12_rho a lam 1 := by
      refine le_trans ?_ hrhoh_le
      exact max_le_iff.mpr ⟨exercise_7_12_rho_nonneg a lam h, hraw_le_rhoh⟩
    have hfrac_le_one :
        max 0
            ((exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z) /
          exercise_7_12_rho a lam 1 ≤
        1 := by
      have hbound :
          max 0
              ((exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z) ≤
            (1 : ℝ) * exercise_7_12_rho a lam 1 := by
        simpa using hmax_le_rho1
      simpa using (div_le_iff₀ hrho1_pos).2 hbound
    have hs_gap : (s : ℝ) + 1 ≤ h := by
      exact_mod_cast Nat.succ_le_of_lt hlt
    have hright_ge :
        (s : ℝ) ≤
          (h : ℝ) -
            max 0
                ((exercise_7_12_mu a h - lam + exercise_7_12_rho a lam h) - z) /
              exercise_7_12_rho a lam 1 := by
      linarith
    exact le_trans hleft_le hright_ge

/-- Helper for Exercise 7.12: every nonzero point of `[0,b]` admits a stage representation of the
form `h - max(0, q_h - z) / ρ₁` that matches the exact value of `g`. -/
theorem exercise_7_12_exists_stage_representation
    {t : ℕ}
    {a : ℕ → ℝ}
    {b : ℝ}
    (ht0 : 0 < t)
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hlam_le_a0 : exercise_7_12_cover_excess a t b ≤ a 0)
    (hcover_sum : b < exercise_7_12_mu a t)
    (hrho1_pos : 0 < exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1)
    {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hz0 : z ≠ 0) :
    ∃ h, h < t ∧
      exercise_7_12_mu a h - exercise_7_12_cover_excess a t b < z ∧
      z ≤ exercise_7_12_mu a (h + 1) - exercise_7_12_cover_excess a t b ∧
      exercise_7_12_g t (exercise_7_12_mu a)
          (exercise_7_12_rho a (exercise_7_12_cover_excess a t b))
          (exercise_7_12_cover_excess a t b) z =
        (h : ℝ) -
          max 0
              ((exercise_7_12_mu a h - exercise_7_12_cover_excess a t b +
                    exercise_7_12_rho a (exercise_7_12_cover_excess a t b) h) -
                  z) /
            exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1 := by
  let μ := exercise_7_12_mu a
  let lam := exercise_7_12_cover_excess a t b
  let ρ := exercise_7_12_rho a lam
  have hz_pos : 0 < z := by
    have hz_nonneg : 0 ≤ z := hz.1
    exact lt_of_le_of_ne hz_nonneg (Ne.symm hz0)
  have hpiece :
      z ∈ exercise_7_12_F μ ρ lam 0 ∨
        ∃ h, 1 ≤ h ∧ h < t ∧ (z ∈ exercise_7_12_S μ ρ lam h ∨ z ∈ exercise_7_12_F μ ρ lam h) :=
    exercise_7_12_mem_piece_of_Ioc (t := t) (a := a) (b := b) ht0 hcover_sum hz_pos hz.2
  rcases hpiece with hzF0 | hpos
  · have hg0 :
        exercise_7_12_g t μ ρ lam z = (0 : ℝ) := by
      simpa [μ, lam, ρ] using
        (exercise_7_12_g_eq_of_mem_F
          (t := t) (a := a) (lam := lam) (h := 0) ha_nonneg hlam_le_a0 ht0 hz0 hzF0)
    have hlower : μ 0 - lam < z := by
      have hlam_pos : 0 < lam := by
        dsimp [lam, exercise_7_12_cover_excess]
        linarith
      simpa [μ] using (show -lam < z by linarith)
    have hdeficit_lt :
        (μ 0 - lam + ρ 0) - z < 0 := by
      linarith [hzF0.1]
    have hdeficit_eq :
        max 0 ((μ 0 - lam + ρ 0) - z) = 0 := by
      simp [hdeficit_lt.le]
    refine ⟨0, ht0, ?_, ?_, ?_⟩
    · simpa [μ, lam] using hlower
    · simpa [μ, lam, ρ] using hzF0.2
    · simpa [μ, lam, ρ] using
        (calc
          exercise_7_12_g t μ ρ lam z = (0 : ℝ) := hg0
          _ = (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - z) / ρ 1 := by
            simp [hdeficit_eq])
  · rcases hpos with ⟨h, h1, hh, hzpiece⟩
    rcases hzpiece with hzS | hzF
    · have hcut_le :
          μ h - lam + ρ h ≤ μ (h + 1) - lam := by
        have hμsucc : μ (h + 1) = μ h + a h := by
          simpa [μ] using exercise_7_12_mu_succ a h
        rw [hμsucc]
        linarith [exercise_7_12_rho_le_weight (t := t) (a := a) (lam := lam) ha_nonneg hlam_le_a0 hh]
      have hgS :
          exercise_7_12_g t μ ρ lam z =
            (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 := by
        simpa [μ, lam, ρ] using
          (exercise_7_12_g_eq_of_mem_S
            (t := t) (a := a) (lam := lam) (h := h)
            ha_nonneg ha_desc hlam_le_a0 h1 hh hrho1_pos hz0 hzS)
      have hdeficit_nonneg : 0 ≤ (μ h - lam + ρ h) - z := by
        linarith [hzS.2]
      refine ⟨h, hh, ?_, ?_, ?_⟩
      · simpa [μ, lam] using hzS.1
      · simpa [μ, lam] using le_trans hzS.2 hcut_le
      -- On an `S_h` piece the active deficit is nonnegative, so the support-line form is exact.
      · simpa [μ, lam, ρ] using
          (calc
            exercise_7_12_g t μ ρ lam z = (h : ℝ) - (μ h - lam + ρ h - z) / ρ 1 := hgS
            _ = (h : ℝ) - max 0 ((μ h - lam + ρ h) - z) / ρ 1 := by
              rw [max_eq_right hdeficit_nonneg])
    · have hgF :
          exercise_7_12_g t μ ρ lam z = (h : ℝ) := by
        simpa [μ, lam, ρ] using
          (exercise_7_12_g_eq_of_mem_F
            (t := t) (a := a) (lam := lam) (h := h) ha_nonneg hlam_le_a0 hh hz0 hzF)
      have hlower : μ h - lam < z := by
        linarith [hzF.1, exercise_7_12_rho_nonneg a lam h]
      have hdeficit_lt : (μ h - lam + ρ h) - z < 0 := by
        linarith [hzF.1]
      have hdeficit_eq :
          max 0 ((μ h - lam + ρ h) - z) = 0 := by
        simp [hdeficit_lt.le]
      refine ⟨h, hh, ?_, ?_, ?_⟩
      · simpa [μ, lam] using hlower
      · simpa [μ, lam] using hzF.2
      -- On an `F_h` piece the deficit vanishes, so the support-line form collapses to the stage value.
      · simpa [μ, lam, ρ] using
          (calc
            exercise_7_12_g t μ ρ lam z = (h : ℝ) := hgF
            _ = (h : ℝ) - max 0 ((μ h - lam + ρ h) - z) / ρ 1 := by
              simp [hdeficit_eq])

/-- Helper for Exercise 7.12: every positive stage provides a valid lower support line for `g`
once the evaluation point has moved past that stage start. -/
theorem exercise_7_12_stageSupport_le_g
    {t : ℕ}
    {a : ℕ → ℝ}
    {b : ℝ}
    (ht0 : 0 < t)
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hlam_le_a0 : exercise_7_12_cover_excess a t b ≤ a 0)
    (hcover_sum : b < exercise_7_12_mu a t)
    (hrho1_pos : 0 < exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1)
    {s : ℕ}
    (hs1 : 1 ≤ s)
    (hs : s < t)
    {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hstart : exercise_7_12_mu a s - exercise_7_12_cover_excess a t b < z) :
    (s : ℝ) -
        max 0
            ((exercise_7_12_mu a s - exercise_7_12_cover_excess a t b +
                  exercise_7_12_rho a (exercise_7_12_cover_excess a t b) s) -
                z) /
          exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1 ≤
      exercise_7_12_g t (exercise_7_12_mu a)
        (exercise_7_12_rho a (exercise_7_12_cover_excess a t b))
        (exercise_7_12_cover_excess a t b) z := by
  let μ := exercise_7_12_mu a
  let lam := exercise_7_12_cover_excess a t b
  let ρ := exercise_7_12_rho a lam
  have hμ1_le : μ 1 ≤ μ s :=
    exercise_7_12_mu_le_of_le ha_nonneg hs1 hs.le
  have hstage_nonneg : 0 ≤ μ s - lam := by
    have hbase : 0 ≤ μ 1 - lam := by
      simpa [μ, lam] using sub_nonneg.mpr hlam_le_a0
    linarith
  have hz0 : z ≠ 0 := by
    -- The requested support stage starts at a nonnegative point, so `z = 0` cannot satisfy `hstart`.
    intro hz0
    have : ¬ μ s - lam < z := by
      simpa [hz0] using not_lt_of_ge hstage_nonneg
    exact this hstart
  -- Route correction: use the actual active-stage representation, then compare support lines once.
  rcases
      exercise_7_12_exists_stage_representation
        (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos hz hz0 with
    ⟨h, hh, hh_lower, hh_upper, hg⟩
  have hsh : s ≤ h :=
    exercise_7_12_stageIndex_le_of_stageBounds
      (t := t) (a := a) ha_nonneg hs hh hstart hh_upper
  have hsupport :
      (s : ℝ) -
          max 0 (((μ s - lam + ρ s) - z)) / ρ 1 ≤
        (h : ℝ) -
          max 0 (((μ h - lam + ρ h) - z)) / ρ 1 :=
    exercise_7_12_supportLine_le_of_stage_le
      (t := t) (a := a) (lam := lam) ha_desc hrho1_pos hs1 hsh hh hh_lower
  -- The exact stage formula identifies the later support line with the actual value of `g z`.
  calc
    (s : ℝ) - max 0 (((μ s - lam + ρ s) - z)) / ρ 1
        ≤ (h : ℝ) - max 0 (((μ h - lam + ρ h) - z)) / ρ 1 := hsupport
    _ = exercise_7_12_g t μ ρ lam z := by simpa [μ, lam, ρ] using hg.symm

/-- Helper for Exercise 7.12: two positive active stages cannot add past the cover length once
their stage starts already lie below a point of `[0,b]`. -/
theorem exercise_7_12_positiveStageIndexSum_le_t
    {t : ℕ}
    {a : ℕ → ℝ}
    {b lam u v : ℝ}
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    {h k : ℕ}
    (h1 : 1 ≤ h)
    (k1 : 1 ≤ k)
    (hh : h < t)
    (hk : k < t)
    (hcover : exercise_7_12_mu a t - lam = b)
    (huv : u + v ∈ Set.Icc (0 : ℝ) b)
    (hu_lower : exercise_7_12_mu a h - lam < u)
    (hv_lower : exercise_7_12_mu a k - lam < v)
    (hmu1_lam_pos : 0 < exercise_7_12_mu a 1 - lam) :
    h + k ≤ t := by
  by_contra hkt
  have htt : t < h + k := lt_of_not_ge hkt
  -- Compare the tail beyond stage `h` with the initial block of the same length.
  have htail :
      exercise_7_12_mu a t - exercise_7_12_mu a h ≤
        exercise_7_12_mu a (t - h + 1) - a 0 := by
    have hshift : h + (t - h) ≤ t := by
      omega
    simpa [Nat.add_sub_of_le hh.le, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (exercise_7_12_mu_tail_le_shifted
        (t := t) (a := a) (h := h) (k := t - h) ha_desc h1 hshift)
  have hprefix :
      exercise_7_12_mu a (t - h + 1) ≤ exercise_7_12_mu a k := by
    refine exercise_7_12_mu_le_of_le (t := t) (a := a) ha_nonneg ?_ hk.le
    omega
  have hsum :
      exercise_7_12_mu a t + exercise_7_12_mu a 1 ≤
        exercise_7_12_mu a h + exercise_7_12_mu a k := by
    have hμ1 : exercise_7_12_mu a 1 = a 0 := by
      simp [exercise_7_12_mu]
    rw [hμ1]
    linarith
  -- The stage-start hypotheses then force `u + v` strictly above `b`, contradicting `huv`.
  have hsum_lt :
      exercise_7_12_mu a t + exercise_7_12_mu a 1 - 2 * lam < u + v := by
    linarith
  have hb1_lt : b + (exercise_7_12_mu a 1 - lam) < u + v := by
    linarith [hcover, hsum_lt]
  have hb_lt : b < u + v := by
    linarith
  linarith [huv.2, hb_lt]

/-- Helper for Exercise 7.12: every stage cutpoint lies to the left of the next stage start. -/
theorem exercise_7_12_prevStageCutpoint_le_nextStageStart
    {t : ℕ}
    {a : ℕ → ℝ}
    {lam : ℝ}
    (ha_nonneg : ∀ ⦃k : ℕ⦄, k < t → 0 ≤ a k)
    (hlam_le_a0 : lam ≤ a 0)
    {s : ℕ}
    (hs : s < t) :
    exercise_7_12_mu a s - lam + exercise_7_12_rho a lam s ≤
      exercise_7_12_mu a (s + 1) - lam := by
  -- Rewrite the next stage start and absorb the cutpoint correction into the stage weight.
  rw [exercise_7_12_mu_succ a s]
  linarith [exercise_7_12_rho_le_weight (t := t) (a := a) (lam := lam) ha_nonneg hlam_le_a0 hs]

/-- Exercise 7.12. Let `a₀ ≥ ⋯ ≥ a_{t-1} > 0` be the ordered cover weights, let
`μ_h = a₀ + ⋯ + a_{h-1}`, let `λ = μ_t - b`, and let `ρ_h = max (0, a_h - (a₀ - λ))`.
If the prefix cover of size `t` is minimal and `μ₁ - λ ≥ ρ₁ > 0`, then the GNS auxiliary
lifting function `(7.12)` is superadditive on `[0, b]`. -/
theorem exercise_7_12_g_superadditive_on_Icc
    (t : ℕ)
    (a : ℕ → ℝ)
    (b : ℝ)
    (ht : 1 < t)
    (ha_pos : ∀ ⦃h : ℕ⦄, h < t → 0 < a h)
    (ha_desc : ∀ ⦃i j : ℕ⦄, i ≤ j → j < t → a j ≤ a i)
    (hcover_drop_last : exercise_7_12_mu a t - a (t - 1) ≤ b)
    (hcover_sum : b < exercise_7_12_mu a t)
    (hmu1 :
      exercise_7_12_mu a 1 - exercise_7_12_cover_excess a t b ≥
        exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1)
    (hrho1_pos : 0 < exercise_7_12_rho a (exercise_7_12_cover_excess a t b) 1) :
    let μ := exercise_7_12_mu a
    let lam := exercise_7_12_cover_excess a t b
    let ρ := exercise_7_12_rho a lam
    is_superadditive_on_Icc (exercise_7_12_g t μ ρ lam) b := by
  dsimp
  let μ := exercise_7_12_mu a
  let lam := exercise_7_12_cover_excess a t b
  let ρ := exercise_7_12_rho a lam
  have ht0 : 0 < t := by
    omega
  have ha_nonneg : ∀ ⦃h : ℕ⦄, h < t → 0 ≤ a h := by
    intro h hh
    exact (ha_pos hh).le
  have hmu1' : μ 1 - lam ≥ ρ 1 := by
    simpa [μ, lam, ρ] using hmu1
  have hlam_le_a0 : lam ≤ a 0 := by
    -- The first-stage side condition forces the excess to sit below the largest cover weight.
    have : 0 < μ 1 - lam := lt_of_lt_of_le hrho1_pos hmu1'
    simpa [μ, lam] using this.le
  have hcover : μ t - lam = b := by
    dsimp [μ, lam, exercise_7_12_cover_excess]
    ring
  have hlam_pos : 0 < lam := by
    dsimp [lam, exercise_7_12_cover_excess]
    linarith
  have hρ0 : ρ 0 = lam := by
    simp [ρ, exercise_7_12_rho, hlam_pos.le]
  have hmu1_lam_pos : 0 < μ 1 - lam := by
    exact lt_of_lt_of_le hrho1_pos hmu1'
  intro u v hu hv huv
  by_cases hu0 : u = 0
  · -- The origin branch is immediate because `g 0 = 0`.
    simpa [hu0, exercise_7_12_g_zero, add_comm, add_left_comm, add_assoc] using
      (le_rfl : exercise_7_12_g t μ ρ lam v ≤ exercise_7_12_g t μ ρ lam v)
  by_cases hv0 : v = 0
  · -- The symmetric origin branch is the same calculation with `u` and `v` swapped.
    simpa [hv0, exercise_7_12_g_zero, add_comm, add_left_comm, add_assoc] using
      (le_rfl : exercise_7_12_g t μ ρ lam u ≤ exercise_7_12_g t μ ρ lam u)
  rcases
      exercise_7_12_exists_stage_representation
        (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos hu hu0 with
    ⟨h, hh, hlower, hupper, hgu⟩
  rcases
      exercise_7_12_exists_stage_representation
        (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos hv hv0 with
    ⟨k, hk, klower, kupper, hgv⟩
  by_cases h0 : h = 0
  · subst h
    have hdeficit_eq : max 0 ((μ 0 - lam + ρ 0) - u) = 0 := by
      have hraw_nonpos : (μ 0 - lam + ρ 0) - u ≤ 0 := by
        simp [μ, hρ0]
        linarith [hu.1]
      exact max_eq_left hraw_nonpos
    have hgu_zero : exercise_7_12_g t μ ρ lam u = 0 := by
      -- Stage `0` has cutpoint `q₀ = 0`, so the exact representation collapses to `g u = 0`.
      have hgu' :
          exercise_7_12_g t μ ρ lam u =
            (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - u) / ρ 1 := by
        simpa [μ, lam, ρ] using hgu
      calc
        exercise_7_12_g t μ ρ lam u
            = (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - u) / ρ 1 := hgu'
        _ = 0 := by simp [hdeficit_eq]
    by_cases k0 : k = 0
    · subst k
      have hdeficit_eq' : max 0 ((μ 0 - lam + ρ 0) - v) = 0 := by
        have hraw_nonpos : (μ 0 - lam + ρ 0) - v ≤ 0 := by
          simp [μ, hρ0]
          linarith [hv.1]
        exact max_eq_left hraw_nonpos
      have hgv_zero : exercise_7_12_g t μ ρ lam v = 0 := by
        -- When both active stages are `0`, superadditivity reduces to nonnegativity at `u + v`.
        have hgv' :
            exercise_7_12_g t μ ρ lam v =
              (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - v) / ρ 1 := by
          simpa [μ, lam, ρ] using hgv
        calc
          exercise_7_12_g t μ ρ lam v
              = (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - v) / ρ 1 := hgv'
          _ = 0 := by simp [hdeficit_eq']
      have hsum_nonneg :
          0 ≤ exercise_7_12_g t μ ρ lam (u + v) :=
        exercise_7_12_g_nonneg (t := t) (μ := μ) (ρ := ρ) (lam := lam) (z := u + v)
      linarith
    · have hk1 : 1 ≤ k := by
        omega
      have hstart_sum : μ k - lam < u + v := by
        linarith [klower, hu.1]
      have hsupport :
          (k : ℝ) - max 0 ((μ k - lam + ρ k - (u + v))) / ρ 1 ≤
            exercise_7_12_g t μ ρ lam (u + v) := by
        -- Evaluate the stage-`k` support line at the larger point `u + v`.
        simpa [μ, lam, ρ] using
          (exercise_7_12_stageSupport_le_g
            (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos
            (s := k) hk1 hk huv hstart_sum)
      have hmax_monotone :
          max 0 (μ k - lam + ρ k - (u + v)) ≤
            max 0 (μ k - lam + ρ k - v) := by
        refine max_le_max le_rfl ?_
        linarith [hu.1]
      have hdiv_monotone :
          max 0 (μ k - lam + ρ k - (u + v)) / ρ 1 ≤
            max 0 (μ k - lam + ρ k - v) / ρ 1 := by
        exact div_le_div_of_nonneg_right hmax_monotone hrho1_pos.le
      have hline :
          exercise_7_12_g t μ ρ lam v ≤
            (k : ℝ) - max 0 (μ k - lam + ρ k - (u + v)) / ρ 1 := by
        linarith [hgv, hdiv_monotone]
      linarith [hgu_zero, hline, hsupport]
  by_cases k0 : k = 0
  · subst k
    have hdeficit_eq : max 0 ((μ 0 - lam + ρ 0) - v) = 0 := by
      have hraw_nonpos : (μ 0 - lam + ρ 0) - v ≤ 0 := by
        simp [μ, hρ0]
        linarith [hv.1]
      exact max_eq_left hraw_nonpos
    have hgv_zero : exercise_7_12_g t μ ρ lam v = 0 := by
      -- This is the symmetric stage-`0` collapse for the second summand.
      have hgv' :
          exercise_7_12_g t μ ρ lam v =
            (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - v) / ρ 1 := by
        simpa [μ, lam, ρ] using hgv
      calc
        exercise_7_12_g t μ ρ lam v
            = (0 : ℝ) - max 0 ((μ 0 - lam + ρ 0) - v) / ρ 1 := hgv'
        _ = 0 := by simp [hdeficit_eq]
    have h1 : 1 ≤ h := by
      omega
    have hstart_sum : μ h - lam < u + v := by
      linarith [hlower, hv.1]
    have hsupport :
        (h : ℝ) - max 0 ((μ h - lam + ρ h - (u + v))) / ρ 1 ≤
          exercise_7_12_g t μ ρ lam (u + v) := by
      -- The same monotonicity argument now uses the positive stage of `u`.
      simpa [μ, lam, ρ] using
        (exercise_7_12_stageSupport_le_g
          (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos
          (s := h) h1 hh huv hstart_sum)
    have hmax_monotone :
        max 0 (μ h - lam + ρ h - (u + v)) ≤
          max 0 (μ h - lam + ρ h - u) := by
      refine max_le_max le_rfl ?_
      linarith [hv.1]
    have hdiv_monotone :
        max 0 (μ h - lam + ρ h - (u + v)) / ρ 1 ≤
          max 0 (μ h - lam + ρ h - u) / ρ 1 := by
      exact div_le_div_of_nonneg_right hmax_monotone hrho1_pos.le
    have hline :
        exercise_7_12_g t μ ρ lam u ≤
          (h : ℝ) - max 0 (μ h - lam + ρ h - (u + v)) / ρ 1 := by
      linarith [hgu, hdiv_monotone]
    linarith [hgv_zero, hline, hsupport]
  have h1 : 1 ≤ h := by
    omega
  have k1 : 1 ≤ k := by
    omega
  let q : ℕ → ℝ := fun i ↦ μ i - lam + ρ i
  let A : ℝ := max 0 (q h - u)
  let B : ℝ := max 0 (q k - v)
  have hqhu : q h - u ≤ A := by
    dsimp [A]
    exact le_max_right 0 (q h - u)
  have hqkv : q k - v ≤ B := by
    dsimp [B]
    exact le_max_right 0 (q k - v)
  have hAB_nonneg : 0 ≤ A + B := by
    dsimp [A, B]
    exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  have hsumIndex : h + k ≤ t :=
    exercise_7_12_positiveStageIndexSum_le_t
      (t := t) (a := a) (b := b) (lam := lam) (u := u) (v := v)
      ha_nonneg ha_desc h1 k1 hh hk hcover huv hlower klower hmu1_lam_pos
  have hsum_formula :
      exercise_7_12_g t μ ρ lam u + exercise_7_12_g t μ ρ lam v =
        ((h + k : ℕ) : ℝ) - (A + B) / ρ 1 := by
    -- Combine the two exact active-stage formulas into one common-deficit expression.
    rw [Nat.cast_add]
    have hadd_div : A / ρ 1 + B / ρ 1 = (A + B) / ρ 1 := by
      rw [add_div]
    linarith [hgu, hgv, hadd_div]
  by_cases hAB : A + B < ρ 1
  · have hstageSlack :
        μ (h + k) - lam + ρ 1 ≤ u + v + (A + B) := by
      have hstage :
          μ (h + k) - lam + ρ 1 ≤ q h + q k := by
        simpa [q] using
          (exercise_7_12_stageStart_add_rho1_le
            (t := t) (a := a) (lam := lam) ha_desc h1 k1 hsumIndex)
      have hqh : q h ≤ u + A := by
        linarith
      have hqk : q k ≤ v + B := by
        linarith
      linarith
    have hstart_sum : μ (h + k) - lam < u + v := by
      -- In the low-deficit branch the full `ρ₁` slack forces the next stage start below `u + v`.
      linarith
    have hstage_lt : h + k < t := by
      by_contra hnot
      have heq : h + k = t := by
        omega
      have hb_lt : b < u + v := by
        have hstage_t : b + ρ 1 ≤ u + v + (A + B) := by
          simpa [heq, hcover] using hstageSlack
        linarith
      linarith [huv.2, hb_lt]
    have hcut :
        q (h + k) - (u + v) ≤ A + B := by
      have hcut' :
          q (h + k) ≤ q h + q k := by
        simpa [q] using
          (exercise_7_12_stageCutpoint_add_le
            (t := t) (a := a) (lam := lam) ha_desc h1 k1 hstage_lt)
      linarith
    have hmax_le :
        max 0 (q (h + k) - (u + v)) ≤ A + B := by
      exact max_le_iff.mpr ⟨hAB_nonneg, hcut⟩
    have hdiv :
        max 0 (q (h + k) - (u + v)) / ρ 1 ≤ (A + B) / ρ 1 := by
      exact div_le_div_of_nonneg_right hmax_le hrho1_pos.le
    have hline :
        exercise_7_12_g t μ ρ lam u + exercise_7_12_g t μ ρ lam v ≤
          ((h + k : ℕ) : ℝ) - max 0 (q (h + k) - (u + v)) / ρ 1 := by
      linarith
    have hsupport :
        ((h + k : ℕ) : ℝ) - max 0 (q (h + k) - (u + v)) / ρ 1 ≤
          exercise_7_12_g t μ ρ lam (u + v) := by
      -- Feed the chosen stage `h + k` into the support-envelope API.
      simpa [q, μ, lam, ρ] using
        (exercise_7_12_stageSupport_le_g
          (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos
          (s := h + k) (by omega) hstage_lt huv hstart_sum)
    exact le_trans hline hsupport
  · have hAB_ge : ρ 1 ≤ A + B := by
      exact le_of_not_gt hAB
    have hs1 : 1 ≤ h + k - 1 := by
      omega
    have hs : h + k - 1 < t := by
      omega
    have hstart_prev : μ (h + k - 1) - lam < u + v := by
      -- The fallback stage start stays below `u + v` by the previous-stage start estimate.
      have hprev :
          μ (h + k - 1) - lam ≤ (μ h - lam) + (μ k - lam) := by
        exact exercise_7_12_prevStageStart_add_le
          (t := t) (a := a) (lam := lam) ha_desc hlam_le_a0 h1 k1 hsumIndex
      linarith
    have hbridge :
        q (h + k - 1) ≤ μ (h + k) - lam := by
      have hbridge_raw :
          μ (h + k - 1) - lam + ρ (h + k - 1) ≤ μ ((h + k - 1) + 1) - lam := by
        simpa [μ, lam, ρ] using
          (exercise_7_12_prevStageCutpoint_le_nextStageStart
            (t := t) (a := a) (lam := lam) ha_nonneg hlam_le_a0 (s := h + k - 1) hs)
      have hstep : (h + k - 1) + 1 = h + k := by
        omega
      simpa [q, hstep] using hbridge_raw
    have hstageSlack :
        q (h + k - 1) + ρ 1 ≤ u + v + (A + B) := by
      have hstage :
          μ (h + k) - lam + ρ 1 ≤ q h + q k := by
        simpa [q] using
          (exercise_7_12_stageStart_add_rho1_le
            (t := t) (a := a) (lam := lam) ha_desc h1 k1 hsumIndex)
      have hqh : q h ≤ u + A := by
        linarith
      have hqk : q k ≤ v + B := by
        linarith
      linarith
    have hraw :
        q (h + k - 1) - (u + v) ≤ A + B - ρ 1 := by
      linarith
    have hAB_sub_nonneg : 0 ≤ A + B - ρ 1 := by
      linarith
    have hmax_le :
        max 0 (q (h + k - 1) - (u + v)) ≤ A + B - ρ 1 := by
      exact max_le_iff.mpr ⟨hAB_sub_nonneg, hraw⟩
    have hdiv :
        max 0 (q (h + k - 1) - (u + v)) / ρ 1 ≤ (A + B - ρ 1) / ρ 1 := by
      exact div_le_div_of_nonneg_right hmax_le hrho1_pos.le
    have hsub_div : (A + B - ρ 1) / ρ 1 = (A + B) / ρ 1 - 1 := by
      have hρ1_ne : ρ 1 ≠ 0 := ne_of_gt hrho1_pos
      rw [sub_div]
      simp [hρ1_ne]
    have hs_cast : (((h + k - 1 : ℕ) : ℝ)) = ((h + k : ℕ) : ℝ) - 1 := by
      have hkpos : 1 ≤ h + k := by
        omega
      rw [Nat.cast_sub hkpos]
      norm_num
    have hline :
        exercise_7_12_g t μ ρ lam u + exercise_7_12_g t μ ρ lam v ≤
          ((h + k - 1 : ℕ) : ℝ) - max 0 (q (h + k - 1) - (u + v)) / ρ 1 := by
      -- The high-deficit branch spends one full unit of `ρ₁` and falls back to stage `h + k - 1`.
      linarith
    have hsupport :
        ((h + k - 1 : ℕ) : ℝ) - max 0 (q (h + k - 1) - (u + v)) / ρ 1 ≤
          exercise_7_12_g t μ ρ lam (u + v) := by
      -- Feed the fallback stage into the support-envelope API.
      simpa [q, μ, lam, ρ] using
        (exercise_7_12_stageSupport_le_g
          (t := t) (a := a) (b := b) ht0 ha_nonneg ha_desc hlam_le_a0 hcover_sum hrho1_pos
          (s := h + k - 1) hs1 hs huv hstart_prev)
    exact le_trans hline hsupport
