/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_21

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω}
variable {X : ℕ → Ω → ℤ}

section SymmetricSimpleRandomWalk

variable (hX_law : ∀ n,
  HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P)

local notation "Xℝ" => fun n ω ↦ (X n ω : ℝ)
local notation "X∞" => fun n ω ↦ (((X n ω : ℤ) : ℝ) : EReal)

/-
Example 11.15 is `source-facing`: its public content is the almost-sure oscillation and failure of
convergence or uniform integrability for a symmetric simple random walk on `ℤ`. The
`core/canonical` owner layer is the increment process `n ↦ X (n + 1) - X n`, the Chapter 2
random-walk partial-sum
theorem `ae_limsup_random_walk_partial_sum_eq_top_of_independent_fair_signs`, the Chapter 9 owner
theorem `symmetricSimpleRandomWalk_squareIntegrable_martingale`, and the Chapter 11 owner
convergence theorem `Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable`. The relevant
`bridge/view` is the centered walk `n ↦ X n - X 0`, obtained by translating the path by its
initial offset. This file keeps only those source-facing consequences and does not introduce a
parallel walk wrapper around that owner data.
-/
local instance : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
local instance : IsFiniteMeasure P := (hX_law 0).isFiniteMeasure

omit hX_law

/-- Helper for Example 11.15: a variable with the symmetric Rademacher law gives mass `1 / 2`
to the atom `{-1}`. -/
private lemma hasLaw_symmetricRademacher_preimage_negOne
    (P : Measure Ω) (Y : Ω → ℤ) (hY : HasLaw Y symmetricRademacherLaw P) :
    P (Set.preimage Y (Set.singleton (-1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
  -- Proof comment: transport the singleton mass through the pushforward law of `Y`.
  change P (Y ⁻¹' {(-1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹
  rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (-1 : ℤ))]
  rw [hY.map_eq]
  simp [symmetricRademacherLaw, one_div]

/-- Helper for Example 11.15: a variable with the symmetric Rademacher law gives mass `1 / 2`
to the atom `{1}`. -/
private lemma hasLaw_symmetricRademacher_preimage_one
    (P : Measure Ω) (Y : Ω → ℤ) (hY : HasLaw Y symmetricRademacherLaw P) :
    P (Set.preimage Y (Set.singleton (1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
  -- Proof comment: the singleton `{1}` mass is the owner theorem for the symmetric law.
  change P (Y ⁻¹' {(1 : ℤ)}) = (2 : ℝ≥0∞)⁻¹
  rw [← Measure.map_apply_of_aemeasurable hY.aemeasurable (measurableSet_singleton (1 : ℤ))]
  rw [hY.map_eq]
  simpa [one_div] using symmetricRademacherLaw_apply_singleton_one

/-- Helper for Example 11.15: the partial sums of the increment process telescope to
`X n - X 0`. -/
private lemma randomWalkPartialSum_increments_eq_sub_initial :
    ∀ n ω,
      random_walk_partial_sum (fun k ω' ↦ X (k + 1) ω' - X k ω') n ω = X n ω - X 0 ω := by
  intro n ω
  induction n with
  | zero =>
      -- Proof comment: the length-`0` partial sum is empty, so only the initial offset remains.
      simp [random_walk_partial_sum]
  | succ n ih =>
      -- Proof comment: split off the last increment and telescope the intermediate terms.
      have hsum :
          ∑ x ∈ Finset.range n, (X (x + 1) ω - X x ω) = X n ω - X 0 ω := by
        simpa [random_walk_partial_sum] using ih
      rw [random_walk_partial_sum, Finset.sum_range_succ, hsum]
      omega

/-- Helper for Example 11.15: the partial sums of the negated increments telescope to
`X 0 - X n`. -/
private lemma randomWalkPartialSum_negIncrements_eq_initial_sub :
    ∀ n ω,
      random_walk_partial_sum (fun k ω' ↦ -(X (k + 1) ω' - X k ω')) n ω = X 0 ω - X n ω := by
  intro n ω
  induction n with
  | zero =>
      -- Proof comment: the length-`0` partial sum is empty, so only the initial offset remains.
      simp [random_walk_partial_sum]
  | succ n ih =>
      -- Proof comment: split off the last negated increment and telescope as before.
      have hsum :
          ∑ x ∈ Finset.range n, -(X (x + 1) ω - X x ω) = X 0 ω - X n ω := by
        simpa [random_walk_partial_sum] using ih
      rw [random_walk_partial_sum, Finset.sum_range_succ, hsum]
      omega

/-- Helper for Example 11.15: negating a symmetric Rademacher variable preserves its law. -/
private lemma symmetricRademacherLaw_map_neg :
    Measure.map (fun z : ℤ ↦ -z) symmetricRademacherLaw = symmetricRademacherLaw := by
  ext s hs
  rw [Measure.map_apply measurable_neg hs]
  by_cases h1 : (1 : ℤ) ∈ s
  · by_cases hm1 : (-1 : ℤ) ∈ s
    · simp [symmetricRademacherLaw, h1, hm1]
    · simp [symmetricRademacherLaw, h1, hm1]
  · by_cases hm1 : (-1 : ℤ) ∈ s
    · simp [symmetricRademacherLaw, h1, hm1]
    · simp [symmetricRademacherLaw, h1, hm1]

/-- Helper for Example 11.15: uniform integrability is preserved when the walk is centered by the
time-constant random offset `X 0`. -/
private lemma uniformIntegrable_centeredWalkReal
    (hUI : UniformIntegrable Xℝ 1 P) :
    UniformIntegrable (fun n ω ↦ ((X n ω - X 0 ω : ℤ) : ℝ)) 1 P := by
  let C : ℕ → Ω → ℝ := fun _ ω ↦ (X 0 ω : ℝ)
  have hconst : UniformIntegrable C 1 P := by
    refine uniformIntegrable_const le_rfl ?_ ?_
    · simp
    · simpa [C] using hUI.memLp 0
  -- Proof comment: subtract the time-constant family `C` from the original uniformly integrable
  -- walk.
  simpa [C, sub_eq_add_neg] using uniformIntegrable_sub hUI hconst

include hX_law

-- Proof sketch: subtract the initial position `X 0` to obtain the zero-start walk with the same
-- increments, rewrite that centered walk as partial sums of its increment process
-- `n ↦ X (n + 1) - X n`, apply Exercise 2.3.1 to those independent fair-sign increments, and
-- finally translate back by the finite initial offset.
/-- Almost surely, a symmetric simple random walk has `limsup X_n = +∞`. -/
theorem ae_limsup_symmetricSimpleRandomWalk_eq_top
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P, limsup (fun n ↦ X∞ n ω) atTop = ⊤ := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Δm : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  have hΔm_eq : ∀ n, Δ n =ᵐ[P] Δm n := by
    intro n
    simpa [Δ, Δm] using (hX_law n).aemeasurable.ae_eq_mk
  have hΔm_meas : ∀ n, Measurable (Δm n) := by
    intro n
    simpa [Δm] using (hX_law n).aemeasurable.measurable_mk
  have hΔm_indep : iIndepFun Δm P := hX_indep.congr hΔm_eq
  have hΔm_law : ∀ n, HasLaw (Δm n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hΔm_eq n).symm
  have hΔm_neg :
      ∀ n : ℕ, P (Set.preimage (Δm n) (Set.singleton (-1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact hasLaw_symmetricRademacher_preimage_negOne P (Δm n) (hΔm_law n)
  have hΔm_pos :
      ∀ n : ℕ, P (Set.preimage (Δm n) (Set.singleton (1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact hasLaw_symmetricRademacher_preimage_one P (Δm n) (hΔm_law n)
  have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Δm n ω := by
    simpa [Filter.EventuallyEq] using (ae_all_iff.2 hΔm_eq)
  filter_upwards
    [ae_infinite_partial_sum_ge_of_independent_fair_signs
      (μ := P) (X := Δm) hΔm_meas hΔm_indep hΔm_neg hΔm_pos,
      h_all] with ω hω hωeq
  -- Proof comment: translate infinitely many threshold crossings of the increment partial sums
  -- back to infinitely many crossings of the walk itself.
  rw [EReal.eq_top_iff_forall_lt]
  intro N
  let M : ℤ := Int.ceil N + 1
  have hM_freq :
      ∃ᶠ n in atTop, (((M : ℤ) : ℝ) : EReal) ≤ X∞ n ω := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (hω (M - X 0 ω)).mono ?_
    intro n hn
    have hsum :
        random_walk_partial_sum Δm n ω = random_walk_partial_sum Δ n ω := by
      unfold random_walk_partial_sum
      refine Finset.sum_congr rfl ?_
      intro j hj
      exact (hωeq j).symm
    have htel := randomWalkPartialSum_increments_eq_sub_initial (X := X) n ω
    have hInt : M ≤ X n ω := by
      have hEq : random_walk_partial_sum Δm n ω = X n ω - X 0 ω := by
        rw [hsum, htel]
      have hInt' : M ≤ X 0 ω + random_walk_partial_sum Δm n ω := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Δ] using hn
      rw [hEq] at hInt'
      omega
    change (((M : ℤ) : ℝ) : EReal) ≤ (((X n ω : ℤ) : ℝ) : EReal)
    exact_mod_cast hInt
  have hM_le :
      ((((M : ℤ) : ℝ) : EReal)) ≤ limsup (fun n ↦ X∞ n ω) atTop :=
    (le_limsup_iff').2 fun z hz ↦ hM_freq.mono fun n hn ↦ le_trans hz.le hn
  have hNM : (N : EReal) < ((((M : ℤ) : ℝ) : EReal)) := by
    have hNM_real : N < (M : ℝ) := by
      calc
        N ≤ (Int.ceil N : ℝ) := by exact_mod_cast Int.le_ceil N
        _ < (Int.ceil N : ℝ) + 1 := by linarith
        _ = (M : ℝ) := by
          dsimp [M]
          norm_num
    exact_mod_cast hNM_real
  exact hNM.trans_le hM_le

-- Proof sketch: apply the preceding `limsup` statement to the reflected walk `-X`, which is again
-- a symmetric simple random walk, and translate `limsup (-X_n) = +∞` into
-- `liminf X_n = -∞`.
/-- Almost surely, a symmetric simple random walk has `liminf X_n = -∞`. -/
theorem ae_liminf_symmetricSimpleRandomWalk_eq_bot
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P, liminf (fun n ↦ X∞ n ω) atTop = ⊥ := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Δm : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  have hΔm_eq : ∀ n, Δ n =ᵐ[P] Δm n := by
    intro n
    simpa [Δ, Δm] using (hX_law n).aemeasurable.ae_eq_mk
  have hΔm_meas : ∀ n, Measurable (Δm n) := by
    intro n
    simpa [Δm] using (hX_law n).aemeasurable.measurable_mk
  have hΔm_indep : iIndepFun Δm P := hX_indep.congr hΔm_eq
  have hΔm_law : ∀ n, HasLaw (Δm n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hΔm_eq n).symm
  have hΔm_neg :
      ∀ n : ℕ, P (Set.preimage (Δm n) (Set.singleton (-1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact hasLaw_symmetricRademacher_preimage_negOne P (Δm n) (hΔm_law n)
  have hΔm_pos :
      ∀ n : ℕ, P (Set.preimage (Δm n) (Set.singleton (1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    exact hasLaw_symmetricRademacher_preimage_one P (Δm n) (hΔm_law n)
  have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Δm n ω := by
    simpa [Filter.EventuallyEq] using (ae_all_iff.2 hΔm_eq)
  have hNegΔm_meas : ∀ n, Measurable (fun ω ↦ -Δm n ω) := by
    intro n
    exact measurable_neg.comp (hΔm_meas n)
  have hNegΔm_indep : iIndepFun (fun n ω ↦ -Δm n ω) P := by
    simpa using hΔm_indep.comp (fun _ z ↦ (-z : ℤ)) (fun _ ↦ measurable_neg)
  have hΔneg_neg : ∀ n : ℕ,
      P (Set.preimage (fun ω ↦ -Δm n ω) (Set.singleton (-1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    have hset :
        Set.preimage (fun ω ↦ -Δm n ω) (Set.singleton (-1 : ℤ)) =
          Set.preimage (Δm n) (Set.singleton (1 : ℤ)) := by
      ext ω
      change (-Δm n ω = (-1 : ℤ)) ↔ Δm n ω = (1 : ℤ)
      constructor <;> intro h <;> omega
    rw [hset]
    exact hΔm_pos n
  have hΔneg_pos : ∀ n : ℕ,
      P (Set.preimage (fun ω ↦ -Δm n ω) (Set.singleton (1 : ℤ))) = (2 : ℝ≥0∞)⁻¹ := by
    intro n
    have hset :
        Set.preimage (fun ω ↦ -Δm n ω) (Set.singleton (1 : ℤ)) =
          Set.preimage (Δm n) (Set.singleton (-1 : ℤ)) := by
      ext ω
      change (-Δm n ω = (1 : ℤ)) ↔ Δm n ω = (-1 : ℤ)
      constructor <;> intro h <;> omega
    rw [hset]
    exact hΔm_neg n
  filter_upwards
    [ae_infinite_partial_sum_ge_of_independent_fair_signs
      (μ := P) (X := fun n ω ↦ -Δm n ω)
      hNegΔm_meas hNegΔm_indep hΔneg_neg hΔneg_pos,
      h_all] with ω hω hωeq
  -- Proof comment: infinitely many large values of the negated increment walk force the original
  -- walk to visit arbitrarily negative levels.
  rw [EReal.eq_bot_iff_forall_lt]
  intro N
  let M : ℤ := Int.floor N - 1
  have hM_freq :
      ∃ᶠ n in atTop, X∞ n ω ≤ (((M : ℤ) : ℝ) : EReal) := by
    rw [Nat.frequently_atTop_iff_infinite]
    refine (hω (X 0 ω - M)).mono ?_
    intro n hn
    have hsum :
        random_walk_partial_sum (fun k ω' ↦ -Δm k ω') n ω =
          random_walk_partial_sum (fun k ω' ↦ -(Δ k ω')) n ω := by
      unfold random_walk_partial_sum
      refine Finset.sum_congr rfl ?_
      intro j hj
      simpa [Δ] using (congrArg Neg.neg (hωeq j)).symm
    have htel := randomWalkPartialSum_negIncrements_eq_initial_sub (X := X) n ω
    have hInt : X n ω ≤ M := by
      have hEq :
          random_walk_partial_sum (fun k ω' ↦ -Δm k ω') n ω = X 0 ω - X n ω := by
        rw [hsum, htel]
      have hInt' : X 0 ω ≤ M + random_walk_partial_sum (fun k ω' ↦ -Δm k ω') n ω := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Δ] using hn
      rw [hEq] at hInt'
      omega
    change (((X n ω : ℤ) : ℝ) : EReal) ≤ (((M : ℤ) : ℝ) : EReal)
    exact_mod_cast hInt
  have hM_le :
      liminf (fun n ↦ X∞ n ω) atTop ≤ (((M : ℤ) : ℝ) : EReal) :=
    (liminf_le_iff').2 fun y hy ↦ hM_freq.mono fun n hn ↦ le_trans hn hy.le
  have hMN : (((M : ℤ) : ℝ) : EReal) < (N : EReal) := by
    have hMN_real : (M : ℝ) < N := by
      have hfloor : (Int.floor N : ℝ) ≤ N := by
        exact_mod_cast Int.floor_le N
      calc
        (M : ℝ) = (Int.floor N : ℝ) - 1 := by
          dsimp [M]
          norm_num
        _ < Int.floor N := by linarith
        _ ≤ N := hfloor
    exact_mod_cast hMN_real
  exact lt_of_le_of_lt hM_le hMN

-- Proof sketch: combine the two preceding almost-sure oscillation statements on the same
-- full-measure event.
/-- Example 11.15: a symmetric simple random walk on `ℤ` oscillates almost surely between `+∞`
and `-∞`; equivalently, its pathwise `limsup` is `∞` and its `liminf` is `-∞`. -/
theorem symmetricSimpleRandomWalk_ae_limsup_eq_top_and_liminf_eq_bot
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ∀ᵐ ω ∂P,
      limsup (fun n ↦ X∞ n ω) atTop = ⊤ ∧ liminf (fun n ↦ X∞ n ω) atTop = ⊥ := by
  -- Proof comment: intersect the two full-measure oscillation events.
  filter_upwards
    [ae_limsup_symmetricSimpleRandomWalk_eq_top (P := P) (X := X) (hX_law := hX_law) hX_indep,
      ae_liminf_symmetricSimpleRandomWalk_eq_bot (P := P) (X := X) (hX_law := hX_law) hX_indep]
    with ω hsup hinf
  exact ⟨hsup, hinf⟩

-- Proof sketch: on any path with `limsup X_n = +∞` and `liminf X_n = -∞`, the sequence cannot
-- converge in `EReal`, even allowing the improper limits `±∞`.
/-- A symmetric simple random walk does not converge almost surely, even in the improper extended
real sense. -/
theorem symmetricSimpleRandomWalk_not_ae_improperly_convergent
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ¬ ∀ᵐ ω ∂P, ∃ ℓ : EReal,
        Tendsto (fun n ↦ X∞ n ω) atTop (𝓝 ℓ) := by
  letI : IsProbabilityMeasure P := (hX_law 0).isProbabilityMeasure
  intro hconv
  have hcontra : ∀ᵐ ω ∂P, False := by
    filter_upwards
      [symmetricSimpleRandomWalk_ae_limsup_eq_top_and_liminf_eq_bot
        (P := P) (X := X) (hX_law := hX_law) hX_indep, hconv] with ω hω hωconv
    rcases hωconv with ⟨ℓ, hℓ⟩
    have hsup : limsup (fun n ↦ X∞ n ω) atTop = ℓ := Filter.Tendsto.limsup_eq hℓ
    have hinf : liminf (fun n ↦ X∞ n ω) atTop = ℓ := Filter.Tendsto.liminf_eq hℓ
    have htop : (⊤ : EReal) = ℓ := by simpa [hω.1] using hsup
    have hbot : (⊥ : EReal) = ℓ := by simpa [hω.2] using hinf
    exact top_ne_bot (htop.trans hbot.symm)
  have hprob : P {ω | False} = 1 := (ae_iff_prob_eq_one (by simp)).1 hcontra
  simp at hprob

-- Proof sketch: if the walk were uniformly integrable, then its centered version
-- `n ↦ X n - X 0`, which has the same increments and starts at `0`, would also be uniformly
-- integrable. Apply Theorem 11.7 to the martingale from
-- `symmetricSimpleRandomWalk_squareIntegrable_martingale` for that centered walk to obtain
-- almost-sure convergence to an integrable limit, then translate back; this contradicts
-- `symmetricSimpleRandomWalk_not_ae_improperly_convergent`.
/-- A symmetric simple random walk on `ℤ`, viewed as a real-valued martingale, is not uniformly
integrable. -/
theorem symmetricSimpleRandomWalk_not_uniformIntegrable
    (hX_indep : iIndepFun (fun n ω ↦ X (n + 1) ω - X n ω) P) :
    ¬ UniformIntegrable Xℝ 1 P := by
  letI : IsFiniteMeasure P := (hX_law 0).isFiniteMeasure
  intro hUI
  let Δ : ℕ → Ω → ℤ := fun n ω ↦ X (n + 1) ω - X n ω
  let Δm : ℕ → Ω → ℤ := fun n ↦ (hX_law n).aemeasurable.mk (Δ n)
  let W : ℕ → Ω → ℤ := random_walk_partial_sum Δm
  let Wℝ : ℕ → Ω → ℝ := fun n ω ↦ (W n ω : ℝ)
  let hW_strMeas : ∀ n, StronglyMeasurable (Wℝ n) := fun n ↦
    Int.cast_continuous.comp_stronglyMeasurable
      ((measurable_random_walk_partial_sum Δm
        (fun k ↦ (hX_law k).aemeasurable.measurable_mk) n).stronglyMeasurable)
  let ℱW : Filtration ℕ ‹MeasurableSpace Ω› := Filtration.natural Wℝ hW_strMeas
  have hΔm_eq : ∀ n, Δ n =ᵐ[P] Δm n := by
    intro n
    simpa [Δ, Δm] using (hX_law n).aemeasurable.ae_eq_mk
  have hΔm_indep : iIndepFun Δm P := hX_indep.congr hΔm_eq
  have hΔm_law : ∀ n, HasLaw (Δm n) symmetricRademacherLaw P := by
    intro n
    exact (hX_law n).congr (hΔm_eq n).symm
  have hW_eq_centered_all : ∀ᵐ ω ∂P, ∀ n, W n ω = X n ω - X 0 ω := by
    have h_all : ∀ᵐ ω ∂P, ∀ n, Δ n ω = Δm n ω := by
      simpa [Filter.EventuallyEq] using (ae_all_iff.2 hΔm_eq)
    filter_upwards [h_all] with ω hω n
    calc
      W n ω = random_walk_partial_sum Δm n ω := by
        rfl
      _ = random_walk_partial_sum Δ n ω := by
        unfold random_walk_partial_sum
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact (hω j).symm
      _ = X n ω - X 0 ω := randomWalkPartialSum_increments_eq_sub_initial (X := X) n ω
  have hW_eq_centered : ∀ n, W n =ᵐ[P] fun ω ↦ X n ω - X 0 ω := by
    intro n
    filter_upwards [hW_eq_centered_all] with ω hω
    exact hω n
  have hW_UI : UniformIntegrable Wℝ 1 P := by
    have hcentered_UI :
        UniformIntegrable (fun n ω ↦ ((X n ω - X 0 ω : ℤ) : ℝ)) 1 P :=
      uniformIntegrable_centeredWalkReal (P := P) (X := X) hUI
    have hWℝ_eq_centered :
        ∀ n, Wℝ n =ᵐ[P] fun ω ↦ ((X n ω - X 0 ω : ℤ) : ℝ) := by
      intro n
      filter_upwards [hW_eq_centered n] with ω hω
      simpa [Wℝ] using congrArg (fun z : ℤ ↦ (z : ℝ)) hω
    exact (uniformIntegrable_congr_ae hWℝ_eq_centered).2 hcentered_UI
  have hW_zero : W 0 = 0 := by
    funext ω
    simp [W, random_walk_partial_sum]
  have hW_meas : ∀ n, Measurable (W n) := by
    intro n
    exact measurable_random_walk_partial_sum Δm
      (fun k ↦ (hX_law k).aemeasurable.measurable_mk) n
  have hW_indep : iIndepFun (fun n ω ↦ W (n + 1) ω - W n ω) P := by
    refine hΔm_indep.congr ?_
    intro n
    filter_upwards with ω
    simpa [W] using (random_walk_partial_sum_succ_sub Δm n ω).symm
  have hW_law : ∀ n, HasLaw (fun ω ↦ W (n + 1) ω - W n ω) symmetricRademacherLaw P := by
    intro n
    refine (hΔm_law n).congr ?_
    filter_upwards with ω
    simpa [W] using random_walk_partial_sum_succ_sub Δm n ω
  have hW_mart : Martingale Wℝ ℱW P := by
    simpa [Wℝ, ℱW, hW_strMeas] using
      (symmetricSimpleRandomWalk_squareIntegrable_martingale
        (P := P) (X := W) hW_zero hW_meas hW_indep hW_law).2
  have hW_tendsto :
      ∀ᵐ ω ∂P, Tendsto (fun n ↦ Wℝ n ω) atTop (𝓝 (ℱW.limitProcess Wℝ P ω)) := by
    -- Proof comment: the measurable centered walk is a uniformly integrable martingale, so the
    -- owner convergence theorem forces almost-sure convergence to its canonical limit process.
    simpa [ℱW] using
      hW_mart.submartingale.ae_tendsto_limitProcess_of_uniformIntegrable hW_UI
  have hX_tendsto :
      ∀ᵐ ω ∂P, ∃ ℓ : EReal, Tendsto (fun n ↦ X∞ n ω) atTop (𝓝 ℓ) := by
    filter_upwards [hW_tendsto, hW_eq_centered_all] with ω hω hωeq
    refine ⟨(((ℱW.limitProcess Wℝ P ω + (X 0 ω : ℝ)) : ℝ) : EReal), ?_⟩
    have hreal :
        Tendsto (fun n ↦ Wℝ n ω + (X 0 ω : ℝ)) atTop
          (𝓝 (ℱW.limitProcess Wℝ P ω + (X 0 ω : ℝ))) := by
      simpa using hω.add tendsto_const_nhds
    have hpoint : ∀ n, (X n ω : ℝ) = Wℝ n ω + (X 0 ω : ℝ) := by
      intro n
      have hEq : (W n ω : ℝ) = (X n ω : ℝ) - (X 0 ω : ℝ) := by
        exact_mod_cast hωeq n
      linarith
    have hXreal :
        Tendsto (fun n ↦ (X n ω : ℝ)) atTop
          (𝓝 (ℱW.limitProcess Wℝ P ω + (X 0 ω : ℝ))) := by
      -- Proof comment: adding back the time-constant offset recovers the original walk.
      refine Tendsto.congr' ?_ hreal
      filter_upwards with n
      simp [hpoint n]
    simpa using (EReal.tendsto_coe).2 hXreal
  exact
    symmetricSimpleRandomWalk_not_ae_improperly_convergent
      (P := P) (X := X) (hX_law := hX_law) hX_indep hX_tendsto

end SymmetricSimpleRandomWalk
