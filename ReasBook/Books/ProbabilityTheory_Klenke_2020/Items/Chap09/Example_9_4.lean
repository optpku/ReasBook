/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

noncomputable section

/-- The symmetric law on `ℤ` giving mass `1 / 2` to both `1` and `-1`. -/
def symmetricRademacherLaw : Measure ℤ :=
  ((1 / 2 : ℝ≥0∞) • Measure.dirac (1 : ℤ)) +
    ((1 / 2 : ℝ≥0∞) • Measure.dirac (-1 : ℤ))

-- Proof sketch: both summands are finite Dirac probability fragments with masses `1 / 2`, so the
-- total mass of `symmetricRademacherLaw` is `1`.
/-- The symmetric Rademacher law is a probability measure on `ℤ`. -/
theorem symmetricRademacherLaw_isProbabilityMeasure :
    IsProbabilityMeasure symmetricRademacherLaw := by
  -- Proof comment: evaluate the two scaled Dirac masses on `univ`.
  refine ⟨?_⟩
  have hmass : symmetricRademacherLaw Set.univ = (2 : ℝ≥0∞)⁻¹ + 2⁻¹ := by
    simp [symmetricRademacherLaw]
  rw [hmass, ENNReal.inv_two_add_inv_two]

instance : IsProbabilityMeasure symmetricRademacherLaw :=
  symmetricRademacherLaw_isProbabilityMeasure

variable {Ω : Type u} [MeasurableSpace Ω]

-- Route correction: this earlier item should not depend on the later broken `Example_9_8` file,
-- so we define the partial-sum walk locally and prove its basic identities here.
/-- Helper for Example 9.4: the partial-sum process associated with the increment sequence `Y`,
realizing the `0`-based walk `X_t = ∑_{n < t} Y_n`. -/
def randomWalkProcess (Y : ℕ → Ω → ℤ) : ℕ → Ω → ℤ :=
  fun n ω ↦ Finset.sum (Finset.range n) fun i ↦ Y i ω

/-- Helper for Example 9.4: evaluating `randomWalkProcess Y` at time `n` is exactly the finite
partial sum over `Finset.range n`. -/
theorem randomWalkProcess_apply (Y : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    randomWalkProcess Y n ω = Finset.sum (Finset.range n) fun i ↦ Y i ω := rfl

-- Proof sketch: evaluate the two Dirac masses on the singleton `{1}` and add the contributions.
/-- The symmetric Rademacher law assigns probability `1 / 2` to the step `1`. -/
theorem symmetricRademacherLaw_apply_singleton_one :
    symmetricRademacherLaw ({1} : Set ℤ) = 1 / 2 := by
  -- Proof comment: only the Dirac mass at `1` contributes on the singleton `{1}`.
  simp [symmetricRademacherLaw]

-- Proof sketch: the increment maps have the symmetric Rademacher law and therefore take values in
-- the discrete countable space `ℤ`; recursively write `X n` as a finite sum of those increments
-- starting from `X 0 = 0`, then compose with the coercion `ℤ → ℝ`.
/-- Helper for Example 9.4: the real-valued version of a symmetric simple random walk is
almost-everywhere strongly measurable at every time index. -/
theorem symmetricSimpleRandomWalk_real_stronglyMeasurable
    {P : Measure Ω} {X : ℕ → Ω → ℤ} (hX_zero : X 0 = 0)
    (hX_law : ∀ n, HasLaw (fun ω ↦ X (n + 1) ω - X n ω) symmetricRademacherLaw P) :
    ∀ n, AEStronglyMeasurable (fun ω ↦ (X n ω : ℝ)) P := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the initial position is the constant path at `0`.
      simpa [hX_zero] using
        (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω ↦ (0 : ℝ)) P)
  | succ n ih =>
      -- Proof comment: decompose `X (n + 1)` into its increment plus the previous position.
      have h_increment :
          AEStronglyMeasurable
            (fun ω ↦ ((X (n + 1) ω - X n ω : ℤ) : ℝ)) P := by
        exact
          Int.cast_continuous.comp_aestronglyMeasurable
            (hX_law n).aemeasurable.aestronglyMeasurable
      refine (h_increment.add ih).congr ?_
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa using congrArg (fun z : ℤ ↦ (z : ℝ)) (sub_add_cancel (X (n + 1) ω) (X n ω))

-- Proof sketch: unfold `randomWalkProcess` at time `0`; the sum over `Finset.range 0` is empty.
/-- The canonical random-walk process associated with `Y` starts at the origin. -/
theorem randomWalkProcess_zero (Y : ℕ → Ω → ℤ) :
    randomWalkProcess Y 0 = 0 := by
  ext ω
  -- Proof comment: the time-`0` partial sum is the empty sum.
  simp [randomWalkProcess_apply]

-- Proof sketch: compare the two consecutive partial sums; the `Finset.range (n + 1)` sum differs
-- from the `Finset.range n` sum by exactly the last term `Y n`.
/-- The one-step increment of the partial-sum walk is the original increment `Y n`. -/
theorem randomWalkProcess_increment (Y : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω = Y n ω := by
  -- Proof comment: expand the later partial sum by its last summand and cancel the common prefix.
  rw [randomWalkProcess_apply, randomWalkProcess_apply, Finset.sum_range_succ]
  simp

-- Proof sketch: use `HasIndepIncrements.of_nat` and the identity
-- `randomWalkProcess Y (t (i + 1)) - randomWalkProcess Y (t i)` as the sum over a disjoint block
-- of the independent increment sequence `Y`.
/-- If the increment sequence `Y` is independent, then its partial-sum walk has independent
increments. -/
theorem randomWalkProcess_hasIndepIncrements
    (P : Measure Ω) (Y : ℕ → Ω → ℤ) (hY_indep : iIndepFun Y P)
    (hY_aemeas : ∀ n, AEMeasurable (Y n) P) :
    HasIndepIncrements (randomWalkProcess Y) P := by
  let Ym : ℕ → Ω → ℤ := fun n ↦ (hY_aemeas n).mk (Y n)
  have hYm_eq : ∀ n, Y n =ᵐ[P] Ym n := by
    intro n
    simpa [Ym] using (hY_aemeas n).ae_eq_mk
  have hYm_meas : ∀ n, Measurable (Ym n) := by
    intro n
    simpa [Ym] using (hY_aemeas n).measurable_mk
  have hYm_indep : iIndepFun Ym P := by
    -- Proof comment: independence is stable under almost-everywhere replacement of coordinates.
    exact hY_indep.congr hYm_eq
  have h_all_eq : ∀ᵐ ω ∂P, ∀ n, Y n ω = Ym n ω := by
    -- Proof comment: we use one full-measure event on which every coordinate agrees with its
    -- measurable modification.
    simpa [Filter.EventuallyEq] using (ae_all_iff.2 hYm_eq)
  refine HasIndepIncrements.of_nat ?_
  intro t ht _
  let I : ℕ → Set ℕ := fun i ↦ (Finset.Ico (t i) (t (i + 1)) : Set ℕ)
  have h_disjoint : Pairwise fun i j ↦ Disjoint (I i) (I j) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · refine Set.disjoint_left.mpr ?_
      intro x hxI hxJ
      have hxI' : t i ≤ x ∧ x < t (i + 1) := by
        simpa [I] using hxI
      have hxJ' : t j ≤ x ∧ x < t (j + 1) := by
        simpa [I] using hxJ
      have hle : t (i + 1) ≤ t j := ht (Nat.succ_le_of_lt hij')
      exact not_lt_of_ge (le_trans hle hxJ'.1) hxI'.2
    · refine Set.disjoint_left.mpr ?_
      intro x hxI hxJ
      have hxI' : t i ≤ x ∧ x < t (i + 1) := by
        simpa [I] using hxI
      have hxJ' : t j ≤ x ∧ x < t (j + 1) := by
        simpa [I] using hxJ
      have hle : t (j + 1) ≤ t i := ht (Nat.succ_le_of_lt hij')
      exact not_lt_of_ge (le_trans hle hxI'.1) hxJ'.2
  have h_blocks :
      iIndepFun (fun i ω (j : I i) ↦ Ym j ω) P :=
    iIndepFun_block_of_pairwise_disjoint_blocks P Ym I h_disjoint hYm_indep hYm_meas
  let blockSum := fun i (f : (j : I i) → ℤ) =>
    Finset.sum (Finset.attach (Finset.Ico (t i) (t (i + 1)))) fun j ↦
      f j
  have h_blockSum_meas : ∀ i, Measurable (blockSum i) := by
    intro i
    -- Proof comment: the block sum is a finite sum of measurable coordinate evaluations.
    refine Finset.measurable_sum _ ?_
    intro j hj
    exact measurable_pi_apply j
  have h_blockSum_indep :
      iIndepFun (fun i ω ↦ blockSum i (fun j : I i ↦ Ym j ω)) P :=
    h_blocks.comp blockSum h_blockSum_meas
  have h_blockSum_eq :
      ∀ i ω,
        blockSum i (fun j : I i ↦ Ym j ω) =
          Finset.sum (Finset.Ico (t i) (t (i + 1))) (fun j ↦ Ym j ω) := by
    intro i ω
    -- Proof comment: summing over the attached block subtype is the same as summing over the
    -- underlying `Ico` index set.
    simpa [blockSum] using
      (Finset.sum_attach (s := Finset.Ico (t i) (t (i + 1))) (f := fun j ↦ Ym j ω))
  have h_incrementYm_eq :
      ∀ i ω,
        randomWalkProcess Ym (t (i + 1)) ω - randomWalkProcess Ym (t i) ω =
          blockSum i (fun j : I i ↦ Ym j ω) := by
    intro i ω
    -- Proof comment: the increment equals the sum over the disjoint block `Ico (t i) (t (i+1))`.
    rw [h_blockSum_eq]
    simpa [randomWalkProcess_apply] using
      (Finset.sum_Ico_eq_sub (fun j ↦ Ym j ω) (ht (Nat.le_succ i))).symm
  have hYm_increment_indep :
      iIndepFun
        (fun i ω ↦ randomWalkProcess Ym (t (i + 1)) ω - randomWalkProcess Ym (t i) ω) P := by
    -- Proof comment: transport independence from the block sums to the increment family of the
    -- measurable modification.
    exact h_blockSum_indep.congr fun i ↦ Filter.Eventually.of_forall fun ω ↦
      (h_incrementYm_eq i ω).symm
  have h_partial_eq :
      ∀ n, randomWalkProcess Ym n =ᵐ[P] randomWalkProcess Y n := by
    intro n
    filter_upwards [h_all_eq] with ω hω
    -- Proof comment: on the full-measure agreement set, the finite partial sums coincide termwise.
    rw [randomWalkProcess_apply, randomWalkProcess_apply]
    exact Finset.sum_congr rfl fun j _ ↦ (hω j).symm
  have h_increment_eq :
      ∀ i,
        (fun ω ↦ randomWalkProcess Ym (t (i + 1)) ω - randomWalkProcess Ym (t i) ω) =ᵐ[P]
          (fun ω ↦ randomWalkProcess Y (t (i + 1)) ω - randomWalkProcess Y (t i) ω) := by
    intro i
    filter_upwards [h_partial_eq (t (i + 1)), h_partial_eq (t i)] with ω hω1 hω0
    simp [hω1, hω0]
  -- Proof comment: the original walk has the same increments almost everywhere as the measurable
  -- modified walk, so the independence transfers back.
  exact hYm_increment_indep.congr h_increment_eq

-- Proof sketch: rewrite the one-step increment of `randomWalkProcess Y` as `Y n` and apply the
-- assumed law of `Y n`.
/-- If each `Y n` has the symmetric Rademacher law, then so does each one-step increment of the
partial-sum walk. -/
theorem randomWalkProcess_increment_hasLaw
    (P : Measure Ω) (Y : ℕ → Ω → ℤ)
    (hY_law : ∀ n, HasLaw (Y n) symmetricRademacherLaw P) (n : ℕ) :
    HasLaw (fun ω ↦ randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω)
      symmetricRademacherLaw P := by
  -- Proof comment: the increment map agrees pointwise with `Y n`.
  refine (hY_law n).congr ?_
  exact Filter.Eventually.of_forall fun ω ↦ randomWalkProcess_increment Y n ω

-- Proof sketch: apply the chapter owner theorem giving independent increments for
-- `randomWalkProcess Y`, then identify each one-step increment with `Y n`.
/-- Example 9.4: if the increments `Y_n` are independent and each has the symmetric Rademacher
law, then the random walk `randomWalkProcess Y` has the canonical independent-increments owner
property and the symmetric Rademacher one-step increment law. Together with
`randomWalkProcess_zero`, this is the canonical `0`-based Lean formulation of the textbook process
`X_t = ∑_{n=1}^t Y_n`. -/
theorem partial_sums_form_symmetric_simple_random_walk
    (P : Measure Ω) (Y : ℕ → Ω → ℤ)
    (hY_indep : iIndepFun Y P)
    (hY_law : ∀ n, HasLaw (Y n) symmetricRademacherLaw P) :
    HasIndepIncrements (randomWalkProcess Y) P ∧
      ∀ n,
        HasLaw (fun ω ↦ randomWalkProcess Y (n + 1) ω - randomWalkProcess Y n ω)
          symmetricRademacherLaw P := by
  constructor
  · -- Proof comment: the partial-sum process inherits independent increments from the blocks.
    exact randomWalkProcess_hasIndepIncrements P Y hY_indep fun n ↦ (hY_law n).aemeasurable
  · intro n
    -- Proof comment: each one-step increment has the same law as the corresponding step `Y n`.
    exact randomWalkProcess_increment_hasLaw P Y hY_law n
