/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_7

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

open scoped BigOperators

universe u v w

variable {Ω : Type u}

/-- The random walk on `ℤ` associated with the increment sequence `ξ`, realized as the partial-sum
process `S_n = ξ₀ + ⋯ + ξ_{n-1}`. -/
def randomWalkProcess (ξ : ℕ → Ω → ℤ) : ℕ → Ω → ℤ :=
  fun n ω ↦ Finset.sum (Finset.range n) fun i ↦ ξ i ω

/-- The order-`k` linear filter associated with the coefficients `c₀, …, c_k`. -/
def movingAverageProcess (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) : ℤ → Ω → ℝ :=
  fun n ω ↦ Finset.sum (Finset.range (k + 1)) fun i ↦ c i * X (n - i) ω

/-- Auxiliary path-space endomorphism for item (iii): its `n`-th coordinate is the
order-`k` linear filter with coefficients `c₀, …, c_k`. -/
def movingAveragePathTransform (c : ℕ → ℝ) (k : ℕ) : (ℤ → ℝ) → (ℤ → ℝ) :=
  fun x n ↦ Finset.sum (Finset.range (k + 1)) fun i ↦ c i * x (n - i)

/-- The textbook moving-average weights are nonnegative and normalized to have total mass `1`. -/
def IsMovingAverageWeights (c : ℕ → ℝ) (k : ℕ) : Prop :=
  (∀ i ∈ Finset.range (k + 1), 0 ≤ c i) ∧
    Finset.sum (Finset.range (k + 1)) c = 1

/-- `Y` is the moving average of `X` with weights `c₀, …, c_k` if it is the corresponding finite
linear filter and the weights are nonnegative with sum `1`. -/
def IsMovingAverageOf (Y X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) : Prop :=
  Y = movingAverageProcess X c k ∧ IsMovingAverageWeights c k

-- Proof sketch: unfold `randomWalkProcess`; it is exactly the finite partial sum of the increment
-- sequence over `Finset.range n`.
/-- The random-walk process is given by the finite partial sums of the increment sequence. -/
theorem randomWalkProcess_apply (ξ : ℕ → Ω → ℤ) (n : ℕ) (ω : Ω) :
    randomWalkProcess ξ n ω = Finset.sum (Finset.range n) fun i ↦ ξ i ω := rfl

-- Proof sketch: unfold `movingAverageProcess`; it is exactly the finite weighted sum from the
-- textbook formula `Y_n = ∑_{i=0}^k c_i X_{n-i}`.
/-- The moving-average process is given by the finite weighted sum from the textbook formula. -/
theorem movingAverageProcess_apply (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) (n : ℤ) (ω : Ω) :
    movingAverageProcess X c k n ω =
      Finset.sum (Finset.range (k + 1)) fun i ↦ c i * X (n - i) ω := rfl

-- Proof sketch: unfold `movingAveragePathTransform`; it is the same finite weighted sum as
-- `movingAverageProcess`, but applied to a deterministic path rather than to a random path.
/-- Auxiliary theorem for item (iii): evaluating the path transform at a path `x` gives the same
finite
weighted sum as `movingAverageProcess`. -/
theorem movingAveragePathTransform_apply (c : ℕ → ℝ) (k : ℕ) (x : ℤ → ℝ) (n : ℤ) :
    movingAveragePathTransform c k x n =
      Finset.sum (Finset.range (k + 1)) fun i ↦ c i * x (n - i) := rfl

-- Proof sketch: this is immediate from the definition of `IsMovingAverageOf`: when the weight
-- sequence is nonnegative and sums to `1`, the finite linear filter `movingAverageProcess X c k`
-- is precisely the textbook moving average of `X`.
/-- If `c₀, …, c_k ≥ 0` and `c₀ + ⋯ + c_k = 1`, then the finite linear filter
`Y_n = ∑_{i=0}^k c_i X_{n-i}` is the moving average of `X` with weights `c₀, …, c_k`. -/
theorem movingAverageProcess_isMovingAverageOf
    (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) (hweights : IsMovingAverageWeights c k) :
    IsMovingAverageOf (movingAverageProcess X c k) X c k :=
  ⟨rfl, hweights⟩

variable [MeasurableSpace Ω]
variable {T : Type v} [AddSemigroup T] {E : Type w} [Sub E] [MeasurableSpace E]

/-- A process has stationary increment laws if translating both endpoints of an increment by the
same amount does not change its law. This is the `E`-valued bridge layer for the Chapter 9 owner
`HasStationaryIncrements`, which is specialized to real-valued processes. -/
def HasStationaryIncrementLaws
    (X : T → Ω → E) (μ : Measure Ω := by volume_tac) : Prop :=
  ∀ r s t,
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ

namespace HasStationaryIncrementLaws

variable {X : T → Ω → E} {μ : Measure Ω}

/-- A process with stationary increment laws has the same increment distribution after common time
translation. -/
theorem identDistrib_increment (hX : HasStationaryIncrementLaws X μ) (r s t : T) :
    IdentDistrib
      (fun ω ↦ X ((s + t) + r) ω - X (t + r) ω)
      (fun ω ↦ X (s + r) ω - X r ω)
      μ μ :=
  hX r s t

end HasStationaryIncrementLaws

-- Proof sketch: the local `E`-valued bridge is definitionally the same three-time translation
-- invariant increment-law predicate as the Chapter 9 real-valued owner.
/-- On real-valued processes, `HasStationaryIncrementLaws` is exactly the Chapter 9 owner
`HasStationaryIncrements`. -/
theorem hasStationaryIncrementLaws_iff_hasStationaryIncrements
    (X : T → Ω → ℝ) (μ : Measure Ω := by volume_tac) :
    HasStationaryIncrementLaws X μ ↔ HasStationaryIncrements X μ :=
  Iff.rfl

/-- A process has stationary independent increments if it has both independent increments and
stationary increment laws. -/
def HasStationaryIndependentIncrements {T : Type v} [Preorder T] [AddSemigroup T]
    {E : Type w} [Sub E] [MeasurableSpace E] (X : T → Ω → E)
    (μ : Measure Ω := by volume_tac) : Prop :=
  HasIndepIncrements X μ ∧ HasStationaryIncrementLaws X μ

-- Proof sketch: split the partial sum at time `m + n` into the first `m` terms and the following
-- block of length `n`; subtracting the common prefix leaves exactly the translated block sum.
omit [MeasurableSpace Ω] in
/-- Auxiliary theorem for item (i): the increment of a random walk over a block of length `n` is
the sum
of the corresponding translated increment block. -/
theorem randomWalkProcess_blockIncrement
    (ξ : ℕ → Ω → ℤ) (m n : ℕ) (ω : Ω) :
    randomWalkProcess ξ (m + n) ω - randomWalkProcess ξ m ω =
      Finset.sum (Finset.range n) fun i ↦ ξ (m + i) ω := by
  -- Proof comment: expand the partial sum up to `m + n` and cancel the initial prefix of length
  -- `m`.
  rw [randomWalkProcess_apply, randomWalkProcess_apply, Finset.sum_range_add]
  simp

-- Proof sketch: package each adjacent block `Ico (t i) (t (i+1))` as a dependent coordinate
-- family, use the earlier disjoint-block independence theorem, then postcompose with the finite
-- block-sum map.
/-- Auxiliary theorem for item (i): sums of a measurable independent integer-valued family over
disjoint
adjacent blocks remain independent. -/
theorem iIndepFun_blockSums_of_iIndepFun
    (μ : Measure Ω) (ζ : ℕ → Ω → ℤ) (hζ_indep : iIndepFun ζ μ)
    (hζ_meas : ∀ n, Measurable (ζ n)) (t : ℕ → ℕ) (ht : Monotone t) :
    iIndepFun (fun i ω ↦ Finset.sum (Finset.Ico (t i) (t (i + 1))) fun j ↦ ζ j ω) μ := by
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
      iIndepFun (fun i ω (j : I i) ↦ ζ j ω) μ :=
    iIndepFun_block_of_pairwise_disjoint_blocks μ ζ I h_disjoint hζ_indep hζ_meas
  let blockSum := fun i (f : (j : I i) → ℤ) ↦
    Finset.sum (Finset.attach (Finset.Ico (t i) (t (i + 1)))) fun j ↦ f j
  have h_blockSum_meas : ∀ i, Measurable (blockSum i) := by
    intro i
    -- Proof comment: the block sum is a finite sum of measurable coordinate evaluations.
    refine Finset.measurable_sum _ ?_
    intro j hj
    exact measurable_pi_apply j
  have h_blockSum_indep :
      iIndepFun (fun i ω ↦ blockSum i (fun j : I i ↦ ζ j ω)) μ :=
    h_blocks.comp blockSum h_blockSum_meas
  -- Proof comment: identify the attached-subtype block sum with the usual `Ico`-indexed sum.
  refine h_blockSum_indep.congr ?_
  intro i
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa [blockSum] using
      (Finset.sum_attach (Finset.Ico (t i) (t (i + 1))) fun j ↦ ζ j ω)

-- Proof sketch: compare the two translated blocks as independent `Fin n`-indexed families with
-- matching coordinate laws, identify their joint laws by `IdentDistrib.pi`, and then postcompose
-- with the measurable finite-sum map.
/-- Auxiliary theorem for item (i): fixed-length translated block sums of an
i.i.d. integer-valued family have the same law. -/
theorem identDistrib_blockSum_of_iIndepFun_identDistrib
    (μ : Measure Ω) (ζ : ℕ → Ω → ℤ) (hζ_indep : iIndepFun ζ μ)
    (hζ_ident : ∀ m n : ℕ, IdentDistrib (ζ m) (ζ n) μ μ) (a b n : ℕ) :
    IdentDistrib
      (fun ω ↦ Finset.sum (Finset.range n) fun i ↦ ζ (a + i) ω)
      (fun ω ↦ Finset.sum (Finset.range n) fun i ↦ ζ (b + i) ω)
      μ μ := by
  -- Proof comment: compare the translated blocks as `Fin n`-indexed random vectors whose
  -- coordinates are i.i.d., then postcompose with the measurable finite-sum map.
  have hvec :
      IdentDistrib
        (fun ω ↦ fun i : Fin n ↦ ζ (a + i) ω)
        (fun ω ↦ fun i : Fin n ↦ ζ (b + i) ω)
        μ μ := by
    let ga : Fin n → ℕ := fun i ↦ a + i
    let gb : Fin n → ℕ := fun i ↦ b + i
    refine IdentDistrib.pi ?_ ?_ ?_
    · intro i
      exact hζ_ident (a + i) (b + i)
    · simpa [ga] using hζ_indep.precomp fun i j hij ↦ Fin.ext (Nat.add_left_cancel hij)
    · simpa [gb] using hζ_indep.precomp fun i j hij ↦ Fin.ext (Nat.add_left_cancel hij)
  let blockSum : (Fin n → ℤ) → ℤ := fun v ↦ ∑ i : Fin n, v i
  have h_blockSum_meas : Measurable blockSum := by
    -- Proof comment: finite sums of measurable coordinate projections are measurable.
    refine Finset.measurable_sum Finset.univ fun i _ ↦ ?_
    exact measurable_pi_apply i
  have hsum :
      IdentDistrib
        (blockSum ∘ fun ω ↦ fun i : Fin n ↦ ζ (a + i) ω)
        (blockSum ∘ fun ω ↦ fun i : Fin n ↦ ζ (b + i) ω)
        μ μ := by
    simpa [blockSum, Function.comp] using hvec.comp h_blockSum_meas
  have hleft :
      (blockSum ∘ fun ω ↦ fun i : Fin n ↦ ζ (a + i) ω) =
        fun ω ↦ Finset.sum (Finset.range n) fun i ↦ ζ (a + i) ω := by
    funext ω
    simpa [blockSum, Function.comp] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ζ (a + i) ω) n)
  have hright :
      (blockSum ∘ fun ω ↦ fun i : Fin n ↦ ζ (b + i) ω) =
        fun ω ↦ Finset.sum (Finset.range n) fun i ↦ ζ (b + i) ω := by
    funext ω
    simpa [blockSum, Function.comp] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ ζ (b + i) ω) n)
  -- Proof comment: rewrite the `Fin n` total sums back to `Finset.range n`.
  simpa [hleft, hright] using hsum

-- Proof sketch: the moving-average path transform is measurable coordinatewise, since each output
-- coordinate is a finite sum of measurable coordinate evaluations on the path space.
/-- Auxiliary theorem for item (iii): the moving-average path transform is measurable on path
space. -/
theorem measurable_movingAveragePathTransform (c : ℕ → ℝ) (k : ℕ) :
    Measurable (movingAveragePathTransform c k) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  -- Proof comment: the `n`-th output coordinate is a finite linear combination of evaluations of
  -- the input path.
  refine Finset.measurable_sum _ ?_
  intro i hi
  exact measurable_const.mul (measurable_pi_apply (n - i))

-- Proof sketch: shifting the input path and then applying the moving-average transform is the
-- same as first filtering the path and then shifting the output coordinates.
/-- Auxiliary theorem for item (iii): the moving-average path transform commutes with additive
shifts on
`ℤ`. -/
theorem movingAveragePathTransform_shift
    (c : ℕ → ℝ) (k : ℕ) (s : ℤ) (x : ℤ → ℝ) :
    movingAveragePathTransform c k (fun n ↦ x (s + n)) =
      fun n ↦ movingAveragePathTransform c k x (s + n) := by
  ext n
  -- Proof comment: each summand is evaluated at the same shifted coordinate after reassociating
  -- the integer subtraction.
  simp [movingAveragePathTransform, sub_eq_add_neg, add_assoc]

-- Proof sketch: apply the owner abstraction `IsPoissonProcess`; independence is one of its
-- fields, and the increment law depends only on the interval length `t - s`, so translating the
-- interval does not change the law.
/-- The Poisson process with intensity `θ` has stationary independent increments. -/
theorem hasStationaryIndependentIncrements_of_poissonProcess
    {μ : Measure Ω} {θ : NNReal} {N : NNReal → Ω → ℕ}
    (hN : IsPoissonProcess θ μ N) :
    HasStationaryIndependentIncrements N μ := by
  refine ⟨hN.indepIncrements, ?_⟩
  intro r s t
  -- Proof comment: both translated increments have the same Poisson law, because the interval
  -- length is `s` in each case.
  have h_left :
      HasLaw
        (fun ω ↦ N ((s + t) + r) ω - N (t + r) ω)
        (poissonMeasure (θ * s))
        μ := by
    have hlen : ((s + t) + r) - (t + r) = s := by
      calc
        ((s + t) + r) - (t + r) = (s + (t + r)) - (t + r) := by
          simp [add_left_comm, add_comm]
        _ = s := by simp
    have h' :
        HasLaw
          (fun ω ↦ N ((s + t) + r) ω - N (t + r) ω)
          (poissonMeasure (θ * (((s + t) + r) - (t + r))))
          μ :=
      hN.poisson_increment (show t + r ≤ (s + t) + r by simp [add_assoc])
    simpa [add_assoc, hlen] using h'
  have h_right :
      HasLaw
        (fun ω ↦ N (s + r) ω - N r ω)
        (poissonMeasure (θ * s))
        μ := by
    have hlen : (s + r) - r = s := by
      simp [add_comm]
    rw [← hlen]
    simpa [add_assoc, add_left_comm, add_comm] using
      hN.poisson_increment (show r ≤ s + r by simp)
  exact h_left.identDistrib h_right

-- Proof sketch: the increments of the partial-sum process over disjoint time intervals are sums
-- over disjoint blocks of the i.i.d. increment sequence, so they are independent and depend in
-- law only on the block length.
/-- The random walk on `ℤ`, realized as the partial-sum process of an i.i.d. integer-valued
increment sequence, has stationary independent increments. -/
theorem randomWalkProcess_hasStationaryIndependentIncrements
    (μ : Measure Ω) (ξ : ℕ → Ω → ℤ) (hξ_iid : IsIID ξ μ) :
    HasStationaryIndependentIncrements (randomWalkProcess ξ) μ := by
  let ξm : ℕ → Ω → ℤ := fun n ↦ ((hξ_iid.identDistrib n 0).aemeasurable_fst).mk (ξ n)
  have hξm_meas : ∀ n, Measurable (ξm n) := by
    intro n
    exact ((hξ_iid.identDistrib n 0).aemeasurable_fst).measurable_mk
  have hξm_ae : ∀ n, ξ n =ᵐ[μ] ξm n := by
    intro n
    exact ((hξ_iid.identDistrib n 0).aemeasurable_fst).ae_eq_mk
  have hξm_iid : IsIID ξm μ := by
    refine ⟨hξ_iid.iIndepFun.congr hξm_ae, ?_⟩
    intro i j
    refine
      (IdentDistrib.of_ae_eq ((hξ_iid.identDistrib i j).aemeasurable_fst) (hξm_ae i)).symm.trans ?_
    refine (hξ_iid.identDistrib i j).trans ?_
    exact IdentDistrib.of_ae_eq ((hξ_iid.identDistrib i j).aemeasurable_snd) (hξm_ae j)
  have h_all_eq : ∀ᵐ ω ∂μ, ∀ n, ξ n ω = ξm n ω := by
    simpa [Filter.EventuallyEq] using (ae_all_iff.2 hξm_ae)
  have hξm_indep : HasIndepIncrements (randomWalkProcess ξm) μ := by
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    have hblocks :=
      iIndepFun_blockSums_of_iIndepFun μ ξm hξm_iid.iIndepFun hξm_meas t ht
    have h_increment_eq :
        ∀ i ω,
          randomWalkProcess ξm (t (i + 1)) ω - randomWalkProcess ξm (t i) ω =
            Finset.sum (Finset.Ico (t i) (t (i + 1))) fun j ↦ ξm j ω := by
      intro i ω
      -- Proof comment: identify the walk increment with the corresponding translated `Ico` sum.
      simpa [randomWalkProcess_apply] using
        (Finset.sum_Ico_eq_sub (fun j ↦ ξm j ω) (ht (Nat.le_succ i))).symm
    exact hblocks.congr fun i ↦ Filter.Eventually.of_forall fun ω ↦ (h_increment_eq i ω).symm
  have h_partial_eq :
      ∀ n, randomWalkProcess ξm n =ᵐ[μ] randomWalkProcess ξ n := by
    intro n
    filter_upwards [h_all_eq] with ω hω
    rw [randomWalkProcess_apply, randomWalkProcess_apply]
    exact Finset.sum_congr rfl fun j _ ↦ (hω j).symm
  have hξ_indep : HasIndepIncrements (randomWalkProcess ξ) μ := by
    rw [hasIndepIncrements_iff_nat]
    intro t ht
    have hξm_nat :
        iIndepFun
          (fun i ω ↦ randomWalkProcess ξm (t (i + 1)) ω - randomWalkProcess ξm (t i) ω)
          μ :=
      (hasIndepIncrements_iff_nat.mp hξm_indep) t ht
    have h_increment_eq :
        ∀ i,
          (fun ω ↦ randomWalkProcess ξm (t (i + 1)) ω - randomWalkProcess ξm (t i) ω) =ᵐ[μ]
            (fun ω ↦ randomWalkProcess ξ (t (i + 1)) ω - randomWalkProcess ξ (t i) ω) := by
      intro i
      filter_upwards [h_partial_eq (t (i + 1)), h_partial_eq (t i)] with ω hω1 hω0
      simp [hω1, hω0]
    exact hξm_nat.congr h_increment_eq
  refine ⟨hξ_indep, ?_⟩
  intro r s t
  have hleft :
      (fun ω ↦ randomWalkProcess ξ ((s + t) + r) ω - randomWalkProcess ξ (t + r) ω) =
        fun ω ↦ Finset.sum (Finset.range s) fun i ↦ ξ ((t + r) + i) ω := by
    funext ω
    simpa [add_assoc, add_left_comm, add_comm] using randomWalkProcess_blockIncrement ξ (t + r) s ω
  have hright :
      (fun ω ↦ randomWalkProcess ξ (s + r) ω - randomWalkProcess ξ r ω) =
        fun ω ↦ Finset.sum (Finset.range s) fun i ↦ ξ (r + i) ω := by
    funext ω
    simpa [add_assoc, add_left_comm, add_comm] using randomWalkProcess_blockIncrement ξ r s ω
  have hsum :=
    identDistrib_blockSum_of_iIndepFun_identDistrib
      μ ξ hξ_iid.iIndepFun hξ_iid.identDistrib (t + r) r s
  -- Proof comment: both increment laws reduce to translated block sums of the i.i.d. steps.
  simpa [hleft, hright] using hsum

-- Verified recall from `lean_leansearch`: `ProbabilityTheory.IdentDistrib.pi` upgrades
-- coordinatewise i.i.d. shift laws to whole-path equality in distribution on countable index sets.
/-- Auxiliary finite-dimensional shift law for the i.i.d.-implies-stationary item:
every finite family of coordinates of an i.i.d. process has the same law as its additive shift. -/
private theorem identDistrib_restrict_shift_of_isIID
    {T : Type v} [AddLeftCancelSemigroup T] {E : Type w} [MeasurableSpace E]
    (μ : Measure Ω) (X : T → Ω → E) (hX_iid : IsIID X μ) (s : T) (I : Finset T) :
    IdentDistrib
      (fun ω ↦ I.restrict (fun t ↦ X (s + t) ω))
      (fun ω ↦ I.restrict (fun t ↦ X t ω))
      μ μ := by
  -- Proof comment: apply the product-law theorem on the finite subtype `I`, using the i.i.d.
  -- hypothesis for both the coordinate laws and the shifted-family independence.
  have hvec :
      IdentDistrib
        (fun ω ↦ fun j : I ↦ X (s + (j : T)) ω)
        (fun ω ↦ fun j : I ↦ X (j : T) ω)
        μ μ := by
    refine IdentDistrib.pi ?_ ?_ ?_
    · intro j
      exact hX_iid.identDistrib (s + (j : T)) (j : T)
    · simpa using
        hX_iid.iIndepFun.precomp (fun a b hab ↦ Subtype.ext (add_left_cancel hab))
    · simpa using hX_iid.iIndepFun.precomp (fun a b hab ↦ Subtype.ext hab)
  -- Proof comment: the coordinate functions on the subtype are exactly the finite restriction maps.
  simpa [Finset.restrict] using hvec

/-- On a countable additive index set, an i.i.d. process is stationary in the Chapter 9 owner
sense. -/
theorem example_9_8_isIID_isStationary
    {T : Type v} [AddLeftCancelSemigroup T] [Countable T]
    {E : Type w} [MeasurableSpace E]
    (μ : Measure Ω) (X : T → Ω → E) (hX_iid : IsIID X μ) :
    IsStationaryProcess X μ := by
  intro s
  -- Proof comment: compare the whole shifted path with the original path as countable products of
  -- i.i.d. coordinates.
  refine IdentDistrib.pi ?_ ?_ ?_
  · intro t
    exact hX_iid.identDistrib (s + t) t
  · simpa using hX_iid.iIndepFun.precomp (fun a b hab ↦ add_left_cancel hab)
  · exact hX_iid.iIndepFun

/-- Helper for Example 9.8: applying the path-space moving-average transform to a sample path
recovers the process-level moving-average coordinates. -/
private theorem movingAveragePathTransform_processEq
    (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ) (ω : Ω) :
    movingAveragePathTransform c k (fun n ↦ X n ω) =
      fun n ↦ movingAverageProcess X c k n ω := by
  -- Proof comment: both sides compute the same finite weighted sum at each output coordinate.
  ext n
  rw [movingAveragePathTransform_apply, movingAverageProcess_apply]

-- Proof sketch: a finite vector of moving-average coordinates is obtained from a finite vector of
-- coordinates of `X` by a fixed linear map depending only on the coefficients `c₀, …, c_k`; the
-- shift-invariance of the finite-dimensional laws of `X` is preserved by this map.
/-- Example 9.8: if `X` is a stationary real-valued process on `ℤ` and
`Y_n = ∑_{i=0}^k c_i X_{n-i}`, then `Y` is stationary. -/
theorem movingAverageProcess_isStationary
    (μ : Measure Ω) (X : ℤ → Ω → ℝ) (c : ℕ → ℝ) (k : ℕ)
    (hX_stationary : IsStationaryProcess X μ) :
    IsStationaryProcess (movingAverageProcess X c k) μ := by
  intro s
  -- Proof comment: transport the stationary path law of `X` through the measurable moving-average
  -- path transform before rewriting back to the process presentation.
  have hpath :
      IdentDistrib
        (fun ω ↦ movingAveragePathTransform c k (fun n ↦ X (s + n) ω))
        (fun ω ↦ movingAveragePathTransform c k (fun n ↦ X n ω))
        μ μ := by
    exact (hX_stationary s).comp (measurable_movingAveragePathTransform c k)
  have hleft :
      (fun ω ↦ movingAveragePathTransform c k (fun n ↦ X (s + n) ω)) =
        fun ω n ↦ movingAverageProcess X c k (s + n) ω := by
    funext ω
    ext n
    -- Proof comment: first commute the shift through the deterministic filter, then identify the
    -- filtered path with the stochastic-process version.
    have hshift :=
      congrFun (movingAveragePathTransform_shift c k s (fun m ↦ X m ω)) n
    have hprocess :=
      congrFun (movingAveragePathTransform_processEq X c k ω) (s + n)
    simpa using hshift.trans hprocess
  have hright :
      (fun ω ↦ movingAveragePathTransform c k (fun n ↦ X n ω)) =
        fun ω n ↦ movingAverageProcess X c k n ω := by
    funext ω
    exact movingAveragePathTransform_processEq X c k ω
  -- Proof comment: after the two normalization rewrites, the composed path law is exactly the
  -- stationarity statement for the moving-average process.
  simpa [hleft, hright] using hpath
