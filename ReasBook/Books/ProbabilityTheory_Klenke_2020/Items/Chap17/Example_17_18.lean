/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.MarkovProcessRealization
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 17.18: powers of a Markov kernel form the discrete-time Markov semigroup
of its iterated transition kernels. -/
instance isMarkovSemigroup_kernelPowers (κ₁ : Kernel ℤ ℤ) [IsMarkovKernel κ₁] :
    IsMarkovSemigroup (fun n : ℕ ↦ κ₁ ^ n) := by
  refine
    { isMarkovKernel := fun n ↦ ?_
      zero_eq := by rfl
      comp_eq := ?_ }
  · induction n with
    | zero =>
        simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel ℤ ℤ))
    | succ n ih =>
        simpa [pow_succ] using (inferInstance : IsMarkovKernel ((κ₁ ^ n) ∘ₖ κ₁))
  · intro s t
    calc
      (κ₁ ^ t) ∘ₖ (κ₁ ^ s) = κ₁ ^ (t + s) := by
        simpa using (Kernel.pow_add κ₁ t s).symm
      _ = κ₁ ^ (s + t) := by simp [Nat.add_comm]

omit [MeasurableSpace Ω] in
/-- Helper for Example 17.18: the present-state sigma-algebra is contained in the generated
history sigma-algebra at the same time. -/
lemma present_le_generatedFiltrationSpace
    (X : ℕ → Ω → ℤ) (s : ℕ) :
    MeasurableSpace.comap (X s) inferInstance ≤ generatedFiltrationSpace X s := by
  exact le_iSup₂_of_le s le_rfl le_rfl

/-- Helper for Example 17.18: the generated history filtration of a measurable process lives
inside the ambient measurable space. -/
lemma generatedFiltrationSpace_le_ambient
    (X : ℕ → Ω → ℤ) (hX : ∀ n : ℕ, Measurable (X n)) (s : ℕ) :
    generatedFiltrationSpace X s ≤ ‹MeasurableSpace Ω› := by
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  exact (hX r).comap_le

/-- Helper for Example 17.18: a finite history tuple is measurable once each sampled coordinate is
measurable. -/
lemma measurable_historyTuple {n : ℕ}
    (X : ℕ → Ω → ℤ) (times : Fin (n + 1) → ℕ)
    (hX : ∀ t : ℕ, Measurable (X t)) :
    Measurable (fun ω k ↦ X (times k) ω) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  exact hX (times k)

omit [MeasurableSpace Ω] in
/-- Helper for Example 17.18: a strictly increasing finite history tuple is measurable with
respect to the generated filtration at its terminal time. -/
lemma historyTuple_comap_le_generatedFiltrationSpace {n : ℕ}
    (X : ℕ → Ω → ℤ) (times : Fin (n + 1) → ℕ)
    (htimes : StrictMono times) :
    MeasurableSpace.comap (fun ω k ↦ X (times k) ω)
      (inferInstance : MeasurableSpace (Fin (n + 1) → ℤ)) ≤
      generatedFiltrationSpace X (times (Fin.last n)) := by
  let m : MeasurableSpace Ω := generatedFiltrationSpace X (times (Fin.last n))
  letI : MeasurableSpace Ω := m
  have h_meas :
      Measurable (fun ω k ↦ X (times k) ω) := by
    refine measurable_pi_iff.2 fun k ↦ ?_
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le (times k) <| le_iSup_of_le
      (htimes.monotone (Fin.le_last k)) le_rfl
  simpa [m] using h_meas.comap_le

omit [MeasurableSpace Ω] in
/-- Helper for Example 17.18: the generated history filtration of a discrete-time process is
monotone in the terminal time. -/
lemma generatedFiltrationSpace_monoNat
    (X : ℕ → Ω → ℤ) {m n : ℕ} (hmn : m ≤ n) :
    generatedFiltrationSpace X m ≤ generatedFiltrationSpace X n := by
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hmn) le_rfl

-- Proof sketch: unfold the recursive definition of `stochasticMatrixTrajectory`; at each step the
-- random map adds the current increment `Z n`, so induction on `n` identifies the trajectory with
-- the initial state plus the partial-sum process `randomWalkProcess Z`.
/-- The random mapping trajectory driven by `R_n(y) = y + Z_n` is the initial state plus the
partial sums of the increment sequence. -/
theorem stochasticMatrixTrajectory_add_eq_randomWalkProcess
    {Ω' : Type v} (Z : ℕ → Ω' → ℤ) (x : ℤ) :
    ∀ n : ℕ,
      stochasticMatrixTrajectory (fun k ω y ↦ y + Z k ω) x n =
        fun ω ↦ x + randomWalkProcess Z n ω := by
  intro n
  induction n with
  | zero =>
      -- At time `0`, both constructions are the constant path at the start state `x`.
      funext ω
      simp [stochasticMatrixTrajectory_zero, randomWalkProcess_apply]
  | succ n ih =>
      -- The recursive step adds the fresh increment `Z n` to the previous partial sum.
      funext ω
      rw [stochasticMatrixTrajectory_succ, ih]
      simp [randomWalkProcess_apply, Finset.sum_range_succ, add_left_comm, add_comm]

/-- Helper for Example 17.18: split the partial sums at time `s` into the past contribution and
the shifted future block. -/
lemma randomWalkProcess_splitAt
    {Ω' : Type v} (Z : ℕ → Ω' → ℤ) (s t : ℕ) (ω : Ω') :
    randomWalkProcess Z (s + t) ω =
      randomWalkProcess Z s ω +
        randomWalkProcess (fun k ω' ↦ Z (s + k) ω') t ω := by
  -- Proof comment: rewrite the long sum over `range (s + t)` as the prefix sum over `range s`
  -- plus the translated tail sum over `range t`.
  rw [randomWalkProcess_apply, randomWalkProcess_apply, randomWalkProcess_apply,
    Finset.sum_range_add]

/-- Helper for Example 17.18: the direct partial-sum tuple rewrites to the public
stochastic-matrix trajectory tuple. -/
lemma directRandomWalkTuple_map_eq_stochasticMatrixTrajectory
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ) (x : ℤ)
    {n : ℕ} (times : Fin (n + 1) → ℕ) :
    (Q : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) =
      (Q : Measure Ω').map
        (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) := by
  -- Proof comment: rewrite each coordinate of the tuple with the trajectory/partial-sum identity
  -- and then transport the measure by pointwise equality of the tuple maps.
  refine Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ ?_
  funext i
  simpa using (congrFun (stochasticMatrixTrajectory_add_eq_randomWalkProcess Z x (times i)) ω).symm

/-- Helper for Example 17.18: the auxiliary walk keeps the start state in the first coordinate
and adds the partial sums of the increment sequence from the second coordinate. -/
def productStartRandomWalk {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) :
    ℕ → (ℤ × Ω') → ℤ :=
  fun n s ↦ s.1 + randomWalkProcess (fun k t ↦ Z k t.2) n s

/-- Helper for Example 17.18: the auxiliary law starts deterministically from `x` and carries the
increment space in the second coordinate. -/
def productStartRandomWalkMeasure {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω')
    (x : ℤ) : ProbabilityMeasure (ℤ × Ω') :=
  ⟨(Measure.dirac x).prod (Q : Measure Ω'), inferInstance⟩

/-- Helper for Example 17.18: translating the origin row of a translation-invariant step matrix
gives the row at `y`. -/
lemma translatedStep_hasLaw_of_translationInvariantStepMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp : IsTranslationInvariantStepMatrix p)
    {Ω' : Type v} [MeasurableSpace Ω'] {μ : Measure Ω'} {W : Ω' → ℤ}
    (hW : HasLaw W (discreteMatrixKernel p 0) μ) (y : ℤ) :
    HasLaw (fun ω ↦ y + W ω) (discreteMatrixKernel p y) μ := by
  have htranslate :
      HasLaw (fun z : ℤ ↦ y + z) (discreteMatrixKernel p y) (discreteMatrixKernel p 0) := by
    refine ⟨by fun_prop, ?_⟩
    refine Measure.ext_of_singleton fun z ↦ ?_
    -- Proof comment: compare the translated origin row and the `y`-row on singleton atoms.
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)]
    have hpreimage : (fun w : ℤ ↦ y + w) ⁻¹' ({z} : Set ℤ) = {z - y} := by
      ext w
      constructor <;> intro hw <;> simp at hw ⊢ <;> omega
    rw [hpreimage]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton (z - y))]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton z)]
    rw [tsum_eq_single (z - y), tsum_eq_single z]
    · simp [hp y z]
    · intro b hb
      simp [Measure.smul_apply, Measure.dirac_apply', hb]
    · intro b hb
      simp [Measure.smul_apply, Measure.dirac_apply', hb]
  -- Proof comment: push the translated row law through the law of `W`.
  exact htranslate.fun_comp hW

/-- Helper for Example 17.18: the finite history tuple of the auxiliary walk up to time `s`. -/
def productStartRandomWalkHistoryTuple {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ)
    (s : ℕ) : (ℤ × Ω') → Fin (s + 1) → ℤ :=
  fun ω i ↦ productStartRandomWalk Z i ω

/-- Helper for Example 17.18: the finite history tuple of the random walk started from `x` and
driven directly on the increment space `Ω'`. -/
def startRandomWalkHistoryTuple {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (x : ℤ)
    (s : ℕ) : Ω' → Fin (s + 1) → ℤ :=
  fun ω i ↦ x + randomWalkProcess Z i ω

/-- Helper for Example 17.18: fixing the deterministic start `x` identifies the auxiliary-history
tuple on `ℤ × Ω'` with the direct random-walk history tuple on `Ω'`. -/
lemma productStartRandomWalkHistoryTuple_comp_prodMk
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (x : ℤ) (s : ℕ) :
    productStartRandomWalkHistoryTuple Z s ∘ (fun ω ↦ (x, ω)) =
      startRandomWalkHistoryTuple Z x s := by
  -- Proof comment: evaluating the auxiliary walk at `(x, ω)` removes the first coordinate and
  -- leaves the direct random-walk partial sums.
  funext ω
  funext i
  simp [productStartRandomWalkHistoryTuple, startRandomWalkHistoryTuple, productStartRandomWalk,
    randomWalkProcess_apply]

/-- Helper for Example 17.18: fixing the deterministic start `x` identifies the auxiliary walk at
time `n` with the direct random walk on the increment space. -/
lemma productStartRandomWalk_comp_prodMk
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (x : ℤ) (n : ℕ) :
    productStartRandomWalk Z n ∘ (fun ω ↦ (x, ω)) =
      fun ω ↦ x + randomWalkProcess Z n ω := by
  -- Proof comment: evaluating the auxiliary state at `(x, ω)` removes the deterministic first
  -- coordinate.
  funext ω
  simp [productStartRandomWalk, randomWalkProcess_apply]

/-- Helper for Example 17.18: at time `0` the auxiliary walk is just the first projection. -/
theorem productStartRandomWalk_zero
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) :
    productStartRandomWalk Z 0 = fun s ↦ s.1 := by
  -- Proof comment: the direct walk starts from the deterministic first coordinate before any
  -- increment is added.
  funext s
  simp [productStartRandomWalk, randomWalkProcess_apply]

/-- Helper for Example 17.18: one auxiliary step adds the fresh increment `Z n` to the current
auxiliary state. -/
lemma productStartRandomWalk_succ
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (n : ℕ) :
    productStartRandomWalk Z (n + 1) =
      fun s ↦ productStartRandomWalk Z n s + Z n s.2 := by
  -- Proof comment: split the next partial sum into the previous sum and the new last increment.
  funext s
  simp [productStartRandomWalk, randomWalkProcess_apply, Finset.sum_range_succ, add_left_comm,
    add_comm]

/-- Helper for Example 17.18: measurable increments give measurable auxiliary coordinates. -/
lemma measurable_productStartRandomWalk
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) :
    ∀ n : ℕ, Measurable (productStartRandomWalk Z n) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the time-zero auxiliary state is the measurable first projection.
      simpa [productStartRandomWalk_zero] using measurable_fst
  | succ n ih =>
      -- Proof comment: the recursive step is the sum of the previous state and the new
      -- increment pulled back along `Prod.snd`.
      rw [productStartRandomWalk_succ]
      exact ih.add ((hZ_meas n).comp measurable_snd)

/-- Helper for Example 17.18: the finite history tuple generates exactly the time-`s`
σ-algebra of the auxiliary walk. -/
lemma generatedFiltrationSpace_productStartRandomWalk_eq_historyTupleComap
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (s : ℕ) :
    generatedFiltrationSpace (productStartRandomWalk Z) s =
      MeasurableSpace.comap (productStartRandomWalkHistoryTuple Z s) inferInstance := by
  let times : Fin (s + 1) → ℕ := fun i ↦ i
  have htimes : StrictMono times := fun i j hij ↦ hij
  have hleft :
      MeasurableSpace.comap (productStartRandomWalkHistoryTuple Z s) inferInstance ≤
        generatedFiltrationSpace (productStartRandomWalk Z) s := by
    -- Proof comment: the history tuple is measurable with respect to the generated filtration
    -- because each sampled time is at most `s`.
    simpa [productStartRandomWalkHistoryTuple, times] using
      (_root_.historyTuple_comap_le_generatedFiltrationSpace
        (X := productStartRandomWalk Z) (times := times) htimes)
  have hright :
      generatedFiltrationSpace (productStartRandomWalk Z) s ≤
        MeasurableSpace.comap (productStartRandomWalkHistoryTuple Z s) inferInstance := by
    -- Proof comment: every generator `X t` with `t ≤ s` is recovered by evaluating the history
    -- tuple at the coordinate `⟨t, t < s + 1⟩`.
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (s + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (productStartRandomWalkHistoryTuple Z s) inferInstance]
          (fun ω ↦ productStartRandomWalkHistoryTuple Z s ω i) := by
      exact (measurable_pi_apply i).comp
        (comap_measurable (productStartRandomWalkHistoryTuple Z s))
    simpa [productStartRandomWalkHistoryTuple, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Example 17.18: the prefix increment tuple up to time `s` is independent of the
fresh increment `Z s`. -/
lemma prefixIncrementTuple_indep_increment
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (hZ_indep : iIndepFun Z (Q : Measure Ω')) (s : ℕ) :
    IndepFun (fun ω ↦ fun i : Fin s ↦ Z i ω) (Z s) (Q : Measure Ω') := by
  let prefixIdx : Finset ℕ := Finset.range s
  let prefixCoord : Ω' → prefixIdx → ℤ := fun ω i ↦ Z i ω
  let prefixToTuple : (prefixIdx → ℤ) → Fin s → ℤ := fun z i ↦
    z ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
  let singletonEval : (({s} : Finset ℕ) → ℤ) → ℤ := fun z ↦
    z ⟨s, Finset.mem_singleton_self s⟩
  have hPrefixToTuple : Measurable prefixToTuple := by
    -- Proof comment: reindex the `range s` block by coordinatewise evaluation on `Fin s`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : prefixIdx := ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
    simpa [prefixToTuple, idx] using
      (measurable_pi_apply idx : Measurable fun z : prefixIdx → ℤ ↦ z idx)
  have hSingletonEval : Measurable singletonEval := by
    -- Proof comment: the singleton block is just evaluation at its unique index `s`.
    let idx : ({s} : Finset ℕ) := ⟨s, Finset.mem_singleton_self s⟩
    simpa [singletonEval, idx] using
      (measurable_pi_apply idx : Measurable fun z : ({s} : Finset ℕ) → ℤ ↦ z idx)
  have hdisj : Disjoint prefixIdx ({s} : Finset ℕ) := by
    -- Proof comment: the fresh time `s` does not lie in the prefix index block `range s`.
    simp [prefixIdx]
  have hRaw :
      IndepFun prefixCoord (fun ω ↦ fun i : ({s} : Finset ℕ) ↦ Z i ω) (Q : Measure Ω') := by
    -- Proof comment: disjoint coordinate blocks of an independent family are independent.
    simpa [prefixCoord] using hZ_indep.indepFun_finset prefixIdx {s} hdisj hZ_meas
  have hTuple :
      IndepFun (prefixToTuple ∘ prefixCoord)
        (singletonEval ∘ fun ω ↦ fun i : ({s} : Finset ℕ) ↦ Z i ω)
        (Q : Measure Ω') := by
    -- Proof comment: compose the raw block independence with the deterministic reindexing maps.
    exact hRaw.comp hPrefixToTuple hSingletonEval
  simpa [Function.comp, prefixToTuple, prefixCoord, singletonEval] using hTuple

/-- Helper for Example 17.18: reconstruct the direct random-walk history from the prefix
increment tuple. -/
def prefixIncrementHistoryMap (x : ℤ) (s : ℕ) : (Fin s → ℤ) → Fin (s + 1) → ℤ :=
  fun u i ↦ x + ∑ j : Fin i, u ⟨(j : ℕ), lt_of_lt_of_le j.2 (Nat.le_of_lt_succ i.2)⟩

/-- Helper for Example 17.18: the history reconstruction map is measurable. -/
lemma measurable_prefixIncrementHistoryMap (x : ℤ) (s : ℕ) :
    Measurable (prefixIncrementHistoryMap x s) := by
  -- Proof comment: each history coordinate is integer-valued, hence measurable on the discrete
  -- state space.
  refine measurable_pi_lambda _ fun _ ↦ Measurable.of_discrete

/-- Helper for Example 17.18: the direct random-walk history tuple is reconstructed from the
prefix increment tuple by taking partial sums. -/
lemma startRandomWalkHistoryTuple_eq_prefixHistory_comp
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (x : ℤ) (s : ℕ) :
    startRandomWalkHistoryTuple Z x s =
      prefixIncrementHistoryMap x s ∘ (fun ω ↦ fun i : Fin s ↦ Z i ω) := by
  funext ω
  funext i
  -- Proof comment: each history coordinate is the start state plus the sum of the preceding
  -- increments, rewritten from `Finset.range i` to `Fin i`.
  rw [startRandomWalkHistoryTuple, Function.comp_apply, randomWalkProcess_apply,
    ← Fin.sum_univ_eq_sum_range]
  simp [prefixIncrementHistoryMap]

/-- Helper for Example 17.18: if the increments are measurable, then the direct random-walk
history tuple is measurable. -/
lemma measurableStartRandomWalkHistoryTuple
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) (s : ℕ) :
    Measurable (startRandomWalkHistoryTuple Z x s) := by
  rw [startRandomWalkHistoryTuple_eq_prefixHistory_comp (Z := Z) (x := x) (s := s)]
  refine (measurable_prefixIncrementHistoryMap x s).comp ?_
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact hZ_meas i

/-- Helper for Example 17.18: under the increment law `Q`, the direct random-walk history up to
time `s` depends only on the prefix increments and is independent of the fresh increment `Z s`. -/
lemma startRandomWalkHistoryTuple_indep_increment
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (x : ℤ) (s : ℕ) :
    IndepFun (startRandomWalkHistoryTuple Z x s) (Z s) (Q : Measure Ω') := by
  have hPrefix :
      IndepFun (fun ω ↦ fun i : Fin s ↦ Z i ω) (Z s) (Q : Measure Ω') :=
    prefixIncrementTuple_indep_increment Q Z hZ_meas hZ_indep s
  -- Route correction: factor the direct walk history through the prefix increment tuple and
  -- compose the block-independence statement once.
  rw [startRandomWalkHistoryTuple_eq_prefixHistory_comp (Z := Z) (x := x) (s := s)]
  simpa [Function.comp] using
    hPrefix.comp (measurable_prefixIncrementHistoryMap x s) measurable_id

/-- Helper for Example 17.18: the auxiliary walk is the stochastic-matrix trajectory driven by
`R_n(y) = y + Z_n`, started from the first coordinate. -/
lemma productStartRandomWalk_eq_stochasticMatrixTrajectory
    {Ω' : Type v} [MeasurableSpace Ω'] (Z : ℕ → Ω' → ℤ) (n : ℕ) :
    productStartRandomWalk Z n =
      fun s : ℤ × Ω' ↦
        stochasticMatrixTrajectory (fun k t y ↦ y + Z k t.2) s.1 n s := by
  -- Proof comment: specialize the trajectory/partial-sum identity to the product space
  -- `ℤ × Ω'`.
  funext s
  simpa [productStartRandomWalk] using
    congrFun
      (stochasticMatrixTrajectory_add_eq_randomWalkProcess (fun k (t : ℤ × Ω') ↦ Z k t.2) s.1 n)
      s |>.symm

/-- Helper for Example 17.18: under the product start law, the auxiliary walk starts from the
deterministic state `x`. -/
lemma productStartRandomWalk_initial
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ) (x : ℤ) :
    (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map (productStartRandomWalk Z 0) =
      Measure.dirac x := by
  -- Proof comment: at time `0` the auxiliary walk is `Prod.fst`, and the first marginal of
  -- `δ_x ⊗ Q` is `δ_x`.
  rw [productStartRandomWalk_zero]
  simp [productStartRandomWalkMeasure]

/-- Helper for Example 17.18: the auxiliary tuple law agrees with the stochastic-matrix
trajectory tuple under the increment law `Q`. -/
lemma productStartRandomWalk_map_eq_stochasticMatrixTrajectory
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) {n : ℕ}
    (times : Fin (n + 1) → ℕ) :
    (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
        (fun s i ↦ productStartRandomWalk Z (times i) s) =
      (Q : Measure Ω').map
        (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) := by
  have hMapMeas : Measurable (fun s i ↦ productStartRandomWalk Z (times i) s) := by
    -- Proof comment: coordinatewise measurability reduces the tuple map to the measurable
    -- auxiliary coordinates.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_productStartRandomWalk Z hZ_meas (times i)
  -- Proof comment: `δ_x ⊗ Q` is the pushforward of `Q` by `ω ↦ (x, ω)`, so the comparison is a
  -- pointwise rewrite of the auxiliary walk into the trajectory formula.
  calc
    (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
        (fun s i ↦ productStartRandomWalk Z (times i) s)
      = (Q : Measure Ω').map (fun ω i ↦ productStartRandomWalk Z (times i) (x, ω)) := by
          change Measure.map (fun s i ↦ productStartRandomWalk Z (times i) s)
            ((Measure.dirac x).prod (Q : Measure Ω')) =
              Measure.map (fun ω i ↦ productStartRandomWalk Z (times i) (x, ω)) (Q : Measure Ω')
          rw [Measure.dirac_prod]
          rw [Measure.map_map hMapMeas measurable_prodMk_left]
          refine Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ ?_
          rfl
    _ = (Q : Measure Ω').map
          (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) := by
            refine Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ ?_
            funext i
            calc
              productStartRandomWalk Z (times i) (x, ω) = x + randomWalkProcess Z (times i) ω := by
                simp [productStartRandomWalk, randomWalkProcess_apply]
              _ = stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω := by
                  simpa using congrFun
                    (stochasticMatrixTrajectory_add_eq_randomWalkProcess Z x (times i)) ω |>.symm

/-- Helper for Example 17.18: the auxiliary tuple law also agrees directly with the partial-sum
tuple under `Q`. -/
lemma productStartRandomWalk_map_eq_directRandomWalkTuple
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) {n : ℕ}
    (times : Fin (n + 1) → ℕ) :
    (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
        (fun s i ↦ productStartRandomWalk Z (times i) s) =
      (Q : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
  -- Proof comment: first rewrite the auxiliary tuple to the trajectory tuple, then collapse that
  -- tuple back to the direct partial-sum description.
  calc
    (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
        (fun s i ↦ productStartRandomWalk Z (times i) s)
      = (Q : Measure Ω').map
          (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) := by
            exact productStartRandomWalk_map_eq_stochasticMatrixTrajectory Q Z hZ_meas x times
    _ = (Q : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
          symm
          exact directRandomWalkTuple_map_eq_stochasticMatrixTrajectory Q Z x times

/-- Helper for Example 17.18: the history-dependent next-step kernel translates the origin row
by the last observed position in the history tuple. -/
def historyStepKernel (p : ℤ → ℤ → ℝ≥0∞) (s : ℕ) :
    Kernel (Fin (s + 1) → ℤ) ℤ :=
  ((Kernel.id : Kernel (Fin (s + 1) → ℤ) (Fin (s + 1) → ℤ)) ×ₖ
      Kernel.const (Fin (s + 1) → ℤ) (discreteMatrixKernel p 0)).map
    (fun z : (Fin (s + 1) → ℤ) × ℤ ↦ z.1 (Fin.last s) + z.2)

/-- Helper for Example 17.18: `historyStepKernel p s` is the pushforward of the origin row by
translation with the last history coordinate. -/
lemma historyStepKernel_apply
    (p : ℤ → ℤ → ℝ≥0∞) (s : ℕ) (h : Fin (s + 1) → ℤ) :
    historyStepKernel p s h =
      Measure.map (fun z : ℤ ↦ h (Fin.last s) + z) (discreteMatrixKernel p 0) := by
  -- Proof comment: unravel the kernel built from the identity row and the origin-step law.
  change
    (((Kernel.id : Kernel (Fin (s + 1) → ℤ) (Fin (s + 1) → ℤ)) ×ₖ
        Kernel.const (Fin (s + 1) → ℤ) (discreteMatrixKernel p 0)).map
        (fun z : (Fin (s + 1) → ℤ) × ℤ ↦ z.1 (Fin.last s) + z.2)) h =
      Measure.map (fun z : ℤ ↦ h (Fin.last s) + z) (discreteMatrixKernel p 0)
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left]
  rfl

/-- Helper for Example 17.18: translation invariance identifies the history-step kernel with the
transition row at the last observed state. -/
lemma historyStepKernel_row
    (p : ℤ → ℤ → ℝ≥0∞) (hp : IsTranslationInvariantStepMatrix p)
    (s : ℕ) (h : Fin (s + 1) → ℤ) :
    historyStepKernel p s h = discreteMatrixKernel p (h (Fin.last s)) := by
  have hid :
      HasLaw (fun z : ℤ ↦ z) (discreteMatrixKernel p 0) (discreteMatrixKernel p 0) := by
    refine ⟨by fun_prop, ?_⟩
    simp
  -- Proof comment: translation invariance moves the origin row to the row at the last history
  -- coordinate `h (Fin.last s)`.
  rw [historyStepKernel_apply p s h]
  simpa using
    (translatedStep_hasLaw_of_translationInvariantStepMatrix
      p hp (μ := discreteMatrixKernel p 0) (W := fun z : ℤ ↦ z) hid
      (h (Fin.last s))).map_eq

/-- Helper for Example 17.18: if a history statistic `H` is independent of the fresh increment
`U`, then the joint law of `(H, H(last) + U)` is the composition product with
`historyStepKernel p s`. -/
lemma historyNext_pairLaw_eq_compProd
    (p : ℤ → ℤ → ℝ≥0∞) {Ω' : Type v} [MeasurableSpace Ω'] (μ : Measure Ω')
    [IsFiniteMeasure μ] {s : ℕ} (H : Ω' → Fin (s + 1) → ℤ) (U : Ω' → ℤ)
    (hH_meas : Measurable H) (hU_meas : Measurable U)
    (hU_law : HasLaw U (discreteMatrixKernel p 0) μ)
    (hHU_indep : IndepFun H U μ) :
    μ.map (fun ω ↦ (H ω, H ω (Fin.last s) + U ω)) = μ.map H ⊗ₘ historyStepKernel p s := by
  let shiftPair : (Fin (s + 1) → ℤ) × ℤ → (Fin (s + 1) → ℤ) × ℤ :=
    fun z ↦ (z.1, z.1 (Fin.last s) + z.2)
  have hshiftPairMeas : Measurable shiftPair := by
    fun_prop
  have hHU_map :
      μ.map (fun ω ↦ (H ω, U ω)) = (μ.map H).prod (discreteMatrixKernel p 0) := by
    have hpair :=
      (indepFun_iff_map_prod_eq_prod_map_map
        (μ := μ) (f := H) (g := U) hH_meas.aemeasurable hU_meas.aemeasurable).mp hHU_indep
    simpa [hU_law.map_eq] using hpair
  let _ : IsSFiniteKernel (historyStepKernel p s) := by
    dsimp [historyStepKernel]
    infer_instance
  -- Proof comment: rewrite the next state as a deterministic map of `(H, U)` and then move the
  -- map through the composition-product normal form of the joint law.
  calc
    μ.map (fun ω ↦ (H ω, H ω (Fin.last s) + U ω))
        = (μ.map (fun ω ↦ (H ω, U ω))).map shiftPair := by
            rw [Measure.map_map hshiftPairMeas (hH_meas.prodMk hU_meas)]
            rfl
    _ = ((μ.map H).prod (discreteMatrixKernel p 0)).map shiftPair := by
          rw [hHU_map]
    _ = μ.map H ⊗ₘ historyStepKernel p s := by
          ext t ht
          rw [Measure.map_apply hshiftPairMeas ht, Measure.prod_apply (hshiftPairMeas ht),
            Measure.compProd_apply ht]
          refine lintegral_congr_ae <| Filter.Eventually.of_forall fun h ↦ ?_
          simpa [historyStepKernel_apply p s h, shiftPair] using
            (Measure.map_apply (μ := discreteMatrixKernel p 0)
              (f := fun z : ℤ ↦ h (Fin.last s) + z)
              (s := Prod.mk h ⁻¹' t) (by fun_prop)
              (measurableSet_preimage measurable_prodMk_left ht)).symm

/-- Helper for Example 17.18: conditioning the next direct random-walk state on the observed
history tuple gives the translated step-kernel row at the last observed position. -/
lemma startRandomWalk_condDistrib_historyTuple_eq_transitionKernel
    (p : ℤ → ℤ → ℝ≥0∞) (hp : IsTranslationInvariantStepMatrix p)
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω'))
    (x : ℤ) (s : ℕ) :
    condDistrib (fun ω ↦ x + randomWalkProcess Z (s + 1) ω)
        (startRandomWalkHistoryTuple Z x s) (Q : Measure Ω') =ᵐ[
          (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)]
      fun h ↦ discreteMatrixKernel p (h (Fin.last s)) := by
  let μ : Measure Ω' := (Q : Measure Ω')
  let H : Ω' → Fin (s + 1) → ℤ := startRandomWalkHistoryTuple Z x s
  let next : Ω' → ℤ := fun ω ↦ H ω (Fin.last s) + Z s ω
  have hH_meas : Measurable H := measurableStartRandomWalkHistoryTuple Z hZ_meas x s
  have hnext_meas : Measurable next := by
    -- Proof comment: `next` is the last history coordinate plus the fresh increment `Z s`.
    exact ((measurable_pi_apply (Fin.last s)).comp hH_meas).add (hZ_meas s)
  have hStepFinite : IsFiniteMeasure (discreteMatrixKernel p 0) := by
    rw [← (hZ_law 0).map_eq]
    infer_instance
  have h_indep :
      IndepFun H (Z s) μ :=
    startRandomWalkHistoryTuple_indep_increment Q Z hZ_meas hZ_indep x s
  have hpair :
      μ.map (fun ω ↦ (H ω, next ω)) = μ.map H ⊗ₘ historyStepKernel p s := by
    -- Proof comment: use the abstract pair-law helper instead of redoing the product-law
    -- computation inside the condDistrib theorem.
    simpa [μ, next] using
      historyNext_pairLaw_eq_compProd
        (p := p) (μ := μ) (H := H) (U := Z s) hH_meas (hZ_meas s) (hZ_law s) h_indep
  have hκFinite : IsFiniteKernel (historyStepKernel p s) := by
    refine ⟨(discreteMatrixKernel p 0) Set.univ, hStepFinite.measure_univ_lt_top, ?_⟩
    intro h
    rw [historyStepKernel_apply p s h, Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Set.preimage_univ]
  let _ : IsFiniteKernel (historyStepKernel p s) := hκFinite
  have hcond :
      condDistrib next H μ =ᵐ[μ.map H] historyStepKernel p s :=
    condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hH_meas hnext_meas hpair
  have hresult :
      condDistrib next H μ =ᵐ[μ.map H] fun h ↦ discreteMatrixKernel p (h (Fin.last s)) := by
    exact hcond.trans <| Filter.Eventually.of_forall fun h ↦ historyStepKernel_row p hp s h
  -- Proof comment: unfold `next` back to the explicit direct random-walk state at time `s + 1`.
  have hnext_eq :
      next = fun ω ↦ x + randomWalkProcess Z (s + 1) ω := by
    funext ω
    simp [next, H, startRandomWalkHistoryTuple, randomWalkProcess_apply, Finset.sum_range_succ,
      add_left_comm, add_comm]
  simpa [μ, H, hnext_eq] using hresult

/-- Helper for Example 17.18: the raw `condDistrib_map` step for the fixed-start embedding
`ω ↦ (x, ω)`. -/
private lemma productStartRandomWalkCondDistribMap
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) (s : ℕ) :
    condDistrib (productStartRandomWalk Z (s + 1)) (productStartRandomWalkHistoryTuple Z s)
        (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')) =ᵐ[
          (Q : Measure Ω').map ((productStartRandomWalkHistoryTuple Z s) ∘ fun ω ↦ (x, ω))]
      condDistrib ((productStartRandomWalk Z (s + 1)) ∘ fun ω ↦ (x, ω))
        ((productStartRandomWalkHistoryTuple Z s) ∘ fun ω ↦ (x, ω)) (Q : Measure Ω') := by
  let μ : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω'))
  let H : (ℤ × Ω') → Fin (s + 1) → ℤ := productStartRandomWalkHistoryTuple Z s
  let next : (ℤ × Ω') → ℤ := productStartRandomWalk Z (s + 1)
  let f : Ω' → ℤ × Ω' := fun ω ↦ (x, ω)
  have hμ_map : μ = (Q : Measure Ω').map f := by
    -- Proof comment: the auxiliary start law is the pushforward of `Q` by `ω ↦ (x, ω)`.
    change ((Measure.dirac x).prod (Q : Measure Ω')) = (Q : Measure Ω').map f
    rw [Measure.dirac_prod]
  have hH_meas : Measurable H := by
    let times : Fin (s + 1) → ℕ := fun i ↦ i
    -- Proof comment: the auxiliary history tuple is coordinatewise measurable.
    simpa [H, productStartRandomWalkHistoryTuple, times] using
      (_root_.measurable_historyTuple
        (X := productStartRandomWalk Z) (times := times)
        (hX := measurable_productStartRandomWalk Z hZ_meas))
  have hnext_meas : Measurable next := measurable_productStartRandomWalk Z hZ_meas (s + 1)
  have hmap :=
    condDistrib_map (X := H) (Y := next) (ν := (Q : Measure Ω')) (f := f)
      hH_meas.aemeasurable hnext_meas.aemeasurable measurable_prodMk_left.aemeasurable
  have hmap' :
      condDistrib next H μ =ᵐ[(Q : Measure Ω').map (H ∘ f)]
        condDistrib (next ∘ f) (H ∘ f) (Q : Measure Ω') := by
    simpa [hμ_map] using hmap
  simpa [μ, H, next] using hmap'

/-- Helper for Example 17.18: transporting the fixed-start embedding identifies the auxiliary and
direct conditional distributions. -/
private lemma productStartRandomWalkCondDistribTransport
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) (s : ℕ) :
    condDistrib (productStartRandomWalk Z (s + 1)) (productStartRandomWalkHistoryTuple Z s)
        (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')) =ᵐ[
          (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)]
      condDistrib (fun ω ↦ x + randomWalkProcess Z (s + 1) ω)
        (startRandomWalkHistoryTuple Z x s) (Q : Measure Ω') := by
  have hmap := productStartRandomWalkCondDistribMap Q Z hZ_meas x s
  have hH_comp :
      ((productStartRandomWalkHistoryTuple Z s) ∘ fun ω ↦ (x, ω)) =
        startRandomWalkHistoryTuple Z x s := by
    -- Proof comment: evaluating the auxiliary history at `(x, ω)` recovers the direct walk
    -- history started from `x`.
    simpa using productStartRandomWalkHistoryTuple_comp_prodMk Z x s
  have hnext_comp :
      ((productStartRandomWalk Z (s + 1)) ∘ fun ω ↦ (x, ω)) =
        fun ω ↦ x + randomWalkProcess Z (s + 1) ω := by
    -- Proof comment: evaluating the auxiliary next state at `(x, ω)` recovers the direct walk.
    simpa using productStartRandomWalk_comp_prodMk Z x (s + 1)
  -- Proof comment: after the raw transport step, only the fixed-start normal forms remain.
  simpa [hH_comp, hnext_comp] using hmap

/-- Helper for Example 17.18: the auxiliary-history pushforward under `δ_x ⊗ Q` agrees with the
direct history pushforward under `Q`. -/
private lemma productStartRandomWalkHistoryTuple_map_eq_startRandomWalkHistoryTuple_map
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (x : ℤ) (s : ℕ) :
    (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s) =
      (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
        (productStartRandomWalkHistoryTuple Z s) := by
  let μ : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω'))
  let H : (ℤ × Ω') → Fin (s + 1) → ℤ := productStartRandomWalkHistoryTuple Z s
  let f : Ω' → ℤ × Ω' := fun ω ↦ (x, ω)
  have hμ_map : μ = (Q : Measure Ω').map f := by
    -- Proof comment: the auxiliary start law is the pushforward of `Q` by the fixed-start map.
    change ((Measure.dirac x).prod (Q : Measure Ω')) = (Q : Measure Ω').map f
    rw [Measure.dirac_prod]
  have hH_meas : Measurable H := by
    let times : Fin (s + 1) → ℕ := fun i ↦ i
    -- Proof comment: record measurability once before using `Measure.map_map`.
    simpa [H, productStartRandomWalkHistoryTuple, times] using
      (_root_.measurable_historyTuple
        (X := productStartRandomWalk Z) (times := times)
        (hX := measurable_productStartRandomWalk Z hZ_meas))
  have hH_comp : H ∘ f = startRandomWalkHistoryTuple Z x s := by
    -- Proof comment: the fixed-start embedding identifies auxiliary and direct histories.
    simpa [H, f] using productStartRandomWalkHistoryTuple_comp_prodMk Z x s
  calc
    (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)
      = (Q : Measure Ω').map (H ∘ f) := by rw [← hH_comp]
    _ = ((Q : Measure Ω').map f).map H := by
          symm
          rw [Measure.map_map]
          · exact hH_meas
          · exact measurable_prodMk_left
    _ = μ.map H := by rw [hμ_map]
    _ = (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
          (productStartRandomWalkHistoryTuple Z s) := by
            simp [μ, H]

/-- Helper for Example 17.18: the auxiliary walk has the same history-tuple conditional law as
the direct walk started from `x`. -/
private lemma productStartRandomWalk_condDistrib_historyTuple_eq_transitionKernel
    (p : ℤ → ℤ → ℝ≥0∞) (hp : IsTranslationInvariantStepMatrix p)
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω'))
    (x : ℤ) (s : ℕ) :
    condDistrib (productStartRandomWalk Z (s + 1)) (productStartRandomWalkHistoryTuple Z s)
        (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')) =ᵐ[
          (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')).map
            (productStartRandomWalkHistoryTuple Z s)]
      fun h ↦ discreteMatrixKernel p (h (Fin.last s)) := by
  let μ : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω'))
  let H : (ℤ × Ω') → Fin (s + 1) → ℤ := productStartRandomWalkHistoryTuple Z s
  have htransport :
      condDistrib (productStartRandomWalk Z (s + 1)) (productStartRandomWalkHistoryTuple Z s)
          (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')) =ᵐ[
            (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)]
        condDistrib (fun ω ↦ x + randomWalkProcess Z (s + 1) ω)
          (startRandomWalkHistoryTuple Z x s) (Q : Measure Ω') :=
    productStartRandomWalkCondDistribTransport Q Z hZ_meas x s
  have hsource :
      condDistrib (fun ω ↦ x + randomWalkProcess Z (s + 1) ω)
          (startRandomWalkHistoryTuple Z x s) (Q : Measure Ω') =ᵐ[
            (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)]
        fun h ↦ discreteMatrixKernel p (h (Fin.last s)) :=
    startRandomWalk_condDistrib_historyTuple_eq_transitionKernel
      p hp Q Z hZ_meas hZ_indep hZ_law x s
  have hcond_aux :
      condDistrib (productStartRandomWalk Z (s + 1)) (productStartRandomWalkHistoryTuple Z s)
          (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω')) =ᵐ[
            (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s)]
        fun h ↦ discreteMatrixKernel p (h (Fin.last s)) :=
    htransport.trans hsource
  have hfilter :
      (Q : Measure Ω').map (startRandomWalkHistoryTuple Z x s) = μ.map H :=
    productStartRandomWalkHistoryTuple_map_eq_startRandomWalkHistoryTuple_map Q Z hZ_meas x s
  simpa [μ, H, hfilter] using hcond_aux

/-- Helper for Example 17.18: the missing owner-level step is the one-step conditional-law bridge
for the auxiliary walk under `δ_x ⊗ Q`. -/
lemma productStartRandomWalk_oneStepConditionalProb_eq_transitionKernel
    (p : ℤ → ℤ → ℝ≥0∞) (hp : IsTranslationInvariantStepMatrix p)
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n)) (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) :
    ∀ x : ℤ, ∀ ⦃A : Set ℤ⦄, MeasurableSet A → ∀ s : ℕ,
      (productStartRandomWalkMeasure Q x)⟦(productStartRandomWalk Z (s + 1)) ⁻¹' A |
          generatedFiltrationSpace (productStartRandomWalk Z) s⟧
        =ᵐ[(productStartRandomWalkMeasure Q x : Measure (ℤ × Ω'))]
          fun ω ↦ ((discreteMatrixKernel p) (productStartRandomWalk Z s ω)).real A := by
  intro x A hA s
  let μ : Measure (ℤ × Ω') := (productStartRandomWalkMeasure Q x : Measure (ℤ × Ω'))
  let H : (ℤ × Ω') → Fin (s + 1) → ℤ := productStartRandomWalkHistoryTuple Z s
  let next : (ℤ × Ω') → ℤ := productStartRandomWalk Z (s + 1)
  have hH_meas : Measurable H := by
    let times : Fin (s + 1) → ℕ := fun i ↦ i
    -- Proof comment: the history tuple is measurable because each auxiliary coordinate is.
    simpa [H, productStartRandomWalkHistoryTuple, times] using
      (_root_.measurable_historyTuple
        (X := productStartRandomWalk Z) (times := times)
        (hX := measurable_productStartRandomWalk Z hZ_meas))
  have hnext_meas : Measurable next := measurable_productStartRandomWalk Z hZ_meas (s + 1)
  have hcond :
      condDistrib next H μ =ᵐ[μ.map H]
        fun h ↦ discreteMatrixKernel p (h (Fin.last s)) := by
    -- Route correction: use the dedicated auxiliary-history conditional-law theorem instead of
    -- composing `condDistrib_map` transport and conditional-expectation conversion here.
    simpa [μ, H] using
      productStartRandomWalk_condDistrib_historyTuple_eq_transitionKernel
        p hp Q Z hZ_meas hZ_indep hZ_law x s
  have hcondexp :
      μ⟦next ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib next H μ (H ω)).real A := by
    -- Proof comment: identify the conditional probability with the conditional-distribution
    -- kernel evaluated at the history tuple.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := next)
        hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ω ↦ (condDistrib next H μ (H ω)).real A) =ᵐ[μ]
        fun ω ↦ ((discreteMatrixKernel p) (productStartRandomWalk Z s ω)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ω hω
    simpa [H, productStartRandomWalkHistoryTuple] using
      congrArg (fun ν : Measure ℤ ↦ ν.real A) hω
  rw [generatedFiltrationSpace_productStartRandomWalk_eq_historyTupleComap (Z := Z) (s := s)]
  exact hcondexp.trans hcond_comp

/-- Helper for Example 17.18: once the one-step kernel bridge is in place, the auxiliary walk is
an `IsMarkovProcessRealization` of the powers of `discreteMatrixKernel p`. -/
lemma productStartRandomWalk_isMarkovProcessRealization
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    {Ω' : Type v} [MeasurableSpace Ω'] (Q : ProbabilityMeasure Ω') (Z : ℕ → Ω' → ℤ)
    (hZ_meas : ∀ n : ℕ, Measurable (Z n))
    (hZ_indep : iIndepFun Z (Q : Measure Ω'))
    (hZ_law : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) :
    IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
      (productStartRandomWalkMeasure Q) (productStartRandomWalk Z) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp_stochastic
  -- Proof comment: the earlier one-step-kernel owner theorem packages the auxiliary walk once
  -- the deterministic start law and one-step conditional law are available.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := discreteMatrixKernel p)
    (P := productStartRandomWalkMeasure Q)
    (X := productStartRandomWalk Z)
    (hmeas := measurable_productStartRandomWalk Z hZ_meas)
    (hstart := ?_)
    (hstep := ?_)
  · intro x
    exact productStartRandomWalk_initial Q Z x
  · intro x A hA s
    exact productStartRandomWalk_oneStepConditionalProb_eq_transitionKernel
      p hp Q Z hZ_meas hZ_indep hZ_law x hA s

/-- Helper for Example 17.18: a translation-invariant chain has the same finite-dimensional laws
as a direct partial-sum walk with i.i.d. increments of law `p(0, ·)`. -/
theorem exists_directRandomWalkRepresentation_of_translationInvariantTransitionMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (x : ℤ)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ Q : ProbabilityMeasure Ω', ∃ Z : ℕ → Ω' → ℤ,
      iIndepFun Z (Q : Measure Ω') ∧
        (∀ n : ℕ,
          HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → ℕ), times 0 = 0 → StrictMono times →
          (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
            (Q : Measure Ω').map
              (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
  let _ : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel p hp_stochastic
  let _ : IsProbabilityMeasure (discreteMatrixKernel p 0) := inferInstance
  obtain ⟨Ω', hΩ', Q, Zlift, hZ_meas, hZ_law, hZ_indep, hQ_prob⟩ :=
    ProbabilityTheory.exists_iid (ULift ℕ) (discreteMatrixKernel p 0)
  let Qprob : ProbabilityMeasure Ω' := ⟨Q, hQ_prob⟩
  let Z : ℕ → Ω' → ℤ := fun n ω ↦ Zlift ⟨n⟩ ω
  have hZ_meas' : ∀ n : ℕ, Measurable (Z n) := by
    intro n
    simpa [Z] using hZ_meas ⟨n⟩
  have hZ_law_prob : ∀ n : ℕ, HasLaw (Z n) (discreteMatrixKernel p 0) (Qprob : Measure Ω') := by
    intro n
    simpa [Z, Qprob] using hZ_law ⟨n⟩
  have hZ_indep_prob : iIndepFun Z (Qprob : Measure Ω') := by
    simpa [Z, Qprob] using
      hZ_indep.precomp (g := fun n : ℕ ↦ (⟨n⟩ : ULift ℕ)) (by
        intro i j hij
        simpa using congrArg ULift.down hij)
  have hproductTuple :
      ∀ {n : ℕ} (times : Fin (n + 1) → ℕ),
        (productStartRandomWalkMeasure Qprob x : Measure (ℤ × Ω')).map
            (fun s i ↦ productStartRandomWalk Z (times i) s) =
          (Qprob : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
    intro n times
    exact productStartRandomWalk_map_eq_directRandomWalkTuple Qprob Z hZ_meas' x times
  refine ⟨Ω', hΩ', Qprob, Z, hZ_indep_prob, hZ_law_prob, ?_⟩
  intro n times htimes_zero htimes_mono
  have haux :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Z) :=
    productStartRandomWalk_isMarkovProcessRealization
      p hp_stochastic hp Qprob Z hZ_meas' hZ_indep_prob hZ_law_prob
  letI :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n)
        (productStartRandomWalkMeasure Qprob) (productStartRandomWalk Z) := haux
  -- Route correction: instead of rebuilding tuple uniqueness locally, compare the original chain
  -- with the auxiliary product-space realization via the earlier one-step-kernel owner theorem,
  -- then rewrite the auxiliary tuple to the direct partial-sum walk.
  calc
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω)
      = (productStartRandomWalkMeasure Qprob x : Measure (ℤ × Ω')).map
          (fun s i ↦ productStartRandomWalk Z (times i) s) := by
            simpa using
              (ProbabilityTheory.finiteDimensionalDistribution_eq_of_same_stochasticMatrix
                (p := p) (P := P) (Q := productStartRandomWalkMeasure Qprob)
                (X := X) (Y := productStartRandomWalk Z) x times htimes_zero htimes_mono)
    _ = (Qprob : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
          exact hproductTuple times

-- Proof sketch: realize the chain with transition matrix `p` through its owner abstraction
-- `IsMarkovProcessRealization`, sample i.i.d. increments with common law given by the row at the
-- origin, and drive the random maps `R_n(y) = y + Z_n`. The resulting trajectory has the same
-- transition semigroup as `X`, so the finite-dimensional distributions agree.
/-- Example 17.18: if a discrete-time Markov chain on `ℤ` has translation-invariant transition
matrix `p`, then for every starting state `x` it has the same finite-dimensional distributions as
the chain driven by i.i.d. increments with common law the row `p(0, ·)`, realized through the
random maps `R_n(y) = y + Z_n`. -/
theorem exists_randomMappingRepresentation_of_translationInvariantTransitionMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (x : ℤ)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ Q : ProbabilityMeasure Ω', ∃ Z : ℕ → Ω' → ℤ,
      iIndepFun Z (Q : Measure Ω') ∧
        (∀ n : ℕ,
          HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → ℕ), times 0 = 0 → StrictMono times →
          (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
            (Q : Measure Ω').map
              (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) :=
            by
  obtain ⟨Ω', hΩ', Q, Z, hZ_indep, hZ_law, hdirect⟩ :=
    exists_directRandomWalkRepresentation_of_translationInvariantTransitionMatrix
      p hp_stochastic hp P X x
  refine ⟨Ω', hΩ', Q, Z, hZ_indep, hZ_law, ?_⟩
  intro n times htimes_zero htimes_mono
  -- Proof comment: first use the direct partial-sum representation, then rewrite each coordinate
  -- into the public stochastic-matrix trajectory form.
  calc
    (P x : Measure Ω).map (fun ω i ↦ X (times i) ω)
      = (Q : Measure Ω').map (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
          exact hdirect (times := times) htimes_zero htimes_mono
    _ = (Q : Measure Ω').map
          (fun ω i ↦ stochasticMatrixTrajectory (fun k ω' y ↦ y + Z k ω') x (times i) ω) := by
          exact directRandomWalkTuple_map_eq_stochasticMatrixTrajectory Q Z x times

-- Proof sketch: apply
-- `exists_randomMappingRepresentation_of_translationInvariantTransitionMatrix` and rewrite the
-- random-mapping trajectory using
-- `stochasticMatrixTrajectory_add_eq_randomWalkProcess`.
/-- Equivalently, a chain with translation-invariant transition matrix has the same finite-
dimensional distributions as the partial-sum random walk `x + ∑_{i < n} Z_i` with i.i.d.
increments of law `p(0, ·)`. In Lean's `0`-based indexing, `randomWalkProcess Z n` is the
textbook sum `Z₁ + ⋯ + Zₙ`. -/
theorem isIntegerRandomWalk_of_translationInvariantTransitionMatrix
    (p : ℤ → ℤ → ℝ≥0∞) (hp_stochastic : IsStochasticMatrix p)
    (hp : IsTranslationInvariantStepMatrix p)
    (P : ℤ → ProbabilityMeasure Ω) (X : ℕ → Ω → ℤ) (x : ℤ)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    ∃ (Ω' : Type v), ∃ _ : MeasurableSpace Ω', ∃ Q : ProbabilityMeasure Ω', ∃ Z : ℕ → Ω' → ℤ,
      iIndepFun Z (Q : Measure Ω') ∧
        (∀ n : ℕ,
          HasLaw (Z n) (discreteMatrixKernel p 0) (Q : Measure Ω')) ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → ℕ), times 0 = 0 → StrictMono times →
          (P x : Measure Ω).map (fun ω i ↦ X (times i) ω) =
            (Q : Measure Ω').map
              (fun ω i ↦ x + randomWalkProcess Z (times i) ω) := by
  exact exists_directRandomWalkRepresentation_of_translationInvariantTransitionMatrix
    p hp_stochastic hp P X x
