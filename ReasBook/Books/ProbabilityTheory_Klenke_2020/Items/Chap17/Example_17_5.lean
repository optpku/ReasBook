/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_8

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d : ℕ}

/- Example 17.5 is `source-facing`: it identifies the path-space law of an i.i.d.-increment walk
and the Markov property of the canonical coordinate process under that law. The relevant
`core/canonical` owner in this chapter is `HasNaturalMarkovProperty` for the canonical process on
path space. The primitive data here is the random-walk path map and its pushforward law; the
natural filtration and coordinate measurability are derived from the owner abstraction, so the file
does not keep parallel wrapper lemmas for those pieces. -/

/-- The partial-sum path of the `ℝ^d`-valued increment sequence `Y`, started at the point `x`.
At time `n`, this path is `x + ∑_{i < n} Y_i`. -/
def randomWalkPath (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ) : Ω → ℕ → Fin d → ℝ :=
  fun ω n ↦ x + Finset.sum (Finset.range n) (fun i ↦ Y i ω)

/-- Helper for Example 17.5: the random-walk path evolves by adding the next increment. -/
theorem randomWalkPath_succ_apply (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (ω : Ω) (n : ℕ) :
    randomWalkPath x Y ω (n + 1) = randomWalkPath x Y ω n + Y n ω := by
  -- Expand the next partial sum and isolate the new increment at time `n`.
  simp [randomWalkPath, Finset.sum_range_succ, add_assoc]

/-- Helper for Example 17.5: every fixed time coordinate of the random-walk path is strongly
measurable when the increments are. -/
theorem stronglyMeasurable_randomWalkPath_apply
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) (n : ℕ) :
    StronglyMeasurable (fun ω ↦ randomWalkPath x Y ω n) := by
  -- The finite partial sum is strongly measurable coordinatewise, and adding the constant
  -- starting point preserves strong measurability.
  simpa [randomWalkPath] using
    (stronglyMeasurable_const.add
      (Finset.stronglyMeasurable_fun_sum (Finset.range n) fun i _ ↦ hY_meas i))

-- Proof sketch: use measurability of each increment coordinate `Y n`, then assemble the finite
-- partial sums coordinatewise and finally apply measurability into the product space on
-- `(ℕ → Fin d → ℝ)`.
/-- The partial-sum path map associated with a measurable increment sequence is almost everywhere
measurable as a random element of path space. -/
theorem aemeasurable_randomWalkPath (P : ProbabilityMeasure Ω)
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) :
    AEMeasurable (randomWalkPath x Y) P := by
  -- Check the path map coordinatewise and reassemble it in the product measurable space.
  refine aemeasurable_pi_lambda _ fun n ↦ ?_
  exact (stronglyMeasurable_randomWalkPath_apply x Y hY_meas n).aemeasurable

/-- The path-space law of the random walk with starting point `x`, obtained by pushing the
underlying probability measure forward along the partial-sum path map. -/
def randomWalkLaw (P : ProbabilityMeasure Ω)
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) : ProbabilityMeasure (ℕ → Fin d → ℝ) :=
  P.map (aemeasurable_randomWalkPath P x Y hY_meas)

/-- Helper for Example 17.5: restricting the random-walk law to the first `n + 1` coordinates is
the same as pushing `P` forward by the corresponding random-walk prefix map. -/
theorem randomWalkLaw_map_frestrictLe
    (P : ProbabilityMeasure Ω) (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) (n : ℕ) :
    ((randomWalkLaw P x Y hY_meas : Measure (ℕ → Fin d → ℝ)).map (Preorder.frestrictLe n)) =
      (P : Measure Ω).map (fun ω ↦ Preorder.frestrictLe n (randomWalkPath x Y ω)) := by
  -- Collapse the two successive pushforwards defining the prefix law into a single map from `Ω`.
  simpa [randomWalkLaw] using
    (AEMeasurable.map_map_of_aemeasurable (Preorder.measurable_frestrictLe n).aemeasurable
      (aemeasurable_randomWalkPath P x Y hY_meas) :
      Measure.map (Preorder.frestrictLe n)
          ((P : Measure Ω).map (randomWalkPath x Y)) =
        (P : Measure Ω).map (fun ω ↦ Preorder.frestrictLe n (randomWalkPath x Y ω)))

/-- Helper for Example 17.5: the time-`n` marginal of the path-space law is the law of the
time-`n` partial sum under the original probability space. -/
theorem randomWalkLaw_map_eval
    (P : ProbabilityMeasure Ω) (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) (n : ℕ) :
    ((randomWalkLaw P x Y hY_meas : Measure (ℕ → Fin d → ℝ)).map (Function.eval n)) =
      (P : Measure Ω).map (fun ω ↦ randomWalkPath x Y ω n) := by
  -- The time-`n` coordinate is the composition of the prefix-law map with the evaluation map.
  simpa [randomWalkLaw] using
    (AEMeasurable.map_map_of_aemeasurable (measurable_pi_apply n).aemeasurable
      (aemeasurable_randomWalkPath P x Y hY_meas) :
      Measure.map (Function.eval n)
          ((P : Measure Ω).map (randomWalkPath x Y)) =
        (P : Measure Ω).map (fun ω ↦ randomWalkPath x Y ω n))

/-- Helper for Example 17.5: the common law of the i.i.d. increment sequence. -/
def randomWalkStepLaw (P : ProbabilityMeasure Ω)
    (Y : ℕ → Ω → Fin d → ℝ) (hY_meas : ∀ n, StronglyMeasurable (Y n)) :
    ProbabilityMeasure (Fin d → ℝ) :=
  P.map ((hY_meas 0).aemeasurable)

/-- Helper for Example 17.5: every increment has the common step law. -/
theorem randomWalkIncrement_map_eq_stepLaw
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n))
    (hY_ident : ∀ n : ℕ, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω))
    (n : ℕ) :
    (P : Measure Ω).map (Y n) = (randomWalkStepLaw P Y hY_meas : Measure (Fin d → ℝ)) := by
  -- Transport the `n`th increment law to the common step law recorded at time `0`.
  simpa [randomWalkStepLaw] using (hY_ident n).map_eq

/-- Helper for Example 17.5: the one-step kernel adds an independent increment with the common
step law to the current position. -/
def randomWalkStepKernel (P : ProbabilityMeasure Ω)
    (Y : ℕ → Ω → Fin d → ℝ) (hY_meas : ∀ n, StronglyMeasurable (Y n)) :
    Kernel (Fin d → ℝ) (Fin d → ℝ) :=
  dirac_convolution_kernel (randomWalkStepLaw P Y hY_meas : Measure (Fin d → ℝ))

/-- Helper for Example 17.5: the one-step kernel at `z` is the translated common step law
`δ_z ∗ ν`. -/
theorem randomWalkStepKernel_apply
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n)) (z : Fin d → ℝ) :
    randomWalkStepKernel P Y hY_meas z =
      Measure.dirac z ∗ (randomWalkStepLaw P Y hY_meas : Measure (Fin d → ℝ)) := by
  -- Unfold the translated kernel and apply the convolution-kernel row formula.
  simpa [randomWalkStepKernel] using
    dirac_convolution_kernel_apply (randomWalkStepLaw P Y hY_meas : Measure (Fin d → ℝ)) z

/-- Helper for Example 17.5: the natural history σ-algebra of the canonical process up to time
`s` is exactly the σ-algebra generated by the finite prefix map `Preorder.frestrictLe s`. -/
private theorem generatedFiltrationSpace_eval_eq_frestrictLeComap (s : ℕ) :
    generatedFiltrationSpace
        (Function.eval : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ) s =
      MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance := by
  refine le_antisymm ?_ ?_
  · rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
    have hCoord :
        Measurable[
          MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance]
          (Function.eval t : (ℕ → Fin d → ℝ) → Fin d → ℝ) := by
      -- Proof comment: each generator `eval t` with `t ≤ s` is recovered by evaluating the
      -- prefix map at the index `⟨t, t ≤ s⟩`.
      simpa [Function.eval, Preorder.frestrictLe_apply, i] using
        (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe s))
    exact hCoord.comap_le
  · have hPrefix :
        Measurable[
          generatedFiltrationSpace
            (Function.eval : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ) s]
          (Preorder.frestrictLe s : (ℕ → Fin d → ℝ) → Finset.Iic s → Fin d → ℝ) := by
      -- Proof comment: every prefix coordinate is one of the canonical coordinates `eval t`
      -- with `t ≤ s`, so the full prefix map is measurable for the generated history.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
    exact hPrefix.comap_le

/-- Helper for Example 17.5: the tuple of increments before time `s` is independent of the fresh
increment `Y s`. -/
private theorem prefixIncrementTuple_indep_increment
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω)) (s : ℕ) :
    IndepFun (fun ω ↦ fun i : Fin s ↦ Y i ω) (Y s) (P : Measure Ω) := by
  let prefixIdx : Finset ℕ := Finset.range s
  let prefixCoord : Ω → prefixIdx → Fin d → ℝ := fun ω i ↦ Y i ω
  let prefixToTuple : (prefixIdx → Fin d → ℝ) → Fin s → Fin d → ℝ := fun z i ↦
    z ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
  let singletonEval : (({s} : Finset ℕ) → Fin d → ℝ) → Fin d → ℝ := fun z ↦
    z ⟨s, Finset.mem_singleton_self s⟩
  have hPrefixToTuple : Measurable prefixToTuple := by
    -- Proof comment: the `range s` block is reindexed to `Fin s` by coordinatewise evaluation.
    refine measurable_pi_lambda _ fun i ↦ ?_
    let idx : prefixIdx := ⟨(i : ℕ), by
      simp [prefixIdx, i.2]⟩
    simpa [prefixToTuple, idx] using
      (measurable_pi_apply idx :
        Measurable fun z : prefixIdx → Fin d → ℝ ↦ z idx)
  have hSingletonEval : Measurable singletonEval := by
    -- Proof comment: the singleton future block is just evaluation at its unique time `s`.
    let idx : ({s} : Finset ℕ) := ⟨s, Finset.mem_singleton_self s⟩
    simpa [singletonEval, idx] using
      (measurable_pi_apply idx :
        Measurable fun z : ({s} : Finset ℕ) → Fin d → ℝ ↦ z idx)
  have hdisj : Disjoint prefixIdx ({s} : Finset ℕ) := by
    -- Proof comment: the fresh time `s` does not belong to the prefix block `range s`.
    simpa [prefixIdx] using
      (Finset.disjoint_singleton_right.mpr
        (Finset.notMem_range_self : s ∉ Finset.range s))
  have hRaw :
      IndepFun prefixCoord (fun ω ↦ fun i : ({s} : Finset ℕ) ↦ Y i ω) (P : Measure Ω) := by
    -- Proof comment: independence of disjoint coordinate blocks is exactly
    -- `iIndepFun.indepFun_finset`.
    simpa [prefixCoord] using hY_indep.indepFun_finset prefixIdx {s} hdisj hY_meas
  have hTuple :
      IndepFun (prefixToTuple ∘ prefixCoord)
        (singletonEval ∘ fun ω ↦ fun i : ({s} : Finset ℕ) ↦ Y i ω)
        (P : Measure Ω) := by
    -- Proof comment: compose the raw block independence with the deterministic reindexing maps.
    exact hRaw.comp hPrefixToTuple hSingletonEval
  simpa [Function.comp, prefixToTuple, prefixCoord, singletonEval] using hTuple

/-- Helper for Example 17.5: reconstruct the walk prefix up to time `s` from the first `s`
increments. -/
private def prefixIncrementHistoryMap (x : Fin d → ℝ) (s : ℕ) :
    (Fin s → Fin d → ℝ) → Finset.Iic s → Fin d → ℝ :=
  fun u i ↦ x + ∑ j : Fin i.1, u ⟨(j : ℕ), lt_of_lt_of_le j.2 (Finset.mem_Iic.1 i.2)⟩

/-- Helper for Example 17.5: the prefix reconstruction map is measurable. -/
private theorem measurable_prefixIncrementHistoryMap (x : Fin d → ℝ) (s : ℕ) :
    Measurable (prefixIncrementHistoryMap x s) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  refine measurable_pi_lambda _ fun k ↦ ?_
  have hsum :
      Measurable
        (fun u : Fin s → Fin d → ℝ ↦
          ∑ j : Fin i.1, u ⟨(j : ℕ), lt_of_lt_of_le j.2 (Finset.mem_Iic.1 i.2)⟩ k) := by
    -- Proof comment: each coordinate is a finite sum of measurable projections from the prefix
    -- increment tuple.
    refine Finset.measurable_sum Finset.univ fun j _ ↦ ?_
    let idx : Fin s := ⟨(j : ℕ), lt_of_lt_of_le j.2 (Finset.mem_Iic.1 i.2)⟩
    exact (measurable_pi_apply k).comp (measurable_pi_apply idx)
  simpa [prefixIncrementHistoryMap] using measurable_const.add hsum

/-- Helper for Example 17.5: the random-walk prefix is obtained by applying the reconstruction map
to the prefix increment tuple. -/
private theorem randomWalkPrefix_eq_prefixHistory_comp
    (x : Fin d → ℝ) (Y : ℕ → Ω → Fin d → ℝ) (s : ℕ) :
    (fun ω ↦ Preorder.frestrictLe s (randomWalkPath x Y ω)) =
      prefixIncrementHistoryMap x s ∘ (fun ω ↦ fun i : Fin s ↦ Y i ω) := by
  funext ω
  funext i
  -- Proof comment: each prefix coordinate is the start point plus the sum of the preceding
  -- increments, rewritten from `Finset.range i` to `Fin i`.
  rw [Function.comp_apply, Preorder.frestrictLe_apply, randomWalkPath,
    ← Fin.sum_univ_eq_sum_range]
  simp [prefixIncrementHistoryMap]

/-- Helper for Example 17.5: the random-walk history up to time `s` depends only on the prefix
increments and is independent of the fresh increment `Y s`. -/
private theorem randomWalkPrefix_indep_increment
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, Measurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω))
    (x : Fin d → ℝ) (s : ℕ) :
    IndepFun (fun ω ↦ Preorder.frestrictLe s (randomWalkPath x Y ω)) (Y s) (P : Measure Ω) := by
  have hPrefix :
      IndepFun (fun ω ↦ fun i : Fin s ↦ Y i ω) (Y s) (P : Measure Ω) :=
    prefixIncrementTuple_indep_increment P Y hY_meas hY_indep s
  -- Route correction: factor the walk history through the prefix increment tuple and compose the
  -- block-independence statement through that deterministic reconstruction.
  rw [randomWalkPrefix_eq_prefixHistory_comp (x := x) (Y := Y) (s := s)]
  simpa [Function.comp] using
    hPrefix.comp (measurable_prefixIncrementHistoryMap x s) measurable_id

/-- Helper for Example 17.5: under the path law `randomWalkLaw P z Y hY_meas`, conditioning the
next coordinate on the history up to time `s` yields the translated step law at the present
state. -/
private theorem randomWalkLaw_oneStepConditionalProb_eq_stepKernel
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω))
    (hY_ident : ∀ n : ℕ, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω))
    (z : Fin d → ℝ) ⦃A : Set (Fin d → ℝ)⦄ (hA : MeasurableSet A) (s : ℕ) :
    (randomWalkLaw P z Y hY_meas : Measure (ℕ → Fin d → ℝ))⟦Function.eval (s + 1) ⁻¹' A |
        generatedFiltrationSpace Function.eval s⟧
      =ᵐ[(randomWalkLaw P z Y hY_meas : Measure (ℕ → Fin d → ℝ))]
        fun ξ ↦ ((randomWalkStepKernel P Y hY_meas) (ξ s)).real A := by
  let μ : Measure (ℕ → Fin d → ℝ) := (randomWalkLaw P z Y hY_meas : Measure (ℕ → Fin d → ℝ))
  let last : Finset.Iic s := ⟨s, Finset.mem_Iic.2 le_rfl⟩
  let H : (ℕ → Fin d → ℝ) → Finset.Iic s → Fin d → ℝ := Preorder.frestrictLe s
  let Hx : Ω → Finset.Iic s → Fin d → ℝ := fun ω ↦ Preorder.frestrictLe s (randomWalkPath z Y ω)
  let ν : Measure (Fin d → ℝ) := (randomWalkStepLaw P Y hY_meas : Measure (Fin d → ℝ))
  let κ : Kernel (Finset.Iic s → Fin d → ℝ) (Fin d → ℝ) :=
    ((Kernel.id : Kernel (Finset.Iic s → Fin d → ℝ) (Finset.Iic s → Fin d → ℝ)) ×ₖ
        Kernel.const (Finset.Iic s → Fin d → ℝ) ν).map
      (fun v : (Finset.Iic s → Fin d → ℝ) × (Fin d → ℝ) ↦ v.1 last + v.2)
  have hY_measurable : ∀ n, Measurable (Y n) := fun n ↦ (hY_meas n).measurable
  have hH_meas : Measurable H := Preorder.measurable_frestrictLe s
  have hnext_meas :
      Measurable (Function.eval (s + 1) : (ℕ → Fin d → ℝ) → Fin d → ℝ) :=
    measurable_pi_apply (s + 1)
  have hHx_meas : Measurable Hx := by
    change Measurable (fun ω ↦ Preorder.frestrictLe s (randomWalkPath z Y ω))
    rw [randomWalkPrefix_eq_prefixHistory_comp (x := z) (Y := Y) (s := s)]
    refine (measurable_prefixIncrementHistoryMap z s).comp ?_
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact hY_measurable i
  have hH_map : μ.map H = (P : Measure Ω).map Hx := by
    -- Proof comment: restricting the path law to the first `s + 1` coordinates is the same as
    -- restricting the underlying random-walk path map before pushing forward.
    simpa [μ, H, Hx] using randomWalkLaw_map_frestrictLe P z Y hY_meas s
  have hstep_map : (P : Measure Ω).map (Y s) = ν :=
    randomWalkIncrement_map_eq_stepLaw P Y hY_meas hY_ident s
  have hκ_apply :
      ∀ h : Finset.Iic s → Fin d → ℝ,
        κ h = Measure.map (fun u : Fin d → ℝ ↦ h last + u) ν := by
    intro h
    -- Proof comment: unpack the product kernel, keep the history fixed, and only translate the
    -- fresh step law by the last observed point of that history.
    change
      (((Kernel.id : Kernel (Finset.Iic s → Fin d → ℝ) (Finset.Iic s → Fin d → ℝ)) ×ₖ
          Kernel.const (Finset.Iic s → Fin d → ℝ) ν).map
          (fun v : (Finset.Iic s → Fin d → ℝ) × (Fin d → ℝ) ↦ v.1 last + v.2)) h =
        Measure.map (fun u : Fin d → ℝ ↦ h last + u) ν
    rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply]
    rw [Measure.dirac_prod, Measure.map_map (by fun_prop) measurable_prodMk_left]
    rfl
  have hκ_row :
      ∀ h : Finset.Iic s → Fin d → ℝ,
        κ h = randomWalkStepKernel P Y hY_meas (h last) := by
    intro h
    -- Proof comment: the auxiliary kernel row is exactly the translated common step law.
    calc
      κ h = Measure.map (fun u : Fin d → ℝ ↦ h last + u) ν := hκ_apply h
      _ = Measure.dirac (h last) ∗ ν := by
            simpa using (Measure.dirac_conv (h last) ν).symm
      _ = randomWalkStepKernel P Y hY_meas (h last) := by
            rw [randomWalkStepKernel_apply]
  have hHU_map_Ω :
      (P : Measure Ω).map (fun ω ↦ (Hx ω, Y s ω)) = ((P : Measure Ω).map Hx).prod ν := by
    have h_indep :
        IndepFun Hx (Y s) (P : Measure Ω) :=
      randomWalkPrefix_indep_increment P Y hY_measurable hY_indep z s
    have hpair :=
      (indepFun_iff_map_prod_eq_prod_map_map
        (μ := (P : Measure Ω)) (f := Hx) (g := Y s)
        hHx_meas.aemeasurable (hY_measurable s).aemeasurable).mp h_indep
    -- Proof comment: independence of the walk history and the fresh increment factors their
    -- joint law into the product of the prefix law and the common step law.
    simpa [hstep_map] using hpair
  have hpair :
      μ.map (fun ξ ↦ (H ξ, Function.eval (s + 1) ξ)) = μ.map H ⊗ₘ κ := by
    let shiftPair :
        (Finset.Iic s → Fin d → ℝ) × (Fin d → ℝ) →
          (Finset.Iic s → Fin d → ℝ) × (Fin d → ℝ) := fun v ↦
      (v.1, v.1 last + v.2)
    have hshiftPairMeas : Measurable shiftPair := by
      fun_prop
    have hcomp :
        ((μ.map H).prod ν).map shiftPair = μ.map H ⊗ₘ κ := by
      let _ : IsFiniteMeasure (μ.map H) := inferInstance
      let _ : IsFiniteMeasure ν := inferInstance
      let _ : IsFiniteMeasure ((μ.map H).prod ν) := by
        refine ⟨?_⟩
        rw [← Set.univ_prod_univ, Measure.prod_prod]
        exact
          ENNReal.mul_lt_top
            (IsFiniteMeasure.measure_univ_lt_top (μ := μ.map H))
            (IsFiniteMeasure.measure_univ_lt_top (μ := ν))
      let _ : IsFiniteMeasure (((μ.map H).prod ν).map shiftPair) := inferInstance
      refine Measure.ext_prod ?_
      intro hs t ht_hs ht_t
      have hshiftPairPre : MeasurableSet (shiftPair ⁻¹' (hs ×ˢ t)) := by
        exact hshiftPairMeas (ht_hs.prod ht_t)
      have hslice :
          (fun h : Finset.Iic s → Fin d → ℝ ↦
            ν (Prod.mk h ⁻¹' (shiftPair ⁻¹' (hs ×ˢ t)))) =
              hs.indicator (fun h ↦ κ h t) := by
        funext h
        by_cases hh : h ∈ hs
        · have hpre :
            Prod.mk h ⁻¹' (shiftPair ⁻¹' (hs ×ˢ t)) =
              (fun u : Fin d → ℝ ↦ h last + u) ⁻¹' t := by
            ext u
            simp [shiftPair, hh]
          rw [hpre, Set.indicator_of_mem hh, hκ_apply h, Measure.map_apply (by fun_prop) ht_t]
        · have hpre :
            Prod.mk h ⁻¹' (shiftPair ⁻¹' (hs ×ˢ t)) = ∅ := by
            ext u
            simp [shiftPair, hh]
          simp [hpre, Set.indicator, hh]
      rw [Measure.map_apply hshiftPairMeas (ht_hs.prod ht_t)]
      rw [Measure.compProd_apply_prod ht_hs ht_t]
      rw [Measure.prod_apply hshiftPairPre]
      rw [hslice, lintegral_indicator ht_hs]
    -- Proof comment: rewrite the next position as the last history coordinate plus the fresh
    -- increment, then transport the factored joint law from the increment space.
    calc
      μ.map (fun ξ ↦ (H ξ, Function.eval (s + 1) ξ))
          = (P : Measure Ω).map (fun ω ↦ (Hx ω, randomWalkPath z Y ω (s + 1))) := by
              simpa [μ, H, Hx, Function.comp] using
                (AEMeasurable.map_map_of_aemeasurable
                  ((hH_meas.prodMk hnext_meas).aemeasurable)
                  (aemeasurable_randomWalkPath P z Y hY_meas) :
                  Measure.map (fun ξ ↦ (H ξ, Function.eval (s + 1) ξ))
                    ((P : Measure Ω).map (randomWalkPath z Y)) =
                    (P : Measure Ω).map
                      (fun ω ↦
                        (H (randomWalkPath z Y ω),
                          Function.eval (s + 1) (randomWalkPath z Y ω))))
      _ = ((P : Measure Ω).map (fun ω ↦ (Hx ω, Y s ω))).map shiftPair := by
            rw [Measure.map_map hshiftPairMeas (hHx_meas.prodMk (hY_measurable s))]
            refine Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ ?_
            simp [shiftPair, Hx, last, randomWalkPath_succ_apply]
      _ = (((P : Measure Ω).map Hx).prod ν).map shiftPair := by
            rw [hHU_map_Ω]
      _ = μ.map H ⊗ₘ κ := by
            simpa [hH_map] using hcomp
  have hcond :
      condDistrib (Function.eval (s + 1)) H μ =ᵐ[μ.map H] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd H hnext_meas.aemeasurable hpair
  have hcondexp :
      μ⟦(Function.eval (s + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ]
        fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A := by
    -- Proof comment: identify the conditional probability with the conditional-distribution
    -- kernel evaluated at the observed prefix.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := H) (Y := Function.eval (s + 1))
        hH_meas hnext_meas hA).symm
  have hcond_comp :
      (fun ξ ↦ (condDistrib (Function.eval (s + 1)) H μ (H ξ)).real A) =ᵐ[μ]
        fun ξ ↦ (κ (H ξ)).real A := by
    filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
    simpa [Function.comp] using congrArg (fun ν' : Measure (Fin d → ℝ) ↦ ν'.real A) hξ
  rw [generatedFiltrationSpace_eval_eq_frestrictLeComap s]
  exact hcondexp.trans <|
    hcond_comp.trans <|
      Filter.Eventually.of_forall fun ξ ↦ by
        simpa [H, Preorder.frestrictLe_apply] using
          congrArg (fun ν' : Measure (Fin d → ℝ) ↦ ν'.real A) (hκ_row (H ξ))

/-- Helper for Example 17.5: the canonical process under the path-law family
`z ↦ randomWalkLaw P z Y hY_meas` realizes the powers of the translated one-step kernel. -/
private theorem canonicalProcess_isMarkovProcessRealization_randomWalkLaw
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω))
    (hY_ident : ∀ n : ℕ, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω)) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ randomWalkStepKernel P Y hY_meas ^ n)
      (fun z ↦ randomWalkLaw P z Y hY_meas)
      (Function.eval : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ) := by
  let _ : IsMarkovKernel (randomWalkStepKernel P Y hY_meas) := by
    refine ⟨?_⟩
    intro z
    rw [randomWalkStepKernel_apply]
    infer_instance
  -- Proof comment: Theorem 17.11 packages the canonical path law once the deterministic start
  -- law and the one-step conditional law have been identified.
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := randomWalkStepKernel P Y hY_meas)
    (P := fun z ↦ randomWalkLaw P z Y hY_meas)
    (X := Function.eval)
    (hmeas := measurable_pi_apply)
    (hstart := ?_)
    (hstep := ?_)
  · intro z
    calc
      ((randomWalkLaw P z Y hY_meas : Measure (ℕ → Fin d → ℝ)).map (Function.eval 0))
          = (P : Measure Ω).map (fun ω ↦ randomWalkPath z Y ω 0) := by
              simpa using randomWalkLaw_map_eval P z Y hY_meas 0
      _ = (P : Measure Ω).map (fun _ : Ω ↦ z) := by
            refine Measure.map_congr <| Filter.Eventually.of_forall fun ω ↦ ?_
            simp [randomWalkPath]
      _ = Measure.dirac z := by
            simpa using (Measure.map_const (P : Measure Ω) z)
  · intro z A hA s
    exact randomWalkLaw_oneStepConditionalProb_eq_stepKernel
      P Y hY_meas hY_indep hY_ident z hA s

-- Proof sketch: identify `randomWalkLaw P x Y hY_meas` with the pushforward law of the i.i.d.
-- increment sequence under the partial-sum map. Then verify the one-step transition law depends
-- only on the present coordinate, so the coordinate process satisfies the chapter owner
-- abstraction `HasNaturalMarkovProperty`.
/-- Example 17.5: if `Y` is an i.i.d. sequence of `ℝ^d`-valued random variables under `P`, then
for every starting point `x` the canonical process on path space, under the pushforward law
`randomWalkLaw P x Y hY_meas`, has the Markov property with respect to its natural filtration.
This is the random walk on `ℝ^d` with initial value `x`; in Lean indexing, the textbook increments
`Y₁, Y₂, ...` are encoded by `Y 0, Y 1, ...`. -/
theorem canonicalProcess_hasNaturalMarkovProperty_randomWalkLaw
    (P : ProbabilityMeasure Ω) (Y : ℕ → Ω → Fin d → ℝ)
    (hY_meas : ∀ n, StronglyMeasurable (Y n))
    (hY_indep : iIndepFun Y (P : Measure Ω))
    (hY_ident : ∀ n : ℕ, IdentDistrib (Y n) (Y 0) (P : Measure Ω) (P : Measure Ω))
    (x : Fin d → ℝ) :
    HasNaturalMarkovProperty
      (randomWalkLaw P x Y hY_meas : Measure (ℕ → Fin d → ℝ))
      (Function.eval : ℕ → (ℕ → Fin d → ℝ) → Fin d → ℝ) := by
  -- Route correction: instead of attacking the natural-filtration identity directly, first
  -- package the canonical path-law family as an owner-level realization of the one-step kernel.
  exact
    (canonicalProcess_isMarkovProcessRealization_randomWalkLaw
      P Y hY_meas hY_indep hY_ident).hasNaturalMarkovProperty x

end ProbabilityTheory
