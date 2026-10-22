/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Example_2_33
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_60

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

/- Exercise 17.7.2 (first claim): reflexivity is already the chapter stochastic-order owner from
Definition 17.57, specialized to the embedded nat-valued laws. -/
recall stochasticLE_refl

/-- Helper for Exercise 17.7.2: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite `poissonMeasure` as the measure attached to the corresponding Poisson
  -- PMF and then evaluate the singleton.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

/-- Helper for Exercise 17.7.2: the Poisson law with rate `r` assigns mass `exp (-r)` to `0`. -/
private lemma poissonMeasure_apply_zero_toReal (r : NNReal) :
    ((poissonMeasure r) ({0} : Set ℕ)).toReal = Real.exp (-(r : ℝ)) := by
  -- Proof comment: specialize the singleton formula at `0` and simplify the Poisson PMF.
  rw [poissonMeasure_apply_singleton, ENNReal.toReal_ofReal poissonPMFReal_nonneg]
  simp [poissonPMFReal]

/-- Helper for Exercise 17.7.2: for a probability measure on `ℕ`, the first upper tail is the
complement of the atom at `0`. -/
private lemma natMeasure_tail_Ici_one_toReal (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    (μ (Set.Ici 1)).toReal = 1 - (μ ({0} : Set ℕ)).toReal := by
  have hcompl : ((Set.Ici 1 : Set ℕ)ᶜ) = ({0} : Set ℕ) := by
    -- Proof comment: on `ℕ`, the only value below `1` is `0`.
    ext n
    simp
  have hTail : μ.real (Set.Ici 1) + μ.real ({0} : Set ℕ) = 1 := by
    -- Proof comment: rewrite the complement term to the singleton `{0}` and use total mass `1`.
    simpa [hcompl] using
      (show μ.real (Set.Ici 1) + μ.real ((Set.Ici 1 : Set ℕ)ᶜ) = μ.real Set.univ from
        MeasureTheory.measureReal_add_measureReal_compl measurableSet_Ici)
  have hTail' : μ.real (Set.Ici 1) = 1 - μ.real ({0} : Set ℕ) := by
    -- Proof comment: isolate the tail mass from the partition identity.
    linarith
  simpa [Measure.real_def] using hTail'

/-- Helper for Exercise 17.7.2: adding two independent Poisson counts corresponds to pushing the
product law forward by addition. -/
private lemma poissonMeasure_prod_map_add_eq (lam1 delta : NNReal) :
    Measure.map (fun z : ℕ × ℕ ↦ z.1 + z.2) ((poissonMeasure lam1).prod (poissonMeasure delta)) =
      poissonMeasure (lam1 + delta) := by
  -- Proof comment: additive convolution on `ℕ` is exactly this pushforward by the sum map.
  simpa [Measure.conv] using poissonMeasure_conv_poissonMeasure lam1 delta

/-- Helper for Exercise 17.7.2: increasing the Poisson parameter increases every upper tail. -/
private lemma poissonMeasure_upper_tail_mono {lam1 lam2 : NNReal} (h12 : lam1 ≤ lam2) (k : ℕ) :
    (poissonMeasure lam1) (Set.Ici k) ≤ (poissonMeasure lam2) (Set.Ici k) := by
  let delta : NNReal := lam2 - lam1
  have hsubset :
      (fun z : ℕ × ℕ ↦ z.1) ⁻¹' (Set.Ici k) ⊆
        (fun z : ℕ × ℕ ↦ z.1 + z.2) ⁻¹' (Set.Ici k) := by
    -- Proof comment: adding a nonnegative second coordinate can only increase the sum.
    intro z hz
    simpa [Set.mem_preimage, Set.mem_Ici] using Nat.le_trans hz (Nat.le_add_right z.1 z.2)
  calc
    (poissonMeasure lam1) (Set.Ici k)
        = Measure.map (fun z : ℕ × ℕ ↦ z.1) ((poissonMeasure lam1).prod (poissonMeasure delta))
            (Set.Ici k) := by
              letI : IsProbabilityMeasure (poissonMeasure delta) := inferInstance
              -- Proof comment: the first projection preserves the first marginal of the product.
              rw [(measurePreserving_fst
                (μ := poissonMeasure lam1)
                (ν := poissonMeasure delta)).map_eq]
    _ ≤ Measure.map (fun z : ℕ × ℕ ↦ z.1 + z.2)
          ((poissonMeasure lam1).prod (poissonMeasure delta)) (Set.Ici k) := by
            rw [Measure.map_apply measurable_fst measurableSet_Ici]
            rw [Measure.map_apply (measurable_fst.add measurable_snd) measurableSet_Ici]
            exact measure_mono hsubset
    _ = (poissonMeasure (lam1 + delta)) (Set.Ici k) := by
          rw [poissonMeasure_prod_map_add_eq]
    _ = (poissonMeasure lam2) (Set.Ici k) := by
          rw [show lam1 + delta = lam2 by
            simpa [delta] using (add_tsub_cancel_of_le h12 : lam1 + (lam2 - lam1) = lam2)]

-- Proof sketch: for the forward implication, test the stochastic order with increasing tail or
-- truncated identity functions to recover `λ₁ ≤ λ₂`; for the reverse implication, couple
-- `Poi_{λ₂}` as `Poi_{λ₁} + Poi_{λ₂ - λ₁}` when `λ₁ ≤ λ₂`.
/-- Exercise 17.7.2: the Poisson law with parameter `λ₁` is below the Poisson law with parameter
`λ₂` in the discrete stochastic order on `ℕ` if and only if `λ₁ ≤ λ₂`. -/
theorem poissonMeasure_stochasticLE_iff (lam1 lam2 : NNReal) :
    StochasticLE
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam1, inferInstance⟩ : ProbabilityMeasure ℕ))
      (ProbabilityMeasure.toFin1Real
        (⟨poissonMeasure lam2, inferInstance⟩ : ProbabilityMeasure ℕ)) ↔
      lam1 ≤ lam2 := by
  constructor
  · intro hst
    -- Proof comment: test the stochastic order at the first nontrivial upper tail `Set.Ici 1`.
    have htail :
        (poissonMeasure lam1) (Set.Ici 1) ≤ (poissonMeasure lam2) (Set.Ici 1) :=
      ProbabilityTheory.StochasticLE.upper_tail_nat
        (μ₁ := (⟨poissonMeasure lam1, inferInstance⟩ : ProbabilityMeasure ℕ))
        (μ₂ := (⟨poissonMeasure lam2, inferInstance⟩ : ProbabilityMeasure ℕ))
        hst 1
    have htail_real :
        ((poissonMeasure lam1) (Set.Ici 1)).toReal ≤
          ((poissonMeasure lam2) (Set.Ici 1)).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top (poissonMeasure lam2) _) htail
    rw [natMeasure_tail_Ici_one_toReal, natMeasure_tail_Ici_one_toReal,
      poissonMeasure_apply_zero_toReal, poissonMeasure_apply_zero_toReal] at htail_real
    have hexp :
        Real.exp (-((lam2 : NNReal) : ℝ)) ≤ Real.exp (-((lam1 : NNReal) : ℝ)) := by
      linarith
    have hneg : -((lam2 : NNReal) : ℝ) ≤ -((lam1 : NNReal) : ℝ) := by
      simpa using Real.log_le_log (Real.exp_pos _) hexp
    have hreal : ((lam1 : NNReal) : ℝ) ≤ ((lam2 : NNReal) : ℝ) := by
      linarith
    exact_mod_cast hreal
  · intro h12
    -- Proof comment: compare every upper tail by writing `Poi(lam2)` as
    -- `Poi(lam1) + Poi(lam2 - lam1)`.
    refine
      (ProbabilityTheory.stochasticLE_toFin1Real_iff_upper_tail
        (⟨poissonMeasure lam1, inferInstance⟩ : ProbabilityMeasure ℕ)
        (⟨poissonMeasure lam2, inferInstance⟩ : ProbabilityMeasure ℕ)).2 ?_
    intro k
    exact poissonMeasure_upper_tail_mono h12 k
