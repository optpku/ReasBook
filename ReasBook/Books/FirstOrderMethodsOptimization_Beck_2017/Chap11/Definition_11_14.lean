/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_37
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Definition_11_4
import Mathlib.Probability.Independence.Kernel.IndepFun

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal BigOperators Gradient

section

variable {ι : Type u} {Ei : ι → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace ℝ (Ei i)]

/-- The realized block-index history `ξ_{k-1}` encoded as the first `k` sampled indices. -/
def randomized_block_history (sampled_block : ℕ → ι) (k : ℕ) : Fin k → ι :=
  fun t ↦ sampled_block t

-- Proof sketch: unfold `randomized_block_history`; the `t`-th coordinate of the prefix history is
-- definitionally the sampled block `sampled_block t`.
/-- Evaluating the realized history `ξ_{k-1}` at the time `t < k` returns the sampled block
`i_t`. -/
@[simp] theorem randomized_block_history_apply
    (sampled_block : ℕ → ι) (k : ℕ) (t : Fin k) :
    randomized_block_history sampled_block k t = sampled_block t := rfl

section

variable {Ω : Type v} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
variable {sampled_block : ℕ → Ω → ι}

/-- Helper for Definition 11.14: reindexing a tuple over `Finset.range n` gives the canonical
history type `Fin n → ι`. -/
def historyFromRangeTuple (n : ℕ) :
    ((i : (Finset.range n : Finset ℕ)) → ι) → (Fin n → ι) :=
  fun x t ↦ x ⟨t, Finset.mem_range.mpr t.2⟩

/-- Helper for Definition 11.14: projecting the singleton tuple over `{n}` recovers its only
coordinate. -/
def currentFromSingletonTuple (n : ℕ) :
    ((i : ({n} : Finset ℕ)) → ι) → ι :=
  fun x ↦ x ⟨n, Finset.mem_singleton_self n⟩

section

omit [IsProbabilityMeasure μ] [DiscreteMeasurableSpace ι]

/-- Helper for Definition 11.14: the finite history `ξ_{n-1}` is independent of the current sampled
block `i_n`. -/
lemma randomizedBlockHistoryIndepCurrent
    (n : ℕ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ) :
    IndepFun
      (fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) n)
      (sampled_block n)
      μ := by
  classical
  -- First isolate the tuple of past coordinates and the current singleton coordinate.
  have h_range_indep :
      IndepFun
        (fun ω (i : (Finset.range n : Finset ℕ)) ↦ sampled_block i ω)
        (fun ω (i : ({n} : Finset ℕ)) ↦ sampled_block i ω) μ := by
    refine h_sampled_block_indep.indepFun_finset (Finset.range n) {n} ?_ h_sampled_block_meas
    rw [Finset.disjoint_singleton_right]
    exact Finset.notMem_range_self
  have h_historyFromRangeTuple_meas : Measurable (historyFromRangeTuple (ι := ι) n) := by
    -- Each coordinate of the reindexed tuple is just an evaluation map.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [historyFromRangeTuple] using
      (measurable_pi_apply
        (a := (⟨(t : ℕ), Finset.mem_range.mpr t.2⟩ : (Finset.range n : Finset ℕ))) :
        Measurable
          (fun x : ((i : (Finset.range n : Finset ℕ)) → ι) =>
            x ⟨t, Finset.mem_range.mpr t.2⟩))
  have h_currentFromSingletonTuple_meas :
      Measurable (currentFromSingletonTuple (ι := ι) n) := by
    -- The singleton tuple projection is the evaluation at its unique index.
    simpa [currentFromSingletonTuple] using
      (measurable_pi_apply
        (a := (⟨n, Finset.mem_singleton_self n⟩ : ({n} : Finset ℕ))) :
        Measurable
          (fun x : ((i : ({n} : Finset ℕ)) → ι) =>
            x ⟨n, Finset.mem_singleton_self n⟩))
  -- Then transport those tuples to the source-facing history and current-block variables.
  simpa [historyFromRangeTuple, currentFromSingletonTuple, randomized_block_history] using
    h_range_indep.comp h_historyFromRangeTuple_meas h_currentFromSingletonTuple_meas

end

/-- Helper for Definition 11.14: integrating a real function against the uniform marginal law of
`sampled_block n` yields the arithmetic average over the finite block set. -/
lemma sampledBlockMarginalIntegral_eq_average
    [Fintype ι]
    (n : ℕ)
    (φ : ι → ℝ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_uniform :
      ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (Fintype.card ι : ℝ≥0∞)) :
    MeasureTheory.integral (μ.map (sampled_block n)) φ =
      ((Fintype.card ι : ℝ)⁻¹) * (∑ i, φ i) := by
  classical
  have hφ_int : Integrable φ (μ.map (sampled_block n)) := by
    -- The marginal lives on a finite discrete space, so every real observable is integrable.
    exact Integrable.of_finite
  have h_mass :
      ∀ i : ι, (μ.map (sampled_block n)).real {i} = (Fintype.card ι : ℝ)⁻¹ := by
    intro i
    -- Rewrite the singleton mass through the map measure, then convert the ENNReal weight to `ℝ`.
    rw [MeasureTheory.measureReal_def, Measure.map_apply_of_aemeasurable
      (h_sampled_block_meas n).aemeasurable (MeasurableSet.singleton i)]
    have h_card_ne_zero_nat : Fintype.card ι ≠ 0 := by
      exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩)
    have h_card_ne_zero_ennreal : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast h_card_ne_zero_nat
    simpa [one_div, ENNReal.toReal_inv, h_card_ne_zero_ennreal] using
      congrArg ENNReal.toReal (h_sampled_block_uniform n i)
  -- Expand the discrete integral into singleton masses and factor out the uniform weight.
  calc
    MeasureTheory.integral (μ.map (sampled_block n)) φ
      = ∑ i, (μ.map (sampled_block n)).real {i} * φ i := by
          rw [MeasureTheory.integral_fintype hφ_int]
          simp [smul_eq_mul]
    _ = ∑ i, ((Fintype.card ι : ℝ)⁻¹) * φ i := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [h_mass i]
    _ = ((Fintype.card ι : ℝ)⁻¹) * (∑ i, φ i) := by
          rw [Finset.mul_sum]

section

omit [DiscreteMeasurableSpace ι]

/-- The finite sampled-block history up to time `n - 1` is independent of the current sampled
block `i_n`, so their joint law splits as a product measure. -/
theorem randomized_block_history_current_block_jointlaw
    (n : ℕ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ) :
    μ.map
        (fun ω ↦
          (randomized_block_history (fun m ↦ sampled_block m ω) n, sampled_block n ω)) =
      (μ.map (fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) n)).prod
        (μ.map (sampled_block n)) := by
  -- Convert the structural independence of `(ξ_{n-1}, i_n)` directly into the product-law identity.
  let history : Ω → Fin n → ι :=
    fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) n
  have h_history_meas :
      Measurable history := by
    -- The history map is measurable because each coordinate is one sampled block.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [history, randomized_block_history] using h_sampled_block_meas t
  simpa using
    (indepFun_iff_map_prod_eq_prod_map_map h_history_meas.aemeasurable
      (h_sampled_block_meas n).aemeasurable).1
      (randomizedBlockHistoryIndepCurrent n h_sampled_block_meas h_sampled_block_indep)

end

/-- Averaging over the current sampled block after freezing the finite history `ξ_{n-1}` gives the
uniform block average from the source proof. -/
theorem randomized_block_history_current_block_average
    [Fintype ι]
    (n : ℕ)
    (ψ : (Fin n → ι) → ι → ℝ)
    (h_sampled_block_meas : ∀ k, Measurable (sampled_block k))
    (h_sampled_block_indep : iIndepFun sampled_block μ)
    (h_sampled_block_uniform :
      ∀ k (i : ι), μ ((sampled_block k) ⁻¹' {i}) = 1 / (Fintype.card ι : ℝ≥0∞)) :
    μ[fun ω ↦ ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) (sampled_block n ω)] =
      μ[fun ω ↦ ((Fintype.card ι : ℝ)⁻¹) *
        (∑ i, ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) i)] := by
  classical
  let history : Ω → Fin n → ι :=
    fun ω ↦ randomized_block_history (fun m ↦ sampled_block m ω) n
  let joint : Ω → (Fin n → ι) × ι :=
    fun ω ↦ (history ω, sampled_block n ω)
  have h_history_meas : Measurable history := by
    -- The history is the tuple of the first `n` sampled blocks.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [history, randomized_block_history] using h_sampled_block_meas t
  have h_joint_meas : AEMeasurable joint μ := by
    -- The joint pair `(ξ_{n-1}, i_n)` is measurable componentwise.
    simpa [joint] using h_history_meas.aemeasurable.prodMk (h_sampled_block_meas n).aemeasurable
  have h_jointlaw :
      μ.map joint = (μ.map history).prod (μ.map (sampled_block n)) := by
    -- Reuse the already proved joint-law factorization after unfolding the local names.
    simpa [history, joint] using
      randomized_block_history_current_block_jointlaw
        (sampled_block := sampled_block)
        n h_sampled_block_meas h_sampled_block_indep
  have h_prod_int :
      Integrable (fun z : (Fin n → ι) × ι ↦ ψ z.1 z.2)
        ((μ.map history).prod (μ.map (sampled_block n))) := by
    -- The product law lives on a finite discrete space, so every real observable is integrable.
    exact Integrable.of_finite
  have h_avg_meas :
      AEStronglyMeasurable (fun ξ : Fin n → ι ↦ ((Fintype.card ι : ℝ)⁻¹) * (∑ i, ψ ξ i))
        (μ.map history) := by
    -- The averaging observable is measurable on the finite discrete history space.
    exact (Measurable.of_discrete :
      Measurable (fun ξ : Fin n → ι ↦ ((Fintype.card ι : ℝ)⁻¹) * (∑ i, ψ ξ i))).aestronglyMeasurable
  have h_joint_eval_meas :
      AEStronglyMeasurable (fun z : (Fin n → ι) × ι ↦ ψ z.1 z.2) (μ.map joint) := by
    exact (Measurable.of_discrete :
      Measurable (fun z : (Fin n → ι) × ι ↦ ψ z.1 z.2)).aestronglyMeasurable
  change
      MeasureTheory.integral μ
          (fun ω ↦ ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) (sampled_block n ω)) =
      MeasureTheory.integral μ
          (fun ω ↦
            ((Fintype.card ι : ℝ)⁻¹) *
              (∑ i, ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) i))
  calc
    MeasureTheory.integral μ
        (fun ω ↦ ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) (sampled_block n ω))
      = MeasureTheory.integral (μ.map joint) (fun z : (Fin n → ι) × ι ↦ ψ z.1 z.2) := by
          -- Push the expectation through the joint random variable.
          symm
          simpa [joint, history] using integral_map h_joint_meas h_joint_eval_meas
    _ = MeasureTheory.integral
          ((μ.map history).prod (μ.map (sampled_block n)))
          (fun z : (Fin n → ι) × ι ↦ ψ z.1 z.2) := by
          rw [h_jointlaw]
    _ = MeasureTheory.integral
          (μ.map history)
          (fun ξ ↦ MeasureTheory.integral (μ.map (sampled_block n)) (ψ ξ)) := by
          rw [MeasureTheory.integral_prod _ h_prod_int]
    _ = MeasureTheory.integral
          (μ.map history)
          (fun ξ ↦ ((Fintype.card ι : ℝ)⁻¹) * (∑ i, ψ ξ i)) := by
          refine integral_congr_ae ?_
          filter_upwards with ξ
          simpa using sampledBlockMarginalIntegral_eq_average
            (sampled_block := sampled_block)
            (μ := μ) n (ψ ξ) h_sampled_block_meas h_sampled_block_uniform
    _ = MeasureTheory.integral μ
          (fun ω ↦
            ((Fintype.card ι : ℝ)⁻¹) *
              (∑ i, ψ (randomized_block_history (fun m ↦ sampled_block m ω) n) i)) := by
          -- Pull the history average back along the history random variable.
          simpa [history] using integral_map h_history_meas.aemeasurable h_avg_meas

/-- A real observable depending only on a finite block history is integrable because that history
takes values in the finite discrete type `Fin k → ι`. -/
theorem randomized_block_history_observable_integrable
    [Finite ι]
    (k : ℕ) (ψ : (Fin k → ι) → ℝ)
    (h_sampled_block_meas : ∀ n, Measurable (sampled_block n)) :
    Integrable (fun ω ↦ ψ (randomized_block_history (fun n ↦ sampled_block n ω) k)) μ := by
  classical
  let history : Ω → Fin k → ι :=
    fun ω ↦ randomized_block_history (fun n ↦ sampled_block n ω) k
  have h_history_meas : Measurable history := by
    -- The finite history is measurable coordinatewise.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [history, randomized_block_history] using h_sampled_block_meas t
  have hψ_int : Integrable ψ (μ.map history) := by
    -- After mapping to the finite history space, every real observable is integrable.
    exact Integrable.of_finite
  simpa [history, randomized_block_history] using hψ_int.comp_measurable h_history_meas

end

variable [Fintype ι]

scoped[RBPG] notation "‖" x "‖_[" L "]" =>
  compositeWeightedL2Norm L x

scoped[RBPG] notation "‖" x "‖_[" L ",*]" =>
  compositeWeightedL2Norm (fun i ↦ (L i)⁻¹) x

open scoped RBPG

-- Proof sketch: rewrite the Chapter 11 notation `‖x‖_[L]` to the Chapter 1 owner
-- `compositeWeightedL2Norm`, then apply `compositeWeightedL2Norm_def`.
/-- The weighted block norm has the textbook formula `√(∑ i, L_i ‖x_i‖²)`. -/
theorem randomized_block_weighted_norm_def
    (L : ι → PosReal) (x : (i : ι) → Ei i) :
    ‖x‖_[L] = √(∑ i, (L i : ℝ) * ‖x i‖ ^ (2 : ℕ)) := by
  simpa using compositeWeightedL2Norm_def L x

-- Proof sketch: rewrite the Chapter 11 notation `‖x‖_[L,*]` to the Chapter 1 owner
-- `compositeWeightedL2Norm`, then apply `compositeWeightedL2Norm_def`.
/-- The dual weighted block norm has the textbook formula
`√(∑ i, (1 / L_i) ‖x_i‖²)`. -/
theorem randomized_block_weighted_dual_norm_def
    (L : ι → PosReal) (x : (i : ι) → Ei i) :
    ‖x‖_[L,*] = √(∑ i, ((L i : ℝ)⁻¹) * ‖x i‖ ^ (2 : ℕ)) := by
  simpa using compositeWeightedL2Norm_def (fun i ↦ (L i)⁻¹) x

end

section

variable {ι : Type u} {Ei : ι → Type v}
variable [Fintype ι]
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : ι) → Ei i) → EReal} {g : (i : ι) → Ei i → EReal}
variable {block_gradient : (i : ι) → ((j : ι) → Ei j) → Ei i}
variable {XStar : Set ((i : ι) → Ei i)} {FOpt : ℝ}
variable {Li : (i : ι) → PosReal}

/- Definition 11.14: besides the realized block history `ξ_{k-1}` and the weighted norms
`‖·‖_[L]`, `‖·‖_[L,*]`, the randomized block proximal-gradient method uses the coordinatewise
randomized block gradient mapping `Gtilde[h] x`, the Lean surface for the textbook tilde-`G`
mapping at `x`,
whose `i`-th block is `G^i_{L_i}(x)`.

Canonical owner recall:
- the one-block residual owner is `IsBlockProximalGradientProblem.gradient_mapping` from
  `Definition_11_4`;
- the source-facing randomized mapping is the coordinatewise packaging
  `fun i ↦ h.gradient_mapping (Li i) i x`.

This file records the history and norm surfaces directly, and exposes the `Gtilde` packaging as a
source-facing bridge to that Chapter 11 owner rather than a second root owner. -/

/-- Definition 11.14: the randomized block gradient mapping packages the block residuals
`G^i_{L_i}(x)` into a single block vector. -/
abbrev randomized_block_gradient_mapping
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : (i : ι) → Ei i) : (i : ι) → Ei i :=
  fun i ↦ G[Li i; h] x i

/- Lean notation `Gtilde[h] x` for the textbook randomized block gradient mapping with tilde-`G`
at `x`, attached to a Chapter 11 block-problem owner. -/
set_option quotPrecheck false in
scoped[RBPG] notation:max "Gtilde[" h "]" =>
  randomized_block_gradient_mapping h

/- Direct-application form of the Chapter 11 notation `Gtilde[h] x`. -/
set_option quotPrecheck false in
scoped[RBPG] notation:max "Gtilde[" h "]" x:arg =>
  randomized_block_gradient_mapping h x

open scoped RBPG

/-- Evaluating the randomized block gradient mapping at block `i` recovers the one-block residual
`G^i_{L_i}(x)`. -/
@[simp] theorem randomized_block_gradient_mapping_apply
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : (i : ι) → Ei i) (i : ι) :
    (Gtilde[h] x) i = G[Li i; h] x i := rfl

/-- Evaluating `Gtilde[h] x` at block `i` gives the stepsize-scaled residual
`L_i • (x_i - T^i_{L_i}(x))`. -/
@[simp] theorem randomized_block_gradient_mapping_apply_def
    (h : IsBlockProximalGradientProblem f g block_gradient XStar FOpt Li)
    (x : (i : ι) → Ei i) (i : ι) :
    (Gtilde[h] x) i = (Li i : ℝ) • (x i - h.prox_point (Li i) i x) := by
  change h.gradient_mapping (Li i) i x = (Li i : ℝ) • (x i - h.prox_point (Li i) i x)
  exact h.gradient_mapping_def (Li i) x i

end
