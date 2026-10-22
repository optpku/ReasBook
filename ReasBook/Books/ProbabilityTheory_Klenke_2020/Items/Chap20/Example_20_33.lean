/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_3
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

/- Example 20.33 is `source-facing`: the textbook conclusion is that the uniform-measure rotation
on the finite cyclic system `ZMod n` has zero Kolmogorov--Sinai entropy. The iterate identity
below is only an auxiliary `bridge/view` fact witnessing the periodicity of the underlying finite
system, while the public owner remains `kolmogorov_sinai_entropy`. -/

/-- Helper for Example 20.33: `Real.negMulLog` is superadditive on nonnegative reals, so merging
two masses cannot increase the corresponding Shannon contribution. -/
private lemma negMulLog_add_le
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hxy : x + y = 0
  · -- If the total mass is zero, both summands already vanish.
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · -- Otherwise normalize by the total mass and use the multiplicative formula for `negMulLog`.
    set s : ℝ := x + y
    have hxy' : x + y ≠ 0 := by
      simpa [s] using hxy
    have hs : 0 < s := by
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg hx hy) (by simpa [ne_comm] using hxy')
    have hs_nonneg : 0 ≤ s := le_of_lt hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hxs : x = s * (x / s) := by
      field_simp [s, hs_ne]
    have hys : y = s * (y / s) := by
      field_simp [s, hs_ne]
    have hx_div_nonneg : 0 ≤ x / s := by positivity
    have hy_div_nonneg : 0 ≤ y / s := by positivity
    have hx_div_le_one : x / s ≤ 1 := by
      have hle : x ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hy_div_le_one : y / s ≤ 1 := by
      have hle : y ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hsum_div : x / s + y / s = 1 := by
      field_simp [s, hs_ne]
      ring
    have hx_term_nonneg : 0 ≤ s * Real.negMulLog (x / s) := by
      exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hx_div_nonneg hx_div_le_one)
    have hy_term_nonneg : 0 ≤ s * Real.negMulLog (y / s) := by
      exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hy_div_nonneg hy_div_le_one)
    have htail_nonneg :
        0 ≤ s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s) := by
      linarith
    have hsplit :
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
      calc
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
            ((x / s + y / s) * Real.negMulLog s) +
              (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
          rw [hsum_div]
          ring
        _ =
            ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
              ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
          ring
    have hnegMulLog_x :
        Real.negMulLog x = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
      calc
        Real.negMulLog x = Real.negMulLog (s * (x / s)) := by
          exact congrArg Real.negMulLog hxs
        _ = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
          rw [Real.negMulLog_mul]
    have hnegMulLog_y :
        Real.negMulLog y = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
      calc
        Real.negMulLog y = Real.negMulLog (s * (y / s)) := by
          exact congrArg Real.negMulLog hys
        _ = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
          rw [Real.negMulLog_mul]
    calc
      Real.negMulLog (x + y) = Real.negMulLog s := by simp [s]
      _ ≤ Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
        linarith
      _ =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
        exact hsplit
      _ = Real.negMulLog x + Real.negMulLog y := by
        rw [hnegMulLog_x, hnegMulLog_y]

/-- Helper for Example 20.33: the Shannon contribution of a finite sum of nonnegative masses is
bounded by the sum of the individual Shannon contributions. -/
private lemma negMulLog_sum_le_sum_negMulLog
    {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.negMulLog (Finset.sum s w) ≤ Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
  induction s using Finset.cons_induction with
  | empty =>
      -- The empty sum has zero Shannon contribution.
      simp [Real.negMulLog_zero]
  | @cons a s ha ih =>
      -- Split off one mass and apply the two-point superadditivity step.
      have hwa : 0 ≤ w a := hw a (by simp)
      have hws : ∀ i ∈ s, 0 ≤ w i := by
        intro i hi
        exact hw i (by simp [hi])
      have hsum_nonneg : 0 ≤ Finset.sum s w := Finset.sum_nonneg hws
      calc
        Real.negMulLog (Finset.sum (Finset.cons a s ha) w) =
            Real.negMulLog (w a + Finset.sum s w) := by
          simp
        _ ≤ Real.negMulLog (w a) + Real.negMulLog (Finset.sum s w) :=
          negMulLog_add_le hwa hsum_nonneg
        _ ≤ Real.negMulLog (w a) + Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
          gcongr
          exact ih hws
        _ = Finset.sum (Finset.cons a s ha) (fun i ↦ Real.negMulLog (w i)) := by
          simp

/-- Helper for Example 20.33: deterministic coding on a finite alphabet cannot increase Shannon
entropy. -/
private lemma entropy_map_le {α β : Type*} [Finite α] [Finite β] (p : PMF α) (Φ : α → β) :
    entropy (PMF.map Φ p) ≤ entropy p := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  have hmap_apply (b : β) :
      ((PMF.map Φ p) b).toReal =
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) fun a ↦ (p a).toReal := by
    -- Rewrite the pushed-forward mass at `b` as the finite sum of the masses in its fiber.
    calc
      ((PMF.map Φ p) b).toReal =
          (∑' a : α, if b = Φ a then p a else 0).toReal := by
        rw [PMF.map_apply]
      _ = (∑ a : α, if b = Φ a then p a else 0).toReal := by
        rw [tsum_fintype]
      _ = ∑ a : α, (if b = Φ a then p a else 0).toReal := by
        refine ENNReal.toReal_sum ?_
        intro a ha
        by_cases hab : b = Φ a
        · simp [hab, p.apply_ne_top a]
        · simp [hab]
      _ = Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) fun a ↦ (p a).toReal := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro a ha
        by_cases hab : Φ a = b
        · simp [hab]
        · have hab' : b ≠ Φ a := by
            simpa [eq_comm] using hab
          simp [hab, hab']
  have hfiber :
      ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) ≤
        (∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal)) := by
    -- Apply the finite superadditivity lemma on each fiber separately.
    refine Finset.sum_le_sum ?_
    intro b hb
    rw [hmap_apply b]
    refine negMulLog_sum_le_sum_negMulLog _ _ ?_
    intro a ha
    exact ENNReal.toReal_nonneg
  have hfiberwise :
      (∑ b : β,
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
          fun a ↦ Real.negMulLog ((p a).toReal)) =
        ∑ a : α, Real.negMulLog ((p a).toReal) := by
    -- Reassemble the fiberwise sum to recover the original entropy sum.
    simpa using
      (Finset.sum_fiberwise (s := Finset.univ) (g := Φ)
        (f := fun a : α ↦ Real.negMulLog ((p a).toReal)))
  rw [entropy_eq_sum, entropy_eq_sum]
  apply EReal.coe_le_coe
  -- Convert both entropies to finite real sums of `Real.negMulLog`.
  calc
    (-∑ b : β, ((PMF.map Φ p) b).toReal * Real.log (((PMF.map Φ p) b).toReal) : ℝ) =
        ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) := by
      simp [Real.negMulLog_def]
    _ ≤ ∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal) := hfiber
    _ = ∑ a : α, Real.negMulLog ((p a).toReal) := hfiberwise
    _ = (-∑ a : α, (p a).toReal * Real.log ((p a).toReal) : ℝ) := by
      simp [Real.negMulLog_def]

/-- Helper for Example 20.33: on a finite measurable state space, the entropy of any finite
measurable partition is bounded by the Shannon entropy of the state law itself. -/
private lemma partitionEntropy_le_stateLawEntropy
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (part : MeasurableFinpartition Ω) :
    part.partitionEntropy P ≤ entropy P.toPMF := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  have htoPMF :
      part.toPMF P = PMF.map part.toSimpleFunc P.toPMF := by
    let μ : Measure part.parts := P.map part.toSimpleFunc
    letI : IsProbabilityMeasure μ :=
      Measure.isProbabilityMeasure_map part.toSimpleFunc.aemeasurable
    change μ.toPMF = PMF.map part.toSimpleFunc P.toPMF
    apply PMF.toMeasure_injective
    -- Rewrite both pmfs to the pushforward measures that define them.
    rw [Measure.toPMF_toMeasure]
    rw [← PMF.toMeasure_map (p := P.toPMF) (f := part.toSimpleFunc)
      (hf := part.toSimpleFunc.measurable)]
    rw [Measure.toPMF_toMeasure]
  -- The partition atoms are a deterministic coding of the original finite state.
  calc
    part.partitionEntropy P = entropy (part.toPMF P) := by
      rw [MeasurableFinpartition.partitionEntropy_def]
    _ = entropy (PMF.map part.toSimpleFunc P.toPMF) := by
      rw [htoPMF]
    _ ≤ entropy P.toPMF := entropy_map_le (P.toPMF) part.toSimpleFunc

/-- Helper for Example 20.33: on a finite measurable state space, every partition dynamical
entropy is zero because all block entropies stay uniformly bounded while the normalization
`1 / n` tends to `0`. -/
private lemma dynamicalEntropy_eq_zero_of_finiteState
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) :
    h(P, τ, hτ; part) = 0 := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  let S : Set EReal :=
    Set.range fun n : ℕ+ ↦
      (part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹)
  rw [MeasurableFinpartition.dynamicalEntropy_def]
  change sInf S = 0
  let C : ℝ := max 1 (Real.log (Fintype.card Ω))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.log (Fintype.card Ω)))
  have hterm_nonneg :
      ∀ a ∈ S, 0 ≤ a := by
    rintro _ ⟨n, rfl⟩
    -- Both the block entropy and the normalization factor are nonnegative.
    refine mul_nonneg ?_ ?_
    · simpa [MeasurableFinpartition.partitionEntropy_def] using
        entropy_nonneg ((part.block τ hτ n).toPMF P)
    · positivity
  have hterm_upper (n : ℕ+) :
      (part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹) ≤
        (C : EReal) * (((n : ℕ) : EReal)⁻¹) := by
    have hstate_upper : entropy P.toPMF ≤ (C : EReal) := by
      exact (entropy_le_log_card P.toPMF).trans <|
        by
          exact_mod_cast (le_max_right 1 (Real.log (Fintype.card Ω)))
    have hpart_upper : (part.block τ hτ n).partitionEntropy P ≤ (C : EReal) := by
      exact (partitionEntropy_le_stateLawEntropy (P := P) (part := part.block τ hτ n)).trans
        hstate_upper
    -- Multiply the uniform entropy bound by the nonnegative factor `1 / n`.
    exact mul_le_mul_of_nonneg_right hpart_upper (by positivity)
  have hsmall_term :
      ∀ w, 0 < w → ∃ a ∈ S, a < w := by
    intro w hw
    by_cases hw_top : w = ⊤
    · refine ⟨(part.block τ hτ (1 : ℕ+)).partitionEntropy P * (((1 : ℕ) : EReal)⁻¹), ?_, ?_⟩
      · exact Set.mem_range.mpr ⟨(1 : ℕ+), rfl⟩
      · have hfinite : (C : EReal) * (((1 : ℕ) : EReal)⁻¹) < ⊤ := by
          simp
        simpa [hw_top] using lt_of_le_of_lt (hterm_upper (1 : ℕ+)) hfinite
    · have hw_bot : w ≠ ⊥ := by
        exact ne_of_gt (lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) hw.le)
      have hw_real_pos : 0 < w.toReal := EReal.toReal_pos hw hw_top
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < w.toReal / C by
        exact div_pos hw_real_pos hC_pos)
      let n : ℕ+ := ⟨m + 1, Nat.succ_pos _⟩
      refine ⟨(part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹),
        Set.mem_range.mpr ⟨n, rfl⟩, ?_⟩
      have hreal_bound : C * (1 / (n : ℝ)) < w.toReal := by
        have hm' : C * (1 / (m + 1 : ℝ)) < w.toReal := by
          calc
            C * (1 / (m + 1 : ℝ)) < C * (w.toReal / C) := by
              exact mul_lt_mul_of_pos_left hm hC_pos
            _ = w.toReal := by
              field_simp [hC_pos.ne']
        simpa [n] using hm'
      have hbound_eq :
          (C : EReal) * (((n : ℕ) : EReal)⁻¹) =
            ((C * (1 / (n : ℝ)) : ℝ) : EReal) := by
        have hnat_inv :
            (((n : ℕ) : EReal)⁻¹) = ((((n : ℝ))⁻¹ : ℝ) : EReal) := by
          rw [show ((n : ℕ) : EReal) = ((n : ℝ) : EReal) by norm_num]
          rw [← EReal.coe_inv (n : ℝ)]
        calc
          (C : EReal) * (((n : ℕ) : EReal)⁻¹) =
              (C : EReal) * ((((n : ℝ))⁻¹ : ℝ) : EReal) := by
                rw [hnat_inv]
          _ = ((C * ((n : ℝ)⁻¹) : ℝ) : EReal) := by
                rw [← EReal.coe_mul]
          _ = ((C * (1 / (n : ℝ)) : ℝ) : EReal) := by
                simp [one_div]
      have hbound_lt_w :
          (C : EReal) * (((n : ℕ) : EReal)⁻¹) < w := by
        rw [hbound_eq, ← EReal.coe_toReal hw_top hw_bot]
        exact_mod_cast hreal_bound
      exact lt_of_le_of_lt (hterm_upper n) hbound_lt_w
  -- The normalized block-entropy range has infimum `0` by the standard `sInf` criterion.
  exact sInf_eq_of_forall_ge_of_forall_gt_exists_lt hterm_nonneg hsmall_term

/-- Helper for Example 20.33: every measurable self-map of a finite measurable probability space
has zero Kolmogorov--Sinai entropy. -/
private lemma kolmogorovSinaiEntropy_eq_zero_of_finiteState
    {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω] [Finite Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (τ : Ω → Ω) (hτ : Measurable τ) :
    h(P, τ, hτ) = 0 := by
  rw [kolmogorov_sinai_entropy_def]
  refine le_antisymm ?_ ?_
  · -- Every competing partition has zero dynamical entropy by the finite-state lemma above.
    refine sSup_le ?_
    rintro _ ⟨part, rfl⟩
    simpa using (dynamicalEntropy_eq_zero_of_finiteState (P := P) (τ := τ) hτ part).le
  · let trivialPart : MeasurableFinpartition Ω :=
        MeasurableFinpartition.ofSimpleFunc (SimpleFunc.const Ω ())
    have htrivial :
        h(P, τ, hτ; trivialPart) = 0 :=
      dynamicalEntropy_eq_zero_of_finiteState (P := P) (τ := τ) hτ trivialPart
    -- The one-atom partition supplies an explicit `0` in the defining supremum range.
    simpa [htrivial] using
      (le_sSup (Set.mem_range.mpr ⟨trivialPart, rfl⟩) :
        h(P, τ, hτ; trivialPart) ≤
          sSup (Set.range fun part : MeasurableFinpartition Ω ↦ h(P, τ, hτ; part)))

-- Proof sketch: each application of the translation map `x ↦ x + r` adds `r` modulo `n`, so the
-- `n`-th iterate adds `n • r`, which vanishes in `ZMod n`.
/-- The `n`-fold iterate of the translation `x ↦ x + r` on `ZMod n` is the identity. -/
theorem zmodTranslation_iterate_eq_id (n r : ℕ) :
    (((· + (r : ZMod n)) : ZMod n → ZMod n)^[n]) = id := by
  ext x
  have hiter : ∀ m : ℕ, (((· + (r : ZMod n)) : ZMod n → ZMod n)^[m]) x = x + m • (r : ZMod n) := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ihm =>
        rw [Function.iterate_succ_apply']
        rw [ihm]
        ring_nf
  rw [hiter n, nsmul_eq_mul]
  simp

variable (n r : ℕ) [NeZero n]

-- Proof sketch: the map `x ↦ x + r` is a finite periodic rotation of the uniform probability space
-- `ZMod n`; Example 20.8 supplies the canonical `MeasurePreserving` owner, and periodic finite
-- systems have zero Kolmogorov--Sinai entropy.
/-- Example 20.33: the Kolmogorov--Sinai entropy of the uniform rotation
`x ↦ x + r` on the finite cyclic group `ZMod n` is zero. -/
theorem zmodTranslationEntropy_eq_zero :
    h(uniformOn (Set.univ : Set (ZMod n)),
      ((· + (r : ZMod n)) : ZMod n → ZMod n), (zmodTranslation_measurePreserving n r).measurable) =
      0 := by
  -- Route correction: instead of unfolding periodic block names, use the stronger finite-state
  -- fact that every deterministic system on a finite measurable probability space has zero
  -- Kolmogorov--Sinai entropy.
  exact kolmogorovSinaiEntropy_eq_zero_of_finiteState
    (P := uniformOn (Set.univ : Set (ZMod n)))
    (τ := ((· + (r : ZMod n)) : ZMod n → ZMod n))
    (hτ := (zmodTranslation_measurePreserving n r).measurable)
