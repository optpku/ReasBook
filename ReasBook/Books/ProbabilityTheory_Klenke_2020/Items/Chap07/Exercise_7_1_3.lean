/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open MeasureTheory
open scoped ENNReal Topology

/-- The `n`-th Cesàro average of the nonnegative integer translates of `f`. -/
noncomputable def integerTranslateCesaro (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun x ↦
    ((n + 1 : ℝ)⁻¹) * Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))

/-- Integer translation preserves `ℒ^p(λ)` because Lebesgue measure is translation invariant. -/
private theorem integerTranslate_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume) (k : ℕ) :
    MemLp (fun x ↦ f (x + k)) p volume := by
  simpa [Function.comp, add_comm] using
    hf.comp_measurePreserving (measurePreserving_add_left volume (k : ℝ))

/-- If `f ∈ ℒ^p(λ)`, then each Cesàro average of its integer translates again belongs to
`ℒ^p(λ)`. -/
private theorem integerTranslateCesaro_memLp {p : ℝ≥0∞} {f : ℝ → ℝ} (hf : MemLp f p volume)
    (n : ℕ) :
    MemLp (integerTranslateCesaro f n) p volume := by
  have hsum : MemLp (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))) p volume := by
    classical
    refine Finset.induction_on (Finset.range (n + 1)) ?_ ?_
    · simp
    · intro k s hk hs
      simpa [Finset.sum_insert hk] using (integerTranslate_memLp hf k).add hs
  simpa [integerTranslateCesaro, smul_eq_mul] using hsum.const_smul ((n + 1 : ℝ)⁻¹)

/-- Helper for Exercise 7.1.3: if `1 < p`, then `1 ≤ (p : ℝ≥0∞)`. -/
private theorem one_le_coe_ennreal_of_fact_one_lt (p : NNReal) [Fact (1 < p)] :
    1 ≤ (p : ℝ≥0∞) := by
  exact_mod_cast (Fact.out : (1 : NNReal) < p).le

/-- Helper for Exercise 7.1.3: the coercion of a finite exponent greater than `1` supplies the
`Fact (1 ≤ (p : ℝ≥0∞))` instance needed by `Lp`. -/
private instance fact_one_le_coe_ennreal_of_fact_one_lt (p : NNReal) [Fact (1 < p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) :=
  ⟨one_le_coe_ennreal_of_fact_one_lt p⟩

/-- Helper for Exercise 7.1.3: subtracting two Cesàro averages is the Cesàro average of the
pointwise difference. -/
private lemma integerTranslateCesaro_sub (f g : ℝ → ℝ) (n : ℕ) :
    integerTranslateCesaro f n - integerTranslateCesaro g n =
      integerTranslateCesaro (fun x ↦ f x - g x) n := by
  -- Rewrite the average pointwise so later norm estimates only see one summand family.
  ext x
  simp [integerTranslateCesaro, Finset.sum_sub_distrib, mul_sub]

/-- Helper for Exercise 7.1.3: the `Lp` class of a Cesàro average is the average of the translated
`Lp` classes. -/
private lemma integerTranslateCesaro_toLp_eq_averageTranslates {p : NNReal} [Fact (1 < p)]
    {f : ℝ → ℝ} (hf : MemLp f (p : ℝ≥0∞) volume) (n : ℕ) :
    (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n) =
      ((n + 1 : ℝ)⁻¹) •
        Finset.sum (Finset.range (n + 1))
          (fun k ↦
            Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
              (measurePreserving_add_left volume (k : ℝ))
              (hf.toLp f)) := by
  classical
  let translatedLp : ℕ → Lp ℝ (p : ℝ≥0∞) volume := fun k ↦
    Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
      (measurePreserving_add_left volume (k : ℝ))
      (hf.toLp f)
  have hsumMem : ∀ s : Finset ℕ,
      MemLp (fun x ↦ Finset.sum s (fun k ↦ f (x + k))) (p : ℝ≥0∞) volume := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro k s hk hs
      simpa [Finset.sum_insert hk] using (integerTranslate_memLp hf k).add hs
  have hsumToLp : ∀ s : Finset ℕ,
      (hsumMem s).toLp (fun x ↦ Finset.sum s (fun k ↦ f (x + k))) =
        Finset.sum s (fun k ↦ translatedLp k) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rfl
    · intro k s hk hs
      have hkToLp :
          (integerTranslate_memLp hf k).toLp (fun x ↦ f (x + k)) = translatedLp k := by
        -- Rewrite one translated summand using the canonical measure-preserving action on `Lp`.
        simpa [translatedLp, Function.comp, add_comm] using
          (Lp.toLp_compMeasurePreserving
            (g := f) (hg := hf)
            (f := fun x : ℝ ↦ (k : ℝ) + x)
            (hf := measurePreserving_add_left volume (k : ℝ))).symm
      -- Build the finite sum in `Lp` one translated summand at a time.
      simpa [Finset.sum_insert hk, hsumMem, hs, hkToLp] using
        (MemLp.toLp_add (integerTranslate_memLp hf k) (hsumMem s))
  have hdef :
      integerTranslateCesaro f n =
        ((n + 1 : ℝ)⁻¹) •
          (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))) := by
    ext x
    simp [integerTranslateCesaro, smul_eq_mul]
  calc
    (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n)
        = (((hsumMem (Finset.range (n + 1))).const_smul ((n + 1 : ℝ)⁻¹)).toLp
            (((n + 1 : ℝ)⁻¹) •
              (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))))) := by
      exact MemLp.toLp_congr
        (integerTranslateCesaro_memLp hf n)
        ((hsumMem (Finset.range (n + 1))).const_smul ((n + 1 : ℝ)⁻¹))
        (Filter.Eventually.of_forall fun x ↦ by simp [hdef])
    _ = ((n + 1 : ℝ)⁻¹) •
          (hsumMem (Finset.range (n + 1))).toLp
            (fun x ↦ Finset.sum (Finset.range (n + 1)) (fun k ↦ f (x + k))) := by
      -- Move the scalar outside once the raw finite sum has been normalized in `Lp`.
      simpa using
        (MemLp.toLp_const_smul ((n + 1 : ℝ)⁻¹) (hsumMem (Finset.range (n + 1))))
    _ = ((n + 1 : ℝ)⁻¹) •
          Finset.sum (Finset.range (n + 1)) (fun k ↦ translatedLp k) := by
      rw [hsumToLp]
    _ = ((n + 1 : ℝ)⁻¹) •
          Finset.sum (Finset.range (n + 1))
            (fun k ↦
              Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
                (measurePreserving_add_left volume (k : ℝ))
                (hf.toLp f)) := rfl

/-- Helper for Exercise 7.1.3: Cesàro averaging is nonexpansive on `Lp`. -/
private lemma integerTranslateCesaro_toLp_norm_le {p : NNReal} [Fact (1 < p)] {f : ℝ → ℝ}
    (hf : MemLp f (p : ℝ≥0∞) volume) (n : ℕ) :
    ‖(integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n)‖ ≤ ‖hf.toLp f‖ := by
  rw [integerTranslateCesaro_toLp_eq_averageTranslates (hf := hf) (n := n)]
  calc
    ‖((n + 1 : ℝ)⁻¹) •
        (Finset.sum (Finset.range (n + 1)) fun k ↦
          Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
            (measurePreserving_add_left volume (k : ℝ))
            (hf.toLp f))‖
      = ‖(n + 1 : ℝ)⁻¹‖ *
          ‖Finset.sum (Finset.range (n + 1)) (fun k ↦
              Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
                (measurePreserving_add_left volume (k : ℝ))
                (hf.toLp f))‖ := by
        rw [norm_smul]
    _ ≤ ‖(n + 1 : ℝ)⁻¹‖ *
          Finset.sum (Finset.range (n + 1)) (fun k ↦
            ‖Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
                (measurePreserving_add_left volume (k : ℝ))
                (hf.toLp f)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range (n + 1)) fun k ↦
          Lp.compMeasurePreserving (fun x : ℝ ↦ (k : ℝ) + x)
            (measurePreserving_add_left volume (k : ℝ))
            (hf.toLp f))
        (norm_nonneg _)
    _ = ‖(n + 1 : ℝ)⁻¹‖ * ((n + 1 : ℝ) * ‖hf.toLp f‖) := by
      simp [Lp.norm_compMeasurePreserving]
    _ = ‖hf.toLp f‖ := by
      have hn : 0 ≤ (n + 1 : ℝ) := by positivity
      rw [Real.norm_of_nonneg (inv_nonneg.mpr hn), ← mul_assoc, inv_mul_cancel₀, one_mul]
      positivity

/-- Helper for Exercise 7.1.3: the Cesàro averaging operator is nonexpansive in `eLpNorm`. -/
private lemma integerTranslateCesaro_eLpNorm_sub_le {p : NNReal} [Fact (1 < p)]
    {f g : ℝ → ℝ} (hf : MemLp f (p : ℝ≥0∞) volume) (hg : MemLp g (p : ℝ≥0∞) volume)
    (n : ℕ) :
    eLpNorm (integerTranslateCesaro f n - integerTranslateCesaro g n) (p : ℝ≥0∞) volume ≤
      eLpNorm (f - g) (p : ℝ≥0∞) volume := by
  have hsub : MemLp (fun x ↦ f x - g x) (p : ℝ≥0∞) volume := hf.sub hg
  have hcesaroSub :
      MemLp (integerTranslateCesaro (fun x ↦ f x - g x) n) (p : ℝ≥0∞) volume :=
    integerTranslateCesaro_memLp hsub n
  have hcontract :
      ENNReal.ofReal
        ‖hcesaroSub.toLp (integerTranslateCesaro (fun x ↦ f x - g x) n)‖ ≤
      ENNReal.ofReal ‖hsub.toLp (fun x ↦ f x - g x)‖ := by
    exact ENNReal.ofReal_le_ofReal
      (integerTranslateCesaro_toLp_norm_le (f := fun x ↦ f x - g x) hsub n)
  -- Route correction: convert the `Lp` contraction back to the textbook `eLpNorm` statement only
  -- after the averaging operator has been normalized in `Lp`.
  calc
    eLpNorm (integerTranslateCesaro f n - integerTranslateCesaro g n) (p : ℝ≥0∞) volume
        = ENNReal.ofReal
            ‖hcesaroSub.toLp (integerTranslateCesaro (fun x ↦ f x - g x) n)‖ := by
      rw [integerTranslateCesaro_sub, Lp.norm_toLp]
      exact (ENNReal.ofReal_toReal hcesaroSub.2.ne).symm
    _ ≤ ENNReal.ofReal ‖hsub.toLp (fun x ↦ f x - g x)‖ := hcontract
    _ = eLpNorm (f - g) (p : ℝ≥0∞) volume := by
      rw [Lp.norm_toLp]
      exact ENNReal.ofReal_toReal hsub.2.ne

/-- Helper for Exercise 7.1.3: if `tsupport g ⊆ Icc a b` and `b - a` is strictly smaller than the
integer `N`, then among the translates `g (x + k)` there are at most `N` nonzero values. -/
private lemma card_nonzeroTranslateIndices_le {g : ℝ → ℝ} {a b x : ℝ} {N : ℕ}
    (hN_pos : 0 < N) (ht : tsupport g ⊆ Set.Icc a b) (hN : b - a < N) (n : ℕ) :
    ((Finset.range (n + 1)).filter (fun k : ℕ ↦ g (x + k) ≠ 0)).card ≤ N := by
  classical
  let s : Finset ℕ := (Finset.range (n + 1)).filter (fun k : ℕ ↦ g (x + k) ≠ 0)
  have hs_inj :
      Set.InjOn (fun k : ℕ ↦ k % N) ↑s := by
    intro k hk l hl hmod
    by_cases hkl : k ≤ l
    · have hk_ne : g (x + k) ≠ 0 := (Finset.mem_filter.mp hk).2
      have hl_ne : g (x + l) ≠ 0 := (Finset.mem_filter.mp hl).2
      have hk_mem : x + k ∈ tsupport g := by
        by_contra hx
        exact hk_ne (image_eq_zero_of_notMem_tsupport hx)
      have hl_mem : x + l ∈ tsupport g := by
        by_contra hx
        exact hl_ne (image_eq_zero_of_notMem_tsupport hx)
      have hkI := ht hk_mem
      have hlI := ht hl_mem
      have hdiffR : ((l - k : ℕ) : ℝ) ≤ b - a := by
        have htmp : (l : ℝ) - k ≤ b - a := by
          linarith [hkI.1, hlI.2]
        simpa [Nat.cast_sub hkl] using htmp
      have hlt : l - k < N := by
        exact_mod_cast (lt_of_le_of_lt hdiffR hN)
      have hdiv : N ∣ l - k := (Nat.modEq_iff_dvd' hkl).1 hmod
      have hzero : l - k = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      have hlk : l ≤ k := Nat.sub_eq_zero_iff_le.mp hzero
      exact le_antisymm hkl hlk
    · have hlk : l ≤ k := le_of_not_ge hkl
      have hk_ne : g (x + k) ≠ 0 := (Finset.mem_filter.mp hk).2
      have hl_ne : g (x + l) ≠ 0 := (Finset.mem_filter.mp hl).2
      have hk_mem : x + k ∈ tsupport g := by
        by_contra hx
        exact hk_ne (image_eq_zero_of_notMem_tsupport hx)
      have hl_mem : x + l ∈ tsupport g := by
        by_contra hx
        exact hl_ne (image_eq_zero_of_notMem_tsupport hx)
      have hkI := ht hk_mem
      have hlI := ht hl_mem
      have hdiffR : ((k - l : ℕ) : ℝ) ≤ b - a := by
        have htmp : (k : ℝ) - l ≤ b - a := by
          linarith [hlI.1, hkI.2]
        simpa [Nat.cast_sub hlk] using htmp
      have hlt : k - l < N := by
        exact_mod_cast (lt_of_le_of_lt hdiffR hN)
      have hdiv : N ∣ k - l := (Nat.modEq_iff_dvd' hlk).1 hmod.symm
      have hzero : k - l = 0 := Nat.eq_zero_of_dvd_of_lt hdiv hlt
      have hkl' : k ≤ l := Nat.sub_eq_zero_iff_le.mp hzero
      have hEq : l = k := le_antisymm hlk hkl'
      simp [hEq]
  -- Count by the residue class modulo `N`.
  have hcard_map :
      (s.image fun k ↦ k % N).card = s.card := Finset.card_image_iff.mpr hs_inj
  have hsubset : s.image (fun k ↦ k % N) ⊆ Finset.range N := by
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hN_pos)
  calc
    s.card = (s.image fun k ↦ k % N).card := hcard_map.symm
    _ ≤ (Finset.range N).card := Finset.card_le_card hsubset
    _ = N := Finset.card_range N

/-- Helper for Exercise 7.1.3: outside the support window where a translated summand could be
nonzero, the Cesàro average vanishes. -/
private lemma integerTranslateCesaro_eq_zero_of_notMem_window {g : ℝ → ℝ} {a b x : ℝ} {n : ℕ}
    (ht : tsupport g ⊆ Set.Icc a b) (hx : x ∉ Set.Icc (a - n) b) :
    integerTranslateCesaro g n x = 0 := by
  -- Every translated sample lies outside `tsupport g`, so the finite sum is zero termwise.
  have hsum : ∀ k ∈ Finset.range (n + 1), g (x + k) = 0 := by
    intro k hk
    by_contra hgk
    have hk_mem : x + k ∈ tsupport g := by
      exact by_contra fun hxk ↦ hgk (image_eq_zero_of_notMem_tsupport hxk)
    have hkI : x + k ∈ Set.Icc a b := ht hk_mem
    have hk_le : (k : ℝ) ≤ n := by
      exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    have hxI : x ∈ Set.Icc (a - n) b := by
      refine ⟨?_, ?_⟩
      · by_contra hxleft
        have hxn : x + k ≤ x + n := by
          simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hk_le x
        linarith [hkI.1, hxn]
      · exact le_trans (le_add_of_nonneg_right hk_nonneg) hkI.2
    exact hx hxI
  have hsum' : Finset.sum (Finset.range (n + 1)) (fun k ↦ g (x + k)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    exact hsum k hk
  -- Route correction: keep the support bookkeeping at the pointwise level before passing to `Lp`.
  simp [integerTranslateCesaro, hsum']

/-- Helper for Exercise 7.1.3: the Cesàro average is pointwise bounded by the overlap count times
the uniform bound on `g`. -/
private lemma norm_integerTranslateCesaro_le_of_support {g : ℝ → ℝ} {a b C : ℝ} {N n : ℕ}
    (hC_nonneg : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) (hN_pos : 0 < N)
    (ht : tsupport g ⊆ Set.Icc a b) (hN : b - a < N) (x : ℝ) :
    ‖integerTranslateCesaro g n x‖ ≤ ((n + 1 : ℝ)⁻¹) * (N : ℝ) * C := by
  classical
  let s : Finset ℕ := (Finset.range (n + 1)).filter fun k : ℕ ↦ g (x + k) ≠ 0
  have hsum_le :
      Finset.sum (Finset.range (n + 1)) (fun k ↦ ‖g (x + k)‖) ≤ (N : ℝ) * C := by
    calc
      Finset.sum (Finset.range (n + 1)) (fun k ↦ ‖g (x + k)‖)
          = Finset.sum s (fun k ↦ ‖g (x + k)‖) := by
              dsimp [s]
              rw [← Finset.sum_filter_ne_zero]
              congr with k
              simp
      _ ≤ Finset.sum s (fun _k ↦ C) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact hC (x + k)
      _ = (s.card : ℝ) * C := by simp [s]
      _ ≤ (N : ℝ) * C := by
        gcongr
        exact card_nonzeroTranslateIndices_le hN_pos ht hN n
  -- Bound the average by the sum of norms, then use the overlap count.
  calc
    ‖integerTranslateCesaro g n x‖
        = ‖((n + 1 : ℝ)⁻¹) * Finset.sum (Finset.range (n + 1)) (fun k ↦ g (x + k))‖ := by
            simp [integerTranslateCesaro]
    _ = ‖((n + 1 : ℝ)⁻¹)‖ *
          ‖Finset.sum (Finset.range (n + 1)) (fun k ↦ g (x + k))‖ := by
      rw [norm_mul]
    _ ≤ ‖((n + 1 : ℝ)⁻¹)‖ *
          Finset.sum (Finset.range (n + 1)) (fun k ↦ ‖g (x + k)‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_sum_le (Finset.range (n + 1)) fun k ↦ g (x + k))
        (norm_nonneg _)
    _ = ((n + 1 : ℝ)⁻¹) *
          Finset.sum (Finset.range (n + 1)) (fun k ↦ ‖g (x + k)‖) := by
      rw [Real.norm_of_nonneg]
      positivity
    _ ≤ ((n + 1 : ℝ)⁻¹) * ((N : ℝ) * C) := by
      have hInv_nonneg : 0 ≤ (n + 1 : ℝ)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hsum_le hInv_nonneg
    _ = ((n + 1 : ℝ)⁻¹) * (N : ℝ) * C := by ring

/-- Helper for Exercise 7.1.3: the reciprocal exponent attached to `p` is nonnegative. -/
private lemma reciprocalExponent_nonneg {p : NNReal} [Fact (1 < p)] {q : ℝ}
    (hq : 1 / (p : ℝ≥0∞).toReal = q) :
    0 ≤ q := by
  -- Rewrite the exponent in the simpler real form `1 / p`.
  have hq' : q = 1 / (p : ℝ) := by
    simpa using hq.symm
  rw [hq']
  positivity

/-- Helper for Exercise 7.1.3: the reciprocal exponent attached to `p` is strictly smaller than
`1`. -/
private lemma reciprocalExponent_lt_one {p : NNReal} [Fact (1 < p)] {q : ℝ}
    (hq : 1 / (p : ℝ≥0∞).toReal = q) :
    q < 1 := by
  -- Rewrite the exponent in the simpler real form `1 / p` and use `p > 1`.
  have hq' : q = 1 / (p : ℝ) := by
    simpa using hq.symm
  have hp_real : (1 : ℝ) < p := by
    exact_mod_cast (Fact.out : (1 : NNReal) < p)
  rw [hq']
  simpa [one_div] using inv_lt_one_of_one_lt₀ hp_real

/-- Helper for Exercise 7.1.3: the compact-support argument first compares the Cesàro average to an
indicator-constant `Lp` element on one enlarged window. -/
private lemma integerTranslateCesaro_toLp_norm_le_indicatorWindow {p : NNReal} [Fact (1 < p)]
    {g : ℝ → ℝ} (hg : MemLp g (p : ℝ≥0∞) volume) {a b C : ℝ} {N n : ℕ}
    (hC_nonneg : 0 ≤ C) (hC : ∀ x, ‖g x‖ ≤ C) (hN_pos : 0 < N)
    (ht : tsupport g ⊆ Set.Icc a b) (hN : b - a < N) :
    ‖(integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)‖ ≤
      ‖indicatorConstLp (p : ℝ≥0∞) (μ := volume)
          (s := Set.Icc (b - ((N : ℝ) + n)) b) measurableSet_Icc measure_Icc_lt_top.ne
          (((n + 1 : ℝ)⁻¹) * (N : ℝ) * C)‖ := by
  let t : Set ℝ := Set.Icc (b - ((N : ℝ) + n)) b
  let c : ℝ := ((n + 1 : ℝ)⁻¹) * (N : ℝ) * C
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hwindow : Set.Icc (a - n) b ⊆ t := by
    intro x hx
    refine ⟨?_, hx.2⟩
    linarith [hN, hx.1]
  have hpoint :
      ∀ x, ‖integerTranslateCesaro g n x‖ ≤ ‖t.indicator (fun _ ↦ c) x‖ := by
    intro x
    by_cases hx : x ∈ t
    · -- On the window, the pointwise overlap-count estimate controls the Cesàro average.
      have hbound :=
        norm_integerTranslateCesaro_le_of_support (n := n) hC_nonneg hC hN_pos ht hN x
      have hc_norm : ‖c‖ = ((n + 1 : ℝ)⁻¹) * (N : ℝ) * C := by
        rw [Real.norm_of_nonneg hc_nonneg]
      simpa [t, c, hx, hc_norm] using hbound
    · -- Outside the window, every translated sample misses the support and the average vanishes.
      have hx' : x ∉ Set.Icc (a - n) b := by
        intro hxI
        exact hx (hwindow hxI)
      have hzero : integerTranslateCesaro g n x = 0 :=
        integerTranslateCesaro_eq_zero_of_notMem_window ht hx'
      simp [t, c, hx, hzero]
  have hpointLp :
      ∀ᵐ x ∂volume,
        ‖((integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)) x‖ ≤
          ‖(indicatorConstLp (p : ℝ≥0∞) (μ := volume) (s := t)
              measurableSet_Icc measure_Icc_lt_top.ne c) x‖ := by
    -- Pass the pointwise window bound to `Lp` using the canonical coercions.
    filter_upwards [(integerTranslateCesaro_memLp hg n).coeFn_toLp,
      (indicatorConstLp_coeFn (μ := volume) (p := (p : ℝ≥0∞)) (s := t)
        (hs := measurableSet_Icc) (hμs := measure_Icc_lt_top.ne) (c := c))] with x
        hx_toLp hx_indicator
    simpa [hx_toLp, hx_indicator] using hpoint x
  -- The `Lp` norm comparison is now a direct application of the pointwise domination.
  simpa [t, c] using (Lp.norm_le_norm_of_ae_le hpointLp)

/-- Helper for Exercise 7.1.3: the indicator-constant window has the expected polynomial-decay
`Lp` norm. -/
private lemma indicatorWindowNorm_le_rpowDecay {p : NNReal} [Fact (1 < p)] {q b C : ℝ}
    {N n : ℕ} (hq : 1 / (p : ℝ≥0∞).toReal = q) (hC_nonneg : 0 ≤ C) :
    ‖indicatorConstLp (p : ℝ≥0∞) (μ := volume)
        (s := Set.Icc (b - ((N : ℝ) + n)) b) measurableSet_Icc measure_Icc_lt_top.ne
        (((n + 1 : ℝ)⁻¹) * (N : ℝ) * C)‖ ≤
      ((N : ℝ) * C) * ((N + 1 : ℝ) ^ q) * ((n + 1 : ℝ) ^ (-(1 - q))) := by
  let t : Set ℝ := Set.Icc (b - ((N : ℝ) + n)) b
  let c : ℝ := ((n + 1 : ℝ)⁻¹) * (N : ℝ) * C
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hq_nonneg : 0 ≤ q := reciprocalExponent_nonneg (p := p) hq
  calc
    ‖indicatorConstLp (p : ℝ≥0∞) (μ := volume) (s := t) measurableSet_Icc
        measure_Icc_lt_top.ne c‖
        ≤ ‖c‖ * volume.real t ^ (1 / (p : ℝ≥0∞).toReal) := by
          simpa using
            (norm_indicatorConstLp_le (p := (p : ℝ≥0∞)) (s := t)
              (hs := measurableSet_Icc) (hμs := measure_Icc_lt_top.ne) (c := c))
    _ = c * volume.real t ^ q := by
      rw [Real.norm_of_nonneg hc_nonneg, hq]
    _ = c * ((N + n : ℝ) ^ q) := by
      have hle : b - ((N : ℝ) + n) ≤ b := by
        linarith
      have hvol : volume.real t = b - (b - ((N : ℝ) + n)) := by
        dsimp [t]
        simpa using Real.volume_real_Icc_of_le hle
      have hbase : b - (b - ((N : ℝ) + n)) = (N : ℝ) + n := by ring
      rw [hvol, hbase]
    _ ≤ c * (((N + 1 : ℝ) * (n + 1 : ℝ)) ^ q) := by
      -- Isolate the interval-length arithmetic from the `Lp` transport layer.
      refine mul_le_mul_of_nonneg_left ?_ hc_nonneg
      apply Real.rpow_le_rpow
      · positivity
      · nlinarith
      · exact hq_nonneg
    _ = ((N : ℝ) * C) * ((N + 1 : ℝ) ^ q) * ((n + 1 : ℝ) ^ (-(1 - q))) := by
      dsimp [c]
      have hNp : 0 ≤ (N + 1 : ℝ) := by positivity
      have hnp_nonneg : 0 ≤ (n + 1 : ℝ) := by positivity
      have hnp : 0 < (n + 1 : ℝ) := by positivity
      have hq_eq : q + (-1 : ℝ) = -(1 - q) := by ring
      have hInv : ((n + 1 : ℝ)⁻¹) = (n + 1 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
      rw [Real.mul_rpow hNp hnp_nonneg]
      calc
        (((n + 1 : ℝ)⁻¹ * (N : ℝ) * C) * ((N + 1 : ℝ) ^ q * (n + 1 : ℝ) ^ q))
            = (N : ℝ) * C * ((N + 1 : ℝ) ^ q) *
                (((n + 1 : ℝ)⁻¹) * (n + 1 : ℝ) ^ q) := by ring
        _ = (N : ℝ) * C * ((N + 1 : ℝ) ^ q) * ((n + 1 : ℝ) ^ (q + (-1 : ℝ))) := by
          have hpow :
              ((n + 1 : ℝ)⁻¹) * (n + 1 : ℝ) ^ q = (n + 1 : ℝ) ^ (q + (-1 : ℝ)) := by
            rw [mul_comm, hInv, ← Real.rpow_add hnp q (-1)]
          rw [hpow]
        _ = (N : ℝ) * C * ((N + 1 : ℝ) ^ q) * ((n + 1 : ℝ) ^ (-(1 - q))) := by
          rw [hq_eq]

/-- Helper for Exercise 7.1.3: compact support yields a uniform polynomial-decay majorant for the
Cesàro averages in `Lp`. -/
private lemma integerTranslateCesaro_norm_le_rpowDecay_of_hasCompactSupport {p : NNReal}
    [Fact (1 < p)] {q : ℝ} (hq : 1 / (p : ℝ≥0∞).toReal = q) {g : ℝ → ℝ}
    (hg : MemLp g (p : ℝ≥0∞) volume) (hgcomp : HasCompactSupport g) (hgcont : Continuous g) :
    ∃ K ≥ 0, ∀ n,
      ‖(integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)‖ ≤
        K * ((n + 1 : ℝ) ^ (-(1 - q))) := by
  let a : ℝ := sInf (tsupport g)
  let b : ℝ := sSup (tsupport g)
  have ht : tsupport g ⊆ Set.Icc a b := by
    -- Enclose the compact support in one closed interval once before estimating all Cesàro terms.
    simpa [a, b] using
      (hgcomp.isCompact.isBounded.subset_Icc_sInf_sSup :
        tsupport g ⊆ Set.Icc (sInf (tsupport g)) (sSup (tsupport g)))
  obtain ⟨M, hM⟩ : ∃ M : ℕ, b - a < M := exists_nat_gt (b - a)
  let N : ℕ := M + 1
  have hN_pos : 0 < N := by
    simp [N]
  have hM_succ : b - a < (M + 1 : ℝ) := by
    have hlt : (M : ℝ) < M + 1 := by
      exact_mod_cast Nat.lt_succ_self M
    linarith
  have hN : b - a < N := by
    simpa [N] using hM_succ
  obtain ⟨C, hC⟩ := hgcont.bounded_above_of_compact_support hgcomp
  have hC_nonneg : 0 ≤ C := le_trans (norm_nonneg (g 0)) (hC 0)
  let K : ℝ := ((N : ℝ) * C) * ((N + 1 : ℝ) ^ q)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  refine ⟨K, hK_nonneg, ?_⟩
  intro n
  calc
    ‖(integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)‖
        ≤ ‖indicatorConstLp (p : ℝ≥0∞) (μ := volume)
            (s := Set.Icc (b - ((N : ℝ) + n)) b) measurableSet_Icc measure_Icc_lt_top.ne
            (((n + 1 : ℝ)⁻¹) * (N : ℝ) * C)‖ := by
              exact integerTranslateCesaro_toLp_norm_le_indicatorWindow
                (hg := hg) hC_nonneg hC hN_pos ht hN
    _ ≤ ((N : ℝ) * C) * ((N + 1 : ℝ) ^ q) * ((n + 1 : ℝ) ^ (-(1 - q))) := by
      exact indicatorWindowNorm_le_rpowDecay (p := p) (q := q) (b := b) (C := C) (N := N)
        (n := n) hq hC_nonneg
    _ = K * ((n + 1 : ℝ) ^ (-(1 - q))) := by
      rfl

/-- Helper for Exercise 7.1.3: Cesàro averages of compactly supported continuous functions converge
to `0` in `Lp`. -/
private lemma integerTranslateCesaro_norm_tendsto_zero_of_hasCompactSupport {p : NNReal}
    [Fact (1 < p)] {g : ℝ → ℝ} (hg : MemLp g (p : ℝ≥0∞) volume)
    (hgcomp : HasCompactSupport g) (hgcont : Continuous g) :
    Tendsto (fun n ↦ ‖(integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)‖)
      atTop (𝓝 0) := by
  let q : ℝ := 1 / (p : ℝ)
  have hq : 1 / (p : ℝ≥0∞).toReal = q := by
    simp [q]
  have hq_lt_one : q < 1 := reciprocalExponent_lt_one (p := p) hq
  rcases integerTranslateCesaro_norm_le_rpowDecay_of_hasCompactSupport
      (p := p) (q := q) hq hg hgcomp hgcont with ⟨K, hK_nonneg, hK_bound⟩
  have hnat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    simpa using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))
  have hpow :
      Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-(1 - q))) atTop (𝓝 0) := by
    have hq_sub : 0 < 1 - q := by
      linarith
    simpa [Nat.cast_add] using (tendsto_rpow_neg_atTop hq_sub).comp hnat
  have hbound_tendsto :
      Tendsto (fun n : ℕ ↦ K * ((n + 1 : ℝ) ^ (-(1 - q)))) atTop (𝓝 0) := by
    -- Route correction: the final compact-support step is now only a squeeze against the packaged
    -- polynomial-decay majorant.
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto ?_ ?_
  · intro n
    exact norm_nonneg _
  · intro n
    exact hK_bound n

/-- Exercise 7.1.3: canonical `Lp`-valued form. For a finite exponent `p > 1`, if
`f ∈ ℒ^p(λ)` on `ℝ`, then the Cesàro averages of the integer translates `x ↦ f (x + k)`
converge to `0` in `Lp ℝ p volume`. -/
-- Proof sketch: view integer translation as a measure-preserving action on
-- `Lp ℝ p volume`, so each translate is an isometric copy of `f`. Prove the
-- claim first for compactly supported continuous functions, where the translates separate and the
-- averages vanish, then extend to general `MemLp` functions by density of nice functions in `L^p`.
theorem integer_translate_cesaro_tendsto_zero_inLp {p : NNReal} [Fact (1 < p)] {f : ℝ → ℝ}
    (hf : MemLp f (p : ℝ≥0∞) volume) :
    Tendsto
      (fun n ↦ (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n))
      atTop (𝓝 (0 : Lp ℝ (p : ℝ≥0∞) volume)) := by
  -- Approximate `f` by a compactly supported continuous function and transfer the decay through the
  -- `Lp` contraction of the Cesàro operator.
  rw [tendsto_def]
  intro s hs
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε_pos, hε_sub⟩
  have hε_half_pos : 0 < ε / 2 := by positivity
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hε_half_pos
  obtain ⟨g, hgcomp, hfg, hgcont, hg⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.coe_ne_top hε_half_ne
  let F : ℕ → Lp ℝ (p : ℝ≥0∞) volume := fun n ↦
    (integerTranslateCesaro_memLp hf n).toLp (integerTranslateCesaro f n)
  let G : ℕ → Lp ℝ (p : ℝ≥0∞) volume := fun n ↦
    (integerTranslateCesaro_memLp hg n).toLp (integerTranslateCesaro g n)
  have hcompact : Tendsto (fun n ↦ ‖G n‖) atTop (𝓝 0) := by
    simpa [G] using integerTranslateCesaro_norm_tendsto_zero_of_hasCompactSupport hg hgcomp hgcont
  have hcompact_eventually : ∀ᶠ n in atTop, ‖G n‖ < ε / 2 := by
    exact hcompact (Iio_mem_nhds hε_half_pos)
  have happrox :
      ∀ n, ‖F n - G n‖ ≤ ε / 2 := by
    intro n
    have hfgCesaro :
        eLpNorm (integerTranslateCesaro f n - integerTranslateCesaro g n) (p : ℝ≥0∞) volume ≤
          ENNReal.ofReal (ε / 2) := by
      exact (integerTranslateCesaro_eLpNorm_sub_le hf hg n).trans hfg
    have hmemDiff :
        MemLp (integerTranslateCesaro f n - integerTranslateCesaro g n) (p : ℝ≥0∞) volume := by
      exact (integerTranslateCesaro_memLp hf n).sub (integerTranslateCesaro_memLp hg n)
    have htoLp :
        hmemDiff.toLp (integerTranslateCesaro f n - integerTranslateCesaro g n) = F n - G n := by
      simpa [F, G] using
        (MemLp.toLp_sub (integerTranslateCesaro_memLp hf n) (integerTranslateCesaro_memLp hg n))
    have hnorm_le :
        ‖hmemDiff.toLp (integerTranslateCesaro f n - integerTranslateCesaro g n)‖ ≤ ε / 2 := by
      have hε_half_top : ENNReal.ofReal (ε / 2) ≠ ∞ := by
        simp
      have htoReal :
          (eLpNorm (integerTranslateCesaro f n - integerTranslateCesaro g n)
            (p : ℝ≥0∞) volume).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono hε_half_top hfgCesaro
      simpa [Lp.norm_toLp, hε_half_pos.le] using htoReal
    simpa [htoLp] using hnorm_le
  refine Filter.mem_atTop_sets.2 ?_
  obtain ⟨N, hN⟩ := Filter.mem_atTop_sets.1 hcompact_eventually
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnorm_lt : ‖F n‖ < ε := by
    calc
      ‖F n‖ = ‖(F n - G n) + G n‖ := by
        congr 1
        abel
      _ ≤ ‖F n - G n‖ + ‖G n‖ := norm_add_le _ _
      _ < ε / 2 + ε / 2 := by
        exact add_lt_add_of_le_of_lt (happrox n) (hN n hn)
      _ = ε := by ring
  have hball : F n ∈ Metric.ball 0 ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
  exact hε_sub hball

/-- The textbook `eLpNorm` formulation of Exercise 7.1.3 follows from the canonical `Lp`-valued
convergence statement via `MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm''`. -/
theorem integer_translate_cesaro_tendsto_zero_in_eLpNorm {p : ℝ} (hp : 1 < p) {f : ℝ → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun n ↦ eLpNorm (integerTranslateCesaro f n) (ENNReal.ofReal p) volume) atTop
      (𝓝 0) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp.le
  let p' : NNReal := ⟨p, hp0⟩
  have hp' : (p' : ℝ≥0∞) = ENNReal.ofReal p := by
    simpa using (ENNReal.ofReal_eq_coe_nnreal hp0).symm
  have hp'Fact : 1 < p' := by
    exact_mod_cast hp
  letI : Fact (1 < p') := ⟨hp'Fact⟩
  have hf' : MemLp f (p' : ℝ≥0∞) volume := by
    simpa [hp'] using hf
  have hCesaroMemLp : ∀ n, MemLp (integerTranslateCesaro f n) (p' : ℝ≥0∞) volume :=
    integerTranslateCesaro_memLp hf'
  simpa [hp'] using
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n ↦ integerTranslateCesaro f n) hCesaroMemLp 0
      MemLp.zero).mp (integer_translate_cesaro_tendsto_zero_inLp hf')
