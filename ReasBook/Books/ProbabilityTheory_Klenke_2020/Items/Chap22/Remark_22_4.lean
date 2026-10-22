/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Corollary_22_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "halfHolderExponent" => ((1 : ℝ≥0) / 2)
local notation "PathSpace" => C(NNReal, ℝ)

/-- Lévy's modulus of continuity `h(δ) = sqrt(2 δ log (1 / δ))` on positive time scales. -/
def levyModulusOfContinuity (δ : NNReal) : ℝ :=
  Real.sqrt (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ)))

/-- Expanding `levyModulusOfContinuity` gives the formula `sqrt(2 δ log (1 / δ))`. -/
theorem levyModulusOfContinuity_eq (δ : NNReal) :
    levyModulusOfContinuity δ =
      Real.sqrt (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ))) :=
  rfl

/-- Helper for Remark 22.4: at the dyadic mesh `δ = 2^{-n}`, Lévy's modulus becomes the canonical
Gaussian tail scale `sqrt(2 * 2^{-n} * n * log 2)`. -/
lemma levyModulusOfContinuity_dyadic (n : ℕ) :
    levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) =
      Real.sqrt (2 * (((2 : ℝ)⁻¹) ^ n) * ((n : ℝ) * Real.log 2)) := by
  -- Proof comment: rewrite the dyadic scale from `NNReal` to `ℝ`, then evaluate
  -- `log ((2⁻¹)⁻ⁿ)` as `n * log 2`.
  rw [levyModulusOfContinuity_eq]
  have hcoe :
      ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) = (((2 : ℝ)⁻¹) ^ n) := by
    norm_num [NNReal.coe_pow]
  rw [hcoe]
  rw [one_div, inv_pow, inv_inv, Real.log_pow]

/-- Helper for Remark 22.4: the admissible oscillation values on `[0, N]` at mesh `δ` for a
Brownian path. -/
def compactIntervalOscillationValues
    (N : ℕ) (ω : PathSpace) (δ : NNReal) : Set NNReal :=
  {r | ∃ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) t ≤ δ ∧ r = ‖ω s - ω t‖₊}

/-- Helper for Remark 22.4: the maximal oscillation of one Brownian path on `[0, N]` at mesh
`δ`. -/
def compactIntervalOscillation
    (N : ℕ) (ω : PathSpace) (δ : NNReal) : NNReal :=
  sSup (compactIntervalOscillationValues N ω δ)

/-- Helper for Remark 22.4: every admissible pair on `[0, N]` contributes its oscillation value to
the compact-interval oscillation value set. -/
lemma mem_compactIntervalOscillationValues
    (N : ℕ) (ω : PathSpace) (δ : NNReal)
    (s t : Set.Icc (0 : NNReal) N) (hst : dist (s : NNReal) t ≤ δ) :
    ‖ω s - ω t‖₊ ∈ compactIntervalOscillationValues N ω δ := by
  -- Proof comment: unfold the defining existential and package the chosen admissible pair.
  exact ⟨s, t, hst, rfl⟩

/-- Helper for Remark 22.4: the admissible oscillation values at fixed mesh form a bounded-above
set, so their supremum is a genuine finite oscillation bound. -/
lemma compactIntervalOscillationValues_bddAbove
    (N : ℕ) (ω : PathSpace) (δ : NNReal) :
    BddAbove (compactIntervalOscillationValues N ω δ) := by
  let admissiblePairs : Set (Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N) :=
    {p | dist (p.1 : NNReal) p.2 ≤ δ}
  let oscillationValue : Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N → NNReal :=
    fun p ↦ ‖ω p.1 - ω p.2‖₊
  have hClosedPairs : IsClosed admissiblePairs := by
    -- Proof comment: the mesh constraint is the inverse image of the closed ray `(-∞, δ]`.
    have hDistCont :
        Continuous fun p : Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N ↦
          dist (p.1 : NNReal) p.2 :=
      continuous_fst.subtype_val.dist continuous_snd.subtype_val
    simpa [admissiblePairs] using isClosed_le hDistCont continuous_const
  have hCompactPairs : IsCompact admissiblePairs := by
    -- Proof comment: the admissible-pair set is closed inside the compact square interval.
    simpa [admissiblePairs] using
      (isCompact_univ : IsCompact
        (Set.univ : Set (Set.Icc (0 : NNReal) N × Set.Icc (0 : NNReal) N))).inter_right
        hClosedPairs
  have hCompactImage : IsCompact (oscillationValue '' admissiblePairs) := by
    -- Proof comment: continuous images of compact sets stay compact.
    refine hCompactPairs.image ?_
    continuity
  have hImageEq :
      oscillationValue '' admissiblePairs = compactIntervalOscillationValues N ω δ := by
    ext r
    constructor
    · rintro ⟨⟨s, t⟩, hp, rfl⟩
      exact ⟨s, t, hp, rfl⟩
    · rintro ⟨s, t, hst, rfl⟩
      exact ⟨⟨s, t⟩, hst, rfl⟩
  simpa [hImageEq] using hCompactImage.bddAbove

/-- Helper for Remark 22.4: a pointwise oscillation bound on all admissible pairs bounds the
compact-interval oscillation supremum. -/
lemma compactIntervalOscillation_le_of_forall
    (N : ℕ) (ω : PathSpace) (δ η : NNReal)
    (hη : ∀ s t : Set.Icc (0 : NNReal) N, dist (s : NNReal) t ≤ δ → ‖ω s - ω t‖₊ ≤ η) :
    compactIntervalOscillation N ω δ ≤ η := by
  -- Proof comment: each admissible oscillation value lies below `η`, so the supremum does too.
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    exact ⟨⟨0, by simp⟩, ⟨0, by simp⟩, by simp, by simp⟩
  · intro r hr
    rcases hr with ⟨s, t, hst, rfl⟩
    exact hη s t hst

/-- Helper for Remark 22.4: every admissible increment on `[0, N]` is dominated by the maximal
oscillation at the same mesh. -/
lemma nnnorm_sub_le_compactIntervalOscillation
    (N : ℕ) (ω : PathSpace) (δ : NNReal)
    (s t : Set.Icc (0 : NNReal) N) (hst : dist (s : NNReal) t ≤ δ) :
    ‖ω s - ω t‖₊ ≤ compactIntervalOscillation N ω δ := by
  -- Proof comment: the chosen increment is one of the values entering the oscillation supremum.
  refine le_csSup (compactIntervalOscillationValues_bddAbove N ω δ) ?_
  exact mem_compactIntervalOscillationValues N ω δ s t hst

/-- Helper for Remark 22.4: enlarging the mesh parameter can only enlarge the compact-interval
oscillation. -/
lemma compactIntervalOscillation_mono
    (N : ℕ) (ω : PathSpace) {δ₁ δ₂ : NNReal} (hδ : δ₁ ≤ δ₂) :
    compactIntervalOscillation N ω δ₁ ≤ compactIntervalOscillation N ω δ₂ := by
  -- Proof comment: every pair admissible at mesh `δ₁` remains admissible at the larger mesh
  -- `δ₂`, so the corresponding supremum is monotone in the mesh size.
  refine
    compactIntervalOscillation_le_of_forall N ω δ₁ (compactIntervalOscillation N ω δ₂) ?_
  intro s t hst
  exact nnnorm_sub_le_compactIntervalOscillation N ω δ₂ s t (le_trans hst hδ)

/-- Helper for Remark 22.4: the refined dyadic scale factor `((2^r + 2) / 2^r)` is at least `1`.
-/
lemma one_le_refinedDyadicScaleFactor (r : ℕ) :
    (1 : NNReal) ≤ (((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) := by
  have hpow_pos : (0 : NNReal) < (2 : NNReal) ^ r := by
    positivity
  refine (le_div_iff₀ hpow_pos).2 ?_
  have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
    norm_num
  rw [hpow_cast]
  have hNat : (1 : ℕ) * 2 ^ r ≤ 2 ^ r + 2 := by
    nlinarith
  exact_mod_cast hNat

/-- Helper for Remark 22.4: the refined dyadic scale factor `((2^r + 2) / 2^r)` is uniformly
bounded by `3`. -/
lemma refinedDyadicScaleFactor_le_three (r : ℕ) :
    (((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) ≤ 3 := by
  have hpow_pos : (0 : NNReal) < (2 : NNReal) ^ r := by
    positivity
  refine (div_le_iff₀ hpow_pos).2 ?_
  have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
    norm_num
  rw [hpow_cast]
  have hpow_nat_pos : 1 ≤ 2 ^ r := by
    exact Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hNat : (2 ^ r + 2 : ℕ) ≤ 3 * 2 ^ r := by
    nlinarith
  exact_mod_cast hNat

/-- Helper for Remark 22.4: once the mesh is at most `2^{-n}`, monotonicity already transports the
oscillation to the slightly larger refined dyadic horizon `((2^r + 2) / 2^r) * 2^{-n}`. -/
lemma compactIntervalOscillation_le_refinedDyadicScale
    (ω : PathSpace) (r n : ℕ) {δ : NNReal}
    (hδ : δ ≤ ((2 : NNReal)⁻¹) ^ n) :
    compactIntervalOscillation 1 ω δ ≤
      compactIntervalOscillation 1 ω
        ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)) := by
  have hscale :
      ((2 : NNReal)⁻¹) ^ n ≤
        (((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n) := by
    have hx_nonneg : 0 ≤ (((2 : NNReal)⁻¹) ^ n) := by
      positivity
    calc
      ((2 : NNReal)⁻¹) ^ n = (1 : NNReal) * (((2 : NNReal)⁻¹) ^ n) := by simp
      _ ≤ (((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n) := by
          exact mul_le_mul_of_nonneg_right (one_le_refinedDyadicScaleFactor r) hx_nonneg
  exact compactIntervalOscillation_mono 1 ω (le_trans hδ hscale)

/-- Helper for Remark 22.4: `dyadicWindowMax ω n J` is the maximal forward oscillation of `ω`
along the row-`n` dyadic mesh using at most `J` consecutive mesh steps. -/
def dyadicWindowMax (ω : PathSpace) (n J : ℕ) : NNReal :=
  (Finset.range (2 ^ n + 1)).sup fun i ↦
    (Finset.Icc 1 (min J (2 ^ n - i))).sup fun j ↦
      ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
        ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊

/-- Helper for Remark 22.4: every admissible forward dyadic window contributes its oscillation to
the finite supremum `dyadicWindowMax`. -/
lemma nnnorm_sub_le_dyadicWindowMax
    (ω : PathSpace) (n J i j : ℕ)
    (hj₁ : 1 ≤ j) (hjJ : j ≤ J) (hij : i + j ≤ 2 ^ n) :
    ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
        ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ ≤
      dyadicWindowMax ω n J := by
  -- Proof comment: realize the chosen window by its start index `i` and window length `j`
  -- inside the nested finite suprema defining `dyadicWindowMax`.
  dsimp [dyadicWindowMax]
  have hi : i ≤ 2 ^ n := by
    omega
  have hmemi : i ∈ Finset.range (2 ^ n + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
  have hjGrid : j ≤ 2 ^ n - i := by
    omega
  have hmemj : j ∈ Finset.Icc 1 (min J (2 ^ n - i)) := by
    exact Finset.mem_Icc.mpr ⟨hj₁, le_min hjJ hjGrid⟩
  have hInner :
      ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
          ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ ≤
        (Finset.Icc 1 (min J (2 ^ n - i))).sup fun j ↦
          ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
              ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ := by
    exact
      Finset.le_sup
        (f := fun j ↦
          ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
              ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊)
        hmemj
  have hOuter :
      (Finset.Icc 1 (min J (2 ^ n - i))).sup
          (fun j ↦
            ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
                ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊) ≤
        (Finset.range (2 ^ n + 1)).sup
          (fun i ↦
            (Finset.Icc 1 (min J (2 ^ n - i))).sup
              (fun j ↦
                ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
                    ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊)) := by
    exact
      Finset.le_sup
        (f := fun i ↦
          (Finset.Icc 1 (min J (2 ^ n - i))).sup
            (fun j ↦
              ‖ω (((i + j : ℕ) : NNReal) / (2 : NNReal) ^ n) -
                  ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊))
        hmemi
  exact le_trans hInner hOuter

/-- Helper for Remark 22.4: adjacent row-`n` dyadic increments are controlled by the one-step
window maximum `dyadicWindowMax ω n 1`. -/
lemma nnnorm_sub_le_dyadicWindowMax_one
    (ω : PathSpace) (n i : ℕ) (hi : i + 1 ≤ 2 ^ n) :
    ‖ω (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) -
        ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ ≤
      dyadicWindowMax ω n 1 := by
  -- Proof comment: this is the special case `j = 1` of the general dyadic-window bound.
  simpa using
    nnnorm_sub_le_dyadicWindowMax (ω := ω) (n := n) (J := 1) (i := i) (j := 1)
      (by simp) (by simp) hi

/-- Helper for Remark 22.4: the one-step dyadic window maximum is bounded by the compact-interval
oscillation at the matching dyadic mesh. -/
lemma dyadicWindowMax_one_le_compactIntervalOscillation
    (ω : PathSpace) (n : ℕ) :
    dyadicWindowMax ω n 1 ≤ compactIntervalOscillation 1 ω (((2 : NNReal)⁻¹) ^ n) := by
  classical
  -- Proof comment: every nonempty inner supremum in `dyadicWindowMax ω n 1` consists of the
  -- adjacent increment from `i / 2^n` to `(i + 1) / 2^n`, and that increment is admissible for
  -- the compact-interval oscillation at mesh `2^{-n}`.
  dsimp [dyadicWindowMax]
  refine Finset.sup_le ?_
  intro i hi
  refine Finset.sup_le ?_
  intro j hj
  rcases Finset.mem_Icc.mp hj with ⟨hj1, hjmax⟩
  have hj : j = 1 := by
    omega
  subst hj
  have hi_step : i + 1 ≤ 2 ^ n := by
    have : 1 ≤ min 1 (2 ^ n - i) := by simpa using hjmax
    have hgrid : 1 ≤ 2 ^ n - i := le_trans this (Nat.min_le_right _ _)
    omega
  have hi_le : i ≤ 2 ^ n := by
    omega
  have hpow_pos : (0 : NNReal) < (2 : NNReal) ^ n := by
    positivity
  let s : Set.Icc (0 : NNReal) (1 : ℕ) :=
    ⟨(i : NNReal) / (2 : NNReal) ^ n, by
      constructor
      · positivity
      ·
        have hi_nn : (i : NNReal) ≤ (2 : NNReal) ^ n := by
          exact_mod_cast hi_le
        exact (div_le_iff₀ hpow_pos).2 (by simpa [one_mul] using hi_nn)⟩
  let t : Set.Icc (0 : NNReal) (1 : ℕ) :=
    ⟨((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n, by
      constructor
      · positivity
      ·
        have hi_step_nn : ((i + 1 : ℕ) : NNReal) ≤ (2 : NNReal) ^ n := by
          exact_mod_cast hi_step
        exact (div_le_iff₀ hpow_pos).2 (by simpa [one_mul] using hi_step_nn)⟩
  have hst_le : (s : NNReal) ≤ t := by
    dsimp [s, t]
    exact (div_le_div_iff_of_pos_right hpow_pos).2 (by exact_mod_cast Nat.le_succ i)
  have hdist :
      dist (t : NNReal) s ≤ (((2 : NNReal)⁻¹) ^ n : NNReal) := by
    have hsub_nonneg : 0 ≤ ((t : NNReal) : ℝ) - s := by
      exact sub_nonneg.mpr hst_le
    have hdist_eq :
        dist (t : NNReal) s = (1 : NNReal) / (2 : NNReal) ^ n := by
      -- Proof comment: for adjacent dyadic points the distance is exactly one mesh step.
      rw [NNReal.dist_eq, abs_of_nonneg hsub_nonneg]
      norm_num [s, t, NNReal.coe_div, NNReal.coe_pow]
      field_simp
      ring
    simpa [one_div, div_eq_mul_inv] using hdist_eq.le
  exact nnnorm_sub_le_compactIntervalOscillation
    1 ω (((2 : NNReal)⁻¹) ^ n) t s hdist

/-- Helper for Remark 22.4: a refined upper bad row records one anchored dyadic window on row
`n + r` whose oscillation above the left endpoint exceeds the target upper envelope `α * h(·)`. -/
def refinedUpperBadRow
    (B : NNReal → Ω → ℝ) (α : ℝ) (r n : ℕ) : Set Ω :=
  {ω | ∃ i J : ℕ,
      i + J ≤ 2 ^ (n + r) ∧
      1 ≤ J ∧
      J ≤ 2 ^ r + 2 ∧
      ∃ t : NNReal,
        t ∈
            Set.Icc
              ((i : NNReal) / (2 : NNReal) ^ (n + r))
              (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ (n + r)) ∧
          α * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
            |B t ω - B ((i : NNReal) / (2 : NNReal) ^ (n + r)) ω|}

/-- Helper for Remark 22.4: any explicit anchored-window oscillation witness puts the sample point
into the corresponding refined upper bad row. -/
lemma mem_refinedUpperBadRow_of_exists_anchoredWindow
    {B : NNReal → Ω → ℝ} {α : ℝ} {r n i J : ℕ} {ω : Ω} {t : NNReal}
    (hij : i + J ≤ 2 ^ (n + r))
    (hJ1 : 1 ≤ J)
    (hJr : J ≤ 2 ^ r + 2)
    (ht :
      t ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ (n + r))
          (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ (n + r)))
    (hbad :
      α * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
        |B t ω - B ((i : NNReal) / (2 : NNReal) ^ (n + r)) ω|) :
    ω ∈ refinedUpperBadRow B α r n := by
  -- Proof comment: unfold the bad-row event and package the chosen dyadic anchor, window length,
  -- and witness time `t`.
  exact ⟨i, J, hij, hJ1, hJr, t, ht, hbad⟩

/-- Helper for Remark 22.4: a dyadic row hit is a positive one-step increment exceeding the lower
envelope `β * h(2^{-n})`. -/
def dyadicRowHit
    (B : NNReal → Ω → ℝ) (β : ℝ) (n i : ℕ) : Set Ω :=
  {ω | β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
      B (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) ω -
        B ((i : NNReal) / (2 : NNReal) ^ n) ω}

/-- Helper for Remark 22.4: a dyadic row failure means that none of the `2^n` adjacent increments
on row `n` realizes the lower envelope. -/
def dyadicRowFailure
    (B : NNReal → Ω → ℝ) (β : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ i < 2 ^ n, ω ∉ dyadicRowHit B β n i}

/-- Helper for Remark 22.4: leaving the dyadic row-failure event means that some row-`n`
adjacent increment realizes the lower envelope. -/
lemma notMem_dyadicRowFailure_iff
    {B : NNReal → Ω → ℝ} {β : ℝ} {n : ℕ} {ω : Ω} :
    ω ∉ dyadicRowFailure B β n ↔ ∃ i < 2 ^ n, ω ∈ dyadicRowHit B β n i := by
  -- Proof comment: negating the universal definition of `dyadicRowFailure` produces exactly one
  -- successful dyadic hit on the same row.
  simp [dyadicRowFailure]

/-- Helper for Remark 22.4: a path `ω : PathSpace` satisfies Lévy's modulus law on `[0,1]` when
its compact-interval oscillation has limsup `1` after division by `h(δ)`. -/
def hasUnitIntervalLevyModulusLimsup (ω : PathSpace) : Prop :=
  limsup
      (fun δ : NNReal ↦
        compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
      (𝓝[>] (0 : NNReal)) = 1

/-- Helper for Remark 22.4: reciprocal-gap bounds on the compact-interval oscillation ratio force
the pathwise Lévy modulus limsup to equal `1`. -/
lemma hasUnitIntervalLevyModulusLimsup_of_forall_invSucc_bounds
    (ω : PathSpace)
    (hupper : ∀ m : ℕ,
      limsup
          (fun δ : NNReal ↦
            compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
          (𝓝[>] (0 : NNReal))
        ≤ 1 + 1 / (m + 1 : ℝ))
    (hlower : ∀ m : ℕ,
      1 - 1 / (m + 1 : ℝ) ≤
        limsup
          (fun δ : NNReal ↦
            compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
          (𝓝[>] (0 : NNReal))) :
    hasUnitIntervalLevyModulusLimsup ω := by
  -- Proof comment: the deterministic squeeze from Theorem 22.1 applies verbatim to the
  -- compact-interval oscillation ratio once both reciprocal approximation families are available.
  unfold hasUnitIntervalLevyModulusLimsup
  exact IsBrownianMotion.eq_one_of_forall_invSucc_bounds hupper hlower

/-- Helper for Remark 22.4: Lévy's modulus is strictly positive on sufficiently small positive
time scales. -/
lemma eventually_pos_levyModulusOfContinuity :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < levyModulusOfContinuity δ := by
  have hlt_one : {δ : NNReal | δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hlt_one] with δ hδ0 hδ1
  rw [levyModulusOfContinuity_eq]
  apply Real.sqrt_pos.2
  have hδ0' : 0 < (δ : ℝ) := by
    exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by
    exact_mod_cast hδ1
  have hlog : 0 < Real.log (1 / (δ : ℝ)) := by
    have hinv : 1 < (δ : ℝ)⁻¹ := by
      exact (one_lt_inv₀ hδ0').2 hδ1'
    simpa [one_div] using Real.log_pos hinv
  positivity

/-- Helper for Remark 22.4: the dyadic Lévy modulus is positive on every nontrivial dyadic row. -/
lemma levyModulusOfContinuity_dyadic_pos {n : ℕ} (hn : 1 ≤ n) :
    0 < levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) := by
  rw [levyModulusOfContinuity_dyadic]
  apply Real.sqrt_pos.2
  have hpow : 0 < (((2 : ℝ)⁻¹) ^ n) := by
    positivity
  have hn' : 0 < (n : ℝ) := by
    positivity
  have hlog_two : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos (by norm_num)
  positivity

/-- Helper for Remark 22.4: the dyadic mesh `2^{-n}` tends to `0` through positive values. -/
lemma tendsto_dyadicScales_nhdsGT_zero :
    Tendsto (fun n : ℕ ↦ ((2 : NNReal)⁻¹) ^ n) atTop (𝓝[>] (0 : NNReal)) := by
  exact tendsto_pow_atTop_nhdsWithin_zero_of_lt_one (by positivity) (by norm_num)

/-- Helper for Remark 22.4: summable real event masses imply almost-sure eventual avoidance by the
first Borel--Cantelli lemma. -/
lemma ae_eventually_notMem_of_summable_measureReal
    (μ : Measure Ω) [IsProbabilityMeasure μ] {s : ℕ → Set Ω}
    (hs : Summable (fun n : ℕ ↦ μ.real (s n))) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in atTop, ω ∉ s n := by
  have htsum : (∑' n, μ (s n)) ≠ ⊤ := by
    -- Proof comment: summability of the real masses lifts directly to finiteness of the ENNReal
    -- series used by `MeasureTheory.ae_eventually_notMem`.
    simpa [MeasureTheory.Measure.real_def] using hs.tsum_ofReal_ne_top
  exact MeasureTheory.ae_eventually_notMem htsum

/-- Helper for Remark 22.4: the product bound `(1 - p)^m ≤ exp (-(m : ℝ) * p)` packages the
repeated complement-to-exponential compression used in the lower row estimates. -/
lemma one_sub_pow_le_exp_neg_mul
    {p : ℝ} (hp1 : p ≤ 1) (m : ℕ) :
    (1 - p) ^ m ≤ Real.exp (-(m : ℝ) * p) := by
  have hbase_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hbase :
      1 - p ≤ Real.exp (-p) := by
    simpa [sub_eq_add_neg] using Real.one_sub_le_exp_neg p
  have hpow :
      (1 - p) ^ m ≤ (Real.exp (-p)) ^ m := by
    -- Proof comment: once the one-step complement factor is bounded by `exp (-p)`, monotonicity
    -- of `x ↦ x^m` on the nonnegative reals upgrades it to the full row product.
    exact pow_le_pow_left₀ hbase_nonneg hbase m
  calc
    (1 - p) ^ m ≤ (Real.exp (-p)) ^ m := hpow
    _ = Real.exp ((m : ℝ) * (-p)) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (-(m : ℝ) * p) := by ring_nf

/-- Helper for Remark 22.4: if the dilation factor `c` stays below `α²`, then on small enough
scales the Lévy modulus at `c * δ` is bounded by `α` times the original one. -/
lemma levyModulus_mul_le_of_factor_sqBound
    {α : ℝ} {c δ : NNReal}
    (hα : 1 < α) (hc1 : 1 ≤ c) (hcα : (c : ℝ) ≤ α ^ (2 : ℕ))
    (hδ : 0 < δ) (hcδ1 : c * δ < 1) :
    levyModulusOfContinuity (c * δ) ≤ α * levyModulusOfContinuity δ := by
  have hα0 : 0 < α := lt_trans zero_lt_one hα
  have hc_pos : 0 < (c : ℝ) := lt_of_lt_of_le zero_lt_one hc1
  have hδ_pos : 0 < (δ : ℝ) := by
    exact_mod_cast hδ
  have hδ_le_cδ : δ ≤ c * δ := by
    have hδ_nonneg : 0 ≤ δ := by
      positivity
    simpa [one_mul] using mul_le_mul_of_nonneg_right hc1 hδ_nonneg
  have hδ_lt_one : δ < 1 := lt_of_le_of_lt hδ_le_cδ hcδ1
  have hδ_real_lt_one : (δ : ℝ) < 1 := by
    exact_mod_cast hδ_lt_one
  have hlogδ_pos : 0 < Real.log (1 / (δ : ℝ)) := by
    have hinv : 1 < (δ : ℝ)⁻¹ := by
      exact (one_lt_inv₀ hδ_pos).2 hδ_real_lt_one
    simpa [one_div] using Real.log_pos hinv
  have hlogc_nonneg : 0 ≤ Real.log (c : ℝ) := by
    exact Real.log_nonneg hc1
  have hlog_mul :
      Real.log (1 / ((c : ℝ) * (δ : ℝ))) = Real.log (1 / (δ : ℝ)) - Real.log (c : ℝ) := by
    -- Proof comment: rewrite the larger scale as the positive product `c * δ` and split the
    -- logarithm across that product.
    rw [one_div, Real.log_inv, Real.log_mul hc_pos.ne' hδ_pos.ne', one_div, Real.log_inv]
    ring
  have hinside_le :
      2 * (((c * δ : NNReal) : ℝ)) * Real.log (1 / (((c * δ : NNReal) : ℝ))) ≤
        α ^ (2 : ℕ) * (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ))) := by
    have hcore :
        (c : ℝ) * Real.log (1 / (δ : ℝ)) - (c : ℝ) * Real.log (c : ℝ) ≤
          α ^ (2 : ℕ) * Real.log (1 / (δ : ℝ)) := by
      have hdrop :
          (c : ℝ) * Real.log (1 / (δ : ℝ)) - (c : ℝ) * Real.log (c : ℝ) ≤
            (c : ℝ) * Real.log (1 / (δ : ℝ)) := by
        nlinarith
      have hscale :
          (c : ℝ) * Real.log (1 / (δ : ℝ)) ≤
            α ^ (2 : ℕ) * Real.log (1 / (δ : ℝ)) := by
        gcongr
      exact hdrop.trans hscale
    -- Proof comment: after expanding `log (1 / (c * δ))`, drop the nonpositive correction
    -- `- c * log c` and then use the square-factor bound `c ≤ α²`.
    calc
      2 * (((c * δ : NNReal) : ℝ)) * Real.log (1 / (((c * δ : NNReal) : ℝ)))
          = 2 * ((c : ℝ) * (δ : ℝ)) * Real.log (1 / ((c : ℝ) * (δ : ℝ))) := by
                simp
      _ =
          2 * (δ : ℝ) *
            ((c : ℝ) * Real.log (1 / (δ : ℝ)) - (c : ℝ) * Real.log (c : ℝ)) := by
                rw [hlog_mul]
                ring
      _ ≤ 2 * (δ : ℝ) * (α ^ (2 : ℕ) * Real.log (1 / (δ : ℝ))) := by
            gcongr
      _ = α ^ (2 : ℕ) * (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ))) := by
            ring
  have hinner_nonneg : 0 ≤ 2 * (δ : ℝ) * Real.log (1 / (δ : ℝ)) := by
    have htwoδ_nonneg : 0 ≤ 2 * (δ : ℝ) := by
      positivity
    exact mul_nonneg htwoδ_nonneg hlogδ_pos.le
  have hsqrt_eq :
      Real.sqrt (α ^ (2 : ℕ) * (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ)))) =
        α * levyModulusOfContinuity δ := by
    rw [levyModulusOfContinuity_eq,
      (Real.sqrt_mul (show 0 ≤ α ^ (2 : ℕ) by positivity)),
      Real.sqrt_sq_eq_abs, abs_of_pos hα0]
  calc
    levyModulusOfContinuity (c * δ)
        = Real.sqrt
            (2 * (((c * δ : NNReal) : ℝ)) * Real.log (1 / (((c * δ : NNReal) : ℝ)))) := by
              rw [levyModulusOfContinuity_eq]
    _ ≤ Real.sqrt (α ^ (2 : ℕ) * (2 * (δ : ℝ) * Real.log (1 / (δ : ℝ)))) := by
          exact Real.sqrt_le_sqrt hinside_le
    _ = α * levyModulusOfContinuity δ := hsqrt_eq

/-- Helper for Remark 22.4: some refined dyadic dilation factor is eventually small enough to sit
below the target square `α²`. -/
lemma exists_refinedDyadicScaleFactor_lt_sq {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ,
      ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r : NNReal) : ℝ) < α ^ (2 : ℕ) := by
  have hgap : 0 < α ^ (2 : ℕ) - 1 := by
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hgap
  refine ⟨N + 1, ?_⟩
  have hpow_ge : (N + 1 : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast Nat.succ_le_of_lt N.lt_two_pow_self
  have hpow_pos : 0 < (2 : ℝ) ^ N := by
    positivity
  have hInv_le : 1 / (2 : ℝ) ^ N ≤ 1 / (N + 1 : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hpow_ge
  have hfactor_eq :
      ((((2 ^ (N + 1) + 2 : ℕ) : NNReal) / (2 : NNReal) ^ (N + 1) : NNReal) : ℝ) =
        1 + 1 / (2 : ℝ) ^ N := by
    -- Proof comment: expand the refined factor and cancel one power of `2`.
    norm_num [NNReal.coe_div, NNReal.coe_pow]
    field_simp [show (2 : ℝ) ^ N ≠ 0 by positivity]
    ring
  have hsmall : 1 / (2 : ℝ) ^ N < α ^ (2 : ℕ) - 1 := lt_of_le_of_lt hInv_le hN
  rw [hfactor_eq]
  linarith

/-- Helper for Remark 22.4: for every `α > 1`, one refined dyadic factor makes the Lévy modulus
stable under dilation by that factor on sufficiently small scales. -/
lemma eventually_levyModulus_refinedFactor_le_mul
    {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ, ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      levyModulusOfContinuity ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) ≤
        α * levyModulusOfContinuity δ := by
  rcases exists_refinedDyadicScaleFactor_lt_sq hα with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  let c : NNReal := (((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r)
  have hc1 : 1 ≤ c := one_le_refinedDyadicScaleFactor r
  have hcα : (c : ℝ) ≤ α ^ (2 : ℕ) := le_of_lt hr
  have hsmall :
      {δ : NNReal | c * δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    have hcont : Continuous fun δ : NNReal ↦ c * δ := continuous_const.mul continuous_id
    exact mem_nhdsWithin_of_mem_nhds <|
      hcont.continuousAt.preimage_mem_nhds <|
        Iio_mem_nhds (by
          have hzero : c * (0 : NNReal) < 1 := by simp [c]
          simpa using hzero)
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
  exact levyModulus_mul_le_of_factor_sqBound hα hc1 hcα hδ hδsmall

/-- Helper for Remark 22.4: once reciprocal-gap upper and lower envelopes are available on the
pathwise oscillation and the dyadic one-step windows, the deterministic squeeze identifies the
Lévy modulus limsup. -/
lemma hasUnitIntervalLevyModulusLimsup_of_sandwichFamilies
    (ω : PathSpace)
    (hUpper : ∀ m : ℕ, ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      ((compactIntervalOscillation 1 ω δ : NNReal) : ℝ) ≤
        (1 + 1 / (m + 1 : ℝ)) * levyModulusOfContinuity δ)
    (hLower : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop,
      (1 - 1 / (m + 1 : ℝ)) * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
        (dyadicWindowMax ω n 1 : ℝ)) :
    hasUnitIntervalLevyModulusLimsup ω := by
  let ratio : NNReal → ℝ := fun δ ↦
    ((compactIntervalOscillation 1 ω δ : NNReal) : ℝ) / levyModulusOfContinuity δ
  have hRatioNonneg :
      ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 ≤ ratio δ := by
    filter_upwards [eventually_pos_levyModulusOfContinuity] with δ hlevy
    have hOsc : 0 ≤ ((compactIntervalOscillation 1 ω δ : NNReal) : ℝ) := by
      positivity
    exact div_nonneg hOsc hlevy.le
  have hRatioCobounded :
      (𝓝[>] (0 : NNReal)).IsCoboundedUnder (· ≤ ·) ratio := by
    apply IsCoboundedUnder.of_frequently_ge (a := 0)
    exact hRatioNonneg.frequently
  have hRatioEventuallyLeTwo :
      ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), ratio δ ≤ 2 := by
    filter_upwards [hUpper 0, eventually_pos_levyModulusOfContinuity] with δ hδ hlevy
    have hTwo : ratio δ ≤ 1 + 1 := by
      simpa [ratio] using (div_le_iff₀ hlevy).2 hδ
    linarith
  have hRatioBounded :
      (𝓝[>] (0 : NNReal)).IsBoundedUnder (· ≤ ·) ratio := by
    exact ⟨2, eventually_map.2 hRatioEventuallyLeTwo⟩
  have hupperRatio :
      ∀ m : ℕ, limsup ratio (𝓝[>] (0 : NNReal)) ≤ 1 + 1 / (m + 1 : ℝ) := by
    intro m
    have hEventually :
        ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), ratio δ ≤ 1 + 1 / (m + 1 : ℝ) := by
      filter_upwards [hUpper m, eventually_pos_levyModulusOfContinuity] with δ hδ hlevy
      exact (div_le_iff₀ hlevy).2 hδ
    -- Proof comment: the upper envelope is already an eventual bound on the full punctured
    -- neighborhood filter, so the ambient limsup inherits the same constant.
    exact limsup_le_of_le hRatioCobounded hEventually
  have hlowerRatio :
      ∀ m : ℕ, 1 - 1 / (m + 1 : ℝ) ≤ limsup ratio (𝓝[>] (0 : NNReal)) := by
    intro m
    let dyadicScale : ℕ → NNReal := fun n ↦ ((2 : NNReal)⁻¹) ^ n
    have hRatioNonnegDyadic :
        ∀ᶠ n : ℕ in atTop, 0 ≤ ratio (dyadicScale n) := by
      exact tendsto_dyadicScales_nhdsGT_zero.eventually hRatioNonneg
    have hRatioCoboundedDyadic :
        atTop.IsCoboundedUnder (· ≤ ·) (ratio ∘ dyadicScale) := by
      apply IsCoboundedUnder.of_frequently_ge (a := 0)
      exact hRatioNonnegDyadic.frequently
    have hRatioBoundedDyadic :
        atTop.IsBoundedUnder (· ≤ ·) (ratio ∘ dyadicScale) := by
      exact ⟨2, eventually_map.2 (tendsto_dyadicScales_nhdsGT_zero.eventually hRatioEventuallyLeTwo)⟩
    have hEventually :
        ∀ᶠ n : ℕ in atTop, 1 - 1 / (m + 1 : ℝ) ≤ ratio (dyadicScale n) := by
      filter_upwards [hLower m, Ici_mem_atTop (1 : ℕ)] with n hn hn1
      have hWindow :
          (dyadicWindowMax ω n 1 : ℝ) ≤
            ((compactIntervalOscillation 1 ω (dyadicScale n) : NNReal) : ℝ) := by
        exact_mod_cast dyadicWindowMax_one_le_compactIntervalOscillation ω n
      have hlevy :
          0 < levyModulusOfContinuity (dyadicScale n) := by
        simpa [dyadicScale] using levyModulusOfContinuity_dyadic_pos hn1
      -- Proof comment: divide the dyadic lower envelope by the positive dyadic modulus and then
      -- use the deterministic domination of `dyadicWindowMax` by the compact-interval oscillation.
      exact (le_div_iff₀ hlevy).2 (le_trans hn hWindow)
    have hSubseq :
        1 - 1 / (m + 1 : ℝ) ≤ limsup ratio (Filter.map dyadicScale atTop) := by
      have hSubseqBase :
          1 - 1 / (m + 1 : ℝ) ≤ limsup (ratio ∘ dyadicScale) atTop := by
        exact le_limsup_of_frequently_le hEventually.frequently hRatioBoundedDyadic
      simpa [limsup_comp] using hSubseqBase
    -- Proof comment: the dyadic scales tend to `0` through positive values, so the dyadic
    -- subsequence limsup is bounded above by the full punctured-neighborhood limsup.
    exact le_trans hSubseq
      (limsup_le_limsup_of_le tendsto_dyadicScales_nhdsGT_zero
        hRatioCoboundedDyadic hRatioBounded)
  -- Proof comment: after converting both eventual families to limsup inequalities, the existing
  -- reciprocal-gap squeeze closes the pathwise Lévy modulus law.
  simpa [ratio] using
    hasUnitIntervalLevyModulusLimsup_of_forall_invSucc_bounds ω hupperRatio hlowerRatio

namespace IsBrownianMotion

/-- Helper for Remark 22.4: packaging a continuous Brownian sample path into `PathSpace` turns the
pathwise predicate `hasUnitIntervalLevyModulusLimsup` into the theorem's displayed limsup
formula. -/
lemma processPath_hasUnitIntervalLevyModulusLimsup
    {B : NNReal → Ω → ℝ} {w : Ω}
    (hcont : Continuous (processPath B w)) :
    hasUnitIntervalLevyModulusLimsup (ContinuousMap.mk (processPath B w) hcont) ↔
      let ω : PathSpace := ContinuousMap.mk (processPath B w) hcont
      limsup
        (fun δ : NNReal ↦
          compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
        (𝓝[>] (0 : NNReal)) = 1 := by
  -- Proof comment: this is only the bookkeeping step that rewrites the bundled sample path
  -- predicate back into the theorem's explicit `let ω := ContinuousMap.mk ...` statement.
  rfl

/-- Helper for Remark 22.4: once the Brownian-path owner theorem is available in the packaged
path-space form, the current theorem follows by the packaging rewrite above. -/
lemma ae_hasUnitIntervalLevyModulusLimsup_of_owner
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hOwner :
      ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
        hasUnitIntervalLevyModulusLimsup (ContinuousMap.mk (processPath B w) hcont)) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      let ω : PathSpace := ContinuousMap.mk (processPath B w) hcont
      limsup
        (fun δ : NNReal ↦
          compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
        (𝓝[>] (0 : NNReal)) = 1 := by
  filter_upwards [hOwner] with w hw
  intro hcont
  -- Proof comment: unwrap the pathwise owner theorem at the bundled sample path and rewrite it
  -- into the explicit formula used by the current remark.
  exact (processPath_hasUnitIntervalLevyModulusLimsup (B := B) (w := w) hcont).mp (hw hcont)

/-- Helper for Remark 22.4: once almost-sure upper envelope families for every `α > 1` and
almost-sure lower envelope families for every `0 < β < 1` are available, the reciprocal-gap
sandwich closes Lévy's modulus law on the bundled Brownian sample path. -/
lemma ae_hasUnitIntervalLevyModulusLimsup_of_envelopeFamilies
    {μ : Measure Ω} {B : NNReal → Ω → ℝ}
    (hUpper :
      ∀ {α : ℝ}, 1 < α →
        ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
          ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
            ((compactIntervalOscillation 1 (ContinuousMap.mk (processPath B w) hcont) δ :
                NNReal) : ℝ) ≤
              α * levyModulusOfContinuity δ)
    (hLower :
      ∀ {β : ℝ}, 0 < β → β < 1 →
        ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
          ∀ᶠ n : ℕ in atTop,
            β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
              (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ)) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      hasUnitIntervalLevyModulusLimsup (ContinuousMap.mk (processPath B w) hcont) := by
  have hUpperAll :
      ∀ m : ℕ, ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
        ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
          ((compactIntervalOscillation 1 (ContinuousMap.mk (processPath B w) hcont) δ :
              NNReal) : ℝ) ≤
            (1 + 1 / (m + 1 : ℝ)) * levyModulusOfContinuity δ := by
    intro m
    -- Proof comment: choose the standard reciprocal-gap upper coefficient `1 + 1 / (m + 1)`.
    exact hUpper (α := 1 + 1 / (m + 1 : ℝ)) (by
      have hrecip_pos : 0 < (1 / (m + 1 : ℝ)) := by
        positivity
      linarith)
  have hUpperAE :
      ∀ᵐ w ∂μ, ∀ m : ℕ, ∀ hcont : Continuous (processPath B w),
        ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
          ((compactIntervalOscillation 1 (ContinuousMap.mk (processPath B w) hcont) δ :
              NNReal) : ℝ) ≤
            (1 + 1 / (m + 1 : ℝ)) * levyModulusOfContinuity δ := by
    -- Proof comment: intersect the countable upper family before introducing the continuity
    -- witness, so `ae_all_iff` only ranges over the natural-number index.
    exact ae_all_iff.2 hUpperAll
  have hLowerAll :
      ∀ m : ℕ, ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
        ∀ᶠ n : ℕ in atTop,
          (1 - 1 / (m + 1 : ℝ)) * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
            (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
    intro m
    -- Proof comment: the `m = 0` lower coefficient is `0`, hence trivial; for `m + 1` use the
    -- strict-`β` lower envelope with `β = 1 - 1 / (m + 2)`.
    cases m with
    | zero =>
        refine Filter.Eventually.of_forall fun w ↦ ?_
        intro hcont
        refine Filter.Eventually.of_forall fun n ↦ ?_
        have hNonneg :
            (0 : ℝ) ≤
              (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
          positivity
        simpa using hNonneg
    | succ k =>
        have hβ0 : 0 < 1 - 1 / (Nat.succ k + 1 : ℝ) := by
          have hdiv_lt_one : 1 / (Nat.succ k + 1 : ℝ) < 1 := by
            have hden_pos : (0 : ℝ) < (1 : ℝ) := zero_lt_one
            have hden_lt : (1 : ℝ) < (Nat.succ k + 1 : ℝ) := by
              exact_mod_cast (show 1 < Nat.succ k + 1 by omega)
            simpa using one_div_lt_one_div_of_lt hden_pos hden_lt
          linarith
        have hβ1 : 1 - 1 / (Nat.succ k + 1 : ℝ) < 1 := by
          have hrecip_pos : 0 < (1 / (Nat.succ k + 1 : ℝ)) := by
            positivity
          linarith
        exact hLower (β := 1 - 1 / (Nat.succ k + 1 : ℝ)) hβ0 hβ1
  have hLowerAE :
      ∀ᵐ w ∂μ, ∀ m : ℕ, ∀ hcont : Continuous (processPath B w),
        ∀ᶠ n : ℕ in atTop,
          (1 - 1 / (m + 1 : ℝ)) * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
            (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
    -- Proof comment: intersect the countable lower family after handling the trivial `m = 0`
    -- branch separately.
    exact ae_all_iff.2 hLowerAll
  -- Proof comment: on the intersection of the countable upper and lower almost-sure envelope
  -- families, the deterministic squeeze `hasUnitIntervalLevyModulusLimsup_of_sandwichFamilies`
  -- identifies the bundled-path limsup.
  filter_upwards [hUpperAE, hLowerAE] with w hwUpper hwLower
  intro hcont
  exact hasUnitIntervalLevyModulusLimsup_of_sandwichFamilies
    (ContinuousMap.mk (processPath B w) hcont) (fun m ↦ hwUpper m hcont) (fun m ↦ hwLower m hcont)

/-- Helper for Remark 22.4: the iterated logarithm `log (log (1 / t))` diverges to `+∞` as
`t ↓ 0`. -/
lemma tendsto_logLogInv_nhdsGT_zero_atTop :
    Tendsto (fun t : NNReal ↦ Real.log (Real.log ((t : ℝ)⁻¹)))
      (𝓝[>] (0 : NNReal)) atTop := by
  -- Proof comment: inversion turns `t ↓ 0` into `1 / t → +∞`, and the logarithm preserves the
  -- `atTop` limit twice.
  have hInv : Tendsto (fun t : NNReal ↦ ((t : ℝ)⁻¹)) (𝓝[>] (0 : NNReal)) atTop := by
    simpa [NNReal.coe_inv] using
      (NNReal.tendsto_coe_atTop.2
        (tendsto_inv_nhdsGT_zero :
          Tendsto (fun x : NNReal ↦ x⁻¹) (𝓝[>] (0 : NNReal)) atTop))
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hInv)

/-- Helper for Remark 22.4: the local `1 / 2`-Hölder numerator exactly cancels the matching
`sqrt t` factor in the law-of-the-iterated-logarithm normalization. -/
lemma halfHolderNormalizer_eq
    (C : ℝ≥0) {t : NNReal}
    (ht : 0 < (t : ℝ))
    (hloglog : 0 < Real.log (Real.log ((t : ℝ)⁻¹))) :
    (C : ℝ) * (t : ℝ) ^ (1 / 2 : ℝ) /
        Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))) =
      (C : ℝ) / Real.sqrt (2 * Real.log (Real.log ((t : ℝ)⁻¹))) := by
  -- Proof comment: rewrite every square root as the positive `1 / 2`-power and cancel the common
  -- `sqrt t` factor from numerator and denominator.
  have ht_nonneg : 0 ≤ (t : ℝ) := le_of_lt ht
  have hsqrt_t : (t : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (t : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
  have hsqrt_mul :
      Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))) =
        Real.sqrt (t : ℝ) * Real.sqrt (2 * Real.log (Real.log ((t : ℝ)⁻¹))) := by
    rw [show 2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹)) =
          (t : ℝ) * (2 * Real.log (Real.log ((t : ℝ)⁻¹))) by ring]
    rw [Real.sqrt_mul ht_nonneg]
  have hsqrt_loglog_ne :
      Real.sqrt (2 * Real.log (Real.log ((t : ℝ)⁻¹))) ≠ 0 := by
    apply Real.sqrt_ne_zero'.2
    positivity
  rw [hsqrt_t, hsqrt_mul]
  field_simp [Real.sqrt_ne_zero'.2 ht, hsqrt_loglog_ne]

/-- Helper for Remark 22.4: every local `1 / 2`-Hölder majorant is negligible compared with the
law-of-the-iterated-logarithm normalization at `0`. -/
lemma tendsto_halfHolderNormalizer_zero (C : ℝ≥0) :
    Tendsto
      (fun t : NNReal ↦
        (C : ℝ) * (t : ℝ) ^ (1 / 2 : ℝ) /
          Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
      (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
  -- Proof comment: after the previous cancellation lemma, only the inverse square root of
  -- `log (log (1 / t))` remains, and that term tends to `0`.
  have hLogLog := tendsto_logLogInv_nhdsGT_zero_atTop
  have hEventuallyLogLogPos :
      ∀ᶠ t : NNReal in 𝓝[>] (0 : NNReal), 0 < Real.log (Real.log ((t : ℝ)⁻¹)) := by
    filter_upwards [hLogLog.eventually_gt_atTop (1 : ℝ)] with t ht
    linarith
  have hScaled :
      Tendsto (fun t : NNReal ↦ 2 * Real.log (Real.log ((t : ℝ)⁻¹)))
        (𝓝[>] (0 : NNReal)) atTop := by
    exact Tendsto.const_mul_atTop (show 0 < (2 : ℝ) by norm_num) hLogLog
  have hSimple :
      Tendsto
        (fun t : NNReal ↦
          (C : ℝ) / Real.sqrt (2 * Real.log (Real.log ((t : ℝ)⁻¹))))
        (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
    have hInvSqrt :
        Tendsto
          (fun t : NNReal ↦ (Real.sqrt (2 * Real.log (Real.log ((t : ℝ)⁻¹))))⁻¹)
          (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
      exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hScaled)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hInvSqrt.const_mul (C : ℝ)
  refine Tendsto.congr' ?_ hSimple
  filter_upwards [self_mem_nhdsWithin, hEventuallyLogLogPos] with t ht0 hloglog
  have ht : 0 < (t : ℝ) := by
    exact_mod_cast ht0
  simpa using (halfHolderNormalizer_eq C ht hloglog).symm

/-- Helper for Remark 22.4: evaluating the standard Gaussian density at the Brownian scaling
threshold `a / √T` yields the explicit Mills-profile factor used in anchored window estimates. -/
lemma gaussianTailUpperBound_scaledBrownianWindowThreshold
    {a : ℝ} (ha : 0 < a) {T : NNReal} (hT : 0 < T) :
    2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) =
      (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
        Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  have hT_real_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := by
    positivity
  have hExponent :
      -((a / Real.sqrt (T : ℝ)) ^ 2) / 2 = -(a ^ 2) / (2 * (T : ℝ)) := by
    -- Proof comment: collapse `(a / √T)^2` to `a^2 / T` using `√T ^ 2 = T`.
    field_simp [hsqrtT_ne, hT_real_pos.ne']
    rw [Real.sq_sqrt hT_real_pos.le]
  calc
    2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)))
        = 2 *
            (((Real.sqrt (2 * Real.pi))⁻¹ *
                Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) /
              (a / Real.sqrt (T : ℝ))) := by
              rw [gaussianPDFReal_def]
              simp [hExponent]
    _ = (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
          field_simp [ha.ne', hsqrtT_ne, show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]

/-- Helper for Remark 22.4: the one-sided Brownian increment tail on the anchored window
`[s, s + T]` satisfies the standard reflection-principle profile. -/
lemma brownianAnchoredIncrement_measureReal_le_profile
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {s T : NNReal} {a : ℝ} (ha : 0 < a) (hT : 0 < T) :
    μ.real {ω | ∃ t ∈ Set.Icc s (s + T), a < B t ω - B s ω} ≤
      (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
        Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  let W : NNReal → Ω → ℝ := fun u ω ↦ B (s + u) ω - B s ω
  let E : Set Ω := {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, a < W u ω}
  have hW : IsBrownianMotion μ W :=
    IsBrownianMotion.incrementProcess_isBrownianMotion hB s
  have hEvent_eq :
      {ω | ∃ t ∈ Set.Icc s (s + T), a < B t ω - B s ω} = E := by
    ext ω
    constructor
    · rintro ⟨t, ht, hωt⟩
      refine ⟨t - s, ?_, ?_⟩
      · constructor
        · positivity
        · exact (tsub_le_iff_right).2 (by simpa [add_comm, add_left_comm, add_assoc] using ht.2)
      · simpa [W, add_tsub_cancel_of_le ht.1]
          using hωt
    · rintro ⟨u, hu, hωu⟩
      refine ⟨s + u, ?_, ?_⟩
      · constructor
        · simpa using le_add_of_nonneg_right hu.1
        · simpa [add_assoc] using add_le_add_left hu.2 s
      · simpa [W, add_assoc, add_left_comm, add_comm] using hωu
  let Y : Ω → ℝ := fun ω ↦ W T ω / Real.sqrt (T : ℝ)
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hT_real_pos : 0 < (T : ℝ) := by
    exact_mod_cast hT
  have hsqrtT_pos : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hT_real_pos
  have hRun : μ E = 2 * μ {ω | a < W T ω} := by
    simpa [E] using
      runningMaximum_eq_two_mul_brownianTerminalTail (hB := hW) (a := a) ha (T := T) hT
  have hMarginal : HasLaw (W T) (gaussianReal 0 T) μ := hW.gaussian_marginal hT
  have hScale :
      HasLaw (fun z : ℝ ↦ (Real.sqrt (T : ℝ))⁻¹ * z) (gaussianReal 0 1) (gaussianReal 0 T) := by
    let c : ℝ := (Real.sqrt (T : ℝ))⁻¹
    let d : NNReal := ⟨c ^ 2, sq_nonneg c⟩
    have hmap :
        (gaussianReal 0 T).map (fun z : ℝ ↦ c * z) = gaussianReal 0 1 := by
      have hmap0 :
          (gaussianReal 0 T).map (c * ·) = gaussianReal 0 (d * T) := by
        simpa [d] using (gaussianReal_map_const_mul (μ := 0) (v := T) c)
      have hvar : d * T = 1 := by
        ext
        simp [c, d, NNReal.coe_mul, hT_real_pos.ne', Real.sq_sqrt hT_real_pos.le]
      rw [hvar] at hmap0
      simpa [c] using hmap0
    refine ⟨?_, hmap⟩
    fun_prop
  have hY : HasLaw Y (gaussianReal 0 1) μ := by
    simpa [Y, Function.comp, div_eq_mul_inv, mul_comm] using hScale.comp hMarginal
  have hx_pos : 0 < a / Real.sqrt (T : ℝ) := by
    positivity
  have hTailIci :
      μ.real {ω | a / Real.sqrt (T : ℝ) ≤ Y ω} ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    simpa [MeasureTheory.Measure.real_def, Y] using
      (ProbabilityTheory.HasLaw.standardNormal_tail_bounds
        (P := μ) (X := Y) hY hx_pos).2
  have hTailSubset :
      {ω | a < W T ω} ⊆ {ω | a / Real.sqrt (T : ℝ) ≤ Y ω} := by
    intro ω hω
    have hScaled : a / Real.sqrt (T : ℝ) < Y ω := by
      simpa [Y] using (div_lt_div_of_pos_right hω hsqrtT_pos)
    exact hScaled.le
  have hTailIoi :
      μ.real {ω | a < W T ω} ≤
        gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ)) := by
    exact MeasureTheory.measureReal_mono hTailSubset |>.trans hTailIci
  calc
    μ.real {ω | ∃ t ∈ Set.Icc s (s + T), a < B t ω - B s ω}
        = μ.real E := by rw [hEvent_eq]
    _ = 2 * μ.real {ω | a < W T ω} := by
          rw [MeasureTheory.Measure.real_def, MeasureTheory.Measure.real_def, hRun,
            ENNReal.toReal_mul]
          norm_num
    _ ≤ 2 * (gaussianPDFReal 0 1 (a / Real.sqrt (T : ℝ)) / (a / Real.sqrt (T : ℝ))) := by
          gcongr
    _ =
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
            exact gaussianTailUpperBound_scaledBrownianWindowThreshold ha hT

/-- Helper for Remark 22.4: the absolute Brownian increment on the anchored window `[s, s + T]`
is controlled by the sum of the positive and negative reflection-principle tails. -/
lemma brownianAnchoredAbsIncrement_measureReal_le_profile
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {s T : NNReal} {a : ℝ} (ha : 0 < a) (hT : 0 < T) :
    μ.real {ω | ∃ t ∈ Set.Icc s (s + T), a < |B t ω - B s ω|} ≤
      2 *
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let Eabs : Set Ω := {ω | ∃ t ∈ Set.Icc s (s + T), a < |B t ω - B s ω|}
  let Epos : Set Ω := {ω | ∃ t ∈ Set.Icc s (s + T), a < B t ω - B s ω}
  let Eneg : Set Ω := {ω | ∃ t ∈ Set.Icc s (s + T), a < (-B t ω) - (-B s ω)}
  have hSubset : Eabs ⊆ Epos ∪ Eneg := by
    intro ω hω
    rcases hω with ⟨t, ht, hωt⟩
    by_cases hnonneg : 0 ≤ B t ω - B s ω
    · left
      exact ⟨t, ht, by simpa [abs_of_nonneg hnonneg] using hωt⟩
    · right
      have hneg : a < -(B t ω - B s ω) := by
        simpa [abs_of_neg (lt_of_not_ge hnonneg)] using hωt
      have hneg' : a < (-B t ω) - (-B s ω) := by
        linarith
      exact ⟨t, ht, hneg'⟩
  have hNegB : IsBrownianMotion μ (fun t ω ↦ -B t ω) :=
    IsBrownianMotion.neg_isBrownianMotion hB
  have hUnion :
      μ.real (Epos ∪ Eneg) ≤ μ.real Epos + μ.real Eneg :=
    MeasureTheory.measureReal_union_le (μ := μ) Epos Eneg
  have hPos :
      μ.real Epos ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) :=
    brownianAnchoredIncrement_measureReal_le_profile (B := B) hB ha hT
  have hNeg :
      μ.real Eneg ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by
    simpa [Eneg] using
      brownianAnchoredIncrement_measureReal_le_profile
        (B := fun t ω ↦ -B t ω) hNegB ha hT
  calc
    μ.real Eabs ≤ μ.real (Epos ∪ Eneg) :=
      by
        simpa [MeasureTheory.Measure.real_def] using
          (ENNReal.toReal_mono (measure_ne_top μ (Epos ∪ Eneg)) (measure_mono hSubset))
    _ ≤ μ.real Epos + μ.real Eneg := hUnion
    _ ≤
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) +
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
          Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := add_le_add hPos hNeg
    _ =
        2 *
          (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / a) *
            Real.exp (-(a ^ 2) / (2 * (T : ℝ)))) := by ring

/-- Helper for Remark 22.4: translating a deterministic window `[s, s + T]` to `[0, T]`
identifies its oscillation event with the oscillation event of the increment process
`u ↦ B (s + u) - B s`. -/
lemma windowOscillationEvent_eq_incrementProcessEvent
    {B : NNReal → Ω → ℝ} (s T : NNReal) (a : ℝ) :
    {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc s (s + T), a < |B v ω - B u ω|} =
      {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc (0 : NNReal) T,
          a < |(B (s + v) ω - B s ω) - (B (s + u) ω - B s ω)|} := by
  ext ω
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: subtract the common left endpoint `s` from both times to recenter the
    -- window at `0`; the Brownian increment difference is unchanged by this translation.
    refine ⟨u - s, ?_, v - s, ?_, ?_⟩
    · constructor
      · positivity
      · simpa [add_comm] using (tsub_le_iff_right).2 hu.2
    · constructor
      · positivity
      · simpa [add_comm] using (tsub_le_iff_right).2 hv.2
    · have hcancel :
          (B (s + (v - s)) ω - B s ω) - (B (s + (u - s)) ω - B s ω) = B v ω - B u ω := by
        rw [add_tsub_cancel_of_le hv.1, add_tsub_cancel_of_le hu.1]
        ring
      simpa [hcancel] using huv
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: add the left endpoint `s` back to the normalized witnesses in `[0, T]` to
    -- recover witnesses in the original interval `[s, s + T]`.
    refine ⟨s + u, ?_, s + v, ?_, ?_⟩
    · constructor
      · simpa using le_add_of_nonneg_right hu.1
      · simpa [add_assoc] using add_le_add_left hu.2 s
    · constructor
      · simpa using le_add_of_nonneg_right hv.1
      · simpa [add_assoc] using add_le_add_left hv.2 s
    · have hcancel :
          (B (s + v) ω - B s ω) - (B (s + u) ω - B s ω) = B (s + v) ω - B (s + u) ω := by
        ring
      simpa [hcancel] using huv

/-- Helper for Remark 22.4: the measure of a deterministic window oscillation event can be
rewritten on the normalized interval `[0, T]` for the translated increment process. -/
lemma measureReal_windowOscillationEvent_eq_incrementProcessEvent
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (s T : NNReal) (a : ℝ) :
    μ.real {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc s (s + T), a < |B v ω - B u ω|} =
      μ.real {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc (0 : NNReal) T,
        a < |(B (s + v) ω - B s ω) - (B (s + u) ω - B s ω)|} := by
  -- Proof comment: after identifying the two events pointwise, their real masses are identical.
  rw [windowOscillationEvent_eq_incrementProcessEvent (B := B) s T a]

/-- Helper for Remark 22.4: a large unordered window oscillation can be reordered into either a
positive drawup for `B` or a positive drawup for `-B`. -/
lemma windowOscillationEvent_subset_positiveOrNegativeDrawup
    {B : NNReal → Ω → ℝ} (s T : NNReal) (a : ℝ) :
    {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc s (s + T), a < |B v ω - B u ω|}
      ⊆
        {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc u (s + T), a < B v ω - B u ω} ∪
          {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc u (s + T), a < (-B v ω) - (-B u ω)} := by
  intro ω hω
  rcases hω with ⟨u, hu, v, hv, huv⟩
  rcases le_total u v with huv_time | hvu_time
  · -- Proof comment: once the witnesses are time-ordered as `u ≤ v`, the absolute value is either
    -- already a positive drawup for `B` or becomes one for the negated path.
    by_cases hnonneg : 0 ≤ B v ω - B u ω
    · left
      exact ⟨u, hu, v, ⟨huv_time, hv.2⟩, by simpa [abs_of_nonneg hnonneg] using huv⟩
    · right
      have hneg : B v ω - B u ω < 0 := lt_of_not_ge hnonneg
      have hdrawup : a < (-B v ω) - (-B u ω) := by
        have habs : a < -(B v ω - B u ω) := by
          simpa [abs_of_neg hneg] using huv
        linarith
      exact ⟨u, hu, v, ⟨huv_time, hv.2⟩, hdrawup⟩
  · -- Proof comment: in the reverse time order, swap the witnesses first and then repeat the same
    -- sign split on the reordered increment.
    have huv' : a < |B u ω - B v ω| := by
      simpa [abs_sub_comm] using huv
    by_cases hnonneg : 0 ≤ B u ω - B v ω
    · left
      exact ⟨v, hv, u, ⟨hvu_time, hu.2⟩, by simpa [abs_of_nonneg hnonneg] using huv'⟩
    · right
      have hneg : B u ω - B v ω < 0 := lt_of_not_ge hnonneg
      have hdrawup : a < (-B u ω) - (-B v ω) := by
        have habs : a < -(B u ω - B v ω) := by
          simpa [abs_of_neg hneg] using huv'
        linarith
      exact ⟨v, hv, u, ⟨hvu_time, hu.2⟩, hdrawup⟩

/-- Helper for Remark 22.4: translating a deterministic window `[s, s + T]` to `[0, T]`
identifies its positive-drawup event with the positive-drawup event of the increment process
`u ↦ B (s + u) - B s`. -/
lemma windowPositiveDrawupEvent_eq_incrementProcessEvent
    {B : NNReal → Ω → ℝ} (s T : NNReal) (a : ℝ) :
    {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc u (s + T), a < B v ω - B u ω} =
      {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc u T,
          a < (B (s + v) ω - B s ω) - (B (s + u) ω - B s ω)} := by
  ext ω
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: subtract the common left endpoint `s` from the ordered witnesses so the
    -- drawup event lives on the normalized interval `[0, T]`.
    refine ⟨u - s, ⟨by positivity, ?_⟩, v - s, ⟨?_, ?_⟩, ?_⟩
    · simpa [add_comm] using (tsub_le_iff_right).2 hu.2
    · exact tsub_le_tsub_right hv.1 s
    · simpa [add_comm] using (tsub_le_iff_right).2 hv.2
    · have hcancel :
          (B (s + (v - s)) ω - B s ω) - (B (s + (u - s)) ω - B s ω) = B v ω - B u ω := by
        have hs_v : s + (v - s) = v := add_tsub_cancel_of_le (le_trans hu.1 hv.1)
        have hs_u : s + (u - s) = u := add_tsub_cancel_of_le hu.1
        rw [hs_v, hs_u]
        ring
      simpa [hcancel] using huv
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: add the left endpoint `s` back to the normalized witnesses to recover the
    -- original ordered drawup event on `[s, s + T]`.
    refine ⟨s + u, ⟨?_, ?_⟩, s + v, ⟨?_, ?_⟩, ?_⟩
    · simpa using le_add_of_nonneg_right hu.1
    · simpa [add_assoc] using add_le_add_left hu.2 s
    · simpa [add_assoc] using add_le_add_left hv.1 s
    · simpa [add_assoc] using add_le_add_left hv.2 s
    · have hcancel :
          (B (s + v) ω - B s ω) - (B (s + u) ω - B s ω) = B (s + v) ω - B (s + u) ω := by
        ring
      simpa [hcancel] using huv

/-- Helper for Remark 22.4: the measure of a deterministic positive-drawup event can be rewritten
on the normalized interval `[0, T]` for the translated increment process. -/
lemma measureReal_windowPositiveDrawupEvent_eq_incrementProcessEvent
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (s T : NNReal) (a : ℝ) :
    μ.real {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc u (s + T), a < B v ω - B u ω} =
      μ.real {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc u T,
        a < (B (s + v) ω - B s ω) - (B (s + u) ω - B s ω)} := by
  -- Proof comment: after identifying the two positive-drawup events pointwise, their real masses
  -- are identical.
  rw [windowPositiveDrawupEvent_eq_incrementProcessEvent (B := B) s T a]

/-- Helper for Remark 22.4: on an interval anchored at `0`, a large non-anchored oscillation
already forces one point of the path to leave the half-threshold anchored tube. -/
lemma windowOscillationEvent_subset_anchoredAbsIncrement_halfThreshold
    {B : NNReal → Ω → ℝ} (T : NNReal) (a : ℝ) :
    {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc (0 : NNReal) T, a < |B v ω - B u ω|}
      ⊆ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a / 2 < |B t ω - B 0 ω|} := by
  intro ω hω
  rcases hω with ⟨u, hu, v, hv, huv⟩
  by_cases huLarge : a / 2 < |B u ω - B 0 ω|
  · -- Proof comment: if one endpoint already exceeds the half-threshold from the anchor, it is
    -- itself the required witness.
    exact ⟨u, hu, huLarge⟩
  · have huSmall : |B u ω - B 0 ω| ≤ a / 2 := le_of_not_gt huLarge
    have hvLarge : a / 2 < |B v ω - B 0 ω| := by
      -- Proof comment: otherwise both endpoints stay within the half-threshold anchored tube, and
      -- the triangle inequality would force the pairwise oscillation to stay below `a`.
      by_contra hvLarge
      have hvSmall : |B v ω - B 0 ω| ≤ a / 2 := le_of_not_gt hvLarge
      have htriangle :
          |B v ω - B u ω| ≤ |B v ω - B 0 ω| + |B u ω - B 0 ω| := by
        have hdecomp :
            B v ω - B u ω = (B v ω - B 0 ω) + (B 0 ω - B u ω) := by
          ring
        rw [hdecomp]
        simpa [abs_sub_comm] using abs_add_le (B v ω - B 0 ω) (B 0 ω - B u ω)
      have hbound : |B v ω - B u ω| ≤ a := by
        calc
          |B v ω - B u ω| ≤ |B v ω - B 0 ω| + |B u ω - B 0 ω| := htriangle
          _ ≤ a / 2 + a / 2 := add_le_add hvSmall huSmall
          _ = a := by ring
      exact (not_le_of_gt huv) hbound
    exact ⟨v, hv, hvLarge⟩

/-- Helper for Remark 22.4: a Brownian oscillation event on one deterministic window is controlled
by the anchored absolute-increment profile at half threshold. -/
lemma brownianWindowOscillation_measureReal_le_halfThresholdProfile
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {s T : NNReal} {a : ℝ} (ha : 0 < a) (hT : 0 < T) :
    μ.real {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc s (s + T), a < |B v ω - B u ω|} ≤
      2 *
        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / (a / 2)) *
          Real.exp (-((a / 2) ^ 2) / (2 * (T : ℝ)))) := by
  let W : NNReal → Ω → ℝ := fun u ω ↦ B (s + u) ω - B s ω
  have hW : IsBrownianMotion μ W :=
    IsBrownianMotion.incrementProcess_isBrownianMotion hB s
  letI : IsProbabilityMeasure μ := hW.isProbabilityMeasure
  have hSubset :
      {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc (0 : NNReal) T, a < |W v ω - W u ω|}
        ⊆ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a / 2 < |W t ω - W 0 ω|} := by
    -- Proof comment: once the window has been translated to `[0, T]`, the previous deterministic
    -- half-threshold reduction applies directly.
    exact windowOscillationEvent_subset_anchoredAbsIncrement_halfThreshold (B := W) T a
  calc
    μ.real {ω | ∃ u ∈ Set.Icc s (s + T), ∃ v ∈ Set.Icc s (s + T), a < |B v ω - B u ω|}
        =
          μ.real
            {ω | ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc (0 : NNReal) T,
                a < |W v ω - W u ω|} := by
            -- Proof comment: recenter the deterministic window at `0` using the increment
            -- process; this is the exact event equality already isolated above.
            simpa [W] using
              measureReal_windowOscillationEvent_eq_incrementProcessEvent
                (μ := μ) (B := B) s T a
    _ ≤ μ.real {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a / 2 < |W t ω - W 0 ω|} := by
          simpa [MeasureTheory.Measure.real_def] using
            (ENNReal.toReal_mono
              (measure_ne_top μ {ω | ∃ t ∈ Set.Icc (0 : NNReal) T, a / 2 < |W t ω - W 0 ω|})
              (measure_mono hSubset))
    _ ≤
        2 *
          (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) * (1 / (a / 2)) *
            Real.exp (-((a / 2) ^ 2) / (2 * (T : ℝ)))) := by
          -- Proof comment: the translated process is Brownian, so the anchored absolute-increment
          -- reflection-principle estimate applies at threshold `a / 2`.
          simpa [W] using
            brownianAnchoredAbsIncrement_measureReal_le_profile
              (B := W) hW (s := 0) (a := a / 2) (T := T) (by positivity) hT

/-- Helper for Remark 22.4: on a continuous path over `[0, T]`, an ordered positive drawup is
equivalent to one time at which the path lies more than `a` above its past minimum. -/
lemma exists_positiveDrawup_iff_exists_excessAbovePastMinimum
    {f : NNReal → ℝ} (hcont : Continuous f) {T : NNReal} {a : ℝ} :
    (∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc u T, a < f v - f u) ↔
      ∃ v ∈ Set.Icc (0 : NNReal) T, a < f v - sInf (f '' Set.Icc (0 : NNReal) v) := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: once `u ≤ v`, the prefix minimum up to `v` is at most `f u`, so any drawup
    -- from `u` to `v` is at least as large as the excess of `f v` over the past minimum.
    refine ⟨v, ⟨le_trans hu.1 hv.1, hv.2⟩, ?_⟩
    let prefixSet : Set NNReal := Set.Icc (0 : NNReal) v
    have hPrefixImageCompact : IsCompact (f '' prefixSet) := by
      exact isCompact_Icc.image_of_continuousOn hcont.continuousOn
    have huPrefix : u ∈ prefixSet := by
      simpa [prefixSet] using (show u ∈ Set.Icc (0 : NNReal) v from ⟨hu.1, hv.1⟩)
    have hsInf_le : sInf (f '' prefixSet) ≤ f u := by
      exact csInf_le hPrefixImageCompact.bddBelow ⟨u, huPrefix, rfl⟩
    linarith
  · rintro ⟨v, hv, hvdraw⟩
    -- Proof comment: continuity on the compact prefix interval gives a point where the past
    -- minimum is attained, and that minimizer is the desired left witness for the drawup.
    let prefixSet : Set NNReal := Set.Icc (0 : NNReal) v
    have hPrefixNonempty : prefixSet.Nonempty := by
      refine ⟨0, ?_⟩
      simpa [prefixSet] using ⟨le_rfl, hv.1⟩
    obtain ⟨u, hu, hsInf_eq, hmin⟩ :=
      isCompact_Icc.exists_sInf_image_eq_and_le hPrefixNonempty hcont.continuousOn
    refine ⟨u, ?_, v, ?_, ?_⟩
    · exact ⟨hu.1, le_trans hu.2 hv.2⟩
    · exact ⟨hu.2, hv.2⟩
    -- Proof comment: substitute the attained prefix minimum back into the excess inequality.
    simpa [prefixSet, hsInf_eq] using hvdraw

/-- Helper for Remark 22.4: on a continuous path over `[0, T]`, an ordered positive drawup of size
at least `a` is equivalent to one time at which the path lies at least `a` above its past
minimum. -/
lemma exists_positiveDrawup_ge_iff_exists_excessAbovePastMinimum
    {f : NNReal → ℝ} (hcont : Continuous f) {T : NNReal} {a : ℝ} :
    (∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc u T, a ≤ f v - f u) ↔
      ∃ v ∈ Set.Icc (0 : NNReal) T, a ≤ f v - sInf (f '' Set.Icc (0 : NNReal) v) := by
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    -- Proof comment: as in the strict version, the prefix minimum up to `v` lies below the left
    -- endpoint `f u`, so the drawup dominates the excess above the past minimum.
    refine ⟨v, ⟨le_trans hu.1 hv.1, hv.2⟩, ?_⟩
    let prefixSet : Set NNReal := Set.Icc (0 : NNReal) v
    have hPrefixImageCompact : IsCompact (f '' prefixSet) := by
      exact isCompact_Icc.image_of_continuousOn hcont.continuousOn
    have huPrefix : u ∈ prefixSet := by
      simpa [prefixSet] using (show u ∈ Set.Icc (0 : NNReal) v from ⟨hu.1, hv.1⟩)
    have hsInf_le : sInf (f '' prefixSet) ≤ f u := by
      exact csInf_le hPrefixImageCompact.bddBelow ⟨u, huPrefix, rfl⟩
    linarith
  · rintro ⟨v, hv, hvdraw⟩
    -- Proof comment: continuity on the compact prefix interval again provides a minimizer where
    -- the running minimum is attained.
    let prefixSet : Set NNReal := Set.Icc (0 : NNReal) v
    have hPrefixNonempty : prefixSet.Nonempty := by
      refine ⟨0, ?_⟩
      simpa [prefixSet] using ⟨le_rfl, hv.1⟩
    obtain ⟨u, hu, hsInf_eq, hmin⟩ :=
      isCompact_Icc.exists_sInf_image_eq_and_le hPrefixNonempty hcont.continuousOn
    refine ⟨u, ?_, v, ?_, ?_⟩
    · exact ⟨hu.1, le_trans hu.2 hv.2⟩
    · exact ⟨hu.2, hv.2⟩
    -- Proof comment: substituting the attained minimum converts the excess bound back to the
    -- original ordered drawup.
    simpa [prefixSet, hsInf_eq] using hvdraw

/-- Helper for Remark 22.4: on the compact interval `[0, T]`, the running minimum
`v ↦ sInf (f '' Set.Icc (0 : NNReal) v)` of a continuous path varies continuously. -/
lemma continuous_prefixInfOnIcc
    {f : NNReal → ℝ} (hcont : Continuous f) (T : NNReal) :
    ContinuousOn (fun v ↦ sInf (f '' Set.Icc (0 : NNReal) v)) (Set.Icc (0 : NNReal) T) := by
  let F : NNReal → Set.Icc (0 : NNReal) T → ℝ := fun v u ↦ f (min (u : NNReal) v)
  have hF : Continuous (Function.uncurry F) := by
    -- Proof comment: the two-variable map `(v, u) ↦ f (min u v)` is continuous because both
    -- `min` and `f` are continuous.
    simpa [F, Function.uncurry] using
      hcont.comp ((continuous_subtype_val.comp continuous_snd).min continuous_fst)
  have hSInfRaw :
      Continuous fun v : NNReal ↦
        sInf (F v '' (Set.univ : Set (Set.Icc (0 : NNReal) T))) := by
    -- Proof comment: `IsCompact.continuous_sInf` applies once the infimum is taken over the fixed
    -- compact carrier `Set.Icc (0, T)`.
    simpa [F] using
      (isCompact_univ : IsCompact (Set.univ : Set (Set.Icc (0 : NNReal) T))).continuous_sInf hF
  have hSInf : Continuous fun v : NNReal ↦ sInf (Set.range (F v)) := by
    simpa [Set.image_univ] using hSInfRaw
  have hRangeCont : ContinuousOn (fun v : NNReal ↦ sInf (Set.range (F v))) (Set.Icc (0 : NNReal) T) :=
    hSInf.continuousOn
  refine ContinuousOn.congr hRangeCont ?_
  intro v hv
  have hImageEq :
      Set.range (F v) = f '' Set.Icc (0 : NNReal) v := by
    -- Proof comment: as the compact carrier variable `u` ranges over `[0, T]`, `min u v` ranges
    -- exactly over `[0, v]`.
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨min (u : NNReal) v, ⟨by positivity, min_le_right _ _⟩, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨⟨w, ⟨hw.1, le_trans hw.2 hv.2⟩⟩, ?_⟩
      change f (min w v) = f w
      rw [min_eq_left hw.2]
  simpa [hImageEq]

/-- Helper for Remark 22.4: for a continuous path, forbidding every drawup of size at least `a`
is equivalent to the reflected-at-the-past-minimum path staying away from `0` on `(0, T]`. -/
lemma noPositiveDrawup_ge_iff_reflectedPastMinimum_avoids_zero
    {f : NNReal → ℝ} (hcont : Continuous f) {T : NNReal} {a : ℝ} (ha : 0 < a) :
    (¬ ∃ u ∈ Set.Icc (0 : NNReal) T, ∃ v ∈ Set.Icc u T, a ≤ f v - f u) ↔
      ∀ v ∈ Set.Ioc (0 : NNReal) T, a + sInf (f '' Set.Icc (0 : NNReal) v) - f v ≠ 0 := by
  let g : NNReal → ℝ := fun v ↦ a + sInf (f '' Set.Icc (0 : NNReal) v) - f v
  have hgContOn : ContinuousOn g (Set.Icc (0 : NNReal) T) := by
    -- Proof comment: the reflected past-minimum path is the continuous running minimum plus the
    -- constant `a`, minus the original continuous path.
    exact (continuousOn_const.add (continuous_prefixInfOnIcc hcont T)).sub hcont.continuousOn
  constructor
  · intro hNo v hv hzero
    apply hNo
    -- Proof comment: a zero of the reflected path is exactly an equality case for the closed
    -- threshold `a`, and the non-strict drawup/minimum lemma repackages it as an ordered drawup.
    refine (exists_positiveDrawup_ge_iff_exists_excessAbovePastMinimum hcont).2 ?_
    refine ⟨v, ⟨hv.1.le, hv.2⟩, ?_⟩
    linarith
  · intro hAvoid hDraw
    rcases (exists_positiveDrawup_ge_iff_exists_excessAbovePastMinimum hcont).1 hDraw with
      ⟨v, hv, hvdraw⟩
    have hg0 : 0 < g 0 := by
      -- Proof comment: at time `0`, the reflected past-minimum path takes the positive value `a`.
      have hsInf0 : sInf (f '' Set.Icc (0 : NNReal) 0) = f 0 := by
        have hSet : Set.Icc (0 : NNReal) 0 = ({0} : Set NNReal) := by
          ext u
          simp
        rw [hSet]
        simp
      dsimp [g]
      simpa [hsInf0] using ha
    have hgv_nonpos : g v ≤ 0 := by
      dsimp [g]
      linarith
    have hsubset : Set.Icc (0 : NNReal) v ⊆ Set.Icc (0 : NNReal) T := by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hv.2⟩
    have hgContOn_v : ContinuousOn g (Set.Icc (0 : NNReal) v) := hgContOn.mono hsubset
    have hnegContOn_v : ContinuousOn (fun x ↦ -g x) (Set.Icc (0 : NNReal) v) := hgContOn_v.neg
    have hzeroMem : (0 : ℝ) ∈ Set.Icc (-g 0) (-g v) := by
      refine ⟨?_, ?_⟩
      · linarith
      · linarith
    obtain ⟨z, hzIcc, hzZero⟩ :=
      intermediate_value_Icc (a := (0 : NNReal)) (b := v) hv.1 hnegContOn_v hzeroMem
    have hzPos : 0 < z := by
      by_contra hzPos
      have hzEq : z = 0 := le_antisymm (le_of_not_gt hzPos) hzIcc.1
      have hnegG0 : -g 0 = 0 := by simpa [hzEq] using hzZero
      linarith
    have hzTail : z ∈ Set.Ioc (0 : NNReal) T := ⟨hzPos, le_trans hzIcc.2 hv.2⟩
    have hgz_zero : g z = 0 := by
      linarith
    exact (hAvoid z hzTail) hgz_zero

/-- Helper for Remark 22.4: one positive dyadic hit already forces the one-step window maximum of
the bundled sample path to dominate the same threshold. -/
lemma dyadicRowHit_le_dyadicWindowMax_one
    {B : NNReal → Ω → ℝ} {w : Ω}
    (hcont : Continuous (processPath B w))
    {β : ℝ} {n i : ℕ} (hi : i + 1 ≤ 2 ^ n)
    (hHit : β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
      B (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) w -
        B ((i : NNReal) / (2 : NNReal) ^ n) w) :
    β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
      (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
  let ω : PathSpace := ContinuousMap.mk (processPath B w) hcont
  have hWindow :
      ‖ω (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) -
          ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ ≤
        dyadicWindowMax ω n 1 := by
    -- Proof comment: this is exactly the deterministic one-step dyadic-window bound isolated
    -- earlier in the file.
    simpa [ω, processPath] using nnnorm_sub_le_dyadicWindowMax_one ω n i hi
  have hAbs :
      B (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) w -
          B ((i : NNReal) / (2 : NNReal) ^ n) w ≤
        (‖ω (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) -
            ω ((i : NNReal) / (2 : NNReal) ^ n)‖₊ : ℝ) := by
    -- Proof comment: the raw positive increment is bounded by its absolute value, and for the
    -- bundled path that absolute value is exactly the coercion of the `NNReal` norm.
    have hAbsBase :
        B (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) w -
            B ((i : NNReal) / (2 : NNReal) ^ n) w ≤
          |B (((i + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n) w -
            B ((i : NNReal) / (2 : NNReal) ^ n) w| := by
      exact le_abs_self _
    simpa [ω, processPath, Real.norm_eq_abs] using hAbsBase
  exact le_trans hHit <| le_trans hAbs <| by
    exact_mod_cast hWindow

/-- Helper for Remark 22.4: eventual avoidance of the dyadic row-failure events already yields the
lower dyadic-window envelope required for the limsup squeeze. -/
lemma ae_eventually_mul_levyModulus_le_dyadicWindowMax_of_ae_eventually_notMem_dyadicRowFailure
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {β : ℝ}
    (hAvoid : ∀ᵐ w ∂μ, ∀ᶠ n : ℕ in atTop, w ∉ dyadicRowFailure B β n) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      ∀ᶠ n : ℕ in atTop,
        β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
          (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
  filter_upwards [hAvoid] with w hw
  intro hcont
  filter_upwards [hw] with n hn
  rcases (notMem_dyadicRowFailure_iff (B := B) (β := β) (n := n) (ω := w)).1 hn with
    ⟨i, hi, hhit⟩
  -- Proof comment: a non-failing row provides one successful adjacent increment, and the earlier
  -- deterministic bridge turns that hit into the required `dyadicWindowMax` lower bound.
  exact
    dyadicRowHit_le_dyadicWindowMax_one (B := B) (w := w) hcont
      (Nat.succ_le_of_lt hi) hhit

/-- Helper for Remark 22.4: summable dyadic row-failure masses already yield the lower dyadic
window envelope, because Borel--Cantelli upgrades summability to eventual row hits and the
deterministic transport has already been isolated. -/
lemma ae_eventually_mul_levyModulus_le_dyadicWindowMax_of_summable_dyadicRowFailure
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : NNReal → Ω → ℝ} {β : ℝ}
    (hsum : Summable (fun n : ℕ => μ.real (dyadicRowFailure B β n))) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      ∀ᶠ n : ℕ in atTop,
        β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
          (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
  -- Proof comment: first convert the summable bad rows to almost-sure eventual avoidance via the
  -- first Borel--Cantelli lemma, then invoke the deterministic bridge from row hits to the
  -- dyadic-window lower envelope.
  have hAvoid :
      ∀ᵐ w ∂μ, ∀ᶠ n : ℕ in atTop, w ∉ dyadicRowFailure B β n :=
    ae_eventually_notMem_of_summable_measureReal (μ := μ) (s := fun n ↦ dyadicRowFailure B β n)
      hsum
  exact
    ae_eventually_mul_levyModulus_le_dyadicWindowMax_of_ae_eventually_notMem_dyadicRowFailure
      (B := B) hAvoid

-- The lower envelope still needs dyadic row-failure summability; the three lemmas below isolate
-- that probabilistic block into explicit placeholders for the next planning pass.
/-- Helper for Remark 22.4: after normalizing the first row-`n` dyadic increment to variance `1`,
Lemma 22.2 gives the Mills lower bound for the hit event at index `0`. -/
lemma dyadicRowHit_zero_measureReal_ge_millsLower
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {β : ℝ} (hβ0 : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
    gaussianPDFReal 0 1 x / (x + 1 / x) ≤ μ.real (dyadicRowHit B β n 0) := by
  let δ : NNReal := ((2 : NNReal)⁻¹) ^ n
  let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
  let Y : Ω → ℝ := fun ω ↦ (B δ ω - B 0 ω) / Real.sqrt (δ : ℝ)
  have hδ_pos : 0 < δ := by
    positivity
  have hδ_real_pos : 0 < (δ : ℝ) := by
    exact_mod_cast hδ_pos
  have hsqrtδ_pos : 0 < Real.sqrt (δ : ℝ) := Real.sqrt_pos.2 hδ_real_pos
  have hIncrement : HasLaw (fun ω ↦ B δ ω - B 0 ω) (gaussianReal 0 δ) μ := by
    -- Proof comment: the first dyadic row increment is the Brownian marginal at time `δ`,
    -- because Brownian motion starts from `0`.
    simpa [δ, hB.zero] using hB.gaussian_marginal (t := δ) hδ_pos
  have hScale :
      HasLaw (fun z : ℝ ↦ (Real.sqrt (δ : ℝ))⁻¹ * z) (gaussianReal 0 1) (gaussianReal 0 δ) := by
    let c : ℝ := (Real.sqrt (δ : ℝ))⁻¹
    let d : NNReal := ⟨c ^ 2, sq_nonneg c⟩
    have hmap :
        (gaussianReal 0 δ).map (fun z : ℝ ↦ c * z) = gaussianReal 0 1 := by
      have hmap0 :
          (gaussianReal 0 δ).map (c * ·) = gaussianReal 0 (d * δ) := by
        simpa [d] using (gaussianReal_map_const_mul (μ := 0) (v := δ) c)
      have hvar : d * δ = 1 := by
        ext
        simp [c, d, NNReal.coe_mul, hδ_real_pos.ne', Real.sq_sqrt hδ_real_pos.le]
      rw [hvar] at hmap0
      simpa [c] using hmap0
    refine ⟨?_, hmap⟩
    fun_prop
  have hScaled : HasLaw Y (gaussianReal 0 1) μ := by
    -- Proof comment: dividing by `sqrt δ` transports the centered Gaussian increment to the
    -- standard normal law.
    simpa [Y, Function.comp, div_eq_mul_inv, mul_comm] using hScale.comp hIncrement
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hx_pos : 0 < x := by
    -- Proof comment: the dyadic threshold `x = β * sqrt (2 n log 2)` is positive because
    -- `β > 0`, `n ≥ 1`, and `log 2 > 0`.
    dsimp [x]
    have hinside_pos : 0 < 2 * (n : ℝ) * Real.log 2 := by
      have hn_real_pos : 0 < (n : ℝ) := by
        positivity
      positivity
    positivity
  have hThreshold :
      x * Real.sqrt (δ : ℝ) = β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) := by
    -- Proof comment: this is the dyadic threshold transport from the standardized normal
    -- coordinate back to the Brownian increment scale `β * h(2^{-n})`.
    rw [levyModulusOfContinuity_dyadic]
    dsimp [x, δ]
    have hpow_nonneg : 0 ≤ (((2 : ℝ)⁻¹) ^ n) := by
      positivity
    have hsqrt_mul :
        Real.sqrt (((2 : ℝ)⁻¹) ^ n) * Real.sqrt (2 * (n : ℝ) * Real.log 2) =
          Real.sqrt ((((2 : ℝ)⁻¹) ^ n) * (2 * (n : ℝ) * Real.log 2)) := by
      rw [Real.sqrt_mul hpow_nonneg]
    calc
      β * Real.sqrt (2 * (n : ℝ) * Real.log 2) * Real.sqrt (((2 : ℝ)⁻¹) ^ n)
          = β * (Real.sqrt (((2 : ℝ)⁻¹) ^ n) * Real.sqrt (2 * (n : ℝ) * Real.log 2)) := by
              ring
      _ = β * Real.sqrt ((((2 : ℝ)⁻¹) ^ n) * (2 * (n : ℝ) * Real.log 2)) := by
            rw [hsqrt_mul]
      _ = β * Real.sqrt (2 * (((2 : ℝ)⁻¹) ^ n) * ((n : ℝ) * Real.log 2)) := by
            congr 2
            ring
  have hEvent : Y ⁻¹' Set.Ici x = dyadicRowHit B β n 0 := by
    ext ω
    constructor
    · intro hω
      have hω' : x * Real.sqrt (δ : ℝ) ≤ B δ ω - B 0 ω := by
        exact (le_div_iff₀ hsqrtδ_pos).1 hω
      have hω'' : β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤ B δ ω - B 0 ω := by
        calc
          β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) = x * Real.sqrt (δ : ℝ) :=
            hThreshold.symm
          _ ≤ B δ ω - B 0 ω := hω'
      simpa [dyadicRowHit, δ] using hω''
    · intro hω
      have hω' : β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤ B δ ω - B 0 ω := by
        simpa [δ, dyadicRowHit] using hω
      have : x * Real.sqrt (δ : ℝ) ≤ B δ ω - B 0 ω := by
        calc
          x * Real.sqrt (δ : ℝ) = β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) :=
            hThreshold
          _ ≤ B δ ω - B 0 ω := hω'
      exact (le_div_iff₀ hsqrtδ_pos).2 this
  -- Proof comment: once the increment is normalized to variance `1`, Lemma 22.2 applies
  -- directly to the preimage of the closed ray `Set.Ici x`.
  change gaussianPDFReal 0 1 x / (x + 1 / x) ≤ μ.real (dyadicRowHit B β n 0)
  simpa [hEvent] using
    (HasLaw.standardNormal_tail_bounds (P := μ) (X := Y) hScaled hx_pos).1

/-- Helper for Remark 22.4: the row-`n` dyadic failure event is the product of the complements of
the independent row hits, and stationarity identifies every factor with the `i = 0` mass. -/
lemma dyadicRowFailure_measureReal_le_hitZeroComplPow
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {β : ℝ} (n : ℕ) :
    μ.real (dyadicRowFailure B β n) ≤ (1 - μ.real (dyadicRowHit B β n 0)) ^ (2 ^ n) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let δ : NNReal := ((2 : NNReal)⁻¹) ^ n
  let τ : ℕ → NNReal := fun i ↦ (i : NNReal) * δ
  let Y : ℕ → Ω → ℝ := fun i ω ↦ B (τ (i + 1)) ω - B (τ i) ω
  let A : Set ℝ := Set.Iio (β * levyModulusOfContinuity δ)
  have hA_meas : MeasurableSet A := by
    simp [A]
  have hτ_mono : Monotone τ := by
    intro i j hij
    dsimp [τ]
    gcongr
  have hY_meas : ∀ i, Measurable (Y i) := by
    intro i
    exact ((hB.stronglyMeasurable (τ (i + 1))).measurable).sub
      ((hB.stronglyMeasurable (τ i)).measurable)
  have hY_indep : iIndepFun Y μ := by
    -- Proof comment: the dyadic row increments form an independent family because they are
    -- consecutive increments along the monotone mesh `τ`.
    simpa [Y, τ, add_assoc, add_left_comm, add_comm] using
      hB.indepIncrements.nat (t := τ) hτ_mono
  have hHit_eq :
      ∀ i : ℕ,
        dyadicRowHit B β n i = Y i ⁻¹' Set.Ici (β * levyModulusOfContinuity δ) := by
    intro i
    ext ω
    simp [dyadicRowHit, Y, τ, δ, div_eq_mul_inv, mul_comm]
  have hHitCompl_eq :
      ∀ i : ℕ,
        (dyadicRowHit B β n i)ᶜ = Y i ⁻¹' A := by
    intro i
    ext ω
    simp [A, hHit_eq i, not_le]
  have hFailure_eq :
      dyadicRowFailure B β n = ⋂ i ∈ Finset.range (2 ^ n), Y i ⁻¹' A := by
    ext ω
    simp [dyadicRowFailure, A, hHit_eq, not_le]
  have hFactor :
      μ (dyadicRowFailure B β n) = ∏ i ∈ Finset.range (2 ^ n), μ (Y i ⁻¹' A) := by
    -- Proof comment: after rewriting row failure as a finite intersection of complement
    -- threshold events, finite independence collapses the row mass to a product.
    rw [hFailure_eq]
    simpa using
      hY_indep.measure_inter_preimage_eq_mul (Finset.range (2 ^ n))
        (fun _ _ ↦ hA_meas)
  have hFactorEq :
      ∀ i ∈ Finset.range (2 ^ n), μ (Y i ⁻¹' A) = μ ((dyadicRowHit B β n 0)ᶜ) := by
    intro i hi
    have hτ_step : τ i + δ = τ (i + 1) := by
      -- Proof comment: the dyadic mesh advances by one fixed step `δ` on each successor index.
      dsimp [τ]
      calc
        (i : NNReal) * δ + δ = (i : NNReal) * δ + 1 * δ := by rw [one_mul]
        _ = ((i : NNReal) + 1) * δ := by rw [← add_mul]
        _ = ((i + 1 : ℕ) : NNReal) * δ := by norm_num
    have hτ_step' : δ + τ i = τ (i + 1) := by
      simpa [add_comm] using hτ_step
    have hYi :
        Y i = fun ω ↦ B (δ + τ i) ω - B (τ i) ω := by
      -- Proof comment: rewrite the successor endpoint of the `i`-th row increment into the exact
      -- `τ i + δ` spelling used by stationary increments.
      funext ω
      change B (τ (i + 1)) ω - B (τ i) ω = B (δ + τ i) ω - B (τ i) ω
      rw [← hτ_step']
    have hY0 : Y 0 = fun ω ↦ B δ ω - B 0 ω := by
      -- Proof comment: the zeroth row increment starts at time `0` and has length `δ`.
      funext ω
      simp [Y, τ]
    have hMeasureEq :
        μ ((fun ω ↦ B (δ + τ i) ω - B (τ i) ω) ⁻¹' A) =
          μ ((fun ω ↦ B δ ω - B 0 ω) ⁻¹' A) := by
      let hIdent :=
        hB.stationaryIncrements.identDistrib_increment (r := 0) (s := δ) (t := τ i)
      simpa [add_assoc] using hIdent.measure_preimage_eq hA_meas
    calc
      μ (Y i ⁻¹' A) = μ ((fun ω ↦ B (δ + τ i) ω - B (τ i) ω) ⁻¹' A) := by rw [hYi]
      _ = μ ((fun ω ↦ B δ ω - B 0 ω) ⁻¹' A) := hMeasureEq
      _ = μ (Y 0 ⁻¹' A) := by rw [← hY0]
      _ = μ ((dyadicRowHit B β n 0)ᶜ) := by rw [← hHitCompl_eq 0]
  have hHitMeas : MeasurableSet (dyadicRowHit B β n 0) := by
    rw [hHit_eq]
    exact (hY_meas 0) measurableSet_Ici
  have hHitComplMass :
      μ.real ((dyadicRowHit B β n 0)ᶜ) = 1 - μ.real (dyadicRowHit B β n 0) := by
    -- Proof comment: because `μ` is a probability measure, the complement mass is exactly
    -- `1 - μ.real (dyadicRowHit ... 0)`.
    rw [MeasureTheory.measureReal_compl (μ := μ) hHitMeas, MeasureTheory.probReal_univ]
  refine le_of_eq ?_
  calc
    μ.real (dyadicRowFailure B β n)
        = ∏ i ∈ Finset.range (2 ^ n), μ.real ((dyadicRowHit B β n 0)ᶜ) := by
            rw [MeasureTheory.Measure.real_def, hFactor, ENNReal.toReal_prod]
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [MeasureTheory.Measure.real_def, hFactorEq i hi]
    _ = ∏ _i ∈ Finset.range (2 ^ n), (1 - μ.real (dyadicRowHit B β n 0)) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          exact hHitComplMass
    _ = (1 - μ.real (dyadicRowHit B β n 0)) ^ (2 ^ n) := by
          simp

/-- Helper for Remark 22.4: on dyadic row `n`, the Mills denominator
`x + 1 / x` at the threshold `x = β * sqrt(2 n log 2)` grows at most linearly in `n`. -/
lemma dyadicMillsThreshold_denominator_le_linear
    {β : ℝ} (hβ0 : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
    let c : ℝ := β * Real.sqrt (2 * Real.log 2)
    x + 1 / x ≤ (c + 1 / c) * (n : ℝ) := by
  let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
  let c : ℝ := β * Real.sqrt (2 * Real.log 2)
  have hc_pos : 0 < c := by
    dsimp [c]
    have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hn_real_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hn_real_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hx_eq : x = c * Real.sqrt (n : ℝ) := by
    dsimp [x, c]
    rw [show 2 * (n : ℝ) * Real.log 2 = (2 * Real.log 2) * (n : ℝ) by ring]
    rw [Real.sqrt_mul (show 0 ≤ 2 * Real.log 2 by
      have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      positivity)]
    ring
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [← sq_le_sq₀ (Real.sqrt_nonneg _) hn_real_nonneg, Real.sq_sqrt hn_real_nonneg]
    nlinarith
  have hsqrt_ge_one : 1 ≤ Real.sqrt (n : ℝ) := (Real.one_le_sqrt).2 hn_real_one
  have hx_pos : 0 < x := by
    rw [hx_eq]
    positivity
  have hx_le : x ≤ c * (n : ℝ) := by
    rw [hx_eq]
    exact mul_le_mul_of_nonneg_left hsqrt_le_n hc_pos.le
  have hx_ge_c : c ≤ x := by
    rw [hx_eq]
    calc
      c = c * 1 := by ring
      _ ≤ c * Real.sqrt (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hsqrt_ge_one hc_pos.le
  have hInvx_le : 1 / x ≤ 1 / c := one_div_le_one_div_of_le hc_pos hx_ge_c
  have hInvc_scaled : 1 / c ≤ (1 / c) * (n : ℝ) := by
    calc
      1 / c = (1 / c) * 1 := by ring
      _ ≤ (1 / c) * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_left hn_real_one (by positivity)
  calc
    x + 1 / x ≤ c * (n : ℝ) + 1 / c := add_le_add hx_le hInvx_le
    _ ≤ c * (n : ℝ) + (1 / c) * (n : ℝ) := add_le_add le_rfl hInvc_scaled
    _ = (c + 1 / c) * (n : ℝ) := by ring

/-- Helper for Remark 22.4: the standard Gaussian density at the dyadic Mills threshold
`β * sqrt(2 n log 2)` has the explicit dyadic profile `2^(-(β^2) n)`. -/
lemma dyadicMillsThreshold_gaussianPDF_eq (β : ℝ) (n : ℕ) :
    let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
    gaussianPDFReal 0 1 x =
      (1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ))) := by
  let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
  have hGauss :
      gaussianPDFReal 0 1 x =
        (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2) := by
    simp [gaussianPDFReal_def, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hx_sq :
      x ^ 2 = β ^ 2 * (2 * (n : ℝ) * Real.log 2) := by
    dsimp [x]
    calc
      (β * Real.sqrt (2 * (n : ℝ) * Real.log 2)) ^ 2
          = β ^ 2 * (Real.sqrt (2 * (n : ℝ) * Real.log 2)) ^ 2 := by ring
      _ = β ^ 2 * (2 * (n : ℝ) * Real.log 2) := by
            rw [Real.sq_sqrt (by positivity)]
  calc
    gaussianPDFReal 0 1 x = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(x ^ 2) / 2) := hGauss
    _ = (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(β ^ 2 * (n : ℝ) * Real.log 2)) := by
          rw [hx_sq]
          congr 2
          ring
    _ = (1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ))) := by
          rw [show -(β ^ 2 * (n : ℝ) * Real.log 2) =
              Real.log 2 * (-(β ^ 2 * (n : ℝ))) by ring]
          rw [Real.exp_mul, Real.exp_log (by norm_num : 0 < (2 : ℝ))]

/-- Helper for Remark 22.4: for every `0 < β < 1`, the renormalized first hit probability on the
`n`-th dyadic row eventually dominates `n`. -/
lemma eventually_natCast_le_twoPow_mul_dyadicRowHit_zero_measureReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ≤ (2 : ℝ) ^ n * μ.real (dyadicRowHit B β n 0) := by
  let c : ℝ := β * Real.sqrt (2 * Real.log 2)
  let K : ℝ := (1 / Real.sqrt (2 * Real.pi)) / (c + 1 / c)
  let base : ℝ := (2 : ℝ) ^ (1 - β ^ 2)
  have hlog2_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc_pos : 0 < c := by
    -- Proof comment: the linear denominator constant `c = β * sqrt (2 log 2)` is positive.
    dsimp [c]
    positivity
  have hK_pos : 0 < K := by
    -- Proof comment: the prefactor coming from the Gaussian density and Mills denominator is
    -- strictly positive, so exponential growth of `base ^ n` eventually beats the polynomial loss.
    dsimp [K]
    positivity
  have hbase_gt_one : 1 < base := by
    -- Proof comment: the exponent `1 - β^2` is positive because `0 < β < 1`.
    have hExp_pos : 0 < 1 - β ^ 2 := by
      nlinarith [sq_nonneg β]
    dsimp [base]
    exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hExp_pos
  have hgrowth :
      ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ 2 ≤ K * base ^ n := by
    have hsmall :
        ∀ᶠ n : ℕ in atTop, ((n : ℝ) ^ 2) / base ^ n < K := by
      simpa [base] using
        (tendsto_pow_const_div_const_pow_of_one_lt 2 hbase_gt_one).eventually (Iio_mem_nhds hK_pos)
    filter_upwards [hsmall] with n hn
    have hbase_pow_pos : 0 < base ^ n := by
      positivity
    have hmul : (n : ℝ) ^ 2 < K * base ^ n := by
      exact (div_lt_iff₀ hbase_pow_pos).1 hn
    exact hmul.le
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [hgrowth, hlarge] with n hgrowth_n hn
  let x : ℝ := β * Real.sqrt (2 * (n : ℝ) * Real.log 2)
  have hn_real_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hhit :
      gaussianPDFReal 0 1 x / (x + 1 / x) ≤ μ.real (dyadicRowHit B β n 0) := by
    -- Proof comment: the row-`n` hit mass is bounded below by the standard Mills lower bound at
    -- the normalized threshold `x = β * sqrt (2 n log 2)`.
    simpa [x] using
      (dyadicRowHit_zero_measureReal_ge_millsLower (μ := μ) (B := B) hB hβ0 (n := n) hn)
  have hden :
      x + 1 / x ≤ (c + 1 / c) * (n : ℝ) := by
    -- Proof comment: replace the Mills denominator by its linear-in-`n` upper bound.
    simpa [x, c] using
      (dyadicMillsThreshold_denominator_le_linear (β := β) hβ0 (n := n) hn)
  have hgauss :
      gaussianPDFReal 0 1 x =
        (1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ))) := by
    -- Proof comment: the Gaussian density at the dyadic threshold has the exact
    -- `2^{-(β² n)}` profile.
    simpa [x] using dyadicMillsThreshold_gaussianPDF_eq β n
  have hx_pos : 0 < x := by
    -- Proof comment: the normalized threshold is positive on the eventual tail `n ≥ 1`.
    dsimp [x]
    positivity
  have hgauss_nonneg : 0 ≤ gaussianPDFReal 0 1 x := by
    rw [hgauss]
    positivity
  have hInv :
      1 / ((c + 1 / c) * (n : ℝ)) ≤ 1 / (x + 1 / x) := by
    have hxden_pos : 0 < x + 1 / x := by positivity
    exact one_div_le_one_div_of_le hxden_pos hden
  have hcore :
      ((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
          ((c + 1 / c) * (n : ℝ)) ≤
        μ.real (dyadicRowHit B β n 0) := by
    -- Proof comment: combine the linear denominator bound with the Mills lower estimate.
    have hdiv :
        gaussianPDFReal 0 1 x / ((c + 1 / c) * (n : ℝ)) ≤
          gaussianPDFReal 0 1 x / (x + 1 / x) := by
      simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hInv hgauss_nonneg
    calc
      ((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
          ((c + 1 / c) * (n : ℝ))
          = gaussianPDFReal 0 1 x / ((c + 1 / c) * (n : ℝ)) := by rw [← hgauss]
      _ ≤ gaussianPDFReal 0 1 x / (x + 1 / x) := hdiv
      _ ≤ μ.real (dyadicRowHit B β n 0) := hhit
  have hprofile :
      K * base ^ n / (n : ℝ) ≤ (2 : ℝ) ^ n * μ.real (dyadicRowHit B β n 0) := by
    -- Proof comment: after multiplying by `2^n`, the exact dyadic Gaussian profile becomes
    -- `K * base^n / n`, which is the form compared against the polynomial term above.
    have hprofile_eq :
        K * base ^ n / (n : ℝ) =
          (2 : ℝ) ^ n *
            (((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
              ((c + 1 / c) * (n : ℝ))) := by
      dsimp [K, base]
      have hc_ne : c ≠ 0 := hc_pos.ne'
      calc
        ((1 / Real.sqrt (2 * Real.pi)) / (c + 1 / c)) * ((2 : ℝ) ^ (1 - β ^ 2)) ^ n / (n : ℝ)
            = ((1 / Real.sqrt (2 * Real.pi)) * ((c + 1 / c) * (n : ℝ))⁻¹) *
                ((2 : ℝ) ^ n * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) := by
                  rw [← Real.rpow_mul_natCast (show 0 ≤ (2 : ℝ) by positivity)]
                  rw [show (1 - β ^ 2) * (n : ℝ) = (n : ℝ) + -(β ^ 2 * (n : ℝ)) by ring]
                  rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
                  rw [Real.rpow_natCast]
                  field_simp [hn_real_pos.ne', hc_ne]
        _ = (2 : ℝ) ^ n *
              (((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
                ((c + 1 / c) * (n : ℝ))) := by
                  field_simp [hn_real_pos.ne', hc_ne]
    have hmul :
        (2 : ℝ) ^ n *
            (((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
              ((c + 1 / c) * (n : ℝ))) ≤
          (2 : ℝ) ^ n * μ.real (dyadicRowHit B β n 0) := by
      exact mul_le_mul_of_nonneg_left hcore (by positivity)
    calc
      K * base ^ n / (n : ℝ)
          = (2 : ℝ) ^ n *
              (((1 / Real.sqrt (2 * Real.pi)) * (2 : ℝ) ^ (-(β ^ 2 * (n : ℝ)))) /
                ((c + 1 / c) * (n : ℝ))) := hprofile_eq
      _ ≤ (2 : ℝ) ^ n * μ.real (dyadicRowHit B β n 0) := hmul
  have hn_le_profile : (n : ℝ) ≤ K * base ^ n / (n : ℝ) := by
    -- Proof comment: the exponential factor `base ^ n` eventually dominates `n^2`, so after one
    -- division by the positive factor `n` we recover the desired linear lower bound.
    have hn_sq : (n : ℝ) * (n : ℝ) ≤ K * base ^ n := by
      simpa [pow_two] using hgrowth_n
    exact (le_div_iff₀ hn_real_pos).2 hn_sq
  exact le_trans hn_le_profile hprofile

/-- Helper for Remark 22.4: summability of the dyadic row-failure masses provides the lower
probabilistic input for the one-step dyadic window envelope. -/
lemma summable_dyadicRowFailure_measureReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Summable (fun n : ℕ => μ.real (dyadicRowFailure B β n)) := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  obtain ⟨N, hN⟩ :=
    Filter.mem_atTop_sets.mp
      (eventually_natCast_le_twoPow_mul_dyadicRowHit_zero_measureReal
        (μ := μ) (B := B) hB hβ0 hβ1)
  have htail :
      Summable (fun n : ℕ => μ.real (dyadicRowFailure B β (n + N))) := by
    have hExpTail :
        Summable (fun n : ℕ => Real.exp (-(((n + N : ℕ) : ℝ)))) := by
      -- Proof comment: the exponential comparison sequence is summable on every shifted tail.
      have hbase :=
        Real.summable_exp_nat_mul_of_ge (c := -1) (by norm_num)
          (f := fun n : ℕ ↦ ((n + N : ℕ) : ℝ)) (fun n ↦ by
            change (n : ℝ) ≤ ((n + N : ℕ) : ℝ)
            exact_mod_cast (Nat.le_add_right n N : n ≤ n + N))
      simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hbase
    refine hExpTail.of_nonneg_of_le (fun _ ↦ MeasureTheory.measureReal_nonneg) ?_
    intro n
    let m : ℕ := n + N
    have hm_ge : N ≤ m := by
      dsimp [m]
      exact Nat.le_add_left N n
    have hm_tail :
        (m : ℝ) ≤ (2 : ℝ) ^ m * μ.real (dyadicRowHit B β m 0) := by
      exact hN m hm_ge
    have hhit_le_one :
        μ.real (dyadicRowHit B β m 0) ≤ 1 := by
      -- Proof comment: hit events are measurable subsets of the whole probability space, so their
      -- real masses are at most `1`.
      simpa [m] using
        (MeasureTheory.measureReal_mono (μ := μ) (Set.subset_univ (dyadicRowHit B β m 0)))
    have hpow :
        (1 - μ.real (dyadicRowHit B β m 0)) ^ (2 ^ m) ≤
          Real.exp (-((2 ^ m : ℕ) : ℝ) * μ.real (dyadicRowHit B β m 0)) := by
      -- Proof comment: compress the product of row-hit complements into one exponential term.
      simpa [m] using
        (one_sub_pow_le_exp_neg_mul (p := μ.real (dyadicRowHit B β m 0)) hhit_le_one (2 ^ m))
    have hExpCompare :
        Real.exp (-((2 ^ m : ℕ) : ℝ) * μ.real (dyadicRowHit B β m 0)) ≤
          Real.exp (-(m : ℝ)) := by
      -- Proof comment: the eventual lower bound on `2^m * μ(hit)` turns the exponential
      -- compression into the model summable tail `exp (-m)`.
      apply Real.exp_monotone
      have hm_pow :
          (m : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) * μ.real (dyadicRowHit B β m 0) := by
        simpa using hm_tail
      linarith
    calc
      μ.real (dyadicRowFailure B β (n + N))
          ≤ (1 - μ.real (dyadicRowHit B β m 0)) ^ (2 ^ m) := by
              simpa [m] using
                (dyadicRowFailure_measureReal_le_hitZeroComplPow
                  (μ := μ) (B := B) hB m)
      _ ≤ Real.exp (-((2 ^ m : ℕ) : ℝ) * μ.real (dyadicRowHit B β m 0)) := hpow
      _ ≤ Real.exp (-(m : ℝ)) := hExpCompare
      _ = Real.exp (-(((n + N : ℕ) : ℝ))) := by simp [m]
  -- Proof comment: summability of the shifted tail is equivalent to summability of the whole row
  -- sequence, so the lower Borel--Cantelli input is now complete.
  exact (_root_.summable_nat_add_iff N).1 htail

/-- Helper for Remark 22.4: the Lévy modulus is positive on every positive scale below `1`. -/
lemma levyModulusOfContinuity_pos_of_pos_lt_one
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < levyModulusOfContinuity δ := by
  -- Proof comment: for `0 < δ < 1`, the logarithmic factor `log (1 / δ)` is positive, so the
  -- square-root definition of the Lévy modulus is strictly positive.
  rw [levyModulusOfContinuity_eq]
  apply Real.sqrt_pos.2
  have hδ0' : 0 < (δ : ℝ) := by
    exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) < 1 := by
    exact_mod_cast hδ1
  have hlog : 0 < Real.log (1 / (δ : ℝ)) := by
    have hinv : 1 < (δ : ℝ)⁻¹ := by
      exact (one_lt_inv₀ hδ0').2 hδ1'
    simpa [one_div] using Real.log_pos hinv
  positivity

/-- Helper for Remark 22.4: the corrected non-anchored refined dyadic scale factor
`((2^r + 3) / 2^r)` stays uniformly below `4`. -/
lemma one_le_refinedDyadicScaleFactor_addThree (r : ℕ) :
    (1 : NNReal) ≤ (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) := by
  -- Proof comment: the corrected refined factor is still at least `1` because its numerator
  -- dominates the denominator term `2^r`.
  have hpow_pos : (0 : NNReal) < (2 : NNReal) ^ r := by
    positivity
  refine (le_div_iff₀ hpow_pos).2 ?_
  have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
    norm_num
  rw [hpow_cast]
  have hNat : (1 : ℕ) * 2 ^ r ≤ 2 ^ r + 3 := by
    nlinarith
  exact_mod_cast hNat

/-- Helper for Remark 22.4: the corrected non-anchored refined dyadic scale factor
`((2^r + 3) / 2^r)` stays uniformly below `4`. -/
lemma refinedDyadicScaleFactor_addThree_le_four (r : ℕ) :
    (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) ≤ 4 := by
  have hpow_pos : (0 : NNReal) < (2 : NNReal) ^ r := by
    positivity
  refine (div_le_iff₀ hpow_pos).2 ?_
  have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
    norm_num
  rw [hpow_cast]
  have hpow_nat_pos : 1 ≤ 2 ^ r := by
    exact Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hNat : (2 ^ r + 3 : ℕ) ≤ 4 * 2 ^ r := by
    nlinarith
  exact_mod_cast hNat

/-- Helper for Remark 22.4: some corrected refined dyadic dilation factor is eventually small
enough to lie below the target square `α²`. -/
lemma exists_refinedDyadicScaleFactor_addThree_lt_sq {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ,
      ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r : NNReal) : ℝ) < α ^ (2 : ℕ) := by
  have hgap : 0 < α ^ (2 : ℕ) - 1 := by
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hgap
  refine ⟨N + 2, ?_⟩
  have hpow_ge : (N + 1 : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast Nat.succ_le_of_lt N.lt_two_pow_self
  have hInv_le : 1 / (2 : ℝ) ^ N ≤ 1 / (N + 1 : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hpow_ge
  have hfactor_eq :
      ((((2 ^ (N + 2) + 3 : ℕ) : NNReal) / (2 : NNReal) ^ (N + 2) : NNReal) : ℝ) =
        1 + (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ N) := by
    -- Proof comment: expand the corrected factor and cancel the shared power `2^(N + 2)`.
    norm_num [NNReal.coe_div, NNReal.coe_pow]
    field_simp [show (2 : ℝ) ^ N ≠ 0 by positivity]
    ring
  have hsmall :
      (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ N) < α ^ (2 : ℕ) - 1 := by
    have hthreeQuarters :
        (3 / 4 : ℝ) * (1 / (2 : ℝ) ^ N) ≤ 1 / (2 : ℝ) ^ N := by
      nlinarith [show 0 ≤ 1 / (2 : ℝ) ^ N by positivity]
    exact lt_of_le_of_lt hthreeQuarters (lt_of_le_of_lt hInv_le hN)
  rw [hfactor_eq]
  linarith

/-- Helper for Remark 22.4: for every `α > 1`, one corrected refined dyadic factor makes the
Lévy modulus stable under dilation by that factor on sufficiently small scales. -/
lemma eventually_levyModulus_correctedRefinedFactor_le_mul
    {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ, ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      levyModulusOfContinuity ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) ≤
        α * levyModulusOfContinuity δ := by
  rcases exists_refinedDyadicScaleFactor_addThree_lt_sq hα with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  let c : NNReal := (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r)
  have hc1 : 1 ≤ c := one_le_refinedDyadicScaleFactor_addThree r
  have hcα : (c : ℝ) ≤ α ^ (2 : ℕ) := le_of_lt hr
  have hsmall :
      {δ : NNReal | c * δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    have hcont : Continuous fun δ : NNReal ↦ c * δ := continuous_const.mul continuous_id
    exact mem_nhdsWithin_of_mem_nhds <|
      hcont.continuousAt.preimage_mem_nhds
        (Iio_mem_nhds (by simpa using (show (0 : NNReal) < 1 by norm_num)))
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hδsmall
  exact levyModulus_mul_le_of_factor_sqBound hα hc1 hcα hδ hδsmall

/-- Helper for Remark 22.4: every sufficiently small scale `δ` is covered from above by one
refined dyadic window length `J * 2 ^ (-(n + r))`, and the covering overhead is controlled by the
refined factor `((2 ^ r + 2) / 2 ^ r)`. -/
lemma existsRefinedWindowLengthCoveringScale
    (r : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      ∃ n J : ℕ,
        1 ≤ J ∧
        J ≤ 2 ^ r + 2 ∧
        δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ∧
        (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ≤
          ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := by
  have hsmall :
      {δ : NNReal | δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ0 hδ1
  obtain ⟨n, hnear, hle⟩ :=
    exists_nat_pow_near_of_lt_one hδ0 hδ1.le
      (show 0 < ((2 : NNReal)⁻¹) by norm_num)
      (show ((2 : NNReal)⁻¹) < 1 by norm_num)
  let x : NNReal := δ * (2 : NNReal) ^ (n + r)
  let J : ℕ := Nat.ceil ((x : NNReal) : ℝ)
  have hx_pos : 0 < x := by
    -- Proof comment: the refined dyadic scaling keeps the positive input scale positive.
    dsimp [x]
    exact mul_pos hδ0 (by positivity)
  have hJ1 : 1 ≤ J := by
    -- Proof comment: the scaled length `x = δ * 2^(n + r)` is positive, so its ceiling is a
    -- nontrivial admissible window length.
    exact Nat.one_le_ceil_iff.mpr (by exact_mod_cast hx_pos)
  have hx_le_pow : x ≤ (2 : NNReal) ^ r := by
    -- Proof comment: the dyadic sandwich `δ ≤ 2^(-n)` keeps the scaled length below `2^r`.
    dsimp [x]
    calc
      δ * (2 : NNReal) ^ (n + r) ≤ ((2 : NNReal)⁻¹) ^ n * (2 : NNReal) ^ (n + r) := by
        gcongr
      _ = (2 : NNReal) ^ r := by
        rw [pow_add]
        calc
          ((2 : NNReal)⁻¹) ^ n * ((2 : NNReal) ^ n * (2 : NNReal) ^ r)
              = ((((2 : NNReal)⁻¹) ^ n * (2 : NNReal) ^ n) * (2 : NNReal) ^ r) := by
                  ac_rfl
          _ = (1 : NNReal) * (2 : NNReal) ^ r := by
                rw [inv_pow, inv_mul_cancel₀]
                positivity
          _ = (2 : NNReal) ^ r := by simp
  have hJ_bound : J ≤ 2 ^ r + 2 := by
    have hJpow : J ≤ 2 ^ r := by
      exact Nat.ceil_le.mpr (by exact_mod_cast hx_le_pow)
    omega
  have hx_le_J : x ≤ J := by
    -- Proof comment: the ceiling is the least integer dominating the scaled target length.
    exact_mod_cast (Nat.le_ceil ((x : NNReal) : ℝ))
  have hx_step :
      x * ((2 : NNReal)⁻¹) ^ (n + r) = δ := by
    -- Proof comment: multiplying the scaled length by the matching refined mesh size cancels the
    -- dyadic rescaling exactly.
    calc
      x * ((2 : NNReal)⁻¹) ^ (n + r)
          = δ * ((2 : NNReal) ^ (n + r) * ((2 : NNReal) ^ (n + r))⁻¹) := by
              dsimp [x]
              rw [inv_pow]
              ac_rfl
      _ = δ * 1 := by
            rw [mul_inv_cancel₀]
            positivity
      _ = δ := by simp
  have hδ_le_length :
      δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := by
    -- Proof comment: the chosen refined window length is the ceiling multiple of the dyadic mesh,
    -- so it dominates `δ`.
    calc
      δ = x * ((2 : NNReal)⁻¹) ^ (n + r) := hx_step.symm
      _ ≤ (J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) := by
            exact mul_le_mul_of_nonneg_right hx_le_J (by positivity)
  have hJ_le_x_add_one : (J : NNReal) ≤ x + 1 := by
    have hJ_lt : ((J : ℕ) : ℝ) < (((x : NNReal) : ℝ)) + 1 := by
      exact Nat.ceil_lt_add_one (by positivity)
    exact_mod_cast (le_of_lt hJ_lt)
  have hpow_lt :
      ((2 : NNReal)⁻¹) ^ n < (2 : NNReal) * δ := by
    -- Proof comment: the left half of the dyadic sandwich upgrades `2^(-(n + 1)) < δ` to the
    -- coarser estimate `2^(-n) < 2δ`.
    have hmul := mul_lt_mul_of_pos_right hnear (show (0 : NNReal) < 2 by norm_num)
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hmul
  have hstep_le :
      ((2 : NNReal)⁻¹) ^ (n + r) ≤ ((2 : NNReal) / (2 : NNReal) ^ r) * δ := by
    -- Proof comment: the refined mesh size is `2^(-r)` times `2^(-n)`, and the previous estimate
    -- bounds the coarse dyadic scale `2^(-n)` by `2δ`.
    calc
      ((2 : NNReal)⁻¹) ^ (n + r)
          = ((2 : NNReal)⁻¹) ^ r * ((2 : NNReal)⁻¹) ^ n := by
              rw [pow_add]
              ac_rfl
      _ ≤ ((2 : NNReal)⁻¹) ^ r * ((2 : NNReal) * δ) := by
            exact mul_le_mul_of_nonneg_left hpow_lt.le (by positivity)
      _ = ((2 : NNReal) / (2 : NNReal) ^ r) * δ := by
            rw [div_eq_mul_inv, inv_pow]
            ac_rfl
  have hfactor_eq :
      ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) =
        δ + (((2 : NNReal) / (2 : NNReal) ^ r) * δ) := by
    have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
      norm_num
    have hsplit :
        (((2 ^ r + 2 : ℕ) : NNReal)) = ((2 ^ r : ℕ) : NNReal) + 2 := by
      norm_num
    have hfirst :
        ((((2 ^ r : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) = δ := by
      have hpow_ne : (((2 ^ r : ℕ) : NNReal)) ≠ 0 := by
        positivity
      rw [hpow_cast, show ((((2 ^ r : ℕ) : NNReal) / (((2 ^ r : ℕ) : NNReal))) = 1) by
        rw [div_self hpow_ne], one_mul]
    -- Proof comment: split the refined factor `((2^r + 2) / 2^r)` as `1 + 2 / 2^r`.
    calc
      ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ)
          = ((((2 ^ r : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) +
              (((2 : NNReal) / (2 : NNReal) ^ r) * δ) := by
                rw [hsplit, add_div, add_mul]
      _ = δ + (((2 : NNReal) / (2 : NNReal) ^ r) * δ) := by
            rw [hfirst]
  have hlength_le :
      (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ≤
        ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := by
    -- Proof comment: the ceiling contributes one extra refined mesh step, and that extra step is
    -- absorbed by the refined factor `1 + 2 / 2^r`.
    calc
      ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r))
          ≤ (x + 1) * ((2 : NNReal)⁻¹) ^ (n + r) := by
              exact mul_le_mul_of_nonneg_right hJ_le_x_add_one (by positivity)
      _ = x * ((2 : NNReal)⁻¹) ^ (n + r) + ((2 : NNReal)⁻¹) ^ (n + r) := by
            rw [add_mul, one_mul]
      _ = δ + ((2 : NNReal)⁻¹) ^ (n + r) := by
            rw [hx_step]
      _ ≤ δ + (((2 : NNReal) / (2 : NNReal) ^ r) * δ) := by
            gcongr
      _ = ((((2 ^ r + 2 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := hfactor_eq.symm
  exact ⟨n, J, hJ1, hJ_bound, hδ_le_length, hlength_le⟩

/-- Helper for Remark 22.4: for the corrected non-anchored refined row, the admissible window
lengths are eventually below `1`. -/
lemma eventually_refinedUpperOscillationWindowLength_lt_one (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
        (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) < 1 := by
  -- Proof comment: isolate the fixed corrected-width factor `J * 2^{-r}` and bound it uniformly
  -- by `4`; the remaining `2^{-n}` term tends to `0`, so eventually the whole window length is
  -- strictly below `1`.
  have hpow :
      Tendsto (fun n : ℕ ↦ (4 : NNReal) * ((2 : NNReal)⁻¹) ^ n) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : NNReal)⁻¹) (by norm_num)))
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (4 : NNReal) * ((2 : NNReal)⁻¹) ^ n < 1 := by
    simpa using hpow.eventually (Iio_mem_nhds (by norm_num : (0 : NNReal) < 1))
  filter_upwards [hsmall] with n hn J hJ
  have hJr : J ≤ 2 ^ r + 3 := (Finset.mem_Icc.mp hJ).2
  have hJscaled :
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r ≤ 4 := by
    calc
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r
          ≤ (((2 ^ r + 3 : ℕ) : NNReal)) * ((2 : NNReal)⁻¹) ^ r := by
              gcongr
      _ = (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) := by
            simp [div_eq_mul_inv]
      _ ≤ 4 := refinedDyadicScaleFactor_addThree_le_four r
  calc
    (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal))
        = ((J : NNReal) * ((2 : NNReal)⁻¹) ^ r) * (((2 : NNReal)⁻¹) ^ n) := by
            rw [pow_add]
            ac_rfl
    _ ≤ 4 * (((2 : NNReal)⁻¹) ^ n) := by
          exact mul_le_mul_of_nonneg_right hJscaled (by positivity)
    _ < 1 := hn

/-- Helper for Remark 22.4: for the corrected non-anchored refined row, the admissible window
lengths are eventually below `1 / 2`. -/
lemma eventually_refinedUpperOscillationWindowLength_lt_half (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
        (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) < (1 / 2 : NNReal) := by
  -- Proof comment: the same decomposition as above reduces the claim to the decay of
  -- `4 * 2^{-n}`, and now we take the tail small enough to lie below `1 / 2`.
  have hpow :
      Tendsto (fun n : ℕ ↦ (4 : NNReal) * ((2 : NNReal)⁻¹) ^ n) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : NNReal)⁻¹) (by norm_num)))
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (4 : NNReal) * ((2 : NNReal)⁻¹) ^ n < (1 / 2 : NNReal) := by
    simpa using hpow.eventually (Iio_mem_nhds (by norm_num : (0 : NNReal) < (1 / 2 : NNReal)))
  filter_upwards [hsmall] with n hn J hJ
  have hJr : J ≤ 2 ^ r + 3 := (Finset.mem_Icc.mp hJ).2
  have hJscaled :
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r ≤ 4 := by
    calc
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r
          ≤ (((2 ^ r + 3 : ℕ) : NNReal)) * ((2 : NNReal)⁻¹) ^ r := by
              gcongr
      _ = (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) := by
            simp [div_eq_mul_inv]
      _ ≤ 4 := refinedDyadicScaleFactor_addThree_le_four r
  calc
    (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal))
        = ((J : NNReal) * ((2 : NNReal)⁻¹) ^ r) * (((2 : NNReal)⁻¹) ^ n) := by
            rw [pow_add]
            ac_rfl
    _ ≤ 4 * (((2 : NNReal)⁻¹) ^ n) := by
          exact mul_le_mul_of_nonneg_right hJscaled (by positivity)
    _ < (1 / 2 : NNReal) := hn

/-- Helper for Remark 22.4: the corrected non-anchored refined bad-window event records a pair of
times in one refined window whose oscillation exceeds the Lévy threshold at that window length. -/
def refinedUpperOscillationBadWindowEvent
    (B : NNReal → Ω → ℝ) (α : ℝ) (N i J : ℕ) : Set Ω :=
  {ω | ∃ s t : NNReal,
      s ∈
          Set.Icc
            ((i : NNReal) / (2 : NNReal) ^ N)
            (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ N) ∧
        t ∈
          Set.Icc
            ((i : NNReal) / (2 : NNReal) ^ N)
            (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ N) ∧
        α * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) <
          |B t ω - B s ω|}

/-- Helper for Remark 22.4: the corrected non-anchored refined bad row is the finite union of the
pairwise oscillation bad-window events on row `n + r`. The cap shifts from `2^r + 2` to
`2^r + 3` because two endpoint roundings can add one extra refined mesh step. -/
def refinedUpperOscillationBadRow
    (B : NNReal → Ω → ℝ) (α : ℝ) (r n : ℕ) : Set Ω :=
  {ω | ∃ i J : ℕ,
      i + J ≤ 2 ^ (n + r) ∧
      1 ≤ J ∧
      J ≤ 2 ^ r + 3 ∧
      ω ∈ refinedUpperOscillationBadWindowEvent B α (n + r) i J}

/-- Helper for Remark 22.4: any explicit non-anchored refined-window witness puts the sample point
into the corrected oscillation bad row. -/
lemma mem_refinedUpperOscillationBadRow_of_exists_window
    {B : NNReal → Ω → ℝ} {α : ℝ} {r n i J : ℕ} {ω : Ω}
    (hij : i + J ≤ 2 ^ (n + r))
    (hJ1 : 1 ≤ J)
    (hJr : J ≤ 2 ^ r + 3)
    (hω : ω ∈ refinedUpperOscillationBadWindowEvent B α (n + r) i J) :
    ω ∈ refinedUpperOscillationBadRow B α r n := by
  -- Proof comment: the corrected bad row is defined by packaging one admissible non-anchored
  -- refined bad window on the same row.
  exact ⟨i, J, hij, hJ1, hJr, hω⟩

/-- Helper for Remark 22.4: if a sample path avoids one corrected oscillation bad window, then
every pair of times inside that window already satisfies the target Lévy bound. -/
lemma abs_sub_le_of_notMem_refinedUpperOscillationBadWindowEvent
    {B : NNReal → Ω → ℝ} {α : ℝ} {N i J : ℕ} {ω : Ω}
    (hω : ω ∉ refinedUpperOscillationBadWindowEvent B α N i J)
    {s t : NNReal}
    (hs :
      s ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ N)
          (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ N))
    (ht :
      t ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ N)
          (((i + J : ℕ) : NNReal) / (2 : NNReal) ^ N)) :
    |B t ω - B s ω| ≤ α * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) := by
  -- Proof comment: if one pair inside the same refined window exceeded the threshold, it would
  -- witness membership in the bad-window event; negating that event gives the required bound.
  by_contra hbound
  exact hω ⟨s, t, hs, ht, lt_of_not_ge hbound⟩

/-- Helper for Remark 22.4: every corrected oscillation bad row is contained in the finite union
of its non-anchored bad-window events indexed by the admissible pairs `(i, J)`. -/
lemma refinedUpperOscillationBadRow_subset_windowUnion
    {B : NNReal → Ω → ℝ} {α : ℝ} (r n : ℕ) :
    refinedUpperOscillationBadRow B α r n ⊆
      ⋃ J ∈ Finset.Icc 1 (2 ^ r + 3),
        ⋃ i ∈ Finset.range (2 ^ (n + r) + 1),
          refinedUpperOscillationBadWindowEvent B α (n + r) i J := by
  -- Proof comment: unpack the corrected bad-row witness and insert its `(J, i)` indices into the
  -- finite biunion that defines the row-wise cover.
  intro ω hω
  rcases hω with ⟨i, J, hij, hJ1, hJr, hω⟩
  have hi_le : i ≤ 2 ^ (n + r) := by
    omega
  have hi_mem : i ∈ Finset.range (2 ^ (n + r) + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le)
  refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ?_⟩
  refine ⟨Finset.mem_Icc.mpr ⟨hJ1, hJr⟩, ?_⟩
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ?_⟩
  exact ⟨hi_mem, hω⟩

/-- Helper for Remark 22.4: the mass of one corrected oscillation bad row is bounded by the finite
sum of the masses of its indexed non-anchored bad-window events. -/
lemma measureReal_refinedUpperOscillationBadRow_le_windowSum
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} {α : ℝ} (r n : ℕ) :
    μ.real (refinedUpperOscillationBadRow B α r n) ≤
      ∑ J ∈ Finset.Icc 1 (2 ^ r + 3),
        ∑ i ∈ Finset.range (2 ^ (n + r) + 1),
          μ.real (refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
  -- Proof comment: rewrite the bad row as the exact finite union over admissible `(J, i)` pairs,
  -- then apply finite subadditivity and finally enlarge each admissible `i`-range to the fixed
  -- row range `0, ..., 2^(n+r)`.
  have hrow_eq :
      refinedUpperOscillationBadRow B α r n =
        ⋃ J ∈ Finset.Icc 1 (2 ^ r + 3),
          ⋃ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
            refinedUpperOscillationBadWindowEvent B α (n + r) i J := by
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨i, J, hij, hJ1, hJr, hω⟩
      have hi_le : i ≤ 2 ^ (n + r) := by omega
      have hi_mem : i ∈ (Finset.range (2 ^ (n + r) + 1)).filter
          (fun i ↦ i + J ≤ 2 ^ (n + r)) := by
        refine Finset.mem_filter.2 ?_
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), hij⟩
      refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ?_⟩
      refine ⟨Finset.mem_Icc.mpr ⟨hJ1, hJr⟩, ?_⟩
      refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ?_⟩
      exact ⟨hi_mem, hω⟩
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨J, hω⟩
      rcases Set.mem_iUnion.1 hω with ⟨hJ, hω⟩
      rcases Set.mem_iUnion.1 hω with ⟨i, hω⟩
      rcases Set.mem_iUnion.1 hω with ⟨hi, hω⟩
      rcases Finset.mem_Icc.mp hJ with ⟨hJ1, hJr⟩
      rcases Finset.mem_filter.mp hi with ⟨_, hij⟩
      exact ⟨i, J, hij, hJ1, hJr, hω⟩
  calc
    μ.real (refinedUpperOscillationBadRow B α r n) =
        μ.real
          (⋃ J ∈ Finset.Icc 1 (2 ^ r + 3),
            ⋃ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
              refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
          rw [hrow_eq]
    _ ≤
        ∑ J ∈ Finset.Icc 1 (2 ^ r + 3),
          μ.real
            (⋃ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
              refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
          exact MeasureTheory.measureReal_biUnion_finset_le (μ := μ) (Finset.Icc 1 (2 ^ r + 3))
            (fun J ↦
              ⋃ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
                refinedUpperOscillationBadWindowEvent B α (n + r) i J)
    _ ≤
        ∑ J ∈ Finset.Icc 1 (2 ^ r + 3),
          ∑ i ∈ Finset.range (2 ^ (n + r) + 1),
            μ.real (refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
          refine Finset.sum_le_sum ?_
          intro J hJ
          calc
            μ.real
                (⋃ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
                  refinedUpperOscillationBadWindowEvent B α (n + r) i J) ≤
                ∑ i ∈ (Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)),
                  μ.real (refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
                    exact
                      MeasureTheory.measureReal_biUnion_finset_le (μ := μ)
                        ((Finset.range (2 ^ (n + r) + 1)).filter (fun i ↦ i + J ≤ 2 ^ (n + r)))
                        (fun i ↦ refinedUpperOscillationBadWindowEvent B α (n + r) i J)
            _ ≤
                ∑ i ∈ Finset.range (2 ^ (n + r) + 1),
                  μ.real (refinedUpperOscillationBadWindowEvent B α (n + r) i J) := by
                    exact
                      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                        (fun i _ _ ↦ MeasureTheory.measureReal_nonneg)

/-- Helper for Remark 22.4: once `n ≥ 2`, the corrected refined window length `2^r + 3` fits
inside a full row-`n + r` dyadic partition of `[0, 1]`. -/
lemma correctedRefinedWindowSteps_le_rowWidth
    (r n : ℕ) (hn : 2 ≤ n) :
    2 ^ r + 3 ≤ 2 ^ (n + r) := by
  have hpow_pos : 1 ≤ 2 ^ r := by
    exact Nat.succ_le_of_lt (pow_pos (by decide) _)
  have hcoarse : 2 ^ r + 3 ≤ 4 * 2 ^ r := by
    nlinarith
  calc
    2 ^ r + 3 ≤ 4 * 2 ^ r := hcoarse
    _ = 2 ^ (2 + r) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← Nat.pow_add]
    _ ≤ 2 ^ (n + r) := by
          refine Nat.pow_le_pow_right (by decide) ?_
          omega

/-- Helper for Remark 22.4: the rightmost corrected refined window on row `n + r` ends exactly at
`1`. This is the stable arithmetic identity needed in the clipped-endpoint case of the covering
argument. -/
lemma correctedRefinedWindow_lastRightEndpoint_eq_one
    (r n : ℕ) (hn : 2 ≤ n) :
    ((((2 ^ (n + r) - (2 ^ r + 3) + (2 ^ r + 3) : ℕ) : NNReal) / (2 : NNReal) ^ (n + r)) : NNReal)
      = 1 := by
  -- Proof comment: the last admissible left index is `2^(n+r) - (2^r + 3)`, and adding the
  -- corrected width lands exactly at the full row length `2^(n+r)`.
  rw [Nat.sub_add_cancel (correctedRefinedWindowSteps_le_rowWidth r n hn)]
  norm_num

/-- Helper for Remark 22.4: the corrected window length on row `n + r` is the corrected refined
factor `((2^r + 3) / 2^r)` times the coarse dyadic mesh `2^{-n}`. -/
lemma correctedRefinedWindowLength_eq_factor_mul_dyadic
    (r n : ℕ) :
    (((2 ^ r + 3 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal) =
      ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)) := by
  -- Proof comment: split the refined power `2^{-(n+r)}` into `2^{-r} * 2^{-n}` once, then rewrite
  -- the fixed corrected factor as division by `2^r`.
  rw [pow_add]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Remark 22.4: for `n ≥ 2`, every pair `s ≤ t` with `t - s ≤ 2^{-n}` lies in one
corrected refined window of row `n + r` and width `(2^r + 3) * 2^{-(n + r)}`. -/
lemma exists_correctedRefinedWindow_containing_pair
    (r n : ℕ) (hn : 2 ≤ n) {s t : Set.Icc (0 : NNReal) 1}
    (hst : (s : NNReal) ≤ t)
    (hdist : dist (s : NNReal) t ≤ ((2 : NNReal)⁻¹) ^ n) :
    ∃ i : ℕ,
      i + (2 ^ r + 3) ≤ 2 ^ (n + r) ∧
      (s : NNReal) ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ (n + r))
          (((i + (2 ^ r + 3) : ℕ) : NNReal) / (2 : NNReal) ^ (n + r)) ∧
      (t : NNReal) ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ (n + r))
          (((i + (2 ^ r + 3) : ℕ) : NNReal) / (2 : NNReal) ^ (n + r)) := by
  -- Route correction: the covering witness is the clipped floor of `s * 2^(n+r)`. The clip case
  -- is handled only at the terminal right endpoint `1`; all other arithmetic stays in the same
  -- `NNReal` spelling world.
  let N : ℕ := n + r
  let width : ℕ := 2 ^ r + 3
  let top : ℕ := 2 ^ N - width
  let i0 : ℕ := Nat.floor ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
  let i : ℕ := min i0 top
  have hwidth_le : width ≤ 2 ^ N := by
    simpa [N, width] using correctedRefinedWindowSteps_le_rowWidth r n hn
  have hpow_pos : 0 < (2 : NNReal) ^ N := by
    positivity
  have hi_le_top : i ≤ top := by
    simp [i, top]
  have hi_le_i0 : i ≤ i0 := by
    simp [i, i0]
  have hi_row : i + width ≤ 2 ^ N := by
    calc
      i + width ≤ top + width := by omega
      _ = 2 ^ N := by simpa [top] using (Nat.sub_add_cancel hwidth_le)
  have hi_scaled :
      (i : NNReal) ≤ (s : NNReal) * (2 : NNReal) ^ N := by
    have hfloor_real :
        ((i0 : ℕ) : ℝ) ≤ ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) := by
      exact Nat.floor_le
        (show 0 ≤ ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) by positivity)
    have hi0_scaled :
        (i0 : NNReal) ≤ (s : NNReal) * (2 : NNReal) ^ N := by
      exact_mod_cast hfloor_real
    exact le_trans (by exact_mod_cast hi_le_i0) hi0_scaled
  have hs_left :
      ((i : NNReal) / (2 : NNReal) ^ N) ≤ s := by
    -- Proof comment: the clipped floor index still lies below `s * 2^(n+r)`, so dividing by the
    -- positive row width gives the left endpoint bound.
    refine (div_le_iff₀ hpow_pos).2 ?_
    simpa [mul_assoc, mul_comm, mul_left_comm] using hi_scaled
  have hdist_real :
      ((t : NNReal) : ℝ) - (s : NNReal) ≤ ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) := by
    have hraw :
        |((s : NNReal) : ℝ) - (t : NNReal)| ≤ ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) := by
      simpa [NNReal.dist_eq] using hdist
    have hnonpos : ((s : NNReal) : ℝ) - (t : NNReal) ≤ 0 := by
      exact sub_nonpos.mpr (by exact_mod_cast hst)
    rw [abs_of_nonpos hnonpos] at hraw
    linarith
  have ht_left :
      ((i : NNReal) / (2 : NNReal) ^ N) ≤ t := le_trans hs_left hst
  have hs_upper :
      (s : NNReal) ≤ (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
    by_cases hclip : i0 ≤ top
    · have hi_eq : i = i0 := by
        simp [i, hclip]
      have hs_scaled_one :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i0 : ℝ) + 1 := by
        have hfloor_lt :
            ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) < (i0 : ℝ) + 1 := by
          simpa [i0] using Nat.lt_floor_add_one ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
        simpa using hfloor_lt.le
      have hnum : i0 + 1 ≤ i + width := by
        simp [hi_eq, width]
      have hs_scaled :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i + width : ℕ) := by
        exact le_trans hs_scaled_one (by exact_mod_cast hnum)
      refine (le_div_iff₀ hpow_pos).2 ?_
      exact_mod_cast hs_scaled
    · have hi_eq : i = top := by
        simp [i, top, Nat.le_of_lt (Nat.not_le.mp hclip)]
      calc
        (s : NNReal) ≤ 1 := s.2.2
        _ = (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
            simpa [N, width, top, hi_eq] using
              (correctedRefinedWindow_lastRightEndpoint_eq_one r n hn).symm
  have ht_upper :
      (t : NNReal) ≤ (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
    by_cases hclip : i0 ≤ top
    · have hi_eq : i = i0 := by
        simp [i, hclip]
      have hpow_real_nonneg : 0 ≤ (((2 : NNReal) ^ N : NNReal) : ℝ) := by
        positivity
      have hdelta_mul :
          ((((2 : NNReal)⁻¹) ^ n : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ) =
            (2 ^ r : ℝ) := by
        dsimp [N]
        rw [pow_add]
        have hcancel : ((2 : ℝ)⁻¹) ^ n * (2 : ℝ) ^ n = 1 := by
          rw [inv_pow, inv_mul_cancel₀]
          positivity
        calc
          (2 : ℝ)⁻¹ ^ n * ((2 : ℝ) ^ n * (2 : ℝ) ^ r)
              = (((2 : ℝ)⁻¹) ^ n * (2 : ℝ) ^ n) * (2 : ℝ) ^ r := by ring
          _ = 1 * (2 : ℝ) ^ r := by rw [hcancel]
          _ = (2 : ℝ) ^ r := by simp
      have hs_scaled_one :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i0 : ℝ) + 1 := by
        have hfloor_lt :
            ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) < (i0 : ℝ) + 1 := by
          simpa [i0] using Nat.lt_floor_add_one ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
        simpa using hfloor_lt.le
      have hdist_scaled :
          ((((t : NNReal) : ℝ) - (s : NNReal)) *
              (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤
            (2 ^ r : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hdist_real hpow_real_nonneg
        rw [hdelta_mul] at hmul
        simpa [mul_assoc] using hmul
      have hnum : i0 + 1 + 2 ^ r ≤ i + width := by
        simp [hi_eq, width]
        omega
      have ht_scaled :
          (((t : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i + width : ℕ) := by
        calc
          (((t : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ))
              = (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) +
                  ((((t : NNReal) : ℝ) - (s : NNReal)) *
                    (((2 : NNReal) ^ N : NNReal) : ℝ)) := by ring
          _ ≤ ((i0 : ℝ) + 1) + (2 ^ r : ℝ) := by gcongr
          _ ≤ (i + width : ℕ) := by exact_mod_cast hnum
      refine (le_div_iff₀ hpow_pos).2 ?_
      exact_mod_cast ht_scaled
    · have hi_eq : i = top := by
        simp [i, top, Nat.le_of_lt (Nat.not_le.mp hclip)]
      calc
        (t : NNReal) ≤ 1 := t.2.2
        _ = (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
            simpa [N, width, top, hi_eq] using
              (correctedRefinedWindow_lastRightEndpoint_eq_one r n hn).symm
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa [N, width] using hi_row
  · refine ⟨?_, ?_⟩
    · simpa [N] using hs_left
    · simpa [N, width] using hs_upper
  · refine ⟨?_, ?_⟩
    · simpa [N] using ht_left
    · simpa [N, width] using ht_upper

/-- Helper for Remark 22.4: if `t - s` is at most `J * 2^{-N}`, then both points lie in one
refined row-`N` window of width `(J + 1) * 2^{-N}`. This isolates the variable-width endpoint
rounding used in the remaining upper-envelope assembly. -/
lemma exists_refinedWindow_containing_pair_of_le_length
    (N J : ℕ) (hJrow : J + 1 ≤ 2 ^ N) {s t : Set.Icc (0 : NNReal) 1}
    (hst : (s : NNReal) ≤ t)
    (hdist : dist (s : NNReal) t ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N : NNReal))) :
    ∃ i : ℕ,
      i + (J + 1) ≤ 2 ^ N ∧
      (s : NNReal) ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ N)
          (((i + (J + 1) : ℕ) : NNReal) / (2 : NNReal) ^ N) ∧
      (t : NNReal) ∈
        Set.Icc
          ((i : NNReal) / (2 : NNReal) ^ N)
          (((i + (J + 1) : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
  -- Proof comment: clip the floor index of `s * 2^N` against the last admissible left endpoint,
  -- then the scaled gap bound contributes at most `J` extra mesh steps, so width `J + 1` covers
  -- both rounded endpoints.
  let width : ℕ := J + 1
  let top : ℕ := 2 ^ N - width
  let i0 : ℕ := Nat.floor ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
  let i : ℕ := min i0 top
  have hpow_pos : 0 < (2 : NNReal) ^ N := by
    positivity
  have hi_le_top : i ≤ top := by
    simp [i, top]
  have hi_le_i0 : i ≤ i0 := by
    simp [i, i0]
  have hi_row : i + width ≤ 2 ^ N := by
    calc
      i + width ≤ top + width := by omega
      _ = 2 ^ N := by simpa [top] using (Nat.sub_add_cancel hJrow)
  have hi_scaled :
      (i : NNReal) ≤ (s : NNReal) * (2 : NNReal) ^ N := by
    have hfloor_real :
        ((i0 : ℕ) : ℝ) ≤ ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) := by
      exact Nat.floor_le
        (show 0 ≤ ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) by positivity)
    have hi0_scaled :
        (i0 : NNReal) ≤ (s : NNReal) * (2 : NNReal) ^ N := by
      exact_mod_cast hfloor_real
    exact le_trans (by exact_mod_cast hi_le_i0) hi0_scaled
  have hs_left :
      ((i : NNReal) / (2 : NNReal) ^ N) ≤ s := by
    -- Proof comment: dividing the floor-index bound by the positive mesh denominator gives the
    -- left endpoint inequality.
    refine (div_le_iff₀ hpow_pos).2 ?_
    simpa [mul_assoc, mul_comm, mul_left_comm] using hi_scaled
  have hdist_real :
      ((t : NNReal) : ℝ) - (s : NNReal) ≤
        ((((J : NNReal) * ((2 : NNReal)⁻¹) ^ N : NNReal) : ℝ)) := by
    have hraw :
        |((s : NNReal) : ℝ) - (t : NNReal)| ≤
          ((((J : NNReal) * ((2 : NNReal)⁻¹) ^ N : NNReal) : ℝ)) := by
      simpa [NNReal.dist_eq] using hdist
    have hnonpos : ((s : NNReal) : ℝ) - (t : NNReal) ≤ 0 := by
      exact sub_nonpos.mpr (by exact_mod_cast hst)
    rw [abs_of_nonpos hnonpos] at hraw
    linarith
  have ht_left :
      ((i : NNReal) / (2 : NNReal) ^ N) ≤ t := le_trans hs_left hst
  have hs_upper :
      (s : NNReal) ≤ (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
    by_cases hclip : i0 ≤ top
    · have hi_eq : i = i0 := by
        simp [i, hclip]
      have hs_scaled_one :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i0 : ℝ) + 1 := by
        have hfloor_lt :
            ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) < (i0 : ℝ) + 1 := by
          simpa [i0] using Nat.lt_floor_add_one ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
        simpa using hfloor_lt.le
      have hnum : i0 + 1 ≤ i + width := by
        rw [hi_eq]
        dsimp [width]
        omega
      have hs_scaled :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i + width : ℕ) := by
        exact le_trans hs_scaled_one (by exact_mod_cast hnum)
      refine (le_div_iff₀ hpow_pos).2 ?_
      exact_mod_cast hs_scaled
    · have hi_eq : i = top := by
        simp [i, top, Nat.le_of_lt (Nat.not_le.mp hclip)]
      have hright_one :
          ((((top + width : ℕ) : NNReal) / (2 : NNReal) ^ N) : NNReal) = 1 := by
        dsimp [top, width]
        rw [Nat.sub_add_cancel hJrow]
        norm_num
      calc
        (s : NNReal) ≤ 1 := s.2.2
        _ = (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
            rw [hi_eq]
            simpa [top, width] using hright_one.symm
  have ht_upper :
      (t : NNReal) ≤ (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
    by_cases hclip : i0 ≤ top
    · have hi_eq : i = i0 := by
        simp [i, hclip]
      have hpow_real_nonneg : 0 ≤ (((2 : NNReal) ^ N : NNReal) : ℝ) := by
        positivity
      have hdelta_mul :
          ((((J : NNReal) * ((2 : NNReal)⁻¹) ^ N : NNReal) : ℝ) *
              (((2 : NNReal) ^ N : NNReal) : ℝ)) = (J : ℝ) := by
        have hcancel : ((2 : ℝ)⁻¹) ^ N * (2 : ℝ) ^ N = 1 := by
          rw [inv_pow, inv_mul_cancel₀]
          positivity
        calc
          (J : ℝ) * (2 : ℝ)⁻¹ ^ N * (2 : ℝ) ^ N
              = (J : ℝ) * (((2 : ℝ)⁻¹) ^ N * (2 : ℝ) ^ N) := by ring
          _ = (J : ℝ) * 1 := by rw [hcancel]
          _ = (J : ℝ) := by ring
      have hs_scaled_one :
          (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i0 : ℝ) + 1 := by
        have hfloor_lt :
            ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ)) < (i0 : ℝ) + 1 := by
          simpa [i0] using Nat.lt_floor_add_one ((((s : NNReal) * (2 : NNReal) ^ N : NNReal) : ℝ))
        simpa using hfloor_lt.le
      have hdist_scaled :
          ((((t : NNReal) : ℝ) - (s : NNReal)) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (J : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hdist_real hpow_real_nonneg
        rw [hdelta_mul] at hmul
        simpa [mul_assoc] using hmul
      have hnum : i0 + 1 + J ≤ i + width := by
        rw [hi_eq]
        dsimp [width]
        omega
      have ht_scaled :
          (((t : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) ≤ (i + width : ℕ) := by
        calc
          (((t : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ))
              = (((s : NNReal) : ℝ) * (((2 : NNReal) ^ N : NNReal) : ℝ)) +
                  ((((t : NNReal) : ℝ) - (s : NNReal)) *
                    (((2 : NNReal) ^ N : NNReal) : ℝ)) := by ring
          _ ≤ ((i0 : ℝ) + 1) + (J : ℝ) := by gcongr
          _ ≤ (i + width : ℕ) := by exact_mod_cast hnum
      refine (le_div_iff₀ hpow_pos).2 ?_
      exact_mod_cast ht_scaled
    · have hi_eq : i = top := by
        simp [i, top, Nat.le_of_lt (Nat.not_le.mp hclip)]
      have hright_one :
          ((((top + width : ℕ) : NNReal) / (2 : NNReal) ^ N) : NNReal) = 1 := by
        dsimp [top, width]
        rw [Nat.sub_add_cancel hJrow]
        norm_num
      calc
        (t : NNReal) ≤ 1 := t.2.2
        _ = (((i + width : ℕ) : NNReal) / (2 : NNReal) ^ N) := by
            rw [hi_eq]
            simpa [top, width] using hright_one.symm
  refine ⟨i, ?_, ?_, ?_⟩
  · simpa [width] using hi_row
  · refine ⟨?_, ?_⟩
    · simpa using hs_left
    · simpa [width] using hs_upper
  · refine ⟨?_, ?_⟩
    · simpa using ht_left
    · simpa [width] using ht_upper

/-- Helper for Remark 22.4: once a sample point avoids the corrected oscillation bad row on level
`n`, the pathwise compact-interval oscillation at mesh `2^{-n}` is bounded by the corrected refined
Lévy scale, provided `n ≥ 2`. -/
lemma compactIntervalOscillation_le_correctedRefinedDyadicScale
    {B : NNReal → Ω → ℝ} {ω : Ω} {η : ℝ} (r n : ℕ) (hn : 2 ≤ n)
    (hη0 : 0 ≤ η)
    (hω : ω ∉ refinedUpperOscillationBadRow B η r n)
    (hcont : Continuous fun t ↦ B t ω) :
    ((compactIntervalOscillation 1 (ContinuousMap.mk (fun t ↦ B t ω) hcont) (((2 : NNReal)⁻¹) ^ n) :
        NNReal) : ℝ) ≤
      η * levyModulusOfContinuity
        ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)) := by
  -- Route correction: the deterministic upper bound now goes through the corrected non-anchored
  -- cover directly; the older anchored `+2` block is not used here.
  let ωpath : PathSpace := ContinuousMap.mk (fun t ↦ B t ω) hcont
  let target :
      NNReal := ⟨η * levyModulusOfContinuity
        ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)),
        mul_nonneg hη0 (by
          rw [levyModulusOfContinuity_eq]
          exact Real.sqrt_nonneg _)⟩
  have hbound :
      ∀ s t : Set.Icc (0 : NNReal) (1 : NNReal),
        dist (s : NNReal) t ≤ ((2 : NNReal)⁻¹) ^ n → ‖ωpath s - ωpath t‖₊ ≤ target := by
    intro s t hst
    rcases le_total (s : NNReal) t with hst' | hts'
    · rcases exists_correctedRefinedWindow_containing_pair r n hn hst' hst with
        ⟨i, hij, hs, ht⟩
      have hwindow :
          ω ∉ refinedUpperOscillationBadWindowEvent B η (n + r) i (2 ^ r + 3) := by
        have hJ1 : 1 ≤ 2 ^ r + 3 := by
          exact Nat.succ_le_of_lt (by positivity : 0 < 2 ^ r + 3)
        intro hbad
        exact hω <|
          mem_refinedUpperOscillationBadRow_of_exists_window
            (B := B) (α := η) (r := r) (n := n) (i := i) (J := 2 ^ r + 3)
            hij hJ1 le_rfl hbad
      have habs :
          |B t ω - B s ω| ≤
            η * levyModulusOfContinuity
              ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)) := by
        have habsWindow :=
          abs_sub_le_of_notMem_refinedUpperOscillationBadWindowEvent
            (B := B) (α := η) (N := n + r) (i := i) (J := 2 ^ r + 3) hwindow hs ht
        rw [correctedRefinedWindowLength_eq_factor_mul_dyadic] at habsWindow
        exact habsWindow
      change ((‖ωpath s - ωpath t‖₊ : NNReal) : ℝ) ≤ (target : ℝ)
      simpa [ωpath, target, Real.norm_eq_abs, abs_sub_comm] using habs
    · rcases
        exists_correctedRefinedWindow_containing_pair r n hn hts'
          (by simpa [dist_comm] using hst) with
        ⟨i, hij, ht, hs⟩
      have hwindow :
          ω ∉ refinedUpperOscillationBadWindowEvent B η (n + r) i (2 ^ r + 3) := by
        have hJ1 : 1 ≤ 2 ^ r + 3 := by
          exact Nat.succ_le_of_lt (by positivity : 0 < 2 ^ r + 3)
        intro hbad
        exact hω <|
          mem_refinedUpperOscillationBadRow_of_exists_window
            (B := B) (α := η) (r := r) (n := n) (i := i) (J := 2 ^ r + 3)
            hij hJ1 le_rfl hbad
      have habs :
          |B t ω - B s ω| ≤
            η * levyModulusOfContinuity
              ((((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) * (((2 : NNReal)⁻¹) ^ n)) := by
        have habsWindow :=
          abs_sub_le_of_notMem_refinedUpperOscillationBadWindowEvent
            (B := B) (α := η) (N := n + r) (i := i) (J := 2 ^ r + 3) hwindow ht hs
        rw [correctedRefinedWindowLength_eq_factor_mul_dyadic] at habsWindow
        simpa [abs_sub_comm] using habsWindow
      change ((‖ωpath s - ωpath t‖₊ : NNReal) : ℝ) ≤ (target : ℝ)
      simpa [ωpath, target, Real.norm_eq_abs, abs_sub_comm] using habs
  have hosc :
      compactIntervalOscillation 1 ωpath (((2 : NNReal)⁻¹) ^ n) ≤ target :=
    compactIntervalOscillation_le_of_forall
      (N := 1) (ω := ωpath) (δ := (((2 : NNReal)⁻¹) ^ n)) (η := target)
      (by
        intro s t hst
        have hs_mem : (s : NNReal) ∈ Set.Icc (0 : NNReal) (1 : NNReal) := by
          simpa using s.2
        have ht_mem : (t : NNReal) ∈ Set.Icc (0 : NNReal) (1 : NNReal) := by
          simpa using t.2
        exact hbound ⟨(s : NNReal), hs_mem⟩ ⟨(t : NNReal), ht_mem⟩ (by simpa using hst))
  simpa [target] using hosc

/-- Helper for Remark 22.4: if one corrected refined row is good, then every oscillation at mesh
at most `J * 2 ^ (-(n + r))` is controlled by the successor refined-window length
`(J + 1) * 2 ^ (-(n + r))`. -/
lemma compactIntervalOscillation_le_of_goodRefinedRowAtSuccessorLength
    {B : NNReal → Ω → ℝ} {ω : Ω} {η : ℝ}
    (r n J : ℕ) (hn : 2 ≤ n) (hη0 : 0 ≤ η)
    (hJ1 : 1 ≤ J) (hJr : J ≤ 2 ^ r + 2)
    (hω : ω ∉ refinedUpperOscillationBadRow B η r n)
    (hcont : Continuous fun t ↦ B t ω) {δ : NNReal}
    (hδ : δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal))) :
    ((compactIntervalOscillation 1 (ContinuousMap.mk (fun t ↦ B t ω) hcont) δ :
        NNReal) : ℝ) ≤
      η * levyModulusOfContinuity
        ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := by
  let ωpath : PathSpace := ContinuousMap.mk (fun t ↦ B t ω) hcont
  let target :
      NNReal := ⟨η * levyModulusOfContinuity
        ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)),
        mul_nonneg hη0 (by
          rw [levyModulusOfContinuity_eq]
          exact Real.sqrt_nonneg _)⟩
  have hJrow : J + 1 ≤ 2 ^ (n + r) := by
    have hsucc : J + 1 ≤ 2 ^ r + 3 := by omega
    exact le_trans hsucc (correctedRefinedWindowSteps_le_rowWidth r n hn)
  have hbound :
      ∀ s t : Set.Icc (0 : NNReal) (1 : NNReal),
        dist (s : NNReal) t ≤ δ → ‖ωpath s - ωpath t‖₊ ≤ target := by
    intro s t hst
    rcases le_total (s : NNReal) t with hst' | hts'
    · rcases
        exists_refinedWindow_containing_pair_of_le_length (N := n + r) (J := J) hJrow hst'
          (le_trans hst hδ) with
        ⟨i, hij, hs, ht⟩
      have hwindow :
          ω ∉ refinedUpperOscillationBadWindowEvent B η (n + r) i (J + 1) := by
        intro hbad
        exact hω <|
          mem_refinedUpperOscillationBadRow_of_exists_window
            (B := B) (α := η) (r := r) (n := n) (i := i) (J := J + 1)
            hij (by omega) (by omega) hbad
      have habs :
          |B t ω - B s ω| ≤
            η * levyModulusOfContinuity
              ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := by
        exact
          abs_sub_le_of_notMem_refinedUpperOscillationBadWindowEvent
            (B := B) (α := η) (N := n + r) (i := i) (J := J + 1) hwindow hs ht
      change ((‖ωpath s - ωpath t‖₊ : NNReal) : ℝ) ≤ (target : ℝ)
      simpa [ωpath, target, Real.norm_eq_abs, abs_sub_comm] using habs
    · rcases
        exists_refinedWindow_containing_pair_of_le_length (N := n + r) (J := J) hJrow hts'
          (le_trans (by simpa [dist_comm] using hst) hδ) with
        ⟨i, hij, ht, hs⟩
      have hwindow :
          ω ∉ refinedUpperOscillationBadWindowEvent B η (n + r) i (J + 1) := by
        intro hbad
        exact hω <|
          mem_refinedUpperOscillationBadRow_of_exists_window
            (B := B) (α := η) (r := r) (n := n) (i := i) (J := J + 1)
            hij (by omega) (by omega) hbad
      have habs :
          |B t ω - B s ω| ≤
            η * levyModulusOfContinuity
              ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := by
        have habsWindow :=
          abs_sub_le_of_notMem_refinedUpperOscillationBadWindowEvent
            (B := B) (α := η) (N := n + r) (i := i) (J := J + 1) hwindow ht hs
        simpa [abs_sub_comm] using habsWindow
      change ((‖ωpath s - ωpath t‖₊ : NNReal) : ℝ) ≤ (target : ℝ)
      simpa [ωpath, target, Real.norm_eq_abs, abs_sub_comm] using habs
  have hosc :
      compactIntervalOscillation 1 ωpath δ ≤ target :=
    compactIntervalOscillation_le_of_forall
      (N := 1) (ω := ωpath) (δ := δ) (η := target)
      (by
        intro s t hst
        have hs_mem : (s : NNReal) ∈ Set.Icc (0 : NNReal) (1 : NNReal) := by
          simpa using s.2
        have ht_mem : (t : NNReal) ∈ Set.Icc (0 : NNReal) (1 : NNReal) := by
          simpa using t.2
        exact hbound ⟨(s : NNReal), hs_mem⟩ ⟨(t : NNReal), ht_mem⟩ (by simpa using hst))
  simpa [target] using hosc

/-- Helper for Remark 22.4: the add-four refined factor is eventually below any target square
`α²` with `α > 1`. This is the successor-window companion to the corrected `+3` scale control.
-/
lemma exists_refinedDyadicScaleFactor_addFour_lt_sq {α : ℝ} (hα : 1 < α) :
    ∃ r : ℕ,
      ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r : NNReal) : ℝ) < α ^ (2 : ℕ) := by
  have hgap : 0 < α ^ (2 : ℕ) - 1 := by
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hgap
  refine ⟨N + 2, ?_⟩
  have hpow_ge : (N + 1 : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast Nat.succ_le_of_lt N.lt_two_pow_self
  have hInv_le : 1 / (2 : ℝ) ^ N ≤ 1 / (N + 1 : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hpow_ge
  have hfactor_eq :
      ((((2 ^ (N + 2) + 4 : ℕ) : NNReal) / (2 : NNReal) ^ (N + 2) : NNReal) : ℝ) =
        1 + 1 / (2 : ℝ) ^ N := by
    -- Proof comment: the add-four successor factor is exactly `1 + 2^{-N}` after cancelling
    -- the shared power `2^(N + 2)`.
    norm_num [NNReal.coe_div, NNReal.coe_pow]
    field_simp [show (2 : ℝ) ^ N ≠ 0 by positivity]
    ring
  have hsmall : 1 / (2 : ℝ) ^ N < α ^ (2 : ℕ) - 1 := by
    exact lt_of_le_of_lt hInv_le hN
  rw [hfactor_eq]
  linarith

/-- Helper for Remark 22.4: every sufficiently small scale is covered by a refined row window
whose successor length is at most the add-four refined factor times the original scale, and the
row index can be forced into any prescribed tail. -/
lemma existsRefinedSuccessorWindowLengthCoveringScale
    (r N₀ : ℕ) :
    ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
      ∃ n J : ℕ,
        N₀ ≤ n ∧
        1 ≤ J ∧
        J ≤ 2 ^ r + 2 ∧
        δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ∧
        ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ≤
          ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := by
  have hsmall :
      {δ : NNReal | δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : NNReal) < 1 by norm_num))
  have hsmallTail :
      {δ : NNReal | δ < ((2 : NNReal)⁻¹) ^ (N₀ + 1)} ∈ 𝓝[>] (0 : NNReal) := by
    exact mem_nhdsWithin_of_mem_nhds <|
      Iio_mem_nhds (by positivity : (0 : NNReal) < ((2 : NNReal)⁻¹) ^ (N₀ + 1))
  filter_upwards [self_mem_nhdsWithin, hsmall, hsmallTail] with δ hδ0 hδ1 hδTail
  obtain ⟨n, hnear, hle⟩ :=
    exists_nat_pow_near_of_lt_one hδ0 hδ1.le
      (show 0 < ((2 : NNReal)⁻¹) by norm_num)
      (show ((2 : NNReal)⁻¹) < 1 by norm_num)
  have hN₀ : N₀ ≤ n := by
    have hpow_lt :
        ((2 : NNReal)⁻¹) ^ (n + 1) < ((2 : NNReal)⁻¹) ^ (N₀ + 1) := lt_trans hnear hδTail
    have hidx :
        N₀ + 1 < n + 1 := by
      exact
        (pow_lt_pow_iff_right_of_lt_one₀
          (show 0 < ((2 : NNReal)⁻¹) by positivity)
          (show ((2 : NNReal)⁻¹) < 1 by norm_num)).1 hpow_lt
    omega
  let x : NNReal := δ * (2 : NNReal) ^ (n + r)
  let J : ℕ := Nat.ceil ((x : NNReal) : ℝ)
  have hx_pos : 0 < x := by
    -- Proof comment: the refined dyadic scaling preserves positivity of the base scale.
    dsimp [x]
    exact mul_pos hδ0 (by positivity)
  have hJ1 : 1 ≤ J := by
    exact Nat.one_le_ceil_iff.mpr (by exact_mod_cast hx_pos)
  have hx_le_pow : x ≤ (2 : NNReal) ^ r := by
    -- Proof comment: `δ ≤ 2^{-n}` bounds the scaled length `x = δ * 2^(n + r)` by `2^r`.
    dsimp [x]
    calc
      δ * (2 : NNReal) ^ (n + r) ≤ ((2 : NNReal)⁻¹) ^ n * (2 : NNReal) ^ (n + r) := by
        gcongr
      _ = (2 : NNReal) ^ r := by
        rw [pow_add]
        calc
          ((2 : NNReal)⁻¹) ^ n * ((2 : NNReal) ^ n * (2 : NNReal) ^ r)
              = ((((2 : NNReal)⁻¹) ^ n * (2 : NNReal) ^ n) * (2 : NNReal) ^ r) := by
                  ac_rfl
          _ = (1 : NNReal) * (2 : NNReal) ^ r := by
                rw [inv_pow, inv_mul_cancel₀]
                positivity
          _ = (2 : NNReal) ^ r := by simp
  have hJr : J ≤ 2 ^ r + 2 := by
    have hJpow : J ≤ 2 ^ r := by
      exact Nat.ceil_le.mpr (by exact_mod_cast hx_le_pow)
    omega
  have hx_le_J : x ≤ J := by
    exact_mod_cast (Nat.le_ceil ((x : NNReal) : ℝ))
  have hx_step :
      x * ((2 : NNReal)⁻¹) ^ (n + r) = δ := by
    -- Proof comment: multiplying back by the refined mesh cancels the scaling defining `x`.
    calc
      x * ((2 : NNReal)⁻¹) ^ (n + r)
          = δ * ((2 : NNReal) ^ (n + r) * ((2 : NNReal) ^ (n + r))⁻¹) := by
              dsimp [x]
              rw [inv_pow]
              ac_rfl
      _ = δ * 1 := by
            rw [mul_inv_cancel₀]
            positivity
      _ = δ := by simp
  have hδ_le_length :
      δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := by
    calc
      δ = x * ((2 : NNReal)⁻¹) ^ (n + r) := hx_step.symm
      _ ≤ (J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) := by
            exact mul_le_mul_of_nonneg_right hx_le_J (by positivity)
  have hJsucc_le_x_add_two : ((J + 1 : ℕ) : NNReal) ≤ x + 2 := by
    have hJ_le_x_add_one : (J : NNReal) ≤ x + 1 := by
      have hJ_lt : ((J : ℕ) : ℝ) < (((x : NNReal) : ℝ)) + 1 := by
        exact Nat.ceil_lt_add_one (by positivity)
      exact_mod_cast (le_of_lt hJ_lt)
    calc
      ((J + 1 : ℕ) : NNReal) ≤ (J : NNReal) + 1 := by norm_num
      _ ≤ x + 1 + 1 := by
            gcongr
      _ = x + 2 := by ring
  have hpow_lt :
      ((2 : NNReal)⁻¹) ^ n < (2 : NNReal) * δ := by
    have hmul := mul_lt_mul_of_pos_right hnear (show (0 : NNReal) < 2 by norm_num)
    simpa [pow_succ', mul_assoc, mul_left_comm, mul_comm] using hmul
  have hstep_le :
      ((2 : NNReal)⁻¹) ^ (n + r) ≤ ((2 : NNReal) / (2 : NNReal) ^ r) * δ := by
    calc
      ((2 : NNReal)⁻¹) ^ (n + r)
          = ((2 : NNReal)⁻¹) ^ r * ((2 : NNReal)⁻¹) ^ n := by
              rw [pow_add]
              ac_rfl
      _ ≤ ((2 : NNReal)⁻¹) ^ r * ((2 : NNReal) * δ) := by
            exact mul_le_mul_of_nonneg_left hpow_lt.le (by positivity)
      _ = ((2 : NNReal) / (2 : NNReal) ^ r) * δ := by
            rw [div_eq_mul_inv, inv_pow]
            ac_rfl
  have hsucc_length_le :
      ((((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ≤
        ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := by
    have hfactor_eq :
        ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) =
          δ + (((4 : NNReal) / (2 : NNReal) ^ r) * δ) := by
      have hpow_cast : (2 : NNReal) ^ r = ((2 ^ r : ℕ) : NNReal) := by
        norm_num
      have hfirst :
          ((((2 ^ r : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) = δ := by
        have hpow_ne : (((2 ^ r : ℕ) : NNReal)) ≠ 0 := by
          positivity
        rw [hpow_cast, show ((((2 ^ r : ℕ) : NNReal) / (((2 ^ r : ℕ) : NNReal))) = 1) by
          rw [div_self hpow_ne], one_mul]
      calc
        ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ)
            = ((((2 ^ r : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) +
                (((4 : NNReal) / (2 : NNReal) ^ r) * δ) := by
                  rw [show (((2 ^ r + 4 : ℕ) : NNReal)) = ((2 ^ r : ℕ) : NNReal) + 4 by norm_num]
                  rw [add_div, add_mul]
        _ = δ + (((4 : NNReal) / (2 : NNReal) ^ r) * δ) := by
              rw [hfirst]
    calc
      (((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r))
          ≤ (x + 2) * ((2 : NNReal)⁻¹) ^ (n + r) := by
              exact mul_le_mul_of_nonneg_right hJsucc_le_x_add_two (by positivity)
      _ = x * ((2 : NNReal)⁻¹) ^ (n + r) + 2 * ((2 : NNReal)⁻¹) ^ (n + r) := by
            ring
      _ = δ + 2 * ((2 : NNReal)⁻¹) ^ (n + r) := by
            rw [hx_step]
      _ ≤ δ + 2 * (((2 : NNReal) / (2 : NNReal) ^ r) * δ) := by
            gcongr
      _ = δ + (((4 : NNReal) / (2 : NNReal) ^ r) * δ) := by
            rw [show (2 : NNReal) * (((2 : NNReal) / (2 : NNReal) ^ r) * δ) =
                (((4 : NNReal) / (2 : NNReal) ^ r) * δ) by
              rw [div_eq_mul_inv]
              ring]
      _ = ((((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r) * δ) := hfactor_eq.symm
  exact ⟨n, J, hN₀, hJ1, hJr, hδ_le_length, hsucc_length_le⟩

/-- Helper for Remark 22.4: at Lévy's threshold, the Gaussian exponential factor collapses to the
power `T ^ (η²)` of the window length. -/
lemma exp_neg_sq_mul_levyModulus_div_two_mul_eq_rpow
    {η : ℝ} {T : NNReal} (hT0 : 0 < T) (hT1 : T < 1) :
    Real.exp (-((η * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ))) =
      (T : ℝ) ^ (η ^ (2 : ℕ)) := by
  have hT0' : 0 < (T : ℝ) := by
    exact_mod_cast hT0
  have hT1' : (T : ℝ) < 1 := by
    exact_mod_cast hT1
  rw [levyModulusOfContinuity_eq]
  have hsq_sqrt :
      (Real.sqrt (2 * (T : ℝ) * Real.log (1 / (T : ℝ)))) ^ (2 : ℕ) =
        2 * (T : ℝ) * Real.log (1 / (T : ℝ)) := by
    -- Proof comment: the Lévy modulus is a square root of a positive logarithmic factor on
    -- `0 < T < 1`, so squaring removes the outer square root exactly.
    rw [Real.sq_sqrt]
    have hlog : 0 < Real.log (1 / (T : ℝ)) := by
      have hinv : 1 < (T : ℝ)⁻¹ := by
        exact (one_lt_inv₀ hT0').2 hT1'
      simpa [one_div] using Real.log_pos hinv
    positivity
  calc
    Real.exp (-((η * Real.sqrt (2 * (T : ℝ) * Real.log (1 / (T : ℝ)))) ^ 2) / (2 * (T : ℝ)))
        = Real.exp (-(η ^ (2 : ℕ)) * Real.log (1 / (T : ℝ))) := by
            congr 1
            have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT0'
            field_simp [hT_ne]
            nlinarith [hsq_sqrt]
    _ = Real.exp ((η ^ (2 : ℕ)) * Real.log (T : ℝ)) := by
          rw [one_div, Real.log_inv]
          ring
    _ = (T : ℝ) ^ (η ^ (2 : ℕ)) := by
          rw [← Real.log_rpow hT0']
          exact Real.exp_log (Real.rpow_pos_of_pos hT0' _)

/-- Helper for Remark 22.4: every corrected refined upper window on row `n + r` has length at
most `4 * 2^{-n}`. -/
lemma refinedUpperOscillationWindowLength_le_four_mul_dyadic
    (r n J : ℕ) (hJ : J ∈ Finset.Icc 1 (2 ^ r + 3)) :
    (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) ≤
      4 * (((2 : NNReal)⁻¹) ^ n) := by
  have hJr : J ≤ 2 ^ r + 3 := (Finset.mem_Icc.mp hJ).2
  have hJscaled :
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r ≤ 4 := by
    -- Proof comment: the bounded refined width `J ≤ 2^r + 3` contributes only a fixed factor.
    calc
      (J : NNReal) * ((2 : NNReal)⁻¹) ^ r
          ≤ (((2 ^ r + 3 : ℕ) : NNReal)) * ((2 : NNReal)⁻¹) ^ r := by
              gcongr
      _ = (((2 ^ r + 3 : ℕ) : NNReal) / (2 : NNReal) ^ r) := by
            simp [div_eq_mul_inv]
      _ ≤ 4 := refinedDyadicScaleFactor_addThree_le_four r
  calc
    (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal))
        = ((J : NNReal) * ((2 : NNReal)⁻¹) ^ r) * (((2 : NNReal)⁻¹) ^ n) := by
            rw [pow_add]
            ac_rfl
    _ ≤ 4 * (((2 : NNReal)⁻¹) ^ n) := by
          exact mul_le_mul_of_nonneg_right hJscaled (by positivity)

/-- Helper for Remark 22.4: choose a partition tolerance `ε` and a finite partition size `M` so
that both the endpoint branch exponent `((1 - 2 * ε) * η)^2` and the short-subwindow branch
exponent `M * (ε * η / 2)^2` are strictly larger than `1`. -/
lemma exists_partitionExponentParameters_gt_one
    {η : ℝ} (hη : 1 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      1 < (((1 - 2 * ε) * η) ^ (2 : ℕ)) ∧
      ∃ M : ℕ, 0 < M ∧
        1 < (M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)) := by
  let ε : ℝ := (η - 1) / (4 * η)
  have hη_pos : 0 < η := lt_trans zero_lt_one hη
  have hε_pos : 0 < ε := by
    have hnum_pos : 0 < η - 1 := by
      linarith
    have hden_pos : 0 < 4 * η := by
      positivity
    dsimp [ε]
    exact div_pos hnum_pos hden_pos
  have hε_lt_half : ε < 1 / 2 := by
    -- Proof comment: the explicit choice `ε = (η - 1) / (4 * η)` is strictly smaller than
    -- `1 / 2` because `η` is positive.
    dsimp [ε]
    have hden_pos : 0 < 4 * η := by positivity
    have hnum_lt : η - 1 < 2 * η := by linarith
    exact (div_lt_iff₀ hden_pos).2 (by linarith)
  have hEndpoint_eq : ((1 - 2 * ε) * η) = (η + 1) / 2 := by
    dsimp [ε]
    field_simp [hη_pos.ne']
    ring
  have hEndpoint : 1 < (((1 - 2 * ε) * η) ^ (2 : ℕ)) := by
    -- Proof comment: the explicit choice of `ε` makes the endpoint branch base equal to
    -- `(η + 1) / 2`, which is strictly larger than `1`.
    rw [hEndpoint_eq]
    have hbase : 1 < (η + 1) / 2 := by
      linarith
    nlinarith
  let s : ℝ := ((ε * η / 2) ^ (2 : ℕ))
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  obtain ⟨M, hM_gt⟩ := exists_nat_gt (1 / s)
  have hM_pos_real : 0 < (M : ℝ) := lt_trans (by positivity : 0 < 1 / s) hM_gt
  have hM_pos : 0 < M := by
    exact_mod_cast hM_pos_real
  have hLocal : 1 < (M : ℝ) * s := by
    -- Proof comment: taking `M > 1 / s` forces the short-subwindow exponent `M * s` above `1`.
    exact (div_lt_iff₀ hs_pos).1 hM_gt
  exact ⟨ε, hε_pos, hε_lt_half, hEndpoint, M, hM_pos, by simpa [s] using hLocal⟩

/-- Helper for Remark 22.4: every point of a deterministic window belongs to one interval of an
equal `M`-partition of that window. -/
lemma exists_partitionSubintervalContaining
    {s₀ T : NNReal} {M : ℕ} (hT : 0 < T) (hM : 0 < M) {u : NNReal}
    (hu : u ∈ Set.Icc s₀ (s₀ + T)) :
    ∃ m ∈ Finset.range M,
      u ∈ Set.Icc
        (s₀ + (m : NNReal) * (T / M))
        (s₀ + (((m + 1 : ℕ) : NNReal)) * (T / M)) := by
  let step : NNReal := T / M
  have hstep_pos : 0 < step := by
    dsimp [step]
    positivity
  have hstep_nonneg : 0 ≤ step := hstep_pos.le
  have hM_ne : (M : NNReal) ≠ 0 := by
    positivity
  have hcover :
      s₀ + (M : NNReal) * step = s₀ + T := by
    -- Proof comment: the `M` equal subintervals exactly cover the whole window length `T`.
    dsimp [step]
    calc
      s₀ + (M : NNReal) * (T / M)
          = s₀ + (T * ((M : NNReal) * ((M : NNReal)⁻¹))) := by
              rw [div_eq_mul_inv]
              congr 1
              ac_rfl
      _ = s₀ + T := by rw [mul_inv_cancel₀ hM_ne, mul_one]
  have hex :
      ∃ k : ℕ, k ≤ M ∧ u ≤ s₀ + (k : NNReal) * step := by
    refine ⟨M, le_rfl, ?_⟩
    simpa [hcover] using hu.2
  let k : ℕ := Nat.find hex
  have hk_le : k ≤ M := (Nat.find_spec hex).1
  have hk_upper : u ≤ s₀ + (k : NNReal) * step := (Nat.find_spec hex).2
  by_cases hk0 : k = 0
  · -- Proof comment: if the first partition endpoint already dominates `u`, then `u = s₀`, so
    -- the first subinterval contains it.
    refine ⟨0, Finset.mem_range.mpr hM, ?_⟩
    have hu_eq : u = s₀ := le_antisymm (by simpa [k, hk0] using hk_upper) hu.1
    constructor
    · simp [hu_eq]
    · have hupper : s₀ ≤ s₀ + step := by
        exact le_add_of_nonneg_right hstep_nonneg
      simpa [hu_eq] using hupper
  · -- Proof comment: otherwise take the predecessor of the first partition endpoint above `u`;
    -- minimality then places `u` inside that single partition interval.
    let m : ℕ := k - 1
    have hm_lt_k : m < k := by
      dsimp [m]
      omega
    have hm_le_M : m ≤ M := by
      dsimp [m]
      omega
    have hm_not_upper :
        ¬ (m ≤ M ∧ u ≤ s₀ + (m : NNReal) * step) := by
      intro hm_upper
      exact Nat.not_lt_of_ge (Nat.find_min' hex hm_upper) hm_lt_k
    have hm_lower : s₀ + (m : NNReal) * step < u := by
      exact lt_of_not_ge (fun hle ↦ hm_not_upper ⟨hm_le_M, hle⟩)
    have hk_eq : k = m + 1 := by
      dsimp [m]
      omega
    refine ⟨m, Finset.mem_range.mpr ?_, ?_⟩
    · dsimp [m]
      omega
    · constructor
      · exact hm_lower.le
      · simpa [hk_eq]
          using hk_upper

/-- Helper for Remark 22.4: a large refined-window oscillation is covered either by a large
increment between two partition left endpoints or by a large oscillation inside one piece of a
fixed equal partition. -/
lemma refinedUpperOscillationBadWindowEvent_subset_endpointOscillation_or_partitionSubwindowUnion
    {B : NNReal → Ω → ℝ} {η ε : ℝ} {N i J M : ℕ}
    (_hε0 : 0 < ε) (hM : 0 < M) (hJ1 : 1 ≤ J) :
    refinedUpperOscillationBadWindowEvent B η N i J ⊆
      (⋃ m₁ ∈ Finset.range M,
        ⋃ m₂ ∈ Finset.range M,
          {ω |
            (1 - 2 * ε) * η *
                levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) <
              |B
                  (((i : NNReal) / (2 : NNReal) ^ N) +
                    (m₂ : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M)) ω -
                B
                  (((i : NNReal) / (2 : NNReal) ^ N) +
                    (m₁ : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M)) ω|}) ∪
        ⋃ m ∈ Finset.range M,
          {ω | ∃ u ∈ Set.Icc
              (((i : NNReal) / (2 : NNReal) ^ N) +
                (m : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M))
              (((i : NNReal) / (2 : NNReal) ^ N) +
                (((m + 1 : ℕ) : NNReal)) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M)),
            ∃ v ∈ Set.Icc
              (((i : NNReal) / (2 : NNReal) ^ N) +
                (m : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M))
              (((i : NNReal) / (2 : NNReal) ^ N) +
                (((m + 1 : ℕ) : NNReal)) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) / M)),
              ε * η * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ N) <
                |B v ω - B u ω|} := by
  intro ω hω
  let s₀ : NNReal := (i : NNReal) / (2 : NNReal) ^ N
  let T : NNReal := (J : NNReal) * ((2 : NNReal)⁻¹) ^ N
  let step : NNReal := T / M
  let endpointGridEvent : Set Ω :=
    ⋃ m₁ ∈ Finset.range M,
      ⋃ m₂ ∈ Finset.range M,
        {ω |
          (1 - 2 * ε) * η * levyModulusOfContinuity T <
            |B (s₀ + (m₂ : NNReal) * step) ω - B (s₀ + (m₁ : NNReal) * step) ω|}
  let localUnion : Set Ω :=
    ⋃ m ∈ Finset.range M,
      {ω | ∃ u ∈ Set.Icc (s₀ + (m : NNReal) * step) (s₀ + (((m + 1 : ℕ) : NNReal)) * step),
          ∃ v ∈ Set.Icc (s₀ + (m : NNReal) * step) (s₀ + (((m + 1 : ℕ) : NNReal)) * step),
            ε * η * levyModulusOfContinuity T < |B v ω - B u ω|}
  have hJ0 : 0 < J := by
    omega
  have hT : 0 < T := by
    dsimp [T]
    positivity
  rcases hω with ⟨s, t, hs, ht, hlarge⟩
  by_cases hlocal : ω ∈ localUnion
  · -- Proof comment: if one partition subwindow already carries the large oscillation, we are in
    -- the local branch of the cover.
    right
    exact hlocal
  · -- Proof comment: otherwise both witnesses are close to the left endpoints of their partition
    -- cells, so the remaining oscillation must already appear between those partition-grid
    -- endpoints.
    left
    have hs_window : s ∈ Set.Icc s₀ (s₀ + T) := by
      simpa [s₀, T, div_eq_mul_inv, Nat.cast_add, add_mul, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using hs
    have ht_window : t ∈ Set.Icc s₀ (s₀ + T) := by
      simpa [s₀, T, div_eq_mul_inv, Nat.cast_add, add_mul, add_assoc, add_left_comm, add_comm,
        mul_assoc, mul_left_comm, mul_comm] using ht
    obtain ⟨ms, hms_mem, hms⟩ :=
      exists_partitionSubintervalContaining (s₀ := s₀) (T := T) hT hM hs_window
    obtain ⟨mt, hmt_mem, hmt⟩ :=
      exists_partitionSubintervalContaining (s₀ := s₀) (T := T) hT hM ht_window
    let ps : NNReal := s₀ + (ms : NNReal) * step
    let pt : NNReal := s₀ + (mt : NNReal) * step
    have hs_small :
        |B s ω - B ps ω| ≤ ε * η * levyModulusOfContinuity T := by
      by_contra hs_small
      have hs_local :
          ω ∈ localUnion := by
        refine Set.mem_iUnion.2 ⟨ms, Set.mem_iUnion.2 ?_⟩
        refine ⟨hms_mem, ?_⟩
        refine ⟨ps, ?_, s, hms, ?_⟩
        · exact ⟨le_rfl, le_trans hms.1 hms.2⟩
        · simpa [ps, abs_sub_comm] using lt_of_not_ge hs_small
      exact hlocal hs_local
    have ht_small :
        |B t ω - B pt ω| ≤ ε * η * levyModulusOfContinuity T := by
      by_contra ht_small
      have ht_local :
          ω ∈ localUnion := by
        refine Set.mem_iUnion.2 ⟨mt, Set.mem_iUnion.2 ?_⟩
        refine ⟨hmt_mem, ?_⟩
        refine ⟨pt, ?_, t, hmt, ?_⟩
        · exact ⟨le_rfl, le_trans hmt.1 hmt.2⟩
        · simpa [pt, abs_sub_comm] using lt_of_not_ge ht_small
      exact hlocal ht_local
    have hps_small :
        |B ps ω - B s ω| ≤ ε * η * levyModulusOfContinuity T := by
      simpa [abs_sub_comm] using hs_small
    have htri :
        |B t ω - B s ω| ≤
          |B t ω - B pt ω| + |B pt ω - B ps ω| + |B ps ω - B s ω| := by
      have hdecomp :
          B t ω - B s ω =
            (B t ω - B pt ω) + ((B pt ω - B ps ω) + (B ps ω - B s ω)) := by
        ring
      calc
        |B t ω - B s ω|
            = |(B t ω - B pt ω) + ((B pt ω - B ps ω) + (B ps ω - B s ω))| := by
                rw [hdecomp]
        _ ≤ |B t ω - B pt ω| + |(B pt ω - B ps ω) + (B ps ω - B s ω)| := by
              exact abs_add_le _ _
        _ ≤ |B t ω - B pt ω| + (|B pt ω - B ps ω| + |B ps ω - B s ω|) := by
              gcongr
              exact abs_add_le _ _
        _ = |B t ω - B pt ω| + |B pt ω - B ps ω| + |B ps ω - B s ω| := by
              ring
    have hendpoint :
        (1 - 2 * ε) * η * levyModulusOfContinuity T < |B pt ω - B ps ω| := by
      have haux :
          η * levyModulusOfContinuity T <
            |B pt ω - B ps ω| + 2 * (ε * η * levyModulusOfContinuity T) := by
        calc
          η * levyModulusOfContinuity T < |B t ω - B s ω| := hlarge
          _ ≤ |B t ω - B pt ω| + |B pt ω - B ps ω| + |B ps ω - B s ω| := htri
          _ ≤ ε * η * levyModulusOfContinuity T +
                |B pt ω - B ps ω| +
                ε * η * levyModulusOfContinuity T := by
                  gcongr
          _ = |B pt ω - B ps ω| + 2 * (ε * η * levyModulusOfContinuity T) := by
                ring
      linarith
    refine Set.mem_iUnion.2 ⟨ms, Set.mem_iUnion.2 ?_⟩
    refine ⟨hms_mem, Set.mem_iUnion.2 ⟨mt, Set.mem_iUnion.2 ?_⟩⟩
    exact ⟨hmt_mem, by simpa [endpointGridEvent, ps, pt, s₀, T, step] using hendpoint⟩

/-- Helper for Remark 22.4: a fixed finite partition of each refined window yields two decay
profiles, one from large endpoint drawups and one from large short-subwindow oscillations. Proving
this is the only remaining probabilistic bridge in the upper-window route. -/
lemma exp_neg_sq_localThreshold_div_two_mul_subwindow_eq_rpow
    {ε η : ℝ} {T : NNReal} {M : ℕ} (hT0 : 0 < T) (hT1 : T < 1) (hM : 0 < M) :
    Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) / (2 * ((T / M : NNReal) : ℝ))) =
      (T : ℝ) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))) := by
  have hT0' : 0 < (T : ℝ) := by
    exact_mod_cast hT0
  have hT1' : (T : ℝ) < 1 := by
    exact_mod_cast hT1
  have hM0' : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hsq_sqrt :
      (Real.sqrt (2 * (T : ℝ) * Real.log (1 / (T : ℝ)))) ^ (2 : ℕ) =
        2 * (T : ℝ) * Real.log (1 / (T : ℝ)) := by
    -- Proof comment: on `0 < T < 1`, the logarithmic factor in Lévy's modulus is positive, so
    -- squaring removes the square root exactly.
    rw [Real.sq_sqrt]
    have hlog : 0 < Real.log (1 / (T : ℝ)) := by
      have hinv : 1 < (T : ℝ)⁻¹ := by
        exact (one_lt_inv₀ hT0').2 hT1'
      simpa [one_div] using Real.log_pos hinv
    positivity
  calc
    Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) / (2 * ((T / M : NNReal) : ℝ)))
        =
          Real.exp (-((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)) * Real.log (1 / (T : ℝ)))) := by
            rw [levyModulusOfContinuity_eq]
            congr 1
            have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT0'
            have hM_ne : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
            field_simp [NNReal.coe_div, hT_ne, hM_ne]
            have hcancel : ((↑(T / M) : ℝ) * (M : ℝ)) = (T : ℝ) := by
              exact_mod_cast div_mul_cancel₀ T (by positivity : (M : NNReal) ≠ 0)
            calc
              -(ε ^ 2 * η ^ 2 * (Real.sqrt (2 * (T : ℝ) * Real.log (1 / (T : ℝ)))) ^ (2 : ℕ))
                  = -(ε ^ 2 * η ^ 2 * (2 * (T : ℝ) * Real.log (1 / (T : ℝ)))) := by
                      rw [hsq_sqrt]
              _ =
                  -(ε ^ 2 * η ^ 2 *
                    (2 * Real.log (1 / (T : ℝ)) * (((↑(T / M) : ℝ) * (M : ℝ))))) := by
                    rw [hcancel]
                    ring
              _ = -(ε ^ 2 * η ^ 2 * 2 * Real.log (1 / (T : ℝ)) * ((↑(T / M) : ℝ)) * (M : ℝ)) := by
                    ring
    _ = Real.exp (((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))) * Real.log (T : ℝ)) := by
          rw [one_div, Real.log_inv]
          ring
    _ = (T : ℝ) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))) := by
          rw [← Real.log_rpow hT0']
          exact Real.exp_log (Real.rpow_pos_of_pos hT0' _)

/-- Helper for Remark 22.4: the discrete endpoint-grid branch of the refined partition cover
decays with the same-threshold exponent `((1 - 2 * ε) * η)^2`. -/
lemma measureReal_endpointOscillationBranch_le_dyadicEndpointPower
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {η ε : ℝ} (hη : 1 < η) (hεlt : ε < 1 / 2) (M : ℕ) (hM : 0 < M) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
          ∀ i : ℕ,
            μ.real
                (⋃ m₁ ∈ Finset.range M,
                  ⋃ m₂ ∈ Finset.range M,
                    {ω |
                      (1 - 2 * ε) * η *
                          levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
                        |B
                            (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                              (m₂ : NNReal) *
                                (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)) ω -
                          B
                            (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                              (m₁ : NNReal) *
                                (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)) ω|}) ≤
              K * ((((2 : ℝ)⁻¹) ^ n) ^ (((1 - 2 * ε) * η) ^ (2 : ℕ))) := by
  -- Route correction: instead of reviving the stalled same-threshold drawup route, use the
  -- strengthened deterministic cover above. The endpoint branch is now a finite grid union of
  -- fixed-time increments, so the existing anchored absolute-increment profile suffices.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hη0 : 0 < η := lt_trans zero_lt_one hη
  let c : ℝ := (1 - 2 * ε) * η
  have hc_pos : 0 < c := by
    dsimp [c]
    have hfac_pos : 0 < 1 - 2 * ε := by
      linarith
    exact mul_pos hfac_pos hη0
  let p : ℝ := c ^ (2 : ℕ)
  let K₀ : ℝ :=
    (M : ℝ) *
      ((M : ℝ) *
        ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) * (4 : ℝ) ^ p))
  refine ⟨K₀, ?_, ?_⟩
  · -- Proof comment: the explicit endpoint-grid constant is a product of nonnegative factors.
    dsimp [K₀, p, c]
    positivity
  · filter_upwards [eventually_refinedUpperOscillationWindowLength_lt_half r] with n hn J hJ i
    let s₀ : NNReal := (i : NNReal) / (2 : NNReal) ^ (n + r)
    let T : NNReal := (J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)
    let step : NNReal := T / M
    let endpointPairEvent : ℕ → ℕ → Set Ω := fun m₁ m₂ ↦
      {ω |
        c * levyModulusOfContinuity T <
          |B (s₀ + (m₂ : NNReal) * step) ω - B (s₀ + (m₁ : NNReal) * step) ω|}
    have hT0 : 0 < T := by
      dsimp [T]
      have hJ0 : 0 < J := by
        exact_mod_cast (Finset.mem_Icc.mp hJ).1
      positivity
    have hT1 : T < 1 := lt_trans (hn J hJ) (by norm_num)
    have hlog_lower : Real.log (1 / (T : ℝ)) ≥ Real.log 2 := by
      have hT_half : (T : ℝ) < 1 / 2 := by
        exact_mod_cast (hn J hJ)
      have hInv_ge : (2 : ℝ) ≤ 1 / (T : ℝ) := by
        have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT0
        exact (le_div_iff₀ hT_pos).2 (by linarith)
      exact Real.log_le_log (by positivity) hInv_ge
    have hLevy_split :
        levyModulusOfContinuity T =
          Real.sqrt (T : ℝ) * Real.sqrt (2 * Real.log (1 / (T : ℝ))) := by
      -- Proof comment: separate the Lévy modulus into the Brownian `√T` scale and the fixed
      -- logarithmic correction used to bound the endpoint-grid coefficient.
      rw [levyModulusOfContinuity_eq]
      rw [show 2 * (T : ℝ) * Real.log (1 / (T : ℝ)) =
            (T : ℝ) * (2 * Real.log (1 / (T : ℝ))) by ring]
      simpa using Real.sqrt_mul hT0.le (2 * Real.log (1 / (T : ℝ)))
    have hSingle :
        ∀ m₁ ∈ Finset.range M, ∀ m₂ ∈ Finset.range M,
          μ.real (endpointPairEvent m₁ m₂) ≤
            (4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) * (T : ℝ) ^ p := by
      intro m₁ hm₁ m₂ hm₂
      let s₁ : NNReal := s₀ + (m₁ : NNReal) * step
      let s₂ : NNReal := s₀ + (m₂ : NNReal) * step
      have hs₁_nonneg : s₀ ≤ s₁ := by
        dsimp [s₁]
        exact le_add_of_nonneg_right (by positivity)
      have hs₂_nonneg : s₀ ≤ s₂ := by
        dsimp [s₂]
        exact le_add_of_nonneg_right (by positivity)
      have hm₁_lt : m₁ < M := Finset.mem_range.mp hm₁
      have hm₂_lt : m₂ < M := Finset.mem_range.mp hm₂
      have hstep_cover : s₀ + (M : NNReal) * step = s₀ + T := by
        dsimp [step]
        have hM_ne : (M : NNReal) ≠ 0 := by positivity
        calc
          s₀ + (M : NNReal) * (T / M)
              = s₀ + (T * ((M : NNReal) * ((M : NNReal)⁻¹))) := by
                  rw [div_eq_mul_inv]
                  congr 1
                  ac_rfl
          _ = s₀ + T := by rw [mul_inv_cancel₀ hM_ne, mul_one]
      have hs₁_end : s₁ ≤ s₀ + T := by
        have hm₁_le : (m₁ : NNReal) ≤ M := by
          exact_mod_cast Nat.le_of_lt hm₁_lt
        have hstep_nonneg : 0 ≤ step := by positivity
        calc
          s₁ ≤ s₀ + (M : NNReal) * step := by
                dsimp [s₁]
                simpa using add_le_add_left (mul_le_mul_of_nonneg_right hm₁_le hstep_nonneg) s₀
          _ = s₀ + T := hstep_cover
      have hs₂_end : s₂ ≤ s₀ + T := by
        have hm₂_le : (m₂ : NNReal) ≤ M := by
          exact_mod_cast Nat.le_of_lt hm₂_lt
        have hstep_nonneg : 0 ≤ step := by positivity
        calc
          s₂ ≤ s₀ + (M : NNReal) * step := by
                dsimp [s₂]
                simpa using add_le_add_left (mul_le_mul_of_nonneg_right hm₂_le hstep_nonneg) s₀
          _ = s₀ + T := hstep_cover
      have hSubset :
          endpointPairEvent m₁ m₂ ⊆
            {ω | ∃ t ∈ Set.Icc (min s₁ s₂) (min s₁ s₂ + T),
                c * levyModulusOfContinuity T < |B t ω - B (min s₁ s₂) ω|} := by
        intro ω hω
        by_cases hm : m₁ ≤ m₂
        · have hs₁_le_s₂ : s₁ ≤ s₂ := by
            have hm_cast : (m₁ : NNReal) ≤ m₂ := by
              exact_mod_cast hm
            have hstep_nonneg : 0 ≤ step := by positivity
            dsimp [s₁, s₂]
            simpa using add_le_add_left (mul_le_mul_of_nonneg_right hm_cast hstep_nonneg) s₀
          refine ⟨s₂, ?_, ?_⟩
          · constructor
            · simpa [min_eq_left hs₁_le_s₂] using hs₁_le_s₂
            · have hs₂_le : s₂ ≤ s₁ + T := by
                exact le_trans hs₂_end (by gcongr)
              simpa [min_eq_left hs₁_le_s₂] using hs₂_le
          · simpa [endpointPairEvent, s₁, s₂, min_eq_left hs₁_le_s₂] using hω
        · have hs₂_le_s₁ : s₂ ≤ s₁ := by
            have hm_cast : (m₂ : NNReal) ≤ m₁ := by
              exact_mod_cast Nat.le_of_lt (lt_of_not_ge hm)
            have hstep_nonneg : 0 ≤ step := by positivity
            dsimp [s₁, s₂]
            simpa using add_le_add_left (mul_le_mul_of_nonneg_right hm_cast hstep_nonneg) s₀
          refine ⟨s₁, ?_, ?_⟩
          · constructor
            · simpa [min_eq_right hs₂_le_s₁] using hs₂_le_s₁
            · have hs₁_le : s₁ ≤ s₂ + T := by
                exact le_trans hs₁_end (by gcongr)
              simpa [min_eq_right hs₂_le_s₁, add_comm, add_left_comm, add_assoc] using hs₁_le
          · simpa [endpointPairEvent, s₁, s₂, min_eq_right hs₂_le_s₁, abs_sub_comm] using hω
      have ha_pos : 0 < c * levyModulusOfContinuity T := by
        exact mul_pos hc_pos (levyModulusOfContinuity_pos_of_pos_lt_one hT0 hT1)
      have hProfile :=
        brownianAnchoredAbsIncrement_measureReal_le_profile
          (B := B) hB (s := min s₁ s₂) (T := T) (a := c * levyModulusOfContinuity T) ha_pos hT0
      have hCoeffBound :
          2 *
              (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) *
                (1 / (c * levyModulusOfContinuity T))) ≤
            4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2)) := by
        have hsqrt_log_inv_le :
            (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹ ≤
              (Real.sqrt (2 * Real.log 2))⁻¹ := by
          have hsqrt_mono :
              Real.sqrt (2 * Real.log 2) ≤ Real.sqrt (2 * Real.log (1 / (T : ℝ))) := by
            refine Real.sqrt_le_sqrt ?_
            nlinarith
          simpa [one_div] using
            one_div_le_one_div_of_le
              (by positivity : 0 < Real.sqrt (2 * Real.log 2))
              hsqrt_mono
        rw [hLevy_split]
        have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := by positivity
        have hcoeff_eq :
            2 *
                (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) *
                  (1 / (c * (Real.sqrt (T : ℝ) * Real.sqrt (2 * Real.log (1 / (T : ℝ))))))) =
              (4 / (c * Real.sqrt (2 * Real.pi))) *
                (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹ := by
          field_simp [hc_pos.ne', hsqrtT_ne,
            show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]
          ring
        rw [hcoeff_eq]
        calc
          (4 / (c * Real.sqrt (2 * Real.pi))) *
              (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹
              ≤
                (4 / (c * Real.sqrt (2 * Real.pi))) *
                  (Real.sqrt (2 * Real.log 2))⁻¹ := by
                    gcongr
          _ = 4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2)) := by
                field_simp [hc_pos.ne',
                  show Real.sqrt (2 * Real.pi) ≠ 0 by positivity,
                  show Real.sqrt (2 * Real.log 2) ≠ 0 by positivity]
      have hExpProfile :
          Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ))) = (T : ℝ) ^ p := by
        simpa [c, p] using
          exp_neg_sq_mul_levyModulus_div_two_mul_eq_rpow (η := c) hT0 hT1
      calc
        μ.real (endpointPairEvent m₁ m₂)
            ≤
              2 *
                (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) *
                  (1 / (c * levyModulusOfContinuity T)) *
                    Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ)))) := by
                  exact
                    (MeasureTheory.measureReal_mono (μ := μ) hSubset (measure_ne_top _ _)).trans
                      hProfile
        _ ≤
            (4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ))) := by
                have hExp_nonneg :
                    0 ≤ Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ))) := by
                  positivity
                have hProfile' :
                    2 *
                        (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) *
                          (1 / (c * levyModulusOfContinuity T)) *
                            Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ)))) =
                      (2 *
                          (((2 * Real.sqrt (T : ℝ)) / Real.sqrt (2 * Real.pi)) *
                            (1 / (c * levyModulusOfContinuity T)))) *
                        Real.exp (-((c * levyModulusOfContinuity T) ^ 2) / (2 * (T : ℝ))) := by
                    ring
                rw [hProfile']
                gcongr
        _ = (4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) * (T : ℝ) ^ p := by
              rw [hExpProfile]
    have hOuter :
        μ.real (⋃ m₁ ∈ Finset.range M, ⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂) ≤
          ∑ m₁ ∈ Finset.range M, μ.real (⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂) := by
      exact
        MeasureTheory.measureReal_biUnion_finset_le
          (μ := μ) (Finset.range M) (fun m₁ ↦ ⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂)
    have hInner :
        ∀ m₁ ∈ Finset.range M,
          μ.real (⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂) ≤
            ∑ m₂ ∈ Finset.range M, μ.real (endpointPairEvent m₁ m₂) := by
      intro m₁ hm₁
      exact
        MeasureTheory.measureReal_biUnion_finset_le
          (μ := μ) (Finset.range M) (endpointPairEvent m₁)
    have hSum :
        ∑ m₁ ∈ Finset.range M, μ.real (⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂) ≤
          (M : ℝ) *
            ((M : ℝ) *
              ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                (T : ℝ) ^ p)) := by
      calc
        ∑ m₁ ∈ Finset.range M, μ.real (⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂)
            ≤ ∑ m₁ ∈ Finset.range M, ∑ m₂ ∈ Finset.range M, μ.real (endpointPairEvent m₁ m₂) := by
                  gcongr with m₁ hm₁
                  exact hInner m₁ hm₁
        _ ≤ ∑ m₁ ∈ Finset.range M,
              ∑ m₂ ∈ Finset.range M,
                ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                  (T : ℝ) ^ p) := by
                  gcongr with m₁ hm₁ m₂ hm₂
                  exact hSingle m₁ hm₁ m₂ hm₂
        _ = (M : ℝ) *
              ((M : ℝ) *
                ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                  (T : ℝ) ^ p)) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
    have hTpow :
        (T : ℝ) ^ p ≤ (4 * (((2 : ℝ)⁻¹) ^ n)) ^ p := by
      have hTle : (T : ℝ) ≤ 4 * (((2 : ℝ)⁻¹) ^ n) := by
        exact_mod_cast refinedUpperOscillationWindowLength_le_four_mul_dyadic r n J hJ
      exact Real.rpow_le_rpow hT0.le hTle (by positivity : 0 ≤ p)
    have hMulRpow :
        (4 * (((2 : ℝ)⁻¹) ^ n)) ^ p = (4 : ℝ) ^ p * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (4 : ℝ))
        (pow_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) _)]
    calc
      μ.real (⋃ m₁ ∈ Finset.range M, ⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂)
          ≤ ∑ m₁ ∈ Finset.range M, μ.real (⋃ m₂ ∈ Finset.range M, endpointPairEvent m₁ m₂) :=
            hOuter
      _ ≤
          (M : ℝ) *
            ((M : ℝ) *
              ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) * (T : ℝ) ^ p)) :=
            hSum
      _ ≤
          (M : ℝ) *
            ((M : ℝ) *
              ((4 / (c * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                ((4 * (((2 : ℝ)⁻¹) ^ n)) ^ p))) := by
                  gcongr
      _ = K₀ * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
            dsimp [K₀]
            rw [hMulRpow]
            ring

/-- Helper for Remark 22.4: the short-subwindow branch of the refined partition cover has the
required dyadic power decay once the Gaussian exponential is normalized at length `T / M`. -/
lemma measureReal_partitionSubwindowUnion_le_dyadicLocalPower
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {η ε : ℝ} (hη : 1 < η) (hε0 : 0 < ε) (M : ℕ) (hM : 0 < M) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
          ∀ i : ℕ,
            μ.real
                (⋃ m ∈ Finset.range M,
                  {ω | ∃ u ∈ Set.Icc
                      (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                        (m : NNReal) *
                          (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M))
                      (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                        (((m + 1 : ℕ) : NNReal)) *
                          (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)),
                    ∃ v ∈ Set.Icc
                      (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                        (m : NNReal) *
                          (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M))
                      (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                        (((m + 1 : ℕ) : NNReal)) *
                          (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)),
                    ε * η * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
                      |B v ω - B u ω|}) ≤
              K * ((((2 : ℝ)⁻¹) ^ n) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) := by
  -- Proof comment: choose one eventual tail where every refined window length satisfies `T < 1/2`
  -- and then sum the uniform single-subwindow oscillation bounds over the finite partition.
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  have hη0 : 0 < η := lt_trans zero_lt_one hη
  let p : ℝ := (M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))
  let K₀ : ℝ :=
    (M : ℝ) *
      (8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
        (4 : ℝ) ^ p
  refine ⟨K₀, ?_, ?_⟩
  · -- Proof comment: the explicit local constant is a product of nonnegative factors.
    dsimp [K₀, p]
    positivity
  · filter_upwards [eventually_refinedUpperOscillationWindowLength_lt_half r] with n hn J hJ i
    let s₀ : NNReal := (i : NNReal) / (2 : NNReal) ^ (n + r)
    let T : NNReal := (J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)
    let step : NNReal := T / M
    let localEvent : ℕ → Set Ω := fun m ↦
      {ω | ∃ u ∈ Set.Icc (s₀ + (m : NNReal) * step) (s₀ + (((m + 1 : ℕ) : NNReal)) * step),
          ∃ v ∈ Set.Icc (s₀ + (m : NNReal) * step) (s₀ + (((m + 1 : ℕ) : NNReal)) * step),
            ε * η * levyModulusOfContinuity T < |B v ω - B u ω|}
    have hT0 : 0 < T := by
      dsimp [T]
      have hJ0 : 0 < J := by
        exact_mod_cast (Finset.mem_Icc.mp hJ).1
      positivity
    have hT1 : T < 1 := lt_trans (hn J hJ) (by norm_num)
    have hStep0 : 0 < step := by
      dsimp [step]
      positivity
    have hStep_le : step ≤ T := by
      dsimp [step]
      have hM_one : (1 : NNReal) ≤ M := by exact_mod_cast Nat.succ_le_of_lt hM
      have hM_pos : (0 : NNReal) < M := by exact_mod_cast hM
      rw [div_eq_mul_inv]
      calc
        T * (M : NNReal)⁻¹ ≤ T * 1 := by
          gcongr
          exact (inv_le_one₀ hM_pos).2 hM_one
        _ = T := by simp
    have hlog_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hlog_lower : Real.log (1 / (T : ℝ)) ≥ Real.log 2 := by
      have hT_half : (T : ℝ) < 1 / 2 := by
        exact_mod_cast (hn J hJ)
      have hInv_ge : (2 : ℝ) ≤ 1 / (T : ℝ) := by
        have hT_pos : 0 < (T : ℝ) := by exact_mod_cast hT0
        exact (le_div_iff₀ hT_pos).2 (by linarith)
      exact Real.log_le_log (by positivity) hInv_ge
    have hLevy_split :
        levyModulusOfContinuity T =
          Real.sqrt (T : ℝ) * Real.sqrt (2 * Real.log (1 / (T : ℝ))) := by
      -- Proof comment: separate the Lévy modulus into the Brownian `√T` scale and the
      -- logarithmic correction needed for the local coefficient bound.
      rw [levyModulusOfContinuity_eq]
      rw [show 2 * (T : ℝ) * Real.log (1 / (T : ℝ)) =
            (T : ℝ) * (2 * Real.log (1 / (T : ℝ))) by ring]
      simpa using Real.sqrt_mul hT0.le (2 * Real.log (1 / (T : ℝ)))
    have hSingle :
        ∀ m ∈ Finset.range M,
          μ.real (localEvent m) ≤
            (8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              (T : ℝ) ^ p := by
      intro m hm
      have ha_pos : 0 < ε * η * levyModulusOfContinuity T := by
        exact mul_pos (mul_pos hε0 hη0) (levyModulusOfContinuity_pos_of_pos_lt_one hT0 hT1)
      have hCoeffProfile :=
        brownianWindowOscillation_measureReal_le_halfThresholdProfile
          (B := B) hB (s := s₀ + (m : NNReal) * step)
          (T := step) (a := ε * η * levyModulusOfContinuity T)
          ha_pos hStep0
      have hCoeffBound :
          2 *
              (((2 * Real.sqrt (step : ℝ)) / Real.sqrt (2 * Real.pi)) *
                (1 / ((ε * η * levyModulusOfContinuity T) / 2))) ≤
            8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2)) := by
        have hεη_pos : 0 < ε * η := by positivity
        have hT0' : 0 < (T : ℝ) := by exact_mod_cast hT0
        have hstep_nonneg : 0 ≤ (step : ℝ) := by positivity
        have hsqrt_step_le : Real.sqrt (step : ℝ) ≤ Real.sqrt (T : ℝ) := by
          exact Real.sqrt_le_sqrt (by exact_mod_cast hStep_le)
        have hsqrt_log_inv_le :
            (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹ ≤
              (Real.sqrt (2 * Real.log 2))⁻¹ := by
          have hsqrt_mono :
              Real.sqrt (2 * Real.log 2) ≤ Real.sqrt (2 * Real.log (1 / (T : ℝ))) := by
            refine Real.sqrt_le_sqrt ?_
            nlinarith
          simpa [one_div] using
            one_div_le_one_div_of_le
              (by positivity : 0 < Real.sqrt (2 * Real.log 2))
              hsqrt_mono
        have hsqrtT_ne : Real.sqrt (T : ℝ) ≠ 0 := by positivity
        have hsqrtLog_ne : Real.sqrt (2 * Real.log (1 / (T : ℝ))) ≠ 0 := by
          apply Real.sqrt_ne_zero'.2
          nlinarith [hlog_lower, hlog_two_pos]
        have hcoeff_eq :
            2 *
                (((2 * Real.sqrt (step : ℝ)) / Real.sqrt (2 * Real.pi)) *
                  (1 / ((ε * η * levyModulusOfContinuity T) / 2))) =
              (8 / (ε * η * Real.sqrt (2 * Real.pi))) *
                (Real.sqrt (step : ℝ) / Real.sqrt (T : ℝ)) *
                (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹ := by
          rw [hLevy_split]
          field_simp [hεη_pos.ne', hsqrtT_ne, hsqrtLog_ne,
            show Real.sqrt (2 * Real.pi) ≠ 0 by positivity]
          ring
        rw [hcoeff_eq]
        have hratio_le_one : Real.sqrt (step : ℝ) / Real.sqrt (T : ℝ) ≤ 1 := by
          refine (div_le_iff₀ (by positivity : 0 < Real.sqrt (T : ℝ))).2 ?_
          simpa using hsqrt_step_le
        calc
          (8 / (ε * η * Real.sqrt (2 * Real.pi))) *
              (Real.sqrt (step : ℝ) / Real.sqrt (T : ℝ)) *
              (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹
              ≤
                (8 / (ε * η * Real.sqrt (2 * Real.pi))) * 1 *
                  (Real.sqrt (2 * Real.log (1 / (T : ℝ))))⁻¹ := by
                    gcongr
          _ ≤ (8 / (ε * η * Real.sqrt (2 * Real.pi))) * 1 *
                (Real.sqrt (2 * Real.log 2))⁻¹ := by
                  gcongr
          _ = 8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2)) := by
                field_simp [show Real.sqrt (2 * Real.pi) ≠ 0 by positivity,
                  show Real.sqrt (2 * Real.log 2) ≠ 0 by positivity, hεη_pos.ne']
      have hExpProfile :
          Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) / (2 * (step : ℝ))) =
            (T : ℝ) ^ p := by
        simpa [step, p] using
          exp_neg_sq_localThreshold_div_two_mul_subwindow_eq_rpow
            (ε := ε) (η := η) (T := T) (M := M) hT0 hT1 hM
      calc
        μ.real (localEvent m)
            ≤
              2 *
                (((2 * Real.sqrt (step : ℝ)) / Real.sqrt (2 * Real.pi)) *
                  (1 / ((ε * η * levyModulusOfContinuity T) / 2)) *
                    Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) /
                      (2 * (step : ℝ)))) := by
                  simpa [localEvent, step, T, s₀, Nat.cast_add, add_mul, add_assoc, add_left_comm,
                    add_comm, mul_assoc, mul_left_comm, mul_comm] using
                    hCoeffProfile
        _ ≤
            (8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) / (2 * (step : ℝ))) := by
                have hExp_nonneg :
                    0 ≤
                      Real.exp
                        (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) / (2 * (step : ℝ))) := by
                  positivity
                have hCoeffProfile' :
                    2 *
                        (((2 * Real.sqrt (step : ℝ)) / Real.sqrt (2 * Real.pi)) *
                          (1 / ((ε * η * levyModulusOfContinuity T) / 2)) *
                            Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) /
                              (2 * (step : ℝ)))) =
                      (2 *
                          (((2 * Real.sqrt (step : ℝ)) / Real.sqrt (2 * Real.pi)) *
                            (1 / ((ε * η * levyModulusOfContinuity T) / 2)))) *
                        Real.exp (-(((ε * η * levyModulusOfContinuity T) / 2) ^ 2) /
                          (2 * (step : ℝ))) := by
                    ring
                rw [hCoeffProfile']
                gcongr
        _ = (8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              (T : ℝ) ^ p := by
                rw [hExpProfile]
    have hUnion :
        μ.real (⋃ m ∈ Finset.range M, localEvent m) ≤
          ∑ m ∈ Finset.range M, μ.real (localEvent m) := by
      exact MeasureTheory.measureReal_biUnion_finset_le (μ := μ) (Finset.range M) localEvent
    have hSum :
        ∑ m ∈ Finset.range M, μ.real (localEvent m) ≤
          (M : ℝ) *
            ((8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              (T : ℝ) ^ p) := by
      calc
        ∑ m ∈ Finset.range M, μ.real (localEvent m)
            ≤ ∑ m ∈ Finset.range M,
                ((8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                  (T : ℝ) ^ p) := by
                    gcongr with m hm
                    exact hSingle m hm
        _ = (M : ℝ) *
              ((8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
                (T : ℝ) ^ p) := by
              simp
    have hTpow :
        (T : ℝ) ^ p ≤ (4 * (((2 : ℝ)⁻¹) ^ n)) ^ p := by
      have hTle : (T : ℝ) ≤ 4 * (((2 : ℝ)⁻¹) ^ n) := by
        exact_mod_cast refinedUpperOscillationWindowLength_le_four_mul_dyadic r n J hJ
      exact Real.rpow_le_rpow hT0.le hTle (by positivity : 0 ≤ p)
    have hMulRpow :
        (4 * (((2 : ℝ)⁻¹) ^ n)) ^ p = (4 : ℝ) ^ p * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (4 : ℝ))
        (pow_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹) _)]
    calc
      μ.real (⋃ m ∈ Finset.range M, localEvent m)
          ≤ ∑ m ∈ Finset.range M, μ.real (localEvent m) := hUnion
      _ ≤ (M : ℝ) *
            ((8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              (T : ℝ) ^ p) := hSum
      _ ≤ (M : ℝ) *
            ((8 / (ε * η * Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.log 2))) *
              ((4 * (((2 : ℝ)⁻¹) ^ n)) ^ p)) := by
                gcongr
      _ = K₀ * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
            dsimp [K₀]
            rw [hMulRpow]
            ring

lemma eventually_measureReal_refinedUpperOscillationBadWindowEvent_le_partitionPowerSum
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {η ε : ℝ} (hη : 1 < η) (hε0 : 0 < ε) (hεlt : ε < 1 / 2) (M : ℕ) (hM : 0 < M) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
          ∀ i : ℕ,
            μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J) ≤
              K * ((((2 : ℝ)⁻¹) ^ n) ^ (((1 - 2 * ε) * η) ^ (2 : ℕ))) +
                K * ((((2 : ℝ)⁻¹) ^ n) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) := by
  -- Proof comment: the deterministic partition cover has already been isolated, so the closing
  -- theorem now only assembles the endpoint and local branch adapters and absorbs their constants.
  rcases measureReal_endpointOscillationBranch_le_dyadicEndpointPower
      (B := B) hB hη hεlt M hM r with ⟨K₁, hK₁, hEndpoint⟩
  rcases measureReal_partitionSubwindowUnion_le_dyadicLocalPower
      (B := B) hB hη hε0 M hM r with ⟨K₂, hK₂, hLocal⟩
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  refine ⟨max K₁ K₂, le_trans hK₁ (le_max_left K₁ K₂), ?_⟩
  filter_upwards [hEndpoint, hLocal] with n hnEndpoint hnLocal J hJ i
  let endpointGridEvent : Set Ω :=
    ⋃ m₁ ∈ Finset.range M,
      ⋃ m₂ ∈ Finset.range M,
        {ω |
          (1 - 2 * ε) * η *
              levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
            |B
                (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                  (m₂ : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)) ω -
              B
                (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
                  (m₁ : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)) ω|}
  let localUnion : Set Ω :=
    ⋃ m ∈ Finset.range M,
      {ω | ∃ u ∈ Set.Icc
          (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
            (m : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M))
          (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
            (((m + 1 : ℕ) : NNReal)) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)),
        ∃ v ∈ Set.Icc
          (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
            (m : NNReal) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M))
          (((i : NNReal) / (2 : NNReal) ^ (n + r)) +
            (((m + 1 : ℕ) : NNReal)) * (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) / M)),
        ε * η * levyModulusOfContinuity ((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r)) <
          |B v ω - B u ω|}
  have hSubset :
      refinedUpperOscillationBadWindowEvent B η (n + r) i J ⊆ endpointGridEvent ∪ localUnion := by
    simpa [endpointGridEvent, localUnion]
      using
        refinedUpperOscillationBadWindowEvent_subset_endpointOscillation_or_partitionSubwindowUnion
          (B := B) (η := η) (ε := ε) (N := n + r) (i := i) (J := J) (M := M)
            hε0 hM (Finset.mem_Icc.mp hJ).1
  have hMain :
      μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J) ≤
        μ.real endpointGridEvent + μ.real localUnion := by
    exact
      (MeasureTheory.measureReal_mono (μ := μ) hSubset (measure_ne_top _ _)).trans
        (MeasureTheory.measureReal_union_le (μ := μ) endpointGridEvent localUnion)
  calc
    μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J)
        ≤ μ.real endpointGridEvent + μ.real localUnion := hMain
    _ ≤
        K₁ * ((((2 : ℝ)⁻¹) ^ n) ^ (((1 - 2 * ε) * η) ^ (2 : ℕ))) +
          K₂ * ((((2 : ℝ)⁻¹) ^ n) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) := by
            gcongr
            · exact hnEndpoint J hJ i
            · exact hnLocal J hJ i
    _ ≤
        max K₁ K₂ * ((((2 : ℝ)⁻¹) ^ n) ^ (((1 - 2 * ε) * η) ^ (2 : ℕ))) +
          max K₁ K₂ * ((((2 : ℝ)⁻¹) ^ n) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) := by
            have hpow₁ :
                0 ≤ ((((2 : ℝ)⁻¹) ^ n) ^ (((1 - 2 * ε) * η) ^ (2 : ℕ))) := by
              positivity
            have hpow₂ :
                0 ≤ ((((2 : ℝ)⁻¹) ^ n) ^ ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) := by
              positivity
            nlinarith [le_max_left K₁ K₂, le_max_right K₁ K₂, hpow₁, hpow₂]

/-- Helper for Remark 22.4: the upper-row summability argument only needs a generic dyadic power
majorant `((2⁻¹)^n)^p` with some exponent `p > 1`; no exact `η²` exponent is required. -/
lemma eventually_measureReal_refinedUpperOscillationBadWindowEvent_le_dyadicRpow
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {η : ℝ} (hη : 1 < η) (r : ℕ) :
    ∃ p : ℝ, 1 < p ∧ ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ J : ℕ, J ∈ Finset.Icc 1 (2 ^ r + 3) →
          ∀ i : ℕ,
            μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J) ≤
              K * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
  rcases exists_partitionExponentParameters_gt_one hη with
    ⟨ε, hε0, hεlt, hEndpoint_gt, M, hM, hLocal_gt⟩
  rcases
    eventually_measureReal_refinedUpperOscillationBadWindowEvent_le_partitionPowerSum
      (B := B) hB hη hε0 hεlt M hM r with
    ⟨K, hK, hTail⟩
  let endpointExponent : ℝ := (((1 - 2 * ε) * η) ^ (2 : ℕ))
  let localExponent : ℝ := (M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))
  let p0 : ℝ := min endpointExponent localExponent
  let p : ℝ := (1 + p0) / 2
  have hp0_gt : 1 < p0 := by
    dsimp [p0, endpointExponent, localExponent]
    exact lt_min hEndpoint_gt hLocal_gt
  have hp : 1 < p := by
    dsimp [p]
    linarith
  have hp_nonneg : 0 ≤ p := by
    linarith
  have hp_le_endpoint : p ≤ endpointExponent := by
    dsimp [p, p0, endpointExponent]
    have hmid : (1 + min ((((1 - 2 * ε) * η) ^ (2 : ℕ))) ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) / 2
        ≤ min ((((1 - 2 * ε) * η) ^ (2 : ℕ))) ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))) := by
      linarith
    exact le_trans hmid (min_le_left _ _)
  have hp_le_local : p ≤ localExponent := by
    dsimp [p, p0, localExponent]
    have hmid : (1 + min ((((1 - 2 * ε) * η) ^ (2 : ℕ))) ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ)))) / 2
        ≤ min ((((1 - 2 * ε) * η) ^ (2 : ℕ))) ((M : ℝ) * ((ε * η / 2) ^ (2 : ℕ))) := by
      linarith
    exact le_trans hmid (min_le_right _ _)
  refine ⟨p, hp, 2 * K, by positivity, ?_⟩
  filter_upwards [hTail] with n hn J hJ i
  let x : ℝ := (((2 : ℝ)⁻¹) ^ n)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    exact pow_le_one₀ (by positivity) (by norm_num)
  have hEndpointPow :
      x ^ endpointExponent ≤ x ^ p := by
    exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp_nonneg hp_le_endpoint
  have hLocalPow :
      x ^ localExponent ≤ x ^ p := by
    exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 hp_nonneg hp_le_local
  calc
    μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J)
        ≤ K * (x ^ endpointExponent) + K * (x ^ localExponent) := by
            simpa [x, endpointExponent, localExponent] using hn J hJ i
    _ ≤ K * (x ^ p) + K * (x ^ p) := by
          gcongr
    _ = (2 * K) * (x ^ p) := by ring
    _ = (2 * K) * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by rfl

/-- Helper for Remark 22.4: the row multiplicity `2^(n + r) + 1` against a generic dyadic power
profile is dominated by a geometric factor once the exponent is greater than `1`. -/
lemma refinedUpperRow_cardinality_mul_dyadicRpow_le_geometric
    {p : ℝ} (r n : ℕ) :
    ((2 ^ (n + r) + 1 : ℕ) : ℝ) * ((((2 : ℝ)⁻¹) ^ n) ^ p) ≤
      (2 : ℝ) ^ (r + 1 : ℕ) * (2 * ((2 : ℝ)⁻¹) ^ p) ^ n := by
  have hcount :
      ((2 ^ (n + r) + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r + 1 : ℕ) * (2 : ℝ) ^ n := by
    have hNat :
        2 ^ (n + r) + 1 ≤ 2 ^ (n + r + 1) := by
      have hpow_pos : 1 ≤ 2 ^ (n + r) := by
        exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < 2) _)
      omega
    exact_mod_cast
      (hNat.trans_eq (by
        simp [pow_succ', pow_add, Nat.mul_comm, Nat.mul_assoc]))
  have hSwap :
      ((((2 : ℝ)⁻¹) ^ n) ^ p) =
        ((((2 : ℝ)⁻¹) ^ p) ^ n) := by
    -- Proof comment: swap the natural power in `n` with the real exponent `p` once, so the
    -- geometric ratio appears as a literal `n`th power.
    calc
      ((((2 : ℝ)⁻¹) ^ n) ^ p)
          = ((2 : ℝ)⁻¹) ^ ((n : ℝ) * p) := by
              rw [← Real.rpow_natCast ((2 : ℝ)⁻¹) n, ← Real.rpow_mul (by positivity)]
      _ = ((2 : ℝ)⁻¹) ^ (p * n) := by ring
      _ = ((((2 : ℝ)⁻¹) ^ p) ^ n) := by
            rw [← Real.rpow_natCast (((2 : ℝ)⁻¹) ^ p) n,
              ← Real.rpow_mul (by positivity)]
  calc
    ((2 ^ (n + r) + 1 : ℕ) : ℝ) * ((((2 : ℝ)⁻¹) ^ n) ^ p)
        ≤ ((2 : ℝ) ^ (r + 1 : ℕ) * (2 : ℝ) ^ n) *
            ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
              exact mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (2 : ℝ) ^ (r + 1 : ℕ) *
          ((2 : ℝ) ^ n * ((((2 : ℝ)⁻¹) ^ n) ^ p)) := by ring
    _ = (2 : ℝ) ^ (r + 1 : ℕ) *
          ((2 : ℝ) ^ n * ((((2 : ℝ)⁻¹) ^ p) ^ n)) := by rw [hSwap]
    _ = (2 : ℝ) ^ (r + 1 : ℕ) * (2 * ((2 : ℝ)⁻¹) ^ p) ^ n := by
          have hmul :
              (2 : ℝ) ^ n * ((((2 : ℝ)⁻¹) ^ p) ^ n) =
                (2 * ((2 : ℝ)⁻¹) ^ p) ^ n := by
            simpa using (mul_pow (2 : ℝ) (((2 : ℝ)⁻¹) ^ p) n).symm
          simpa [mul_assoc] using congrArg (fun x : ℝ => (2 : ℝ) ^ (r + 1 : ℕ) * x) hmul

lemma summable_refinedUpperOscillationBadRow_measureReal
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {η : ℝ} (hη : 1 < η) (r : ℕ) :
    Summable (fun n : ℕ => μ.real (refinedUpperOscillationBadRow B η r n)) := by
  -- Route correction: the row sum only needs a generic geometric majorant. The exact exponent
  -- from the discarded same-threshold route is no longer part of the API.
  rcases
    eventually_measureReal_refinedUpperOscillationBadWindowEvent_le_dyadicRpow
      (B := B) hB hη r with
    ⟨p, hp, K, hK0, hWindowTail⟩
  let q : ℝ := 2 * ((2 : ℝ)⁻¹) ^ p
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt_one : q < 1 := by
    have hq_eq : q = ((2 : ℝ)⁻¹) ^ (p - 1) := by
      dsimp [q]
      calc
        2 * ((2 : ℝ)⁻¹) ^ p
            = ((2 : ℝ)⁻¹) ^ (-1 : ℝ) * ((2 : ℝ)⁻¹) ^ p := by norm_num
        _ = ((2 : ℝ)⁻¹) ^ ((-1 : ℝ) + p) := by
              rw [← Real.rpow_add (by positivity : 0 < ((2 : ℝ)⁻¹))]
        _ = ((2 : ℝ)⁻¹) ^ (p - 1) := by congr 1; ring
    rw [hq_eq]
    refine Real.rpow_lt_one (by positivity) (by norm_num) ?_
    linarith
  let A : ℝ := (((2 ^ r + 3 : ℕ) : ℝ) * K) * (2 : ℝ) ^ (r + 1 : ℕ)
  have hGeom : Summable (fun n : ℕ => A * q ^ n) := by
    exact (summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left A
  have hRowTail :
      ∀ᶠ n : ℕ in atTop,
        μ.real (refinedUpperOscillationBadRow B η r n) ≤ A * q ^ n := by
    filter_upwards [hWindowTail] with n hn
    calc
      μ.real (refinedUpperOscillationBadRow B η r n)
          ≤ ∑ J ∈ Finset.Icc 1 (2 ^ r + 3),
              ∑ i ∈ Finset.range (2 ^ (n + r) + 1),
                μ.real (refinedUpperOscillationBadWindowEvent B η (n + r) i J) := by
                  exact measureReal_refinedUpperOscillationBadRow_le_windowSum
                    (μ := μ) (B := B) (α := η) r n
      _ ≤ ∑ J ∈ Finset.Icc 1 (2 ^ r + 3),
            ∑ i ∈ Finset.range (2 ^ (n + r) + 1),
              K * ((((2 : ℝ)⁻¹) ^ n) ^ p) := by
                refine Finset.sum_le_sum ?_
                intro J hJ
                refine Finset.sum_le_sum ?_
                intro i hi
                exact hn J hJ i
      _ = (((2 ^ r + 3 : ℕ) : ℝ) * K) *
            (((2 ^ (n + r) + 1 : ℕ) : ℝ) * ((((2 : ℝ)⁻¹) ^ n) ^ p)) := by
              simp [mul_assoc, mul_left_comm, mul_comm]
      _ ≤ (((2 ^ r + 3 : ℕ) : ℝ) * K) * ((2 : ℝ) ^ (r + 1 : ℕ) * q ^ n) := by
            refine mul_le_mul_of_nonneg_left ?_ ?_
            · simpa [q] using refinedUpperRow_cardinality_mul_dyadicRpow_le_geometric r n
            · positivity
      _ = A * q ^ n := by
            dsimp [A]
            ring
  rcases Filter.eventually_atTop.1 hRowTail with ⟨N, hN⟩
  have hGeomTail : Summable (fun n : ℕ => A * q ^ (n + N)) := by
    exact (_root_.summable_nat_add_iff N).2 hGeom
  have hTail :
      Summable (fun n : ℕ => μ.real (refinedUpperOscillationBadRow B η r (n + N))) := by
    refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ hGeomTail
    intro n
    exact hN (n + N) (by omega)
  exact (_root_.summable_nat_add_iff N).1 hTail

/-- Helper for Remark 22.4: the upper probabilistic input is the almost-sure upper envelope
family for the compact-interval oscillation. The remaining work is to combine summable refined
anchored-window bad rows with the deterministic refined-dyadic transport proved earlier. -/
lemma ae_eventually_compactIntervalOscillation_le_mul_levyModulus
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B)
    {α : ℝ} (hα : 1 < α) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
        ((compactIntervalOscillation 1 (ContinuousMap.mk (processPath B w) hcont) δ :
            NNReal) : ℝ) ≤
          α * levyModulusOfContinuity δ := by
  letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
  let η : ℝ := Real.sqrt α
  have hη_pos : 0 < η := by
    -- Proof comment: the eventual upper-envelope coefficient is routed through `η = √α`, so the
    -- Brownian tail exponent is naturally expressed in terms of `η² = α`.
    positivity
  have hη_one : 1 < η := by
    have hα_nonneg : 0 ≤ α := by
      linarith
    have hη_sq : η ^ (2 : ℕ) = α := by
      dsimp [η]
      simpa [pow_two] using (Real.sq_sqrt hα_nonneg)
    by_contra hη_one
    have hη_le : η ≤ 1 := le_of_not_gt hη_one
    have hα_le : α ≤ 1 := by
      calc
        α = η ^ (2 : ℕ) := hη_sq.symm
        _ ≤ 1 ^ (2 : ℕ) := by gcongr
        _ = 1 := by norm_num
    linarith
  have hη0 : 0 ≤ η := le_of_lt hη_pos
  have hη_sq : η ^ (2 : ℕ) = α := by
    have hα_nonneg : 0 ≤ α := by linarith
    dsimp [η]
    simpa [pow_two] using (Real.sq_sqrt hα_nonneg)
  rcases exists_refinedDyadicScaleFactor_addFour_lt_sq hη_one with ⟨r, hr⟩
  let factor : NNReal := (((2 ^ r + 4 : ℕ) : NNReal) / (2 : NNReal) ^ r)
  have hfactor_sq : (factor : ℝ) ≤ η ^ (2 : ℕ) := le_of_lt hr
  have hsmall :
      {δ : NNReal | factor * δ < 1} ∈ 𝓝[>] (0 : NNReal) := by
    have hcont : Continuous fun δ : NNReal ↦ factor * δ := continuous_const.mul continuous_id
    exact mem_nhdsWithin_of_mem_nhds <|
      hcont.continuousAt.preimage_mem_nhds <|
        Iio_mem_nhds (by
          have hzero : factor * (0 : NNReal) < 1 := by simp [factor]
          simpa using hzero)
  have hAvoid :
      ∀ᵐ w ∂μ, ∀ᶠ n : ℕ in atTop, w ∉ refinedUpperOscillationBadRow B η r n :=
    ae_eventually_notMem_of_summable_measureReal (μ := μ)
      (s := fun n ↦ refinedUpperOscillationBadRow B η r n)
      (summable_refinedUpperOscillationBadRow_measureReal (B := B) hB hη_one r)
  filter_upwards [hAvoid] with w hw
  intro hcont
  rcases Filter.eventually_atTop.1 hw with ⟨N₀, hN₀⟩
  have hcover := existsRefinedSuccessorWindowLengthCoveringScale r (max N₀ 2)
  filter_upwards [self_mem_nhdsWithin, hsmall, hcover] with δ hδ0 hδsmall hcoverδ
  rcases hcoverδ with ⟨n, J, hn₀, hJ1, hJr, hδcover, hsuccCover⟩
  let ωpath : PathSpace := ContinuousMap.mk (processPath B w) hcont
  let succLength : NNReal := (((J + 1 : ℕ) : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r))
  have hn_two : 2 ≤ n := le_trans (by omega) hn₀
  have hgood : w ∉ refinedUpperOscillationBadRow B η r n :=
    hN₀ n (le_trans (Nat.le_max_left _ _) hn₀)
  have hosc :
      ((compactIntervalOscillation 1 ωpath δ : NNReal) : ℝ) ≤
        η * levyModulusOfContinuity succLength := by
    simpa [ωpath, succLength, processPath] using
      compactIntervalOscillation_le_of_goodRefinedRowAtSuccessorLength
        (B := B) (ω := w) (η := η) r n J hn_two hη0 hJ1 hJr hgood hcont hδcover
  let c : NNReal := succLength / δ
  have hδ_le_succ : δ ≤ succLength := by
    calc
      δ ≤ (((J : NNReal) * ((2 : NNReal)⁻¹) ^ (n + r) : NNReal)) := hδcover
      _ ≤ succLength := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ J) (by positivity)
  have hc1 : 1 ≤ c := by
    exact (le_div_iff₀ hδ0).2 (by simpa using hδ_le_succ)
  have hc_le_factor : c ≤ factor := by
    exact (div_le_iff₀ hδ0).2 (by simpa [succLength, factor] using hsuccCover)
  have hc_sq : (c : ℝ) ≤ η ^ (2 : ℕ) := by
    exact le_trans (by exact_mod_cast hc_le_factor) hfactor_sq
  have hsucc_small : c * δ < 1 := by
    have hsucc_lt : succLength < 1 := lt_of_le_of_lt hsuccCover hδsmall
    simpa [c, succLength, div_mul_cancel₀ _ (show δ ≠ 0 by exact ne_of_gt hδ0)] using hsucc_lt
  have hlevy :
      levyModulusOfContinuity succLength ≤ η * levyModulusOfContinuity δ := by
    simpa [c, succLength, div_mul_cancel₀ _ (show δ ≠ 0 by exact ne_of_gt hδ0)] using
      levyModulus_mul_le_of_factor_sqBound hη_one hc1 hc_sq hδ0 hsucc_small
  calc
    ((compactIntervalOscillation 1 ωpath δ : NNReal) : ℝ)
        ≤ η * levyModulusOfContinuity succLength := hosc
    _ ≤ η * (η * levyModulusOfContinuity δ) := by gcongr
    _ = α * levyModulusOfContinuity δ := by
          rw [← hη_sq]
          ring

-- Proof sketch: prove Lévy's modulus-of-continuity law by controlling the maximal oscillation on
-- dyadic scales, using Gaussian increment estimates with Borel--Cantelli, and then compare the
-- discrete oscillation bounds with the canonical compact-interval path oscillation on `[0,1]`.
/-- Remark 22.4: for Brownian motion `B`, Lévy's modulus of continuity satisfies
`limsup_{δ ↓ 0} V¹(ω, δ) / h(δ) = 1` almost surely on continuous sample paths `ω(t) = B_t`, where
`V¹` is the compact-interval path oscillation on `[0,1]`. -/
theorem ae_limsup_compactIntervalPathOscillation_div_levyModulus_eq_one
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
      let ω : PathSpace := ContinuousMap.mk (processPath B w) hcont
      limsup
        (fun δ : NNReal ↦
          compactIntervalOscillation 1 ω δ / levyModulusOfContinuity δ)
        (𝓝[>] (0 : NNReal)) = 1 := by
  -- Route correction: the fixed-time LIL from Corollary 22.3 is already enough for theorem 2, but
  -- theorem 1 needs a separate owner theorem for Lévy's uniform modulus law on Brownian paths.
  -- Route correction: the earlier upper-bound plan via `dyadicWindowMax` is too weak because that
  -- endpoint-only object does not dominate arbitrary oscillation inside one dyadic cell. The
  -- current verified deterministic upper transfer therefore goes first through the monotonicity
  -- lemma `compactIntervalOscillation_le_refinedDyadicScale`; the remaining gap is purely the
  -- probabilistic refined-scale owner theorem.
  have hOwner :
      ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
        hasUnitIntervalLevyModulusLimsup (ContinuousMap.mk (processPath B w) hcont) := by
    letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
    have hUpper :
        ∀ {α : ℝ}, 1 < α →
          ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
            ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal),
              ((compactIntervalOscillation 1 (ContinuousMap.mk (processPath B w) hcont) δ :
                  NNReal) : ℝ) ≤
                α * levyModulusOfContinuity δ := by
      intro α hα
      -- Proof comment: the main theorem now depends on the named upper probabilistic owner lemma
      -- rather than keeping that whole Borel--Cantelli argument inline.
      exact ae_eventually_compactIntervalOscillation_le_mul_levyModulus (B := B) hB hα
    have hLower :
        ∀ {β : ℝ}, 0 < β → β < 1 →
          ∀ᵐ w ∂μ, ∀ hcont : Continuous (processPath B w),
            ∀ᶠ n : ℕ in atTop,
              β * levyModulusOfContinuity (((2 : NNReal)⁻¹) ^ n) ≤
                (dyadicWindowMax (ContinuousMap.mk (processPath B w) hcont) n 1 : ℝ) := by
      intro β hβ0 hβ1
      -- Proof comment: the lower family is reduced to the standalone summability theorem and the
      -- already verified Borel--Cantelli-to-dyadic-window transport.
      exact
        ae_eventually_mul_levyModulus_le_dyadicWindowMax_of_summable_dyadicRowFailure
          (B := B)
          (summable_dyadicRowFailure_measureReal (μ := μ) (B := B) hB hβ0 hβ1)
    -- Proof comment: once the upper and lower owner lemmas are named, the bundled-path theorem is
    -- exactly the sandwich assembly from the previous helper.
    exact ae_hasUnitIntervalLevyModulusLimsup_of_envelopeFamilies (B := B) hUpper hLower
  -- Proof comment: after isolating the pathwise predicate, the displayed theorem is just the
  -- owner theorem rewritten through the bundled-path interface.
  exact ae_hasUnitIntervalLevyModulusLimsup_of_owner (B := B) hOwner

-- Proof sketch: if a sample path were locally `1 / 2`-Hölder on `[0,1]`, then compactness of
-- `[0,1]` would yield a uniform local `1 / 2`-Hölder bound on sufficiently short increments. This
-- forces the oscillation ratio against Lévy's modulus to converge to `0`, contradicting the
-- previous almost-sure limsup equality.
/-- Almost surely, a Brownian sample path on `[0,1]` is not locally Hölder continuous with
exponent `1 / 2`. -/
theorem ae_not_locallyHolderContinuous_oneHalf_on_unitInterval
    {μ : Measure Ω} {B : NNReal → Ω → ℝ} (hB : IsBrownianMotion μ B) :
    ∀ᵐ w ∂μ,
      ¬ LocallyHolderWith halfHolderExponent
        (fun t : Set.Icc (0 : NNReal) 1 ↦ B t w) := by
  have hLILAtZero :
      ∀ᵐ w ∂μ,
        limsup
          (fun t : NNReal ↦
            (B t w - B 0 w) /
              Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))))
          (𝓝[>] (0 : NNReal)) = 1 := by
    -- Proof comment: Corollary 22.3 already gives the local law of the iterated logarithm at the
    -- fixed base point `s = 0`.
    simpa using ae_limsup_increment_div_sqrt_two_mul_t_log_log_inv_eq_one (B := B) hB (0 : NNReal)
  filter_upwards [hLILAtZero] with w hLIL
  intro hLoc
  let x0 : Set.Icc (0 : NNReal) 1 := ⟨0, by simp⟩
  rcases hLoc.exists_holderOnWith_ball x0 with ⟨ε, hε, C, hC⟩
  let δ : NNReal := min ⟨ε / 2, by positivity⟩ 1
  have hδpos : 0 < δ := by
    -- Proof comment: shrink the local Hölder ball so that every positive `t < δ` still lies in
    -- the subtype interval `[0, 1]`.
    change 0 < min (ε / 2) 1
    exact lt_min (by linarith) zero_lt_one
  have hHalfExponent :
      ((halfHolderExponent : ℝ≥0) : ℝ) = (1 / 2 : ℝ) := by
    change (((1 : ℝ≥0) / 2 : ℝ≥0) : ℝ) = (1 / 2 : ℝ)
    norm_num
  let f : NNReal → ℝ := fun t ↦
    (B t w - B 0 w) / Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹)))
  let m : NNReal → ℝ := fun t ↦
    (C : ℝ) * (t : ℝ) ^ (1 / 2 : ℝ) /
      Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹)))
  have hLogLogPos :
      ∀ᶠ t : NNReal in 𝓝[>] (0 : NNReal), 0 < Real.log (Real.log ((t : ℝ)⁻¹)) := by
    filter_upwards [tendsto_logLogInv_nhdsGT_zero_atTop.eventually_gt_atTop (0 : ℝ)] with t ht
    exact ht
  have hNormLeMajorant :
      ∀ᶠ t : NNReal in 𝓝[>] (0 : NNReal), ‖f t‖ ≤ m t := by
    have hSmall : {t : NNReal | t < δ} ∈ 𝓝[>] (0 : NNReal) := by
      exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδpos)
    filter_upwards [self_mem_nhdsWithin, hSmall, hLogLogPos] with t ht0 htδ hloglog
    have htHalf : t < ⟨ε / 2, by positivity⟩ := lt_of_lt_of_le htδ (min_le_left _ _)
    have htε : (t : ℝ) < ε := by
      have htHalf' : (t : ℝ) < ε / 2 := htHalf
      linarith
    have htOne : t ≤ (1 : NNReal) := le_of_lt <| lt_of_lt_of_le htδ (min_le_right _ _)
    let xt : Set.Icc (0 : NNReal) 1 := ⟨t, ⟨le_of_lt ht0, htOne⟩⟩
    have hx0 : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
    have hxt : xt ∈ Metric.ball x0 ε := by
      -- Proof comment: every `t < δ ≤ ε / 2` lies inside the same local Hölder ball centered at
      -- `0`.
      rw [Metric.mem_ball]
      rw [dist_comm]
      change dist (0 : NNReal) (xt : NNReal) < ε
      simpa [xt, NNReal.dist_eq] using htε
    have hHolderENN :
        ENNReal.ofReal (dist (B 0 w) (B t w)) ≤
          ENNReal.ofReal ((C : ℝ) * dist x0 xt ^ ((halfHolderExponent : ℝ≥0) : ℝ)) := by
      -- Proof comment: evaluate the local Hölder estimate on the pair `(0, t)` in the subtype.
      simpa [x0, xt, edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using
        hC x0 hx0 xt hxt
    have hHolder :
        dist (B 0 w) (B t w) ≤
          (C : ℝ) * dist x0 xt ^ ((halfHolderExponent : ℝ≥0) : ℝ) := by
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hHolderENN
    have hDist : dist x0 xt = (t : ℝ) := by
      change dist (0 : NNReal) (xt : NNReal) = (t : ℝ)
      simp [xt, NNReal.dist_eq]
    have hHolder' : dist (B 0 w) (B t w) ≤ (C : ℝ) * (t : ℝ) ^ (1 / 2 : ℝ) := by
      simpa [hDist, hHalfExponent] using hHolder
    have hDenPos :
        0 < Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))) := by
      have htReal : 0 < (t : ℝ) := by
        exact_mod_cast ht0
      apply Real.sqrt_pos.2
      positivity
    have hAbs :
        |f t| ≤ m t := by
      -- Proof comment: divide the absolute increment estimate by the positive LIL denominator.
      calc
        |f t|
            = |B t w - B 0 w| /
                Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))) := by
                  change
                    |(B t w - B 0 w) /
                        Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹)))| =
                      |B t w - B 0 w| /
                        Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹)))
                  rw [abs_div, abs_of_pos hDenPos]
        _ = dist (B 0 w) (B t w) /
              Real.sqrt (2 * (t : ℝ) * Real.log (Real.log ((t : ℝ)⁻¹))) := by
                rw [Real.dist_eq, abs_sub_comm]
        _ ≤ m t := by
          simpa [m] using div_le_div_of_nonneg_right hHolder' hDenPos.le
    simpa [Real.norm_eq_abs] using hAbs
  have hTendstoZero : Tendsto f (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) := by
    -- Route correction: the contradiction only needs the one-point local increment law from
    -- Corollary 22.3, not the unresolved uniform oscillation statement above.
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) hNormLeMajorant ?_
    simpa [m] using tendsto_halfHolderNormalizer_zero C
  have hLimsupZero : limsup f (𝓝[>] (0 : NNReal)) = 0 := hTendstoZero.limsup_eq
  have hLILEq : limsup f (𝓝[>] (0 : NNReal)) = 1 := by
    simpa [f] using hLIL
  have : (1 : ℝ) = 0 := by
    rw [← hLILEq, hLimsupZero]
  linarith

end IsBrownianMotion

end ProbabilityTheory
