/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Definition_23_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Lemma_23_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10Core
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_1_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_2_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Exercise_23_2_5

open Filter MeasureTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

variable [MeasurableSpace Ω]

/-- The `n + 1`st canonical normalized partial-sum law is the pushforward of `P` by the
`0`-based empirical mean `ω ↦ (∑ i ∈ range (n + 1), X i ω) / (n + 1)`. -/
theorem normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    normalizedPartialSumLaw X P ⟨n + 1, Nat.succ_pos _⟩ =
      Measure.map
        (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  rw [normalizedPartialSumLaw]
  congr 1
  ext ω
  simp [partialRealSum]

/-- Helper for Theorem 23.11: the `0`-based empirical mean is a.e.-measurable once each
coordinate is. -/
private theorem empiricalMean_aemeasurable
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    AEMeasurable
      (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  have hsum : AEMeasurable (∑ i ∈ Finset.range (n + 1), X i) P := by
    exact Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ ↦ hXae i
  simpa [div_eq_mul_inv, mul_comm] using hsum.mul_const ((n + 1 : ℝ)⁻¹)

/-- The owner `ℕ`-indexed empirical-mean law formed from the `0`-based averages of the first
`n + 1` coordinates. -/
noncomputable def empiricalMeanLaw
    (X : ℕ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXae : ∀ n, AEMeasurable (X n) P) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (empiricalMean_aemeasurable P X hXae n)

/-- The owner empirical-mean law agrees with the chapter's positive-indexed normalized
partial-sum law after coercion to measures. -/
theorem empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    (empiricalMeanLaw X P hXae n : Measure ℝ) =
      normalizedPartialSumLaw X P (Nat.succPNat n) := by
  simpa [empiricalMeanLaw] using
    (normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage P X n).symm

/-- Helper for Theorem 23.11: every measurable event under the `n + 1`st normalized partial-sum
law is the corresponding preimage event for the `0`-based empirical mean. -/
private theorem normalizedPartialSumLaw_mapApply_zeroBasedAverage
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P)
    {s : Set ℝ} (hs : MeasurableSet s) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) s =
      P {ω |
        Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ) ∈ s} := by
  -- Proof comment: unfold the normalized law into the empirical-mean pushforward and then read
  -- off the event by `Measure.map_apply`.
  have hMap :
      normalizedPartialSumLaw X P (Nat.succPNat n) =
        Measure.map
          (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
    simpa using normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage (P := P) (X := X) n
  rw [hMap]
  rw [Measure.map_apply_of_aemeasurable (empiricalMean_aemeasurable P X hXae n) hs]
  rfl

/-- Helper for Theorem 23.11: the positive-indexed normalized partial-sum law assigns the closed
half-line `Set.Ici x` exactly the source-facing upper-tail event for the `0`-based empirical
average. -/
private theorem normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ici x) =
      P {ω | x * (n + 1 : ℝ) ≤ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)} := by
  -- Proof comment: specialize the generic pushforward bridge to `Set.Ici x`, then clear the
  -- positive denominator `n + 1`.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage
    (P := P) (X := X) hXae measurableSet_Ici]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by
    positivity
  simp [le_div_iff₀ hn]

/-- Helper for Theorem 23.11: the positive-indexed normalized partial-sum law assigns the closed
half-line `Set.Iic x` exactly the source-facing lower-tail event for the `0`-based empirical
average. -/
private theorem normalizedPartialSumLaw_closedHalfline_eq_lowerTailEvent
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Iic x) =
      P {ω | Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) ≤ x * (n + 1 : ℝ)} := by
  -- Proof comment: specialize the pushforward event formula to `Set.Iic x`, then clear the
  -- positive denominator `n + 1`.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage
    (P := P) (X := X) hXae measurableSet_Iic]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by
    positivity
  simp [div_le_iff₀ hn]

/-- Helper for Theorem 23.11: the positive-indexed normalized partial-sum law assigns the open
half-line `Set.Ioi x` exactly the strict upper-tail event for the `0`-based empirical average. -/
private theorem normalizedPartialSumLaw_openHalfline_eq_strictUpperTailEvent
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (x : ℝ) (n : ℕ) :
    (normalizedPartialSumLaw X P (Nat.succPNat n)) (Set.Ioi x) =
      P {ω | x * (n + 1 : ℝ) < Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)} := by
  -- Proof comment: the open-halfline case is the same transport, with a strict inequality after
  -- clearing the positive denominator.
  rw [normalizedPartialSumLaw_mapApply_zeroBasedAverage
    (P := P) (X := X) hXae measurableSet_Ioi]
  congr 1
  ext ω
  have hn : (0 : ℝ) < n + 1 := by
    positivity
  simp [lt_div_iff₀ hn]

/-- Helper for Theorem 23.11: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`limsup` along `atTop`. -/
private theorem limsup_succPNat_eq {α : Type*} [ConditionallyCompleteLattice α] [OrderBot α]
    (f : ℕ+ → α) :
    Filter.limsup (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.limsup f atTop := by
  -- Proof comment: `Nat.succPNat` is an order isomorphism from `ℕ` onto `ℕ+`, so reindexing only
  -- changes the presentation of the `atTop` filter.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.limsup_comp]
  simpa using congrArg (Filter.limsup f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Theorem 23.11: reindexing a `ℕ+`-sequence along `Nat.succPNat` does not change its
`liminf` along `atTop`. -/
private theorem liminf_succPNat_eq {α : Type*} [ConditionallyCompleteLattice α] [OrderTop α]
    (f : ℕ+ → α) :
    Filter.liminf (fun n : ℕ ↦ f (Nat.succPNat n)) atTop = Filter.liminf f atTop := by
  -- Proof comment: the same order-isomorphism argument applies to `liminf`.
  rw [show (fun n : ℕ ↦ f (Nat.succPNat n)) = f ∘ Nat.succPNat by rfl, Filter.liminf_comp]
  simpa using congrArg (Filter.liminf f) (OrderIso.pnatIsoNat.symm.map_atTop)

/-- Helper for Theorem 23.11: an i.i.d. family is coordinatewise a.e.-measurable. -/
private theorem iidAEMeasurable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    ∀ n, AEMeasurable (X n) P :=
  fun n ↦ (hX_iid.identDistrib n 0).aemeasurable_fst

/-- Under finite exponential moments for all tilts, the owner Legendre-Fenchel rate agrees with
the chapter's cumulant-generating-function Legendre transform. -/
theorem legendreFenchelRateFunction_extendedLogMomentGeneratingFunction_eq_legendreCgfRateFunction
    (X : Ω → ℝ) (P : Measure Ω)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    legendreFenchelRateFunction (Λ(X; P)) =
      legendreCgfRateFunction X P := by
  funext x
  have hmem : ∀ t : ℝ, t ∈ integrableExpSet X P := fun t ↦ hmgf t
  simp [legendreFenchelRateFunction, legendreCgfRateFunction, extendedLogMomentGeneratingFunction,
    hmem, EReal.coe_sub]

/-- Helper for Theorem 23.11: the Cramér rate is always nonnegative because the zero tilt
contributes the value `0`. -/
private theorem legendreCgfRateFunction_nonneg
    (X : Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] (x : ℝ) :
    (0 : EReal) ≤ legendreCgfRateFunction X P x := by
  -- Proof comment: evaluate the Legendre supremum at tilt `t = 0`.
  rw [legendreCgfRateFunction]
  refine le_sSup ?_
  refine ⟨0, ?_⟩
  simp [cgf_zero]

/-- Helper for Theorem 23.11: under finite exponential moments, the owner Legendre-Fenchel rate
agrees, as an `EReal`-valued function, with `legendreCgfRateFunction`. -/
private theorem ownerLegendreFenchelRate_ereal_eq_legendreCgfRateFunction
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    (fun x ↦
        (((legendreFenchelRateFunction (Λ(X; P)) x).toENNReal : ENNReal) : EReal)) =
      legendreCgfRateFunction X P := by
  -- Proof comment: first identify the two rate functions in `EReal`, then remove the owner
  -- `toENNReal` coercion using nonnegativity of the Cramér rate.
  funext x
  have hRatePoint :
      legendreFenchelRateFunction (Λ(X; P)) x = legendreCgfRateFunction X P x := by
    simpa using
      congrArg (fun f : ℝ → EReal ↦ f x)
        (legendreFenchelRateFunction_extendedLogMomentGeneratingFunction_eq_legendreCgfRateFunction
          (X := X) (P := P) hmgf)
  rw [hRatePoint]
  exact EReal.coe_toENNReal (legendreCgfRateFunction_nonneg X P x)

/-- Helper for Theorem 23.11: the canonical owner rate is lower semicontinuous. -/
private theorem ownerRate_lowerSemicontinuous
    (P : Measure Ω) (X : Ω → ℝ) :
    LowerSemicontinuous (fun x : ℝ ↦ (legendreFenchelRateFunction (Λ(X; P)) x).toENNReal) := by
  have hCore :
      LowerSemicontinuous fun x : ℝ ↦
        ⨆ t : ℝ, (((t * x : ℝ) : EReal) - Λ(X; P) t) := by
    refine lowerSemicontinuous_iSup fun t ↦ ?_
    by_cases ht : t ∈ integrableExpSet X P
    · have hContReal : Continuous fun x : ℝ ↦ t * x - cgf X P t := by
        -- Proof comment: for fixed `t`, the Legendre summand is an affine continuous function of
        -- `x`.
        exact (continuous_const.mul continuous_id).sub continuous_const
      have hLsc :
          LowerSemicontinuous fun x : ℝ ↦ (((t * x - cgf X P t : ℝ) : EReal)) := by
        exact (continuous_coe_real_ereal.comp hContReal).lowerSemicontinuous
      -- Proof comment: on the effective domain, `Λ` is just the finite-valued `cgf`.
      simpa [extendedLogMomentGeneratingFunction, ht, EReal.coe_sub] using hLsc
    · -- Proof comment: outside the effective domain the summand is constantly `⊥`.
      simpa [extendedLogMomentGeneratingFunction, ht] using
        (lowerSemicontinuous_const : LowerSemicontinuous fun _ : ℝ ↦ (⊥ : EReal))
  -- Proof comment: compose the extended-real supremum with the monotone continuous map
  -- `EReal.toENNReal`.
  simpa [legendreFenchelRateFunction, sSup_range] using
    Continuous.comp_lowerSemicontinuous EReal.continuous_toENNReal hCore
      (fun _ _ hxy ↦ EReal.toENNReal_le_toENNReal hxy)

/-- Helper for Theorem 23.11: every affine summand of the one-letter Legendre transform is bounded
by the resulting Legendre-Fenchel rate. -/
private theorem affineSummand_le_legendreFenchelRateFunction
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) {x t : ℝ} :
    ((((t * x : ℝ) : EReal) - Λ(X; P) t)) ≤ legendreFenchelRateFunction (Λ(X; P)) x := by
  -- Proof comment: the defining Legendre-Fenchel supremum already contains the affine summand at
  -- the chosen tilt `t`.
  rw [legendreFenchelRateFunction]
  exact le_sSup ⟨t, rfl⟩

/-- Helper for Theorem 23.11: at finite endpoint values, the one-letter Legendre-Fenchel rate is
convex along line segments. -/
private theorem legendreFenchelRateFunction_convexCombo_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    {x y r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx_top : legendreFenchelRateFunction (Λ(X; P)) x ≠ ⊤)
    (hy_top : legendreFenchelRateFunction (Λ(X; P)) y ≠ ⊤) :
    legendreFenchelRateFunction (Λ(X; P)) ((1 - r) * x + r * y) ≤
      ((((1 - r) * (legendreFenchelRateFunction (Λ(X; P)) x).toReal +
          r * (legendreFenchelRateFunction (Λ(X; P)) y).toReal : ℝ) : EReal)) := by
  rw [legendreFenchelRateFunction]
  refine sSup_le ?_
  rintro _ ⟨t, rfl⟩
  dsimp
  by_cases ht : t ∈ integrableExpSet X P
  · have hx_bound :
        ((((t * x : ℝ) : EReal) - Λ(X; P) t)) ≤ legendreFenchelRateFunction (Λ(X; P)) x := by
      exact affineSummand_le_legendreFenchelRateFunction (P := P) (X := X)
    have hy_bound :
        ((((t * y : ℝ) : EReal) - Λ(X; P) t)) ≤ legendreFenchelRateFunction (Λ(X; P)) y := by
      exact affineSummand_le_legendreFenchelRateFunction (P := P) (X := X)
    have hx_bound' :
        (((t * x - cgf X P t : ℝ)) : EReal) ≤ legendreFenchelRateFunction (Λ(X; P)) x := by
      -- Proof comment: on the effective domain, the extended log-moment generating function is
      -- the finite-valued cumulant-generating function.
      calc
        (((t * x - cgf X P t : ℝ)) : EReal) = ((((t * x : ℝ) : EReal) - Λ(X; P) t)) := by
          rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
            (X := X) (P := P) ht]
          simp [EReal.coe_sub]
        _ ≤ legendreFenchelRateFunction (Λ(X; P)) x := hx_bound
    have hy_bound' :
        (((t * y - cgf X P t : ℝ)) : EReal) ≤ legendreFenchelRateFunction (Λ(X; P)) y := by
      -- Proof comment: the same reduction applies at the right endpoint.
      calc
        (((t * y - cgf X P t : ℝ)) : EReal) = ((((t * y : ℝ) : EReal) - Λ(X; P) t)) := by
          rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
            (X := X) (P := P) ht]
          simp [EReal.coe_sub]
        _ ≤ legendreFenchelRateFunction (Λ(X; P)) y := hy_bound
    have hx_ne_bot : (((t * x - cgf X P t : ℝ)) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hy_ne_bot : (((t * y - cgf X P t : ℝ)) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
    have hx_real : t * x - cgf X P t ≤ (legendreFenchelRateFunction (Λ(X; P)) x).toReal := by
      exact EReal.toReal_le_toReal hx_bound' hx_ne_bot hx_top
    have hy_real : t * y - cgf X P t ≤ (legendreFenchelRateFunction (Λ(X; P)) y).toReal := by
      exact EReal.toReal_le_toReal hy_bound' hy_ne_bot hy_top
    have hreal :
        t * ((1 - r) * x + r * y) - cgf X P t ≤
          (1 - r) * (legendreFenchelRateFunction (Λ(X; P)) x).toReal +
            r * (legendreFenchelRateFunction (Λ(X; P)) y).toReal := by
      -- Proof comment: the affine summand is linear in the space variable, so the endpoint
      -- bounds combine with the convex weights `1 - r` and `r`.
      nlinarith
    calc
      ((((t * ((1 - r) * x + r * y) : ℝ) : EReal) - Λ(X; P) t))
          = (((t * ((1 - r) * x + r * y) - cgf X P t : ℝ)) : EReal) := by
              rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
                (X := X) (P := P) ht]
              simp [EReal.coe_sub]
      _ ≤
          ((((1 - r) * (legendreFenchelRateFunction (Λ(X; P)) x).toReal +
            r * (legendreFenchelRateFunction (Λ(X; P)) y).toReal : ℝ) : EReal)) := by
              exact_mod_cast hreal
  · -- Proof comment: outside the effective domain the affine summand is `⊥`, so the convexity
    -- estimate is automatic.
    rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      (X := X) (P := P) ht]
    simp

/-- Helper for Theorem 23.11: a closed set missing a point is contained in two closed rays that
leave a gap around that point. -/
private theorem closedSet_twoRayCover_of_notMem
    {C : Set ℝ} (hC : IsClosed C) {x : ℝ} (hx : x ∉ C) :
    ∃ a b, a < x ∧ x < b ∧ C ⊆ Set.Iic a ∪ Set.Ici b := by
  have hOpen : IsOpen Cᶜ := hC.isOpen_compl
  have hxMem : x ∈ Cᶜ := hx
  rcases Metric.isOpen_iff.mp hOpen x hxMem with ⟨δ, hδpos, hball⟩
  refine ⟨x - δ, x + δ, by linarith, by linarith, ?_⟩
  intro y hy
  by_cases hyLeft : y ≤ x - δ
  · exact Or.inl hyLeft
  by_cases hyRight : x + δ ≤ y
  · exact Or.inr hyRight
  -- Proof comment: otherwise `y` lies in the open interval `(x - δ, x + δ)`, hence in the ball
  -- around `x` that is disjoint from `C`.
  have hyGt : x - δ < y := lt_of_not_ge hyLeft
  have hyLt : y < x + δ := lt_of_not_ge hyRight
  have hyBall : y ∈ Metric.ball x δ := by
    show dist y x < δ
    simpa [Real.dist_eq, abs_lt] using And.intro (by linarith) (by linarith)
  have hyComp : y ∈ Cᶜ := hball hyBall
  exact False.elim (hyComp hy)

/-- Helper for Theorem 23.11: a closed convex subset of `ℝ` has one of the five standard interval
shapes. -/
private theorem closedConvex_real_shape
    {s : Set ℝ} (hsClosed : IsClosed s) (hsConvex : Convex ℝ s) :
    s = ∅ ∨ s = Set.univ ∨ (∃ a, s = Set.Iic a) ∨ (∃ b, s = Set.Ici b) ∨
      ∃ a b, a ≤ b ∧ s = Set.Icc a b := by
  by_cases hsEmpty : s = ∅
  · exact Or.inl hsEmpty
  · have hsNonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hsEmpty
    have hsOrd : s.OrdConnected := hsConvex.ordConnected
    by_cases hsBelow : BddBelow s
    · by_cases hsAbove : BddAbove s
      · -- Proof comment: if both bounds exist, the closed convex set is the closed interval
        -- between its infimum and supremum.
        refine Or.inr ?_
        refine Or.inr ?_
        refine Or.inr ?_
        refine Or.inr ⟨sInf s, sSup s, ?_, ?_⟩
        · exact (isLUB_csSup hsNonempty hsAbove).1 (hsClosed.csInf_mem hsNonempty hsBelow)
        · ext x
          constructor
          · intro hx
            exact ⟨(isGLB_csInf hsNonempty hsBelow).1 hx, (isLUB_csSup hsNonempty hsAbove).1 hx⟩
          · intro hx
            exact hsOrd.out
              (hsClosed.csInf_mem hsNonempty hsBelow)
              (hsClosed.csSup_mem hsNonempty hsAbove)
              hx
      · -- Proof comment: if the set has a lower bound but no upper bound, order-convexity forces
        -- it to contain every point above its infimum.
        refine Or.inr ?_
        refine Or.inr ?_
        refine Or.inr (Or.inl ?_)
        refine ⟨sInf s, ?_⟩
        ext x
        constructor
        · intro hx
          exact (isGLB_csInf hsNonempty hsBelow).1 hx
        · intro hx
          have hAbovePoint : ∃ y ∈ s, x < y := by
            by_contra hNo
            apply hsAbove
            refine ⟨x, ?_⟩
            intro y hy
            by_contra hyx
            exact hNo ⟨y, hy, lt_of_not_ge hyx⟩
          rcases hAbovePoint with ⟨y, hy, hxy⟩
          exact hsOrd.out (hsClosed.csInf_mem hsNonempty hsBelow) hy ⟨hx, hxy.le⟩
    · by_cases hsAbove : BddAbove s
      · -- Proof comment: the upper-bounded but not lower-bounded case is the reflected version of
        -- the previous half-line argument.
        refine Or.inr ?_
        refine Or.inr (Or.inl ?_)
        refine ⟨sSup s, ?_⟩
        ext x
        constructor
        · intro hx
          exact (isLUB_csSup hsNonempty hsAbove).1 hx
        · intro hx
          have hBelowPoint : ∃ y ∈ s, y < x := by
            by_contra hNo
            apply hsBelow
            refine ⟨x, ?_⟩
            intro y hy
            by_contra hxy
            exact hNo ⟨y, hy, lt_of_not_ge hxy⟩
          rcases hBelowPoint with ⟨y, hy, hyx⟩
          exact hsOrd.out hy (hsClosed.csSup_mem hsNonempty hsAbove) ⟨hyx.le, hx⟩
      · -- Proof comment: without either bound, the closed convex set contains points on both sides
        -- of every `x`, hence it is all of `ℝ`.
        refine Or.inr <| Or.inl ?_
        ext x
        constructor
        · intro hx
          simp
        · intro _
          have hBelowPoint : ∃ y ∈ s, y < x := by
            by_contra hNo
            apply hsBelow
            refine ⟨x, ?_⟩
            intro y hy
            by_contra hxy
            exact hNo ⟨y, hy, lt_of_not_ge hxy⟩
          have hAbovePoint : ∃ z ∈ s, x < z := by
            by_contra hNo
            apply hsAbove
            refine ⟨x, ?_⟩
            intro z hz
            by_contra hzx
            exact hNo ⟨z, hz, lt_of_not_ge hzx⟩
          rcases hBelowPoint with ⟨y, hy, hyx⟩
          rcases hAbovePoint with ⟨z, hz, hxz⟩
          exact hsOrd.out hy hz ⟨hyx.le, hxz.le⟩

/-- Helper for Theorem 23.11: if a closed set is disjoint from a closed left ray, then there is a
strictly larger right-ray cover of the set. -/
private theorem closedSet_rightRay_of_disjoint_leftRay
    {C : Set ℝ} (hC : IsClosed C) {a : ℝ} (hDisj : Disjoint C (Set.Iic a)) :
    ∃ b, a < b ∧ C ⊆ Set.Ici b := by
  have haNot : a ∉ C := by
    intro ha
    exact (Set.disjoint_left.1 hDisj) ha (by simpa using le_rfl)
  rcases closedSet_twoRayCover_of_notMem hC haNot with ⟨u, v, huv, hav, hCover⟩
  refine ⟨v, hav, ?_⟩
  intro x hx
  rcases hCover hx with hxLeft | hxRight
  · exfalso
    exact (Set.disjoint_left.1 hDisj) hx (le_trans hxLeft huv.le)
  · exact hxRight

/-- Helper for Theorem 23.11: if a closed set is disjoint from a closed right ray, then there is a
strictly smaller left-ray cover of the set. -/
private theorem closedSet_leftRay_of_disjoint_rightRay
    {C : Set ℝ} (hC : IsClosed C) {b : ℝ} (hDisj : Disjoint C (Set.Ici b)) :
    ∃ a, a < b ∧ C ⊆ Set.Iic a := by
  have hbNot : b ∉ C := by
    intro hb
    exact (Set.disjoint_left.1 hDisj) hb (by simpa using le_rfl)
  rcases closedSet_twoRayCover_of_notMem hC hbNot with ⟨u, v, hub, hvb, hCover⟩
  refine ⟨u, hub, ?_⟩
  intro x hx
  rcases hCover hx with hxLeft | hxRight
  · exact hxLeft
  · exfalso
    exact (Set.disjoint_left.1 hDisj) hx (le_trans hvb.le hxRight)

/-- Helper for Theorem 23.11: if a closed set is disjoint from a closed interval, then shrinking a
small neighborhood around each endpoint produces the expected two-ray cover. -/
private theorem closedSet_twoRayCover_of_disjoint_interval
    {C : Set ℝ} (hC : IsClosed C) {a b : ℝ} (hab : a ≤ b)
    (hDisj : Disjoint C (Set.Icc a b)) :
    ∃ a' b', a' < a ∧ b < b' ∧ C ⊆ Set.Iic a' ∪ Set.Ici b' := by
  have haNot : a ∉ C := by
    intro ha
    exact (Set.disjoint_left.1 hDisj) ha ⟨le_rfl, hab⟩
  have hbNot : b ∉ C := by
    intro hb
    exact (Set.disjoint_left.1 hDisj) hb ⟨hab, le_rfl⟩
  have hOpen : IsOpen Cᶜ := hC.isOpen_compl
  rcases Metric.isOpen_iff.mp hOpen a haNot with ⟨δa, hδa, hBallA⟩
  rcases Metric.isOpen_iff.mp hOpen b hbNot with ⟨δb, hδb, hBallB⟩
  refine ⟨a - δa / 2, b + δb / 2, by linarith, by linarith, ?_⟩
  intro x hx
  by_cases hxLeft : x ≤ a - δa / 2
  · exact Or.inl hxLeft
  by_cases hxRight : b + δb / 2 ≤ x
  · exact Or.inr hxRight
  have hxLeft' : a - δa / 2 < x := lt_of_not_ge hxLeft
  have hxRight' : x < b + δb / 2 := lt_of_not_ge hxRight
  by_cases hxltA : x < a
  · exfalso
    have hxBall : x ∈ Metric.ball a δa := by
      show dist x a < δa
      simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using
        And.intro (by linarith) (by linarith)
    exact hBallA hxBall hx
  by_cases hBltx : b < x
  · exfalso
    have hxBall : x ∈ Metric.ball b δb := by
      show dist x b < δb
      simpa [Metric.mem_ball, Real.dist_eq, abs_lt] using
        And.intro (by linarith) (by linarith)
    exact hBallB hxBall hx
  exfalso
  have hxIcc : x ∈ Set.Icc a b := ⟨le_of_not_gt hxltA, le_of_not_gt hBltx⟩
  exact (Set.disjoint_left.1 hDisj) hx hxIcc

/-- Helper for Theorem 23.11: once a nonempty closed convex subset of `ℝ` is separated from a
closed set, the closed set is covered either by one closed ray or by two closed rays leaving a
gap around the convex set. -/
private theorem closedSet_cover_of_disjoint_nonempty_closedConvex
    {C K : Set ℝ} (hC : IsClosed C) (hKClosed : IsClosed K) (hKConvex : Convex ℝ K)
    (hKne : K.Nonempty) (hDisj : Disjoint C K) :
    (∃ a, C ⊆ Set.Iic a) ∨
      (∃ b, C ⊆ Set.Ici b) ∨
      ∃ a b, a < b ∧ C ⊆ Set.Iic a ∪ Set.Ici b := by
  rcases closedConvex_real_shape hKClosed hKConvex with hEmpty | hUniv | hLeft | hRight | hIcc
  · exact False.elim (hKne.ne_empty hEmpty)
  · -- Proof comment: if the convex set is all of `ℝ`, disjointness forces `C = ∅`, so any
    -- closed ray covers `C`.
    refine Or.inl ⟨0, ?_⟩
    intro x hx
    exact False.elim ((Set.disjoint_left.1 hDisj) hx (by simpa [hUniv]))
  · rcases hLeft with ⟨a, hK⟩
    -- Proof comment: missing a closed left ray pushes the closed set into a strictly larger
    -- right ray.
    rcases closedSet_rightRay_of_disjoint_leftRay hC (by simpa [hK] using hDisj) with
      ⟨b, _hab, hCover⟩
    exact Or.inr <| Or.inl ⟨b, hCover⟩
  · rcases hRight with ⟨b, hK⟩
    -- Proof comment: the right-ray case is the symmetric companion of the left-ray case.
    rcases closedSet_leftRay_of_disjoint_rightRay hC (by simpa [hK] using hDisj) with
      ⟨a, _hab, hCover⟩
    exact Or.inl ⟨a, hCover⟩
  · rcases hIcc with ⟨a, b, hab, hK⟩
    -- Proof comment: when the convex set is a bounded interval, the previous endpoint-gap lemma
    -- gives the required two-ray cover.
    rcases closedSet_twoRayCover_of_disjoint_interval hC hab (by simpa [hK] using hDisj) with
      ⟨a', b', ha', hb', hCover⟩
    have hab' : a' < b' := by
      linarith
    exact Or.inr <| Or.inr ⟨a', b', hab', hCover⟩

/-- Helper for Theorem 23.11: the one-letter Legendre-Fenchel rate is always nonnegative because
the zero tilt contributes the value `0`. -/
private theorem legendreFenchelRateFunction_nonneg
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (x : ℝ) :
    (0 : EReal) ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
  -- Proof comment: the defining Legendre-Fenchel supremum contains the affine summand at `t = 0`,
  -- and that summand equals `0`.
  rw [legendreFenchelRateFunction]
  refine le_sSup ?_
  refine ⟨0, ?_⟩
  have hzero : (0 : ℝ) ∈ integrableExpSet (X 0) P := by
    simp [integrableExpSet]
  have hzeroEval : ((((0 * x : ℝ) : EReal) - Λ(X 0; P) 0)) = 0 := by
    rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
      (X := X 0) (P := P) hzero]
    simp [cgf_zero]
  simpa using hzeroEval

/-- Helper for Theorem 23.11: every owner-rate sublevel is closed and convex, so on `ℝ` it has
one of the standard interval shapes. -/
private theorem empiricalMeanOwnerRateSublevel_shape
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (a : ENNReal) :
    let K : Set ℝ := {x : ℝ | (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal ≤ a}
    IsClosed K ∧ Convex ℝ K ∧
      (K = ∅ ∨ K = Set.univ ∨ (∃ u, K = Set.Iic u) ∨ (∃ v, K = Set.Ici v) ∨
        ∃ u v, u ≤ v ∧ K = Set.Icc u v) := by
  let K : Set ℝ := {x : ℝ | (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal ≤ a}
  have hClosed : IsClosed K := by
    have hLsc := ownerRate_lowerSemicontinuous (P := P) (X := X 0)
    rw [lowerSemicontinuous_iff_isClosed_preimage] at hLsc
    simpa [K] using hLsc a
  have hConvex : Convex ℝ K := by
    by_cases haTop : a = ⊤
    · -- Proof comment: the top sublevel is all of `ℝ`, so convexity is immediate.
      simpa [K, haTop] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    · intro x hx y hy u v hu hv huv
      have hv_le_one : v ≤ 1 := by
        linarith
      have hu_eq : u = 1 - v := by
        linarith
      have hx_top :
          legendreFenchelRateFunction (Λ(X 0; P)) x ≠ ⊤ := by
        intro hxTop
        have htop_le : (⊤ : ENNReal) ≤ a := by
          simpa [K, hxTop] using hx
        exact haTop (top_le_iff.mp htop_le)
      have hy_top :
          legendreFenchelRateFunction (Λ(X 0; P)) y ≠ ⊤ := by
        intro hyTop
        have htop_le : (⊤ : ENNReal) ≤ a := by
          simpa [K, hyTop] using hy
        exact haTop (top_le_iff.mp htop_le)
      have hx_enn_top :
          (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal ≠ ⊤ := by
        simpa [EReal.toENNReal_eq_top_iff, hx_top]
      have hy_enn_top :
          (legendreFenchelRateFunction (Λ(X 0; P)) y).toENNReal ≠ ⊤ := by
        simpa [EReal.toENNReal_eq_top_iff, hy_top]
      have hx_real :
          (legendreFenchelRateFunction (Λ(X 0; P)) x).toReal ≤ a.toReal := by
        have hx_real' :
            (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal.toReal ≤ a.toReal := by
          exact (ENNReal.toReal_le_toReal hx_enn_top haTop).2 hx
        simpa [EReal.toReal_toENNReal,
          legendreFenchelRateFunction_nonneg (P := P) (X := X) x] using hx_real'
      have hy_real :
          (legendreFenchelRateFunction (Λ(X 0; P)) y).toReal ≤ a.toReal := by
        have hy_real' :
            (legendreFenchelRateFunction (Λ(X 0; P)) y).toENNReal.toReal ≤ a.toReal := by
          exact (ENNReal.toReal_le_toReal hy_enn_top haTop).2 hy
        simpa [EReal.toReal_toENNReal,
          legendreFenchelRateFunction_nonneg (P := P) (X := X) y] using hy_real'
      have hSegment :
          legendreFenchelRateFunction (Λ(X 0; P)) ((1 - v) * x + v * y) ≤
            ((((1 - v) * (legendreFenchelRateFunction (Λ(X 0; P)) x).toReal +
              v * (legendreFenchelRateFunction (Λ(X 0; P)) y).toReal : ℝ) : EReal)) := by
        -- Proof comment: finite endpoint values let the convexity estimate from the Legendre
        -- transform control the whole segment.
        exact legendreFenchelRateFunction_convexCombo_le
          (P := P) (X := X 0) hv hv_le_one hx_top hy_top
      have hRealLe :
          (1 - v) * (legendreFenchelRateFunction (Λ(X 0; P)) x).toReal +
              v * (legendreFenchelRateFunction (Λ(X 0; P)) y).toReal ≤
            a.toReal := by
        have hOneMinusNonneg : 0 ≤ 1 - v := by
          linarith
        nlinarith
      let combo : ℝ :=
        (1 - v) * (legendreFenchelRateFunction (Λ(X 0; P)) x).toReal +
          v * (legendreFenchelRateFunction (Λ(X 0; P)) y).toReal
      have hComboNonneg : 0 ≤ combo := by
        dsimp [combo]
        have hx_nonneg : 0 ≤ (legendreFenchelRateFunction (Λ(X 0; P)) x).toReal := by
          exact EReal.toReal_nonneg (legendreFenchelRateFunction_nonneg (P := P) (X := X) x)
        have hy_nonneg : 0 ≤ (legendreFenchelRateFunction (Λ(X 0; P)) y).toReal := by
          exact EReal.toReal_nonneg (legendreFenchelRateFunction_nonneg (P := P) (X := X) y)
        have hOneMinusNonneg : 0 ≤ 1 - v := by
          linarith
        nlinarith
      have hBound :
          ((combo : ℝ) : EReal) ≤
            ((a : ENNReal) : EReal) := by
        have hBoundENN : ENNReal.ofReal combo ≤ a := by
          exact (ENNReal.ofReal_le_iff_le_toReal haTop).2 hRealLe
        have hComboCast :
            ((combo : ℝ) : EReal) = (((ENNReal.ofReal combo : ENNReal) : EReal)) := by
          rw [ENNReal.ofReal_eq_coe_nnreal hComboNonneg]
          rfl
        rw [hComboCast]
        exact_mod_cast hBoundENN
      have hToENN :
          (legendreFenchelRateFunction (Λ(X 0; P)) (((u : ℝ) • x) + ((v : ℝ) • y))).toENNReal ≤ a := by
        have hComb :
            (((u : ℝ) • x) + ((v : ℝ) • y) : ℝ) = ((1 - v) * x + v * y) := by
          simp [smul_eq_mul, hu_eq]
        have hle :
            legendreFenchelRateFunction (Λ(X 0; P)) (((u : ℝ) • x) + ((v : ℝ) • y)) ≤
              ((a : ENNReal) : EReal) := by
          rw [hComb]
          calc
            legendreFenchelRateFunction (Λ(X 0; P)) ((1 - v) * x + v * y) ≤ ((combo : ℝ) : EReal) := by
              simpa [combo] using hSegment
            _ ≤ ((a : ENNReal) : EReal) := hBound
        simpa using EReal.toENNReal_le_toENNReal hle
      exact hToENN
  simpa [K] using And.intro hClosed <| And.intro hConvex <|
    closedConvex_real_shape hClosed hConvex

/-- Helper for Theorem 23.11: a strict comparison value above the negated owner rate infimum on
`C` forces `C` to be disjoint from the corresponding owner-rate sublevel. -/
private theorem disjoint_empiricalMeanOwnerRateSublevel_of_lt_neg_sInf
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {C : Set ℝ} {y : EReal}
    (hy :
      y >
        -sInf
          ((fun x ↦
            (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) '' C)) :
    Disjoint C
      {x : ℝ |
        ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) ≤ -y} := by
  refine Set.disjoint_left.2 ?_
  intro x hxC hxLevel
  have hNegLevel :
      -y <
        sInf
          ((fun x ↦
            (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) '' C) := by
    simpa using EReal.neg_strictAnti hy
  have hMem :
      ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) ∈
        ((fun x ↦
          (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) '' C) := by
    exact ⟨x, hxC, rfl⟩
  have hRateLower :
      -y <
        ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
    exact hNegLevel.trans_le (sInf_le hMem)
  exact (not_lt_of_ge hxLevel) hRateLower

/-- Helper for Theorem 23.11: if a point to the right of a low-rate left-ray sublevel already has
rate strictly above that level, then some nonnegative tilt witnesses the strict inequality. -/
private theorem exists_nonneg_affineWitness_of_leftRaySublevel
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    {a x : ℝ} {y : EReal}
    (ha : legendreFenchelRateFunction (Λ(X; P)) a ≤ -y)
    (hx : -y < legendreFenchelRateFunction (Λ(X; P)) x)
    (hax : a < x) :
    ∃ t : ℝ, 0 ≤ t ∧ -((((t * x : ℝ) : EReal) - Λ(X; P) t)) < y := by
  rw [legendreFenchelRateFunction, sSup_range] at hx
  rcases lt_iSup_iff.mp hx with ⟨t, ht⟩
  have htNonneg : 0 ≤ t := by
    by_contra htNeg
    have htxa : t * x ≤ t * a := by nlinarith
    have hAffineLe :
        ((((t * x : ℝ) : EReal) - Λ(X; P) t)) ≤
          ((((t * a : ℝ) : EReal) - Λ(X; P) t)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (show (((t * x : ℝ) : EReal)) ≤ (((t * a : ℝ) : EReal)) by
            exact_mod_cast htxa)
          (-(Λ(X; P) t))
    have hContra :
        -y < legendreFenchelRateFunction (Λ(X; P)) a := by
      exact ht.trans_le <|
        le_trans hAffineLe (affineSummand_le_legendreFenchelRateFunction (P := P) (X := X))
    exact not_lt_of_ge ha hContra
  refine ⟨t, htNonneg, ?_⟩
  simpa using EReal.neg_lt_neg_iff.mpr ht

/-- Helper for Theorem 23.11: if a point to the left of a low-rate right-ray sublevel already has
rate strictly above that level, then some nonpositive tilt witnesses the strict inequality. -/
private theorem exists_nonpos_affineWitness_of_rightRaySublevel
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    {x b : ℝ} {y : EReal}
    (hb : legendreFenchelRateFunction (Λ(X; P)) b ≤ -y)
    (hx : -y < legendreFenchelRateFunction (Λ(X; P)) x)
    (hxb : x < b) :
    ∃ t : ℝ, t ≤ 0 ∧ -((((t * x : ℝ) : EReal) - Λ(X; P) t)) < y := by
  rw [legendreFenchelRateFunction, sSup_range] at hx
  rcases lt_iSup_iff.mp hx with ⟨t, ht⟩
  have htNonpos : t ≤ 0 := by
    by_contra htPos
    have htxb : t * x ≤ t * b := by nlinarith
    have hAffineLe :
        ((((t * x : ℝ) : EReal) - Λ(X; P) t)) ≤
          ((((t * b : ℝ) : EReal) - Λ(X; P) t)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (show (((t * x : ℝ) : EReal)) ≤ (((t * b : ℝ) : EReal)) by
            exact_mod_cast htxb)
          (-(Λ(X; P) t))
    have hContra :
        -y < legendreFenchelRateFunction (Λ(X; P)) b := by
      exact ht.trans_le <|
        le_trans hAffineLe (affineSummand_le_legendreFenchelRateFunction (P := P) (X := X))
    exact not_lt_of_ge hb hContra
  refine ⟨t, htNonpos, ?_⟩
  simpa using EReal.neg_lt_neg_iff.mpr ht

/-- Helper for Theorem 23.11: every point of an open set lies in a smaller open interval still
contained in that set. -/
private theorem exists_Ioo_subset_of_isOpen_mem
    {s : Set ℝ} (hsOpen : IsOpen s) {x : ℝ} (hx : x ∈ s) :
    ∃ δ > 0, Set.Ioo (x - δ) (x + δ) ⊆ s := by
  rcases Metric.isOpen_iff.mp hsOpen x hx with ⟨δ, hδpos, hball⟩
  refine ⟨δ, hδpos, ?_⟩
  intro y hy
  apply hball
  -- Proof comment: points of the interval satisfy `|y - x| < δ`, so they lie in the metric ball
  -- provided by openness.
  show dist y x < δ
  have habs : |y - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  simpa [Real.dist_eq] using habs

/-- Helper for Theorem 23.11: enlarging an event can only increase its scaled logarithmic mass. -/
private theorem scaledLogMassAlong_mono_of_subset
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) {s t : Set E}
    (hst : s ⊆ t) (i : ι) :
    scaledLogMassAlong μ ε s i ≤ scaledLogMassAlong μ ε t i := by
  -- Proof comment: measure and `ENNReal.log` are monotone, and the positive scale preserves the
  -- inequality.
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def]
  have hlog : ENNReal.log (μ i s) ≤ ENNReal.log (μ i t) := by
    exact ENNReal.log_monotone (measure_mono hst)
  have hε_nonneg : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  exact mul_le_mul_of_nonneg_left hlog hε_nonneg

/-- Helper for Theorem 23.11: the scaled logarithmic mass of the empty event is `⊥` because
`log 0 = ⊥` and the speed parameter is strictly positive. -/
private theorem scaledLogMassAlong_empty_eq_bot
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (i : ι) :
    scaledLogMassAlong μ ε (∅ : Set E) i = ⊥ := by
  -- Proof comment: unfold the scaled logarithmic mass and use positivity of the speed factor to
  -- keep the bottom value coming from `log 0`.
  rw [scaledLogMassAlong_def]
  have hε : (0 : EReal) < ((ε i : ℝ) : EReal) := by
    exact_mod_cast (ε i).2
  simp [EReal.mul_bot_of_pos hε]

/-- Helper for Theorem 23.11: for the logarithmic mass, the union of two events costs only the
vanishing penalty `ε log 2` on top of the larger scaled exponent. -/
private theorem scaledLogMassAlong_union_le_logTwo_add_max
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → Measure E) (ε : ι → PositiveParameter) (s t : Set E) (i : ι) :
    scaledLogMassAlong μ ε (s ∪ t) i ≤
      ((((ε i : ℝ) * Real.log 2 : ℝ) : EReal)) +
        max (scaledLogMassAlong μ ε s i) (scaledLogMassAlong μ ε t i) := by
  have hα : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    have hα_real : 0 ≤ (ε i : ℝ) := le_of_lt (show 0 < (ε i : ℝ) from (ε i).2)
    exact_mod_cast hα_real
  have hUnionMass : μ i (s ∪ t) ≤ μ i s + μ i t := by
    simpa using measure_union_le s t (μ := μ i)
  have hAddLe : μ i s + μ i t ≤ (2 : ENNReal) * max (μ i s) (μ i t) := by
    calc
      μ i s + μ i t ≤ max (μ i s) (μ i t) + max (μ i s) (μ i t) := by
        exact add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = (2 : ENNReal) * max (μ i s) (μ i t) := by
        simp [two_mul]
  have hLog :
      ENNReal.log (μ i (s ∪ t)) ≤ ENNReal.log ((2 : ENNReal) * max (μ i s) (μ i t)) := by
    exact ENNReal.log_monotone (hUnionMass.trans hAddLe)
  have hMul :
      ((ε i : ℝ) : EReal) * ENNReal.log (μ i (s ∪ t)) ≤
        ((ε i : ℝ) : EReal) * ENNReal.log ((2 : ENNReal) * max (μ i s) (μ i t)) := by
    exact mul_le_mul_of_nonneg_left hLog hα
  have hα_ne_top : ((ε i : ℝ) : EReal) ≠ ⊤ := by
    simp
  have hlogTwo :
      ENNReal.log (2 : ENNReal) = ((Real.log 2 : ℝ) : EReal) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
    simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
  rw [scaledLogMassAlong_def, scaledLogMassAlong_def, scaledLogMassAlong_def]
  refine le_trans hMul ?_
  rw [ENNReal.log_mul_add, EReal.left_distrib_of_nonneg_of_ne_top hα hα_ne_top, hlogTwo]
  rcases le_total (μ i s) (μ i t) with hab | hba
  · -- Proof comment: when the right event has larger mass, the dominant exponent is the right
    -- one and the union only contributes the additive `ε log 2` penalty.
    have hmono :
        ((ε i : ℝ) : EReal) * ENNReal.log (μ i s) ≤
          ((ε i : ℝ) : EReal) * ENNReal.log (μ i t) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hab) hα
    rw [max_eq_right hab, max_eq_right hmono]
    simpa [mul_comm, mul_left_comm, mul_assoc]
  · -- Proof comment: the symmetric branch uses the left event as the dominant mass.
    have hmono :
        ((ε i : ℝ) : EReal) * ENNReal.log (μ i t) ≤
          ((ε i : ℝ) : EReal) * ENNReal.log (μ i s) := by
      exact mul_le_mul_of_nonneg_left (ENNReal.log_monotone hba) hα
    rw [max_eq_left hba, max_eq_left hmono]
    simpa [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Theorem 23.11: every scaled logarithmic mass is nonpositive for a family of
probability laws, because every event has mass at most `1`. -/
private theorem scaledLogMassAlong_nonpos_of_probability
    {E : Type*} [MeasurableSpace E] {ι : Type*}
    (μ : ι → ProbabilityMeasure E) (ε : ι → PositiveParameter) {s : Set E} (i : ι) :
    scaledLogMassAlong (fun j ↦ (μ j : Measure E)) ε s i ≤ 0 := by
  -- Proof comment: event masses under a probability law are bounded by `1`, so their logarithms
  -- are nonpositive, and the positive speed preserves that inequality.
  rw [scaledLogMassAlong_def]
  have hMass : ((μ i : Measure E) s) ≤ 1 := by
    calc
      (μ i : Measure E) s ≤ (μ i : Measure E) Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := by simp
  have hLog : ENNReal.log ((μ i : Measure E) s) ≤ 0 := by
    simpa using (ENNReal.log_le_zero_iff).2 hMass
  have hε : (0 : EReal) ≤ ((ε i : ℝ) : EReal) := by
    exact_mod_cast le_of_lt (ε i).2
  have hMul :
      ((ε i : ℝ) : EReal) * ENNReal.log ((μ i : Measure E) s) ≤
        ((ε i : ℝ) : EReal) * 0 := by
    exact mul_le_mul_of_nonneg_left hLog hε
  simpa using hMul

/-- Helper for Theorem 23.11: if the exponential-integrability domain is exactly `{0}`, then the
canonical owner Legendre-Fenchel rate is identically zero. -/
private theorem ownerRate_eq_zero_of_integrableExpSet_eq_singleton_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hSet : integrableExpSet X P = ({0} : Set ℝ)) :
    ∀ x : ℝ, legendreFenchelRateFunction (Λ(X; P)) x = 0 := by
  intro x
  refine le_antisymm ?_ ?_
  · -- Proof comment: every nonzero tilt leaves the effective domain, while the `t = 0` summand
    -- contributes exactly `0`.
    rw [legendreFenchelRateFunction]
    refine sSup_le ?_
    rintro _ ⟨t, rfl⟩
    change (((t * x : ℝ) : EReal) - Λ(X; P) t) ≤ 0
    by_cases ht : t = 0
    · rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet (X := X) (P := P)]
      · simp [ht]
      · simp [hSet, ht]
    · rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet (X := X) (P := P)]
      · simp
      · simp [hSet, ht]
  · -- Proof comment: the `t = 0` affine summand lies in the defining range and already equals `0`.
    rw [legendreFenchelRateFunction]
    let f : ℝ → EReal := fun t ↦ ((t * x : ℝ) : EReal) - Λ(X; P) t
    have hmem : f 0 ∈ Set.range f := ⟨0, rfl⟩
    have hzero : f 0 = 0 := by
      change (((0 * x : ℝ) : EReal) - Λ(X; P) 0) = 0
      rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet (X := X) (P := P)]
      · simp
      · simp [hSet]
    have hle : f 0 ≤ sSup (Set.range f) := le_sSup hmem
    rw [hzero] at hle
    simpa using hle

/-- Helper for Theorem 23.11: in the singleton-domain branch, the owner rate-image infimum on any
nonempty set is `0`. -/
private theorem ownerRateImage_sInf_eq_zero_of_nonempty_of_integrableExpSet_eq_singleton_zero
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hSet : integrableExpSet X P = ({0} : Set ℝ)) {s : Set ℝ} (hs : s.Nonempty) :
    sInf ((fun x ↦
      ((((legendreFenchelRateFunction (Λ(X; P)) x).toENNReal : ENNReal) : EReal))) '' s) = 0 := by
  rcases hs with ⟨x, hx⟩
  have hzero :
      ∀ y : ℝ,
        ((((legendreFenchelRateFunction (Λ(X; P)) y).toENNReal : ENNReal) : EReal)) = 0 := by
    intro y
    -- Proof comment: first rewrite the owner rate to `0`, then coerce back through `toENNReal`.
    rw [ownerRate_eq_zero_of_integrableExpSet_eq_singleton_zero (P := P) (X := X) hSet y]
    simp
  have himage :
      ((fun y ↦
        ((((legendreFenchelRateFunction (Λ(X; P)) y).toENNReal : ENNReal) : EReal))) '' s) =
        ({0} : Set EReal) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hzero y
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      refine ⟨x, hx, ?_⟩
      simpa [hz] using hzero x
  rw [himage]
  simp

/-- Helper for Theorem 23.11: along any ray inside the effective domain, the cumulant-generating
function returns to `0` as the ray parameter tends to `0`. -/
private theorem cgf_tendsto_zero_along_inverseMultiples
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → ℝ) {τ : ℝ}
    (hτ : τ ∈ integrableExpSet Y P) :
    Tendsto (fun n : ℕ ↦ cgf Y P (τ / (n + 2 : ℝ))) atTop (𝓝 0) := by
  have hτInt : Integrable (fun ω ↦ Real.exp (τ * Y ω)) P :=
    integrable_of_mem_integrableExpSet hτ
  have hZero : (0 : ℝ) ∈ integrableExpSet Y P := by
    simp [integrableExpSet]
  let F : ℕ → Ω → ℝ := fun n ω ↦ Real.exp ((τ / (n + 2 : ℝ)) * Y ω)
  have hIntegral :
      Tendsto (fun n : ℕ ↦ ∫ ω, F n ω ∂P) atTop (𝓝 (∫ ω, (1 : ℝ) ∂P)) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (bound := fun ω ↦ 1 + Real.exp (τ * Y ω)) ?_ ?_ ?_ ?_
    · intro n
      have hMem :
          τ / (n + 2 : ℝ) ∈ integrableExpSet Y P := by
        have hr0 : 0 ≤ ((n + 2 : ℝ)⁻¹) := by positivity
        have hr1 : ((n + 2 : ℝ)⁻¹) ≤ 1 := by
          have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
          have hge : (1 : ℝ) ≤ n + 2 := by nlinarith
          exact inv_le_one_of_one_le₀ hge
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          convex_integrableExpSet.smul_mem_of_zero_mem hZero hτ ⟨hr0, hr1⟩
      exact (integrable_of_mem_integrableExpSet hMem).aestronglyMeasurable
    · exact (integrable_const (1 : ℝ)).add hτInt
    · intro n
      filter_upwards with ω
      have hr0 : 0 ≤ ((n + 2 : ℝ)⁻¹) := by positivity
      have hr1 : ((n + 2 : ℝ)⁻¹) ≤ 1 := by
        have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
        have hge : (1 : ℝ) ≤ n + 2 := by nlinarith
        exact inv_le_one_of_one_le₀ hge
      have hbound :
          Real.exp (((n + 2 : ℝ)⁻¹) * (τ * Y ω)) ≤ 1 + Real.exp (τ * Y ω) := by
        by_cases hNonneg : 0 ≤ τ * Y ω
        · have hle :
              ((n + 2 : ℝ)⁻¹) * (τ * Y ω) ≤ τ * Y ω := by
            nlinarith
          exact le_trans (Real.exp_le_exp.mpr hle) (le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num))
        · have hle :
              ((n + 2 : ℝ)⁻¹) * (τ * Y ω) ≤ 0 := by
            nlinarith
          exact le_trans (Real.exp_le_one_iff.mpr hle)
            (by nlinarith [show (0 : ℝ) ≤ Real.exp (τ * Y ω) by positivity])
      simpa [F, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_pos _).le] using hbound
    · filter_upwards with ω
      have hNat :
          Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop := by
        exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
      have hInv :
          Tendsto (fun n : ℕ ↦ ((n : ℝ) + 2)⁻¹) atTop (𝓝 (0 : ℝ)) := by
        exact tendsto_inv_atTop_zero.comp hNat
      have hCoeff :
          Tendsto (fun n : ℕ ↦ τ / (n + 2 : ℝ)) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          tendsto_const_nhds.mul hInv
      have hPoint :
          Tendsto (fun n : ℕ ↦ Real.exp ((τ / (n + 2 : ℝ)) * Y ω)) atTop (𝓝 1) := by
        have hMul :
            Tendsto (fun n : ℕ ↦ (τ / (n + 2 : ℝ)) * Y ω) atTop (𝓝 (0 * Y ω)) := by
          simpa using hCoeff.mul tendsto_const_nhds
        simpa [F] using Real.continuous_exp.continuousAt.tendsto.comp hMul
      simpa using hPoint
  have hMgf :
      Tendsto (fun n : ℕ ↦ mgf Y P (τ / (n + 2 : ℝ))) atTop (𝓝 1) := by
    simpa [mgf, F] using hIntegral
  have hLog :
      Tendsto (fun n : ℕ ↦ Real.log (mgf Y P (τ / (n + 2 : ℝ)))) atTop (𝓝 (Real.log 1)) := by
    exact (Real.continuousAt_log (by norm_num)).tendsto.comp hMgf
  simpa [cgf] using hLog

/-- Helper for Theorem 23.11: at an interior tilt, the owner rate is exactly the supporting affine
value at the derivative point of the cumulant-generating function. -/
private theorem empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {t : ℝ} (ht : t ∈ interior (integrableExpSet (X 0) P)) :
    ((((legendreFenchelRateFunction (Λ(X 0; P))
        (deriv (cgf (X 0) P) t)).toENNReal : ENNReal) : EReal)) =
      (((t * deriv (cgf (X 0) P) t - cgf (X 0) P t : ℝ)) : EReal) := by
  -- Route correction: instead of expanding convex secant algebra directly on `cgf`, move to the
  -- tilted law at slope `t`, apply Jensen to `exp ((s - t) * X)`, and bring the supporting-line
  -- inequality back to the Legendre transform in one step.
  let x : ℝ := deriv (cgf (X 0) P) t
  let ν : Measure Ω := P.tilted (t * X 0 ·)
  have htInt : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
    interior_subset (s := integrableExpSet (X 0) P) ht
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted htInt
  have hx :
      ν[X 0] = x := by
    -- Proof comment: the tilted first moment is exactly the derivative of the one-letter cgf.
    simpa [ν, x] using integral_tilted_mul_self (μ := P) (X := X 0) (t := t) ht
  have hUpper :
      legendreFenchelRateFunction (Λ(X 0; P)) x ≤
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    rw [legendreFenchelRateFunction]
    refine sSup_le ?_
    rintro _ ⟨s, rfl⟩
    by_cases hs : s ∈ integrableExpSet (X 0) P
    · have hsInt : Integrable (fun ω ↦ Real.exp (s * X 0 ω)) P := hs
      have hIntX : Integrable (X 0) ν := by
        simpa using (memLp_tilted_mul (μ := P) (X := X 0) (t := t) ht 1).integrable
      have hfi : Integrable (fun ω ↦ (s - t) * X 0 ω) ν := by
        simpa [sub_eq_add_neg, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
          hIntX.const_mul (s - t)
      have hgi : Integrable (fun ω ↦ Real.exp ((s - t) * X 0 ω)) ν := by
        rw [integrable_tilted_iff (μ := P) (f := fun ω ↦ t * X 0 ω)
          (g := fun ω ↦ Real.exp ((s - t) * X 0 ω)) htInt]
        have hWeighted :
            Integrable
              (fun ω ↦ Real.exp (t * X 0 ω) * Real.exp ((s - t) * X 0 ω)) P := by
          convert hsInt using 1
          ext ω
          rw [← Real.exp_add]
          ring_nf
        simpa [smul_eq_mul] using hWeighted
      have hJensen :
          Real.exp (∫ ω, (s - t) * X 0 ω ∂ν) ≤
            ∫ ω, Real.exp ((s - t) * X 0 ω) ∂ν := by
        -- Proof comment: Jensen under the tilted law gives the supporting-line inequality at the
        -- derivative point.
        exact
          ConvexOn.map_integral_le (μ := ν) (s := Set.univ) (g := Real.exp)
            convexOn_exp Real.continuousOn_exp isClosed_univ
            (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _)
            hfi hgi
      have hIntegral :
          ∫ ω, Real.exp ((s - t) * X 0 ω) ∂ν =
            Real.exp (cgf (X 0) P s - cgf (X 0) P t) := by
        -- Proof comment: compute the tilted exponential moment by collapsing the density back to
        -- the original cgf at slopes `s` and `t`.
        rw [show ν = P.tilted (fun ω ↦ t * X 0 ω) by rfl]
        rw [MeasureTheory.integral_exp_tilted
          (μ := P) (f := fun ω ↦ t * X 0 ω) (g := fun ω ↦ (s - t) * X 0 ω)]
        rw [Real.exp_sub, exp_cgf hsInt, exp_cgf htInt]
        congr 1
        congr with ω
        congr 1
        change t * X 0 ω + ((s - t) * X 0 ω) = s * X 0 ω
        ring
      have hIntegralX :
          ∫ ω, (s - t) * X 0 ω ∂ν = (s - t) * x := by
        -- Proof comment: the tilted expectation of `X₀` was already identified as `x`.
        rw [MeasureTheory.integral_const_mul, hx]
      have hReal :
          s * x - cgf (X 0) P s ≤ t * x - cgf (X 0) P t := by
        have hExp :
            Real.exp ((s - t) * x) ≤ Real.exp (cgf (X 0) P s - cgf (X 0) P t) := by
          calc
            Real.exp ((s - t) * x) = Real.exp (∫ ω, (s - t) * X 0 ω ∂ν) := by
              rw [hIntegralX]
            _ ≤ ∫ ω, Real.exp ((s - t) * X 0 ω) ∂ν := hJensen
            _ = Real.exp (cgf (X 0) P s - cgf (X 0) P t) := hIntegral
        have hSlope : (s - t) * x ≤ cgf (X 0) P s - cgf (X 0) P t := by
          exact Real.exp_le_exp.mp hExp
        linarith
      calc
        ((((s * x : ℝ) : EReal) - Λ(X 0; P) s)) = (((s * x - cgf (X 0) P s : ℝ)) : EReal) := by
          rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
            (X := X 0) (P := P) hs]
          simp [EReal.coe_sub]
        _ ≤ (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
          exact_mod_cast hReal
    · -- Proof comment: outside the effective domain, the Legendre summand is `⊥`.
      change ((((s * x : ℝ) : EReal) - Λ(X 0; P) s)) ≤
        (((t * x - cgf (X 0) P t : ℝ)) : EReal)
      rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
        (X := X 0) (P := P) hs]
      simp
  have hLower :
      (((t * x - cgf (X 0) P t : ℝ)) : EReal) ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
    -- Proof comment: the defining supremum contains the affine summand at the tilt `t` itself.
    calc
      (((t * x - cgf (X 0) P t : ℝ)) : EReal) = ((((t * x : ℝ) : EReal) - Λ(X 0; P) t)) := by
        rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
          (X := X 0) (P := P) (interior_subset ht)]
        simp [EReal.coe_sub]
      _ ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
        exact affineSummand_le_legendreFenchelRateFunction (P := P) (X := X 0)
  have hRate :
      legendreFenchelRateFunction (Λ(X 0; P)) x =
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    exact le_antisymm hUpper hLower
  rw [show deriv (cgf (X 0) P) t = x by rfl, hRate]
  exact EReal.coe_toENNReal <| by
    simpa [hRate] using
      legendreFenchelRateFunction_nonneg (P := P) (X := X) x

/-- Helper for Theorem 23.11: evaluating the supporting affine line at `2 * t` bounds the affine
gap at an interior tilt `t` by a nearby difference of cumulant-generating functions. -/
private theorem affineGap_atDeriv_le_cgfDoubleGap_of_mem_interior
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {t : ℝ} (ht : t ∈ interior (integrableExpSet (X 0) P))
    (hDouble : 2 * t ∈ integrableExpSet (X 0) P) :
    t * deriv (cgf (X 0) P) t - cgf (X 0) P t ≤
      cgf (X 0) P (2 * t) - 2 * cgf (X 0) P t := by
  let x : ℝ := deriv (cgf (X 0) P) t
  have hRateEq :
      (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal) =
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    -- Proof comment: identify the owner rate at the derivative point with its supporting affine
    -- value before comparing against the `2 * t` affine summand.
    simpa [x] using
      empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior (P := P) (X := X) ht
  have hLegEq :
      legendreFenchelRateFunction (Λ(X 0; P)) x =
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    -- Proof comment: remove the owner `toENNReal` wrapper using nonnegativity of the Legendre
    -- transform at the derivative point.
    calc
      legendreFenchelRateFunction (Λ(X 0; P)) x =
          ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
            symm
            simpa using EReal.coe_toENNReal
              (legendreFenchelRateFunction_nonneg (P := P) (X := X) x)
      _ = (((t * x - cgf (X 0) P t : ℝ)) : EReal) := hRateEq
  have hAffine :
      (((2 * t * x - cgf (X 0) P (2 * t) : ℝ)) : EReal) ≤
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    -- Proof comment: the `2 * t` affine summand is one candidate in the Legendre supremum, so it
    -- is bounded by the supporting affine value at `t`.
    calc
      (((2 * t * x - cgf (X 0) P (2 * t) : ℝ)) : EReal) =
          ((((2 * t * x : ℝ) : EReal) - Λ(X 0; P) (2 * t)) : EReal) := by
            rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
              (X := X 0) (P := P) hDouble]
            simp [EReal.coe_sub]
      _ ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
        exact affineSummand_le_legendreFenchelRateFunction
          (P := P) (X := X 0) (x := x) (t := 2 * t)
      _ = (((t * x - cgf (X 0) P t : ℝ)) : EReal) := hLegEq
  have hReal :
      2 * t * x - cgf (X 0) P (2 * t) ≤ t * x - cgf (X 0) P t := by
    exact_mod_cast hAffine
  -- Proof comment: rearrange the affine comparison into the desired `cgf(2t) - 2 cgf(t)` bound.
  linarith

/-- Helper for Theorem 23.11: once the exponential-integrability domain is not the singleton
`{0}`, every positive owner-rate sublevel contains a derivative-point witness. -/
private theorem empiricalMeanOwnerRateSublevel_nonempty_of_pos_of_nontrivialIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {level : ENNReal} (hLevel : 0 < level) :
    ({x : ℝ | (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal ≤ level}).Nonempty := by
  let s : Set ℝ := integrableExpSet (X 0) P
  have hZero : (0 : ℝ) ∈ s := by
    simp [s, integrableExpSet]
  have hNontrivial : s.Nontrivial := by
    -- Proof comment: the effective domain always contains `0`, so `s ≠ {0}` immediately upgrades
    -- to a genuinely nontrivial convex set.
    exact (Set.eq_singleton_or_nontrivial hZero).resolve_left hSet
  have hConv : Convex ℝ s := by
    simpa [s] using (convex_integrableExpSet (X := X 0) (μ := P))
  rcases (hConv.nontrivial_iff_nonempty_interior).mp hNontrivial with ⟨τ, hτ⟩
  by_cases hTop : level = ⊤
  · let t : ℝ := τ / 2
    have hHalfInt : t ∈ interior s := by
      -- Proof comment: any strict convex combination of the interior tilt `τ` with `0 ∈ s`
      -- stays inside the interior, so `τ / 2` is a legal derivative point.
      have hHalf :
          (1 / 2 : ℝ) • τ + (1 / 2 : ℝ) • (0 : ℝ) ∈ interior s := by
        exact hConv.combo_interior_self_mem_interior hτ hZero (by norm_num) (by norm_num) (by norm_num)
      simpa [t, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hHalf
    refine ⟨deriv (cgf (X 0) P) t, ?_⟩
    simp [hTop]
  have hLevelRealPos : 0 < level.toReal := by
    exact ENNReal.toReal_pos (ne_of_gt hLevel) hTop
  let σ : ℝ := τ / 2
  have hσInt : σ ∈ interior s := by
    -- Proof comment: first move from the arbitrary interior point `τ` to the smaller interior
    -- point `σ = τ / 2`, which will support the inverse-multiple argument.
    have hHalf :
        (1 / 2 : ℝ) • τ + (1 / 2 : ℝ) • (0 : ℝ) ∈ interior s := by
      exact hConv.combo_interior_self_mem_interior hτ hZero (by norm_num) (by norm_num) (by norm_num)
    simpa [σ, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hHalf
  have hσMem : σ ∈ s := interior_subset hσInt
  have hτMem : τ ∈ s := interior_subset hτ
  have hCgfSigma :
      Tendsto (fun n : ℕ ↦ cgf (X 0) P (σ / (n + 2 : ℝ))) atTop (𝓝 0) :=
    cgf_tendsto_zero_along_inverseMultiples (P := P) (Y := X 0) hσMem
  have hCgfTau :
      Tendsto (fun n : ℕ ↦ cgf (X 0) P (τ / (n + 2 : ℝ))) atTop (𝓝 0) :=
    cgf_tendsto_zero_along_inverseMultiples (P := P) (Y := X 0) hτMem
  have hGapTendsto :
      Tendsto
        (fun n : ℕ ↦ cgf (X 0) P (τ / (n + 2 : ℝ)) - 2 * cgf (X 0) P (σ / (n + 2 : ℝ)))
        atTop (𝓝 0) := by
    -- Proof comment: both cumulant-generating-function evaluations vanish as the tilt tends to
    -- `0`, so the nearby double-gap also vanishes.
    simpa [sub_eq_add_neg] using hCgfTau.sub (hCgfSigma.const_mul 2)
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        cgf (X 0) P (τ / (n + 2 : ℝ)) - 2 * cgf (X 0) P (σ / (n + 2 : ℝ)) < level.toReal := by
    exact hGapTendsto (Iio_mem_nhds hLevelRealPos)
  rcases Filter.eventually_atTop.mp hEventually with ⟨n₀, hn₀⟩
  let t : ℝ := σ / (n₀ + 2 : ℝ)
  have htInt : t ∈ interior s := by
    -- Proof comment: scaling the interior tilt `σ` by the positive factor `(n₀ + 2)⁻¹` keeps the
    -- new tilt inside the interior.
    have ha : 0 < ((n₀ + 2 : ℝ)⁻¹) := by positivity
    have hb : 0 ≤ 1 - (n₀ + 2 : ℝ)⁻¹ := by
      have hge : (1 : ℝ) ≤ n₀ + 2 := by
        have hn₀ge : (0 : ℝ) ≤ n₀ := by exact_mod_cast Nat.zero_le n₀
        nlinarith
      exact sub_nonneg.mpr <| inv_le_one_of_one_le₀ hge
    have hsum : ((n₀ + 2 : ℝ)⁻¹) + (1 - (n₀ + 2 : ℝ)⁻¹) = 1 := by ring
    have hCombo :
        ((n₀ + 2 : ℝ)⁻¹) • σ + (1 - (n₀ + 2 : ℝ)⁻¹) • (0 : ℝ) ∈ interior s := by
      exact hConv.combo_interior_self_mem_interior hσInt hZero ha hb hsum
    simpa [t, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hCombo
  have hDoubleMem : 2 * t ∈ s := by
    -- Proof comment: the doubled tilt is exactly `τ / (n₀ + 2)`, still inside the effective
    -- domain by convexity between `0` and `τ`.
    have hCoeff :
        (n₀ + 2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      ·
        have hge : (1 : ℝ) ≤ n₀ + 2 := by
          have hn₀ge : (0 : ℝ) ≤ n₀ := by exact_mod_cast Nat.zero_le n₀
          nlinarith
        exact inv_le_one_of_one_le₀ hge
    have hScaled :
        (n₀ + 2 : ℝ)⁻¹ • τ ∈ s := by
      simpa [Set.mem_Icc] using hConv.smul_mem_of_zero_mem hZero hτMem hCoeff
    simpa [t, σ, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hScaled
  have hGapBound :
      t * deriv (cgf (X 0) P) t - cgf (X 0) P t ≤
        cgf (X 0) P (2 * t) - 2 * cgf (X 0) P t := by
    exact affineGap_atDeriv_le_cgfDoubleGap_of_mem_interior
      (P := P) (X := X) htInt hDoubleMem
  have hGapLt :
      cgf (X 0) P (2 * t) - 2 * cgf (X 0) P t < level.toReal := by
    -- Proof comment: specialize the vanishing double-gap estimate at the chosen large index `n₀`.
    simpa [t, σ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hn₀ n₀ le_rfl
  let x : ℝ := deriv (cgf (X 0) P) t
  have hRateEq :
      (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal) =
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    -- Proof comment: rewrite the owner rate at the chosen derivative point back to the affine
    -- expression controlled by the double-gap estimate.
    simpa [x] using
      empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior (P := P) (X := X) htInt
  have hAffineNonneg :
      0 ≤ t * x - cgf (X 0) P t := by
    have hNonnegE :
        (0 : EReal) ≤ (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
      calc
        (0 : EReal) ≤
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
              exact_mod_cast
                (show (0 : ENNReal) ≤ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal
                  from bot_le)
        _ = (((t * x - cgf (X 0) P t : ℝ)) : EReal) := hRateEq
    exact_mod_cast hNonnegE
  have hAffineLeLevel :
      t * x - cgf (X 0) P t ≤ level.toReal := by
    exact le_of_lt <| lt_of_le_of_lt hGapBound hGapLt
  have hAffineLeLevelE :
      (((t * x - cgf (X 0) P t : ℝ)) : EReal) ≤ ((level : ENNReal) : EReal) := by
    have hOfRealLe : ENNReal.ofReal (t * x - cgf (X 0) P t) ≤ level := by
      exact (ENNReal.ofReal_le_iff_le_toReal hTop).2 hAffineLeLevel
    have hCast :
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) =
          (((ENNReal.ofReal (t * x - cgf (X 0) P t) : ENNReal) : EReal)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hAffineNonneg]
      rfl
    rw [hCast]
    exact_mod_cast hOfRealLe
  refine ⟨x, ?_⟩
  have hRateLeE :
      ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) ≤
        ((level : ENNReal) : EReal) := by
    exact hRateEq.trans_le hAffineLeLevelE
  exact_mod_cast hRateLeE

/-- Helper for Theorem 23.11: a strict comparison below the negated owner-rate infimum on a
nonempty set yields a point of that set with the same strict inequality. -/
private theorem exists_mem_lt_neg_empiricalMeanOwnerRate_of_lt_neg_sInf
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {s : Set ℝ} (_hs : s.Nonempty) {y : EReal}
    (hy :
      y <
        -sInf
          ((fun x ↦
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' s)) :
    ∃ x ∈ s,
      y <
        -((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
  by_contra hNo
  have hLower :
      -y ≤
        sInf
          ((fun x ↦
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' s) := by
    refine le_sInf ?_
    rintro z ⟨x, hx, rfl⟩
    have hNot :
        ¬ y <
          -((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
      exact fun hlt ↦ hNo ⟨x, hx, hlt⟩
    have hLe :
        -((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) ≤ y :=
      le_of_not_gt hNot
    exact EReal.neg_le_neg_iff.mp (by simpa using hLe)
  have hUpper :
      -sInf
          ((fun x ↦
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' s) ≤
        y := by
    exact EReal.neg_le_neg_iff.mp (by simpa using hLower)
  exact (not_lt_of_ge hUpper hy).elim

/-- Helper for Theorem 23.11: once the exponential-integrability domain is not the singleton
`{0}`, every positive owner-rate threshold is achieved by some interior tilt derivative point. -/
private theorem existsInteriorTilt_ownerRate_le_of_pos_of_nontrivialIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {level : ENNReal} (hLevel : 0 < level) :
    ∃ t, t ∈ interior (integrableExpSet (X 0) P) ∧
      ((((legendreFenchelRateFunction (Λ(X 0; P))
          (deriv (cgf (X 0) P) t)).toENNReal : ENNReal) : EReal)) ≤
        ((level : ENNReal) : EReal) := by
  let s : Set ℝ := integrableExpSet (X 0) P
  have hZero : (0 : ℝ) ∈ s := by
    simp [s, integrableExpSet]
  have hNontrivial : s.Nontrivial := by
    -- Proof comment: the effective domain always contains `0`, so `s ≠ {0}` upgrades to a
    -- genuinely nontrivial convex set with nonempty interior.
    exact (Set.eq_singleton_or_nontrivial hZero).resolve_left hSet
  have hConv : Convex ℝ s := by
    simpa [s] using (convex_integrableExpSet (X := X 0) (μ := P))
  rcases (hConv.nontrivial_iff_nonempty_interior).mp hNontrivial with ⟨τ, hτ⟩
  by_cases hTop : level = ⊤
  · let t : ℝ := τ / 2
    have hHalfInt : t ∈ interior s := by
      -- Proof comment: halving an interior tilt keeps us inside the interior by convexity with
      -- the origin.
      have hHalf :
          (1 / 2 : ℝ) • τ + (1 / 2 : ℝ) • (0 : ℝ) ∈ interior s := by
        exact
          hConv.combo_interior_self_mem_interior hτ hZero
            (by norm_num) (by norm_num) (by norm_num)
      simpa [t, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hHalf
    refine ⟨t, hHalfInt, ?_⟩
    simp [hTop]
  have hLevelRealPos : 0 < level.toReal := by
    exact ENNReal.toReal_pos (ne_of_gt hLevel) hTop
  let σ : ℝ := τ / 2
  have hσInt : σ ∈ interior s := by
    -- Proof comment: move from the arbitrary interior point `τ` to the smaller interior point
    -- `σ = τ / 2`, which supports the inverse-multiple construction.
    have hHalf :
        (1 / 2 : ℝ) • τ + (1 / 2 : ℝ) • (0 : ℝ) ∈ interior s := by
      exact
        hConv.combo_interior_self_mem_interior hτ hZero
          (by norm_num) (by norm_num) (by norm_num)
    simpa [σ, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hHalf
  have hσMem : σ ∈ s := interior_subset hσInt
  have hτMem : τ ∈ s := interior_subset hτ
  have hCgfSigma :
      Tendsto (fun n : ℕ ↦ cgf (X 0) P (σ / (n + 2 : ℝ))) atTop (𝓝 0) :=
    cgf_tendsto_zero_along_inverseMultiples (P := P) (Y := X 0) hσMem
  have hCgfTau :
      Tendsto (fun n : ℕ ↦ cgf (X 0) P (τ / (n + 2 : ℝ))) atTop (𝓝 0) :=
    cgf_tendsto_zero_along_inverseMultiples (P := P) (Y := X 0) hτMem
  have hGapTendsto :
      Tendsto
        (fun n : ℕ ↦ cgf (X 0) P (τ / (n + 2 : ℝ)) - 2 * cgf (X 0) P (σ / (n + 2 : ℝ)))
        atTop (𝓝 0) := by
    -- Proof comment: both cumulant-generating-function evaluations vanish as the tilt tends to
    -- `0`, so the nearby double-gap also vanishes.
    simpa [sub_eq_add_neg] using hCgfTau.sub (hCgfSigma.const_mul 2)
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        cgf (X 0) P (τ / (n + 2 : ℝ)) - 2 * cgf (X 0) P (σ / (n + 2 : ℝ)) < level.toReal := by
    exact hGapTendsto (Iio_mem_nhds hLevelRealPos)
  rcases Filter.eventually_atTop.mp hEventually with ⟨n₀, hn₀⟩
  let t : ℝ := σ / (n₀ + 2 : ℝ)
  have htInt : t ∈ interior s := by
    -- Proof comment: scaling the interior tilt `σ` by the positive factor `(n₀ + 2)⁻¹` keeps the
    -- new tilt inside the interior.
    have ha : 0 < ((n₀ + 2 : ℝ)⁻¹) := by positivity
    have hb : 0 ≤ 1 - (n₀ + 2 : ℝ)⁻¹ := by
      have hge : (1 : ℝ) ≤ n₀ + 2 := by
        have hn₀ge : (0 : ℝ) ≤ n₀ := by exact_mod_cast Nat.zero_le n₀
        nlinarith
      exact sub_nonneg.mpr <| inv_le_one_of_one_le₀ hge
    have hsum : ((n₀ + 2 : ℝ)⁻¹) + (1 - (n₀ + 2 : ℝ)⁻¹) = 1 := by ring
    have hCombo :
        ((n₀ + 2 : ℝ)⁻¹) • σ + (1 - (n₀ + 2 : ℝ)⁻¹) • (0 : ℝ) ∈ interior s := by
      exact hConv.combo_interior_self_mem_interior hσInt hZero ha hb hsum
    simpa [t, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hCombo
  have hDoubleMem : 2 * t ∈ s := by
    -- Proof comment: the doubled tilt is exactly `τ / (n₀ + 2)`, still inside the effective
    -- domain by convexity between `0` and `τ`.
    have hCoeff :
        (n₀ + 2 : ℝ)⁻¹ ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      ·
        have hge : (1 : ℝ) ≤ n₀ + 2 := by
          have hn₀ge : (0 : ℝ) ≤ n₀ := by exact_mod_cast Nat.zero_le n₀
          nlinarith
        exact inv_le_one_of_one_le₀ hge
    have hScaled :
        (n₀ + 2 : ℝ)⁻¹ • τ ∈ s := by
      simpa [Set.mem_Icc] using hConv.smul_mem_of_zero_mem hZero hτMem hCoeff
    simpa [t, σ, s, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hScaled
  let x : ℝ := deriv (cgf (X 0) P) t
  have hGapBound :
      t * x - cgf (X 0) P t ≤
        cgf (X 0) P (2 * t) - 2 * cgf (X 0) P t := by
    exact affineGap_atDeriv_le_cgfDoubleGap_of_mem_interior
      (P := P) (X := X) htInt hDoubleMem
  have hGapLt :
      cgf (X 0) P (2 * t) - 2 * cgf (X 0) P t < level.toReal := by
    -- Proof comment: specialize the vanishing double-gap estimate at the chosen large index `n₀`.
    simpa [t, σ, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hn₀ n₀ le_rfl
  have hRateEq :
      (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal) =
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
    -- Proof comment: rewrite the owner rate at the chosen derivative point back to the affine
    -- expression controlled by the double-gap estimate.
    simpa [x] using
      empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior (P := P) (X := X) htInt
  have hAffineNonneg :
      0 ≤ t * x - cgf (X 0) P t := by
    have hNonnegE :
        (0 : EReal) ≤ (((t * x - cgf (X 0) P t : ℝ)) : EReal) := by
      calc
        (0 : EReal) ≤
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) := by
              exact_mod_cast
                (show (0 : ENNReal) ≤ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal
                  from bot_le)
        _ = (((t * x - cgf (X 0) P t : ℝ)) : EReal) := hRateEq
    exact_mod_cast hNonnegE
  have hAffineLeLevel :
      t * x - cgf (X 0) P t ≤ level.toReal := by
    exact le_of_lt <| lt_of_le_of_lt hGapBound hGapLt
  have hAffineLeLevelE :
      (((t * x - cgf (X 0) P t : ℝ)) : EReal) ≤ ((level : ENNReal) : EReal) := by
    have hOfRealLe : ENNReal.ofReal (t * x - cgf (X 0) P t) ≤ level := by
      exact (ENNReal.ofReal_le_iff_le_toReal hTop).2 hAffineLeLevel
    have hCast :
        (((t * x - cgf (X 0) P t : ℝ)) : EReal) =
          (((ENNReal.ofReal (t * x - cgf (X 0) P t) : ENNReal) : EReal)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hAffineNonneg]
      rfl
    rw [hCast]
    exact_mod_cast hOfRealLe
  refine ⟨t, htInt, ?_⟩
  calc
    ((((legendreFenchelRateFunction (Λ(X 0; P))
        (deriv (cgf (X 0) P) t)).toENNReal : ENNReal) : EReal))
        = (((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal) := by
            simp [x]
    _ = (((t * x - cgf (X 0) P t : ℝ)) : EReal) := hRateEq
    _ ≤ ((level : ENNReal) : EReal) := hAffineLeLevelE

/-- Helper for Theorem 23.11: shrinking the target owner-rate level by a factor of `2` upgrades
the nontrivial-domain derivative witness from `≤ level / 2` to a strict `< level` bound. -/
private theorem existsInteriorTilt_ownerRate_lt_of_pos_of_nontrivialIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {level : ENNReal} (hLevel : 0 < level) :
    ∃ t, t ∈ interior (integrableExpSet (X 0) P) ∧
      ((((legendreFenchelRateFunction (Λ(X 0; P))
          (deriv (cgf (X 0) P) t)).toENNReal : ENNReal) : EReal)) <
        ((level : ENNReal) : EReal) := by
  by_cases hTop : level = ⊤
  · -- Proof comment: at the top threshold every finite owner rate is automatically strictly
    -- below `⊤`, so any existing interior derivative witness suffices.
    subst hTop
    rcases existsInteriorTilt_ownerRate_le_of_pos_of_nontrivialIntegrableExpSet
        (P := P) (X := X) hSet hLevel with ⟨t, ht, hRate⟩
    refine ⟨t, ht, ?_⟩
    have hRateEq :
        ((((legendreFenchelRateFunction (Λ(X 0; P))
            (deriv (cgf (X 0) P) t)).toENNReal : ENNReal) : EReal)) =
          (((t * deriv (cgf (X 0) P) t - cgf (X 0) P t : ℝ)) : EReal) := by
      simpa using
        empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior (P := P) (X := X) ht
    have hNotTop :
        legendreFenchelRateFunction (Λ(X 0; P)) (deriv (cgf (X 0) P) t) ≠ ⊤ := by
      intro hTopRate
      have : (⊤ : EReal) = (((t * deriv (cgf (X 0) P) t - cgf (X 0) P t : ℝ)) : EReal) := by
        simpa [hTopRate] using hRateEq
      exact (EReal.coe_ne_top _ ) this.symm
    have hFin :
        (legendreFenchelRateFunction (Λ(X 0; P)) (deriv (cgf (X 0) P) t)).toENNReal <
          (⊤ : ENNReal) := by
      exact lt_top_iff_ne_top.mpr <| by
        simpa [EReal.toENNReal_eq_top_iff, hNotTop]
    exact_mod_cast hFin
  · let halfLevel : ENNReal := level / 2
    have hHalfLevel : 0 < halfLevel := by
      dsimp [halfLevel]
      exact ENNReal.half_pos hLevel.ne'
    rcases existsInteriorTilt_ownerRate_le_of_pos_of_nontrivialIntegrableExpSet
        (P := P) (X := X) hSet hHalfLevel with ⟨t, ht, hRate⟩
    have hHalfLt :
        ((halfLevel : ENNReal) : EReal) < ((level : ENNReal) : EReal) := by
      -- Proof comment: the strict inequality is paid entirely on the ENNReal threshold, so the
      -- derivative witness from the halved level also works for the original level.
      exact_mod_cast ENNReal.half_lt_self hLevel.ne' hTop
    exact ⟨t, ht, hRate.trans_lt hHalfLt⟩

/-- Helper for Theorem 23.11: a point strictly between two points of the same owner-rate sublevel
lies in the interior of that sublevel. -/
private theorem mem_interior_ownerRateSublevel_of_mem_of_mem_of_between
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {a : ENNReal} {x y z : ℝ}
    (hx : (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal ≤ a)
    (hy : (legendreFenchelRateFunction (Λ(X 0; P)) y).toENNReal ≤ a)
    (hxy : x < y) (hz : z ∈ Set.Ioo x y) :
    z ∈ interior {u : ℝ | (legendreFenchelRateFunction (Λ(X 0; P)) u).toENNReal ≤ a} := by
  let K : Set ℝ := {u : ℝ | (legendreFenchelRateFunction (Λ(X 0; P)) u).toENNReal ≤ a}
  have hKConv : Convex ℝ K := by
    -- Proof comment: the owner-rate sublevel inherits convexity from the Legendre-Fenchel rate.
    simpa [K] using
      (empiricalMeanOwnerRateSublevel_shape (P := P) (X := X) a).2.1
  have hSubset : Set.Ioo x y ⊆ K := by
    -- Proof comment: on the real line, convexity says every point between two sublevel points
    -- stays in the same sublevel.
    intro u hu
    exact hKConv.ordConnected.out hx hy ⟨hu.1.le, hu.2.le⟩
  -- Proof comment: the whole strict interval `(x, y)` is an open neighborhood of `z` contained in
  -- the owner-rate sublevel, so `z` is interior.
  refine mem_interior_iff_mem_nhds.2 ?_
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hz) hSubset

/-- Helper for Theorem 23.11: in the nonpositive comparison regime, one can choose a positive
owner-rate threshold strictly between `-y` and the owner-rate infimum on `C`. -/
private theorem exists_positive_ownerRate_threshold_between_lt_neg_sInf
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {C : Set ℝ} {y : EReal}
    (hy :
      y >
        -sInf
          ((fun x ↦
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' C))
    (hyNonpos : y ≤ 0) :
    ∃ a : ENNReal,
      0 < a ∧
        ((a : ENNReal) : EReal) <
          sInf
            ((fun x ↦
              ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' C) ∧
        -(((a : ENNReal) : EReal)) < y := by
  have hGap :
      -y <
        sInf
          ((fun x ↦
            ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal))) '' C) := by
    -- Proof comment: negating the strict comparison exposes an honest open interval between
    -- `-y` and the owner-rate infimum.
    simpa using EReal.neg_strictAnti hy
  rcases EReal.lt_iff_exists_real_btwn.mp hGap with ⟨a, hLower, hUpper⟩
  have haPosE : (0 : EReal) < (a : EReal) := by
    exact lt_of_le_of_lt (EReal.neg_nonneg.2 hyNonpos) hLower
  have haPos : 0 < a := by
    simpa using haPosE
  have hcoea : (((ENNReal.ofReal a : ENNReal) : EReal)) = (a : EReal) := by
    rw [ENNReal.ofReal_eq_coe_nnreal haPos.le]
    rfl
  have hNeg : -((a : EReal)) < y := by
    -- Proof comment: the chosen positive threshold sits strictly above `-y`, so its negative
    -- remains strictly below the original comparison value `y`.
    simpa using (EReal.neg_lt_neg_iff.mpr hLower)
  refine ⟨ENNReal.ofReal a, ENNReal.ofReal_pos.mpr haPos, ?_, ?_⟩
  · simpa [hcoea] using hUpper
  · simpa [hcoea] using hNeg

/-- Helper for Theorem 23.11: if the complement of a measurable set carries less than half the
mass under a probability measure, then the set itself carries at least half the mass. -/
private theorem one_half_le_measure_of_compl_lt_half
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : Set ℝ} (hs : MeasurableSet s)
    (hcompl : μ sᶜ < (1 / 2 : ENNReal)) :
    (1 / 2 : ENNReal) ≤ μ s := by
  have hsum : μ s + μ sᶜ = 1 := by
    -- Proof comment: a probability measure splits between a measurable set and its complement.
    simpa using prob_add_prob_compl (μ := μ) hs
  have hsum_real :
      (μ s).toReal + (μ sᶜ).toReal = 1 := by
    simpa [ENNReal.toReal_add, measure_ne_top μ _] using congrArg ENNReal.toReal hsum
  have hcompl_real : (μ sᶜ).toReal < (1 / 2 : ℝ) := by
    have hcompl' : μ sᶜ < ENNReal.ofReal (1 / 2 : ℝ) := by
      simpa using hcompl
    simpa using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).2 hcompl'
  have hset_real : (1 / 2 : ℝ) ≤ (μ s).toReal := by
    linarith
  have hset : ENNReal.ofReal (1 / 2 : ℝ) ≤ μ s := by
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ _)).2 hset_real
  simpa using hset

/-- Helper for Theorem 23.11: the correction term `(n + 1)⁻¹ log b` eventually dominates any
strictly negative comparison value when `b` is a fixed positive finite constant. -/
private theorem eventually_lt_cramerLogConstCorrection
    {b : ENNReal} (hb0 : b ≠ 0) (hbTop : b ≠ ⊤) {y : EReal} (hy : y < 0) :
    ∀ᶠ n : ℕ in atTop,
      y < (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log b) := by
  have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hInv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ)) := by
    -- Proof comment: the Cramér speed `(n + 1)⁻¹` vanishes along `atTop`.
    exact tendsto_inv_atTop_zero.comp hNat
  have hInvEReal :
      Tendsto (fun n : ℕ ↦ ((((n : ℝ) + 1)⁻¹ : ℝ) : EReal)) atTop (nhds (0 : EReal)) := by
    simpa using EReal.tendsto_coe.2 hInv
  have hlog_bot : ENNReal.log b ≠ ⊥ := by
    intro h
    exact hb0 (ENNReal.log_eq_bot_iff.mp h)
  have hlog_top : ENNReal.log b ≠ ⊤ := by
    intro h
    exact hbTop (ENNReal.log_eq_top_iff.mp h)
  have hCorr :
      Tendsto
        (fun n : ℕ ↦ ((((n : ℝ) + 1)⁻¹ : ℝ) : EReal) * ENNReal.log b)
        atTop (nhds (0 : EReal)) := by
    -- Proof comment: multiply the vanishing speed by the fixed finite logarithmic constant.
    simpa using
      (EReal.Tendsto.mul_const (b := ENNReal.log b) hInvEReal
        (Or.inr hlog_bot) (Or.inr hlog_top))
  simpa [Nat.cast_add] using hCorr (Ioi_mem_nhds hy)

/-- Helper for Theorem 23.11: an eventual positive constant lower bound on the event mass already
forces a nonnegative logarithmic `liminf` at the Cramér speed `(n + 1)⁻¹`. -/
private theorem empiricalMeanLaw_liminf_nonneg_of_eventually_const_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s : Set ℝ} {b : ENNReal}
    (hb0 : b ≠ 0) (hbTop : b ≠ ⊤)
    (hMass :
      ∀ᶠ n : ℕ in atTop,
        b ≤
          ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) s)) :
    0 ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
            have hn : 0 < (n + 1 : ℝ) := by
              positivity
            simpa using inv_pos.mpr hn⟩)
          s)
        atTop := by
  rw [Filter.le_liminf_iff']
  intro y hy
  by_cases hyBot : y = ⊥
  · -- Proof comment: the bottom comparison value lies below every scaled logarithmic mass.
    exact Filter.Eventually.of_forall fun n : ℕ ↦ by simp [hyBot]
  · have hyNeg : y < 0 := by
      simpa [hyBot] using hy
    have hCorr := eventually_lt_cramerLogConstCorrection hb0 hbTop hyNeg
    have hCompare :
        ∀ᶠ n : ℕ in atTop,
          (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log b) ≤
            scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
                have hn : 0 < (n + 1 : ℝ) := by
                  positivity
                simpa using inv_pos.mpr hn⟩)
              s n := by
      filter_upwards [hMass] with n hn
      have hn_pos : 0 < (n + 1 : ℝ) := by
        positivity
      have hε_nonneg : (0 : EReal) ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal)) := by
        exact_mod_cast le_of_lt (inv_pos.mpr hn_pos)
      calc
        (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log b)
            ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) *
                ENNReal.log ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) s)) := by
                  exact mul_le_mul_of_nonneg_left (ENNReal.log_le_log hn) hε_nonneg
        _ = scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
                have hn : 0 < (n + 1 : ℝ) := by
                  positivity
                simpa using inv_pos.mpr hn⟩)
              s n := by
                simp [scaledLogMassAlong_def]
    filter_upwards [hCorr, hCompare] with n hyn hcompare
    exact hyn.le.trans hcompare

/-- Helper for Theorem 23.11: the special case `b = 1 / 2` is a convenient interface for
eventual half-mass lower bounds. -/
private theorem empiricalMeanLaw_liminf_nonneg_of_eventually_one_half_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s : Set ℝ}
    (hHalf :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ENNReal) ≤
          ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) s)) :
    0 ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
            have hn : 0 < (n + 1 : ℝ) := by
              positivity
            simpa using inv_pos.mpr hn⟩)
          s)
        atTop := by
  exact empiricalMeanLaw_liminf_nonneg_of_eventually_const_le
    (P := P) (X := X) hX_iid (b := (1 / 2 : ENNReal)) (by norm_num) (by simp) hHalf

/-- Helper for Theorem 23.11: it is enough to show that the complement event eventually has mass
strictly below `1 / 2` in order to get the singleton-branch lower bound `liminf ≥ 0`. -/
private theorem empiricalMeanLaw_liminf_nonneg_of_eventually_compl_lt_half
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s : Set ℝ} (hs : MeasurableSet s)
    (hCompl :
      ∀ᶠ n : ℕ in atTop,
        ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) sᶜ) <
          (1 / 2 : ENNReal)) :
    0 ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
            have hn : 0 < (n + 1 : ℝ) := by
              positivity
            simpa using inv_pos.mpr hn⟩)
          s)
        atTop := by
  apply empiricalMeanLaw_liminf_nonneg_of_eventually_one_half_le (P := P) (X := X) hX_iid
  filter_upwards [hCompl] with n hn
  exact one_half_le_measure_of_compl_lt_half
    ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)) hs hn

/-- Helper for Theorem 23.11: eventual lower bounds of size `exp (-ε (n + 1))` for every
`ε > 0` force a nonnegative scaled-logarithmic `liminf` at the Cramér speed. -/
private theorem scaledLogMassAlong_liminf_nonneg_of_eventually_expNegLinear_le
    {μ : ℕ → Measure ℝ} {s : Set ℝ}
    (hMass :
      ∀ ε > 0,
        ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (Real.exp (-ε * (n + 1 : ℝ))) ≤ μ n s) :
    0 ≤
      Filter.liminf
        (scaledLogMassAlong
          μ
          (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
            have hn : 0 < (n + 1 : ℝ) := by
              positivity
            simpa using inv_pos.mpr hn⟩)
          s)
        atTop := by
  rw [Filter.le_liminf_iff']
  intro y hy
  by_cases hyBot : y = ⊥
  · -- Proof comment: the bottom comparison value lies below every scaled logarithmic mass.
    exact Filter.Eventually.of_forall fun n ↦ by simp [hyBot]
  · have hyNeg : y < 0 := by
      simpa [hyBot] using hy
    rcases EReal.lt_iff_exists_real_btwn.mp hyNeg with ⟨z, hyz, hz0⟩
    let ε : ℝ := -z
    have hε : 0 < ε := by
      have hz0' : z < 0 := by
        exact_mod_cast hz0
      dsimp [ε]
      linarith
    filter_upwards [hMass ε hε] with n hn
    have hLog :
        (((-ε * (n + 1 : ℝ) : ℝ)) : EReal) ≤ ENNReal.log (μ n s) := by
      -- Proof comment: take logarithms of the assumed exponential lower bound at index `n`.
      have hLogRaw := ENNReal.log_monotone hn
      rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp] at hLogRaw
      exact hLogRaw
    have hεNonneg : (0 : EReal) ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal)) := by
      have hn : 0 < (n + 1 : ℝ) := by
        positivity
      exact_mod_cast le_of_lt (inv_pos.mpr hn)
    have hScaled :
        (((-ε : ℝ)) : EReal) ≤
          scaledLogMassAlong
            μ
            (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
              have hn : 0 < (n + 1 : ℝ) := by
                positivity
              simpa using inv_pos.mpr hn⟩)
            s n := by
      -- Proof comment: multiply the logarithmic bound by `(n + 1)⁻¹` and collapse the exact
      -- normalization to `-ε`.
      calc
        (((-ε : ℝ)) : EReal) =
            (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * (((-ε * (n + 1 : ℝ) : ℝ)) : EReal)) := by
              have hAlg : ((n + 1 : ℝ)⁻¹) * (-ε * (n + 1 : ℝ)) = -ε := by
                have hn' : (n + 1 : ℝ) ≠ 0 := by positivity
                field_simp [hn']
              exact_mod_cast hAlg.symm
        _ ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (μ n s)) := by
              exact mul_le_mul_of_nonneg_left hLog hεNonneg
        _ =
            scaledLogMassAlong
              μ
              (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
                have hn : 0 < (n + 1 : ℝ) := by
                  positivity
                simpa using inv_pos.mpr hn⟩)
              s n := by
              simp [scaledLogMassAlong_def]
    have hyε : y < (((-ε : ℝ)) : EReal) := by
      -- Proof comment: choose `ε` so that the target comparison value still lies strictly below
      -- the deterministic rate `-ε`.
      have hzEq : ((z : ℝ) : EReal) = (((-ε : ℝ)) : EReal) := by
        have hzEqReal : z = -ε := by
          dsimp [ε]
          ring
        exact_mod_cast hzEqReal
      exact hyz.trans_eq hzEq
    exact hyε.le.trans hScaled

/-- Helper for Theorem 23.11: the owner Cramér speed at index `n` is `(n + 1)⁻¹ > 0`. -/
private theorem cramerSpeed_pos (n : ℕ) : 0 < (n + 1 : ℝ)⁻¹ := by
  have hn : 0 < (n + 1 : ℝ) := by
    positivity
  simpa using inv_pos.mpr hn

/-- Helper for Theorem 23.11: the owner speed family used for empirical means. -/
private noncomputable def cramerSpeed : ℕ → PositiveParameter :=
  fun n ↦ ⟨((n + 1 : ℝ)⁻¹), cramerSpeed_pos n⟩

/-- Helper for Theorem 23.11: the deterministic union penalty
`(n + 1)⁻¹ log 2` vanishes along the Cramér speed. -/
private theorem scaledLogTwoCorrection_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ ↦ ((((n + 1 : ℝ)⁻¹ * Real.log 2 : ℝ)) : EReal))
      atTop (nhds (0 : EReal)) := by
  have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hInv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ)) := by
    -- Proof comment: the Cramér speed is exactly the reciprocal of a sequence diverging to
    -- infinity.
    exact tendsto_inv_atTop_zero.comp hNat
  have hBase : Tendsto (fun x : ℝ ↦ x * Real.log 2) (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    -- Proof comment: multiplication by the constant `log 2` is continuous at `0`.
    have hCont : ContinuousAt (fun x : ℝ ↦ x * Real.log 2) (0 : ℝ) := by
      simpa using (continuousAt_id.mul continuousAt_const)
    simpa using hCont.tendsto
  have hReal :
      Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ * Real.log 2) atTop (nhds (0 : ℝ)) := by
    exact hBase.comp hInv
  simpa [Nat.cast_add] using EReal.tendsto_coe.2 hReal

/-- Helper for Theorem 23.11: after paying the vanishing `log 2` correction, the `limsup` of a
union is bounded by the maximum of the two branch `limsup`s. -/
private theorem empiricalMeanLaw_union_limsup_le_max
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) (s t : Set ℝ) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          (s ∪ t))
        atTop ≤
      max
        (Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            s)
          atTop)
        (Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            t)
          atTop) := by
  let μn : ℕ → Measure ℝ :=
    fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  have hUnionPointwise :
      ∀ᶠ n : ℕ in atTop,
        scaledLogMassAlong μn cramerSpeed (s ∪ t) n ≤
          ((((n + 1 : ℝ)⁻¹ * Real.log 2 : ℝ) : EReal)) +
            max (scaledLogMassAlong μn cramerSpeed s n)
              (scaledLogMassAlong μn cramerSpeed t n) := by
    exact Filter.Eventually.of_forall fun n ↦ by
      have hlogTwo : ENNReal.log (2 : ENNReal) = ((Real.log 2 : ℝ) : EReal) := by
        have hTwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
          norm_num
        rw [hTwo]
        simpa using (ENNReal.log_ofReal_of_pos (show 0 < (2 : ℝ) by norm_num))
      -- Proof comment: the pointwise union estimate separates the deterministic `log 2`
      -- correction from the larger of the two branch exponents.
      simpa [μn, cramerSpeed, hlogTwo, EReal.coe_mul] using
        scaledLogMassAlong_union_le_logTwo_add_max
          (μ := μn) (ε := cramerSpeed) s t n
  have hMain :
    Filter.limsup (scaledLogMassAlong μn cramerSpeed (s ∪ t)) atTop ≤
      max
        (Filter.limsup (scaledLogMassAlong μn cramerSpeed s) atTop)
        (Filter.limsup (scaledLogMassAlong μn cramerSpeed t) atTop) := by
    calc
      Filter.limsup (scaledLogMassAlong μn cramerSpeed (s ∪ t)) atTop
        ≤ Filter.limsup
            (fun n : ℕ ↦
              ((((n + 1 : ℝ)⁻¹ * Real.log 2 : ℝ) : EReal)) +
                max (scaledLogMassAlong μn cramerSpeed s n)
                  (scaledLogMassAlong μn cramerSpeed t n))
            atTop := by
              exact Filter.limsup_le_limsup hUnionPointwise
      _ =
          Filter.limsup
            (fun n : ℕ ↦
              max (scaledLogMassAlong μn cramerSpeed s n)
                (scaledLogMassAlong μn cramerSpeed t n))
            atTop := by
              -- Proof comment: the additive `log 2` penalty tends to `0`, so it disappears at the
              -- `limsup` level.
              simpa [add_comm] using
                ENNReal.limsup_add_tendsto_zero_right
                  (f := fun n : ℕ ↦
                    max (scaledLogMassAlong μn cramerSpeed s n)
                      (scaledLogMassAlong μn cramerSpeed t n))
                  (g := fun n : ℕ ↦ ((((n + 1 : ℝ)⁻¹ * Real.log 2 : ℝ) : EReal)))
                  scaledLogTwoCorrection_tendsto_zero
      _ =
          max
            (Filter.limsup (scaledLogMassAlong μn cramerSpeed s) atTop)
            (Filter.limsup (scaledLogMassAlong μn cramerSpeed t) atTop) := by
              -- Proof comment: `limsup` turns the pointwise maximum into the maximum of the two
              -- branch `limsup`s.
              rw [limsup_max
                (f := atTop)
                (u := scaledLogMassAlong μn cramerSpeed s)
                (v := scaledLogMassAlong μn cramerSpeed t)]
  simpa [μn] using hMain

/-- Helper for Theorem 23.11: once a set is contained in a two-piece cover, its `limsup` is
controlled by the maximum of the two covering `limsup`s. -/
private theorem empiricalMeanLaw_limsup_le_of_subset_union
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s t u : Set ℝ} (hsub : s ⊆ t ∪ u) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          s)
        atTop ≤
      max
        (Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            t)
          atTop)
        (Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            u)
          atTop) := by
  let μn : ℕ → Measure ℝ :=
    fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  have hPointwise :
      ∀ᶠ n : ℕ in atTop,
        scaledLogMassAlong μn cramerSpeed s n ≤
          scaledLogMassAlong μn cramerSpeed (t ∪ u) n := by
    exact Filter.Eventually.of_forall fun n ↦
      scaledLogMassAlong_mono_of_subset (μ := μn) (ε := cramerSpeed) hsub n
  calc
    Filter.limsup (scaledLogMassAlong μn cramerSpeed s) atTop
      ≤ Filter.limsup (scaledLogMassAlong μn cramerSpeed (t ∪ u)) atTop := by
          exact Filter.limsup_le_limsup hPointwise
    _ ≤
        max
          (Filter.limsup (scaledLogMassAlong μn cramerSpeed t) atTop)
          (Filter.limsup (scaledLogMassAlong μn cramerSpeed u) atTop) := by
            -- Proof comment: after monotonicity reduces to the cover, the union helper takes over.
            simpa [μn] using
              empiricalMeanLaw_union_limsup_le_max (P := P) (X := X) hX_iid t u

/-- Helper for Theorem 23.11: once both pieces of a two-set cover have `limsup` strictly below
`y`, the covered set has `limsup` strictly below `y` as well. -/
private theorem empiricalMeanLaw_limsup_lt_of_subset_union
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s t u : Set ℝ} (hsub : s ⊆ t ∪ u) {y : EReal}
    (ht :
      Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            t)
          atTop < y)
    (hu :
      Filter.limsup
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            u)
          atTop < y) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          s)
        atTop < y := by
  -- Proof comment: combine the existing monotone-union `limsup ≤ max` estimate with the fact
  -- that the maximum of two strict upper bounds is still strictly below `y`.
  refine (empiricalMeanLaw_limsup_le_of_subset_union (P := P) (X := X) hX_iid hsub).trans_lt ?_
  simpa [max_lt_iff] using And.intro ht hu

/-- Helper for Theorem 23.11: the owner rate function is the Legendre-Fenchel transform of the
one-letter extended log-moment generating function. -/
private noncomputable def empiricalMeanOwnerRate
    (P : Measure Ω) (X : ℕ → Ω → ℝ) : ℝ → ENNReal :=
  fun x ↦ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal

/-- Helper for Theorem 23.11: the owner scaled logarithmic mass of an arbitrary set rewrites to
the chapter's `ℕ+`-indexed normalized-partial-sum logarithmic mass. -/
private theorem ownerScaledLogMass_eq_normalizedLogMass
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (s : Set ℝ) :
    scaledLogMassAlong
        (fun n ↦ (empiricalMeanLaw X P hXae n : Measure ℝ))
        cramerSpeed
        s =
      (fun n : ℕ ↦
        ENNReal.log ((normalizedPartialSumLaw X P (Nat.succPNat n)) s) /
          ((Nat.succPNat n : ℕ+) : EReal)) := by
  funext n
  -- Proof comment: first identify the owner law with the chapter's `n + 1`st normalized law, then
  -- rewrite the speed factor `((n + 1) : ℝ)⁻¹` as division by `Nat.succPNat n`.
  rw [scaledLogMassAlong_def,
    empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw (P := P) (X := X) hXae n]
  simp [cramerSpeed, Nat.succPNat_coe, div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm,
    mul_assoc]

/-- Helper for Theorem 23.11: at a fixed tilt in the effective domain, the cumulant-generating
function of the `0`-based partial sum over the first `n + 1` IID coordinates is `(n + 1)` times
the one-letter cumulant-generating function. -/
private theorem zeroBasedPartialSum_cgf_eq_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ integrableExpSet (X 0) P) (n : ℕ) :
    cgf (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)) P t =
      (n + 1 : ℝ) * cgf (X 0) P t := by
  have hXae : ∀ i, AEMeasurable (X i) P := iidAEMeasurable P X hX_iid
  have hSumFn :
      (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)) =
        ∑ i ∈ Finset.range (n + 1), X i := by
    funext ω
    simp
  have hInt0 : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
    integrable_of_mem_integrableExpSet ht
  have hInt :
      ∀ i ∈ Finset.range (n + 1), Integrable (fun ω ↦ Real.exp (t * X i ω)) P := by
    intro i hi
    have hIdentExp :
        IdentDistrib
          (fun ω ↦ Real.exp (t * X i ω))
          (fun ω ↦ Real.exp (t * X 0 ω)) P P := by
      simpa using (hX_iid.identDistrib i 0).comp ((measurable_const_mul t).exp)
    exact hIdentExp.integrable_iff.2 hInt0
  calc
    cgf (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)) P t
        = cgf (∑ i ∈ Finset.range (n + 1), X i) P t := by
            rw [hSumFn]
    _ = ∑ i ∈ Finset.range (n + 1), cgf (X i) P t := by
          exact hX_iid.iIndepFun.cgf_sum₀ hXae hInt
    _ = ∑ _i ∈ Finset.range (n + 1), cgf (X 0) P t := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp [cgf, mgf_congr_of_identDistrib (X := X i) (X' := X 0)
            (hident := hX_iid.identDistrib i 0) t]
    _ = (n + 1 : ℝ) * cgf (X 0) P t := by
          simp [nsmul_eq_mul, mul_comm]

/-- Helper for Theorem 23.11: evaluating the cumulant-generating function of the empirical-mean
law at slope `(n + 1) * t` reduces to the `0`-based partial-sum cgf at slope `t`. -/
private theorem empiricalMeanLaw_cgf_eq_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ integrableExpSet (X 0) P) (n : ℕ) :
    cgf id
        (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
        (((n + 1 : ℝ) * t)) =
      (n + 1 : ℝ) * cgf (X 0) P t := by
  let S : Ω → ℝ := fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)
  let Y : Ω → ℝ := fun ω ↦ S ω / (n + 1 : ℝ)
  have hYae : AEMeasurable Y P := by
    -- Proof comment: the empirical mean is the measurable average of the first `n + 1`
    -- coordinates.
    simpa [Y, S] using
      empiricalMean_aemeasurable P X (iidAEMeasurable P X hX_iid) n
  have hνmap :
      (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) = Measure.map Y P := by
    -- Proof comment: rewrite the owner empirical-mean law as the pushforward of `P` by the
    -- zero-based average.
    simpa [Y, S] using
      (empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
        (P := P) (X := X) (iidAEMeasurable P X hX_iid) n).trans
        (normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage (P := P) (X := X) n)
  have hMgfMap :
      mgf id
          (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
          (((n + 1 : ℝ) * t)) =
        mgf Y P (((n + 1 : ℝ) * t)) := by
    rw [hνmap]
    simpa using
      congrFun
        (ProbabilityTheory.mgf_id_map (μ := P) (X := Y) hYae)
        (((n + 1 : ℝ) * t))
  have hMgfAverage :
      mgf Y P (((n + 1 : ℝ) * t)) = mgf S P t := by
    -- Proof comment: the tilt `(n + 1) * t` exactly cancels the averaging denominator.
    rw [mgf, mgf]
    refine integral_congr_ae ?_
    filter_upwards with ω
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    dsimp [Y, S]
    field_simp [hn]
  calc
    cgf id
        (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
        (((n + 1 : ℝ) * t))
      = cgf Y P (((n + 1 : ℝ) * t)) := by
          exact congrArg Real.log hMgfMap
    _ = cgf S P t := by
          exact congrArg Real.log hMgfAverage
    _ = (n + 1 : ℝ) * cgf (X 0) P t := by
          simpa [S] using zeroBasedPartialSum_cgf_eq_mul (P := P) (X := X) hX_iid ht n

/-- Helper for Theorem 23.11: if `t` is in the one-letter exponential-integrability domain, then
the `n + 1`st empirical-mean law has a finite exponential moment at slope `(n + 1) * t`. -/
private theorem empiricalMeanLaw_integrable_exp_mul
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ integrableExpSet (X 0) P) (n : ℕ) :
    Integrable
      (fun z : ℝ ↦ Real.exp ((((n + 1 : ℝ) * t) * z)))
      (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) := by
  let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  let S : Ω → ℝ := fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)
  let Y : Ω → ℝ := fun ω ↦ S ω / (n + 1 : ℝ)
  have hXae : ∀ i, AEMeasurable (X i) P := iidAEMeasurable P X hX_iid
  have hYae : AEMeasurable Y P := by
    -- Proof comment: the empirical mean is the measurable average of the first `n + 1`
    -- coordinates.
    simpa [Y, S] using empiricalMean_aemeasurable P X hXae n
  have hνmap : ν = Measure.map Y P := by
    -- Proof comment: rewrite the empirical-mean law as the pushforward of `P` by the zero-based
    -- empirical mean so the exponential integrability can be checked upstairs on `Ω`.
    simpa [ν, Y, S] using
      (empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
        (P := P) (X := X) hXae n).trans
        (normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage (P := P) (X := X) n)
  have hInt0 : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
    integrable_of_mem_integrableExpSet ht
  have hInt :
      ∀ i ∈ Finset.range (n + 1), Integrable (fun ω ↦ Real.exp (t * X i ω)) P := by
    intro i hi
    have hIdentExp :
        IdentDistrib
          (fun ω ↦ Real.exp (t * X i ω))
          (fun ω ↦ Real.exp (t * X 0 ω)) P P := by
      simpa using (hX_iid.identDistrib i 0).comp ((measurable_const_mul t).exp)
    exact hIdentExp.integrable_iff.2 hInt0
  have hMgfPos : 0 < mgf S P t := by
    -- Proof comment: the IID factorization turns the partial-sum mgf into a finite product of
    -- positive one-letter mgfs.
    rw [show S = ∑ i ∈ Finset.range (n + 1), X i by
      funext ω
      simp [S]]
    rw [hX_iid.iIndepFun.mgf_sum₀ hXae (Finset.range (n + 1))]
    refine Finset.prod_pos ?_
    intro i hi
    exact mgf_pos' (IsProbabilityMeasure.ne_zero P) (hInt i hi)
  have hSumInt : Integrable (fun ω ↦ Real.exp (t * S ω)) P := by
    -- Proof comment: a positive mgf value rules out the `mgf_undef` branch, so the partial-sum
    -- exponential is integrable.
    by_contra hNotInt
    exact hMgfPos.ne' (mgf_undef hNotInt)
  change Integrable
      (fun z : ℝ ↦ Real.exp ((((n + 1 : ℝ) * t) * z)))
      ν
  rw [hνmap]
  have hMeas :
      AEStronglyMeasurable (fun z : ℝ ↦ Real.exp ((((n + 1 : ℝ) * t) * z)))
        (Measure.map Y P) := by
    exact ((measurable_const_mul (((n + 1 : ℝ) * t))).exp.aestronglyMeasurable)
  refine (integrable_map_measure hMeas hYae).2 ?_
  -- Proof comment: the empirical-mean tilt collapses to the original partial-sum tilt after the
  -- averaging denominator cancels.
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hCompose :
      (fun ω ↦ Real.exp ((((n + 1 : ℝ) * t) * Y ω))) =
        (fun ω ↦ Real.exp (t * S ω)) := by
    funext ω
    have hArg :
        (((n + 1 : ℝ) * t) * (S ω / (n + 1 : ℝ))) = t * S ω := by
      field_simp [hn]
    simpa [Y] using congrArg Real.exp hArg
  change Integrable (fun ω ↦ Real.exp ((((n + 1 : ℝ) * t) * Y ω))) P
  exact hCompose.symm ▸ hSumInt

/-- Helper for Theorem 23.11: on a centered interval, the finite-index tilted exponent is bounded
by the affine cost at the center plus the deterministic `|t| * δ` error. -/
private theorem empiricalMeanLaw_centeredInterval_exponent_le_affineError
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {x t δ z : ℝ}
    (ht : t ∈ integrableExpSet (X 0) P) {n : ℕ}
    (hz : z ∈ Set.Ioo (x - δ) (x + δ)) :
    (((n + 1 : ℝ) * t) * z -
        cgf id
          (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
          (((n + 1 : ℝ) * t))) ≤
      (n + 1 : ℝ) * (t * x - cgf (X 0) P t + |t| * δ) := by
  have hzAbs : |z - x| < δ := by
    rw [abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  have hMulAbs : |t * (z - x)| ≤ |t| * δ := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hzAbs.le (abs_nonneg t)
  have hMulLe : t * (z - x) ≤ |t| * δ := by
    exact le_trans (le_abs_self _) hMulAbs
  have hAffine :
      t * z - cgf (X 0) P t ≤ t * x - cgf (X 0) P t + |t| * δ := by
    -- Proof comment: the interval membership controls the deviation `z - x`, so the affine tilt
    -- differs from its center value by at most `|t| * δ`.
    have hSplit : t * z = t * x + t * (z - x) := by ring
    rw [hSplit]
    linarith
  have hScale :
      (n + 1 : ℝ) * (t * z - cgf (X 0) P t) ≤
        (n + 1 : ℝ) * (t * x - cgf (X 0) P t + |t| * δ) := by
    have hn : 0 ≤ (n + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hAffine hn
  -- Proof comment: after evaluating the empirical-mean cgf at slope `(n + 1) * t`, the whole
  -- exponent is just the scaled affine term from the previous line.
  rw [empiricalMeanLaw_cgf_eq_mul (P := P) (X := X) hX_iid ht n]
  calc
    (((n + 1 : ℝ) * t) * z - (n + 1 : ℝ) * cgf (X 0) P t)
      = (n + 1 : ℝ) * (t * z - cgf (X 0) P t) := by ring
    _ ≤ (n + 1 : ℝ) * (t * x - cgf (X 0) P t + |t| * δ) := hScale

/-- Helper for Theorem 23.11: a half-mass lower bound under the empirical-mean tilted law yields
the fixed-index centered-interval lower bound after paying the deterministic Cramér correction. -/
private theorem empiricalMeanLaw_scaledTilt_mem_interior
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P)) (n : ℕ) :
    ((n + 1 : ℝ) * t) ∈
      interior
        (integrableExpSet id
          (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)) := by
  -- Proof comment: the one-letter interior domain is open, and the empirical-mean law inherits
  -- exponential integrability at every nearby scaled tilt by the fixed-index transport lemma.
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  let T : Set ℝ := ((fun s : ℝ ↦ ((n + 1 : ℝ) * s)) '' interior (integrableExpSet (X 0) P))
  have hTopen : IsOpen T := by
    simpa [T] using
      (Homeomorph.mulLeft₀ (n + 1 : ℝ) hn).isOpenMap _ isOpen_interior
  have hTmem : ((n + 1 : ℝ) * t) ∈ T := by
    exact ⟨t, ht, rfl⟩
  have hTsubset :
      T ⊆
        integrableExpSet id
          (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ) := by
    intro y hy
    rcases hy with ⟨s, hs, rfl⟩
    exact empiricalMeanLaw_integrable_exp_mul
      (P := P) (X := X) hX_iid (interior_subset hs) n
  exact mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (hTopen.mem_nhds hTmem) hTsubset

/-- Helper for Theorem 23.11: under the empirical-mean tilt at slope `(n + 1) * t`, the tilted
law is centered at the one-letter derivative `deriv (cgf (X 0) P) t`. -/
private theorem empiricalMeanLaw_tiltedMean_eq_derivCgf
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P)) (n : ℕ) :
    let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
    (ν.tilted (fun z ↦ ((n + 1 : ℝ) * t * z)))[id] = deriv (cgf (X 0) P) t := by
  let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  have hScaledMem :
      ((n + 1 : ℝ) * t) ∈ interior (integrableExpSet id ν) := by
    simpa [ν] using
      empiricalMeanLaw_scaledTilt_mem_interior (P := P) (X := X) hX_iid ht n
  have hMoment :
      (ν.tilted (fun z ↦ ((n + 1 : ℝ) * t * z)))[id] =
        deriv (cgf id ν) (((n + 1 : ℝ) * t)) := by
    -- Proof comment: the tilted first moment is the derivative of the empirical-mean cgf at the
    -- matching scaled tilt.
    simpa [ν, id, mul_assoc, mul_left_comm, mul_comm] using
      (integral_tilted_mul_self (μ := ν) (X := id) (t := ((n + 1 : ℝ) * t)) hScaledMem)
  have hCgfEventually :
      (cgf id ν ∘ HMul.hMul (n + 1 : ℝ)) =ᶠ[𝓝 t]
        fun s ↦ (n + 1 : ℝ) * cgf (X 0) P s := by
    -- Proof comment: near `t`, the scaled empirical-mean cgf is exactly `(n + 1)` times the
    -- one-letter cgf.
    filter_upwards [isOpen_interior.eventually_mem ht] with s hs
    simpa [Function.comp, ν] using
      empiricalMeanLaw_cgf_eq_mul (P := P) (X := X) hX_iid (interior_subset hs) n
  have hDerivLeft :
      HasDerivAt
        (cgf id ν ∘ HMul.hMul (n + 1 : ℝ))
        (deriv (cgf id ν) (((n + 1 : ℝ) * t)) * (n + 1 : ℝ))
        t := by
    -- Proof comment: differentiate the empirical-mean cgf after composing with the linear scaling
    -- `s ↦ (n + 1) * s`.
    have hScaleDeriv :
        HasDerivAt (fun s : ℝ ↦ ((n + 1 : ℝ) * s)) (n + 1 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (n + 1 : ℝ)
    have hComp :
        HasDerivAt
          (cgf id ν ∘ HMul.hMul (n + 1 : ℝ))
          (deriv (cgf id ν) (((n + 1 : ℝ) * t)) * (n + 1 : ℝ))
          t := by
      exact
        (analyticAt_cgf (X := id) (μ := ν) hScaledMem).differentiableAt.hasDerivAt.comp t
          hScaleDeriv
    exact hComp
  have hDerivRight :
      HasDerivAt
        (fun s : ℝ ↦ (n + 1 : ℝ) * cgf (X 0) P s)
        ((n + 1 : ℝ) * deriv (cgf (X 0) P) t)
        t := by
    -- Proof comment: the right-hand side is just a constant multiple of the one-letter cgf.
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      ((analyticAt_cgf (X := X 0) (μ := P) ht).differentiableAt.hasDerivAt.const_mul
        (n + 1 : ℝ))
  have hDerivLeft' :
      HasDerivAt
        (fun s : ℝ ↦ (n + 1 : ℝ) * cgf (X 0) P s)
        (deriv (cgf id ν) (((n + 1 : ℝ) * t)) * (n + 1 : ℝ))
        t := by
    exact (EventuallyEq.hasDerivAt_iff hCgfEventually).1 hDerivLeft
  have hScaledEq :
      deriv (cgf id ν) (((n + 1 : ℝ) * t)) * (n + 1 : ℝ) =
        (n + 1 : ℝ) * deriv (cgf (X 0) P) t := by
    exact hDerivLeft'.unique hDerivRight
  have hDerivEq :
      deriv (cgf id ν) (((n + 1 : ℝ) * t)) = deriv (cgf (X 0) P) t := by
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    exact mul_right_cancel₀ hn <| by simpa [mul_comm] using hScaledEq
  exact hMoment.trans hDerivEq

/-- Helper for Theorem 23.11: under the empirical-mean tilt at slope `(n + 1) * t`, the tilted
variance is the one-letter second cgf derivative divided by `n + 1`. -/
private theorem empiricalMeanLaw_tiltedVariance_eq_iteratedDerivTwo_div
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P)) (n : ℕ) :
    let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
    Var[id; ν.tilted (fun z ↦ ((n + 1 : ℝ) * t * z))] =
      iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ) := by
  let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  let a : ℝ := n + 1
  have ha_ne : a ≠ 0 := by
    positivity
  have hScaledMem :
      (a * t) ∈ interior (integrableExpSet id ν) := by
    simpa [ν, a] using
      empiricalMeanLaw_scaledTilt_mem_interior (P := P) (X := X) hX_iid ht n
  have hVariance :
      Var[id; ν.tilted (fun z ↦ (a * t * z))] =
        iteratedDeriv 2 (cgf id ν) (a * t) := by
    -- Proof comment: the tilted variance is the second derivative of the empirical-mean cgf at
    -- the matching scaled tilt.
    simpa [ν, a, id, mul_assoc, mul_left_comm, mul_comm] using
      (variance_tilted_mul (μ := ν) (X := id) (t := (a * t)) hScaledMem)
  have hFirstDerivEventually :
      (fun s : ℝ ↦ deriv (cgf id ν) (a * s) * a) =ᶠ[𝓝 t]
        fun s ↦ a * deriv (cgf (X 0) P) s := by
    filter_upwards [isOpen_interior.eventually_mem ht] with s hs
    have hScaledMemS :
        (a * s) ∈ interior (integrableExpSet id ν) := by
      simpa [ν, a] using
        empiricalMeanLaw_scaledTilt_mem_interior (P := P) (X := X) hX_iid hs n
    have hCgfEventuallyS :
        (cgf id ν ∘ HMul.hMul a) =ᶠ[𝓝 s]
          fun u ↦ a * cgf (X 0) P u := by
      -- Proof comment: near `s`, the scaled empirical-mean cgf is exactly `a` times the one-letter
      -- cgf, so the derivative comparison can be run pointwise along the same neighborhood.
      filter_upwards [isOpen_interior.eventually_mem hs] with u hu
      simpa [Function.comp, ν, a] using
        empiricalMeanLaw_cgf_eq_mul (P := P) (X := X) hX_iid (interior_subset hu) n
    have hDerivLeftS :
        HasDerivAt
          (cgf id ν ∘ HMul.hMul a)
          (deriv (cgf id ν) (a * s) * a)
          s := by
      have hScaleDeriv : HasDerivAt (fun u : ℝ ↦ a * u) a s := by
        simpa [a] using (hasDerivAt_id s).const_mul a
      exact
        (analyticAt_cgf (X := id) (μ := ν) hScaledMemS).differentiableAt.hasDerivAt.comp s
          hScaleDeriv
    have hDerivRightS :
        HasDerivAt
          (fun u : ℝ ↦ a * cgf (X 0) P u)
          (a * deriv (cgf (X 0) P) s)
          s := by
      simpa [a, mul_assoc, mul_left_comm, mul_comm] using
        ((analyticAt_cgf (X := X 0) (μ := P) hs).differentiableAt.hasDerivAt.const_mul a)
    have hEqDeriv :
        deriv (cgf id ν ∘ HMul.hMul a) s =
          deriv (fun u : ℝ ↦ a * cgf (X 0) P u) s := by
      exact hCgfEventuallyS.deriv_eq
    calc
      deriv (cgf id ν) (a * s) * a = deriv (cgf id ν ∘ HMul.hMul a) s := by
        symm
        exact hDerivLeftS.deriv
      _ = deriv (fun u : ℝ ↦ a * cgf (X 0) P u) s := hEqDeriv
      _ = a * deriv (cgf (X 0) P) s := by
        exact hDerivRightS.deriv
  let F : ℝ → ℝ := fun s ↦ deriv (cgf id ν) (a * s) * a
  let G : ℝ → ℝ := fun s ↦ a * deriv (cgf (X 0) P) s
  have hDerivFBase :
      HasDerivAt
        (fun s : ℝ ↦ deriv (cgf id ν) (a * s))
        (iteratedDeriv 2 (cgf id ν) (a * t) * a)
        t := by
    have hDerivDeriv :
        HasDerivAt
          (fun u : ℝ ↦ deriv (cgf id ν) u)
          (iteratedDeriv 2 (cgf id ν) (a * t))
          (a * t) := by
      simpa [iteratedDeriv_succ] using
        ((analyticAt_cgf (X := id) (μ := ν) hScaledMem).iterated_deriv 1).differentiableAt.hasDerivAt
    have hScaleDeriv : HasDerivAt (fun s : ℝ ↦ a * s) a t := by
      simpa [a] using (hasDerivAt_id t).const_mul a
    exact hDerivDeriv.comp t hScaleDeriv
  have hDerivF :
      HasDerivAt F ((iteratedDeriv 2 (cgf id ν) (a * t) * a) * a) t := by
    -- Proof comment: differentiate the pointwise first-derivative transport once more.
    simpa [F, mul_assoc, mul_left_comm, mul_comm] using hDerivFBase.mul_const a
  have hDerivG :
      HasDerivAt G (a * iteratedDeriv 2 (cgf (X 0) P) t) t := by
    have hDerivDeriv :
        HasDerivAt
          (fun s : ℝ ↦ deriv (cgf (X 0) P) s)
          (iteratedDeriv 2 (cgf (X 0) P) t)
          t := by
      simpa [iteratedDeriv_succ] using
        ((analyticAt_cgf (X := X 0) (μ := P) ht).iterated_deriv 1).differentiableAt.hasDerivAt
    simpa [G, mul_assoc, mul_left_comm, mul_comm] using hDerivDeriv.const_mul a
  have hSecondScaled :
      ((iteratedDeriv 2 (cgf id ν) (a * t) * a) * a) =
        a * iteratedDeriv 2 (cgf (X 0) P) t := by
    have hEqDeriv : deriv F t = deriv G t := hFirstDerivEventually.deriv_eq
    rw [hDerivF.deriv, hDerivG.deriv] at hEqDeriv
    exact hEqDeriv
  have hSecond :
      iteratedDeriv 2 (cgf id ν) (a * t) = iteratedDeriv 2 (cgf (X 0) P) t / a := by
    apply (eq_div_iff ha_ne).2
    exact mul_right_cancel₀ ha_ne <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hSecondScaled
  calc
    Var[id; ν.tilted (fun z ↦ (a * t * z))]
        = iteratedDeriv 2 (cgf id ν) (a * t) := hVariance
    _ = iteratedDeriv 2 (cgf (X 0) P) t / a := hSecond
    _ = iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ) := by
          simp [a]

/-- Helper for Theorem 23.11: a half-mass lower bound under the empirical-mean tilted law yields
the fixed-index centered-interval lower bound after paying the deterministic Cramér correction. -/
private theorem empiricalMeanLaw_centeredInterval_scaledLog_ge_halfCorrection
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {x t δ : ℝ} (ht : t ∈ integrableExpSet (X 0) P)
    (n : ℕ)
    (hHalf :
      let νt : Measure ℝ :=
        (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ).tilted
          (fun z ↦ ((n + 1 : ℝ) * t * z))
      ; (1 / 2 : ENNReal) ≤ νt (Set.Ioo (x - δ) (x + δ))) :
    (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
      ((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) +
      scaledLogMassAlong
        (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
        cramerSpeed
        (Set.Ioo (x - δ) (x + δ))
        n := by
  let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  let A : Set ℝ := Set.Ioo (x - δ) (x + δ)
  let c : ℝ := t * x - cgf (X 0) P t + |t| * δ
  let S : Ω → ℝ := fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)
  let Y : Ω → ℝ := fun ω ↦ S ω / (n + 1 : ℝ)
  have hXae : ∀ i, AEMeasurable (X i) P := iidAEMeasurable P X hX_iid
  have hYae : AEMeasurable Y P := by
    -- Proof comment: the empirical mean is the measurable average of the first `n + 1`
    -- coordinates.
    simpa [Y, S] using empiricalMean_aemeasurable P X hXae n
  have hνmap : ν = Measure.map Y P := by
    -- Proof comment: rewrite the owner empirical-mean law as the pushforward of `P` by the
    -- zero-based average so the tilt integrability can be checked on `P`.
    simpa [ν, Y, S] using
      (empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
        (P := P) (X := X) hXae n).trans
        (normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage (P := P) (X := X) n)
  have hInt0 : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
    integrable_of_mem_integrableExpSet ht
  have hInt :
      ∀ i ∈ Finset.range (n + 1), Integrable (fun ω ↦ Real.exp (t * X i ω)) P := by
    intro i hi
    have hIdentExp :
        IdentDistrib
          (fun ω ↦ Real.exp (t * X i ω))
          (fun ω ↦ Real.exp (t * X 0 ω)) P P := by
      simpa using (hX_iid.identDistrib i 0).comp ((measurable_const_mul t).exp)
    exact hIdentExp.integrable_iff.2 hInt0
  have hMgfPos : 0 < mgf S P t := by
    rw [show S = ∑ i ∈ Finset.range (n + 1), X i by
      funext ω
      simp [S]]
    rw [hX_iid.iIndepFun.mgf_sum₀ hXae (Finset.range (n + 1))]
    refine Finset.prod_pos ?_
    intro i hi
    exact mgf_pos' (IsProbabilityMeasure.ne_zero P) (hInt i hi)
  have hSumInt : Integrable (fun ω ↦ Real.exp (t * S ω)) P := by
    by_contra hNotInt
    exact hMgfPos.ne' (mgf_undef hNotInt)
  have hIntTilt :
      Integrable (fun z : ℝ ↦ Real.exp ((((n + 1 : ℝ) * t) * z))) ν := by
    -- Proof comment: this is the reusable tilted-integrability bridge for empirical means.
    simpa [ν] using
      empiricalMeanLaw_integrable_exp_mul (P := P) (X := X) hX_iid ht n
  have hTiltApply :
      (ν.tilted (fun z ↦ (((n + 1 : ℝ) * t) * z))) A =
        ∫⁻ z in A,
          ENNReal.ofReal
            (Real.exp
              ((((n + 1 : ℝ) * t) * z) -
                cgf id ν (((n + 1 : ℝ) * t)))) ∂ν := by
    -- Proof comment: rewrite the tilted event mass using the owner `cgf` formula on `ν`.
    simpa [A, ν] using
      (ProbabilityTheory.tilted_mul_apply_cgf'
        (μ := ν) (X := id) (t := ((n + 1 : ℝ) * t))
        (s := A) measurableSet_Ioo hIntTilt)
  have hMassLe :
      (ν.tilted (fun z ↦ (((n + 1 : ℝ) * t) * z))) A ≤
        ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * c)) * ν A := by
    calc
      (ν.tilted (fun z ↦ (((n + 1 : ℝ) * t) * z))) A =
          ∫⁻ z in A,
            ENNReal.ofReal
              (Real.exp
                ((((n + 1 : ℝ) * t) * z) -
                  cgf id ν (((n + 1 : ℝ) * t)))) ∂ν := hTiltApply
      _ ≤ ∫⁻ _z in A, ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * c)) ∂ν := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
            exact ENNReal.ofReal_le_ofReal <|
              Real.exp_le_exp.mpr <|
                by
                  simpa [ν, A, c] using
                    (empiricalMeanLaw_centeredInterval_exponent_le_affineError
                      (P := P) (X := X) hX_iid (x := x) (t := t) (δ := δ)
                      (z := z) ht (n := n) hz)
      _ = ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * c)) * ν A := by
            simp [A, MeasureTheory.lintegral_const]
  have hLog :
      ENNReal.log (1 / 2 : ENNReal) ≤
        ((((n + 1 : ℝ) * c : ℝ) : EReal)) + ENNReal.log (ν A) := by
    calc
      ENNReal.log (1 / 2 : ENNReal) ≤
          ENNReal.log (ENNReal.ofReal (Real.exp ((n + 1 : ℝ) * c)) * ν A) := by
            exact ENNReal.log_monotone (le_trans hHalf hMassLe)
      _ = ((((n + 1 : ℝ) * c : ℝ) : EReal)) + ENNReal.log (ν A) := by
            rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
  have hεNonneg : (0 : EReal) ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal)) := by
    exact_mod_cast le_of_lt (cramerSpeed_pos n)
  have hUpper :
      (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
        (((c : ℝ) : EReal)) +
          scaledLogMassAlong
            (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
            cramerSpeed A n := by
    have hMul :
        (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
          (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) *
            (((((n + 1 : ℝ) * c : ℝ) : EReal)) + ENNReal.log (ν A))) := by
      exact mul_le_mul_of_nonneg_left hLog hεNonneg
    calc
      (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
          (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) *
            (((((n + 1 : ℝ) * c : ℝ) : EReal)) + ENNReal.log (ν A))) := hMul
      _ = (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ((((n + 1 : ℝ) * c : ℝ) : EReal))) +
            (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (ν A)) := by
              rw [EReal.left_distrib_of_nonneg_of_ne_top hεNonneg (by simp)]
      _ = (((c : ℝ) : EReal)) +
            scaledLogMassAlong
              (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
              cramerSpeed A n := by
              have hAlg : ((n + 1 : ℝ)⁻¹) * ((n + 1 : ℝ) * c) = c := by
                have hn : (n + 1 : ℝ) ≠ 0 := by positivity
                field_simp [hn]
              have hAlgEReal :
                  (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ((((n + 1 : ℝ) * c : ℝ) : EReal))) =
                    (((c : ℝ) : EReal)) := by
                exact_mod_cast hAlg
              rw [hAlgEReal, scaledLogMassAlong_def]
              simp [A, ν, cramerSpeed]
  -- Proof comment: move the affine cost to the left to obtain the fixed-index lower bound for
  -- the original interval mass.
  have hUpper' :
      (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
        ((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) +
          scaledLogMassAlong
            (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
            cramerSpeed
            (Set.Ioo (x - δ) (x + δ))
            n := by
    have hCost :
        (((c : ℝ) : EReal)) =
          ((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) := by
      change ((((t * x - cgf (X 0) P t + |t| * δ : ℝ)) : EReal)) =
        ((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal))
      rw [EReal.coe_add]
    calc
      (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) ≤
          (((c : ℝ) : EReal)) +
            scaledLogMassAlong
              (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
              cramerSpeed
              A
              n := hUpper
      _ =
          ((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) +
            scaledLogMassAlong
              (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
              cramerSpeed
              (Set.Ioo (x - δ) (x + δ))
              n := by
                simpa [A] using congrArg
                  (fun z : EReal ↦
                    z +
                      scaledLogMassAlong
                        (fun m ↦
                          (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
                        cramerSpeed
                        A
                        n)
                  hCost
  exact hUpper'

/-- Helper for Theorem 23.11: under an interior tilt, the empirical-mean tilted law eventually
puts at least half of its mass on every fixed centered interval around the tilted mean. -/
private theorem empiricalMeanLaw_tiltedWindow_eventually_ge_half
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t δ : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P)) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ENNReal) ≤
        ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ).tilted
          (fun z ↦ ((n + 1 : ℝ) * t * z)))
          (Set.Ioo (deriv (cgf (X 0) P) t - δ) (deriv (cgf (X 0) P) t + δ)) := by
  let x : ℝ := deriv (cgf (X 0) P) t
  have hNat : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hInv :
      Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹)) atTop (nhds (0 : ℝ)) := by
    -- Proof comment: the empirical-mean variance scale decays like `(n + 1)⁻¹`.
    exact tendsto_inv_atTop_zero.comp hNat
  have hSmall :
      Tendsto
        (fun n : ℕ ↦
          (iteratedDeriv 2 (cgf (X 0) P) t / δ ^ (2 : ℕ)) * (((n : ℝ) + 1)⁻¹))
        atTop (nhds (0 : ℝ)) := by
    simpa using tendsto_const_nhds.mul hInv
  have hEventuallySmall :
      ∀ᶠ n : ℕ in atTop,
        (iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ)) / δ ^ (2 : ℕ) < (1 / 2 : ℝ) := by
    have hTarget :
        ∀ᶠ n : ℕ in atTop,
          (iteratedDeriv 2 (cgf (X 0) P) t / δ ^ (2 : ℕ)) * (((n : ℝ) + 1)⁻¹) <
            (1 / 2 : ℝ) := by
      exact hSmall (Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [hTarget] with n hn
    simpa [Nat.cast_add, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hn
  filter_upwards [hEventuallySmall] with n hnSmall
  let ν : Measure ℝ := (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ)
  let νt : Measure ℝ := ν.tilted (fun z ↦ ((n + 1 : ℝ) * t * z))
  have hInt :
      Integrable (fun z : ℝ ↦ Real.exp (((n + 1 : ℝ) * t * z))) ν := by
    -- Proof comment: the empirical-mean law has the required exponential moment at the scaled
    -- interior tilt.
    simpa [ν, mul_assoc, mul_left_comm, mul_comm] using
      empiricalMeanLaw_integrable_exp_mul
        (P := P) (X := X) hX_iid (interior_subset ht) n
  letI : IsProbabilityMeasure νt := isProbabilityMeasure_tilted hInt
  have hScaledMem :
      ((n + 1 : ℝ) * t) ∈ interior (integrableExpSet id ν) := by
    simpa [ν] using empiricalMeanLaw_scaledTilt_mem_interior (P := P) (X := X) hX_iid ht n
  have hMean : νt[id] = x := by
    -- Proof comment: the previous mean transport identifies the tilted center with the one-letter
    -- cgf derivative.
    simpa [ν, νt, x, mul_assoc, mul_left_comm, mul_comm] using
      empiricalMeanLaw_tiltedMean_eq_derivCgf (P := P) (X := X) hX_iid ht n
  have hVar :
      Var[id; νt] = iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ) := by
    -- Proof comment: the variance decays exactly like `(n + 1)⁻¹` after the cgf transport.
    simpa [ν, νt, mul_assoc, mul_left_comm, mul_comm] using
      empiricalMeanLaw_tiltedVariance_eq_iteratedDerivTwo_div
        (P := P) (X := X) hX_iid ht n
  have hMemLp : MemLp id 2 νt := by
    -- Proof comment: finite exponential moments place the tilted identity random variable in `L²`.
    simpa [ν, νt, mul_assoc, mul_left_comm, mul_comm] using
      (memLp_tilted_mul (μ := ν) (X := id) (t := ((n + 1 : ℝ) * t)) hScaledMem 2)
  let center : ℝ := νt[id]
  have hChebyshev :
      νt {z | δ ≤ |z - center|} ≤
        ENNReal.ofReal ((iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ)) / δ ^ (2 : ℕ)) := by
    -- Proof comment: Chebyshev bounds the complement of the centered interval by the tilted
    -- variance divided by `δ²`.
    simpa [center, hVar, νt] using
      (meas_ge_le_variance_div_sq (μ := νt) (X := id) hMemLp (c := δ) hδ)
  have hComplSubset :
      (Set.Ioo (x - δ) (x + δ))ᶜ ⊆ {z | δ ≤ |z - center|} := by
    -- Proof comment: outside the centered interval, the distance from the tilted mean is at
    -- least `δ`.
    intro z hz
    have hzNot : z ∉ Set.Ioo (x - δ) (x + δ) := by
      simpa using hz
    change δ ≤ |z - νt[id]|
    rw [hMean]
    by_cases hLeft : z ≤ x - δ
    · have hNonpos : z - x ≤ 0 := by
        linarith
      rw [abs_of_nonpos hNonpos]
      linarith
    · have hRight : x + δ ≤ z := by
        by_contra hRight
        exact hzNot ⟨lt_of_not_ge hLeft, lt_of_not_ge hRight⟩
      have hNonneg : 0 ≤ z - x := by
        linarith
      rw [abs_of_nonneg hNonneg]
      linarith
  have hBoundLt :
      ENNReal.ofReal ((iteratedDeriv 2 (cgf (X 0) P) t / (n + 1 : ℝ)) / δ ^ (2 : ℕ)) <
        (1 / 2 : ENNReal) := by
    simpa using
      (ENNReal.ofReal_lt_ofReal_iff (show (0 : ℝ) < 1 / 2 by norm_num)).2 hnSmall
  have hComplLt :
      νt (Set.Ioo (x - δ) (x + δ))ᶜ < (1 / 2 : ENNReal) := by
    exact lt_of_le_of_lt (le_trans (measure_mono hComplSubset) hChebyshev) hBoundLt
  exact one_half_le_measure_of_compl_lt_half
    (μ := νt) (s := Set.Ioo (x - δ) (x + δ)) measurableSet_Ioo hComplLt

/-- Helper for Theorem 23.11: an interior tilt gives the centered-interval lower bound in final
scaled-log form after absorbing the `log (1 / 2)` correction. -/
private theorem empiricalMeanLaw_centeredOpenInterval_liminf_ge_negAffine_of_interiorTilt
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {t δ : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P)) (hδ : 0 < δ) :
    -((((t * deriv (cgf (X 0) P) t - cgf (X 0) P t : ℝ)) : EReal) +
        (((|t| * δ : ℝ)) : EReal)) ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          (Set.Ioo (deriv (cgf (X 0) P) t - δ) (deriv (cgf (X 0) P) t + δ)))
        atTop := by
  let x : ℝ := deriv (cgf (X 0) P) t
  let c : ℝ := t * x - cgf (X 0) P t + |t| * δ
  have hHalfEventually :
      ∀ᶠ n : ℕ in atTop,
        (1 / 2 : ENNReal) ≤
          ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ).tilted
            (fun z ↦ ((n + 1 : ℝ) * t * z))) (Set.Ioo (x - δ) (x + δ)) := by
    simpa [x] using
      empiricalMeanLaw_tiltedWindow_eventually_ge_half
        (P := P) (X := X) hX_iid ht hδ
  rw [Filter.le_liminf_iff']
  intro y hy
  have hyShift : y + ((c : ℝ) : EReal) < 0 := by
    -- Proof comment: rewrite the target comparison as a negative shifted constant so the
    -- deterministic `log (1 / 2)` term can absorb it.
    exact EReal.add_lt_of_lt_sub <| by
      simpa [c, x, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
  have hCorr :
      ∀ᶠ n : ℕ in atTop,
        y + ((c : ℝ) : EReal) <
          (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) := by
    exact eventually_lt_cramerLogConstCorrection (b := (1 / 2 : ENNReal)) (by norm_num) (by simp)
      hyShift
  filter_upwards [hCorr, hHalfEventually] with n hyn hHalf
  have hyCompare :
      y <
        (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) -
          ((c : ℝ) : EReal) := by
    exact
      (EReal.lt_sub_iff_add_lt (.inl (by simp)) (.inl (by simp))).2 <|
        by simpa [c, add_assoc, add_left_comm, add_comm] using hyn
  have hInterval :
      (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (1 / 2 : ENNReal)) -
          ((c : ℝ) : EReal) ≤
        scaledLogMassAlong
          (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
          cramerSpeed
          (Set.Ioo (x - δ) (x + δ))
          n := by
    -- Proof comment: the fixed-index change-of-measure inequality is exactly the centered-window
    -- interface established earlier.
    refine (EReal.sub_le_iff_le_add (.inl (by simp)) (.inl (by simp))).2 ?_
    simpa [c, add_assoc, add_left_comm, add_comm] using
      empiricalMeanLaw_centeredInterval_scaledLog_ge_halfCorrection
        (P := P) (X := X) hX_iid (x := x) (t := t) (δ := δ) (interior_subset ht) n hHalf
  exact hyCompare.le.trans hInterval

/-- Helper for Theorem 23.11: a nonnegative tilt gives the owner closed-right-ray Chernoff bound
at each finite index. -/
private theorem empiricalMeanLaw_closedRightHalfline_le_neg_affine
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {a t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    scaledLogMassAlong
        (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
        cramerSpeed
        (Set.Ici a) n ≤
      -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) := by
  by_cases hmem : t ∈ integrableExpSet (X 0) P
  · let S : Ω → ℝ := fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)
    let event : Set Ω := {ω | a * (n + 1 : ℝ) ≤ S ω}
    have hS :
        S = ∑ i ∈ Finset.range (n + 1), X i := by
      funext ω
      simp [S]
    have hXae : ∀ i, AEMeasurable (X i) P := iidAEMeasurable P X hX_iid
    have hInt0 : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
      integrable_of_mem_integrableExpSet hmem
    have hInt :
        ∀ i ∈ Finset.range (n + 1), Integrable (fun ω ↦ Real.exp (t * X i ω)) P := by
      intro i hi
      have hIdentExp :
          IdentDistrib
            (fun ω ↦ Real.exp (t * X i ω))
            (fun ω ↦ Real.exp (t * X 0 ω)) P P := by
        simpa using (hX_iid.identDistrib i 0).comp ((measurable_const_mul t).exp)
      exact hIdentExp.integrable_iff.2 hInt0
    have hMgfPos : 0 < mgf S P t := by
      rw [hS]
      rw [hX_iid.iIndepFun.mgf_sum₀ hXae (Finset.range (n + 1))]
      refine Finset.prod_pos ?_
      intro i hi
      exact mgf_pos' (IsProbabilityMeasure.ne_zero P) (hInt i hi)
    have hSumInt : Integrable (fun ω ↦ Real.exp (t * S ω)) P := by
      by_contra hNotInt
      exact hMgfPos.ne' (mgf_undef hNotInt)
    have hChernoff :
        P.real event ≤ Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t) := by
      simpa [S, event, mul_assoc, mul_left_comm, mul_comm] using
        (measure_ge_le_exp_cgf (μ := P) (X := S) (ε := a * (n + 1 : ℝ)) (t := t) ht hSumInt)
    have hMassLe :
        P event ≤ ENNReal.ofReal (Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t)) := by
      rw [← MeasureTheory.ofReal_measureReal (μ := P) (s := event)]
      exact ENNReal.ofReal_le_ofReal hChernoff
    have hLogMass :
        ENNReal.log (P event) ≤
          (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal)) := by
      calc
        ENNReal.log (P event) ≤
            ENNReal.log
              (ENNReal.ofReal (Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t))) :=
          ENNReal.log_monotone hMassLe
        _ = (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal)) := by
            rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    have hε_nonneg : (0 : EReal) ≤ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast le_of_lt (cramerSpeed_pos n)
    have hEvalCgf :
        cgf S P t = (n + 1 : ℝ) * cgf (X 0) P t := by
      simpa [S] using zeroBasedPartialSum_cgf_eq_mul (P := P) (X := X) hX_iid hmem n
    have hAlg :
        ((n + 1 : ℝ)⁻¹) *
            (-(t * (a * (n + 1 : ℝ))) + (n + 1 : ℝ) * cgf (X 0) P t) =
          -(t * a - cgf (X 0) P t) := by
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      ring
    calc
      scaledLogMassAlong
          (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
          cramerSpeed
          (Set.Ici a) n
          = (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (P event)) := by
              rw [scaledLogMassAlong_def,
                empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
                  (P := P) (X := X) hXae n,
                normalizedPartialSumLaw_closedHalfline_eq_upperTailEvent
                  (P := P) (X := X) hXae a n]
              simp [cramerSpeed, event, S]
      _ ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) *
            (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal))) := by
              exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
      _ = -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) := by
            rw [hEvalCgf,
              extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
                (X := X 0) (P := P) hmem]
            exact_mod_cast hAlg
  · -- Proof comment: outside the effective domain the affine exponent is `⊥`, so the target
    -- upper bound is trivially `≤ ⊤`.
    rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      (X := X 0) (P := P) hmem]
    simp

/-- Helper for Theorem 23.11: a nonpositive tilt gives the owner closed-left-ray Chernoff bound
at each finite index. -/
private theorem empiricalMeanLaw_closedLeftHalfline_le_neg_affine
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {a t : ℝ} (ht : t ≤ 0) (n : ℕ) :
    scaledLogMassAlong
        (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
        cramerSpeed
        (Set.Iic a) n ≤
      -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) := by
  by_cases hmem : t ∈ integrableExpSet (X 0) P
  · let S : Ω → ℝ := fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω)
    let event : Set Ω := {ω | S ω ≤ a * (n + 1 : ℝ)}
    have hS :
        S = ∑ i ∈ Finset.range (n + 1), X i := by
      funext ω
      simp [S]
    have hXae : ∀ i, AEMeasurable (X i) P := iidAEMeasurable P X hX_iid
    have hInt0 : Integrable (fun ω ↦ Real.exp (t * X 0 ω)) P :=
      integrable_of_mem_integrableExpSet hmem
    have hInt :
        ∀ i ∈ Finset.range (n + 1), Integrable (fun ω ↦ Real.exp (t * X i ω)) P := by
      intro i hi
      have hIdentExp :
          IdentDistrib
            (fun ω ↦ Real.exp (t * X i ω))
            (fun ω ↦ Real.exp (t * X 0 ω)) P P := by
        simpa using (hX_iid.identDistrib i 0).comp ((measurable_const_mul t).exp)
      exact hIdentExp.integrable_iff.2 hInt0
    have hMgfPos : 0 < mgf S P t := by
      rw [hS]
      rw [hX_iid.iIndepFun.mgf_sum₀ hXae (Finset.range (n + 1))]
      refine Finset.prod_pos ?_
      intro i hi
      exact mgf_pos' (IsProbabilityMeasure.ne_zero P) (hInt i hi)
    have hSumInt : Integrable (fun ω ↦ Real.exp (t * S ω)) P := by
      by_contra hNotInt
      exact hMgfPos.ne' (mgf_undef hNotInt)
    have hChernoff :
        P.real event ≤ Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t) := by
      simpa [S, event, mul_assoc, mul_left_comm, mul_comm] using
        (measure_le_le_exp_cgf (μ := P) (X := S) (ε := a * (n + 1 : ℝ)) (t := t) ht hSumInt)
    have hMassLe :
        P event ≤ ENNReal.ofReal (Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t)) := by
      rw [← MeasureTheory.ofReal_measureReal (μ := P) (s := event)]
      exact ENNReal.ofReal_le_ofReal hChernoff
    have hLogMass :
        ENNReal.log (P event) ≤
          (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal)) := by
      calc
        ENNReal.log (P event) ≤
            ENNReal.log
              (ENNReal.ofReal (Real.exp (-(t * (a * (n + 1 : ℝ))) + cgf S P t))) :=
          ENNReal.log_monotone hMassLe
        _ = (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal)) := by
            rw [ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    have hε_nonneg : (0 : EReal) ≤ (((n + 1 : ℝ)⁻¹ : ℝ) : EReal) := by
      exact_mod_cast le_of_lt (cramerSpeed_pos n)
    have hEvalCgf :
        cgf S P t = (n + 1 : ℝ) * cgf (X 0) P t := by
      simpa [S] using zeroBasedPartialSum_cgf_eq_mul (P := P) (X := X) hX_iid hmem n
    have hAlg :
        ((n + 1 : ℝ)⁻¹) *
            (-(t * (a * (n + 1 : ℝ))) + (n + 1 : ℝ) * cgf (X 0) P t) =
          -(t * a - cgf (X 0) P t) := by
      have hn : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp [hn]
      ring
    calc
      scaledLogMassAlong
          (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
          cramerSpeed
          (Set.Iic a) n
          = (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) * ENNReal.log (P event)) := by
              rw [scaledLogMassAlong_def,
                empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
                  (P := P) (X := X) hXae n,
                normalizedPartialSumLaw_closedHalfline_eq_lowerTailEvent
                  (P := P) (X := X) hXae a n]
              simp [cramerSpeed, event, S]
      _ ≤ (((((n + 1 : ℝ)⁻¹ : ℝ)) : EReal) *
            (((-(t * (a * (n + 1 : ℝ))) + cgf S P t : ℝ) : EReal))) := by
              exact mul_le_mul_of_nonneg_left hLogMass hε_nonneg
      _ = -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) := by
            rw [hEvalCgf,
              extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
                (X := X 0) (P := P) hmem]
            exact_mod_cast hAlg
  · -- Proof comment: outside the effective domain the affine exponent is `⊥`, so the target
    -- upper bound is trivially `≤ ⊤`.
    rw [extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
      (X := X 0) (P := P) hmem]
    simp

/-- Helper for Theorem 23.11: the sign-appropriate one-sided Chernoff bounds on owner closed rays
already control the corresponding `limsup` exponents. -/
private theorem empiricalMeanLaw_closedRay_limsup_le_neg_affine
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {a t : ℝ} :
    (0 ≤ t →
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Ici a))
            atTop ≤
          -((((t * a : ℝ) : EReal) - Λ(X 0; P) t))) ∧
      (t ≤ 0 →
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Iic a))
            atTop ≤
          -((((t * a : ℝ) : EReal) - Λ(X 0; P) t))) := by
  constructor
  · intro ht
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          scaledLogMassAlong
              (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
              cramerSpeed
              (Set.Ici a) n ≤
            -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) := by
      exact Filter.Eventually.of_forall
        (empiricalMeanLaw_closedRightHalfline_le_neg_affine
          (P := P) (X := X) hX_iid ht)
    exact Filter.limsup_le_of_le
      (hf := by
        simpa [Filter.IsCoboundedUnder] using
          (Filter.isCobounded_le_of_bot :
            (Filter.map
              (scaledLogMassAlong
                (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                cramerSpeed
                (Set.Ici a))
              atTop).IsCobounded (· ≤ ·)))
      hEventually
  · intro ht
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          scaledLogMassAlong
              (fun m ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) m : Measure ℝ))
              cramerSpeed
              (Set.Iic a) n ≤
            -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) :=
      Filter.Eventually.of_forall
        (empiricalMeanLaw_closedLeftHalfline_le_neg_affine
          (P := P) (X := X) hX_iid ht)
    exact Filter.limsup_le_of_le
      (hf := by
        simpa [Filter.IsCoboundedUnder] using
          (Filter.isCobounded_le_of_bot :
            (Filter.map
              (scaledLogMassAlong
                (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                cramerSpeed
                (Set.Iic a))
              atTop).IsCobounded (· ≤ ·)))
      hEventually

/-- Helper for Theorem 23.11: a positive comparison value already dominates every scaled
logarithmic mass because empirical-mean laws are probability measures. -/
private theorem empiricalMeanLaw_eventually_lt_of_pos
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {s : Set ℝ} {y : EReal} (hy : 0 < y) :
    ∀ᶠ n : ℕ in atTop,
      scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          s n < y := by
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            s n ≤ 0 := by
    -- Proof comment: every event under a probability law has nonpositive scaled logarithmic mass.
    exact Filter.Eventually.of_forall fun n ↦
      scaledLogMassAlong_nonpos_of_probability
        (μ := empiricalMeanLaw X P (iidAEMeasurable P X hX_iid))
        (ε := cramerSpeed) (s := s) n
  filter_upwards [hEventually] with n hn
  exact hn.trans_lt hy

/-- Helper for Theorem 23.11: once the one-sided Chernoff affine bound on a right ray is strictly
below `y`, the corresponding `limsup` is strictly below `y`. -/
private theorem empiricalMeanLaw_closedRightHalfline_limsup_lt_of_neg_affine
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {a t : ℝ} {y : EReal} (ht : 0 ≤ t)
    (hy :
      -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) < y) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          (Set.Ici a))
        atTop < y := by
  -- Proof comment: combine the closed-ray `limsup ≤` package with the strict affine comparison.
  exact ((empiricalMeanLaw_closedRay_limsup_le_neg_affine
    (P := P) (X := X) hX_iid).1 ht).trans_lt hy

/-- Helper for Theorem 23.11: once the one-sided Chernoff affine bound on a left ray is strictly
below `y`, the corresponding `limsup` is strictly below `y`. -/
private theorem empiricalMeanLaw_closedLeftHalfline_limsup_lt_of_neg_affine
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {a t : ℝ} {y : EReal} (ht : t ≤ 0)
    (hy :
      -((((t * a : ℝ) : EReal) - Λ(X 0; P) t)) < y) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          (Set.Iic a))
        atTop < y := by
  -- Proof comment: the left-ray case is the sign-reversed companion to the right-ray helper.
  exact ((empiricalMeanLaw_closedRay_limsup_le_neg_affine
    (P := P) (X := X) hX_iid).2 ht).trans_lt hy

/-- Helper for Theorem 23.11: when the exponential-integrability domain collapses to `{0}`, the
closed-set upper bound is already the trivial `limsup ≤ 0` estimate. -/
private theorem empiricalMeanLaw_closed_upper_bound_of_singletonIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hSet : integrableExpSet (X 0) P = ({0} : Set ℝ))
    {C : Set ℝ} (_hC : IsClosed C) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          C)
        atTop ≤
      -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' C) := by
  by_cases hEmpty : C = ∅
  · -- Proof comment: the empty closed set still has logarithmic mass `⊥` at every index, so this
    -- branch is immediate.
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (∅ : Set ℝ) n = ⊥ := by
      exact Filter.Eventually.of_forall fun n ↦
        scaledLogMassAlong_empty_eq_bot
          (μ := fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (ε := cramerSpeed) n
    have hEmptyLimsup :
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (∅ : Set ℝ))
            atTop ≤
          -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' (∅ : Set ℝ)) := by
      rw [Filter.limsup_congr hEventually]
      simp
    simpa [hEmpty] using hEmptyLimsup
  · have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hRateInf :
        sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' C) = 0 := by
      -- Proof comment: in the singleton-domain branch the owner rate vanishes pointwise, so its
      -- image on every nonempty set has infimum `0`.
      simpa [empiricalMeanOwnerRate] using
        ownerRateImage_sInf_eq_zero_of_nonempty_of_integrableExpSet_eq_singleton_zero
          (P := P) (X := X 0) hSet hCne
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              C n ≤ 0 := by
      -- Proof comment: every empirical-mean law is a probability law, so every event has
      -- nonpositive scaled logarithmic mass.
      exact Filter.Eventually.of_forall fun n ↦
        scaledLogMassAlong_nonpos_of_probability
          (μ := empiricalMeanLaw X P (iidAEMeasurable P X hX_iid))
          (ε := cramerSpeed) (s := C) n
    have hLimsupLeZero :
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              C)
            atTop ≤ 0 := by
      exact Filter.limsup_le_of_le
        (hf := by
          simpa [Filter.IsCoboundedUnder] using
            (Filter.isCobounded_le_of_bot :
              (Filter.map
                (scaledLogMassAlong
                  (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                  cramerSpeed
                  C)
                atTop).IsCobounded (· ≤ ·)))
        hEventually
    simpa [hRateInf] using hLimsupLeZero

/-- Helper for Theorem 23.11: closed sets satisfy the owner empirical-mean upper bound once the
two-ray Chernoff package is available. -/
private theorem empiricalMeanLaw_closed_upper_bound
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) {C : Set ℝ} (hC : IsClosed C) :
    Filter.limsup
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          C)
        atTop ≤
      -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' C) := by
  by_cases hEmpty : C = ∅
  · -- Proof comment: the empty closed set has logarithmic mass `⊥` at every index, so its
    -- `limsup` is the trivial upper bound.
    have hEventually :
        ∀ᶠ n : ℕ in atTop,
          scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (∅ : Set ℝ) n = ⊥ := by
      exact Filter.Eventually.of_forall fun n ↦
        scaledLogMassAlong_empty_eq_bot
          (μ := fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (ε := cramerSpeed) n
    have hEmptyLimsup :
        Filter.limsup
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (∅ : Set ℝ))
            atTop ≤
          -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' (∅ : Set ℝ)) := by
      rw [Filter.limsup_congr hEventually]
      simp
    simpa [hEmpty] using hEmptyLimsup
  · by_cases hSet : integrableExpSet (X 0) P = ({0} : Set ℝ)
    · -- Proof comment: route correction for the repeated closed-branch blocker: isolate the
      -- degenerate domain first so the geometric two-ray argument is only used in the genuinely
      -- nontrivial case.
      exact empiricalMeanLaw_closed_upper_bound_of_singletonIntegrableExpSet
        (P := P) (X := X) hX_iid hSet hC
    · -- TODO: the closed convex geometry is now factored into `closedConvex_real_shape`,
      -- `closedSet_rightRay_of_disjoint_leftRay`, `closedSet_leftRay_of_disjoint_rightRay`,
      -- `closedSet_twoRayCover_of_disjoint_interval`, and the sign-forcing affine witness lemmas.
      -- The remaining closed-branch work is to instantiate those helpers for the low-rate sublevel
      -- `{x | legendreFenchelRateFunction (Λ(X 0; P)) x ≤ -y}` and feed the resulting cover into
      -- the already proved one-ray and union `limsup` estimates.
      rw [Filter.limsup_le_iff']
      intro y hy
      by_cases hyTop : y = ⊤
      · simp [hyTop]
      by_cases hyPos : 0 < y
      · -- Proof comment: the positive comparison regime is already trivial because the scaled
        -- logarithmic masses are always nonpositive.
        exact (empiricalMeanLaw_eventually_lt_of_pos
          (P := P) (X := X) hX_iid (s := C) hyPos).mono fun _ hn ↦ hn.le
      · have hyNonpos : y ≤ 0 := le_of_not_gt hyPos
        have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
        rcases exists_positive_ownerRate_threshold_between_lt_neg_sInf
            (P := P) (X := X) (C := C) hy hyNonpos with
          ⟨level, hLevelPos, hLevelInf, hLevelLtY⟩
        let y₀ : EReal := -((level : ENNReal) : EReal)
        have hy₀_lt_y : y₀ < y := by
          simpa [y₀] using hLevelLtY
        let K : Set ℝ := {x : ℝ | empiricalMeanOwnerRate P X x ≤ level}
        have hKshape :
            IsClosed K ∧ Convex ℝ K ∧
              (K = ∅ ∨ K = Set.univ ∨ (∃ u, K = Set.Iic u) ∨ (∃ v, K = Set.Ici v) ∨
                ∃ u v, u ≤ v ∧ K = Set.Icc u v) := by
          simpa [K, empiricalMeanOwnerRate] using
            empiricalMeanOwnerRateSublevel_shape
              (P := P) (X := X) level
        have hKeq :
            K = {x : ℝ | ((empiricalMeanOwnerRate P X x : ENNReal) : EReal) ≤ -y₀} := by
          ext x
          constructor
          · intro hx
            calc
              ((empiricalMeanOwnerRate P X x : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
                    exact_mod_cast hx
              _ = -y₀ := by
                    simp [y₀]
          · intro hx
            have hx' :
                ((empiricalMeanOwnerRate P X x : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
              simpa [y₀] using hx
            exact_mod_cast hx'
        have hKdisj :
            Disjoint C {x : ℝ | ((empiricalMeanOwnerRate P X x : ENNReal) : EReal) ≤ -y₀} := by
          have hy₀ :
              y₀ >
                -sInf
                  ((fun x ↦
                    ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' C) := by
            -- Proof comment: the intermediate positive threshold `level` stays strictly below the
            -- owner-rate infimum on `C`, so the comparison value `y₀ = -level` is still
            -- admissible.
            simpa [y₀] using EReal.neg_strictAnti hLevelInf
          exact disjoint_empiricalMeanOwnerRateSublevel_of_lt_neg_sInf
            (P := P) (X := X) hy₀
        have hKDisj : Disjoint C K := by
          simpa [hKeq] using hKdisj
        have hKClosed : IsClosed K := hKshape.1
        have hKConvex : Convex ℝ K := hKshape.2.1
        have hKCases := hKshape.2.2
        have hKne : K.Nonempty := by
          -- Proof comment: the positive-threshold refactor reduces the closed-branch geometry to
          -- a pure owner-rate fact: once the effective domain contains a nonzero tilt, derivative
          -- points close enough to the origin have arbitrarily small owner rate.
          simpa [K] using
            empiricalMeanOwnerRateSublevel_nonempty_of_pos_of_nontrivialIntegrableExpSet
              (P := P) (X := X) hSet hLevelPos
        rcases hKCases with hKempty | hKuniv | hKLeft | hKRight | hKIcc
        · exact False.elim (hKne.ne_empty hKempty)
        · have hFalse : False := by
            rcases hCne with ⟨x, hx⟩
            exact (Set.disjoint_left.1 hKDisj) hx (by simpa [hKuniv])
          exact False.elim hFalse
        · rcases hKLeft with ⟨u, hKu⟩
          rcases closedSet_rightRay_of_disjoint_leftRay hC (by simpa [hKu] using hKDisj) with
            ⟨b, hub, hCover⟩
          have huMem : u ∈ K := by
            simpa [hKu]
          have huRateENN : empiricalMeanOwnerRate P X u ≤ level := huMem
          have huRateE :
              ((empiricalMeanOwnerRate P X u : ENNReal) : EReal) ≤ -y₀ := by
            calc
              ((empiricalMeanOwnerRate P X u : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
                    exact_mod_cast huRateENN
              _ = -y₀ := by
                    simp [y₀]
          have huRate :
              legendreFenchelRateFunction (Λ(X 0; P)) u ≤ -y₀ := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) u)] using
              huRateE
          have hbNotMem : b ∉ K := by
            simpa [hKu] using not_le_of_gt hub
          have hbRateE :
              -y₀ < ((empiricalMeanOwnerRate P X b : ENNReal) : EReal) := by
            calc
              -y₀ = ((level : ENNReal) : EReal) := by
                    simp [y₀]
              _ < ((empiricalMeanOwnerRate P X b : ENNReal) : EReal) := by
                    exact_mod_cast (lt_of_not_ge hbNotMem)
          have hbRate :
              -y₀ < legendreFenchelRateFunction (Λ(X 0; P)) b := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) b)] using
              hbRateE
          rcases exists_nonneg_affineWitness_of_leftRaySublevel
              (P := P) (X := X 0) (a := u) (x := b) (y := y₀) huRate hbRate hub with
            ⟨t, ht, hAffine⟩
          have hMono :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    C)
                  atTop ≤
                Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    (Set.Ici b))
                  atTop := by
            exact Filter.limsup_le_limsup <| Filter.Eventually.of_forall fun n ↦
              scaledLogMassAlong_mono_of_subset
                (μ := fun n ↦
                  (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                (ε := cramerSpeed) hCover n
          have hLimsupLt :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    C)
                  atTop < y₀ := by
            exact hMono.trans_lt <|
              empiricalMeanLaw_closedRightHalfline_limsup_lt_of_neg_affine
                (P := P) (X := X) hX_iid (a := b) (t := t) ht hAffine
          exact (eventually_lt_of_limsup_lt (hLimsupLt.trans hy₀_lt_y)).mono fun _ hn ↦ hn.le
        · rcases hKRight with ⟨v, hKv⟩
          rcases closedSet_leftRay_of_disjoint_rightRay hC (by simpa [hKv] using hKDisj) with
            ⟨a, hav, hCover⟩
          have hvMem : v ∈ K := by
            simpa [hKv]
          have hvRateENN : empiricalMeanOwnerRate P X v ≤ level := hvMem
          have hvRateE :
              ((empiricalMeanOwnerRate P X v : ENNReal) : EReal) ≤ -y₀ := by
            calc
              ((empiricalMeanOwnerRate P X v : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
                    exact_mod_cast hvRateENN
              _ = -y₀ := by
                    simp [y₀]
          have hvRate :
              legendreFenchelRateFunction (Λ(X 0; P)) v ≤ -y₀ := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) v)] using
              hvRateE
          have haNotMem : a ∉ K := by
            simpa [hKv] using not_le_of_gt hav
          have haRateE :
              -y₀ < ((empiricalMeanOwnerRate P X a : ENNReal) : EReal) := by
            calc
              -y₀ = ((level : ENNReal) : EReal) := by
                    simp [y₀]
              _ < ((empiricalMeanOwnerRate P X a : ENNReal) : EReal) := by
                    exact_mod_cast (lt_of_not_ge haNotMem)
          have haRate :
              -y₀ < legendreFenchelRateFunction (Λ(X 0; P)) a := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) a)] using
              haRateE
          rcases exists_nonpos_affineWitness_of_rightRaySublevel
              (P := P) (X := X 0) (x := a) (b := v) (y := y₀) hvRate haRate hav with
            ⟨t, ht, hAffine⟩
          have hMono :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    C)
                  atTop ≤
                Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    (Set.Iic a))
                  atTop := by
            exact Filter.limsup_le_limsup <| Filter.Eventually.of_forall fun n ↦
              scaledLogMassAlong_mono_of_subset
                (μ := fun n ↦
                  (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                (ε := cramerSpeed) hCover n
          have hLimsupLt :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    C)
                  atTop < y₀ := by
            exact hMono.trans_lt <|
              empiricalMeanLaw_closedLeftHalfline_limsup_lt_of_neg_affine
                (P := P) (X := X) hX_iid (a := a) (t := t) ht hAffine
          exact (eventually_lt_of_limsup_lt (hLimsupLt.trans hy₀_lt_y)).mono fun _ hn ↦ hn.le
        · rcases hKIcc with ⟨u, v, huv, hKuv⟩
          rcases closedSet_twoRayCover_of_disjoint_interval hC huv
              (by simpa [hKuv] using hKDisj) with
            ⟨a, b, hau, hvb, hCover⟩
          have huMem : u ∈ K := by
            simpa [hKuv]
          have hvMem : v ∈ K := by
            simpa [hKuv]
          have huRateENN : empiricalMeanOwnerRate P X u ≤ level := huMem
          have hvRateENN : empiricalMeanOwnerRate P X v ≤ level := hvMem
          have huRateE :
              ((empiricalMeanOwnerRate P X u : ENNReal) : EReal) ≤ -y₀ := by
            calc
              ((empiricalMeanOwnerRate P X u : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
                    exact_mod_cast huRateENN
              _ = -y₀ := by
                    simp [y₀]
          have hvRateE :
              ((empiricalMeanOwnerRate P X v : ENNReal) : EReal) ≤ -y₀ := by
            calc
              ((empiricalMeanOwnerRate P X v : ENNReal) : EReal) ≤
                  ((level : ENNReal) : EReal) := by
                    exact_mod_cast hvRateENN
              _ = -y₀ := by
                    simp [y₀]
          have huRate :
              legendreFenchelRateFunction (Λ(X 0; P)) u ≤ -y₀ := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) u)] using
              huRateE
          have hvRate :
              legendreFenchelRateFunction (Λ(X 0; P)) v ≤ -y₀ := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) v)] using
              hvRateE
          have haNotMem : a ∉ K := by
            intro haMem
            rw [hKuv] at haMem
            exact (not_le_of_gt hau) haMem.1
          have hbNotMem : b ∉ K := by
            intro hbMem
            rw [hKuv] at hbMem
            exact (not_le_of_gt hvb) hbMem.2
          have haRateE :
              -y₀ < ((empiricalMeanOwnerRate P X a : ENNReal) : EReal) := by
            calc
              -y₀ = ((level : ENNReal) : EReal) := by
                    simp [y₀]
              _ < ((empiricalMeanOwnerRate P X a : ENNReal) : EReal) := by
                    exact_mod_cast (lt_of_not_ge haNotMem)
          have hbRateE :
              -y₀ < ((empiricalMeanOwnerRate P X b : ENNReal) : EReal) := by
            calc
              -y₀ = ((level : ENNReal) : EReal) := by
                    simp [y₀]
              _ < ((empiricalMeanOwnerRate P X b : ENNReal) : EReal) := by
                    exact_mod_cast (lt_of_not_ge hbNotMem)
          have haRate :
              -y₀ < legendreFenchelRateFunction (Λ(X 0; P)) a := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) a)] using
              haRateE
          have hbRate :
              -y₀ < legendreFenchelRateFunction (Λ(X 0; P)) b := by
            simpa [empiricalMeanOwnerRate,
              EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) b)] using
              hbRateE
          rcases exists_nonpos_affineWitness_of_rightRaySublevel
              (P := P) (X := X 0) (x := a) (b := u) (y := y₀) huRate haRate hau with
            ⟨tLeft, htLeft, hAffineLeft⟩
          rcases exists_nonneg_affineWitness_of_leftRaySublevel
              (P := P) (X := X 0) (a := v) (x := b) (y := y₀) hvRate hbRate hvb with
            ⟨tRight, htRight, hAffineRight⟩
          have hLeft :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    (Set.Iic a))
                  atTop < y₀ := by
            exact empiricalMeanLaw_closedLeftHalfline_limsup_lt_of_neg_affine
              (P := P) (X := X) hX_iid (a := a) (t := tLeft) htLeft hAffineLeft
          have hRight :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    (Set.Ici b))
                  atTop < y₀ := by
            exact empiricalMeanLaw_closedRightHalfline_limsup_lt_of_neg_affine
              (P := P) (X := X) hX_iid (a := b) (t := tRight) htRight hAffineRight
          have hLimsupLt :
              Filter.limsup
                  (scaledLogMassAlong
                    (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
                    cramerSpeed
                    C)
                  atTop < y₀ := by
            exact empiricalMeanLaw_limsup_lt_of_subset_union
              (P := P) (X := X) hX_iid hCover hLeft hRight
          exact (eventually_lt_of_limsup_lt (hLimsupLt.trans hy₀_lt_y)).mono fun _ hn ↦ hn.le

/-- Helper for Theorem 23.11: in the non-singleton branch of the exponential-integrability
domain, nonempty open sets satisfy the owner empirical-mean lower bound once the tilted interval
estimate is available. -/
private theorem empiricalMeanLaw_eventually_gt_of_lt_neg_ownerRate_atDeriv_mem_open
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    {U : Set ℝ} (hU : IsOpen U) {t : ℝ}
    (ht : t ∈ interior (integrableExpSet (X 0) P))
    (htU : deriv (cgf (X 0) P) t ∈ U)
    {y : EReal}
    (hy :
      y <
        -(((empiricalMeanOwnerRate P X (deriv (cgf (X 0) P) t) : ENNReal) : EReal))) :
    ∀ᶠ n : ℕ in atTop,
      y <
        scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          U
          n := by
  let x : ℝ := deriv (cgf (X 0) P) t
  let c : ℝ := t * x - cgf (X 0) P t
  have hRateEq :
      (((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) = ((c : ℝ) : EReal) := by
    -- Proof comment: at derivative points the owner rate is the supporting affine value.
    simpa [empiricalMeanOwnerRate, x, c] using
      empiricalMeanOwnerRate_atDeriv_eq_affine_of_mem_interior (P := P) (X := X) ht
  have hyAffine : y < -((c : ℝ) : EReal) := by
    simpa [x, c, hRateEq] using hy
  rcases exists_Ioo_subset_of_isOpen_mem hU (by simpa [x] using htU) with ⟨δ₀, hδ₀, hδ₀U⟩
  by_cases hyBot : y = ⊥
  · -- Proof comment: if the comparison value is `⊥`, every open window suffices.
    have hLiminf :
        -((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ₀ : ℝ)) : EReal)) ≤
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Ioo (x - δ₀) (x + δ₀)))
            atTop := by
      -- Proof comment: the existing centered tilted-interval lower bound applies directly to the
      -- open window around the derivative point.
      simpa [x] using
        empiricalMeanLaw_centeredOpenInterval_liminf_ge_negAffine_of_interiorTilt
          (P := P) (X := X) hX_iid ht hδ₀
    have hMono :
        Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Ioo (x - δ₀) (x + δ₀)))
            atTop ≤
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              U)
            atTop := by
      exact Filter.liminf_le_liminf <|
        Filter.Eventually.of_forall fun n ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun n ↦
              (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            (ε := cramerSpeed) hδ₀U n
    have hyLiminf :
        y <
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              U)
            atTop := by
      have hFinite' :
          (⊥ : EReal) <
            (((-(|t| * δ₀ + (t * x - cgf (X 0) P t)) : ℝ)) : EReal) := by
        exact EReal.bot_lt_coe _
      have hFiniteEq :
          -((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ₀ : ℝ)) : EReal)) =
            (((-(|t| * δ₀ + (t * x - cgf (X 0) P t)) : ℝ)) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_neg]
        ring
      have hFinite :
          (⊥ : EReal) <
            -((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ₀ : ℝ)) : EReal)) := by
        rw [hFiniteEq]
        exact hFinite'
      rw [hyBot]
      exact lt_of_lt_of_le hFinite (hLiminf.trans hMono)
    exact Filter.eventually_lt_of_lt_liminf hyLiminf
  · rcases EReal.lt_iff_exists_real_btwn.mp hyAffine with ⟨z, hyz, hz⟩
    let η : ℝ := -c - z
    have hη : 0 < η := by
      have hzReal : z < -c := by
        exact EReal.coe_lt_coe_iff.mp <| by simpa using hz
      dsimp [η]
      linarith
    rcases exists_pos_mul_lt hη (|t|) with ⟨δ₁, hδ₁, hδ₁lt⟩
    let δ : ℝ := min δ₀ δ₁
    have hδ : 0 < δ := by
      exact lt_min hδ₀ hδ₁
    have hδU :
        Set.Ioo (x - δ) (x + δ) ⊆ U := by
      -- Proof comment: shrinking the open window preserves inclusion in `U`.
      intro u hu
      apply hδ₀U
      refine ⟨?_, ?_⟩ <;> linarith [min_le_left δ₀ δ₁, hu.1, hu.2]
    have hScaleLt : |t| * δ < η := by
      have hδLe : δ ≤ δ₁ := min_le_right _ _
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδLe (abs_nonneg t)) hδ₁lt
    have hyWindow :
        y <
          -((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) := by
      have hzEq :
          (z : EReal) = -(((c + η : ℝ)) : EReal) := by
        have hzEqReal : z = -(c + η) := by
          dsimp [η]
          ring
        exact_mod_cast hzEqReal
      have hyη : y < -(((c + η : ℝ)) : EReal) := by
        -- Proof comment: choose a slightly smaller affine target still above `y`.
        exact hyz.trans_eq hzEq
      have hCostLe : c + |t| * δ ≤ c + η := by
        linarith
      have hNegLe :
          -(((c + η : ℝ)) : EReal) ≤ -(((c + |t| * δ : ℝ)) : EReal) := by
        exact EReal.neg_le_neg_iff.mpr <| by exact_mod_cast hCostLe
      exact hyη.trans_le <| by
        simpa [c, x, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hNegLe
    have hLiminf :
        -((((t * x - cgf (X 0) P t : ℝ)) : EReal) + (((|t| * δ : ℝ)) : EReal)) ≤
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Ioo (x - δ) (x + δ)))
            atTop := by
      -- Proof comment: once the affine window fits inside `U`, the tilted interval lower bound
      -- provides the needed `liminf` estimate.
      simpa [x] using
        empiricalMeanLaw_centeredOpenInterval_liminf_ge_negAffine_of_interiorTilt
          (P := P) (X := X) hX_iid ht hδ
    have hMono :
        Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              (Set.Ioo (x - δ) (x + δ)))
            atTop ≤
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              U)
            atTop := by
      exact Filter.liminf_le_liminf <|
        Filter.Eventually.of_forall fun n ↦
          scaledLogMassAlong_mono_of_subset
            (μ := fun n ↦
              (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            (ε := cramerSpeed) hδU n
    have hyLiminf :
        y <
          Filter.liminf
            (scaledLogMassAlong
              (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
              cramerSpeed
              U)
            atTop := by
      exact hyWindow.trans_le (hLiminf.trans hMono)
    exact Filter.eventually_lt_of_lt_liminf hyLiminf

/-- Helper for Theorem 23.11: in the non-singleton branch of the exponential-integrability
domain, nonempty open sets satisfy the owner empirical-mean lower bound once the tilted interval
estimate is available. -/
private theorem cgfDerivImage_ordConnectedOnInteriorIntegrableExpSet
    (P : Measure Ω) (X : ℕ → Ω → ℝ) :
    Set.OrdConnected
      (deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P)) := by
  have hOrd :
      Set.OrdConnected (interior (integrableExpSet (X 0) P)) := by
    simpa using
      (convex_integrableExpSet (X := X 0) (μ := P)).interior.ordConnected
  have hDiff :
      ∀ t ∈ interior (integrableExpSet (X 0) P), DifferentiableAt ℝ (cgf (X 0) P) t := by
    intro t ht
    -- Proof comment: analyticity of `cgf` on the interior effective domain provides the
    -- differentiability needed for Darboux.
    exact (analyticAt_cgf (X := X 0) (μ := P) ht).differentiableAt
  -- Proof comment: Darboux turns the derivative image of an interval into an interval again.
  exact hOrd.image_deriv hDiff

/-- Helper for Theorem 23.11: once two interior tilts bracket a target derivative value, Darboux
produces an interior tilt whose derivative is exactly that target. -/
private theorem existsInteriorTilt_eq_of_betweenDerivValues
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    {s t x0 : ℝ}
    (hs : s ∈ interior (integrableExpSet (X 0) P))
    (ht : t ∈ interior (integrableExpSet (X 0) P))
    (hx0 :
      deriv (cgf (X 0) P) s ≤ x0 ∧ x0 ≤ deriv (cgf (X 0) P) t ∨
        deriv (cgf (X 0) P) t ≤ x0 ∧ x0 ≤ deriv (cgf (X 0) P) s) :
    ∃ u, u ∈ interior (integrableExpSet (X 0) P) ∧ deriv (cgf (X 0) P) u = x0 := by
  have hImage :
      Set.OrdConnected
        (deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P)) :=
    cgfDerivImage_ordConnectedOnInteriorIntegrableExpSet (P := P) (X := X)
  have hsImage :
      deriv (cgf (X 0) P) s ∈
        deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P) := by
    exact ⟨s, hs, rfl⟩
  have htImage :
      deriv (cgf (X 0) P) t ∈
        deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P) := by
    exact ⟨t, ht, rfl⟩
  rcases hx0 with hst | hts
  · have hx0Image :
        x0 ∈ deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P) := by
      exact hImage.out hsImage htImage hst
    rcases hx0Image with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩
  · have hx0Image :
        x0 ∈ deriv (cgf (X 0) P) '' interior (integrableExpSet (X 0) P) := by
      exact hImage.out htImage hsImage hts
    rcases hx0Image with ⟨u, hu, rfl⟩
    exact ⟨u, hu, rfl⟩

/-- Helper for Theorem 23.11: every interior point of a real set admits smaller and larger points
of the same set. -/
private theorem exists_lt_mem_and_mem_lt_of_mem_interior
    {s : Set ℝ} {x : ℝ} (hx : x ∈ interior s) :
    ∃ a b, a < x ∧ x < b ∧ a ∈ s ∧ b ∈ s := by
  rcases exists_Ioo_subset_of_isOpen_mem isOpen_interior hx with ⟨δ, hδ, hδs⟩
  refine ⟨x - δ / 2, x + δ / 2, by linarith, by linarith, ?_, ?_⟩
  · exact interior_subset <| hδs ⟨by linarith, by linarith⟩
  · exact interior_subset <| hδs ⟨by linarith, by linarith⟩

/-- Helper for Theorem 23.11: membership in a finite owner-rate sublevel forces the Legendre
transform to be finite at that point. -/
private theorem legendreFenchelRateFunction_ne_top_of_mem_empiricalMeanOwnerRateSublevel
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    {a : ENNReal} (ha : a ≠ ⊤) {x : ℝ}
    (hx : empiricalMeanOwnerRate P X x ≤ a) :
    legendreFenchelRateFunction (Λ(X 0; P)) x ≠ ⊤ := by
  -- Proof comment: if the Legendre transform were `⊤`, its `toENNReal` coercion would also be
  -- `⊤`, contradicting membership in the finite sublevel.
  intro hTop
  have hTopLe : (⊤ : ENNReal) ≤ a := by
    simpa [empiricalMeanOwnerRate, hTop] using hx
  exact ha (top_le_iff.mp hTopLe)

/-- Helper for Theorem 23.11: a finite owner-rate sublevel cannot be all of `ℝ` once the
effective domain contains a nonzero tilt. -/
private theorem empiricalMeanOwnerRateSublevel_ne_univ_of_nontrivialIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {a : ENNReal} (ha : a ≠ ⊤) :
    {z : ℝ | empiricalMeanOwnerRate P X z ≤ a} ≠ Set.univ := by
  let S : Set ℝ := integrableExpSet (X 0) P
  have hZero : (0 : ℝ) ∈ S := by
    simp [S, integrableExpSet]
  have hNontrivial : S.Nontrivial := by
    exact (Set.eq_singleton_or_nontrivial hZero).resolve_left hSet
  rcases hNontrivial.exists_ne (0 : ℝ) with ⟨τ, hτS, hτne⟩
  let x : ℝ := (cgf (X 0) P τ + a.toReal + 1) / τ
  have hAffineEq : τ * x - cgf (X 0) P τ = a.toReal + 1 := by
    -- Proof comment: choose `x` so that the affine summand at the nonzero admissible tilt `τ`
    -- lands exactly one unit above the finite level `a`.
    have hMul : τ * x = cgf (X 0) P τ + a.toReal + 1 := by
      dsimp [x]
      field_simp [hτne]
    linarith
  have hAffineLeRate :
      (((a.toReal + 1 : ℝ)) : EReal) ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
    calc
      (((a.toReal + 1 : ℝ)) : EReal) = (((τ * x - cgf (X 0) P τ : ℝ)) : EReal) := by
        exact_mod_cast hAffineEq.symm
      _ = ((((τ * x : ℝ) : EReal) - Λ(X 0; P) τ)) := by
        rw [extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
          (X := X 0) (P := P) hτS]
        simp [EReal.coe_sub]
      _ ≤ legendreFenchelRateFunction (Λ(X 0; P)) x := by
        exact affineSummand_le_legendreFenchelRateFunction (P := P) (X := X 0)
  have haLt :
      ((a : ENNReal) : EReal) < (((a.toReal + 1 : ℝ)) : EReal) := by
    have haReal : (a.toReal : ℝ) < a.toReal + 1 := by
      linarith
    have haCast : ((a : ENNReal) : EReal) = (((a.toReal : ℝ)) : EReal) := by
      rw [show a = ENNReal.ofReal a.toReal by
        exact (ENNReal.ofReal_toReal ha).symm]
      simp
    rw [haCast]
    exact_mod_cast haReal
  have hxNotMem : x ∉ {z : ℝ | empiricalMeanOwnerRate P X z ≤ a} := by
    intro hxMem
    have hRateLe :
        legendreFenchelRateFunction (Λ(X 0; P)) x ≤ ((a : ENNReal) : EReal) := by
      have hRateLeToENN :
          ((((legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal : ENNReal) : EReal)) ≤
            ((a : ENNReal) : EReal) := by
        exact_mod_cast hxMem
      simpa [empiricalMeanOwnerRate,
        EReal.coe_toENNReal (legendreFenchelRateFunction_nonneg (P := P) (X := X) x)] using
        hRateLeToENN
    exact (not_lt_of_ge hRateLe) (haLt.trans_le hAffineLeRate)
  intro hUniv
  exact hxNotMem (by simpa [hUniv] using (show x ∈ (Set.univ : Set ℝ) by simp))

/-- Helper for Theorem 23.11: in the non-singleton branch of the exponential-integrability
domain, interior points of finite owner-rate sublevels admit interior local minimizers of the
affine-gap function `s ↦ cgf s - x₀ s`. -/
private theorem existsInteriorTilt_localMinCgfMinusLinear_of_mem_interiorOwnerRateSublevel
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {a : ENNReal} (ha : a ≠ ⊤) {x0 : ℝ}
    (hx0 :
      x0 ∈ interior {z : ℝ | empiricalMeanOwnerRate P X z ≤ a}) :
    ∃ t, t ∈ interior (integrableExpSet (X 0) P) ∧
      IsLocalMin (fun s : ℝ ↦ cgf (X 0) P s - x0 * s) t := by
  -- Route correction: the main theorem no longer asks for a derivative witness already lying in
  -- `U`; the new pivot is to build an interior local minimizer of the affine-gap function and
  -- then differentiate it in a separate bridge lemma.
  have hKneUniv :
      {z : ℝ | empiricalMeanOwnerRate P X z ≤ a} ≠ Set.univ :=
    empiricalMeanOwnerRateSublevel_ne_univ_of_nontrivialIntegrableExpSet
      (P := P) (X := X) hSet ha
  rcases exists_lt_mem_and_mem_lt_of_mem_interior hx0 with ⟨xL, xR, hxL, hxR, _hxLK, _hxRK⟩
  -- Proof comment: the remaining work is now reduced to a two-sided derivative bracketing
  -- problem. The new Darboux helper will close the goal as soon as two interior tilts with
  -- derivatives on opposite sides of `x0` are constructed.
  -- TODO: split by the interval shape of `{z | empiricalMeanOwnerRate P X z ≤ a}` and use the
  -- monotone Darboux image of `deriv (cgf (X 0) P)` on `interior (integrableExpSet (X 0) P)` to
  -- recover a tilt whose derivative equals `x0`.
  have hx0Finite :
      legendreFenchelRateFunction (Λ(X 0; P)) x0 ≠ ⊤ := by
    have hx0Mem : x0 ∈ {z : ℝ | empiricalMeanOwnerRate P X z ≤ a} := interior_subset hx0
    exact legendreFenchelRateFunction_ne_top_of_mem_empiricalMeanOwnerRateSublevel
      (P := P) (X := X) ha hx0Mem
  have hKshape :
      let K : Set ℝ := {z : ℝ | empiricalMeanOwnerRate P X z ≤ a}
      IsClosed K ∧ Convex ℝ K ∧
        (K = ∅ ∨ K = Set.univ ∨ (∃ u, K = Set.Iic u) ∨ (∃ v, K = Set.Ici v) ∨
          ∃ u v, u ≤ v ∧ K = Set.Icc u v) := by
    simpa [empiricalMeanOwnerRate] using empiricalMeanOwnerRateSublevel_shape
      (P := P) (X := X) a
  have hKnonempty :
      ({z : ℝ | empiricalMeanOwnerRate P X z ≤ a} : Set ℝ).Nonempty := by
    exact ⟨x0, interior_subset hx0⟩
  have hKnotEmpty :
      ({z : ℝ | empiricalMeanOwnerRate P X z ≤ a} : Set ℝ) ≠ ∅ := hKnonempty.ne_empty
  -- Proof comment: the corrected finite-level hypotheses already eliminate the bogus `K = univ`
  -- branch that made the previous statement false at `a = ⊤`.
  have hKnotUniv : ({z : ℝ | empiricalMeanOwnerRate P X z ≤ a} : Set ℝ) ≠ Set.univ := hKneUniv
  let K : Set ℝ := {z : ℝ | empiricalMeanOwnerRate P X z ≤ a}
  have hKnotTop := hx0Finite
  -- TODO: choose a compact interval inside `interior (integrableExpSet (X 0) P)` whose endpoint
  -- affine-gap values are larger than an interior reference value, apply `IsCompact.exists_isMinOn`
  -- on that interval, and then show the minimizer lies in the interior by the strict witnesses
  -- `xL < x0 < xR`.
  sorry

/-- Helper for Theorem 23.11: in the non-singleton branch of the exponential-integrability
domain, interior points of finite owner-rate sublevels are the derivative points of interior
tilts. -/
private theorem existsInteriorTilt_eq_of_mem_interiorOwnerRateSublevel
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hSet : integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {a : ENNReal} (ha : a ≠ ⊤) {x0 : ℝ}
    (hx0 :
      x0 ∈ interior {z : ℝ | empiricalMeanOwnerRate P X z ≤ a}) :
    ∃ t, t ∈ interior (integrableExpSet (X 0) P) ∧ deriv (cgf (X 0) P) t = x0 := by
  -- Route correction: the inverse-gradient step now factors through an affine-gap local minimum,
  -- so this lemma only rewrites the derivative of `cgf - x₀·`.
  rcases existsInteriorTilt_localMinCgfMinusLinear_of_mem_interiorOwnerRateSublevel
      (P := P) (X := X) hSet ha hx0 with ⟨t, ht, hMin⟩
  have hDiff : DifferentiableAt ℝ (cgf (X 0) P) t := by
    -- Proof comment: analyticity of `cgf` on the interior effective domain provides the
    -- differentiability needed to differentiate the affine-gap function at the minimizer.
    exact (analyticAt_cgf (X := X 0) (μ := P) ht).differentiableAt
  have hDeriv :
      HasDerivAt
        (fun s : ℝ ↦ cgf (X 0) P s - x0 * s)
        (deriv (cgf (X 0) P) t - x0) t := by
    -- Proof comment: differentiate `cgf` and the linear correction separately, then subtract the
    -- resulting derivatives.
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (hDiff.hasDerivAt.sub ((hasDerivAt_id t).const_mul x0))
  have hZero : deriv (fun s : ℝ ↦ cgf (X 0) P s - x0 * s) t = 0 := hMin.deriv_eq_zero
  have hRewrite :
      deriv (fun s : ℝ ↦ cgf (X 0) P s - x0 * s) t =
        deriv (cgf (X 0) P) t - x0 := hDeriv.deriv
  refine ⟨t, ht, ?_⟩
  rw [hRewrite] at hZero
  linarith

/-- Helper for Theorem 23.11: in the non-singleton branch of the exponential-integrability
domain, nonempty open sets satisfy the owner empirical-mean lower bound once the localized
inverse-gradient step is available. -/
private theorem empiricalMeanLaw_open_lower_bound_of_nontrivialIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hSet :
      integrableExpSet (X 0) P ≠ ({0} : Set ℝ))
    {U : Set ℝ} (hUNonempty : U.Nonempty) (hU : IsOpen U) :
    -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' U) ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          U)
        atTop := by
  rw [Filter.le_liminf_iff']
  intro y hy
  rcases exists_mem_lt_neg_empiricalMeanOwnerRate_of_lt_neg_sInf
      (P := P) (X := X) hUNonempty (by simpa [empiricalMeanOwnerRate] using hy) with
      ⟨x, hxU, hxRate⟩
  have hxRate' : y < -(((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) := by
    simpa [empiricalMeanOwnerRate] using hxRate
  have hRateNonneg :
      (0 : EReal) ≤ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal) := by
    exact_mod_cast
      (show (0 : ENNReal) ≤ empiricalMeanOwnerRate P X x from bot_le)
  have hyNeg : y < 0 := by
    have hNegNonpos :
        -(((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) ≤ (0 : EReal) := by
      simpa using EReal.neg_le_neg_iff.mpr hRateNonneg
    exact lt_of_lt_of_le hxRate' hNegNonpos
  have hRateTop : empiricalMeanOwnerRate P X x ≠ ⊤ := by
    intro hTop
    simpa [hTop] using hxRate'
  rcases EReal.lt_iff_exists_real_btwn.mp hxRate' with ⟨z, hyz, hzRate⟩
  let level : ENNReal := ENNReal.ofReal (-z)
  have hLevel : 0 < level := by
    have hNegNonpos :
        -(((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) ≤ (0 : EReal) := by
      simpa using EReal.neg_le_neg_iff.mpr hRateNonneg
    have hzReal : z < 0 := EReal.coe_lt_coe_iff.mp <| lt_of_lt_of_le hzRate hNegNonpos
    dsimp [level]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hLevelEq :
      (((level : ENNReal) : EReal)) = (((-z : ℝ)) : EReal) := by
    have hzReal : z < 0 := EReal.coe_lt_coe_iff.mp <| by
      have hNegNonpos :
          -(((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) ≤ (0 : EReal) := by
        simpa using EReal.neg_le_neg_iff.mpr hRateNonneg
      exact lt_of_lt_of_le hzRate hNegNonpos
    dsimp [level]
    simp [hzReal.le]
  have hzEq : (z : EReal) = -((level : ENNReal) : EReal) := by
    calc
      (z : EReal) = -(((-z : ℝ)) : EReal) := by
        exact_mod_cast (neg_neg z).symm
      _ = -((level : ENNReal) : EReal) := by rw [hLevelEq]
  have hxLevel :
      (((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) < ((level : ENNReal) : EReal) := by
    exact EReal.neg_lt_neg_iff.mp <| by simpa [hzEq] using hzRate
  rcases existsInteriorTilt_ownerRate_lt_of_pos_of_nontrivialIntegrableExpSet
      (P := P) (X := X) hSet hLevel with ⟨tLow, htLow, hRateLow⟩
  have hyLevel :
      y < -((level : ENNReal) : EReal) := by
    exact hyz.trans_eq hzEq
  let xLow : ℝ := deriv (cgf (X 0) P) tLow
  have hyRateLow :
      y < -(((empiricalMeanOwnerRate P X xLow : ENNReal) : EReal)) := by
    -- Proof comment: the strict companion lemma makes the derivative witness live below the
    -- chosen intermediate threshold.
    exact hyLevel.trans <|
      EReal.neg_lt_neg_iff.mpr <| by simpa [xLow] using hRateLow
  -- Proof comment: the `-sInf` comparison now yields both an open-set witness `x ∈ U` and,
  -- independently, an interior tilt with sufficiently small owner rate. The remaining blocker is
  -- purely geometric: force a low-rate derivative point to stay in the same open component of `U`
  -- as `x`.
  by_cases htLowU : xLow ∈ U
  · exact empiricalMeanLaw_eventually_gt_of_lt_neg_ownerRate_atDeriv_mem_open
      (P := P) (X := X) hX_iid hU htLow htLowU hyRateLow |>.mono fun _ hn ↦ hn.le
  let K : Set ℝ := {z : ℝ | empiricalMeanOwnerRate P X z ≤ level}
  have hxK : x ∈ K := by
    -- Proof comment: the open-set witness `x` belongs to the intermediate owner-rate sublevel by
    -- construction of `level`.
    dsimp [K]
    exact_mod_cast hxLevel.le
  have hxLowK : xLow ∈ K := by
    -- Proof comment: the derivative witness also lies in the same sublevel because its owner rate
    -- is strictly below `level`.
    dsimp [K, xLow]
    exact_mod_cast hRateLow.le
  have hxLowNe : xLow ≠ x := by
    intro hEq
    apply htLowU
    simpa [xLow, hEq] using hxU
  rcases exists_Ioo_subset_of_isOpen_mem hU hxU with ⟨δ, hδ, hδU⟩
  have hInteriorWitness : ∃ x0 ∈ U, x0 ∈ interior K := by
    by_cases hxxLow : x < xLow
    · let b : ℝ := min (x + δ) xLow
      have hxb : x < b := by
        dsimp [b]
        exact lt_min (by linarith) hxxLow
      rcases exists_between hxb with ⟨x0, hx0Left, hx0Right⟩
      have hx0U : x0 ∈ U := by
        refine hδU ?_
        refine ⟨?_, ?_⟩
        · linarith
        · exact lt_of_lt_of_le hx0Right (min_le_left _ _)
      have hx0Int : x0 ∈ interior K := by
        have hx0Seg : x0 ∈ Set.Ioo x xLow := ⟨hx0Left, lt_of_lt_of_le hx0Right (min_le_right _ _)⟩
        simpa [K] using
          mem_interior_ownerRateSublevel_of_mem_of_mem_of_between
            (P := P) (X := X) hxK hxLowK hxxLow hx0Seg
      exact ⟨x0, hx0U, hx0Int⟩
    · have hxLowx : xLow < x := lt_of_le_of_ne (le_of_not_gt hxxLow) hxLowNe
      let b : ℝ := max (x - δ) xLow
      have hbx : b < x := by
        dsimp [b]
        exact max_lt (by linarith) hxLowx
      rcases exists_between hbx with ⟨x0, hx0Left, hx0Right⟩
      have hx0U : x0 ∈ U := by
        refine hδU ?_
        refine ⟨?_, ?_⟩
        · exact lt_of_le_of_lt (le_max_left _ _) hx0Left
        · linarith
      have hx0Int : x0 ∈ interior K := by
        have hx0Seg : x0 ∈ Set.Ioo xLow x := ⟨lt_of_le_of_lt (le_max_right _ _) hx0Left, hx0Right⟩
        simpa [K] using
          mem_interior_ownerRateSublevel_of_mem_of_mem_of_between
            (P := P) (X := X) hxLowK hxK hxLowx hx0Seg
      exact ⟨x0, hx0U, hx0Int⟩
  rcases hInteriorWitness with ⟨x0, hx0U, hx0Int⟩
  rcases existsInteriorTilt_eq_of_mem_interiorOwnerRateSublevel
      (P := P) (X := X) hSet ENNReal.ofReal_ne_top hx0Int with ⟨t, ht, htEq⟩
  have hx0Level :
      (((empiricalMeanOwnerRate P X x0 : ENNReal) : EReal)) ≤ ((level : ENNReal) : EReal) := by
    have hx0K : x0 ∈ K := interior_subset hx0Int
    dsimp [K] at hx0K
    exact_mod_cast hx0K
  have hyx0 :
      y < -(((empiricalMeanOwnerRate P X x0 : ENNReal) : EReal)) := by
    exact hyLevel.trans_le (EReal.neg_le_neg_iff.mpr hx0Level)
  have htU : deriv (cgf (X 0) P) t ∈ U := by
    simpa [htEq] using hx0U
  have hyt :
      y <
        -(((empiricalMeanOwnerRate P X (deriv (cgf (X 0) P) t) : ENNReal) : EReal)) := by
    simpa [htEq] using hyx0
  exact empiricalMeanLaw_eventually_gt_of_lt_neg_ownerRate_atDeriv_mem_open
      (P := P) (X := X) hX_iid hU ht htU hyt |>.mono fun _ hn ↦ hn.le

/-- Helper for Theorem 23.11: in the singleton exponential-integrability branch, nonempty open
intervals satisfy the exact eventual exponential-mass lower bound used by the public open-set
argument. -/
private theorem singletonIntervalCore_eventually_expNegLinear_le
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hSet : integrableExpSet (X 0) P = ({0} : Set ℝ))
    {x δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-ε * (n + 1 : ℝ))) ≤
        ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (Set.Ioo (x - δ) (x + δ)) := by
  -- Route correction: keep the singleton branch behind one exact interval interface instead of
  -- mixing the bounded-core and steering pieces into the public lower-bound proof.
  -- TODO: prove the interval estimate by combining a bounded-core concentration block with a
  -- one-coordinate steering window, both specialized to `integrableExpSet (X 0) P = {0}`.
  sorry

/-- Helper for Theorem 23.11: in the singleton exponential-integrability branch, nonempty open
sets satisfy the owner empirical-mean lower bound once the interval half-mass estimate is
supplied. -/
private theorem empiricalMeanLaw_openInterval_eventually_expNegLinear_le_of_singletonIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hSet : integrableExpSet (X 0) P = ({0} : Set ℝ))
    {x δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (Real.exp (-ε * (n + 1 : ℝ))) ≤
        ((empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (Set.Ioo (x - δ) (x + δ)) := by
  -- Proof comment: the public singleton theorem is now a thin adapter over the isolated
  -- interval-core estimate, so the liminf proof above no longer depends on its internal
  -- decomposition.
  exact singletonIntervalCore_eventually_expNegLinear_le
    (P := P) (X := X) hX_iid hSet hδ hε

/-- Helper for Theorem 23.11: in the singleton exponential-integrability branch, nonempty open
sets satisfy the owner empirical-mean lower bound once the interval exponential-mass estimate is
available. -/
private theorem empiricalMeanLaw_open_lower_bound_of_singletonIntegrableExpSet
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P)
    (hSet :
      integrableExpSet (X 0) P = ({0} : Set ℝ))
    {U : Set ℝ} (hUNonempty : U.Nonempty) (hU : IsOpen U) :
    -sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' U) ≤
      Filter.liminf
        (scaledLogMassAlong
          (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          cramerSpeed
          U)
        atTop := by
  have hRateInf :
      sInf ((fun x ↦ ((empiricalMeanOwnerRate P X x : ENNReal) : EReal)) '' U) = 0 := by
    -- Proof comment: in the singleton-domain branch the owner rate vanishes pointwise, so every
    -- nonempty image has infimum `0`.
    simpa [empiricalMeanOwnerRate] using
      ownerRateImage_sInf_eq_zero_of_nonempty_of_integrableExpSet_eq_singleton_zero
        (P := P) (X := X 0) hSet hUNonempty
  rw [hRateInf, neg_zero]
  rcases hUNonempty with ⟨x, hxU⟩
  rcases exists_Ioo_subset_of_isOpen_mem hU hxU with ⟨δ, hδ, hδU⟩
  have hMono :
      Filter.liminf
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            (Set.Ioo (x - δ) (x + δ)))
          atTop ≤
        Filter.liminf
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            U)
          atTop := by
    -- Proof comment: once a smaller open interval is inside `U`, monotonicity lifts its `liminf`
    -- lower bound to the target set.
    exact Filter.liminf_le_liminf <|
      Filter.Eventually.of_forall fun n ↦
        scaledLogMassAlong_mono_of_subset
          (μ := fun n ↦
            (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
          (ε := cramerSpeed) hδU n
  have hInterval :
      0 ≤
        Filter.liminf
          (scaledLogMassAlong
            (fun n ↦ (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid) n : Measure ℝ))
            cramerSpeed
            (Set.Ioo (x - δ) (x + δ)))
          atTop := by
    -- Proof comment: the singleton-domain branch now delegates all large-scale interval mass
    -- geometry to the exact exponential lower-bound interface.
    refine scaledLogMassAlong_liminf_nonneg_of_eventually_expNegLinear_le ?_
    intro ε hε
    exact empiricalMeanLaw_openInterval_eventually_expNegLinear_le_of_singletonIntegrableExpSet
      (P := P) (X := X) hX_iid hSet hδ hε
  exact hInterval.trans hMono

-- Proof comment: this shim only restores the owner theorem interface needed by
-- `Example_23_10`; the full proof remains in the dedicated theorem file under repair.
/-- Theorem 23.11: shim interface exporting the owner empirical-mean Cramér theorem used by
Example 23.10. -/
theorem cramer_empiricalMean_largeDeviationPrinciple
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) :
    HasLargeDeviationsPrincipleAlong
      (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid))
      (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
        have hn : 0 < (n + 1 : ℝ) := by
          positivity
        simpa using inv_pos.mpr hn⟩)
      atTop
      (fun x ↦ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal) := by
  -- Route correction: the local duplicate `Λ` and Legendre-Fenchel definitions blocked reuse of
  -- the canonical Chapter 23 API, so the remaining proof should be assembled on the imported
  -- owner surface.
  refine
    { lowerSemicontinuous := ?_
      open_lower_bound := ?_
      closed_upper_bound := ?_ }
  · -- Proof comment: the owner rate is lower semicontinuous by direct Legendre-Fenchel convexity.
    simpa [empiricalMeanOwnerRate] using ownerRate_lowerSemicontinuous (P := P) (X := X 0)
  · intro U hU
    by_cases hUNonempty : U.Nonempty
    · -- Proof comment: the open branch splits according to whether the one-letter exponential
      -- domain is degenerate or not.
      by_cases hSet : integrableExpSet (X 0) P = ({0} : Set ℝ)
      · exact empiricalMeanLaw_open_lower_bound_of_singletonIntegrableExpSet
          (P := P) (X := X) hX_iid hSet hUNonempty hU
      · exact empiricalMeanLaw_open_lower_bound_of_nontrivialIntegrableExpSet
          (P := P) (X := X) hX_iid hSet hUNonempty hU
    · -- Proof comment: the empty open set gives the trivial lower bound `⊥ ≤ liminf`.
      have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hUNonempty
      subst hUempty
      simp
  · intro C hC
    -- Proof comment: the closed branch is isolated in a theorem-sized package so the main owner
    -- proof remains flat.
    simpa [empiricalMeanOwnerRate, cramerSpeed] using
      empiricalMeanLaw_closed_upper_bound (P := P) (X := X) hX_iid hC

end ProbabilityTheory
