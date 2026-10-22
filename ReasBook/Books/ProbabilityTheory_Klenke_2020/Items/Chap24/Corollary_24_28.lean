/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_3_1
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {n : ℕ}

/-- The terminal time `t_n = ∑_{j=1}^n θ_j` attached to the parameter vector `θ`. -/
def dirichletTerminalTime (θ : Fin n → NNReal) : NNReal :=
  ∑ i, θ i

/-- The cumulative times `t_i = ∑_{j=1}^i θ_j`, with `t_0 = 0`, attached to the parameter vector
`θ`. -/
def dirichletCumulativeTimes (θ : Fin n → NNReal) : Fin (n + 1) → NNReal :=
  fun i ↦
    ∑ j : Fin i.1,
      θ (Fin.castLT j (Nat.lt_of_lt_of_le j.2 (Nat.lt_succ_iff.mp i.2)))

/-- The increment `M_{t_i} - M_{t_{i-1}}` along the cumulative times determined by `θ`. -/
def gammaCumulativeIncrement
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) (i : Fin n) : Ω → ℝ :=
  fun ω ↦
    M (dirichletCumulativeTimes θ i.succ) ω -
      M (dirichletCumulativeTimes θ i.castSucc) ω

/-- The normalized increment vector
`((M_{t_i} - M_{t_{i-1}}) / M_{t_n})_{i=1}^n`. -/
def dirichletNormalizedIncrementVector
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) : Ω → Fin n → ℝ :=
  fun ω i ↦ gammaCumulativeIncrement θ M i ω / M (dirichletTerminalTime θ) ω

/-- The pair consisting of the normalized increment vector and the terminal value `M_{t_n}`. -/
def dirichletNormalizedIncrementPair
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) : Ω → (Fin n → ℝ) × ℝ :=
  fun ω ↦ (dirichletNormalizedIncrementVector θ M ω, M (dirichletTerminalTime θ) ω)

-- Proof sketch: unfold `dirichletNormalizedIncrementPair`; the two coordinates are, by
-- definition, the normalized increment vector and the terminal value `M_{t_n}`.
omit [MeasurableSpace Ω] in
/-- Unfolding `dirichletNormalizedIncrementPair` recovers the pair `(X, S)` from the source
corollary. -/
theorem dirichletNormalizedIncrementPair_def
    (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) :
    dirichletNormalizedIncrementPair θ M =
      fun ω ↦
        (dirichletNormalizedIncrementVector θ M ω, M (dirichletTerminalTime θ) ω) := by
  -- Proof comment: `dirichletNormalizedIncrementPair` is defined by this pair of coordinates.
  rfl

section Corollary2428

variable {P : ProbabilityMeasure Ω}
variable (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ)

/-- Helper for Corollary 24.28: the unit-rate Gamma measure with zero shape is the zero measure. -/
private theorem gammaMeasure_zero_shape_eq_zero :
    ProbabilityTheory.gammaMeasure (0 : ℝ) 1 = 0 := by
  -- Proof comment: after `Gamma 0 = 0`, the density vanishes pointwise on every measurable set.
  ext s hs
  simp [ProbabilityTheory.gammaMeasure, ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal,
    Real.Gamma_zero, hs]

/-- Helper for Corollary 24.28: a Gamma law coming from a probability source has strictly
positive shape. -/
private theorem gammaShapePos_of_hasLawUnitRate
    {X : Ω → ℝ} {a : NNReal}
    (hX : HasLaw X (ProbabilityTheory.gammaMeasure (a : ℝ) 1) (P : Measure Ω)) :
    0 < (a : ℝ) := by
  -- Proof comment: `HasLaw` transfers the probability-measure property to the target Gamma law,
  -- ruling out the degenerate zero-shape case.
  by_cases hzero : a = 0
  · have hprob : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (a : ℝ) 1) :=
      hX.isProbabilityMeasure_iff.mp inferInstance
    have huniv : (ProbabilityTheory.gammaMeasure (a : ℝ) 1) Set.univ = 1 := hprob.measure_univ
    rw [hzero] at huniv
    have : False := by
      simp [gammaMeasure_zero_shape_eq_zero] at huniv
    exact False.elim this
  · exact_mod_cast (show 0 < a from pos_iff_ne_zero.mpr hzero)

/-- Helper for Corollary 24.28: finite telescoping over successive `Fin` indices leaves only the
last value minus the first value. -/
private theorem sum_succ_sub_castSucc_eq_last_sub_zero {α : Type*} [AddCommGroup α]
    {m : ℕ} (f : Fin (m + 1) → α) :
    (∑ i : Fin m, (f i.succ - f i.castSucc)) = f (Fin.last m) - f 0 := by
  induction m with
  | zero =>
      -- Proof comment: the empty sum telescopes trivially.
      simp
  | succ m ih =>
      -- Proof comment: split off the final edge, rewrite the head block as the same telescope for
      -- the prefix function `i ↦ f i.castSucc`, and then cancel the middle terms.
      rw [Fin.sum_univ_castSucc]
      have hhead :
          (∑ x : Fin m, (f x.castSucc.succ - f x.castSucc.castSucc)) =
            (∑ x : Fin m,
              (((fun i : Fin (m + 1) ↦ f i.castSucc) x.succ) -
                ((fun i : Fin (m + 1) ↦ f i.castSucc) x.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rfl
      rw [hhead, ih (fun i : Fin (m + 1) ↦ f i.castSucc)]
      simp

/-- Helper for Corollary 24.28: splitting off the last Gamma coordinate factors the finite
Gamma-product source into the prefix product and the last marginal. -/
private theorem map_piGamma_splitLast_eq_prod {m : ℕ} (η : Fin (m + 1) → NNReal)
    (hη : ∀ i, 0 < (η i : ℝ)) :
    ((Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1).map
      (fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m)))) =
      (Measure.pi fun i : Fin m ↦ ProbabilityTheory.gammaMeasure (η i.castSucc : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (η (Fin.last m) : ℝ) 1) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1
  let splitLast : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
    fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m))
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) (Fin.last m)
  have hMapEq :
      (Measure.pi μ).map e =
        (μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)) :=
    (measurePreserving_piFinSuccAbove μ (Fin.last m)).map_eq
  have hSplitLast : splitLast = Prod.swap ∘ e := by
    -- Proof comment: for `Fin.last`, `succAbove` is `castSucc`, so the measurable equivalence
    -- exposes the prefix coordinates together with the final one.
    funext x
    ext i
    · simp [splitLast, Function.comp, e, Fin.init]
    · simp [splitLast, Function.comp, e]
  -- Proof comment: factor through `piFinSuccAbove`, then swap the product factors into the
  -- desired order.
  calc
    ((Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1).map splitLast)
        = (((Measure.pi μ).map e).map Prod.swap) := by
            rw [hSplitLast, Measure.map_map measurable_swap e.measurable]
    _ = (((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))).map
          Prod.swap) := by
            rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)).prod (μ (Fin.last m)) := by
          rw [Measure.prod_swap]
    _ = (Measure.pi fun i : Fin m ↦ ProbabilityTheory.gammaMeasure (η i.castSucc : ℝ) 1).prod
          (ProbabilityTheory.gammaMeasure (η (Fin.last m) : ℝ) 1) := by
          simp [μ, Fin.succAbove_last]

/-- Helper for Corollary 24.28: splitting off the first Gamma coordinate factors the finite
Gamma-product source into the head marginal and the tail product. -/
private theorem map_piGamma_splitHead_eq_prod {m : ℕ} (η : Fin (m + 1) → NNReal)
    (hη : ∀ i, 0 < (η i : ℝ)) :
    ((Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1).map
      (fun x ↦ (x 0, fun i : Fin m ↦ x i.succ))) =
      (ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1).prod
        (Measure.pi fun i : Fin m ↦ ProbabilityTheory.gammaMeasure (η i.succ : ℝ) 1) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1
  let splitHead : (Fin (m + 1) → ℝ) → ℝ × (Fin m → ℝ) :=
    fun x ↦ (x 0, Fin.tail x)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
  have hMapEq :
      (Measure.pi μ).map e =
        (μ 0).prod (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i)) :=
    (measurePreserving_piFinSuccAbove μ 0).map_eq
  have hSplitHead : splitHead = e := by
    -- Proof comment: removing the initial coordinate leaves the tail block indexed by `i.succ`.
    funext x
    rfl
  -- Proof comment: `piFinSuccAbove` at `0` already has the desired head/tail order.
  calc
    ((Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1).map splitHead)
        = (Measure.pi μ).map e := by
            rw [hSplitHead]
    _ = (μ 0).prod (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i)) := by
          rw [hMapEq]
    _ = (ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1).prod
          (Measure.pi fun i : Fin m ↦ ProbabilityTheory.gammaMeasure (η i.succ : ℝ) 1) := by
          simp [μ, Fin.zero_succAbove]

/-- Helper for Corollary 24.28: the sum of a Gamma pair has the Gamma law with summed shape. -/
private theorem hasLaw_sum_gammaPair (a b : NNReal)
    (ha : 0 < (a : ℝ)) (hb : 0 < (b : ℝ)) :
    HasLaw
      (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (ProbabilityTheory.gammaMeasure ((a : ℝ) + (b : ℝ)) 1)
      ((ProbabilityTheory.gammaMeasure (a : ℝ) 1).prod
        (ProbabilityTheory.gammaMeasure (b : ℝ) 1)) := by
  let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
  have hRatio :
      HasLaw ratioSum
        ((betaMeasure (a : ℝ) (b : ℝ)).prod
          (ProbabilityTheory.gammaMeasure ((a : ℝ) + (b : ℝ)) 1))
        (((ProbabilityTheory.gammaMeasure (a : ℝ) 1).prod
          (ProbabilityTheory.gammaMeasure (b : ℝ) 1))) := by
    refine ⟨by fun_prop, ?_⟩
    simpa [ratioSum, add_comm, add_left_comm, add_assoc] using
      map_gammaPair_toRatioSum_eq_prod_beta_gamma (θ₁ := (a : ℝ)) (θ₂ := (b : ℝ)) ha hb
  have hSnd :
      HasLaw Prod.snd
        (ProbabilityTheory.gammaMeasure ((a : ℝ) + (b : ℝ)) 1)
        ((betaMeasure (a : ℝ) (b : ℝ)).prod
          (ProbabilityTheory.gammaMeasure ((a : ℝ) + (b : ℝ)) 1)) :=
    betaGammaProdSource_snd_hasLaw (θ₁ := (a : ℝ)) (θ₂ := (b : ℝ)) ha hb
  -- Proof comment: the sum is the second coordinate of the ratio/sum map.
  simpa [Function.comp, ratioSum] using hSnd.comp hRatio

/-- Helper for Corollary 24.28: the sum of the independent Gamma-product coordinates again has a
Gamma law with shape equal to the parameter sum. -/
private theorem hasLaw_sum_piGamma {m : ℕ} (η : Fin (m + 1) → NNReal)
    (hη : ∀ i, 0 < (η i : ℝ)) :
    HasLaw
      (fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
      (ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1)
      (Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) := by
  induction m with
  | zero =>
      -- Proof comment: for a single coordinate, the total sum is just the evaluation at that
      -- unique coordinate, so the Gamma law is immediate from the product marginal.
      letI : ∀ i : Fin 1, IsProbabilityMeasure
          (ProbabilityTheory.gammaMeasure (η i : ℝ) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
      simpa [dirichletTerminalTime] using
        ((measurePreserving_eval
          (fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) 0).hasLaw :
          HasLaw (Function.eval 0)
            (ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1)
            (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1))
  | succ m ih =>
      let ηPrefix : Fin (m + 1) → NNReal := fun i ↦ η i.castSucc
      let μPrefix : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (ηPrefix i : ℝ) 1
      let μLast : Measure ℝ := ProbabilityTheory.gammaMeasure (η (Fin.last (m + 1)) : ℝ) 1
      let splitLast : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
        fun y ↦ ((fun i : Fin (m + 1) ↦ y i.castSucc), y (Fin.last (m + 1)))
      let sumPair : (Fin (m + 1) → ℝ) × ℝ → ℝ := fun p ↦ (∑ i, p.1 i) + p.2
      letI : ∀ i : Fin (m + 1), IsProbabilityMeasure
          (ProbabilityTheory.gammaMeasure (ηPrefix i : ℝ) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i.castSucc) zero_lt_one
      letI : IsProbabilityMeasure μPrefix := by
        dsimp [μPrefix]
        infer_instance
      letI : SFinite μPrefix := by
        infer_instance
      letI : IsProbabilityMeasure μLast := by
        exact isProbabilityMeasure_gammaMeasure (hη (Fin.last (m + 1))) zero_lt_one
      letI : SFinite μLast := by
        infer_instance
      have hPrefix :
          HasLaw
            (fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
            (ProbabilityTheory.gammaMeasure (dirichletTerminalTime ηPrefix : ℝ) 1)
            μPrefix :=
        ih ηPrefix (fun i ↦ hη i.castSucc)
      have hPrefixPos : 0 < (dirichletTerminalTime ηPrefix : ℝ) := by
        -- Proof comment: the prefix sum dominates its first strictly positive Gamma shape.
        let i0 : Fin (m + 1) := 0
        have hi0 : 0 < (ηPrefix i0 : ℝ) := hη i0.castSucc
        have hleNN : ηPrefix i0 ≤ dirichletTerminalTime ηPrefix := by
          exact Finset.single_le_sum (f := ηPrefix) (by
            intro i hi
            positivity) (by simp [i0])
        have hle : (ηPrefix i0 : ℝ) ≤ (dirichletTerminalTime ηPrefix : ℝ) := by
          exact_mod_cast hleNN
        exact lt_of_lt_of_le hi0 hle
      have hPairLaw :
          HasLaw
            (fun p : (Fin (m + 1) → ℝ) × ℝ ↦ ((∑ i, p.1 i), p.2))
            ((ProbabilityTheory.gammaMeasure (dirichletTerminalTime ηPrefix : ℝ) 1).prod μLast)
            (μPrefix.prod μLast) := by
        refine ⟨by fun_prop, ?_⟩
        -- Proof comment: on a product source, mapping the two coordinates separately gives the
        -- product of their marginal laws.
        rw [← hPrefix.map_eq, ← Measure.map_id (μ := μLast)]
        simpa [Prod.map] using
          (Measure.map_prod_map μPrefix μLast
            (f := fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
            (g := id) (by fun_prop) measurable_id).symm
      have hAddLaw :
          HasLaw
            (fun p : ℝ × ℝ ↦ p.1 + p.2)
            (ProbabilityTheory.gammaMeasure
              ((dirichletTerminalTime ηPrefix : ℝ) + (η (Fin.last (m + 1)) : ℝ)) 1)
            ((ProbabilityTheory.gammaMeasure (dirichletTerminalTime ηPrefix : ℝ) 1).prod μLast) :=
        hasLaw_sum_gammaPair (dirichletTerminalTime ηPrefix) (η (Fin.last (m + 1)))
          hPrefixPos (hη (Fin.last (m + 1)))
      have hSumLaw :
          HasLaw
            sumPair
            (ProbabilityTheory.gammaMeasure
              ((dirichletTerminalTime ηPrefix : ℝ) + (η (Fin.last (m + 1)) : ℝ)) 1)
            (μPrefix.prod μLast) :=
        hAddLaw.comp hPairLaw
      have hSplit :
          HasLaw splitLast (μPrefix.prod μLast)
            (Measure.pi fun i : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) := by
        refine ⟨by fun_prop, ?_⟩
        simpa [ηPrefix, μPrefix, μLast, splitLast] using
          map_piGamma_splitLast_eq_prod (η := η) hη
      have hsum_eq :
          sumPair ∘ splitLast = (fun y : Fin (m + 2) → ℝ ↦ ∑ i, y i) := by
        -- Proof comment: splitting off the last coordinate and then re-adding it recovers the
        -- full finite sum.
        funext y
        simp [sumPair, splitLast, Fin.sum_univ_castSucc, add_comm, add_left_comm]
      have htotal_eq :
          (∑ i : Fin (m + 1), (η i.castSucc : ℝ)) + (η (Fin.last (m + 1)) : ℝ) =
            (dirichletTerminalTime η : ℝ) := by
        simpa [dirichletTerminalTime, ηPrefix] using
          (Fin.sum_univ_castSucc (fun i : Fin (m + 2) ↦ (η i : ℝ))).symm
      -- Proof comment: split off the last coordinate, add the prefix total to the last Gamma
      -- variable, and then rewrite that sum as the full coordinate sum.
      rw [← hsum_eq]
      simpa [dirichletTerminalTime, ηPrefix, μPrefix, μLast, htotal_eq] using hSumLaw.comp hSplit

/-- Helper for Corollary 24.28: after normalizing the tail block and converting the head/total
pair to Beta/Gamma coordinates, reassembling the coordinates recovers the canonical normalize-and-
sum map. -/
private theorem assemble_headTail_normalizeWithSum_eq {m : ℕ} (y : Fin (m + 2) → ℝ)
    (hhead : 0 < y 0) (htail : 0 < ∑ i : Fin (m + 1), y i.succ) :
    let tailNorm := fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ
    let b := y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)
    let t := y 0 + ∑ j : Fin (m + 1), y j.succ
    (Fin.cons b (fun i ↦ (1 - b) * tailNorm i), t) =
      ((fun i ↦ y i / ∑ j, y j), ∑ j, y j) := by
  -- Proof comment: rewrite the full sum into head plus tail mass, then verify the coordinates of
  -- the reassembled vector separately.
  dsimp
  have hsum : (∑ j : Fin (m + 2), y j) = y 0 + ∑ j : Fin (m + 1), y j.succ := by
    simpa using (Fin.sum_univ_succ (f := y))
  refine Prod.ext ?_ ?_
  · funext i
    refine Fin.cases ?_ ?_ i
    · -- Proof comment: the head coordinate is exactly the Beta ratio `y 0 / total`.
      simp [hsum]
    · intro j
      -- Proof comment: on the tail coordinates, rewrite `1 - b` as `tail / total` and cancel the
      -- tail mass from the normalized tail block.
      have htotal_ne : y 0 + ∑ k : Fin (m + 1), y k.succ ≠ 0 := (add_pos hhead htail).ne'
      have hb :
          1 - y 0 / (y 0 + ∑ k : Fin (m + 1), y k.succ) =
            (∑ k : Fin (m + 1), y k.succ) / (y 0 + ∑ k : Fin (m + 1), y k.succ) := by
        field_simp [htotal_ne]
        ring_nf
      simp [Fin.cons, hsum, hb]
      field_simp [htotal_ne, htail.ne']
  · -- Proof comment: the carried total mass is exactly the full finite coordinate sum.
    simp [hsum]

/-- Helper for Corollary 24.28: the `Corollary_24_29` head/tail decomposition of a Dirichlet law
packages the renormalized tail and the first coordinate into an explicit product law. -/
private theorem hasLaw_dirichlet_headTailDecompose {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i, 0 < η i) :
    HasLaw
      (fun x : Fin (m + 2) → ℝ ↦ (fun i : Fin (m + 1) ↦ x i.succ / (1 - x 0), x 0))
      ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)))
      (dirichletMeasure η) := by
  let tail : (Fin (m + 2) → ℝ) → Fin (m + 1) → ℝ := fun x i ↦ x i.succ / (1 - x 0)
  let head : (Fin (m + 2) → ℝ) → ℝ := fun x ↦ x 0
  let decompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ := fun x ↦ (tail x, head x)
  letI : ∀ i : Fin (m + 2), IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (η i) 1) :=
    fun i ↦ isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  haveI : IsProbabilityMeasure (dirichletMeasure η) := by
    haveI :
        IsProbabilityMeasure
          ((Measure.pi fun i : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η i) 1).map
            (fun y i ↦ y i / ∑ j, y j)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    simpa [dirichletMeasure_def]
  have hId :
      HasLaw (fun x : Fin (m + 2) → ℝ ↦ x) (dirichletMeasure η) (dirichletMeasure η) :=
    HasLaw.id
  have hTail :
      HasLaw tail (dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ) (dirichletMeasure η) := by
    -- Proof comment: Corollary 24.29 identifies the renormalized tail with the tail Dirichlet
    -- law.
    simpa [tail] using
      (hasLaw_tail_dirichlet_of_hasLaw_dirichlet (μ := dirichletMeasure η) (θ := η) hη hId)
  have hHead :
      HasLaw head (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)) (dirichletMeasure η) := by
    -- Proof comment: the first coordinate has the Beta marginal from Corollary 24.29.
    simpa [head] using
      (hasLaw_fst_beta_of_hasLaw_dirichlet (μ := dirichletMeasure η) (θ := η) hη hId)
  have hIndep : IndepFun head tail (dirichletMeasure η) := by
    -- Proof comment: the same corollary gives independence of the head and the renormalized tail.
    simpa [head, tail] using
      (indepFun_fst_tail_of_hasLaw_dirichlet (μ := dirichletMeasure η) (θ := η) hη hId)
  refine ⟨by fun_prop, ?_⟩
  -- Proof comment: package the independent marginal laws in the requested tail-first order.
  calc
    Measure.map decompose (dirichletMeasure η)
        = Measure.map Prod.swap
            (Measure.map (fun x : Fin (m + 2) → ℝ ↦ (head x, tail x)) (dirichletMeasure η)) := by
            rw [show decompose = Prod.swap ∘ (fun x : Fin (m + 2) → ℝ ↦ (head x, tail x)) by
              funext x
              rfl,
              Measure.map_map measurable_swap (by fun_prop)]
    _ = Measure.map Prod.swap
          ((Measure.map head (dirichletMeasure η)).prod
            (Measure.map tail (dirichletMeasure η))) := by
            rw [(indepFun_iff_map_prod_eq_prod_map_map hHead.aemeasurable hTail.aemeasurable).mp
              hIndep]
    _ = (Measure.map tail (dirichletMeasure η)).prod (Measure.map head (dirichletMeasure η)) := by
          rw [Measure.prod_swap]
    _ = ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
          (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ))) := by
          rw [hTail.map_eq, hHead.map_eq]

/-- Helper for Corollary 24.28: on the Dirichlet surface, reassembling the head/tail
decomposition is almost surely the identity. -/
private theorem dirichlet_headTailReassemble_ae {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i, 0 < η i) :
    (fun x : Fin (m + 2) → ℝ ↦
      Fin.cons (x 0) (fun i ↦ (1 - x 0) * (x i.succ / (1 - x 0)))) =ᵐ[dirichletMeasure η] id := by
  let μ : Measure (Fin (m + 2) → ℝ) :=
    Measure.pi fun i : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η i) 1
  let normalize : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ := fun y i ↦ y i / ∑ j, y j
  let reassemble : (Fin (m + 2) → ℝ) → Fin (m + 2) → ℝ :=
    fun x ↦ Fin.cons (x 0) (fun i ↦ (1 - x 0) * (x i.succ / (1 - x 0)))
  letI : ∀ i : Fin (m + 2), IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (η i) 1) :=
    fun i ↦ isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  have hcoord_pos : ∀ i : Fin (m + 2), ∀ᵐ y ∂ μ, 0 < y i := by
    intro i
    have hEval :
        HasLaw (Function.eval i) (ProbabilityTheory.gammaMeasure (η i) 1) μ :=
      (measurePreserving_eval
        (fun j : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η j) 1) i).hasLaw
    -- Proof comment: each Gamma source coordinate is almost surely strictly positive.
    exact (hEval.ae_iff (by fun_prop)).2 (ae_pos_gammaMeasure_unitRate (η i) (hη i))
  have hall_pos : ∀ᵐ y ∂ μ, ∀ i : Fin (m + 2), 0 < y i := by
    -- Proof comment: because the index set is finite, coordinatewise positivity upgrades to
    -- simultaneous positivity.
    exact ae_all_iff.2 hcoord_pos
  have hreassemble_meas : Measurable reassemble := by
    refine measurable_pi_lambda _ ?_
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [reassemble] using measurable_pi_apply 0
    · intro j
      simp [reassemble]
      simpa using (measurable_const.sub (measurable_pi_apply 0)).mul
        ((measurable_pi_apply j.succ).div (measurable_const.sub (measurable_pi_apply 0)))
  rw [dirichletMeasure_def]
  refine (ae_map_iff (by fun_prop) (measurableSet_eq_fun hreassemble_meas measurable_id)).2 ?_
  filter_upwards [hall_pos] with y hy
  have hsum : (∑ j : Fin (m + 2), y j) = y 0 + ∑ j : Fin (m + 1), y j.succ := by
    simpa using (Fin.sum_univ_succ (f := y))
  have htail : 0 < ∑ i : Fin (m + 1), y i.succ := by
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < y i0.succ := hy i0.succ
    have hle : y i0.succ ≤ ∑ i : Fin (m + 1), y i.succ := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ y i.succ) (by
        intro i hi
        exact le_of_lt (hy i.succ)) (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  have htotal_ne' : y 0 + ∑ j : Fin (m + 1), y j.succ ≠ 0 := (add_pos (hy 0) htail).ne'
  have htotal_ne : (∑ j : Fin (m + 2), y j) ≠ 0 := by
    simpa [hsum] using htotal_ne'
  have htailEq :
      (fun i : Fin (m + 1) ↦ normalize y i.succ / (1 - normalize y 0)) =
        fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ := by
    funext i
    have hb : 1 - normalize y 0 = (∑ j : Fin (m + 1), y j.succ) / ∑ j : Fin (m + 2), y j := by
      dsimp [normalize]
      rw [hsum]
      field_simp [htotal_ne']
      ring_nf
    dsimp [normalize]
    rw [hb]
    field_simp [htotal_ne, htail.ne']
  have hheadEq : normalize y 0 = y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ) := by
    dsimp [normalize]
    simp [hsum]
  have hreassembleEq :
      reassemble (normalize y) =
        Fin.cons (y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ))
          (fun i ↦ (1 - y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)) *
            (y i.succ / ∑ j : Fin (m + 1), y j.succ)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [reassemble, normalize, hsum]
    · intro i
      have htailEq_i := congrFun htailEq i
      change (1 - normalize y 0) * (normalize y i.succ / (1 - normalize y 0)) =
        (1 - y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)) *
          (y i.succ / ∑ j : Fin (m + 1), y j.succ)
      have hden : 1 - y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ) = 1 - normalize y 0 := by
        rw [hheadEq]
      rw [hden]
      exact congrArg (fun t ↦ (1 - normalize y 0) * t) htailEq_i
  rw [hreassembleEq]
  -- Proof comment: this pointwise identity is exactly the first-coordinate part of the
  -- deterministic normalize-and-sum assembly lemma.
  simpa [normalize] using
    congrArg Prod.fst (assemble_headTail_normalizeWithSum_eq (m := m) y (hy 0) htail)

/-- Helper for Corollary 24.28: the current `Corollary_24_29` Dirichlet surface can be
reassembled from the independent tail-Dirichlet and first-coordinate Beta factors. -/
private theorem map_dirichlet_tail_beta_to_dirichletMeasure {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i, 0 < η i) :
    Measure.map
      (fun p : (Fin (m + 1) → ℝ) × ℝ ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * p.1 i))
      ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ))) =
      dirichletMeasure η := by
  -- Route correction: the earlier one-piece converse assembly theorem mixed the forward product
  -- law and the inverse-a.e. identity. Prove those parts separately and compose them here.
  let decompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
    fun x ↦ (fun i : Fin (m + 1) ↦ x i.succ / (1 - x 0), x 0)
  let assemble : (Fin (m + 1) → ℝ) × ℝ → Fin (m + 2) → ℝ :=
    fun p ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * p.1 i)
  have hassemble_meas : Measurable assemble := by
    refine measurable_pi_lambda _ ?_
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa [assemble] using measurable_snd
    · intro j
      simpa [assemble] using (measurable_const.sub measurable_snd).mul
        ((measurable_pi_apply j).comp measurable_fst)
  have hDecompose :
      HasLaw decompose
        ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
          (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)))
        (dirichletMeasure η) :=
    hasLaw_dirichlet_headTailDecompose (hη := hη)
  calc
    Measure.map assemble
        ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
          (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)))
      = Measure.map assemble (Measure.map decompose (dirichletMeasure η)) := by
          rw [← hDecompose.map_eq]
    _ = Measure.map (assemble ∘ decompose) (dirichletMeasure η) := by
          rw [Measure.map_map hassemble_meas (by fun_prop)]
    _ = Measure.map id (dirichletMeasure η) := by
          refine Measure.map_congr ?_
          simpa [Function.comp, assemble, decompose] using
            dirichlet_headTailReassemble_ae (hη := hη)
    _ = dirichletMeasure η := by
          simp

-- Semantic recall note: reuse the chapter's normalized-Gamma Dirichlet law from Corollary 24.29;
-- the discarded ambient-density package on `Fin n → ℝ` was not the source-faithful probability
-- measure.
-- Semantic recall note: no dedicated gamma-subordinator owner is available in the current chapter
-- API, so Corollary 24.28 uses a single source-faithful hypothesis bundle instead of three ad hoc
-- assumptions on an arbitrary process.
/-- The local gamma-subordinator bundle along the cumulative times
`t_i = ∑_{j=1}^i θ_j`, used as the source-faithful ambient hypothesis for Corollary 24.28 until
the chapter exposes a dedicated owner for the gamma subordinator itself. -/
structure IsGammaSubordinatorAtDirichletTimes
    (P : ProbabilityMeasure Ω) (θ : Fin n → NNReal) (M : NNReal → Ω → ℝ) : Prop where
  /-- The gamma subordinator starts from `0`. -/
  map_zero : ∀ ω, M 0 ω = 0
  /-- The cumulative increments `M_{t_i} - M_{t_{i-1}}` are independent. -/
  indep_increments :
    iIndepFun (fun i ↦ gammaCumulativeIncrement θ M i) (P : Measure Ω)
  /-- Each cumulative increment has the Gamma law with shape parameter `θ i` and unit rate. -/
  increment_hasLaw : ∀ i,
    HasLaw (gammaCumulativeIncrement θ M i)
      (ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) (P : Measure Ω)

/-- Helper for Corollary 24.28: the cumulative increment vector has the product Gamma law. -/
private theorem hasLaw_cumulativeIncrementVector_piGamma
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    HasLaw
      (fun ω i ↦ gammaCumulativeIncrement θ M i ω)
      (Measure.pi fun i : Fin n ↦ ProbabilityTheory.gammaMeasure (θ i : ℝ) 1)
      (P : Measure Ω) := by
  refine ⟨by
    -- Proof comment: each coordinate is measurable because it already has an explicit Gamma law.
    exact aemeasurable_pi_lambda _ fun i ↦ (hGamma.increment_hasLaw i).aemeasurable, ?_⟩
  -- Proof comment: independent coordinates have joint law equal to the product of their
  -- one-dimensional marginals.
  rw [show
      (P : Measure Ω).map (fun ω i ↦ gammaCumulativeIncrement θ M i ω) =
        Measure.pi fun i : Fin n ↦
          (P : Measure Ω).map (gammaCumulativeIncrement θ M i) by
        simpa using
          (iIndepFun_iff_map_fun_eq_pi_map
            (μ := (P : Measure Ω))
            (f := fun i ↦ gammaCumulativeIncrement θ M i)
            (fun i ↦ (hGamma.increment_hasLaw i).aemeasurable)).1 hGamma.indep_increments]
  congr 1
  funext i
  exact (hGamma.increment_hasLaw i).map_eq

/-- Helper for Corollary 24.28: the cumulative increments telescope to the terminal value. -/
private theorem sum_gammaCumulativeIncrement_eq_terminalValue
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) (ω : Ω) :
    ∑ i, gammaCumulativeIncrement θ M i ω = M (dirichletTerminalTime θ) ω := by
  -- Proof comment: first telescope the successive differences of the cumulative-time values.
  calc
    ∑ i, gammaCumulativeIncrement θ M i ω
        = M (dirichletCumulativeTimes θ (Fin.last n)) ω -
            M (dirichletCumulativeTimes θ 0) ω := by
              simpa [gammaCumulativeIncrement] using
                (sum_succ_sub_castSucc_eq_last_sub_zero
                  (f := fun i : Fin (n + 1) ↦ M (dirichletCumulativeTimes θ i) ω))
    _ = M (dirichletTerminalTime θ) ω - M 0 ω := by
          -- Proof comment: the cumulative-time grid starts at `0` and ends at `t_n`.
          have hlastTime : dirichletCumulativeTimes θ (Fin.last n) = dirichletTerminalTime θ := by
            rw [dirichletCumulativeTimes, dirichletTerminalTime]
            simp only [Fin.val_last]
            refine Finset.sum_congr rfl ?_
            intro i hi
            congr
          have hzeroTime : dirichletCumulativeTimes θ 0 = 0 := by
            simp [dirichletCumulativeTimes]
          rw [hlastTime, hzeroTime]
    _ = M (dirichletTerminalTime θ) ω := by
          rw [hGamma.map_zero ω, sub_zero]

/-- Helper for Corollary 24.28: the normalized increment vector is the normalization of the
Gamma increment vector by its total sum. -/
private theorem dirichletNormalizedIncrementVector_eq_normalize_cumulativeIncrementVector
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    dirichletNormalizedIncrementVector θ M =
      (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j) ∘
        (fun ω i ↦ gammaCumulativeIncrement θ M i ω) := by
  -- Proof comment: both sides divide the same increment coordinate by the total increment sum,
  -- and the latter is `M t_n` by the telescoping lemma above.
  funext ω i
  simp [Function.comp, dirichletNormalizedIncrementVector,
    sum_gammaCumulativeIncrement_eq_terminalValue (P := P) (θ := θ) (M := M) hGamma ω]

/-- Helper for Corollary 24.28: the pair `(X, S)` is the normalize-and-sum image of the Gamma
increment vector. -/
private theorem dirichletNormalizedIncrementPair_eq_normalizeWithSum_incrementVector
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    dirichletNormalizedIncrementPair θ M =
      (fun y : Fin n → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j)) ∘
        (fun ω i ↦ gammaCumulativeIncrement θ M i ω) := by
  -- Proof comment: rewrite the first coordinate by normalization and the second by the telescoping
  -- identity for the cumulative increment sum.
  funext ω
  ext i <;> simp [Function.comp, dirichletNormalizedIncrementPair,
    dirichletNormalizedIncrementVector,
    sum_gammaCumulativeIncrement_eq_terminalValue (P := P) (θ := θ) (M := M) hGamma ω]

/-- Helper for Corollary 24.28: in dimension `1`, the normalized Gamma source carries the
constant Dirichlet vector together with its total mass. -/
private theorem normalizedGammaTransportEqDirichletProdGammaZero
    (η : Fin 1 → NNReal) (hη : ∀ i, 0 < (η i : ℝ)) :
    Measure.map
      (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
      (dirichletMeasure fun i ↦ (η i : ℝ)).prod
        (ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1) := by
  let ν : Measure ℝ := ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let constOne : Fin 1 → ℝ := fun _ ↦ 1
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
  have hgammaFamily :
      (fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
        fun _ : Fin 1 ↦ ν := by
    funext i
    fin_cases i
    simp [ν]
  have hmap_e :
      Measure.map e
          (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
        ν := by
    -- Proof comment: the `Fin 1` Gamma product is measurably equivalent to its unique coordinate.
    rw [hgammaFamily]
    simpa [e] using (measurePreserving_funUnique ν (Fin 1)).map_eq
  have hsource :
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
        Measure.map e.symm ν := by
    -- Proof comment: invert the unique-coordinate measurable equivalence to rewrite the source.
    calc
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1)
          =
            Measure.map e.symm
              (Measure.map e
                (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1)) := by
              rw [Measure.map_map e.symm.measurable
                e.measurable]
              simp
      _ = Measure.map e.symm ν := by rw [hmap_e]
  have hpos : ∀ᵐ x ∂ ν, 0 < x := by
    -- Proof comment: the one-dimensional Gamma source is almost surely strictly positive.
    simpa [ν] using ae_pos_gammaMeasure_unitRate (η 0 : ℝ) (hη 0)
  have hDir :
      dirichletMeasure (fun i ↦ (η i : ℝ)) = Measure.map (fun _ : ℝ ↦ constOne) ν := by
    -- Proof comment: normalizing a single positive Gamma coordinate yields the constant vector `1`.
    rw [dirichletMeasure_def, hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    funext i
    simp [constOne, e, hx.ne']
  have hPair :
      Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
      Measure.map (fun x : ℝ ↦ (constOne, x)) ν := by
    -- Proof comment: after identifying the unique Gamma coordinate, the pair map becomes
    -- `(const 1, id)` almost surely on the positive support.
    rw [hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    ext i <;> simp [constOne, e, hx.ne']
  have hconst :
      Measure.map (fun _ : ℝ ↦ constOne) ν = Measure.dirac constOne := by
    -- Proof comment: mapping a probability measure by a constant produces the corresponding Dirac
    -- mass.
    rw [Measure.map_const]
    simp
  -- Proof comment: the joint one-dimensional law is exactly the product of the constant
  -- Dirichlet marginal with the original Gamma marginal.
  calc
    Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1)
      = Measure.map (fun x : ℝ ↦ (constOne, x)) ν := hPair
    _ = (Measure.dirac constOne).prod ν := by
          simpa using (Measure.dirac_prod (ν := ν) (x := constOne)).symm
    _ = (Measure.map (fun _ : ℝ ↦ constOne) ν).prod ν := by rw [hconst]
    _ = (dirichletMeasure fun i ↦ (η i : ℝ)).prod ν := by rw [hDir]
    _ = (dirichletMeasure fun i ↦ (η i : ℝ)).prod
          (ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1) := by
          simp [ν, dirichletTerminalTime]

/-- Helper for Corollary 24.28: the remaining source-side transport theorem sends the Gamma
product law to the joint law of the normalized vector and the total mass. -/
private theorem normalizedGammaTransportEqDirichletProdGamma {m : ℕ}
    (η : Fin (m + 1) → NNReal) (hη : ∀ i, 0 < (η i : ℝ)) :
    Measure.map
      (fun y : Fin (m + 1) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) =
      (dirichletMeasure fun i ↦ (η i : ℝ)).prod
        (ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1) := by
  induction m with
  | zero =>
      -- Proof comment: the one-dimensional Gamma source reduces to the verified base case above.
      simpa using normalizedGammaTransportEqDirichletProdGammaZero η hη
  | succ m ih =>
      let μ : Measure (Fin (m + 2) → ℝ) :=
        Measure.pi fun i : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1
      let tailη : Fin (m + 1) → NNReal := fun i ↦ η i.succ
      let μHead : Measure ℝ := ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1
      let μTail : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (tailη i : ℝ) 1
      let νTail : Measure (Fin (m + 1) → ℝ) :=
        dirichletMeasure fun i : Fin (m + 1) ↦ (tailη i : ℝ)
      let γTail : Measure ℝ :=
        ProbabilityTheory.gammaMeasure (dirichletTerminalTime tailη : ℝ) 1
      let γTotal : Measure ℝ :=
        ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1
      let splitHead : (Fin (m + 2) → ℝ) → ℝ × (Fin (m + 1) → ℝ) :=
        fun y ↦ (y 0, fun i : Fin (m + 1) ↦ y i.succ)
      let normalizeTailWithSum : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
        fun z ↦ ((fun i ↦ z i / ∑ j, z j), ∑ j, z j)
      let liftTail :
          ℝ × (Fin (m + 1) → ℝ) → ℝ × ((Fin (m + 1) → ℝ) × ℝ) :=
        Prod.map id normalizeTailWithSum
      let assoc1 :
          ℝ × ((Fin (m + 1) → ℝ) × ℝ) → (ℝ × (Fin (m + 1) → ℝ)) × ℝ :=
        fun p ↦ ((p.1, p.2.1), p.2.2)
      let swap1 :
          (ℝ × (Fin (m + 1) → ℝ)) × ℝ → ((Fin (m + 1) → ℝ) × ℝ) × ℝ :=
        Prod.map Prod.swap id
      let assoc2 :
          ((Fin (m + 1) → ℝ) × ℝ) × ℝ → (Fin (m + 1) → ℝ) × (ℝ × ℝ) :=
        fun p ↦ (p.1.1, (p.1.2, p.2))
      let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
      let liftRatio : (Fin (m + 1) → ℝ) × (ℝ × ℝ) → (Fin (m + 1) → ℝ) × (ℝ × ℝ) :=
        Prod.map id ratioSum
      let assoc3 :
          (Fin (m + 1) → ℝ) × (ℝ × ℝ) → ((Fin (m + 1) → ℝ) × ℝ) × ℝ :=
        fun p ↦ ((p.1, p.2.1), p.2.2)
      let assembleDir : (Fin (m + 1) → ℝ) × ℝ → Fin (m + 2) → ℝ :=
        fun p ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * p.1 i)
      let liftAssemble :
          ((Fin (m + 1) → ℝ) × ℝ) × ℝ → (Fin (m + 2) → ℝ) × ℝ :=
        Prod.map assembleDir id
      let expanded :
          (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) × ℝ :=
        liftAssemble ∘ assoc3 ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead
      letI : ∀ i : Fin (m + 2),
          IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (η i : ℝ) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
      letI : IsProbabilityMeasure μHead := by
        dsimp [μHead]
        exact isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
      letI : ∀ i : Fin (m + 1),
          IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (tailη i : ℝ) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i.succ) zero_lt_one
      letI : IsProbabilityMeasure μTail := by
        dsimp [μTail]
        infer_instance
      have hTailTotalPos : 0 < (dirichletTerminalTime tailη : ℝ) := by
        -- Proof comment: the tail parameter sum dominates its first strictly positive coordinate.
        let i0 : Fin (m + 1) := 0
        have hi0 : 0 < (tailη i0 : ℝ) := hη i0.succ
        have hleNN : tailη i0 ≤ dirichletTerminalTime tailη := by
          exact Finset.single_le_sum (f := tailη) (by
            intro i hi
            positivity) (by simp [i0])
        have hle : (tailη i0 : ℝ) ≤ (dirichletTerminalTime tailη : ℝ) := by
          exact_mod_cast hleNN
        exact lt_of_lt_of_le hi0 hle
      have hTotalEq :
          (η 0 : ℝ) + (dirichletTerminalTime tailη : ℝ) = (dirichletTerminalTime η : ℝ) := by
        simpa [dirichletTerminalTime, tailη] using
          (Fin.sum_univ_succ (f := fun i : Fin (m + 2) ↦ (η i : ℝ))).symm
      have hTotalPos : 0 < (dirichletTerminalTime η : ℝ) := by
        rw [← hTotalEq]
        exact add_pos (hη 0) hTailTotalPos
      letI : IsProbabilityMeasure γTail := by
        dsimp [γTail]
        exact isProbabilityMeasure_gammaMeasure hTailTotalPos zero_lt_one
      letI : IsProbabilityMeasure γTotal := by
        dsimp [γTotal]
        exact isProbabilityMeasure_gammaMeasure hTotalPos zero_lt_one
      letI : IsProbabilityMeasure νTail := by
        dsimp [νTail]
        rw [dirichletMeasure_def]
        exact Measure.isProbabilityMeasure_map (by fun_prop)
      letI : IsProbabilityMeasure
          (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)) :=
        isProbabilityMeasureBeta (hη 0) hTailTotalPos
      have hassembleDir_meas : Measurable assembleDir := by
        -- Proof comment: the Dirichlet reassembly is measurable coordinatewise.
        refine measurable_pi_lambda _ ?_
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [assembleDir] using measurable_snd
        · intro j
          simpa [assembleDir] using (measurable_const.sub measurable_snd).mul
            ((measurable_pi_apply j).comp measurable_fst)
      have hLiftAssemble_meas : Measurable liftAssemble := by
        simpa [liftAssemble] using hassembleDir_meas.prodMap measurable_id
      have hHeadPos :
          ∀ᵐ y ∂ μ, 0 < y 0 := by
        have hEval :
            HasLaw (Function.eval 0) (ProbabilityTheory.gammaMeasure (η 0 : ℝ) 1) μ :=
          (measurePreserving_eval
            (fun i : Fin (m + 2) ↦ ProbabilityTheory.gammaMeasure (η i : ℝ) 1) 0).hasLaw
        -- Proof comment: the first Gamma coordinate is almost surely strictly positive.
        exact (hEval.ae_iff (by fun_prop)).2
          (ae_pos_gammaMeasure_unitRate (η 0 : ℝ) (hη 0))
      have hTailLaw :
          HasLaw
            (fun z : Fin (m + 1) → ℝ ↦ ∑ i, z i)
            γTail
            μTail := by
        simpa [γTail, μTail, tailη] using
          hasLaw_sum_piGamma (η := tailη) (fun i ↦ hη i.succ)
      have hTailPos :
          ∀ᵐ y ∂ μ, 0 < ∑ i : Fin (m + 1), y i.succ := by
        have hTailOnProd :
            HasLaw
              (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ ∑ i, p.2 i)
              γTail
              (μHead.prod μTail) := by
          simpa using hTailLaw.comp
            ((measurePreserving_snd (μ := μHead) (ν := μTail)).hasLaw)
        have hSplitLaw :
            HasLaw splitHead (μHead.prod μTail) μ := by
          refine ⟨by fun_prop, ?_⟩
          simpa [μ, μHead, μTail, splitHead, tailη] using
            map_piGamma_splitHead_eq_prod (η := η) hη
        have hTailSource :
            HasLaw
              (fun y : Fin (m + 2) → ℝ ↦ ∑ i : Fin (m + 1), y i.succ)
              γTail
              μ := by
          simpa [splitHead] using hTailOnProd.comp hSplitLaw
        -- Proof comment: the tail total inherits strict positivity from its Gamma law.
        exact (hTailSource.ae_iff (by fun_prop)).2
          (ae_pos_gammaMeasure_unitRate (dirichletTerminalTime tailη : ℝ) hTailTotalPos)
      have hExpanded :
          (fun y : Fin (m + 2) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j)) =ᵐ[μ] expanded := by
        -- Proof comment: on the positive Gamma support, the staged head/tail assembly matches the
        -- canonical normalize-and-sum map.
        filter_upwards [hHeadPos, hTailPos] with y hyHead hyTail
        simpa [expanded, splitHead, normalizeTailWithSum, liftTail, assoc1, swap1, assoc2,
          ratioSum, liftRatio, assoc3, assembleDir, liftAssemble] using
          (assemble_headTail_normalizeWithSum_eq (m := m) y hyHead hyTail).symm
      have hExpandedMap :
          Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail
                          (Measure.map splitHead μ))))))) =
            Measure.map expanded μ := by
      -- Proof comment: collapse the staged deterministic maps back into the single composite
      -- `expanded`.
        have hAssoc1_meas : Measurable assoc1 := by fun_prop
        have hSwap1_meas : Measurable swap1 := by fun_prop
        have hAssoc2_meas : Measurable assoc2 := by fun_prop
        have hLiftRatio_meas : Measurable liftRatio := by fun_prop
        have hAssoc3_meas : Measurable assoc3 := by fun_prop
        have hStep1 : Measurable (liftAssemble ∘ assoc3) := by
          simpa [Function.comp] using hLiftAssemble_meas.comp hAssoc3_meas
        have hStep2 : Measurable ((liftAssemble ∘ assoc3) ∘ liftRatio) := by
          simpa [Function.comp] using hStep1.comp hLiftRatio_meas
        have hStep3 : Measurable (((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) := by
          simpa [Function.comp] using hStep2.comp hAssoc2_meas
        have hStep4 : Measurable ((((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1) := by
          simpa [Function.comp] using hStep3.comp hSwap1_meas
        have hStep5 :
            Measurable (((((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1) ∘ assoc1) := by
          simpa [Function.comp] using hStep4.comp hAssoc1_meas
        have hStep6 :
            Measurable
              ((((((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1) ∘ assoc1) ∘
                liftTail) := by
          simpa [Function.comp] using hStep5.comp (by fun_prop)
        rw [Measure.map_map
          (μ := Measure.map liftRatio
            (Measure.map assoc2
              (Measure.map swap1
                (Measure.map assoc1
                  (Measure.map liftTail
                    (Measure.map splitHead μ))))))
          (f := assoc3) (g := liftAssemble) hLiftAssemble_meas hAssoc3_meas]
        rw [Measure.map_map
          (μ := Measure.map assoc2
            (Measure.map swap1
              (Measure.map assoc1
                (Measure.map liftTail
                  (Measure.map splitHead μ)))))
          (f := liftRatio) (g := liftAssemble ∘ assoc3) hStep1 hLiftRatio_meas]
        rw [Measure.map_map
          (μ := Measure.map swap1
            (Measure.map assoc1
              (Measure.map liftTail
                (Measure.map splitHead μ))))
          (f := assoc2) (g := (liftAssemble ∘ assoc3) ∘ liftRatio) hStep2 hAssoc2_meas]
        rw [Measure.map_map
          (μ := Measure.map assoc1
            (Measure.map liftTail
              (Measure.map splitHead μ)))
          (f := swap1) (g := ((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) hStep3
          hSwap1_meas]
        rw [Measure.map_map
          (μ := Measure.map liftTail (Measure.map splitHead μ))
          (f := assoc1) (g := (((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1)
          hStep4 hAssoc1_meas]
        rw [Measure.map_map
          (μ := Measure.map splitHead μ)
          (f := liftTail)
          (g := ((((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1) ∘ assoc1)
          hStep5 (by fun_prop)]
        rw [Measure.map_map (μ := μ) (f := splitHead)
          (g := (((((liftAssemble ∘ assoc3) ∘ liftRatio) ∘ assoc2) ∘ swap1) ∘ assoc1) ∘ liftTail)
          hStep6 (by fun_prop)]
        rfl
      have hLiftTail :
          Measure.map liftTail (μHead.prod μTail) =
            μHead.prod (νTail.prod γTail) := by
        -- Proof comment: only the tail block is transported through the induction hypothesis.
        rw [← Measure.map_prod_map (μa := μHead) (μc := μTail)
          (f := id) (g := normalizeTailWithSum) measurable_id (by fun_prop)]
        rw [Measure.map_id]
        rw [ih tailη (fun i ↦ hη i.succ)]
      have hAssoc1 :
          Measure.map assoc1 (μHead.prod (νTail.prod γTail)) =
            (μHead.prod νTail).prod γTail := by
        -- Proof comment: reassociate the product so the head Gamma and the tail Dirichlet factor
        -- sit together.
        simpa [assoc1] using (measurePreserving_prodAssoc μHead νTail γTail).symm.map_eq
      have hSwap1 :
          Measure.map swap1 ((μHead.prod νTail).prod γTail) =
            ((νTail.prod μHead).prod γTail) := by
        -- Proof comment: swap the head Gamma and the tail Dirichlet factors, leaving the carried
        -- tail sum untouched.
        calc
          Measure.map swap1 ((μHead.prod νTail).prod γTail)
              = (Measure.map Prod.swap (μHead.prod νTail)).prod (Measure.map id γTail) := by
                  simpa [swap1] using
                    (Measure.map_prod_map (μa := μHead.prod νTail) (μc := γTail)
                      (f := Prod.swap) (g := id) measurable_swap measurable_id).symm
          _ = (Measure.map Prod.swap (μHead.prod νTail)).prod γTail := by
                rw [Measure.map_id]
          _ = ((νTail.prod μHead).prod γTail) := by
                rw [Measure.prod_swap]
      have hAssoc2 :
          Measure.map assoc2 ((νTail.prod μHead).prod γTail) =
            νTail.prod (μHead.prod γTail) := by
        -- Proof comment: regroup the factors so the pair `(head, tailSum)` becomes the second
        -- coordinate.
        simpa [assoc2] using
          (Measure.prodAssoc_prod (μ := νTail) (ν := μHead) (τ := γTail))
      have hLiftRatio :
          Measure.map liftRatio (νTail.prod (μHead.prod γTail)) =
            νTail.prod
              ((betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)).prod γTotal) := by
        -- Proof comment: now only the isolated `(head, tail-sum)` pair is sent through the
        -- Beta/Gamma ratio-sum transport.
        have hRatio :
            Measure.map ratioSum (μHead.prod γTail) =
              (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)).prod γTotal := by
          simpa [ratioSum, μHead, γTail, γTotal, hTotalEq] using
            map_gammaPair_toRatioSum_eq_prod_beta_gamma
              (θ₁ := (η 0 : ℝ))
              (θ₂ := (dirichletTerminalTime tailη : ℝ))
              (hη 0) hTailTotalPos
        rw [← Measure.map_prod_map (μa := νTail) (μc := μHead.prod γTail)
          (f := id) (g := ratioSum) measurable_id (by fun_prop)]
        rw [Measure.map_id]
        rw [hRatio]
      have hAssoc3 :
          Measure.map assoc3
              (νTail.prod
                ((betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)).prod γTotal)) =
            ((νTail.prod
              (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ))).prod γTotal) := by
        -- Proof comment: reassociate once more so the Dirichlet/Beta assembly acts on the first
        -- product factor only.
        simpa [assoc3] using
          (measurePreserving_prodAssoc
            νTail
            (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ))
            γTotal).symm.map_eq
      have hLiftAssemble :
          Measure.map liftAssemble
              ((νTail.prod (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ))).prod
                γTotal) =
            (dirichletMeasure fun i ↦ (η i : ℝ)).prod γTotal := by
        -- Proof comment: the first two factors reassemble to the full Dirichlet law, and the
        -- total Gamma mass is carried along unchanged.
        calc
          Measure.map liftAssemble
              ((νTail.prod (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ))).prod
                γTotal)
              =
                (Measure.map assembleDir
                  (νTail.prod
                    (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)))).prod γTotal := by
                      simpa [liftAssemble] using
                        (Measure.map_prod_map
                          (μa := νTail.prod
                            (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)))
                          (μc := γTotal)
                          (f := assembleDir) (g := id) hassembleDir_meas measurable_id).symm
          _ = (dirichletMeasure fun i ↦ (η i : ℝ)).prod γTotal := by
                simpa [assembleDir, νTail, tailη, dirichletTerminalTime] using
                  congrArg (fun ν => ν.prod γTotal)
                    (map_dirichlet_tail_beta_to_dirichletMeasure
                      (η := fun i : Fin (m + 2) ↦ (η i : ℝ))
                      (hη := fun i ↦ hη i))
      -- Proof comment: replace the canonical normalize-and-sum map by the staged head/tail
      -- composite on the positive Gamma support, then run the split/IH/Beta/Gamma/reassembly
      -- transport pipeline.
      calc
        Measure.map
            (fun y : Fin (m + 2) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
            μ = Measure.map expanded μ := by
                  rw [Measure.map_congr hExpanded]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail
                          (Measure.map splitHead μ))))))) := by
                rw [hExpandedMap]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail (μHead.prod μTail))))))) := by
                rw [map_piGamma_splitHead_eq_prod (η := η) hη]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (μHead.prod (νTail.prod γTail))))))) := by
                rw [hLiftTail]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      ((μHead.prod νTail).prod γTail))))) := by
                rw [hAssoc1]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (((νTail.prod μHead).prod γTail))))) := by
                rw [hSwap1]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (νTail.prod (μHead.prod γTail)))) := by
                rw [hAssoc2]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (νTail.prod
                  ((betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ)).prod γTotal))) := by
                rw [hLiftRatio]
        _ = Measure.map liftAssemble
              ((νTail.prod
                (betaMeasure (η 0 : ℝ) (dirichletTerminalTime tailη : ℝ))).prod γTotal) := by
                rw [hAssoc3]
        _ = (dirichletMeasure fun i ↦ (η i : ℝ)).prod γTotal := by
              rw [hLiftAssemble]
        _ = (dirichletMeasure fun i ↦ (η i : ℝ)).prod
              (ProbabilityTheory.gammaMeasure (dirichletTerminalTime η : ℝ) 1) := by
              rfl

-- Proof sketch: Theorem 24.27 gives independent Gamma increments with unit rate and shapes
-- `θ_i`. The classical Beta-Gamma / Dirichlet-Gamma factorization sends these increments to the
-- pair consisting of their normalized vector and their total sum, and the bundled starting-value
-- hypothesis identifies that total sum with `M_{t_n}` because the cumulative increments telescope.
/-- Corollary 24.28: if `t_i = ∑_{j=1}^i θ_j`, then the pair consisting of the normalized
increment vector `((M_{t_i} - M_{t_{i-1}}) / M_{t_n})_{i=1}^n` and the terminal value `M_{t_n}`
has the product law `Dir_{θ_1,\dots,θ_n} ⊗ Γ_{1,t_n}`. This product-law statement packages the
independence of `X` and `S` together with their two marginal distributions. -/
theorem gammaSubordinator_normalizedIncrementPair_hasLaw_dirichlet_prod_gamma
    (hn : 0 < n)
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    let X : Ω → Fin n → ℝ := dirichletNormalizedIncrementVector θ M
    let S : Ω → ℝ := fun ω ↦ M (dirichletTerminalTime θ) ω
    HasLaw (fun ω ↦ (X ω, S ω))
      ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
        (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
      (P : Measure Ω) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  let Y : Ω → Fin (m + 1) → ℝ := fun ω i ↦ gammaCumulativeIncrement θ M i ω
  have hY :
      HasLaw Y
        (Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (θ i : ℝ) 1)
        (P : Measure Ω) :=
    hasLaw_cumulativeIncrementVector_piGamma (P := P) (θ := θ) (M := M) hGamma
  have hθ : ∀ i : Fin (m + 1), 0 < (θ i : ℝ) := by
    intro i
    -- Proof comment: each increment law is a genuine Gamma probability measure, so each shape is
    -- strictly positive.
    exact gammaShapePos_of_hasLawUnitRate (P := P) (hGamma.increment_hasLaw i)
  have hTransport :
      HasLaw
        (fun y : Fin (m + 1) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
          (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
        (Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) := by
    refine ⟨by fun_prop, ?_⟩
    simpa using normalizedGammaTransportEqDirichletProdGamma (η := θ) hθ
  change HasLaw (dirichletNormalizedIncrementPair θ M)
    ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
      (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
    (P : Measure Ω)
  rw [dirichletNormalizedIncrementPair_eq_normalizeWithSum_incrementVector
    (P := P) (θ := θ) (M := M) hGamma]
  exact hTransport.comp hY

-- Proof sketch: project the first coordinate of the product-law statement for
-- `dirichletNormalizedIncrementPair`.
/-- The normalized increment vector has Dirichlet law with parameter vector `θ`. -/
theorem gammaSubordinator_normalizedIncrementVector_hasLaw_dirichlet
    (_hn : 0 < n)
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    let X : Ω → Fin n → ℝ := dirichletNormalizedIncrementVector θ M
    HasLaw X (dirichletMeasure fun i ↦ (θ i : ℝ)) (P : Measure Ω) := by
  let Y : Ω → Fin n → ℝ := fun ω i ↦ gammaCumulativeIncrement θ M i ω
  have hY :
      HasLaw Y
        (Measure.pi fun i : Fin n ↦ ProbabilityTheory.gammaMeasure (θ i : ℝ) 1)
        (P : Measure Ω) :=
    hasLaw_cumulativeIncrementVector_piGamma (P := P) (θ := θ) (M := M) hGamma
  have hNormalize :
      HasLaw (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j) (dirichletMeasure fun i ↦ (θ i : ℝ))
        (Measure.pi fun i : Fin n ↦ ProbabilityTheory.gammaMeasure (θ i : ℝ) 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [dirichletMeasure_def]
  have hVecEq :
      dirichletNormalizedIncrementVector θ M =
        (fun y : Fin n → ℝ ↦ fun i ↦ y i / ∑ j, y j) ∘ Y :=
    dirichletNormalizedIncrementVector_eq_normalize_cumulativeIncrementVector
      (P := P) (θ := θ) (M := M) hGamma
  -- Proof comment: identify the normalized increment vector with the normalization of the Gamma
  -- increment vector and compose the two laws.
  rw [hVecEq]
  exact hNormalize.comp hY

-- Proof sketch: project the second coordinate of the product-law statement for
-- `dirichletNormalizedIncrementPair`.
/-- The terminal value `M_{t_n}` has Gamma law `Γ_{1,t_n}`. -/
theorem gammaSubordinator_terminalValue_hasLaw_gamma
    (hn : 0 < n)
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    let S : Ω → ℝ := fun ω ↦ M (dirichletTerminalTime θ) ω
    HasLaw S
      (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1)
      (P : Measure Ω) := by
  let X : Ω → Fin n → ℝ := dirichletNormalizedIncrementVector θ M
  let S : Ω → ℝ := fun ω ↦ M (dirichletTerminalTime θ) ω
  have hPair :
      HasLaw (fun ω ↦ (X ω, S ω))
        ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
          (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
        (P : Measure Ω) := by
    -- Proof comment: this is exactly the joint product-law statement proved above.
    simpa [X, S] using
      (gammaSubordinator_normalizedIncrementPair_hasLaw_dirichlet_prod_gamma
        (P := P) (θ := θ) (M := M) hn hGamma)
  have hX :
      HasLaw X (dirichletMeasure fun i ↦ (θ i : ℝ)) (P : Measure Ω) := by
    -- Proof comment: the first marginal gives the Dirichlet law needed to view the source product
    -- as a probability product measure.
    simpa [X] using
      (gammaSubordinator_normalizedIncrementVector_hasLaw_dirichlet
        (P := P) (θ := θ) (M := M) hn hGamma)
  let i0 : Fin n := ⟨0, hn⟩
  have hθ0pos : 0 < (θ i0 : ℝ) := by
    -- Proof comment: every increment law is a genuine probability Gamma law, so in particular the
    -- first shape parameter is positive.
    exact gammaShapePos_of_hasLawUnitRate (P := P) (hGamma.increment_hasLaw i0)
  have hterminalPos : 0 < (dirichletTerminalTime θ : ℝ) := by
    -- Proof comment: `t_n = ∑ i, θ i` dominates the positive first parameter.
    have hleNN : θ i0 ≤ dirichletTerminalTime θ := by
      exact Finset.single_le_sum (f := θ) (by
        intro i hi
        positivity) (by simp [i0])
    have hle : (θ i0 : ℝ) ≤ (dirichletTerminalTime θ : ℝ) := by
      exact_mod_cast hleNN
    exact lt_of_lt_of_le hθ0pos hle
  letI : IsProbabilityMeasure (dirichletMeasure fun i ↦ (θ i : ℝ)) :=
    hX.isProbabilityMeasure_iff.mp inferInstance
  letI : IsProbabilityMeasure (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure hterminalPos zero_lt_one
  letI : SFinite (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1) :=
    inferInstance
  have hSae : AEMeasurable S (P : Measure Ω) := by
    simpa [Function.comp, S] using
      measurable_snd.aemeasurable.comp_aemeasurable hPair.aemeasurable
  refine ⟨hSae, ?_⟩
  -- Proof comment: map the joint product-law pair to its second coordinate and use the standard
  -- product-measure marginal formula.
  change Measure.map (Prod.snd ∘ fun ω ↦ (X ω, S ω)) (P : Measure Ω) =
    ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1
  rw [← AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hPair.aemeasurable,
    hPair.map_eq, Measure.map_snd_prod, measure_univ, one_smul]

-- Proof sketch: the main product-law statement implies that the two coordinates of
-- `dirichletNormalizedIncrementPair` are independent.
/-- The normalized increment vector and the terminal value `M_{t_n}` are independent. -/
theorem gammaSubordinator_normalizedIncrementVector_indep_terminalValue
    (hn : 0 < n)
    (hGamma : IsGammaSubordinatorAtDirichletTimes P θ M) :
    let X : Ω → Fin n → ℝ := dirichletNormalizedIncrementVector θ M
    let S : Ω → ℝ := fun ω ↦ M (dirichletTerminalTime θ) ω
    IndepFun X S (P : Measure Ω) := by
  let X : Ω → Fin n → ℝ := dirichletNormalizedIncrementVector θ M
  let S : Ω → ℝ := fun ω ↦ M (dirichletTerminalTime θ) ω
  have hPair :
      HasLaw (fun ω ↦ (X ω, S ω))
        ((dirichletMeasure fun i ↦ (θ i : ℝ)).prod
          (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1))
        (P : Measure Ω) := by
    -- Proof comment: start from the same pair-valued law as in the terminal marginal proof.
    simpa [X, S] using
      (gammaSubordinator_normalizedIncrementPair_hasLaw_dirichlet_prod_gamma
        (P := P) (θ := θ) (M := M) hn hGamma)
  have hX :
      HasLaw X (dirichletMeasure fun i ↦ (θ i : ℝ)) (P : Measure Ω) := by
    simpa [X] using
      (gammaSubordinator_normalizedIncrementVector_hasLaw_dirichlet
        (P := P) (θ := θ) (M := M) hn hGamma)
  have hS :
      HasLaw S
        (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1)
        (P : Measure Ω) := by
    simpa [S] using
      (gammaSubordinator_terminalValue_hasLaw_gamma
        (P := P) (θ := θ) (M := M) hn hGamma)
  -- Proof comment: the joint law is the product of the two marginals, which is exactly the
  -- measure-theoretic characterization of independence.
  refine (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hS.aemeasurable).2 ?_
  calc
    Measure.map (fun ω ↦ (X ω, S ω)) (P : Measure Ω)
        = (dirichletMeasure fun i ↦ (θ i : ℝ)).prod
            (ProbabilityTheory.gammaMeasure (dirichletTerminalTime θ : ℝ) 1) := hPair.map_eq
    _ = (Measure.map X (P : Measure Ω)).prod (Measure.map S (P : Measure Ω)) := by
          rw [hX.map_eq, hS.map_eq]

end Corollary2428

end ProbabilityTheory
