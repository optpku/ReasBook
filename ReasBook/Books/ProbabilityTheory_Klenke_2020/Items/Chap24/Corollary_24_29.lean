/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Exercise_24_3_1
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

noncomputable section

namespace ProbabilityTheory

-- Semantic recall note: mathlib provides `betaMeasure`, `gammaMeasure`, `HasLaw`, and `IndepFun`,
-- but no reusable finite-dimensional Dirichlet-law owner surfaced in semantic search, so this item
-- keeps the local normalized-Gamma definition.

/-- The Dirichlet law with parameter vector `θ` on a finite coordinate set is the pushforward of
independent Gamma laws by normalization with the total mass. -/
def dirichletMeasure {n : ℕ} (θ : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j)

-- Proof sketch: this is just the defining normalized-Gamma pushforward formula for
-- `dirichletMeasure`.
/-- The Dirichlet measure is the pushforward of the independent Gamma product law by the
normalization map. -/
theorem dirichletMeasure_def {n : ℕ} (θ : Fin n → ℝ) :
    dirichletMeasure θ =
      (Measure.pi fun i ↦ gammaMeasure (θ i) 1).map (fun y i ↦ y i / ∑ j, y j) := by
  -- Proof comment: this theorem is exactly the local definition of `dirichletMeasure`.
  rfl

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Corollary 24.29: splitting off the last Gamma coordinate factors the finite
Gamma-product source into the prefix product and the last marginal. -/
private theorem mapPiGammaSplitLastEqProd {m : ℕ} (η : Fin (m + 1) → ℝ)
    (hη : ∀ i, 0 < η i) :
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (η i) 1).map
      (fun x ↦ ((fun i : Fin m ↦ x i.castSucc), x (Fin.last m)))) =
      (Measure.pi fun i : Fin m ↦ gammaMeasure (η i.castSucc) 1).prod
        (gammaMeasure (η (Fin.last m)) 1) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ gammaMeasure (η i) 1
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
  have hswap_meas :
      Measurable (Prod.swap : ℝ × (Fin m → ℝ) → (Fin m → ℝ) × ℝ) := measurable_swap
  have he_meas : Measurable e := e.measurable
  -- Proof comment: factor through `piFinSuccAbove`, then swap the product factors into the
  -- desired order.
  calc
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (η i) 1).map splitLast)
        = (((Measure.pi μ).map e).map Prod.swap) := by
            rw [hSplitLast, Measure.map_map hswap_meas he_meas]
    _ = (((μ (Fin.last m)).prod (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i))).map
          Prod.swap) := by
            rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ ((Fin.last m).succAbove i)).prod (μ (Fin.last m)) := by
          rw [Measure.prod_swap]
    _ = (Measure.pi fun i : Fin m ↦ gammaMeasure (η i.castSucc) 1).prod
          (gammaMeasure (η (Fin.last m)) 1) := by
          simp [μ, Fin.succAbove_last]

/-- Helper for Corollary 24.29: splitting off the first Gamma coordinate factors the finite
Gamma-product source into the head marginal and the tail product. -/
private theorem mapPiGammaSplitHeadEqProd {m : ℕ} (η : Fin (m + 1) → ℝ)
    (hη : ∀ i, 0 < η i) :
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (η i) 1).map
      (fun x ↦ (x 0, fun i : Fin m ↦ x i.succ))) =
      (gammaMeasure (η 0) 1).prod
        (Measure.pi fun i : Fin m ↦ gammaMeasure (η i.succ) 1) := by
  let μ : Fin (m + 1) → Measure ℝ := fun i ↦ gammaMeasure (η i) 1
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
    ((Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (η i) 1).map splitHead)
        = (Measure.pi μ).map e := by
            rw [hSplitHead]
    _ = (μ 0).prod (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i)) := by
          rw [hMapEq]
    _ = (gammaMeasure (η 0) 1).prod
          (Measure.pi fun i : Fin m ↦ gammaMeasure (η i.succ) 1) := by
          simp [μ, Fin.zero_succAbove]

/-- Helper for Corollary 24.29: the sum of a Gamma pair again has Gamma law with shape equal to
the sum of the shapes. -/
private theorem hasLawSumGammaPair (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    HasLaw
      (fun p : ℝ × ℝ ↦ p.1 + p.2)
      (gammaMeasure (a + b) 1)
      ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by
  let ratioSum : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 / (p.1 + p.2), p.1 + p.2)
  have hRatio :
      HasLaw ratioSum
        ((betaMeasure a b).prod (gammaMeasure (a + b) 1))
        ((gammaMeasure a 1).prod (gammaMeasure b 1)) := by
    refine ⟨by fun_prop, ?_⟩
    -- Proof comment: the ratio/sum map is exactly the Beta-Gamma transport already proved
    -- earlier in the chapter.
    simpa [ratioSum, add_comm, add_left_comm, add_assoc] using
      map_gammaPair_toRatioSum_eq_prod_beta_gamma (θ₁ := a) (θ₂ := b) ha hb
  have hSnd :
      HasLaw Prod.snd
        (gammaMeasure (a + b) 1)
        ((betaMeasure a b).prod (gammaMeasure (a + b) 1)) :=
    betaGammaProdSource_snd_hasLaw (θ₁ := a) (θ₂ := b) ha hb
  -- Proof comment: the sum is the second projection of the ratio/sum transport.
  simpa [Function.comp, ratioSum] using hSnd.comp hRatio

/-- Helper for Corollary 24.29: the sum of finitely many independent Gamma coordinates again has
Gamma law with the summed shape parameter. -/
private theorem hasLawSumPiGamma {m : ℕ} (η : Fin (m + 1) → ℝ) (hη : ∀ i, 0 < η i) :
    HasLaw
      (fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
      (gammaMeasure (∑ i : Fin (m + 1), η i) 1)
      (Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (η i) 1) := by
  induction m with
  | zero =>
      letI : ∀ i : Fin 1, IsProbabilityMeasure (gammaMeasure (η i) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
      -- Proof comment: in dimension `1`, the total sum is evaluation at the unique coordinate.
      simpa using
        ((measurePreserving_eval (fun i : Fin 1 ↦ gammaMeasure (η i) 1) 0).hasLaw :
          HasLaw (Function.eval 0) (gammaMeasure (η 0) 1)
            (Measure.pi fun i : Fin 1 ↦ gammaMeasure (η i) 1))
  | succ m ih =>
      let ηPrefix : Fin (m + 1) → ℝ := fun i ↦ η i.castSucc
      let μPrefix : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (ηPrefix i) 1
      let μLast : Measure ℝ := gammaMeasure (η (Fin.last (m + 1))) 1
      let splitLast : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
        fun y ↦ ((fun i : Fin (m + 1) ↦ y i.castSucc), y (Fin.last (m + 1)))
      let sumPair : (Fin (m + 1) → ℝ) × ℝ → ℝ := fun p ↦ (∑ i, p.1 i) + p.2
      letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (ηPrefix i) 1) := fun i ↦
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
            (gammaMeasure (∑ i : Fin (m + 1), ηPrefix i) 1)
            μPrefix :=
        ih ηPrefix (fun i ↦ hη i.castSucc)
      have hPrefixPos : 0 < ∑ i : Fin (m + 1), ηPrefix i := by
        -- Proof comment: the prefix sum dominates its first strictly positive coordinate.
        let i0 : Fin (m + 1) := 0
        have hi0 : 0 < ηPrefix i0 := hη i0.castSucc
        have hle : ηPrefix i0 ≤ ∑ i : Fin (m + 1), ηPrefix i := by
          exact Finset.single_le_sum (f := ηPrefix) (by
            intro i hi
            exact le_of_lt (hη i.castSucc)) (by simp [i0])
        exact lt_of_lt_of_le hi0 hle
      have hPairLaw :
          HasLaw
            (fun p : (Fin (m + 1) → ℝ) × ℝ ↦ ((∑ i, p.1 i), p.2))
            ((gammaMeasure (∑ i : Fin (m + 1), ηPrefix i) 1).prod μLast)
            (μPrefix.prod μLast) := by
        refine ⟨by fun_prop, ?_⟩
        -- Proof comment: the prefix total and the final coordinate are mapped independently from
        -- the product source.
        rw [← hPrefix.map_eq, ← Measure.map_id (μ := μLast)]
        simpa [Prod.map] using
          (Measure.map_prod_map
            (μa := μPrefix) (μc := μLast)
            (f := fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
            (g := id) (by fun_prop) measurable_id).symm
      have hAddLaw :
          HasLaw
            (fun p : ℝ × ℝ ↦ p.1 + p.2)
            (gammaMeasure ((∑ i : Fin (m + 1), ηPrefix i) + η (Fin.last (m + 1))) 1)
            ((gammaMeasure (∑ i : Fin (m + 1), ηPrefix i) 1).prod μLast) :=
        hasLawSumGammaPair
          (∑ i : Fin (m + 1), ηPrefix i)
          (η (Fin.last (m + 1)))
          hPrefixPos
          (hη (Fin.last (m + 1)))
      have hSumLaw :
          HasLaw
            sumPair
            (gammaMeasure ((∑ i : Fin (m + 1), ηPrefix i) + η (Fin.last (m + 1))) 1)
            (μPrefix.prod μLast) :=
        hAddLaw.comp hPairLaw
      have hSplit :
          HasLaw
            splitLast
            (μPrefix.prod μLast)
            (Measure.pi fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1) := by
        refine ⟨by fun_prop, ?_⟩
        simpa [ηPrefix, μPrefix, μLast, splitLast] using
          mapPiGammaSplitLastEqProd (η := η) hη
      have hsum_eq :
          sumPair ∘ splitLast = (fun y : Fin (m + 2) → ℝ ↦ ∑ i, y i) := by
        -- Proof comment: splitting off the final coordinate and then re-adding it recovers the
        -- full finite sum.
        funext y
        simp [sumPair, splitLast, Fin.sum_univ_castSucc, add_comm, add_left_comm]
      have htotal_eq :
          (∑ i : Fin (m + 1), ηPrefix i) + η (Fin.last (m + 1)) =
            ∑ i : Fin (m + 2), η i := by
        simpa [ηPrefix] using
          (Fin.sum_univ_castSucc (f := fun i : Fin (m + 2) ↦ η i)).symm
      -- Proof comment: factor the source at the last coordinate, sum the prefix by induction,
      -- then combine the two Gamma factors by the pair-sum theorem.
      rw [← hsum_eq]
      simpa [ηPrefix, μPrefix, μLast, htotal_eq] using hSumLaw.comp hSplit

/-- Helper for Corollary 24.29: after normalizing the tail block and converting the pair
`(head, tailSum)` into `(Beta share, total)`, reassembling the coordinates recovers the canonical
normalize-and-sum map. -/
private theorem assembleHeadTailNormalizeWithSumEq {m : ℕ} (y : Fin (m + 2) → ℝ)
    (hhead : 0 < y 0) (htail : 0 < ∑ i : Fin (m + 1), y i.succ) :
    let tailNorm := fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ
    let b := y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)
    let t := y 0 + ∑ j : Fin (m + 1), y j.succ
    (Fin.cons b (fun i ↦ (1 - b) * tailNorm i), t) =
      ((fun i ↦ y i / ∑ j, y j), ∑ j, y j) := by
  -- Proof comment: first rewrite the total mass as head plus tail mass, then compare the
  -- reassembled coordinates one by one.
  dsimp
  have hsum : (∑ j : Fin (m + 2), y j) = y 0 + ∑ j : Fin (m + 1), y j.succ := by
    simpa using (Fin.sum_univ_succ (f := y))
  refine Prod.ext ?_ ?_
  · funext i
    refine Fin.cases ?_ ?_ i
    · simp [hsum]
    · intro j
      have htotal_ne : y 0 + ∑ k : Fin (m + 1), y k.succ ≠ 0 := (add_pos hhead htail).ne'
      have hb :
          1 - y 0 / (y 0 + ∑ k : Fin (m + 1), y k.succ) =
            (∑ k : Fin (m + 1), y k.succ) / (y 0 + ∑ k : Fin (m + 1), y k.succ) := by
        field_simp [htotal_ne]
        ring_nf
      simp [Fin.cons, hsum, hb]
      field_simp [htotal_ne, htail.ne']
  · simp [hsum]

/-- Helper for Corollary 24.29: the one-dimensional normalize-and-sum transport is the base case
for the recursive Dirichlet/Gamma factorization. -/
private theorem normalizedGammaTransportEqDirichletProdGammaZero
    (η : Fin 1 → ℝ) (hη : ∀ i, 0 < η i) :
    Measure.map
      (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1) =
      (dirichletMeasure η).prod
        (ProbabilityTheory.gammaMeasure (∑ i : Fin 1, η i) 1) := by
  let ν : Measure ℝ := ProbabilityTheory.gammaMeasure (η 0) 1
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let constOne : Fin 1 → ℝ := fun _ ↦ 1
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
  have hgammaFamily :
      (fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1) = fun _ : Fin 1 ↦ ν := by
    funext i
    fin_cases i
    simp [ν]
  have hmap_e :
      Measure.map e
          (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1) =
        ν := by
    -- Proof comment: the `Fin 1` Gamma product is measurably equivalent to its unique coordinate.
    rw [hgammaFamily]
    simpa [e] using (measurePreserving_funUnique ν (Fin 1)).map_eq
  have hsource :
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1) =
        Measure.map e.symm ν := by
    -- Proof comment: invert the unique-coordinate measurable equivalence to rewrite the source.
    calc
      (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1)
          =
            Measure.map e.symm
              (Measure.map e
                (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1)) := by
              rw [Measure.map_map e.symm.measurable e.measurable]
              simp
      _ = Measure.map e.symm ν := by
            rw [hmap_e]
  have hpos : ∀ᵐ x ∂ ν, 0 < x := by
    -- Proof comment: the one-dimensional Gamma source is almost surely strictly positive.
    simpa [ν] using ae_pos_gammaMeasure_unitRate (η 0) (hη 0)
  have hDir :
      dirichletMeasure η = Measure.map (fun _ : ℝ ↦ constOne) ν := by
    -- Proof comment: normalizing a single positive Gamma coordinate yields the constant vector
    -- `1`.
    rw [dirichletMeasure_def, hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    funext i
    simp [constOne, e, hx.ne']
  have hPair :
      Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1) =
      Measure.map (fun x : ℝ ↦ (constOne, x)) ν := by
    -- Proof comment: after identifying the unique Gamma coordinate, the pair map becomes
    -- `(const 1, id)` almost surely on the positive support.
    rw [hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    ext i <;> simp [constOne, e, hx.ne']
  have hconst :
      Measure.map (fun _ : ℝ ↦ constOne) ν = Measure.dirac constOne := by
    -- Proof comment: mapping a probability measure by a constant produces the corresponding
    -- Dirac mass.
    rw [Measure.map_const]
    simp
  -- Proof comment: the joint one-dimensional law is exactly the product of the constant
  -- Dirichlet marginal with the original Gamma marginal.
  calc
    Measure.map
        (fun y : Fin 1 → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
        (Measure.pi fun i : Fin 1 ↦ ProbabilityTheory.gammaMeasure (η i) 1)
      = Measure.map (fun x : ℝ ↦ (constOne, x)) ν := hPair
    _ = (Measure.dirac constOne).prod ν := by
          simpa using (Measure.dirac_prod (ν := ν) (x := constOne)).symm
    _ = (Measure.map (fun _ : ℝ ↦ constOne) ν).prod ν := by
          rw [hconst]
    _ = (dirichletMeasure η).prod ν := by
          rw [hDir]
    _ = (dirichletMeasure η).prod
          (ProbabilityTheory.gammaMeasure (∑ i : Fin 1, η i) 1) := by
          simp [ν]

/-- Helper for Corollary 24.29: the Gamma-product source should push forward to the joint law of
the normalized vector and its total mass. -/
private theorem normalizedGammaTransportEqDirichletProdGamma {m : ℕ}
    (η : Fin (m + 1) → ℝ) (hη : ∀ i, 0 < η i) :
    Measure.map
      (fun y : Fin (m + 1) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j))
      (Measure.pi fun i : Fin (m + 1) ↦ ProbabilityTheory.gammaMeasure (η i) 1) =
      (dirichletMeasure η).prod
        (ProbabilityTheory.gammaMeasure (∑ i : Fin (m + 1), η i) 1) := by
  induction m with
  | zero =>
      -- Proof comment: the one-dimensional source is exactly the verified base case.
      simpa using normalizedGammaTransportEqDirichletProdGammaZero η hη
  | succ m ih =>
      let μ : Measure (Fin (m + 2) → ℝ) :=
        Measure.pi fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1
      let tailη : Fin (m + 1) → ℝ := fun i ↦ η i.succ
      let μHead : Measure ℝ := gammaMeasure (η 0) 1
      let μTail : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (tailη i) 1
      let νTail : Measure (Fin (m + 1) → ℝ) := dirichletMeasure tailη
      let γTail : Measure ℝ := gammaMeasure (∑ i : Fin (m + 1), tailη i) 1
      let γTotal : Measure ℝ := gammaMeasure (∑ i : Fin (m + 2), η i) 1
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
      let dropTotal : (Fin (m + 1) → ℝ) × (ℝ × ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
        fun p ↦ (p.1, p.2.1)
      let rawDecompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
        fun y ↦
          (fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ,
            y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ))
      let expanded :
          (Fin (m + 2) → ℝ) → (Fin (m + 2) → ℝ) × ℝ :=
        liftAssemble ∘ assoc3 ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead
      letI : ∀ i : Fin (m + 2), IsProbabilityMeasure (gammaMeasure (η i) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
      letI : IsProbabilityMeasure μHead := by
        dsimp [μHead]
        exact isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
      letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (tailη i) 1) := fun i ↦
        isProbabilityMeasure_gammaMeasure (hη i.succ) zero_lt_one
      letI : IsProbabilityMeasure μTail := by
        dsimp [μTail]
        infer_instance
      have hTailTotalPos : 0 < ∑ i : Fin (m + 1), tailη i := by
        -- Proof comment: the tail-parameter sum dominates its first strictly positive summand.
        let i0 : Fin (m + 1) := 0
        have hi0 : 0 < tailη i0 := hη i0.succ
        have hle : tailη i0 ≤ ∑ i : Fin (m + 1), tailη i := by
          exact Finset.single_le_sum (f := tailη) (by
            intro i hi
            exact le_of_lt (hη i.succ)) (by simp [i0])
        exact lt_of_lt_of_le hi0 hle
      have hTotalEq :
          η 0 + ∑ i : Fin (m + 1), tailη i = ∑ i : Fin (m + 2), η i := by
        simpa [tailη] using
          (Fin.sum_univ_succ (f := fun i : Fin (m + 2) ↦ η i)).symm
      have hTotalPos : 0 < ∑ i : Fin (m + 2), η i := by
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
      letI : IsProbabilityMeasure (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) :=
        isProbabilityMeasureBeta (hη 0) hTailTotalPos
      have hassembleDir_meas : Measurable assembleDir := by
        -- Proof comment: the reassembly map is coordinatewise measurable.
        refine measurable_pi_lambda _ ?_
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [assembleDir] using measurable_snd
        · intro j
          simpa [assembleDir] using (measurable_const.sub measurable_snd).mul
            ((measurable_pi_apply j).comp measurable_fst)
      have hdropTotal_meas : Measurable dropTotal := by
        fun_prop
      have hHeadPos : ∀ᵐ y ∂ μ, 0 < y 0 := by
        have hEval :
            HasLaw (Function.eval 0) (gammaMeasure (η 0) 1) μ :=
          (measurePreserving_eval (fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1) 0).hasLaw
        -- Proof comment: the head Gamma coordinate is almost surely strictly positive.
        exact (hEval.ae_iff (by fun_prop)).2 (ae_pos_gammaMeasure_unitRate (η 0) (hη 0))
      have hTailLaw :
          HasLaw
            (fun z : Fin (m + 1) → ℝ ↦ ∑ i, z i)
            γTail
            μTail := by
        simpa [γTail, μTail, tailη] using
          hasLawSumPiGamma (η := tailη) (fun i ↦ hη i.succ)
      have hTailPos : ∀ᵐ y ∂ μ, 0 < ∑ i : Fin (m + 1), y i.succ := by
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
            mapPiGammaSplitHeadEqProd (η := η) hη
        have hTailSource :
            HasLaw
              (fun y : Fin (m + 2) → ℝ ↦ ∑ i : Fin (m + 1), y i.succ)
              γTail
              μ := by
          simpa [splitHead] using hTailOnProd.comp hSplitLaw
        -- Proof comment: the tail total inherits almost-sure positivity from its Gamma law.
        exact (hTailSource.ae_iff (by fun_prop)).2
          (ae_pos_gammaMeasure_unitRate (∑ i : Fin (m + 1), tailη i) hTailTotalPos)
      have hExpanded :
          (fun y : Fin (m + 2) → ℝ ↦ ((fun i ↦ y i / ∑ j, y j), ∑ j, y j)) =ᵐ[μ] expanded := by
        -- Proof comment: on the positive Gamma source, the staged head/tail reassembly matches
        -- the canonical normalize-and-sum map.
        filter_upwards [hHeadPos, hTailPos] with y hyHead hyTail
        simpa [expanded, splitHead, normalizeTailWithSum, liftTail, assoc1, swap1, assoc2,
          ratioSum, liftRatio, assoc3, assembleDir, liftAssemble] using
          (assembleHeadTailNormalizeWithSumEq (m := m) y hyHead hyTail).symm
      have hLiftTail :
          Measure.map liftTail (μHead.prod μTail) = μHead.prod (νTail.prod γTail) := by
        -- Proof comment: only the tail block is sent through the induction hypothesis.
        rw [← Measure.map_prod_map (μa := μHead) (μc := μTail)
          (f := id) (g := normalizeTailWithSum) measurable_id (by fun_prop)]
        rw [Measure.map_id]
        rw [ih tailη (fun i ↦ hη i.succ)]
      have hAssoc1 :
          Measure.map assoc1 (μHead.prod (νTail.prod γTail)) =
            (μHead.prod νTail).prod γTail := by
        -- Proof comment: reassociate so the head coordinate sits next to the tail Dirichlet
        -- factor.
        simpa [assoc1] using (measurePreserving_prodAssoc μHead νTail γTail).symm.map_eq
      have hSwap1 :
          Measure.map swap1 ((μHead.prod νTail).prod γTail) =
            ((νTail.prod μHead).prod γTail) := by
        -- Proof comment: swap the head Gamma and tail-Dirichlet factors, keeping the carried
        -- tail sum in place.
        calc
          Measure.map swap1 ((μHead.prod νTail).prod γTail)
              = (Measure.map Prod.swap (μHead.prod νTail)).prod (Measure.map id γTail) := by
                  simpa [swap1] using
                    (Measure.map_prod_map
                      (μa := μHead.prod νTail) (μc := γTail)
                      (f := Prod.swap) (g := id) measurable_swap measurable_id).symm
          _ = (Measure.map Prod.swap (μHead.prod νTail)).prod γTail := by
                rw [Measure.map_id]
          _ = ((νTail.prod μHead).prod γTail) := by
                rw [Measure.prod_swap]
      have hAssoc2 :
          Measure.map assoc2 ((νTail.prod μHead).prod γTail) =
            νTail.prod (μHead.prod γTail) := by
        -- Proof comment: now isolate the pair `(head, tailTotal)` as the second factor.
        simpa [assoc2] using
          (Measure.prodAssoc_prod (μ := νTail) (ν := μHead) (τ := γTail))
      have hLiftRatio :
          Measure.map liftRatio (νTail.prod (μHead.prod γTail)) =
            νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal) := by
        -- Proof comment: transport only the isolated `(head, tailTotal)` pair through the
        -- Beta-Gamma ratio/sum theorem.
        have hRatio :
            Measure.map ratioSum (μHead.prod γTail) =
              (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal := by
          simpa [ratioSum, μHead, γTail, γTotal, hTotalEq] using
            map_gammaPair_toRatioSum_eq_prod_beta_gamma
              (θ₁ := η 0) (θ₂ := ∑ i : Fin (m + 1), tailη i) (hη 0) hTailTotalPos
        rw [← Measure.map_prod_map (μa := νTail) (μc := μHead.prod γTail)
          (f := id) (g := ratioSum) measurable_id (by fun_prop)]
        rw [Measure.map_id]
        rw [hRatio]
      have hRawMap :
          Measure.map rawDecompose μ =
            νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
        have hRawEq :
            rawDecompose =
              dropTotal ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead := by
          funext y
          rfl
        have hDropTotal :
            Measure.map dropTotal
                (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) =
              νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
          calc
            Measure.map dropTotal
                (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal))
                =
                  (Measure.map id νTail).prod
                    (Measure.map Prod.fst
                      ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
                        simpa [dropTotal] using
                          (Measure.map_prod_map
                            (μa := νTail)
                            (μc := (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)
                            (f := id) (g := Prod.fst) measurable_id measurable_fst).symm
            _ = νTail.prod
                  (Measure.map Prod.fst
                    ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
                  rw [Measure.map_id]
            _ = νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
                  rw [(measurePreserving_fst
                    (μ := betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))
                    (ν := γTotal)).map_eq]
        calc
          Measure.map rawDecompose μ
              = Measure.map
                  (dropTotal ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead) μ := by
                    rw [hRawEq]
          _ = Measure.map dropTotal
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail
                          (Measure.map splitHead μ)))))) := by
                rw [← Measure.map_map hdropTotal_meas (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
                rw [← Measure.map_map (by fun_prop) (by fun_prop)]
          _ = Measure.map dropTotal
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail (μHead.prod μTail)))))) := by
                rw [mapPiGammaSplitHeadEqProd (η := η) hη]
          _ = Measure.map dropTotal
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (μHead.prod (νTail.prod γTail)))))) := by
                rw [hLiftTail]
          _ = Measure.map dropTotal
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      ((μHead.prod νTail).prod γTail)))) := by
                rw [hAssoc1]
          _ = Measure.map dropTotal
                (Measure.map liftRatio
                  (Measure.map assoc2 (((νTail.prod μHead).prod γTail)))) := by
                rw [hSwap1]
          _ = Measure.map dropTotal
                (Measure.map liftRatio (νTail.prod (μHead.prod γTail))) := by
                rw [hAssoc2]
          _ = Measure.map dropTotal
                (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
                rw [hLiftRatio]
          _ = νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
                rw [hDropTotal]
      have hAssemble :
          Measure.map assembleDir
              (νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))) =
            dirichletMeasure η := by
        have hCompose :
            (fun y : Fin (m + 2) → ℝ ↦ assembleDir (rawDecompose y)) =ᵐ[μ]
              (fun y : Fin (m + 2) → ℝ ↦ fun i ↦ y i / ∑ j, y j) := by
          -- Proof comment: reassembling the raw head/tail normalization recovers the normalized
          -- source vector on the positive Gamma support.
          filter_upwards [hHeadPos, hTailPos] with y hyHead hyTail
          simpa [rawDecompose, assembleDir] using
            congrArg Prod.fst (assembleHeadTailNormalizeWithSumEq (m := m) y hyHead hyTail)
        calc
          Measure.map assembleDir
              (νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)))
              =
                Measure.map assembleDir (Measure.map rawDecompose μ) := by
                  rw [hRawMap]
          _ = Measure.map (assembleDir ∘ rawDecompose) μ := by
                rw [Measure.map_map hassembleDir_meas (by fun_prop)]
          _ = Measure.map (fun y : Fin (m + 2) → ℝ ↦ fun i ↦ y i / ∑ j, y j) μ := by
                exact Measure.map_congr hCompose
          _ = dirichletMeasure η := by
                rw [dirichletMeasure_def]
      have hLiftAssemble :
          Measure.map liftAssemble
              ((νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))).prod γTotal) =
            (dirichletMeasure η).prod γTotal := by
        -- Proof comment: reassemble the Dirichlet/Beta factors, while carrying the total Gamma
        -- mass through untouched.
        calc
          Measure.map liftAssemble
              ((νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))).prod γTotal)
              =
                (Measure.map assembleDir
                  (νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)))).prod γTotal := by
                    simpa [liftAssemble] using
                      (Measure.map_prod_map
                        (μa := νTail.prod
                          (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)))
                        (μc := γTotal)
                        (f := assembleDir) (g := id) hassembleDir_meas measurable_id).symm
          _ = (dirichletMeasure η).prod γTotal := by
                rw [hAssemble]
      -- Proof comment: replace the canonical normalize-and-sum map by the staged head/tail
      -- composite on the positive Gamma support, then run the split/IH/Beta-Gamma/reassembly
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
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rfl
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (Measure.map liftRatio
                  (Measure.map assoc2
                    (Measure.map swap1
                      (Measure.map assoc1
                        (Measure.map liftTail (μHead.prod μTail))))))) := by
                rw [mapPiGammaSplitHeadEqProd (η := η) hη]
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
                (Measure.map liftRatio (νTail.prod (μHead.prod γTail)))) := by
                rw [hAssoc2]
        _ = Measure.map liftAssemble
              (Measure.map assoc3
                (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal))) := by
                rw [hLiftRatio]
        _ = Measure.map liftAssemble
              ((νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))).prod γTotal) := by
                rw [show
                  Measure.map assoc3
                      (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) =
                    ((νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))).prod γTotal) by
                      simpa [assoc3] using
                        (measurePreserving_prodAssoc
                          νTail
                          (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))
                          γTotal).symm.map_eq]
        _ = (dirichletMeasure η).prod γTotal := by
                rw [hLiftAssemble]
        _ = (dirichletMeasure η).prod
              (gammaMeasure (∑ i : Fin (m + 2), η i) 1) := by
                rfl

/-- Helper for Corollary 24.29: on the positive Gamma source, the head/tail decomposition of the
normalized vector agrees with the raw tail normalization and Beta ratio. -/
private theorem headTailDecomposeNormalizeEq {m : ℕ} (y : Fin (m + 2) → ℝ)
    (hhead : 0 < y 0) (htail : 0 < ∑ i : Fin (m + 1), y i.succ) :
    (fun i : Fin (m + 1) ↦
      (y i.succ / ∑ j : Fin (m + 2), y j) / (1 - y 0 / ∑ j : Fin (m + 2), y j),
      y 0 / ∑ j : Fin (m + 2), y j) =
      (fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ,
        y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)) := by
  have hsum :
      ∑ j : Fin (m + 2), y j = y 0 + ∑ j : Fin (m + 1), y j.succ := by
    simpa using (Fin.sum_univ_succ (f := y))
  have htotal : 0 < ∑ j : Fin (m + 2), y j := by
    rw [hsum]
    exact add_pos hhead htail
  have hb :
      1 - y 0 / ∑ j : Fin (m + 2), y j =
        (∑ j : Fin (m + 1), y j.succ) / ∑ j : Fin (m + 2), y j := by
    rw [hsum]
    field_simp [htotal.ne']
    ring_nf
  refine Prod.ext ?_ ?_
  · funext i
    rw [hb]
    field_simp [htail.ne', htotal.ne']
  · simp [hsum]

/-- Helper for Corollary 24.29: the Dirichlet law should decompose into the renormalized tail and
the first Beta coordinate. -/
private theorem mapGammaHeadTailToDirichletBeta {m : ℕ} (η : Fin (m + 2) → ℝ)
    (hη : ∀ i, 0 < η i) :
    Measure.map
      (fun y : Fin (m + 2) → ℝ ↦
        (fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ,
          y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ)))
      (Measure.pi fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1) =
      (dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)) := by
  let μ : Measure (Fin (m + 2) → ℝ) :=
    Measure.pi fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1
  let tailη : Fin (m + 1) → ℝ := fun i ↦ η i.succ
  let μHead : Measure ℝ := gammaMeasure (η 0) 1
  let μTail : Measure (Fin (m + 1) → ℝ) :=
    Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (tailη i) 1
  let νTail : Measure (Fin (m + 1) → ℝ) := dirichletMeasure tailη
  let γTail : Measure ℝ := gammaMeasure (∑ i : Fin (m + 1), tailη i) 1
  let γTotal : Measure ℝ := gammaMeasure (∑ i : Fin (m + 2), η i) 1
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
  let dropTotal : (Fin (m + 1) → ℝ) × (ℝ × ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
    fun p ↦ (p.1, p.2.1)
  let rawDecompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
    fun y ↦
      (fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ,
        y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ))
  letI : ∀ i : Fin (m + 2), IsProbabilityMeasure (gammaMeasure (η i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  letI : IsProbabilityMeasure μHead := by
    dsimp [μHead]
    exact isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
  letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (tailη i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hη i.succ) zero_lt_one
  letI : IsProbabilityMeasure μTail := by
    dsimp [μTail]
    infer_instance
  have hTailTotalPos : 0 < ∑ i : Fin (m + 1), tailη i := by
    -- Proof comment: the tail parameter sum dominates its first strictly positive summand.
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < tailη i0 := hη i0.succ
    have hle : tailη i0 ≤ ∑ i : Fin (m + 1), tailη i := by
      exact Finset.single_le_sum (f := tailη) (by
        intro i hi
        exact le_of_lt (hη i.succ)) (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  have hTotalEq :
      η 0 + ∑ i : Fin (m + 1), tailη i = ∑ i : Fin (m + 2), η i := by
    simpa [tailη] using
      (Fin.sum_univ_succ (f := fun i : Fin (m + 2) ↦ η i)).symm
  have hTotalPos : 0 < ∑ i : Fin (m + 2), η i := by
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
  letI : IsProbabilityMeasure (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) :=
    isProbabilityMeasureBeta (hη 0) hTailTotalPos
  have hdropTotal_meas : Measurable dropTotal := by
    fun_prop
  have hLiftTail :
      Measure.map liftTail (μHead.prod μTail) = μHead.prod (νTail.prod γTail) := by
    -- Proof comment: reuse the normalized-Gamma transport theorem on the tail block.
    rw [← Measure.map_prod_map (μa := μHead) (μc := μTail)
      (f := id) (g := normalizeTailWithSum) measurable_id (by fun_prop)]
    rw [Measure.map_id]
    rw [normalizedGammaTransportEqDirichletProdGamma tailη (fun i ↦ hη i.succ)]
  have hAssoc1 :
      Measure.map assoc1 (μHead.prod (νTail.prod γTail)) =
        (μHead.prod νTail).prod γTail := by
    simpa [assoc1] using (measurePreserving_prodAssoc μHead νTail γTail).symm.map_eq
  have hSwap1 :
      Measure.map swap1 ((μHead.prod νTail).prod γTail) =
        ((νTail.prod μHead).prod γTail) := by
    calc
      Measure.map swap1 ((μHead.prod νTail).prod γTail)
          = (Measure.map Prod.swap (μHead.prod νTail)).prod (Measure.map id γTail) := by
              simpa [swap1] using
                (Measure.map_prod_map
                  (μa := μHead.prod νTail) (μc := γTail)
                  (f := Prod.swap) (g := id) measurable_swap measurable_id).symm
      _ = (Measure.map Prod.swap (μHead.prod νTail)).prod γTail := by
            rw [Measure.map_id]
      _ = ((νTail.prod μHead).prod γTail) := by
            rw [Measure.prod_swap]
  have hAssoc2 :
      Measure.map assoc2 ((νTail.prod μHead).prod γTail) =
        νTail.prod (μHead.prod γTail) := by
    simpa [assoc2] using
      (Measure.prodAssoc_prod (μ := νTail) (ν := μHead) (τ := γTail))
  have hLiftRatio :
      Measure.map liftRatio (νTail.prod (μHead.prod γTail)) =
        νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal) := by
    have hRatio :
        Measure.map ratioSum (μHead.prod γTail) =
          (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal := by
      simpa [ratioSum, μHead, γTail, γTotal, hTotalEq] using
        map_gammaPair_toRatioSum_eq_prod_beta_gamma
          (θ₁ := η 0) (θ₂ := ∑ i : Fin (m + 1), tailη i) (hη 0) hTailTotalPos
    rw [← Measure.map_prod_map (μa := νTail) (μc := μHead.prod γTail)
      (f := id) (g := ratioSum) measurable_id (by fun_prop)]
    rw [Measure.map_id]
    rw [hRatio]
  have hDropTotal :
      Measure.map dropTotal
          (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) =
        νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
    calc
      Measure.map dropTotal
          (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal))
          =
            (Measure.map id νTail).prod
              (Measure.map Prod.fst
                ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
                  simpa [dropTotal] using
                    (Measure.map_prod_map
                      (μa := νTail)
                      (μc := (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)
                      (f := id) (g := Prod.fst) measurable_id measurable_fst).symm
      _ = νTail.prod
            (Measure.map Prod.fst
              ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
            rw [Measure.map_id]
      _ = νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
            rw [(measurePreserving_fst
              (μ := betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i))
              (ν := γTotal)).map_eq]
  have hRawEq :
      rawDecompose =
        dropTotal ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead := by
    funext y
    rfl
  -- Proof comment: split off the first Gamma coordinate, transport the tail block by the
  -- normalized-Gamma theorem, then apply the Beta/Gamma ratio-sum theorem and drop the carried
  -- total mass.
  calc
    Measure.map rawDecompose μ
        = Measure.map
            (dropTotal ∘ liftRatio ∘ assoc2 ∘ swap1 ∘ assoc1 ∘ liftTail ∘ splitHead) μ := by
              rw [hRawEq]
    _ = Measure.map dropTotal
          (Measure.map liftRatio
            (Measure.map assoc2
              (Measure.map swap1
                (Measure.map assoc1
                  (Measure.map liftTail
                    (Measure.map splitHead μ)))))) := by
            rw [← Measure.map_map hdropTotal_meas (by fun_prop)]
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
            rw [← Measure.map_map (by fun_prop) (by fun_prop)]
    _ = Measure.map dropTotal
          (Measure.map liftRatio
            (Measure.map assoc2
              (Measure.map swap1
                (Measure.map assoc1
                  (Measure.map liftTail (μHead.prod μTail)))))) := by
            rw [mapPiGammaSplitHeadEqProd (η := η) hη]
    _ = Measure.map dropTotal
          (Measure.map liftRatio
            (Measure.map assoc2
              (Measure.map swap1
                (Measure.map assoc1
                  (μHead.prod (νTail.prod γTail)))))) := by
            rw [hLiftTail]
    _ = Measure.map dropTotal
          (Measure.map liftRatio
            (Measure.map assoc2
              (Measure.map swap1 ((μHead.prod νTail).prod γTail)))) := by
            rw [hAssoc1]
    _ = Measure.map dropTotal
          (Measure.map liftRatio
            (Measure.map assoc2 (((νTail.prod μHead).prod γTail)))) := by
            rw [hSwap1]
    _ = Measure.map dropTotal
          (Measure.map liftRatio (νTail.prod (μHead.prod γTail))) := by
            rw [hAssoc2]
    _ = Measure.map dropTotal
          (νTail.prod ((betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)).prod γTotal)) := by
            rw [hLiftRatio]
    _ = νTail.prod (betaMeasure (η 0) (∑ i : Fin (m + 1), tailη i)) := by
            rw [hDropTotal]

/-- Corollary 24.29: under the Dirichlet law, the head/tail decomposition has product law
`Dir(tail η) × Beta(η₀, tailSum)`. -/
theorem hasLawDirichletHeadTailDecompose {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i, 0 < η i) :
    HasLaw
      (fun x : Fin (m + 2) → ℝ ↦
        (fun i : Fin (m + 1) ↦ x i.succ / (1 - x 0), x 0))
      ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)))
      (dirichletMeasure η) := by
  let μ : Measure (Fin (m + 2) → ℝ) :=
    Measure.pi fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1
  let decompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
    fun x ↦ (fun i : Fin (m + 1) ↦ x i.succ / (1 - x 0), x 0)
  let rawDecompose : (Fin (m + 2) → ℝ) → (Fin (m + 1) → ℝ) × ℝ :=
    fun y ↦
      (fun i : Fin (m + 1) ↦ y i.succ / ∑ j : Fin (m + 1), y j.succ,
        y 0 / (y 0 + ∑ j : Fin (m + 1), y j.succ))
  letI : ∀ i : Fin (m + 2), IsProbabilityMeasure (gammaMeasure (η i) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hη i) zero_lt_one
  have hHeadPos : ∀ᵐ y ∂ μ, 0 < y 0 := by
    have hEval :
        HasLaw (Function.eval 0) (gammaMeasure (η 0) 1) μ :=
      (measurePreserving_eval (fun i : Fin (m + 2) ↦ gammaMeasure (η i) 1) 0).hasLaw
    -- Proof comment: the first Gamma coordinate is almost surely strictly positive.
    exact (hEval.ae_iff (by fun_prop)).2 (ae_pos_gammaMeasure_unitRate (η 0) (hη 0))
  have hTailPos : ∀ᵐ y ∂ μ, 0 < ∑ i : Fin (m + 1), y i.succ := by
    let tailη : Fin (m + 1) → ℝ := fun i ↦ η i.succ
    have hTailTotalPos : 0 < ∑ i : Fin (m + 1), tailη i := by
      -- Proof comment: the tail-parameter sum dominates its first positive coordinate.
      let i0 : Fin (m + 1) := 0
      have hi0 : 0 < tailη i0 := hη i0.succ
      have hle : tailη i0 ≤ ∑ i : Fin (m + 1), tailη i := by
        exact Finset.single_le_sum (f := tailη) (by
          intro i hi
          exact le_of_lt (hη i.succ)) (by simp [i0])
      exact lt_of_lt_of_le hi0 hle
    have hTailLaw :
        HasLaw
          (fun y : Fin (m + 1) → ℝ ↦ ∑ i, y i)
          (gammaMeasure (∑ i : Fin (m + 1), tailη i) 1)
          (Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (tailη i) 1) := by
      simpa [tailη] using hasLawSumPiGamma (η := tailη) (fun i ↦ hη i.succ)
    let μHead : Measure ℝ := gammaMeasure (η 0) 1
    let μTail : Measure (Fin (m + 1) → ℝ) :=
      Measure.pi fun i : Fin (m + 1) ↦ gammaMeasure (tailη i) 1
    let splitHead : (Fin (m + 2) → ℝ) → ℝ × (Fin (m + 1) → ℝ) :=
      fun y ↦ (y 0, fun i : Fin (m + 1) ↦ y i.succ)
    letI : IsProbabilityMeasure μHead := by
      dsimp [μHead]
      exact isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
    letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (tailη i) 1) := fun i ↦
      isProbabilityMeasure_gammaMeasure (hη i.succ) zero_lt_one
    letI : IsProbabilityMeasure μTail := by
      dsimp [μTail]
      infer_instance
    have hTailOnProd :
        HasLaw
          (fun p : ℝ × (Fin (m + 1) → ℝ) ↦ ∑ i, p.2 i)
          (gammaMeasure (∑ i : Fin (m + 1), tailη i) 1)
          (μHead.prod μTail) := by
      simpa using hTailLaw.comp ((measurePreserving_snd (μ := μHead) (ν := μTail)).hasLaw)
    have hSplitLaw :
        HasLaw splitHead (μHead.prod μTail) μ := by
      refine ⟨by fun_prop, ?_⟩
      simpa [μ, μHead, μTail, splitHead, tailη] using mapPiGammaSplitHeadEqProd (η := η) hη
    have hTailSource :
        HasLaw
          (fun y : Fin (m + 2) → ℝ ↦ ∑ i : Fin (m + 1), y i.succ)
          (gammaMeasure (∑ i : Fin (m + 1), tailη i) 1)
          μ := by
      simpa [splitHead] using hTailOnProd.comp hSplitLaw
    -- Proof comment: the tail total is positive almost surely because it has Gamma law.
    exact (hTailSource.ae_iff (by fun_prop)).2
      (ae_pos_gammaMeasure_unitRate (∑ i : Fin (m + 1), tailη i) hTailTotalPos)
  refine ⟨by fun_prop, ?_⟩
  -- Route correction: rewrite the Dirichlet law back to the normalized Gamma source and compare
  -- the head/tail decomposition with the raw head/tail Gamma coordinates on the positive source.
  rw [dirichletMeasure_def, Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    Measure.map (decompose ∘ fun y i ↦ y i / ∑ j, y j) μ
        = Measure.map rawDecompose μ := by
            refine Measure.map_congr ?_
            filter_upwards [hHeadPos, hTailPos] with y hyHead hyTail
            simpa [decompose, rawDecompose, Function.comp] using
              headTailDecomposeNormalizeEq (m := m) y hyHead hyTail
    _ = (dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
          (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)) := by
            simpa using mapGammaHeadTailToDirichletBeta (η := η) hη

-- Proof sketch: project the normalized-Gamma realization of the Dirichlet law onto the first
-- coordinate and identify the resulting ratio law with the Beta distribution having parameters
-- `θ 0` and the sum of the remaining coordinates.
/-- First marginal consequence of Corollary 24.29: for a Dirichlet-distributed `(n + 1)`-tuple,
the first coordinate has Beta law with parameters `θ 0` and `∑ i, θ i.succ`, assuming the tail
block is nonempty. -/
theorem hasLaw_fst_beta_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hn : 0 < n) (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω ↦ X ω 0) (betaMeasure (θ 0) (∑ i : Fin n, θ i.succ)) μ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  let decompose : Ω → (Fin (m + 1) → ℝ) × ℝ :=
    fun ω ↦ (fun i : Fin (m + 1) ↦ X ω i.succ / (1 - X ω 0), X ω 0)
  have hTailPos : 0 < ∑ i : Fin (m + 1), θ i.succ := by
    -- Proof comment: the tail shape sum dominates its first strictly positive coordinate.
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < θ i0.succ := hθ i0.succ
    have hle : θ i0.succ ≤ ∑ i : Fin (m + 1), θ i.succ := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ θ i.succ) (by
        intro i hi
        exact le_of_lt (hθ i.succ)) (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (θ i.succ) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ i.succ) zero_lt_one
  letI : IsProbabilityMeasure (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) := by
    rw [dirichletMeasure_def]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)) :=
    isProbabilityMeasureBeta (hθ 0) hTailPos
  have hDecompose :
      HasLaw decompose
        ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
          (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) μ := by
    -- Proof comment: transfer the Dirichlet law of `X` through the head/tail decomposition.
    simpa [decompose] using
      (hasLawDirichletHeadTailDecompose (η := θ) hθ).comp hX
  have hProj :
      HasLaw Prod.snd
        (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))
        ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
          (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) :=
    (measurePreserving_snd
      (μ := dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ)
      (ν := betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))).hasLaw
  -- Proof comment: the first coordinate of the original Dirichlet vector is the second
  -- projection of the tail/head decomposition pair.
  simpa [Function.comp, decompose] using hProj.comp hDecompose

-- Proof sketch: rewrite the residual coordinates as the normalized tail of the Gamma realization
-- from the Dirichlet law, then remove the first Gamma coordinate and apply the same normalized
-- Gamma description to the remaining parameter vector.
/-- Tail-marginal consequence of Corollary 24.29: after dividing the remaining coordinates by
`1 - X₁`, the residual vector again has Dirichlet law with the tail parameter vector, assuming
the tail block is nonempty. -/
theorem hasLaw_tail_dirichlet_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hn : 0 < n) (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    HasLaw (fun ω ↦ fun i : Fin n ↦ X ω i.succ / (1 - X ω 0))
      (dirichletMeasure fun i : Fin n ↦ θ i.succ) μ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  let decompose : Ω → (Fin (m + 1) → ℝ) × ℝ :=
    fun ω ↦ (fun i : Fin (m + 1) ↦ X ω i.succ / (1 - X ω 0), X ω 0)
  have hTailPos : 0 < ∑ i : Fin (m + 1), θ i.succ := by
    -- Proof comment: the tail shape sum dominates its first strictly positive coordinate.
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < θ i0.succ := hθ i0.succ
    have hle : θ i0.succ ≤ ∑ i : Fin (m + 1), θ i.succ := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ θ i.succ) (by
        intro i hi
        exact le_of_lt (hθ i.succ)) (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (θ i.succ) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ i.succ) zero_lt_one
  letI : IsProbabilityMeasure (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) := by
    rw [dirichletMeasure_def]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsProbabilityMeasure (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)) :=
    isProbabilityMeasureBeta (hθ 0) hTailPos
  have hDecompose :
      HasLaw decompose
        ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
          (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) μ := by
    -- Proof comment: transfer the Dirichlet law of `X` through the head/tail decomposition.
    simpa [decompose] using
      (hasLawDirichletHeadTailDecompose (η := θ) hθ).comp hX
  have hProj :
      HasLaw Prod.fst
        (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ)
        ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
          (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) :=
    (measurePreserving_fst
      (μ := dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ)
      (ν := betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))).hasLaw
  -- Proof comment: the renormalized tail is the first projection of the decomposition pair.
  simpa [Function.comp, decompose] using hProj.comp hDecompose

-- Proof sketch: in the normalized-Gamma model, the first ratio depends only on the first Gamma
-- variable and the remaining total mass, while the residual vector depends only on the normalized
-- tail; the independent Gamma coordinates then give the claimed independence.
/-- Independence consequence of Corollary 24.29: the first Dirichlet coordinate is independent of
the renormalized tail vector, assuming the tail block is nonempty. -/
theorem indepFun_fst_tail_of_hasLaw_dirichlet
    {n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → Fin (n + 1) → ℝ}
    {θ : Fin (n + 1) → ℝ} (hn : 0 < n) (hθ : ∀ i, 0 < θ i)
    (hX : HasLaw X (dirichletMeasure θ) μ) :
    IndepFun (fun ω ↦ X ω 0) (fun ω ↦ fun i : Fin n ↦ X ω i.succ / (1 - X ω 0)) μ := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
  let head : Ω → ℝ := fun ω ↦ X ω 0
  let tail : Ω → Fin (m + 1) → ℝ := fun ω i ↦ X ω i.succ / (1 - X ω 0)
  let decompose : Ω → (Fin (m + 1) → ℝ) × ℝ := fun ω ↦ (tail ω, head ω)
  have hTailPos : 0 < ∑ i : Fin (m + 1), θ i.succ := by
    -- Proof comment: the tail shape sum dominates its first strictly positive coordinate.
    let i0 : Fin (m + 1) := 0
    have hi0 : 0 < θ i0.succ := hθ i0.succ
    have hle : θ i0.succ ≤ ∑ i : Fin (m + 1), θ i.succ := by
      exact Finset.single_le_sum (f := fun i : Fin (m + 1) ↦ θ i.succ) (by
        intro i hi
        exact le_of_lt (hθ i.succ)) (by simp [i0])
    exact lt_of_lt_of_le hi0 hle
  letI : ∀ i : Fin (m + 1), IsProbabilityMeasure (gammaMeasure (θ i.succ) 1) := fun i ↦
    isProbabilityMeasure_gammaMeasure (hθ i.succ) zero_lt_one
  letI : IsProbabilityMeasure (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) := by
    rw [dirichletMeasure_def]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : SFinite (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) := by
    infer_instance
  letI : IsProbabilityMeasure (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)) :=
    isProbabilityMeasureBeta (hθ 0) hTailPos
  letI : SFinite (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)) := by
    infer_instance
  have hHead :
      HasLaw head
        (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)) μ := by
    -- Proof comment: reuse the proved first-coordinate marginal.
    simpa [head] using
      hasLaw_fst_beta_of_hasLaw_dirichlet (μ := μ) (X := X) (θ := θ) (n := m + 1)
        (hn := Nat.succ_pos m) hθ hX
  have hTail :
      HasLaw tail
        (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) μ := by
    -- Proof comment: reuse the proved renormalized-tail marginal.
    simpa [tail] using
      hasLaw_tail_dirichlet_of_hasLaw_dirichlet (μ := μ) (X := X) (θ := θ) (n := m + 1)
        (hn := Nat.succ_pos m) hθ hX
  have hDecompose :
      HasLaw decompose
        ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
          (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) μ := by
    -- Proof comment: this is the tail/head product law supplied by the source-side
    -- decomposition theorem.
    simpa [decompose] using
      (hasLawDirichletHeadTailDecompose (η := θ) hθ).comp hX
  -- Proof comment: swap the decomposition law into head/tail order and compare it with the two
  -- marginal laws.
  refine (indepFun_iff_map_prod_eq_prod_map_map hHead.aemeasurable hTail.aemeasurable).2 ?_
  calc
    Measure.map (fun ω ↦ (head ω, tail ω)) μ
        = Measure.map Prod.swap (Measure.map decompose μ) := by
            rw [show (fun ω ↦ (head ω, tail ω)) = Prod.swap ∘ decompose by
              funext ω
              rfl,
              ← AEMeasurable.map_map_of_aemeasurable
                measurable_swap.aemeasurable hDecompose.aemeasurable]
    _ = Measure.map Prod.swap
          (((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
            (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)))) := by
            rw [hDecompose.map_eq]
    _ = (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)).prod
          (dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ) := by
          rw [Measure.prod_swap]
    _ = (Measure.map head μ).prod (Measure.map tail μ) := by
          rw [hHead.map_eq, hTail.map_eq]

end ProbabilityTheory
