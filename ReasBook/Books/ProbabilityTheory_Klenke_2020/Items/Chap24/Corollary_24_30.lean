/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_29
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_33
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Semantic recall: reuse the chapter's canonical `ProbabilityTheory.dirichletMeasure` and finite
-- stick-breaking API, rather than reintroducing duplicate public wrappers here.
/-- The sum of the parameters strictly following the `i`th stick-breaking factor. -/
private def stickBreakingTailSum {n : ℕ} (θ : Fin (n + 1) → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ i.castSucc < j), θ j

/-- Helper for Corollary 24.30: each tail parameter sum contains the next strictly positive
coordinate, hence is itself strictly positive. -/
private theorem stickBreakingTailSum_pos {n : ℕ} {θ : Fin (n + 1) → ℝ}
    (hθ : ∀ i : Fin (n + 1), 0 < θ i) (i : Fin n) :
    0 < stickBreakingTailSum θ i := by
  -- Proof comment: the tail block contains the immediate successor coordinate `i.succ`.
  have hle : θ i.succ ≤ stickBreakingTailSum θ i := by
    unfold stickBreakingTailSum
    exact Finset.single_le_sum (f := θ) (by
      intro j hj
      exact le_of_lt (hθ j)) (by
      simp [Fin.castSucc_lt_succ_iff])
  exact lt_of_lt_of_le (hθ i.succ) hle

/-- Helper for Corollary 24.30: the initial tail sum is the sum of the remaining coordinates. -/
private theorem stickBreakingTailSum_zero {m : ℕ} (θ : Fin (m + 2) → ℝ) :
    stickBreakingTailSum θ 0 = ∑ i : Fin (m + 1), θ i.succ := by
  -- Proof comment: filtering out the initial index leaves exactly the successor coordinates.
  unfold stickBreakingTailSum
  have hfilter :
      Finset.univ.filter (fun j : Fin (m + 2) ↦ (0 : Fin (m + 1)).castSucc < j) =
        (Finset.univ : Finset (Fin (m + 1))).map ⟨Fin.succ, Fin.succ_injective _⟩ := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      simp
  rw [hfilter, Finset.sum_map]
  simp

/-- Helper for Corollary 24.30: tail sums for the shifted parameter vector agree with the
corresponding shifted tail sums of the original parameter vector. -/
-- TODO: identify both filtered sums by transporting the index set along `Fin.succ`.
private theorem stickBreakingTailSum_succ {m : ℕ} (η : Fin (m + 2) → ℝ) (i : Fin m) :
    stickBreakingTailSum (fun j : Fin (m + 1) ↦ η j.succ) i =
      stickBreakingTailSum η i.succ := by
  -- Proof comment: the shifted tail block is indexed by the same successor coordinates on both
  -- sides.
  unfold stickBreakingTailSum
  have hfilter :
      (Finset.univ.filter (fun j : Fin (m + 1) ↦ i.castSucc < j)).map
          ⟨Fin.succ, Fin.succ_injective _⟩ =
        Finset.univ.filter (fun j : Fin (m + 2) ↦ i.succ.castSucc < j) := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      simp
  have hsum :
      (∑ j ∈ Finset.univ.filter (fun j : Fin (m + 1) ↦ i.castSucc < j), η j.succ) =
        Finset.sum
          ((Finset.univ.filter (fun j : Fin (m + 1) ↦ i.castSucc < j)).map
            ⟨Fin.succ, Fin.succ_injective _⟩)
          η := by
    rw [Finset.sum_map]
    simp
  rw [hsum, hfilter]

/-- Helper for Corollary 24.30: in dimension `1`, the Dirichlet law is the Dirac mass at the
constant vector `1`. -/
private theorem dirichletMeasure_finOne_eq_dirac_constOne {η : Fin 1 → ℝ}
    (hη : ∀ i : Fin 1, 0 < η i) :
    dirichletMeasure η = Measure.dirac (fun _ : Fin 1 ↦ 1) := by
  let ν : Measure ℝ := gammaMeasure (η 0) 1
  let e : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let constOne : Fin 1 → ℝ := fun _ ↦ 1
  letI : IsProbabilityMeasure ν := by
    simpa [ν] using isProbabilityMeasure_gammaMeasure (hη 0) zero_lt_one
  have hgammaFamily :
      (fun i : Fin 1 ↦ gammaMeasure (η i) 1) = fun _ : Fin 1 ↦ gammaMeasure (η 0) 1 := by
    funext i
    rw [Subsingleton.elim i 0]
  have hsource :
      (Measure.pi fun i : Fin 1 ↦ gammaMeasure (η i) 1) = Measure.map e.symm ν := by
    have hmap : Measure.map e (Measure.pi fun i : Fin 1 ↦ gammaMeasure (η i) 1) = ν := by
      -- Proof comment: the `Fin 1` Gamma product is measurably equivalent to its unique
      -- coordinate law.
      rw [hgammaFamily]
      simpa [ν, e] using (measurePreserving_funUnique ν (Fin 1)).map_eq
    calc
      (Measure.pi fun i : Fin 1 ↦ gammaMeasure (η i) 1)
          =
            Measure.map e.symm
              (Measure.map e (Measure.pi fun i : Fin 1 ↦ gammaMeasure (η i) 1)) := by
                rw [Measure.map_map e.symm.measurable e.measurable]
                simp
      _ = Measure.map e.symm ν := by
            rw [hmap]
  have hpos : ∀ᵐ x ∂ ν, 0 < x := by
    -- Proof comment: the unique Gamma coordinate is almost surely strictly positive.
    simpa [ν] using ae_pos_gammaMeasure_unitRate (η 0) (hη 0)
  have hdir :
      dirichletMeasure η = Measure.map (fun _ : ℝ ↦ constOne) ν := by
    -- Proof comment: normalizing a one-dimensional positive vector gives the constant value `1`.
    rw [dirichletMeasure_def, hsource, Measure.map_map (by fun_prop) e.symm.measurable]
    refine Measure.map_congr ?_
    filter_upwards [hpos] with x hx
    funext i
    simp [constOne, e, hx.ne']
  -- Proof comment: a constant pushforward of a probability measure is the corresponding Dirac
  -- mass.
  rw [hdir, Measure.map_const]
  simp [constOne]

/-- Helper for Corollary 24.30: splitting off the head Beta coordinate factors the Beta-product
source into the tail Beta product together with the head Beta marginal. -/
private theorem map_piBeta_split_head_eq_prod {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i : Fin (m + 2), 0 < η i) :
    ((Measure.pi fun i : Fin (m + 1) ↦ betaMeasure (η i.castSucc) (stickBreakingTailSum η i)).map
      (fun x ↦ ((fun i : Fin m ↦ x i.succ), x 0))) =
      (Measure.pi fun i : Fin m ↦
        betaMeasure ((fun j : Fin (m + 1) ↦ η j.succ) i.castSucc)
          (stickBreakingTailSum (fun j : Fin (m + 1) ↦ η j.succ) i)).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)) := by
  let μ : Fin (m + 1) → Measure ℝ :=
    fun i ↦ betaMeasure (η i.castSucc) (stickBreakingTailSum η i)
  let splitHead : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
    fun x ↦ (Fin.tail x, x 0)
  letI : ∀ i, IsProbabilityMeasure (μ i) := fun i ↦ by
    dsimp [μ]
    exact isProbabilityMeasureBeta (hη i.castSucc) (stickBreakingTailSum_pos hη i)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0
  have hMapEq :
      (Measure.pi μ).map e =
        (μ 0).prod (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i)) :=
    (measurePreserving_piFinSuccAbove μ 0).map_eq
  have hSplitHead : splitHead = Prod.swap ∘ e := by
    -- Proof comment: `piFinSuccAbove` at `0` exposes the head coordinate first, so one swap puts
    -- the tail block in front.
    funext x
    ext i
    · simp [splitHead, Function.comp, e]
    · simp [splitHead, Function.comp, e]
  -- Proof comment: factor the Beta product through `piFinSuccAbove` and rewrite the shifted tail
  -- parameters once, outside the later induction.
  calc
    ((Measure.pi fun i : Fin (m + 1) ↦ betaMeasure (η i.castSucc) (stickBreakingTailSum η i)).map
        splitHead)
        = (((Measure.pi μ).map e).map Prod.swap) := by
            rw [hSplitHead, Measure.map_map measurable_swap e.measurable]
    _ = (((μ 0).prod (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i))).map Prod.swap) := by
          rw [hMapEq]
    _ = (Measure.pi fun i : Fin m ↦ μ (Fin.succAbove 0 i)).prod (μ 0) := by
          rw [Measure.prod_swap]
    _ = (Measure.pi fun i : Fin m ↦
          betaMeasure ((fun j : Fin (m + 1) ↦ η j.succ) i.castSucc)
            (stickBreakingTailSum (fun j : Fin (m + 1) ↦ η j.succ) i)).prod
          (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ)) := by
          simp [μ, stickBreakingTailSum_zero, stickBreakingTailSum_succ, Fin.zero_succAbove]

/-- Helper for Corollary 24.30: after dropping the head coordinate, the successor coordinates of
the extended input agree with the extended shifted tail input. -/
private theorem gemExtendWithTerminalOne_succ_eq_tail {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) :
    gemExtendWithTerminalOne v i.succ =
      gemExtendWithTerminalOne (fun j : Fin m ↦ v j.succ) i := by
  -- Proof comment: nonterminal tail coordinates are read from the shifted input, while the
  -- terminal coordinate is `1` on both sides.
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · calc
      gemExtendWithTerminalOne v j.castSucc.succ = v j.succ := by
        change Fin.lastCases (1 : ℝ) v j.castSucc.succ = v j.succ
        rw [show j.castSucc.succ = j.succ.castSucc by rw [Fin.succ_castSucc]]
        rw [Fin.lastCases_castSucc]
      _ = gemExtendWithTerminalOne (fun k : Fin m ↦ v k.succ) j.castSucc := by
        change v j.succ = Fin.lastCases (1 : ℝ) (fun k : Fin m ↦ v k.succ) j.castSucc
        rw [Fin.lastCases_castSucc]
  · calc
      gemExtendWithTerminalOne v (Fin.last m).succ = (1 : ℝ) := by
        change Fin.lastCases (1 : ℝ) v (Fin.last (m + 1)) = (1 : ℝ)
        rw [Fin.lastCases_last]
      _ = gemExtendWithTerminalOne (fun j : Fin m ↦ v j.succ) (Fin.last m) := by
        change (1 : ℝ) = Fin.lastCases (1 : ℝ) (fun j : Fin m ↦ v j.succ) (Fin.last m)
        rw [Fin.lastCases_last]

/-- Helper for Corollary 24.30: the predecessor residual product below a successor coordinate
splits into the head residual factor and the shifted tail predecessor product. -/
private theorem stickBreakingPredecessorProd_succ {m : ℕ} (v : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) :
    ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 2) ↦ j < i.succ), (1 - gemExtendWithTerminalOne v j)
      =
        (1 - v 0) *
          ∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) ↦ j < i),
            (1 - gemExtendWithTerminalOne (fun k : Fin m ↦ v k.succ) j) := by
  let succEmb : Fin (m + 1) ↪ Fin (m + 2) := ⟨Fin.succ, Fin.succ_injective _⟩
  have hfull :
      Finset.univ.filter (fun j : Fin (m + 2) ↦ j < i.succ) = Finset.Iio i.succ := by
    ext j
    simp [Finset.mem_Iio]
  have htail :
      Finset.univ.filter (fun j : Fin (m + 1) ↦ j < i) = Finset.Iio i := by
    ext j
    simp [Finset.mem_Iio]
  have hsplit :
      Finset.Iio i.succ = insert 0 ((Finset.Iio i).map succEmb) := by
    ext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      simp [succEmb]
  have hzero :
      (0 : Fin (m + 2)) ∉ (Finset.Iio i).map succEmb := by
    simp [succEmb]
  have hzero_apply : gemExtendWithTerminalOne v 0 = v 0 := by
    change Fin.lastCases (1 : ℝ) v ((0 : Fin (m + 1)).castSucc) = v 0
    rw [Fin.lastCases_castSucc]
  -- Proof comment: the predecessor set of a successor index is `{0}` together with the successor
  -- image of the tail predecessor set.
  rw [hfull, hsplit, Finset.prod_insert hzero, Finset.prod_map, htail]
  rw [hzero_apply]
  refine congrArg ((1 - v 0) * ·) ?_
  refine Finset.prod_congr rfl ?_
  intro j hj
  simpa [succEmb] using gemExtendWithTerminalOne_succ_eq_tail (v := v) j

/-- Helper for Corollary 24.30: the finite stick-breaking map has the expected head/tail recursive
form after adjoining the terminal value `1`. -/
private theorem finiteGemStickBreakingMap_cons {m : ℕ} (v : Fin (m + 1) → ℝ) :
    finiteGemStickBreakingMap (gemExtendWithTerminalOne v) =
      Fin.cons (v 0)
        (fun i ↦ (1 - v 0) *
          finiteGemStickBreakingMap (gemExtendWithTerminalOne (fun j : Fin m ↦ v j.succ)) i) := by
  ext j
  refine Fin.cases ?_ ?_ j
  · -- Proof comment: the first stick-breaking mass is exactly the head proportion.
    rw [finiteGemStickBreakingMap_apply]
    change (∏ j ∈ Finset.univ.filter (fun j : Fin (m + 2) ↦ j < 0), (1 - gemExtendWithTerminalOne v j)) *
        gemExtendWithTerminalOne v 0 = v 0
    have hhead : gemExtendWithTerminalOne v 0 = v 0 := by
      change Fin.lastCases (1 : ℝ) v ((0 : Fin (m + 1)).castSucc) = v 0
      rw [Fin.lastCases_castSucc]
    rw [hhead]
    simp
  · intro i
    -- Route correction: instead of normalizing the predecessor product inline, first split it into
    -- the head residual and the shifted tail predecessor product.
    rw [finiteGemStickBreakingMap_apply, Fin.cons_succ, finiteGemStickBreakingMap_apply]
    rw [stickBreakingPredecessorProd_succ (v := v) i, gemExtendWithTerminalOne_succ_eq_tail (v := v) i]
    simp [mul_assoc]

/-- Helper for Corollary 24.30: after normalizing a positive Gamma vector, reassembling the head
ratio and normalized tail recovers the original normalized vector together with its total mass. -/
private theorem assembleHeadTailNormalizeWithSumEq {m : ℕ} (y : Fin (m + 2) → ℝ)
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

/-- Helper for Corollary 24.30: on the Dirichlet surface, reassembling the head/tail
decomposition is almost surely the identity. -/
private theorem dirichletHeadTailReassemble_ae {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i : Fin (m + 2), 0 < η i) :
    (fun x : Fin (m + 2) → ℝ ↦
      Fin.cons (x 0) (fun i ↦ (1 - x 0) * (x i.succ / (1 - x 0)))) =ᵐ[dirichletMeasure η] id := by
  -- Route correction: pull the Dirichlet law back to the positive Gamma source first, and prove
  -- the head/tail reassembly identity there by a deterministic normalization calculation.
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
  -- Proof comment: the Dirichlet surface identity is the first-coordinate component of the
  -- deterministic normalized-Gamma reassembly lemma.
  simpa [normalize] using
    congrArg Prod.fst (assembleHeadTailNormalizeWithSumEq (m := m) y (hy 0) htail)

/-- Helper for Corollary 24.30: the independent tail-Dirichlet and head-Beta factors reassemble
to the full Dirichlet law. -/
private theorem map_dirichletTailBeta_to_dirichletMeasure {m : ℕ} {η : Fin (m + 2) → ℝ}
    (hη : ∀ i : Fin (m + 2), 0 < η i) :
    Measure.map
      (fun p : (Fin (m + 1) → ℝ) × ℝ ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * p.1 i))
      ((dirichletMeasure fun i : Fin (m + 1) ↦ η i.succ).prod
        (betaMeasure (η 0) (∑ i : Fin (m + 1), η i.succ))) =
      dirichletMeasure η := by
  -- Route correction: separate the forward head/tail product law from the inverse-a.e.
  -- reassembly identity, then compose them by `Measure.map_map`.
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
    hasLawDirichletHeadTailDecompose (η := η) hη
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
            dirichletHeadTailReassemble_ae (η := η) (hη := hη)
    _ = dirichletMeasure η := by
          simp

/-- Helper for Corollary 24.30: each coordinate of the terminal-one extension map is measurable. -/
private theorem measurable_gemExtendWithTerminalOne_apply {n : ℕ} (i : Fin (n + 1)) :
    Measurable (fun v : Fin n → ℝ ↦ gemExtendWithTerminalOne v i) := by
  -- Proof comment: nonterminal coordinates are ordinary projections, while the terminal
  -- coordinate is the constant value `1`.
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa [gemExtendWithTerminalOne] using
      (measurable_pi_apply j : Measurable fun v : Fin n → ℝ ↦ v j)
  · simpa [gemExtendWithTerminalOne] using
      (measurable_const : Measurable fun _ : Fin n → ℝ ↦ (1 : ℝ))

/-- Helper for Corollary 24.30: the canonical finite Beta input law pushes forward to the
Dirichlet law under the finite stick-breaking map. -/
private theorem map_finiteGemStickBreaking_piBeta_eq_dirichletMeasure
    {n : ℕ} {θ : Fin (n + 1) → ℝ} (hθ : ∀ i : Fin (n + 1), 0 < θ i) :
    Measure.map
      (fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v))
      (Measure.pi fun i : Fin n ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)) =
      dirichletMeasure θ := by
  induction n with
  | zero =>
      let source : Measure (Fin 0 → ℝ) :=
        Measure.pi fun i : Fin 0 ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)
      let constOne : Fin 1 → ℝ := fun _ ↦ 1
      have hconst :
          (fun v : Fin 0 → ℝ ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v)) =
            fun _ : Fin 0 → ℝ ↦ constOne := by
        funext v i
        fin_cases i
        rw [finiteGemStickBreakingMap_apply]
        simp [constOne]
        change Fin.lastCases (1 : ℝ) v (Fin.last 0) = (1 : ℝ)
        rw [Fin.lastCases_last]
      calc
        Measure.map
            (fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v))
            (Measure.pi fun i : Fin 0 ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i))
          = Measure.map (fun _ : Fin 0 → ℝ ↦ constOne) source := by
              simp [source, hconst]
        _ = Measure.dirac constOne := by
              rw [Measure.map_const]
              simp [source]
        _ = dirichletMeasure θ := by
              simpa [constOne] using (dirichletMeasure_finOne_eq_dirac_constOne (η := θ) hθ).symm
  | succ m ih =>
      let splitHead : (Fin (m + 1) → ℝ) → (Fin m → ℝ) × ℝ :=
        fun x ↦ ((fun i : Fin m ↦ x i.succ), x 0)
      let tailMap : (Fin m → ℝ) → Fin (m + 1) → ℝ :=
        fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v)
      let recurseAssemble : (Fin m → ℝ) × ℝ → Fin (m + 2) → ℝ :=
        fun p ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * tailMap p.1 i)
      let assemble : (Fin (m + 1) → ℝ) × ℝ → Fin (m + 2) → ℝ :=
        fun p ↦ Fin.cons p.2 (fun i ↦ (1 - p.2) * p.1 i)
      let sourceTail : Measure (Fin m → ℝ) :=
        Measure.pi fun i : Fin m ↦
          betaMeasure ((fun j : Fin (m + 1) ↦ θ j.succ) i.castSucc)
            (stickBreakingTailSum (fun j : Fin (m + 1) ↦ θ j.succ) i)
      let sourceHead : Measure ℝ := betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ)
      have hsourceHead_pos : 0 < ∑ i : Fin (m + 1), θ i.succ := by
        rw [← stickBreakingTailSum_zero (θ := θ)]
        exact stickBreakingTailSum_pos hθ 0
      letI : ∀ i : Fin m,
          IsProbabilityMeasure
            (betaMeasure ((fun j : Fin (m + 1) ↦ θ j.succ) i.castSucc)
              (stickBreakingTailSum (fun j : Fin (m + 1) ↦ θ j.succ) i)) := fun i ↦ by
        exact isProbabilityMeasureBeta (hθ i.castSucc.succ)
          (stickBreakingTailSum_pos (θ := fun j : Fin (m + 1) ↦ θ j.succ)
            (fun j ↦ hθ j.succ) i)
      letI : IsProbabilityMeasure sourceTail := by
        dsimp [sourceTail]
        infer_instance
      letI : IsProbabilityMeasure sourceHead := by
        dsimp [sourceHead]
        exact isProbabilityMeasureBeta (hθ 0) hsourceHead_pos
      have hsplit_meas : Measurable splitHead := by
        fun_prop
      have htailMap_meas : Measurable tailMap := by
        refine measurable_pi_lambda _ ?_
        intro i
        have hcoord :
            Measurable
              (fun v : Fin m → ℝ ↦
                (∏ j ∈ Finset.univ.filter (fun j : Fin (m + 1) ↦ j < i),
                  (1 - gemExtendWithTerminalOne v j)) *
                  gemExtendWithTerminalOne v i) := by
          refine (Finset.measurable_prod _ ?_).mul ?_
          · intro j hj
            exact measurable_const.sub (measurable_gemExtendWithTerminalOne_apply (n := m) j)
          · exact measurable_gemExtendWithTerminalOne_apply (n := m) i
        simpa [finiteGemStickBreakingMap] using hcoord
      have hassemble_meas : Measurable assemble := by
        refine measurable_pi_lambda _ ?_
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [assemble] using measurable_snd
        · intro j
          simpa [assemble] using (measurable_const.sub measurable_snd).mul
            ((measurable_pi_apply j).comp measurable_fst)
      have hrecurseAssemble_meas : Measurable recurseAssemble := by
        refine measurable_pi_lambda _ ?_
        intro i
        refine Fin.cases ?_ ?_ i
        · simpa [recurseAssemble] using measurable_snd
        · intro j
          simpa [recurseAssemble] using (measurable_const.sub measurable_snd).mul
            ((measurable_pi_apply j).comp (htailMap_meas.comp measurable_fst))
      have hrec :
          (fun v : Fin (m + 1) → ℝ ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v)) =
            recurseAssemble ∘ splitHead := by
        funext v
        simpa [splitHead, recurseAssemble, tailMap] using finiteGemStickBreakingMap_cons (v := v)
      calc
        Measure.map
            (fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v))
            (Measure.pi fun i : Fin (m + 1) ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i))
          = Measure.map recurseAssemble
              (((Measure.pi fun i : Fin (m + 1) ↦
                betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i))).map splitHead) := by
                  rw [hrec, Measure.map_map hrecurseAssemble_meas hsplit_meas]
        _ = Measure.map recurseAssemble (sourceTail.prod sourceHead) := by
              exact congrArg (Measure.map recurseAssemble)
                (map_piBeta_split_head_eq_prod (η := θ) hθ)
        _ = Measure.map assemble
              (Measure.map (Prod.map tailMap id) (sourceTail.prod sourceHead)) := by
                rw [show recurseAssemble = assemble ∘ Prod.map tailMap id by
                  funext p
                  rfl,
                  Measure.map_map hassemble_meas (htailMap_meas.prodMap measurable_id)]
        _ = Measure.map assemble ((Measure.map tailMap sourceTail).prod (Measure.map id sourceHead)) := by
              rw [Measure.map_prod_map _ _ htailMap_meas measurable_id]
        _ = Measure.map assemble ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod sourceHead) := by
              rw [ih (θ := fun i : Fin (m + 1) ↦ θ i.succ) (hθ := fun i ↦ hθ i.succ), Measure.map_id]
        _ = Measure.map assemble
              ((dirichletMeasure fun i : Fin (m + 1) ↦ θ i.succ).prod
                (betaMeasure (θ 0) (∑ i : Fin (m + 1), θ i.succ))) := by
              simp [sourceHead]
        _ = dirichletMeasure θ := by
              simpa [assemble] using map_dirichletTailBeta_to_dirichletMeasure (η := θ) hθ

-- Proof sketch: identify the law of the Beta input vector via `iIndepFun_iff_map_fun_eq_pi_map`,
-- then compose with the chapter's finite stick-breaking map and canonical Dirichlet law.
/-- Corollary 24.30: an independent finite stick-breaking family of Beta variables, extended by a
terminal value `1`, has the associated Dirichlet law under the stick-breaking map. -/
theorem stickBreaking_hasLaw_dirichletMeasure
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hθ : ∀ i : Fin (n + 1), 0 < θ i) {V : Fin n → Ω → ℝ}
    (hV_indep : iIndepFun V P)
    (hV_law : ∀ i : Fin n,
      HasLaw (V i) (betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)) P) :
    HasLaw
      (fun ω ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne (fun i : Fin n ↦ V i ω)))
      (dirichletMeasure θ) P := by
  have hInput :
      HasLaw
        (fun ω i ↦ V i ω)
        (Measure.pi fun i : Fin n ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i))
        P := by
    refine ⟨aemeasurable_pi_lambda _ fun i ↦ (hV_law i).aemeasurable, ?_⟩
    -- Proof comment: independence identifies the whole Beta input vector with the product of its
    -- one-dimensional coordinate laws.
    rw [show
        P.map (fun ω i ↦ V i ω) = Measure.pi fun i : Fin n ↦ P.map (V i) by
          simpa using
            (iIndepFun_iff_map_fun_eq_pi_map
              (μ := P) (f := fun i ↦ V i) (fun i ↦ (hV_law i).aemeasurable)).1 hV_indep]
    congr 1
    funext i
    exact (hV_law i).map_eq
  have hSource :
      HasLaw
        (fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v))
        (dirichletMeasure θ)
        (Measure.pi fun i : Fin n ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)) := by
    have hAemeas :
        AEMeasurable
          (fun v ↦ finiteGemStickBreakingMap (gemExtendWithTerminalOne v))
          (Measure.pi fun i : Fin n ↦ betaMeasure (θ i.castSucc) (stickBreakingTailSum θ i)) :=
      -- Proof comment: the finite stick-breaking map is assembled from measurable coordinate
      -- projections, finite products, and the terminal-value extension.
      (by
        refine (measurable_pi_lambda _ ?_).aemeasurable
        intro i
        have hcoord :
            Measurable
              (fun c : Fin n → ℝ ↦
                (∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) ↦ j < i),
                  (1 - gemExtendWithTerminalOne c j)) *
                  gemExtendWithTerminalOne c i) := by
          refine (Finset.measurable_prod _ ?_).mul ?_
          · intro j hj
            exact measurable_const.sub (measurable_gemExtendWithTerminalOne_apply (n := n) j)
          · exact measurable_gemExtendWithTerminalOne_apply (n := n) i
        simpa [finiteGemStickBreakingMap] using hcoord)
    exact ⟨hAemeas, map_finiteGemStickBreaking_piBeta_eq_dirichletMeasure (θ := θ) hθ⟩
  -- Proof comment: compose the canonical source law with the identified law of the actual Beta
  -- input vector.
  simpa using hSource.comp hInput
