/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part23

open scoped BigOperators Pointwise

section Chap06
section Section30

/-- Helper for Theorem 6.30.24: even after changing the feasible-branch sign, the full dependent
theorem type is still not inhabited. The zero-multiplier restricted-domain witness specializes any
global positive-sign proof term to the impossible equality `0 = -∞`. -/
lemma helperForTheorem_6_30_24_currentPositiveSignTargetStatementFunctionType_not_nonempty :
    ¬ Nonempty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) := by
  rintro ⟨hTarget⟩
  -- The packaged restricted-domain contradiction already collapses any purported global
  -- positive-sign theorem term.
  exact helperForTheorem_6_30_24_currentTargetStatementFunction_false hTarget

/-- Helper for Theorem 6.30.24: even the sign-only repaired dependent theorem type is empty as a
type. This records the zero-multiplier restricted-domain obstruction in the same `IsEmpty` format
already used for the literal negative-sign theorem header. -/
lemma helperForTheorem_6_30_24_currentPositiveSignTargetStatementFunctionType_isEmpty :
    IsEmpty
      (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
        (data : IntermediateProgramData m n n0 ni)
        (_hh0 : IsClosedProperConvexERealFunction data.h0)
        (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
          (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
            (intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar =
                intermediateProgramDualObjective data wStar) ∧
            (¬ intermediateProgramDualFeasible data xStar wStar →
              adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
          dualProgramValueOfIntermediateProgram data =
            sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
              intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                v = intermediateProgramDualObjective data wStar}) := by
  -- Any inhabitant again specializes to the named restricted-domain witness, so the repaired
  -- positive-sign theorem type is also empty.
  refine ⟨?_⟩
  intro hTarget
  exact helperForTheorem_6_30_24_currentTargetStatementFunction_false hTarget

/-- Helper for Theorem 6.30.24: changing only the feasible-branch sign is not enough. The named
wrong-sign witness validates the repaired specialization, but the zero-multiplier restricted-
domain witness still rules out any global positive-sign theorem term. -/
lemma helperForTheorem_6_30_24_signRepairStillNeedsObjectiveRepair :
    helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusionProp ∧
      ¬ Nonempty
        (∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
          (data : IntermediateProgramData m n n0 ni)
          (_hh0 : IsClosedProperConvexERealFunction data.h0)
          (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
            (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
              (intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar =
                  intermediateProgramDualObjective data wStar) ∧
              (¬ intermediateProgramDualFeasible data xStar wStar →
                adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
            dualProgramValueOfIntermediateProgram data =
              sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
                intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
                  v = intermediateProgramDualObjective data wStar}) := by
  constructor
  · -- The wrong-sign witness already computes the repaired specialization directly.
    exact helperForTheorem_6_30_24_wrongSignWitness_correctedSpecializedConclusion
  · -- The zero-multiplier restricted-domain witness then shows that this sign repair is still not
    -- a globally provable theorem.
    exact helperForTheorem_6_30_24_currentPositiveSignTargetStatementFunctionType_not_nonempty

/-- Helper for Theorem 6.30.24: closed proper convexity supplies one finite witness point for
`h₀` and one finite witness point for each `hᵢ`. -/
lemma helperForTheorem_6_30_24_exists_finiteWitnessFamily
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)) :
    ∃ y0 : Fin n0 → ℝ, data.h0 y0 ≠ (⊤ : EReal) ∧
      ∃ y : ∀ i : Fin m, Fin (ni i) → ℝ, ∀ i : Fin m, data.h i (y i) ≠ (⊤ : EReal) := by
  classical
  -- Properness provides a point where `h₀` is finite above.
  rcases hh0.1.1.2 with ⟨y0, hy0⟩
  -- The same properness argument applies independently to each indexed function `hᵢ`.
  have hy_exists : ∀ i : Fin m, ∃ yi : Fin (ni i) → ℝ, data.h i yi ≠ (⊤ : EReal) := by
    intro i
    exact (hh i).1.1.2
  choose y hy using hy_exists
  exact ⟨y0, hy0, y, hy⟩

/-- Helper for Theorem 6.30.24: on the nonnegative branch, every Fenchel-conjugate term in the
explicit dual objective stays away from `-∞`, so the whole objective stays away from `+∞`. -/
lemma helperForTheorem_6_30_24_dualObjective_ne_top_of_nonnegative
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hnonneg : ∀ i : Fin m, 0 ≤ wStar.vStar i) :
    intermediateProgramDualObjective data wStar ≠ (⊤ : EReal) := by
  let conjTail : Fin m → EReal := fun i =>
    fenchelConjugate (ni i)
      (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
      (wStar.p i)
  have hhead_ne_bot : fenchelConjugate n0 data.h0 wStar.p0 ≠ (⊥ : EReal) := by
    -- Properness of `h₀` rules out `-∞` for its Fenchel conjugate.
    exact helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
      (hf := hh0.1.1) (xStar := wStar.p0)
  have hhead_ne_top :
      ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
        fenchelConjugate n0 data.h0 wStar.p0) ≠ (⊤ : EReal) := by
    -- The head block is a finite affine term plus the negated conjugate.
    have hfinite_head :
        ((((data.α0 + (data.a0 ⬝ᵥ wStar.p0 : ℝ) : ℝ) : ℝ) : EReal)) ≠ (⊤ : EReal) :=
      EReal.coe_ne_top _
    rw [sub_eq_add_neg]
    refine EReal.add_ne_top ?_ ?_
    · simpa [EReal.coe_add] using hfinite_head
    simpa [EReal.neg_eq_top_iff] using hhead_ne_bot
  have htail_term_ne_top :
      ∀ i : Fin m,
        ((((data.α i * wStar.vStar i : ℝ) : EReal) +
              ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
            fenchelConjugate (ni i)
              (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
              (wStar.p i)) ≠ (⊤ : EReal) := by
    intro i
    have hscaled_on :
        ProperConvexFunctionOn (Set.univ : Set (Fin (ni i) → ℝ))
          (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y)) := by
      simpa using
        helperForTheorem_6_30_21_properConvexFunctionOn_univ_mul_of_nonneg
          (f := data.h i) (hf := (hh i).1) (hlam := hnonneg i)
    have hscaled :
        ProperConvexERealFunction (F := Fin (ni i) → ℝ)
          (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y)) :=
      helperForLemma_26_2_properConvexERealFunction hscaled_on
    have hconj_ne_bot :
        conjTail i ≠ (⊥ : EReal) := by
      exact helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
        (hf := hscaled.1) (xStar := wStar.p i)
    -- Each tail block is again a finite affine term plus the negated conjugate.
    have hfinite_tail :
        ((((data.α i * wStar.vStar i + (data.a i ⬝ᵥ wStar.p i : ℝ) : ℝ) : ℝ) : EReal)) ≠
          (⊤ : EReal) :=
      EReal.coe_ne_top _
    rw [sub_eq_add_neg]
    refine EReal.add_ne_top ?_ ?_
    · simpa [EReal.coe_add, left_distrib] using hfinite_tail
    simpa [conjTail, EReal.neg_eq_top_iff] using hconj_ne_bot
  have htail_ne_top :
      (∑ i : Fin m,
          ((((data.α i * wStar.vStar i : ℝ) : EReal) +
                ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
              fenchelConjugate (ni i)
                (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
                (wStar.p i))) ≠ (⊤ : EReal) := by
    -- A finite sum of non-`⊤` tail blocks stays away from `⊤`.
    exact finset_sum_ne_top_of_forall (s := Finset.univ) (f := fun i : Fin m =>
      ((((data.α i * wStar.vStar i : ℝ) : EReal) +
            ((data.a i ⬝ᵥ wStar.p i : ℝ) : EReal)) -
          fenchelConjugate (ni i)
            (fun y => (((wStar.vStar i : ℝ) : EReal) * data.h i y))
            (wStar.p i))) (by
      intro i hi
      exact htail_term_ne_top i)
  -- The explicit dual objective is the sum of the head block and the tail sum.
  rw [intermediateProgramDualObjective]
  exact EReal.add_ne_top hhead_ne_top htail_ne_top

/-- Helper for Theorem 6.30.24: along the feasible ray obtained by increasing one threshold
coordinate `vᵢ`, the adjoint integrand is affine in the ray parameter with slope `vᵢ*`. -/
lemma helperForTheorem_6_30_24_negativeMultiplierRayWitnessValue
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (w0 : IntermediateProgramParameter m n n0 ni) (x0 : Fin n → ℝ)
    (hxFeas : x0 ∈ intermediateProgramFeasibleSet data w0)
    (i0 : Fin m) (t : ℝ) (ht : 0 ≤ t) :
    let w : IntermediateProgramParameter m n n0 ni :=
      { v := w0.v + (Pi.single i0 t : Fin m → ℝ)
        p0 := w0.p0
        p := w0.p }
    intermediateProgramBifunction data w x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
        (((intermediateProgramDualPairing w wStar : ℝ) : EReal)) =
      (intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal))) +
        (((t * wStar.vStar i0 : ℝ) : EReal)) := by
  -- Raising one threshold coordinate preserves feasibility of the chosen witness point.
  dsimp
  have hfeas :
      x0 ∈ intermediateProgramFeasibleSet data
        { v := w0.v + (Pi.single i0 t : Fin m → ℝ), p0 := w0.p0, p := w0.p } := by
    intro j
    by_cases hj : j = i0
    · have hincReal : w0.v j ≤ w0.v j + t := by
        linarith
      have hincE : (((w0.v j : ℝ) : EReal)) ≤ (((w0.v j + t : ℝ) : EReal)) := by
        exact_mod_cast hincReal
      have hbase :
          data.h j ((data.A j).mulVec x0 + data.a j - w0.p j) +
              ((((data.aStar j ⬝ᵥ x0 : ℝ) + data.α j : ℝ) : EReal)) ≤
            (((w0.v j : ℝ) : EReal)) := hxFeas j
      have hgoal :
          data.h j ((data.A j).mulVec x0 + data.a j - w0.p j) +
              ((((data.aStar j ⬝ᵥ x0 : ℝ) + data.α j : ℝ) : EReal)) ≤
            (((w0.v j + t : ℝ) : EReal)) := le_trans hbase hincE
      simpa [hj] using hgoal
    · simpa [Pi.single_eq_of_ne hj] using (hxFeas j)
  have hpair :
      intermediateProgramDualPairing
          { v := w0.v + (Pi.single i0 t : Fin m → ℝ), p0 := w0.p0, p := w0.p } wStar =
        intermediateProgramDualPairing w0 wStar + t * wStar.vStar i0 := by
    -- Only the `v`-pairing changes along this ray.
    unfold intermediateProgramDualPairing
    rw [add_dotProduct, single_dotProduct]
    ring
  -- Evaluate the bifunction at the preserved feasible point and simplify the affine increment.
  rw [intermediateProgramBifunction, intermediateProgramBifunction]
  have hIndicatorZero :
      indicatorFunction
          (intermediateProgramFeasibleSet data
            { v := w0.v + (Pi.single i0 t : Fin m → ℝ), p0 := w0.p0, p := w0.p }) x0 =
        (0 : EReal) := by
    simp [indicatorFunction, hfeas]
  have hIndicatorZero0 :
      indicatorFunction (intermediateProgramFeasibleSet data w0) x0 = (0 : EReal) := by
    simp [indicatorFunction, hxFeas]
  rw [hIndicatorZero, hIndicatorZero0, hpair]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 6.30.24: if one multiplier coordinate is negative, then the intermediate
adjoint value is `-∞`, obtained by sending the corresponding threshold variable to `+∞` along a
feasible ray while keeping the affine-shift coordinates fixed. -/
lemma helperForTheorem_6_30_24_adjoint_eq_bot_of_exists_negativeMultiplier
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hneg : ∃ i0 : Fin m, wStar.vStar i0 < 0) :
    adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal) := by
  classical
  -- Show the defining infimum lies below every real number by following a feasible threshold ray.
  rw [adjointOfIntermediateProgram, EReal.eq_bot_iff_forall_lt]
  intro y
  rcases hneg with ⟨i0, hi0neg⟩
  rcases
      helperForTheorem_6_30_24_exists_finiteWitnessFamily
        (data := data) hh0 hh with
    ⟨y0, hy0_ne_top, yWitness, hyWitness_ne_top⟩
  let x0 : Fin n → ℝ := 0
  let w0 : IntermediateProgramParameter m n n0 ni :=
    helperForTheorem_6_30_24_parameterFromWitnesses data x0 y0 yWitness
  have hxFeas : x0 ∈ intermediateProgramFeasibleSet data w0 := by
    -- The witness points were chosen so that each affine constraint is active at `x = 0`.
    simpa [x0, w0] using
      helperForTheorem_6_30_24_parameterFromWitnesses_feasiblePoint
        (data := data) (x := x0) (y0 := y0) (y := yWitness) hyWitness_ne_top
  have hy0_ne_bot : data.h0 y0 ≠ (⊥ : EReal) := hh0.1.1.1 y0
  have hhead_ne_top :
      data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) : EReal)) ≠ (⊤ : EReal) := by
    exact EReal.add_ne_top hy0_ne_top (EReal.coe_ne_top _)
  have hhead_ne_bot :
      data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) : EReal)) ≠ (⊥ : EReal) := by
    exact add_ne_bot_of_notbot hy0_ne_bot (EReal.coe_ne_bot _)
  let base : ℝ :=
    (data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) : EReal))).toReal -
      (x0 ⬝ᵥ xStar : ℝ) + intermediateProgramDualPairing w0 wStar
  let t : ℝ := |((base - y) / (-wStar.vStar i0))| + 1
  have hden : 0 < -wStar.vStar i0 := by
    linarith
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hratio :
      ((base - y) / (-wStar.vStar i0)) < t := by
    -- The chosen ray parameter strictly dominates the controlling quotient.
    dsimp [t]
    refine lt_of_le_of_lt (le_abs_self ((base - y) / (-wStar.vStar i0))) ?_
    linarith [abs_nonneg ((base - y) / (-wStar.vStar i0))]
  have hmul : (base - y) < t * (-wStar.vStar i0) := by
    exact (div_lt_iff₀ hden).mp hratio
  have hreal : base + t * wStar.vStar i0 < y := by
    linarith
  have hcoex0 :
      ((((data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) : EReal))).toReal : ℝ) :
          EReal)) =
        data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) : EReal)) := by
    exact EReal.coe_toReal (x := data.h0 y0 + ((((data.a0Star ⬝ᵥ x0 : ℝ) + data.α0 : ℝ) :
      EReal))) hhead_ne_top hhead_ne_bot
  let wRay : IntermediateProgramParameter m n n0 ni :=
    { v := w0.v + (Pi.single i0 t : Fin m → ℝ)
      p0 := w0.p0
      p := w0.p }
  have hwitnessEval :
      intermediateProgramBifunction data wRay x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing wRay wStar : ℝ) : EReal)) =
        (intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.vStar i0 : ℝ) : EReal)) := by
    -- The previously established ray computation applies to the explicit feasible base point.
    simpa [w0, wRay] using
      helperForTheorem_6_30_24_negativeMultiplierRayWitnessValue
        (data := data) (xStar := xStar) (wStar := wStar)
        (w0 := w0) (x0 := x0) (hxFeas := hxFeas) (i0 := i0) (t := t) ht
  have hwitnessLe :
      sInf
          (Set.range fun q : IntermediateProgramParameter m n n0 ni × (Fin n → ℝ) =>
            intermediateProgramBifunction data q.1 q.2 - (((q.2 ⬝ᵥ xStar : ℝ) : EReal)) +
              (((intermediateProgramDualPairing q.1 wStar : ℝ) : EReal))) ≤
        (intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.vStar i0 : ℝ) : EReal)) := by
    -- The infimum is bounded above by the value at the chosen ray witness.
    have hLePair :
        sInf
            (Set.range fun q : IntermediateProgramParameter m n n0 ni × (Fin n → ℝ) =>
              intermediateProgramBifunction data q.1 q.2 - (((q.2 ⬝ᵥ xStar : ℝ) : EReal)) +
                (((intermediateProgramDualPairing q.1 wStar : ℝ) : EReal))) ≤
          intermediateProgramBifunction data wRay x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing wRay wStar : ℝ) : EReal)) := by
      exact sInf_le ⟨(wRay, x0), rfl⟩
    exact hLePair.trans (le_of_eq hwitnessEval)
  have hbaseEval :
      intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
          (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal)) =
        (((base : ℝ) : EReal)) := by
    -- At the feasible witness, the bifunction reduces to the finite translated `h₀` value.
    have hIndicatorZero0 :
        indicatorFunction (intermediateProgramFeasibleSet data w0) x0 = (0 : EReal) := by
      simp [indicatorFunction, hxFeas]
    have hArg0 : data.A0.mulVec x0 + data.a0 - w0.p0 = y0 := by
      ext j
      simp [x0, w0, helperForTheorem_6_30_24_parameterFromWitnesses, sub_eq_add_neg,
        add_left_comm, add_comm]
    have hArg0' : data.h0 (data.A0.mulVec x0 + data.a0 - w0.p0) = data.h0 y0 := by
      rw [hArg0]
    rw [intermediateProgramBifunction, hIndicatorZero0, hArg0', ← hcoex0]
    simp [base, x0, sub_eq_add_neg, add_comm]
  have htargetEq :
      (intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.vStar i0 : ℝ) : EReal)) =
        (((base + t * wStar.vStar i0 : ℝ) : EReal)) := by
    rw [hbaseEval]
    simp [EReal.coe_add]
  have hltTarget :
      (((base + t * wStar.vStar i0 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    exact_mod_cast hreal
  have hltWitness :
      (intermediateProgramBifunction data w0 x0 - (((x0 ⬝ᵥ xStar : ℝ) : EReal)) +
            (((intermediateProgramDualPairing w0 wStar : ℝ) : EReal))) +
          (((t * wStar.vStar i0 : ℝ) : EReal)) < ((y : ℝ) : EReal) := by
    rw [htargetEq]
    exact hltTarget
  exact lt_of_le_of_lt hwitnessLe hltWitness

/-- Helper for Theorem 6.30.24: if the affine balance equation already holds, then any failure of
dual feasibility must come from a negative multiplier coordinate, so the adjoint is `-∞`. -/
lemma helperForTheorem_6_30_24_adjoint_eq_bot_of_not_dualFeasible_and_balance
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (hh0 : IsClosedProperConvexERealFunction data.h0)
    (hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i))
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni)
    (hnotfeas : ¬ intermediateProgramDualFeasible data xStar wStar)
    (hbalance :
      data.a0Star + ∑ i : Fin m, (wStar.vStar i) • data.aStar i +
          (data.A0.transpose.mulVec wStar.p0) +
          ∑ i : Fin m, (data.A i).transpose.mulVec (wStar.p i) = xStar) :
    adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal) := by
  have hneg : ∃ i : Fin m, wStar.vStar i < 0 := by
    by_contra hneg
    push_neg at hneg
    -- Once the balance identity is fixed, infeasibility can only come from a negative
    -- multiplier coordinate.
    exact hnotfeas ⟨hneg, hbalance⟩
  -- The finished negative-multiplier ray argument now applies verbatim.
  exact helperForTheorem_6_30_24_adjoint_eq_bot_of_exists_negativeMultiplier
    (data := data) (hh0 := hh0) (hh := hh) (xStar := xStar) (wStar := wStar) hneg

/-- Helper for Theorem 6.30.24: non-feasibility splits into the two structural obstruction
branches that remain in the corrected proof plan, namely a negative multiplier or a failed
balance equation under nonnegative multipliers. -/
lemma helperForTheorem_6_30_24_not_dualFeasible_iff_exists_negativeMultiplier_or_balanceMismatch
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni) :
    ¬ intermediateProgramDualFeasible data xStar wStar ↔
      (∃ i : Fin m, wStar.vStar i < 0) ∨
        ((∀ i : Fin m, 0 ≤ wStar.vStar i) ∧
          data.a0Star + ∑ i : Fin m, (wStar.vStar i) • data.aStar i +
              (data.A0.transpose.mulVec wStar.p0) +
              ∑ i : Fin m, (data.A i).transpose.mulVec (wStar.p i) ≠ xStar) := by
  constructor
  · intro hnotfeas
    by_cases hnonneg : ∀ i : Fin m, 0 ≤ wStar.vStar i
    · right
      refine ⟨hnonneg, ?_⟩
      -- On the nonnegative branch, the only way feasibility can fail is that the balance
      -- equation does not hold.
      intro hbalance
      exact hnotfeas ⟨hnonneg, hbalance⟩
    · left
      -- Negating the nonnegative branch produces the explicit negative multiplier witness.
      push_neg at hnonneg
      exact hnonneg
  · rintro (hneg | ⟨hnonneg, hbalance_ne⟩) hfeas
    · rcases hneg with ⟨i, hi⟩
      -- A negative multiplier coordinate contradicts the nonnegativity half of feasibility.
      exact not_lt_of_ge (hfeas.1 i) hi
    · -- On the nonnegative branch, the balance mismatch directly contradicts feasibility.
      exact hbalance_ne hfeas.2

/-- Helper for Theorem 6.30.24: the exact universal proposition obtained by abstracting the
current negative-sign theorem header over the datum `data` and the convexity hypotheses. -/
abbrev helperForTheorem_6_30_24_negativeSignUniversalStatementProp : Prop :=
  ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (_hh0 : IsClosedProperConvexERealFunction data.h0)
    (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
      (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
        (intermediateProgramDualFeasible data xStar wStar →
          adjointOfIntermediateProgram data xStar wStar =
            -intermediateProgramDualObjective data wStar) ∧
        (¬ intermediateProgramDualFeasible data xStar wStar →
          adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram data =
        sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
          intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
            v = intermediateProgramDualObjective data wStar}

/-- Helper for Theorem 6.30.24: the sign-only repaired universal proposition replaces the
negative feasible-branch value by the positive-sign dual objective, but leaves the rest of the
theorem unchanged. -/
abbrev helperForTheorem_6_30_24_positiveSignUniversalStatementProp : Prop :=
  ∀ {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (_hh0 : IsClosedProperConvexERealFunction data.h0)
    (_hh : ∀ i : Fin m, IsClosedProperConvexERealFunction (data.h i)),
      (∀ xStar : Fin n → ℝ, ∀ wStar : IntermediateProgramDualParameter m n n0 ni,
        (intermediateProgramDualFeasible data xStar wStar →
          adjointOfIntermediateProgram data xStar wStar =
            intermediateProgramDualObjective data wStar) ∧
        (¬ intermediateProgramDualFeasible data xStar wStar →
          adjointOfIntermediateProgram data xStar wStar = (⊥ : EReal))) ∧
      dualProgramValueOfIntermediateProgram data =
        sSup {v : EReal | ∃ wStar : IntermediateProgramDualParameter m n n0 ni,
          intermediateProgramDualFeasible data (0 : Fin n → ℝ) wStar ∧
            v = intermediateProgramDualObjective data wStar}

/-- Helper for Theorem 6.30.24: both universal theorem types are globally obstructed. The
wrong-sign witness kills the literal current header, and the restricted-domain zero-multiplier
witness kills the sign-only positive-sign repair. -/
lemma helperForTheorem_6_30_24_bothUniversalStatementTypes_not_nonempty :
    ¬ Nonempty helperForTheorem_6_30_24_negativeSignUniversalStatementProp ∧
      ¬ Nonempty helperForTheorem_6_30_24_positiveSignUniversalStatementProp := by
  constructor
  · -- The already packaged wrong-sign contradiction is exactly the current universal header.
    simpa [helperForTheorem_6_30_24_negativeSignUniversalStatementProp] using
      helperForTheorem_6_30_24_targetStatementFunctionType_not_nonempty
  · -- The restricted-domain witness already rules out the sign-only repair globally.
    simpa [helperForTheorem_6_30_24_positiveSignUniversalStatementProp] using
      helperForTheorem_6_30_24_currentPositiveSignTargetStatementFunctionType_not_nonempty

/-- Helper for Theorem 6.30.24: both abstracted universal propositions are empty as types. This
repackages the two `¬ Nonempty` obstructions into the exact `IsEmpty` form needed to record that
no proof term can exist for either the literal theorem header or the sign-only repair. -/
lemma helperForTheorem_6_30_24_bothUniversalStatementTypes_isEmpty :
    IsEmpty helperForTheorem_6_30_24_negativeSignUniversalStatementProp ∧
      IsEmpty helperForTheorem_6_30_24_positiveSignUniversalStatementProp := by
  constructor
  · -- The negative-sign universal proposition is definitionally the already obstructed dependent
    -- theorem type.
    simpa [helperForTheorem_6_30_24_negativeSignUniversalStatementProp] using
      helperForTheorem_6_30_24_targetStatementFunctionType_isEmpty
  · -- The positive-sign universal proposition is definitionally the repaired dependent theorem
    -- type, which is still empty by the restricted-domain witness.
    simpa [helperForTheorem_6_30_24_positiveSignUniversalStatementProp] using
      helperForTheorem_6_30_24_currentPositiveSignTargetStatementFunctionType_isEmpty

/-- Helper for Theorem 6.30.24: the full-domain hypothesis makes every constraint value finite
above at every point. -/
lemma helperForTheorem_6_30_24_constraint_lt_top_of_fullDomain
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    {i : Fin m} {y : Fin (ni i) → ℝ}
    (hdomi : effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) = Set.univ) :
    data.h i y < (⊤ : EReal) := by
  -- Rewriting the effective domain as `univ` turns every point into a finite domain point.
  have hy :
      y ∈ effectiveDomain (Set.univ : Set (Fin (ni i) → ℝ)) (data.h i) := by
    rw [hdomi]
    simp
  simpa [effectiveDomain_eq] using hy

/-- Helper for Theorem 6.30.24: the balance vector appearing in the explicit feasibility
constraint, namely `a₀* + ∑ᵢ vᵢ* aᵢ* + A₀ᵀ p₀* + ∑ᵢ Aᵢᵀ pᵢ*`. -/
abbrev helperForTheorem_6_30_24_dualBalanceVector
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (wStar : IntermediateProgramDualParameter m n n0 ni) : Fin n → ℝ :=
  data.a0Star + ∑ i : Fin m, (wStar.vStar i) • data.aStar i +
    (data.A0.transpose.mulVec wStar.p0) +
    ∑ i : Fin m, (data.A i).transpose.mulVec (wStar.p i)

/-- Helper for Theorem 6.30.24: dotting a matrix image against a covector is the same as dotting
the original vector against the transposed matrix image of that covector. -/
lemma helperForTheorem_6_30_24_mulVec_dotProduct_eq_dotProduct_transposeMulVec
    {k n : ℕ} (A : Matrix (Fin k) (Fin n) ℝ)
    (x : Fin n → ℝ) (p : Fin k → ℝ) :
    ((A.mulVec x) ⬝ᵥ p : ℝ) = (x ⬝ᵥ (A.transpose.mulVec p) : ℝ) := by
  -- Reorient the standard matrix-dot-product identity into the form needed for the affine
  -- balance collection.
  rw [dotProduct_comm]
  simpa [Matrix.mulVec_transpose, dotProduct_comm] using (Matrix.dotProduct_mulVec p A x)

/-- Helper for Theorem 6.30.24: the head affine terms collect into the displayed coefficient of
`x` plus the head constant term. -/
lemma helperForTheorem_6_30_24_headAffineTerms_collect
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x : Fin n → ℝ) (p0Star : Fin n0 → ℝ) :
    (((data.A0.mulVec x + data.a0) ⬝ᵥ p0Star : ℝ) + ((data.a0Star ⬝ᵥ x : ℝ) + data.α0)) =
      (x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec p0Star) : ℝ) +
        (data.α0 + (data.a0 ⬝ᵥ p0Star : ℝ)) := by
  have hMatrix :
      (((data.A0.mulVec x + data.a0) ⬝ᵥ p0Star : ℝ)) =
        ((x ⬝ᵥ data.A0.transpose.mulVec p0Star : ℝ) + (data.a0 ⬝ᵥ p0Star : ℝ)) := by
    -- Rewrite the translated matrix image into a linear term in `x` plus the constant shift.
    calc
      (((data.A0.mulVec x + data.a0) ⬝ᵥ p0Star : ℝ)) =
          (((data.A0.mulVec x) ⬝ᵥ p0Star : ℝ) + (data.a0 ⬝ᵥ p0Star : ℝ)) := by
            simp
      _ = ((x ⬝ᵥ data.A0.transpose.mulVec p0Star : ℝ) + (data.a0 ⬝ᵥ p0Star : ℝ)) := by
            rw [helperForTheorem_6_30_24_mulVec_dotProduct_eq_dotProduct_transposeMulVec]
  have hLinear :
      (x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec p0Star) : ℝ) =
        ((data.a0Star ⬝ᵥ x : ℝ) + (x ⬝ᵥ data.A0.transpose.mulVec p0Star : ℝ)) := by
    -- Expand the dot product against the summed coefficient and commute the first term.
    calc
      (x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec p0Star) : ℝ) =
          ((x ⬝ᵥ data.a0Star : ℝ) + (x ⬝ᵥ data.A0.transpose.mulVec p0Star : ℝ)) := by
            simp [dotProduct_add]
      _ = ((data.a0Star ⬝ᵥ x : ℝ) + (x ⬝ᵥ data.A0.transpose.mulVec p0Star : ℝ)) := by
            rw [dotProduct_comm]
  -- The remaining step is ordinary real arithmetic after the two dot-product rewrites.
  rw [hMatrix, hLinear]
  ring

/-- Helper for Theorem 6.30.24: for a fixed constraint index, the affine terms produced by the
translated block collapse collect into the displayed linear coefficient of `x` plus the indexed
constant term. -/
lemma helperForTheorem_6_30_24_constraintAffineTerms_collect
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (i : Fin m) (x : Fin n → ℝ) (lam : ℝ) (pStar : Fin (ni i) → ℝ) :
    (((data.A i).mulVec x + data.a i) ⬝ᵥ pStar : ℝ) +
        lam * ((data.aStar i ⬝ᵥ x : ℝ) + data.α i) =
      (x ⬝ᵥ (lam • data.aStar i + (data.A i).transpose.mulVec pStar) : ℝ) +
        (data.α i * lam + (data.a i ⬝ᵥ pStar : ℝ)) := by
  have hMatrix :
      (((data.A i).mulVec x + data.a i) ⬝ᵥ pStar : ℝ) =
        ((x ⬝ᵥ (data.A i).transpose.mulVec pStar : ℝ) + (data.a i ⬝ᵥ pStar : ℝ)) := by
    -- Rewrite the translated matrix image into the transpose-dot-product form.
    calc
      (((data.A i).mulVec x + data.a i) ⬝ᵥ pStar : ℝ) =
          (((data.A i).mulVec x) ⬝ᵥ pStar : ℝ) + (data.a i ⬝ᵥ pStar : ℝ) := by
            simp
      _ = ((x ⬝ᵥ (data.A i).transpose.mulVec pStar : ℝ) + (data.a i ⬝ᵥ pStar : ℝ)) := by
            rw [helperForTheorem_6_30_24_mulVec_dotProduct_eq_dotProduct_transposeMulVec]
  have hScaled :
      lam * ((data.aStar i ⬝ᵥ x : ℝ) + data.α i) =
        (x ⬝ᵥ (lam • data.aStar i) : ℝ) + data.α i * lam := by
    -- Move the scalar multiplier onto `aᵢ*` so that all `x`-linear terms share one dot product.
    calc
      lam * ((data.aStar i ⬝ᵥ x : ℝ) + data.α i) =
          lam * (data.aStar i ⬝ᵥ x : ℝ) + data.α i * lam := by
            ring
      _ = (x ⬝ᵥ (lam • data.aStar i) : ℝ) + data.α i * lam := by
            simp [dotProduct_comm, dotProduct_smul, smul_eq_mul]
  have hLinear :
      (x ⬝ᵥ (lam • data.aStar i + (data.A i).transpose.mulVec pStar) : ℝ) =
        (x ⬝ᵥ (lam • data.aStar i) : ℝ) + (x ⬝ᵥ (data.A i).transpose.mulVec pStar : ℝ) := by
    -- Expand the final collected coefficient of `x`.
    simp [dotProduct_add]
  -- After the affine terms are normalized, plain real arithmetic closes the identity.
  rw [hMatrix, hScaled, hLinear]
  ring

/-- Helper for Theorem 6.30.24: an infimum over intermediate-program perturbation parameters can
be rewritten as nested infima over the scalar thresholds, the head translation `p₀`, and the
dependent family of translated constraint coordinates `pᵢ`. -/
lemma helperForTheorem_6_30_24_iInf_parameter_eq_nestedBlocks
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (H : IntermediateProgramParameter m n n0 ni → EReal) :
    (⨅ w : IntermediateProgramParameter m n n0 ni, H w) =
      (⨅ v : Fin m → ℝ, ⨅ p0 : Fin n0 → ℝ, ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
        H { v := v, p0 := p0, p := p }) := by
  -- The structure infimum and the explicit block infimum dominate each other by evaluation.
  refine le_antisymm ?_ ?_
  · refine le_iInf ?_
    intro v
    refine le_iInf ?_
    intro p0
    refine le_iInf ?_
    intro p
    exact iInf_le H { v := v, p0 := p0, p := p }
  · refine le_iInf ?_
    intro w
    exact le_trans
      (iInf_le (fun v : Fin m → ℝ =>
        ⨅ p0 : Fin n0 → ℝ, ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
          H { v := v, p0 := p0, p := p }) w.v)
      (le_trans
        (iInf_le (fun p0 : Fin n0 → ℝ =>
          ⨅ p : ∀ i : Fin m, Fin (ni i) → ℝ,
            H { v := w.v, p0 := p0, p := p }) w.p0)
        (iInf_le (fun p : ∀ i : Fin m, Fin (ni i) → ℝ =>
          H { v := w.v, p0 := w.p0, p := p }) w.p))

/-- Helper for Theorem 6.30.24: at fixed `x`, the feasibility indicator of the intermediate
program splits into the finite sum of the independent scalar-threshold indicators for each pair
`(vᵢ, pᵢ)`. -/
lemma helperForTheorem_6_30_24_feasibleIndicator_eq_sum_pairIndicators
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x : Fin n → ℝ) (v : Fin m → ℝ) (p0 : Fin n0 → ℝ)
    (p : ∀ i : Fin m, Fin (ni i) → ℝ) :
    indicatorFunction (intermediateProgramFeasibleSet data
        ({ v := v, p0 := p0, p := p } : IntermediateProgramParameter m n n0 ni)) x =
      ∑ i : Fin m,
        (if data.h i ((data.A i).mulVec x + data.a i - p i) +
            ((((data.aStar i ⬝ᵥ x : ℝ) + data.α i : ℝ) : EReal)) ≤
              ((v i : ℝ) : EReal) then
            (0 : EReal)
          else
            (⊤ : EReal)) := by
  classical
  let term : Fin m → EReal := fun i =>
    if data.h i ((data.A i).mulVec x + data.a i - p i) +
          ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal))) ≤
        ((v i : ℝ) : EReal) then
      (0 : EReal)
    else
      (⊤ : EReal)
  by_cases hx : x ∈ intermediateProgramFeasibleSet data
      ({ v := v, p0 := p0, p := p } : IntermediateProgramParameter m n n0 ni)
  · -- On the feasible branch every coordinate indicator is zero.
    have hterm_zero : ∀ i : Fin m, term i = 0 := by
      intro i
      have hle :
          data.h i ((data.A i).mulVec x + data.a i - p i) +
              ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal))) ≤
            ((v i : ℝ) : EReal) := by
        simpa [EReal.coe_add, add_assoc] using hx i
      simp [term, hle]
    have hsum_zero : ∑ i : Fin m, term i = 0 := by
      simp [hterm_zero]
    rw [indicatorFunction, if_pos hx]
    exact hsum_zero.symm
  · -- On the infeasible branch one violated constraint forces the whole finite sum to be `⊤`.
    have hx' :
      ¬ ∀ i : Fin m,
        data.h i ((data.A i).mulVec x + data.a i - p i) +
              ((((data.aStar i ⬝ᵥ x : ℝ) : EReal) + ((data.α i : ℝ) : EReal))) ≤
            ((v i : ℝ) : EReal) := by
      simpa [intermediateProgramFeasibleSet, EReal.coe_add, add_assoc] using hx
    push_neg at hx'
    rcases hx' with ⟨i0, hi0⟩
    have htop_term : term i0 = (⊤ : EReal) := by
      simp [term, hi0]
    have hbot_term :
        ∀ j ∈ (Finset.univ : Finset (Fin m)), term j ≠ (⊥ : EReal) := by
      intro j hj
      by_cases hj' :
          data.h j ((data.A j).mulVec x + data.a j - p j) +
              ((((data.aStar j ⬝ᵥ x : ℝ) : EReal) + ((data.α j : ℝ) : EReal))) ≤
            ((v j : ℝ) : EReal)
      · simp [term, hj']
      · simp [term, hj']
    have hsum_top : ∑ i : Fin m, term i = (⊤ : EReal) := by
      exact sum_eq_top_of_term_top (s := (Finset.univ : Finset (Fin m)))
        (f := term) (i := i0) (by simp) htop_term hbot_term
    rw [indicatorFunction, if_neg hx]
    exact hsum_top.symm

/-- Helper for Theorem 6.30.24: a dependent finite family of independent blocks splits under an
infimum into the sum of the blockwise infima once each block has one finite witness. -/
lemma helperForTheorem_6_30_24_dependentFamily_iInf_sum_eq_sum_iInf_generic
    {m : ℕ} {α : Fin m → Type*}
    (g : ∀ i : Fin m, α i → EReal)
    (hfinite : ∀ i : Fin m, ∃ a : α i, g i a < (⊤ : EReal)) :
    (⨅ z : (i : Fin m) → α i, ∑ i : Fin m, g i (z i)) =
      ∑ i : Fin m, (⨅ a : α i, g i a) := by
  induction m with
  | zero =>
      -- With no blocks there is only the empty family, so both sides are the empty sum.
      simp
  | succ m ih =>
      have hsnoc :
          (⨅ z : (i : Fin (m + 1)) → α i, ∑ i : Fin (m + 1), g i (z i)) =
            (⨅ p : α (Fin.last m) × ((i : Fin m) → α i.castSucc),
              ∑ i : Fin (m + 1), g i ((Fin.snoc p.2 p.1) i)) := by
        -- Reindex the dependent family by its last block together with the cast-succ tail.
        simpa using
          (Equiv.iInf_congr (Fin.snocEquiv α).symm
            (f := fun z : (i : Fin (m + 1)) → α i => ∑ i : Fin (m + 1), g i (z i))
            (g := fun p : α (Fin.last m) × ((i : Fin m) → α i.castSucc) =>
              ∑ i : Fin (m + 1), g i ((Fin.snoc p.2 p.1) i))
            (fun z => by simp [Fin.snocEquiv_symm_apply]))
      rw [hsnoc]
      have hRewrite :
          (⨅ p : α (Fin.last m) × ((i : Fin m) → α i.castSucc),
              ∑ i : Fin (m + 1), g i ((Fin.snoc p.2 p.1) i)) =
            (⨅ p : α (Fin.last m) × ((i : Fin m) → α i.castSucc),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) := by
        -- Splitting the `Fin (m + 1)` sum isolates the last block.
        refine iInf_congr ?_
        intro p
        rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc]
      rw [hRewrite]
      have hTailWitness :
          ∃ z : (i : Fin m) → α i.castSucc,
            (∑ i : Fin m, g (Fin.castSucc i) (z i)) < (⊤ : EReal) := by
        -- Choose a finite witness independently for each tail block and sum them.
        refine ⟨fun i => Classical.choose (hfinite (Fin.castSucc i)), ?_⟩
        exact lt_of_le_of_ne le_top <|
          finset_sum_ne_top_of_forall (s := Finset.univ)
            (f := fun i : Fin m => g (Fin.castSucc i) (Classical.choose (hfinite (Fin.castSucc i))))
            (fun i _ => ne_of_lt (Classical.choose_spec (hfinite (Fin.castSucc i))))
      have hLastWitness :
          ∃ a : α (Fin.last m), g (Fin.last m) a < (⊤ : EReal) :=
        hfinite (Fin.last m)
      letI : Nonempty ((i : Fin m) → α i.castSucc) := ⟨Classical.choose hTailWitness⟩
      letI : Nonempty (α (Fin.last m)) := ⟨Classical.choose hLastWitness⟩
      have hCommute :
          (⨅ p : α (Fin.last m) × ((i : Fin m) → α i.castSucc),
              (∑ i : Fin m, g (Fin.castSucc i) (p.2 i)) + g (Fin.last m) p.1) =
            (⨅ p : ((i : Fin m) → α i.castSucc) × α (Fin.last m),
              (∑ i : Fin m, g (Fin.castSucc i) (p.1 i)) + g (Fin.last m) p.2) := by
        -- Swap the last block and the tail family so the two-factor splitting lemma applies.
        refine (Equiv.iInf_congr
          (Equiv.prodComm (α (Fin.last m)) ((i : Fin m) → α i.castSucc)) ?_)
        intro p
        simp [add_comm]
      rw [hCommute]
      rw [helperForTheorem_6_30_22_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun z : (i : Fin m) → α i.castSucc => ∑ i : Fin m, g (Fin.castSucc i) (z i))
        (G := fun a : α (Fin.last m) => g (Fin.last m) a)
        hTailWitness hLastWitness]
      let gTail : ∀ i : Fin m, α i.castSucc → EReal := fun i => g (Fin.castSucc i)
      have hTailFinite : ∀ i : Fin m, ∃ a : α i.castSucc, gTail i a < (⊤ : EReal) := by
        -- The tail family inherits the same finite witnesses.
        intro i
        exact hfinite (Fin.castSucc i)
      rw [show
          (⨅ z : (i : Fin m) → α i.castSucc, ∑ i : Fin m, g (Fin.castSucc i) (z i)) =
            ∑ i : Fin m, (⨅ a : α i.castSucc, g (Fin.castSucc i) a) by
              simpa [gTail] using ih gTail hTailFinite]
      -- Reassemble the tail sum with the last block.
      simp [Fin.sum_univ_castSucc, add_comm]

/-- Helper for Theorem 6.30.24: the linear terms coming from the head block, the indexed
constraint blocks, and the outer subtraction `-⟪x,x*⟫` collect into the single balance-vector
coefficient `a₀* + ∑ᵢ vᵢ* aᵢ* + A₀ᵀ p₀* + ∑ᵢ Aᵢᵀ pᵢ* - x*`. -/
lemma helperForTheorem_6_30_24_translationLinearTerms_collect
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x xStar : Fin n → ℝ) (wStar : IntermediateProgramDualParameter m n n0 ni) :
    (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
      ∑ i : Fin m,
        (((x ⬝ᵥ
            ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) : ℝ) :
            EReal)) +
      (((-(x ⬝ᵥ xStar) : ℝ) : EReal)) =
    (((x ⬝ᵥ (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) : EReal)) := by
  have hsum :
      (∑ i : Fin m,
          (((x ⬝ᵥ
              ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                ℝ) : EReal))) =
        ((((∑ i : Fin m,
              (x ⬝ᵥ
                ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                  ℝ) : ℝ)) : ℝ) : EReal) := by
    -- Convert the finite `EReal` sum of linear terms back into the corresponding real sum.
    have hsumSet :
        ∀ s : Finset (Fin m),
          s.sum (fun i =>
            (((x ⬝ᵥ
                ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                  ℝ) : EReal))) =
            (((s.sum (fun i =>
                (x ⬝ᵥ
                  ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                    ℝ)) : ℝ) : EReal)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro i s hi hs
        rw [Finset.sum_insert hi, Finset.sum_insert hi, hs]
        simp [EReal.coe_add, add_assoc, add_comm]
    simpa using hsumSet Finset.univ
  have hsumDot :
      (∑ i : Fin m,
          (x ⬝ᵥ
            ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
              ℝ)) =
        (x ⬝ᵥ
          ∑ i : Fin m,
            ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) : ℝ) := by
    -- The indexed linear contributions combine into one dot product with the finite sum of
    -- coefficients.
    simpa using
      (dotProduct_sum x Finset.univ
        (fun i : Fin m =>
          (wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i))).symm
  have hreal :
      (x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) +
          (∑ i : Fin m,
            (x ⬝ᵥ
              ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) :
                ℝ)) +
          (-(x ⬝ᵥ xStar : ℝ)) =
        (x ⬝ᵥ (helperForTheorem_6_30_24_dualBalanceVector data wStar - xStar) : ℝ) := by
    -- Expand the balance vector and collect all `x`-linear coefficients in `ℝ`.
    rw [hsumDot]
    simp [helperForTheorem_6_30_24_dualBalanceVector, dotProduct_add,
      Finset.sum_add_distrib, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Lift the collected real identity back to `EReal`.
  rw [hsum]
  let a : ℝ := x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0)
  let b : ℝ :=
    ∑ i : Fin m,
      (x ⬝ᵥ ((wStar.vStar i) • data.aStar i + (data.A i).transpose.mulVec (wStar.p i)) : ℝ)
  let d : ℝ := -(x ⬝ᵥ xStar : ℝ)
  have hcoe :
      (((a : ℝ) : EReal) + (((b : ℝ) : EReal)) + (((d : ℝ) : EReal))) =
        ((((a + b + d : ℝ)) : ℝ) : EReal) := by
    simp [a, b, d, EReal.coe_add, add_assoc]
  rw [hcoe]
  simpa [a, b, d] using congrArg (fun t : ℝ => ((t : ℝ) : EReal)) hreal

/-- Helper for Theorem 6.30.24: after fixing the primal point `x`, the head `p₀`-block collapses
to the expected affine term `⟪x, a₀* + A₀ᵀ p₀*⟫` plus the head contribution to the explicit dual
objective. -/
lemma helperForTheorem_6_30_24_headBlock_iInf_eq_linear_minus_fenchel
    {m n n0 : ℕ} {ni : Fin m → ℕ}
    (data : IntermediateProgramData m n n0 ni)
    (x : Fin n → ℝ)
    (wStar : IntermediateProgramDualParameter m n n0 ni) :
    (⨅ p0 : Fin n0 → ℝ,
        data.h0 (data.A0.mulVec x + data.a0 - p0) +
          ((((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal)) +
          (((p0 ⬝ᵥ wStar.p0 : ℝ) : EReal))) =
      (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
        ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
          fenchelConjugate n0 data.h0 wStar.p0) := by
  let c : ℝ := (data.a0Star ⬝ᵥ x : ℝ) + data.α0
  have hSplit :
      (⨅ p0 : Fin n0 → ℝ,
          data.h0 (data.A0.mulVec x + data.a0 - p0) +
            ((((data.a0Star ⬝ᵥ x : ℝ) + data.α0 : ℝ) : EReal)) +
            (((p0 ⬝ᵥ wStar.p0 : ℝ) : EReal))) =
        (⨅ p0 : Fin n0 → ℝ,
          (data.h0 (data.A0.mulVec x + data.a0 - p0) +
              (((p0 ⬝ᵥ wStar.p0 : ℝ) : EReal))) +
            ((c : ℝ) : EReal)) := by
    -- The finite head constant can be reassociated to the right of the `p₀`-dependent block.
    refine iInf_congr ?_
    intro p0
    simp [c, add_assoc, add_left_comm, add_comm]
  have hAffine :
      (((data.A0.mulVec x + data.a0) ⬝ᵥ wStar.p0 : ℝ) + c) =
        (x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) +
          (data.α0 + (data.a0 ⬝ᵥ wStar.p0 : ℝ)) := by
    -- The real affine pieces match the displayed coefficient of `x` and constant term.
    simpa [c, add_assoc, add_left_comm, add_comm] using
      helperForTheorem_6_30_24_headAffineTerms_collect data x wStar.p0
  -- Pull the finite constant through the infimum, collapse the translated affine block, and
  -- rewrite the remaining real affine terms.
  rw [hSplit, helperForTheorem_6_30_22_iInf_add_realConst
    (G := fun p0 : Fin n0 → ℝ =>
      data.h0 (data.A0.mulVec x + data.a0 - p0) +
        (((p0 ⬝ᵥ wStar.p0 : ℝ) : EReal)))
    (c := c)]
  rw [helperForTheorem_6_30_22_translatedAffineBlock_iInf_eq_linear_minus_fenchel
    (g := data.h0) (x := data.A0.mulVec x + data.a0) (p := wStar.p0)]
  rw [sub_eq_add_neg]
  have hAffineE :
      (((((data.A0.mulVec x + data.a0) ⬝ᵥ wStar.p0 : ℝ) + c : ℝ)) : EReal) =
        (((((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) +
            (data.α0 + (data.a0 ⬝ᵥ wStar.p0 : ℝ)) : ℝ)) : ℝ) : EReal) := by
    exact congrArg (fun t : ℝ => ((t : ℝ) : EReal)) hAffine
  calc
    ((((data.A0.mulVec x + data.a0) ⬝ᵥ wStar.p0 : ℝ) : EReal) +
          -fenchelConjugate n0 data.h0 wStar.p0) +
        ((c : ℝ) : EReal) =
      ((((((data.A0.mulVec x + data.a0) ⬝ᵥ wStar.p0 : ℝ) + c : ℝ)) : EReal)) +
        -fenchelConjugate n0 data.h0 wStar.p0 := by
            simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
    _ =
      ((((((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) +
            (data.α0 + (data.a0 ⬝ᵥ wStar.p0 : ℝ)) : ℝ)) : ℝ) : EReal)) +
        -fenchelConjugate n0 data.h0 wStar.p0 := by
            rw [hAffineE]
    _ =
      (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
        ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) +
          -fenchelConjugate n0 data.h0 wStar.p0) := by
            simp [EReal.coe_add, add_assoc, add_left_comm, add_comm]
    _ =
      (((x ⬝ᵥ (data.a0Star + data.A0.transpose.mulVec wStar.p0) : ℝ) : EReal)) +
        ((((data.α0 : ℝ) : EReal) + ((data.a0 ⬝ᵥ wStar.p0 : ℝ) : EReal)) -
          fenchelConjugate n0 data.h0 wStar.p0) := by
            rw [sub_eq_add_neg]


end Section30
end Chap06
