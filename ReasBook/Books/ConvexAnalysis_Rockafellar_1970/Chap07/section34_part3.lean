/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part2

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePredPart3 {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

section SaddleAmbient

variable {m n : ℕ}


/-- Helper for Text 34.1.4: reverse-minimax inequality on a pair of open balls, derived from
local concave-convexity on those balls.

This lemma is the true upstream minimax/duality input required by the current proof route.
Once it is available, `helperForText_34_1_4_reverseMinimax_closedBallRadiusEnvelope` follows
by deterministic rewriting to the closed-ball-radius envelope form. -/


lemma helperForText_34_1_4_openBall_reverseMinimax_of_localConcaveConvexOn_of_saddlePointOn
    (K : SaddleFunction m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ)
    (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ})
    (hLocal :
      IsConcaveConvexOn
        ({w : Fin m → ℝ | ‖w - u‖ < ε.1})
        ({z : Fin n → ℝ | ‖z - xStar‖ < δ.1}) K)
    (w0 : Fin m → ℝ) (hw0 : ‖w0 - u‖ < ε.1)
    (z0 : Fin n → ℝ) (hz0 : ‖z0 - xStar‖ < δ.1)
    (hS : IsSaddlePointOn
      (X := {z : Fin n → ℝ | ‖z - xStar‖ < δ.1})
      (Y := {w : Fin m → ℝ | ‖w - u‖ < ε.1})
      (f := fun z w => K w z) z0 w0) :
    (⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), K w.1 z.1)
      ≤
    (⨆ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin n → ℝ // ‖z - xStar‖ < δ.1}), K w.1 z.1) := by
  -- Record the local concave-convex hypothesis to keep this helper aligned with the blocker
  -- interface used by Text 34.1.4.
  have _ :
      IsConcaveConvexOn
        ({w : Fin m → ℝ | ‖w - u‖ < ε.1})
        ({z : Fin n → ℝ | ‖z - xStar‖ < δ.1}) K := hLocal
  -- The inequality itself is the previously established saddle-point implication.
  exact
    helperForText_34_1_4_fixedNeighborhood_reverseMinimax_of_saddlePointOn
      (K := K) (u := u) (xStar := xStar) (ε := ε) (δ := δ)
      (w0 := w0) (hw0 := hw0) (z0 := z0) (hz0 := hz0) hS

/-- Helper for Text 34.1.4: a one-dimensional coordinate kernel used to exhibit that Jensen-style
concave-convexity on open balls does not force existence of a saddle point. -/
noncomputable def helperForText_34_1_4_coordKernel : SaddleFunction 1 1 :=
  fun w (_ : Fin 1 → ℝ) => (w 0 : ℝ)

/-- Helper for Text 34.1.4: the coordinate kernel is concave-convex on every pair of open balls.

The first-variable Jensen inequality holds by equality for the linear map `w ↦ w 0`, while the
second-variable inequality holds because the kernel is constant in the second variable. -/
lemma helperForText_34_1_4_coordKernel_concaveConvexOn_openBalls
    (u xStar : Fin 1 → ℝ) (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    IsConcaveConvexOn
      ({w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
      ({z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
      helperForText_34_1_4_coordKernel := by
  -- Split into concavity in the first variable and convexity in the second.
  constructor
  · intro v hv
    intro x y hx hy a b ha hb hab hxy
    -- The defining Jensen inequality reduces to a reflexive `≤` after evaluation at `0`.
    simp [helperForText_34_1_4_coordKernel]
  · intro u' hu'
    intro x y hx hy a b ha hb hab hxy
    -- Normalize the constant-in-`z` kernel and reduce the inequality to `ℝ`.
    simp [helperForText_34_1_4_coordKernel]
    have hmulA : (a : EReal) * (u' 0 : EReal) = ((a * u' 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul a (u' 0)).symm
    have hmulB : (b : EReal) * (u' 0 : EReal) = ((b * u' 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul b (u' 0)).symm
    rw [hmulA, hmulB]
    have hadd :
        ((a * u' 0 : ℝ) : EReal) + ((b * u' 0 : ℝ) : EReal) =
          ((a * u' 0 + b * u' 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_add (a * u' 0) (b * u' 0)).symm
    rw [hadd]
    have h : a * u' 0 + b * u' 0 = u' 0 := by
      -- Use `a + b = 1` to collapse the affine combination.
      calc
        a * u' 0 + b * u' 0 = (a + b) * u' 0 := by ring
        _ = u' 0 := by simpa [hab]
    -- Cast the equality back into the `EReal` inequality.
    exact
      (EReal.coe_le_coe_iff (x := (u' 0 : ℝ)) (y := (a * u' 0 + b * u' 0 : ℝ))).2
        (le_of_eq h.symm)

/-- Helper for Text 34.1.4: the one-dimensional coordinate kernel is globally
concave-convex. -/
lemma helperForText_34_1_4_coordKernel_isConcaveConvex :
    IsConcaveConvex helperForText_34_1_4_coordKernel := by
  -- The first-variable Jensen inequality is linear, while the second-variable section is
  -- constant.
  constructor
  · intro v hv
    intro x y hx hy a b ha hb hab hxy
    simp [helperForText_34_1_4_coordKernel]
  · intro u hu
    intro x y hx hy a b ha hb hab hxy
    simp [helperForText_34_1_4_coordKernel]
    have hmulA : (a : EReal) * (u 0 : EReal) = ((a * u 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul a (u 0)).symm
    have hmulB : (b : EReal) * (u 0 : EReal) = ((b * u 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul b (u 0)).symm
    rw [hmulA, hmulB]
    have hadd :
        ((a * u 0 : ℝ) : EReal) + ((b * u 0 : ℝ) : EReal) =
          ((a * u 0 + b * u 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_add (a * u 0) (b * u 0)).symm
    rw [hadd]
    have h : a * u 0 + b * u 0 = u 0 := by
      calc
        a * u 0 + b * u 0 = (a + b) * u 0 := by ring
        _ = u 0 := by simpa [hab]
    exact
      (EReal.coe_le_coe_iff (x := (u 0 : ℝ)) (y := (a * u 0 + b * u 0 : ℝ))).2
        (le_of_eq h.symm)

/-- Helper for Text 34.1.4: the first-variable closure of the coordinate kernel vanishes at the
origin of the first variable. -/
lemma helperForText_34_1_4_coordKernel_firstClosure_at_origin
    (z : Fin 1 → ℝ) :
    partialClosure₁ helperForText_34_1_4_coordKernel 0 z = 0 := by
  -- The one-variable section `w ↦ w₀` is continuous, so Section 33 fixes its concave closure.
  let g : (Fin 1 → ℝ) → EReal := fun w => (((w 0 : ℝ)) : EReal)
  have hNegLsc : LowerSemicontinuous (fun w : Fin 1 → ℝ => -g w) := by
    have hcont : Continuous (fun w : Fin 1 → ℝ => (-((w 0 : ℝ)) : EReal)) := by
      exact continuous_coe_real_ereal.comp ((continuous_apply 0).neg)
    simpa [g] using hcont.lowerSemicontinuous
  have hNegClosed : IsFunctionConvexClosed (fun w : Fin 1 → ℝ => -g w) := by
    exact helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hNegLsc
  have hClosed : IsFunctionConcaveClosed g :=
    (helperForLemma33_0_22_functionConcaveClosed_iff_neg_isFunctionConvexClosed).2 hNegClosed
  have hPoint := congrArg (fun f => f 0) hClosed
  simpa [g, IsFunctionConcaveClosed, functionConcaveClosure, partialClosure₁,
    concaveClosureInFirst, helperForText_34_1_4_coordKernel] using hPoint.symm

/-- Helper for Text 34.1.4: the mixed lower closure of the coordinate kernel also vanishes at
the origin of the first variable. -/
lemma helperForText_34_1_4_coordKernel_lowerClosure_at_origin
    (z : Fin 1 → ℝ) :
    lowerClosureConcaveConvex
        helperForText_34_1_4_coordKernel
        helperForText_34_1_4_coordKernel_isConcaveConvex
        0 z = 0 := by
  rcases
      helperForText_34_0_1_mixedClosure_formulas
        helperForText_34_1_4_coordKernel
        helperForText_34_1_4_coordKernel_isConcaveConvex with
    ⟨hLowerFormula, -⟩
  rw [hLowerFormula, partialClosure₂, convexClosureInSecond]
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    refine iInf_le_of_le ⟨z, by simpa using ε.2⟩ ?_
    simpa using (helperForText_34_1_4_coordKernel_firstClosure_at_origin z).le
  · refine le_iSup_of_le ⟨1, by norm_num⟩ ?_
    refine le_iInf ?_
    intro w
    simpa using (helperForText_34_1_4_coordKernel_firstClosure_at_origin w.1).symm.le

/-- Helper for Text 34.1.4: a one-dimensional coordinate kernel in the second variable, used to
test the right closed-ball bridge. -/
noncomputable def helperForText_34_1_4_secondCoordKernel : SaddleFunction 1 1 :=
  fun (_ : Fin 1 → ℝ) z => (z 0 : ℝ)

/-- Helper for Text 34.1.4: the second-coordinate kernel is globally concave-convex. -/
lemma helperForText_34_1_4_secondCoordKernel_isConcaveConvex :
    IsConcaveConvex helperForText_34_1_4_secondCoordKernel := by
  -- The first-variable section is constant, while the second-variable Jensen inequality is
  -- linear.
  constructor
  · intro v hv
    intro x y hx hy a b ha hb hab hxy
    simp [helperForText_34_1_4_secondCoordKernel]
    have hmulA : (a : EReal) * (v 0 : EReal) = ((a * v 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul a (v 0)).symm
    have hmulB : (b : EReal) * (v 0 : EReal) = ((b * v 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_mul b (v 0)).symm
    rw [hmulA, hmulB]
    have hadd :
        ((a * v 0 : ℝ) : EReal) + ((b * v 0 : ℝ) : EReal) =
          ((a * v 0 + b * v 0 : ℝ) : EReal) := by
      simpa using (EReal.coe_add (a * v 0) (b * v 0)).symm
    rw [hadd]
    have h : a * v 0 + b * v 0 = v 0 := by
      calc
        a * v 0 + b * v 0 = (a + b) * v 0 := by ring
        _ = v 0 := by simpa [hab]
    rw [h]
  · intro u hu
    intro x y hx hy a b ha hb hab hxy
    simp [helperForText_34_1_4_secondCoordKernel]

/-- Helper for Text 34.1.4: the first closure of the second-coordinate kernel is trivial because
the kernel is constant in the first variable. -/
lemma helperForText_34_1_4_secondCoordKernel_firstClosure
    (u z : Fin 1 → ℝ) :
    partialClosure₁ helperForText_34_1_4_secondCoordKernel u z = (((z 0 : ℝ)) : EReal) := by
  apply le_antisymm
  · have hε : (0 : ℝ) < 1 := by
      norm_num
    calc
      partialClosure₁ helperForText_34_1_4_secondCoordKernel u z
          ≤
        ⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < (1 : ℝ)}), (((z 0 : ℝ)) : EReal) := by
            exact
              iInf_le
                (fun ε : {ε : ℝ // 0 < ε} =>
                  ⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}), (((z 0 : ℝ)) : EReal))
                ⟨1, hε⟩
      _ = (((z 0 : ℝ)) : EReal) := by
          apply le_antisymm
          · refine iSup_le ?_
            intro w
            exact le_rfl
          · exact
              le_iSup
                (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < (1 : ℝ)} => (((z 0 : ℝ)) : EReal))
                ⟨u, by simpa using hε⟩
  · refine le_iInf ?_
    intro ε
    refine le_iSup
      (fun w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} => (((z 0 : ℝ)) : EReal))
      ⟨u, by simpa using ε.2⟩

/-- Helper for Text 34.1.4: the second closure of the second-coordinate kernel vanishes at the
origin of the second variable. -/
lemma helperForText_34_1_4_secondCoordKernel_secondClosure_at_origin
    (u : Fin 1 → ℝ) :
    partialClosure₂ helperForText_34_1_4_secondCoordKernel u 0 = 0 := by
  -- The second-variable section `z ↦ z₀` is continuous, so Section 33 fixes its convex
  -- closure.
  let g : (Fin 1 → ℝ) → EReal := fun z => (((z 0 : ℝ)) : EReal)
  have hgLsc : LowerSemicontinuous g := by
    have hcont : Continuous (fun z : Fin 1 → ℝ => (((z 0 : ℝ)) : EReal)) := by
      exact continuous_coe_real_ereal.comp (continuous_apply 0)
    simpa [g] using hcont.lowerSemicontinuous
  have hgClosed : IsFunctionConvexClosed g := by
    exact helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hgLsc
  have hPoint := congrArg (fun f => f 0) hgClosed
  simpa [g, IsFunctionConvexClosed, functionConvexClosure, partialClosure₂,
    convexClosureInSecond, helperForText_34_1_4_secondCoordKernel] using hPoint.symm

/-- Helper for Text 34.1.4: the mixed lower closure of the second-coordinate kernel also
vanishes at the origin of the second variable. -/
lemma helperForText_34_1_4_secondCoordKernel_lowerClosure_at_origin
    (u : Fin 1 → ℝ) :
    lowerClosureConcaveConvex
        helperForText_34_1_4_secondCoordKernel
        helperForText_34_1_4_secondCoordKernel_isConcaveConvex
        u 0 = 0 := by
  rcases
      helperForText_34_0_1_mixedClosure_formulas
        helperForText_34_1_4_secondCoordKernel
        helperForText_34_1_4_secondCoordKernel_isConcaveConvex with
    ⟨hLowerFormula, -⟩
  rw [hLowerFormula]
  calc
    partialClosure₂ (partialClosure₁ helperForText_34_1_4_secondCoordKernel) u 0
        =
      partialClosure₂ helperForText_34_1_4_secondCoordKernel u 0 := by
          congr 1
          funext u'
          funext z
          exact helperForText_34_1_4_secondCoordKernel_firstClosure u' z
    _ = 0 := helperForText_34_1_4_secondCoordKernel_secondClosure_at_origin u

/-- Helper for Text 34.1.4: any point in a nontrivial open ball in `Fin 1 → ℝ` can be moved to a
nearby point in the same ball with strictly larger `0`-th coordinate. -/
lemma helperForText_34_1_4_exists_mem_openBall_gt_coord_fin1
    (u : Fin 1 → ℝ) (ε : ℝ) (w0 : Fin 1 → ℝ) (hw0 : ‖w0 - u‖ < ε) :
    ∃ w : Fin 1 → ℝ, ‖w - u‖ < ε ∧ w0 0 < w 0 := by
  -- Take a step of size `t` in the (unique) coordinate direction.
  have hpos : 0 < ε - ‖w0 - u‖ := sub_pos.mpr hw0
  let t : ℝ := (ε - ‖w0 - u‖) / 2
  have htpos : 0 < t := by
    dsimp [t]
    nlinarith
  let e : Fin 1 → ℝ := fun _ => 1
  refine ⟨w0 + t • e, ?_, ?_⟩
  · -- Stay inside the open ball by triangle inequality.
    have he : ‖e‖ = (1 : ℝ) := by
      simp [e, Pi.norm_def]
    have hstep : ‖t • e‖ < ε - ‖w0 - u‖ := by
      have ht0 : 0 ≤ t := le_of_lt htpos
      have hn : ‖t • e‖ = t := by
        calc
          ‖t • e‖ = |t| * ‖e‖ := by simpa using (norm_smul t e)
          _ = |t| := by simp [he]
          _ = t := by simp [abs_of_nonneg ht0]
      have : t < ε - ‖w0 - u‖ := by
        dsimp [t]
        nlinarith
      simpa [hn] using this
    have hwsub : (w0 + t • e) - u = (w0 - u) + t • e := by
      abel
    have htriangle : ‖(w0 - u) + t • e‖ ≤ ‖w0 - u‖ + ‖t • e‖ := by
      simpa using (norm_add_le (w0 - u) (t • e))
    have : ‖(w0 + t • e) - u‖ < ε := by
      calc
        ‖(w0 + t • e) - u‖ = ‖(w0 - u) + t • e‖ := by simpa [hwsub]
        _ ≤ ‖w0 - u‖ + ‖t • e‖ := htriangle
        _ < ‖w0 - u‖ + (ε - ‖w0 - u‖) := by
              have : ‖t • e‖ < ε - ‖w0 - u‖ := hstep
              linarith
        _ = ε := by ring
    simpa using this
  · -- The `0`-th coordinate strictly increases by `t > 0`.
    have : w0 0 < (w0 + t • e) 0 := by
      simp [Pi.add_apply, Pi.smul_apply, e, htpos]
    simpa [Pi.add_apply] using this

/-- Helper for Text 34.1.4: the coordinate kernel admits no saddle point on open balls.

This gives a concrete counterexample to the naive implication
`IsConcaveConvexOn (openBall u ε) (openBall xStar δ) K → ∃ saddle point`,
so the corresponding step in the proof pipeline must be replaced by a genuine minimax/duality
theorem with additional hypotheses (compactness/attainment, semicontinuity, etc.). -/
lemma helperForText_34_1_4_coordKernel_no_saddlePointOn_openBalls
    (u xStar : Fin 1 → ℝ) (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    ¬ (∃ (w0 : Fin 1 → ℝ), ‖w0 - u‖ < ε.1 ∧
        ∃ (z0 : Fin 1 → ℝ), ‖z0 - xStar‖ < δ.1 ∧
          IsSaddlePointOn
            (X := {z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
            (Y := {w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
            (f := fun z w => helperForText_34_1_4_coordKernel w z) z0 w0) := by
  intro h
  rcases h with ⟨w0, hw0, z0, hz0, hS⟩
  -- Move `w0` to a nearby point `w` in the same open ball with larger coordinate.
  rcases
      helperForText_34_1_4_exists_mem_openBall_gt_coord_fin1
        (u := u) (ε := ε.1) (w0 := w0) hw0 with
    ⟨w, hw, hlt⟩
  -- Apply the saddle-point inequality with `x = z0` and `y = w`.
  have hineq : helperForText_34_1_4_coordKernel w z0 ≤ helperForText_34_1_4_coordKernel w0 z0 := by
    have := hS z0 hz0 w hw
    simpa [helperForText_34_1_4_coordKernel] using this
  -- Contradict the strict inequality on the `0`-th coordinate.
  have hltE : (w0 0 : EReal) < (w 0 : EReal) :=
    (EReal.coe_lt_coe_iff (x := w0 0) (y := w 0)).2 hlt
  have hcontr : (w0 0 : EReal) < (w0 0 : EReal) :=
    lt_of_lt_of_le hltE (by simpa [helperForText_34_1_4_coordKernel] using hineq)
  exact (lt_irrefl _ hcontr)

/-- Helper for Text 34.1.4: counterexample showing that the open-ball saddle-point existence step
cannot be proved from `IsConcaveConvexOn` alone. -/
lemma helperForText_34_1_4_counterexample_openBall_exists_saddlePointOn_false
    (u xStar : Fin 1 → ℝ) (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    IsConcaveConvexOn
        ({w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
        ({z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
        helperForText_34_1_4_coordKernel ∧
      ¬ (∃ (w0 : Fin 1 → ℝ), ‖w0 - u‖ < ε.1 ∧
          ∃ (z0 : Fin 1 → ℝ), ‖z0 - xStar‖ < δ.1 ∧
            IsSaddlePointOn
              (X := {z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
              (Y := {w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
              (f := fun z w => helperForText_34_1_4_coordKernel w z) z0 w0) := by
  -- The first component is the concave-convexity check; the second is the no-saddle-point lemma.
  refine ⟨?_, ?_⟩
  · exact
      helperForText_34_1_4_coordKernel_concaveConvexOn_openBalls
        (u := u) (xStar := xStar) (ε := ε) (δ := δ)
  · exact
      helperForText_34_1_4_coordKernel_no_saddlePointOn_openBalls
        (u := u) (xStar := xStar) (ε := ε) (δ := δ)

/-- Helper for Text 34.1.4: the abandoned open-ball route is already false in dimension `1`.

Concretely, there is no uniform theorem saying that local concave-convexity on open balls forces
existence of a saddle point on those balls. -/
lemma helperForText_34_1_4_no_uniform_openBall_saddlePointExistence_in_dim1 :
    ¬ ∀ (K : SaddleFunction 1 1) (u xStar : Fin 1 → ℝ)
        (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}),
        IsConcaveConvexOn
          ({w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
          ({z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
          K →
        ∃ (w0 : Fin 1 → ℝ), ‖w0 - u‖ < ε.1 ∧
          ∃ (z0 : Fin 1 → ℝ), ‖z0 - xStar‖ < δ.1 ∧
            IsSaddlePointOn
              (X := {z : Fin 1 → ℝ | ‖z - xStar‖ < δ.1})
              (Y := {w : Fin 1 → ℝ | ‖w - u‖ < ε.1})
              (f := fun z w => K w z) z0 w0 := by
  intro hPrinciple
  let u : Fin 1 → ℝ := 0
  let xStar : Fin 1 → ℝ := 0
  let ε : {ε : ℝ // 0 < ε} := ⟨1, by norm_num⟩
  let δ : {δ : ℝ // 0 < δ} := ⟨1, by norm_num⟩
  -- Instantiate the claimed uniform principle at the explicit coordinate-kernel counterexample.
  have hCounterexample :=
    helperForText_34_1_4_counterexample_openBall_exists_saddlePointOn_false
      (u := u) (xStar := xStar) (ε := ε) (δ := δ)
  -- The counterexample supplies local concave-convexity but forbids any saddle point.
  exact
    hCounterexample.2
      (hPrinciple helperForText_34_1_4_coordKernel u xStar ε δ hCounterexample.1)

/-- Helper for Text 34.1.4: the coordinate kernel satisfies the reverse-minimax inequality on
open balls even though it has no saddle point there.

This emphasizes that failure of saddle-point attainment does not by itself refute reverse minimax;
what is missing for the general theorem is a genuine minimax/duality input, not the simple
saddle-point existence step. -/
lemma helperForText_34_1_4_coordKernel_reverseMinimax_openBalls
    (u xStar : Fin 1 → ℝ) (ε : {ε : ℝ // 0 < ε}) (δ : {δ : ℝ // 0 < δ}) :
    (⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
        ⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
          helperForText_34_1_4_coordKernel w.1 z.1)
      ≤
    (⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
        ⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
          helperForText_34_1_4_coordKernel w.1 z.1) := by
  classical
  -- Pick the ball center `xStar` as a witness to evaluate the outer `iInf`.
  have hz0 : ‖xStar - xStar‖ < δ.1 := by
    simpa using δ.2
  let z0 : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1} := ⟨xStar, hz0⟩

  -- Step 1: `iInf` is below any of its terms, so we can drop the outer infimum by evaluating at
  -- `z0`.
  have hDrop :
      (⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
          ⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
            helperForText_34_1_4_coordKernel w.1 z.1)
        ≤
      (⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
          helperForText_34_1_4_coordKernel w.1 z0.1) := by
    exact
      iInf_le
        (fun z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1} =>
          ⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
            helperForText_34_1_4_coordKernel w.1 z.1)
        z0

  -- Step 2: since the coordinate kernel is constant in the second variable, the inner `iInf`
  -- evaluates to the same value at every `z`, in particular at `z0`.
  have hConst :
      (⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
          helperForText_34_1_4_coordKernel w.1 z0.1)
        =
      (⨆ (w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1}),
          ⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
            helperForText_34_1_4_coordKernel w.1 z.1) := by
    -- Since the coordinate kernel ignores `z`, we can show that each inner `iInf` is equal to
    -- the value at `z0`, then take `iSup` over `w`.
    have hpoint :
        ∀ w : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1},
          (⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
              helperForText_34_1_4_coordKernel w.1 z.1) =
            helperForText_34_1_4_coordKernel w.1 z0.1 := by
      intro w
      -- Both sides are the same constant `w 0`.
      apply le_antisymm
      · -- `iInf` is below its value at `z0`.
        exact iInf_le (fun z => helperForText_34_1_4_coordKernel w.1 z.1) z0
      · -- Conversely, the value at `z0` is below the `iInf` of the constant function.
        refine le_iInf ?_
        intro z
        simp [helperForText_34_1_4_coordKernel]
    -- Now lift the pointwise equality to the two `iSup` expressions.
    apply le_antisymm
    · -- `≤`: rewrite the value at `z0` as an inner `iInf`, then use `le_iSup`.
      refine iSup_le ?_
      intro w
      have hw :
          helperForText_34_1_4_coordKernel w.1 z0.1 =
            (⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
                helperForText_34_1_4_coordKernel w.1 z.1) :=
        (hpoint w).symm
      -- After rewriting, this is exactly the canonical bound into an `iSup`.
      simpa [hw] using
        (le_iSup
          (fun w' : {w : Fin 1 → ℝ // ‖w - u‖ < ε.1} =>
            ⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
              helperForText_34_1_4_coordKernel w'.1 z.1)
          w)
    · -- `≥`: bound each inner `iInf` by the value at `z0`, then use `le_iSup`.
      refine iSup_le ?_
      intro w
      -- First, `iInf` is below its value at `z0`.
      have hw :
          (⨅ (z : {z : Fin 1 → ℝ // ‖z - xStar‖ < δ.1}),
              helperForText_34_1_4_coordKernel w.1 z.1)
            ≤
          helperForText_34_1_4_coordKernel w.1 z0.1 :=
        iInf_le (fun z => helperForText_34_1_4_coordKernel w.1 z.1) z0
      -- Then lift this to the `iSup` bound.
      exact le_trans hw (le_iSup (fun w' => helperForText_34_1_4_coordKernel w'.1 z0.1) w)

  -- Combine the drop of `iInf` with the constant-in-`z` rewrite.
  exact le_trans hDrop (le_of_eq hConst)

/-- Helper for Text 34.1.4: graph-function closedness upgrades a Rockafellar convex bifunction
to a closed convex bifunction. -/
lemma helperForText_34_1_4_closedConvexBifunction_of_graphFunctionClosed
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hGraphClosed : IsFunctionConvexClosed (graphFunctionOfBifunction F)) :
    ClosedConvexBifunction F := by
  -- First freeze the parameter to recover exact sectionwise convex-closedness from graph
  -- closedness.
  have hSectionClosed :
      ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  have hSectionClosureExact :
      ∀ u x, convexFunctionClosure (F u) x = F u x := by
    intro u x
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x := helperForLemma33_0_18_functionConvexClosure_eq_self (hSectionClosed u) x
  -- Then the valid Section 33 graph-convexity theorem applies to the exact sectionwise
  -- closure formulas.
  have hGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) :=
    helperForLemma33_0_14_graphConvex_of_rockafellarConvex_and_exactSectionwiseClosure
      (F := F) hRock hSectionClosureExact hNoBot
  -- A fixed point of the raw graph convex-closure operator is automatically lower
  -- semicontinuous because the closure itself always is.
  have hGraphLsc : LowerSemicontinuous (graphFunctionOfBifunction F) := by
    have hClosureLsc :
        LowerSemicontinuous (functionConvexClosure (graphFunctionOfBifunction F)) :=
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous
        (f := graphFunctionOfBifunction F)
    exact hGraphClosed ▸ hClosureLsc
  have hGraphConvexFunctionOn :
      ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
    intro p hp q hq a b ha hb hab
    rcases hp with ⟨-, hpLe⟩
    rcases hq with ⟨-, hqLe⟩
    constructor
    · simpa using
        (show a • p.1 + b • q.1 ∈ (Set.univ : Set (Fin (m + n) → ℝ)) from by
          trivial)
    · -- Apply the Jensen inequality from `IsERealConvexOn`, then bound the weighted endpoint
      -- values by the weighted endpoint heights in the epigraph.
      have hJensen :
          graphFunctionOfBifunction F (a • p.1 + b • q.1) ≤
            (a : EReal) * graphFunctionOfBifunction F p.1 +
              (b : EReal) * graphFunctionOfBifunction F q.1 :=
        hGraphConvex (x := p.1) (y := q.1) (by simp) (by simp) ha hb hab (by simp)
      have hWeightedHeights :
          (a : EReal) * graphFunctionOfBifunction F p.1 +
              (b : EReal) * graphFunctionOfBifunction F q.1
            ≤
          (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := by
        gcongr
      calc
        graphFunctionOfBifunction F (a • p.1 + b • q.1)
            ≤
          (a : EReal) * graphFunctionOfBifunction F p.1 +
            (b : EReal) * graphFunctionOfBifunction F q.1 := hJensen
        _ ≤ (a : EReal) * (p.2 : EReal) + (b : EReal) * (q.2 : EReal) := hWeightedHeights
        _ = ((a * p.2 + b * q.2 : ℝ) : EReal) := by
              have hMulA : (a : EReal) * (p.2 : EReal) = ((a * p.2 : ℝ) : EReal) := by
                simpa using (EReal.coe_mul a p.2).symm
              have hMulB : (b : EReal) * (q.2 : EReal) = ((b * q.2 : ℝ) : EReal) := by
                simpa using (EReal.coe_mul b q.2).symm
              rw [hMulA, hMulB, ← EReal.coe_add]
  have hBifConvex : ConvexBifunction F := by
    -- Unfold the graph-based convexity predicate until it matches the already-proved
    -- convexity of the graph epigraph.
    unfold ConvexBifunction ConvexFunction
    simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphConvexFunctionOn
  have hClosedGraph : ClosedConvexFunction (bifunctionGraphFunction F) := by
    -- The graph function is closed because it is convex and lower semicontinuous.
    refine ⟨?_, ?_⟩
    · unfold ConvexFunction
      simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphConvexFunctionOn
    · simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using hGraphLsc
  exact ⟨hBifConvex, hClosedGraph⟩

/-- Dimension-wide realization qualification for the converse direction of Corollary 33.3.1.
The forward closure theorem does not construct a bifunction witness from an arbitrary closure
pair, so the two canonical realization clauses are recorded explicitly. -/
structure Section34CanonicalClosureRealizationQualification (m n : ℕ) : Prop where
  upper : ∀ (K : SaddleFunction m n) (h : IsConcaveConvex K),
    HasNoBotValuesBifunction K →
    HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h) →
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          (∀ u xStar,
            lowerClosureConcaveConvex K h u xStar = convexBifunctionPairing F u xStar) ∧
          ∀ u xStar,
            partialClosure₁ (lowerClosureConcaveConvex K h) u xStar =
              convexBifunctionCanonicalAdjointPairing F xStar u
  lower : ∀ (K : SaddleFunction m n) (h : IsConcaveConvex K),
    HasNoBotValuesBifunction K →
    HasNoTopOrBotValuesBifunction (partialClosure₂ (upperClosureConcaveConvex K h)) →
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          (∀ u xStar,
            partialClosure₂ (upperClosureConcaveConvex K h) u xStar =
              convexBifunctionPairing F u xStar) ∧
          ∀ u xStar,
            upperClosureConcaveConvex K h u xStar =
              convexBifunctionCanonicalAdjointPairing F xStar u

/-- Helper for Text 34.1.4: the qualified converse of Corollary 33.3.1 gives a closed convex witness for the
canonical pair `(underline(K), cl₁ underline(K))` once the primal side is assumed to avoid both
`⊥` and `⊤`. -/
lemma helperForText_34_1_4_closedConvexWitness_exists_for_canonicalUpperPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hKNoBot : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      ClosedConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        partialClosure₁ (lowerClosureConcaveConvex K h) =
          helperForText_34_0_1_convexAdjointPairingKernel F := by
  let L := lowerClosureConcaveConvex K h
  let U := partialClosure₁ L
  have hLOrient : IsConcaveConvex L := by
    -- The mixed lower closure keeps the concave-convex orientation of `K`.
    simpa [L] using
      (helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hKNoBot).1
  have hCanonicalUpper :
      IsConcaveConvex U ∧
        IsUpperClosedSaddleFunction U ∧
        U = partialClosure₁ L ∧
        partialClosure₂ U = L := by
    -- Package `cl₁ underline(K)` in the exact closure-pair format used by Corollary 33.3.1.
    simpa [L, U] using
      helperForText_34_1_4_firstClosureOfLower_isCanonicalUpperPartner K h hKNoBot
  have hExistsUnique :
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          (∀ u xStar, L u xStar = convexBifunctionPairing F u xStar) ∧
          ∀ u xStar, U u xStar = convexBifunctionCanonicalAdjointPairing F xStar u := by
    -- The corrected existence half of Corollary 33.3.1 converts the canonical closure pair
    -- into the desired witness once `underline(K)` is assumed proper in the extended-real
    -- sense.
    simpa [L, U] using hRealization.upper K h hKNoBot hLowerNoTopBot
  rcases hExistsUnique with ⟨F, hF, -⟩
  rcases hF with ⟨hClosed, hNoBot, hLowerRepPointwise, hUpperRepPointwise⟩
  refine ⟨F, hClosed, hNoBot, ?_, ?_⟩
  · -- Convert the pointwise pairing formula into an equality of saddle-functions.
    funext u
    funext xStar
    exact hLowerRepPointwise u xStar
  · -- Do the same for the canonical upper partner written as the adjoint pairing kernel.
    funext u
    funext xStar
    simpa [L, U, helperForText_34_0_1_convexAdjointPairingKernel] using
      hUpperRepPointwise u xStar

/-- Helper for Text 34.1.4: the corrected Corollary 33.3.1 likewise gives a closed convex
witness for the canonical pair `(cl₂ overline(K), overline(K))` once the lower partner is
assumed to avoid both `⊥` and `⊤`. -/
lemma helperForText_34_1_4_closedConvexWitness_exists_for_canonicalLowerPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hKNoBot : HasNoBotValuesBifunction K)
    (hCanonicalLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (partialClosure₂ (upperClosureConcaveConvex K h)))
    (hRealization : Section34CanonicalClosureRealizationQualification m n) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      ClosedConvexBifunction F ∧
        partialClosure₂ (upperClosureConcaveConvex K h) = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h =
          helperForText_34_0_1_convexAdjointPairingKernel F := by
  let L := partialClosure₂ (upperClosureConcaveConvex K h)
  let U := upperClosureConcaveConvex K h
  have hLOrient : IsConcaveConvex L := by
    -- The canonical lower partner `cl₂ overline(K)` is concave-convex by the same
    -- one-step closure theorem used throughout the local Section 33 reductions.
    simpa [L] using
      (helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner K h hKNoBot).1
  have hUOrient : IsConcaveConvex U := by
    -- The mixed upper closure keeps the ambient concave-convex orientation of `K`.
    simpa [U] using
      (helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hKNoBot).2.1
  have hCanonicalLower :
      IsConcaveConvex L ∧
        IsLowerClosedSaddleFunction L ∧
        U = partialClosure₁ L ∧
        partialClosure₂ U = L := by
    -- Package `cl₂ overline(K)` in the exact closure-pair format required by
    -- Corollary 33.3.1.
    simpa [L, U] using
      helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner K h hKNoBot
  have hExistsUnique :
      ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          (∀ u xStar, L u xStar = convexBifunctionPairing F u xStar) ∧
          ∀ u xStar, U u xStar = convexBifunctionCanonicalAdjointPairing F xStar u := by
    -- The corrected existence half of Corollary 33.3.1 handles the dual canonical pair once
    -- its primal side is assumed proper in the same extended-real sense.
    simpa [L, U] using hRealization.lower K h hKNoBot hCanonicalLowerNoTopBot
  rcases hExistsUnique with ⟨F, hF, -⟩
  rcases hF with ⟨hClosed, -, hLowerRepPointwise, hUpperRepPointwise⟩
  refine ⟨F, hClosed, ?_, ?_⟩
  · -- Rewrite the canonical lower partner to the pointwise convex pairing.
    funext u
    funext xStar
    exact hLowerRepPointwise u xStar
  · -- Rewrite the upper mixed closure to the corresponding adjoint pairing kernel.
    funext u
    funext xStar
    simpa [L, U, helperForText_34_0_1_convexAdjointPairingKernel] using
      hUpperRepPointwise u xStar

/-- Helper for Text 34.1.4: a closed convex bifunction already has graph function fixed by the
raw convex-closure operator. -/
lemma helperForText_34_1_4_graphFunction_isFunctionConvexClosed_of_closedConvexBifunction
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F) :
    IsFunctionConvexClosed (graphFunctionOfBifunction F) := by
  -- Lower semicontinuity of the closed graph already forces equality with the raw convex
  -- closure from Section 33.
  unfold IsFunctionConvexClosed
  simpa [bifunctionGraphFunction, graphFunctionOfBifunction] using
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous hClosed.2.2

/-- Helper for Text 34.1.4: the constant `⊥` function is concave in the Jensen sense on `ℝ^n`. -/
lemma helperForText_34_1_4_constBot_isERealConcaveOn
    {n : ℕ} :
    IsERealConcaveOn (Set.univ : Set (Fin n → ℝ))
      (fun _ : Fin n → ℝ => (⊥ : EReal)) := by
  intro x y hx hy a b ha hb hab hxy
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    simp [hZeroA, hBOne]
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    simp [hZeroB, hAOne]
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  simp [EReal.coe_mul_bot_of_pos hPosA, EReal.coe_mul_bot_of_pos hPosB]

/-- Route correction for Text 34.1.4: the zero-dimensional constant-`⊥` kernel is
concave-convex, and its mixed lower closure still equals `⊥` at the unique point. -/
lemma helperForText_34_1_4_zeroDimensional_constBot_lowerClosure_eq_bot :
    let K : SaddleFunction 0 0 := fun _ _ => (⊥ : EReal)
    let h : IsConcaveConvex K := by
      constructor
      · intro v hv
        simpa using helperForText_34_1_4_constBot_isERealConcaveOn (n := 0)
      · intro u hu
        simpa using helperForTheorem33_1_constBot_isERealConvexOn (n := 0)
    lowerClosureConcaveConvex K h 0 0 = (⊥ : EReal) := by
  intro K h
  have hFirstAtZero : concaveClosureInFirst K 0 0 = (⊥ : EReal) := by
    unfold concaveClosureInFirst
    change
      (⨅ (ε : {ε : ℝ // 0 < ε}),
        ⨆ (w : {w : Fin 0 → ℝ // ‖w - 0‖ < ε.1}), K w.1 0) = (⊥ : EReal)
    apply le_antisymm
    · have hε : (0 : ℝ) < 1 := by
        norm_num
      calc
        (⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin 0 → ℝ // ‖w - 0‖ < ε.1}), K w.1 0)
            ≤ ⨆ (w : {w : Fin 0 → ℝ // ‖w - 0‖ < (1 : ℝ)}), K w.1 0 := by
                exact
                  iInf_le
                    (fun ε : {ε : ℝ // 0 < ε} =>
                      ⨆ (w : {w : Fin 0 → ℝ // ‖w - 0‖ < ε.1}), K w.1 0)
                    ⟨1, hε⟩
        _ ≤ (⊥ : EReal) := by
              refine iSup_le ?_
              intro w
              simp [K]
    · exact bot_le
  have hFirstAll : ∀ y : Fin 0 → ℝ, concaveClosureInFirst K 0 y = (⊥ : EReal) := by
    intro y
    have hy : y = 0 := Subsingleton.elim _ _
    rw [hy]
    exact hFirstAtZero
  change convexClosureInSecond (concaveClosureInFirst K) 0 0 = (⊥ : EReal)
  unfold convexClosureInSecond
  change
    (⨆ (ε : {ε : ℝ // 0 < ε}),
      ⨅ (w : {w : Fin 0 → ℝ // ‖w - 0‖ < ε.1}), concaveClosureInFirst K 0 w.1) =
        (⊥ : EReal)
  apply le_antisymm
  · refine iSup_le ?_
    intro ε
    have hε0 : ‖(0 : Fin 0 → ℝ) - 0‖ < ε.1 := by
      simpa using ε.2
    exact
      le_trans
        (iInf_le_of_le ⟨0, hε0⟩ le_rfl)
        (by simpa using hFirstAll 0)
  · exact bot_le

/-- Route correction for Text 34.1.4: the statement
`HasNoBotValuesBifunction (lowerClosureConcaveConvex K h)` is false in general. The
zero-dimensional constant-`⊥` kernel already refutes it. -/
lemma helperForText_34_1_4_zeroDimensional_constBot_refutes_lowerClosure_hasNoBot_statement :
    let K : SaddleFunction 0 0 := fun _ _ => (⊥ : EReal)
    let h : IsConcaveConvex K := by
      constructor
      · intro v hv
        simpa using helperForText_34_1_4_constBot_isERealConcaveOn (n := 0)
      · intro u hu
        simpa using helperForTheorem33_1_constBot_isERealConvexOn (n := 0)
    ¬ HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) := by
  intro K h hNoBot
  exact hNoBot 0 0 (helperForText_34_1_4_zeroDimensional_constBot_lowerClosure_eq_bot)

/-- Helper for Text 34.1.4: although `underline(K)` need not avoid `⊥` in general, any actual
closed-convex witness for `underline(K)` forces the represented mixed lower closure to have no
`⊥` values. -/
lemma helperForText_34_1_4_lowerClosure_hasNoBot_of_closedConvexLowerRepresentation
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hFiniteSections : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x < (⊤ : EReal)) :
    HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) := by
  have hRockGraph :
      IsGraphConvexBifunction F ∧
        IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
      (F := F) hClosed hNoBot
  intro u xStar hbot
  have hbot' : convexBifunctionPairing F u xStar = (⊥ : EReal) := by
    rw [← hLowerRep]
    exact hbot
  rcases hFiniteSections u with ⟨x, hx⟩
  have hPairNeBot : convexBifunctionPairing F u xStar ≠ (⊥ : EReal) := by
    simpa [convexBifunctionPairing] using
      helperForTheorem33_1_convexConjugate_ne_bot_of_point
        (f := F u) (x₀ := x) (by simpa [lt_top_iff_ne_top] using hx) xStar
  exact hPairNeBot hbot'

/-- Helper for Text 34.1.4: the usable no-`⊥` statement for `underline(K)` is the witness-local
one. The naive global version is false by the constant-`⊥` counterexample above, so the
remaining development only uses this corrected interface. -/
lemma helperForText_34_1_4_lowerClosure_hasNoBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hFiniteSections : ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x < (⊤ : EReal)) :
    HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) := by
  exact
    helperForText_34_1_4_lowerClosure_hasNoBot_of_closedConvexLowerRepresentation
      (K := K) (h := h) hRock hNoBot hClosed hLowerRep hFiniteSections

/-- Helper for Text 34.1.4: if a convex bifunction represents `underline(K)`, then none of its
parameter sections can be identically `⊤`; otherwise the pairing would force `underline(K)` to
take the value `⊥`. -/
lemma helperForText_34_1_4_witness_sections_notTop_of_lowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    ∀ u : Fin m → ℝ, ∃ x : Fin n → ℝ, F u x ≠ (⊤ : EReal) := by
  intro u
  by_contra hNotTop
  push_neg at hNotTop
  have hPairBot : convexBifunctionPairing F u (0 : Fin n → ℝ) = (⊥ : EReal) := by
    -- If the whole parameter section were `⊤`, every term in the pairing supremum would be `⊥`.
    simp only [convexBifunctionPairing, bifunctionPairingNotation, conjugatePairingNotation]
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, rfl⟩
      simpa [hNotTop x]
    · refine le_sSup ?_
      refine ⟨0, ?_⟩
      simpa [hNotTop 0]
  have hLowerBot : lowerClosureConcaveConvex K h u (0 : Fin n → ℝ) = (⊥ : EReal) := by
    -- Evaluate the representation at the zero dual vector.
    rw [hLowerRep]
    exact hPairBot
  exact (hLowerNoBot u 0) hLowerBot

/-- Helper for Text 34.1.4: any convex bifunction representing `underline(K)` already has full
strict parameter domain, because `underline(K)` never takes the value `⊥`. -/
lemma helperForText_34_1_4_strictParameterDomain_eq_univ_of_lowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    {u' : Fin m → ℝ | ∃ x : Fin n → ℝ, F u' x < ⊤} = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    -- The lower-representation witness prevents the whole parameter section from collapsing to
    -- `⊤`, so one point already lies strictly below `⊤`.
    rcases
        helperForText_34_1_4_witness_sections_notTop_of_lowerRepresentation
          (K := K) (h := h) hLowerNoBot hLowerRep u with
      ⟨x, hxTop⟩
    exact ⟨x, lt_of_le_of_ne le_top hxTop⟩

/-- Helper for Text 34.1.4: any convex bifunction representing `underline(K)` has full
Section 33 parameter domain, not just the strict `< ⊤` variant. -/
lemma helperForText_34_1_4_parameterDomain_eq_univ_of_lowerRepresentation
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerNoBot : HasNoBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F) :
    convexBifunctionParameterDomain F = Set.univ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    -- The lower-representation witness already prevents the whole section `F u` from collapsing
    -- to `⊤`, so `u` lies in the Section 33 parameter domain.
    rcases
        helperForText_34_1_4_witness_sections_notTop_of_lowerRepresentation
          (K := K) (h := h) hLowerNoBot hLowerRep u with
      ⟨x, hxTop⟩
    exact ⟨x, hxTop⟩

end SaddleAmbient

end Section34
end Chap07
